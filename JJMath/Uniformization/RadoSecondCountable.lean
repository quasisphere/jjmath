import JJMath.ComplexProjective.Prerequisites.RiemannSurface
import JJMath.AnalyticContinuation.LocalBranch
import JJMath.Hyperbolic.Cover
import JJMath.Uniformization.Perron
import JJMath.Uniformization.Subharmonic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.Zorn
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Radó's second-countability theorem

This file isolates the formalization target that every connected Riemann
surface is second countable.  The intended proof is Radó's theorem: local
complex coordinates give countable coordinate bases, and the analytic
one-dimensional structure rules out the non-second-countable behavior possible
for bare topological manifolds.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

private theorem equicontinuousOn_congr_pointwise_for_rado_ascoli
    {ι X Y : Type} [TopologicalSpace X] [UniformSpace Y]
    {S : Set X} {F G : ι → X → Y}
    (hFG : ∀ i x, F i x = G i x)
    (hF : EquicontinuousOn F S) :
    EquicontinuousOn G S := by
  intro x hx U hU
  filter_upwards [hF x hx U hU] with y hy i
  simpa [hFG i x, hFG i y] using hy i

/-- Arzelà--Ascoli extraction in the compact-open topology for continuous
maps into a second-countable Hausdorff uniform space. -/
theorem uniformContinuousMap_subsequence_tendsto_of_equicontinuousOn_compactExhaustion
    {X Y : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [SecondCountableTopology X]
    [UniformSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (K : CompactExhaustion X) (G : ℕ → C(X, Y))
    (hpointwise : ∀ x : X, ∃ Q : Set Y, IsCompact Q ∧
      ∀ n : ℕ, G n x ∈ Q)
    (heq : ∀ m : ℕ,
      EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) (K m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : C(X, Y), Filter.Tendsto (fun n : ℕ ↦ G (φ n))
        Filter.atTop (𝓝 g) := by
  haveI : SecondCountableTopology C(X, Y) := inferInstance
  have hclosedEmbedding :
      Topology.IsClosedEmbedding
        (ContinuousMap.toUniformOnFunIsCompact :
          C(X, Y) → UniformOnFun X Y {S : Set X | IsCompact S}) := by
    refine
      ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous
      CompactlyCoherentSpace.isCoherentWith
  have hcompactClosure : IsCompact (closure (Set.range G)) := by
    refine
      ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
        (𝔖 := {S : Set X | IsCompact S})
        (F := fun g : C(X, Y) ↦ fun x : X ↦ g x)
        (fun S hS ↦ hS) ?_ ?_ ?_
    · simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
        hclosedEmbedding
    · intro S hS
      obtain ⟨m, hmS⟩ := K.exists_superset_of_isCompact hS
      let chooseIndex : Set.range G → ℕ :=
        fun g ↦ Classical.choose g.property
      have hchoose : ∀ g : Set.range G, G (chooseIndex g) = g :=
        fun g ↦ Classical.choose_spec g.property
      have hseqS :
          EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) S :=
        (heq m).mono hmS
      have hcomp :
          EquicontinuousOn
            ((fun n : ℕ ↦ fun x : X ↦ G n x) ∘ chooseIndex) S :=
        hseqS.comp chooseIndex
      refine equicontinuousOn_congr_pointwise_for_rado_ascoli ?_ hcomp
      intro g x
      simpa [Function.comp_def] using
        congrArg (fun h : C(X, Y) ↦ h x) (hchoose g)
    · intro S hS x hx
      rcases hpointwise x with ⟨Q, hQcompact, hQmem⟩
      refine ⟨Q, hQcompact, ?_⟩
      intro g hg
      rcases hg with ⟨n, rfl⟩
      exact hQmem n
  have hmem : ∀ n : ℕ, G n ∈ closure (Set.range G) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  rcases hcompactClosure.tendsto_subseq hmem with
    ⟨g, _hg, φ, hφ, hφ_tendsto⟩
  exact ⟨φ, hφ, g, by simpa [Function.comp_def] using hφ_tendsto⟩

/-- The generic compact-open Arzelà--Ascoli subsequence converges locally
uniformly. -/
theorem uniformContinuousMap_subsequence_tendstoLocallyUniformly_of_equicontinuousOn_compactExhaustion
    {X Y : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [SecondCountableTopology X]
    [UniformSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (K : CompactExhaustion X) (G : ℕ → C(X, Y))
    (hpointwise : ∀ x : X, ∃ Q : Set Y, IsCompact Q ∧
      ∀ n : ℕ, G n x ∈ Q)
    (heq : ∀ m : ℕ,
      EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) (K m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : C(X, Y),
        TendstoLocallyUniformly
          (fun n : ℕ ↦ fun x : X ↦ G (φ n) x)
          (fun x : X ↦ g x) Filter.atTop := by
  rcases
    uniformContinuousMap_subsequence_tendsto_of_equicontinuousOn_compactExhaustion
      K G hpointwise heq with
    ⟨φ, hφ, g, hg⟩
  exact ⟨φ, hφ, g,
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hg⟩

/--
%%handwave
name:
  Real-valued compact-open Arzelà-Ascoli extraction
statement:
  A sequence of real-valued continuous functions on a locally compact
  sigma-compact second-countable space has a compact-open convergent
  subsequence if it is pointwise relatively compact and equicontinuous on
  every member of a compact exhaustion.
proof:
  Mathlib's Arzelà-Ascoli theorem gives compactness of the closure of the
  sequence in the compact-open topology.  Since the compact-open function
  space is second countable, compactness gives a convergent subsequence.
-/
theorem surfaceRealContinuousMap_subsequence_tendsto_of_equicontinuousOn_compactExhaustion
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [SecondCountableTopology X] (K : CompactExhaustion X)
    (G : ℕ → C(X, ℝ))
    (hpointwise : ∀ x : X, ∃ Q : Set ℝ, IsCompact Q ∧
      ∀ n : ℕ, G n x ∈ Q)
    (heq : ∀ m : ℕ,
      EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) (K m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : C(X, ℝ), Filter.Tendsto (fun n : ℕ ↦ G (φ n)) Filter.atTop (𝓝 g) := by
  haveI : SecondCountableTopology C(X, ℝ) := inferInstance
  have hclosedEmbedding :
      Topology.IsClosedEmbedding
        (ContinuousMap.toUniformOnFunIsCompact :
          C(X, ℝ) → UniformOnFun X ℝ {S : Set X | IsCompact S}) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
  have hcompactClosure : IsCompact (closure (Set.range G)) := by
    refine
      ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
        (𝔖 := {S : Set X | IsCompact S})
        (F := fun g : C(X, ℝ) ↦ fun x : X ↦ g x)
        (fun S hS ↦ hS) ?_ ?_ ?_
    · simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using hclosedEmbedding
    · intro S hS
      obtain ⟨m, hmS⟩ := K.exists_superset_of_isCompact hS
      let chooseIndex : Set.range G → ℕ := fun g ↦ Classical.choose g.property
      have hchoose : ∀ g : Set.range G, G (chooseIndex g) = g := fun g ↦
        Classical.choose_spec g.property
      have hseqS :
          EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) S :=
        (heq m).mono hmS
      have hcomp :
          EquicontinuousOn
            ((fun n : ℕ ↦ fun x : X ↦ G n x) ∘ chooseIndex) S :=
        hseqS.comp chooseIndex
      refine equicontinuousOn_congr_pointwise_for_rado_ascoli ?_ hcomp
      intro g x
      simpa [Function.comp_def] using congrArg (fun h : C(X, ℝ) ↦ h x) (hchoose g)
    · intro S hS x hx
      rcases hpointwise x with ⟨Q, hQcompact, hQmem⟩
      refine ⟨Q, hQcompact, ?_⟩
      intro g hg
      rcases hg with ⟨n, rfl⟩
      exact hQmem n
  have hmem : ∀ n : ℕ, G n ∈ closure (Set.range G) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  rcases hcompactClosure.tendsto_subseq hmem with
    ⟨g, _hg, φ, hφ, hφ_tendsto⟩
  exact ⟨φ, hφ, g, by simpa [Function.comp_def] using hφ_tendsto⟩

/--
%%handwave
name:
  Real-valued locally uniform Arzelà-Ascoli extraction
statement:
  Under the same compact-exhaustion hypotheses, the compact-open convergent
  subsequence converges locally uniformly.
proof:
  On weakly locally compact spaces, mathlib identifies compact-open
  convergence of continuous maps with locally uniform convergence.
-/
theorem surfaceRealContinuousMap_subsequence_tendstoLocallyUniformly_of_equicontinuousOn_compactExhaustion
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [SecondCountableTopology X] (K : CompactExhaustion X)
    (G : ℕ → C(X, ℝ))
    (hpointwise : ∀ x : X, ∃ Q : Set ℝ, IsCompact Q ∧
      ∀ n : ℕ, G n x ∈ Q)
    (heq : ∀ m : ℕ,
      EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) (K m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : C(X, ℝ),
        TendstoLocallyUniformly
          (fun n : ℕ ↦ fun x : X ↦ G (φ n) x)
          (fun x : X ↦ g x) Filter.atTop := by
  rcases
    surfaceRealContinuousMap_subsequence_tendsto_of_equicontinuousOn_compactExhaustion
      K G hpointwise heq with
    ⟨φ, hφ, g, hg⟩
  exact ⟨φ, hφ, g, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hg⟩

/--
%%handwave
name:
  Eventually interval-valued real sequences have compact range
statement:
  If a real sequence eventually lies in a fixed closed interval, then all of
  its values lie in some compact subset of the real line.
proof:
  Put the finitely many exceptional initial values into a finite compact set
  and put the tail into the closed interval.
-/
theorem exists_compact_range_of_eventually_mem_Icc
    {a : ℕ → ℝ} {A B : ℝ}
    (ha : ∀ᶠ n : ℕ in Filter.atTop, a n ∈ Set.Icc A B) :
    ∃ Q : Set ℝ, IsCompact Q ∧ ∀ n : ℕ, a n ∈ Q := by
  rcases Filter.eventually_atTop.mp ha with ⟨N, hN⟩
  let Q : Set ℝ := (Set.range fun k : Fin N ↦ a k.1) ∪ Set.Icc A B
  refine ⟨Q, ?_, ?_⟩
  · have hfinite : (Set.range fun k : Fin N ↦ a k.1).Finite :=
      Set.finite_range _
    exact hfinite.isCompact.union isCompact_Icc
  · intro n
    by_cases hn : n < N
    · exact Or.inl ⟨⟨n, hn⟩, rfl⟩
    · exact Or.inr (hN n (le_of_not_gt hn))

/--
%%handwave
name:
  Compact-restriction Arzelà-Ascoli extraction
statement:
  On a compact subset of a second-countable space, a sequence of functions
  valued in a second-countable Hausdorff uniform space has a uniformly
  convergent subsequence if the functions are continuous on the compact set,
  pointwise relatively compact there, and equicontinuous there.
proof:
  Restrict the functions to the compact subset and apply compact-open
  Arzelà--Ascoli extraction to the compact subtype.  Since the subtype is
  compact, locally uniform convergence is uniform on the whole subtype,
  hence uniform on the original compact set.
-/
theorem functions_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X]
    [UniformSpace Y] [T2Space Y] [SecondCountableTopology Y]
    {K : Set X} (hK : IsCompact K) {F : ℕ → X → Y}
    (hcont : ∀ n : ℕ, ContinuousOn (F n) K)
    (hpointwise : ∀ x ∈ K, ∃ Q : Set Y, IsCompact Q ∧
      ∀ n : ℕ, F n x ∈ Q)
    (heq : EquicontinuousOn F K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → Y,
        TendstoUniformlyOn (fun n : ℕ ↦ F (φ n)) f Filter.atTop K := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : LocallyCompactSpace K := inferInstance
  haveI : SigmaCompactSpace K := inferInstance
  haveI : SecondCountableTopology K := inferInstance
  let G : ℕ → C(K, Y) := fun n ↦
    ⟨fun x : K ↦ F n x,
      continuousOn_iff_continuous_restrict.mp (hcont n)⟩
  let Kex : CompactExhaustion K := CompactExhaustion.choice K
  have hpointwiseG :
      ∀ x : K, ∃ Q : Set Y, IsCompact Q ∧ ∀ n : ℕ, G n x ∈ Q := by
    intro x
    exact hpointwise x x.property
  have heq_restrict : Equicontinuous (K.restrict ∘ F) :=
    (equicontinuous_restrict_iff F).2 heq
  have heq_univ :
      EquicontinuousOn (fun n : ℕ ↦ fun x : K ↦ G n x) Set.univ := by
    rw [equicontinuousOn_univ]
    simpa [G, Function.comp_def] using heq_restrict
  have heqG :
      ∀ m : ℕ,
        EquicontinuousOn (fun n : ℕ ↦ fun x : K ↦ G n x) (Kex m) := by
    intro m
    exact heq_univ.mono (fun x _hx ↦ trivial)
  rcases
    uniformContinuousMap_subsequence_tendstoLocallyUniformly_of_equicontinuousOn_compactExhaustion
      Kex G hpointwiseG heqG with
    ⟨φ, hφ, g, hconv⟩
  let f : X → Y := fun x ↦ if hx : x ∈ K then g ⟨x, hx⟩ else F 0 x
  refine ⟨φ, hφ, f, ?_⟩
  have hconv_univ :
      TendstoUniformlyOn
        (fun n : ℕ ↦ fun x : K ↦ G (φ n) x)
        (fun x : K ↦ g x) Filter.atTop Set.univ :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_univ : IsCompact (Set.univ : Set K))).mp
      (by simpa [tendstoLocallyUniformlyOn_univ] using hconv)
  intro U hU
  filter_upwards [hconv_univ U hU] with n hn x hxK
  have hx : (⟨x, hxK⟩ : K) ∈ (Set.univ : Set K) := by trivial
  simpa [G, f, hxK] using hn ⟨x, hxK⟩ hx

theorem realFunctions_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : ℕ → X → ℝ}
    (hcont : ∀ n : ℕ, ContinuousOn (F n) K)
    (hpointwise : ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
      ∀ n : ℕ, F n x ∈ Q)
    (heq : EquicontinuousOn F K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn (fun n : ℕ ↦ F (φ n)) f Filter.atTop K := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : LocallyCompactSpace K := inferInstance
  haveI : SigmaCompactSpace K := inferInstance
  haveI : SecondCountableTopology K := inferInstance
  let G : ℕ → C(K, ℝ) := fun n ↦
    ⟨fun x : K ↦ F n x,
      continuousOn_iff_continuous_restrict.mp (hcont n)⟩
  let Kex : CompactExhaustion K := CompactExhaustion.choice K
  have hpointwiseG :
      ∀ x : K, ∃ Q : Set ℝ, IsCompact Q ∧ ∀ n : ℕ, G n x ∈ Q := by
    intro x
    exact hpointwise x x.property
  have heq_restrict :
      Equicontinuous (K.restrict ∘ F) :=
    (equicontinuous_restrict_iff F).2 heq
  have heq_univ :
      EquicontinuousOn (fun n : ℕ ↦ fun x : K ↦ G n x) Set.univ := by
    rw [equicontinuousOn_univ]
    simpa [G, Function.comp_def] using heq_restrict
  have heqG :
      ∀ m : ℕ,
        EquicontinuousOn (fun n : ℕ ↦ fun x : K ↦ G n x) (Kex m) := by
    intro m
    exact heq_univ.mono (fun x _hx ↦ trivial)
  rcases
    surfaceRealContinuousMap_subsequence_tendstoLocallyUniformly_of_equicontinuousOn_compactExhaustion
      Kex G hpointwiseG heqG with
    ⟨φ, hφ, g, hconv⟩
  let f : X → ℝ := fun x ↦ if hx : x ∈ K then g ⟨x, hx⟩ else 0
  refine ⟨φ, hφ, f, ?_⟩
  have hconv_univ :
      TendstoUniformlyOn
        (fun n : ℕ ↦ fun x : K ↦ G (φ n) x)
        (fun x : K ↦ g x) Filter.atTop Set.univ :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_univ : IsCompact (Set.univ : Set K))).mp
      (by simpa [tendstoLocallyUniformlyOn_univ] using hconv)
  intro U hU
  filter_upwards [hconv_univ U hU] with n hn x hxK
  have hx : (⟨x, hxK⟩ : K) ∈ (Set.univ : Set K) := by trivial
  simpa [G, f, hxK] using hn ⟨x, hxK⟩ hx

/--
%%handwave
name:
  Tail compact-restriction Arzelà-Ascoli extraction
statement:
  On a compact subset of a second-countable space, a tail of a sequence of
  functions with values in a second-countable Hausdorff uniform space has a
  uniformly convergent subsequence if that tail
  is continuous on the compact set, pointwise relatively compact there, and
  equicontinuous there.
proof:
  Apply the compact-restriction extraction theorem to the shifted sequence
  and add the finite shift back to the selected indices.
-/
theorem functions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X]
    [UniformSpace Y] [T2Space Y] [SecondCountableTopology Y]
    {K : Set X} (hK : IsCompact K) {F : ℕ → X → Y} (N : ℕ)
    (hcont : ∀ n : ℕ, ContinuousOn (F (N + n)) K)
    (hpointwise : ∀ x ∈ K, ∃ Q : Set Y, IsCompact Q ∧
      ∀ n : ℕ, F (N + n) x ∈ Q)
    (heq : EquicontinuousOn (fun n : ℕ ↦ F (N + n)) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → Y,
        TendstoUniformlyOn (fun n : ℕ ↦ F (φ n)) f Filter.atTop K := by
  rcases functions_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK hcont hpointwise heq with
    ⟨ψ, hψ, f, hf⟩
  let φ : ℕ → ℕ := fun n ↦ N + ψ n
  refine ⟨φ, ?_, f, ?_⟩
  · intro a b hab
    exact Nat.add_lt_add_left (hψ hab) N
  · simpa [φ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf

theorem realFunctions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : ℕ → X → ℝ} (N : ℕ)
    (hcont : ∀ n : ℕ, ContinuousOn (F (N + n)) K)
    (hpointwise : ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
      ∀ n : ℕ, F (N + n) x ∈ Q)
    (heq : EquicontinuousOn (fun n : ℕ ↦ F (N + n)) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn (fun n : ℕ ↦ F (φ n)) f Filter.atTop K := by
  rcases realFunctions_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK hcont hpointwise heq with
    ⟨ψ, hψ, f, hf⟩
  let φ : ℕ → ℕ := fun n ↦ N + ψ n
  refine ⟨φ, ?_, f, ?_⟩
  · intro a b hab
    exact Nat.add_lt_add_left (hψ hab) N
  · simpa [φ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf

/--
%%handwave
name:
  Uniform convergence on a compact exhaustion gives uniform convergence on compact sets
statement:
  If a sequence of functions converges uniformly on every member of a compact
  exhaustion, then it converges uniformly on every compact subset of the
  space.
proof:
  A compact subset is contained in one exhaustion member, and uniform
  convergence restricts to smaller sets.
-/
theorem tendstoUniformlyOn_of_compactExhaustion
    {ι X Y : Type} [TopologicalSpace X] [UniformSpace Y]
    (Kex : CompactExhaustion X)
    {F : ι → X → Y} {f : X → Y} {l : Filter ι}
    (hconv : ∀ n : ℕ, TendstoUniformlyOn F f l (Kex n)) :
    ∀ K : Set X, IsCompact K → TendstoUniformlyOn F f l K := by
  intro K hK
  rcases Kex.exists_superset_of_isCompact hK with ⟨n, hKn⟩
  exact (hconv n).mono hKn

/-- Uniform limits named separately on the members of a compact exhaustion
glue to one global limit. -/
theorem tendstoUniformlyOn_compactExhaustion_glue
    {X Y : Type} [TopologicalSpace X] [UniformSpace Y] [T2Space Y]
    (Kex : CompactExhaustion X)
    {F : ℕ → X → Y} {g : ℕ → X → Y}
    (hconv : ∀ n : ℕ, TendstoUniformlyOn F (g n) Filter.atTop (Kex n)) :
    ∃ f : X → Y,
      ∀ n : ℕ, TendstoUniformlyOn F f Filter.atTop (Kex n) := by
  classical
  let f : X → Y := fun x ↦ g (Kex.find x) x
  refine ⟨f, ?_⟩
  intro n
  exact (hconv n).congr_right (by
    intro x hx
    have hfind_tendsto :
        Filter.Tendsto (fun k : ℕ ↦ F k x) Filter.atTop
          (𝓝 (g (Kex.find x) x)) :=
      (hconv (Kex.find x)).tendsto_at (Kex.mem_find x)
    have hn_tendsto :
        Filter.Tendsto (fun k : ℕ ↦ F k x) Filter.atTop (𝓝 (g n x)) :=
      (hconv n).tendsto_at hx
    have h_eq : g n x = g (Kex.find x) x :=
      tendsto_nhds_unique hn_tendsto hfind_tendsto
    simpa [f] using h_eq)

/--
%%handwave
name:
  Compatible compact-exhaustion limits glue to a global limit
statement:
  If one sequence of real-valued functions converges uniformly on each
  compact member of an exhaustion, possibly with a separately named limit on
  each member, then those local limits agree on overlaps and define a single
  global function to which the sequence converges on every exhaustion member.
proof:
  At a point lying in two exhaustion members, both local limits are limits of
  the same real sequence along the singleton, hence are equal by uniqueness
  of limits.  Define the global limit using the first exhaustion member that
  contains the point and replace each local limit by this global one.
-/
theorem tendstoUniformlyOn_compactExhaustion_glue_real
    {X : Type} [TopologicalSpace X]
    (Kex : CompactExhaustion X)
    {F : ℕ → X → ℝ} {g : ℕ → X → ℝ}
    (hconv : ∀ n : ℕ, TendstoUniformlyOn F (g n) Filter.atTop (Kex n)) :
    ∃ f : X → ℝ,
      ∀ n : ℕ, TendstoUniformlyOn F f Filter.atTop (Kex n) := by
  classical
  let f : X → ℝ := fun x ↦ g (Kex.find x) x
  refine ⟨f, ?_⟩
  intro n
  exact (hconv n).congr_right (by
    intro x hx
    have hfind_tendsto :
        Filter.Tendsto (fun k : ℕ ↦ F k x) Filter.atTop
          (𝓝 (g (Kex.find x) x)) :=
      (hconv (Kex.find x)).tendsto_at (Kex.mem_find x)
    have hn_tendsto :
        Filter.Tendsto (fun k : ℕ ↦ F k x) Filter.atTop (𝓝 (g n x)) :=
      (hconv n).tendsto_at hx
    have h_eq : g n x = g (Kex.find x) x :=
      tendsto_nhds_unique hn_tendsto hfind_tendsto
    simpa [f] using h_eq)

/--
%%handwave
name:
  Diagonal compact-exhaustion extraction from one-compact extractions
statement:
  Suppose that, on each compact member of an exhaustion, every subsequence of
  a function sequence with values in a Hausdorff uniform space has a further
  uniformly convergent subsequence.  Then there is one subsequence converging
  uniformly on every member of the exhaustion, hence on every compact subset.
proof:
  Recursively choose a subsequence converging on the zeroth compact set, then
  a further subsequence converging on the first compact set, and so on.  The
  diagonal sequence is strictly increasing.  For any fixed exhaustion member,
  the diagonal tail factors through the corresponding chosen subsequence with
  indices tending to infinity, so it has the same uniform limit there.  The
  preceding gluing theorem assembles these local limits into one global
  limit.
-/
theorem functions_subsequence_tendstoUniformlyOn_compactExhaustion_of_subsequence_extractions
    {X Y : Type} [TopologicalSpace X] [UniformSpace Y] [T2Space Y]
    (Kex : CompactExhaustion X)
    {F : ℕ → X → Y}
    (hextract :
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ m : ℕ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ f : X → Y,
            TendstoUniformlyOn
              (fun n : ℕ ↦ F (φ (ψ n))) f Filter.atTop (Kex m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → Y,
        ∀ m : ℕ,
          TendstoUniformlyOn (fun n : ℕ ↦ F (φ n)) f Filter.atTop (Kex m) := by
  classical
  let Step := {φ : ℕ → ℕ // StrictMono φ}
  let next : ℕ → Step → Step := fun m s =>
    let ψ : ℕ → ℕ := Classical.choose (hextract s.1 s.2 m)
    ⟨s.1 ∘ ψ, s.2.comp (Classical.choose_spec (hextract s.1 s.2 m)).1⟩
  let S : ℕ → Step := Nat.rec ⟨id, strictMono_id⟩ (fun m s ↦ next m s)
  let diag : ℕ → ℕ := fun n ↦ (S n).1 n
  have hfactor :
      ∀ {a b : ℕ}, a ≤ b → ∀ i : ℕ,
        ∃ j : ℕ, i ≤ j ∧ (S b).1 i = (S a).1 j := by
    intro a b hab
    induction hab with
    | refl =>
        intro i
        exact ⟨i, le_rfl, rfl⟩
    | @step b hab ih =>
        intro i
        let ψ : ℕ → ℕ := Classical.choose (hextract (S b).1 (S b).2 b)
        have hψ : StrictMono ψ :=
          (Classical.choose_spec (hextract (S b).1 (S b).2 b)).1
        rcases ih (ψ i) with ⟨j, hij, hEq⟩
        refine ⟨j, le_trans (StrictMono.id_le hψ i) hij, ?_⟩
        simpa [S, next, ψ, Function.comp_def] using hEq
  have hdiag_strict : StrictMono diag := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    rcases hfactor (a := n) (b := n + 1) (Nat.le_succ n) (n + 1) with
      ⟨j, hj_le, hEq⟩
    have hn_lt_j : n < j := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hj_le
    have hlt : (S n).1 n < (S n).1 j := (S n).2 hn_lt_j
    dsimp [diag]
    rw [hEq]
    exact hlt
  have hlocal :
      ∀ m : ℕ, ∃ g : X → Y,
        TendstoUniformlyOn
          (fun n : ℕ ↦ F (diag n)) g Filter.atTop (Kex m) := by
    intro m
    let ψ : ℕ → ℕ := Classical.choose (hextract (S m).1 (S m).2 m)
    let g : X → Y :=
      Classical.choose
        (Classical.choose_spec (hextract (S m).1 (S m).2 m)).2
    have hconv_step :
        TendstoUniformlyOn
          (fun n : ℕ ↦ F ((S (m + 1)).1 n)) g Filter.atTop (Kex m) := by
      have hchosen :
          TendstoUniformlyOn
            (fun n : ℕ ↦ F ((S m).1 (ψ n))) g Filter.atTop (Kex m) :=
        Classical.choose_spec
          (Classical.choose_spec (hextract (S m).1 (S m).2 m)).2
      simpa [S, next, ψ, g, Function.comp_def] using hchosen
    let shift : ℕ := m + 1
    let idx : ℕ → ℕ := fun n =>
      Classical.choose
        (hfactor (a := shift) (b := shift + n)
          (Nat.le_add_right shift n) (shift + n))
    have hidx_spec : ∀ n : ℕ,
        shift + n ≤ idx n ∧
          (S (shift + n)).1 (shift + n) = (S shift).1 (idx n) := by
      intro n
      exact Classical.choose_spec
        (hfactor (a := shift) (b := shift + n)
          (Nat.le_add_right shift n) (shift + n))
    have hidx_tendsto : Filter.Tendsto idx Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_atTop.mpr ?_
      intro b
      refine ⟨b, ?_⟩
      intro n hn
      exact le_trans hn (le_trans (Nat.le_add_left n shift) (hidx_spec n).1)
    have hconv_idx :
        TendstoUniformlyOn
          (fun n : ℕ ↦ F ((S shift).1 (idx n))) g Filter.atTop (Kex m) := by
      intro U hU
      exact hidx_tendsto.eventually (hconv_step U hU)
    have hconv_tail :
        TendstoUniformlyOn
          (fun n : ℕ ↦ F (diag (n + shift))) g Filter.atTop (Kex m) := by
      refine hconv_idx.congr ?_
      filter_upwards with n x hx
      have hEq := (hidx_spec n).2
      have hEq' :
          (S shift).1 (idx n) = (S (n + shift)).1 (n + shift) := by
        simpa [shift, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hEq.symm
      exact congrArg (fun z : ℕ ↦ F z x) hEq'
    have hconv_diag :
        TendstoUniformlyOn
          (fun n : ℕ ↦ F (diag n)) g Filter.atTop (Kex m) := by
      intro U hU
      rcases Filter.eventually_atTop.mp (hconv_tail U hU) with ⟨N, hN⟩
      refine Filter.eventually_atTop.2 ⟨N + shift, ?_⟩
      intro n hn x hx
      have hn_shift : shift ≤ n := le_trans (Nat.le_add_left shift N) hn
      rcases Nat.exists_eq_add_of_le hn_shift with ⟨t, rfl⟩
      have hNt : N ≤ t := by
        have hn' : shift + N ≤ shift + t := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
        exact Nat.add_le_add_iff_left.mp hn'
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hN t hNt x hx
    exact ⟨g, hconv_diag⟩
  choose g hg using hlocal
  rcases tendstoUniformlyOn_compactExhaustion_glue
      Kex (F := fun n : ℕ ↦ F (diag n)) (g := g) hg with
    ⟨f, hf⟩
  exact ⟨diag, hdiag_strict, f, hf⟩

theorem realFunctions_subsequence_tendstoUniformlyOn_compactExhaustion_of_subsequence_extractions
    {X : Type} [TopologicalSpace X]
    (Kex : CompactExhaustion X)
    {F : ℕ → X → ℝ}
    (hextract :
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ m : ℕ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ f : X → ℝ,
            TendstoUniformlyOn
              (fun n : ℕ ↦ F (φ (ψ n))) f Filter.atTop (Kex m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℝ,
        ∀ m : ℕ,
          TendstoUniformlyOn (fun n : ℕ ↦ F (φ n)) f Filter.atTop (Kex m) :=
  functions_subsequence_tendstoUniformlyOn_compactExhaustion_of_subsequence_extractions
    Kex hextract

/-- A diagonal subsequence which converges uniformly on a compact exhaustion
converges locally uniformly on the ambient locally compact space. -/
theorem functions_subsequence_tendstoLocallyUniformly_of_compactExhaustion_subsequence_extractions
    {X Y : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [UniformSpace Y] [T2Space Y]
    (Kex : CompactExhaustion X)
    {F : ℕ → X → Y}
    (hextract :
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ m : ℕ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ f : X → Y,
            TendstoUniformlyOn
              (fun n : ℕ ↦ F (φ (ψ n))) f Filter.atTop (Kex m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → Y,
        TendstoLocallyUniformly
          (fun n : ℕ ↦ F (φ n)) f Filter.atTop := by
  rcases
    functions_subsequence_tendstoUniformlyOn_compactExhaustion_of_subsequence_extractions
      Kex hextract with
    ⟨φ, hφ, f, hf⟩
  refine ⟨φ, hφ, f, ?_⟩
  rw [← tendstoLocallyUniformlyOn_univ,
    tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _hKuniv hK
  exact tendstoUniformlyOn_of_compactExhaustion Kex hf K hK

/-- Local Arzelà--Ascoli hypotheses on a tail of every subsequence and every
compact exhaustion member produce one locally uniformly convergent
subsequence. -/
theorem functions_subsequence_tendstoLocallyUniformly_of_compactExhaustion_tail_equicontinuous
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [UniformSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (Kex : CompactExhaustion X)
    {F : ℕ → X → Y}
    (htail :
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ m : ℕ,
        ∃ N : ℕ,
          (∀ n : ℕ, ContinuousOn (F (φ (N + n))) (Kex m)) ∧
          (∀ x ∈ Kex m, ∃ Q : Set Y, IsCompact Q ∧
            ∀ n : ℕ, F (φ (N + n)) x ∈ Q) ∧
          EquicontinuousOn (fun n : ℕ ↦ F (φ (N + n))) (Kex m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → Y,
        TendstoLocallyUniformly
          (fun n : ℕ ↦ F (φ n)) f Filter.atTop := by
  apply
    functions_subsequence_tendstoLocallyUniformly_of_compactExhaustion_subsequence_extractions
      Kex
  intro φ hφ m
  rcases htail φ hφ m with ⟨N, hcont, hpointwise, heq⟩
  rcases functions_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      (Kex.isCompact m) hcont hpointwise heq with
    ⟨χ, hχ, f, hf⟩
  let ψ : ℕ → ℕ := fun n ↦ N + χ n
  refine ⟨ψ, ?_, f, ?_⟩
  · intro a b hab
    exact Nat.add_lt_add_left (hχ hab) N
  · simpa [ψ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf

/--
%%handwave
name:
  Coordinate disk
statement:
  A coordinate disk on a surface is the inverse image of an open Euclidean
  disk under a complex chart.
-/
structure CoordinateDisk (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The underlying open subset of the surface. -/
  carrier : Set X
  /-- The complex coordinate chart used to define the disk. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chart belongs to the surface atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The Euclidean center of the image disk. -/
  center : ℂ
  /-- The Euclidean radius of the image disk. -/
  radius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- The Euclidean disk lies in the chart target. -/
  ball_subset_target : Metric.ball center radius ⊆ chart.target
  /-- The surface disk is exactly the chart preimage of the Euclidean disk. -/
  carrier_eq : carrier = chart.source ∩ chart ⁻¹' Metric.ball center radius

namespace CoordinateDisk

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name:
  Coordinate disks are open
statement:
  Every coordinate disk is open in the surface.
proof:
  Its carrier is the intersection of the open chart source with the preimage
  of an open Euclidean disk under the chart.
-/
theorem isOpen (D : CoordinateDisk X) : IsOpen D.carrier := by
  rw [D.carrier_eq]
  exact D.chart.isOpen_inter_preimage Metric.isOpen_ball

/--
%%handwave
name:
  Coordinate disks are path connected
statement:
  Every coordinate disk on a surface is path connected.
proof:
  The inverse coordinate map identifies the disk with a Euclidean open ball,
  and Euclidean balls are path connected.
-/
theorem isPathConnected (D : CoordinateDisk X) :
    IsPathConnected D.carrier := by
  have himage :
      D.chart.symm '' Metric.ball D.center D.radius = D.carrier := by
    rw [D.chart.symm_image_eq_source_inter_preimage D.ball_subset_target]
    exact D.carrier_eq.symm
  rw [← himage]
  exact (Metric.isPathConnected_ball D.radius_pos).image'
    (D.chart.continuousOn_symm.mono D.ball_subset_target)

/--
%%handwave
name:
  Coordinate disks are second countable
statement:
  Every coordinate disk has a second-countable subspace topology.
proof:
  The defining chart identifies the coordinate disk with an open Euclidean
  disk in the complex plane, and open subsets of the complex plane are second
  countable.
-/
theorem secondCountable (D : CoordinateDisk X) :
    SecondCountableTopology D.carrier := by
  have hsubset : D.carrier ⊆ D.chart.source := by
    rw [D.carrier_eq]
    exact Set.inter_subset_left
  haveI : SecondCountableTopology D.chart.source :=
    D.chart.secondCountableTopology_source
  exact (Topology.IsEmbedding.inclusion hsubset).secondCountableTopology

end CoordinateDisk

/--
%%handwave
name:
  Internal tangent disks lie below exterior closed-ball points
statement:
  If a point \(z\) lies outside the closed disk \(\overline B(c,r)\), then
  its distance from the internal tangent disk center \(c+r/2\) is at least
  \(r/2\).
proof:
  This is the reverse triangle inequality:
  \[
    \|z-(c+r/2)\|\ge \|z-c\|-\|r/2\|\ge r-r/2.
  \]
-/
theorem complex_internalTangentDisk_distance_le_of_closedBall_exterior
    {z c : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : r ≤ ‖z - c‖) :
    r / 2 ≤ ‖z - (c + ((r / 2 : ℝ) : ℂ))‖ := by
  let a : ℂ := ((r / 2 : ℝ) : ℂ)
  have ha_norm : ‖a‖ = r / 2 := by
    exact Complex.norm_of_nonneg (by linarith)
  have hrev : ‖z - c‖ - ‖a‖ ≤ ‖(z - c) - a‖ :=
    norm_sub_norm_le (z - c) a
  have htarget :
      ‖(z - c) - a‖ = ‖z - (c + ((r / 2 : ℝ) : ℂ))‖ := by
    congr 1
    dsimp [a]
    ring
  rw [ha_norm, htarget] at hrev
  linarith

/--
%%handwave
name:
  Internal tangent disk touches an exterior closed ball at one point
statement:
  If a point \(z\) lies outside \(\overline B(c,r)\) and has distance exactly
  \(r/2\) from the internal tangent disk center \(c+r/2\), then
  \(z=c+r\).
proof:
  Translate to \(c=0\).  The two equations are
  \(|w|\ge r\) and \(|w-r/2|=r/2\).  Squaring the second equation gives
  \(w_x^2+w_y^2=r w_x\); combined with \(r^2\le w_x^2+w_y^2\) this implies
  \(w_x\ge r\).  The circle equation then forces
  \(w_x=r\) and \(w_y=0\).
-/
theorem complex_eq_positiveRealBoundary_of_closedBall_exterior_and_internalTangent
    {z c : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : r ≤ ‖z - c‖)
    (htangent : ‖z - (c + ((r / 2 : ℝ) : ℂ))‖ = r / 2) :
    z = c + (r : ℂ) := by
  let w : ℂ := z - c
  have hw_norm : r ≤ ‖w‖ := by
    simpa [w] using hz
  have htangent_w : ‖w - ((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
    simpa [w, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htangent
  have hnorm_sq_ge : r ^ 2 ≤ ‖w‖ ^ 2 := by
    exact (sq_le_sq₀ (le_of_lt hr) (norm_nonneg w)).2 hw_norm
  have hnorm_sq :
      ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  have hge : r ^ 2 ≤ w.re ^ 2 + w.im ^ 2 := by
    simpa [hnorm_sq] using hnorm_sq_ge
  have htangent_sq :
      ‖w - ((r / 2 : ℝ) : ℂ)‖ ^ 2 = (r / 2) ^ 2 := by
    rw [htangent_w]
  have hcircle : w.re ^ 2 + w.im ^ 2 = r * w.re := by
    rw [Complex.sq_norm] at htangent_sq
    simp [Complex.normSq_apply, pow_two] at htangent_sq
    nlinarith
  have hre_ge : r ≤ w.re := by
    nlinarith
  have hsum_zero : w.re * (w.re - r) + w.im ^ 2 = 0 := by
    nlinarith
  have hprod_nonneg : 0 ≤ w.re * (w.re - r) := by
    nlinarith
  have him_sq_nonneg : 0 ≤ w.im ^ 2 := sq_nonneg w.im
  have hprod_zero : w.re * (w.re - r) = 0 := by
    nlinarith
  have him_sq_zero : w.im ^ 2 = 0 := by
    nlinarith
  have him_zero : w.im = 0 := sq_eq_zero_iff.mp him_sq_zero
  have hre_eq : w.re = r := by
    rcases mul_eq_zero.mp hprod_zero with hre_zero | hsub_zero
    · nlinarith
    · linarith
  have hw_eq : w = (r : ℂ) := by
    apply Complex.ext
    · simp [hre_eq]
    · simp [him_zero]
  calc
    z = c + w := by
      dsimp [w]
      ring
    _ = c + (r : ℂ) := by rw [hw_eq]

/--
%%handwave
name:
  Relatively compact coordinate disk
statement:
  A relatively compact coordinate disk is a coordinate disk whose closure in
  the surface is compact.
-/
structure RelativelyCompactCoordinateDisk (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] extends CoordinateDisk X where
  /-- The closure of the disk is compact. -/
  closure_compact : IsCompact (closure carrier)

namespace RelativelyCompactCoordinateDisk

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name:
  Relatively compact coordinate disks are open
statement:
  Every relatively compact coordinate disk is open in the surface.
proof:
  [Every coordinate disk is open](lean:JJMath.Uniformization.CoordinateDisk.isOpen), and a relatively compact coordinate disk has the same carrier as its underlying coordinate disk.
-/
theorem isOpen (D : RelativelyCompactCoordinateDisk X) : IsOpen D.carrier := by
  simpa using CoordinateDisk.isOpen D.toCoordinateDisk

/--
%%handwave
name:
  Relatively compact coordinate disks are second countable
statement:
  Every relatively compact coordinate disk has a second-countable subspace
  topology.
proof:
  [Every coordinate disk is second countable](lean:JJMath.Uniformization.CoordinateDisk.secondCountable), and the underlying coordinate disk has the same carrier.
-/
theorem secondCountable (D : RelativelyCompactCoordinateDisk X) :
    SecondCountableTopology D.carrier := by
  simpa using CoordinateDisk.secondCountable D.toCoordinateDisk

/--
%%handwave
name:
  Relatively compact coordinate disks have compact frontier
statement:
  The frontier of a relatively compact coordinate disk is compact.
proof:
  The frontier is closed and is contained in the compact closure of the disk.
-/
theorem frontier_compact (D : RelativelyCompactCoordinateDisk X) :
    IsCompact (frontier D.carrier) := by
  exact D.closure_compact.of_isClosed_subset isClosed_frontier frontier_subset_closure

end RelativelyCompactCoordinateDisk

/--
%%handwave
name:
  Relatively compact coordinate disks inside open neighborhoods
statement:
  Every point of an open subset of a Riemann surface lies in a relatively
  compact coordinate disk whose closure is contained in that open subset.
proof:
  Apply the compactly contained coordinate Perron-disk construction inside the
  open subset, then forget the Perron-domain structure.
-/
theorem exists_relativelyCompactCoordinateDisk_subset_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} {N : Set X}
    (hxN : x ∈ N) (hN_open : IsOpen N) :
    ∃ D : RelativelyCompactCoordinateDisk X,
      x ∈ D.carrier ∧ closure D.carrier ⊆ N := by
  let Ω : PerronOpen X :=
    { carrier := N
      isOpen := hN_open
      nonempty := ⟨x, hxN⟩ }
  rcases exists_coordinate_perron_disk_compactly_contained_open
      (X := X) Ω hxN with
    ⟨V, hxV, hV_coord, hV_closure_subset, _hV_preconnected,
      _hV_frontier_nonempty⟩
  rcases hV_coord with ⟨e, he, c, r, hr, hclosed_target, hcarrier_eq⟩
  let D : RelativelyCompactCoordinateDisk X :=
    { carrier := V.carrier
      chart := e
      chart_mem_atlas := he
      center := c
      radius := r
      radius_pos := hr
      ball_subset_target := fun z hz ↦ hclosed_target (Metric.ball_subset_closedBall hz)
      carrier_eq := hcarrier_eq
      closure_compact := V.compact_closure }
  refine ⟨D, ?_, ?_⟩
  · exact hxV
  · simpa [D, Ω] using hV_closure_subset

/--
%%handwave
name:
  Countable coordinate-disk cover
statement:
  A countable coordinate-disk cover is a sequence of coordinate disks whose
  union is the whole surface.
-/
structure CountableCoordinateDiskCover (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The coordinate disks in the countable cover. -/
  disk : ℕ → CoordinateDisk X
  /-- The disks cover the surface. -/
  covers : (⋃ n : ℕ, (disk n).carrier) = Set.univ

/--
%%handwave
name:
  Countable open covers by second-countable pieces
statement:
  A countable open cover by second-countable subspaces makes the whole space
  second countable.
proof:
  Take the union of the images of countable bases for all the members of the
  cover.  This is a countable basis for the whole topology.
-/
theorem secondCountableTopology_of_countable_open_cover_explicit
    {X : Type} [TopologicalSpace X] {ι : Type} [Countable ι]
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ)
    (hsecond : ∀ i, SecondCountableTopology (U i)) :
    SecondCountableTopology X := by
  classical
  haveI : ∀ i, SecondCountableTopology (U i) := hsecond
  simpa using TopologicalSpace.secondCountableTopology_of_countable_cover
    (Uo := hopen) (hc := hcover)

namespace CountableCoordinateDiskCover

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name:
  Countable coordinate cover implies second countable
statement:
  A surface with a countable coordinate-disk cover is second countable.
proof:
  Each coordinate disk is second countable, and the disks form a countable
  open cover.
-/
theorem secondCountable (C : CountableCoordinateDiskCover X) :
    SecondCountableTopology X := by
  exact secondCountableTopology_of_countable_open_cover_explicit
    (fun n : ℕ ↦ (C.disk n).carrier)
    (fun n : ℕ ↦ (C.disk n).isOpen)
    C.covers
    (fun n : ℕ ↦ (C.disk n).secondCountable)

end CountableCoordinateDiskCover

/--
%%handwave
name:
  Second-countable open domain
statement:
  A second-countable open domain in a surface is a nonempty preconnected open
  subset with second-countable subspace topology.
-/
structure SecondCountableOpenDomain (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The underlying subset. -/
  carrier : Set X
  /-- The domain is open. -/
  isOpen : IsOpen carrier
  /-- The domain is nonempty. -/
  nonempty : carrier.Nonempty
  /-- The domain is preconnected. -/
  isPreconnected : IsPreconnected carrier
  /-- The subspace topology is second countable. -/
  secondCountable : SecondCountableTopology carrier

private def unionLeftPieceHomeomorph {X : Type} [TopologicalSpace X] (s t : Set X) :
    {y : (s ∪ t : Set X) // (y : X) ∈ s} ≃ₜ s where
  toFun y := ⟨y.1.1, y.2⟩
  invFun x := ⟨⟨x.1, Or.inl x.2⟩, x.2⟩
  left_inv y := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun x : s ↦ Or.inl x.2))
      (fun x : s ↦ x.2)

private def unionRightPieceHomeomorph {X : Type} [TopologicalSpace X] (s t : Set X) :
    {y : (s ∪ t : Set X) // (y : X) ∈ t} ≃ₜ t where
  toFun y := ⟨y.1.1, y.2⟩
  invFun x := ⟨⟨x.1, Or.inr x.2⟩, x.2⟩
  left_inv y := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun x : t ↦ Or.inr x.2))
      (fun x : t ↦ x.2)

private theorem secondCountableTopology_union {X : Type} [TopologicalSpace X]
    {s t : Set X} (hs : IsOpen s) (ht : IsOpen t)
    [SecondCountableTopology s] [SecondCountableTopology t] :
    SecondCountableTopology (s ∪ t : Set X) := by
  let U : Fin 2 → Set (s ∪ t : Set X) :=
    fun i ↦ if i = 0 then {y | (y : X) ∈ s} else {y | (y : X) ∈ t}
  have hopen : ∀ i, IsOpen (U i) := by
    intro i
    fin_cases i
    · dsimp [U]
      simpa using hs.preimage continuous_subtype_val
    · dsimp [U]
      simpa using ht.preimage continuous_subtype_val
  have hcover : (⋃ i, U i) = Set.univ := by
    ext y
    rcases y.2 with hy | hy <;> simp [U, hy]
  have hsecond : ∀ i, SecondCountableTopology (U i) := by
    intro i
    fin_cases i
    · simpa [U] using (unionLeftPieceHomeomorph s t).secondCountableTopology
    · simpa [U] using (unionRightPieceHomeomorph s t).secondCountableTopology
  exact secondCountableTopology_of_countable_open_cover_explicit U hopen hcover hsecond

/--
%%handwave
name:
  Union of meeting second-countable domains
statement:
  The union of two second-countable open domains with nonempty intersection is
  again a second-countable open domain.
proof:
  Openness and preconnectedness are preserved by a union along a common point.
  A finite open cover by the two original domains gives second countability of
  the union.
-/
def SecondCountableOpenDomain.unionOfInterNonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D E : SecondCountableOpenDomain X)
    (hDE : (D.carrier ∩ E.carrier).Nonempty) :
    SecondCountableOpenDomain X := by
  haveI : SecondCountableTopology D.carrier := D.secondCountable
  haveI : SecondCountableTopology E.carrier := E.secondCountable
  exact
    { carrier := D.carrier ∪ E.carrier
      isOpen := D.isOpen.union E.isOpen
      nonempty := D.nonempty.mono Set.subset_union_left
      isPreconnected := D.isPreconnected.union' hDE E.isPreconnected
      secondCountable := secondCountableTopology_union D.isOpen E.isOpen }

/--
%%handwave
name:
  Coordinate disk through a point
statement:
  Every point of a Riemann surface lies in a coordinate disk.
proof:
  Use the chart at the point and choose a Euclidean ball around the image of
  the point contained in the chart target.  The inverse image of that ball is
  a coordinate disk containing the original point.
-/
theorem exists_coordinateDisk_mem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    ∃ D : CoordinateDisk X, p ∈ D.carrier := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let z : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hz_target : z ∈ e.target := by
    simp [e, z, mem_chart_target ℂ p]
  rcases Metric.isOpen_iff.mp e.open_target z hz_target with ⟨r, hr_pos, hball_target⟩
  let C : CoordinateDisk X :=
    { carrier := e.source ∩ e ⁻¹' Metric.ball z r
      chart := e
      chart_mem_atlas := by
        simp [e, chart_mem_atlas ℂ p]
      center := z
      radius := r
      radius_pos := hr_pos
      ball_subset_target := hball_target
      carrier_eq := rfl }
  have hpC : p ∈ C.carrier := by
    have hp_ball : e p ∈ Metric.ball z r := by
      simpa [z] using (Metric.mem_ball_self hr_pos : z ∈ Metric.ball z r)
    exact ⟨hp_source, hp_ball⟩
  exact ⟨C, hpC⟩

/--
%%handwave
name:
  Local second-countable domain
statement:
  Every point of a Riemann surface lies in a second-countable open
  domain.
proof:
  Choose a complex coordinate chart around the point and take a sufficiently
  small coordinate disk.  Euclidean disks are connected and second countable,
  and the chart transports those properties to the surface.
-/
theorem exists_secondCountableOpenDomain_mem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    ∃ D : SecondCountableOpenDomain X, p ∈ D.carrier := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let z : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hz_target : z ∈ e.target := by
    simp [e, z, mem_chart_target ℂ p]
  rcases Metric.isOpen_iff.mp e.open_target z hz_target with ⟨r, hr_pos, hball_target⟩
  let C : CoordinateDisk X :=
    { carrier := e.source ∩ e ⁻¹' Metric.ball z r
      chart := e
      chart_mem_atlas := by
        simp [e, chart_mem_atlas ℂ p]
      center := z
      radius := r
      radius_pos := hr_pos
      ball_subset_target := hball_target
      carrier_eq := rfl }
  have hpC : p ∈ C.carrier := by
    have hp_ball : e p ∈ Metric.ball z r := by
      simpa [z] using (Metric.mem_ball_self hr_pos : z ∈ Metric.ball z r)
    exact ⟨hp_source, hp_ball⟩
  have hpre : IsPreconnected C.carrier := by
    have himage :
        e.symm '' Metric.ball z r = e.source ∩ e ⁻¹' Metric.ball z r :=
      e.symm_image_eq_source_inter_preimage hball_target
    have hpre_image : IsPreconnected (e.symm '' Metric.ball z r) :=
      Metric.isPreconnected_ball.image e.symm
        (e.continuousOn_symm.mono hball_target)
    simpa [C, himage] using hpre_image
  exact
    ⟨{ carrier := C.carrier
       isOpen := C.isOpen
       nonempty := ⟨p, hpC⟩
       isPreconnected := hpre
       secondCountable := C.secondCountable },
      hpC⟩

/--
%%handwave
name:
  Pullback sheets over a plane open set
statement:
  Given a map from a surface to the complex plane and an open set in the plane,
  the pullback sheets over that open set are the connected components of its
  inverse image.
-/
def pullbackSheetsOver
    {X : Type} [TopologicalSpace X] (f : X → ℂ) (U : Set ℂ) :
    Set (Set X) :=
  {S | ∃ x : X, x ∈ f ⁻¹' U ∧ S = connectedComponentIn (f ⁻¹' U) x}

/--
%%handwave
name:
  Pullback sheets over a countable plane basis
statement:
  The candidate basis on the surface is obtained by taking all pullback sheets
  over the members of a fixed countable basis of the complex plane.
-/
def holomorphicPullbackSheets
    {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    Set (Set X) :=
  ⋃ U ∈ TopologicalSpace.countableBasis ℂ, pullbackSheetsOver f U

/--
%%handwave
name:
  Good pullback sheets
statement:
  A good pullback sheet is a connected component of the inverse image of a
  member of the fixed countable basis of the complex plane, with the additional
  property that the sheet itself is second countable.
-/
def goodPullbackSheets
    {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    Set (Set X) :=
  {S | ∃ U ∈ TopologicalSpace.countableBasis ℂ,
    ∃ x : X, x ∈ f ⁻¹' U ∧
      S = connectedComponentIn (f ⁻¹' U) x ∧ SecondCountableTopology S}

/--
%%handwave
name:
  Good sheets are pullback sheets
statement:
  Every good pullback sheet is one of the pullback sheets over the countable
  plane basis.
proof:
  Unpack a good sheet as the connected component of \(f^{-1}(U)\) containing
  some \(x\), where \(U\) belongs to the fixed countable basis, and use this
  same \(U\) and \(x\) in the definition of a pullback sheet.
-/
theorem mem_holomorphicPullbackSheets_of_mem_goodPullbackSheets
    {X : Type} [TopologicalSpace X] {f : X → ℂ} {S : Set X}
    (hS : S ∈ goodPullbackSheets f) :
    S ∈ holomorphicPullbackSheets f := by
  rcases hS with ⟨U, hU_basis, x, hxU, rfl, _hsecond⟩
  exact Set.mem_iUnion.mpr
    ⟨U, Set.mem_iUnion.mpr ⟨hU_basis, ⟨x, hxU, rfl⟩⟩⟩

/--
%%handwave
name:
  Good sheets are open
statement:
  If the map to the complex plane is continuous, then every good pullback
  sheet is open.
proof:
  The target member of the countable plane basis is open.  Its inverse image is
  open, and connected components of open sets are open in locally connected
  spaces.
-/
theorem isOpen_of_mem_goodPullbackSheets
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {f : X → ℂ} (hf_cont : Continuous f) {S : Set X}
    (hS : S ∈ goodPullbackSheets f) :
    IsOpen S := by
  rcases hS with ⟨U, hU_basis, x, hxU, rfl, _hsecond⟩
  have hpre : IsOpen (f ⁻¹' U) :=
    (TopologicalSpace.isOpen_of_mem_countableBasis hU_basis).preimage hf_cont
  exact hpre.connectedComponentIn

/--
%%handwave
name:
  Good sheets are nonempty
statement:
  Every good pullback sheet is nonempty.
proof:
  If the sheet is the connected component of \(f^{-1}(U)\) containing
  \(x\in f^{-1}(U)\), then \(x\) itself belongs to that component.
-/
theorem nonempty_of_mem_goodPullbackSheets
    {X : Type} [TopologicalSpace X] {f : X → ℂ} {S : Set X}
    (hS : S ∈ goodPullbackSheets f) :
    S.Nonempty := by
  rcases hS with ⟨U, _hU_basis, x, hxU, rfl, _hsecond⟩
  exact ⟨x, mem_connectedComponentIn hxU⟩

/--
%%handwave
name:
  Pullback sheets are open
statement:
  If the map to the complex plane is continuous and the plane set is open, then
  every pullback sheet over that set is open.
proof:
  The inverse image of the plane open set is open.  In a locally connected
  space, connected components of open sets are open.
-/
theorem isOpen_of_mem_pullbackSheetsOver
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {f : X → ℂ} (hf_cont : Continuous f) {U : Set ℂ}
    (hU_open : IsOpen U) {S : Set X}
    (hS : S ∈ pullbackSheetsOver f U) :
    IsOpen S := by
  rcases hS with ⟨x, _hx, rfl⟩
  exact (hU_open.preimage hf_cont).connectedComponentIn

/--
%%handwave
name:
  Meeting pullback sheets over the same plane set are equal
statement:
  Two pullback sheets over the same plane set are either disjoint or equal.
proof:
  Pullback sheets are connected components of the same inverse image.  If two
  such components meet at a point, both are the connected component of that
  point.
-/
theorem eq_of_mem_pullbackSheetsOver_of_inter_nonempty
    {X : Type} [TopologicalSpace X] {f : X → ℂ} {U : Set ℂ}
    {S T : Set X}
    (hS : S ∈ pullbackSheetsOver f U)
    (hT : T ∈ pullbackSheetsOver f U)
    (hST : (S ∩ T).Nonempty) :
    S = T := by
  rcases hS with ⟨x, _hxU, rfl⟩
  rcases hT with ⟨y, _hyU, rfl⟩
  rcases hST with ⟨z, hzS, hzT⟩
  exact (connectedComponentIn_eq (F := f ⁻¹' U) (x := x) (y := z) hzS).trans
    (connectedComponentIn_eq (F := f ⁻¹' U) (x := y) (y := z) hzT).symm

/--
%%handwave
name:
  Countable sheets over a countable plane basis
statement:
  If each member of the countable plane basis has only countably many pullback
  sheets, then all pullback sheets over the countable plane basis form a
  countable family.
proof:
  This is a countable union of countable sets.
-/
theorem holomorphicPullbackSheets_countable_of_countable_sheetsOver
    {X : Type} [TopologicalSpace X] {f : X → ℂ}
    (hcount :
      ∀ U ∈ TopologicalSpace.countableBasis ℂ, (pullbackSheetsOver f U).Countable) :
    (holomorphicPullbackSheets f).Countable := by
  unfold holomorphicPullbackSheets
  exact (TopologicalSpace.countable_countableBasis ℂ).biUnion hcount

/--
%%handwave
name:
  Countable preimages from countable fibers
statement:
  If a subset of the target is countable and every fiber above that subset is
  countable, then its inverse image is countable.
proof:
  Regard the inverse image as mapping to the countable target subset.  The
  fibers of this restricted map inject into the original fibers.
-/
theorem preimage_countable_of_countable_fibers
    {X Y : Type} {f : X → Y} {A : Set Y}
    (hA_count : A.Countable)
    (hfibers : ∀ y ∈ A, (f ⁻¹' {y}).Countable) :
    (f ⁻¹' A).Countable := by
  classical
  haveI : Countable A := hA_count.to_subtype
  let g : f ⁻¹' A → A := fun x ↦ ⟨f x.1, x.2⟩
  have hg_fibers : ∀ y : A, (g ⁻¹' {y}).Countable := by
    intro y
    have hbase : (f ⁻¹' {y.1}).Countable := hfibers y.1 y.2
    haveI : Countable (f ⁻¹' {y.1}) := hbase.to_subtype
    let toBaseFiber : (g ⁻¹' {y}) → (f ⁻¹' {y.1}) :=
      fun x ↦
        ⟨x.1.1, by
          have hxg : g x.1 = y := by
            exact Set.mem_singleton_iff.mp x.2
          exact congrArg Subtype.val hxg⟩
    have hinj : Function.Injective toBaseFiber := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have hbaseeq :
          (toBaseFiber a).1 = (toBaseFiber b).1 :=
        congrArg (fun q : (f ⁻¹' {y.1}) ↦ q.1) hab
      simpa [toBaseFiber] using hbaseeq
    exact hinj.countable
  haveI : Countable (f ⁻¹' A) :=
    Set.Countable.of_preimage_singleton (f := g) hg_fibers
  exact (f ⁻¹' A).to_countable

/--
%%handwave
name:
  Countably many sheets from countable fibers and openness
statement:
  Let \(f : X \to \mathbb C\) be continuous and open, with countable fibers.
  If \(U\) is open in the plane, then the inverse image of \(U\) has only
  countably many connected components.
proof:
  Choose a countable dense subset \(D\) of the plane.  Each pullback sheet is
  open, so its image under the open map is a nonempty open subset of \(U\) and
  therefore meets \(D\).  Thus every sheet is represented by a point lying over
  \(D \cap U\).  The preimage of \(D \cap U\) is countable because the fibers
  are countable, and taking components through those points gives a countable
  surjection onto the set of sheets.
-/
theorem pullbackSheetsOver_countable_of_countable_fibers_of_openMap
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {f : X → ℂ} (hf_cont : Continuous f) (hf_open : IsOpenMap f)
    (hfibers : ∀ z : ℂ, (f ⁻¹' {z}).Countable)
    (D : Set ℂ) (hD_count : D.Countable) (hD_dense : Dense D)
    {U : Set ℂ} (hU_open : IsOpen U) :
    (pullbackSheetsOver f U).Countable := by
  classical
  let A : Set X := f ⁻¹' (D ∩ U)
  have hDU_count : (D ∩ U).Countable :=
    hD_count.mono Set.inter_subset_left
  have hA_count : A.Countable := by
    dsimp [A]
    exact preimage_countable_of_countable_fibers (f := f) (A := D ∩ U) hDU_count
      (fun z _hz ↦ hfibers z)
  have hsubset :
      pullbackSheetsOver f U ⊆
        (fun x : X ↦ connectedComponentIn (f ⁻¹' U) x) '' A := by
    intro S hS
    rcases hS with ⟨x, hxU, rfl⟩
    let C : Set X := connectedComponentIn (f ⁻¹' U) x
    have hxC : x ∈ C := mem_connectedComponentIn hxU
    have hC_open : IsOpen C := by
      dsimp [C]
      exact (hU_open.preimage hf_cont).connectedComponentIn
    have himage_open : IsOpen (f '' C) := hf_open C hC_open
    have himage_nonempty : (f '' C).Nonempty :=
      ⟨f x, ⟨x, hxC, rfl⟩⟩
    rcases hD_dense.inter_open_nonempty (f '' C) himage_open
        himage_nonempty with
      ⟨w, ⟨hw_image, hwD⟩⟩
    rcases hw_image with ⟨z, hzC, hfz⟩
    have hzU : f z ∈ U :=
      connectedComponentIn_subset (f ⁻¹' U) x hzC
    have hzA : z ∈ A := by
      dsimp [A]
      exact ⟨by simpa [hfz] using hwD, hzU⟩
    refine ⟨z, hzA, ?_⟩
    exact (connectedComponentIn_eq (F := f ⁻¹' U) (x := x) (y := z) hzC).symm
  exact (hA_count.image
    (fun x : X ↦ connectedComponentIn (f ⁻¹' U) x)).mono hsubset

/--
%%handwave
name:
  Pullback sheets form a basis from local refinement
statement:
  Suppose every point and every surface neighborhood admit a smaller pullback
  sheet over a member of the countable plane basis.  Then all pullback sheets
  over that plane basis form a basis for the surface topology.
proof:
  Use the open-set basis of the surface and refine each open neighborhood by
  the assumed pullback sheet.  Openness of the sheets follows from continuity
  and local connectedness.
-/
theorem holomorphicPullbackSheets_isTopologicalBasis_of_local_refinement
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {f : X → ℂ} (hf_cont : Continuous f)
    (hrefine :
      ∀ x : X, ∀ N : Set X, x ∈ N → IsOpen N →
        ∃ U ∈ TopologicalSpace.countableBasis ℂ,
          f x ∈ U ∧ connectedComponentIn (f ⁻¹' U) x ⊆ N) :
    TopologicalSpace.IsTopologicalBasis (holomorphicPullbackSheets f) := by
  refine TopologicalSpace.isTopologicalBasis_opens
    |>.isTopologicalBasis_of_exists_subset ?_ ?_
  · intro S hS
    rcases Set.mem_iUnion.mp hS with ⟨U, hSU⟩
    rcases Set.mem_iUnion.mp hSU with ⟨hU_basis, hSover⟩
    exact isOpen_of_mem_pullbackSheetsOver hf_cont
      (TopologicalSpace.isOpen_of_mem_countableBasis hU_basis) hSover
  · intro N hN x hxN
    rcases hrefine x N hxN hN with
      ⟨U, hU_basis, hxU, hcomponent_subset⟩
    refine
      ⟨connectedComponentIn (f ⁻¹' U) x, ?_,
        mem_connectedComponentIn hxU, hcomponent_subset⟩
    exact Set.mem_iUnion.mpr
      ⟨U, Set.mem_iUnion.mpr ⟨hU_basis, ⟨x, hxU, rfl⟩⟩⟩

/--
%%handwave
name:
  Good sheets form a basis from local refinement
statement:
  Suppose every point and every surface neighborhood admit a smaller good
  pullback sheet.  Then the good pullback sheets form a basis for the surface
  topology.
proof:
  The proof is the usual basis-refinement criterion: good sheets are open, and
  by hypothesis they refine arbitrary open neighborhoods.
-/
theorem goodPullbackSheets_isTopologicalBasis_of_local_refinement
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {f : X → ℂ} (hf_cont : Continuous f)
    (hrefine :
      ∀ x : X, ∀ N : Set X, x ∈ N → IsOpen N →
        ∃ S ∈ goodPullbackSheets f, x ∈ S ∧ S ⊆ N) :
    TopologicalSpace.IsTopologicalBasis (goodPullbackSheets f) := by
  refine TopologicalSpace.isTopologicalBasis_opens
    |>.isTopologicalBasis_of_exists_subset ?_ ?_
  · intro S hS
    exact isOpen_of_mem_goodPullbackSheets hf_cont hS
  · intro N hN x hxN
    exact hrefine x N hxN hN

/--
%%handwave
name:
  Sheets meeting a fixed sheet
statement:
  For a family of surface sheets and a fixed sheet \(S\), the sheets meeting
  \(S\) are exactly the members with nonempty intersection with \(S\).
-/
def sheetsMeeting
    {X : Type} (B : Set (Set X)) (S : Set X) :
    Set (Set X) :=
  {T | T ∈ B ∧ (S ∩ T).Nonempty}

/--
%%handwave
name:
  Countably many open sets with disjoint traces on a second-countable set
statement:
  Let \(S\) be second countable.  If a family of open subsets has nonempty
  traces on \(S\), and distinct members have disjoint traces on \(S\), then the
  family is countable.
proof:
  For each member choose a countable-basis element of \(S\) contained in its
  trace.  Distinct members must choose distinct basis elements, because a
  common chosen basis element would give a point in both traces.
-/
theorem countable_of_pairwiseDisjoint_open_intersections
    {X : Type} [TopologicalSpace X] {S : Set X}
    [SecondCountableTopology S] {A : Set (Set X)}
    (hopen : ∀ T ∈ A, IsOpen T)
    (hnonempty : ∀ T ∈ A, (S ∩ T).Nonempty)
    (hdisj : ∀ T ∈ A, ∀ V ∈ A, T ≠ V →
      Disjoint (Subtype.val ⁻¹' T : Set S) (Subtype.val ⁻¹' V)) :
    A.Countable := by
  classical
  have hex :
      ∀ T : A, ∃ b ∈ TopologicalSpace.countableBasis S,
        b.Nonempty ∧ b ⊆ (Subtype.val ⁻¹' (T : Set X) : Set S) := by
    intro T
    rcases hnonempty (T : Set X) T.2 with ⟨x, hxS, hxT⟩
    let xS : S := ⟨x, hxS⟩
    have hxpre : xS ∈ (Subtype.val ⁻¹' (T : Set X) : Set S) := hxT
    have hopen_sub : IsOpen (Subtype.val ⁻¹' (T : Set X) : Set S) :=
      (hopen (T : Set X) T.2).preimage continuous_subtype_val
    rcases (TopologicalSpace.isBasis_countableBasis S).exists_subset_of_mem_open
        hxpre hopen_sub with
      ⟨b, hb_basis, hxb, hb_subset⟩
    exact ⟨b, hb_basis, ⟨xS, hxb⟩, hb_subset⟩
  choose b hb_basis hb_nonempty hb_subset using hex
  let toBasis : A → TopologicalSpace.countableBasis S :=
    fun T ↦ ⟨b T, hb_basis T⟩
  have htoBasis_inj : Function.Injective toBasis := by
    intro T V hTV
    apply Subtype.ext
    by_contra hne
    have hb_eq : b T = b V := congrArg Subtype.val hTV
    rcases hb_nonempty T with ⟨x, hxbT⟩
    have hxT : x ∈ (Subtype.val ⁻¹' (T : Set X) : Set S) :=
      hb_subset T hxbT
    have hxV : x ∈ (Subtype.val ⁻¹' (V : Set X) : Set S) := by
      apply hb_subset V
      simpa [hb_eq] using hxbT
    exact Set.disjoint_left.mp
      (hdisj (T : Set X) T.2 (V : Set X) V.2 hne) hxT hxV
  haveI : Countable A := htoBasis_inj.countable
  exact A.to_countable

/--
%%handwave
name:
  Countably many pullback sheets over one plane set meet a second-countable sheet
statement:
  Fix a second-countable surface subset \(S\).  Over one plane open set, only
  countably many pullback sheets can meet \(S\).
proof:
  Pullback sheets over the same plane open set are pairwise disjoint unless
  equal.  Their traces on \(S\) are therefore pairwise disjoint nonempty open
  subsets of the second-countable space \(S\), so there are only countably many.
-/
theorem pullbackSheetsOver_meeting_secondCountable_countable
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {f : X → ℂ} (hf_cont : Continuous f) {S : Set X}
    [SecondCountableTopology S] {U : Set ℂ} (hU_open : IsOpen U) :
    {T : Set X | T ∈ pullbackSheetsOver f U ∧ (S ∩ T).Nonempty}.Countable := by
  refine countable_of_pairwiseDisjoint_open_intersections
    (S := S)
    (A := {T : Set X | T ∈ pullbackSheetsOver f U ∧ (S ∩ T).Nonempty})
    ?_ ?_ ?_
  · intro T hT
    exact isOpen_of_mem_pullbackSheetsOver hf_cont hU_open hT.1
  · intro T hT
    exact hT.2
  · intro T hT V hV hne
    rw [Set.disjoint_left]
    intro x hxT hxV
    exact hne
      (eq_of_mem_pullbackSheetsOver_of_inter_nonempty hT.1 hV.1
        ⟨x.1, hxT, hxV⟩)

private def sheetAdjacencyReach
    {X : Type} (B : Set (Set X)) (S0 : Set X) :
    ℕ → Set (Set X)
  | 0 => {S0}
  | n + 1 => ⋃ S ∈ sheetAdjacencyReach B S0 n, sheetsMeeting B S

/--
%%handwave
name:
  Countable basis from countable sheet adjacency
statement:
  Let \(B\) be a basis of nonempty open sets on a connected space.  If every
  basis element meets only countably many basis elements, then \(B\) is
  countable.
proof:
  Choose one basis element and close it under the adjacency relation
  "\(S\) meets \(T\)".  Since every vertex has countably many neighbors, the
  finite-stage closure is a countable union of countable sets, and the union
  of all finite stages is countable.  The union of the reached basis elements
  is open.  Its complement is also open: any basis element containing a point
  outside the union is disjoint from every reached element, otherwise it would
  be reached at the next stage.  Connectedness forces this reached union to be
  all of the space, so every basis element is reached.
-/
theorem countable_basis_of_countable_sheet_adjacency
    {X : Type} [TopologicalSpace X] [ConnectedSpace X]
    {B : Set (Set X)}
    (hB_basis : TopologicalSpace.IsTopologicalBasis B)
    (hB_nonempty : B.Nonempty)
    (hB_sets_nonempty : ∀ S ∈ B, S.Nonempty)
    (hmeet_count : ∀ S ∈ B, (sheetsMeeting B S).Countable) :
    B.Countable := by
  classical
  let S0 : Set X := Classical.choose hB_nonempty
  have hS0B : S0 ∈ B := Classical.choose_spec hB_nonempty
  let reach : ℕ → Set (Set X) := sheetAdjacencyReach B S0
  let R : Set (Set X) := ⋃ n : ℕ, reach n
  have hreach_subset_B : ∀ n : ℕ, reach n ⊆ B := by
    intro n
    induction n with
    | zero =>
        intro S hS
        have hS_eq : S = S0 := by
          simpa [reach, sheetAdjacencyReach] using hS
        simpa [hS_eq] using hS0B
    | succ n hn =>
        intro T hT
        rcases (by simpa [reach, sheetAdjacencyReach] using hT :
            ∃ S ∈ reach n, T ∈ sheetsMeeting B S) with
          ⟨S, _hS_reach, hT_meets⟩
        exact hT_meets.1
  have hR_subset_B : R ⊆ B := by
    intro S hS
    rcases Set.mem_iUnion.mp hS with ⟨n, hSn⟩
    exact hreach_subset_B n hSn
  have hreach_count : ∀ n : ℕ, (reach n).Countable := by
    intro n
    induction n with
    | zero =>
        simp [reach, sheetAdjacencyReach]
    | succ n hn =>
        simpa [reach, sheetAdjacencyReach] using
          hn.biUnion (fun S hS ↦ hmeet_count S (hreach_subset_B n hS))
  have hR_count : R.Countable := by
    simpa [R] using Set.countable_iUnion hreach_count
  let U : Set X := ⋃ S ∈ R, S
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_biUnion fun S hS ↦ hB_basis.isOpen (hR_subset_B hS)
  have hS0R : S0 ∈ R := by
    exact Set.mem_iUnion.mpr ⟨0, by simp [reach, sheetAdjacencyReach]⟩
  have hU_nonempty : U.Nonempty := by
    rcases hB_sets_nonempty S0 hS0B with ⟨x, hxS0⟩
    exact ⟨x, Set.mem_iUnion.mpr
      ⟨S0, Set.mem_iUnion.mpr ⟨hS0R, hxS0⟩⟩⟩
  have hU_compl_open : IsOpen Uᶜ := by
    rw [hB_basis.isOpen_iff]
    intro x hxUcompl
    rcases hB_basis.exists_subset_of_mem_open
        (show x ∈ (Set.univ : Set X) by simp) isOpen_univ with
      ⟨T, hT_B, hxT, _hT_subset_univ⟩
    refine ⟨T, hT_B, hxT, ?_⟩
    intro y hyT hyU
    rcases Set.mem_iUnion.mp hyU with ⟨S, hyU'⟩
    rcases Set.mem_iUnion.mp hyU' with ⟨hS_R, hyS⟩
    rcases Set.mem_iUnion.mp hS_R with ⟨n, hS_reach⟩
    have hT_meets : T ∈ sheetsMeeting B S := by
      exact ⟨hT_B, ⟨y, hyS, hyT⟩⟩
    have hT_reach : T ∈ reach (n + 1) := by
      simpa [reach, sheetAdjacencyReach] using
        (show ∃ S ∈ reach n, T ∈ sheetsMeeting B S from
          ⟨S, hS_reach, hT_meets⟩)
    have hT_R : T ∈ R := Set.mem_iUnion.mpr ⟨n + 1, hT_reach⟩
    have hxU : x ∈ U := Set.mem_iUnion.mpr
      ⟨T, Set.mem_iUnion.mpr ⟨hT_R, hxT⟩⟩
    exact hxUcompl hxU
  have hU_clopen : IsClopen U := ⟨isOpen_compl_iff.mp hU_compl_open, hU_open⟩
  have hU_univ : U = Set.univ := hU_clopen.eq_univ hU_nonempty
  have hB_subset_R : B ⊆ R := by
    intro T hT_B
    rcases hB_sets_nonempty T hT_B with ⟨x, hxT⟩
    have hxU : x ∈ U := by
      rw [hU_univ]
      exact Set.mem_univ x
    rcases Set.mem_iUnion.mp hxU with ⟨S, hxU'⟩
    rcases Set.mem_iUnion.mp hxU' with ⟨hS_R, hxS⟩
    rcases Set.mem_iUnion.mp hS_R with ⟨n, hS_reach⟩
    have hT_meets : T ∈ sheetsMeeting B S := by
      exact ⟨hT_B, ⟨x, hxS, hxT⟩⟩
    have hT_reach : T ∈ reach (n + 1) := by
      simpa [reach, sheetAdjacencyReach] using
        (show ∃ S ∈ reach n, T ∈ sheetsMeeting B S from
          ⟨S, hS_reach, hT_meets⟩)
    exact Set.mem_iUnion.mpr ⟨n + 1, hT_reach⟩
  exact hR_count.mono hB_subset_R

/--
%%handwave
name:
  A good sheet meets countably many good sheets
statement:
  A fixed good pullback sheet meets only countably many good pullback sheets.
proof:
  Fix the good sheet \(S\).  For a fixed plane basis element \(U\), distinct
  components of \(f^{-1}(U)\) are disjoint.  The components that meet \(S\)
  therefore give pairwise disjoint nonempty open subsets of the second-countable
  space \(S\).  A second-countable space has only countably many pairwise
  disjoint nonempty open subsets.  Finally take the countable union over the
  countable plane basis.
-/
theorem goodPullbackSheet_meets_countably_many
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {f : X → ℂ} (hf_cont : Continuous f)
    {S : Set X} (hS : S ∈ goodPullbackSheets f) :
    (sheetsMeeting (goodPullbackSheets f) S).Countable := by
  classical
  rcases hS with ⟨_US, _hUS_basis, _xS, _hxS, _hS_eq, hS_second⟩
  haveI : SecondCountableTopology S := hS_second
  let sheetsOverMeetingS : Set ℂ → Set (Set X) :=
    fun U ↦ {T : Set X | T ∈ pullbackSheetsOver f U ∧ (S ∩ T).Nonempty}
  have hcover :
      sheetsMeeting (goodPullbackSheets f) S ⊆
        ⋃ U ∈ TopologicalSpace.countableBasis ℂ, sheetsOverMeetingS U := by
    intro T hT
    rcases hT.1 with ⟨U, hU_basis, x, hxU, hT_eq, _hT_second⟩
    exact Set.mem_iUnion.mpr
      ⟨U, Set.mem_iUnion.mpr
        ⟨hU_basis, ⟨⟨x, hxU, hT_eq⟩, hT.2⟩⟩⟩
  have hcount :
      (⋃ U ∈ TopologicalSpace.countableBasis ℂ, sheetsOverMeetingS U).Countable :=
    (TopologicalSpace.countable_countableBasis ℂ).biUnion
      (fun U hU_basis ↦
        pullbackSheetsOver_meeting_secondCountable_countable
          (f := f) hf_cont (S := S)
          (TopologicalSpace.isOpen_of_mem_countableBasis hU_basis))
  exact hcount.mono hcover

/--
%%handwave
name:
  Good pullback sheets are countable from local refinement
statement:
  If good pullback sheets form a basis on a connected surface, then there are
  only countably many of them.
proof:
  Apply the countable-adjacency theorem.  A basis on a nonempty connected
  space has at least one member, each good sheet is nonempty, and a fixed good
  sheet meets only countably many good sheets.
-/
theorem goodPullbackSheets_countable_of_basis
    {X : Type} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {f : X → ℂ} (hf_cont : Continuous f)
    (hbasis : TopologicalSpace.IsTopologicalBasis (goodPullbackSheets f)) :
    (goodPullbackSheets f).Countable := by
  classical
  have hB_nonempty : (goodPullbackSheets f).Nonempty := by
    let x : X := Classical.choice (inferInstance : Nonempty X)
    rcases hbasis.exists_subset_of_mem_open (show x ∈ (Set.univ : Set X) by simp)
        isOpen_univ with
      ⟨S, hS, _hxS, _hS_subset⟩
    exact ⟨S, hS⟩
  exact
    countable_basis_of_countable_sheet_adjacency
      (B := goodPullbackSheets f) hbasis hB_nonempty
      (fun S hS ↦ nonempty_of_mem_goodPullbackSheets hS)
      (fun S hS ↦ goodPullbackSheet_meets_countably_many hf_cont hS)

/--
%%handwave
name:
  Subsets of second-countable subspaces are second countable
statement:
  If \(A\subset B\) and \(B\) is second countable in the subspace topology, then
  \(A\) is second countable.
proof:
  The inclusion \(A\hookrightarrow B\) is an embedding, and second countability
  pulls back along embeddings.
-/
theorem secondCountableTopology_of_subset_secondCountable
    {X : Type} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) [SecondCountableTopology B] :
    SecondCountableTopology A :=
  (Topology.IsEmbedding.inclusion hAB).secondCountableTopology

/--
%%handwave
name:
  Boundary avoidance traps a connected component
statement:
  Let \(F\) be a subset of a topological space and \(W\) an open set.  If
  \(x\in F\cap W\) and \(F\) is disjoint from the frontier of \(W\), then the
  connected component of \(x\) in \(F\) is contained in \(W\).
proof:
  The component is preconnected.  Inside the component, the two open sets
  \(W\) and \(\overline W^{\,c}\) cover everything: a point of \(F\) outside
  \(W\) and still in \(\overline W\) would lie on the frontier of \(W\), which
  is excluded.  Since the component meets \(W\) at \(x\), preconnectedness
  forces it to lie entirely in \(W\).
-/
theorem connectedComponentIn_subset_of_isOpen_of_disjoint_frontier
    {X : Type} [TopologicalSpace X] {F W : Set X} {x : X}
    (hW_open : IsOpen W) (hxF : x ∈ F) (hxW : x ∈ W)
    (hdisj : Disjoint (frontier W) F) :
    connectedComponentIn F x ⊆ W := by
  let C : Set X := connectedComponentIn F x
  have hC_pre : IsPreconnected C := by
    simpa [C] using (isPreconnected_connectedComponentIn (x := x) (F := F))
  have hC_subset_F : C ⊆ F := by
    simpa [C] using (connectedComponentIn_subset F x)
  have hC_subset_union : C ⊆ W ∪ (closure W)ᶜ := by
    intro y hyC
    by_cases hyW : y ∈ W
    · exact Or.inl hyW
    · right
      intro hy_closure
      have hy_frontier : y ∈ frontier W := by
        rw [frontier, hW_open.interior_eq]
        exact ⟨hy_closure, hyW⟩
      exact Set.disjoint_left.mp hdisj hy_frontier (hC_subset_F hyC)
  have hC_meets_W : (C ∩ W).Nonempty :=
    ⟨x, by
      exact ⟨by simpa [C] using mem_connectedComponentIn hxF, hxW⟩⟩
  exact hC_pre.subset_left_of_subset_union hW_open isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left subset_closure)
    hC_subset_union hC_meets_W

/--
%%handwave
name:
  A countable plane basis element avoids a closed set
statement:
  If a point of the complex plane is outside a closed set \(K\), then some
  member of the fixed countable plane basis contains the point and is disjoint
  from \(K\).
proof:
  Apply the basis-refinement property to the open complement of \(K\).
-/
theorem exists_countableBasis_complex_subset_compl_of_isClosed
    {K : Set ℂ} {z : ℂ} (hK_closed : IsClosed K) (hzK : z ∉ K) :
    ∃ U ∈ TopologicalSpace.countableBasis ℂ, z ∈ U ∧ U ⊆ Kᶜ := by
  exact (TopologicalSpace.isBasis_countableBasis ℂ).exists_subset_of_mem_open
    (show z ∈ Kᶜ by exact hzK) hK_closed.isOpen_compl

/--
%%handwave
name:
  A plane basis element can avoid the image of a compact frontier
statement:
  Let \(W\) be a set with compact frontier and let \(f\) be continuous.  If
  \(f(x)\) is not in the image of the frontier of \(W\), then some member
  \(U\) of the fixed countable plane basis contains \(f(x)\) and
  \(f^{-1}(U)\) is disjoint from the frontier of \(W\).
proof:
  The image of the compact frontier is compact, hence closed in the complex
  plane.  Choose a countable-basis element contained in its complement.
-/
theorem exists_countableBasis_disjoint_frontier_preimage
    {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf_cont : Continuous f)
    {W : Set X} (hfrontier_compact : IsCompact (frontier W)) {x : X}
    (hx_not_image : f x ∉ f '' frontier W) :
    ∃ U ∈ TopologicalSpace.countableBasis ℂ,
      f x ∈ U ∧ Disjoint (frontier W) (f ⁻¹' U) := by
  have himage_closed : IsClosed (f '' frontier W) :=
    (hfrontier_compact.image hf_cont).isClosed
  rcases exists_countableBasis_complex_subset_compl_of_isClosed
      himage_closed hx_not_image with
    ⟨U, hU_basis, hxU, hU_subset⟩
  refine ⟨U, hU_basis, hxU, ?_⟩
  rw [Set.disjoint_left]
  intro y hy_frontier hy_pre
  exact hU_subset hy_pre ⟨y, hy_frontier, rfl⟩

/--
%%handwave
name:
  Plane analytic maps have isolated fibers unless locally constant
statement:
  If a complex analytic function is not locally equal to its value at \(z_0\),
  then \(z_0\) has a neighborhood in which no other point maps to that same
  value.
proof:
  Apply Mathlib's isolated-zero theorem to \(g-g(z_0)\).  The alternative
  that \(g=g(z_0)\) on a neighborhood is excluded by hypothesis, so
  \(g(z)\ne g(z_0)\) eventually on the punctured neighborhood of \(z_0\).
  Unpack the punctured-neighborhood filter to an ordinary open neighborhood.
-/
theorem analyticAt_exists_isolatedFiber_neighborhood
    {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀)
    (hnot : ¬ ∀ᶠ z in 𝓝 z₀, g z = g z₀) :
    ∃ P : Set ℂ, IsOpen P ∧ z₀ ∈ P ∧
      ∀ z ∈ P, z ≠ z₀ → g z ≠ g z₀ := by
  have hconst : AnalyticAt ℂ (fun _ : ℂ ↦ g z₀) z₀ := analyticAt_const
  rcases hg.eventually_eq_or_eventually_ne hconst with hEq | hNe
  · exact False.elim (hnot (hEq.mono fun z hz ↦ by simpa using hz))
  · have hNeSet : {z : ℂ | g z ≠ g z₀} ∈ 𝓝[≠] z₀ := by
      simpa using hNe
    rw [nhdsWithin, Filter.mem_inf_principal] at hNeSet
    rcases mem_nhds_iff.mp hNeSet with ⟨P, hP_subset, hP_open, hzP⟩
    refine ⟨P, hP_open, hzP, ?_⟩
    intro z hzP' hz_ne
    exact hP_subset hzP'
      (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz_ne)

/--
%%handwave
name:
  Coordinate expressions of holomorphic surface maps are analytic
statement:
  A holomorphic complex-valued map on a Riemann surface becomes analytic after
  composing with the inverse of any surface chart.
proof:
  The inverse chart is complex-manifold differentiable on its target.  Compose
  it with the holomorphic surface map, translate manifold differentiability
  between open subsets of \(\mathbb C\) into ordinary complex
  differentiability, and hence obtain analyticity at the chosen coordinate.
-/
theorem surface_coordinateExpression_analyticAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X)
    {x : X} (hx_source : x ∈ e.source) :
    AnalyticAt ℂ (fun z : ℂ ↦ f (e.symm z)) (e x) := by
  have hsymm : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target :=
    mdifferentiableOn_atlas_symm (I := 𝓘(ℂ)) he
  have hcomp : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ e.symm) e.target :=
    hf.comp_mdifferentiableOn hsymm
  have hdiff : DifferentiableOn ℂ (fun z : ℂ ↦ f (e.symm z)) e.target := by
    intro z hz
    have hz' := hcomp z hz
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at hz'
    exact hz'
  exact (hdiff.analyticOnNhd e.open_target) (e x) (e.map_source hx_source)

/--
%%handwave
name:
  Holomorphic surface maps satisfy the local isolated-zero dichotomy
statement:
  For a holomorphic complex-valued map on a Riemann surface and a value
  \(a\), at each point either \(f\) is locally equal to \(a\), or \(f\ne a\)
  eventually on the punctured neighborhood of that point.
proof:
  Express \(f\) in a local coordinate and apply Mathlib's analytic
  isolated-zero dichotomy to the coordinate expression and the constant
  function \(a\).  The chart identifies ordinary and punctured neighborhoods
  with their coordinate counterparts.
-/
theorem holomorphicMap_eventually_eq_or_eventually_ne_value
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (a : ℂ) (y : X) :
    (∀ᶠ z in 𝓝 y, f z = a) ∨
      (∀ᶠ z in 𝓝[≠] y, f z ≠ a) := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ y
  let z₀ : ℂ := e y
  have hy_source : y ∈ e.source := mem_chart_source ℂ y
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ y
  have hg_an : AnalyticAt ℂ (fun z : ℂ ↦ f (e.symm z)) z₀ := by
    simpa [z₀] using
      surface_coordinateExpression_analyticAt (X := X) (f := f) hf he hy_source
  have hconst : AnalyticAt ℂ (fun _ : ℂ ↦ a) z₀ := analyticAt_const
  rcases hg_an.eventually_eq_or_eventually_ne hconst with hEq | hNe
  · left
    exact (e.eventually_nhds' (fun w : X ↦ f w = a) hy_source).1
      (by simpa using hEq)
  · right
    have hNe_pre :
        ∀ᶠ w in 𝓝[(e ⁻¹' ({z₀} : Set ℂ))ᶜ] y, f w ≠ a := by
      rw [← e.map_nhdsWithin_preimage_eq hy_source ({z₀}ᶜ : Set ℂ),
        Filter.eventually_map] at hNe
      have hsource_within :
          ∀ᶠ w in 𝓝[e ⁻¹' ({z₀}ᶜ : Set ℂ)] y, w ∈ e.source :=
        eventually_nhdsWithin_of_eventually_nhds
          (e.open_source.mem_nhds hy_source)
      filter_upwards [hNe, hsource_within] with w hwne hwsource
      simpa [Set.preimage_compl, e.left_inv hwsource] using hwne
    have hwithin_eq :
        𝓝[(e ⁻¹' ({z₀} : Set ℂ))ᶜ] y = 𝓝[≠] y := by
      rw [nhdsWithin_eq_iff_eventuallyEq]
      filter_upwards [e.open_source.mem_nhds hy_source] with w hwsource
      apply propext
      constructor
      · intro hwpre hwy
        apply hwpre
        have hwy_eq : w = y := by
          simpa using hwy
        simp [z₀, hwy_eq]
      · intro hwne heq
        apply hwne
        calc
          w = e.symm (e w) := (e.left_inv hwsource).symm
          _ = e.symm z₀ := by rw [heq]
          _ = y := by simp [z₀, e.left_inv hy_source]
    rw [← hwithin_eq]
    exact hNe_pre

/--
%%handwave
name:
  Local equality set is closed for holomorphic surface maps
statement:
  Let \(f\) be a holomorphic complex-valued function on a connected Riemann
  surface.  If a point lies in the closure of the set of points near which
  \(f\) is locally equal to a fixed value \(a\), then \(f\) is locally equal
  to \(a\) near that point.
proof:
  Choose a coordinate disk around the closure point.  Points from the local
  equality set accumulate in this coordinate disk, so the coordinate
  expression of \(f\) agrees with the constant function \(a\) on a set with an
  accumulation point.  The complex analytic identity theorem then gives
  equality on a smaller coordinate neighborhood.
-/
theorem holomorphicMap_eventually_eq_value_of_mem_closure_eventually_eq_value
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {a : ℂ} {y : X}
    (hy : y ∈ closure {p : X | ∀ᶠ z in 𝓝 p, f z = a}) :
    ∀ᶠ z in 𝓝 y, f z = a := by
  let A : Set X := {p : X | ∀ᶠ z in 𝓝 p, f z = a}
  by_cases hyA : y ∈ A
  · exact hyA
  have hy_diff : y ∈ closure (A \ {y}) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    rcases mem_closure_iff_nhds.mp (by simpa [A] using hy) U hU with
      ⟨p, hpU, hpA⟩
    refine ⟨p, hpU, hpA, ?_⟩
    intro hpy
    exact hyA (hpy ▸ hpA)
  have hfreqA : ∃ᶠ p in 𝓝[≠] y, p ∈ A :=
    mem_closure_ne_iff_frequently_within.mp hy_diff
  rcases holomorphicMap_eventually_eq_or_eventually_ne_value
      (f := f) hf a y with hEq | hNe
  · exact hEq
  · exfalso
    have hA_value : ∀ p : X, p ∈ A → f p = a := by
      intro p hpA
      rcases mem_nhds_iff.mp hpA with ⟨U, hU_subset, _hU_open, hpU⟩
      exact hU_subset hpU
    have hfreq_eq : ∃ᶠ p in 𝓝[≠] y, f p = a :=
      hfreqA.mono hA_value
    rcases (hfreq_eq.and_eventually hNe).exists with ⟨p, hp_eq, hp_ne⟩
    exact hp_ne hp_eq

/--
%%handwave
name:
  Local equality of a holomorphic surface map propagates globally
statement:
  If a holomorphic map from a Riemann surface to the complex plane is
  equal to one value on a neighborhood of one point, then it is equal to that
  value on the whole surface.
proof:
  In coordinate charts this is the analytic identity theorem.  The set of
  points having a neighborhood on which \(f\) equals the chosen value is open,
  nonempty, and closed by the coordinate identity theorem; connectedness of
  the surface makes it the whole surface.
-/
theorem holomorphicMap_eq_const_of_eventually_eq_value
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {x : X}
    (hlocal : ∀ᶠ y in 𝓝 x, f y = f x) :
    ∀ y : X, f y = f x := by
  let A : Set X := {y : X | ∀ᶠ z in 𝓝 y, f z = f x}
  have hxA : x ∈ A := hlocal
  have hA_open : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hyA
    rcases mem_nhds_iff.mp hyA with ⟨U, hU_subset, hU_open, hyU⟩
    refine mem_nhds_iff.mpr ⟨U, ?_, hU_open, hyU⟩
    intro z hzU
    exact Filter.mem_of_superset (hU_open.mem_nhds hzU) hU_subset
  have hA_closed : IsClosed A := by
    apply isClosed_of_closure_subset
    intro y hy
    exact holomorphicMap_eventually_eq_value_of_mem_closure_eventually_eq_value
      (f := f) hf (a := f x) hy
  have hA_univ : A = Set.univ :=
    (IsClopen.eq_univ ⟨hA_closed, hA_open⟩ ⟨x, hxA⟩)
  intro y
  have hyA : y ∈ A := by
    rw [hA_univ]
    exact Set.mem_univ y
  rcases mem_nhds_iff.mp hyA with ⟨U, hU_subset, _hU_open, hyU⟩
  exact hU_subset hyU

/--
%%handwave
name:
  Nonconstant holomorphic surface maps are not locally constant at a point
statement:
  A nonconstant holomorphic map from a Riemann surface to the
  complex plane is not locally equal to \(f(x)\) at any point \(x\).
proof:
  Otherwise
  [local equality would propagate globally](lean:JJMath.Uniformization.holomorphicMap_eq_const_of_eventually_eq_value),
  making the range a subsingleton.
-/
theorem nonconstant_holomorphicMap_not_eventually_eq_value
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    ∀ x : X, ¬ ∀ᶠ y in 𝓝 x, f y = f x := by
  intro x hlocal
  have hconst :
      ∀ y : X, f y = f x :=
    holomorphicMap_eq_const_of_eventually_eq_value (f := f) hf hlocal
  have hrange : (Set.range f).Subsingleton := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [hconst a, hconst b]
  exact hnonconstant.not_subsingleton hrange

/--
%%handwave
name:
  Nonconstant holomorphic maps have isolated fibers locally
statement:
  Let \(f\) be a nonconstant holomorphic map from a Riemann surface
  to the complex plane.  Around every point \(x\) there is a neighborhood on
  which \(x\) is the only point mapping to \(f(x)\).
proof:
  In a complex coordinate, \(f-f(x)\) is analytic.  If its zeros accumulated
  at \(x\), the isolated-zero theorem would make it vanish on a coordinate
  neighborhood.  The surface identity theorem would then propagate this local
  equality across the connected surface, making \(f\) constant, contrary to
  the hypothesis.
-/
theorem nonconstant_holomorphicMap_exists_isolatedFiber_neighborhood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    ∀ x : X, ∃ P : Set X,
      IsOpen P ∧ x ∈ P ∧ ∀ y ∈ P, y ≠ x → f y ≠ f x := by
  intro x
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z₀ : ℂ := e x
  have hx_source : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hg_an : AnalyticAt ℂ (fun z : ℂ ↦ f (e.symm z)) z₀ := by
    simpa [z₀] using
      surface_coordinateExpression_analyticAt (X := X) (f := f) hf he hx_source
  have hnot_surface :
      ¬ ∀ᶠ y in 𝓝 x, f y = f x :=
    nonconstant_holomorphicMap_not_eventually_eq_value
      (f := f) hf hnonconstant x
  have hnot_coord :
      ¬ ∀ᶠ z in 𝓝 z₀,
        (fun z : ℂ ↦ f (e.symm z)) z =
          (fun z : ℂ ↦ f (e.symm z)) z₀ := by
    intro hcoord
    apply hnot_surface
    have hcoord_set :
        {z : ℂ | f (e.symm z) = f (e.symm z₀)} ∈ 𝓝 z₀ := by
      simpa using hcoord
    have hpre :
        e ⁻¹' {z : ℂ | f (e.symm z) = f (e.symm z₀)} ∈ 𝓝 x := by
      rw [← e.map_nhds_eq hx_source, Filter.mem_map] at hcoord_set
      exact hcoord_set
    have hsource_mem : e.source ∈ 𝓝 x :=
      e.open_source.mem_nhds hx_source
    refine Filter.mem_of_superset (Filter.inter_mem hsource_mem hpre) ?_
    intro y hy
    rcases hy with ⟨hy_source, hy_pre⟩
    change f (e.symm (e y)) = f (e.symm z₀) at hy_pre
    simpa [z₀, e.left_inv hy_source, e.left_inv hx_source] using hy_pre
  rcases analyticAt_exists_isolatedFiber_neighborhood
      hg_an hnot_coord with
    ⟨Q, hQ_open, hzQ, hQ_isolated⟩
  let P : Set X := e.source ∩ e ⁻¹' Q
  refine ⟨P, e.isOpen_inter_preimage hQ_open, ⟨hx_source, hzQ⟩, ?_⟩
  intro y hyP hy_ne_x
  have hy_source : y ∈ e.source := hyP.1
  have hey_ne : e y ≠ z₀ := by
    intro hey
    apply hy_ne_x
    calc
      y = e.symm (e y) := (e.left_inv hy_source).symm
      _ = e.symm z₀ := by rw [hey]
      _ = x := by simp [z₀, e.left_inv hx_source]
  have hne := hQ_isolated (e y) hyP.2 hey_ne
  simpa [z₀, e.left_inv hy_source, e.left_inv hx_source] using hne

/--
%%handwave
name:
  Local normal form gives an avoiding coordinate disk
statement:
  For a nonconstant holomorphic map from a Riemann surface to the
  complex plane, every point and every neighborhood contain a relatively
  compact coordinate disk \(D\) such that \(f(x)\) is not attained on the
  frontier of \(D\).
proof:
  In a local coordinate centered at \(x\), the nonconstant holomorphic map has
  normal form
  \[
    f(z)=f(x)+z^m g(z)
  \]
  with \(m>0\) and \(g(0)\ne 0\).  After shrinking, \(g\) has no zeros on the
  closed coordinate disk.  Hence \(f(z)=f(x)\) has no solution on the boundary
  circle.  Choose the radius small enough that the closed coordinate disk is
  contained in the prescribed neighborhood.
-/
theorem nonconstant_holomorphicMap_exists_relativelyCompactCoordinateDisk_boundaryImage_avoids
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    ∀ x : X, ∀ N : Set X, x ∈ N → IsOpen N →
      ∃ D : RelativelyCompactCoordinateDisk X,
        x ∈ D.carrier ∧ D.carrier ⊆ N ∧ f x ∉ f '' frontier D.carrier := by
  intro x N hxN hN_open
  rcases nonconstant_holomorphicMap_exists_isolatedFiber_neighborhood
      (f := f) hf hnonconstant x with
    ⟨P, hP_open, hxP, hP_isolated⟩
  let M : Set X := N ∩ P
  have hxM : x ∈ M := ⟨hxN, hxP⟩
  have hM_open : IsOpen M := hN_open.inter hP_open
  rcases exists_relativelyCompactCoordinateDisk_subset_open
      (X := X) hxM hM_open with
    ⟨D, hxD, hD_closure_subset_M⟩
  have hD_subset_N : D.carrier ⊆ N := by
    intro y hyD
    exact (hD_closure_subset_M (subset_closure hyD)).1
  have hx_not_frontier : x ∉ frontier D.carrier := by
    intro hx_frontier
    have hx_interior : x ∈ interior D.carrier := by
      rw [D.isOpen.interior_eq]
      exact hxD
    rw [frontier] at hx_frontier
    exact hx_frontier.2 hx_interior
  have hx_not_image : f x ∉ f '' frontier D.carrier := by
    rintro ⟨y, hy_frontier, hy_eq⟩
    have hy_closure : y ∈ closure D.carrier :=
      frontier_subset_closure hy_frontier
    have hyP : y ∈ P := (hD_closure_subset_M hy_closure).2
    have hy_ne_x : y ≠ x := by
      intro hyx
      subst y
      exact hx_not_frontier hy_frontier
    exact (hP_isolated y hyP hy_ne_x) hy_eq
  exact ⟨D, hxD, hD_subset_N, hx_not_image⟩

/--
%%handwave
name:
  Local normal form gives a second-countable neighborhood whose boundary image is avoided
statement:
  For a nonconstant holomorphic map from a Riemann surface to the
  complex plane, every point and every surface neighborhood contain a
  second-countable open neighborhood \(W\) with compact frontier such that
  \(f(x)\) is not in the image of the frontier of \(W\).
proof:
  Choose a relatively compact coordinate disk \(W\) around the point inside the
  prescribed neighborhood.  By the local normal form of a nonconstant
  holomorphic map, after shrinking \(W\) the value \(f(x)\) is not in
  \(f(\partial W)\).  The frontier is a compact coordinate circle, and the
  coordinate disk is second countable.
-/
theorem nonconstant_holomorphicMap_exists_secondCountable_neighborhood_boundaryImage_avoids
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    ∀ x : X, ∀ N : Set X, x ∈ N → IsOpen N →
      ∃ W : Set X,
        IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ SecondCountableTopology W ∧
          IsCompact (frontier W) ∧ f x ∉ f '' frontier W := by
  intro x N hxN hN_open
  rcases nonconstant_holomorphicMap_exists_relativelyCompactCoordinateDisk_boundaryImage_avoids
      (f := f) hf hnonconstant x N hxN hN_open with
    ⟨D, hxD, hD_subset_N, hx_not_image⟩
  exact ⟨D.carrier, D.isOpen, hxD, hD_subset_N, D.secondCountable,
    D.frontier_compact, hx_not_image⟩

/--
%%handwave
name:
  Local normal form gives a boundary-avoiding second-countable neighborhood
statement:
  For a nonconstant holomorphic map from a Riemann surface to the
  complex plane, every point and every surface neighborhood contain a
  second-countable open neighborhood \(W\) and admit a plane-basis element
  \(U\) around the image point such that \(f^{-1}(U)\) avoids the frontier of
  \(W\).
proof:
  Use
  [a second-countable neighborhood whose boundary image is
  avoided](lean:JJMath.Uniformization.nonconstant_holomorphicMap_exists_secondCountable_neighborhood_boundaryImage_avoids).
  Since the frontier is compact, its image is closed in \(\mathbb C\).  Choose
  [a countable-basis element avoiding that image](lean:JJMath.Uniformization.exists_countableBasis_disjoint_frontier_preimage).
-/
theorem nonconstant_holomorphicMap_exists_boundaryAvoiding_secondCountable_neighborhood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    ∀ x : X, ∀ N : Set X, x ∈ N → IsOpen N →
      ∃ W : Set X, ∃ U ∈ TopologicalSpace.countableBasis ℂ,
        IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ SecondCountableTopology W ∧
          f x ∈ U ∧ Disjoint (frontier W) (f ⁻¹' U) := by
  intro x N hxN hN_open
  rcases nonconstant_holomorphicMap_exists_secondCountable_neighborhood_boundaryImage_avoids
      (f := f) hf hnonconstant x N hxN hN_open with
    ⟨W, hW_open, hxW, hW_subset_N, hW_second, hfrontier_compact, hx_not_image⟩
  rcases exists_countableBasis_disjoint_frontier_preimage
      (f := f) hf.continuous hfrontier_compact hx_not_image with
    ⟨U, hU_basis, hxU, hdisj⟩
  exact ⟨W, U, hU_basis, hW_open, hxW, hW_subset_N, hW_second, hxU, hdisj⟩

/--
%%handwave
name:
  Local normal form gives a trapped second-countable pullback component
statement:
  For a nonconstant holomorphic map from a Riemann surface to the
  complex plane, every point and every surface neighborhood admit a plane
  basis element whose pullback component through the point is contained in the
  neighborhood and is second countable.
proof:
  Use
  [a boundary-avoiding second-countable neighborhood](lean:JJMath.Uniformization.nonconstant_holomorphicMap_exists_boundaryAvoiding_secondCountable_neighborhood).
  Since \(f^{-1}(U)\) avoids the frontier of \(W\), the connected component
  through \(x\)
  [is trapped inside \(W\)](lean:JJMath.Uniformization.connectedComponentIn_subset_of_isOpen_of_disjoint_frontier).
  It is therefore a subspace of a second-countable subspace, hence second
  countable.
-/
theorem nonconstant_holomorphicMap_trappedSecondCountablePullbackComponent
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    ∀ x : X, ∀ N : Set X, x ∈ N → IsOpen N →
      ∃ U ∈ TopologicalSpace.countableBasis ℂ,
        f x ∈ U ∧ connectedComponentIn (f ⁻¹' U) x ⊆ N ∧
          SecondCountableTopology (connectedComponentIn (f ⁻¹' U) x) := by
  intro x N hxN hN_open
  rcases nonconstant_holomorphicMap_exists_boundaryAvoiding_secondCountable_neighborhood
      (f := f) hf hnonconstant x N hxN hN_open with
    ⟨W, U, hU_basis, hW_open, hxW, hW_subset_N, hW_second, hxU, hdisj⟩
  have hcomponent_subset_W :
      connectedComponentIn (f ⁻¹' U) x ⊆ W :=
    connectedComponentIn_subset_of_isOpen_of_disjoint_frontier
      hW_open hxU hxW hdisj
  have hcomponent_second :
      SecondCountableTopology (connectedComponentIn (f ⁻¹' U) x) := by
    haveI : SecondCountableTopology W := hW_second
    exact secondCountableTopology_of_subset_secondCountable hcomponent_subset_W
  exact ⟨U, hU_basis, hxU, hcomponent_subset_W.trans hW_subset_N, hcomponent_second⟩

/--
%%handwave
name:
  Good pullback sheets refine neighborhoods
statement:
  For a nonconstant holomorphic map from a Riemann surface to the
  complex plane, every point and every surface neighborhood contain a good
  pullback sheet.
proof:
  Apply
  [the local normal form gives a trapped second-countable pullback
  component](lean:JJMath.Uniformization.nonconstant_holomorphicMap_trappedSecondCountablePullbackComponent)
  and then package that component as a good pullback sheet.
-/
theorem nonconstant_holomorphicMap_goodPullbackSheets_local_refinement
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    ∀ x : X, ∀ N : Set X, x ∈ N → IsOpen N →
      ∃ S ∈ goodPullbackSheets f, x ∈ S ∧ S ⊆ N := by
  intro x N hxN hN_open
  rcases nonconstant_holomorphicMap_trappedSecondCountablePullbackComponent
      (f := f) hf hnonconstant x N hxN hN_open with
    ⟨U, hU_basis, hxU, hcomponent_subset, hcomponent_second⟩
  let S : Set X := connectedComponentIn (f ⁻¹' U) x
  refine ⟨S, ?_, ?_, hcomponent_subset⟩
  · exact ⟨U, hU_basis, x, hxU, rfl, hcomponent_second⟩
  · exact mem_connectedComponentIn hxU

/--
%%handwave
name:
  Countably many good pullback sheets
statement:
  For a nonconstant holomorphic map from a Riemann surface to the
  complex plane, the good pullback sheets form a countable family.
proof:
  The local boundary-avoidance construction shows that good sheets form a
  basis.  Then the adjacency argument counts the whole basis: one good sheet
  meets only countably many good sheets, and connectedness propagates from one
  sheet to all sheets.
-/
theorem nonconstant_holomorphicMap_goodPullbackSheets_countable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    (goodPullbackSheets f).Countable := by
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hbasis : TopologicalSpace.IsTopologicalBasis (goodPullbackSheets f) :=
    goodPullbackSheets_isTopologicalBasis_of_local_refinement
      (f := f) hf.continuous
      (nonconstant_holomorphicMap_goodPullbackSheets_local_refinement
        (f := f) hf hnonconstant)
  exact goodPullbackSheets_countable_of_basis
    (f := f) hf.continuous hbasis

/--
%%handwave
name:
  Poincare-Volterra countability mechanism
statement:
  A Riemann surface carrying a nonconstant holomorphic function to
  the complex plane is second countable.
proof:
  Take the connected components of inverse images of members of a countable
  basis of \(\mathbb C\). Keep those components that are trapped in
  second-countable coordinate neighborhoods. [These good sheets refine every surface neighborhood](lean:JJMath.Uniformization.nonconstant_holomorphicMap_goodPullbackSheets_local_refinement), so they form a basis.
  For a fixed good sheet, the components over one plane-basis element that
  meet it determine pairwise disjoint nonempty open subsets of a
  second-countable space. Thus [each good sheet meets only countably many other good sheets](lean:JJMath.Uniformization.goodPullbackSheet_meets_countably_many). Connectedness propagates from one sheet through finite adjacency chains, proving that the entire good-sheet basis is countable.
-/
theorem secondCountable_of_nonconstant_holomorphicMap_to_complex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnonconstant : (Set.range f).Nontrivial) :
    SecondCountableTopology X := by
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hbasis : TopologicalSpace.IsTopologicalBasis
      (goodPullbackSheets f) :=
    goodPullbackSheets_isTopologicalBasis_of_local_refinement
      (f := f) hf.continuous
      (nonconstant_holomorphicMap_goodPullbackSheets_local_refinement
        (f := f) hf hnonconstant)
  have hcount : (goodPullbackSheets f).Countable :=
    nonconstant_holomorphicMap_goodPullbackSheets_countable
      (f := f) hf hnonconstant
  exact hbasis.secondCountableTopology hcount

def radoChainUnionOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {ι : Type}
    (D : ι → SecondCountableOpenDomain X) : TopologicalSpace.Opens X where
  carrier := ⋃ i : ι, (D i).carrier
  is_open' := isOpen_iUnion fun i : ι ↦ (D i).isOpen

/--
%%handwave
name:
  Open subsets of complex one-manifolds are complex one-manifolds
statement:
  An open subset of a complex one-manifold, with its induced complex charts,
  is again a complex one-manifold.
-/
theorem openSubset_complexOneManifold
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (U : TopologicalSpace.Opens X) :
    ComplexOneManifold U := by
  exact {}

/--
%%handwave
name:
  Complex charted spaces are locally simply connected
statement:
  Any space locally charted by open subsets of the complex plane is locally
  simply connected.
proof:
  Around a point and inside a prescribed open neighborhood, choose a complex
  chart and then a sufficiently small Euclidean ball in the chart image.  Pull
  this ball back by the chart.  The chart identifies the pulled-back
  neighborhood with a Euclidean ball, and Euclidean balls are contractible,
  hence path connected and simply connected.
-/
theorem chartedSpace_complex_locallySimplyConnectedSpace
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] :
    LocallySimplyConnectedSpace X := by
  classical
  refine ⟨?_⟩
  intro x N hxN hN
  let e := chartAt ℂ x
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' N
  have hS_open : IsOpen S := e.isOpen_inter_preimage_symm hN
  have hxS : e x ∈ S := by
    refine ⟨mem_chart_target ℂ x, ?_⟩
    have hx_source : x ∈ e.source := mem_chart_source ℂ x
    simpa [e.left_inv hx_source] using hxN
  rcases Metric.isOpen_iff.mp hS_open (e x) hxS with ⟨r, hr_pos, hr_subset⟩
  let B : Set ℂ := Metric.ball (e x) r
  let U : Set X := e.symm '' B
  have hB_subset_target : B ⊆ e.target := by
    intro z hz
    exact (hr_subset hz).1
  have hU_open : IsOpen U := by
    exact e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hB_subset_target
  have hxU : x ∈ U := by
    refine ⟨e x, ?_, ?_⟩
    · change e x ∈ Metric.ball (e x) r
      exact Metric.mem_ball_self hr_pos
    · exact e.left_inv (mem_chart_source ℂ x)
  have hU_subset_N : U ⊆ N := by
    intro y hy
    rcases hy with ⟨z, hzB, rfl⟩
    exact (hr_subset hzB).2
  have hU_subset_source : U ⊆ e.source := by
    intro y hy
    rcases hy with ⟨z, hzB, rfl⟩
    exact e.map_target (hB_subset_target hzB)
  have himage : e '' U = B := by
    simpa [U] using e.image_symm_image_of_subset_target hB_subset_target
  let hUB : U ≃ₜ B := e.homeomorphOfImageSubsetSource hU_subset_source himage
  refine ⟨U, hxU, hU_open, hU_subset_N, ?_, ?_⟩
  · haveI : ContractibleSpace B := by
      change ContractibleSpace (Metric.ball (e x) r)
      exact Metric.contractibleSpace_ball hr_pos
    exact ⟨hUB.symm.surjective.pathConnectedSpace hUB.symm.continuous⟩
  · haveI : ContractibleSpace B := by
      change ContractibleSpace (Metric.ball (e x) r)
      exact Metric.contractibleSpace_ball hr_pos
    haveI : SimplyConnectedSpace B := SimplyConnectedSpace.ofContractible B
    exact ⟨hUB.toHomotopyEquiv.simplyConnectedSpace⟩

/--
%%handwave
name:
  Open subsets preserve local simple connectedness
statement:
  An open subset of a locally simply connected space is locally simply
  connected.
proof:
  Given a point of the open subset and an open neighborhood inside it, view the
  neighborhood as an open set in the ambient space.  Choose a simply connected
  ambient refinement and pull it back to the open subset.
-/
theorem locallySimplyConnectedSpace_openSubset
    {X : Type} [TopologicalSpace X] [LocallySimplyConnectedSpace X]
    (U : TopologicalSpace.Opens X) :
    LocallySimplyConnectedSpace U := by
  refine ⟨?_⟩
  intro x N hxN hN
  let N' : Set X := ((↑) : U → X) '' N
  have hxN' : (x : X) ∈ N' := ⟨x, hxN, rfl⟩
  have hN'_open : IsOpen N' := U.is_open'.isOpenMap_subtype_val N hN
  rcases LocallySimplyConnectedSpace.exists_subset (x : X) hxN' hN'_open with
    ⟨W, hxW, hWopen, hWsub, ⟨hW_pathConnected⟩, ⟨hW_simplyConnected⟩⟩
  let V : Set U := ((↑) : U → X) ⁻¹' W
  have hV_subset : V ⊆ N := by
    intro y hy
    have hyW : (y : X) ∈ W := hy
    rcases hWsub hyW with ⟨z, hzN, hz_eq⟩
    have hzy : z = y := Subtype.ext hz_eq
    simpa [hzy] using hzN
  have hW_subset_U : W ⊆ (U : Set X) := by
    intro y hy
    rcases hWsub hy with ⟨z, _hzN, hz_eq⟩
    simpa [hz_eq] using z.2
  let e : V ≃ₜ W :=
    { toFun := fun y ↦ ⟨((y : U) : X), y.2⟩
      invFun := fun y ↦ ⟨⟨(y : X), hW_subset_U y.2⟩, y.2⟩
      left_inv := by
        intro y
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl
      continuous_toFun := by
        exact Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_subtype_val) (fun y : V ↦ y.2)
      continuous_invFun := by
        exact Continuous.subtype_mk
          (Continuous.subtype_mk continuous_subtype_val (fun y : W ↦ hW_subset_U y.2))
          (fun y : W ↦ y.2) }
  refine ⟨V, hxW, hWopen.preimage continuous_subtype_val, hV_subset, ?_, ?_⟩
  · haveI : PathConnectedSpace W := hW_pathConnected
    exact ⟨e.symm.surjective.pathConnectedSpace e.symm.continuous⟩
  · haveI : SimplyConnectedSpace W := hW_simplyConnected
    exact ⟨e.toHomotopyEquiv.simplyConnectedSpace⟩

/--
%%handwave
name:
  Connected open subsets are Riemann surfaces
statement:
  A nonempty preconnected open subset of a Riemann surface is a
  Riemann surface with the induced complex structure.
proof:
  The open subset inherits the complex-manifold charts and Hausdorff property,
  while nonemptiness and preconnectedness give connectedness.
-/
theorem riemannSurface_openSubset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (U : TopologicalSpace.Opens X)
    (hne : (U : Set X).Nonempty) (hpre : IsPreconnected (U : Set X)) :
    RiemannSurface U := by
  haveI : ComplexOneManifold U := openSubset_complexOneManifold U
  haveI : ConnectedSpace U := Subtype.connectedSpace ⟨hne, hpre⟩
  exact {}

/--
%%handwave
name:
  Nested unions of domains are connected
statement:
  A nonempty nested union of second-countable open domains in a Riemann surface
  is connected.
proof:
  Each member of the chain is nonempty and preconnected.  Any two members of
  the chain meet, because one contains the other and the smaller one is
  nonempty.  Hence the intersection graph of the family is connected, so the
  union is connected.
-/
theorem rado_chain_union_isConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {ι : Type} [Nonempty ι]
    (D : ι → SecondCountableOpenDomain X)
    (hchain : IsChain (· ⊆ ·) (Set.range fun i : ι => (D i).carrier)) :
    IsConnected (⋃ i : ι, (D i).carrier) := by
  refine IsConnected.iUnion_of_reflTransGen ?_ ?_
  · intro i
    exact ⟨(D i).nonempty, (D i).isPreconnected⟩
  · intro i j
    refine Relation.ReflTransGen.single ?_
    by_cases hEq : (D i).carrier = (D j).carrier
    · rcases (D i).nonempty with ⟨x, hx⟩
      exact ⟨x, hx, by simpa [← hEq] using hx⟩
    · rcases hchain (Set.mem_range_self i) (Set.mem_range_self j) hEq with hsub | hsub
      · rcases (D i).nonempty with ⟨x, hx⟩
        exact ⟨x, hx, hsub hx⟩
      · rcases (D j).nonempty with ⟨x, hx⟩
        exact ⟨x, hsub hx, hx⟩

/--
%%handwave
name:
  The chain union is a Riemann surface
statement:
  A nonempty nested union of second-countable open domains in a connected
  Riemann surface is itself a Riemann surface.
proof:
  The union is open.  By
  [the nested union is connected](lean:JJMath.Uniformization.rado_chain_union_isConnected),
  it is nonempty and preconnected, so the induced open-subset structure is a
  Riemann surface.
-/
theorem rado_chain_union_riemannSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {ι : Type} [Nonempty ι]
    (D : ι → SecondCountableOpenDomain X)
    (hchain : IsChain (· ⊆ ·) (Set.range fun i : ι => (D i).carrier)) :
    RiemannSurface (radoChainUnionOpen D) := by
  have hconn := rado_chain_union_isConnected D hchain
  exact riemannSurface_openSubset (radoChainUnionOpen D)
    hconn.nonempty hconn.isPreconnected

/--
%%handwave
name:
  Compact chain unions are second countable
statement:
  A compact nested union of second-countable open domains in a Riemann surface
  is second countable.
proof:
  Cover the compact union by coordinate disks of the induced surface.  A finite
  subcover suffices, and a finite union of second-countable coordinate disks is
  second countable.
-/
theorem rado_chain_union_secondCountable_of_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {ι : Type} [Nonempty ι]
    (D : ι → SecondCountableOpenDomain X)
    (hchain : IsChain (· ⊆ ·) (Set.range fun i : ι => (D i).carrier))
    [CompactSpace (radoChainUnionOpen D)] :
    SecondCountableTopology (radoChainUnionOpen D) := by
  classical
  haveI : RiemannSurface (radoChainUnionOpen D) :=
    rado_chain_union_riemannSurface D hchain
  choose coord hcoord using
    fun x : radoChainUnionOpen D ↦ exists_coordinateDisk_mem (radoChainUnionOpen D) x
  let V : radoChainUnionOpen D → Set (radoChainUnionOpen D) :=
    fun x ↦ (coord x).carrier
  have hcover_univ : (Set.univ : Set (radoChainUnionOpen D)) ⊆ ⋃ x, V x := by
    intro x _hx
    exact Set.mem_iUnion.mpr ⟨x, hcoord x⟩
  rcases isCompact_univ.elim_finite_subcover V
      (fun x ↦ (coord x).isOpen) hcover_univ with
    ⟨t, htcover⟩
  let W : t → Set (radoChainUnionOpen D) := fun x ↦ V x
  have hcover : (⋃ x : t, W x) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr ?_
    intro x
    have hx : x ∈ ⋃ y ∈ t, V y := htcover (Set.mem_univ x)
    rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hxy⟩
  exact secondCountableTopology_of_countable_open_cover_explicit
    W
    (fun x : t ↦ (coord x).isOpen)
    hcover
    (fun x : t ↦ (coord x).secondCountable)

/--
%%handwave
name:
  Closed coordinate disk
statement:
  A closed coordinate disk is the preimage of a closed Euclidean disk whose
  radius is strictly smaller than the radius of an ambient coordinate disk.
-/
structure ClosedCoordinateDisk (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The ambient open coordinate disk. -/
  openDisk : CoordinateDisk X
  /-- The closed disk as a subset of the surface. -/
  carrier : Set X
  /-- The Euclidean radius of the closed disk in the chosen coordinate. -/
  closedRadius : ℝ
  /-- The closed radius is positive. -/
  closedRadius_pos : 0 < closedRadius
  /-- The closed disk is strictly contained in the ambient open coordinate disk. -/
  closedRadius_lt_openRadius : closedRadius < openDisk.radius
  /-- The surface closed disk is exactly the chart preimage of the Euclidean closed disk. -/
  carrier_eq :
    carrier = openDisk.chart.source ∩ openDisk.chart ⁻¹'
      Metric.closedBall openDisk.center closedRadius
  /-- The closed coordinate disk is compact in the surface. -/
  compact : IsCompact carrier

namespace ClosedCoordinateDisk

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name:
  Closed coordinate disks are closed
statement:
  In a Hausdorff surface, a closed coordinate disk is closed as a subset of the
  surface.
proof:
  The closed coordinate disk is compact by definition, and compact subsets of
  Hausdorff spaces are closed.
-/
theorem isClosed [T2Space X] (D : ClosedCoordinateDisk X) :
    IsClosed D.carrier :=
  D.compact.isClosed

/--
%%handwave
name:
  Closed coordinate disks lie in their ambient coordinate disks
statement:
  A closed coordinate disk is contained in its ambient open coordinate disk.
proof:
  In coordinates this is the inclusion
  \(\overline B(c,r)\subset B(c,R)\), which follows from \(r<R\).
-/
theorem subset_openDisk (D : ClosedCoordinateDisk X) :
    D.carrier ⊆ D.openDisk.carrier := by
  intro x hx
  rw [D.carrier_eq] at hx
  rw [D.openDisk.carrier_eq]
  exact ⟨hx.1, Metric.closedBall_subset_ball D.closedRadius_lt_openRadius hx.2⟩

/--
%%handwave
name:
  Closed coordinate disks lie in the chart target
statement:
  The Euclidean closed disk defining a closed coordinate disk lies inside the
  target of its coordinate chart.
proof:
  The closed radius is strictly smaller than the open coordinate radius, and
  the open coordinate disk lies in the chart target.
-/
theorem closedBall_subset_chart_target (D : ClosedCoordinateDisk X) :
    Metric.closedBall D.openDisk.center D.closedRadius ⊆
      D.openDisk.chart.target := by
  exact (Metric.closedBall_subset_ball D.closedRadius_lt_openRadius).trans
    D.openDisk.ball_subset_target

/--
%%handwave
name:
  Boundary circle of a closed coordinate disk
statement:
  The boundary circle of a closed coordinate disk is the preimage, in the
  defining coordinate chart, of the Euclidean circle with the closed disk's
  center and radius.
-/
def boundaryCircle (D : ClosedCoordinateDisk X) : Set X :=
  D.openDisk.chart.source ∩ D.openDisk.chart ⁻¹'
    Metric.sphere D.openDisk.center D.closedRadius

/--
%%handwave
name:
  The boundary circle lies in the closed coordinate disk
statement:
  The boundary circle of a closed coordinate disk is contained in the closed
  coordinate disk.
proof:
  Both sets use the same chart source, and the Euclidean sphere
  \(S(c,r)\) is contained in the closed ball \(\overline B(c,r)\).
-/
theorem boundaryCircle_subset_carrier (D : ClosedCoordinateDisk X) :
    D.boundaryCircle ⊆ D.carrier := by
  intro x hx
  rw [D.carrier_eq]
  exact ⟨hx.1, Metric.sphere_subset_closedBall hx.2⟩

/--
%%handwave
name:
  Exterior annulus of a closed coordinate disk
statement:
  The exterior annulus of a closed coordinate disk is the part of the ambient
  coordinate disk whose coordinate radius is strictly between the closed radius
  and the ambient open radius.
-/
def exteriorAnnulus (D : ClosedCoordinateDisk X) : Set X :=
  D.openDisk.chart.source ∩ D.openDisk.chart ⁻¹'
    ((fun z : ℂ ↦ dist z D.openDisk.center) ⁻¹'
      Set.Ioo D.closedRadius D.openDisk.radius)

/--
%%handwave
name:
  Exterior annuli are open
statement:
  The exterior annulus of a closed coordinate disk is open in the surface.
proof:
  It is the chart preimage of an open interval under the continuous distance
  from the disk center.
-/
theorem exteriorAnnulus_isOpen (D : ClosedCoordinateDisk X) :
    IsOpen D.exteriorAnnulus := by
  have hdist : Continuous fun z : ℂ ↦ dist z D.openDisk.center :=
    continuous_id.dist continuous_const
  exact D.openDisk.chart.isOpen_inter_preimage
    (isOpen_Ioo.preimage hdist)

/--
%%handwave
name:
  Exterior annuli avoid the closed coordinate disk
statement:
  The exterior annulus of a closed coordinate disk is contained in the
  complement of the closed coordinate disk.
proof:
  A point of the annulus has coordinate distance strictly greater than the
  closed radius, whereas a point of the closed disk has coordinate distance at
  most that radius.
-/
theorem exteriorAnnulus_subset_compl_carrier (D : ClosedCoordinateDisk X) :
    D.exteriorAnnulus ⊆ D.carrierᶜ := by
  intro x hx hxD
  have hx' :
      x ∈ D.openDisk.chart.source ∩
        D.openDisk.chart ⁻¹'
          ((fun z : ℂ ↦ dist z D.openDisk.center) ⁻¹'
            Set.Ioo D.closedRadius D.openDisk.radius) := by
    simpa [exteriorAnnulus] using hx
  have hx_ann :
      D.closedRadius < dist (D.openDisk.chart x) D.openDisk.center ∧
        dist (D.openDisk.chart x) D.openDisk.center <
          D.openDisk.radius := by
    simpa [Set.mem_Ioo] using hx'.2
  rw [D.carrier_eq] at hxD
  have hclosed :
      dist (D.openDisk.chart x) D.openDisk.center ≤ D.closedRadius := by
    simpa [Metric.mem_closedBall] using hxD.2
  exact (not_lt_of_ge hclosed) hx_ann.1

/--
%%handwave
name:
  Exterior annuli lie in the ambient coordinate disk
statement:
  The exterior annulus of a closed coordinate disk is contained in the ambient
  open coordinate disk.
proof:
  An annulus point lies in the chart source and its coordinate distance from
  the center is smaller than the ambient open radius, exactly the two
  conditions defining the ambient coordinate disk.
-/
theorem exteriorAnnulus_subset_openDisk (D : ClosedCoordinateDisk X) :
    D.exteriorAnnulus ⊆ D.openDisk.carrier := by
  intro x hx
  have hx' :
      x ∈ D.openDisk.chart.source ∩
        D.openDisk.chart ⁻¹'
          ((fun z : ℂ ↦ dist z D.openDisk.center) ⁻¹'
            Set.Ioo D.closedRadius D.openDisk.radius) := by
    simpa [exteriorAnnulus] using hx
  have hx_ann :
      D.closedRadius < dist (D.openDisk.chart x) D.openDisk.center ∧
        dist (D.openDisk.chart x) D.openDisk.center <
          D.openDisk.radius := by
    simpa [Set.mem_Ioo] using hx'.2
  rw [D.openDisk.carrier_eq]
  exact ⟨hx'.1, by simpa [Metric.mem_ball] using hx_ann.2⟩

/--
%%handwave
name:
  Closed coordinate disks are disjoint from their exterior annuli
statement:
  A closed coordinate disk is disjoint from its exterior annulus.
proof:
  [The exterior annulus lies in the complement of the closed disk](lean:JJMath.Uniformization.ClosedCoordinateDisk.exteriorAnnulus_subset_compl_carrier), which is precisely the desired disjointness.
-/
theorem disjoint_carrier_exteriorAnnulus (D : ClosedCoordinateDisk X) :
    Disjoint D.carrier D.exteriorAnnulus := by
  refine Set.disjoint_left.mpr ?_
  intro x hxD hxA
  exact (D.exteriorAnnulus_subset_compl_carrier hxA) hxD

/--
%%handwave
name:
  Exterior annulus with prescribed outer radius
statement:
  Given an outer radius, the corresponding exterior annulus is the set of
  points whose coordinate radius lies strictly between the closed disk radius
  and that outer radius.
-/
def exteriorAnnulusWithOuterRadius (D : ClosedCoordinateDisk X) (R : ℝ) :
    Set X :=
  D.openDisk.chart.source ∩ D.openDisk.chart ⁻¹'
    ((fun z : ℂ ↦ dist z D.openDisk.center) ⁻¹'
      Set.Ioo D.closedRadius R)

/--
%%handwave
name:
  Prescribed-radius exterior annuli are open
statement:
  An exterior annulus with prescribed outer radius is open in the surface.
proof:
  It is the intersection of the open chart source with the chart preimage of
  the open condition \(r<|z-c|<R\).
-/
theorem exteriorAnnulusWithOuterRadius_isOpen
    (D : ClosedCoordinateDisk X) (R : ℝ) :
    IsOpen (D.exteriorAnnulusWithOuterRadius R) := by
  have hdist : Continuous fun z : ℂ ↦ dist z D.openDisk.center :=
    continuous_id.dist continuous_const
  exact D.openDisk.chart.isOpen_inter_preimage
    (isOpen_Ioo.preimage hdist)

/--
%%handwave
name:
  Prescribed-radius exterior annuli avoid the closed coordinate disk
statement:
  Every exterior annulus with prescribed outer radius is contained in the
  complement of the closed coordinate disk.
proof:
  Its points have coordinate distance strictly greater than the closed radius,
  while points of the closed disk have distance at most that radius.
-/
theorem exteriorAnnulusWithOuterRadius_subset_compl_carrier
    (D : ClosedCoordinateDisk X) (R : ℝ) :
    D.exteriorAnnulusWithOuterRadius R ⊆ D.carrierᶜ := by
  intro x hx hxD
  have hx' :
      x ∈ D.openDisk.chart.source ∩
        D.openDisk.chart ⁻¹'
          ((fun z : ℂ ↦ dist z D.openDisk.center) ⁻¹'
            Set.Ioo D.closedRadius R) := by
    simpa [exteriorAnnulusWithOuterRadius] using hx
  have hx_ann :
      D.closedRadius < dist (D.openDisk.chart x) D.openDisk.center ∧
        dist (D.openDisk.chart x) D.openDisk.center < R := by
    simpa [Set.mem_Ioo] using hx'.2
  rw [D.carrier_eq] at hxD
  have hclosed :
      dist (D.openDisk.chart x) D.openDisk.center ≤ D.closedRadius := by
    simpa [Metric.mem_closedBall] using hxD.2
  exact (not_lt_of_ge hclosed) hx_ann.1

/--
%%handwave
name:
  Small prescribed-radius exterior annuli lie in the ambient coordinate disk
statement:
  If the prescribed outer radius is no larger than the ambient coordinate-disk
  radius, then the corresponding exterior annulus lies in the ambient
  coordinate disk.
proof:
  For an annulus point, \(|z-c|<R\le R_0\), where \(R_0\) is the ambient
  coordinate-disk radius; together with membership in the chart source this
  gives membership in the ambient disk.
-/
theorem exteriorAnnulusWithOuterRadius_subset_openDisk
    (D : ClosedCoordinateDisk X) {R : ℝ} (hR : R ≤ D.openDisk.radius) :
    D.exteriorAnnulusWithOuterRadius R ⊆ D.openDisk.carrier := by
  intro x hx
  have hx' :
      x ∈ D.openDisk.chart.source ∩
        D.openDisk.chart ⁻¹'
          ((fun z : ℂ ↦ dist z D.openDisk.center) ⁻¹'
            Set.Ioo D.closedRadius R) := by
    simpa [exteriorAnnulusWithOuterRadius] using hx
  have hx_ann :
      D.closedRadius < dist (D.openDisk.chart x) D.openDisk.center ∧
        dist (D.openDisk.chart x) D.openDisk.center < R := by
    simpa [Set.mem_Ioo] using hx'.2
  rw [D.openDisk.carrier_eq]
  exact ⟨hx'.1, by
    change D.openDisk.chart x ∈
      Metric.ball D.openDisk.center D.openDisk.radius
    simpa [Metric.mem_ball] using hx_ann.2.trans_le hR⟩

/--
%%handwave
name:
  Expanded closed coordinate disk
statement:
  For any radius, the expanded closed coordinate disk is the inverse image of
  the Euclidean closed ball with that radius in the same coordinate chart.
-/
def expandedClosedDisk (D : ClosedCoordinateDisk X) (ρ : ℝ) : Set X :=
  D.openDisk.chart.source ∩ D.openDisk.chart ⁻¹'
    Metric.closedBall D.openDisk.center ρ

/--
%%handwave
name:
  Expanded open coordinate disk
statement:
  For any radius, the expanded open coordinate disk is the inverse image of
  the Euclidean open ball with that radius in the same coordinate chart.
-/
def expandedOpenDisk (D : ClosedCoordinateDisk X) (ρ : ℝ) : Set X :=
  D.openDisk.chart.source ∩ D.openDisk.chart ⁻¹'
    Metric.ball D.openDisk.center ρ

/--
%%handwave
name:
  Expanded open coordinate disks are open
statement:
  Every expanded open coordinate disk is open in the surface.
proof:
  It is the intersection of the open chart source with the chart preimage of
  the open Euclidean ball \(B(c,\rho)\).
-/
theorem expandedOpenDisk_isOpen
    (D : ClosedCoordinateDisk X) (ρ : ℝ) :
    IsOpen (D.expandedOpenDisk ρ) := by
  rw [expandedOpenDisk]
  exact D.openDisk.chart.isOpen_inter_preimage Metric.isOpen_ball

/--
%%handwave
name:
  Expanded open coordinate disks lie in expanded closed coordinate disks
statement:
  The expanded open disk of radius \(\rho\) is contained in the expanded
  closed disk of the same radius.
proof:
  This follows in coordinates from
  \(B(c,\rho)\subseteq\overline B(c,\rho)\).
-/
theorem expandedOpenDisk_subset_expandedClosedDisk
    (D : ClosedCoordinateDisk X) (ρ : ℝ) :
    D.expandedOpenDisk ρ ⊆ D.expandedClosedDisk ρ := by
  intro x hx
  rw [expandedOpenDisk] at hx
  rw [expandedClosedDisk]
  exact ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩

/--
%%handwave
name:
  Expanded closed coordinate disks are compact
statement:
  If the expanded radius is still below the ambient coordinate radius, then
  the expanded closed coordinate disk is compact.
proof:
  The Euclidean closed ball \(\overline B(c,\rho)\) then lies in the chart
  target.  The expanded disk is its image under the continuous inverse chart,
  so it is compact.
-/
theorem expandedClosedDisk_compact [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ : ρ < D.openDisk.radius) :
    IsCompact (D.expandedClosedDisk ρ) := by
  have hclosedBall_target :
      Metric.closedBall D.openDisk.center ρ ⊆ D.openDisk.chart.target := by
    exact (Metric.closedBall_subset_ball hρ).trans
      D.openDisk.ball_subset_target
  rw [expandedClosedDisk,
    ← D.openDisk.chart.symm_image_eq_source_inter_preimage hclosedBall_target]
  exact (isCompact_closedBall D.openDisk.center ρ).image_of_continuousOn
    (D.openDisk.chart.continuousOn_symm.mono hclosedBall_target)

/--
%%handwave
name:
  Closed coordinate disks lie in expanded closed coordinate disks
statement:
  If the expanded radius is at least the closed radius, then the original
  closed coordinate disk is contained in the expanded one.
proof:
  A point of the original disk satisfies \(|z-c|\le r\le\rho\), hence lies
  in the expanded closed disk defined by \(|z-c|\le\rho\).
-/
theorem carrier_subset_expandedClosedDisk
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ : D.closedRadius ≤ ρ) :
    D.carrier ⊆ D.expandedClosedDisk ρ := by
  intro x hx
  rw [D.carrier_eq] at hx
  rw [expandedClosedDisk]
  refine ⟨hx.1, ?_⟩
  have hdist : dist (D.openDisk.chart x) D.openDisk.center ≤ D.closedRadius := by
    simpa [Metric.mem_closedBall] using hx.2
  simpa [Metric.mem_closedBall] using hdist.trans hρ

/--
%%handwave
name:
  Complements of expanded closed coordinate disks lie outside the original disk
statement:
  If the expanded radius is at least the closed radius, then avoiding the
  expanded closed coordinate disk implies avoiding the original closed
  coordinate disk.
proof:
  Take complements in [the inclusion of the original disk in the expanded closed disk](lean:JJMath.Uniformization.ClosedCoordinateDisk.carrier_subset_expandedClosedDisk).
-/
theorem compl_expandedClosedDisk_subset_compl_carrier
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ : D.closedRadius ≤ ρ) :
    (D.expandedClosedDisk ρ)ᶜ ⊆ D.carrierᶜ := by
  intro x hx hD
  exact hx (D.carrier_subset_expandedClosedDisk hρ hD)

/--
%%handwave
name:
  Expanded radius avoiding two exterior points
statement:
  If two points lie outside a closed coordinate disk and \(R\) is any radius
  larger than the closed radius, then there is an intermediate expanded radius
  below \(R\) whose expanded closed disk still misses both points.
proof:
  For a point in the chart source, being outside the closed coordinate disk
  means that its coordinate radius is strictly larger than the closed radius.
  For a point outside the chart source, every expanded coordinate disk misses
  it automatically.  Choose the expanded radius below \(R\) and below the
  relevant endpoint coordinate radii.
-/
theorem exists_expandedRadius_lt_outerRadius_avoids_points
    (D : ClosedCoordinateDisk X) {R : ℝ}
    (hR : D.closedRadius < R)
    {x y : X}
    (hx : x ∈ D.carrierᶜ)
    (hy : y ∈ D.carrierᶜ) :
    ∃ ρ : ℝ,
      D.closedRadius < ρ ∧ ρ < R ∧
        x ∈ (D.expandedClosedDisk ρ)ᶜ ∧
          y ∈ (D.expandedClosedDisk ρ)ᶜ := by
  by_cases hx_source : x ∈ D.openDisk.chart.source
  · have hx_dist :
        D.closedRadius < dist (D.openDisk.chart x) D.openDisk.center := by
      by_contra hnot
      have hx_closed :
          dist (D.openDisk.chart x) D.openDisk.center ≤ D.closedRadius :=
        le_of_not_gt hnot
      exact hx (by
        rw [D.carrier_eq]
        exact ⟨hx_source, by
          simpa [Metric.mem_closedBall] using hx_closed⟩)
    by_cases hy_source : y ∈ D.openDisk.chart.source
    · have hy_dist :
          D.closedRadius < dist (D.openDisk.chart y) D.openDisk.center := by
        by_contra hnot
        have hy_closed :
            dist (D.openDisk.chart y) D.openDisk.center ≤ D.closedRadius :=
          le_of_not_gt hnot
        exact hy (by
          rw [D.carrier_eq]
          exact ⟨hy_source, by
            simpa [Metric.mem_closedBall] using hy_closed⟩)
      obtain ⟨ρ, hρD, hρ_upper⟩ :=
        exists_between (lt_min (lt_min hR hx_dist) hy_dist)
      have hρR : ρ < R :=
        hρ_upper.trans_le
          ((min_le_left (min R (dist (D.openDisk.chart x) D.openDisk.center))
            (dist (D.openDisk.chart y) D.openDisk.center)).trans
              (min_le_left R (dist (D.openDisk.chart x) D.openDisk.center)))
      have hρx : ρ < dist (D.openDisk.chart x) D.openDisk.center :=
        hρ_upper.trans_le
          ((min_le_left (min R (dist (D.openDisk.chart x) D.openDisk.center))
            (dist (D.openDisk.chart y) D.openDisk.center)).trans
              (min_le_right R (dist (D.openDisk.chart x) D.openDisk.center)))
      have hρy : ρ < dist (D.openDisk.chart y) D.openDisk.center :=
        hρ_upper.trans_le
          (min_le_right (min R (dist (D.openDisk.chart x) D.openDisk.center))
            (dist (D.openDisk.chart y) D.openDisk.center))
      refine ⟨ρ, hρD, hρR, ?_, ?_⟩
      · intro hxρ
        rw [expandedClosedDisk] at hxρ
        have hx_le :
            dist (D.openDisk.chart x) D.openDisk.center ≤ ρ := by
          simpa [Metric.mem_closedBall] using hxρ.2
        exact (not_lt_of_ge hx_le) hρx
      · intro hyρ
        rw [expandedClosedDisk] at hyρ
        have hy_le :
            dist (D.openDisk.chart y) D.openDisk.center ≤ ρ := by
          simpa [Metric.mem_closedBall] using hyρ.2
        exact (not_lt_of_ge hy_le) hρy
    · obtain ⟨ρ, hρD, hρ_upper⟩ := exists_between (lt_min hR hx_dist)
      have hρR : ρ < R :=
        hρ_upper.trans_le
          (min_le_left R (dist (D.openDisk.chart x) D.openDisk.center))
      have hρx : ρ < dist (D.openDisk.chart x) D.openDisk.center :=
        hρ_upper.trans_le
          (min_le_right R (dist (D.openDisk.chart x) D.openDisk.center))
      refine ⟨ρ, hρD, hρR, ?_, ?_⟩
      · intro hxρ
        rw [expandedClosedDisk] at hxρ
        have hx_le :
            dist (D.openDisk.chart x) D.openDisk.center ≤ ρ := by
          simpa [Metric.mem_closedBall] using hxρ.2
        exact (not_lt_of_ge hx_le) hρx
      · intro hyρ
        rw [expandedClosedDisk] at hyρ
        exact hy_source hyρ.1
  · by_cases hy_source : y ∈ D.openDisk.chart.source
    · have hy_dist :
          D.closedRadius < dist (D.openDisk.chart y) D.openDisk.center := by
        by_contra hnot
        have hy_closed :
            dist (D.openDisk.chart y) D.openDisk.center ≤ D.closedRadius :=
          le_of_not_gt hnot
        exact hy (by
          rw [D.carrier_eq]
          exact ⟨hy_source, by
            simpa [Metric.mem_closedBall] using hy_closed⟩)
      obtain ⟨ρ, hρD, hρ_upper⟩ := exists_between (lt_min hR hy_dist)
      have hρR : ρ < R :=
        hρ_upper.trans_le
          (min_le_left R (dist (D.openDisk.chart y) D.openDisk.center))
      have hρy : ρ < dist (D.openDisk.chart y) D.openDisk.center :=
        hρ_upper.trans_le
          (min_le_right R (dist (D.openDisk.chart y) D.openDisk.center))
      refine ⟨ρ, hρD, hρR, ?_, ?_⟩
      · intro hxρ
        rw [expandedClosedDisk] at hxρ
        exact hx_source hxρ.1
      · intro hyρ
        rw [expandedClosedDisk] at hyρ
        have hy_le :
            dist (D.openDisk.chart y) D.openDisk.center ≤ ρ := by
          simpa [Metric.mem_closedBall] using hyρ.2
        exact (not_lt_of_ge hy_le) hρy
    · obtain ⟨ρ, hρD, hρR⟩ := exists_between hR
      refine ⟨ρ, hρD, hρR, ?_, ?_⟩
      · intro hxρ
        rw [expandedClosedDisk] at hxρ
        exact hx_source hxρ.1
      · intro hyρ
        rw [expandedClosedDisk] at hyρ
        exact hy_source hyρ.1

/--
%%handwave
name:
  Radius boundary circle
statement:
  The radius boundary circle is the inverse image of the Euclidean circle with
  the prescribed radius in the same coordinate chart.
-/
def radiusBoundaryCircle (D : ClosedCoordinateDisk X) (ρ : ℝ) : Set X :=
  D.openDisk.chart.source ∩ D.openDisk.chart ⁻¹'
    Metric.sphere D.openDisk.center ρ

/--
%%handwave
name:
  Closed expanded disk points outside the open expanded disk lie on the radius circle
statement:
  A point in the expanded closed coordinate disk but not in the expanded open
  coordinate disk has coordinate radius exactly \(\rho\), hence lies on the
  radius boundary circle.
proof:
  Closed-disk membership gives \(|z-c|\le\rho\), while failure of open-disk
  membership, with the same chart-source condition, gives
  \(\rho\le|z-c|\).  Thus \(|z-c|=\rho\).
-/
theorem mem_radiusBoundaryCircle_of_mem_expandedClosedDisk_of_not_mem_expandedOpenDisk
    (D : ClosedCoordinateDisk X) {ρ : ℝ} {x : X}
    (hx_closed : x ∈ D.expandedClosedDisk ρ)
    (hx_not_open : x ∉ D.expandedOpenDisk ρ) :
    x ∈ D.radiusBoundaryCircle ρ := by
  rw [expandedClosedDisk] at hx_closed
  have hdist_le :
      dist (D.openDisk.chart x) D.openDisk.center ≤ ρ := by
    simpa [Metric.mem_closedBall] using hx_closed.2
  have hnot_lt :
      ¬ dist (D.openDisk.chart x) D.openDisk.center < ρ := by
    intro hlt
    apply hx_not_open
    rw [expandedOpenDisk]
    exact ⟨hx_closed.1, by
      simpa [Metric.mem_ball] using hlt⟩
  have hρ_le :
      ρ ≤ dist (D.openDisk.chart x) D.openDisk.center :=
    le_of_not_gt hnot_lt
  have hdist_eq :
      dist (D.openDisk.chart x) D.openDisk.center = ρ :=
    le_antisymm hdist_le hρ_le
  rw [radiusBoundaryCircle]
  exact ⟨hx_closed.1, by
    simpa [Metric.mem_sphere, dist_eq_norm] using hdist_eq⟩

/--
%%handwave
name:
  Frontier of an expanded coordinate disk
statement:
  If an expanded radius lies below the ambient coordinate radius, then every
  frontier point of the expanded open coordinate disk lies on the
  corresponding coordinate radius circle.
proof:
  Compact containment puts the closure of the open expanded disk in the
  corresponding closed expanded disk.  A frontier point is not in the open
  disk, so its coordinate radius is exactly the expanded radius.
-/
theorem frontier_expandedOpenDisk_subset_radiusBoundaryCircle [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ_open : ρ < D.openDisk.radius) :
    frontier (D.expandedOpenDisk ρ) ⊆ D.radiusBoundaryCircle ρ := by
  have hclosed_compact : IsCompact (D.expandedClosedDisk ρ) :=
    D.expandedClosedDisk_compact hρ_open
  have hclosure_subset :
      closure (D.expandedOpenDisk ρ) ⊆ D.expandedClosedDisk ρ :=
    closure_minimal (D.expandedOpenDisk_subset_expandedClosedDisk ρ)
      hclosed_compact.isClosed
  intro x hx
  apply D.mem_radiusBoundaryCircle_of_mem_expandedClosedDisk_of_not_mem_expandedOpenDisk
    (hclosure_subset (frontier_subset_closure hx))
  intro hx_open
  have hx_empty :
      x ∈ D.expandedOpenDisk ρ ∩ frontier (D.expandedOpenDisk ρ) :=
    ⟨hx_open, hx⟩
  simp [(D.expandedOpenDisk_isOpen ρ).inter_frontier_eq] at hx_empty

/--
%%handwave
name:
  Larger radius boundary circles avoid the closed coordinate disk
statement:
  A radius boundary circle whose radius is larger than the closed radius lies
  in the complement of the original closed coordinate disk.
proof:
  On the radius circle one has \(|z-c|=\rho>r\), whereas membership in the
  original closed disk would require \(|z-c|\le r\).
-/
theorem radiusBoundaryCircle_subset_compl_carrier
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ : D.closedRadius < ρ) :
    D.radiusBoundaryCircle ρ ⊆ D.carrierᶜ := by
  intro x hx hxD
  have hsphere :
      dist (D.openDisk.chart x) D.openDisk.center = ρ := by
    simpa [radiusBoundaryCircle, Metric.mem_sphere, dist_eq_norm] using hx.2
  rw [D.carrier_eq] at hxD
  have hclosed :
      dist (D.openDisk.chart x) D.openDisk.center ≤ D.closedRadius := by
    simpa [Metric.mem_closedBall] using hxD.2
  exact (not_lt_of_ge hclosed) (by simpa [hsphere] using hρ)

/--
%%handwave
name:
  Coordinate radius circles are compact
statement:
  A coordinate radius circle lying inside the ambient coordinate disk is
  compact as a subset of the surface.
proof:
  It is the image of the corresponding compact Euclidean circle under the
  continuous inverse coordinate map.
-/
theorem radiusBoundaryCircle_isCompact
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ_open : ρ < D.openDisk.radius) :
    IsCompact (D.radiusBoundaryCircle ρ) := by
  have hsphere_target :
      Metric.sphere D.openDisk.center ρ ⊆ D.openDisk.chart.target :=
    (Metric.sphere_subset_ball hρ_open).trans D.openDisk.ball_subset_target
  rw [ClosedCoordinateDisk.radiusBoundaryCircle,
    ← D.openDisk.chart.symm_image_eq_source_inter_preimage hsphere_target]
  exact (isCompact_sphere D.openDisk.center ρ).image_of_continuousOn
    (D.openDisk.chart.continuousOn_symm.mono hsphere_target)

/--
%%handwave
name:
  Positive coordinate radius circles are nonempty
statement:
  A nonnegative coordinate radius strictly below the ambient coordinate
  radius determines a nonempty coordinate circle.
proof:
  Add the given radius along the positive real axis from the coordinate
  center and pull that point back by the inverse chart.
-/
theorem radiusBoundaryCircle_nonempty
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ_open : ρ < D.openDisk.radius) :
    (D.radiusBoundaryCircle ρ).Nonempty := by
  let z : ℂ := D.openDisk.center + (ρ : ℂ)
  have hdist : dist z D.openDisk.center = ρ := by
    rw [dist_eq_norm]
    have hsub : z - D.openDisk.center = (ρ : ℂ) := by
      dsimp [z]
      ring
    rw [hsub]
    exact Complex.norm_of_nonneg hρ
  have hz_ball : z ∈ Metric.ball D.openDisk.center D.openDisk.radius := by
    simpa [Metric.mem_ball, hdist] using hρ_open
  have hz_target : z ∈ D.openDisk.chart.target :=
    D.openDisk.ball_subset_target hz_ball
  refine ⟨D.openDisk.chart.symm z, ?_⟩
  rw [ClosedCoordinateDisk.radiusBoundaryCircle]
  refine ⟨D.openDisk.chart.map_target hz_target, ?_⟩
  have hnorm : ‖z - D.openDisk.center‖ = ρ := by
    simpa [dist_eq_norm] using hdist
  simpa [D.openDisk.chart.right_inv hz_target, Metric.mem_sphere] using hnorm

/--
%%handwave
name:
  Radius boundary circles lie in prescribed exterior annuli
statement:
  If the boundary radius lies strictly between the closed radius and a
  prescribed outer radius, then the corresponding radius boundary circle lies
  in that prescribed exterior annulus.
proof:
  Substitute \(|z-c|=\rho\) into the annulus inequalities
  \(r<|z-c|<R\), using \(r<\rho<R\).
-/
theorem radiusBoundaryCircle_subset_exteriorAnnulusWithOuterRadius
    (D : ClosedCoordinateDisk X) {ρ R : ℝ}
    (hρ : D.closedRadius < ρ) (hρR : ρ < R) :
    D.radiusBoundaryCircle ρ ⊆ D.exteriorAnnulusWithOuterRadius R := by
  intro x hx
  rw [radiusBoundaryCircle] at hx
  rw [exteriorAnnulusWithOuterRadius]
  refine ⟨hx.1, ?_⟩
  have hsphere :
      dist (D.openDisk.chart x) D.openDisk.center = ρ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hx.2
  simpa [Set.mem_Ioo, hsphere] using And.intro hρ hρR

/--
%%handwave
name:
  Expanded closed coordinate disk hitting times are compact
statement:
  For a path on the unit interval, the set of parameters whose image lies in
  an expanded closed coordinate disk is compact whenever the expanded disk is
  compact.
proof:
  The expanded disk is closed because it is compact in a Hausdorff surface.
  Its inverse image under the path is therefore closed in the compact unit
  interval.
-/
theorem expandedClosedDisk_hittingTimes_compact [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ : ρ < D.openDisk.radius)
    {x y : X} (γ : Path x y) :
    IsCompact {t : unitInterval | γ t ∈ D.expandedClosedDisk ρ} := by
  have hK : IsCompact (D.expandedClosedDisk ρ) :=
    D.expandedClosedDisk_compact hρ
  have hclosed : IsClosed (γ ⁻¹' D.expandedClosedDisk ρ) :=
    hK.isClosed.preimage γ.continuous
  simpa using isCompact_univ.of_isClosed_subset hclosed (Set.subset_univ _)

/--
%%handwave
name:
  First and last expanded-disk hitting times
statement:
  If a path meets an expanded closed coordinate disk, then among all hitting
  parameters there is a first one and a last one.
proof:
  Minimize and maximize the ordinary real parameter on the compact hitting
  set.
-/
theorem exists_first_last_expandedClosedDisk_hit [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ : ρ < D.openDisk.radius)
    {x y : X} (γ : Path x y)
    (hhit : ∃ t : unitInterval, γ t ∈ D.expandedClosedDisk ρ) :
    ∃ t₀ t₁ : unitInterval,
      γ t₀ ∈ D.expandedClosedDisk ρ ∧
        γ t₁ ∈ D.expandedClosedDisk ρ ∧
          (∀ t : unitInterval,
            γ t ∈ D.expandedClosedDisk ρ → (t₀ : ℝ) ≤ (t : ℝ)) ∧
            (∀ t : unitInterval,
              γ t ∈ D.expandedClosedDisk ρ → (t : ℝ) ≤ (t₁ : ℝ)) := by
  let S : Set unitInterval := {t : unitInterval | γ t ∈ D.expandedClosedDisk ρ}
  have hS_compact : IsCompact S := by
    simpa [S] using D.expandedClosedDisk_hittingTimes_compact hρ γ
  have hS_nonempty : S.Nonempty := by
    rcases hhit with ⟨t, ht⟩
    exact ⟨t, ht⟩
  let parameter : unitInterval → ℝ := fun t ↦ t
  have hparameter_continuous : ContinuousOn parameter S :=
    continuous_subtype_val.continuousOn
  rcases hS_compact.exists_isMinOn hS_nonempty hparameter_continuous with
    ⟨t₀, ht₀, ht₀_min⟩
  rcases hS_compact.exists_isMaxOn hS_nonempty hparameter_continuous with
    ⟨t₁, ht₁, ht₁_max⟩
  exact ⟨t₀, t₁, ht₀, ht₁, (fun t ht ↦ ht₀_min ht),
    (fun t ht ↦ ht₁_max ht)⟩

private theorem unitInterval_exists_mem_open_lt
    {U : Set unitInterval} (hU : IsOpen U) {t : unitInterval}
    (htU : t ∈ U) (ht_ne_zero : t ≠ 0) :
    ∃ s : unitInterval, s ∈ U ∧ (s : ℝ) < (t : ℝ) := by
  rcases Metric.isOpen_iff.mp hU t htU with ⟨ε, hε, hball⟩
  have ht_pos_I : (0 : unitInterval) < t :=
    unitInterval.pos_iff_ne_zero.mpr ht_ne_zero
  have ht_pos : (0 : ℝ) < (t : ℝ) := by
    rwa [unitInterval.coe_pos]
  let δ : ℝ := min (ε / 2) ((t : ℝ) / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hε) (half_pos ht_pos)
  have hδ_lt_ε : δ < ε := by
    have hδ_le : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have hδ_lt_t : δ < (t : ℝ) := by
    have hδ_le : δ ≤ (t : ℝ) / 2 := min_le_right _ _
    linarith
  let s : unitInterval :=
    ⟨(t : ℝ) - δ, ⟨by linarith, by
      have ht_le_one : (t : ℝ) ≤ 1 := unitInterval.le_one t
      linarith⟩⟩
  have hslt : (s : ℝ) < (t : ℝ) := by
    dsimp [s]
    linarith
  have hdist_real : dist ((s : ℝ)) ((t : ℝ)) < ε := by
    have hdist_eq : dist ((s : ℝ)) ((t : ℝ)) = δ := by
      rw [dist_comm, Real.dist_eq, abs_of_nonneg]
      · dsimp [s]
        ring
      · dsimp [s]
        linarith
    rw [hdist_eq]
    exact hδ_lt_ε
  have hs_ball : s ∈ Metric.ball t ε := by
    simpa [Metric.mem_ball, Subtype.dist_eq] using hdist_real
  exact ⟨s, hball hs_ball, hslt⟩

private theorem unitInterval_exists_mem_open_gt
    {U : Set unitInterval} (hU : IsOpen U) {t : unitInterval}
    (htU : t ∈ U) (ht_ne_one : t ≠ 1) :
    ∃ s : unitInterval, s ∈ U ∧ (t : ℝ) < (s : ℝ) := by
  rcases Metric.isOpen_iff.mp hU t htU with ⟨ε, hε, hball⟩
  have ht_lt_one_I : t < (1 : unitInterval) :=
    unitInterval.lt_one_iff_ne_one.mpr ht_ne_one
  have ht_lt_one : (t : ℝ) < 1 := by
    rwa [unitInterval.coe_lt_one]
  let δ : ℝ := min (ε / 2) ((1 - (t : ℝ)) / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hε) (half_pos (by linarith))
  have hδ_lt_ε : δ < ε := by
    have hδ_le : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have hδ_lt_one_sub : δ < 1 - (t : ℝ) := by
    have hδ_le : δ ≤ (1 - (t : ℝ)) / 2 := min_le_right _ _
    linarith
  let s : unitInterval :=
    ⟨(t : ℝ) + δ, ⟨by
      have ht_nonneg : 0 ≤ (t : ℝ) := unitInterval.nonneg t
      linarith, by
      linarith⟩⟩
  have htlt_s : (t : ℝ) < (s : ℝ) := by
    dsimp [s]
    linarith
  have hdist_real : dist ((s : ℝ)) ((t : ℝ)) < ε := by
    have hdist_eq : dist ((s : ℝ)) ((t : ℝ)) = δ := by
      rw [Real.dist_eq, abs_of_nonneg]
      · dsimp [s]
        ring
      · dsimp [s]
        linarith
    rw [hdist_eq]
    exact hδ_lt_ε
  have hs_ball : s ∈ Metric.ball t ε := by
    simpa [Metric.mem_ball, Subtype.dist_eq] using hdist_real
  exact ⟨s, hball hs_ball, htlt_s⟩

/--
%%handwave
name:
  First and last expanded-disk hits are not interior hits
statement:
  If the endpoints of a path avoid an expanded closed coordinate disk, then
  the first and last hitting points of that expanded disk do not lie in the
  expanded open disk.
proof:
  If the first hit lay in the open expanded disk, continuity of the path would
  give slightly earlier hitting parameters, contradicting minimality.  The
  endpoint hypothesis rules out the endpoint \(0\).  The last-hit argument is
  the same, using slightly later parameters and the endpoint \(1\).
-/
theorem first_last_expandedClosedDisk_hits_not_mem_expandedOpenDisk [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (_hρ : ρ < D.openDisk.radius)
    {x y : X} (γ : Path x y)
    (hxρ : x ∈ (D.expandedClosedDisk ρ)ᶜ)
    (hyρ : y ∈ (D.expandedClosedDisk ρ)ᶜ)
    {t₀ t₁ : unitInterval}
    (ht₀ : γ t₀ ∈ D.expandedClosedDisk ρ)
    (ht₁ : γ t₁ ∈ D.expandedClosedDisk ρ)
    (ht₀_min : ∀ t : unitInterval,
      γ t ∈ D.expandedClosedDisk ρ → (t₀ : ℝ) ≤ (t : ℝ))
    (ht₁_max : ∀ t : unitInterval,
      γ t ∈ D.expandedClosedDisk ρ → (t : ℝ) ≤ (t₁ : ℝ)) :
    γ t₀ ∉ D.expandedOpenDisk ρ ∧
      γ t₁ ∉ D.expandedOpenDisk ρ := by
  have hpre_open : IsOpen (γ ⁻¹' D.expandedOpenDisk ρ) :=
    (D.expandedOpenDisk_isOpen ρ).preimage γ.continuous
  constructor
  · intro ht₀_open
    have ht₀_ne_zero : t₀ ≠ 0 := by
      intro ht₀_zero
      have hx_hit : x ∈ D.expandedClosedDisk ρ := by
        simpa [ht₀_zero] using ht₀
      exact hxρ hx_hit
    rcases unitInterval_exists_mem_open_lt hpre_open ht₀_open ht₀_ne_zero with
      ⟨s, hs_open, hs_lt⟩
    have hs_closed : γ s ∈ D.expandedClosedDisk ρ :=
      D.expandedOpenDisk_subset_expandedClosedDisk ρ hs_open
    have ht₀_le_s := ht₀_min s hs_closed
    exact (not_lt_of_ge ht₀_le_s) hs_lt
  · intro ht₁_open
    have ht₁_ne_one : t₁ ≠ 1 := by
      intro ht₁_one
      have hy_hit : y ∈ D.expandedClosedDisk ρ := by
        simpa [ht₁_one] using ht₁
      exact hyρ hy_hit
    rcases unitInterval_exists_mem_open_gt hpre_open ht₁_open ht₁_ne_one with
      ⟨s, hs_open, ht₁_lt_s⟩
    have hs_closed : γ s ∈ D.expandedClosedDisk ρ :=
      D.expandedOpenDisk_subset_expandedClosedDisk ρ hs_open
    have hs_le_t₁ := ht₁_max s hs_closed
    exact (not_lt_of_ge hs_le_t₁) ht₁_lt_s

/--
%%handwave
name:
  First and last expanded-disk hits lie on the radius boundary circle
statement:
  If the endpoints of a path avoid an expanded closed coordinate disk, then
  the first and last hitting points of that expanded disk lie on the
  corresponding radius boundary circle.
proof:
  At a first hit, the point cannot be in the interior of the expanded disk:
  otherwise continuity would give slightly earlier hitting times.  The same
  argument applies at the last hit.  Since both points are in the expanded
  closed disk, they therefore have coordinate radius exactly the expanded
  radius.
-/
theorem first_last_expandedClosedDisk_hits_mem_radiusBoundaryCircle [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ : ρ < D.openDisk.radius)
    {x y : X} (γ : Path x y)
    (hxρ : x ∈ (D.expandedClosedDisk ρ)ᶜ)
    (hyρ : y ∈ (D.expandedClosedDisk ρ)ᶜ)
    {t₀ t₁ : unitInterval}
    (ht₀ : γ t₀ ∈ D.expandedClosedDisk ρ)
    (ht₁ : γ t₁ ∈ D.expandedClosedDisk ρ)
    (ht₀_min : ∀ t : unitInterval,
      γ t ∈ D.expandedClosedDisk ρ → (t₀ : ℝ) ≤ (t : ℝ))
    (ht₁_max : ∀ t : unitInterval,
      γ t ∈ D.expandedClosedDisk ρ → (t : ℝ) ≤ (t₁ : ℝ)) :
    γ t₀ ∈ D.radiusBoundaryCircle ρ ∧
      γ t₁ ∈ D.radiusBoundaryCircle ρ := by
  rcases D.first_last_expandedClosedDisk_hits_not_mem_expandedOpenDisk
      hρ γ hxρ hyρ ht₀ ht₁ ht₀_min ht₁_max with
    ⟨ht₀_not_open, ht₁_not_open⟩
  exact
    ⟨D.mem_radiusBoundaryCircle_of_mem_expandedClosedDisk_of_not_mem_expandedOpenDisk
        ht₀ ht₀_not_open,
      D.mem_radiusBoundaryCircle_of_mem_expandedClosedDisk_of_not_mem_expandedOpenDisk
        ht₁ ht₁_not_open⟩

/--
%%handwave
name:
  Euclidean circles are path connected
statement:
  Any two points on a Euclidean circle of positive radius in the complex plane
  are joined by a path inside that circle.
proof:
  Write both points as values of the standard circle parametrization
  \(\theta \mapsto c+\rho e^{i\theta}\).  The straight-line interpolation
  between the two parameters gives a continuous path in the parameter line,
  and composing with the circle parametrization gives an arc in the circle.
-/
theorem complex_sphere_joinedIn
    {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {z w : ℂ}
    (hz : z ∈ Metric.sphere c ρ)
    (hw : w ∈ Metric.sphere c ρ) :
    JoinedIn (Metric.sphere c ρ) z w := by
  have hz_range : z ∈ Set.range (circleMap c ρ) := by
    rw [range_circleMap, abs_of_nonneg hρ.le]
    exact hz
  have hw_range : w ∈ Set.range (circleMap c ρ) := by
    rw [range_circleMap, abs_of_nonneg hρ.le]
    exact hw
  rcases hz_range with ⟨θz, rfl⟩
  rcases hw_range with ⟨θw, rfl⟩
  refine JoinedIn.ofLine
    (f := fun t : ℝ ↦ circleMap c ρ ((1 - t) * θz + t * θw))
    ?_ ?_ ?_ ?_
  · have hparam :
        Continuous (fun t : ℝ ↦ (1 - t) * θz + t * θw) := by
      fun_prop
    exact (continuous_circleMap c ρ).comp_continuousOn hparam.continuousOn
  · ring_nf
  · ring_nf
  · intro z hz_image
    rcases hz_image with ⟨t, _ht, rfl⟩
    exact circleMap_mem_sphere c hρ.le ((1 - t) * θz + t * θw)

/--
%%handwave
name:
  Radius boundary circles are path connected
statement:
  A positive radius boundary circle strictly inside the coordinate disk is
  path connected.
proof:
  The coordinate chart identifies the radius boundary circle with the
  Euclidean circle of radius \(\rho\).  Euclidean circles of positive radius
  are path connected by circular arcs, and the inverse coordinate chart pulls
  those arcs back to the surface.
-/
theorem radiusBoundaryCircle_joinedIn
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρ_pos : 0 < ρ) (hρ_open : ρ < D.openDisk.radius)
    {p q : X}
    (hp : p ∈ D.radiusBoundaryCircle ρ)
    (hq : q ∈ D.radiusBoundaryCircle ρ) :
    JoinedIn (D.radiusBoundaryCircle ρ) p q := by
  have hp' :
      p ∈ D.openDisk.chart.source ∧
        D.openDisk.chart p ∈ Metric.sphere D.openDisk.center ρ := by
    simpa [radiusBoundaryCircle] using hp
  have hq' :
      q ∈ D.openDisk.chart.source ∧
        D.openDisk.chart q ∈ Metric.sphere D.openDisk.center ρ := by
    simpa [radiusBoundaryCircle] using hq
  have hsphere_target :
      Metric.sphere D.openDisk.center ρ ⊆ D.openDisk.chart.target := by
    intro z hz
    apply D.openDisk.ball_subset_target
    rw [Metric.mem_ball]
    have hz_dist : dist z D.openDisk.center = ρ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [hz_dist]
    exact hρ_open
  have harc_chart :
      JoinedIn (Metric.sphere D.openDisk.center ρ)
        (D.openDisk.chart p) (D.openDisk.chart q) :=
    complex_sphere_joinedIn hρ_pos hp'.2 hq'.2
  have hsymm_cont :
      ContinuousOn D.openDisk.chart.symm (Metric.sphere D.openDisk.center ρ) :=
    D.openDisk.chart.continuousOn_symm.mono hsphere_target
  have hmapped :
      JoinedIn
        (D.openDisk.chart.symm '' Metric.sphere D.openDisk.center ρ)
        (D.openDisk.chart.symm (D.openDisk.chart p))
        (D.openDisk.chart.symm (D.openDisk.chart q)) :=
    harc_chart.map_continuousOn hsymm_cont
  have himage_subset :
      D.openDisk.chart.symm '' Metric.sphere D.openDisk.center ρ ⊆
        D.radiusBoundaryCircle ρ := by
    rintro x ⟨z, hz, rfl⟩
    have hz_target : z ∈ D.openDisk.chart.target := hsphere_target hz
    rw [radiusBoundaryCircle]
    exact ⟨D.openDisk.chart.map_target hz_target, by
      simpa [D.openDisk.chart.right_inv hz_target] using hz⟩
  have hmapped_circle :
      JoinedIn (D.radiusBoundaryCircle ρ)
        (D.openDisk.chart.symm (D.openDisk.chart p))
        (D.openDisk.chart.symm (D.openDisk.chart q)) :=
    hmapped.mono himage_subset
  simpa [D.openDisk.chart.left_inv hp'.1, D.openDisk.chart.left_inv hq'.1]
    using hmapped_circle

/--
%%handwave
name:
  Boundary circles of disjoint closed coordinate disks are disjoint
statement:
  If two closed coordinate disks are disjoint, then their boundary circles are
  disjoint.
proof:
  [Each boundary circle lies in its corresponding closed disk](lean:JJMath.Uniformization.ClosedCoordinateDisk.boundaryCircle_subset_carrier), so disjointness of the disk carriers restricts to disjointness of their circles.
-/
theorem disjoint_boundaryCircles_of_disjoint_carriers
    {D E : ClosedCoordinateDisk X}
    (hDE : Disjoint D.carrier E.carrier) :
    Disjoint D.boundaryCircle E.boundaryCircle := by
  refine hDE.mono ?_ ?_
  · exact D.boundaryCircle_subset_carrier
  · exact E.boundaryCircle_subset_carrier

/--
%%handwave
name:
  Thin exterior annulus avoiding another closed coordinate disk
statement:
  If two closed coordinate disks are disjoint, then the first disk has a thin
  exterior annulus, with outer radius still below the ambient coordinate radius,
  that is disjoint from the second disk.
proof:
  Choose a slightly larger closed Euclidean disk inside the same coordinate
  chart.  Its inverse image is compact, and its intersection with the other
  closed coordinate disk is compact.  The coordinate-radius function is
  continuous on this compact intersection.  If the intersection is empty, any
  sufficiently thin annulus works.  Otherwise, disjointness from the original
  closed disk says the minimum coordinate radius on that compact intersection
  is strictly larger than the closed radius, and an intermediate outer radius
  gives the required annulus.
-/
theorem exists_exteriorAnnulusWithOuterRadius_disjoint
    [T2Space X] {D E : ClosedCoordinateDisk X}
    (hDE : Disjoint D.carrier E.carrier) :
    ∃ R : ℝ,
      D.closedRadius < R ∧ R < D.openDisk.radius ∧
        Disjoint (D.exteriorAnnulusWithOuterRadius R) E.carrier := by
  obtain ⟨R₀, hD_R₀, hR₀_open⟩ := exists_between D.closedRadius_lt_openRadius
  let K₀ : Set X :=
    D.openDisk.chart.symm '' Metric.closedBall D.openDisk.center R₀
  have hclosedBall_target :
      Metric.closedBall D.openDisk.center R₀ ⊆ D.openDisk.chart.target := by
    exact (Metric.closedBall_subset_ball hR₀_open).trans
      D.openDisk.ball_subset_target
  have hK₀_eq :
      K₀ =
        D.openDisk.chart.source ∩
          D.openDisk.chart ⁻¹' Metric.closedBall D.openDisk.center R₀ := by
    simpa [K₀] using
      D.openDisk.chart.symm_image_eq_source_inter_preimage hclosedBall_target
  have hK₀_compact : IsCompact K₀ := by
    exact (isCompact_closedBall D.openDisk.center R₀).image_of_continuousOn
      (D.openDisk.chart.continuousOn_symm.mono hclosedBall_target)
  let S : Set X := K₀ ∩ E.carrier
  have hS_compact : IsCompact S := by
    exact hK₀_compact.inter_right E.isClosed
  have hK₀_source : K₀ ⊆ D.openDisk.chart.source := by
    intro x hx
    rw [hK₀_eq] at hx
    exact hx.1
  have hS_source : S ⊆ D.openDisk.chart.source := by
    intro x hx
    exact hK₀_source hx.1
  by_cases hS_empty : S = ∅
  · obtain ⟨R, hD_R, hR_R₀⟩ := exists_between hD_R₀
    refine ⟨R, hD_R, hR_R₀.trans hR₀_open, ?_⟩
    refine Set.disjoint_left.mpr ?_
    intro x hxA hxE
    have hxA' :
        x ∈ D.openDisk.chart.source ∩
          D.openDisk.chart ⁻¹'
            ((fun z : ℂ ↦ dist z D.openDisk.center) ⁻¹'
              Set.Ioo D.closedRadius R) := by
      simpa [exteriorAnnulusWithOuterRadius] using hxA
    have hx_ann :
        D.closedRadius < dist (D.openDisk.chart x) D.openDisk.center ∧
          dist (D.openDisk.chart x) D.openDisk.center < R := by
      simpa [Set.mem_Ioo] using hxA'.2
    have hxK₀ : x ∈ K₀ := by
      rw [hK₀_eq]
      exact ⟨hxA'.1, by
        simpa [Metric.mem_closedBall] using le_of_lt (hx_ann.2.trans hR_R₀)⟩
    have hxS : x ∈ S := ⟨hxK₀, hxE⟩
    rw [hS_empty] at hxS
    exact hxS
  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
    let f : X → ℝ := fun x ↦ dist (D.openDisk.chart x) D.openDisk.center
    have hf_continuous : ContinuousOn f S := by
      have hpair :
          ContinuousOn
            (fun x : X ↦ (D.openDisk.chart x, D.openDisk.center)) S :=
        (D.openDisk.chart.continuousOn.mono hS_source).prodMk continuousOn_const
      simpa [f] using continuous_dist.comp_continuousOn hpair
    obtain ⟨x₀, hx₀S, hx₀_min⟩ :=
      hS_compact.exists_isMinOn hS_nonempty hf_continuous
    have hx₀_dist_gt : D.closedRadius < f x₀ := by
      by_contra hnot
      have hx₀_dist_le : f x₀ ≤ D.closedRadius := le_of_not_gt hnot
      have hx₀D : x₀ ∈ D.carrier := by
        rw [D.carrier_eq]
        exact ⟨hS_source hx₀S, by
          simpa [f, Metric.mem_closedBall] using hx₀_dist_le⟩
      exact (Set.disjoint_left.mp hDE hx₀D) hx₀S.2
    obtain ⟨R, hD_R, hR_min⟩ :=
      exists_between (lt_min hD_R₀ hx₀_dist_gt)
    have hR_R₀ : R < R₀ := hR_min.trans_le (min_le_left R₀ (f x₀))
    have hR_x₀ : R < f x₀ := hR_min.trans_le (min_le_right R₀ (f x₀))
    refine ⟨R, hD_R, hR_R₀.trans hR₀_open, ?_⟩
    refine Set.disjoint_left.mpr ?_
    intro x hxA hxE
    have hxA' :
        x ∈ D.openDisk.chart.source ∩
          D.openDisk.chart ⁻¹'
            ((fun z : ℂ ↦ dist z D.openDisk.center) ⁻¹'
              Set.Ioo D.closedRadius R) := by
      simpa [exteriorAnnulusWithOuterRadius] using hxA
    have hx_ann :
        D.closedRadius < dist (D.openDisk.chart x) D.openDisk.center ∧
          dist (D.openDisk.chart x) D.openDisk.center < R := by
      simpa [Set.mem_Ioo] using hxA'.2
    have hxK₀ : x ∈ K₀ := by
      rw [hK₀_eq]
      exact ⟨hxA'.1, by
        simpa [Metric.mem_closedBall] using le_of_lt (hx_ann.2.trans hR_R₀)⟩
    have hxS : x ∈ S := ⟨hxK₀, hxE⟩
    have hx₀_le_x : f x₀ ≤ f x := hx₀_min hxS
    exact (not_lt_of_ge hx₀_le_x) (hx_ann.2.trans hR_x₀)

/--
%%handwave
name:
  Distinguished boundary point of a closed coordinate disk
statement:
  The positive-real boundary point of a closed coordinate disk is the point
  whose coordinate is the center plus the closed radius on the real axis.
-/
noncomputable def positiveRealBoundaryPoint (D : ClosedCoordinateDisk X) : X :=
  D.openDisk.chart.symm (D.openDisk.center + (D.closedRadius : ℂ))

/--
%%handwave
name:
  The distinguished coordinate point lies in the chart target
statement:
  The coordinate \(c+r\) of the positive-real boundary point lies in the chart
  target.
-/
theorem positiveRealBoundaryPoint_coordinate_mem_target (D : ClosedCoordinateDisk X) :
    D.openDisk.center + (D.closedRadius : ℂ) ∈ D.openDisk.chart.target := by
  apply D.openDisk.ball_subset_target
  rw [Metric.mem_ball]
  have hdist :
      dist (D.openDisk.center + (D.closedRadius : ℂ)) D.openDisk.center =
        D.closedRadius := by
    rw [dist_eq_norm]
    have hsub :
        D.openDisk.center + (D.closedRadius : ℂ) - D.openDisk.center =
          (D.closedRadius : ℂ) := by
      ring
    rw [hsub]
    exact Complex.norm_of_nonneg D.closedRadius_pos.le
  simpa [hdist] using D.closedRadius_lt_openRadius

/--
%%handwave
name:
  The distinguished boundary point lies in the chart source
statement:
  The positive-real boundary point lies in the source of its coordinate chart.
-/
theorem positiveRealBoundaryPoint_mem_source (D : ClosedCoordinateDisk X) :
    D.positiveRealBoundaryPoint ∈ D.openDisk.chart.source := by
  exact D.openDisk.chart.map_target
    (D.positiveRealBoundaryPoint_coordinate_mem_target)

/--
%%handwave
name:
  The distinguished boundary point has the expected coordinate
statement:
  The coordinate of the positive-real boundary point is the center plus the
  closed radius.
-/
theorem chart_positiveRealBoundaryPoint (D : ClosedCoordinateDisk X) :
    D.openDisk.chart D.positiveRealBoundaryPoint =
      D.openDisk.center + (D.closedRadius : ℂ) := by
  exact D.openDisk.chart.right_inv
    (D.positiveRealBoundaryPoint_coordinate_mem_target)

/--
%%handwave
name:
  The distinguished boundary point belongs to the closed coordinate disk
statement:
  The positive-real boundary point is a point of the closed coordinate disk.
proof:
  Its coordinate is \(c+r\), whose distance from \(c\) is \(r\); hence it
  belongs to the defining closed ball and lies in the chart source.
-/
theorem positiveRealBoundaryPoint_mem_carrier (D : ClosedCoordinateDisk X) :
    D.positiveRealBoundaryPoint ∈ D.carrier := by
  rw [D.carrier_eq]
  refine ⟨D.positiveRealBoundaryPoint_mem_source, ?_⟩
  change D.openDisk.chart D.positiveRealBoundaryPoint ∈
    Metric.closedBall D.openDisk.center D.closedRadius
  rw [Metric.mem_closedBall, D.chart_positiveRealBoundaryPoint]
  have hdist :
      dist (D.openDisk.center + (D.closedRadius : ℂ)) D.openDisk.center =
        D.closedRadius := by
    rw [dist_eq_norm]
    have hsub :
        D.openDisk.center + (D.closedRadius : ℂ) - D.openDisk.center =
          (D.closedRadius : ℂ) := by
      ring
    rw [hsub]
    exact Complex.norm_of_nonneg D.closedRadius_pos.le
  exact le_of_eq hdist

/--
%%handwave
name:
  The distinguished boundary point belongs to the boundary circle
statement:
  The positive-real boundary point of a closed coordinate disk is a point of
  its boundary circle.
proof:
  Its coordinate is \(c+r\), so its coordinate distance from \(c\) is
  exactly \(r\), which is the defining equation of the boundary circle.
-/
theorem positiveRealBoundaryPoint_mem_boundaryCircle (D : ClosedCoordinateDisk X) :
    D.positiveRealBoundaryPoint ∈ D.boundaryCircle := by
  rw [boundaryCircle]
  refine ⟨D.positiveRealBoundaryPoint_mem_source, ?_⟩
  change D.openDisk.chart D.positiveRealBoundaryPoint ∈
    Metric.sphere D.openDisk.center D.closedRadius
  rw [Metric.mem_sphere, D.chart_positiveRealBoundaryPoint]
  have hdist :
      dist (D.openDisk.center + (D.closedRadius : ℂ)) D.openDisk.center =
        D.closedRadius := by
    rw [dist_eq_norm]
    have hsub :
        D.openDisk.center + (D.closedRadius : ℂ) - D.openDisk.center =
          (D.closedRadius : ℂ) := by
      ring
    rw [hsub]
    exact Complex.norm_of_nonneg D.closedRadius_pos.le
  exact hdist

end ClosedCoordinateDisk

/--
%%handwave
name:
  Closed coordinate disk from one chart ball
statement:
  If a Euclidean closed ball is strictly contained in a Euclidean ball inside
  the target of a complex chart, then its inverse image is a closed coordinate
  disk.
proof:
  The open coordinate disk is the inverse image of the larger Euclidean ball.
  The closed disk is the inverse image of the smaller closed ball.  Since the
  closed Euclidean ball lies in the chart target, the inverse chart identifies
  the closed coordinate disk with a compact Euclidean closed ball.
-/
noncomputable def closedCoordinateDiskOfChartBall
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (c : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hball_target : Metric.ball c R ⊆ e.target) :
    ClosedCoordinateDisk X := by
  have hR : 0 < R := hr.trans hrR
  let openDisk : CoordinateDisk X :=
    { carrier := e.source ∩ e ⁻¹' Metric.ball c R
      chart := e
      chart_mem_atlas := he
      center := c
      radius := R
      radius_pos := hR
      ball_subset_target := hball_target
      carrier_eq := rfl }
  let carrier : Set X := e.source ∩ e ⁻¹' Metric.closedBall c r
  have hclosed_target : Metric.closedBall c r ⊆ e.target :=
    (Metric.closedBall_subset_ball hrR).trans hball_target
  have hcarrier_eq_image : carrier = e.symm '' Metric.closedBall c r := by
    ext x
    constructor
    · intro hx
      refine ⟨e x, hx.2, ?_⟩
      exact e.left_inv hx.1
    · intro hx
      rcases hx with ⟨z, hz, rfl⟩
      have hz_target : z ∈ e.target := hclosed_target hz
      refine ⟨e.map_target hz_target, ?_⟩
      simpa [e.right_inv hz_target] using hz
  have hcompact : IsCompact carrier := by
    rw [hcarrier_eq_image]
    exact (isCompact_closedBall c r).image_of_continuousOn
      (e.continuousOn_symm.mono hclosed_target)
  exact
    { openDisk := openDisk
      carrier := carrier
      closedRadius := r
      closedRadius_pos := hr
      closedRadius_lt_openRadius := hrR
      carrier_eq := rfl
      compact := hcompact }

/--
%%handwave
name:
  Open neighborhoods contain punctured points
statement:
  Every open neighborhood of a point on a Riemann surface contains
  another point distinct from the original one.
proof:
  Work in a coordinate chart at the point.  The image of the neighborhood is a
  neighborhood of the coordinate point in the plane, so it contains a small
  Euclidean ball.  Move a positive real distance inside that ball and pull the
  resulting point back by the chart.
-/
theorem exists_ne_mem_open_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {N : Set X} {p : X}
    (hN_open : IsOpen N) (hpN : p ∈ N) :
    ∃ q : X, q ∈ N ∧ q ≠ p := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hlocal : N ∩ e.source ∈ 𝓝 p :=
    Filter.inter_mem (hN_open.mem_nhds hpN) (e.open_source.mem_nhds hp_source)
  have himage : e '' (N ∩ e.source) ∈ 𝓝 c := by
    simpa [c] using e.image_mem_nhds hp_source hlocal
  rcases Metric.mem_nhds_iff.mp himage with ⟨R, hRpos, hball_image⟩
  let z : ℂ := c + ((R / 2 : ℝ) : ℂ)
  have hdist_z : dist z c = R / 2 := by
    rw [dist_eq_norm]
    have hsub : z - c = ((R / 2 : ℝ) : ℂ) := by
      dsimp [z]
      ring
    rw [hsub]
    exact Complex.norm_of_nonneg (by linarith)
  have hz_ball : z ∈ Metric.ball c R := by
    rw [Metric.mem_ball, hdist_z]
    linarith
  rcases hball_image hz_ball with ⟨q, hq, hqz⟩
  refine ⟨q, hq.1, ?_⟩
  intro hqp
  have hz_eq_c : z = c := by
    rw [← hqz, hqp]
  have hzero : (0 : ℝ) = R / 2 := by
    simpa [hz_eq_c] using hdist_z
  linarith

/--
%%handwave
name:
  Tiny closed coordinate disk inside an open neighborhood
statement:
  Given a point \(p\), an open neighborhood \(N\), and a second point
  \(q\ne p\), there is a closed coordinate disk containing \(p\), contained in
  \(N\), and avoiding \(q\).
proof:
  In a chart at \(p\), choose a Euclidean ball whose inverse image lies in the
  neighborhood.  If \(q\) lies in the chart, shrink the radius below its
  coordinate distance from \(p\); otherwise every chart-preimage disk already
  avoids \(q\).
-/
theorem exists_closedCoordinateDisk_mem_subset_open_avoids_point
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {N : Set X} {p q : X}
    (hN_open : IsOpen N) (hpN : p ∈ N) (hqp : q ≠ p) :
    ∃ D : ClosedCoordinateDisk X,
      p ∈ D.carrier ∧ D.closedRadius ≤ 1 ∧ D.carrier ⊆ N ∧ q ∉ D.carrier := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ p
  have hlocal : N ∩ e.source ∈ 𝓝 p :=
    Filter.inter_mem (hN_open.mem_nhds hpN) (e.open_source.mem_nhds hp_source)
  have himage : e '' (N ∩ e.source) ∈ 𝓝 c := by
    simpa [c] using e.image_mem_nhds hp_source hlocal
  rcases Metric.mem_nhds_iff.mp himage with ⟨R, hRpos, hball_image⟩
  have hball_target : Metric.ball c R ⊆ e.target := by
    intro z hz
    rcases hball_image hz with ⟨y, hy, hyz⟩
    rw [← hyz]
    exact e.map_source hy.2
  let δq : ℝ := if hqsrc : q ∈ e.source then dist (e q) c else R
  have hδq_pos : 0 < δq := by
    dsimp [δq]
    split_ifs with hqsrc
    · refine dist_pos.mpr ?_
      intro hqchart
      exact hqp (e.injOn hqsrc hp_source hqchart)
    · exact hRpos
  let r : ℝ := min (min R δq) 1 / 2
  have hmin_pos : 0 < min (min R δq) 1 :=
    lt_min (lt_min hRpos hδq_pos) zero_lt_one
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hrR : r < R := by
    have hmin_le : min (min R δq) 1 ≤ R :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp [r]
    linarith
  have hrδq : r < δq := by
    have hmin_le : min (min R δq) 1 ≤ δq :=
      (min_le_left _ _).trans (min_le_right _ _)
    dsimp [r]
    linarith
  have hr_le_one : r ≤ 1 := by
    have hmin_le : min (min R δq) 1 ≤ 1 := min_le_right _ _
    dsimp [r]
    linarith
  let D : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e he c hrpos hrR hball_target
  refine ⟨D, ?_, hr_le_one, ?_, ?_⟩
  · change p ∈ e.source ∩ e ⁻¹' Metric.closedBall c r
    refine ⟨hp_source, ?_⟩
    simpa [c, Metric.mem_closedBall] using hrpos.le
  · intro y hyD
    change y ∈ e.source ∩ e ⁻¹' Metric.closedBall c r at hyD
    have hy_ball : e y ∈ Metric.ball c R := by
      rw [Metric.mem_ball]
      have hydist : dist (e y) c ≤ r := by
        simpa [Metric.mem_closedBall] using hyD.2
      exact lt_of_le_of_lt hydist hrR
    rcases hball_image hy_ball with ⟨x, hx, hxy⟩
    have hxy_eq : x = y := e.injOn hx.2 hyD.1 hxy
    simpa [← hxy_eq] using hx.1
  · intro hqD
    change q ∈ e.source ∩ e ⁻¹' Metric.closedBall c r at hqD
    have hqsrc : q ∈ e.source := hqD.1
    have hqdist : dist (e q) c ≤ r := by
      simpa [Metric.mem_closedBall] using hqD.2
    have hδq_eq : δq = dist (e q) c := by
      simp [δq, hqsrc]
    linarith

/--
%%handwave
name:
  Tiny closed coordinate disk with the base point in its interior
statement:
  Given a point \(p\), an open neighborhood \(N\), and a second point
  \(q\ne p\), there is a closed coordinate disk whose interior contains
  \(p\), whose carrier is contained in \(N\), and whose carrier avoids \(q\).
proof:
  Use the chart-centered disk construction from the ordinary tiny-disk
  theorem, choosing the closed radius smaller than both the available chart
  radius and the coordinate distance to \(q\).  Since the disk is centered at
  \(p\), the corresponding open coordinate disk of the same radius is an open
  neighborhood of \(p\) contained in the closed disk.
-/
theorem exists_closedCoordinateDisk_mem_interior_subset_open_avoids_point
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {N : Set X} {p q : X}
    (hN_open : IsOpen N) (hpN : p ∈ N) (hqp : q ≠ p) :
    ∃ D : ClosedCoordinateDisk X,
      p ∈ interior D.carrier ∧ D.closedRadius ≤ 1 ∧
        D.carrier ⊆ N ∧ q ∉ D.carrier := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ p
  have hlocal : N ∩ e.source ∈ 𝓝 p :=
    Filter.inter_mem (hN_open.mem_nhds hpN) (e.open_source.mem_nhds hp_source)
  have himage : e '' (N ∩ e.source) ∈ 𝓝 c := by
    simpa [c] using e.image_mem_nhds hp_source hlocal
  rcases Metric.mem_nhds_iff.mp himage with ⟨R, hRpos, hball_image⟩
  have hball_target : Metric.ball c R ⊆ e.target := by
    intro z hz
    rcases hball_image hz with ⟨y, hy, hyz⟩
    rw [← hyz]
    exact e.map_source hy.2
  let δq : ℝ := if hqsrc : q ∈ e.source then dist (e q) c else R
  have hδq_pos : 0 < δq := by
    dsimp [δq]
    split_ifs with hqsrc
    · refine dist_pos.mpr ?_
      intro hqchart
      exact hqp (e.injOn hqsrc hp_source hqchart)
    · exact hRpos
  let r : ℝ := min (min R δq) 1 / 2
  have hmin_pos : 0 < min (min R δq) 1 :=
    lt_min (lt_min hRpos hδq_pos) zero_lt_one
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hrR : r < R := by
    have hmin_le : min (min R δq) 1 ≤ R :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp [r]
    linarith
  have hrδq : r < δq := by
    have hmin_le : min (min R δq) 1 ≤ δq :=
      (min_le_left _ _).trans (min_le_right _ _)
    dsimp [r]
    linarith
  have hr_le_one : r ≤ 1 := by
    have hmin_le : min (min R δq) 1 ≤ 1 := min_le_right _ _
    dsimp [r]
    linarith
  let D : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e he c hrpos hrR hball_target
  refine ⟨D, ?_, hr_le_one, ?_, ?_⟩
  · have hopen : IsOpen (D.expandedOpenDisk r) :=
      D.expandedOpenDisk_isOpen r
    have hp_open : p ∈ D.expandedOpenDisk r := by
      change p ∈ e.source ∩ e ⁻¹' Metric.ball c r
      exact ⟨hp_source, by simpa [c, Metric.mem_ball] using hrpos⟩
    have hsubset : D.expandedOpenDisk r ⊆ D.carrier := by
      intro y hy
      change y ∈ e.source ∩ e ⁻¹' Metric.ball c r at hy
      change y ∈ e.source ∩ e ⁻¹' Metric.closedBall c r
      exact ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩
    exact interior_maximal hsubset hopen hp_open
  · intro y hyD
    change y ∈ e.source ∩ e ⁻¹' Metric.closedBall c r at hyD
    have hy_ball : e y ∈ Metric.ball c R := by
      rw [Metric.mem_ball]
      have hydist : dist (e y) c ≤ r := by
        simpa [Metric.mem_closedBall] using hyD.2
      exact lt_of_le_of_lt hydist hrR
    rcases hball_image hy_ball with ⟨x, hx, hxy⟩
    have hxy_eq : x = y := e.injOn hx.2 hyD.1 hxy
    simpa [← hxy_eq] using hx.1
  · intro hqD
    change q ∈ e.source ∩ e ⁻¹' Metric.closedBall c r at hqD
    have hqsrc : q ∈ e.source := hqD.1
    have hqdist : dist (e q) c ≤ r := by
      simpa [Metric.mem_closedBall] using hqD.2
    have hδq_eq : δq = dist (e q) c := by
      simp [δq, hqsrc]
    linarith

/--
%%handwave
name:
  Centered coordinate disks with controlled ambient disk
statement:
  Given a point $p$ in an open set $N$ and a second point $q\ne p$, there is
  a closed coordinate disk centered at $p$ whose ambient open coordinate disk
  lies in $N$, whose closed radius is less than one, and whose carrier avoids
  $q$.
proof:
  In a chart centered at $p$, choose an ambient Euclidean ball whose inverse
  image lies in $N$.  Choose the closed radius smaller than the ambient
  radius, the coordinate distance to $q$ when $q$ lies in the chart, and one.
-/
theorem exists_centered_closedCoordinateDisk_openDisk_subset_open_avoids_point
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {N : Set X} {p q : X}
    (hN_open : IsOpen N) (hpN : p ∈ N) (hqp : q ≠ p) :
    ∃ D : ClosedCoordinateDisk X,
      p ∈ interior D.carrier ∧ D.closedRadius < 1 ∧
        D.openDisk.chart = chartAt ℂ p ∧
        D.openDisk.center = (chartAt ℂ p) p ∧
        D.openDisk.carrier ⊆ N ∧ D.carrier ⊆ N ∧
        q ∉ D.carrier := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ p
  have hlocal : N ∩ e.source ∈ nhds p :=
    Filter.inter_mem (hN_open.mem_nhds hpN) (e.open_source.mem_nhds hp_source)
  have himage : e '' (N ∩ e.source) ∈ nhds c := by
    simpa [c] using e.image_mem_nhds hp_source hlocal
  rcases Metric.mem_nhds_iff.mp himage with ⟨R, hRpos, hball_image⟩
  have hball_target : Metric.ball c R ⊆ e.target := by
    intro z hz
    rcases hball_image hz with ⟨y, hy, rfl⟩
    exact e.map_source hy.2
  let δq : ℝ := if hqsrc : q ∈ e.source then dist (e q) c else R
  have hδq_pos : 0 < δq := by
    dsimp [δq]
    split_ifs with hqsrc
    · refine dist_pos.mpr ?_
      intro hqchart
      exact hqp (e.injOn hqsrc hp_source hqchart)
    · exact hRpos
  let r : ℝ := min (min R δq) 1 / 2
  have hmin_pos : 0 < min (min R δq) 1 :=
    lt_min (lt_min hRpos hδq_pos) zero_lt_one
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hrR : r < R := by
    have hmin_le : min (min R δq) 1 ≤ R :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp [r]
    linarith
  have hrδq : r < δq := by
    have hmin_le : min (min R δq) 1 ≤ δq :=
      (min_le_left _ _).trans (min_le_right _ _)
    dsimp [r]
    linarith
  have hr_one : r < 1 := by
    have hmin_le : min (min R δq) 1 ≤ 1 := min_le_right _ _
    dsimp [r]
    linarith
  let D : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e he c hrpos hrR hball_target
  have hp_interior : p ∈ interior D.carrier := by
    have hopen : IsOpen (D.expandedOpenDisk r) :=
      D.expandedOpenDisk_isOpen r
    have hp_open : p ∈ D.expandedOpenDisk r := by
      change p ∈ e.source ∩ e ⁻¹' Metric.ball c r
      exact ⟨hp_source, by simpa [c, Metric.mem_ball] using hrpos⟩
    have hsubset : D.expandedOpenDisk r ⊆ D.carrier := by
      intro y hy
      change y ∈ e.source ∩ e ⁻¹' Metric.ball c r at hy
      change y ∈ e.source ∩ e ⁻¹' Metric.closedBall c r
      exact ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩
    exact interior_maximal hsubset hopen hp_open
  have hopen_subset : D.openDisk.carrier ⊆ N := by
    intro y hy
    change y ∈ e.source ∩ e ⁻¹' Metric.ball c R at hy
    rcases hball_image hy.2 with ⟨x, hx, hxy⟩
    have hxy_eq : x = y := e.injOn hx.2 hy.1 hxy
    simpa [← hxy_eq] using hx.1
  have hcarrier_subset : D.carrier ⊆ N :=
    D.subset_openDisk.trans hopen_subset
  have hq_avoid : q ∉ D.carrier := by
    intro hqD
    change q ∈ e.source ∩ e ⁻¹' Metric.closedBall c r at hqD
    have hqdist : dist (e q) c ≤ r := by
      simpa [Metric.mem_closedBall] using hqD.2
    have hδq_eq : δq = dist (e q) c := by
      simp [δq, hqD.1]
    linarith
  refine ⟨D, hp_interior, hr_one, ?_, ?_, hopen_subset,
    hcarrier_subset, hq_avoid⟩
  · rfl
  · rfl

/--
%%handwave
name:
  Two disjoint closed coordinate disks exist
statement:
  Every Riemann surface contains two disjoint closed coordinate
  disks.
proof:
  Work in one coordinate chart.  Choose a Euclidean ball inside the chart
  target, then take two much smaller closed Euclidean disks whose centers are
  separated along the real axis.  Their inverse images under the chart are
  closed coordinate disks, and chart injectivity transfers Euclidean
  disjointness to the surface.
-/
theorem exists_disjoint_closedCoordinateDisks
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    ∃ D0 D1 : ClosedCoordinateDisk X,
      Disjoint D0.carrier D1.carrier := by
  classical
  let p : X := Classical.choice (PathConnectedSpace.nonempty : Nonempty X)
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let z : ℂ := e p
  have hz_target : z ∈ e.target := by
    simp [e, z, mem_chart_target ℂ p]
  rcases Metric.isOpen_iff.mp e.open_target z hz_target with
    ⟨R, hRpos, hball_target⟩
  let ρ : ℝ := R / 16
  let σ : ℝ := R / 8
  let c0 : ℂ := z
  let c1 : ℂ := z + ((R / 2 : ℝ) : ℂ)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρσ : ρ < σ := by
    dsimp [ρ, σ]
    linarith
  have hσpos : 0 < σ := hρpos.trans hρσ
  have hball0_target : Metric.ball c0 σ ⊆ e.target := by
    intro w hw
    exact hball_target (Metric.ball_subset_ball (by
      dsimp [c0, σ]
      linarith) hw)
  have hdist_c1_z : dist c1 z = R / 2 := by
    rw [dist_eq_norm]
    have hsub : c1 - z = ((R / 2 : ℝ) : ℂ) := by
      dsimp [c1]
      ring
    rw [hsub]
    exact Complex.norm_of_nonneg (by linarith)
  have hball1_target : Metric.ball c1 σ ⊆ e.target := by
    exact (Metric.ball_subset_ball' (x := c1) (y := z) (ε₁ := σ) (ε₂ := R)
      (by
        rw [hdist_c1_z]
        dsimp [σ]
        linarith)).trans hball_target
  let D0 : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e (by simp [e, chart_mem_atlas ℂ p])
      c0 hρpos hρσ hball0_target
  let D1 : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e (by simp [e, chart_mem_atlas ℂ p])
      c1 hρpos hρσ hball1_target
  have hdist_centers : ρ + ρ < dist c0 c1 := by
    have hdist : dist c0 c1 = R / 2 := by
      rw [dist_eq_norm]
      have hsub : c0 - c1 = -((R / 2 : ℝ) : ℂ) := by
        dsimp [c0, c1]
        ring
      rw [hsub, norm_neg]
      exact Complex.norm_of_nonneg (by linarith)
    rw [hdist]
    dsimp [ρ]
    linarith
  have hclosed_disjoint :
      Disjoint (Metric.closedBall c0 ρ) (Metric.closedBall c1 ρ) :=
    Metric.closedBall_disjoint_closedBall hdist_centers
  have hdisj : Disjoint D0.carrier D1.carrier := by
    refine Set.disjoint_left.mpr ?_
    intro x hx0 hx1
    have hx0' : x ∈ e.source ∩ e ⁻¹' Metric.closedBall c0 ρ := by
      simpa [D0, closedCoordinateDiskOfChartBall] using hx0
    have hx1' : x ∈ e.source ∩ e ⁻¹' Metric.closedBall c1 ρ := by
      simpa [D1, closedCoordinateDiskOfChartBall] using hx1
    exact (Set.disjoint_left.mp hclosed_disjoint) hx0'.2 hx1'.2
  exact ⟨D0, D1, hdisj⟩

/--
%%handwave
name:
  Compact disk complements are nonempty in noncompact surfaces
statement:
  In a noncompact surface, the complement of the union of two closed
  coordinate disks is nonempty.
proof:
  Each closed coordinate disk is compact, so their union is compact.  If the
  complement were empty, this compact union would be the whole space,
  contradicting noncompactness.
-/
theorem closedCoordinateDisks_complement_nonempty_of_noncompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [NoncompactSpace X]
    (D0 D1 : ClosedCoordinateDisk X) :
    ((D0.carrier ∪ D1.carrier)ᶜ : Set X).Nonempty := by
  have hcompact : IsCompact (D0.carrier ∪ D1.carrier) :=
    D0.compact.union D1.compact
  have hne_univ : D0.carrier ∪ D1.carrier ≠ Set.univ :=
    hcompact.ne_univ
  by_contra hnonempty
  have hcompl_empty : ((D0.carrier ∪ D1.carrier)ᶜ : Set X) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hnonempty
  apply hne_univ
  refine Set.eq_univ_iff_forall.mpr ?_
  intro x
  by_contra hx
  have hx_compl : x ∈ ((D0.carrier ∪ D1.carrier)ᶜ : Set X) := hx
  rw [hcompl_empty] at hx_compl
  exact hx_compl

/-- Pairwise path-joinability inside a set implies preconnectedness. -/
theorem isPreconnected_of_forall_joinedIn
    {X : Type} [TopologicalSpace X] {s : Set X}
    (h : ∀ x ∈ s, ∀ y ∈ s, JoinedIn s x y) :
    IsPreconnected s := by
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  let γ : Path x y := (h x hx y hy).somePath
  refine ⟨Set.range γ, ?_, γ.source_mem_range, γ.target_mem_range, ?_⟩
  · intro z hz
    rcases hz with ⟨t, rfl⟩
    exact (h x hx y hy).somePath_mem t
  · exact (isConnected_range γ.continuous).isPreconnected

/--
%%handwave
name:
  Points on a Riemann surface are joined by paths
statement:
  Any two points on a Riemann surface are joined by a path.
proof:
  This is part of the standing meaning of a Riemann surface in this
  development: the class includes path connectedness.
-/
theorem riemannSurface_joined
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x y : X) :
    Joined x y :=
  PathConnectedSpace.joined x y

/--
%%handwave
name:
  Path surgery using a boundary-circle arc
statement:
  Suppose a path meets an expanded closed coordinate disk first at \(t_0\)
  and last at \(t_1\), and suppose the two hitting points are joined by an arc
  in the corresponding radius boundary circle.  Then replacing the middle
  part of the path by that arc gives a path with the same endpoints that
  avoids the original closed coordinate disk.
proof:
  Before \(t_0\) and after \(t_1\), the path avoids the expanded closed disk by
  the defining minimality and maximality of the hitting times.  Since the
  original closed disk lies inside the expanded disk, these outside pieces
  avoid the original disk.  The replacement arc avoids the original disk
  because it lies on a larger radius boundary circle.  Concatenating the three
  pieces gives the required path.
-/
theorem path_surgery_off_closedCoordinateDisk_from_boundaryCircle_arc
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρD : D.closedRadius < ρ)
    {x y : X}
    (γ : Path x y)
    {t₀ t₁ : unitInterval}
    (_ht₀ : γ t₀ ∈ D.expandedClosedDisk ρ)
    (_ht₁ : γ t₁ ∈ D.expandedClosedDisk ρ)
    (ht₀_min : ∀ t : unitInterval,
      γ t ∈ D.expandedClosedDisk ρ → (t₀ : ℝ) ≤ (t : ℝ))
    (ht₁_max : ∀ t : unitInterval,
      γ t ∈ D.expandedClosedDisk ρ → (t : ℝ) ≤ (t₁ : ℝ))
    (harc : JoinedIn (D.radiusBoundaryCircle ρ) (γ t₀) (γ t₁)) :
    ∃ η : Path x y, ∀ t, η t ∈ D.carrierᶜ := by
  have hcircle_compl : D.radiusBoundaryCircle ρ ⊆ D.carrierᶜ :=
    D.radiusBoundaryCircle_subset_compl_carrier hρD
  have hleft_range :
      Set.range (γ.subpath (0 : unitInterval) t₀) ⊆ D.carrierᶜ := by
    rw [Path.range_subpath_of_le γ (0 : unitInterval) t₀ unitInterval.nonneg']
    rintro z ⟨s, hs, rfl⟩
    intro hcar
    have hs_expanded : γ s ∈ D.expandedClosedDisk ρ :=
      D.carrier_subset_expandedClosedDisk hρD.le hcar
    have ht₀_le_s : (t₀ : ℝ) ≤ (s : ℝ) := ht₀_min s hs_expanded
    have hs_le_t₀ : (s : ℝ) ≤ (t₀ : ℝ) := by
      exact_mod_cast hs.2
    have hs_eq : s = t₀ := Subtype.ext (le_antisymm hs_le_t₀ ht₀_le_s)
    have ht₀_compl : γ t₀ ∈ D.carrierᶜ :=
      hcircle_compl harc.source_mem
    exact ht₀_compl (by simpa [hs_eq] using hcar)
  have hright_range :
      Set.range (γ.subpath t₁ (1 : unitInterval)) ⊆ D.carrierᶜ := by
    rw [Path.range_subpath_of_le γ t₁ (1 : unitInterval) unitInterval.le_one']
    rintro z ⟨s, hs, rfl⟩
    intro hcar
    have hs_expanded : γ s ∈ D.expandedClosedDisk ρ :=
      D.carrier_subset_expandedClosedDisk hρD.le hcar
    have hs_le_t₁ : (s : ℝ) ≤ (t₁ : ℝ) := ht₁_max s hs_expanded
    have ht₁_le_s : (t₁ : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs.1
    have hs_eq : s = t₁ := Subtype.ext (le_antisymm hs_le_t₁ ht₁_le_s)
    have ht₁_compl : γ t₁ ∈ D.carrierᶜ :=
      hcircle_compl harc.target_mem
    exact ht₁_compl (by simpa [hs_eq] using hcar)
  let left : Path x (γ t₀) :=
    (γ.subpath (0 : unitInterval) t₀).cast γ.source.symm rfl
  let middle : Path (γ t₀) (γ t₁) := harc.somePath
  let right : Path (γ t₁) y :=
    (γ.subpath t₁ (1 : unitInterval)).cast rfl γ.target.symm
  let η : Path x y := (left.trans middle).trans right
  refine ⟨η, ?_⟩
  intro t
  have ht_range : η t ∈ Set.range η := ⟨t, rfl⟩
  dsimp [η] at ht_range
  rw [Path.trans_range, Path.trans_range] at ht_range
  rcases ht_range with (hleft | hmiddle) | hright
  · rcases hleft with ⟨s, hs⟩
    rw [← hs]
    have hs' : (γ.subpath (0 : unitInterval) t₀) s ∈ D.carrierᶜ :=
      hleft_range ⟨s, rfl⟩
    simpa [left] using hs'
  · rcases hmiddle with ⟨s, hs⟩
    rw [← hs]
    exact hcircle_compl (harc.somePath_mem s)
  · rcases hright with ⟨s, hs⟩
    rw [← hs]
    have hs' : (γ.subpath t₁ (1 : unitInterval)) s ∈ D.carrierᶜ :=
      hright_range ⟨s, rfl⟩
    simpa [right] using hs'

/--
%%handwave
name:
  Paths can be pushed off one closed coordinate disk at a fixed expanded radius when they hit
statement:
  Suppose the endpoints of a path avoid an expanded closed coordinate disk
  whose radius is larger than the removed closed disk and still lies in the
  ambient coordinate disk.  If the path meets the expanded disk, then it can
  be replaced by a path with the same endpoints that avoids the original
  closed coordinate disk.
proof:
  Use
  [the first and last hitting times](lean:JJMath.Uniformization.ClosedCoordinateDisk.exists_first_last_expandedClosedDisk_hit)
  of the expanded disk.  By
  [the endpoint-avoiding first/last-hit argument](lean:JJMath.Uniformization.ClosedCoordinateDisk.first_last_expandedClosedDisk_hits_mem_radiusBoundaryCircle),
  the corresponding points lie on the radius boundary circle.  Join these two
  points inside that circle by
  [a circular arc in the coordinate chart](lean:JJMath.Uniformization.ClosedCoordinateDisk.radiusBoundaryCircle_joinedIn),
  and replace the intervening part of the original path by this arc.  The
  circular arc lies outside the original closed coordinate disk because
  [larger radius boundary circles avoid the closed coordinate disk](lean:JJMath.Uniformization.ClosedCoordinateDisk.radiusBoundaryCircle_subset_compl_carrier).
-/
theorem path_can_be_pushed_off_closedCoordinateDisk_with_expandedRadius_when_hits
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρD : D.closedRadius < ρ)
    (hρ_open : ρ < D.openDisk.radius)
    {x y : X}
    (γ : Path x y)
    (hxρ : x ∈ (D.expandedClosedDisk ρ)ᶜ)
    (hyρ : y ∈ (D.expandedClosedDisk ρ)ᶜ)
    (hhit : ∃ t : unitInterval, γ t ∈ D.expandedClosedDisk ρ) :
    ∃ η : Path x y, ∀ t, η t ∈ D.carrierᶜ := by
  rcases D.exists_first_last_expandedClosedDisk_hit hρ_open γ hhit with
    ⟨t₀, t₁, ht₀, ht₁, ht₀_min, ht₁_max⟩
  rcases D.first_last_expandedClosedDisk_hits_mem_radiusBoundaryCircle hρ_open
      γ hxρ hyρ ht₀ ht₁ ht₀_min ht₁_max with
    ⟨ht₀_circle, ht₁_circle⟩
  have hρ_pos : 0 < ρ := D.closedRadius_pos.trans hρD
  have harc : JoinedIn (D.radiusBoundaryCircle ρ) (γ t₀) (γ t₁) :=
    D.radiusBoundaryCircle_joinedIn hρ_pos hρ_open ht₀_circle ht₁_circle
  exact path_surgery_off_closedCoordinateDisk_from_boundaryCircle_arc
    D hρD γ ht₀ ht₁ ht₀_min ht₁_max harc

/--
%%handwave
name:
  Paths can be pushed off one closed coordinate disk at a fixed expanded radius
statement:
  Suppose the endpoints of a path avoid an expanded closed coordinate disk
  whose radius is larger than the removed closed disk and still lies in the
  ambient coordinate disk.  Then the path can be replaced by another path
  with the same endpoints that avoids the original closed coordinate disk.
proof:
  If the path never meets the expanded disk, keep it; avoiding the expanded
  disk implies avoiding the original disk because
  [the original closed disk lies in the expanded one](lean:JJMath.Uniformization.ClosedCoordinateDisk.compl_expandedClosedDisk_subset_compl_carrier).
  If the path does meet the expanded disk, use
  [the one-disk replacement at this radius](lean:JJMath.Uniformization.path_can_be_pushed_off_closedCoordinateDisk_with_expandedRadius_when_hits).
-/
theorem path_can_be_pushed_off_closedCoordinateDisk_with_expandedRadius
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D : ClosedCoordinateDisk X) {ρ : ℝ}
    (hρD : D.closedRadius < ρ)
    (hρ_open : ρ < D.openDisk.radius)
    {x y : X}
    (γ : Path x y)
    (hxρ : x ∈ (D.expandedClosedDisk ρ)ᶜ)
    (hyρ : y ∈ (D.expandedClosedDisk ρ)ᶜ) :
    ∃ η : Path x y, ∀ t, η t ∈ D.carrierᶜ := by
  by_cases hhit : ∃ t : unitInterval, γ t ∈ D.expandedClosedDisk ρ
  · exact
      path_can_be_pushed_off_closedCoordinateDisk_with_expandedRadius_when_hits
        D hρD hρ_open γ hxρ hyρ hhit
  · refine ⟨γ, ?_⟩
    intro t
    exact D.compl_expandedClosedDisk_subset_compl_carrier hρD.le
      (by
        intro ht
        exact hhit ⟨t, ht⟩)

/--
%%handwave
name:
  Paths can be pushed off one closed coordinate disk
statement:
  If a path starts and ends outside a closed coordinate disk, then it can be
  replaced by another path with the same endpoints whose image stays outside
  the disk.
proof:
  Choose an expanded closed coordinate disk whose radius is still below the
  ambient coordinate radius and whose expanded closed disk still misses the
  endpoints; this uses
  [an intermediate expanded radius below the endpoint coordinate
  radii](lean:JJMath.Uniformization.ClosedCoordinateDisk.exists_expandedRadius_lt_outerRadius_avoids_points).
  If the path does not meet this expanded disk, keep the path.  Otherwise,
  compactness of the inverse image of the expanded disk gives a first and last
  hitting time.  The corresponding points lie on the expanded radius boundary
  circle.  Replace the intervening segment by the circular arc in that radius
  boundary circle.  Since this radius is larger than the original closed radius,
  [the circle avoids the original closed coordinate
  disk](lean:JJMath.Uniformization.ClosedCoordinateDisk.radiusBoundaryCircle_subset_compl_carrier).
-/
theorem path_can_be_pushed_off_closedCoordinateDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D : ClosedCoordinateDisk X)
    {x y : X}
    (γ : Path x y)
    (_hx : x ∈ D.carrierᶜ)
    (_hy : y ∈ D.carrierᶜ) :
    ∃ η : Path x y, ∀ t, η t ∈ D.carrierᶜ := by
  rcases D.exists_expandedRadius_lt_outerRadius_avoids_points
      D.closedRadius_lt_openRadius _hx _hy with
    ⟨ρ, hρD, hρ_open, hxρ, hyρ⟩
  exact path_can_be_pushed_off_closedCoordinateDisk_with_expandedRadius
    D hρD hρ_open γ hxρ hyρ

/--
%%handwave
name:
  Points outside one closed coordinate disk can be joined outside it
statement:
  Any two points outside a closed coordinate disk in a connected Riemann
  surface can be joined by a path that avoids the disk.
proof:
  Join the points by an arbitrary surface path and push that path off the
  closed coordinate disk.
-/
theorem closedCoordinateDisk_complement_joinedIn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : ClosedCoordinateDisk X) {x y : X}
    (hx : x ∈ D.carrierᶜ) (hy : y ∈ D.carrierᶜ) :
    JoinedIn D.carrierᶜ x y := by
  let γ : Path x y := (riemannSurface_joined x y).somePath
  rcases path_can_be_pushed_off_closedCoordinateDisk D γ hx hy with
    ⟨η, hη⟩
  exact ⟨η, hη⟩

/--
%%handwave
name:
  The complement of one closed coordinate disk is connected
statement:
  The complement of a closed coordinate disk in a Riemann surface
  is preconnected.
proof:
  Every pair of points in the complement can be joined by a path staying in
  the complement.
-/
theorem closedCoordinateDisk_complement_preconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : ClosedCoordinateDisk X) :
    IsPreconnected D.carrierᶜ := by
  exact isPreconnected_of_forall_joinedIn
    (fun x hx y hy ↦
      closedCoordinateDisk_complement_joinedIn D hx hy)

/--
%%handwave
name:
  Coordinate-disk path surgery preserves an ambient region
statement:
  Let a path lie in a set containing the ambient open coordinate disk of a
  closed coordinate disk.  If its endpoints avoid the closed disk, the path
  can be replaced by one which both avoids the closed disk and remains in the
  original set.
proof:
  Choose a slightly expanded coordinate circle that still misses the two
  endpoints.  If the path misses the expanded disk, leave it unchanged.
  Otherwise replace the portion between the first and last hits by an arc on
  the expanded circle.  The unchanged portions remain in the original set,
  while the new arc lies in the ambient open coordinate disk and hence also
  in that set.
-/
theorem path_can_be_pushed_off_closedCoordinateDisk_preserving_set
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D : ClosedCoordinateDisk X) (S : Set X)
    (hopenDiskS : D.openDisk.carrier ⊆ S)
    {x y : X}
    (γ : Path x y)
    (hγS : ∀ t, γ t ∈ S)
    (hx : x ∈ D.carrierᶜ)
    (hy : y ∈ D.carrierᶜ) :
    ∃ η : Path x y,
      (∀ t, η t ∈ D.carrierᶜ) ∧ (∀ t, η t ∈ S) := by
  rcases D.exists_expandedRadius_lt_outerRadius_avoids_points
      D.closedRadius_lt_openRadius hx hy with
    ⟨ρ, hρD, hρ_open, hxρ, hyρ⟩
  by_cases hhit : ∃ t : unitInterval, γ t ∈ D.expandedClosedDisk ρ
  · rcases D.exists_first_last_expandedClosedDisk_hit hρ_open γ hhit with
      ⟨t₀, t₁, ht₀, ht₁, ht₀_min, ht₁_max⟩
    rcases D.first_last_expandedClosedDisk_hits_mem_radiusBoundaryCircle
        hρ_open γ hxρ hyρ ht₀ ht₁ ht₀_min ht₁_max with
      ⟨ht₀_circle, ht₁_circle⟩
    have hρ_pos : 0 < ρ := D.closedRadius_pos.trans hρD
    have harc : JoinedIn (D.radiusBoundaryCircle ρ) (γ t₀) (γ t₁) :=
      D.radiusBoundaryCircle_joinedIn hρ_pos hρ_open ht₀_circle ht₁_circle
    have hcircle_D : D.radiusBoundaryCircle ρ ⊆ D.carrierᶜ :=
      D.radiusBoundaryCircle_subset_compl_carrier hρD
    have hcircle_S : D.radiusBoundaryCircle ρ ⊆ S := by
      intro z hz
      apply hopenDiskS
      rw [D.openDisk.carrier_eq]
      refine ⟨hz.1, ?_⟩
      have hzdist :
          dist (D.openDisk.chart z) D.openDisk.center = ρ := by
        simpa [ClosedCoordinateDisk.radiusBoundaryCircle,
          Metric.mem_sphere, dist_eq_norm] using hz.2
      simpa [Metric.mem_ball, hzdist] using hρ_open
    have hleft_range_D :
        Set.range (γ.subpath (0 : unitInterval) t₀) ⊆ D.carrierᶜ := by
      rw [Path.range_subpath_of_le γ (0 : unitInterval) t₀
        unitInterval.nonneg']
      rintro z ⟨s, hs, rfl⟩
      intro hcar
      have hs_expanded : γ s ∈ D.expandedClosedDisk ρ :=
        D.carrier_subset_expandedClosedDisk hρD.le hcar
      have ht₀_le_s : (t₀ : ℝ) ≤ (s : ℝ) := ht₀_min s hs_expanded
      have hs_le_t₀ : (s : ℝ) ≤ (t₀ : ℝ) := by
        exact_mod_cast hs.2
      have hs_eq : s = t₀ :=
        Subtype.ext (le_antisymm hs_le_t₀ ht₀_le_s)
      have ht₀_compl : γ t₀ ∈ D.carrierᶜ :=
        hcircle_D harc.source_mem
      exact ht₀_compl (by simpa [hs_eq] using hcar)
    have hright_range_D :
        Set.range (γ.subpath t₁ (1 : unitInterval)) ⊆ D.carrierᶜ := by
      rw [Path.range_subpath_of_le γ t₁ (1 : unitInterval)
        unitInterval.le_one']
      rintro z ⟨s, hs, rfl⟩
      intro hcar
      have hs_expanded : γ s ∈ D.expandedClosedDisk ρ :=
        D.carrier_subset_expandedClosedDisk hρD.le hcar
      have hs_le_t₁ : (s : ℝ) ≤ (t₁ : ℝ) := ht₁_max s hs_expanded
      have ht₁_le_s : (t₁ : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast hs.1
      have hs_eq : s = t₁ :=
        Subtype.ext (le_antisymm hs_le_t₁ ht₁_le_s)
      have ht₁_compl : γ t₁ ∈ D.carrierᶜ :=
        hcircle_D harc.target_mem
      exact ht₁_compl (by simpa [hs_eq] using hcar)
    have hleft_range_S :
        Set.range (γ.subpath (0 : unitInterval) t₀) ⊆ S := by
      rw [Path.range_subpath_of_le γ (0 : unitInterval) t₀
        unitInterval.nonneg']
      rintro z ⟨s, _hs, rfl⟩
      exact hγS s
    have hright_range_S :
        Set.range (γ.subpath t₁ (1 : unitInterval)) ⊆ S := by
      rw [Path.range_subpath_of_le γ t₁ (1 : unitInterval)
        unitInterval.le_one']
      rintro z ⟨s, _hs, rfl⟩
      exact hγS s
    let left : Path x (γ t₀) :=
      (γ.subpath (0 : unitInterval) t₀).cast γ.source.symm rfl
    let middle : Path (γ t₀) (γ t₁) := harc.somePath
    let right : Path (γ t₁) y :=
      (γ.subpath t₁ (1 : unitInterval)).cast rfl γ.target.symm
    let η : Path x y := (left.trans middle).trans right
    refine ⟨η, ?_, ?_⟩
    · intro t
      have ht_range : η t ∈ Set.range η := ⟨t, rfl⟩
      dsimp [η] at ht_range
      rw [Path.trans_range, Path.trans_range] at ht_range
      rcases ht_range with (hleft | hmiddle) | hright
      · rcases hleft with ⟨s, hs⟩
        rw [← hs]
        have hs' :
            (γ.subpath (0 : unitInterval) t₀) s ∈ D.carrierᶜ :=
          hleft_range_D ⟨s, rfl⟩
        simpa [left] using hs'
      · rcases hmiddle with ⟨s, hs⟩
        rw [← hs]
        exact hcircle_D (harc.somePath_mem s)
      · rcases hright with ⟨s, hs⟩
        rw [← hs]
        have hs' : (γ.subpath t₁ (1 : unitInterval)) s ∈ D.carrierᶜ :=
          hright_range_D ⟨s, rfl⟩
        simpa [right] using hs'
    · intro t
      have ht_range : η t ∈ Set.range η := ⟨t, rfl⟩
      dsimp [η] at ht_range
      rw [Path.trans_range, Path.trans_range] at ht_range
      rcases ht_range with (hleft | hmiddle) | hright
      · rcases hleft with ⟨s, hs⟩
        rw [← hs]
        have hs' : (γ.subpath (0 : unitInterval) t₀) s ∈ S :=
          hleft_range_S ⟨s, rfl⟩
        simpa [left] using hs'
      · rcases hmiddle with ⟨s, hs⟩
        rw [← hs]
        exact hcircle_S (harc.somePath_mem s)
      · rcases hright with ⟨s, hs⟩
        rw [← hs]
        have hs' : (γ.subpath t₁ (1 : unitInterval)) s ∈ S :=
          hright_range_S ⟨s, rfl⟩
        simpa [right] using hs'
  · refine ⟨γ, ?_, hγS⟩
    intro t
    exact D.compl_expandedClosedDisk_subset_compl_carrier hρD.le
      (by
        intro ht
        exact hhit ⟨t, ht⟩)

/--
%%handwave
name:
  Removing a coordinate disk preserves connectedness inside an ambient region
statement:
  Suppose every two points of a set can be joined by a path in that set and
  the set contains the ambient open coordinate disk of a closed coordinate
  disk.  Then the set with the closed disk removed is connected.
proof:
  Join two points before removing the disk and apply coordinate-disk path
  surgery while preserving the ambient set.  The resulting path joins the
  same points inside the set with the closed disk removed.
-/
theorem isPreconnected_diff_closedCoordinateDisk_of_forall_joinedIn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D : ClosedCoordinateDisk X) (S : Set X)
    (hopenDiskS : D.openDisk.carrier ⊆ S)
    (hjoined : ∀ x ∈ S, ∀ y ∈ S, JoinedIn S x y) :
    IsPreconnected (S \ D.carrier) := by
  apply isPreconnected_of_forall_joinedIn
  intro x hx y hy
  let γ : Path x y := (hjoined x hx.1 y hy.1).somePath
  have hγS : ∀ t, γ t ∈ S :=
    (hjoined x hx.1 y hy.1).somePath_mem
  rcases path_can_be_pushed_off_closedCoordinateDisk_preserving_set
      D S hopenDiskS γ hγS (by simpa using hx.2) (by simpa using hy.2) with
    ⟨η, hηD, hηS⟩
  exact ⟨η, fun t ↦ ⟨hηS t, by simpa using hηD t⟩⟩

/--
%%handwave
name:
  Path surgery using a boundary-circle arc while preserving another disk
statement:
  In the one-disk surgery, if the replacement radius boundary circle lies in
  an exterior annulus disjoint from a second closed coordinate disk, and the
  original path avoided that second disk, then the surgically modified path
  avoids both disks.
proof:
  The parts of the path left unchanged avoid the second disk by hypothesis.
  The replacement arc lies in the radius boundary circle, hence in the chosen
  exterior annulus, and this annulus is disjoint from the second disk.
-/
theorem path_surgery_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk_from_boundaryCircle_arc
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D E : ClosedCoordinateDisk X) {ρ R : ℝ}
    (hρD : D.closedRadius < ρ)
    (hρR : ρ < R)
    (hAnnE : Disjoint (D.exteriorAnnulusWithOuterRadius R) E.carrier)
    {x y : X}
    (γ : Path x y)
    (hγE : ∀ t, γ t ∈ E.carrierᶜ)
    {t₀ t₁ : unitInterval}
    (_ht₀ : γ t₀ ∈ D.expandedClosedDisk ρ)
    (_ht₁ : γ t₁ ∈ D.expandedClosedDisk ρ)
    (ht₀_min : ∀ t : unitInterval,
      γ t ∈ D.expandedClosedDisk ρ → (t₀ : ℝ) ≤ (t : ℝ))
    (ht₁_max : ∀ t : unitInterval,
      γ t ∈ D.expandedClosedDisk ρ → (t : ℝ) ≤ (t₁ : ℝ))
    (harc : JoinedIn (D.radiusBoundaryCircle ρ) (γ t₀) (γ t₁)) :
    ∃ η : Path x y,
      (∀ t, η t ∈ D.carrierᶜ) ∧
        (∀ t, η t ∈ E.carrierᶜ) := by
  have hcircle_D : D.radiusBoundaryCircle ρ ⊆ D.carrierᶜ :=
    D.radiusBoundaryCircle_subset_compl_carrier hρD
  have hcircle_E : D.radiusBoundaryCircle ρ ⊆ E.carrierᶜ := by
    intro z hz hzE
    have hz_ann : z ∈ D.exteriorAnnulusWithOuterRadius R :=
      D.radiusBoundaryCircle_subset_exteriorAnnulusWithOuterRadius hρD hρR hz
    exact (Set.disjoint_left.mp hAnnE hz_ann) hzE
  have hleft_range_D :
      Set.range (γ.subpath (0 : unitInterval) t₀) ⊆ D.carrierᶜ := by
    rw [Path.range_subpath_of_le γ (0 : unitInterval) t₀ unitInterval.nonneg']
    rintro z ⟨s, hs, rfl⟩
    intro hcar
    have hs_expanded : γ s ∈ D.expandedClosedDisk ρ :=
      D.carrier_subset_expandedClosedDisk hρD.le hcar
    have ht₀_le_s : (t₀ : ℝ) ≤ (s : ℝ) := ht₀_min s hs_expanded
    have hs_le_t₀ : (s : ℝ) ≤ (t₀ : ℝ) := by
      exact_mod_cast hs.2
    have hs_eq : s = t₀ := Subtype.ext (le_antisymm hs_le_t₀ ht₀_le_s)
    have ht₀_compl : γ t₀ ∈ D.carrierᶜ :=
      hcircle_D harc.source_mem
    exact ht₀_compl (by simpa [hs_eq] using hcar)
  have hright_range_D :
      Set.range (γ.subpath t₁ (1 : unitInterval)) ⊆ D.carrierᶜ := by
    rw [Path.range_subpath_of_le γ t₁ (1 : unitInterval) unitInterval.le_one']
    rintro z ⟨s, hs, rfl⟩
    intro hcar
    have hs_expanded : γ s ∈ D.expandedClosedDisk ρ :=
      D.carrier_subset_expandedClosedDisk hρD.le hcar
    have hs_le_t₁ : (s : ℝ) ≤ (t₁ : ℝ) := ht₁_max s hs_expanded
    have ht₁_le_s : (t₁ : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs.1
    have hs_eq : s = t₁ := Subtype.ext (le_antisymm hs_le_t₁ ht₁_le_s)
    have ht₁_compl : γ t₁ ∈ D.carrierᶜ :=
      hcircle_D harc.target_mem
    exact ht₁_compl (by simpa [hs_eq] using hcar)
  have hleft_range_E :
      Set.range (γ.subpath (0 : unitInterval) t₀) ⊆ E.carrierᶜ := by
    rw [Path.range_subpath_of_le γ (0 : unitInterval) t₀ unitInterval.nonneg']
    rintro z ⟨s, _hs, rfl⟩
    exact hγE s
  have hright_range_E :
      Set.range (γ.subpath t₁ (1 : unitInterval)) ⊆ E.carrierᶜ := by
    rw [Path.range_subpath_of_le γ t₁ (1 : unitInterval) unitInterval.le_one']
    rintro z ⟨s, _hs, rfl⟩
    exact hγE s
  let left : Path x (γ t₀) :=
    (γ.subpath (0 : unitInterval) t₀).cast γ.source.symm rfl
  let middle : Path (γ t₀) (γ t₁) := harc.somePath
  let right : Path (γ t₁) y :=
    (γ.subpath t₁ (1 : unitInterval)).cast rfl γ.target.symm
  let η : Path x y := (left.trans middle).trans right
  refine ⟨η, ?_, ?_⟩
  · intro t
    have ht_range : η t ∈ Set.range η := ⟨t, rfl⟩
    dsimp [η] at ht_range
    rw [Path.trans_range, Path.trans_range] at ht_range
    rcases ht_range with (hleft | hmiddle) | hright
    · rcases hleft with ⟨s, hs⟩
      rw [← hs]
      have hs' : (γ.subpath (0 : unitInterval) t₀) s ∈ D.carrierᶜ :=
        hleft_range_D ⟨s, rfl⟩
      simpa [left] using hs'
    · rcases hmiddle with ⟨s, hs⟩
      rw [← hs]
      exact hcircle_D (harc.somePath_mem s)
    · rcases hright with ⟨s, hs⟩
      rw [← hs]
      have hs' : (γ.subpath t₁ (1 : unitInterval)) s ∈ D.carrierᶜ :=
        hright_range_D ⟨s, rfl⟩
      simpa [right] using hs'
  · intro t
    have ht_range : η t ∈ Set.range η := ⟨t, rfl⟩
    dsimp [η] at ht_range
    rw [Path.trans_range, Path.trans_range] at ht_range
    rcases ht_range with (hleft | hmiddle) | hright
    · rcases hleft with ⟨s, hs⟩
      rw [← hs]
      have hs' : (γ.subpath (0 : unitInterval) t₀) s ∈ E.carrierᶜ :=
        hleft_range_E ⟨s, rfl⟩
      simpa [left] using hs'
    · rcases hmiddle with ⟨s, hs⟩
      rw [← hs]
      exact hcircle_E (harc.somePath_mem s)
    · rcases hright with ⟨s, hs⟩
      rw [← hs]
      have hs' : (γ.subpath t₁ (1 : unitInterval)) s ∈ E.carrierᶜ :=
        hright_range_E ⟨s, rfl⟩
      simpa [right] using hs'

/--
%%handwave
name:
  One-disk push-off at a fixed radius preserves avoidance of a disjoint disk when it hits
statement:
  Suppose a path already avoids a second closed coordinate disk.  If the
  replacement circle for the first disk lies in an exterior annulus disjoint
  from the second disk, then the first-disk push-off preserves avoidance of
  the second disk.
proof:
  The first/last-hit construction only changes the part of the path inside
  the expanded disk.  The replacement arc lies in the chosen radius boundary
  circle, hence in
  [the exterior annulus determined by the outer radius](lean:JJMath.Uniformization.ClosedCoordinateDisk.radiusBoundaryCircle_subset_exteriorAnnulusWithOuterRadius).
  Since that annulus is disjoint from the second closed disk and the original
  path avoided the second disk, the modified path avoids it throughout.
-/
theorem path_can_be_pushed_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk_with_expandedRadius_when_hits
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D E : ClosedCoordinateDisk X) {ρ R : ℝ}
    (hρD : D.closedRadius < ρ)
    (hρR : ρ < R)
    (hR_open : R < D.openDisk.radius)
    (hAnnE : Disjoint (D.exteriorAnnulusWithOuterRadius R) E.carrier)
    {x y : X}
    (γ : Path x y)
    (hγE : ∀ t, γ t ∈ E.carrierᶜ)
    (hxρ : x ∈ (D.expandedClosedDisk ρ)ᶜ)
    (hyρ : y ∈ (D.expandedClosedDisk ρ)ᶜ)
    (hhit : ∃ t : unitInterval, γ t ∈ D.expandedClosedDisk ρ) :
    ∃ η : Path x y,
      (∀ t, η t ∈ D.carrierᶜ) ∧
        (∀ t, η t ∈ E.carrierᶜ) := by
  have hρ_open : ρ < D.openDisk.radius := hρR.trans hR_open
  rcases D.exists_first_last_expandedClosedDisk_hit hρ_open γ hhit with
    ⟨t₀, t₁, ht₀, ht₁, ht₀_min, ht₁_max⟩
  rcases D.first_last_expandedClosedDisk_hits_mem_radiusBoundaryCircle hρ_open
      γ hxρ hyρ ht₀ ht₁ ht₀_min ht₁_max with
    ⟨ht₀_circle, ht₁_circle⟩
  have hρ_pos : 0 < ρ := D.closedRadius_pos.trans hρD
  have harc : JoinedIn (D.radiusBoundaryCircle ρ) (γ t₀) (γ t₁) :=
    D.radiusBoundaryCircle_joinedIn hρ_pos hρ_open ht₀_circle ht₁_circle
  exact
    path_surgery_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk_from_boundaryCircle_arc
      D E hρD hρR hAnnE γ hγE ht₀ ht₁ ht₀_min ht₁_max harc

/--
%%handwave
name:
  One-disk push-off at a fixed radius preserves avoidance of a disjoint disk
statement:
  Suppose a path already avoids a second closed coordinate disk and the
  replacement circle for the first disk lies in an exterior annulus disjoint
  from the second disk.  Then pushing the path off the first disk preserves
  avoidance of the second disk.
proof:
  If the path never meets the expanded disk, keep the original path.  If it
  does meet the expanded disk, use
  [the hit-case push-off preserving the second disk](lean:JJMath.Uniformization.path_can_be_pushed_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk_with_expandedRadius_when_hits).
-/
theorem path_can_be_pushed_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk_with_expandedRadius
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D E : ClosedCoordinateDisk X) {ρ R : ℝ}
    (hρD : D.closedRadius < ρ)
    (hρR : ρ < R)
    (hR_open : R < D.openDisk.radius)
    (hAnnE : Disjoint (D.exteriorAnnulusWithOuterRadius R) E.carrier)
    {x y : X}
    (γ : Path x y)
    (hγE : ∀ t, γ t ∈ E.carrierᶜ)
    (hxρ : x ∈ (D.expandedClosedDisk ρ)ᶜ)
    (hyρ : y ∈ (D.expandedClosedDisk ρ)ᶜ) :
    ∃ η : Path x y,
      (∀ t, η t ∈ D.carrierᶜ) ∧
        (∀ t, η t ∈ E.carrierᶜ) := by
  by_cases hhit : ∃ t : unitInterval, γ t ∈ D.expandedClosedDisk ρ
  · exact
      path_can_be_pushed_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk_with_expandedRadius_when_hits
        D E hρD hρR hR_open hAnnE γ hγE hxρ hyρ hhit
  · refine ⟨γ, ?_, hγE⟩
    intro t
    exact D.compl_expandedClosedDisk_subset_compl_carrier hρD.le
      (by
        intro ht
        exact hhit ⟨t, ht⟩)

/--
%%handwave
name:
  One-disk push-off preserves avoidance of a disjoint closed coordinate disk
statement:
  Suppose two closed coordinate disks are disjoint.  If a path already avoids
  the second disk and its endpoints lie outside the first disk, then the path
  can be pushed off the first disk while still avoiding the second disk.
proof:
  Use
  [a thin exterior annulus around the first disk that misses the second
  disk](lean:JJMath.Uniformization.ClosedCoordinateDisk.exists_exteriorAnnulusWithOuterRadius_disjoint).
  Choose the expanded radius for the first-hit/last-hit construction below the
  annulus outer radius and below the endpoint coordinate radii, using
  [the endpoint-avoiding radius selection](lean:JJMath.Uniformization.ClosedCoordinateDisk.exists_expandedRadius_lt_outerRadius_avoids_points).
  The circular replacement arc lies in a radius boundary circle, hence in
  [that exterior annulus](lean:JJMath.Uniformization.ClosedCoordinateDisk.radiusBoundaryCircle_subset_exteriorAnnulusWithOuterRadius),
  so it avoids both the original closed disk and the second closed disk.
-/
theorem path_can_be_pushed_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D E : ClosedCoordinateDisk X)
    (_hdisj : Disjoint D.carrier E.carrier)
    {x y : X}
    (γ : Path x y)
    (_hγE : ∀ t, γ t ∈ E.carrierᶜ)
    (_hxD : x ∈ D.carrierᶜ)
    (_hyD : y ∈ D.carrierᶜ) :
    ∃ η : Path x y,
      (∀ t, η t ∈ D.carrierᶜ) ∧
        (∀ t, η t ∈ E.carrierᶜ) := by
  rcases ClosedCoordinateDisk.exists_exteriorAnnulusWithOuterRadius_disjoint
      (D := D) (E := E) _hdisj with
    ⟨R, hDR, hR_open, hAnnE⟩
  rcases D.exists_expandedRadius_lt_outerRadius_avoids_points
      hDR _hxD _hyD with
    ⟨ρ, hρD, hρR, hxρ, hyρ⟩
  exact
    path_can_be_pushed_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk_with_expandedRadius
      D E hρD hρR hR_open hAnnE γ _hγE hxρ hyρ

/--
%%handwave
name:
  Paths can be pushed off disjoint closed coordinate disks
statement:
  If a path starts and ends outside two disjoint closed coordinate disks, then
  it can be replaced by another path with the same endpoints whose image stays
  outside the two disks.
proof:
  Push the original path off the first closed coordinate disk.  The resulting
  path avoids the first disk.  Then push it off the second closed coordinate
  disk using the version that preserves avoidance of a disjoint disk.
-/
theorem path_can_be_pushed_off_disjoint_closedCoordinateDisks
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D0 D1 : ClosedCoordinateDisk X)
    (hdisj : Disjoint D0.carrier D1.carrier)
    {x y : X}
    (γ : Path x y)
    (_hx : x ∈ ((D0.carrier ∪ D1.carrier)ᶜ : Set X))
    (_hy : y ∈ ((D0.carrier ∪ D1.carrier)ᶜ : Set X)) :
    ∃ η : Path x y, ∀ t, η t ∈
      ((D0.carrier ∪ D1.carrier)ᶜ : Set X) := by
  have hx0 : x ∈ D0.carrierᶜ := by
    intro hxD0
    exact _hx (Or.inl hxD0)
  have hy0 : y ∈ D0.carrierᶜ := by
    intro hyD0
    exact _hy (Or.inl hyD0)
  have hx1 : x ∈ D1.carrierᶜ := by
    intro hxD1
    exact _hx (Or.inr hxD1)
  have hy1 : y ∈ D1.carrierᶜ := by
    intro hyD1
    exact _hy (Or.inr hyD1)
  rcases path_can_be_pushed_off_closedCoordinateDisk D0 γ hx0 hy0 with
    ⟨γ0, hγ0D0⟩
  rcases
      path_can_be_pushed_off_closedCoordinateDisk_preserving_disjoint_closedCoordinateDisk
        D1 D0 (Disjoint.symm hdisj) γ0 hγ0D0 hx1 hy1 with
    ⟨η, hηD1, hηD0⟩
  refine ⟨η, ?_⟩
  intro t
  rw [Set.mem_compl_iff]
  intro ht
  rcases ht with ht0 | ht1
  · exact hηD0 t ht0
  · exact hηD1 t ht1

/--
%%handwave
name:
  Disjoint closed coordinate disks can be avoided by paths
statement:
  Any two points outside two disjoint closed coordinate disks in a connected
  Riemann surface can be joined by a path that stays outside the two disks.
proof:
  First join the two points by
  [some path in the surface](lean:JJMath.Uniformization.riemannSurface_joined).
  Then replace that path by
  [one avoiding the closed disks](lean:JJMath.Uniformization.path_can_be_pushed_off_disjoint_closedCoordinateDisks).
-/
theorem disjoint_closedCoordinateDisks_complement_joinedIn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D0 D1 : ClosedCoordinateDisk X)
    (hdisj : Disjoint D0.carrier D1.carrier)
    {x y : X}
    (hx : x ∈ ((D0.carrier ∪ D1.carrier)ᶜ : Set X))
    (hy : y ∈ ((D0.carrier ∪ D1.carrier)ᶜ : Set X)) :
    JoinedIn ((D0.carrier ∪ D1.carrier)ᶜ : Set X) x y := by
  let γ : Path x y := (riemannSurface_joined x y).somePath
  rcases path_can_be_pushed_off_disjoint_closedCoordinateDisks
      D0 D1 hdisj γ hx hy with
    ⟨η, hη⟩
  exact ⟨η, hη⟩

/--
%%handwave
name:
  Disjoint closed coordinate disks have connected complement
statement:
  The complement of two disjoint closed coordinate disks in a connected Riemann
  surface is preconnected.
proof:
  Since [any two complement points can be joined by a path that avoids the two
  closed disks](lean:JJMath.Uniformization.disjoint_closedCoordinateDisks_complement_joinedIn),
  the range of such a path gives a connected subset of the complement joining
  any prescribed pair of points.  Pairwise joining by connected subsets implies
  preconnectedness.
-/
theorem disjoint_closedCoordinateDisks_complement_preconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D0 D1 : ClosedCoordinateDisk X)
    (hdisj : Disjoint D0.carrier D1.carrier) :
    IsPreconnected ((D0.carrier ∪ D1.carrier)ᶜ : Set X) := by
  exact isPreconnected_of_forall_joinedIn
    (fun x hx y hy =>
      disjoint_closedCoordinateDisks_complement_joinedIn D0 D1 hdisj hx hy)

/--
%%handwave
name:
  Twice-cut Radó domain
statement:
  A twice-cut Radó domain consists of two disjoint closed coordinate disks and
  their connected open complement.
-/
structure RadoTwoDiskCut (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The first removed closed coordinate disk. -/
  closedDisk0 : ClosedCoordinateDisk X
  /-- The second removed closed coordinate disk. -/
  closedDisk1 : ClosedCoordinateDisk X
  /-- The two removed closed coordinate disks are disjoint. -/
  disjoint_closedDisks : Disjoint closedDisk0.carrier closedDisk1.carrier
  /-- The surface with the two closed coordinate disks removed. -/
  complement : TopologicalSpace.Opens X
  /-- The complement is exactly the complement of the two removed closed disks. -/
  complement_eq :
    (complement : Set X) = (closedDisk0.carrier ∪ closedDisk1.carrier)ᶜ
  /-- The complement is a Riemann surface with the induced structure. -/
  [connected_complement : RiemannSurface complement]

attribute [instance] RadoTwoDiskCut.connected_complement

namespace RadoTwoDiskCut

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name:
  The twice-cut complement and ambient coordinate disks cover the surface
statement:
  The complement in a twice-cut Radó domain, together with the two ambient open
  coordinate disks, covers the original surface.
proof:
  A point outside both closed disks belongs to their complement.  A point in
  either closed disk belongs to that disk's ambient open coordinate disk.
-/
theorem openCover (C : RadoTwoDiskCut X) :
    ((C.complement : Set X) ∪ C.closedDisk0.openDisk.carrier ∪
      C.closedDisk1.openDisk.carrier) = Set.univ := by
  rw [C.complement_eq]
  refine Set.eq_univ_iff_forall.mpr ?_
  intro x
  by_cases hx0 : x ∈ C.closedDisk0.carrier
  · exact Or.inl (Or.inr (C.closedDisk0.subset_openDisk hx0))
  by_cases hx1 : x ∈ C.closedDisk1.carrier
  · exact Or.inr (C.closedDisk1.subset_openDisk hx1)
  · exact Or.inl (Or.inl (by simp [hx0, hx1]))

/--
%%handwave
name:
  The twice-cut complement as a Perron-open region
statement:
  The complement of the two closed coordinate disks is a Perron-open region in
  the original surface.
-/
def toPerronOpen (C : RadoTwoDiskCut X) : PerronOpen X where
  carrier := C.complement
  isOpen := C.complement.is_open'
  nonempty := by
    rcases (PathConnectedSpace.nonempty : Nonempty C.complement) with ⟨x⟩
    exact ⟨x, x.2⟩

@[simp] theorem toPerronOpen_carrier (C : RadoTwoDiskCut X) :
    C.toPerronOpen.carrier = (C.complement : Set X) := rfl

@[simp] theorem toPerronOpen_boundary (C : RadoTwoDiskCut X) :
    C.toPerronOpen.boundary = frontier (C.complement : Set X) := rfl

/--
%%handwave
name:
  The twice-cut boundary lies on the removed disks
statement:
  The frontier of the twice-cut complement is contained in the union of the two
  removed closed coordinate disks.
proof:
  The complement is open, so its frontier is disjoint from it.  Since the
  complement is exactly the complement of the union of the removed disks, every
  frontier point lies in that union.
-/
theorem boundary_subset_closedDisks (C : RadoTwoDiskCut X) :
    C.toPerronOpen.boundary ⊆
      C.closedDisk0.carrier ∪ C.closedDisk1.carrier := by
  intro x hx
  have hx_frontier : x ∈ frontier (C.complement : Set X) := by
    simpa [RadoTwoDiskCut.toPerronOpen_boundary] using hx
  have hx_not_complement : x ∉ (C.complement : Set X) := by
    intro hx_complement
    have hx_inter :
        x ∈ (C.complement : Set X) ∩ frontier (C.complement : Set X) :=
      ⟨hx_complement, hx_frontier⟩
    have hdisj :
        (C.complement : Set X) ∩ frontier (C.complement : Set X) = ∅ :=
      C.complement.is_open'.inter_frontier_eq
    rw [hdisj] at hx_inter
    exact hx_inter
  by_contra hx_union
  exact hx_not_complement (by
    simpa [C.complement_eq] using hx_union)

end RadoTwoDiskCut

/--
%%handwave
name:
  Two closed coordinate disks with connected complement
statement:
  In a noncompact Riemann surface, there are two disjoint closed
  coordinate disks whose complement is nonempty and preconnected.
proof:
  Choose two sufficiently small disjoint closed coordinate disks, for instance
  inside a single coordinate chart.  The standard surface-topology fact used
  here is that removing finitely many pairwise disjoint closed coordinate
  disks from a connected noncompact surface leaves a nonempty connected open
  surface.  Equivalently, a small closed disk in a surface has a collar and is
  nonseparating for the complement considered as a surface with boundary; the
  same argument applies to two disjoint disks.
-/
theorem exists_disjoint_closedCoordinateDisks_connected_complement
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [NoncompactSpace X] :
    ∃ D0 D1 : ClosedCoordinateDisk X,
      Disjoint D0.carrier D1.carrier ∧
        ((D0.carrier ∪ D1.carrier)ᶜ : Set X).Nonempty ∧
          IsPreconnected ((D0.carrier ∪ D1.carrier)ᶜ : Set X) := by
  rcases exists_disjoint_closedCoordinateDisks (X := X) with
    ⟨D0, D1, hdisj⟩
  exact ⟨D0, D1, hdisj,
    closedCoordinateDisks_complement_nonempty_of_noncompact D0 D1,
    disjoint_closedCoordinateDisks_complement_preconnected D0 D1 hdisj⟩

/--
%%handwave
name:
  Existence of a twice-cut Radó domain
statement:
  In a noncompact Riemann surface one can remove two disjoint closed
  coordinate disks so that the complement is still a Riemann surface,
  and the complement together with two coordinate disks covers the original
  surface.
proof:
  Choose two distinct points and disjoint coordinate neighborhoods with compact
  closed subdisks.  On a noncompact connected surface the complement of two
  sufficiently small closed disks can be chosen connected.  The remaining
  complement is open, and the inherited complex structure makes it a connected
  Riemann surface.
-/
theorem exists_radoTwoDiskCut
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [NoncompactSpace X] :
    Nonempty (RadoTwoDiskCut X) := by
  rcases exists_disjoint_closedCoordinateDisks_connected_complement (X := X) with
    ⟨D0, D1, hdisj, hne, hpre⟩
  let U : TopologicalSpace.Opens X :=
    { carrier := (D0.carrier ∪ D1.carrier)ᶜ
      is_open' := by
        exact ((ClosedCoordinateDisk.isClosed D0).union
          (ClosedCoordinateDisk.isClosed D1)).isOpen_compl }
  haveI : RiemannSurface U :=
    riemannSurface_openSubset U hne hpre
  exact ⟨
    { closedDisk0 := D0
      closedDisk1 := D1
      disjoint_closedDisks := hdisj
      complement := U
      complement_eq := rfl
      connected_complement := inferInstance }⟩

/--
%%handwave
name:
  The path-homotopy cover is path connected
statement:
  The path-homotopy universal cover of a Riemann surface is path
  connected.
proof:
  Every point of the path-homotopy cover is represented by a path starting at
  the base point.  Varying the endpoint along that representing path gives a
  path from the distinguished lift to the represented point, and concatenating
  such paths joins any two upstairs points.
-/
theorem pathHomotopyUniversalCover_pathConnected
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) :
    PathConnectedSpace (PathHomotopyUniversalCover Y y0) := by
  infer_instance

/--
%%handwave
name:
  The path-homotopy cover is simply connected
statement:
  The path-homotopy universal cover of a Riemann surface is simply
  connected.
proof:
  Path classes in the cover project to the endpoint-fixed homotopy classes
  stored in their endpoints.  This forces any two paths with the same upstairs
  endpoints to be homotopic, while the previous path-connectedness statement
  supplies paths between points.
-/
theorem pathHomotopyUniversalCover_simplyConnected
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) :
    SimplyConnectedSpace (PathHomotopyUniversalCover Y y0) := by
  infer_instance

/--
%%handwave
name:
  The path-homotopy cover is locally path connected
statement:
  The pulled-back complex charted structure on the path-homotopy cover is
  locally path connected.
proof:
  The cover has complex charts obtained by composing local sheets of the
  endpoint projection with charts downstairs.  Since the model space
  \(\mathbb C\) is locally path connected, every charted space modelled on it
  is locally path connected.
-/
theorem pathHomotopyUniversalCover_locPathConnected
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) :
    LocPathConnectedSpace (PathHomotopyUniversalCover Y y0) := by
  exact ChartedSpace.locPathConnectedSpace (H := ℂ)
    (M := PathHomotopyUniversalCover Y y0)

/--
%%handwave
name:
  The path-homotopy cover is Hausdorff
statement:
  The path-homotopy universal cover of a Riemann surface is
  Hausdorff.
proof:
  Distinct points with different endpoints are separated by disjoint
  neighborhoods downstairs and pulled back by the endpoint map.  Distinct
  points in the same endpoint fiber are separated by disjoint local sheets of a
  sufficiently small simply connected neighborhood.
-/
theorem pathHomotopyUniversalCover_t2Space
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) :
    T2Space (PathHomotopyUniversalCover Y y0) := by
  classical
  constructor
  intro x y hxy
  by_cases hendpoint :
      PathHomotopyUniversalCover.endpoint x =
        PathHomotopyUniversalCover.endpoint y
  · let W := SimplyConnectedOpenNeighborhood.choose
      (x := PathHomotopyUniversalCover.endpoint x) (N := Set.univ)
      (by simp) isOpen_univ
    let a : W.carrier := ⟨PathHomotopyUniversalCover.endpoint x, W.mem_carrier⟩
    let ηx : PathHomotopyUniversalCover.Fiber y0 (a : Y) := ⟨x, rfl⟩
    let ηy : PathHomotopyUniversalCover.Fiber y0 (a : Y) :=
      ⟨y, by simpa [a] using hendpoint.symm⟩
    have hηxy : ηx ≠ ηy := by
      intro hη
      exact hxy (congrArg Subtype.val hη)
    let C : PathHomotopyUniversalCover.LocalSheetChart (X := Y) y0 :=
      { base := W.carrier
        base_open := W.carrier_open
        base_pathConnected := W.carrier_pathConnected
        base_simplyConnected := W.carrier_simplyConnected
        center := a
        fiberPoint := ηx }
    let D : PathHomotopyUniversalCover.LocalSheetChart (X := Y) y0 :=
      { base := W.carrier
        base_open := W.carrier_open
        base_pathConnected := W.carrier_pathConnected
        base_simplyConnected := W.carrier_simplyConnected
        center := a
        fiberPoint := ηy }
    have hxC : x ∈ C.sheet := by
      simpa [C, ηx, PathHomotopyUniversalCover.LocalSheetChart.sheet] using
        (PathHomotopyUniversalCover.fiberPoint_mem_localSheet_of_simplyConnected
          (x₀ := y0) a ηx)
    have hyD : y ∈ D.sheet := by
      simpa [D, ηy, PathHomotopyUniversalCover.LocalSheetChart.sheet] using
        (PathHomotopyUniversalCover.fiberPoint_mem_localSheet_of_simplyConnected
          (x₀ := y0) a ηy)
    have hdisj : Disjoint C.sheet D.sheet := by
      rw [Set.disjoint_left]
      intro z hzC hzD
      apply hηxy
      rcases hzC with ⟨hzW, hlabelC⟩
      rcases hzD with ⟨hzW', hlabelD⟩
      have hlabel_same :
          ((PathHomotopyUniversalCover.localTrivializationFiberEquiv
            (x₀ := y0) a) ⟨z, hzW'⟩).2 = ηx := by
        convert hlabelC
      exact hlabel_same.symm.trans hlabelD
    exact
      ⟨C.sheet, D.sheet,
        PathHomotopyUniversalCover.isOpen_localSheetChart_sheet C,
        PathHomotopyUniversalCover.isOpen_localSheetChart_sheet D,
        hxC, hyD, hdisj⟩
  · have hcont :
        Continuous
          (PathHomotopyUniversalCover.endpoint :
            PathHomotopyUniversalCover Y y0 → Y) :=
      PathHomotopyUniversalCover.continuous_endpoint_of_riemannSurface
        Y y0
    exact separated_by_continuous hcont hendpoint

/--
%%handwave
name:
  The pulled-back charts make the path-homotopy cover a complex manifold
statement:
  The pulled-back complex charts on the path-homotopy universal cover form a
  complex manifold atlas.
proof:
  On an overlap of two upstairs charts, the transition map agrees locally with
  the transition map of the corresponding downstairs charts.  Downstairs
  transitions are smooth complex-manifold transitions, so the upstairs
  transitions are smooth as well.
-/
theorem pathHomotopyUniversalCover_isManifold
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) :
    IsManifold 𝓘(ℂ) ⊤ (PathHomotopyUniversalCover Y y0) := by
  classical
  apply isManifold_of_contDiffOn
  intro e e' he he'
  let b := PathHomotopyUniversalCover.baseChartOfCoverChart (x₀ := y0) e he
  let b' := PathHomotopyUniversalCover.baseChartOfCoverChart (x₀ := y0) e' he'
  have hb_mem : b ∈ atlas ℂ Y :=
    PathHomotopyUniversalCover.baseChartOfCoverChart_mem_atlas
      (x₀ := y0) e he
  have hb'_mem : b' ∈ atlas ℂ Y :=
    PathHomotopyUniversalCover.baseChartOfCoverChart_mem_atlas
      (x₀ := y0) e' he'
  have hbase :
      ContDiffOn ℂ ⊤ ((𝓘(ℂ)).extendCoordChange b b')
        ((𝓘(ℂ)).extendCoordChange b b').source :=
    (𝓘(ℂ)).contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas hb_mem)
      (IsManifold.subset_maximalAtlas hb'_mem)
  have hsubset :
      (𝓘(ℂ)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range (𝓘(ℂ)) ⊆
        ((𝓘(ℂ)).extendCoordChange b b').source := by
    intro z hz
    have hzCover : z ∈ (e.symm ≫ₕ e').source := by
      simpa using hz.1
    have hzParts : z ∈ e.target ∧ e.symm z ∈ e'.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hzCover
    have hz_b_target : z ∈ b.target :=
      PathHomotopyUniversalCover.coverChart_target_subset_baseChart_target
        (x₀ := y0) e he hzParts.1
    have hendpoint :
        PathHomotopyUniversalCover.endpoint (e.symm z) = b.symm z :=
      PathHomotopyUniversalCover.endpoint_coverChart_symm_eq_baseChart_symm
        (x₀ := y0) e he hzParts.1
    have hz_b'_source : b.symm z ∈ b'.source := by
      have hz_endpoint :
          PathHomotopyUniversalCover.endpoint (e.symm z) ∈ b'.source :=
        PathHomotopyUniversalCover.coverChart_source_projection_mem_baseChart_source
          (x₀ := y0) e' he' hzParts.2
      simpa [hendpoint] using hz_endpoint
    rw [(𝓘(ℂ)).extendCoordChange_source]
    refine ⟨z, ?_, by simp⟩
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hz_b_target, hz_b'_source⟩
  refine hbase.congr_mono ?_ hsubset
  intro z hz
  have hzCover : z ∈ (e.symm ≫ₕ e').source := by
    simpa using hz.1
  have hzParts : z ∈ e.target ∧ e.symm z ∈ e'.source := by
    simpa [OpenPartialHomeomorph.trans_source] using hzCover
  have hendpoint :
      PathHomotopyUniversalCover.endpoint (e.symm z) = b.symm z :=
    PathHomotopyUniversalCover.endpoint_coverChart_symm_eq_baseChart_symm
      (x₀ := y0) e he hzParts.1
  calc
    (𝓘(ℂ)) ((e.symm ≫ₕ e') ((𝓘(ℂ)).symm z))
        = e' (e.symm z) := by
          simp
    _ = b' (PathHomotopyUniversalCover.endpoint (e.symm z)) := by
          exact
            PathHomotopyUniversalCover.coverChart_apply_eq_baseChart_apply_endpoint
              (x₀ := y0) e' he' hzParts.2
    _ = b' (b.symm z) := by
          rw [hendpoint]
    _ = ((𝓘(ℂ)).extendCoordChange b b') z := by
          simp [ModelWithCorners.extendCoordChange]

/--
%%handwave
name:
  The path-homotopy cover is a Riemann surface
statement:
  The path-homotopy universal cover of a Riemann surface inherits a
  Riemann-surface structure.
proof:
  Combine [Hausdorffness of the path-homotopy
  cover](lean:JJMath.Uniformization.pathHomotopyUniversalCover_t2Space)
  with [the pulled-back complex manifold
  atlas](lean:JJMath.Uniformization.pathHomotopyUniversalCover_isManifold).
-/
theorem pathHomotopyUniversalCover_complexOneManifold
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) :
    ComplexOneManifold (PathHomotopyUniversalCover Y y0) := by
  haveI : T2Space (PathHomotopyUniversalCover Y y0) :=
    pathHomotopyUniversalCover_t2Space (Y := Y) y0
  haveI : IsManifold 𝓘(ℂ) ⊤ (PathHomotopyUniversalCover Y y0) :=
    pathHomotopyUniversalCover_isManifold (Y := Y) y0
  exact {}

/--
%%handwave
name:
  The path-homotopy cover is locally simply connected
statement:
  The path-homotopy universal cover of a Riemann surface is locally
  simply connected.
proof:
  Apply [the local simple connectedness of complex charted
  spaces](lean:JJMath.Uniformization.chartedSpace_complex_locallySimplyConnectedSpace)
  to the pulled-back complex charted structure on the cover.
-/
theorem pathHomotopyUniversalCover_locallySimplyConnected
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) :
    LocallySimplyConnectedSpace (PathHomotopyUniversalCover Y y0) := by
  exact chartedSpace_complex_locallySimplyConnectedSpace
    (PathHomotopyUniversalCover Y y0)

/--
%%handwave
name:
  The path-homotopy cover of a Riemann surface is a Riemann surface
statement:
  The path-homotopy universal cover of a Riemann surface inherits a
  Riemann-surface structure.
proof:
  Combine [the inherited Riemann-surface
  structure](lean:JJMath.Uniformization.pathHomotopyUniversalCover_complexOneManifold),
  with [path connectedness](lean:JJMath.Uniformization.pathHomotopyUniversalCover_pathConnected).
-/
theorem pathHomotopyUniversalCover_riemannSurface
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) :
    RiemannSurface (PathHomotopyUniversalCover Y y0) := by
  haveI : ComplexOneManifold (PathHomotopyUniversalCover Y y0) :=
    pathHomotopyUniversalCover_complexOneManifold (Y := Y) y0
  haveI : PathConnectedSpace (PathHomotopyUniversalCover Y y0) :=
    pathHomotopyUniversalCover_pathConnected (Y := Y) y0
  exact {}

/--
%%handwave
name:
  A second-countable universal cover makes the base second countable
statement:
  If the path-homotopy universal cover of a Riemann surface is second
  countable, then the surface itself is second countable.
proof:
  The endpoint projection is a surjective open quotient map.  A second-countable
  space maps through an open quotient map to a second-countable quotient.
-/
theorem secondCountable_of_secondCountable_pathHomotopyUniversalCover
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y)
    [SecondCountableTopology (PathHomotopyUniversalCover Y y0)] :
    SecondCountableTopology Y := by
  let p : PathHomotopyUniversalCover Y y0 → Y :=
    PathHomotopyUniversalCover.endpoint
  have hcov : IsCoveringMap p :=
    PathHomotopyUniversalCover.isCoveringMap_endpoint_of_riemannSurface Y y0
  have hcont : Continuous p := hcov.continuous
  have hopen : IsOpenMap p := hcov.isOpenMap
  have hsurj : Function.Surjective p :=
    PathHomotopyUniversalCover.endpoint_surjective_of_riemannSurface Y y0
  exact (hopen.isQuotientMap hcont hsurj).secondCountableTopology hopen

/--
%%handwave
name:
  A second-countable twice-cut complement makes the surface second countable
statement:
  If the complement in a twice-cut Radó domain is second countable, then the
  original surface is second countable.
proof:
  The surface is covered by the complement and two coordinate disks.  Each of
  those three open pieces is second countable, so a finite open cover by
  second-countable pieces gives a countable basis for the whole surface.
-/
theorem secondCountable_of_radoTwoDiskCut_complement
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (C : RadoTwoDiskCut X) [SecondCountableTopology C.complement] :
    SecondCountableTopology X := by
  let U : Fin 3 → Set X :=
    fun
      | ⟨0, _⟩ => (C.complement : Set X)
      | ⟨1, _⟩ => C.closedDisk0.openDisk.carrier
      | _ => C.closedDisk1.openDisk.carrier
  have hopen : ∀ i, IsOpen (U i) := by
    intro i
    fin_cases i
    · simpa [U] using C.complement.is_open'
    · simpa [U] using C.closedDisk0.openDisk.isOpen
    · simpa [U] using C.closedDisk1.openDisk.isOpen
  have hcover : (⋃ i : Fin 3, U i) = Set.univ := by
    rw [← C.openCover]
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      fin_cases i
      · exact Or.inl (Or.inl (by simpa [U] using hxi))
      · exact Or.inl (Or.inr (by simpa [U] using hxi))
      · exact Or.inr (by simpa [U] using hxi)
    · intro hx
      rcases hx with hx01 | hx2
      · rcases hx01 with hx0 | hx1
        · exact Set.mem_iUnion.mpr ⟨0, by simpa [U] using hx0⟩
        · exact Set.mem_iUnion.mpr ⟨1, by simpa [U] using hx1⟩
      · exact Set.mem_iUnion.mpr ⟨2, by simpa [U] using hx2⟩
  have hsecond : ∀ i, SecondCountableTopology (U i) := by
    intro i
    fin_cases i
    · simpa [U] using (inferInstance : SecondCountableTopology C.complement)
    · simpa [U] using C.closedDisk0.openDisk.secondCountable
    · simpa [U] using C.closedDisk1.openDisk.secondCountable
  exact secondCountableTopology_of_countable_open_cover_explicit U hopen hcover hsecond

/--
%%handwave
name:
  Pullback of a function to the path-homotopy cover
statement:
  A function on a surface pulls back to its path-homotopy universal cover by
  composing with the endpoint projection.
-/
def pathHomotopyUniversalCoverPullback
    {Y : Type} [TopologicalSpace Y] (y0 : Y) (h : Y → ℝ) :
    PathHomotopyUniversalCover Y y0 → ℝ :=
  fun z ↦ h (PathHomotopyUniversalCover.endpoint z)

/--
%%handwave
name:
  Harmonic functions pull back to the path-homotopy cover
statement:
  The pullback of a harmonic function along the endpoint projection of the
  path-homotopy universal cover is harmonic.
proof:
  In a pulled-back cover chart, the endpoint projection is just the inverse of
  the corresponding base chart.  Thus the coordinate expression of the pulled
  back function agrees locally with the coordinate expression of the original
  harmonic function in the extracted base chart.
-/
theorem pathHomotopyUniversalCoverPullback_harmonicOnSurface
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) {h : Y → ℝ}
    (hh : IsHarmonicOnSurface (Set.univ : Set Y) h) :
    IsHarmonicOnSurface
      (Set.univ : Set (PathHomotopyUniversalCover Y y0))
      (pathHomotopyUniversalCoverPullback y0 h) := by
  intro e he z hz
  let b := PathHomotopyUniversalCover.baseChartOfCoverChart (x₀ := y0) e he
  have hb_mem : b ∈ atlas ℂ Y :=
    PathHomotopyUniversalCover.baseChartOfCoverChart_mem_atlas
      (x₀ := y0) e he
  have hz_target : z ∈ e.target := hz.1
  have hz_b_target : z ∈ b.target :=
    PathHomotopyUniversalCover.coverChart_target_subset_baseChart_target
      (x₀ := y0) e he hz_target
  have hbase_at :
      InnerProductSpace.HarmonicAt
        (fun w : ℂ ↦ h (b.symm w)) z := by
    simpa using (hh b hb_mem z ⟨hz_b_target, by simp⟩)
  have heq_nhds :
      (fun w : ℂ ↦ pathHomotopyUniversalCoverPullback y0 h (e.symm w))
        =ᶠ[𝓝 z] fun w : ℂ ↦ h (b.symm w) := by
    filter_upwards [e.open_target.mem_nhds hz_target] with w hw
    have hendpoint :
        PathHomotopyUniversalCover.endpoint (e.symm w) = b.symm w :=
      PathHomotopyUniversalCover.endpoint_coverChart_symm_eq_baseChart_symm
        (x₀ := y0) e he hw
    simp [pathHomotopyUniversalCoverPullback, hendpoint]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq_nhds).mpr hbase_at

/--
%%handwave
name:
  Boundary values for the twice-cut Perron problem
statement:
  The boundary value for the twice-cut Perron problem is \(0\) on the first
  removed disk and \(1\) on the second removed disk.
-/
noncomputable def radoTwoDiskBoundaryValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (C : RadoTwoDiskCut X) : X → ℝ :=
  by
    classical
    exact fun x ↦ if x ∈ C.closedDisk0.carrier then 0
      else if x ∈ C.closedDisk1.carrier then 1
      else 0

/--
%%handwave
name:
  The twice-cut boundary value is zero on the first disk
statement:
  The twice-cut Perron boundary value is \(0\) on the first removed disk.
-/
theorem radoTwoDiskBoundaryValue_eq_zero_on_closedDisk0
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (C : RadoTwoDiskCut X) {x : X} (hx : x ∈ C.closedDisk0.carrier) :
    radoTwoDiskBoundaryValue C x = 0 := by
  classical
  simp [radoTwoDiskBoundaryValue, hx]

/--
%%handwave
name:
  The twice-cut boundary value is one on the second disk
statement:
  The twice-cut Perron boundary value is \(1\) on the second removed disk.
-/
theorem radoTwoDiskBoundaryValue_eq_one_on_closedDisk1
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (C : RadoTwoDiskCut X) {x : X} (hx : x ∈ C.closedDisk1.carrier) :
    radoTwoDiskBoundaryValue C x = 1 := by
  classical
  have hx0 : x ∉ C.closedDisk0.carrier :=
    (Set.disjoint_right.mp C.disjoint_closedDisks) hx
  simp [radoTwoDiskBoundaryValue, hx, hx0]

/--
%%handwave
name:
  Twice-cut boundary value is continuous on the Perron-open boundary
statement:
  The \(0/1\) boundary value is continuous on the frontier of the twice-cut
  complement.
proof:
  The frontier is contained in the union of the two disjoint closed coordinate
  disks.  On the part of the frontier lying in the first disk the boundary
  value is locally \(0\), and on the part lying in the second disk it is
  locally \(1\).  The disks are disjoint closed coordinate disks, so the two
  pieces are separated along the frontier.
-/
theorem radoTwoDiskBoundaryValue_continuousOn_perronOpen_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (C : RadoTwoDiskCut X) :
    ContinuousOn (radoTwoDiskBoundaryValue C) C.toPerronOpen.boundary := by
  classical
  intro x hx_boundary
  rcases C.boundary_subset_closedDisks hx_boundary with hx0 | hx1
  · have hx_not1 : x ∉ C.closedDisk1.carrier :=
      (Set.disjoint_left.mp C.disjoint_closedDisks) hx0
    have hx_value : radoTwoDiskBoundaryValue C x = 0 := by
      simp [radoTwoDiskBoundaryValue, hx0]
    have hnear :
        radoTwoDiskBoundaryValue C =ᶠ[𝓝[C.toPerronOpen.boundary] x]
          (fun _ : X ↦ (0 : ℝ)) := by
      change ∀ᶠ y in 𝓝[C.toPerronOpen.boundary] x,
        radoTwoDiskBoundaryValue C y = (0 : ℝ)
      rw [eventually_nhdsWithin_iff]
      filter_upwards
        [(ClosedCoordinateDisk.isClosed C.closedDisk1).isOpen_compl.mem_nhds hx_not1]
        with y hy_not1 hy_boundary
      rcases C.boundary_subset_closedDisks hy_boundary with hy0 | hy1
      · simp [radoTwoDiskBoundaryValue, hy0]
      · exact (hy_not1 hy1).elim
    exact continuousWithinAt_const.congr_of_eventuallyEq hnear hx_value
  · have hx_not0 : x ∉ C.closedDisk0.carrier :=
      (Set.disjoint_right.mp C.disjoint_closedDisks) hx1
    have hx_value : radoTwoDiskBoundaryValue C x = 1 := by
      simp [radoTwoDiskBoundaryValue, hx_not0, hx1]
    have hnear :
        radoTwoDiskBoundaryValue C =ᶠ[𝓝[C.toPerronOpen.boundary] x]
          (fun _ : X ↦ (1 : ℝ)) := by
      change ∀ᶠ y in 𝓝[C.toPerronOpen.boundary] x,
        radoTwoDiskBoundaryValue C y = (1 : ℝ)
      rw [eventually_nhdsWithin_iff]
      filter_upwards
        [(ClosedCoordinateDisk.isClosed C.closedDisk0).isOpen_compl.mem_nhds hx_not0]
        with y hy_not0 hy_boundary
      rcases C.boundary_subset_closedDisks hy_boundary with hy0 | hy1
      · exact (hy_not0 hy0).elim
      · have hy_not0' : y ∉ C.closedDisk0.carrier := by
          simpa using hy_not0
        simp [radoTwoDiskBoundaryValue, hy_not0', hy1]
    exact continuousWithinAt_const.congr_of_eventuallyEq hnear hx_value

/--
%%handwave
name:
  Twice-cut Perron-open boundary data
statement:
  The \(0/1\) boundary value on the twice-cut complement, regarded as
  boundary data for the Perron-open region in the original surface.
-/
noncomputable def radoTwoDiskPerronOpenBoundaryData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (C : RadoTwoDiskCut X) : PerronOpenBoundaryData C.toPerronOpen where
  toFun := radoTwoDiskBoundaryValue C
  continuous_boundary :=
    radoTwoDiskBoundaryValue_continuousOn_perronOpen_boundary C

/--
%%handwave
name:
  Bounded twice-cut Perron-open envelope
statement:
  The twice-cut Perron-open envelope is the bounded Perron-open envelope on
  the ambient surface, with upper bound \(1\).
-/
noncomputable def radoTwoDiskBoundedPerronOpenEnvelope
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (C : RadoTwoDiskCut X) : X → ℝ :=
  boundedPerronOpenEnvelope C.toPerronOpen
    (radoTwoDiskPerronOpenBoundaryData C) 1

/--
%%handwave
name:
  The zero function is bounded twice-cut Perron-open admissible
statement:
  The zero function belongs to the bounded Perron-open family for the
  twice-cut problem.
proof:
  The zero function is continuous and subharmonic, lies below the boundary
  values \(0\) and \(1\), and is everywhere bounded above by \(1\).
-/
theorem radoTwoDiskBoundedPerronOpenAdmissible_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    IsBoundedPerronOpenAdmissible C.toPerronOpen
      (radoTwoDiskPerronOpenBoundaryData C) 1 (fun _ : X ↦ 0) := by
  refine ⟨?_, ?_⟩
  · refine ⟨continuousOn_const,
      subharmonicOnSurface_const C.toPerronOpen.carrier 0, ?_⟩
    intro x _hx
    classical
    by_cases hx0 : x ∈ C.closedDisk0.carrier
    · simp [radoTwoDiskPerronOpenBoundaryData, radoTwoDiskBoundaryValue, hx0]
    · by_cases hx1 : x ∈ C.closedDisk1.carrier
      · simp [radoTwoDiskPerronOpenBoundaryData, radoTwoDiskBoundaryValue, hx0, hx1]
      · simp [radoTwoDiskPerronOpenBoundaryData, radoTwoDiskBoundaryValue, hx0, hx1]
  · intro x _hx
    norm_num

/--
%%handwave
name:
  The bounded twice-cut Perron-open envelope is nonnegative
statement:
  Inside the twice-cut complement, the bounded Perron-open envelope is
  nonnegative.
proof:
  The zero function is a bounded admissible subfunction, and the envelope is
  the supremum of all bounded admissible subfunctions.
-/
theorem radoTwoDiskBoundedPerronOpenEnvelope_nonnegative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) {x : X} (hx : x ∈ C.toPerronOpen.carrier) :
    0 ≤ radoTwoDiskBoundedPerronOpenEnvelope C x := by
  have hbdd :
      BddAbove
        (boundedPerronOpenValueSet C.toPerronOpen
          (radoTwoDiskPerronOpenBoundaryData C) 1 x) :=
    boundedPerronOpenValueSet_bddAbove C.toPerronOpen
      (radoTwoDiskPerronOpenBoundaryData C) 1 hx
  simpa [radoTwoDiskBoundedPerronOpenEnvelope] using
    boundedPerronOpenAdmissible_le_boundedPerronOpenEnvelope_of_bddAbove
      C.toPerronOpen (radoTwoDiskPerronOpenBoundaryData C) 1
      (v := fun _ : X ↦ 0)
      (radoTwoDiskBoundedPerronOpenAdmissible_zero C)
      (x := x) hbdd

/--
%%handwave
name:
  The bounded twice-cut Perron-open envelope is at most one
statement:
  Inside the twice-cut complement, the bounded Perron-open envelope is bounded
  above by \(1\).
proof:
  This is the defining upper bound in the bounded Perron-open family.  The
  zero function shows that the family is nonempty.
-/
theorem radoTwoDiskBoundedPerronOpenEnvelope_le_one
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) {x : X} (hx : x ∈ C.toPerronOpen.carrier) :
    radoTwoDiskBoundedPerronOpenEnvelope C x ≤ 1 := by
  simpa [radoTwoDiskBoundedPerronOpenEnvelope] using
    boundedPerronOpenEnvelope_le_bound C.toPerronOpen
      (radoTwoDiskPerronOpenBoundaryData C) 1
      ⟨fun _ : X ↦ 0, radoTwoDiskBoundedPerronOpenAdmissible_zero C⟩ hx

/--
%%handwave
name:
  The bounded twice-cut Perron-open envelope is harmonic in the complement
statement:
  The bounded Perron-open envelope for the twice-cut problem is harmonic in the
  twice-cut complement.
proof:
  This is the general Perron-open interior harmonicity theorem applied to the
  twice-cut complement, with the zero function supplying a nonempty bounded
  Perron family.
-/
theorem radoTwoDiskBoundedPerronOpenEnvelope_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    IsHarmonicOnSurface (C.complement : Set X)
      (radoTwoDiskBoundedPerronOpenEnvelope C) := by
  simpa [radoTwoDiskBoundedPerronOpenEnvelope,
      RadoTwoDiskCut.toPerronOpen_carrier] using
    boundedPerronOpenEnvelope_is_harmonic C.toPerronOpen
      (radoTwoDiskPerronOpenBoundaryData C) 1
      ⟨fun _ : X ↦ 0, radoTwoDiskBoundedPerronOpenAdmissible_zero C⟩

/--
%%handwave
name:
  The bounded twice-cut Perron-open envelope restricts to a harmonic function
statement:
  Restricting the bounded Perron-open envelope to the twice-cut complement
  gives a harmonic function on the complement as a surface in its own right.
proof:
  Harmonicity is local in charts, and charts of an open subspace are
  restrictions of ambient charts, so ambient harmonicity on the open complement
  restricts to harmonicity on the subspace.
-/
theorem radoTwoDiskBoundedPerronOpenEnvelope_harmonic_on_complement
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    IsHarmonicOnSurface (Set.univ : Set C.complement)
      (fun x : C.complement ↦ radoTwoDiskBoundedPerronOpenEnvelope C x) := by
  exact harmonicOnSurface_openSubtype_univ_of_ambient C.complement
    (radoTwoDiskBoundedPerronOpenEnvelope_harmonic C)

private theorem closedCoordinateDisk_positiveRealBoundaryPoint_mem_boundary_of_compl_union
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (D E : ClosedCoordinateDisk X) (hDE : Disjoint D.carrier E.carrier)
    (Ω : TopologicalSpace.Opens X)
    (hΩ : (Ω : Set X) = (D.carrier ∪ E.carrier)ᶜ) :
    D.positiveRealBoundaryPoint ∈ frontier (Ω : Set X) := by
  have hpD : D.positiveRealBoundaryPoint ∈ D.carrier :=
    D.positiveRealBoundaryPoint_mem_carrier
  have hp_not_E : D.positiveRealBoundaryPoint ∉ E.carrier :=
    (Set.disjoint_left.mp hDE) hpD
  have hp_not_Ω : D.positiveRealBoundaryPoint ∉ (Ω : Set X) := by
    intro hpΩ
    have hp_not_union :
        D.positiveRealBoundaryPoint ∈ (D.carrier ∪ E.carrier)ᶜ := by
      simpa [hΩ] using hpΩ
    exact hp_not_union (Or.inl hpD)
  have hp_closure : D.positiveRealBoundaryPoint ∈ closure (Ω : Set X) := by
    refine mem_closure_iff_nhds.mpr ?_
    intro U hU
    let U' : Set X :=
      (U ∩ E.carrierᶜ) ∩ D.openDisk.chart.source
    have hU'_nhds : U' ∈ 𝓝 D.positiveRealBoundaryPoint := by
      refine Filter.inter_mem (Filter.inter_mem hU ?_) ?_
      · exact (ClosedCoordinateDisk.isClosed E).isOpen_compl.mem_nhds hp_not_E
      · exact D.openDisk.chart.open_source.mem_nhds
          D.positiveRealBoundaryPoint_mem_source
    have hW :
        D.openDisk.chart '' U' ∈
          𝓝 (D.openDisk.center + (D.closedRadius : ℂ)) := by
      simpa [D.chart_positiveRealBoundaryPoint] using
        D.openDisk.chart.image_mem_nhds D.positiveRealBoundaryPoint_mem_source hU'_nhds
    rcases Metric.mem_nhds_iff.mp hW with ⟨ε, hε_pos, hε_subset⟩
    let δ : ℝ := ε / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      linarith
    have hδ_lt_ε : δ < ε := by
      dsimp [δ]
      linarith
    let z : ℂ := D.openDisk.center + (((D.closedRadius + δ : ℝ)) : ℂ)
    have hz_dist_boundary :
        dist z (D.openDisk.center + (D.closedRadius : ℂ)) = δ := by
      rw [dist_eq_norm]
      have hsub :
          z - (D.openDisk.center + (D.closedRadius : ℂ)) = (δ : ℂ) := by
        calc
          z - (D.openDisk.center + (D.closedRadius : ℂ)) =
              (((D.closedRadius + δ : ℝ)) : ℂ) - (D.closedRadius : ℂ) := by
            dsimp [z]
            abel
          _ = (δ : ℂ) := by
            exact_mod_cast
              (by ring : (D.closedRadius + δ) - D.closedRadius = δ)
      rw [hsub]
      exact Complex.norm_of_nonneg hδ_pos.le
    have hz_dist_center :
        dist z D.openDisk.center = D.closedRadius + δ := by
      rw [dist_eq_norm]
      have hsub :
          z - D.openDisk.center =
            (((D.closedRadius + δ : ℝ)) : ℂ) := by
        dsimp [z]
        ring
      rw [hsub]
      exact Complex.norm_of_nonneg (by linarith [D.closedRadius_pos, hδ_pos])
    have hzW : z ∈ D.openDisk.chart '' U' := by
      apply hε_subset
      rw [Metric.mem_ball, hz_dist_boundary]
      exact hδ_lt_ε
    rcases hzW with ⟨y, hyU', hyz⟩
    have hy_not_D : y ∉ D.carrier := by
      intro hyD
      rw [D.carrier_eq] at hyD
      have hy_closed :
          D.openDisk.chart y ∈
            Metric.closedBall D.openDisk.center D.closedRadius := hyD.2
      have hz_closed :
          z ∈ Metric.closedBall D.openDisk.center D.closedRadius := by
        simpa [hyz] using hy_closed
      rw [Metric.mem_closedBall, hz_dist_center] at hz_closed
      linarith [hδ_pos]
    have hy_not_E : y ∉ E.carrier := by
      exact hyU'.1.2
    have hyΩ : y ∈ (Ω : Set X) := by
      have hy_not_union : y ∉ D.carrier ∪ E.carrier := by
        intro hy_union
        rcases hy_union with hyD | hyE
        · exact hy_not_D hyD
        · exact hy_not_E hyE
      simpa [hΩ] using hy_not_union
    exact ⟨y, hyU'.1.1, hyΩ⟩
  rw [frontier]
  have hInterior : interior (Ω : Set X) = (Ω : Set X) :=
    Ω.is_open'.interior_eq
  rw [hInterior]
  exact ⟨hp_closure, hp_not_Ω⟩

/--
%%handwave
name:
  The first distinguished disk point lies on the twice-cut boundary
statement:
  The positive-real boundary point of the first removed closed coordinate disk
  lies in the frontier of the twice-cut complement.
proof:
  The point belongs to the removed disk, so it is not in the complement.  In
  the coordinate chart, points just outside the closed Euclidean disk and close
  to the boundary point lie in the complement after shrinking away from the
  second removed disk; hence every neighborhood of the point meets the
  complement.
-/
theorem radoTwoDiskCut_closedDisk0_positiveRealBoundaryPoint_mem_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    C.closedDisk0.positiveRealBoundaryPoint ∈ C.toPerronOpen.boundary := by
  simpa [RadoTwoDiskCut.toPerronOpen_boundary] using
    closedCoordinateDisk_positiveRealBoundaryPoint_mem_boundary_of_compl_union
      C.closedDisk0 C.closedDisk1 C.disjoint_closedDisks C.complement C.complement_eq

/--
%%handwave
name:
  The second distinguished disk point lies on the twice-cut boundary
statement:
  The positive-real boundary point of the second removed closed coordinate disk
  lies in the frontier of the twice-cut complement.
proof:
  This is the same local coordinate argument as for the first removed disk,
  with the roles of the two disks exchanged.
-/
theorem radoTwoDiskCut_closedDisk1_positiveRealBoundaryPoint_mem_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    C.closedDisk1.positiveRealBoundaryPoint ∈ C.toPerronOpen.boundary := by
  simpa [RadoTwoDiskCut.toPerronOpen_boundary, Set.union_comm] using
    closedCoordinateDisk_positiveRealBoundaryPoint_mem_boundary_of_compl_union
      C.closedDisk1 C.closedDisk0 C.disjoint_closedDisks.symm C.complement
      (by
        rw [C.complement_eq]
        ext x
        simp [Set.union_comm])

/--
%%handwave
name:
  The local closed complement is outside the first closed coordinate disk
statement:
  A point in the closure of the twice-cut complement and in the first
  coordinate chart cannot have coordinate strictly inside the first removed
  closed disk.
proof:
  If the coordinate were strictly inside the closed disk, a small coordinate
  neighborhood would lie inside the removed disk, hence be disjoint from the
  complement.  This contradicts membership in the closure of the complement.
-/
theorem radoTwoDiskCut_closedDisk0_closedRegion_outside_closedBall
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) {x : X}
    (hx_closure : x ∈ closure C.toPerronOpen.carrier)
    (hx_chart : x ∈ C.closedDisk0.openDisk.carrier) :
    C.closedDisk0.closedRadius ≤
      ‖C.closedDisk0.openDisk.chart x - C.closedDisk0.openDisk.center‖ := by
  by_contra hnot
  have hlt :
      ‖C.closedDisk0.openDisk.chart x - C.closedDisk0.openDisk.center‖ <
        C.closedDisk0.closedRadius := lt_of_not_ge hnot
  let U : Set X :=
    C.closedDisk0.openDisk.chart.source ∩
      C.closedDisk0.openDisk.chart ⁻¹'
        Metric.ball C.closedDisk0.openDisk.center C.closedDisk0.closedRadius
  have hU_open : IsOpen U :=
    C.closedDisk0.openDisk.chart.isOpen_inter_preimage Metric.isOpen_ball
  have hx_source : x ∈ C.closedDisk0.openDisk.chart.source := by
    rw [C.closedDisk0.openDisk.carrier_eq] at hx_chart
    exact hx_chart.1
  have hxU : x ∈ U := by
    refine ⟨hx_source, ?_⟩
    change C.closedDisk0.openDisk.chart x ∈
      Metric.ball C.closedDisk0.openDisk.center C.closedDisk0.closedRadius
    rw [Metric.mem_ball, dist_eq_norm]
    exact hlt
  have hU_nhds : U ∈ 𝓝 x := hU_open.mem_nhds hxU
  rcases mem_closure_iff_nhds.mp hx_closure U hU_nhds with
    ⟨y, hyU, hyΩ⟩
  have hyD0 : y ∈ C.closedDisk0.carrier := by
    rw [C.closedDisk0.carrier_eq]
    refine ⟨hyU.1, ?_⟩
    change C.closedDisk0.openDisk.chart y ∈
      Metric.closedBall C.closedDisk0.openDisk.center C.closedDisk0.closedRadius
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt (by
      simpa [Metric.mem_ball, dist_eq_norm] using hyU.2)
  have hy_complement :
      y ∈ (C.closedDisk0.carrier ∪ C.closedDisk1.carrier)ᶜ := by
    simpa [RadoTwoDiskCut.toPerronOpen_carrier, C.complement_eq] using hyΩ
  exact hy_complement (Or.inl hyD0)

/--
%%handwave
name:
  The local closed complement is outside the second closed coordinate disk
statement:
  A point in the closure of the twice-cut complement and in the second
  coordinate chart cannot have coordinate strictly inside the second removed
  closed disk.
proof:
  This is the same closure argument as for the first removed disk.
-/
theorem radoTwoDiskCut_closedDisk1_closedRegion_outside_closedBall
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) {x : X}
    (hx_closure : x ∈ closure C.toPerronOpen.carrier)
    (hx_chart : x ∈ C.closedDisk1.openDisk.carrier) :
    C.closedDisk1.closedRadius ≤
      ‖C.closedDisk1.openDisk.chart x - C.closedDisk1.openDisk.center‖ := by
  by_contra hnot
  have hlt :
      ‖C.closedDisk1.openDisk.chart x - C.closedDisk1.openDisk.center‖ <
        C.closedDisk1.closedRadius := lt_of_not_ge hnot
  let U : Set X :=
    C.closedDisk1.openDisk.chart.source ∩
      C.closedDisk1.openDisk.chart ⁻¹'
        Metric.ball C.closedDisk1.openDisk.center C.closedDisk1.closedRadius
  have hU_open : IsOpen U :=
    C.closedDisk1.openDisk.chart.isOpen_inter_preimage Metric.isOpen_ball
  have hx_source : x ∈ C.closedDisk1.openDisk.chart.source := by
    rw [C.closedDisk1.openDisk.carrier_eq] at hx_chart
    exact hx_chart.1
  have hxU : x ∈ U := by
    refine ⟨hx_source, ?_⟩
    change C.closedDisk1.openDisk.chart x ∈
      Metric.ball C.closedDisk1.openDisk.center C.closedDisk1.closedRadius
    rw [Metric.mem_ball, dist_eq_norm]
    exact hlt
  have hU_nhds : U ∈ 𝓝 x := hU_open.mem_nhds hxU
  rcases mem_closure_iff_nhds.mp hx_closure U hU_nhds with
    ⟨y, hyU, hyΩ⟩
  have hyD1 : y ∈ C.closedDisk1.carrier := by
    rw [C.closedDisk1.carrier_eq]
    refine ⟨hyU.1, ?_⟩
    change C.closedDisk1.openDisk.chart y ∈
      Metric.closedBall C.closedDisk1.openDisk.center C.closedDisk1.closedRadius
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt (by
      simpa [Metric.mem_ball, dist_eq_norm] using hyU.2)
  have hy_complement :
      y ∈ (C.closedDisk0.carrier ∪ C.closedDisk1.carrier)ᶜ := by
    simpa [RadoTwoDiskCut.toPerronOpen_carrier, C.complement_eq] using hyΩ
  exact hy_complement (Or.inr hyD1)

/--
%%handwave
name:
  Exterior tangent disk at the first removed coordinate disk
statement:
  At the positive-real boundary point of the first removed closed coordinate
  disk, the twice-cut complement has an exterior tangent disk in the same
  coordinate chart.
proof:
  In the chart of the first coordinate disk, the removed disk is the closed
  Euclidean disk \(\overline B(c,r)\).  At \(c+r\), take the Euclidean disk
  with center \(c+r/2\) and radius \(r/2\).  This disk lies inside the removed
  closed disk and is tangent to it at \(c+r\).  The local closed complement
  lies outside this tangent disk, and equality of the distance to its center
  occurs only at the tangency point.
-/
theorem radoTwoDiskCut_closedDisk0_positiveRealBoundaryPoint_exterior_tangent_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    C.closedDisk0.positiveRealBoundaryPoint ∈ C.toPerronOpen.boundary ∧
      ∃ N : Set X, ∃ c : ℂ, ∃ R : ℝ,
        IsOpen N ∧
          C.closedDisk0.positiveRealBoundaryPoint ∈ N ∧
            N ⊆ C.closedDisk0.openDisk.chart.source ∧
              0 < R ∧
                (∀ x ∈ closure C.toPerronOpen.carrier ∩ N,
                  R ≤ ‖C.closedDisk0.openDisk.chart x - c‖) ∧
                  (∀ x ∈ closure C.toPerronOpen.carrier ∩ N,
                    ‖C.closedDisk0.openDisk.chart x - c‖ = R ↔
                      x = C.closedDisk0.positiveRealBoundaryPoint) := by
  let D := C.closedDisk0
  let N : Set X := D.openDisk.carrier
  let q : ℂ := D.openDisk.center + ((D.closedRadius / 2 : ℝ) : ℂ)
  let R : ℝ := D.closedRadius / 2
  refine ⟨radoTwoDiskCut_closedDisk0_positiveRealBoundaryPoint_mem_boundary C,
    N, q, R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.openDisk.isOpen
  · exact D.subset_openDisk D.positiveRealBoundaryPoint_mem_carrier
  · intro x hx
    exact (by
      dsimp [N] at hx
      rw [D.openDisk.carrier_eq] at hx
      exact hx.1)
  · dsimp [R]
    linarith [D.closedRadius_pos]
  · intro x hx
    have houtside :
        D.closedRadius ≤ ‖D.openDisk.chart x - D.openDisk.center‖ :=
      radoTwoDiskCut_closedDisk0_closedRegion_outside_closedBall C hx.1 hx.2
    simpa [D, q, R] using
      complex_internalTangentDisk_distance_le_of_closedBall_exterior
        D.closedRadius_pos houtside
  · intro x hx
    constructor
    · intro hdist
      have houtside :
          D.closedRadius ≤ ‖D.openDisk.chart x - D.openDisk.center‖ :=
        radoTwoDiskCut_closedDisk0_closedRegion_outside_closedBall C hx.1 hx.2
      have hchart_eq :
          D.openDisk.chart x =
            D.openDisk.center + (D.closedRadius : ℂ) := by
        exact complex_eq_positiveRealBoundary_of_closedBall_exterior_and_internalTangent
          D.closedRadius_pos houtside (by simpa [D, q, R] using hdist)
      have hxsource : x ∈ D.openDisk.chart.source := by
        have hxN : x ∈ N := hx.2
        dsimp [N] at hxN
        rw [D.openDisk.carrier_eq] at hxN
        exact hxN.1
      calc
        x = D.openDisk.chart.symm (D.openDisk.chart x) :=
          (D.openDisk.chart.left_inv hxsource).symm
        _ = D.positiveRealBoundaryPoint := by
          rw [hchart_eq]
          rfl
    · intro hxp
      subst hxp
      rw [D.chart_positiveRealBoundaryPoint]
      have hsub :
          D.openDisk.center + (D.closedRadius : ℂ) -
              (D.openDisk.center + ((D.closedRadius / 2 : ℝ) : ℂ)) =
            ((D.closedRadius / 2 : ℝ) : ℂ) := by
        calc
          D.openDisk.center + (D.closedRadius : ℂ) -
              (D.openDisk.center + ((D.closedRadius / 2 : ℝ) : ℂ)) =
            (D.closedRadius : ℂ) - ((D.closedRadius / 2 : ℝ) : ℂ) := by
              abel
          _ = ((D.closedRadius / 2 : ℝ) : ℂ) := by
            exact_mod_cast
              (by ring : D.closedRadius - D.closedRadius / 2 = D.closedRadius / 2)
      rw [hsub]
      exact Complex.norm_of_nonneg (by linarith [D.closedRadius_pos])

/--
%%handwave
name:
  Exterior tangent disk at the second removed coordinate disk
statement:
  At the positive-real boundary point of the second removed closed coordinate
  disk, the twice-cut complement has an exterior tangent disk in the same
  coordinate chart.
proof:
  This is the same Euclidean construction as for the first removed disk, using
  the coordinate chart of the second disk.
-/
theorem radoTwoDiskCut_closedDisk1_positiveRealBoundaryPoint_exterior_tangent_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    C.closedDisk1.positiveRealBoundaryPoint ∈ C.toPerronOpen.boundary ∧
      ∃ N : Set X, ∃ c : ℂ, ∃ R : ℝ,
        IsOpen N ∧
          C.closedDisk1.positiveRealBoundaryPoint ∈ N ∧
            N ⊆ C.closedDisk1.openDisk.chart.source ∧
              0 < R ∧
                (∀ x ∈ closure C.toPerronOpen.carrier ∩ N,
                  R ≤ ‖C.closedDisk1.openDisk.chart x - c‖) ∧
                  (∀ x ∈ closure C.toPerronOpen.carrier ∩ N,
                    ‖C.closedDisk1.openDisk.chart x - c‖ = R ↔
                      x = C.closedDisk1.positiveRealBoundaryPoint) := by
  let D := C.closedDisk1
  let N : Set X := D.openDisk.carrier
  let q : ℂ := D.openDisk.center + ((D.closedRadius / 2 : ℝ) : ℂ)
  let R : ℝ := D.closedRadius / 2
  refine ⟨radoTwoDiskCut_closedDisk1_positiveRealBoundaryPoint_mem_boundary C,
    N, q, R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.openDisk.isOpen
  · exact D.subset_openDisk D.positiveRealBoundaryPoint_mem_carrier
  · intro x hx
    exact (by
      dsimp [N] at hx
      rw [D.openDisk.carrier_eq] at hx
      exact hx.1)
  · dsimp [R]
    linarith [D.closedRadius_pos]
  · intro x hx
    have houtside :
        D.closedRadius ≤ ‖D.openDisk.chart x - D.openDisk.center‖ :=
      radoTwoDiskCut_closedDisk1_closedRegion_outside_closedBall C hx.1 hx.2
    simpa [D, q, R] using
      complex_internalTangentDisk_distance_le_of_closedBall_exterior
        D.closedRadius_pos houtside
  · intro x hx
    constructor
    · intro hdist
      have houtside :
          D.closedRadius ≤ ‖D.openDisk.chart x - D.openDisk.center‖ :=
        radoTwoDiskCut_closedDisk1_closedRegion_outside_closedBall C hx.1 hx.2
      have hchart_eq :
          D.openDisk.chart x =
            D.openDisk.center + (D.closedRadius : ℂ) := by
        exact complex_eq_positiveRealBoundary_of_closedBall_exterior_and_internalTangent
          D.closedRadius_pos houtside (by simpa [D, q, R] using hdist)
      have hxsource : x ∈ D.openDisk.chart.source := by
        have hxN : x ∈ N := hx.2
        dsimp [N] at hxN
        rw [D.openDisk.carrier_eq] at hxN
        exact hxN.1
      calc
        x = D.openDisk.chart.symm (D.openDisk.chart x) :=
          (D.openDisk.chart.left_inv hxsource).symm
        _ = D.positiveRealBoundaryPoint := by
          rw [hchart_eq]
          rfl
    · intro hxp
      subst hxp
      rw [D.chart_positiveRealBoundaryPoint]
      have hsub :
          D.openDisk.center + (D.closedRadius : ℂ) -
              (D.openDisk.center + ((D.closedRadius / 2 : ℝ) : ℂ)) =
            ((D.closedRadius / 2 : ℝ) : ℂ) := by
        calc
          D.openDisk.center + (D.closedRadius : ℂ) -
              (D.openDisk.center + ((D.closedRadius / 2 : ℝ) : ℂ)) =
            (D.closedRadius : ℂ) - ((D.closedRadius / 2 : ℝ) : ℂ) := by
              abel
          _ = ((D.closedRadius / 2 : ℝ) : ℂ) := by
            exact_mod_cast
              (by ring : D.closedRadius - D.closedRadius / 2 = D.closedRadius / 2)
      rw [hsub]
      exact Complex.norm_of_nonneg (by linarith [D.closedRadius_pos])

/--
%%handwave
name:
  The first removed disk gives a local Perron-open barrier
statement:
  The positive-real boundary point of the first removed disk admits a local
  Perron-open barrier for the twice-cut complement.
proof:
  Apply the explicit logarithmic-potential barrier construction to the
  exterior tangent disk at that point.
-/
theorem radoTwoDiskCut_closedDisk0_positiveRealBoundaryPoint_has_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    HasLocalPerronOpenBarrierAt C.toPerronOpen
      C.closedDisk0.positiveRealBoundaryPoint := by
  rcases radoTwoDiskCut_closedDisk0_positiveRealBoundaryPoint_exterior_tangent_disk C with
    ⟨hp, N, c, R, hN_open, hpN, hN_source, hRpos, houtside, htangent⟩
  exact exteriorTangentDisk_logPotential_has_local_perronOpen_barrier
    C.toPerronOpen hp C.closedDisk0.openDisk.chart_mem_atlas
    hN_open hpN hN_source hRpos houtside htangent

/--
%%handwave
name:
  The second removed disk gives a local Perron-open barrier
statement:
  The positive-real boundary point of the second removed disk admits a local
  Perron-open barrier for the twice-cut complement.
proof:
  Apply the explicit logarithmic-potential barrier construction to the
  exterior tangent disk at that point.
-/
theorem radoTwoDiskCut_closedDisk1_positiveRealBoundaryPoint_has_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    HasLocalPerronOpenBarrierAt C.toPerronOpen
      C.closedDisk1.positiveRealBoundaryPoint := by
  rcases radoTwoDiskCut_closedDisk1_positiveRealBoundaryPoint_exterior_tangent_disk C with
    ⟨hp, N, c, R, hN_open, hpN, hN_source, hRpos, houtside, htangent⟩
  exact exteriorTangentDisk_logPotential_has_local_perronOpen_barrier
    C.toPerronOpen hp C.closedDisk1.openDisk.chart_mem_atlas
    hN_open hpN hN_source hRpos houtside htangent

/--
%%handwave
name:
  Twice-cut boundary points with local barriers
statement:
  The two removed coordinate disks contain boundary points of the twice-cut
  complement, and each such point admits a local Perron barrier for the open
  complement.
proof:
  In the coordinate chart of each removed closed disk, take a point on the
  coordinate circle.  The complement is locally the outside of a smooth disk,
  so the signed radial coordinate gives a positive superharmonic local barrier
  that vanishes exactly at the chosen boundary point.
-/
theorem exists_radoTwoDiskCut_boundary_points_with_local_barriers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    ∃ p0 p1 : X,
      p0 ∈ C.toPerronOpen.boundary ∧
        p0 ∈ C.closedDisk0.carrier ∧
          HasLocalPerronOpenBarrierAt C.toPerronOpen p0 ∧
      p1 ∈ C.toPerronOpen.boundary ∧
        p1 ∈ C.closedDisk1.carrier ∧
          HasLocalPerronOpenBarrierAt C.toPerronOpen p1 := by
  refine ⟨C.closedDisk0.positiveRealBoundaryPoint,
    C.closedDisk1.positiveRealBoundaryPoint, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (radoTwoDiskCut_closedDisk0_positiveRealBoundaryPoint_exterior_tangent_disk C).1
  · exact C.closedDisk0.positiveRealBoundaryPoint_mem_carrier
  · exact radoTwoDiskCut_closedDisk0_positiveRealBoundaryPoint_has_local_barrier C
  · exact
      (radoTwoDiskCut_closedDisk1_positiveRealBoundaryPoint_exterior_tangent_disk C).1
  · exact C.closedDisk1.positiveRealBoundaryPoint_mem_carrier
  · exact radoTwoDiskCut_closedDisk1_positiveRealBoundaryPoint_has_local_barrier C

/--
%%handwave
name:
  Upper barrier estimate at a zero boundary value
statement:
  At a locally regular boundary point where the twice-cut boundary value is
  \(0\), the bounded Perron-open envelope is eventually smaller than every
  positive number.
proof:
  The local barrier is positive away from the boundary point and vanishes at
  it.  Comparing every bounded admissible subfunction with a small positive
  multiple of this barrier gives an upper bound near the point; letting the
  multiple tend to zero gives the estimate.
-/
theorem radoTwoDiskBoundedPerronOpenEnvelope_eventually_lt_of_zero_boundary_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) {p : X}
    (hp : HasLocalPerronOpenBarrierAt C.toPerronOpen p)
    (hp_value : radoTwoDiskBoundaryValue C p = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[C.toPerronOpen.carrier] p,
      radoTwoDiskBoundedPerronOpenEnvelope C x < ε := by
  have h :=
    boundedPerronOpenEnvelope_eventually_lt_boundary_add_of_local_barrier
      C.toPerronOpen (radoTwoDiskPerronOpenBoundaryData C) 1
      ⟨fun _ : X ↦ 0, radoTwoDiskBoundedPerronOpenAdmissible_zero C⟩
      hp hε
  simpa [radoTwoDiskBoundedPerronOpenEnvelope,
      radoTwoDiskPerronOpenBoundaryData, hp_value] using h

/--
%%handwave
name:
  Lower barrier estimate at a one boundary value
statement:
  At a locally regular boundary point where the twice-cut boundary value is
  \(1\), the bounded Perron-open envelope is eventually larger than
  \(1-\varepsilon\) for every positive \(\varepsilon\).
proof:
  The general lower local-barrier estimate applies because the boundary data
  is globally bounded below by \(0\), the envelope family is bounded above by
  \(1\), and the boundary value at the chosen point is \(1\).
-/
theorem radoTwoDiskBoundedPerronOpenEnvelope_eventually_gt_of_one_boundary_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) {p : X}
    (hp : HasLocalPerronOpenBarrierAt C.toPerronOpen p)
    (hp_value : radoTwoDiskBoundaryValue C p = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[C.toPerronOpen.carrier] p,
      1 - ε < radoTwoDiskBoundedPerronOpenEnvelope C x := by
  have hboundary_nonneg :
      ∀ x ∈ C.toPerronOpen.boundary,
        (0 : ℝ) ≤ radoTwoDiskPerronOpenBoundaryData C x := by
    intro x _hx
    classical
    by_cases hx0 : x ∈ C.closedDisk0.carrier
    · simp [radoTwoDiskPerronOpenBoundaryData, radoTwoDiskBoundaryValue, hx0]
    · by_cases hx1 : x ∈ C.closedDisk1.carrier
      · simp [radoTwoDiskPerronOpenBoundaryData, radoTwoDiskBoundaryValue, hx0, hx1]
      · simp [radoTwoDiskPerronOpenBoundaryData, radoTwoDiskBoundaryValue, hx0, hx1]
  have hpM : radoTwoDiskPerronOpenBoundaryData C p ≤ (1 : ℝ) := by
    simp [radoTwoDiskPerronOpenBoundaryData, hp_value]
  have h :=
    boundedPerronOpenEnvelope_eventually_gt_boundary_sub_of_local_barrier
      C.toPerronOpen (radoTwoDiskPerronOpenBoundaryData C) 1
      (c := 0) hboundary_nonneg (by norm_num) hp hpM hε
  simpa [radoTwoDiskBoundedPerronOpenEnvelope,
      radoTwoDiskPerronOpenBoundaryData, hp_value] using h

/--
%%handwave
name:
  Bounded Perron-open envelopes recover locally regular boundary values
statement:
  At a locally regular boundary point of the twice-cut complement, the bounded
  Perron-open envelope tends to the prescribed boundary value.
proof:
  A boundary point of the twice-cut complement lies on one of the two removed
  disks.  On the first disk the boundary value is \(0\), so
  [the envelope is eventually smaller than every positive
  number](lean:JJMath.Uniformization.radoTwoDiskBoundedPerronOpenEnvelope_eventually_lt_of_zero_boundary_local_barrier)
  and the zero subfunction gives the lower bound.  On the second disk the
  boundary value is \(1\), so
  [the envelope is eventually larger than \(1-\varepsilon\)](lean:JJMath.Uniformization.radoTwoDiskBoundedPerronOpenEnvelope_eventually_gt_of_one_boundary_local_barrier)
  and boundedness by \(1\) gives the upper bound.
-/
theorem radoTwoDiskBoundedPerronOpenEnvelope_tends_to_boundaryValue_of_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) {p : X}
    (hp : HasLocalPerronOpenBarrierAt C.toPerronOpen p) :
    Filter.Tendsto (radoTwoDiskBoundedPerronOpenEnvelope C)
      (𝓝[C.toPerronOpen.carrier] p)
      (𝓝 (radoTwoDiskBoundaryValue C p)) := by
  rw [tendsto_order]
  rcases C.boundary_subset_closedDisks hp.1 with hp0 | hp1
  · have hp_value : radoTwoDiskBoundaryValue C p = 0 :=
      radoTwoDiskBoundaryValue_eq_zero_on_closedDisk0 C hp0
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with x hxΩ
      have hnonneg := radoTwoDiskBoundedPerronOpenEnvelope_nonnegative C hxΩ
      rw [hp_value] at ha
      linarith
    · intro a ha
      rw [hp_value] at ha
      filter_upwards [
        radoTwoDiskBoundedPerronOpenEnvelope_eventually_lt_of_zero_boundary_local_barrier
          C hp hp_value ha
      ] with x hx
      exact hx
  · have hp_value : radoTwoDiskBoundaryValue C p = 1 :=
      radoTwoDiskBoundaryValue_eq_one_on_closedDisk1 C hp1
    constructor
    · intro a ha
      rw [hp_value] at ha
      have hε : 0 < 1 - a := by linarith
      filter_upwards [
        radoTwoDiskBoundedPerronOpenEnvelope_eventually_gt_of_one_boundary_local_barrier
          C hp hp_value hε
      ] with x hx
      linarith
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with x hxΩ
      have hle := radoTwoDiskBoundedPerronOpenEnvelope_le_one C hxΩ
      rw [hp_value] at ha
      linarith

theorem exists_mem_lt_of_tendsto_nhdsWithin_of_mem_closure
    {X : Type} [TopologicalSpace X] {s : Set X} {p : X} {f : X → ℝ}
    {a b : ℝ} (hp : p ∈ closure s)
    (hf : Filter.Tendsto f (𝓝[s] p) (𝓝 a)) (hab : a < b) :
    ∃ x : X, x ∈ s ∧ f x < b := by
  haveI : (𝓝[s] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hnear : ∀ᶠ x in 𝓝[s] p, f x < b :=
    hf.eventually (Iio_mem_nhds hab)
  rcases (hnear.and self_mem_nhdsWithin).exists with ⟨x, hxlt, hxs⟩
  exact ⟨x, hxs, hxlt⟩

theorem exists_mem_gt_of_tendsto_nhdsWithin_of_mem_closure
    {X : Type} [TopologicalSpace X] {s : Set X} {p : X} {f : X → ℝ}
    {a b : ℝ} (hp : p ∈ closure s)
    (hf : Filter.Tendsto f (𝓝[s] p) (𝓝 a)) (hab : b < a) :
    ∃ x : X, x ∈ s ∧ b < f x := by
  haveI : (𝓝[s] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hnear : ∀ᶠ x in 𝓝[s] p, b < f x :=
    hf.eventually (Ioi_mem_nhds hab)
  rcases (hnear.and self_mem_nhdsWithin).exists with ⟨x, hxgt, hxs⟩
  exact ⟨x, hxs, hxgt⟩

/--
%%handwave
name:
  The bounded twice-cut Perron-open envelope has separated interior values
statement:
  The bounded Perron-open envelope takes a value less than \(1/3\) near the
  first boundary component and a value greater than \(2/3\) near the second
  boundary component.
proof:
  Choose locally regular boundary points on the two removed disks.  Boundary
  convergence gives limits \(0\) and \(1\) there, and each boundary point lies
  in the closure of the open complement.  Therefore nearby points inside the
  complement have values arbitrarily close to those limiting values.
-/
theorem exists_radoTwoDiskBoundedPerronOpenEnvelope_values_near_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    ∃ x y : C.complement,
      radoTwoDiskBoundedPerronOpenEnvelope C x < (1 / 3 : ℝ) ∧
        (2 / 3 : ℝ) < radoTwoDiskBoundedPerronOpenEnvelope C y := by
  rcases exists_radoTwoDiskCut_boundary_points_with_local_barriers C with
    ⟨p0, p1, hp0_boundary, hp0_disk, hp0_barrier,
      hp1_boundary, hp1_disk, hp1_barrier⟩
  have hp0_value : radoTwoDiskBoundaryValue C p0 = 0 :=
    radoTwoDiskBoundaryValue_eq_zero_on_closedDisk0 C hp0_disk
  have hp1_value : radoTwoDiskBoundaryValue C p1 = 1 :=
    radoTwoDiskBoundaryValue_eq_one_on_closedDisk1 C hp1_disk
  have hp0_closure : p0 ∈ closure (C.complement : Set X) := by
    have hp0_frontier : p0 ∈ frontier (C.complement : Set X) := by
      simpa [RadoTwoDiskCut.toPerronOpen_boundary] using hp0_boundary
    exact frontier_subset_closure hp0_frontier
  have hp1_closure : p1 ∈ closure (C.complement : Set X) := by
    have hp1_frontier : p1 ∈ frontier (C.complement : Set X) := by
      simpa [RadoTwoDiskCut.toPerronOpen_boundary] using hp1_boundary
    exact frontier_subset_closure hp1_frontier
  have htendsto0 :
      Filter.Tendsto (radoTwoDiskBoundedPerronOpenEnvelope C)
        (𝓝[(C.complement : Set X)] p0) (𝓝 (0 : ℝ)) := by
    have htendsto :=
      radoTwoDiskBoundedPerronOpenEnvelope_tends_to_boundaryValue_of_local_barrier
        C hp0_barrier
    simpa [RadoTwoDiskCut.toPerronOpen_carrier, hp0_value] using htendsto
  have htendsto1 :
      Filter.Tendsto (radoTwoDiskBoundedPerronOpenEnvelope C)
        (𝓝[(C.complement : Set X)] p1) (𝓝 (1 : ℝ)) := by
    have htendsto :=
      radoTwoDiskBoundedPerronOpenEnvelope_tends_to_boundaryValue_of_local_barrier
        C hp1_barrier
    simpa [RadoTwoDiskCut.toPerronOpen_carrier, hp1_value] using htendsto
  rcases exists_mem_lt_of_tendsto_nhdsWithin_of_mem_closure
      hp0_closure htendsto0 (by norm_num : (0 : ℝ) < 1 / 3) with
    ⟨x, hx_complement, hxlt⟩
  rcases exists_mem_gt_of_tendsto_nhdsWithin_of_mem_closure
      hp1_closure htendsto1 (by norm_num : (2 / 3 : ℝ) < 1) with
    ⟨y, hy_complement, hygt⟩
  exact ⟨⟨x, hx_complement⟩, ⟨y, hy_complement⟩, hxlt, hygt⟩

/--
%%handwave
name:
  The bounded twice-cut Perron-open envelope separates two points
statement:
  The bounded Perron-open envelope for the twice-cut problem takes two
  different values in the complement.
proof:
  Barriers at the two smooth boundary components show that the envelope tends
  to the prescribed values \(0\) and \(1\) at the two removed disks.  A constant
  harmonic function could not have two distinct boundary limits.
-/
theorem exists_radoTwoDiskBoundedPerronOpenEnvelope_pair_ne
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    ∃ x y : C.complement,
      radoTwoDiskBoundedPerronOpenEnvelope C x ≠
        radoTwoDiskBoundedPerronOpenEnvelope C y := by
  rcases exists_radoTwoDiskBoundedPerronOpenEnvelope_values_near_boundary C with
    ⟨x, y, hxlt, hygt⟩
  refine ⟨x, y, ?_⟩
  intro hxy
  have hcontr : (2 / 3 : ℝ) < 1 / 3 := by
    calc
      (2 / 3 : ℝ) < radoTwoDiskBoundedPerronOpenEnvelope C y := hygt
      _ = radoTwoDiskBoundedPerronOpenEnvelope C x := by rw [← hxy]
      _ < (1 / 3 : ℝ) := hxlt
  norm_num at hcontr

/--
%%handwave
name:
  The bounded twice-cut Perron-open envelope has nontrivial range
statement:
  The bounded Perron-open envelope for the twice-cut problem is nonconstant on
  the complement.
proof:
  Since [the envelope takes two different
  values](lean:JJMath.Uniformization.exists_radoTwoDiskBoundedPerronOpenEnvelope_pair_ne),
  its range has at least two distinct points.
-/
theorem radoTwoDiskBoundedPerronOpenEnvelope_nonconstant
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    (Set.range (fun x : C.complement ↦
      radoTwoDiskBoundedPerronOpenEnvelope C x)).Nontrivial := by
  rcases exists_radoTwoDiskBoundedPerronOpenEnvelope_pair_ne C with ⟨x, y, hxy⟩
  exact Set.nontrivial_of_mem_mem_ne
    (show radoTwoDiskBoundedPerronOpenEnvelope C x ∈
      Set.range (fun x : C.complement ↦
        radoTwoDiskBoundedPerronOpenEnvelope C x) from
      ⟨x, rfl⟩)
    (show radoTwoDiskBoundedPerronOpenEnvelope C y ∈
      Set.range (fun x : C.complement ↦
        radoTwoDiskBoundedPerronOpenEnvelope C x) from
      ⟨y, rfl⟩)
    hxy

/--
%%handwave
name:
  Perron's method gives a harmonic separator on the twice-cut complement
statement:
  The complement in a twice-cut Radó domain carries a nonconstant harmonic
  function.
proof:
  Regard the twice-cut complement as an open Perron region in the ambient
  surface.  The [bounded Perron envelope is
  harmonic](lean:JJMath.Uniformization.radoTwoDiskBoundedPerronOpenEnvelope_harmonic_on_complement),
  and [the barrier argument gives two distinct
  values](lean:JJMath.Uniformization.radoTwoDiskBoundedPerronOpenEnvelope_nonconstant).
-/
theorem radoTwoDiskCut_has_harmonic_separator
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) :
    ∃ h : C.complement → ℝ,
      IsHarmonicOnSurface (Set.univ : Set C.complement) h ∧
        (Set.range h).Nontrivial := by
  exact ⟨fun x : C.complement ↦ radoTwoDiskBoundedPerronOpenEnvelope C x,
    radoTwoDiskBoundedPerronOpenEnvelope_harmonic_on_complement C,
    radoTwoDiskBoundedPerronOpenEnvelope_nonconstant C⟩

/--
%%handwave
name:
  Local holomorphic real parts in chart balls
statement:
  If a real-valued function is harmonic on a surface, then on every coordinate
  ball inside a chart target it is the real part of a holomorphic function in
  that coordinate.
proof:
  The surface harmonicity definition says precisely that the coordinate
  expression is harmonic on the chart target.  Restrict to the given Euclidean
  ball and apply Mathlib's plane harmonic-conjugate theorem.
-/
theorem harmonicOnSurface_exists_analyticOnNhd_chart_ball_re_eq
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    {u : Z → ℝ}
    (hu : IsHarmonicOnSurface (Set.univ : Set Z) u)
    (e : OpenPartialHomeomorph Z ℂ) (he : e ∈ atlas ℂ Z)
    {c : ℂ} {R : ℝ}
    (hball_subset : Metric.ball c R ⊆ e.target) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (Metric.ball c R) ∧
        ∀ z ∈ Metric.ball c R, (F z).re = u (e.symm z) := by
  have hHarm :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ u (e.symm z)) (Metric.ball c R) :=
    (hu e he).mono (by
      intro z hz
      exact ⟨hball_subset hz, by simp⟩)
  rcases hHarm.exists_analyticOnNhd_ball_re_eq with ⟨F, hF_hol, hF_re⟩
  exact ⟨F, hF_hol, hF_re⟩

/--
%%handwave
name:
  Equal real parts differ by an imaginary constant
statement:
  On a connected open plane domain, two holomorphic functions with the same
  real part differ by an imaginary constant.
proof:
  The difference is holomorphic and has constant real part zero.  Mathlib's
  open mapping theorem consequence for holomorphic functions with constant
  real part makes the difference constant, and the constant must be purely
  imaginary.
-/
theorem analyticOnNhd_eq_add_imaginary_constant_of_re_eq
    {U : Set ℂ} {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (hre : ∀ z ∈ U, (F z).re = (G z).re) :
    ∃ c : ℝ, ∀ z ∈ U, F z = G z + c * Complex.I := by
  have hdiff_hol : AnalyticOnNhd ℂ (fun z ↦ F z - G z) U :=
    hF.sub hG
  have hdiff_re : ∀ z ∈ U, ((fun z ↦ F z - G z) z).re = (0 : ℝ) := by
    intro z hz
    rw [Complex.sub_re, hre z hz]
    simp
  rcases AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const hdiff_hol
      hdiff_re hU_open hU_connected with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro z hz
  have hdiff : F z - G z = c * Complex.I := by
    simpa using hc z hz
  calc
    F z = G z + (F z - G z) := by abel
    _ = G z + c * Complex.I := by rw [hdiff]

/--
%%handwave
name:
  Imaginary overlap constants add on triple overlaps
statement:
  If three local holomorphic potentials differ pairwise by imaginary constants
  on a nonempty overlap, then the direct transition constant is the sum of the
  two intermediate transition constants.
proof:
  Evaluate at one point of the overlap and take imaginary parts.
-/
theorem imaginaryConstant_overlap_cocycle
    {U : Set ℂ} (hU_nonempty : U.Nonempty)
    {F G H : ℂ → ℂ} {cFG cGH cFH : ℝ}
    (hFG : ∀ z ∈ U, F z = G z + cFG * Complex.I)
    (hGH : ∀ z ∈ U, G z = H z + cGH * Complex.I)
    (hFH : ∀ z ∈ U, F z = H z + cFH * Complex.I) :
    cFH = cFG + cGH := by
  rcases hU_nonempty with ⟨z, hz⟩
  have h : H z + cGH * Complex.I + cFG * Complex.I =
      H z + cFH * Complex.I := by
    rw [← hGH z hz, ← hFG z hz, hFH z hz]
  have him := congrArg Complex.im h
  simp [Complex.add_im, add_comm, add_left_comm] at him
  linarith

/--
%%handwave
name:
  Local branch of a holomorphic real part
statement:
  A local branch of a holomorphic real part for \(u\) consists of a surface
  neighborhood described by a complex chart and a coordinate-domain
  holomorphic function whose real part is \(u\) in that chart.
-/
structure SurfaceHolomorphicRealPartBranch
    (Z : Type) [TopologicalSpace Z] [ChartedSpace ℂ Z]
    (u : Z → ℝ) where
  /-- The surface source of the branch. -/
  source : Set Z
  /-- The source is open. -/
  source_open : IsOpen source
  /-- The complex chart used to express the branch. -/
  chart : OpenPartialHomeomorph Z ℂ
  /-- The chart belongs to the surface atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ Z
  /-- The coordinate-domain on which the holomorphic representative is defined. -/
  coordinateSource : Set ℂ
  /-- The coordinate-domain is open. -/
  coordinateSource_open : IsOpen coordinateSource
  /-- The coordinate-domain lies in the chart target. -/
  coordinateSource_subset_chart_target : coordinateSource ⊆ chart.target
  /-- The surface source is the inverse image of the coordinate-domain. -/
  source_eq : source = chart.source ∩ chart ⁻¹' coordinateSource
  /-- The holomorphic coordinate representative. -/
  potential : ℂ → ℂ
  /-- The coordinate representative is holomorphic. -/
  potential_holomorphic : AnalyticOnNhd ℂ potential coordinateSource
  /-- Its real part is the coordinate expression of \(u\). -/
  potential_re_eq : ∀ z ∈ coordinateSource, (potential z).re = u (chart.symm z)

namespace SurfaceHolomorphicRealPartBranch

variable {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z] {u : Z → ℝ}

theorem mem_chart_source_of_mem_source
    (B : SurfaceHolomorphicRealPartBranch Z u)
    {x : Z} (hx : x ∈ B.source) :
    x ∈ B.chart.source := by
  rw [B.source_eq] at hx
  exact hx.1

theorem chart_mem_coordinateSource_of_mem_source
    (B : SurfaceHolomorphicRealPartBranch Z u)
    {x : Z} (hx : x ∈ B.source) :
    B.chart x ∈ B.coordinateSource := by
  rw [B.source_eq] at hx
  exact hx.2

/-- The surface-valued branch function determined by the coordinate potential. -/
noncomputable def toSurfaceFunction (B : SurfaceHolomorphicRealPartBranch Z u) :
    B.source → ℂ :=
  fun x ↦ B.potential (B.chart (x : Z))
/--
%%handwave
name:
  The real part of a local branch recovers the surface function
statement:
  If \(B\) is a local holomorphic real-part branch for \(u:Z\to\mathbb R\),
  then for every \(x\) in the source of \(B\),
  \[\operatorname{Re}(B(x))=u(x).\]
proof:
  The coordinate potential has real part \(u\) after applying the inverse
  chart.  Since \(x\) lies in the chart source, the chart followed by its
  inverse returns \(x\).
-/
theorem toSurfaceFunction_re_eq
    (B : SurfaceHolomorphicRealPartBranch Z u) (x : B.source) :
    (B.toSurfaceFunction x).re = u x := by
  have hx_source : (x : Z) ∈ B.source := x.2
  have hx_chart : (x : Z) ∈ B.chart.source :=
    B.mem_chart_source_of_mem_source hx_source
  have hx_coord : B.chart (x : Z) ∈ B.coordinateSource :=
    B.chart_mem_coordinateSource_of_mem_source hx_source
  rw [toSurfaceFunction, B.potential_re_eq (B.chart (x : Z)) hx_coord,
    B.chart.left_inv hx_chart]

/-- The ambient function represented by a local holomorphic real-part branch. -/
noncomputable def toSurfaceTotalFunction (B : SurfaceHolomorphicRealPartBranch Z u) : Z → ℂ :=
  fun x ↦ B.potential (B.chart x)

theorem toSurfaceTotalFunction_re_eq
    (B : SurfaceHolomorphicRealPartBranch Z u)
    {x : Z} (hx : x ∈ B.source) :
    (B.toSurfaceTotalFunction x).re = u x := by
  have hx_chart : x ∈ B.chart.source :=
    B.mem_chart_source_of_mem_source hx
  have hx_coord : B.chart x ∈ B.coordinateSource :=
    B.chart_mem_coordinateSource_of_mem_source hx
  rw [toSurfaceTotalFunction, B.potential_re_eq (B.chart x) hx_coord,
    B.chart.left_inv hx_chart]

/--
%%handwave
name:
  Local real-part branches are holomorphic on their surface source
statement:
  The surface function represented by a local holomorphic real-part branch is
  holomorphic on the branch source.
proof:
  It is the composition of the complex chart with the holomorphic coordinate
  potential.
-/
theorem toSurfaceTotalFunction_mdifferentiableOn
    [ComplexOneManifold Z]
    (B : SurfaceHolomorphicRealPartBranch Z u) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      B.toSurfaceTotalFunction B.source := by
  have hsource_chart : B.source ⊆ B.chart.source := by
    intro x hx
    exact B.mem_chart_source_of_mem_source hx
  have hchart :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) B.chart B.source :=
    (mdifferentiableOn_atlas (I := 𝓘(ℂ)) B.chart_mem_atlas).mono
      hsource_chart
  have hpotential_diff :
      DifferentiableOn ℂ B.potential B.coordinateSource :=
    B.potential_holomorphic.differentiableOn
  have hpotential :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        B.potential B.coordinateSource := by
    exact mdifferentiableOn_iff_differentiableOn.mpr hpotential_diff
  have hmaps :
      B.source ⊆ B.chart ⁻¹' B.coordinateSource := by
    intro x hx
    exact B.chart_mem_coordinateSource_of_mem_source hx
  simpa [toSurfaceTotalFunction, Function.comp_def] using
    hpotential.comp hchart hmaps

/--
%%handwave
name:
  Matching local real-part branches differ by an imaginary constant
statement:
  On a connected coordinate-domain where two local holomorphic real-part
  branches represent the same surface points, their holomorphic potentials
  differ by an imaginary constant.
proof:
  Both potentials have the same real part there, namely the value of the same
  harmonic function at the same surface point.  Apply [the plane overlap
  lemma](lean:JJMath.Uniformization.analyticOnNhd_eq_add_imaginary_constant_of_re_eq).
-/
theorem potentials_eq_add_imaginary_constant_on_connected_coordinate_subset
    (B C : SurfaceHolomorphicRealPartBranch Z u)
    {U : Set ℂ}
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (hUB : U ⊆ B.coordinateSource) (hUC : U ⊆ C.coordinateSource)
    (hsymm : ∀ z ∈ U, B.chart.symm z = C.chart.symm z) :
    ∃ c : ℝ, ∀ z ∈ U, B.potential z = C.potential z + c * Complex.I := by
  exact analyticOnNhd_eq_add_imaginary_constant_of_re_eq
    (B.potential_holomorphic.mono hUB)
    (C.potential_holomorphic.mono hUC)
    hU_open hU_connected
    (by
      intro z hz
      calc
        (B.potential z).re = u (B.chart.symm z) :=
          B.potential_re_eq z (hUB hz)
        _ = u (C.chart.symm z) := by rw [hsymm z hz]
        _ = (C.potential z).re :=
          (C.potential_re_eq z (hUC hz)).symm)

/--
%%handwave
name:
  Local real-part branches in the same chart differ by an imaginary constant
statement:
  On a connected coordinate-domain contained in the domains of two branches
  written in the same chart, their holomorphic potentials differ by an
  imaginary constant.
proof:
  This is the matching-branch overlap lemma with the identity equality of the
  inverse chart maps.
-/
theorem potentials_eq_add_imaginary_constant_on_connected_coordinate_subset_sameChart
    (B C : SurfaceHolomorphicRealPartBranch Z u)
    {U : Set ℂ}
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (hUB : U ⊆ B.coordinateSource) (hUC : U ⊆ C.coordinateSource)
    (hchart : B.chart = C.chart) :
    ∃ c : ℝ, ∀ z ∈ U, B.potential z = C.potential z + c * Complex.I := by
  exact B.potentials_eq_add_imaginary_constant_on_connected_coordinate_subset C
    hU_open hU_connected hUB hUC (by
      intro z hz
      rw [hchart])

/--
%%handwave
name:
  Chart transitions between local real-part branches are holomorphic
statement:
  On a coordinate-domain contained in one local branch and whose inverse image
  lies in another branch, the transition map from the first coordinates to the
  second coordinates is holomorphic.
proof:
  The inverse of the first chart and the second chart are differentiable maps
  of complex manifolds.  Their composition is differentiable as a map between
  open subsets of \(\mathbb C\), hence analytic on the open coordinate-domain.
-/
theorem transition_analyticOnNhd
    [ComplexOneManifold Z]
    (B C : SurfaceHolomorphicRealPartBranch Z u)
    {U : Set ℂ} (hU_open : IsOpen U)
    (hUB : U ⊆ B.coordinateSource)
    (hBC : ∀ z ∈ U, B.chart.symm z ∈ C.source) :
    AnalyticOnNhd ℂ (fun z ↦ C.chart (B.chart.symm z)) U := by
  have hU_target : U ⊆ B.chart.target := by
    intro z hz
    exact B.coordinateSource_subset_chart_target (hUB hz)
  have hsymm_mdiff :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) B.chart.symm U :=
    (mdifferentiableOn_atlas_symm (I := 𝓘(ℂ)) B.chart_mem_atlas).mono hU_target
  have hchart_mdiff :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) C.chart C.chart.source :=
    mdifferentiableOn_atlas (I := 𝓘(ℂ)) C.chart_mem_atlas
  have hmaps_chart_source :
      U ⊆ B.chart.symm ⁻¹' C.chart.source := by
    intro z hz
    exact C.mem_chart_source_of_mem_source (hBC z hz)
  have hcomp_mdiff :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (C.chart ∘ B.chart.symm) U :=
    hchart_mdiff.comp hsymm_mdiff hmaps_chart_source
  have hcomp_diff :
      DifferentiableOn ℂ (C.chart ∘ B.chart.symm) U := by
    exact mdifferentiableOn_iff_differentiableOn.mp hcomp_mdiff
  exact (Complex.analyticOnNhd_iff_differentiableOn hU_open).2
    (by simpa [Function.comp_def] using hcomp_diff)

/--
%%handwave
name:
  Local real-part branches differ by an imaginary constant on chart overlaps
statement:
  On a connected coordinate-domain in one local branch whose inverse image
  lies in another branch, the first holomorphic potential and the transported
  second potential differ by an imaginary constant.
proof:
  Transport the second potential through the holomorphic chart transition.
  Both holomorphic functions then have the same real part: they both recover
  the same harmonic function at the same surface point.  Apply [the plane
  overlap lemma](lean:JJMath.Uniformization.analyticOnNhd_eq_add_imaginary_constant_of_re_eq).
-/
theorem potentials_comp_transition_eq_add_imaginary_constant_on_connected_coordinate_subset
    [ComplexOneManifold Z]
    (B C : SurfaceHolomorphicRealPartBranch Z u)
    {U : Set ℂ}
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (hUB : U ⊆ B.coordinateSource)
    (hBC : ∀ z ∈ U, B.chart.symm z ∈ C.source) :
    ∃ c : ℝ,
      ∀ z ∈ U,
        B.potential z =
          C.potential (C.chart (B.chart.symm z)) + c * Complex.I := by
  have htransition :
      AnalyticOnNhd ℂ (fun z ↦ C.chart (B.chart.symm z)) U :=
    B.transition_analyticOnNhd C hU_open hUB hBC
  have hmaps_coordinate :
      Set.MapsTo (fun z ↦ C.chart (B.chart.symm z)) U C.coordinateSource := by
    intro z hz
    exact C.chart_mem_coordinateSource_of_mem_source (hBC z hz)
  have htransported_hol :
      AnalyticOnNhd ℂ (fun z ↦ C.potential (C.chart (B.chart.symm z))) U := by
    simpa [Function.comp_def] using
      C.potential_holomorphic.comp htransition hmaps_coordinate
  exact analyticOnNhd_eq_add_imaginary_constant_of_re_eq
    (B.potential_holomorphic.mono hUB)
    htransported_hol hU_open hU_connected
    (by
      intro z hz
      calc
        (B.potential z).re = u (B.chart.symm z) :=
          B.potential_re_eq z (hUB hz)
        _ = u (C.chart.symm (C.chart (B.chart.symm z))) := by
          rw [C.chart.left_inv (C.mem_chart_source_of_mem_source (hBC z hz))]
        _ = (C.potential (C.chart (B.chart.symm z))).re :=
          (C.potential_re_eq (C.chart (B.chart.symm z))
            (hmaps_coordinate hz)).symm)

end SurfaceHolomorphicRealPartBranch

/--
%%handwave
name:
  Imaginary translations are holomorphic
statement:
  Translation by a purely imaginary constant is a holomorphic transformation of
  the complex plane.
proof:
  The map \(z\mapsto z+c i\) is the sum of the identity map and a constant
  map, hence is holomorphic.
-/
theorem imaginaryTranslation_mdifferentiable (c : ℝ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℂ ↦ z + (c : ℂ) * Complex.I) := by
  simpa using
    (mdifferentiable_id.add
      (mdifferentiable_const (c := (c : ℂ) * Complex.I)))

/--
%%handwave
name:
  Local real-part branches as a holomorphic branch system
statement:
  Local holomorphic real-part branches form a holomorphic branch system whose
  transition group is the group of imaginary translations of the complex
  plane.
proof:
  The local branches are their ambient surface functions.  They are
  holomorphic on their sources, and imaginary translations are holomorphic.
-/
noncomputable def holomorphicRealPartBranchSystem
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] {u : Z → ℝ}
    (hbranches :
      ∀ p : Z, ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source) :
    AnalyticContinuation.HolomorphicLocalBranchSystem
      (Multiplicative ℝ) Z ℂ (SurfaceHolomorphicRealPartBranch Z u) where
  act := fun γ z ↦ z + ((γ.toAdd : ℝ) : ℂ) * Complex.I
  act_holomorphic := by
    intro γ
    exact imaginaryTranslation_mdifferentiable γ.toAdd
  act_one := by
    intro z
    simp
  act_mul := by
    intro γ δ z
    simp [add_mul]
    ring
  domain := fun B ↦ B.source
  domain_open := fun B ↦ B.source_open
  branch := fun B ↦ B.toSurfaceTotalFunction
  branch_holomorphicOn := fun B ↦ B.toSurfaceTotalFunction_mdifferentiableOn
  covers := hbranches

/--
%%handwave
name:
  Local real-part branch systems have local imaginary-translation transitions
statement:
  The branch system associated to local holomorphic real-part branches has
  local transitions by imaginary translations.
proof:
  Near an overlap point, shrink in one coordinate chart to a connected
  coordinate disk contained in the overlap.  On that disk, [the transported
  local potentials differ by an imaginary
  constant](lean:JJMath.Uniformization.SurfaceHolomorphicRealPartBranch.potentials_comp_transition_eq_add_imaginary_constant_on_connected_coordinate_subset),
  which is exactly an imaginary-translation transition.
-/
theorem holomorphicRealPartBranchSystem_hasLocalTransitions
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] {u : Z → ℝ}
    (hbranches :
      ∀ p : Z, ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source) :
    (holomorphicRealPartBranchSystem hbranches).HasLocalTransitions := by
  intro B C x hx
  have hxB : x ∈ B.source := by
    simpa [holomorphicRealPartBranchSystem] using hx.1
  have hxC : x ∈ C.source := by
    simpa [holomorphicRealPartBranchSystem] using hx.2
  let z0 : ℂ := B.chart x
  let Scoord : Set ℂ :=
    B.coordinateSource ∩ (B.chart.target ∩ B.chart.symm ⁻¹' C.source)
  have hScoord_open : IsOpen Scoord := by
    dsimp [Scoord]
    exact B.coordinateSource_open.inter
      (B.chart.isOpen_inter_preimage_symm C.source_open)
  have hz0_coord : z0 ∈ B.coordinateSource := by
    simpa [z0] using B.chart_mem_coordinateSource_of_mem_source hxB
  have hz0_target : z0 ∈ B.chart.target :=
    B.coordinateSource_subset_chart_target hz0_coord
  have hx_chart : x ∈ B.chart.source :=
    B.mem_chart_source_of_mem_source hxB
  have hz0_C : B.chart.symm z0 ∈ C.source := by
    have hsymm : B.chart.symm z0 = x := by
      simpa [z0] using B.chart.left_inv hx_chart
    simpa [hsymm] using hxC
  have hz0_Scoord : z0 ∈ Scoord :=
    ⟨hz0_coord, ⟨hz0_target, hz0_C⟩⟩
  rcases Metric.isOpen_iff.mp hScoord_open z0 hz0_Scoord with
    ⟨R, hR_pos, hball_subset⟩
  let U : Set ℂ := Metric.ball z0 R
  have hU_open : IsOpen U := by
    simp [U]
  have hU_connected : IsConnected U := by
    simpa [U] using Metric.isConnected_ball (x := z0) hR_pos
  have hUB : U ⊆ B.coordinateSource := by
    intro z hz
    exact (hball_subset (by simpa [U] using hz)).1
  have hBC : ∀ z ∈ U, B.chart.symm z ∈ C.source := by
    intro z hz
    exact (hball_subset (by simpa [U] using hz)).2.2
  rcases
    B.potentials_comp_transition_eq_add_imaginary_constant_on_connected_coordinate_subset
      C hU_open hU_connected hUB hBC with
    ⟨c, hc⟩
  let N : Set Z := B.chart.source ∩ B.chart ⁻¹' U
  have hN_open : IsOpen N := by
    dsimp [N]
    exact B.chart.isOpen_inter_preimage hU_open
  have hxN : x ∈ N := by
    refine ⟨hx_chart, ?_⟩
    simpa [U, z0] using Metric.mem_ball_self (x := z0) hR_pos
  have hN_subset : N ⊆ B.source ∩ C.source := by
    intro y hy
    have hy_chart : y ∈ B.chart.source := hy.1
    have hyU : B.chart y ∈ U := hy.2
    have hyB : y ∈ B.source := by
      rw [B.source_eq]
      exact ⟨hy_chart, hUB hyU⟩
    have hyC : y ∈ C.source := by
      have hsymm : B.chart.symm (B.chart y) = y :=
        B.chart.left_inv hy_chart
      have hCpre : B.chart.symm (B.chart y) ∈ C.source :=
        hBC (B.chart y) hyU
      simpa [hsymm] using hCpre
    exact ⟨hyB, hyC⟩
  refine
    ⟨
      { neighborhood := N
        neighborhood_open := hN_open
        mem_neighborhood := hxN
        subset_overlap := ?_
        transition := Multiplicative.ofAdd (-c)
        transition_eq := ?_ }⟩
  · intro y hy
    simpa [holomorphicRealPartBranchSystem] using hN_subset hy
  · intro y hy
    have hy_chart : y ∈ B.chart.source := hy.1
    have hyU : B.chart y ∈ U := hy.2
    have hsymm : B.chart.symm (B.chart y) = y :=
      B.chart.left_inv hy_chart
    have hB_eq :
        B.toSurfaceTotalFunction y =
          C.toSurfaceTotalFunction y + (c : ℂ) * Complex.I := by
      have hlocal := hc (B.chart y) hyU
      simpa [SurfaceHolomorphicRealPartBranch.toSurfaceTotalFunction, hsymm]
        using hlocal
    have htarget :
        C.toSurfaceTotalFunction y =
          B.toSurfaceTotalFunction y +
            (((Multiplicative.ofAdd (-c) : Multiplicative ℝ).toAdd : ℝ) : ℂ) *
              Complex.I := by
      rw [hB_eq]
      simp
    simpa [holomorphicRealPartBranchSystem] using htarget

/--
%%handwave
name:
  Local real-part branches have single-valued continuation on simply connected surfaces
statement:
  On a simply connected Riemann surface, the local holomorphic
  real-part branch system has a single-valued continuation.
proof:
  Apply the general simply connected branch-continuation principle to the
  imaginary-translation branch system.  The transition input is supplied by
  the local overlap theorem for real-part branches.
-/
theorem holomorphicRealPartBranchSystem_has_singleValuedContinuation
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [RiemannSurface Z] [SimplyConnectedSpace Z] {u : Z → ℝ}
    (hbranches :
      ∀ p : Z, ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source) :
    Nonempty
      (holomorphicRealPartBranchSystem hbranches).SingleValuedContinuation := by
  exact
    (holomorphicRealPartBranchSystem hbranches)
      |>.exists_singleValuedContinuation_of_simplyConnected_localTransitions
        (holomorphicRealPartBranchSystem_hasLocalTransitions hbranches)

/--
%%handwave
name:
  Harmonic functions have local holomorphic real-part branches
statement:
  Every point of a surface has a neighborhood on which a harmonic real-valued
  function is the real part of a holomorphic branch.
proof:
  Choose the complex chart at the point.  Since its target is open, choose a
  Euclidean ball in the chart target around the coordinate of the point.  The
  local branch is supplied by [the chart-ball harmonic-conjugate
  theorem](lean:JJMath.Uniformization.harmonicOnSurface_exists_analyticOnNhd_chart_ball_re_eq).
-/
theorem harmonicOnSurface_exists_local_holomorphicRealPartBranch
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    {u : Z → ℝ}
    (hu : IsHarmonicOnSurface (Set.univ : Set Z) u)
    (p : Z) :
    ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source := by
  let e : OpenPartialHomeomorph Z ℂ := chartAt ℂ p
  have he : e ∈ atlas ℂ Z := chart_mem_atlas ℂ p
  have hp_target : e p ∈ e.target := by
    simp [e]
  rcases Metric.isOpen_iff.mp e.open_target (e p) hp_target with
    ⟨R, hR_pos, hball_subset⟩
  rcases harmonicOnSurface_exists_analyticOnNhd_chart_ball_re_eq
      hu e he hball_subset with
    ⟨F, hF_hol, hF_re⟩
  let coordinateSource : Set ℂ := Metric.ball (e p) R
  let source : Set Z := e.source ∩ e ⁻¹' coordinateSource
  have hsource_open : IsOpen source :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  refine ⟨
    SurfaceHolomorphicRealPartBranch.mk source hsource_open e he
      coordinateSource Metric.isOpen_ball hball_subset rfl F
      (by simpa [coordinateSource] using hF_hol)
      (by
        intro z hz
        exact hF_re z (by simpa [coordinateSource] using hz)),
    ?_⟩
  have hp_ball : e p ∈ coordinateSource := by
    change e p ∈ Metric.ball (e p) R
    exact Metric.mem_ball_self hR_pos
  exact ⟨by simp [e], hp_ball⟩

/--
%%handwave
name:
  Local holomorphic real-part branches continue on simply connected surfaces
statement:
  If local holomorphic real-part branches cover a simply connected connected
  Riemann surface, then they continue to a single global holomorphic function
  with the same real part.
proof:
  On an overlap, [the first potential and the transported second potential
  differ by an imaginary
  constant](lean:JJMath.Uniformization.SurfaceHolomorphicRealPartBranch.potentials_comp_transition_eq_add_imaginary_constant_on_connected_coordinate_subset).
  These constants [add on triple
  overlaps](lean:JJMath.Uniformization.imaginaryConstant_overlap_cocycle), so
  continuing branches along paths gives additive \(i\mathbb R\)-valued
  transition constants.  The branches are organized as [a holomorphic local
  branch
  system](lean:JJMath.Uniformization.holomorphicRealPartBranchSystem), whose
  [local transitions](lean:JJMath.Uniformization.holomorphicRealPartBranchSystem_hasLocalTransitions)
  feed into [the simply connected branch-continuation
  principle](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_singleValuedContinuation_of_simplyConnected_localTransitions).
  The resulting single-valued continuation is holomorphic because [local
  agreement with transformed holomorphic branches implies
  holomorphicity](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.SingleValuedContinuation.mdifferentiable),
  and imaginary translations preserve real parts.
-/
theorem holomorphicRealPartBranches_continue_on_simplyConnected_surface
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [RiemannSurface Z] [SimplyConnectedSpace Z]
    {u : Z → ℝ}
    (hbranches :
      ∀ p : Z, ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source) :
    ∃ F : Z → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
        ∀ z, (F z).re = u z := by
  let S := holomorphicRealPartBranchSystem hbranches
  rcases holomorphicRealPartBranchSystem_has_singleValuedContinuation
      hbranches with
    ⟨C⟩
  refine ⟨C.global, C.mdifferentiable, ?_⟩
  intro z
  rcases C.local_agreement z with
    ⟨U, _hU_open, hzU, B, γ, hU_domain, hglobal_eq⟩
  have hzB : z ∈ B.source := hU_domain hzU
  have hF :
      C.global z = S.act γ (S.branch B z) :=
    hglobal_eq z hzU
  calc
    (C.global z).re = (S.act γ (S.branch B z)).re := by rw [hF]
    _ = (B.toSurfaceTotalFunction z).re := by
      simp [S, holomorphicRealPartBranchSystem, Complex.add_re]
    _ = u z := B.toSurfaceTotalFunction_re_eq hzB

/--
%%handwave
name:
  Harmonic functions on simply connected surfaces have holomorphic real parts
statement:
  On a simply connected Riemann surface, every harmonic real-valued
  function is the real part of a holomorphic function.
proof:
  In each coordinate disk, Mathlib's plane harmonic-conjugate theorem gives a
  holomorphic function whose real part is the coordinate expression of the
  harmonic function.  On chart overlaps, [the corresponding local potentials
  differ by imaginary
  constants](lean:JJMath.Uniformization.SurfaceHolomorphicRealPartBranch.potentials_comp_transition_eq_add_imaginary_constant_on_connected_coordinate_subset).
  These constants form the periods of the harmonic conjugate.  Simply
  connectedness kills the periods, so the local holomorphic functions glue to a
  global holomorphic function with the prescribed real part.
-/
theorem simplyConnected_harmonicOnSurface_has_holomorphic_real_part
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [RiemannSurface Z] [SimplyConnectedSpace Z]
    {u : Z → ℝ}
    (hu : IsHarmonicOnSurface (Set.univ : Set Z) u) :
    ∃ F : Z → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
        ∀ z, (F z).re = u z := by
  exact holomorphicRealPartBranches_continue_on_simplyConnected_surface
    (fun p ↦ harmonicOnSurface_exists_local_holomorphicRealPartBranch hu p)

/--
%%handwave
name:
  Harmonic functions have holomorphic primitives on the path-homotopy cover
statement:
  A harmonic function on a Riemann surface has a holomorphic primitive
  on the path-homotopy universal cover whose real part is the pulled-back
  harmonic function.
proof:
  In local coordinates the \(\partial\)-differential of a harmonic function is a
  holomorphic one-form.  Pull this one-form back to the path-homotopy universal
  cover.  Since the cover is simply connected, the pulled-back holomorphic
  one-form is exact; integrating it gives a holomorphic primitive.  The real
  part of the primitive differs from the pulled-back harmonic function by a
  constant, and the constant is normalized away at the base lift.
-/
theorem harmonicOn_univ_has_holomorphic_primitive_on_pathHomotopyUniversalCover
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) {h : Y → ℝ}
    (hh : IsHarmonicOnSurface (Set.univ : Set Y) h) :
    ∃ F : PathHomotopyUniversalCover Y y0 → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
        ∀ z, (F z).re = pathHomotopyUniversalCoverPullback y0 h z := by
  haveI : RiemannSurface (PathHomotopyUniversalCover Y y0) :=
    pathHomotopyUniversalCover_riemannSurface (Y := Y) y0
  haveI : SimplyConnectedSpace (PathHomotopyUniversalCover Y y0) :=
    pathHomotopyUniversalCover_simplyConnected (Y := Y) y0
  exact simplyConnected_harmonicOnSurface_has_holomorphic_real_part
    (Z := PathHomotopyUniversalCover Y y0)
    (pathHomotopyUniversalCoverPullback_harmonicOnSurface y0 hh)

/--
%%handwave
name:
  A primitive with nonconstant pulled-back real part is nonconstant
statement:
  If the real part of a function on the path-homotopy cover is the pullback of
  a nonconstant function on the base, then the function on the cover is
  nonconstant.
proof:
  Choose two base points where the real-valued function differs and lift them
  to the cover.  Equality of the complex values at the two lifts would force
  equality of their real parts, contradicting the choice of the points.
-/
theorem nontrivial_range_of_real_part_eq_pathHomotopyUniversalCoverPullback
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) {h : Y → ℝ}
    (hh_nonconstant : (Set.range h).Nontrivial)
    {F : PathHomotopyUniversalCover Y y0 → ℂ}
    (hF_re : ∀ z, (F z).re = pathHomotopyUniversalCoverPullback y0 h z) :
    (Set.range F).Nontrivial := by
  rcases hh_nonconstant with ⟨a, ha, b, hb, hab⟩
  rcases ha with ⟨p, rfl⟩
  rcases hb with ⟨q, rfl⟩
  rcases PathHomotopyUniversalCover.endpoint_surjective_of_riemannSurface Y y0 p with
    ⟨p', hp'⟩
  rcases PathHomotopyUniversalCover.endpoint_surjective_of_riemannSurface Y y0 q with
    ⟨q', hq'⟩
  refine Set.nontrivial_of_mem_mem_ne
    (show F p' ∈ Set.range F from ⟨p', rfl⟩)
    (show F q' ∈ Set.range F from ⟨q', rfl⟩)
    ?_
  intro hF_eq
  apply hab
  have hp_re : (F p').re = h p := by
    rw [hF_re p', pathHomotopyUniversalCoverPullback, hp']
  have hq_re : (F q').re = h q := by
    rw [hF_re q', pathHomotopyUniversalCoverPullback, hq']
  rw [← hp_re, ← hq_re, hF_eq]

/--
%%handwave
name:
  A nonconstant harmonic function gives a nonconstant holomorphic function on the cover
statement:
  If a Riemann surface carries a nonconstant harmonic function, then
  its path-homotopy universal cover carries a nonconstant holomorphic function
  to the complex plane.
proof:
  Apply
  [the primitive theorem on the path-homotopy
  cover](lean:JJMath.Uniformization.harmonicOn_univ_has_holomorphic_primitive_on_pathHomotopyUniversalCover).
  The real part of the primitive is the pullback of the given harmonic
  function.  Since the endpoint map is surjective,
  [nonconstancy of the real part forces nonconstancy of the primitive](lean:JJMath.Uniformization.nontrivial_range_of_real_part_eq_pathHomotopyUniversalCoverPullback).
-/
theorem nonconstant_harmonicOn_univ_yields_nonconstant_holomorphicMap_on_pathHomotopyUniversalCover
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [RiemannSurface Y] (y0 : Y) {h : Y → ℝ}
    (hh : IsHarmonicOnSurface (Set.univ : Set Y) h)
    (hh_nonconstant : (Set.range h).Nontrivial) :
    ∃ F : PathHomotopyUniversalCover Y y0 → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ (Set.range F).Nontrivial := by
  rcases harmonicOn_univ_has_holomorphic_primitive_on_pathHomotopyUniversalCover
      y0 hh with
    ⟨F, hF_hol, hF_re⟩
  exact ⟨F, hF_hol,
    nontrivial_range_of_real_part_eq_pathHomotopyUniversalCoverPullback
      y0 hh_nonconstant hF_re⟩

/--
%%handwave
name:
  Perron's method gives a nonconstant holomorphic function on the cover of the twice-cut complement
statement:
  The universal cover of the complement in a twice-cut Radó domain carries a
  nonconstant holomorphic function to the complex plane.
proof:
  First,
  [Perron's method gives a nonconstant harmonic
  separator](lean:JJMath.Uniformization.radoTwoDiskCut_has_harmonic_separator)
  on the twice-cut complement.  Then
  [the harmonic function has a holomorphic primitive on the path-homotopy
  cover](lean:JJMath.Uniformization.harmonicOn_univ_has_holomorphic_primitive_on_pathHomotopyUniversalCover)
  whose real part is the pulled-back harmonic function.  Since
  [a primitive with nonconstant pulled-back real part is
  nonconstant](lean:JJMath.Uniformization.nontrivial_range_of_real_part_eq_pathHomotopyUniversalCoverPullback),
  this primitive is the desired holomorphic map.
-/
theorem radoTwoDiskCut_universalCover_has_nonconstant_holomorphicMap_to_complex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (C : RadoTwoDiskCut X) (y0 : C.complement) :
    ∃ f : PathHomotopyUniversalCover C.complement y0 → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ (Set.range f).Nontrivial := by
  rcases radoTwoDiskCut_has_harmonic_separator C with ⟨h, hh, hnonconstant⟩
  exact
    nonconstant_harmonicOn_univ_yields_nonconstant_holomorphicMap_on_pathHomotopyUniversalCover
      (Y := C.complement) y0 hh hnonconstant

/--
%%handwave
name:
  Noncompact Riemann surfaces are second countable by Perron and the universal cover
statement:
  Every noncompact Riemann surface is second countable.
proof:
  First choose
  [a twice-cut Radó domain](lean:JJMath.Uniformization.exists_radoTwoDiskCut).
  Perron's method gives
  [a nonconstant holomorphic function on the universal cover of the
  complement](lean:JJMath.Uniformization.radoTwoDiskCut_universalCover_has_nonconstant_holomorphicMap_to_complex).
  The Poincare-Volterra mechanism makes that universal cover second countable.
  Then [second countability descends along the endpoint
  projection](lean:JJMath.Uniformization.secondCountable_of_secondCountable_pathHomotopyUniversalCover),
  and [a finite open cover by the complement and two coordinate disks makes the
  original surface second
  countable](lean:JJMath.Uniformization.secondCountable_of_radoTwoDiskCut_complement).

  This is the noncircular use of Perron's method in Radó's theorem: no countable
  exhaustion of the original surface is assumed.
-/
theorem noncompact_riemannSurface_secondCountable_via_perron_universal_cover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [NoncompactSpace X] :
    SecondCountableTopology X := by
  classical
  rcases exists_radoTwoDiskCut (X := X) with ⟨C⟩
  let y0 : C.complement := Classical.choice (PathConnectedSpace.nonempty : Nonempty C.complement)
  haveI : RiemannSurface (PathHomotopyUniversalCover C.complement y0) :=
    pathHomotopyUniversalCover_riemannSurface (Y := C.complement) y0
  rcases radoTwoDiskCut_universalCover_has_nonconstant_holomorphicMap_to_complex C y0 with
    ⟨f, hf, hnonconstant⟩
  haveI : SecondCountableTopology (PathHomotopyUniversalCover C.complement y0) :=
    secondCountable_of_nonconstant_holomorphicMap_to_complex
      (X := PathHomotopyUniversalCover C.complement y0) (f := f) hf hnonconstant
  haveI : SecondCountableTopology C.complement :=
    secondCountable_of_secondCountable_pathHomotopyUniversalCover
      (Y := C.complement) y0
  exact secondCountable_of_radoTwoDiskCut_complement C

/--
%%handwave
name:
  Compact Riemann surfaces are second countable
statement:
  Every compact Riemann surface is second countable.
proof:
  Cover the compact surface by coordinate disks.  Compactness gives a finite
  subcover, and each coordinate disk is second countable.  A finite open cover
  by second-countable subspaces gives a countable basis for the whole surface.
-/
theorem compact_riemannSurface_secondCountable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [CompactSpace X] :
    SecondCountableTopology X := by
  classical
  choose coord hcoord using
    fun x : X ↦ exists_coordinateDisk_mem X x
  let V : X → Set X := fun x ↦ (coord x).carrier
  have hcover_univ : (Set.univ : Set X) ⊆ ⋃ x, V x := by
    intro x _hx
    exact Set.mem_iUnion.mpr ⟨x, hcoord x⟩
  rcases isCompact_univ.elim_finite_subcover V
      (fun x ↦ (coord x).isOpen) hcover_univ with
    ⟨t, htcover⟩
  let W : t → Set X := fun x ↦ V x
  have hcover : (⋃ x : t, W x) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr ?_
    intro x
    have hx : x ∈ ⋃ y ∈ t, V y := htcover (Set.mem_univ x)
    rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hxy⟩
  exact secondCountableTopology_of_countable_open_cover_explicit
    W
    (fun x : t ↦ (coord x).isOpen)
    hcover
    (fun x : t ↦ (coord x).secondCountable)

/--
%%handwave
name:
  Radó's theorem by the direct compact-or-Perron split
statement:
  Every Riemann surface is second countable.
proof:
  If the surface is compact, finitely many coordinate disks give a
  second-countable open cover.  If it is noncompact, remove two disjoint closed
  coordinate disks, solve the twice-cut Perron problem, integrate the harmonic
  differential on the universal cover, and use the resulting nonconstant
  holomorphic map to pull back a countable basis from the complex plane.
-/
theorem rado_secondCountableTopology_riemannSurface_direct
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    SecondCountableTopology X := by
  classical
  by_cases hcompact : CompactSpace X
  · haveI : CompactSpace X := hcompact
    exact compact_riemannSurface_secondCountable (X := X)
  · haveI : NoncompactSpace X := not_compactSpace_iff.mp hcompact
    exact noncompact_riemannSurface_secondCountable_via_perron_universal_cover
      (X := X)

/--
%%handwave
name:
  Radó chain lemma
statement:
  The union of a nested chain of second-countable open domains in a Riemann
  surface is second countable.
proof:
  This is the analytic heart of Radó's theorem.  In a bare topological
  manifold the corresponding assertion fails: a long line is a nested union of
  second-countable open intervals.  On a Riemann surface,
  [the chain union is again a Riemann surface](lean:JJMath.Uniformization.rado_chain_union_riemannSurface).
  If it is compact,
  [finitely many coordinate disks give second countability](lean:JJMath.Uniformization.rado_chain_union_secondCountable_of_compact).
  Otherwise
  [the noncompact Riemann surface is second countable by Perron's method on a twice-cut surface and its universal cover](lean:JJMath.Uniformization.noncompact_riemannSurface_secondCountable_via_perron_universal_cover).
-/
theorem rado_chain_union_secondCountable_of_isChain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {ι : Type}
    (D : ι → SecondCountableOpenDomain X)
    (hchain : IsChain (· ⊆ ·) (Set.range fun i : ι => (D i).carrier)) :
    SecondCountableTopology {x : X // x ∈ ⋃ i : ι, (D i).carrier} := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    let U := radoChainUnionOpen D
    haveI : RiemannSurface U := by
      simpa [U] using rado_chain_union_riemannSurface D hchain
    by_cases hcompact : CompactSpace U
    · haveI : CompactSpace U := hcompact
      simpa [U, radoChainUnionOpen] using
        (rado_chain_union_secondCountable_of_compact D hchain)
    · haveI : NoncompactSpace U := (not_compactSpace_iff.mp hcompact)
      simpa [U, radoChainUnionOpen] using
        (noncompact_riemannSurface_secondCountable_via_perron_universal_cover
          (X := U))
  · haveI : IsEmpty {x : X // x ∈ ⋃ i : ι, (D i).carrier} := by
      refine ⟨?_⟩
      intro x
      rcases Set.mem_iUnion.mp x.2 with ⟨i, _hi⟩
      exact hι ⟨i⟩
    infer_instance

/--
%%handwave
name:
  Linearly nested Radó chain lemma
statement:
  The union of a linearly indexed nested family of second-countable open
  domains in a Riemann surface is second countable.
proof:
  The linearly indexed family determines a chain of carriers, so this is the
  chain-indexed form of Radó's chain lemma applied to the range of the family.
-/
theorem rado_chain_union_secondCountable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {ι : Type} [LinearOrder ι]
    (D : ι → SecondCountableOpenDomain X)
    (hmono : ∀ {i j : ι}, i ≤ j → (D i).carrier ⊆ (D j).carrier) :
    SecondCountableTopology {x : X // x ∈ ⋃ i : ι, (D i).carrier} := by
  refine rado_chain_union_secondCountable_of_isChain D ?_
  intro U hU V hV hne
  rcases hU with ⟨i, rfl⟩
  rcases hV with ⟨j, rfl⟩
  rcases le_total i j with hij | hji
  · exact Or.inl (hmono hij)
  · exact Or.inr (hmono hji)

/--
%%handwave
name:
  Maximal second-countable domain
statement:
  Through a chosen point of a Riemann surface there is a maximal
  second-countable open domain.
proof:
  Order second-countable open domains containing the point by inclusion.
  Coordinate disks give a nonempty starting domain.  Radó's chain lemma gives
  upper bounds for chains, so Zorn's lemma gives a maximal domain.
-/
theorem exists_maximal_secondCountableOpenDomain
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    ∃ D : SecondCountableOpenDomain X,
      p ∈ D.carrier ∧
        ∀ E : SecondCountableOpenDomain X,
          p ∈ E.carrier → D.carrier ⊆ E.carrier → E.carrier = D.carrier := by
  classical
  rcases exists_secondCountableOpenDomain_mem X p with ⟨D₀, hpD₀⟩
  let S : Set (Set X) :=
    {U | ∃ D : SecondCountableOpenDomain X, p ∈ D.carrier ∧ D.carrier = U}
  have hD₀S : D₀.carrier ∈ S := ⟨D₀, hpD₀, rfl⟩
  have hchain_upper :
      ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
        ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hc hne
    let Dof : c → SecondCountableOpenDomain X :=
      fun U ↦ Classical.choose (hcS U.property)
    have hpDof : ∀ U : c, p ∈ (Dof U).carrier := by
      intro U
      exact (Classical.choose_spec (hcS U.property)).1
    have hcarrierDof : ∀ U : c, (Dof U).carrier = (U : Set X) := by
      intro U
      exact (Classical.choose_spec (hcS U.property)).2
    let U : Set X := ⋃ A : c, (Dof A).carrier
    rcases hne with ⟨A₀, hA₀c⟩
    have hpU : p ∈ U := by
      exact Set.mem_iUnion_of_mem ⟨A₀, hA₀c⟩ (hpDof ⟨A₀, hA₀c⟩)
    have hU_open : IsOpen U := by
      exact isOpen_iUnion fun A : c ↦ (Dof A).isOpen
    have hU_preconnected : IsPreconnected U := by
      refine IsPreconnected.iUnion_of_reflTransGen
        (fun A : c ↦ (Dof A).isPreconnected) ?_
      intro A B
      exact Relation.ReflTransGen.single ⟨p, hpDof A, hpDof B⟩
    have hcarrier_chain :
        IsChain (· ⊆ ·) (Set.range fun A : c ↦ (Dof A).carrier) := by
      intro A hA B hB hneAB
      rcases hA with ⟨A', rfl⟩
      rcases hB with ⟨B', rfl⟩
      by_cases hAB : (A' : Set X) = (B' : Set X)
      · exfalso
        exact hneAB (by simp [hcarrierDof A', hcarrierDof B', hAB])
      · rcases hc A'.property B'.property hAB with hsub | hsub
        · exact Or.inl (by simpa [hcarrierDof A', hcarrierDof B'] using hsub)
        · exact Or.inr (by simpa [hcarrierDof A', hcarrierDof B'] using hsub)
    have hU_second : SecondCountableTopology U := by
      simpa [U] using
        (rado_chain_union_secondCountable_of_isChain
          (X := X) (D := Dof) hcarrier_chain)
    let DU : SecondCountableOpenDomain X :=
      { carrier := U
        isOpen := hU_open
        nonempty := ⟨p, hpU⟩
        isPreconnected := hU_preconnected
        secondCountable := hU_second }
    refine ⟨U, ⟨DU, hpU, rfl⟩, ?_⟩
    intro A hAc x hxA
    exact Set.mem_iUnion_of_mem ⟨A, hAc⟩
      (by simpa [hcarrierDof ⟨A, hAc⟩] using hxA)
  rcases zorn_subset_nonempty S hchain_upper D₀.carrier hD₀S with
    ⟨Umax, hD₀Umax, hmaxU⟩
  rcases hmaxU.prop with ⟨D, hpD, hDUmax⟩
  refine ⟨D, hpD, ?_⟩
  intro E hpE hDE
  have hES : E.carrier ∈ S := ⟨E, hpE, rfl⟩
  have hUmaxE : Umax ⊆ E.carrier := by
    simpa [← hDUmax] using hDE
  have hUmax_eq_E : Umax = E.carrier := hmaxU.eq_of_subset hES hUmaxE
  exact hUmax_eq_E.symm.trans hDUmax.symm

/--
%%handwave
name:
  Maximal second-countable domain is closed
statement:
  A maximal second-countable open domain through a point in a connected
  Riemann surface is closed.
proof:
  If a boundary point existed, choose a small connected coordinate disk around
  it that meets the domain.  Adjoining this disk to the maximal domain gives a
  larger open connected set.  Since it is the union of two second-countable
  open subspaces, it is still second countable, contradicting maximality.
-/
theorem maximal_secondCountableOpenDomain_isClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {D : SecondCountableOpenDomain X}
    (hpD : p ∈ D.carrier)
    (hmax : ∀ E : SecondCountableOpenDomain X,
      p ∈ E.carrier → D.carrier ⊆ E.carrier → E.carrier = D.carrier) :
    IsClosed D.carrier := by
  rw [← closure_subset_iff_isClosed]
  intro x hx_closure
  by_contra hxD
  rcases exists_secondCountableOpenDomain_mem X x with ⟨E, hxE⟩
  have hED : (E.carrier ∩ D.carrier).Nonempty :=
    mem_closure_iff.mp hx_closure E.carrier E.isOpen hxE
  have hDE : (D.carrier ∩ E.carrier).Nonempty := by
    simpa [Set.inter_comm] using hED
  let F := D.unionOfInterNonempty E hDE
  have hpF : p ∈ F.carrier := by
    exact Or.inl hpD
  have hDF : D.carrier ⊆ F.carrier := Set.subset_union_left
  have hF_eq_D : F.carrier = D.carrier := hmax F hpF hDF
  have hxF : x ∈ F.carrier := by
    exact Or.inr hxE
  exact hxD (by simpa [hF_eq_D] using hxF)

/--
%%handwave
name:
  Maximal domain is all of the surface
statement:
  A maximal second-countable open domain through a point in a connected
  Riemann surface is the whole surface.
proof:
  The maximal domain is open by definition and
  [the maximal second-countable open domain is
  closed](lean:JJMath.Uniformization.maximal_secondCountableOpenDomain_isClosed).
  A nonempty clopen subset of a connected space is the whole space.
-/
theorem maximal_secondCountableOpenDomain_eq_univ
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {D : SecondCountableOpenDomain X}
    (hpD : p ∈ D.carrier)
    (hmax : ∀ E : SecondCountableOpenDomain X,
      p ∈ E.carrier → D.carrier ⊆ E.carrier → E.carrier = D.carrier) :
    D.carrier = Set.univ := by
  have hclosed := maximal_secondCountableOpenDomain_isClosed hpD hmax
  exact (IsClopen.eq_univ ⟨hclosed, D.isOpen⟩ D.nonempty)

/--
%%handwave
name:
  A full second-countable domain makes the surface second countable
statement:
  If a second-countable open domain has carrier equal to the whole surface,
  then the surface is second countable.
-/
theorem secondCountable_of_full_secondCountableOpenDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SecondCountableOpenDomain X) (hD : D.carrier = Set.univ) :
    SecondCountableTopology X := by
  haveI : SecondCountableTopology D.carrier := D.secondCountable
  let e : D.carrier ≃ₜ X :=
    (Homeomorph.setCongr hD).trans (Homeomorph.Set.univ X)
  exact e.symm.secondCountableTopology

/--
%%handwave
name:
  Radó countable coordinate cover
statement:
  Every Riemann surface has a countable coordinate-disk cover.
proof:
  First apply Radó's theorem in its direct compact-or-Perron form.  A countable
  basis for the resulting topology can then be refined by coordinate disks,
  yielding a countable coordinate-disk cover.
-/
theorem rado_countableCoordinateDiskCover
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    Nonempty (CountableCoordinateDiskCover X) := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface_direct X
  have hcover_all :
      (⋃ D : CoordinateDisk X, D.carrier) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr ?_
    intro x
    rcases exists_coordinateDisk_mem X x with ⟨D, hxD⟩
    exact Set.mem_iUnion.mpr ⟨D, hxD⟩
  rcases TopologicalSpace.isOpen_iUnion_countable
      (fun D : CoordinateDisk X ↦ D.carrier)
      (fun D : CoordinateDisk X ↦ D.isOpen) with
    ⟨T, hT_count, hT_union⟩
  have hT_cover : (⋃ D ∈ T, (D : CoordinateDisk X).carrier) = Set.univ := by
    simpa [hcover_all] using hT_union
  have hT_nonempty : T.Nonempty := by
    let p : X := Classical.choice (PathConnectedSpace.nonempty : Nonempty X)
    have hpT : p ∈ ⋃ D ∈ T, (D : CoordinateDisk X).carrier := by
      simp [hT_cover]
    rcases Set.mem_iUnion.mp hpT with ⟨D, hD⟩
    rcases Set.mem_iUnion.mp hD with ⟨hDT, _hpD⟩
    exact ⟨D, hDT⟩
  rcases hT_count.exists_eq_range hT_nonempty with ⟨disk, hdisk⟩
  refine ⟨{ disk := disk, covers := ?_ }⟩
  have hrange_union :
      (⋃ n : ℕ, (disk n).carrier) =
        ⋃ D ∈ Set.range disk, (D : CoordinateDisk X).carrier := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
      exact Set.mem_iUnion.mpr
        ⟨disk n, Set.mem_iUnion.mpr ⟨Set.mem_range_self n, hxn⟩⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨D, hD⟩
      rcases Set.mem_iUnion.mp hD with ⟨hD_range, hxD⟩
      rcases hD_range with ⟨n, rfl⟩
      exact Set.mem_iUnion.mpr ⟨n, hxD⟩
  calc
    (⋃ n : ℕ, (disk n).carrier)
        = ⋃ D ∈ Set.range disk, (D : CoordinateDisk X).carrier := hrange_union
    _ = ⋃ D ∈ T, (D : CoordinateDisk X).carrier := by rw [← hdisk]
    _ = Set.univ := hT_cover

/--
%%handwave
name:
  Radó's theorem for Riemann surfaces
statement:
  Every Riemann surface is second countable.
proof:
  Use
  [the direct compact-or-Perron
  split](lean:JJMath.Uniformization.rado_secondCountableTopology_riemannSurface_direct).
  In the compact case a finite coordinate cover suffices.  In the noncompact
  case Perron's method on a twice-cut complement produces a nonconstant
  holomorphic function on the universal cover, and the countable basis of
  \(\mathbb C\) pulls back through that function to a countable surface basis.
tags:
  milestone
-/
theorem rado_secondCountableTopology_riemannSurface
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
  [RiemannSurface X] :
    SecondCountableTopology X := by
  exact rado_secondCountableTopology_riemannSurface_direct X

end Uniformization

end JJMath
