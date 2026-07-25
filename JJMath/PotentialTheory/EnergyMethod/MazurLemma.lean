import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Combination

/-!
# Mazur-type convexification for the energy method

This file records the functional-analytic leaves used by the pure Dirichlet
normal-contraction argument.  The intended proof is the standard Hilbert-space
route: extract a weakly convergent subsequence from a bounded sequence, then
apply Mazur's lemma to convex hulls of tails to obtain norm convergence.
-/

namespace JJMath

open Filter
open scoped Topology

namespace Uniformization

/--
%%handwave
name:
  Bounded sequences in separable Hilbert spaces have weakly convergent subsequences
statement:
  Every norm-bounded sequence in a separable complete real Hilbert space has a
  subsequence which converges in the weak topology of the Hilbert space.
proof:
  Send a vector \(x\) to the continuous functional \(y \mapsto \langle x,y\rangle\).
  The sequence of functionals is norm-bounded, so sequential Banach--Alaoglu
  gives a weak-star convergent subsequence.  The Fréchet--Riesz theorem
  identifies the weak-star limit with a Hilbert-space vector, and the weak-star
  convergence is exactly weak convergence of the original vectors.
-/
theorem separable_hilbert_bounded_sequence_has_weakly_convergent_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H)
    (hbounded : ∃ C : ℝ, ∀ n : ℕ, ‖u n‖ ≤ C) :
    ∃ uLim : H, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (u (φ n)))
          atTop (𝓝 (toWeakSpace ℝ H uLim)) := by
  classical
  rcases hbounded with ⟨C, hC⟩
  let x : ℕ → WeakDual ℝ H :=
    fun n ↦ StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
  have hx_mem :
      ∀ n : ℕ,
        x n ∈ WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ H) C := by
    intro n
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ H (u n)‖ ≤ C
    simpa using hC n
  rcases
    (WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := H)
      (0 : StrongDual ℝ H) C) hx_mem with
    ⟨ℓ, _hℓ, φ, hφ_mono, hφ_tendsto⟩
  let uLim : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ)
  refine ⟨uLim, φ, hφ_mono, ?_⟩
  have hweak_inj : Function.Injective ((topDualPairing ℝ H).flip) := by
    intro a b hab
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hne
    exact hf (DFunLike.congr_fun hab f)
  have hdual_inj : Function.Injective (topDualPairing ℝ H) := by
    intro f g hfg
    exact ContinuousLinearMap.ext fun y ↦ DFunLike.congr_fun hfg y
  refine
    (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ H).flip) hweak_inj).2 ?_
  intro f
  have h_eval :
      Tendsto (fun n : ℕ ↦ x (φ n) ((InnerProductSpace.toDual ℝ H).symm f))
        atTop
        (𝓝 (ℓ ((InnerProductSpace.toDual ℝ H).symm f))) := by
    exact
      (WeakBilin.tendsto_iff_forall_eval_tendsto
        (B := topDualPairing ℝ H) hdual_inj).1
        hφ_tendsto ((InnerProductSpace.toDual ℝ H).symm f)
  convert h_eval using 1
  · ext n
    change
      f (u (φ n)) =
        inner ℝ (u (φ n)) ((InnerProductSpace.toDual ℝ H).symm f)
    calc
      f (u (φ n)) =
          inner ℝ ((InnerProductSpace.toDual ℝ H).symm f) (u (φ n)) := by
        exact (InnerProductSpace.toDual_symm_apply (x := u (φ n)) (y := f)).symm
      _ = inner ℝ (u (φ n)) ((InnerProductSpace.toDual ℝ H).symm f) := by
        exact real_inner_comm (u (φ n)) ((InnerProductSpace.toDual ℝ H).symm f)
  · apply congrArg 𝓝
    change
      f uLim =
        ℓ ((InnerProductSpace.toDual ℝ H).symm f)
    calc
      f uLim =
          inner ℝ ((InnerProductSpace.toDual ℝ H).symm f) uLim := by
        exact (InnerProductSpace.toDual_symm_apply (x := uLim) (y := f)).symm
      _ = inner ℝ uLim ((InnerProductSpace.toDual ℝ H).symm f) := by
        exact real_inner_comm uLim ((InnerProductSpace.toDual ℝ H).symm f)
      _ = ℓ ((InnerProductSpace.toDual ℝ H).symm f) := by
        simp [uLim]

/--
%%handwave
name:
  Bounded Hilbert sequences have weakly convergent subsequences
statement:
  Every norm-bounded sequence in a complete real Hilbert space has a
  subsequence which converges in the weak topology of the Hilbert space.
proof:
  The closed linear span of the sequence is separable.  On that separable
  Hilbert subspace, the closed ball containing the sequence is weakly
  sequentially compact by reflexivity and Banach--Alaoglu.  The weak limit in
  the subspace is also the weak limit in the ambient Hilbert space.
-/
theorem hilbert_bounded_sequence_has_weakly_convergent_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (u : ℕ → H)
    (hbounded : ∃ C : ℝ, ∀ n : ℕ, ‖u n‖ ≤ C) :
    ∃ uLim : H, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (u (φ n)))
          atTop (𝓝 (toWeakSpace ℝ H uLim)) := by
  classical
  let K : Submodule ℝ H := (Submodule.span ℝ (Set.range u)).topologicalClosure
  have hsepK_set : TopologicalSpace.IsSeparable (K : Set H) := by
    rw [Submodule.topologicalClosure_coe]
    exact (Set.countable_range u).isSeparable.span.closure
  letI : TopologicalSpace.SeparableSpace K := hsepK_set.separableSpace
  letI : CompleteSpace K := by
    dsimp [K]
    exact isClosed_closure.completeSpace_coe
  let uK : ℕ → K := fun n ↦
    ⟨u n,
      (Submodule.le_topologicalClosure (Submodule.span ℝ (Set.range u)))
        (Submodule.subset_span (Set.mem_range_self n))⟩
  have hboundedK : ∃ C : ℝ, ∀ n : ℕ, ‖uK n‖ ≤ C := by
    rcases hbounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    simpa [uK] using hC n
  have hsubseq :
      ∃ uLim : K, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          Tendsto (fun n : ℕ ↦ toWeakSpace ℝ K (uK (φ n)))
            atTop (𝓝 (toWeakSpace ℝ K uLim)) :=
    @separable_hilbert_bounded_sequence_has_weakly_convergent_subsequence
      K inferInstance inferInstance (by dsimp [K]; exact isClosed_closure.completeSpace_coe)
      hsepK_set.separableSpace uK hboundedK
  rcases hsubseq with
    ⟨uLimK, φ, hφ_mono, hweakK⟩
  refine ⟨(uLimK : H), φ, hφ_mono, ?_⟩
  have hmap :
      Tendsto
        (fun n : ℕ ↦
          WeakSpace.map (K.subtypeL : K →L[ℝ] H)
            (toWeakSpace ℝ K (uK (φ n))))
        atTop
        (𝓝
          (WeakSpace.map (K.subtypeL : K →L[ℝ] H)
            (toWeakSpace ℝ K uLimK))) :=
    ((WeakSpace.map (K.subtypeL : K →L[ℝ] H)).continuous.tendsto
      (toWeakSpace ℝ K uLimK)).comp hweakK
  simpa [WeakSpace.map_apply, uK] using hmap

end Uniformization

end JJMath
