import JJMath.Uniformization.SmoothUnitPhaseCirclePrimitive

/-!
# Smooth limits of locally stable phases

An escaping vortex telescope is most naturally described by finite partial
products.  Near every fixed point, sufficiently late partial products are
defined, smooth, and identical.  This file records the elementary local
gluing principle which turns such a locally stationary sequence into one
global smooth unit phase.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

/-- A sequence of functions which is eventually represented by one smooth
member on a neighborhood of every point has a global smooth locally stable
limit. -/
theorem exists_contMDiffMap_of_locally_eventuallyEq
    (f : ℕ → M → ℂ)
    (hlocal : ∀ x : M, ∃ N : ℕ, ∃ U : TopologicalSpace.Opens M,
      x ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf ℝ ℂ) ∞ (f N) U ∧
      ∀ n ≥ N, Set.EqOn (f n) (f N) U) :
    ∃ P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞,
      ∀ x : M, ∃ N : ℕ, ∀ n ≥ N, P x = f n x := by
  choose N U hxU hsmooth hstable using hlocal
  let Pfun : M → ℂ := fun x ↦ f (N x) x
  have hP_smooth : ContMDiff I (modelWithCornersSelf ℝ ℂ) ∞ Pfun := by
    intro x
    have hrepresent : ∀ᶠ y in 𝓝 x, Pfun y = f (N x) y := by
      filter_upwards [((U x).isOpen.mem_nhds (hxU x))] with y hy
      let k : ℕ := max (N x) (N y)
      have hkx : N x ≤ k := Nat.le_max_left _ _
      have hky : N y ≤ k := Nat.le_max_right _ _
      have hxEq : f k y = f (N x) y := hstable x k hkx hy
      have hyEq : f k y = f (N y) y := hstable y k hky (hxU y)
      exact hyEq.symm.trans hxEq
    have hfAt : ContMDiffAt I (modelWithCornersSelf ℝ ℂ) ∞ (f (N x)) x :=
      (hsmooth x).contMDiffAt ((U x).isOpen.mem_nhds (hxU x))
    exact hfAt.congr_of_eventuallyEq hrepresent
  let P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞ :=
    ⟨Pfun, hP_smooth⟩
  refine ⟨P, ?_⟩
  intro x
  refine ⟨N x, ?_⟩
  intro n hn
  exact (hstable x n hn (hxU x)).symm

/-- If the stationary tails have unit norm pointwise, their global smooth
limit is a unit phase. -/
theorem exists_smoothUnitPhase_of_locally_eventuallyEq
    (f : ℕ → M → ℂ)
    (hlocal : ∀ x : M, ∃ N : ℕ, ∃ U : TopologicalSpace.Opens M,
      x ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf ℝ ℂ) ∞ (f N) U ∧
      ∀ n ≥ N, Set.EqOn (f n) (f N) U)
    (hnorm : ∀ x : M, ∃ N : ℕ, ∀ n ≥ N, ‖f n x‖ = 1) :
    ∃ P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞,
      (∀ x : M, ‖P x‖ = 1) ∧
      ∀ x : M, ∃ N : ℕ, ∀ n ≥ N, P x = f n x := by
  rcases exists_contMDiffMap_of_locally_eventuallyEq I f hlocal with
    ⟨P, hP⟩
  refine ⟨P, ?_, hP⟩
  intro x
  rcases hP x with ⟨NP, hNP⟩
  rcases hnorm x with ⟨Nnorm, hNnorm⟩
  let N := max NP Nnorm
  rw [hNP N (Nat.le_max_left _ _)]
  exact hNnorm N (Nat.le_max_right _ _)

/-- A locally stationary sequence of unit phases therefore supplies the
circle primitive of a global smooth logarithmic one-form. -/
theorem exists_circlePrimitive_of_locally_eventuallyEq_unitPhase
    (f : ℕ → M → ℂ)
    (hlocal : ∀ x : M, ∃ N : ℕ, ∃ U : TopologicalSpace.Opens M,
      x ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf ℝ ℂ) ∞ (f N) U ∧
      ∀ n ≥ N, Set.EqOn (f n) (f N) U)
    (hnorm : ∀ x : M, ∃ N : ℕ, ∀ n ≥ N, ‖f n x‖ = 1) :
    ∃ (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
        (hP : ∀ x : M, ‖P x‖ = 1),
      Nonempty (JJMath.Manifold.SmoothCirclePrimitive I
        (smoothUnitPhaseOneForm I P hP)) := by
  rcases exists_smoothUnitPhase_of_locally_eventuallyEq I f hlocal hnorm with
    ⟨P, hP, _hstable⟩
  exact ⟨P, hP, ⟨smoothUnitPhaseCirclePrimitive I P hP⟩⟩

/-- The circle primitive construction may retain the pointwise eventual
agreement between the global phase and the stationary sequence. -/
theorem exists_circlePrimitive_of_locally_eventuallyEq_unitPhase_with_stability
    (f : ℕ → M → ℂ)
    (hlocal : ∀ x : M, ∃ N : ℕ, ∃ U : TopologicalSpace.Opens M,
      x ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf ℝ ℂ) ∞ (f N) U ∧
      ∀ n ≥ N, Set.EqOn (f n) (f N) U)
    (hnorm : ∀ x : M, ∃ N : ℕ, ∀ n ≥ N, ‖f n x‖ = 1) :
    ∃ (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
        (hP : ∀ x : M, ‖P x‖ = 1),
      (∀ x : M, ∃ N : ℕ, ∀ n ≥ N, P x = f n x) ∧
        Nonempty (JJMath.Manifold.SmoothCirclePrimitive I
          (smoothUnitPhaseOneForm I P hP)) := by
  rcases exists_smoothUnitPhase_of_locally_eventuallyEq I f hlocal hnorm with
    ⟨P, hP, hstable⟩
  exact ⟨P, hP, hstable, ⟨smoothUnitPhaseCirclePrimitive I P hP⟩⟩

end

end JJMath.Uniformization
