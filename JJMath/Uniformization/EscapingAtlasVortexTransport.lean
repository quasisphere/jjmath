import JJMath.Uniformization.AtlasVortexChainSubdivision

/-!
# Escaping blockwise atlas vortex transports

Finite controlled vortex paths may be appended a block at a time.  If the
open sets controlling those blocks eventually miss a neighborhood of every
point, the corresponding unit phases are locally eventually constant and
therefore define one global smooth circle-valued phase.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/-- Coherent finite transports obtained by appending one controlled finite
path at each stage. -/
noncomputable def controlledAtlasVortexPathTransport
    (p : X) (W : ℕ → TopologicalSpace.Opens X) (v : ℕ → X)
    (path : ∀ n, ControlledAtlasVortexPath (W n) (v n) (v (n + 1)))
    (T₀ : AtlasVortexTransportData X p (v 0))
    (hpW : ∀ n, p ∉ W n) :
    ∀ n, AtlasVortexTransportData X p (v n)
  | 0 => T₀
  | n + 1 => Classical.choose
      ((path n).exists_append_transport
        (controlledAtlasVortexPathTransport p W v path T₀ hpW n) (hpW n))

/-- Appending the next controlled block does not change the transport phase
outside that block's control set. -/
theorem controlledAtlasVortexPathTransport_phase_succ
    (p : X) (W : ℕ → TopologicalSpace.Opens X) (v : ℕ → X)
    (path : ∀ n, ControlledAtlasVortexPath (W n) (v n) (v (n + 1)))
    (T₀ : AtlasVortexTransportData X p (v 0))
    (hpW : ∀ n, p ∉ W n) (n : ℕ)
    (z : coordinateVortexPairOpen p (v (n + 1)))
    (hzW : (z : X) ∉ W n) :
    (controlledAtlasVortexPathTransport p W v path T₀ hpW (n + 1)).phase z =
      (controlledAtlasVortexPathTransport p W v path T₀ hpW n).phase
        ⟨(z : X), ⟨z.2.1,
          fun hz ↦ hzW (hz ▸ (path n).start_mem)⟩⟩ := by
  exact Classical.choose_spec
    ((path n).exists_append_transport
      (controlledAtlasVortexPathTransport p W v path T₀ hpW n) (hpW n)) z hzW

/-- A blockwise finite transport phase, totalized on the initially punctured
surface by assigning an irrelevant value at its moving terminal point. -/
noncomputable def controlledAtlasVortexPathTransportPartialPhase
    (p : X) (W : ℕ → TopologicalSpace.Opens X) (v : ℕ → X)
    (path : ∀ n, ControlledAtlasVortexPath (W n) (v n) (v (n + 1)))
    (T₀ : AtlasVortexTransportData X p (v 0))
    (hpW : ∀ n, p ∉ W n)
    (n : ℕ) (z : atlasVortexInitialOpen p) : ℂ := by
  classical
  exact if hzt : (z : X) ≠ v n then
    (controlledAtlasVortexPathTransport p W v path T₀ hpW n).phase
      ⟨(z : X), ⟨z.2, hzt⟩⟩
  else 1

theorem norm_controlledAtlasVortexPathTransportPartialPhase
    (p : X) (W : ℕ → TopologicalSpace.Opens X) (v : ℕ → X)
    (path : ∀ n, ControlledAtlasVortexPath (W n) (v n) (v (n + 1)))
    (T₀ : AtlasVortexTransportData X p (v 0))
    (hpW : ∀ n, p ∉ W n)
    (n : ℕ) (z : atlasVortexInitialOpen p) :
    ‖controlledAtlasVortexPathTransportPartialPhase
      p W v path T₀ hpW n z‖ = 1 := by
  by_cases hzt : (z : X) ≠ v n
  · rw [show controlledAtlasVortexPathTransportPartialPhase
        p W v path T₀ hpW n z =
        (controlledAtlasVortexPathTransport p W v path T₀ hpW n).phase
          ⟨(z : X), ⟨z.2, hzt⟩⟩ by
      simp [controlledAtlasVortexPathTransportPartialPhase, hzt]]
    exact (controlledAtlasVortexPathTransport p W v path T₀ hpW n).norm_phase _
  · simp [controlledAtlasVortexPathTransportPartialPhase, hzt]

/-- Away from the moving terminal point, a blockwise partial phase is
smooth. -/
theorem contMDiffAt_controlledAtlasVortexPathTransportPartialPhase_of_ne
    (p : X) (W : ℕ → TopologicalSpace.Opens X) (v : ℕ → X)
    (path : ∀ n, ControlledAtlasVortexPath (W n) (v n) (v (n + 1)))
    (T₀ : AtlasVortexTransportData X p (v 0))
    (hpW : ∀ n, p ∉ W n)
    (n : ℕ) (z : atlasVortexInitialOpen p) (hzt : (z : X) ≠ v n) :
    ContMDiffAt SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      (controlledAtlasVortexPathTransportPartialPhase p W v path T₀ hpW n) z := by
  let B : TopologicalSpace.Opens (atlasVortexInitialOpen p) :=
    ⟨{y | (y : X) ≠ v n}, isOpen_ne.preimage
      (continuous_subtype_val : Continuous
        (fun y : atlasVortexInitialOpen p ↦ (y : X)))⟩
  let zB : B := ⟨z, hzt⟩
  have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun y : B ↦ (y : X)) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  have hlift : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun y : B ↦
        (⟨(y : X), ⟨y.1.2, y.2⟩⟩ :
          coordinateVortexPairOpen p (v n))) :=
    contMDiffCodRestrictOpen_transport hval
      (coordinateVortexPairOpen p (v n)) (fun y ↦ ⟨y.1.2, y.2⟩)
  have hsmooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun y : B ↦
        (controlledAtlasVortexPathTransport p W v path T₀ hpW n).phase
          (⟨(y : X), ⟨y.1.2, y.2⟩⟩ :
            coordinateVortexPairOpen p (v n))) :=
    (controlledAtlasVortexPathTransport p W v path T₀ hpW n).phase.contMDiff.comp
      hlift
  rw [← contMDiffAt_subtype_iff (U := B) (x := zB)]
  have heq :
      (fun y : B ↦ controlledAtlasVortexPathTransportPartialPhase
        p W v path T₀ hpW n (y : atlasVortexInitialOpen p)) =
      fun y : B ↦
        (controlledAtlasVortexPathTransport p W v path T₀ hpW n).phase
          (⟨(y : X), ⟨y.1.2, y.2⟩⟩ :
            coordinateVortexPairOpen p (v n)) := by
    funext y
    have hy : (y : X) ≠ v n := y.2
    simp [controlledAtlasVortexPathTransportPartialPhase, hy]
  rw [heq]
  exact hsmooth.contMDiffAt

/-- Consecutive blockwise partial phases agree at every point outside the
next block's control set. -/
theorem controlledAtlasVortexPathTransportPartialPhase_succ_eq
    (p : X) (W : ℕ → TopologicalSpace.Opens X) (v : ℕ → X)
    (path : ∀ n, ControlledAtlasVortexPath (W n) (v n) (v (n + 1)))
    (T₀ : AtlasVortexTransportData X p (v 0))
    (hpW : ∀ n, p ∉ W n)
    (n : ℕ) (z : atlasVortexInitialOpen p) (hzW : (z : X) ∉ W n) :
    controlledAtlasVortexPathTransportPartialPhase
        p W v path T₀ hpW (n + 1) z =
      controlledAtlasVortexPathTransportPartialPhase
        p W v path T₀ hpW n z := by
  have hzLeft : (z : X) ≠ v n := by
    intro hz
    exact hzW (hz ▸ (path n).start_mem)
  have hzRight : (z : X) ≠ v (n + 1) := by
    intro hz
    exact hzW (hz ▸ (path n).end_mem)
  rw [show controlledAtlasVortexPathTransportPartialPhase
        p W v path T₀ hpW (n + 1) z =
      (controlledAtlasVortexPathTransport p W v path T₀ hpW (n + 1)).phase
        ⟨(z : X), ⟨z.2, hzRight⟩⟩ by
      simp [controlledAtlasVortexPathTransportPartialPhase, hzRight],
    controlledAtlasVortexPathTransport_phase_succ
      p W v path T₀ hpW n ⟨(z : X), ⟨z.2, hzRight⟩⟩ hzW]
  simp [controlledAtlasVortexPathTransportPartialPhase, hzLeft]

/-- Escaping controlled finite paths give a global smooth unit phase and a
circle primitive on the surface punctured at the fixed initial point. -/
theorem exists_circlePrimitive_of_locallyEscaping_controlledAtlasVortexPaths_with_stability
    (p : X) (W : ℕ → TopologicalSpace.Opens X) (v : ℕ → X)
    (path : ∀ n, ControlledAtlasVortexPath (W n) (v n) (v (n + 1)))
    (T₀ : AtlasVortexTransportData X p (v 0))
    (hpW : ∀ n, p ∉ W n)
    (hescape : ∀ z : atlasVortexInitialOpen p,
      ∃ N : ℕ, ∃ U : TopologicalSpace.Opens (atlasVortexInitialOpen p),
        z ∈ U ∧ ∀ n ≥ N, ∀ y ∈ U, (y : X) ∉ W n) :
    ∃ (P : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
          (atlasVortexInitialOpen p) ℂ ∞)
        (hP : ∀ z : atlasVortexInitialOpen p, ‖P z‖ = 1),
      (∀ z : atlasVortexInitialOpen p, ∃ N : ℕ, ∀ n ≥ N,
          P z = controlledAtlasVortexPathTransportPartialPhase
            p W v path T₀ hpW n z) ∧
        Nonempty (JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
          (smoothUnitPhaseOneForm SurfaceRealModel P hP)) := by
  let f : ℕ → atlasVortexInitialOpen p → ℂ :=
    controlledAtlasVortexPathTransportPartialPhase p W v path T₀ hpW
  have hlocal : ∀ z : atlasVortexInitialOpen p,
      ∃ N : ℕ, ∃ U : TopologicalSpace.Opens (atlasVortexInitialOpen p),
        z ∈ U ∧
        ContMDiffOn SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞ (f N) U ∧
        ∀ n ≥ N, Set.EqOn (f n) (f N) U := by
    intro z
    rcases hescape z with ⟨N, U, hzU, havoid⟩
    refine ⟨N, U, hzU, ?_, ?_⟩
    · intro y hy
      have hyTerminal : (y : X) ≠ v N := by
        intro hyv
        exact (havoid N le_rfl y hy) (hyv ▸ (path N).start_mem)
      exact (contMDiffAt_controlledAtlasVortexPathTransportPartialPhase_of_ne
        p W v path T₀ hpW N y hyTerminal).contMDiffWithinAt
    · intro n hn y hy
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih =>
          exact (controlledAtlasVortexPathTransportPartialPhase_succ_eq
            p W v path T₀ hpW n y (havoid n hn y hy)).trans ih
  have hnorm : ∀ z : atlasVortexInitialOpen p,
      ∃ N : ℕ, ∀ n ≥ N, ‖f n z‖ = 1 := by
    intro z
    exact ⟨0, fun n _ ↦
      norm_controlledAtlasVortexPathTransportPartialPhase
        p W v path T₀ hpW n z⟩
  exact exists_circlePrimitive_of_locally_eventuallyEq_unitPhase_with_stability
    SurfaceRealModel f hlocal hnorm

/-- Escaping controlled finite paths give a global smooth unit phase and a
circle primitive on the surface punctured at the fixed initial point. -/
theorem exists_circlePrimitive_of_locallyEscaping_controlledAtlasVortexPaths
    (p : X) (W : ℕ → TopologicalSpace.Opens X) (v : ℕ → X)
    (path : ∀ n, ControlledAtlasVortexPath (W n) (v n) (v (n + 1)))
    (T₀ : AtlasVortexTransportData X p (v 0))
    (hpW : ∀ n, p ∉ W n)
    (hescape : ∀ z : atlasVortexInitialOpen p,
      ∃ N : ℕ, ∃ U : TopologicalSpace.Opens (atlasVortexInitialOpen p),
        z ∈ U ∧ ∀ n ≥ N, ∀ y ∈ U, (y : X) ∉ W n) :
    ∃ (P : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
          (atlasVortexInitialOpen p) ℂ ∞)
        (hP : ∀ z : atlasVortexInitialOpen p, ‖P z‖ = 1),
      Nonempty (JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
        (smoothUnitPhaseOneForm SurfaceRealModel P hP)) := by
  rcases
      exists_circlePrimitive_of_locallyEscaping_controlledAtlasVortexPaths_with_stability
        p W v path T₀ hpW hescape with ⟨P, hP, _hstable, hprimitive⟩
  exact ⟨P, hP, hprimitive⟩

end

end JJMath.Uniformization
