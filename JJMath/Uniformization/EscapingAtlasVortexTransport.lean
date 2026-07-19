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

/--
%%handwave
name:
  A controlled transport block preserves the phase outside its control set
statement:
  When the \(n\)-th controlled vortex path inside \(W_n\) is appended to a
  transport, the new phase agrees with the preceding transport phase at every
  point outside \(W_n\).
proof:
  This is the exterior phase-preservation identity supplied by appending the
  controlled path, specialized to the recursively chosen transport.
-/
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

/--
%%handwave
name:
  Unit norm of a blockwise partial transport phase
statement:
  At every stage, the totalized blockwise transport phase on the surface
  punctured at the fixed initial point has complex modulus one.
proof:
  Away from the moving terminal point it is the unit phase of the current
  finite transport, while at that terminal point it is defined to be \(1\).
-/
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

/--
%%handwave
name:
  Smoothness of a blockwise partial phase off its moving endpoint
statement:
  The stage-\(n\) blockwise partial phase is smooth at every point other than
  its moving terminal point \(v_n\).
proof:
  On the open complement of \(v_n\), the partial phase is the smooth phase of
  the current finite transport, composed with the inclusion into the
  twice-punctured surface.
-/
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

/--
%%handwave
name:
  Successive blockwise partial phases agree outside the next control set
statement:
  If \(z\notin W_n\), then the stage-\(n+1\) and stage-\(n\) totalized
  transport phases take the same value at \(z\).
proof:
  Both endpoints of the \(n\)-th controlled path lie in \(W_n\), so \(z\)
  differs from them.  Expand both partial phases into the corresponding
  transport phases and apply preservation outside the control set.
-/
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

/--
%%handwave
name:
  Stable circle primitive from locally escaping controlled vortex paths
statement:
  Suppose a sequence of controlled vortex paths has control sets \(W_n\) that
  eventually miss a neighborhood of every point of
  \(X\setminus\{p\}\), and suppose \(p\notin W_n\) for all \(n\).  Then the
  blockwise phases stabilize locally to a smooth unit phase \(P\) on the
  punctured surface.  Pointwise, \(P\) equals every sufficiently late partial
  phase, and its logarithmic one-form has a circle primitive.
proof:
  On an escaping neighborhood, a sufficiently late partial phase is smooth
  and every subsequent block leaves it unchanged.  Thus the phases are
  locally eventually constant and have unit norm.  Apply the locally stable
  unit-phase theorem, retaining its pointwise stability conclusion.
-/
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

/--
%%handwave
name:
  Circle primitive from locally escaping controlled vortex paths
statement:
  Under the same local escape hypotheses, there is a smooth unit phase on
  \(X\setminus\{p\}\) whose canonical logarithmic one-form admits a circle
  primitive.
proof:
  Apply the stable escaping-path construction and discard its additional
  pointwise stabilization statement.
-/
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
