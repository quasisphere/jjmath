import JJMath.Hyperbolic.Converse.Continuation.PathSkeletons

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
Choose the normalized initial handoff from the basepoint chart to the chart
used by the first segment of a weak handoff skeleton.
-/
noncomputable def PathLocalTransitionModelWeakHandoffSkeleton.toBasedWeakHandoffSkeleton
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    (S :
      PathLocalTransitionModelWeakHandoffSkeleton x₀ g localModels p) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p where
  toPathLocalTransitionModelWeakHandoffSkeleton := S
  initialTransition := by
    have hx₀_base : x₀ ∈ (localModels.chartAt x₀).domain :=
      localModels.mem_chartAt_domain x₀
    have hx₀_first :
        x₀ ∈ (localModels.chartAt (S.centerAt 0)).domain := by
      have hsample := S.sample_mem_model_domain 0
      simpa [S.parameterAt_zero, p.source] using hsample
    exact Classical.choice
      (localModels.transition_localRealMobius x₀ (S.centerAt 0) x₀
        ⟨hx₀_base, hx₀_first⟩)

omit [RiemannSurface X] in
/--
%%handwave
name:
  Finite continuation chain along a path
statement:
  Let $p:[0,1]\to X$ run from $x_0$ to $x$. For an atlas of local
  hyperbolic branches, there are numbers
  $0=t_0<t_1<\cdots<t_n=1$ and local branches $F_0,\ldots,F_n$ such that
  $p([t_k,t_{k+1}])$ lies in the domain of $F_k$, consecutive branch domains
  overlap at $p(t_{k+1})$, and the chain begins with the branch normalized at
  $x_0$.
proof:
  Compactness of $p([0,1])$ gives a finite ordered subdivision subordinate to
  the local branch domains. Choose the initial transition from the normalized
  branch at $x_0$ to the first branch.
-/
theorem exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
    {x₀ : X} {g : HyperbolicMetric X}
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    {x : X} (p : Path x₀ x) :
    Nonempty
      (PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :=
  (exists_pathLocalTransitionModelWeakHandoffSkeleton localModels p).map
    PathLocalTransitionModelWeakHandoffSkeleton.toBasedWeakHandoffSkeleton

/--
A finite chain whose adjacent branch equalities are produced by explicit
local-transition handoff data.

This is closer to the eventual construction: once a path subdivision and
overlap neighborhoods are chosen, the accumulated Mobius representatives are
forced by the handoff rule `Mₖ₊₁ = Mₖ * Tₖ⁻¹`.
-/
structure PathLocalTransitionModelContinuationHandoffChain
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    {x : X} (p : Path x₀ x) where
  /-- Number of continuation steps. -/
  length : ℕ
  /-- Ordered path parameters at the vertices of the chain. -/
  parameterAt : Fin (length + 1) → unitInterval
  /-- The chain begins at the initial parameter. -/
  parameterAt_zero : parameterAt 0 = 0
  /-- The chain ends at the terminal parameter. -/
  parameterAt_last : parameterAt (Fin.last length) = 1
  /-- The parameters are weakly increasing. -/
  parameterAt_mono :
    ∀ k : Fin length,
      (parameterAt k.castSucc : ℝ) ≤ (parameterAt k.succ : ℝ)
  /-- Consecutive subdivision parameters are genuinely distinct. -/
  parameterAt_strictMono :
    ∀ k : Fin length,
      (parameterAt k.castSucc : ℝ) < (parameterAt k.succ : ℝ)
  /-- The local-transition model center used at each chain vertex. -/
  centerAt : Fin (length + 1) → X
  /-- The real Mobius postcomposition for the branch at each chain vertex. -/
  mobiusAt : Fin (length + 1) → RealMobiusRepresentative
  /-- The chain starts with the selected local model at the basepoint. -/
  initial_center_eq : centerAt 0 = x₀
  /-- The initial branch has identity Mobius normalization. -/
  initial_mobius_eq : mobiusAt 0 = 1
  /-- The local transition selected at each handoff. -/
  transitionAt :
    ∀ k : Fin length,
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (centerAt k.castSucc))
        (localModels.chartAt (centerAt k.succ))
        (p (parameterAt k.succ))
  /-- The accumulated Mobius representative is updated by the local handoff. -/
  mobiusAt_succ_eq :
    ∀ k : Fin length,
      mobiusAt k.succ =
        mobiusAt k.castSucc * (transitionAt k).representative⁻¹
  /-- The sampled path point lies in its selected model domain. -/
  sample_mem_model_domain :
    ∀ i,
      p (parameterAt i) ∈ (localModels.chartAt (centerAt i)).domain
  /--
  Each subinterval of the representative path is contained in the model domain
  attached to the initial vertex of that subinterval.
  -/
  path_segment_mem_model_domain :
    ∀ k : Fin length, ∀ t : unitInterval,
      (parameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (parameterAt k.succ : ℝ) →
      p t ∈ (localModels.chartAt (centerAt k.castSucc)).domain
  /-- The endpoint lies in the terminal model domain. -/
  terminal_endpoint_mem_domain :
    x ∈ (localModels.chartAt (centerAt (Fin.last length))).domain

namespace PathLocalTransitionModelContinuationHandoffChain

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

/--
The explicit handoff chain forgets to the finite-chain record by deriving the
adjacent normalized branch equalities from the local-transition representatives.
-/
def toPathLocalTransitionModelContinuationChain
    (C :
      PathLocalTransitionModelContinuationHandoffChain x₀ g localModels p) :
    PathLocalTransitionModelContinuationChain x₀ g localModels p where
  length := C.length
  parameterAt := C.parameterAt
  parameterAt_zero := C.parameterAt_zero
  parameterAt_last := C.parameterAt_last
  parameterAt_mono := C.parameterAt_mono
  parameterAt_strictMono := C.parameterAt_strictMono
  centerAt := C.centerAt
  mobiusAt := C.mobiusAt
  initial_center_eq := C.initial_center_eq
  initial_mobius_eq := C.initial_mobius_eq
  sample_mem_model_domain := C.sample_mem_model_domain
  path_segment_mem_model_domain := C.path_segment_mem_model_domain
  terminal_endpoint_mem_domain := C.terminal_endpoint_mem_domain
  adjacent_branch_agrees_at_transition := by
    intro k
    rw [C.mobiusAt_succ_eq k]
    exact
      localRealMobiusTransitionData_accumulated_handoff
        (C.transitionAt k) (C.transitionAt k).mem_neighborhood
        (C.mobiusAt k.castSucc)

omit [RiemannSurface X] in
@[simp]
theorem toPathLocalTransitionModelContinuationChain_length
    (C :
      PathLocalTransitionModelContinuationHandoffChain x₀ g localModels p) :
    C.toPathLocalTransitionModelContinuationChain.length = C.length :=
  rfl

end PathLocalTransitionModelContinuationHandoffChain

namespace PathLocalTransitionModelContinuationChain

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

/-- The initial local-transition model center selected by a finite chain. -/
def initialCenter
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) : X :=
  C.centerAt 0

/-- The initial Mobius representative selected by a finite chain. -/
def initialMobius
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    RealMobiusRepresentative :=
  C.mobiusAt 0

/-- The terminal local-transition model center selected by a finite chain. -/
def terminalCenter
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) : X :=
  C.centerAt (Fin.last C.length)

/-- The terminal Mobius representative selected by a finite chain. -/
def terminalMobius
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    RealMobiusRepresentative :=
  C.mobiusAt (Fin.last C.length)

/-- The normalized branch value at a sampled path point of the chain. -/
def branchValueAt
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (i : Fin (C.length + 1)) : ℍ :=
  realMobiusRepresentativeAction (C.mobiusAt i)
    ((localModels.chartAt (C.centerAt i)).toUpperHalfPlane
      (p (C.parameterAt i)))

/-- The normalized branch value along a subinterval of the chain. -/
def segmentBranchValue
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) (t : unitInterval) : ℍ :=
  realMobiusRepresentativeAction (C.mobiusAt k.castSucc)
    ((localModels.chartAt (C.centerAt k.castSucc)).toUpperHalfPlane (p t))

/-- The terminal value forced by a finite local-transition continuation chain. -/
def terminalValue
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) : ℍ :=
  realMobiusRepresentativeAction C.terminalMobius
    ((localModels.chartAt C.terminalCenter).toUpperHalfPlane x)

omit [RiemannSurface X] in
@[simp]
theorem terminalCenter_def
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.terminalCenter = C.centerAt (Fin.last C.length) :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem terminalMobius_def
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.terminalMobius = C.mobiusAt (Fin.last C.length) :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem initialCenter_eq_basepoint
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.initialCenter = x₀ := by
  simpa [initialCenter] using C.initial_center_eq

omit [RiemannSurface X] in
@[simp]
theorem initialMobius_eq_one
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.initialMobius = 1 := by
  simpa [initialMobius] using C.initial_mobius_eq

omit [RiemannSurface X] in
/--
A finite local-transition continuation chain has at least one subinterval:
the first and last subdivision parameters are forced to be `0` and `1`.
-/
theorem length_pos
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    0 < C.length := by
  rcases C with
    ⟨length, parameterAt, parameterAt_zero, parameterAt_last, _parameterAt_mono,
      _parameterAt_strictMono, _centerAt, _mobiusAt, _initial_center_eq,
      _initial_mobius_eq, _sample_mem_model_domain,
      _path_segment_mem_model_domain, _terminal_endpoint_mem_domain,
      _adjacent_branch_agrees_at_transition⟩
  dsimp
  cases length with
  | zero =>
      have h01 : (0 : unitInterval) = 1 :=
        parameterAt_zero.symm.trans (by simpa using parameterAt_last)
      have hreal : (0 : ℝ) = 1 := by
        simpa using congrArg (fun t : unitInterval => (t : ℝ)) h01
      norm_num at hreal
  | succ n =>
      simp

omit [RiemannSurface X] in
/-- The number of subintervals in a finite local-transition chain is nonzero. -/
theorem length_ne_zero
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.length ≠ 0 :=
  Nat.ne_of_gt C.length_pos

/-- The first subinterval of a finite local-transition continuation chain. -/
def firstSegmentIndex
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    Fin C.length :=
  ⟨0, C.length_pos⟩

/-- The last subinterval of a finite local-transition continuation chain. -/
def lastSegmentIndex
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    Fin C.length :=
  ⟨C.length - 1, Nat.pred_lt C.length_ne_zero⟩

omit [RiemannSurface X] in
@[simp]
theorem firstSegmentIndex_castSucc
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.firstSegmentIndex.castSucc = (0 : Fin (C.length + 1)) := by
  ext
  simp [firstSegmentIndex]

omit [RiemannSurface X] in
@[simp]
theorem lastSegmentIndex_succ_eq_last
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.lastSegmentIndex.succ = Fin.last C.length := by
  ext
  change C.length - 1 + 1 = C.length
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt C.length_pos)

omit [RiemannSurface X] in
/-- Consecutive subdivision parameters are strictly ordered. -/
theorem parameterAt_castSucc_lt_succ
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    (C.parameterAt k.castSucc : ℝ) < (C.parameterAt k.succ : ℝ) :=
  C.parameterAt_strictMono k

omit [RiemannSurface X] in
/-- The weak subdivision order follows from the strict subdivision order. -/
theorem parameterAt_castSucc_le_succ_of_strict
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    (C.parameterAt k.castSucc : ℝ) ≤ (C.parameterAt k.succ : ℝ) :=
  le_of_lt (C.parameterAt_castSucc_lt_succ k)

omit [RiemannSurface X] in
/-- Consecutive subdivision vertices are distinct as unit-interval points. -/
theorem parameterAt_castSucc_ne_succ
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    C.parameterAt k.castSucc ≠ C.parameterAt k.succ := by
  intro h
  have hreal :
      (C.parameterAt k.castSucc : ℝ) = (C.parameterAt k.succ : ℝ) := by
    simp [h]
  exact (ne_of_lt (C.parameterAt_castSucc_lt_succ k)) hreal

omit [RiemannSurface X] in
/-- The basepoint lies in the initial model domain forced by the chain. -/
theorem basepoint_mem_initial_model_domain
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    x₀ ∈ (localModels.chartAt x₀).domain := by
  have hsample := C.sample_mem_model_domain 0
  simpa [C.parameterAt_zero, C.initial_center_eq] using hsample

omit [RiemannSurface X] in
/-- The initial normalized branch is exactly the basepoint local model. -/
theorem initialBranchValue_eq_baseModel
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    realMobiusRepresentativeAction (C.mobiusAt 0)
        ((localModels.chartAt (C.centerAt 0)).toUpperHalfPlane x₀) =
      (localModels.chartAt x₀).toUpperHalfPlane x₀ := by
  simp [C.initial_center_eq, C.initial_mobius_eq,
    realMobiusRepresentativeAction_one]

omit [RiemannSurface X] in
/-- The first sampled branch value is the basepoint local model value. -/
theorem branchValueAt_zero_eq_baseModel
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.branchValueAt 0 = (localModels.chartAt x₀).toUpperHalfPlane x₀ := by
  simpa [branchValueAt, C.parameterAt_zero] using
    C.initialBranchValue_eq_baseModel

omit [RiemannSurface X] in
/-- The endpoint lies in the domain of the terminal center of the chain. -/
theorem endpoint_mem_terminalCenter_domain
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    x ∈ (localModels.chartAt C.terminalCenter).domain := by
  simpa [terminalCenter] using C.terminal_endpoint_mem_domain

omit [RiemannSurface X] in
/--
The segment branch is defined on the whole corresponding closed subinterval
of the representative path.
-/
theorem segmentBranchValue_mem_model_domain
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) {t : unitInterval}
    (ht_left : (C.parameterAt k.castSucc : ℝ) ≤ (t : ℝ))
    (ht_right : (t : ℝ) ≤ (C.parameterAt k.succ : ℝ)) :
    p t ∈ (localModels.chartAt (C.centerAt k.castSucc)).domain :=
  C.path_segment_mem_model_domain k t ht_left ht_right

omit [RiemannSurface X] in
/-- At the left endpoint, a segment branch gives the sampled branch value. -/
theorem segmentBranchValue_leftEndpoint
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    C.segmentBranchValue k (C.parameterAt k.castSucc) =
      C.branchValueAt k.castSucc :=
  rfl

omit [RiemannSurface X] in
/-- The first segment starts with the basepoint local model value. -/
theorem firstSegmentBranchValue_leftEndpoint_eq_baseModel
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.segmentBranchValue C.firstSegmentIndex
        (C.parameterAt C.firstSegmentIndex.castSucc) =
      (localModels.chartAt x₀).toUpperHalfPlane x₀ := by
  simpa [segmentBranchValue, branchValueAt] using
    C.branchValueAt_zero_eq_baseModel

omit [RiemannSurface X] in
/--
The transition point between two consecutive subintervals lies in both
adjacent model domains.
-/
theorem transitionPoint_mem_adjacent_overlap
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    p (C.parameterAt k.succ) ∈
      (localModels.chartAt (C.centerAt k.castSucc)).domain ∩
        (localModels.chartAt (C.centerAt k.succ)).domain := by
  constructor
  · exact C.path_segment_mem_model_domain k (C.parameterAt k.succ)
      (C.parameterAt_mono k) le_rfl
  · exact C.sample_mem_model_domain k.succ

omit [RiemannSurface X] in
/-- Adjacent overlap nonemptiness follows from the shared transition point. -/
theorem adjacent_overlap_nonempty_from_transition
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    Set.Nonempty
      ((localModels.chartAt (C.centerAt k.castSucc)).domain ∩
        (localModels.chartAt (C.centerAt k.succ)).domain) :=
  ⟨p (C.parameterAt k.succ), C.transitionPoint_mem_adjacent_overlap k⟩

omit [RiemannSurface X] in
/-- Adjacent normalized branches agree at the actual subdivision transition. -/
theorem adjacent_branch_eq_at_transition
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    realMobiusRepresentativeAction (C.mobiusAt k.succ)
        ((localModels.chartAt (C.centerAt k.succ)).toUpperHalfPlane
          (p (C.parameterAt k.succ))) =
      realMobiusRepresentativeAction (C.mobiusAt k.castSucc)
        ((localModels.chartAt (C.centerAt k.castSucc)).toUpperHalfPlane
          (p (C.parameterAt k.succ))) := by
  exact C.adjacent_branch_agrees_at_transition k

omit [RiemannSurface X] in
/--
The sampled value at the next vertex equals the previous branch evaluated at
the transition point.
-/
theorem branchValueAt_succ_eq_leftTransitionValue
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    C.branchValueAt k.succ =
      realMobiusRepresentativeAction (C.mobiusAt k.castSucc)
        ((localModels.chartAt (C.centerAt k.castSucc)).toUpperHalfPlane
          (p (C.parameterAt k.succ))) := by
  simpa [branchValueAt] using C.adjacent_branch_agrees_at_transition k

omit [RiemannSurface X] in
/-- At the right endpoint, a segment branch gives the next sampled value. -/
theorem segmentBranchValue_rightEndpoint
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    C.segmentBranchValue k (C.parameterAt k.succ) =
      C.branchValueAt k.succ := by
  simpa [segmentBranchValue] using
    (C.branchValueAt_succ_eq_leftTransitionValue k).symm

omit [RiemannSurface X] in
/--
Adjacent segment branches glue at a shared subdivision vertex.  The hypothesis
`k.succ = l.castSucc` says that the right endpoint of segment `k` is the left
endpoint of segment `l`.
-/
theorem segmentBranchValue_glues_at_shared_endpoint
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k l : Fin C.length) (h : k.succ = l.castSucc) :
    C.segmentBranchValue k (C.parameterAt k.succ) =
      C.segmentBranchValue l (C.parameterAt l.castSucc) := by
  rw [C.segmentBranchValue_rightEndpoint k,
    C.segmentBranchValue_leftEndpoint l, h]

omit [RiemannSurface X] in
/-- The terminal value of the chain is the last sampled branch value. -/
theorem terminalValue_eq_branchValueAt_last
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.terminalValue = C.branchValueAt (Fin.last C.length) := by
  simp [terminalValue, branchValueAt, terminalCenter, terminalMobius,
    C.parameterAt_last]

omit [RiemannSurface X] in
/--
If a subinterval ends at the final subdivision vertex, its segment branch value
at that endpoint is the terminal value of the whole chain.
-/
theorem segmentBranchValue_rightEndpoint_eq_terminalValue_of_succ_eq_last
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) (hk : k.succ = Fin.last C.length) :
    C.segmentBranchValue k (C.parameterAt k.succ) = C.terminalValue := by
  rw [C.segmentBranchValue_rightEndpoint k, hk]
  exact C.terminalValue_eq_branchValueAt_last.symm

omit [RiemannSurface X] in
/-- The last segment ends at the terminal value of the whole chain. -/
theorem lastSegmentBranchValue_rightEndpoint_eq_terminalValue
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    C.segmentBranchValue C.lastSegmentIndex
        (C.parameterAt C.lastSegmentIndex.succ) =
      C.terminalValue :=
  C.segmentBranchValue_rightEndpoint_eq_terminalValue_of_succ_eq_last
    C.lastSegmentIndex C.lastSegmentIndex_succ_eq_last

end PathLocalTransitionModelContinuationChain

/--
Value-level terminal continuation data produced by explicit handoff chains.

This is the boundary closest to the eventual path-subdivision construction:
each representative path is assigned a finite handoff chain whose accumulated
Mobius representatives are updated by local transition inverses.
-/
structure PathLocalTransitionHandoffChainTerminalBranchAnalyticContinuationValueData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- An explicit finite local-transition handoff chain along each representative path. -/
  handoffChainAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelContinuationHandoffChain x₀ g localModels p
  /-- A sheet neighborhood on which the terminal handoff-chain branch is valid. -/
  neighborhoodAlong :
    ∀ {x : X}, Path x₀ x → Set (PathHomotopyUniversalCover X x₀)
  /-- The terminal value descends through endpoint-fixed path homotopy. -/
  terminalValue_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      ((handoffChainAlong p).toPathLocalTransitionModelContinuationChain).terminalValue =
        ((handoffChainAlong q).toPathLocalTransitionModelContinuationChain).terminalValue
  /-- The terminal sheet is open. -/
  isOpen_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x), IsOpen (neighborhoodAlong p)
  /-- The represented path-class point lies in its terminal sheet. -/
  mem_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x),
      (⟨x, Path.Homotopic.Quotient.mk p⟩ :
        PathHomotopyUniversalCover X x₀) ∈ neighborhoodAlong p
  /-- Points in the terminal sheet project into the terminal handoff-chain model domain. -/
  endpoint_mem_model_domain :
    ∀ {x : X} (p : Path x₀ x) y', y' ∈ neighborhoodAlong p →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt
          (((handoffChainAlong p).toPathLocalTransitionModelContinuationChain).terminalCenter)).domain
  /--
  On the terminal sheet, the terminal handoff-chain branch computed from any
  representative of the upstairs point agrees with the sheet formula
  determined by `p`.
  -/
  terminalValue_eq_on_neighborhood :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ neighborhoodAlong p →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      realMobiusRepresentativeAction
          (((handoffChainAlong p').toPathLocalTransitionModelContinuationChain).terminalMobius)
          ((localModels.chartAt
              (((handoffChainAlong p').toPathLocalTransitionModelContinuationChain).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction
          (((handoffChainAlong p).toPathLocalTransitionModelContinuationChain).terminalMobius)
          ((localModels.chartAt
              (((handoffChainAlong p).toPathLocalTransitionModelContinuationChain).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

/--
Value-level finite-chain terminal continuation data for a local-transition
atlas.

Only the continued value is required to descend through endpoint-fixed
homotopy.  Auxiliary terminal chart and sheet choices may be selected from a
representative path class.
-/
structure PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- A finite local-transition continuation chain along each representative path. -/
  chainAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelContinuationChain x₀ g localModels p
  /-- A sheet neighborhood on which the terminal chain branch is valid. -/
  neighborhoodAlong :
    ∀ {x : X}, Path x₀ x → Set (PathHomotopyUniversalCover X x₀)
  /-- The terminal value descends through endpoint-fixed path homotopy. -/
  terminalValue_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      (chainAlong p).terminalValue = (chainAlong q).terminalValue
  /-- The terminal sheet is open. -/
  isOpen_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x), IsOpen (neighborhoodAlong p)
  /-- The represented path-class point lies in its terminal sheet. -/
  mem_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x),
      (⟨x, Path.Homotopic.Quotient.mk p⟩ :
        PathHomotopyUniversalCover X x₀) ∈ neighborhoodAlong p
  /-- Points in the terminal sheet project into the terminal chain model domain. -/
  endpoint_mem_model_domain :
    ∀ {x : X} (p : Path x₀ x) y', y' ∈ neighborhoodAlong p →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt ((chainAlong p).terminalCenter)).domain
  /--
  On the terminal sheet, the finite-chain terminal branch computed from any
  representative of the upstairs point agrees with the sheet formula
  determined by `p`.
  -/
  terminalValue_eq_on_neighborhood :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ neighborhoodAlong p →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      realMobiusRepresentativeAction ((chainAlong p').terminalMobius)
          ((localModels.chartAt ((chainAlong p').terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction ((chainAlong p).terminalMobius)
          ((localModels.chartAt ((chainAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

namespace PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The terminal value forced by a finite-chain terminal branch. -/
def terminalValue
    (C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  (C.chainAlong p).terminalValue

omit [RiemannSurface X] in
@[simp]
theorem terminalValue_eq_chain_terminalValue
    (C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValue p = (C.chainAlong p).terminalValue :=
  rfl

omit [ChartedSpace ℂ X] [RiemannSurface X] in
theorem out_homotopic_mk
    {x : X} (p : Path x₀ x) :
    Path.Homotopic
      (Quot.out (Path.Homotopic.Quotient.mk p))
      p := by
  exact
    (Path.Homotopic.Quotient.eq).mp
      (Quot.out_eq (Path.Homotopic.Quotient.mk p))

/--
The terminal value at a path-homotopy class, computed from Lean's chosen
representative and justified by value-level homotopy descent.
-/
noncomputable def terminalValueAt
    (C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) : ℍ :=
  C.terminalValue (Quot.out q)

/-- The terminal center attached to Lean's chosen representative of a path class. -/
noncomputable def terminalCenterAt
    (C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) : X :=
  (C.chainAlong (Quot.out q)).terminalCenter

/-- The terminal Mobius representative attached to Lean's chosen representative. -/
noncomputable def terminalMobiusAt
    (C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    RealMobiusRepresentative :=
  (C.chainAlong (Quot.out q)).terminalMobius

/-- The terminal sheet attached to Lean's chosen representative of a path class. -/
noncomputable def terminalNeighborhoodAt
    (C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    Set (PathHomotopyUniversalCover X x₀) :=
  C.neighborhoodAlong (Quot.out q)

omit [RiemannSurface X] in
@[simp]
theorem terminalValueAt_mk
    (C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValueAt x (Path.Homotopic.Quotient.mk p) =
      C.terminalValue p := by
  exact C.terminalValue_homotopic (out_homotopic_mk p)

/--
Value-level finite-chain local-transition continuation data descend to
path-class local-transition continuation data.
-/
noncomputable def toPathClassLocalTransitionAnalyticContinuationData
    (C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationData x₀ g localModels where
  valueAt := C.terminalValueAt
  centerAt := C.terminalCenterAt
  mobiusAt := C.terminalMobiusAt
  neighborhoodAt := C.terminalNeighborhoodAt
  isOpen_neighborhoodAt := by
    intro x q
    exact C.isOpen_neighborhoodAlong (Quot.out q)
  mem_neighborhoodAt := by
    intro x q
    have hmem := C.mem_neighborhoodAlong (Quot.out q)
    have hpoint :
        (⟨x, q⟩ : PathHomotopyUniversalCover X x₀) =
          ⟨x, Path.Homotopic.Quotient.mk (Quot.out q)⟩ := by
      exact Sigma.ext rfl (heq_of_eq (Quot.out_eq q).symm)
    simpa [terminalNeighborhoodAt, hpoint] using hmem
  endpoint_mem_model_domain := by
    intro x q y' hy'
    exact C.endpoint_mem_model_domain (Quot.out q) y' hy'
  value_eq_on_neighborhood := by
    intro x q y' hy'
    let p : Path x₀ x := Quot.out q
    let p' : Path x₀ (PathHomotopyUniversalCover.endpoint y') :=
      Quot.out (PathHomotopyUniversalCover.pathClass y')
    have hclass :
        Path.Homotopic.Quotient.mk p' =
          PathHomotopyUniversalCover.pathClass y' := by
      exact Quot.out_eq (PathHomotopyUniversalCover.pathClass y')
    simpa [terminalValueAt, terminalValue, terminalCenterAt,
      terminalMobiusAt, terminalNeighborhoodAt, p, p'] using
      C.terminalValue_eq_on_neighborhood p y' p' hy' hclass

end PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData

namespace PathLocalTransitionHandoffChainTerminalBranchAnalyticContinuationValueData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Explicit handoff-chain value data forgets to ordinary finite-chain value data.
-/
def toPathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
    (C :
      PathLocalTransitionHandoffChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels) :
    PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
      x₀ g localModels where
  chainAlong := fun {_} p =>
    (C.handoffChainAlong p).toPathLocalTransitionModelContinuationChain
  neighborhoodAlong := C.neighborhoodAlong
  terminalValue_homotopic := C.terminalValue_homotopic
  isOpen_neighborhoodAlong := C.isOpen_neighborhoodAlong
  mem_neighborhoodAlong := C.mem_neighborhoodAlong
  endpoint_mem_model_domain := C.endpoint_mem_model_domain
  terminalValue_eq_on_neighborhood := C.terminalValue_eq_on_neighborhood

omit [RiemannSurface X] in
@[simp]
theorem toValueData_chainAlong
    (C :
      PathLocalTransitionHandoffChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    (C.toPathLocalTransitionChainTerminalBranchAnalyticContinuationValueData.chainAlong p) =
      (C.handoffChainAlong p).toPathLocalTransitionModelContinuationChain :=
  rfl

end PathLocalTransitionHandoffChainTerminalBranchAnalyticContinuationValueData

/--
Value-level terminal continuation data produced by based weak handoff skeletons.

This boundary uses the compactness-produced local-transition subdivisions and
the initial basepoint handoff directly.  It avoids requiring a strict
finite-chain subdivision whose first whole segment lies in the basepoint
chart.
-/
structure PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- A based weak handoff skeleton along each representative path. -/
  basedWeakHandoffAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /-- A sheet neighborhood on which the terminal branch is valid. -/
  neighborhoodAlong :
    ∀ {x : X}, Path x₀ x → Set (PathHomotopyUniversalCover X x₀)
  /-- The terminal value descends through endpoint-fixed path homotopy. -/
  terminalValue_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      (basedWeakHandoffAlong p).terminalValue =
        (basedWeakHandoffAlong q).terminalValue
  /-- The terminal sheet is open. -/
  isOpen_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x), IsOpen (neighborhoodAlong p)
  /-- The represented path-class point lies in its terminal sheet. -/
  mem_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x),
      (⟨x, Path.Homotopic.Quotient.mk p⟩ :
        PathHomotopyUniversalCover X x₀) ∈ neighborhoodAlong p
  /-- Points in the terminal sheet project into the terminal model domain. -/
  endpoint_mem_model_domain :
    ∀ {x : X} (p : Path x₀ x) y', y' ∈ neighborhoodAlong p →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt ((basedWeakHandoffAlong p).terminalCenter)).domain
  /--
  On the terminal sheet, the based weak handoff terminal branch computed from
  any representative of the upstairs point agrees with the sheet formula
  determined by `p`.
  -/
  terminalValue_eq_on_neighborhood :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ neighborhoodAlong p →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      realMobiusRepresentativeAction ((basedWeakHandoffAlong p').terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p').terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction ((basedWeakHandoffAlong p).terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

namespace PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The terminal value forced by a based weak handoff terminal branch. -/
def terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  (C.basedWeakHandoffAlong p).terminalValue

omit [RiemannSurface X] in
@[simp]
theorem terminalValue_eq_basedWeakHandoff_terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValue p = (C.basedWeakHandoffAlong p).terminalValue :=
  rfl

/--
The terminal value at a path-homotopy class, computed from Lean's chosen
representative and justified by value-level homotopy descent.
-/
noncomputable def terminalValueAt
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) : ℍ :=
  C.terminalValue (Quot.out q)

/-- The terminal center attached to Lean's chosen representative of a path class. -/
noncomputable def terminalCenterAt
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) : X :=
  (C.basedWeakHandoffAlong (Quot.out q)).terminalCenter

/-- The terminal Mobius representative attached to Lean's chosen representative. -/
noncomputable def terminalMobiusAt
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    RealMobiusRepresentative :=
  (C.basedWeakHandoffAlong (Quot.out q)).terminalMobius

/-- The terminal sheet attached to Lean's chosen representative of a path class. -/
noncomputable def terminalNeighborhoodAt
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    Set (PathHomotopyUniversalCover X x₀) :=
  C.neighborhoodAlong (Quot.out q)

omit [RiemannSurface X] in
@[simp]
theorem terminalValueAt_mk
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValueAt x (Path.Homotopic.Quotient.mk p) =
      C.terminalValue p := by
  exact C.terminalValue_homotopic
    (PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData.out_homotopic_mk p)

/--
Based weak handoff value-continuation data descend to path-class
local-transition continuation data.
-/
noncomputable def toPathClassLocalTransitionAnalyticContinuationData
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationData x₀ g localModels where
  valueAt := C.terminalValueAt
  centerAt := C.terminalCenterAt
  mobiusAt := C.terminalMobiusAt
  neighborhoodAt := C.terminalNeighborhoodAt
  isOpen_neighborhoodAt := by
    intro x q
    exact C.isOpen_neighborhoodAlong (Quot.out q)
  mem_neighborhoodAt := by
    intro x q
    have hmem := C.mem_neighborhoodAlong (Quot.out q)
    have hpoint :
        (⟨x, q⟩ : PathHomotopyUniversalCover X x₀) =
          ⟨x, Path.Homotopic.Quotient.mk (Quot.out q)⟩ := by
      exact Sigma.ext rfl (heq_of_eq (Quot.out_eq q).symm)
    simpa [terminalNeighborhoodAt, hpoint] using hmem
  endpoint_mem_model_domain := by
    intro x q y' hy'
    exact C.endpoint_mem_model_domain (Quot.out q) y' hy'
  value_eq_on_neighborhood := by
    intro x q y' hy'
    let p : Path x₀ x := Quot.out q
    let p' : Path x₀ (PathHomotopyUniversalCover.endpoint y') :=
      Quot.out (PathHomotopyUniversalCover.pathClass y')
    have hclass :
        Path.Homotopic.Quotient.mk p' =
          PathHomotopyUniversalCover.pathClass y' := by
      exact Quot.out_eq (PathHomotopyUniversalCover.pathClass y')
    simpa [terminalValueAt, terminalValue, terminalCenterAt,
      terminalMobiusAt, terminalNeighborhoodAt, p, p'] using
      C.terminalValue_eq_on_neighborhood p y' p' hy' hclass

end PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData

/--
Based weak handoff terminal continuation data using the canonical terminal
sheet attached to the terminal local-model domain.

Compared with
`PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData`,
this record no longer asks for open terminal neighborhoods or endpoint-domain
membership: those are constructed canonically from the terminal model domain.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- A based weak handoff skeleton along each representative path. -/
  basedWeakHandoffAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /-- The terminal value descends through endpoint-fixed path homotopy. -/
  terminalValue_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      (basedWeakHandoffAlong p).terminalValue =
        (basedWeakHandoffAlong q).terminalValue
  /--
  On the canonical terminal sheet, the based weak handoff terminal branch
  computed from any representative of the upstairs point agrees with the
  terminal sheet formula determined by `p`.
  -/
  terminalValue_eq_on_terminalSheet :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ (basedWeakHandoffAlong p).terminalSheet →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      realMobiusRepresentativeAction ((basedWeakHandoffAlong p').terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p').terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction ((basedWeakHandoffAlong p).terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The terminal value forced by canonical-terminal-sheet based weak handoff data. -/
def terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  (C.basedWeakHandoffAlong p).terminalValue

@[simp]
theorem terminalValue_eq_basedWeakHandoff_terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValue p = (C.basedWeakHandoffAlong p).terminalValue :=
  rfl

/--
Canonical-terminal-sheet based weak handoff data fill the full value
continuation record by using the terminal local sheet as the neighborhood.
-/
noncomputable def toPathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
      x₀ g localModels where
  basedWeakHandoffAlong := C.basedWeakHandoffAlong
  neighborhoodAlong := fun {_} p =>
    (C.basedWeakHandoffAlong p).terminalSheet
  terminalValue_homotopic := C.terminalValue_homotopic
  isOpen_neighborhoodAlong := by
    intro x p
    exact (C.basedWeakHandoffAlong p).isOpen_terminalSheet
  mem_neighborhoodAlong := by
    intro x p
    have hmem := (C.basedWeakHandoffAlong p).terminalCoverPoint_mem_terminalSheet
    simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCoverPoint] using hmem
  endpoint_mem_model_domain := by
    intro x p y' hy'
    exact
      (C.basedWeakHandoffAlong p).endpoint_mem_terminal_domain_of_mem_terminalSheet
        hy'
  terminalValue_eq_on_neighborhood := C.terminalValue_eq_on_terminalSheet

@[simp]
theorem toValueData_neighborhoodAlong
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toPathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData.neighborhoodAlong p =
      (C.basedWeakHandoffAlong p).terminalSheet :=
  rfl

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData

/--
Canonical-terminal-sheet agreement data for based weak handoff continuation.

This is weaker than
`PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData`:
it does not assume endpoint-fixed homotopy invariance of terminal values.
Homotopy invariance is derived from terminal-sheet agreement, because
homotopic paths determine the same point of the canonical cover.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- A based weak handoff skeleton along each representative path. -/
  basedWeakHandoffAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /--
  On the canonical terminal sheet, the based weak handoff terminal branch
  computed from any representative of the upstairs point agrees with the
  terminal sheet formula determined by `p`.
  -/
  terminalValue_eq_on_terminalSheet :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ (basedWeakHandoffAlong p).terminalSheet →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      realMobiusRepresentativeAction ((basedWeakHandoffAlong p').terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p').terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction ((basedWeakHandoffAlong p).terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

/--
A set of upper-half-plane points is large enough to identify PSL
transformations by their actions.
-/
def RealMobiusActionFaithfulOn (s : Set ℍ) : Prop :=
  ∀ g h : RealMobiusGroup,
    (∀ z ∈ s, realMobiusAction g z = realMobiusAction h z) → g = h

/-- A set of upper-half-plane points contains three pairwise distinct points. -/
def ContainsThreeDistinctUpperHalfPlanePoints (s : Set ℍ) : Prop :=
  ∃ z₁ z₂ z₃ : ℍ,
    z₁ ∈ s ∧ z₂ ∈ s ∧ z₃ ∈ s ∧
      z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃

/--
The global three-point faithfulness theorem for the PSL action on `ℍ`.
Mathematically, this is the statement that three distinct points and their
images determine a Möbius transformation.
-/
def RealMobiusActionDeterminedByThreePointsTheoremPSL : Prop :=
  ∀ (g h : RealMobiusGroup) (z₁ z₂ z₃ : ℍ),
    z₁ ≠ z₂ → z₁ ≠ z₃ → z₂ ≠ z₃ →
      realMobiusAction g z₁ = realMobiusAction h z₁ →
      realMobiusAction g z₂ = realMobiusAction h z₂ →
      realMobiusAction g z₃ = realMobiusAction h z₃ →
      g = h

/-- The PSL action on `ℍ` is determined by three distinct points. -/
theorem realMobiusActionDeterminedByThreePointsTheoremPSL :
    RealMobiusActionDeterminedByThreePointsTheoremPSL :=
  realMobiusAction_determined_by_three_points

/--
Three contained distinct points make a set PSL-action-faithful, assuming the
global three-point faithfulness theorem.
-/
theorem realMobiusActionFaithfulOn_of_containsThreeDistinctUpperHalfPlanePoints
    (hThree : RealMobiusActionDeterminedByThreePointsTheoremPSL)
    {s : Set ℍ}
    (hs : ContainsThreeDistinctUpperHalfPlanePoints s) :
    RealMobiusActionFaithfulOn s := by
  intro g h hAction
  rcases hs with ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, h₁₂, h₁₃, h₂₃⟩
  exact
    hThree g h z₁ z₂ z₃ h₁₂ h₁₃ h₂₃
      (hAction z₁ hz₁) (hAction z₂ hz₂) (hAction z₃ hz₃)

/-- The whole upper half-plane contains three pairwise distinct points. -/
theorem containsThreeDistinctUpperHalfPlanePoints_univ :
    ContainsThreeDistinctUpperHalfPlanePoints (Set.univ : Set ℍ) := by
  refine
    ⟨(⟨I, by norm_num⟩ : ℍ),
      (⟨2 * I, by norm_num⟩ : ℍ),
      (⟨3 * I, by norm_num⟩ : ℍ),
      by simp, by simp, by simp, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun z : ℍ => (z : ℂ)) h
    norm_num at hc
  · intro h
    have hc := congrArg (fun z : ℍ => (z : ℂ)) h
    norm_num at hc
  · intro h
    have hc := congrArg (fun z : ℍ => (z : ℂ)) h
    norm_num at hc

/-- The PSL action on the whole upper half-plane is faithful. -/
theorem realMobiusActionFaithfulOn_univ :
    RealMobiusActionFaithfulOn (Set.univ : Set ℍ) :=
  realMobiusActionFaithfulOn_of_containsThreeDistinctUpperHalfPlanePoints
    realMobiusActionDeterminedByThreePointsTheoremPSL
    containsThreeDistinctUpperHalfPlanePoints_univ

/--
Two real-Mobius representatives inducing the same action on all of `ℍ` have the
same PSL class.
-/
theorem realMobiusProjection_eq_of_representative_action_eq
    (A B : RealMobiusRepresentative)
    (hAction :
      ∀ z : ℍ,
        realMobiusRepresentativeAction A z =
          realMobiusRepresentativeAction B z) :
    realMobiusProjection A = realMobiusProjection B :=
  realMobiusActionFaithfulOn_univ
    (realMobiusProjection A) (realMobiusProjection B) (by
      intro z _hz
      simpa only [realMobiusAction_realMobiusProjection] using hAction z)

/--
Two real-Mobius representatives whose inverse representatives induce the same
action on all of `ℍ` have the same PSL class.
-/
theorem realMobiusProjection_eq_of_representative_inverse_action_eq
    (A B : RealMobiusRepresentative)
    (hAction :
      ∀ z : ℍ,
        realMobiusRepresentativeAction A⁻¹ z =
          realMobiusRepresentativeAction B⁻¹ z) :
    realMobiusProjection A = realMobiusProjection B := by
  have hInv :
      realMobiusProjection A⁻¹ = realMobiusProjection B⁻¹ :=
    realMobiusProjection_eq_of_representative_action_eq A⁻¹ B⁻¹ hAction
  simpa using congrArg Inv.inv hInv

omit [RiemannSurface X] in
/--
If two based handoff skeletons have matching inverse actions at every handoff,
then their terminal Mobius representatives have the same PSL class.
-/
theorem PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalMobius_projection_eq_of_transition_inverse_actions
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (hLength : S.length = T.length)
    (hInitial :
      ∀ z : ℍ,
        realMobiusRepresentativeAction S.initialTransition.representative⁻¹ z =
          realMobiusRepresentativeAction T.initialTransition.representative⁻¹ z)
    (hTransition :
      ∀ n (hnS : n < S.length) (hnT : n < T.length) (z : ℍ),
        realMobiusRepresentativeAction
            (S.transitionAt ⟨n, hnS⟩).representative⁻¹ z =
          realMobiusRepresentativeAction
            (T.transitionAt ⟨n, hnT⟩).representative⁻¹ z) :
    realMobiusProjection S.terminalMobius =
      realMobiusProjection T.terminalMobius := by
  have hacc :
      ∀ z : ℍ,
        realMobiusRepresentativeAction
            (S.accumulatedMobiusNat S.length) z =
          realMobiusRepresentativeAction
            (T.accumulatedMobiusNat S.length) z :=
    S.accumulatedMobiusNat_action_eq_of_transition_inverse_actions T
      hLength hInitial hTransition S.length le_rfl
  have hindex :
      T.accumulatedMobiusNat S.length =
        T.accumulatedMobiusNat T.length :=
    congrArg T.accumulatedMobiusNat hLength
  change realMobiusProjection (S.accumulatedMobiusNat S.length) =
    realMobiusProjection (T.accumulatedMobiusNat T.length)
  rw [← hindex]
  exact realMobiusProjection_eq_of_representative_action_eq _ _ hacc

/-- An infinite set contains three pairwise distinct points. -/
theorem containsThreeDistinctUpperHalfPlanePoints_of_infinite
    {s : Set ℍ} (hs : s.Infinite) :
    ContainsThreeDistinctUpperHalfPlanePoints s := by
  rcases hs.nonempty with ⟨z₁, hz₁⟩
  have hdiff₁ : (s \ ({z₁} : Set ℍ)).Infinite :=
    hs.diff (Set.finite_singleton z₁)
  rcases hdiff₁.nonempty with ⟨z₂, hz₂⟩
  have hz₂s : z₂ ∈ s := hz₂.1
  have hz₂_ne_z₁ : z₂ ≠ z₁ := by
    intro h
    exact hz₂.2 (by simp [h])
  have hpairFinite : ({z₁, z₂} : Set ℍ).Finite := by
    exact (Set.finite_singleton z₂).insert z₁
  have hdiff₂ : (s \ ({z₁, z₂} : Set ℍ)).Infinite :=
    hs.diff hpairFinite
  rcases hdiff₂.nonempty with ⟨z₃, hz₃⟩
  have hz₃s : z₃ ∈ s := hz₃.1
  have hz₃_ne_z₁ : z₃ ≠ z₁ := by
    intro h
    exact hz₃.2 (by simp [h])
  have hz₃_ne_z₂ : z₃ ≠ z₂ := by
    intro h
    exact hz₃.2 (by simp [h])
  exact
    ⟨z₁, z₂, z₃, hz₁, hz₂s, hz₃s,
      hz₂_ne_z₁.symm, hz₃_ne_z₁.symm, hz₃_ne_z₂.symm⟩

/--
A set containing a nonempty open subset of the upper half-plane contains three
pairwise distinct points.
-/
theorem containsThreeDistinctUpperHalfPlanePoints_of_nonempty_open_subset
    {s u : Set ℍ} (huOpen : IsOpen u) (huNonempty : u.Nonempty)
    (huSubset : u ⊆ s) :
    ContainsThreeDistinctUpperHalfPlanePoints s := by
  rcases huNonempty with ⟨z, hzu⟩
  have huMem : u ∈ nhds z := huOpen.mem_nhds hzu
  have huInfinite : u.Infinite := infinite_of_mem_nhds z huMem
  exact containsThreeDistinctUpperHalfPlanePoints_of_infinite
    (huInfinite.mono huSubset)

/--
The PSL class of a local real-Mobius transition between fixed local charts is
unique.

Two representatives that realize the same chart transition near the same
overlap point agree on an open upper-half-plane patch in the source
coordinate.  Three-point faithfulness of the PSL action then identifies their
projective classes.  This is the local algebraic uniqueness needed by the
componentwise monodromy proof when a finite continuation chain is refined.
-/
theorem localRealMobiusTransitionData_projection_eq
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g} {x : X}
    (T₁ T₂ : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x) :
    realMobiusProjection T₁.representative =
      realMobiusProjection T₂.representative := by
  classical
  let W : Set X := T₁.neighborhood ∩ T₂.neighborhood
  have hWopen : IsOpen W :=
    T₁.isOpen_neighborhood.inter T₂.isOpen_neighborhood
  have hxW : x ∈ W := ⟨T₁.mem_neighborhood, T₂.mem_neighborhood⟩
  have hxU : x ∈ U.domain :=
    (T₁.subset_overlap T₁.mem_neighborhood).1
  rcases
      HyperbolicLocalChart.exists_open_upperHalfPlane_subset_image_of_mem_nhds
        U hxU (hWopen.mem_nhds hxW) with
    ⟨u, huOpen, hxu, huSubset⟩
  let s : Set ℍ := U.toUpperHalfPlane '' (W ∩ U.domain)
  have hsThree : ContainsThreeDistinctUpperHalfPlanePoints s :=
    containsThreeDistinctUpperHalfPlanePoints_of_nonempty_open_subset
      huOpen ⟨U.toUpperHalfPlane x, hxu⟩ (by
        intro z hz
        exact huSubset hz)
  have hsFaithful : RealMobiusActionFaithfulOn s :=
    realMobiusActionFaithfulOn_of_containsThreeDistinctUpperHalfPlanePoints
      realMobiusActionDeterminedByThreePointsTheoremPSL hsThree
  exact
    hsFaithful
      (realMobiusProjection T₁.representative)
      (realMobiusProjection T₂.representative)
      (by
        intro z hz
        rcases hz with ⟨y, hy, rfl⟩
        have h₁ := T₁.transition_eq y hy.1.1
        have h₂ := T₂.transition_eq y hy.1.2
        have hRep :
            realMobiusRepresentativeAction T₁.representative
                (U.toUpperHalfPlane y) =
              realMobiusRepresentativeAction T₂.representative
                (U.toUpperHalfPlane y) :=
          h₁.symm.trans h₂
        simpa only [realMobiusAction_realMobiusProjection] using hRep)

/--
On a preconnected overlap region, the PSL class of the local real-Mobius
transition between two fixed charts is constant.

The only extra input is local existence of transition data at every point of
the region.  The proof is the usual clopen propagation argument: near any
point, recentering one local transition datum gives the same representative,
and same-point uniqueness identifies it with any other local datum there.
-/
theorem localRealMobiusTransitionData_projection_eq_of_preconnected
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {W : Set X} (hWpre : IsPreconnected W)
    (hWexists :
      ∀ ⦃y : X⦄, y ∈ W →
        Nonempty (HyperbolicLocalChart.LocalRealMobiusTransitionData U V y))
    {x y : X} (hxW : x ∈ W) (hyW : y ∈ W)
    (Tx : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (Ty : HyperbolicLocalChart.LocalRealMobiusTransitionData U V y) :
    realMobiusProjection Ty.representative =
      realMobiusProjection Tx.representative := by
  classical
  let E : Set W :=
    {z | ∀ Tz : HyperbolicLocalChart.LocalRealMobiusTransitionData U V (z : X),
      realMobiusProjection Tz.representative =
        realMobiusProjection Tx.representative}
  have hEopen : IsOpen E := by
    rw [isOpen_iff_forall_mem_open]
    intro z hzE
    rcases hWexists z.property with ⟨Tz⟩
    let O : Set W := {w | (w : X) ∈ Tz.neighborhood}
    have hOopen : IsOpen O :=
      Tz.isOpen_neighborhood.preimage continuous_subtype_val
    have hzO : z ∈ O := Tz.mem_neighborhood
    refine ⟨O, ?_, hOopen, hzO⟩
    intro w hwO Tw
    have hTw :
        realMobiusProjection Tw.representative =
          realMobiusProjection
            (localRealMobiusTransitionData_recenter Tz hwO).representative :=
      localRealMobiusTransitionData_projection_eq Tw
        (localRealMobiusTransitionData_recenter Tz hwO)
    exact hTw.trans (by simpa using hzE Tz)
  have hEcompl_open : IsOpen Eᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro z hzNotE
    rcases hWexists z.property with ⟨Tz⟩
    have hzTz_ne :
        realMobiusProjection Tz.representative ≠
          realMobiusProjection Tx.representative := by
      intro h
      exact hzNotE (by
        intro Tz'
        exact (localRealMobiusTransitionData_projection_eq Tz' Tz).trans h)
    let O : Set W := {w | (w : X) ∈ Tz.neighborhood}
    have hOopen : IsOpen O :=
      Tz.isOpen_neighborhood.preimage continuous_subtype_val
    have hzO : z ∈ O := Tz.mem_neighborhood
    refine ⟨O, ?_, hOopen, hzO⟩
    intro w hwO hwE
    rcases hWexists w.property with ⟨Tw⟩
    have hTw_recenter :
        realMobiusProjection Tw.representative =
          realMobiusProjection
            (localRealMobiusTransitionData_recenter Tz hwO).representative :=
      localRealMobiusTransitionData_projection_eq Tw
        (localRealMobiusTransitionData_recenter Tz hwO)
    exact hzTz_ne ((hTw_recenter.symm).trans (hwE Tw))
  have hEclopen : IsClopen E := ⟨isOpen_compl_iff.mp hEcompl_open, hEopen⟩
  have hxE : (⟨x, hxW⟩ : W) ∈ E := by
    intro Tx'
    exact localRealMobiusTransitionData_projection_eq Tx' Tx
  haveI : PreconnectedSpace W :=
    Subtype.preconnectedSpace hWpre
  have hEuniv : E = Set.univ :=
    IsClopen.eq_univ hEclopen ⟨⟨x, hxW⟩, hxE⟩
  have hyE : (⟨y, hyW⟩ : W) ∈ E := by
    rw [hEuniv]
    exact Set.mem_univ _
  exact hyE Ty

/--
Along a path interval contained in a two-chart overlap, the PSL class of the
local real-Mobius transition between the two fixed charts is independent of
the chosen point of the interval.
-/
theorem localRealMobiusTransitionData_projection_eq_along_path_Icc
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {x₀ x : X} (p : Path x₀ x)
    {a b : unitInterval} (hab : a ≤ b)
    (hExists :
      ∀ t : unitInterval, t ∈ Set.Icc a b →
        Nonempty (HyperbolicLocalChart.LocalRealMobiusTransitionData U V (p t)))
    (Ta : HyperbolicLocalChart.LocalRealMobiusTransitionData U V (p a))
    (Tb : HyperbolicLocalChart.LocalRealMobiusTransitionData U V (p b)) :
    realMobiusProjection Tb.representative =
      realMobiusProjection Ta.representative := by
  let W : Set X := p '' Set.Icc a b
  have hWpre : IsPreconnected W :=
    isPreconnected_Icc.image p p.continuous.continuousOn
  have hWexists :
      ∀ ⦃y : X⦄, y ∈ W →
        Nonempty (HyperbolicLocalChart.LocalRealMobiusTransitionData U V y) := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact hExists t ht
  have haW : p a ∈ W := by
    exact ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  have hbW : p b ∈ W := by
    exact ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  exact
    localRealMobiusTransitionData_projection_eq_of_preconnected
      hWpre hWexists haW hbW Ta Tb

/--
The PSL class of an inverse local transition is the inverse PSL class of the
original transition.
-/
theorem localRealMobiusTransitionData_projection_eq_symm
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g} {x : X}
    (TUV : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (TVU : HyperbolicLocalChart.LocalRealMobiusTransitionData V U x) :
    realMobiusProjection TVU.representative =
      realMobiusProjection TUV.representative⁻¹ := by
  simpa using
    localRealMobiusTransitionData_projection_eq
      TVU (localRealMobiusTransitionData_symm TUV)

/--
%%handwave
name:
  Cocycle law for local projective transitions
statement:
  Suppose local branches $F_U,F_V,F_W$ near $x$ satisfy
  $F_V=A_{UV}\cdot F_U$, $F_W=A_{VW}\cdot F_V$, and
  $F_W=A_{UW}\cdot F_U$. Then in $\mathrm{PSL}_2(\mathbb R)$,
  $[A_{UW}]=[A_{VW}A_{UV}]$.
proof:
  [Any two local transitions between the same ordered pair of branches have the same projective class](lean:JJMath.localRealMobiusTransitionData_projection_eq). Apply this to the direct transition $A_{UW}$ and the composite transition $A_{VW}A_{UV}$.
-/
theorem localRealMobiusTransitionData_projection_eq_trans
    {g : HyperbolicMetric X}
    {U V W : HyperbolicLocalChart X g} {x : X}
    (TUV : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (TVW : HyperbolicLocalChart.LocalRealMobiusTransitionData V W x)
    (TUW : HyperbolicLocalChart.LocalRealMobiusTransitionData U W x) :
    realMobiusProjection TUW.representative =
      realMobiusProjection (TVW.representative * TUV.representative) := by
  simpa using
    localRealMobiusTransitionData_projection_eq
      TUW (localRealMobiusTransitionData_trans TUV TVW)

/--
Updating an accumulated branch by the direct transition `U → W` has the same
PSL class as updating through the two successive transitions `U → V → W`.

This is the algebraic cocycle used by zero-length center insertions in a
refined continuation chain.
-/
theorem localRealMobiusTransitionData_projection_handoff_cocycle
    {g : HyperbolicMetric X}
    {U V W : HyperbolicLocalChart X g} {x : X}
    (TUV : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (TVW : HyperbolicLocalChart.LocalRealMobiusTransitionData V W x)
    (TUW : HyperbolicLocalChart.LocalRealMobiusTransitionData U W x)
    (M : RealMobiusRepresentative) :
    realMobiusProjection (M * TUW.representative⁻¹) =
      realMobiusProjection ((M * TUV.representative⁻¹) *
        TVW.representative⁻¹) := by
  have hcomp :
      realMobiusProjection TUW.representative =
        realMobiusProjection (TVW.representative * TUV.representative) :=
    localRealMobiusTransitionData_projection_eq_trans TUV TVW TUW
  calc
    realMobiusProjection (M * TUW.representative⁻¹)
        = realMobiusProjection M *
            (realMobiusProjection TUW.representative)⁻¹ := by
          simp
    _ = realMobiusProjection M *
            (realMobiusProjection (TVW.representative *
              TUV.representative))⁻¹ := by
          rw [hcomp]
    _ = realMobiusProjection ((M * TUV.representative⁻¹) *
            TVW.representative⁻¹) := by
          simp [mul_assoc]

namespace PathLocalTransitionModelBasedWeakHandoffSkeleton

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

/--
At the initial point, converting the accumulated branch of a skeleton to any
fixed comparison chart agrees projectively with the direct basepoint
transition into that chart.
-/
theorem initialFixedChartAccumulatedProjection_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X)
    (T0 :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt 0))
        (localModels.chartAt c)
        x₀)
    (Tbase :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt x₀)
        (localModels.chartAt c)
        x₀) :
    realMobiusProjection
        (S.accumulatedMobiusAt 0 * T0.representative⁻¹) =
      realMobiusProjection Tbase.representative⁻¹ := by
  have hcocycle :
      realMobiusProjection Tbase.representative =
        realMobiusProjection
          (T0.representative * S.initialTransition.representative) :=
    localRealMobiusTransitionData_projection_eq_trans
      S.initialTransition T0 Tbase
  simp [S.accumulatedMobiusAt_zero, hcocycle]

/--
On one segment of a handoff skeleton, if a fixed comparison chart contains
the whole segment image, then the PSL class of the local transition from the
segment chart to the comparison chart is constant from the left endpoint to
the right endpoint.
-/
theorem segmentTransitionProjection_eq_along_fixedChart
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc_segment :
      ∀ t : unitInterval,
        (S.parameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ (S.parameterAt k.succ : ℝ) →
          p t ∈ (localModels.chartAt c).domain)
    (Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.castSucc)))
    (Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.succ))) :
    realMobiusProjection Tright.representative =
      realMobiusProjection Tleft.representative := by
  classical
  let a := S.parameterAt k.castSucc
  let b := S.parameterAt k.succ
  have hab : a ≤ b := by
    exact_mod_cast S.parameterAt_mono k
  have hExists :
      ∀ t : unitInterval, t ∈ Set.Icc a b →
        Nonempty
          (HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt (S.centerAt k.castSucc))
            (localModels.chartAt c)
            (p t)) := by
    intro t ht
    refine localModels.transition_localRealMobius
      (S.centerAt k.castSucc) c (p t) ?_
    have ht_left : (S.parameterAt k.castSucc : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast ht.1
    have ht_right : (t : ℝ) ≤ (S.parameterAt k.succ : ℝ) := by
      exact_mod_cast ht.2
    exact
      ⟨S.path_segment_mem_model_domain k t ht_left ht_right,
        hc_segment t ht_left ht_right⟩
  simpa [a, b] using
    localRealMobiusTransitionData_projection_eq_along_path_Icc
      p hab hExists Tleft Tright

/--
Crossing one skeleton segment preserves the accumulated PSL branch after
conversion to any fixed chart whose domain contains the whole segment image.

This is the algebraic handoff step behind same-path value propagation.
-/
theorem segmentFixedChartAccumulatedProjection_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc_segment :
      ∀ t : unitInterval,
        (S.parameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ (S.parameterAt k.succ : ℝ) →
          p t ∈ (localModels.chartAt c).domain)
    (Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.castSucc)))
    (TrightLeft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.succ)))
    (TrightNext :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.succ))
        (localModels.chartAt c)
        (p (S.parameterAt k.succ))) :
    realMobiusProjection
        (S.accumulatedMobiusAt k.succ * TrightNext.representative⁻¹) =
      realMobiusProjection
        (S.accumulatedMobiusAt k.castSucc * Tleft.representative⁻¹) := by
  have hconst :
      realMobiusProjection TrightLeft.representative =
        realMobiusProjection Tleft.representative :=
    S.segmentTransitionProjection_eq_along_fixedChart
      k c hc_segment Tleft TrightLeft
  have hcocycle :
      realMobiusProjection TrightLeft.representative =
        realMobiusProjection
          (TrightNext.representative * (S.transitionAt k).representative) :=
    localRealMobiusTransitionData_projection_eq_trans
      (S.transitionAt k) TrightNext TrightLeft
  rw [S.accumulatedMobiusAt_succ k]
  calc
    realMobiusProjection
        ((S.accumulatedMobiusAt k.castSucc *
            (S.transitionAt k).representative⁻¹) *
          TrightNext.representative⁻¹)
        =
      realMobiusProjection (S.accumulatedMobiusAt k.castSucc) *
        (realMobiusProjection
          (TrightNext.representative * (S.transitionAt k).representative))⁻¹ := by
          simp [mul_assoc]
    _ =
      realMobiusProjection (S.accumulatedMobiusAt k.castSucc) *
        (realMobiusProjection TrightLeft.representative)⁻¹ := by
          rw [← hcocycle]
    _ =
      realMobiusProjection (S.accumulatedMobiusAt k.castSucc) *
        (realMobiusProjection Tleft.representative)⁻¹ := by
          rw [hconst]
    _ =
      realMobiusProjection
        (S.accumulatedMobiusAt k.castSucc * Tleft.representative⁻¹) := by
          simp

/--
If one fixed comparison chart contains the whole path image, then the
accumulated branch of a skeleton, converted to that chart at any sampled
vertex, has the same PSL class as the direct basepoint transition into the
fixed chart.
-/
theorem accumulatedProjection_eq_fixedChart
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X)
    (hc_path : ∀ t : unitInterval, p t ∈ (localModels.chartAt c).domain)
    (Tbase :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt x₀)
        (localModels.chartAt c)
        x₀)
    (Tvertex :
      ∀ i : Fin (S.length + 1),
        HyperbolicLocalChart.LocalRealMobiusTransitionData
          (localModels.chartAt (S.centerAt i))
          (localModels.chartAt c)
          (p (S.parameterAt i))) :
    ∀ n : ℕ, ∀ hn : n ≤ S.length,
      realMobiusProjection
          (S.accumulatedMobiusAt
              ⟨n, Nat.lt_succ_of_le hn⟩ *
            (Tvertex ⟨n, Nat.lt_succ_of_le hn⟩).representative⁻¹) =
        realMobiusProjection Tbase.representative⁻¹ := by
  intro n hn
  induction n with
  | zero =>
      have h0point :
          x₀ = p (S.parameterAt (0 : Fin (S.length + 1))) := by
        simp [S.parameterAt_zero, p.source]
      let T0 :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt (S.centerAt 0))
            (localModels.chartAt c)
            x₀ :=
        localRealMobiusTransitionData_congr rfl rfl h0point (Tvertex 0)
      have h :=
        S.initialFixedChartAccumulatedProjection_eq c T0 Tbase
      simpa [T0] using h
  | succ n ih =>
      have hnlt : n < S.length := Nat.succ_le_iff.mp hn
      let k : Fin S.length := ⟨n, hnlt⟩
      let iPrev : Fin (S.length + 1) :=
        ⟨n, Nat.lt_succ_of_lt hnlt⟩
      let iCur : Fin (S.length + 1) :=
        ⟨n + 1, Nat.lt_succ_of_le hn⟩
      have hprev_eq : iPrev = k.castSucc := by
        ext
        rfl
      have hcur_eq : iCur = k.succ := by
        ext
        rfl
      let TrightLeft :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt (S.centerAt k.castSucc))
            (localModels.chartAt c)
            (p (S.parameterAt k.succ)) :=
        Classical.choice
          (localModels.transition_localRealMobius
            (S.centerAt k.castSucc) c
            (p (S.parameterAt k.succ))
            ⟨S.path_segment_mem_model_domain k (S.parameterAt k.succ)
                (S.parameterAt_mono k) le_rfl,
              hc_path (S.parameterAt k.succ)⟩)
      have hstep :
          realMobiusProjection
              (S.accumulatedMobiusAt k.succ *
                (Tvertex k.succ).representative⁻¹) =
            realMobiusProjection
              (S.accumulatedMobiusAt k.castSucc *
                (Tvertex k.castSucc).representative⁻¹) :=
        S.segmentFixedChartAccumulatedProjection_eq
          k c
          (fun t _ _ => hc_path t)
          (Tvertex k.castSucc)
          TrightLeft
          (Tvertex k.succ)
      have hprev :
          realMobiusProjection
              (S.accumulatedMobiusAt k.castSucc *
                (Tvertex k.castSucc).representative⁻¹) =
            realMobiusProjection Tbase.representative⁻¹ := by
        change
          realMobiusProjection
              (S.accumulatedMobiusAt
                  ⟨n, Nat.lt_succ_of_le (Nat.le_of_lt hnlt)⟩ *
                (Tvertex
                  ⟨n, Nat.lt_succ_of_le (Nat.le_of_lt hnlt)⟩).representative⁻¹) =
            realMobiusProjection Tbase.representative⁻¹
        exact ih (Nat.le_of_lt hnlt)
      change
        realMobiusProjection
            (S.accumulatedMobiusAt k.succ *
              (Tvertex k.succ).representative⁻¹) =
          realMobiusProjection Tbase.representative⁻¹
      exact hstep.trans hprev

/--
If one fixed comparison chart contains the whole path image, then every
handoff skeleton along the path has the terminal value obtained by continuing
the base branch directly in that fixed chart.
-/
theorem terminalValue_eq_fixedChartBranch
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X)
    (hc_path : ∀ t : unitInterval, p t ∈ (localModels.chartAt c).domain)
    (Tbase :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt x₀)
        (localModels.chartAt c)
        x₀) :
    S.terminalValue =
      realMobiusRepresentativeAction Tbase.representative⁻¹
        ((localModels.chartAt c).toUpperHalfPlane x) := by
  classical
  let Tvertex :
      ∀ i : Fin (S.length + 1),
        HyperbolicLocalChart.LocalRealMobiusTransitionData
          (localModels.chartAt (S.centerAt i))
          (localModels.chartAt c)
          (p (S.parameterAt i)) :=
    fun i =>
      Classical.choice
        (localModels.transition_localRealMobius
          (S.centerAt i) c (p (S.parameterAt i))
          ⟨S.sample_mem_model_domain i, hc_path (S.parameterAt i)⟩)
  have hproj :
      realMobiusProjection
          (S.terminalMobius *
            (Tvertex (Fin.last S.length)).representative⁻¹) =
        realMobiusProjection Tbase.representative⁻¹ := by
    simpa [terminalMobius] using
      S.accumulatedProjection_eq_fixedChart
        c hc_path Tbase Tvertex S.length le_rfl
  have hconvert :
      realMobiusRepresentativeAction
          (S.terminalMobius *
            (Tvertex (Fin.last S.length)).representative⁻¹)
          ((localModels.chartAt c).toUpperHalfPlane x) =
        S.terminalValue := by
    have hxparam : p (S.parameterAt (Fin.last S.length)) = x := by
      simp [S.parameterAt_last, p.target]
    have h :=
      localRealMobiusTransitionData_accumulated_handoff
        (Tvertex (Fin.last S.length))
        (Tvertex (Fin.last S.length)).mem_neighborhood
        S.terminalMobius
    simpa [terminalValue, terminalCenter, hxparam] using h
  exact
    hconvert.symm.trans
      (realMobiusRepresentativeAction_eq_of_projection_eq hproj
        ((localModels.chartAt c).toUpperHalfPlane x))

/--
If one fixed comparison chart contains the whole path image, then terminal
values are independent of the handoff skeleton chosen along that path.
-/
theorem terminalValue_eq_of_common_fixedChart
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X)
    (hc_path : ∀ t : unitInterval, p t ∈ (localModels.chartAt c).domain)
    (Tbase :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt x₀)
        (localModels.chartAt c)
        x₀) :
    S.terminalValue = T.terminalValue := by
  calc
    S.terminalValue =
        realMobiusRepresentativeAction Tbase.representative⁻¹
          ((localModels.chartAt c).toUpperHalfPlane x) := by
          exact S.terminalValue_eq_fixedChartBranch c hc_path Tbase
    _ = T.terminalValue := by
          exact (T.terminalValue_eq_fixedChartBranch c hc_path Tbase).symm

/--
If two based handoff skeletons over the same path use the same subdivision
parameters, then their accumulated branches agree projectively after
converting the chart of `T` at each aligned vertex to the chart of `S` at that
same vertex.

This is the local algebraic comparison behind same-path mutual refinements.
The only geometric input is ordinary local-transition data between the two
chosen charts at each shared vertex; constancy of those transition classes
along each common segment is supplied by the componentwise transition atlas.
-/
theorem alignedAccumulatedProjection_eq
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (_hLength : S.length = T.length)
    (hParam :
      ∀ n (hnS : n ≤ S.length) (hnT : n ≤ T.length),
        S.parameterAt ⟨n, Nat.lt_succ_of_le hnS⟩ =
          T.parameterAt ⟨n, Nat.lt_succ_of_le hnT⟩)
    (Avertex :
      ∀ n (hnS : n ≤ S.length) (hnT : n ≤ T.length),
        HyperbolicLocalChart.LocalRealMobiusTransitionData
          (localModels.chartAt
            (S.centerAt ⟨n, Nat.lt_succ_of_le hnS⟩))
          (localModels.chartAt
            (T.centerAt ⟨n, Nat.lt_succ_of_le hnT⟩))
          (p (S.parameterAt ⟨n, Nat.lt_succ_of_le hnS⟩))) :
    ∀ n (hnS : n ≤ S.length) (hnT : n ≤ T.length),
      realMobiusProjection
          (T.accumulatedMobiusAt ⟨n, Nat.lt_succ_of_le hnT⟩ *
            (Avertex n hnS hnT).representative) =
        realMobiusProjection
          (S.accumulatedMobiusAt ⟨n, Nat.lt_succ_of_le hnS⟩) := by
  classical
  intro n hnS hnT
  induction n with
  | zero =>
      let A0 := Avertex 0 (Nat.zero_le _) (Nat.zero_le _)
      have h0point :
          x₀ =
            p (S.parameterAt
              (⟨0, Nat.lt_succ_of_le (Nat.zero_le S.length)⟩ :
                Fin (S.length + 1))) := by
        simp [S.parameterAt_zero, p.source]
      let A0x :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt
              (S.centerAt
                (⟨0, Nat.lt_succ_of_le (Nat.zero_le S.length)⟩ :
                  Fin (S.length + 1))))
            (localModels.chartAt
              (T.centerAt
                (⟨0, Nat.lt_succ_of_le (Nat.zero_le T.length)⟩ :
                  Fin (T.length + 1))))
            x₀ :=
        localRealMobiusTransitionData_congr rfl rfl h0point A0
      have hcomp :
          realMobiusProjection T.initialTransition.representative =
            realMobiusProjection
              (A0.representative * S.initialTransition.representative) := by
        simpa [A0, A0x] using
          localRealMobiusTransitionData_projection_eq_trans
            S.initialTransition A0x T.initialTransition
      calc
        realMobiusProjection
            (T.accumulatedMobiusAt
                (⟨0, Nat.lt_succ_of_le hnT⟩ : Fin (T.length + 1)) *
              (Avertex 0 hnS hnT).representative)
            =
          realMobiusProjection T.initialTransition.representative⁻¹ *
            realMobiusProjection A0.representative := by
              simp [A0]
        _ =
          (realMobiusProjection
              (A0.representative * S.initialTransition.representative))⁻¹ *
            realMobiusProjection A0.representative := by
              have hcompInv :
                  realMobiusProjection T.initialTransition.representative⁻¹ =
                    (realMobiusProjection
                      (A0.representative *
                        S.initialTransition.representative))⁻¹ := by
                simpa using congrArg Inv.inv hcomp
              rw [hcompInv]
        _ =
          realMobiusProjection S.initialTransition.representative⁻¹ := by
              simp [mul_assoc]
        _ =
          realMobiusProjection
            (S.accumulatedMobiusAt
              (⟨0, Nat.lt_succ_of_le hnS⟩ : Fin (S.length + 1))) := by
              simp
  | succ n ih =>
      have hnSlt : n < S.length := Nat.succ_le_iff.mp hnS
      have hnTlt : n < T.length := Nat.succ_le_iff.mp hnT
      let kS : Fin S.length := ⟨n, hnSlt⟩
      let kT : Fin T.length := ⟨n, hnTlt⟩
      have hnSprev : n ≤ S.length := Nat.le_of_lt hnSlt
      have hnTprev : n ≤ T.length := Nat.le_of_lt hnTlt
      let Aleft := Avertex n hnSprev hnTprev
      let Anext := Avertex (n + 1) hnS hnT
      have hleftParamR :
          (T.parameterAt kT.castSucc : ℝ) =
            (S.parameterAt kS.castSucc : ℝ) := by
        simpa [kS, kT] using
          congrArg (fun u : unitInterval => (u : ℝ))
            (hParam n hnSprev hnTprev).symm
      have hrightParam :
          S.parameterAt kS.succ = T.parameterAt kT.succ := by
        simpa [kS, kT] using hParam (n + 1) hnS hnT
      have hrightParamR :
          (T.parameterAt kT.succ : ℝ) =
            (S.parameterAt kS.succ : ℝ) := by
        exact congrArg (fun u : unitInterval => (u : ℝ)) hrightParam.symm
      have hc_segment :
          ∀ t : unitInterval,
            (S.parameterAt kS.castSucc : ℝ) ≤ (t : ℝ) →
            (t : ℝ) ≤ (S.parameterAt kS.succ : ℝ) →
              p t ∈
                (localModels.chartAt (T.centerAt kT.castSucc)).domain := by
        intro t ht_left ht_right
        have ht_leftT : (T.parameterAt kT.castSucc : ℝ) ≤ (t : ℝ) := by
          simpa [hleftParamR] using ht_left
        have ht_rightT : (t : ℝ) ≤ (T.parameterAt kT.succ : ℝ) := by
          simpa [hrightParamR] using ht_right
        exact T.path_segment_mem_model_domain kT t ht_leftT ht_rightT
      let ArightLeft :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt (S.centerAt kS.castSucc))
            (localModels.chartAt (T.centerAt kT.castSucc))
            (p (S.parameterAt kS.succ)) :=
        Classical.choice
          (localModels.transition_localRealMobius
            (S.centerAt kS.castSucc) (T.centerAt kT.castSucc)
            (p (S.parameterAt kS.succ))
            ⟨S.path_segment_mem_model_domain kS (S.parameterAt kS.succ)
                (S.parameterAt_mono kS) le_rfl,
              hc_segment (S.parameterAt kS.succ)
                (S.parameterAt_mono kS) le_rfl⟩)
      let Bnext :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt (T.centerAt kT.castSucc))
            (localModels.chartAt (T.centerAt kT.succ))
            (p (S.parameterAt kS.succ)) :=
        localRealMobiusTransitionData_congr rfl rfl
          (congrArg p hrightParam)
          (T.transitionAt kT)
      have hconst :
          realMobiusProjection ArightLeft.representative =
            realMobiusProjection Aleft.representative := by
        simpa [Aleft, ArightLeft, kS, kT] using
          S.segmentTransitionProjection_eq_along_fixedChart
            kS (T.centerAt kT.castSucc) hc_segment Aleft ArightLeft
      have hcocycle :
          realMobiusProjection
              (Anext.representative * (S.transitionAt kS).representative) =
            realMobiusProjection
              (Bnext.representative * ArightLeft.representative) := by
        have h :=
          localRealMobiusTransitionData_projection_eq
            (localRealMobiusTransitionData_trans (S.transitionAt kS) Anext)
            (localRealMobiusTransitionData_trans ArightLeft Bnext)
        simpa [localRealMobiusTransitionData_trans, Anext, ArightLeft,
          Bnext, kS, kT] using h
      have hsolve :
          realMobiusProjection
              (Bnext.representative⁻¹ * Anext.representative) =
            realMobiusProjection
              (ArightLeft.representative *
                (S.transitionAt kS).representative⁻¹) := by
        have hcocycle' :
            realMobiusProjection Anext.representative *
                realMobiusProjection (S.transitionAt kS).representative =
              realMobiusProjection Bnext.representative *
                realMobiusProjection ArightLeft.representative := by
          simpa using hcocycle
        calc
          realMobiusProjection
              (Bnext.representative⁻¹ * Anext.representative)
              =
            (realMobiusProjection Bnext.representative)⁻¹ *
              realMobiusProjection Anext.representative := by
                simp
          _ =
            (realMobiusProjection Bnext.representative)⁻¹ *
              (realMobiusProjection Anext.representative *
                realMobiusProjection (S.transitionAt kS).representative) *
              (realMobiusProjection (S.transitionAt kS).representative)⁻¹ := by
                simp [mul_assoc]
          _ =
            (realMobiusProjection Bnext.representative)⁻¹ *
              (realMobiusProjection Bnext.representative *
                realMobiusProjection ArightLeft.representative) *
              (realMobiusProjection (S.transitionAt kS).representative)⁻¹ := by
                rw [hcocycle']
          _ =
            realMobiusProjection
                (ArightLeft.representative *
                  (S.transitionAt kS).representative⁻¹) := by
                  simp
      have hprev :
          realMobiusProjection
              (T.accumulatedMobiusAt kT.castSucc *
                Aleft.representative) =
            realMobiusProjection (S.accumulatedMobiusAt kS.castSucc) := by
        simpa [Aleft, kS, kT] using ih hnSprev hnTprev
      have hTsucc :
          T.accumulatedMobiusAt
              (⟨n + 1, Nat.lt_succ_of_le hnT⟩ :
                Fin (T.length + 1)) =
            T.accumulatedMobiusAt kT.castSucc *
              Bnext.representative⁻¹ := by
        change T.accumulatedMobiusNat (n + 1) =
          T.accumulatedMobiusNat n * Bnext.representative⁻¹
        rw [T.accumulatedMobiusNat_succ_of_lt hnTlt]
        simp [Bnext, kT]
      have hSsucc :
          S.accumulatedMobiusAt
              (⟨n + 1, Nat.lt_succ_of_le hnS⟩ :
                Fin (S.length + 1)) =
            S.accumulatedMobiusAt kS.castSucc *
              (S.transitionAt kS).representative⁻¹ := by
        change S.accumulatedMobiusNat (n + 1) =
          S.accumulatedMobiusNat n *
            (S.transitionAt kS).representative⁻¹
        rw [S.accumulatedMobiusNat_succ_of_lt hnSlt]
      calc
        realMobiusProjection
            (T.accumulatedMobiusAt
                (⟨n + 1, Nat.lt_succ_of_le hnT⟩ :
                  Fin (T.length + 1)) *
              (Avertex (n + 1) hnS hnT).representative)
            =
          realMobiusProjection
            ((T.accumulatedMobiusAt kT.castSucc *
                Bnext.representative⁻¹) *
              Anext.representative) := by
              rw [hTsucc]
        _ =
          realMobiusProjection (T.accumulatedMobiusAt kT.castSucc) *
            realMobiusProjection
              (Bnext.representative⁻¹ * Anext.representative) := by
              simp [mul_assoc]
        _ =
          realMobiusProjection (T.accumulatedMobiusAt kT.castSucc) *
            realMobiusProjection
              (ArightLeft.representative *
                (S.transitionAt kS).representative⁻¹) := by
              rw [hsolve]
        _ =
          realMobiusProjection (T.accumulatedMobiusAt kT.castSucc) *
            (realMobiusProjection Aleft.representative *
              realMobiusProjection (S.transitionAt kS).representative⁻¹) := by
              simp [hconst]
        _ =
          realMobiusProjection (S.accumulatedMobiusAt kS.castSucc) *
            realMobiusProjection (S.transitionAt kS).representative⁻¹ := by
              calc
                realMobiusProjection (T.accumulatedMobiusAt kT.castSucc) *
                    (realMobiusProjection Aleft.representative *
                      realMobiusProjection
                        (S.transitionAt kS).representative⁻¹)
                    =
                  realMobiusProjection
                      (T.accumulatedMobiusAt kT.castSucc *
                        Aleft.representative) *
                    realMobiusProjection
                      (S.transitionAt kS).representative⁻¹ := by
                      simp [mul_assoc]
                _ =
                  realMobiusProjection (S.accumulatedMobiusAt kS.castSucc) *
                    realMobiusProjection
                      (S.transitionAt kS).representative⁻¹ := by
                      rw [hprev]
        _ =
          realMobiusProjection
            (S.accumulatedMobiusAt
              (⟨n + 1, Nat.lt_succ_of_le hnS⟩ :
                Fin (S.length + 1))) := by
              rw [hSsucc]
              simp [kS]

/--
Aligned based handoff skeletons over the same path have the same terminal
value.  The terminal chart change is the aligned transition at the final
vertex, and the accumulated-projective comparison above supplies the branch
identity.
-/
theorem terminalValue_eq_of_alignedSubdivision
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (hLength : S.length = T.length)
    (hParam :
      ∀ n (hnS : n ≤ S.length) (hnT : n ≤ T.length),
        S.parameterAt ⟨n, Nat.lt_succ_of_le hnS⟩ =
          T.parameterAt ⟨n, Nat.lt_succ_of_le hnT⟩)
    (Avertex :
      ∀ n (hnS : n ≤ S.length) (hnT : n ≤ T.length),
        HyperbolicLocalChart.LocalRealMobiusTransitionData
          (localModels.chartAt
            (S.centerAt ⟨n, Nat.lt_succ_of_le hnS⟩))
          (localModels.chartAt
            (T.centerAt ⟨n, Nat.lt_succ_of_le hnT⟩))
          (p (S.parameterAt ⟨n, Nat.lt_succ_of_le hnS⟩))) :
    S.terminalValue = T.terminalValue := by
  classical
  have hlastT : S.length ≤ T.length := by
    omega
  let AtermAtParam := Avertex S.length le_rfl hlastT
  have hxpoint :
      x =
        p (S.parameterAt
          (⟨S.length, Nat.lt_succ_self S.length⟩ :
            Fin (S.length + 1))) := by
    change x = p (S.parameterAt (Fin.last S.length))
    rw [S.parameterAt_last]
    exact p.target.symm
  have hidxT :
      (⟨S.length, Nat.lt_succ_of_le hlastT⟩ :
        Fin (T.length + 1)) = Fin.last T.length := by
    ext
    exact hLength
  let Aterm :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt T.terminalCenter)
        x :=
    localRealMobiusTransitionData_congr rfl
      (by
        congr 1
        simp [terminalCenter, hidxT])
      hxpoint
      AtermAtParam
  have hproj :
      realMobiusProjection (T.terminalMobius * Aterm.representative) =
        realMobiusProjection S.terminalMobius := by
    simpa [terminalMobius, terminalCenter, Aterm, AtermAtParam, hidxT] using
      S.alignedAccumulatedProjection_eq T hLength hParam Avertex
        S.length le_rfl hlastT
  exact
    (S.terminalValue_eq_of_terminalTransitionDataProjection_eq
      T Aterm hproj).symm

/--
The endpoint chart-insertion terminal Mobius PSL class is preserved for actual
local-transition witnesses.  The only algebraic input is the PSL cocycle for
the two inserted handoffs.
-/
theorem segmentEndpointChartInsertSkeleton_terminalMobius_projection_eq_of_localTransitions
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc :
      p (S.parameterAt k.succ) ∈ (localModels.chartAt c).domain)
    (Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.succ)))
    (Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt c)
        (localModels.chartAt (S.centerAt k.succ))
        (p (S.parameterAt k.succ))) :
    realMobiusProjection
        (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).terminalMobius =
      realMobiusProjection S.terminalMobius :=
  S.segmentEndpointChartInsertSkeleton_terminalMobius_projection_eq
    k c hc Tleft Tright
    (localRealMobiusTransitionData_projection_eq_trans
      Tleft Tright (S.transitionAt k))

/--
The endpoint chart-insertion terminal branch formula is preserved for actual
local-transition witnesses.
-/
theorem segmentEndpointChartInsertSkeleton_terminalFormulaAt_eq_of_localTransitions
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc :
      p (S.parameterAt k.succ) ∈ (localModels.chartAt c).domain)
    (Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.succ)))
    (Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt c)
        (localModels.chartAt (S.centerAt k.succ))
        (p (S.parameterAt k.succ)))
    (z : X) :
    (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).terminalFormulaAt z =
      S.terminalFormulaAt z :=
  S.segmentEndpointChartInsertSkeleton_terminalFormulaAt_eq
    k c hc Tleft Tright
    (localRealMobiusTransitionData_projection_eq_trans
      Tleft Tright (S.transitionAt k))
    z

/--
The endpoint chart-insertion terminal value is preserved for actual
local-transition witnesses.
-/
theorem segmentEndpointChartInsertSkeleton_terminalValue_eq_of_localTransitions
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc :
      p (S.parameterAt k.succ) ∈ (localModels.chartAt c).domain)
    (Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.succ)))
    (Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt c)
        (localModels.chartAt (S.centerAt k.succ))
        (p (S.parameterAt k.succ))) :
    (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).terminalValue =
      S.terminalValue :=
  S.segmentEndpointChartInsertSkeleton_terminalValue_eq
    k c hc Tleft Tright
    (localRealMobiusTransitionData_projection_eq_trans
      Tleft Tright (S.transitionAt k))

end PathLocalTransitionModelBasedWeakHandoffSkeleton

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The terminal value forced by canonical-terminal-sheet agreement data. -/
def terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  (C.basedWeakHandoffAlong p).terminalValue

@[simp]
theorem terminalValue_eq_basedWeakHandoff_terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValue p = (C.basedWeakHandoffAlong p).terminalValue :=
  rfl

/--
%%handwave
name:
  Homotopy invariance of the continued value
statement:
  Suppose a coherent family of continuation chains has terminal formulas
  agreeing on every canonical terminal sheet. If $p,q:[0,1]\to X$ have the
  same endpoints and are homotopic relative to those endpoints, then
  continuation of the normalized local branch along $p$ and along $q$ gives
  the same value at their common endpoint.
proof:
  The paths determine the same point of the path-homotopy cover. Terminal-sheet
  agreement evaluates both continuations by the same local branch formula on
  a neighborhood of that point.
-/
theorem terminalValue_homotopic
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} {p q : Path x₀ x} (hpq : Path.Homotopic p q) :
    (C.basedWeakHandoffAlong p).terminalValue =
      (C.basedWeakHandoffAlong q).terminalValue := by
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong q
  have hST : S.terminalCoverPoint = T.terminalCoverPoint :=
    S.terminalCoverPoint_eq_of_homotopic T hpq
  have hyS : T.terminalCoverPoint ∈ S.terminalSheet := by
    simpa [hST] using S.terminalCoverPoint_mem_terminalSheet
  have hclass :
      Path.Homotopic.Quotient.mk q =
        PathHomotopyUniversalCover.pathClass T.terminalCoverPoint := by
    rfl
  have h :=
    C.terminalValue_eq_on_terminalSheet p T.terminalCoverPoint q hyS hclass
  simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalValue,
    S, T] using h.symm

/--
Canonical-terminal-sheet agreement data fill the value-continuation record;
homotopy descent is derived from terminal-sheet agreement.
-/
noncomputable def toCanonicalSheetAnalyticContinuationValueData
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
      x₀ g localModels where
  basedWeakHandoffAlong := C.basedWeakHandoffAlong
  terminalValue_homotopic := by
    intro x p q hpq
    exact C.terminalValue_homotopic hpq
  terminalValue_eq_on_terminalSheet := C.terminalValue_eq_on_terminalSheet

/--
The single-valued upstairs map defined by choosing Lean's representative of
the stored path class.
-/
noncomputable def dev
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  fun y =>
    (C.basedWeakHandoffAlong
      (Quot.out (PathHomotopyUniversalCover.pathClass y))).terminalValue

/-- At a represented path-class point, the constructed upstairs map has the terminal value. -/
theorem dev_terminalCoverPoint
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.dev (C.basedWeakHandoffAlong p).terminalCoverPoint =
      (C.basedWeakHandoffAlong p).terminalValue := by
  exact C.terminalValue_homotopic
    (PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData.out_homotopic_mk p)

/--
At an explicitly represented point of the canonical cover, the constructed
upstairs map has the terminal value of the representing path.
-/
theorem dev_mk
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.dev (⟨x, Path.Homotopic.Quotient.mk p⟩ :
        PathHomotopyUniversalCover X x₀) =
      C.terminalValue p := by
  simpa [dev, terminalValue] using
    C.terminalValue_homotopic
      (PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData.out_homotopic_mk p)

/--
The constructed upstairs map agrees with the terminal-sheet formula on every
canonical terminal sheet.
-/
theorem dev_eq_on_terminalSheet
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
    (hy' : y' ∈ (C.basedWeakHandoffAlong p).terminalSheet) :
    C.dev y' =
      realMobiusRepresentativeAction
        ((C.basedWeakHandoffAlong p).terminalMobius)
        ((localModels.chartAt
            ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y')) := by
  let p' : Path x₀ (PathHomotopyUniversalCover.endpoint y') :=
    Quot.out (PathHomotopyUniversalCover.pathClass y')
  have hclass :
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' := by
    exact Quot.out_eq (PathHomotopyUniversalCover.pathClass y')
  have h := C.terminalValue_eq_on_terminalSheet p y' p' hy' hclass
  simpa [dev, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalValue,
    p'] using h

/--
%%handwave
name:
  Deck equivariance from monodromy
statement:
  Let $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ be the monodromy of
  analytic continuation. If continuation along a loop representing
  $\gamma^{-1}$ followed by a path $p$ changes the terminal value by
  $\rho(\gamma)$, then
  $\operatorname{dev}(\gamma\cdot y)=\rho(\gamma)\cdot
  \operatorname{dev}(y)$ for every $y\in\widetilde X_{x_0}$.
proof:
  Represent $y$ by $p$. The deck action replaces $[p]$ by the class of the
  concatenation of a loop representing $\gamma^{-1}$ with $p$, so the claimed
  identity is precisely the path-level monodromy formula.
-/
theorem dev_deckAction_eq_of_terminal_path_equivariant
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (holonomy : RealHolonomyRepresentation X x₀)
    (hpath :
      ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
        {x : X} (p : Path x₀ x),
        Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
        C.terminalValue (loop.trans p) =
          holonomy.upperHalfPlaneAction γ (C.terminalValue p))
    (γ : FundamentalGroup X x₀)
    (y : (canonicalContinuationCover x₀).total) :
    C.dev ((canonicalContinuationCover x₀).deckAction γ y) =
      holonomy.upperHalfPlaneAction γ (C.dev y) := by
  rcases y with ⟨x, q⟩
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      induction hloop : FundamentalGroup.toPath γ⁻¹ using
        Path.Homotopic.Quotient.ind with
      | mk loop =>
          dsimp [canonicalContinuationCover, SimplyConnectedCover.deckAction,
            PathHomotopyUniversalCover.deckHomeomorphism_apply,
            PathHomotopyUniversalCover.deckAction,
            PathHomotopyUniversalCover.endpoint,
            PathHomotopyUniversalCover.pathClass]
          change
            C.dev
                (⟨x,
                  Path.Homotopic.Quotient.trans
                    (FundamentalGroup.toPath γ⁻¹)
                    (Path.Homotopic.Quotient.mk p)⟩ :
                  PathHomotopyUniversalCover X x₀) =
              holonomy.upperHalfPlaneAction γ
                (C.dev
                  (⟨x, Path.Homotopic.Quotient.mk p⟩ :
                    PathHomotopyUniversalCover X x₀))
          rw [hloop, ← Path.Homotopic.Quotient.mk_trans]
          rw [C.dev_mk (loop.trans p), C.dev_mk p]
          exact hpath γ loop p hloop.symm

/--
The local transition between the terminal chart of `p` and the terminal chart
of `loop.trans p` at their common endpoint.  This data exists automatically
from the componentwise local-transition atlas.
-/
noncomputable def terminalTransitionData
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (_hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData
      (localModels.chartAt ((C.basedWeakHandoffAlong p).terminalCenter))
      (localModels.chartAt
        ((C.basedWeakHandoffAlong (loop.trans p)).terminalCenter))
      x := by
  classical
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (loop.trans p)
  have hS :
      x ∈ (localModels.chartAt S.terminalCenter).domain := by
    simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCenter]
      using S.terminal_endpoint_mem_domain
  have hT :
      x ∈ (localModels.chartAt T.terminalCenter).domain := by
    simpa [T, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCenter]
      using T.terminal_endpoint_mem_domain
  exact Classical.choice
    (localModels.transition_localRealMobius S.terminalCenter T.terminalCenter
      x ⟨hS, hT⟩)

/--
The automatically selected terminal chart-transition representative.
-/
noncomputable def terminalTransitionRepresentative
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    RealMobiusRepresentative :=
  (C.terminalTransitionData γ loop p hloop).representative

/--
The automatically selected terminal transition identifies the terminal charts
at the endpoint.
-/
theorem terminalTransitionAtEndpoint
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    (localModels.chartAt
        ((C.basedWeakHandoffAlong (loop.trans p)).terminalCenter)).toUpperHalfPlane x =
      realMobiusRepresentativeAction
        (C.terminalTransitionRepresentative γ loop p hloop)
        ((localModels.chartAt
            ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane x) := by
  exact
    (C.terminalTransitionData γ loop p hloop).transition_eq x
      (C.terminalTransitionData γ loop p hloop).mem_neighborhood

/--
The local transition between the terminal charts of two based weak handoff
skeletons with the same endpoint.

This is the path-independent terminal-chart comparison primitive used in the
monodromy cocycle: loop-prepending is one important source of such pairs, but
the PSL composition law is really a statement about three terminal charts at a
common surface point.
-/
noncomputable def terminalTransitionDataBetween
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q : Path x₀ x) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData
      (localModels.chartAt ((C.basedWeakHandoffAlong p).terminalCenter))
      (localModels.chartAt ((C.basedWeakHandoffAlong q).terminalCenter))
      x := by
  classical
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong q
  have hS :
      x ∈ (localModels.chartAt S.terminalCenter).domain := by
    simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCenter]
      using S.terminal_endpoint_mem_domain
  have hT :
      x ∈ (localModels.chartAt T.terminalCenter).domain := by
    simpa [T, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCenter]
      using T.terminal_endpoint_mem_domain
  exact Classical.choice
    (localModels.transition_localRealMobius S.terminalCenter T.terminalCenter
      x ⟨hS, hT⟩)

/-- The automatically selected representative comparing two terminal charts. -/
noncomputable def terminalTransitionRepresentativeBetween
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q : Path x₀ x) :
    RealMobiusRepresentative :=
  (C.terminalTransitionDataBetween p q).representative

/--
The generic terminal transition identifies the two terminal charts at their
common endpoint.
-/
theorem terminalTransitionBetweenAtEndpoint
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q : Path x₀ x) :
    (localModels.chartAt
        ((C.basedWeakHandoffAlong q).terminalCenter)).toUpperHalfPlane x =
      realMobiusRepresentativeAction
        (C.terminalTransitionRepresentativeBetween p q)
        ((localModels.chartAt
            ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane x) := by
  exact
    (C.terminalTransitionDataBetween p q).transition_eq x
      (C.terminalTransitionDataBetween p q).mem_neighborhood

/--
The loop-prepending terminal transition and the generic terminal transition
from `p` to `loop.trans p` define the same PSL class.
-/
theorem terminalTransitionRepresentative_projection_eq_between
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    realMobiusProjection
        (C.terminalTransitionRepresentative γ loop p hloop) =
      realMobiusProjection
        (C.terminalTransitionRepresentativeBetween p (loop.trans p)) := by
  exact
    localRealMobiusTransitionData_projection_eq
      (C.terminalTransitionData γ loop p hloop)
      (C.terminalTransitionDataBetween p (loop.trans p))

/--
Automatic terminal-chart representatives compose correctly in PSL.

For three based paths with the same endpoint, the direct terminal transition
`p → r` has the same PSL class as the product of `p → q` followed by `q → r`.
-/
theorem terminalTransitionRepresentativeBetween_projection_trans
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q r : Path x₀ x) :
    realMobiusProjection
        (C.terminalTransitionRepresentativeBetween p r) =
      realMobiusProjection
        ((C.terminalTransitionRepresentativeBetween q r) *
          C.terminalTransitionRepresentativeBetween p q) := by
  exact
    localRealMobiusTransitionData_projection_eq_trans
      (C.terminalTransitionDataBetween p q)
      (C.terminalTransitionDataBetween q r)
      (C.terminalTransitionDataBetween p r)

/--
The terminal-chart cocycle remains true after postcomposition with a terminal
Mobius branch.

This is the algebraic identity needed when comparing a direct continuation
with a two-step continuation through an intermediate terminal sheet.
-/
theorem terminalTransitionRepresentativeBetween_adjusted_projection_trans
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q r : Path x₀ x) (M : RealMobiusRepresentative) :
    realMobiusProjection
        (M * C.terminalTransitionRepresentativeBetween p r) =
      realMobiusProjection
        ((M * C.terminalTransitionRepresentativeBetween q r) *
          C.terminalTransitionRepresentativeBetween p q) := by
  have htrans :=
    C.terminalTransitionRepresentativeBetween_projection_trans p q r
  calc
    realMobiusProjection
        (M * C.terminalTransitionRepresentativeBetween p r)
        = realMobiusProjection M *
            realMobiusProjection
              (C.terminalTransitionRepresentativeBetween p r) := by
          simp
    _ = realMobiusProjection M *
            realMobiusProjection
              ((C.terminalTransitionRepresentativeBetween q r) *
                C.terminalTransitionRepresentativeBetween p q) := by
          rw [htrans]
    _ = realMobiusProjection
        ((M * C.terminalTransitionRepresentativeBetween q r) *
          C.terminalTransitionRepresentativeBetween p q) := by
          simp [mul_assoc]

/--
The source-coordinate set on which two homotopic terminal path formulae can be
compared after changing terminal charts from `p` to `q`.
-/
def terminalTransitionBetweenCoordinateAgreementSet
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q : Path x₀ x) : Set ℍ :=
  {z | ∃ y : PathHomotopyUniversalCover X x₀,
    y ∈ (C.basedWeakHandoffAlong p).terminalSheet ∧
    y ∈ (C.basedWeakHandoffAlong q).terminalSheet ∧
    PathHomotopyUniversalCover.endpoint y ∈
      (C.terminalTransitionDataBetween p q).neighborhood ∧
    z =
      (localModels.chartAt
          ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
        (PathHomotopyUniversalCover.endpoint y)}

/--
For endpoint-fixed homotopic paths, the generic terminal-chart comparison set
contains a nonempty open patch in the source terminal coordinate.
-/
theorem terminalTransitionBetweenCoordinateAgreementSet_containsNonemptyOpen_of_homotopic
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q : Path x₀ x) (hpq : Path.Homotopic p q) :
    ∃ u : Set ℍ,
      IsOpen u ∧ u.Nonempty ∧
        u ⊆ C.terminalTransitionBetweenCoordinateAgreementSet p q := by
  classical
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong q
  let τ := C.terminalTransitionDataBetween p q
  let U := localModels.chartAt S.terminalCenter
  let eSheet :=
    PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph
      (x₀ := x₀) S.terminalSheetChart
  let O : Set (PathHomotopyUniversalCover X x₀) :=
    (S.terminalSheet ∩ T.terminalSheet) ∩
      (PathHomotopyUniversalCover.endpoint (x₀ := x₀)) ⁻¹' τ.neighborhood
  have hEndpointOpen :
      IsOpen ((PathHomotopyUniversalCover.endpoint (x₀ := x₀)) ⁻¹' τ.neighborhood) := by
    simpa using
      PathHomotopyUniversalCover.isOpen_endpoint_preimage_of_isOpen
        (x₀ := x₀) τ.isOpen_neighborhood
  have hOopen : IsOpen O := by
    simpa [O] using
      (S.isOpen_terminalSheet.inter T.isOpen_terminalSheet).inter hEndpointOpen
  have hOsubSource : O ⊆ eSheet.source := by
    intro y hy
    simpa [eSheet, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using hy.1.1
  have hCoverPoint :
      S.terminalCoverPoint = T.terminalCoverPoint :=
    S.terminalCoverPoint_eq_of_homotopic T hpq
  have hOpoint : S.terminalCoverPoint ∈ O := by
    refine ⟨⟨S.terminalCoverPoint_mem_terminalSheet, ?_⟩, ?_⟩
    · simpa [S, T, hCoverPoint] using T.terminalCoverPoint_mem_terminalSheet
    · simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
        using τ.mem_neighborhood
  let W : Set X := eSheet '' O
  have hWopen : IsOpen W :=
    eSheet.isOpen_image_of_subset_source hOopen hOsubSource
  have hxW : x ∈ W := by
    refine ⟨S.terminalCoverPoint, hOpoint, ?_⟩
    simp [eSheet, PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
  have hxU : x ∈ U.domain := by
    simpa [U, S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
      using S.terminalCoverPoint_endpoint_mem_terminal_domain
  rcases
      HyperbolicLocalChart.exists_open_upperHalfPlane_subset_image_of_mem_nhds U hxU
        (hWopen.mem_nhds hxW) with
    ⟨u, huOpen, huMem, huSub⟩
  refine ⟨u, huOpen, ⟨U.toUpperHalfPlane x, huMem⟩, ?_⟩
  intro z hz
  rcases huSub hz with ⟨x', hx'WU, hx'z⟩
  rcases hx'WU with ⟨hx'W, hx'U⟩
  rcases hx'W with ⟨y, hyO, hyEndpoint⟩
  have hEndpoint : PathHomotopyUniversalCover.endpoint y = x' := by
    simpa [W, eSheet, PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph]
      using hyEndpoint
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · exact hyO.1.1
  · exact hyO.1.2
  · simpa [O, hEndpoint] using hyO.2
  · rw [← hx'z, hEndpoint]

/--
Endpoint-fixed homotopic paths have the same terminal Mobius PSL class after
transporting the terminal chart of `p` to the terminal chart of `q`.

This is the local monodromy uniqueness statement independent of loop
equivariance: two representatives of the same upstairs point compute the same
single-valued `dev` on a common terminal sheet patch, and PSL faithfulness on
that patch identifies the adjusted terminal class.
-/
theorem terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q : Path x₀ x) (hpq : Path.Homotopic p q) :
    realMobiusProjection
        ((C.basedWeakHandoffAlong q).terminalMobius *
          C.terminalTransitionRepresentativeBetween p q) =
      realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius) := by
  classical
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong q
  let A := C.terminalTransitionRepresentativeBetween p q
  rcases
      C.terminalTransitionBetweenCoordinateAgreementSet_containsNonemptyOpen_of_homotopic
        p q hpq with
    ⟨u, huOpen, huNonempty, huSubset⟩
  have hThree :
      ContainsThreeDistinctUpperHalfPlanePoints
        (C.terminalTransitionBetweenCoordinateAgreementSet p q) :=
    containsThreeDistinctUpperHalfPlanePoints_of_nonempty_open_subset
      huOpen huNonempty huSubset
  have hFaithful :
      RealMobiusActionFaithfulOn
        (C.terminalTransitionBetweenCoordinateAgreementSet p q) :=
    realMobiusActionFaithfulOn_of_containsThreeDistinctUpperHalfPlanePoints
      realMobiusActionDeterminedByThreePointsTheoremPSL hThree
  exact
    hFaithful
      (realMobiusProjection (T.terminalMobius * A))
      (realMobiusProjection S.terminalMobius)
      (by
        intro z hz
        rcases hz with ⟨y, hySource, hyTarget, hyTransition, rfl⟩
        have hTargetFormula := C.dev_eq_on_terminalSheet q y hyTarget
        have hSourceFormula := C.dev_eq_on_terminalSheet p y hySource
        have hTransition :
            (localModels.chartAt T.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint y) =
              realMobiusRepresentativeAction A
                ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                  (PathHomotopyUniversalCover.endpoint y)) := by
          simpa [S, T, A,
            PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween]
            using
              (C.terminalTransitionDataBetween p q).transition_eq
                (PathHomotopyUniversalCover.endpoint y) hyTransition
        calc
          realMobiusAction (realMobiusProjection (T.terminalMobius * A))
              ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint y))
              =
            realMobiusRepresentativeAction (T.terminalMobius * A)
              ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint y)) := by
              simp [realMobiusAction_realMobiusProjection]
          _ =
            realMobiusRepresentativeAction T.terminalMobius
              (realMobiusRepresentativeAction A
                ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                  (PathHomotopyUniversalCover.endpoint y))) := by
              simp [realMobiusRepresentativeAction_mul]
          _ =
            realMobiusRepresentativeAction T.terminalMobius
              ((localModels.chartAt T.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint y)) := by
              rw [← hTransition]
          _ = C.dev y := by
              simpa [T] using hTargetFormula.symm
          _ =
            realMobiusRepresentativeAction S.terminalMobius
              ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint y)) := by
              rw [hSourceFormula]
          _ =
            realMobiusAction (realMobiusProjection S.terminalMobius)
              ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint y)) := by
              simp [realMobiusAction_realMobiusProjection])

/--
The local transition between the terminal charts of two terminal-sheet
branches at an arbitrary common upstairs point.

Unlike `terminalTransitionDataBetween`, the two representative paths need not
have the same endpoint.  The common base point is supplied by a point of the
intersection of the two terminal sheets.
-/
noncomputable def terminalSheetTransitionDataAt
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x y : X} (p : Path x₀ x) (q : Path x₀ y)
    (η : PathHomotopyUniversalCover X x₀)
    (hηp : η ∈ (C.basedWeakHandoffAlong p).terminalSheet)
    (hηq : η ∈ (C.basedWeakHandoffAlong q).terminalSheet) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData
      (localModels.chartAt ((C.basedWeakHandoffAlong p).terminalCenter))
      (localModels.chartAt ((C.basedWeakHandoffAlong q).terminalCenter))
      (PathHomotopyUniversalCover.endpoint η) := by
  classical
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong q
  have hS :
      PathHomotopyUniversalCover.endpoint η ∈
        (localModels.chartAt S.terminalCenter).domain :=
    S.endpoint_mem_terminal_domain_of_mem_terminalSheet hηp
  have hT :
      PathHomotopyUniversalCover.endpoint η ∈
        (localModels.chartAt T.terminalCenter).domain :=
    T.endpoint_mem_terminal_domain_of_mem_terminalSheet hηq
  exact Classical.choice
    (localModels.transition_localRealMobius S.terminalCenter T.terminalCenter
      (PathHomotopyUniversalCover.endpoint η) ⟨hS, hT⟩)

/-- The representative of the arbitrary terminal-sheet transition. -/
noncomputable def terminalSheetTransitionRepresentativeAt
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x y : X} (p : Path x₀ x) (q : Path x₀ y)
    (η : PathHomotopyUniversalCover X x₀)
    (hηp : η ∈ (C.basedWeakHandoffAlong p).terminalSheet)
    (hηq : η ∈ (C.basedWeakHandoffAlong q).terminalSheet) :
    RealMobiusRepresentative :=
  (C.terminalSheetTransitionDataAt p q η hηp hηq).representative

/--
The source-coordinate agreement set for two terminal sheets meeting at an
arbitrary upstairs point.
-/
def terminalSheetTransitionCoordinateAgreementSet
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x y : X} (p : Path x₀ x) (q : Path x₀ y)
    (η : PathHomotopyUniversalCover X x₀)
    (hηp : η ∈ (C.basedWeakHandoffAlong p).terminalSheet)
    (hηq : η ∈ (C.basedWeakHandoffAlong q).terminalSheet) : Set ℍ :=
  {z | ∃ ξ : PathHomotopyUniversalCover X x₀,
    ξ ∈ (C.basedWeakHandoffAlong p).terminalSheet ∧
    ξ ∈ (C.basedWeakHandoffAlong q).terminalSheet ∧
    PathHomotopyUniversalCover.endpoint ξ ∈
      (C.terminalSheetTransitionDataAt p q η hηp hηq).neighborhood ∧
    z =
      (localModels.chartAt
          ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
        (PathHomotopyUniversalCover.endpoint ξ)}

/--
The coordinate agreement set for two overlapping terminal sheets contains a
nonempty open upper-half-plane patch.
-/
theorem terminalSheetTransitionCoordinateAgreementSet_containsNonemptyOpen
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x y : X} (p : Path x₀ x) (q : Path x₀ y)
    (η : PathHomotopyUniversalCover X x₀)
    (hηp : η ∈ (C.basedWeakHandoffAlong p).terminalSheet)
    (hηq : η ∈ (C.basedWeakHandoffAlong q).terminalSheet) :
    ∃ u : Set ℍ,
      IsOpen u ∧ u.Nonempty ∧
        u ⊆ C.terminalSheetTransitionCoordinateAgreementSet p q η hηp hηq := by
  classical
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong q
  let τ := C.terminalSheetTransitionDataAt p q η hηp hηq
  let U := localModels.chartAt S.terminalCenter
  let eSheet :=
    PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph
      (x₀ := x₀) S.terminalSheetChart
  let O : Set (PathHomotopyUniversalCover X x₀) :=
    (S.terminalSheet ∩ T.terminalSheet) ∩
      (PathHomotopyUniversalCover.endpoint (x₀ := x₀)) ⁻¹' τ.neighborhood
  have hEndpointOpen :
      IsOpen ((PathHomotopyUniversalCover.endpoint (x₀ := x₀)) ⁻¹' τ.neighborhood) := by
    simpa using
      PathHomotopyUniversalCover.isOpen_endpoint_preimage_of_isOpen
        (x₀ := x₀) τ.isOpen_neighborhood
  have hOopen : IsOpen O := by
    simpa [O] using
      (S.isOpen_terminalSheet.inter T.isOpen_terminalSheet).inter hEndpointOpen
  have hOsubSource : O ⊆ eSheet.source := by
    intro ξ hξ
    simpa [eSheet, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using hξ.1.1
  have hOη : η ∈ O := by
    refine ⟨⟨hηp, hηq⟩, ?_⟩
    simpa [τ] using τ.mem_neighborhood
  let W : Set X := eSheet '' O
  have hWopen : IsOpen W :=
    eSheet.isOpen_image_of_subset_source hOopen hOsubSource
  have hηW : PathHomotopyUniversalCover.endpoint η ∈ W := by
    refine ⟨η, hOη, ?_⟩
    simp [eSheet, PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph]
  have hηU : PathHomotopyUniversalCover.endpoint η ∈ U.domain := by
    simpa [U, S] using S.endpoint_mem_terminal_domain_of_mem_terminalSheet hηp
  rcases
      HyperbolicLocalChart.exists_open_upperHalfPlane_subset_image_of_mem_nhds
        U hηU (hWopen.mem_nhds hηW) with
    ⟨u, huOpen, huMem, huSub⟩
  refine
    ⟨u, huOpen,
      ⟨U.toUpperHalfPlane (PathHomotopyUniversalCover.endpoint η), huMem⟩, ?_⟩
  intro z hz
  rcases huSub hz with ⟨x', hx'WU, hx'z⟩
  rcases hx'WU with ⟨hx'W, hx'U⟩
  rcases hx'W with ⟨ξ, hξO, hξEndpoint⟩
  have hEndpoint : PathHomotopyUniversalCover.endpoint ξ = x' := by
    simpa [W, eSheet, PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph]
      using hξEndpoint
  refine ⟨ξ, ?_, ?_, ?_, ?_⟩
  · exact hξO.1.1
  · exact hξO.1.2
  · simpa [O, hEndpoint] using hξO.2
  · rw [← hx'z, hEndpoint]

/--
If two terminal sheets overlap, their terminal Mobius classes agree after
adjusting by the local transition between their terminal charts at the common
base point.

This is the local branch-uniqueness statement used to avoid any global choice
of terminal charts under terminal-sheet extension.
-/
theorem terminalSheetTransitionAdjustedProjection_eq_of_mem_inter
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x y : X} (p : Path x₀ x) (q : Path x₀ y)
    (η : PathHomotopyUniversalCover X x₀)
    (hηp : η ∈ (C.basedWeakHandoffAlong p).terminalSheet)
    (hηq : η ∈ (C.basedWeakHandoffAlong q).terminalSheet) :
    realMobiusProjection
        ((C.basedWeakHandoffAlong q).terminalMobius *
          C.terminalSheetTransitionRepresentativeAt p q η hηp hηq) =
      realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius) := by
  classical
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong q
  let A := C.terminalSheetTransitionRepresentativeAt p q η hηp hηq
  rcases
      C.terminalSheetTransitionCoordinateAgreementSet_containsNonemptyOpen
        p q η hηp hηq with
    ⟨u, huOpen, huNonempty, huSubset⟩
  have hThree :
      ContainsThreeDistinctUpperHalfPlanePoints
        (C.terminalSheetTransitionCoordinateAgreementSet p q η hηp hηq) :=
    containsThreeDistinctUpperHalfPlanePoints_of_nonempty_open_subset
      huOpen huNonempty huSubset
  have hFaithful :
      RealMobiusActionFaithfulOn
        (C.terminalSheetTransitionCoordinateAgreementSet p q η hηp hηq) :=
    realMobiusActionFaithfulOn_of_containsThreeDistinctUpperHalfPlanePoints
      realMobiusActionDeterminedByThreePointsTheoremPSL hThree
  exact
    hFaithful
      (realMobiusProjection (T.terminalMobius * A))
      (realMobiusProjection S.terminalMobius)
      (by
        intro z hz
        rcases hz with ⟨ξ, hξS, hξT, hξTransition, rfl⟩
        have hTargetFormula := C.dev_eq_on_terminalSheet q ξ hξT
        have hSourceFormula := C.dev_eq_on_terminalSheet p ξ hξS
        have hTransition :
            (localModels.chartAt T.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint ξ) =
              realMobiusRepresentativeAction A
                ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                  (PathHomotopyUniversalCover.endpoint ξ)) := by
          simpa [S, T, A,
            PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalSheetTransitionRepresentativeAt]
            using
              (C.terminalSheetTransitionDataAt p q η hηp hηq).transition_eq
                (PathHomotopyUniversalCover.endpoint ξ) hξTransition
        calc
          realMobiusAction (realMobiusProjection (T.terminalMobius * A))
              ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint ξ))
              =
            realMobiusRepresentativeAction (T.terminalMobius * A)
              ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint ξ)) := by
              simp [realMobiusAction_realMobiusProjection]
          _ =
            realMobiusRepresentativeAction T.terminalMobius
              (realMobiusRepresentativeAction A
                ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                  (PathHomotopyUniversalCover.endpoint ξ))) := by
              simp [realMobiusRepresentativeAction_mul]
          _ =
            realMobiusRepresentativeAction T.terminalMobius
              ((localModels.chartAt T.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint ξ)) := by
              rw [← hTransition]
          _ = C.dev ξ := by
              simpa [T] using hTargetFormula.symm
          _ =
            realMobiusRepresentativeAction S.terminalMobius
              ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint ξ)) := by
              rw [hSourceFormula]
          _ =
            realMobiusAction (realMobiusProjection S.terminalMobius)
              ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
                (PathHomotopyUniversalCover.endpoint ξ)) := by
              simp [realMobiusAction_realMobiusProjection])

/--
The loop-prepending covariance statement can be read using the generic
terminal-chart transition `p → loop.trans p`.
-/
theorem terminalTransitionRepresentativeBetween_loopTrans_projection_eq_of_automaticTerminalTransitionProjection_equivariant
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (H : FundamentalGroup X x₀ → RealMobiusGroup)
    (hEquiv :
      ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
        {x : X} (p : Path x₀ x)
        (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
        realMobiusProjection
            (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
              C.terminalTransitionRepresentative γ loop p hloop) =
          H γ *
            realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius))
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    realMobiusProjection
        (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
          C.terminalTransitionRepresentativeBetween p (loop.trans p)) =
      H γ *
        realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius) := by
  let M := (C.basedWeakHandoffAlong (loop.trans p)).terminalMobius
  have hBetween :=
    C.terminalTransitionRepresentative_projection_eq_between γ loop p hloop
  have hLeft :
      realMobiusProjection
          (M * C.terminalTransitionRepresentative γ loop p hloop) =
        realMobiusProjection
          (M * C.terminalTransitionRepresentativeBetween p (loop.trans p)) := by
    calc
      realMobiusProjection
          (M * C.terminalTransitionRepresentative γ loop p hloop)
          = realMobiusProjection M *
              realMobiusProjection
                (C.terminalTransitionRepresentative γ loop p hloop) := by
            simp
      _ = realMobiusProjection M *
              realMobiusProjection
                (C.terminalTransitionRepresentativeBetween p (loop.trans p)) := by
            rw [hBetween]
      _ = realMobiusProjection
          (M * C.terminalTransitionRepresentativeBetween p (loop.trans p)) := by
            simp
  rw [← hLeft]
  exact hEquiv γ loop p hloop

/--
The transition-adjusted terminal PSL class for loop-prepending is independent
of the chosen representative of the loop homotopy class.
-/
theorem terminalTransitionRepresentativeBetween_loopTrans_adjusted_projection_eq_of_homotopic_loop
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (loop₁ loop₂ : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic loop₁ loop₂) :
    realMobiusProjection
        (((C.basedWeakHandoffAlong (loop₁.trans p)).terminalMobius) *
          C.terminalTransitionRepresentativeBetween p (loop₁.trans p)) =
      realMobiusProjection
        (((C.basedWeakHandoffAlong (loop₂.trans p)).terminalMobius) *
          C.terminalTransitionRepresentativeBetween p (loop₂.trans p)) := by
  let p₁ : Path x₀ x := loop₁.trans p
  let p₂ : Path x₀ x := loop₂.trans p
  let M₁ := (C.basedWeakHandoffAlong p₁).terminalMobius
  let M₂ := (C.basedWeakHandoffAlong p₂).terminalMobius
  have hp₁p₂ : Path.Homotopic p₁ p₂ := by
    simpa [p₁, p₂] using hloop.hcomp (Path.Homotopic.refl p)
  have hHom :
      realMobiusProjection
          (M₂ * C.terminalTransitionRepresentativeBetween p₁ p₂) =
        realMobiusProjection M₁ := by
    simpa [p₁, p₂, M₁, M₂] using
      C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
        p₁ p₂ hp₁p₂
  exact
    (calc
      realMobiusProjection
          (((C.basedWeakHandoffAlong (loop₂.trans p)).terminalMobius) *
            C.terminalTransitionRepresentativeBetween p (loop₂.trans p))
          =
        realMobiusProjection
          (M₂ * C.terminalTransitionRepresentativeBetween p p₂) := by
          simp [p₂, M₂]
      _ =
        realMobiusProjection
          ((M₂ * C.terminalTransitionRepresentativeBetween p₁ p₂) *
            C.terminalTransitionRepresentativeBetween p p₁) := by
          exact
            C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
              p p₁ p₂ M₂
      _ =
        realMobiusProjection
            (M₂ * C.terminalTransitionRepresentativeBetween p₁ p₂) *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p p₁) := by
          simp
      _ =
        realMobiusProjection M₁ *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p p₁) := by
          rw [hHom]
      _ =
        realMobiusProjection
          (M₁ * C.terminalTransitionRepresentativeBetween p p₁) := by
          simp
      _ =
        realMobiusProjection
          (((C.basedWeakHandoffAlong (loop₁.trans p)).terminalMobius) *
            C.terminalTransitionRepresentativeBetween p (loop₁.trans p)) := by
          simp [p₁, M₁]).symm

/--
The transition-adjusted terminal formula equality at a point of the canonical
cover.  This is the pointwise formula-level statement that PSL faithfulness
will consume.
-/
def terminalTransitionAdjustedFormulaAgreementAt
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (holonomy : RealHolonomyRepresentation X x₀)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹)
    (y : PathHomotopyUniversalCover X x₀) : Prop :=
  realMobiusRepresentativeAction
      (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
        C.terminalTransitionRepresentative γ loop p hloop)
      ((localModels.chartAt
          ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
        (PathHomotopyUniversalCover.endpoint y)) =
    holonomy.upperHalfPlaneAction γ
      (realMobiusRepresentativeAction
        ((C.basedWeakHandoffAlong p).terminalMobius)
        ((localModels.chartAt
            ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y)))

/--
The source-coordinate set on which the automatic terminal transition can be
compared.  It is the image, in the source terminal coordinate, of points of
the canonical cover lying in the source terminal sheet, whose deck translates
lie in the target terminal sheet, and whose endpoints lie in the selected
terminal transition neighborhood.
-/
def terminalTransitionCoordinateAgreementSet
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    Set ℍ :=
  {z | ∃ y : PathHomotopyUniversalCover X x₀,
    y ∈ (C.basedWeakHandoffAlong p).terminalSheet ∧
    (canonicalContinuationCover x₀).deckAction γ y ∈
      (C.basedWeakHandoffAlong (loop.trans p)).terminalSheet ∧
    PathHomotopyUniversalCover.endpoint y ∈
      (C.terminalTransitionData γ loop p hloop).neighborhood ∧
    z =
      (localModels.chartAt
          ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
        (PathHomotopyUniversalCover.endpoint y)}

/--
The terminal coordinate agreement set is always nonempty: the terminal cover
point of `p` satisfies the source sheet condition, its loop-deck translate is
the terminal cover point of `loop.trans p`, and the automatic terminal
transition is valid at the common endpoint.
-/
theorem terminalTransitionCoordinateAgreementSet_nonempty
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    (C.terminalTransitionCoordinateAgreementSet γ loop p hloop).Nonempty := by
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (loop.trans p)
  refine
    ⟨(localModels.chartAt S.terminalCenter).toUpperHalfPlane x, ?_⟩
  refine ⟨S.terminalCoverPoint, ?_, ?_, ?_, ?_⟩
  · exact S.terminalCoverPoint_mem_terminalSheet
  · have hdeck :
        T.terminalCoverPoint =
          (canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint :=
      PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCoverPoint_loopTrans_eq_deckAction
        γ loop S T hloop
    simpa [S, T, ← hdeck] using T.terminalCoverPoint_mem_terminalSheet
  · simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint] using
      (C.terminalTransitionData γ loop p hloop).mem_neighborhood
  · simp [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]

/--
The terminal coordinate agreement set contains a genuine open patch in the
source terminal upper-half-plane coordinate.

The proof is local.  Intersect the source terminal sheet, the deck-preimage of
the target terminal sheet, and the endpoint-preimage of the automatic terminal
transition neighborhood.  This is an open neighborhood of the terminal cover
point.  The endpoint projection is a homeomorphism on the source terminal
sheet, so its image gives a surface neighborhood of the endpoint.  Finally the
source terminal hyperbolic coordinate is locally open by the inverse function
theorem.
-/
theorem terminalTransitionCoordinateAgreementSet_containsNonemptyOpen
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    ∃ u : Set ℍ,
      IsOpen u ∧ u.Nonempty ∧
        u ⊆ C.terminalTransitionCoordinateAgreementSet γ loop p hloop := by
  classical
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (loop.trans p)
  let τ := C.terminalTransitionData γ loop p hloop
  let U := localModels.chartAt S.terminalCenter
  let eSheet :=
    PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph
      (x₀ := x₀) S.terminalSheetChart
  let O : Set (PathHomotopyUniversalCover X x₀) :=
    (S.terminalSheet ∩
      ((canonicalContinuationCover x₀).deckAction γ) ⁻¹' T.terminalSheet) ∩
        (PathHomotopyUniversalCover.endpoint (x₀ := x₀)) ⁻¹' τ.neighborhood
  have hDeckOpen :
      IsOpen (((canonicalContinuationCover x₀).deckAction γ) ⁻¹' T.terminalSheet) := by
    simpa [canonicalContinuationCover] using
      T.isOpen_terminalSheet.preimage
        (PathHomotopyUniversalCover.continuous_deckAction (x₀ := x₀) γ)
  have hEndpointOpen :
      IsOpen ((PathHomotopyUniversalCover.endpoint (x₀ := x₀)) ⁻¹' τ.neighborhood) := by
    simpa using
      PathHomotopyUniversalCover.isOpen_endpoint_preimage_of_isOpen
        (x₀ := x₀) τ.isOpen_neighborhood
  have hOopen : IsOpen O := by
    simpa [O] using (S.isOpen_terminalSheet.inter hDeckOpen).inter hEndpointOpen
  have hOsubSource : O ⊆ eSheet.source := by
    intro y hy
    simpa [eSheet, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using hy.1.1
  have hdeckPoint :
      T.terminalCoverPoint =
        (canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint :=
    PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCoverPoint_loopTrans_eq_deckAction
      γ loop S T hloop
  have hOpoint : S.terminalCoverPoint ∈ O := by
    refine ⟨⟨S.terminalCoverPoint_mem_terminalSheet, ?_⟩, ?_⟩
    · simpa [S, T, ← hdeckPoint] using T.terminalCoverPoint_mem_terminalSheet
    · simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
        using τ.mem_neighborhood
  let W : Set X := eSheet '' O
  have hWopen : IsOpen W :=
    eSheet.isOpen_image_of_subset_source hOopen hOsubSource
  have hxW : x ∈ W := by
    refine ⟨S.terminalCoverPoint, hOpoint, ?_⟩
    simp [eSheet, PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
  have hxU : x ∈ U.domain := by
    simpa [U, S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
      using S.terminalCoverPoint_endpoint_mem_terminal_domain
  rcases
      HyperbolicLocalChart.exists_open_upperHalfPlane_subset_image_of_mem_nhds U hxU
        (hWopen.mem_nhds hxW) with
    ⟨u, huOpen, huMem, huSub⟩
  refine ⟨u, huOpen, ⟨U.toUpperHalfPlane x, huMem⟩, ?_⟩
  intro z hz
  rcases huSub hz with ⟨x', hx'WU, hx'z⟩
  rcases hx'WU with ⟨hx'W, hx'U⟩
  rcases hx'W with ⟨y, hyO, hyEndpoint⟩
  have hEndpoint : PathHomotopyUniversalCover.endpoint y = x' := by
    simpa [W, eSheet, PathHomotopyUniversalCover.localSheetOpenPartialHomeomorph]
      using hyEndpoint
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · exact hyO.1.1
  · exact hyO.1.2
  · simpa [O, hEndpoint] using hyO.2
  · rw [← hx'z, hEndpoint]

/--
Formula agreement on terminal sheets is exactly action agreement of the two
PSL transformations on the source-coordinate agreement set.
-/
theorem terminalTransitionActionAgreement_on_coordinateAgreementSet_of_formulaAgreement
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (holonomy : RealHolonomyRepresentation X x₀)
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹)
    (hFormula :
      ∀ y : PathHomotopyUniversalCover X x₀,
        y ∈ (C.basedWeakHandoffAlong p).terminalSheet →
        (canonicalContinuationCover x₀).deckAction γ y ∈
          (C.basedWeakHandoffAlong (loop.trans p)).terminalSheet →
        PathHomotopyUniversalCover.endpoint y ∈
          (C.terminalTransitionData γ loop p hloop).neighborhood →
        C.terminalTransitionAdjustedFormulaAgreementAt
          holonomy γ loop p hloop y) :
    ∀ z ∈ C.terminalTransitionCoordinateAgreementSet γ loop p hloop,
      realMobiusAction
          (realMobiusProjection
            (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
              C.terminalTransitionRepresentative γ loop p hloop))
          z =
        realMobiusAction
          (holonomy γ *
            realMobiusProjection
              ((C.basedWeakHandoffAlong p).terminalMobius))
          z := by
  intro z hz
  rcases hz with ⟨y, hySource, hyTarget, hyTransition, rfl⟩
  have hFormulaAt :=
    hFormula y hySource hyTarget hyTransition
  simpa [terminalTransitionAdjustedFormulaAgreementAt,
    RealHolonomyRepresentation.upperHalfPlaneAction,
    realMobiusAction_mul]
    using hFormulaAt

/--
Deck equivariance and terminal-sheet agreement compare the two explicit
terminal local formulae on any point where both terminal sheets and the
automatic endpoint chart transition are valid.
-/
theorem terminalTransitionAdjustedFormula_eq_holonomy_action_of_dev_equivariant
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (holonomy : RealHolonomyRepresentation X x₀)
    (hdev :
      ∀ (γ : FundamentalGroup X x₀)
        (y : (canonicalContinuationCover x₀).total),
        C.dev ((canonicalContinuationCover x₀).deckAction γ y) =
          holonomy.upperHalfPlaneAction γ (C.dev y))
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    {x : X} (p : Path x₀ x)
    (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹)
    (y : PathHomotopyUniversalCover X x₀)
    (hySource : y ∈ (C.basedWeakHandoffAlong p).terminalSheet)
    (hyTarget :
      (canonicalContinuationCover x₀).deckAction γ y ∈
        (C.basedWeakHandoffAlong (loop.trans p)).terminalSheet)
    (hyTransition :
      PathHomotopyUniversalCover.endpoint y ∈
        (C.terminalTransitionData γ loop p hloop).neighborhood) :
    C.terminalTransitionAdjustedFormulaAgreementAt
      holonomy γ loop p hloop y := by
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (loop.trans p)
  let A := C.terminalTransitionRepresentative γ loop p hloop
  have hEndpoint :
      PathHomotopyUniversalCover.endpoint
          ((canonicalContinuationCover x₀).deckAction γ y) =
        PathHomotopyUniversalCover.endpoint y := by
    simpa [canonicalContinuationCover] using
      (canonicalContinuationCover x₀).projection_deckAction γ y
  have hTargetFormula :=
    C.dev_eq_on_terminalSheet (loop.trans p)
      ((canonicalContinuationCover x₀).deckAction γ y) hyTarget
  have hSourceFormula :=
    C.dev_eq_on_terminalSheet p y hySource
  have hTransition :
      (localModels.chartAt T.terminalCenter).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y) =
        realMobiusRepresentativeAction A
          ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y)) := by
    simpa [S, T, A, PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentative]
      using
        (C.terminalTransitionData γ loop p hloop).transition_eq
          (PathHomotopyUniversalCover.endpoint y) hyTransition
  calc
    realMobiusRepresentativeAction
        (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
          C.terminalTransitionRepresentative γ loop p hloop)
        ((localModels.chartAt
            ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y))
        =
      realMobiusRepresentativeAction T.terminalMobius
        (realMobiusRepresentativeAction A
          ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y))) := by
          simp [S, T, A, realMobiusRepresentativeAction_mul]
    _ =
      realMobiusRepresentativeAction T.terminalMobius
        ((localModels.chartAt T.terminalCenter).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y)) := by
          rw [← hTransition]
    _ =
      realMobiusRepresentativeAction T.terminalMobius
        ((localModels.chartAt T.terminalCenter).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint
            ((canonicalContinuationCover x₀).deckAction γ y))) := by
          rw [hEndpoint]
    _ = C.dev ((canonicalContinuationCover x₀).deckAction γ y) := by
          simpa [T] using hTargetFormula.symm
    _ = holonomy.upperHalfPlaneAction γ (C.dev y) := hdev γ y
    _ =
      holonomy.upperHalfPlaneAction γ
        (realMobiusRepresentativeAction
          ((C.basedWeakHandoffAlong p).terminalMobius)
          ((localModels.chartAt
              ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y))) := by
          rw [hSourceFormula]

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

/--
The local homotopy principle needed to build canonical-terminal-sheet
agreement from arbitrary based weak handoff skeleton choices.

Mathematically, this is the finite homotopy-grid/monodromy uniqueness step:
if a representative path is homotopic to a continued path followed by the
canonical local path in the terminal sheet, then their terminal branch formulae
agree at the endpoint of that local path.
-/
def PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Prop :=
  ∀ {x : X} (p : Path x₀ x)
    (y' : PathHomotopyUniversalCover X x₀)
    (hy' : y' ∈ (basedWeakHandoffAlong p).terminalSheet)
    (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
    Path.Homotopic p'
      (p.trans ((basedWeakHandoffAlong p).terminalSheetPathInSet hy')) →
      realMobiusRepresentativeAction ((basedWeakHandoffAlong p').terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p').terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction ((basedWeakHandoffAlong p).terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

/--
A finite homotopy-grid walk between two representative paths.

The field `step_terminalFormula_eq` is the elementary square/edge-move output
of the grid proof: crossing one grid move preserves the terminal branch
formula at the common endpoint.
-/
structure PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {x : X} (p q : Path x₀ x) where
  /-- Number of elementary grid moves. -/
  length : ℕ
  /-- The representative path after `n` elementary grid moves. -/
  pathAt : ℕ → Path x₀ x
  /-- The walk starts at `p`. -/
  pathAt_zero : pathAt 0 = p
  /-- The walk ends at `q`. -/
  pathAt_length : pathAt length = q
  /-- Each elementary grid move preserves the terminal branch formula. -/
  step_terminalFormula_eq :
    ∀ n, n < length →
      (basedWeakHandoffAlong (pathAt n)).terminalFormulaAt x =
        (basedWeakHandoffAlong (pathAt (n + 1))).terminalFormulaAt x

end HyperbolicMetric

end

end JJMath
