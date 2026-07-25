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

%%handwave
name: Choose the normalized initial handoff from the basepoint chart to the chart used by the first segment of a weak handoff skeleton
statement:
  Choose the normalized initial handoff from the basepoint chart to the chart used by the first
  segment of a weak handoff skeleton.
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



namespace PathLocalTransitionModelContinuationChain

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

/-- The terminal local-transition model center selected by a finite chain.

%%handwave
name: The terminal local-transition model center selected by a finite chain
statement:
  For a finite continuation chain with segment centers
  $c_0,\ldots,c_n$, define its terminal center to be $c_n$.
-/
def terminalCenter
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) : X :=
  C.centerAt (Fin.last C.length)

/-- The terminal Mobius representative selected by a finite chain.

%%handwave
name: The terminal Möbius representative selected by a finite chain
statement:
  For a finite continuation chain with accumulated representatives
  $M_0,\ldots,M_n$, define its terminal representative to be $M_n$.
-/
def terminalMobius
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) :
    RealMobiusRepresentative :=
  C.mobiusAt (Fin.last C.length)

/-- The terminal value forced by a finite local-transition continuation chain.

%%handwave
name: The terminal value forced by a finite local-transition continuation chain
statement:
  If a continuation chain along $p:x_0\rightsquigarrow x$ ends with chart
  $U_n$ and accumulated representative $M_n$, define its terminal value by
  $M_n\cdot U_n(x)\in\mathbb H$.
-/
def terminalValue
    (C : PathLocalTransitionModelContinuationChain x₀ g localModels p) : ℍ :=
  realMobiusRepresentativeAction C.terminalMobius
    ((localModels.chartAt C.terminalCenter).toUpperHalfPlane x)

end PathLocalTransitionModelContinuationChain

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

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The chosen representative of a represented path-homotopy class is homotopic to the original path.

%%handwave
name: A chosen quotient representative is homotopic to the represented path
statement: For every based path $p$, the representative chosen from its endpoint-fixed homotopy class is endpoint-fixed homotopic to $p$.
proof: The quotient representative has the same quotient class as $p$; quotient equality is exactly endpoint-fixed path homotopy.
-/
theorem out_homotopic_mk
    {x : X} (p : Path x₀ x) :
    Path.Homotopic
      (Quot.out (Path.Homotopic.Quotient.mk p))
      p := by
  exact
    (Path.Homotopic.Quotient.eq).mp
      (Quot.out_eq (Path.Homotopic.Quotient.mk p))

end PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData

namespace PathLocalTransitionHandoffChainTerminalBranchAnalyticContinuationValueData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

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

/-- The terminal value forced by a based weak handoff terminal branch.

%%handwave
name: The terminal value forced by a based weak handoff terminal branch
statement:
  The terminal value of a based weak-handoff continuation is the terminal
  value of its chosen finite continuation skeleton.
-/
def terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  (C.basedWeakHandoffAlong p).terminalValue

/--
The terminal value at a path-homotopy class, computed from Lean's chosen
representative and justified by value-level homotopy descent.

%%handwave
name: Terminal value of a path-homotopy class
statement:
  For a based path class $[p]$, define its terminal value using a chosen
  representative $p$; homotopy invariance makes this independent of that
  representative.
-/
noncomputable def terminalValueAt
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) : ℍ :=
  C.terminalValue (Quot.out q)

/-- The terminal center attached to Lean's chosen representative of a path class.

%%handwave
name: Terminal chart center of a path-homotopy class
statement:
  For a based path class $[p]$, choose a representative and take the terminal
  chart center of its weak-handoff continuation skeleton.
-/
noncomputable def terminalCenterAt
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) : X :=
  (C.basedWeakHandoffAlong (Quot.out q)).terminalCenter

/-- The terminal Mobius representative attached to Lean's chosen representative.

%%handwave
name: Terminal Möbius representative of a path-homotopy class
statement:
  For a based path class $[p]$, choose a representative and take the terminal
  accumulated real Möbius representative of its continuation skeleton.
-/
noncomputable def terminalMobiusAt
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    RealMobiusRepresentative :=
  (C.basedWeakHandoffAlong (Quot.out q)).terminalMobius

/-- The terminal sheet attached to Lean's chosen representative of a path class.

%%handwave
name: Terminal continuation sheet of a path-homotopy class
statement:
  For a based path class $[p]$, define its terminal continuation sheet as the
  terminal sheet of the skeleton chosen along a representative of $[p]$.
-/
noncomputable def terminalNeighborhoodAt
    (C :
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    Set (PathHomotopyUniversalCover X x₀) :=
  C.neighborhoodAlong (Quot.out q)

omit [RiemannSurface X] in
/-- The path-class terminal value of weak-handoff data agrees with the value along a representing path.

%%handwave
name: The descended weak-handoff value agrees on represented paths
statement: For weak-handoff continuation data and a path $p:x_0⇝x$, evaluating the path-class value at $[p]$ gives $V(x,[p])=v(p)$.
proof: The quotient’s chosen representative is homotopic to $p$; apply the assumed path-homotopy invariance of the skeleton terminal value.
-/
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

%%handwave
name: Based weak handoff value-continuation data descend to path-class local-transition continuation data
statement:
  Homotopy-invariant terminal values of based weak-handoff continuations
  descend to a path-class developing value, with the chosen terminal chart,
  accumulated Möbius representative, and terminal sheet supplying its local
  continuation formula.
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

/-- The terminal value forced by canonical-terminal-sheet based weak handoff data.

%%handwave
name: The terminal value forced by canonical-terminal-sheet based weak handoff data
statement:
  The terminal value of canonical-sheet agreement data is the terminal value
  of its based weak-handoff continuation skeleton.
-/
def terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  (C.basedWeakHandoffAlong p).terminalValue

/--
Canonical-terminal-sheet based weak handoff data fill the full value
continuation record by using the terminal local sheet as the neighborhood.

%%handwave
name: Canonical-terminal-sheet based weak handoff data fill the full value continuation data by using the terminal local sheet as the neighborhood
statement:
  Canonical terminal-sheet agreement supplies homotopy-invariant terminal
  values and a local terminal branch formula on the terminal sheet, hence
  gives pathwise analytic-continuation value data.
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

%%handwave
name: A set of upper-half-plane points is large enough to identify PSL transformations by their actions
statement:
  A subset $S\subseteq\mathbb H$ is faithful for the real projective action
  when two elements of $\mathrm{PSL}_2(\mathbb R)$ that agree on every point
  of $S$ are equal.
-/
def RealMobiusActionFaithfulOn (s : Set ℍ) : Prop :=
  ∀ g h : RealMobiusGroup,
    (∀ z ∈ s, realMobiusAction g z = realMobiusAction h z) → g = h

/-- A set of upper-half-plane points contains three pairwise distinct points.

%%handwave
name: A set of upper-half-plane points contains three pairwise distinct points
statement:
  A subset $S\subseteq\mathbb H$ contains three distinct points when there
  exist $z_1,z_2,z_3\in S$ with $z_i\ne z_j$ for $i\ne j$.
-/
def ContainsThreeDistinctUpperHalfPlanePoints (s : Set ℍ) : Prop :=
  ∃ z₁ z₂ z₃ : ℍ,
    z₁ ∈ s ∧ z₂ ∈ s ∧ z₃ ∈ s ∧
      z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃

/--
The global three-point faithfulness theorem for the PSL action on `ℍ`.
Mathematically, this is the statement that three distinct points and their
images determine a Möbius transformation.

%%handwave
name: The global three-point faithfulness theorem for the PSL action on ℍ
statement:
  If two elements of $\mathrm{PSL}_2(\mathbb R)$ have equal actions on three
  pairwise distinct points of $\mathbb H$, then the two projective
  transformations are equal.
-/
def RealMobiusActionDeterminedByThreePointsTheoremPSL : Prop :=
  ∀ (g h : RealMobiusGroup) (z₁ z₂ z₃ : ℍ),
    z₁ ≠ z₂ → z₁ ≠ z₃ → z₂ ≠ z₃ →
      realMobiusAction g z₁ = realMobiusAction h z₁ →
      realMobiusAction g z₂ = realMobiusAction h z₂ →
      realMobiusAction g z₃ = realMobiusAction h z₃ →
      g = h

/-- The PSL action on `ℍ` is determined by three distinct points.

%%handwave
name: Three points determine an orientation-preserving real Möbius transformation
statement: If $g,h∈PSL_2(ℝ)$ agree on three pairwise distinct points $z_1,z_2,z_3∈ℍ$, then $g=h$.
proof: Apply the standard three-point determination theorem for the projective real Möbius action.
-/
theorem realMobiusActionDeterminedByThreePointsTheoremPSL :
    RealMobiusActionDeterminedByThreePointsTheoremPSL :=
  realMobiusAction_determined_by_three_points

/--
Three contained distinct points make a set PSL-action-faithful, assuming the
global three-point faithfulness theorem.

%%handwave
name: Three distinct points make the projective action faithful on a set
statement: Let $A⊆ℍ$ contain pairwise distinct points $z_1,z_2,z_3$. If two elements of $PSL_2(ℝ)$ act identically on $A$, then they are equal.
proof: Evaluate the action equality at the three contained points and apply three-point determination.
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

/-- An infinite set contains three pairwise distinct points.

%%handwave
name: Every infinite subset of the upper half-plane contains three distinct points
statement: If $A⊆ℍ$ is infinite, then there are pairwise distinct $z_1,z_2,z_3∈A$.
proof: Choose one point of $A$, then a second outside the first singleton, and a third outside the two-point set; infinitude guarantees each choice.
-/
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

%%handwave
name: A set containing a nonempty open patch contains three distinct points
statement: If a set $A⊆ℍ$ contains a nonempty open subset $U$, then $A$ contains three pairwise distinct points.
proof: A nonempty open subset of the upper half-plane is infinite. Choose three distinct points of $U$ and use $U⊆A$.
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

%%handwave
name: A local chart transition has a unique projective Möbius class
statement: For fixed hyperbolic charts $U,V$ and an overlap point $x$, any two local real Möbius transition representatives at $x$ have the same class in $PSL_2(ℝ)$.
proof: Their transition formulas agree on the intersection of two source-coordinate neighborhoods, a nonempty open subset of $ℍ$. That set contains three points, so faithfulness identifies the two projective classes.
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

%%handwave
name: The projective transition class is constant on a preconnected overlap
statement: Let $W$ be preconnected and suppose a local transition from chart $U$ to chart $V$ exists at every point of $W$. For $x,y∈W$, transition representatives $T_x,T_y$ satisfy $[T_y]=[T_x]$.
proof: Consider the points of $W$ where some local transition has class $[T_x]$. Local recentering and same-point uniqueness make this subset and its complement open in $W$; preconnectedness and membership of $x$ force it to contain $y$.
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

%%handwave
name: The projective transition class is constant along a path interval
statement: Let $a≤b$ and suppose transitions between fixed charts $U,V$ exist at every $p(t)$ for $t∈[a,b]$. Then transition representatives at $p(a)$ and $p(b)$ have the same projective class.
proof: The image $p([a,b])$ is preconnected. Apply constancy of the transition class on that image, using the assumed transition existence at every image point.
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

namespace PathLocalTransitionModelBasedWeakHandoffSkeleton

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

/--
On one segment of a handoff skeleton, if a fixed comparison chart contains
the whole segment image, then the PSL class of the local transition from the
segment chart to the comparison chart is constant from the left endpoint to
the right endpoint.

%%handwave
name: Conversion to a fixed chart has constant projective class along one segment
statement: Suppose a fixed chart $c$ contains the image of segment $[t_k,t_{k+1}]$ of a skeleton. Local transitions from the segment chart $c_k$ to $c$ at the two endpoints have the same class in $PSL_2(ℝ)$.
proof: Transitions exist at every point of the path interval because both charts contain the segment. Apply constancy of the projective transition class along a path interval.
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
If two based handoff skeletons over the same path use the same subdivision
parameters, then their accumulated branches agree projectively after
converting the chart of `T` at each aligned vertex to the chart of `S` at that
same vertex.

This is the local algebraic comparison behind same-path mutual refinements.
The only geometric input is ordinary local-transition data between the two
chosen charts at each shared vertex; constancy of those transition classes
along each common segment is supplied by the componentwise transition atlas.

%%handwave
name: Aligned subdivisions have projectively equal accumulated branches
statement: Let skeletons $S,T$ over the same path have equal lengths and identical subdivision parameters. For a transition $A_n:c^S_n→c^T_n$ at each common vertex, one has $[M^T_nA_n]=[M^S_n]$ for every aligned index $n$.
proof: Induct over the aligned vertices. At the basepoint use the cocycle of the two initial handoffs and $A_0$. For a successor, compare the transition classes along the common segment, apply the handoff cocycle at its right endpoint, and combine with the induction hypothesis.
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

%%handwave
name: Aligned continuation skeletons have equal terminal values
statement: If two skeletons over one path have equal length and identical subdivision parameters, and local transitions relate their selected charts at every common vertex, then their terminal values agree: $v(S)=v(T)$.
proof: Apply aligned accumulated projective equality at the final vertex. The final chart transition converts the terminal coordinate of $S$ to that of $T$, so equality of projective actions identifies the two endpoint values.
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
The endpoint chart-insertion terminal value is preserved for actual
local-transition witnesses.

%%handwave
name: Inserting an endpoint chart preserves the terminal value
statement: Under the endpoint-chart insertion hypotheses, the refined skeleton and the original skeleton have equal terminal values.
proof: Evaluate the equality of their terminal branch formulas at the common path endpoint.
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

/-- The terminal value forced by canonical-terminal-sheet agreement data.

%%handwave
name: The terminal value forced by canonical-terminal-sheet agreement data
statement:
  The terminal value attached to a path is the value obtained by evaluating
  its canonical continuation skeleton at the endpoint.
-/
def terminalValue
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  (C.basedWeakHandoffAlong p).terminalValue

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
The single-valued upstairs map defined by choosing Lean's representative of
the stored path class.

%%handwave
name: Developing map defined by terminal continuation values
statement:
  For a point $(x,[p])$ of the canonical path-homotopy cover, define
  $\operatorname{dev}(x,[p])$ as the terminal continuation value of a chosen
  representative of $[p]$; homotopy invariance makes the value single-valued.
-/
noncomputable def dev
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  fun y =>
    (C.basedWeakHandoffAlong
      (Quot.out (PathHomotopyUniversalCover.pathClass y))).terminalValue

/--
At an explicitly represented point of the canonical cover, the constructed
upstairs map has the terminal value of the representing path.

%%handwave
name: The developing map at a represented lift is the path terminal value
statement: For every path $p:x_0⇝x$, the point $(x,[p])$ in the canonical cover satisfies $dev(x,[p])=v(p)$.
proof: Rewrite the represented lift as the terminal cover point of $p$ and apply terminal-value invariance under the quotient’s chosen representative.
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

%%handwave
name: The developing map equals the terminal branch formula on each terminal sheet
statement: If $y$ lies in the terminal sheet of a skeleton $S_p$, then $dev(y)=M_p·c_p(π(y))$, where $c_p$ and $M_p$ are its terminal chart and accumulated transformation.
proof: Choose a path representing the path class of $y$. The sheet-agreement hypothesis identifies its continuation value with the displayed terminal formula, while the definition of $dev$ uses that same representative.
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

%%handwave
name: The local transition between the terminal chart of p and the terminal chart of loop.trans p at their common endpoint
statement:
  If a loop representing $\gamma^{-1}$ is prepended to
  $p:x_0\rightsquigarrow x$, choose local real Möbius transition data at $x$
  from the terminal chart of $p$ to the terminal chart of the prepended path.
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

%%handwave
name: The automatically selected terminal chart-transition representative
statement:
  For a loop-prepended path, take the real Möbius representative of the
  selected transition between the original and prepended terminal charts.
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

%%handwave
name: The automatic transition identifies the two terminal coordinates at the endpoint
statement: Let a loop representing $γ^{-1}$ be prepended to $p:x_0⇝x$. If $A$ is the automatically selected transition from the terminal chart of $p$ to that of the prepended path, then $c_{loop⋆p}(x)=A·c_p(x)$.
proof: The automatic local transition datum is valid at $x$ and its defining coordinate identity gives exactly this equation.
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

%%handwave
name: The local transition between the terminal charts of two based weak handoff skeletons with the same endpoint
statement:
  For based paths $p,q:x_0\rightsquigarrow x$, choose local real Möbius
  transition data at $x$ from the terminal chart of the continuation along
  $p$ to that along $q$.
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

/-- The automatically selected representative comparing two terminal charts.

%%handwave
name: The automatically selected representative comparing two terminal charts
statement:
  For based paths $p,q$ with a common endpoint, take the real Möbius
  representative of the selected transition from the terminal chart of $p$
  to that of $q$.
-/
noncomputable def terminalTransitionRepresentativeBetween
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    {x : X} (p q : Path x₀ x) :
    RealMobiusRepresentative :=
  (C.terminalTransitionDataBetween p q).representative

/--
The loop-prepending terminal transition and the generic terminal transition
from `p` to `loop.trans p` define the same PSL class.

%%handwave
name: The loop transition and generic terminal-chart transition have the same projective class
statement: For a loop representing $γ^{-1}$ and a path $p$, the automatically selected loop transition and the generic transition from the terminal chart of $p$ to that of $loop⋆p$ define the same element of $PSL_2(ℝ)$.
proof: Both are local real Möbius transitions between the same two charts at the same endpoint, so uniqueness of the local transition class applies.
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

%%handwave
name: Automatic terminal-chart transitions satisfy the projective cocycle
statement: For based paths $p,q,r$ with the same endpoint, let $A_{pq}$ be the automatic terminal-chart transition from $p$ to $q$. Then $[A_{pr}]=[A_{qr}A_{pq}]$.
proof: The direct transition and the composite of the two successive transitions are local transitions between the same endpoint charts. Apply the local transition cocycle in $PSL_2(ℝ)$.
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

%%handwave
name: The terminal-chart cocycle remains valid after a branch transformation
statement: For paths $p,q,r$ ending at one point and any real Möbius representative $M$, $[MA_{pr}]=[(MA_{qr})A_{pq}]$.
proof: Multiply the projective cocycle $[A_{pr}]=[A_{qr}A_{pq}]$ on the left by $[M]$ and use associativity.
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

%%handwave
name: The source-coordinate set on which two homotopic terminal path formulae can be compared after changing terminal charts from p to q
statement:
  For homotopic based paths $p,q$ with common endpoint, define the set of
  source terminal coordinates arising from cover points that lie in both
  terminal sheets and in the neighborhood where the selected terminal-chart
  transition is valid.
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

%%handwave
name: Homotopic paths have an open terminal-coordinate agreement patch
statement: If $p,q:x_0⇝x$ are endpoint-fixed homotopic, then the source terminal coordinate contains a nonempty open set on which the two terminal-sheet lifts and their automatic terminal-chart transition are simultaneously valid.
proof: The terminal lift represented by $p$ equals that represented by $q$ and lies in both terminal sheets. Intersect these open sheets with the transition neighborhood, project through the covering chart, and map by the source terminal coordinate to obtain the required open patch.
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

%%handwave
name: Homotopic paths have the same adjusted terminal projective branch
statement: If $p,q:x_0⇝x$ are endpoint-fixed homotopic and $A_{pq}$ changes from the terminal chart of $p$ to that of $q$, then $[M_qA_{pq}]=[M_p]$.
proof: On a nonempty open source-coordinate patch, terminal-sheet agreement identifies both formulas with the single-valued developing map. The two projective transformations therefore act identically on three distinct points, so faithfulness gives the stated equality.
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

%%handwave
name: The local transition between the terminal charts of two terminal-sheet branches at an arbitrary common upstairs point
statement:
  If a cover point $\eta$ belongs to the terminal sheets of paths $p$ and
  $q$, choose local real Möbius transition data at $\pi(\eta)$ from the
  terminal chart of $p$ to that of $q$.
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

/-- The representative of the arbitrary terminal-sheet transition.

%%handwave
name: The representative of the arbitrary terminal-sheet transition
statement:
  For two terminal sheets meeting at $\eta$, take the real Möbius
  representative of their selected local transition at $\pi(\eta)$.
-/
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

%%handwave
name: The source-coordinate agreement set for two terminal sheets meeting at an arbitrary upstairs point
statement:
  For terminal sheets of $p$ and $q$ meeting at $\eta$, define the source
  terminal coordinates of cover points lying in both sheets and in the
  neighborhood where their selected terminal-chart transition is valid.
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

%%handwave
name: Overlapping terminal sheets have an open coordinate agreement patch
statement: If a cover point $η$ lies in the terminal sheets of paths $p$ and $q$, then the source terminal coordinate contains a nonempty open set on which both sheet formulas and the local transition between their terminal charts are valid.
proof: Intersect the two open terminal sheets and the transition neighborhood around $η$. Project this open cover neighborhood to the surface and then through the source terminal coordinate, whose local homeomorphism makes the image open and nonempty.
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

%%handwave
name: Branches on overlapping terminal sheets agree after chart transition
statement: If $η$ lies in the terminal sheets of $p$ and $q$, and $A$ is the local transition from the terminal chart of $p$ to that of $q$ at $π(η)$, then $[M_qA]=[M_p]$.
proof: On the open coordinate agreement patch, both adjusted transformations compute the same developing-map values. Three-point faithfulness of the projective action identifies their classes.
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

%%handwave
name: Projective loop covariance can use the generic terminal transition
statement: Assume automatic loop transitions satisfy $[M_{loop⋆p}A_γ]=H(γ)[M_p]$. For a loop representing $γ^{-1}$, the generic terminal transition $A_{p,loop⋆p}$ also satisfies $[M_{loop⋆p}A_{p,loop⋆p}]=H(γ)[M_p]$.
proof: The automatic loop transition and the generic terminal-chart transition have the same projective class; substitute this equality into the assumed covariance formula.
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

%%handwave
name: The adjusted loop-prepending class depends only on the loop homotopy class
statement: If based loops $ℓ_1,ℓ_2$ are endpoint-fixed homotopic, then for every based path $p$, $[M_{ℓ_1⋆p}A_{p,ℓ_1⋆p}]=[M_{ℓ_2⋆p}A_{p,ℓ_2⋆p}]$.
proof: The concatenated paths $ℓ_1⋆p$ and $ℓ_2⋆p$ are homotopic. Apply adjusted terminal-class equality to them and use the terminal-transition cocycle through the intermediate path $p$.
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

%%handwave
name: The transition-adjusted terminal formula equality at a point of the canonical cover
statement:
  At a cover point $y$, transition-adjusted loop covariance is the equality
  between the terminal formula for the loop-prepended path, after changing
  from the source terminal chart, and the holonomy translate by $\gamma$ of
  the source terminal formula.
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

%%handwave
name: The source-coordinate set on which the automatic terminal transition can be compared
statement:
  For a loop representing $\gamma^{-1}$ and a path $p$, define the source
  terminal coordinates of cover points lying in the source terminal sheet,
  whose $\gamma$-deck translates lie in the target terminal sheet, and whose
  endpoints lie in the selected transition neighborhood.
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
The terminal coordinate agreement set contains a genuine open patch in the
source terminal upper-half-plane coordinate.

The proof is local.  Intersect the source terminal sheet, the deck-preimage of
the target terminal sheet, and the endpoint-preimage of the automatic terminal
transition neighborhood.  This is an open neighborhood of the terminal cover
point.  The endpoint projection is a homeomorphism on the source terminal
sheet, so its image gives a surface neighborhood of the endpoint.  Finally the
source terminal hyperbolic coordinate is locally open by the inverse function
theorem.

%%handwave
name: The loop transition coordinate agreement set contains an open patch
statement: For a loop representing $γ^{-1}$ and a path $p$, the source terminal upper-half-plane coordinate contains a nonempty open set on which the source sheet, the deck-translated target sheet, and the automatic transition neighborhood all agree.
proof: Intersect the source terminal sheet, the deck-preimage of the target terminal sheet, and the endpoint-preimage of the transition neighborhood at the represented terminal lift. Project through the terminal-sheet covering chart and then the locally open source coordinate.
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

%%handwave
name: Terminal formula agreement implies projective action agreement
statement: Assume the adjusted terminal formula after loop continuation equals the holonomy-transformed source formula wherever both terminal sheets and the transition are valid. Then on every point $z$ of the coordinate agreement set, $[M_{loop⋆p}A_γ]·z=(H(γ)[M_p])·z$.
proof: Represent $z$ by a surface point and its lift supplied by membership in the coordinate agreement set. Expand the two terminal formulas at that lift, use the automatic chart-transition identity, and apply the assumed formula equality.
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

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

/--
The local homotopy principle needed to build canonical-terminal-sheet
agreement from arbitrary based weak handoff skeleton choices.

Mathematically, this is the finite homotopy-grid/monodromy uniqueness step:
if a representative path is homotopic to a continued path followed by the
canonical local path in the terminal sheet, then their terminal branch formulae
agree at the endpoint of that local path.

%%handwave
name: The local homotopy principle needed to build canonical-terminal-sheet agreement from arbitrary based weak handoff skeleton choices
statement:
  Given a continuation skeleton along every based path, if a representative
  path is endpoint-fixed homotopic to another path followed by the canonical
  local path in its terminal sheet, then the two accumulated terminal branch
  formulae have the same value at the endpoint of that local path.
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
