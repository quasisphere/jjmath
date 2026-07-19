import JJMath.AnalyticContinuation.LocalBranch
import JJMath.Hyperbolic.Converse.Continuation.Chains

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

namespace PathLocalTransitionBasedWeakHandoffHomotopyGridWalk

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {x : X} {p q : Path x₀ x}

omit [RiemannSurface X] in
/-- The constant homotopy-grid walk at a representative path. -/
def refl
    (p : Path x₀ x) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
      basedWeakHandoffAlong p p where
  length := 0
  pathAt := fun _ => p
  pathAt_zero := rfl
  pathAt_length := rfl
  step_terminalFormula_eq := by
    intro n hn
    omega

omit [RiemannSurface X] in
/-- Append one formula-preserving grid step to a homotopy-grid walk. -/
def snoc
    {r : Path x₀ x}
    (W :
      PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
        basedWeakHandoffAlong p q)
    (hstep :
      (basedWeakHandoffAlong q).terminalFormulaAt x =
        (basedWeakHandoffAlong r).terminalFormulaAt x) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
      basedWeakHandoffAlong p r where
  length := W.length + 1
  pathAt := fun n =>
    if h : n ≤ W.length then
      W.pathAt n
    else
      r
  pathAt_zero := by
    simp [W.pathAt_zero]
  pathAt_length := by
    simp
  step_terminalFormula_eq := by
    intro n hn
    by_cases hnlt : n < W.length
    · have hnle : n ≤ W.length := Nat.le_of_lt hnlt
      have hsuccle : n + 1 ≤ W.length := Nat.succ_le_of_lt hnlt
      have hpath₀ :
          (if h : n ≤ W.length then W.pathAt n else r) = W.pathAt n := by
        simp [hnle]
      have hpath₁ :
          (if h : n + 1 ≤ W.length then W.pathAt (n + 1) else r) =
            W.pathAt (n + 1) := by
        simp [hsuccle]
      rw [hpath₀, hpath₁]
      exact W.step_terminalFormula_eq n hnlt
    · have hn_eq : n = W.length := by omega
      subst n
      have hle : W.length ≤ W.length := le_rfl
      have hnot : ¬ W.length + 1 ≤ W.length := by omega
      have hpath₀ :
          (if h : W.length ≤ W.length then W.pathAt W.length else r) =
            W.pathAt W.length := by
        simp
      have hpath₁ :
          (if h : W.length + 1 ≤ W.length then W.pathAt (W.length + 1) else r) =
            r := by
        simp [hnot]
      rw [hpath₀, hpath₁, W.pathAt_length]
      exact hstep

omit [RiemannSurface X] in
/-- A single formula-preserving step as a homotopy-grid walk. -/
def ofStep
    (hstep :
      (basedWeakHandoffAlong p).terminalFormulaAt x =
        (basedWeakHandoffAlong q).terminalFormulaAt x) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
      basedWeakHandoffAlong p q :=
  (refl p).snoc hstep

omit [RiemannSurface X] in
/-- Reverse a homotopy-grid walk. -/
def symm
    (W :
      PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
        basedWeakHandoffAlong p q) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
      basedWeakHandoffAlong q p where
  length := W.length
  pathAt := fun n => W.pathAt (W.length - n)
  pathAt_zero := by
    simpa using W.pathAt_length
  pathAt_length := by
    simpa using W.pathAt_zero
  step_terminalFormula_eq := by
    intro n hn
    let m := W.length - (n + 1)
    have hm : m < W.length := by omega
    have hnext : W.length - n = m + 1 := by
      omega
    have hcur : W.length - (n + 1) = m := rfl
    rw [hnext, hcur]
    exact (W.step_terminalFormula_eq m hm).symm

omit [RiemannSurface X] in
/-- Concatenate two homotopy-grid walks. -/
def trans
    {r : Path x₀ x}
    (W₁ :
      PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
        basedWeakHandoffAlong p q)
    (W₂ :
      PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
        basedWeakHandoffAlong q r) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
      basedWeakHandoffAlong p r where
  length := W₁.length + W₂.length
  pathAt := fun n =>
    if h : n ≤ W₁.length then
      W₁.pathAt n
    else
      W₂.pathAt (n - W₁.length)
  pathAt_zero := by
    simp [W₁.pathAt_zero]
  pathAt_length := by
    by_cases hW₂zero : W₂.length = 0
    · have hqr : q = r := by
        have hlen := W₂.pathAt_length
        rw [hW₂zero] at hlen
        exact W₂.pathAt_zero.symm.trans hlen
      simp [hW₂zero, W₁.pathAt_length, hqr]
    · have hnot : ¬ W₁.length + W₂.length ≤ W₁.length := by
        have hpos : 0 < W₂.length := Nat.pos_of_ne_zero hW₂zero
        omega
      have hidx : W₁.length + W₂.length - W₁.length = W₂.length := by
        omega
      simp [hnot, hidx, W₂.pathAt_length]
  step_terminalFormula_eq := by
    intro n hn
    by_cases hnlt : n < W₁.length
    · have hnle : n ≤ W₁.length := Nat.le_of_lt hnlt
      have hsuccle : n + 1 ≤ W₁.length := Nat.succ_le_of_lt hnlt
      have hpath₀ :
          (if h : n ≤ W₁.length then W₁.pathAt n
            else W₂.pathAt (n - W₁.length)) = W₁.pathAt n := by
        simp [hnle]
      have hpath₁ :
          (if h : n + 1 ≤ W₁.length then W₁.pathAt (n + 1)
            else W₂.pathAt (n + 1 - W₁.length)) =
            W₁.pathAt (n + 1) := by
        simp [hsuccle]
      rw [hpath₀, hpath₁]
      exact W₁.step_terminalFormula_eq n hnlt
    · by_cases hn_eq : n = W₁.length
      · subst n
        have hW₂pos : 0 < W₂.length := by omega
        have hnot : ¬ W₁.length + 1 ≤ W₁.length := by omega
        have hidx : W₁.length + 1 - W₁.length = 1 := by omega
        have hidx0 : W₁.length - W₁.length = 0 := by omega
        have hle : W₁.length ≤ W₁.length := le_rfl
        have hpath₀ :
            (if h : W₁.length ≤ W₁.length then W₁.pathAt W₁.length
              else W₂.pathAt (W₁.length - W₁.length)) =
              W₁.pathAt W₁.length := by
          simp
        have hpath₁ :
            (if h : W₁.length + 1 ≤ W₁.length then W₁.pathAt (W₁.length + 1)
              else W₂.pathAt (W₁.length + 1 - W₁.length)) =
              W₂.pathAt 1 := by
          simp [hnot, hidx]
        rw [hpath₀, hpath₁, W₁.pathAt_length]
        exact
          (congrArg
              (fun s : Path x₀ x =>
                (basedWeakHandoffAlong s).terminalFormulaAt x)
              W₂.pathAt_zero).symm.trans
            (W₂.step_terminalFormula_eq 0 hW₂pos)
      · have hn_after : W₁.length < n := by omega
        have hn₂ : n - W₁.length < W₂.length := by omega
        have hnot_n : ¬ n ≤ W₁.length := by omega
        have hnot_succ : ¬ n + 1 ≤ W₁.length := by omega
        have hidx_succ : n + 1 - W₁.length = (n - W₁.length) + 1 := by
          omega
        have hpath₀ :
            (if h : n ≤ W₁.length then W₁.pathAt n
              else W₂.pathAt (n - W₁.length)) =
              W₂.pathAt (n - W₁.length) := by
          simp [hnot_n]
        have hpath₁ :
            (if h : n + 1 ≤ W₁.length then W₁.pathAt (n + 1)
              else W₂.pathAt (n + 1 - W₁.length)) =
              W₂.pathAt ((n - W₁.length) + 1) := by
          simp [hnot_succ, hidx_succ]
        rw [hpath₀, hpath₁]
        exact W₂.step_terminalFormula_eq (n - W₁.length) hn₂

omit [RiemannSurface X] in
/-- A finite grid walk preserves the terminal branch formula from its first path
to its last path.

%%handwave
name: A finite homotopy-grid walk preserves the terminal formula
statement: If a finite homotopy-grid walk joins based paths $p$ and $q$ with common endpoint $x$, then the chosen continuation formulas satisfy $F_p(x)=F_q(x)$.
proof: Induct over the grid walk. The empty walk is reflexive, and adjoining an elementary grid move composes its endpoint formula equality with the induction hypothesis.
-/
theorem terminalFormulaAt_start_eq_end
    (W :
      PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
        basedWeakHandoffAlong p q) :
    (basedWeakHandoffAlong p).terminalFormulaAt x =
      (basedWeakHandoffAlong q).terminalFormulaAt x := by
  have hprefix :
      ∀ m, m ≤ W.length →
        (basedWeakHandoffAlong (W.pathAt 0)).terminalFormulaAt x =
          (basedWeakHandoffAlong (W.pathAt m)).terminalFormulaAt x := by
    intro m hm
    induction m with
    | zero =>
        rfl
    | succ m ih =>
        have hm_lt : m < W.length := Nat.lt_of_succ_le hm
        exact (ih (Nat.le_of_lt hm_lt)).trans
          (W.step_terminalFormula_eq m hm_lt)
  have h := hprefix W.length le_rfl
  rw [W.pathAt_zero, W.pathAt_length] at h
  exact h

end PathLocalTransitionBasedWeakHandoffHomotopyGridWalk

/--
An elementary grid move between two representative paths with the same
endpoints.

This isolates the local square/edge argument in the homotopy-grid proof.  The
mathematical content of such a move is precisely preservation of the terminal
branch formula at the common endpoint.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridMove
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {x : X} (p q : Path x₀ x) where
  /-- The elementary move preserves the terminal branch formula. -/
  terminalFormula_eq :
    (basedWeakHandoffAlong p).terminalFormulaAt x =
      (basedWeakHandoffAlong q).terminalFormulaAt x

namespace PathLocalTransitionBasedWeakHandoffElementaryGridMove

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {x : X} {p q : Path x₀ x}

omit [RiemannSurface X] in
/-- The identity elementary grid move. -/
def refl
    (p : Path x₀ x) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMove
      basedWeakHandoffAlong p p where
  terminalFormula_eq := rfl

/--
Two representative paths with the same endpoints give an elementary grid move
when both path images lie in one fixed comparison chart.
-/
def of_common_fixedChart
    (p q : Path x₀ x) (c : X)
    (hcp : ∀ t : unitInterval, p t ∈ (localModels.chartAt c).domain)
    (hcq : ∀ t : unitInterval, q t ∈ (localModels.chartAt c).domain)
    (Tbase :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt x₀)
        (localModels.chartAt c)
        x₀) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMove
      basedWeakHandoffAlong p q where
  terminalFormula_eq := by
    let S := basedWeakHandoffAlong p
    let T := basedWeakHandoffAlong q
    change S.terminalValue = T.terminalValue
    calc
      S.terminalValue =
          realMobiusRepresentativeAction Tbase.representative⁻¹
            ((localModels.chartAt c).toUpperHalfPlane x) := by
            exact S.terminalValue_eq_fixedChartBranch c hcp Tbase
      _ = T.terminalValue := by
            exact (T.terminalValue_eq_fixedChartBranch c hcq Tbase).symm

omit [RiemannSurface X] in
/-- The terminal formula equality carried by an elementary grid move.

%%handwave
name: An elementary grid move preserves the endpoint formula
statement: If an elementary grid move joins paths $p,q:x_0⇝x$, then the chosen continuation formulas satisfy $F_p(x)=F_q(x)$.
proof: This is the terminal-formula equality carried by the elementary move.
-/
theorem terminalFormulaAt_eq
    (M :
      PathLocalTransitionBasedWeakHandoffElementaryGridMove
        basedWeakHandoffAlong p q) :
    (basedWeakHandoffAlong p).terminalFormulaAt x =
      (basedWeakHandoffAlong q).terminalFormulaAt x :=
  M.terminalFormula_eq

omit [RiemannSurface X] in
/-- Reverse an elementary grid move. -/
def symm
    (M :
      PathLocalTransitionBasedWeakHandoffElementaryGridMove
        basedWeakHandoffAlong p q) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMove
      basedWeakHandoffAlong q p where
  terminalFormula_eq := M.terminalFormula_eq.symm

end PathLocalTransitionBasedWeakHandoffElementaryGridMove

/--
A finite walk whose steps are elementary grid moves.

This is the intended combinatorial output of subdividing an endpoint-fixed
homotopy square by local transition neighborhoods.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
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
  /-- Each step is an elementary grid move. -/
  moveAt :
    ∀ n, n < length →
      PathLocalTransitionBasedWeakHandoffElementaryGridMove
        basedWeakHandoffAlong (pathAt n) (pathAt (n + 1))

namespace PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {x : X} {p q : Path x₀ x}

omit [RiemannSurface X] in
/-- The constant elementary grid-move walk at a representative path. -/
def refl
    (p : Path x₀ x) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
      basedWeakHandoffAlong p p where
  length := 0
  pathAt := fun _ => p
  pathAt_zero := rfl
  pathAt_length := rfl
  moveAt := by
    intro n hn
    omega

omit [RiemannSurface X] in
/-- Change only the named endpoint paths of an elementary grid-move walk. -/
def cast
    (W :
      PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
        basedWeakHandoffAlong p q)
    {p' q' : Path x₀ x} (hp : p' = p) (hq : q' = q) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
      basedWeakHandoffAlong p' q' where
  length := W.length
  pathAt := W.pathAt
  pathAt_zero := W.pathAt_zero.trans hp.symm
  pathAt_length := W.pathAt_length.trans hq.symm
  moveAt := W.moveAt

/--
An elementary-move walk is a homotopy-grid walk after forgetting the
individual move witnesses.
-/
def toHomotopyGridWalk
    (W :
      PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
        basedWeakHandoffAlong p q) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
      basedWeakHandoffAlong p q where
  length := W.length
  pathAt := W.pathAt
  pathAt_zero := W.pathAt_zero
  pathAt_length := W.pathAt_length
  step_terminalFormula_eq := by
    intro n hn
    exact (W.moveAt n hn).terminalFormulaAt_eq

omit [RiemannSurface X] in
/-- Append one elementary grid move to the end of an elementary grid-move walk. -/
def snoc
    {r : Path x₀ x}
    (W :
      PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
        basedWeakHandoffAlong p q)
    (M :
      PathLocalTransitionBasedWeakHandoffElementaryGridMove
        basedWeakHandoffAlong q r) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
      basedWeakHandoffAlong p r where
  length := W.length + 1
  pathAt := fun n =>
    if h : n ≤ W.length then
      W.pathAt n
    else
      r
  pathAt_zero := by
    simp [W.pathAt_zero]
  pathAt_length := by
    simp
  moveAt := by
    intro n hn
    by_cases hnlt : n < W.length
    · have hnle : n ≤ W.length := Nat.le_of_lt hnlt
      have hsuccle : n + 1 ≤ W.length := Nat.succ_le_of_lt hnlt
      simpa [hnle, hsuccle] using W.moveAt n hnlt
    · have hn_eq : n = W.length := by omega
      subst n
      have hnot : ¬ W.length + 1 ≤ W.length := by omega
      simpa [hnot, W.pathAt_length] using M

omit [RiemannSurface X] in
/-- A single elementary grid move as an elementary grid-move walk. -/
def ofMove
    (M :
      PathLocalTransitionBasedWeakHandoffElementaryGridMove
        basedWeakHandoffAlong p q) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
      basedWeakHandoffAlong p q :=
  (refl p).snoc M

omit [RiemannSurface X] in
/-- Reverse a finite elementary grid-move walk. -/
def symm
    (W :
      PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
        basedWeakHandoffAlong p q) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
      basedWeakHandoffAlong q p where
  length := W.length
  pathAt := fun n => W.pathAt (W.length - n)
  pathAt_zero := by
    simpa using W.pathAt_length
  pathAt_length := by
    simpa using W.pathAt_zero
  moveAt := by
    intro n hn
    let m := W.length - (n + 1)
    have hm : m < W.length := by omega
    have hnext : W.length - n = m + 1 := by
      omega
    have hcur : W.length - (n + 1) = m := rfl
    simpa [m, hnext] using
      (W.moveAt m hm).symm

omit [RiemannSurface X] in
/-- Concatenate two finite elementary grid-move walks. -/
def trans
    {r : Path x₀ x}
    (W₁ :
      PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
        basedWeakHandoffAlong p q)
    (W₂ :
      PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
        basedWeakHandoffAlong q r) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
      basedWeakHandoffAlong p r where
  length := W₁.length + W₂.length
  pathAt := fun n =>
    if h : n ≤ W₁.length then
      W₁.pathAt n
    else
      W₂.pathAt (n - W₁.length)
  pathAt_zero := by
    simp [W₁.pathAt_zero]
  pathAt_length := by
    by_cases hW₂zero : W₂.length = 0
    · have hqr : q = r := by
        have hlen := W₂.pathAt_length
        rw [hW₂zero] at hlen
        exact W₂.pathAt_zero.symm.trans hlen
      simp [hW₂zero, W₁.pathAt_length, hqr]
    · have hnot : ¬ W₁.length + W₂.length ≤ W₁.length := by
        have hpos : 0 < W₂.length := Nat.pos_of_ne_zero hW₂zero
        omega
      have hidx : W₁.length + W₂.length - W₁.length = W₂.length := by
        omega
      simp [hnot, hidx, W₂.pathAt_length]
  moveAt := by
    intro n hn
    by_cases hnlt : n < W₁.length
    · have hnle : n ≤ W₁.length := Nat.le_of_lt hnlt
      have hsuccle : n + 1 ≤ W₁.length := Nat.succ_le_of_lt hnlt
      simpa [hnle, hsuccle] using W₁.moveAt n hnlt
    · by_cases hn_eq : n = W₁.length
      · subst n
        have hW₂pos : 0 < W₂.length := by omega
        have hnot : ¬ W₁.length + 1 ≤ W₁.length := by omega
        have hidx : W₁.length + 1 - W₁.length = 1 := by omega
        have hidx0 : W₁.length - W₁.length = 0 := by omega
        simpa [hnot, hidx, hidx0, W₁.pathAt_length, W₂.pathAt_zero] using
          W₂.moveAt 0 hW₂pos
      · have hn_after : W₁.length < n := by omega
        have hn₂ : n - W₁.length < W₂.length := by omega
        have hnot_n : ¬ n ≤ W₁.length := by omega
        have hnot_succ : ¬ n + 1 ≤ W₁.length := by omega
        have hidx_succ : n + 1 - W₁.length = (n - W₁.length) + 1 := by
          omega
        simpa [hnot_n, hnot_succ, hidx_succ] using
          W₂.moveAt (n - W₁.length) hn₂

omit [RiemannSurface X] in
/-- An elementary-move walk preserves the terminal branch formula.

%%handwave
name: A finite elementary-move walk preserves the terminal formula
statement: If a finite walk of elementary grid moves joins paths $p,q:x_0⇝x$, then the chosen continuation formulas satisfy $F_p(x)=F_q(x)$.
proof: Induct along the move walk and compose the terminal-formula equality of each elementary move.
-/
theorem terminalFormulaAt_start_eq_end
    (W :
      PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
        basedWeakHandoffAlong p q) :
    (basedWeakHandoffAlong p).terminalFormulaAt x =
      (basedWeakHandoffAlong q).terminalFormulaAt x :=
  W.toHomotopyGridWalk.terminalFormulaAt_start_eq_end

end PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk

/--
A finite grid walk whose every step is controlled by one fixed comparison
chart containing both whole representative paths of that step.

This is a deliberately strong global-chart special case of the homotopy-grid
boundary.  It is useful as an analytic test for the fixed-chart propagation
lemma, but the genuine topological homotopy-grid theorem for long paths must
use local square moves with common prefix/suffix data instead of asking a
single chart to contain an entire representative path.
-/
structure PathLocalTransitionBasedWeakHandoffFixedChartGridMoveWalk
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {x : X} (p q : Path x₀ x) where
  /-- Number of chart-controlled grid steps. -/
  length : ℕ
  /-- The representative path after `n` chart-controlled steps. -/
  pathAt : ℕ → Path x₀ x
  /-- The walk starts at `p`. -/
  pathAt_zero : pathAt 0 = p
  /-- The walk ends at `q`. -/
  pathAt_length : pathAt length = q
  /-- A chart controlling each elementary step. -/
  stepChart : ∀ n, n < length → X
  /-- The left path of each step stays in its controlling chart. -/
  left_mem_stepChart :
    ∀ n (hn : n < length) (t : unitInterval),
      pathAt n t ∈ (localModels.chartAt (stepChart n hn)).domain
  /-- The right path of each step stays in its controlling chart. -/
  right_mem_stepChart :
    ∀ n (hn : n < length) (t : unitInterval),
      pathAt (n + 1) t ∈ (localModels.chartAt (stepChart n hn)).domain
  /-- The basepoint transition into the controlling chart of each step. -/
  baseTransition :
    ∀ n (hn : n < length),
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt x₀)
        (localModels.chartAt (stepChart n hn))
        x₀

namespace PathLocalTransitionBasedWeakHandoffFixedChartGridMoveWalk

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {x : X} {p q : Path x₀ x}

/--
A chart-controlled grid walk gives an elementary grid-move walk.
-/
def toElementaryGridMoveWalk
    (W :
      PathLocalTransitionBasedWeakHandoffFixedChartGridMoveWalk
        basedWeakHandoffAlong p q) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
      basedWeakHandoffAlong p q where
  length := W.length
  pathAt := W.pathAt
  pathAt_zero := W.pathAt_zero
  pathAt_length := W.pathAt_length
  moveAt := by
    intro n hn
    exact
      PathLocalTransitionBasedWeakHandoffElementaryGridMove.of_common_fixedChart
        (W.pathAt n) (W.pathAt (n + 1))
        (W.stepChart n hn)
        (W.left_mem_stepChart n hn)
        (W.right_mem_stepChart n hn)
        (W.baseTransition n hn)

end PathLocalTransitionBasedWeakHandoffFixedChartGridMoveWalk

/--
Every endpoint-fixed path homotopy admits a finite walk by elementary grid
moves.
-/
def PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
    Nonempty
      (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
        basedWeakHandoffAlong p q)

/--
Every endpoint-fixed path homotopy admits a finite walk by chart-controlled
grid moves.
-/
def PathLocalTransitionBasedWeakHandoffFixedChartGridMoveWalkPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
    Nonempty
      (PathLocalTransitionBasedWeakHandoffFixedChartGridMoveWalk
        basedWeakHandoffAlong p q)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The raw cut path through one homotopy strip: follow the lower row up to the
cut, cross vertically through the homotopy, then follow the upper row.
-/
def homotopyStripCutPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r : unitInterval) :
    Path (F (a, 0)) (F (b, 1)) :=
  (((F.eval a).subpath 0 r).trans ((F.evalAt r).subpath a b)).trans
    ((F.eval b).subpath r 1)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The raw cut path through one homotopy strip, cast back to the fixed endpoints.
-/
def homotopyStripCutPathRaw
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r : unitInterval) :
    Path x₀ x :=
  (homotopyStripCutPathRawCore F a b r).cast (by simp) (by simp)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The cut path through one homotopy strip, normalized at the two endpoint cuts
so that `r = 1` is exactly the lower row and `r = 0` is exactly the upper row.
-/
noncomputable def homotopyStripCutPath
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r : unitInterval) :
    Path x₀ x :=
  if r = 1 then
    F.eval a
  else if r = 0 then
    F.eval b
  else
    homotopyStripCutPathRaw F a b r

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- At the lower boundary of a strip, the normalized cut is the row at the left horizontal parameter.

%%handwave
name: The terminal strip cut is the left row
statement: For an endpoint-fixed homotopy $F$ and $a,b∈[0,1]$, the normalized strip cut at $r=1$ equals the row path $s↦F(a,s)$.
proof: Expand the normalized cut definition; its $r=1$ branch is exactly the row at $a$.
-/
@[simp]
theorem homotopyStripCutPath_one
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b : unitInterval) :
    homotopyStripCutPath F a b 1 = F.eval a := by
  simp [homotopyStripCutPath]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- At the upper boundary of a strip, the normalized cut is the row at the right horizontal parameter.

%%handwave
name: The initial strip cut is the right row
statement: For an endpoint-fixed homotopy $F$ and $a,b∈[0,1]$, the normalized strip cut at $r=0$ equals the row path $s↦F(b,s)$.
proof: Expand the normalized cut definition; after excluding $0=1$, its $r=0$ branch is exactly the row at $b$.
-/
@[simp]
theorem homotopyStripCutPath_zero
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b : unitInterval) :
    homotopyStripCutPath F a b 0 = F.eval b := by
  simp [homotopyStripCutPath]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The lower-then-right path across one homotopy rectangle.
-/
def homotopyRectangleBottomRightPath
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, r₀)) (F (b, r₁)) :=
  ((F.eval a).subpath r₀ r₁).trans ((F.evalAt r₁).subpath a b)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The left-then-upper path across one homotopy rectangle.
-/
def homotopyRectangleLeftTopPath
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, r₀)) (F (b, r₁)) :=
  ((F.evalAt r₀).subpath a b).trans ((F.eval b).subpath r₀ r₁)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The explicitly decomposed upper cut path for one column: common prefix, then
the lower-then-right rectangle edge, then the common upper suffix.
-/
def homotopyStripColumnTopPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, 0)) (F (b, 1)) :=
  (((F.eval a).subpath 0 r₀).trans
      (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans
    ((F.eval b).subpath r₁ 1)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The explicitly decomposed lower cut path for one column: common prefix, then
the left-then-upper rectangle edge, then the common upper suffix.
-/
def homotopyStripColumnBottomPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, 0)) (F (b, 1)) :=
  (((F.eval a).subpath 0 r₀).trans
      (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans
    ((F.eval b).subpath r₁ 1)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The common lower-row prefix in a column move, cast to the fixed basepoint.
-/
def homotopyStripColumnPrefix
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a r₀ : unitInterval) :
    Path x₀ (F (a, r₀)) :=
  ((F.eval a).subpath 0 r₀).cast (by simp) rfl

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The common upper-row suffix in a column move, cast to the fixed endpoint.
-/
def homotopyStripColumnSuffix
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (b r₁ : unitInterval) :
    Path (F (b, r₁)) x :=
  ((F.eval b).subpath r₁ 1).cast rfl (by simp)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The decomposed upper cut path, cast back to the fixed endpoints.
-/
def homotopyStripColumnTopPath
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path x₀ x :=
  (homotopyStripColumnTopPathRawCore F a b r₀ r₁).cast (by simp) (by simp)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The decomposed lower cut path, cast back to the fixed endpoints.
-/
def homotopyStripColumnBottomPath
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path x₀ x :=
  (homotopyStripColumnBottomPathRawCore F a b r₀ r₁).cast (by simp) (by simp)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The top-column path after reassociating concatenations, but before merging
the two consecutive lower-row subpaths.
-/
def homotopyStripColumnTopAssocPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, 0)) (F (b, 1)) :=
  ((((F.eval a).subpath 0 r₀).trans
      ((F.eval a).subpath r₀ r₁)).trans
    ((F.evalAt r₁).subpath a b)).trans
    ((F.eval b).subpath r₁ 1)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The bottom-column path after reassociating concatenations, but before merging
the two consecutive upper-row subpaths.
-/
def homotopyStripColumnBottomAssocPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, 0)) (F (b, 1)) :=
  (((F.eval a).subpath 0 r₀).trans
    ((F.evalAt r₀).subpath a b)).trans
    (((F.eval b).subpath r₀ r₁).trans
      ((F.eval b).subpath r₁ 1))

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
Casted endpoint form of `homotopyStripColumnTopAssocPathRawCore`.
-/
def homotopyStripColumnTopAssocPath
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path x₀ x :=
  (homotopyStripColumnTopAssocPathRawCore F a b r₀ r₁).cast
    (by simp) (by simp)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
Casted endpoint form of `homotopyStripColumnBottomAssocPathRawCore`.
-/
def homotopyStripColumnBottomAssocPath
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path x₀ x :=
  (homotopyStripColumnBottomAssocPathRawCore F a b r₀ r₁).cast
    (by simp) (by simp)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The decomposed top route is the common prefix, the lower-then-right rectangle edge, and the common suffix.

%%handwave
name: The top column route decomposes into prefix, rectangle edge, and suffix
statement: For a homotopy rectangle $[a,b]×[r_0,r_1]$, the decomposed top route is exactly $(P_{a,r_0}⋆B_{a,b,r_0,r_1})⋆Q_{b,r_1}$, where $B$ traverses the lower edge and then the right edge.
proof: This equality follows by unfolding the definitions of the decomposed top path, common prefix, rectangle edge, and common suffix.
-/
@[simp]
theorem homotopyStripColumnTopPath_eq_prefix_rectangle_suffix
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    homotopyStripColumnTopPath F a b r₀ r₁ =
      ((homotopyStripColumnPrefix F a r₀).trans
        (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans
          (homotopyStripColumnSuffix F b r₁) := by
  rfl

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The decomposed bottom route is the common prefix, the left-then-upper rectangle edge, and the common suffix.

%%handwave
name: The bottom column route decomposes into prefix, rectangle edge, and suffix
statement: For a homotopy rectangle $[a,b]×[r_0,r_1]$, the decomposed bottom route is exactly $(P_{a,r_0}⋆L_{a,b,r_0,r_1})⋆Q_{b,r_1}$, where $L$ traverses the left edge and then the upper edge.
proof: This equality follows directly by unfolding the four path definitions.
-/
@[simp]
theorem homotopyStripColumnBottomPath_eq_prefix_rectangle_suffix
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    homotopyStripColumnBottomPath F a b r₀ r₁ =
      ((homotopyStripColumnPrefix F a r₀).trans
        (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans
          (homotopyStripColumnSuffix F b r₁) := by
  rfl

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The decomposed upper cut path is endpoint-fixed homotopic to the raw upper
cut path.  This is only reparameterization/parenthesization bookkeeping:
first merge the two lower-row subpaths, then reassociate concatenations.

%%handwave
name: The decomposed top route is homotopic to the raw upper cut
statement: For every endpoint-fixed homotopy $F$ and parameters $a,b,r_0,r_1$, the raw-core top column route is endpoint-fixed homotopic to the raw strip cut at height $r_1$.
proof: Merge the two adjacent subpaths of the row at $a$, whisker that homotopy by the common horizontal and suffix paths, and reassociate the concatenations.
-/
theorem homotopyStripColumnTopPathRawCore_homotopic_cutPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    (homotopyStripColumnTopPathRawCore F a b r₀ r₁).Homotopic
      (homotopyStripCutPathRawCore F a b r₁) := by
  let γ := F.eval a
  let δ := (F.evalAt r₁).subpath a b
  let σ := (F.eval b).subpath r₁ 1
  have hAssoc :
      ((γ.subpath 0 r₀).trans ((γ.subpath r₀ r₁).trans δ)).Homotopic
        (((γ.subpath 0 r₀).trans (γ.subpath r₀ r₁)).trans δ) :=
    (Path.Homotopic.trans_assoc
      (γ.subpath 0 r₀) (γ.subpath r₀ r₁) δ).symm
  have hSplit :
      (((γ.subpath 0 r₀).trans (γ.subpath r₀ r₁)).trans δ).Homotopic
        ((γ.subpath 0 r₁).trans δ) := by
    exact
      Path.Homotopic.hcomp
        (⟨Path.Homotopy.subpathTransSubpath γ 0 r₀ r₁⟩ :
          ((γ.subpath 0 r₀).trans (γ.subpath r₀ r₁)).Homotopic
            (γ.subpath 0 r₁))
        (Path.Homotopic.refl δ)
  have hPrefix :
      ((γ.subpath 0 r₀).trans ((γ.subpath r₀ r₁).trans δ)).Homotopic
        ((γ.subpath 0 r₁).trans δ) :=
    hAssoc.trans hSplit
  simpa [homotopyStripColumnTopPathRawCore,
    homotopyStripCutPathRawCore, homotopyRectangleBottomRightPath,
    γ, δ, σ] using
    Path.Homotopic.hcomp hPrefix (Path.Homotopic.refl σ)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The decomposed lower cut path is endpoint-fixed homotopic to the raw lower
cut path.  This is the analogous upper-row subpath merge for the bottom edge.

%%handwave
name: The decomposed bottom route is homotopic to the raw lower cut
statement: For every endpoint-fixed homotopy $F$ and parameters $a,b,r_0,r_1$, the raw-core bottom column route is endpoint-fixed homotopic to the raw strip cut at height $r_0$.
proof: Merge the two adjacent subpaths of the row at $b$ after the common prefix and horizontal route, then reassociate the concatenations.
-/
theorem homotopyStripColumnBottomPathRawCore_homotopic_cutPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    (homotopyStripColumnBottomPathRawCore F a b r₀ r₁).Homotopic
      (homotopyStripCutPathRawCore F a b r₀) := by
  let γ := F.eval a
  let υ := F.eval b
  let δ := (F.evalAt r₀).subpath a b
  let ρ := υ.subpath r₀ r₁
  let σ := υ.subpath r₁ 1
  have hAssocLeft :
      ((γ.subpath 0 r₀).trans (δ.trans ρ)).Homotopic
        (((γ.subpath 0 r₀).trans δ).trans ρ) :=
    (Path.Homotopic.trans_assoc (γ.subpath 0 r₀) δ ρ).symm
  have hWithSuffix :
      (((γ.subpath 0 r₀).trans (δ.trans ρ)).trans σ).Homotopic
        ((((γ.subpath 0 r₀).trans δ).trans ρ).trans σ) :=
    Path.Homotopic.hcomp hAssocLeft (Path.Homotopic.refl σ)
  have hAssocRight :
      ((((γ.subpath 0 r₀).trans δ).trans ρ).trans σ).Homotopic
        (((γ.subpath 0 r₀).trans δ).trans (ρ.trans σ)) :=
    Path.Homotopic.trans_assoc ((γ.subpath 0 r₀).trans δ) ρ σ
  have hSplit :
      (((γ.subpath 0 r₀).trans δ).trans (ρ.trans σ)).Homotopic
        (((γ.subpath 0 r₀).trans δ).trans (υ.subpath r₀ 1)) := by
    exact
      Path.Homotopic.hcomp
        (Path.Homotopic.refl ((γ.subpath 0 r₀).trans δ))
        (⟨Path.Homotopy.subpathTransSubpath υ r₀ r₁ 1⟩ :
          (ρ.trans σ).Homotopic (υ.subpath r₀ 1))
  simpa [homotopyStripColumnBottomPathRawCore,
    homotopyStripCutPathRawCore, homotopyRectangleLeftTopPath,
    γ, υ, δ, ρ, σ] using
    (hWithSuffix.trans hAssocRight).trans hSplit

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
Casted endpoint form of
`homotopyStripColumnTopPathRawCore_homotopic_cutPathRawCore`.

%%handwave
name: The based top column route is homotopic to the based raw cut
statement: For paths based at $x_0$ and ending at $x$, the decomposed top column path over $[a,b]×[r_0,r_1]$ is endpoint-fixed homotopic to the raw cut at $r_1$.
proof: Transport the raw-core homotopy through the endpoint casts identifying its source with $x_0$ and target with $x$.
-/
theorem homotopyStripColumnTopPath_homotopic_cutPathRaw
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    (homotopyStripColumnTopPath F a b r₀ r₁).Homotopic
      (homotopyStripCutPathRaw F a b r₁) :=
  (homotopyStripColumnTopPathRawCore_homotopic_cutPathRawCore
    F a b r₀ r₁).pathCast (by simp) (by simp)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
Casted endpoint form of
`homotopyStripColumnBottomPathRawCore_homotopic_cutPathRawCore`.

%%handwave
name: The based bottom column route is homotopic to the based raw cut
statement: For paths based at $x_0$ and ending at $x$, the decomposed bottom column path over $[a,b]×[r_0,r_1]$ is endpoint-fixed homotopic to the raw cut at $r_0$.
proof: Transport the raw-core bottom homotopy through the common endpoint casts.
-/
theorem homotopyStripColumnBottomPath_homotopic_cutPathRaw
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    (homotopyStripColumnBottomPath F a b r₀ r₁).Homotopic
      (homotopyStripCutPathRaw F a b r₀) :=
  (homotopyStripColumnBottomPathRawCore_homotopic_cutPathRawCore
    F a b r₀ r₁).pathCast (by simp) (by simp)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
Taking a subpath of a subpath is the same as taking the corresponding
subpath of the original path.

%%handwave
name: A subpath of a subpath is an affine subpath
statement: For a path $γ$ and $a,b,s,t∈[0,1]$, $(γ|_{[a,b]})|_{[s,t]}=γ|_{[(1-s)a+sb,(1-t)a+tb]}$.
proof: Extensionality reduces the claim to associativity of affine interpolation on the unit interval.
-/
theorem path_subpath_subpath
    {x y : X} (γ : Path x y)
    (a b s t : unitInterval) :
    (γ.subpath a b).subpath s t =
      γ.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) := by
  ext u
  simp only [Path.subpath]
  change
    γ (Set.Icc.convexComb a b (Set.Icc.convexComb s t u)) =
      γ (Set.Icc.convexComb (Set.Icc.convexComb a b s)
          (Set.Icc.convexComb a b t) u)
  apply congrArg γ
  ext
  simp [Set.Icc.convexComb]
  ring_nf

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
If `b` lies between `a` and `c`, it is the convex-combination breakpoint for
the subpath from `a` to `c`.
-/
def unitInterval.middleParameter
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) : unitInterval :=
  ⟨((b - a) / (c - a) : ℝ),
    by
      by_cases h : (c - a : ℝ) = 0
      · have hac : (a : ℝ) = c := by linarith
        simp [hac]
      · have hba : 0 ≤ ((b : ℝ) - (a : ℝ)) := sub_nonneg.mpr hab
        have hca : 0 ≤ ((c : ℝ) - (a : ℝ)) := sub_nonneg.mpr (hab.trans hbc)
        exact div_nonneg hba hca,
    by
      by_cases h : (c - a : ℝ) = 0
      · have hac : (a : ℝ) = c := by linarith
        simp [hac]
      · have hba_ca : ((b : ℝ) - (a : ℝ)) ≤ ((c : ℝ) - (a : ℝ)) := by
          linarith [show (b : ℝ) ≤ c from hbc]
        have hca : 0 ≤ ((c : ℝ) - (a : ℝ)) := sub_nonneg.mpr (hab.trans hbc)
        exact div_le_one_of_le₀ hba_ca hca⟩

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- A point between two ordered unit-interval parameters is their convex combination at the middle parameter.

%%handwave
name: An intermediate parameter is a convex combination of the endpoints
statement: If $a≤b≤c$ in $[0,1]$, then for the explicit middle parameter $θ=(b-a)/(c-a)$, with the degenerate case interpreted in $[0,1]$, one has $b=(1-θ)a+θc$.
proof: Apply the convex-combination representation of a point lying in the closed interval $[a,c]$.
-/
theorem unitInterval.middleParameter_spec
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    b = Set.Icc.convexComb a c
      (unitInterval.middleParameter a b c hab hbc) :=
  Set.Icc.eq_convexComb hab hbc

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Rescale a parameter `u ∈ [0,r]` back to the unit interval. -/
def unitInterval.rescaleLeft
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hu : u ≤ r) :
    unitInterval :=
  ⟨(u : ℝ) / r,
    div_nonneg (unitInterval.nonneg u) hr0.le,
    div_le_one_of_le₀ hu hr0.le⟩

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Rescaling really inverts the left subinterval parametrization.

%%handwave
name: Left rescaling inverts the left affine parametrization
statement: If $0<r$ and $0≤u≤r$, then the affine point of $[0,r]$ at parameter $u/r$ is $u$: $(1-u/r)0+(u/r)r=u$.
proof: Reduce subtype equality to real equality and simplify the quotient using $r≠0$.
-/
theorem unitInterval.convexCombo_zero_right_rescaleLeft
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hu : u ≤ r) :
    Set.Icc.convexComb 0 r (unitInterval.rescaleLeft r u hr0 hu) = u := by
  ext
  simp [unitInterval.rescaleLeft, Set.Icc.convexComb]
  field_simp [ne_of_gt hr0]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Rescale a parameter `u ∈ [r,1]` back to the unit interval. -/
def unitInterval.rescaleRight
    (r u : unitInterval) (hr1 : (r : ℝ) < 1) (hu : r ≤ u) :
    unitInterval :=
  ⟨((u : ℝ) - r) / (1 - r),
    by
      exact div_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hr1.le),
    by
      have hur : ((u : ℝ) - r) ≤ 1 - (r : ℝ) := by
        linarith [unitInterval.le_one u]
      exact div_le_one_of_le₀ hur (sub_nonneg.mpr hr1.le)⟩

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Rescaling really inverts the right subinterval parametrization.

%%handwave
name: Right rescaling inverts the right affine parametrization
statement: If $r<1$ and $r≤u≤1$, then the affine point of $[r,1]$ at parameter $(u-r)/(1-r)$ is $u$.
proof: Reduce to real equality, clear the nonzero denominator $1-r$, and expand the resulting ring identity.
-/
theorem unitInterval.convexCombo_left_one_rescaleRight
    (r u : unitInterval) (hr1 : (r : ℝ) < 1) (hu : r ≤ u) :
    Set.Icc.convexComb r 1 (unitInterval.rescaleRight r u hr1 hu) = u := by
  ext
  have hne : (1 - (r : ℝ)) ≠ 0 := by linarith
  simp [unitInterval.rescaleRight, Set.Icc.convexComb]
  field_simp [hne]
  ring

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
On the first half of the split path, the left rescaling recovers the original
path value at `u`.

%%handwave
name: Left rescaling recovers the original path on the first split half
statement: If $0<r$ and $u≤r$, evaluating $(γ|_{[0,r]})⋆(γ|_{[r,1]})$ at the first-half parameter corresponding to $u/r$ gives $γ(u)$.
proof: The first half of a concatenated path evaluates on the left subpath, and left affine rescaling sends its parameter back to $u$.
-/
theorem path_unitSplit_firstHalf_rescaleLeft
    {x y : X} (γ : Path x y)
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hu : u ≤ r) :
    ((γ.subpath 0 r).trans (γ.subpath r 1))
        (unitInterval.firstHalf (unitInterval.rescaleLeft r u hr0 hu)) =
      γ u := by
  rw [path_trans_firstHalf_apply]
  change γ (Set.Icc.convexComb 0 r
      (unitInterval.rescaleLeft r u hr0 hu)) = γ u
  rw [unitInterval.convexCombo_zero_right_rescaleLeft]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
On the second half of the split path, the right rescaling recovers the
original path value at `u`.

%%handwave
name: Right rescaling recovers the original path on the second split half
statement: If $r<1$ and $r≤u$, evaluating $(γ|_{[0,r]})⋆(γ|_{[r,1]})$ at the second-half parameter corresponding to $(u-r)/(1-r)$ gives $γ(u)$.
proof: Use the second-half evaluation formula for concatenation and the inverse formula for right affine rescaling.
-/
theorem path_unitSplit_secondHalf_rescaleRight
    {x y : X} (γ : Path x y)
    (r u : unitInterval) (hr1 : (r : ℝ) < 1) (hu : r ≤ u) :
    ((γ.subpath 0 r).trans (γ.subpath r 1))
        (unitInterval.secondHalf (unitInterval.rescaleRight r u hr1 hu)) =
      γ u := by
  rw [path_trans_secondHalf_apply]
  change γ (Set.Icc.convexComb r 1
      (unitInterval.rescaleRight r u hr1 hu)) = γ u
  rw [unitInterval.convexCombo_left_one_rescaleRight]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The split-path parameter corresponding to an original parameter `u`, for an
interior breakpoint `r`.
-/
noncomputable def unitInterval.unitSplitReparam
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    unitInterval :=
  if hu : u ≤ r then
    unitInterval.firstHalf (unitInterval.rescaleLeft r u hr0 hu)
  else
    unitInterval.secondHalf
      (unitInterval.rescaleRight r u hr1 (le_of_lt (lt_of_not_ge hu)))

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Below the breakpoint, the split reparameterization is the rescaled first half.

%%handwave
name: The split reparameterization uses the first half below the breakpoint
statement: For $0<r<1$ and $u≤r$, the split reparameterization is $R_r(u)=u/(2r)$.
proof: The defining case distinction selects the left branch under the hypothesis $u≤r$.
-/
theorem unitInterval.unitSplitReparam_of_le
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (hu : u ≤ r) :
    unitInterval.unitSplitReparam r u hr0 hr1 =
      unitInterval.firstHalf (unitInterval.rescaleLeft r u hr0 hu) := by
  simp [unitInterval.unitSplitReparam, hu]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Above the breakpoint, the split reparameterization is the rescaled second half.

%%handwave
name: The split reparameterization uses the second half above the breakpoint
statement: For $0<r<1$ and $r≤u$, the split reparameterization is $R_r(u)=1/2+(u-r)/(2(1-r))$.
proof: If $u>r$, unfold the right branch. At $u=r$, compute both branches and show that each equals $1/2$.
-/
theorem unitInterval.unitSplitReparam_of_ge
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (hu : r ≤ u) :
    unitInterval.unitSplitReparam r u hr0 hr1 =
      unitInterval.secondHalf (unitInterval.rescaleRight r u hr1 hu) := by
  by_cases hur : u ≤ r
  · have hru : u = r := le_antisymm hur hu
    subst u
    have hleft :
        unitInterval.firstHalf
            (unitInterval.rescaleLeft r r hr0 le_rfl) =
          unitInterval.secondHalf
            (unitInterval.rescaleRight r r hr1 le_rfl) := by
      ext
      simp [unitInterval.firstHalf, unitInterval.secondHalf,
        unitInterval.rescaleLeft, unitInterval.rescaleRight]
      field_simp [ne_of_gt hr0, sub_ne_zero.mpr (ne_of_lt hr1)]
    rw [unitInterval.unitSplitReparam_of_le r r hr0 hr1 le_rfl, hleft]
  · simp [unitInterval.unitSplitReparam, hur]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The split reparameterization is monotone.

%%handwave
name: The unit-split reparameterization is monotone
statement: For $0<r<1$ and $u≤v$, one has $R_r(u)≤R_r(v)$.
proof: Split according to whether $u$ and $v$ lie below or above $r$. On one side monotonicity follows from affine rescaling; across the breakpoint the first-half image is at most $1/2$ and the second-half image is at least $1/2$.
-/
theorem unitInterval.unitSplitReparam_mono
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    {u v : unitInterval} (huv : u ≤ v) :
    unitInterval.unitSplitReparam r u hr0 hr1 ≤
      unitInterval.unitSplitReparam r v hr0 hr1 := by
  by_cases hur : u ≤ r
  · by_cases hvr : v ≤ r
    · rw [unitInterval.unitSplitReparam_of_le r u hr0 hr1 hur,
        unitInterval.unitSplitReparam_of_le r v hr0 hr1 hvr]
      change ((u : ℝ) / r) / 2 ≤ ((v : ℝ) / r) / 2
      have hdiv : (u : ℝ) / r ≤ (v : ℝ) / r :=
        div_le_div_of_nonneg_right huv hr0.le
      nlinarith
    · have hrv : r ≤ v := le_of_lt (lt_of_not_ge hvr)
      rw [unitInterval.unitSplitReparam_of_le r u hr0 hr1 hur,
        unitInterval.unitSplitReparam_of_ge r v hr0 hr1 hrv]
      change
        (unitInterval.firstHalf (unitInterval.rescaleLeft r u hr0 hur) : ℝ) ≤
          (unitInterval.secondHalf (unitInterval.rescaleRight r v hr1 hrv) : ℝ)
      exact le_trans (unitInterval.firstHalf_le_half _)
        (unitInterval.half_le_secondHalf _)
  · have hru : r ≤ u := le_of_lt (lt_of_not_ge hur)
    have hrv : r ≤ v := hru.trans huv
    rw [unitInterval.unitSplitReparam_of_ge r u hr0 hr1 hru,
      unitInterval.unitSplitReparam_of_ge r v hr0 hr1 hrv]
    change
      (1 + (((u : ℝ) - r) / (1 - r))) / 2 ≤
        (1 + (((v : ℝ) - r) / (1 - r))) / 2
    have hnum : ((u : ℝ) - r) ≤ ((v : ℝ) - r) := by
      linarith [show (u : ℝ) ≤ v from huv]
    have hdiv :
        ((u : ℝ) - r) / (1 - r) ≤
          ((v : ℝ) - r) / (1 - r) :=
      div_le_div_of_nonneg_right hnum (sub_nonneg.mpr hr1.le)
    nlinarith

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The split reparameterization fixes the left endpoint.

%%handwave
name: The unit-split reparameterization fixes zero
statement: For every $0<r<1$, $R_r(0)=0$.
proof: Use the left-branch formula and evaluate the left rescaling and first-half map at zero.
-/
@[simp]
theorem unitInterval.unitSplitReparam_zero
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    unitInterval.unitSplitReparam r 0 hr0 hr1 = 0 := by
  rw [unitInterval.unitSplitReparam_of_le r 0 hr0 hr1
    (show (0 : unitInterval) ≤ r from hr0.le)]
  ext
  simp [unitInterval.firstHalf, unitInterval.rescaleLeft]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The split reparameterization fixes the right endpoint.

%%handwave
name: The unit-split reparameterization fixes one
statement: For every $0<r<1$, $R_r(1)=1$.
proof: Use the right-branch formula, simplify $(1-r)/(1-r)=1$, and evaluate the second-half map at one.
-/
@[simp]
theorem unitInterval.unitSplitReparam_one
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    unitInterval.unitSplitReparam r 1 hr0 hr1 = 1 := by
  rw [unitInterval.unitSplitReparam_of_ge r 1 hr0 hr1
    (show r ≤ (1 : unitInterval) from hr1.le)]
  ext
  have hne : (1 - (r : ℝ)) ≠ 0 := by linarith
  simp [unitInterval.secondHalf, unitInterval.rescaleRight]
  field_simp [hne]
  norm_num

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The combined split reparameterization recovers the original path value.

%%handwave
name: The split path composed with its reparameterization is the original path
statement: For a path $γ$, a breakpoint $0<r<1$, and $u∈[0,1]$, $((γ|_{[0,r]})⋆(γ|_{[r,1]}))(R_r(u))=γ(u)$.
proof: If $u≤r$, use the first-half recovery formula; otherwise $r≤u$ and the second-half recovery formula applies.
-/
theorem path_unitSplit_unitSplitReparam
    {x y : X} (γ : Path x y)
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    ((γ.subpath 0 r).trans (γ.subpath r 1))
        (unitInterval.unitSplitReparam r u hr0 hr1) =
      γ u := by
  by_cases hu : u ≤ r
  · rw [unitInterval.unitSplitReparam_of_le r u hr0 hr1 hu]
    exact path_unitSplit_firstHalf_rescaleLeft γ r u hr0 hu
  · have hru : r ≤ u := le_of_lt (lt_of_not_ge hu)
    rw [unitInterval.unitSplitReparam_of_ge r u hr0 hr1 hru]
    exact path_unitSplit_secondHalf_rescaleRight γ r u hr1 hru

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
The original-path parameter corresponding to a parameter on the split path.
-/
noncomputable def unitInterval.unitSplitOriginalParameter
    (r t : unitInterval) (_hr0 : (0 : ℝ) < r) (_hr1 : (r : ℝ) < 1) :
    unitInterval :=
  if ht : (t : ℝ) ≤ 1 / 2 then
    Set.Icc.convexComb 0 r (unitInterval.doubleOfLeHalf t ht)
  else
    Set.Icc.convexComb r 1
      (unitInterval.doubleSubOneOfHalfLe t (le_of_lt (lt_of_not_ge ht)))

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- On the first half, the inverse split parameter is the corresponding point of the left original subinterval.

%%handwave
name: The inverse split parameter uses the left original interval on the first half
statement: For $0<r<1$ and $t≤1/2$, the original parameter associated with $t$ is $P_r(t)=2tr$.
proof: The definition selects the first branch, the affine parametrization of $[0,r]$ at the doubled parameter $2t$.
-/
theorem unitInterval.unitSplitOriginalParameter_of_le_half
    (r t : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (ht : (t : ℝ) ≤ 1 / 2) :
    unitInterval.unitSplitOriginalParameter r t hr0 hr1 =
      Set.Icc.convexComb 0 r (unitInterval.doubleOfLeHalf t ht) := by
  unfold unitInterval.unitSplitOriginalParameter
  rw [dif_pos ht]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- On the second half, the inverse split parameter is the corresponding point of the right original subinterval.

%%handwave
name: The inverse split parameter uses the right original interval on the second half
statement: For $0<r<1$ and $1/2≤t$, the original parameter is $P_r(t)=r+(2t-1)(1-r)$.
proof: For $t>1/2$ the defining right branch applies. At $t=1/2$, direct affine calculation shows the left and right expressions both equal $r$.
-/
theorem unitInterval.unitSplitOriginalParameter_of_half_le
    (r t : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (ht : (1 / 2 : ℝ) ≤ t) :
    unitInterval.unitSplitOriginalParameter r t hr0 hr1 =
      Set.Icc.convexComb r 1 (unitInterval.doubleSubOneOfHalfLe t ht) := by
  by_cases ht' : (t : ℝ) ≤ 1 / 2
  · have ht_eq : (t : ℝ) = 1 / 2 := le_antisymm ht' ht
    unfold unitInterval.unitSplitOriginalParameter
    rw [dif_pos ht']
    ext
    simp [Set.Icc.convexComb,
      unitInterval.doubleOfLeHalf, unitInterval.doubleSubOneOfHalfLe]
    nlinarith [ht_eq]
  · ext
    unfold unitInterval.unitSplitOriginalParameter
    rw [dif_neg ht']

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The inverse split parameter is monotone.

%%handwave
name: The inverse unit-split parameter is monotone
statement: For $0<r<1$ and $s≤t$, one has $P_r(s)≤P_r(t)$.
proof: Split at $1/2$. Each affine branch is monotone, while in the mixed case the left branch is at most $r$ and the right branch is at least $r$.
-/
theorem unitInterval.unitSplitOriginalParameter_mono
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    {s t : unitInterval} (hst : s ≤ t) :
    unitInterval.unitSplitOriginalParameter r s hr0 hr1 ≤
      unitInterval.unitSplitOriginalParameter r t hr0 hr1 := by
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [unitInterval.unitSplitOriginalParameter_of_le_half r s hr0 hr1 hs,
        unitInterval.unitSplitOriginalParameter_of_le_half r t hr0 hr1 ht]
      change
        ((Set.Icc.convexComb 0 r (unitInterval.doubleOfLeHalf s hs) :
            unitInterval) : ℝ) ≤
          ((Set.Icc.convexComb 0 r (unitInterval.doubleOfLeHalf t ht) :
            unitInterval) : ℝ)
      simp [Set.Icc.convexComb]
      nlinarith [show (0 : ℝ) ≤ r from hr0.le, show (s : ℝ) ≤ t from hst]
    · have ht' : (1 / 2 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
      rw [unitInterval.unitSplitOriginalParameter_of_le_half r s hr0 hr1 hs,
        unitInterval.unitSplitOriginalParameter_of_half_le r t hr0 hr1 ht']
      exact Set.Icc.convexComb_le (show (0 : unitInterval) ≤ r from hr0.le) _
        |>.trans (Set.Icc.le_convexComb (show r ≤ (1 : unitInterval) from hr1.le) _)
  · have hs' : (1 / 2 : ℝ) ≤ s := le_of_lt (lt_of_not_ge hs)
    have ht' : (1 / 2 : ℝ) ≤ t := hs'.trans hst
    rw [unitInterval.unitSplitOriginalParameter_of_half_le r s hr0 hr1 hs',
      unitInterval.unitSplitOriginalParameter_of_half_le r t hr0 hr1 ht']
    change
      ((Set.Icc.convexComb r 1 (unitInterval.doubleSubOneOfHalfLe s hs') :
          unitInterval) : ℝ) ≤
        ((Set.Icc.convexComb r 1 (unitInterval.doubleSubOneOfHalfLe t ht') :
          unitInterval) : ℝ)
    simp [Set.Icc.convexComb]
    nlinarith [show (r : ℝ) ≤ 1 from hr1.le, show (s : ℝ) ≤ t from hst]

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Inverting the split reparameterization recovers the original parameter.

%%handwave
name: The inverse split parameter undoes the split reparameterization
statement: For every $0<r<1$ and $u∈[0,1]$, $P_r(R_r(u))=u$.
proof: Split according to $u≤r$. Substitute the corresponding formulas for $R_r$ and $P_r$, then simplify the affine rescalings.
-/
theorem unitInterval.unitSplitOriginalParameter_unitSplitReparam
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    unitInterval.unitSplitOriginalParameter r
        (unitInterval.unitSplitReparam r u hr0 hr1) hr0 hr1 = u := by
  by_cases hu : u ≤ r
  · rw [unitInterval.unitSplitReparam_of_le r u hr0 hr1 hu]
    rw [unitInterval.unitSplitOriginalParameter_of_le_half]
    · rw [unitInterval.doubleOfLeHalf_firstHalf]
      exact unitInterval.convexCombo_zero_right_rescaleLeft r u hr0 hu
    · exact unitInterval.firstHalf_le_half _
  · have hru : r ≤ u := le_of_lt (lt_of_not_ge hu)
    rw [unitInterval.unitSplitReparam_of_ge r u hr0 hr1 hru]
    rw [unitInterval.unitSplitOriginalParameter_of_half_le]
    · rw [unitInterval.doubleSubOneOfHalfLe_secondHalf]
      exact unitInterval.convexCombo_left_one_rescaleRight r u hr1 hru
    · exact unitInterval.half_le_secondHalf _

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
If a split parameter lies between the split images of two original
parameters, its original inverse lies between those original parameters.

%%handwave
name: Bounds in split coordinates pull back to bounds in original coordinates
statement: For $0<r<1$, if $R_r(a)≤t≤R_r(b)$, then $a≤P_r(t)≤b$.
proof: Apply monotonicity of $P_r$ to both inequalities and replace $P_r(R_r(a))$ and $P_r(R_r(b))$ by $a$ and $b$.
-/
theorem unitInterval.unitSplitOriginalParameter_mem_interval_of_reparam_bounds
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    {a b t : unitInterval}
    (hleft : unitInterval.unitSplitReparam r a hr0 hr1 ≤ t)
    (hright : t ≤ unitInterval.unitSplitReparam r b hr0 hr1) :
    a ≤ unitInterval.unitSplitOriginalParameter r t hr0 hr1 ∧
      unitInterval.unitSplitOriginalParameter r t hr0 hr1 ≤ b := by
  constructor
  · have hmono :=
      unitInterval.unitSplitOriginalParameter_mono r hr0 hr1 hleft
    simpa [unitInterval.unitSplitOriginalParameter_unitSplitReparam] using hmono
  · have hmono :=
      unitInterval.unitSplitOriginalParameter_mono r hr0 hr1 hright
    simpa [unitInterval.unitSplitOriginalParameter_unitSplitReparam] using hmono

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
Evaluating the split path and then inverting its parameter recovers the same
point of the original path.

%%handwave
name: The inverse split parameter recovers the original path point
statement: For every path $γ$, breakpoint $0<r<1$, and $t∈[0,1]$, $((γ|_{[0,r]})⋆(γ|_{[r,1]}))(t)=γ(P_r(t))$.
proof: Split according to $t≤1/2$ and use the appropriate concatenation half together with the left or right formula for $P_r$.
-/
theorem path_unitSplit_originalParameter
    {x y : X} (γ : Path x y)
    (r t : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    ((γ.subpath 0 r).trans (γ.subpath r 1)) t =
      γ (unitInterval.unitSplitOriginalParameter r t hr0 hr1) := by
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [unitInterval.unitSplitOriginalParameter_of_le_half r t hr0 hr1 ht,
      path_trans_apply_of_le_half (γ.subpath 0 r) (γ.subpath r 1) t ht]
    rfl
  · have ht' : (1 / 2 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
    rw [unitInterval.unitSplitOriginalParameter_of_half_le r t hr0 hr1 ht',
      path_trans_apply_of_half_le (γ.subpath 0 r) (γ.subpath r 1) t ht']
    rfl

namespace PathLocalTransitionModelBasedWeakHandoffSkeleton

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

omit [RiemannSurface X] in
/--
Transport a weak handoff skeleton along the inverse of the normalized unit
split reparameterization.  The charts and local transition representatives are
unchanged; only the subdivision parameters are pushed through the split path.
-/
noncomputable def unitSplitReparamSkeleton
    {x y : X} (γ : Path x y) (r : unitInterval)
    (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
        (γ.subpath 0 1)) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
      ((γ.subpath 0 r).trans (γ.subpath r 1)) where
  length := S.length
  length_pos := S.length_pos
  parameterAt := fun i =>
    unitInterval.unitSplitReparam r (S.parameterAt i) hr0 hr1
  parameterAt_zero := by
    rw [S.parameterAt_zero]
    exact unitInterval.unitSplitReparam_zero r hr0 hr1
  parameterAt_last := by
    rw [S.parameterAt_last]
    exact unitInterval.unitSplitReparam_one r hr0 hr1
  parameterAt_mono := by
    intro k
    exact unitInterval.unitSplitReparam_mono r hr0 hr1 (S.parameterAt_mono k)
  centerAt := S.centerAt
  sample_mem_model_domain := by
    intro i
    have hmem :
        γ (S.parameterAt i) ∈
          (localModels.chartAt (S.centerAt i)).domain := by
      simpa [Path.subpath] using S.sample_mem_model_domain i
    simpa [path_unitSplit_unitSplitReparam γ r (S.parameterAt i) hr0 hr1]
      using hmem
  path_segment_mem_model_domain := by
    intro k t ht_left ht_right
    let u := unitInterval.unitSplitOriginalParameter r t hr0 hr1
    have hu :
        S.parameterAt k.castSucc ≤ u ∧ u ≤ S.parameterAt k.succ :=
      unitInterval.unitSplitOriginalParameter_mem_interval_of_reparam_bounds
        r hr0 hr1 ht_left ht_right
    have hmem :
        γ u ∈ (localModels.chartAt (S.centerAt k.castSucc)).domain := by
      simpa [Path.subpath] using
        S.path_segment_mem_model_domain k u hu.1 hu.2
    simpa [u, path_unitSplit_originalParameter γ r t hr0 hr1] using hmem
  terminal_endpoint_mem_domain := by
    simpa [Path.subpath] using S.terminal_endpoint_mem_domain
  transitionAt := by
    intro k
    exact
      localRealMobiusTransitionData_congr rfl rfl
        (by
          simpa [Path.subpath] using
            path_unitSplit_unitSplitReparam γ r (S.parameterAt k.succ) hr0 hr1)
        (S.transitionAt k)
  initialTransition := S.initialTransition

omit [RiemannSurface X] in
/-- Reparameterizing a skeleton across a unit split leaves its terminal chart center unchanged.

%%handwave
name: Unit-split reparameterization preserves the terminal chart
statement: If a continuation skeleton $S$ along $γ|_{[0,1]}$ is transported to the split path through $R_r$, then its terminal chart center is unchanged.
proof: The transported skeleton retains the same ordered charts, so the terminal center is definitionally the same.
-/
@[simp]
theorem unitSplitReparamSkeleton_terminalCenter
    {x y : X} (γ : Path x y) (r : unitInterval)
    (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
        (γ.subpath 0 1)) :
    (S.unitSplitReparamSkeleton γ r hr0 hr1).terminalCenter =
      S.terminalCenter :=
  rfl

omit [RiemannSurface X] in
/-- Reparameterizing a skeleton across a unit split leaves its accumulated terminal Möbius transformation unchanged.

%%handwave
name: Unit-split reparameterization preserves the accumulated terminal transformation
statement: If a continuation skeleton $S$ along $γ|_{[0,1]}$ is transported to the split path through $R_r$, then its accumulated terminal Möbius transformation is unchanged.
proof: Induct over the accumulated products. The transported skeleton has the same initial and successive transition representatives, so every partial product, and hence the terminal product, agrees.
-/
@[simp]
theorem unitSplitReparamSkeleton_terminalMobius
    {x y : X} (γ : Path x y) (r : unitInterval)
    (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
        (γ.subpath 0 1)) :
    (S.unitSplitReparamSkeleton γ r hr0 hr1).terminalMobius =
      S.terminalMobius := by
  let T := S.unitSplitReparamSkeleton γ r hr0 hr1
  have hacc :
      ∀ n : ℕ, n ≤ S.length →
        T.accumulatedMobiusNat n = S.accumulatedMobiusNat n := by
    intro n hn
    induction n with
    | zero =>
        simp [T, unitSplitReparamSkeleton, accumulatedMobiusNat]
    | succ n ih =>
        have hnS : n < S.length := Nat.succ_le_iff.mp hn
        have hnT : n < T.length := by
          simpa [T, unitSplitReparamSkeleton] using hnS
        have hnle : n ≤ S.length := Nat.le_of_lt hnS
        rw [T.accumulatedMobiusNat_succ_of_lt hnT,
          S.accumulatedMobiusNat_succ_of_lt hnS, ih hnle]
        simp [T, unitSplitReparamSkeleton]
  change T.accumulatedMobiusNat T.length = S.accumulatedMobiusNat S.length
  simpa [T, unitSplitReparamSkeleton] using hacc S.length le_rfl

end PathLocalTransitionModelBasedWeakHandoffSkeleton

/--
Normalized unit-interval split boundary: following `γ` from `0` to `r` and
then from `r` to `1` has the same terminal branch data as following `γ`.

The general ordered subpath-merge boundary below reduces to this form by
affine bookkeeping.
-/
def PathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x y : X} (γ : Path x y) (r : unitInterval),
    ∃ (Ssplit :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
          ((γ.subpath 0 r).trans (γ.subpath r 1)))
      (Smerged :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
          (γ.subpath 0 1)),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        Ssplit Smerged

/--
Interior normalized unit-interval split boundary: the same statement as
`PathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple`, but
only for genuine breakpoints `0 < r < 1`.
-/
def PathLocalTransitionBasedWeakHandoffInteriorUnitSplitBranchDataWitnessPrinciple
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x y : X} (γ : Path x y) (r : unitInterval),
    (0 : ℝ) < r → (r : ℝ) < 1 →
    ∃ (Ssplit :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
          ((γ.subpath 0 r).trans (γ.subpath r 1)))
      (Smerged :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
          (γ.subpath 0 1)),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        Ssplit Smerged

omit [RiemannSurface X] in
/--
The interior normalized unit-split witness is unconditional: transport any
finite handoff skeleton for `γ.subpath 0 1` through the explicit split
reparameterization.

%%handwave
name: An interior unit split preserves terminal branch data
statement: For every path $γ$ and breakpoint $0<r<1$, there exist continuation skeletons over $(γ|_{[0,r]})⋆(γ|_{[r,1]})$ and $γ|_{[0,1]}$ with the same terminal chart and accumulated Möbius transformation.
proof: Choose any skeleton over the unsplit path and transport it through the explicit unit-split reparameterization. The preceding invariance formulas identify its terminal chart and accumulated transformation.
-/
theorem pathLocalTransitionBasedWeakHandoffInteriorUnitSplitBranchDataWitnessPrinciple
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    PathLocalTransitionBasedWeakHandoffInteriorUnitSplitBranchDataWitnessPrinciple
      g localModels := by
  intro x y γ r hr0 hr1
  classical
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels (γ.subpath 0 1) with ⟨S⟩
  let T := S.unitSplitReparamSkeleton γ r hr0 hr1
  refine ⟨T, S, ?_⟩
  exact
    { terminalCenter_eq := by
        simp [T]
      terminalMobius_eq := by
        simp [T] }

omit [RiemannSurface X] in
/-- The normalized unit split is direct at the left endpoint.

%%handwave
name: Splitting at zero preserves terminal branch data
statement: For every path $γ$, there are continuation skeletons over $(γ|_{[0,0]})⋆(γ|_{[0,1]})$ and $γ|_{[0,1]}$ with identical terminal branch data.
proof: Choose a skeleton over $γ|_{[0,1]}$ and prepend the constant path $γ|_{[0,0]}$; constant-prefix invariance supplies the branch-data equality.
-/
theorem exists_terminalBranchDataEq_unitSplit_zero
    {x y : X} (γ : Path x y)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    ∃ (Ssplit :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
          ((γ.subpath 0 0).trans (γ.subpath 0 1)))
      (Smerged :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
          (γ.subpath 0 1)),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        Ssplit Smerged := by
  classical
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels (γ.subpath 0 1) with ⟨C⟩
  have hκ : ∀ t : unitInterval, (γ.subpath 0 0) t = γ 0 := by
    intro t
    simp [Path.subpath]
  rcases C.exists_terminalBranchDataEq_after_constantPrefix_trans hκ with
    ⟨S, H⟩
  exact ⟨S, C, H⟩

omit [RiemannSurface X] in
/-- The normalized unit split is direct at the right endpoint.

%%handwave
name: Splitting at one preserves terminal branch data
statement: For every path $γ$, there are continuation skeletons over $(γ|_{[0,1]})⋆(γ|_{[1,1]})$ and $γ|_{[0,1]}$ with identical terminal branch data.
proof: Choose a skeleton over $γ|_{[0,1]}$ and append the constant path $γ|_{[1,1]}$; constant-suffix invariance supplies the branch-data equality.
-/
theorem exists_terminalBranchDataEq_unitSplit_one
    {x y : X} (γ : Path x y)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    ∃ (Ssplit :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
          ((γ.subpath 0 1).trans (γ.subpath 1 1)))
      (Smerged :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ 0) g localModels
          (γ.subpath 0 1)),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        Ssplit Smerged := by
  classical
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels (γ.subpath 0 1) with ⟨C⟩
  have hσ : ∀ t : unitInterval, (γ.subpath 1 1) t = γ 1 := by
    intro t
    simp [Path.subpath]
  rcases C.exists_terminalBranchDataEq_after_constantSuffix_trans hσ with
    ⟨S, H⟩
  exact ⟨S, C, H⟩

omit [RiemannSurface X] in
/--
Once the genuine interior unit-split case is known, the full normalized
unit-split boundary follows from the constant-prefix and constant-suffix
endpoint cases.

%%handwave
name: Interior and endpoint cases give unit-split invariance
statement: If terminal branch data are preserved by splitting every path at each $0<r<1$, then they are preserved by splitting at every $r∈[0,1]$.
proof: Separate the cases $r=0$, $r=1$, and $0<r<1$. Use the constant-prefix lemma, constant-suffix lemma, and the assumed interior principle respectively.
-/
theorem pathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple_of_interior
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hInterior :
      PathLocalTransitionBasedWeakHandoffInteriorUnitSplitBranchDataWitnessPrinciple
        g localModels) :
    PathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple
      g localModels := by
  intro x y γ r
  by_cases h0 : r = 0
  · subst r
    exact exists_terminalBranchDataEq_unitSplit_zero γ
  by_cases h1 : r = 1
  · subst r
    exact exists_terminalBranchDataEq_unitSplit_one γ
  have hr0 : (0 : ℝ) < r := by
    exact lt_of_le_of_ne (unitInterval.nonneg r) (by
      intro h
      exact h0 (Subtype.ext h.symm))
  have hr1 : (r : ℝ) < 1 := by
    exact lt_of_le_of_ne (unitInterval.le_one r) (by
      intro h
      exact h1 (Subtype.ext h))
  exact hInterior γ r hr0 hr1

/--
Generic one-dimensional subpath-merge witness principle.

This is a strong compatibility form retained for older routes.  The sharp
mathematical boundary for the grid proof is the monotone version below; without
order hypotheses this generic statement can include extra loop monodromy.
-/
def PathLocalTransitionBasedWeakHandoffSubpathMergeBranchDataWitnessPrinciple
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x y : X} (γ : Path x y) (t₀ t₁ t₂ : unitInterval),
    ∃ (Ssplit :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ t₀) g localModels
          ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)))
      (Smerged :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ t₀) g localModels
          (γ.subpath t₀ t₂)),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        Ssplit Smerged

/--
Monotone one-dimensional subpath-merge witness principle.

This is the mathematically correct form used by the homotopy-grid route:
continuing along `γ|[t₀,t₁]` and then `γ|[t₁,t₂]` agrees with continuing
along `γ|[t₀,t₂]` when `t₀ ≤ t₁ ≤ t₂`.  Without these order hypotheses the
statement can include extra loop monodromy and is too strong.
-/
def PathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x y : X} (γ : Path x y) (t₀ t₁ t₂ : unitInterval),
    t₀ ≤ t₁ → t₁ ≤ t₂ →
    ∃ (Ssplit :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ t₀) g localModels
          ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)))
      (Smerged :
        PathLocalTransitionModelBasedWeakHandoffSkeleton (γ t₀) g localModels
          (γ.subpath t₀ t₂)),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        Ssplit Smerged

/--
Generic prefixed one-dimensional subpath-merge witness principle.

This is the form needed when the two adjacent subpaths occur after some
already-continued prefix.  It is still purely one-dimensional: the only
geometric change is replacing two consecutive subpaths of the same path by
their merged subpath.
-/
def PathLocalTransitionBasedWeakHandoffPrefixedSubpathMergeValueWitnessPrinciple
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
  Prop :=
  ∀ {x₀ y z : X} (γ : Path y z) (t₀ t₁ t₂ : unitInterval)
    (pref : Path x₀ (γ t₀)),
    ∃ (Ssplit :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (pref.trans ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂))))
      (Smerged :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (pref.trans (γ.subpath t₀ t₂))),
      Ssplit.terminalValue = Smerged.terminalValue

/--
Monotone prefixed one-dimensional subpath-merge witness principle.

This is the ordered version actually needed by chart-grid continuation.  The
prefix may be arbitrary, but the two adjacent subpaths being merged must be an
ordered subdivision of a single interval.
-/
def PathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
  Prop :=
  ∀ {x₀ y z : X} (γ : Path y z) (t₀ t₁ t₂ : unitInterval)
    (pref : Path x₀ (γ t₀)),
    t₀ ≤ t₁ → t₁ ≤ t₂ →
    ∃ (Ssplit :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (pref.trans ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂))))
      (Smerged :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (pref.trans (γ.subpath t₀ t₂))),
      Ssplit.terminalValue = Smerged.terminalValue

omit [RiemannSurface X] in
/--
The general ordered subpath-merge boundary reduces to the normalized split of
a single path at one parameter.

%%handwave
name: Unit-split invariance implies monotone subpath merging
statement: Assume splitting any path once preserves terminal branch data. Then for every path $γ$ and $t_0≤t_1≤t_2$, there are skeletons over $(γ|_{[t_0,t_1]})⋆(γ|_{[t_1,t_2]})$ and $γ|_{[t_0,t_2]}$ with identical terminal branch data.
proof: Express $t_1$ as the affine middle parameter of $[t_0,t_2]$, apply unit-split invariance to $γ|_{[t_0,t_2]}$, and identify its two subpaths with the original adjacent subpaths.
-/
theorem pathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple_of_unitSplit
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hUnit :
      PathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple
        g localModels) :
    PathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple
      g localModels := by
  classical
  intro x y γ t₀ t₁ t₂ ht₀₁ ht₁₂
  let r := unitInterval.middleParameter t₀ t₁ t₂ ht₀₁ ht₁₂
  let η := γ.subpath t₀ t₂
  have hr : t₁ = Set.Icc.convexComb t₀ t₂ r := by
    simpa [r] using
      unitInterval.middleParameter_spec t₀ t₁ t₂ ht₀₁ ht₁₂
  rcases hUnit η r with ⟨Ssplit₀, Smerged₀, H₀⟩
  have h0 : γ t₀ = η 0 := by
    simp [η, Path.subpath]
  have h1 : γ t₂ = η 1 := by
    simp [η, Path.subpath]
  let Ssplit₁ := Ssplit₀.castEndpoints h0 h1
  let Smerged₁ := Smerged₀.castEndpoints h0 h1
  have hsplitPath :
      (((η.subpath 0 r).trans (η.subpath r 1)).cast h0 h1) =
        ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) := by
    ext u
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · rw [Path.cast_coe,
        path_trans_apply_of_le_half (η.subpath 0 r) (η.subpath r 1) u hu,
        path_trans_apply_of_le_half (γ.subpath t₀ t₁) (γ.subpath t₁ t₂) u hu]
      apply congrArg γ
      ext
      simp [hr, Set.Icc.convexComb]
      ring_nf
    · have hu' : (1 / 2 : ℝ) ≤ u := le_of_not_gt (by
        intro hlt
        exact hu hlt.le)
      rw [Path.cast_coe,
        path_trans_apply_of_half_le (η.subpath 0 r) (η.subpath r 1) u hu',
        path_trans_apply_of_half_le (γ.subpath t₀ t₁) (γ.subpath t₁ t₂) u hu']
      apply congrArg γ
      ext
      simp [hr, Set.Icc.convexComb]
      ring_nf
  have hmergedPath :
      ((η.subpath 0 1).cast h0 h1) = γ.subpath t₀ t₂ := by
    ext u
    rw [Path.cast_coe]
    apply congrArg γ
    ext
    simp [Set.Icc.convexComb]
  refine ⟨Ssplit₁.castPath hsplitPath, Smerged₁.castPath hmergedPath, ?_⟩
  exact H₀.castEndpoints h0 h1 |>.castPath hsplitPath hmergedPath

omit [RiemannSurface X] in
/--
The prefixed ordered subpath-merge value witness is not an independent
continuation boundary.

Given the ordered branch-data merge for the two suffix paths, prepend an
arbitrary already-continued prefix by bridging through the actual source chart
of the suffix.  The append formula then shows that both terminal Mobius
products are obtained from the equal suffix terminal products by the same
left factor.

%%handwave
name: Monotone branch-data merging survives a common prefix
statement: Assume adjacent ordered subpaths $γ|_{[t_0,t_1]}$ and $γ|_{[t_1,t_2]}$ can be merged without changing terminal branch data. After any based prefix ending at $γ(t_0)$, there are skeletons over the prefixed split and merged routes with equal terminal values.
proof: Choose a prefix skeleton, bridge its terminal chart to the source chart of the two suffix witnesses, and append the split and merged suffix skeletons. Equal suffix terminal branch data make the two accumulated products differ by the same left factor.
-/
theorem pathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple_of_monotoneSubpathMergeBranchData
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      PathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple
        g localModels) :
    PathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple
      g localModels := by
  classical
  intro x₀ y z γ t₀ t₁ t₂ pref ht₀₁ ht₁₂
  rcases hMerge γ t₀ t₁ t₂ ht₀₁ ht₁₂ with
    ⟨Qsplit, Qmerged, Hsuffix⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels pref with
    ⟨P⟩
  let B :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt P.terminalCenter)
        (localModels.chartAt (γ t₀))
        (γ t₀) :=
    Classical.choice
      (localModels.transition_localRealMobius
        P.terminalCenter (γ t₀) (γ t₀)
        ⟨P.terminal_endpoint_mem_domain,
          localModels.mem_chartAt_domain (γ t₀)⟩)
  let ASplit :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt P.terminalCenter)
        (localModels.chartAt (Qsplit.centerAt 0))
        (γ t₀) :=
    localRealMobiusTransitionData_trans B Qsplit.initialTransition
  let AMerged :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt P.terminalCenter)
        (localModels.chartAt (Qmerged.centerAt 0))
        (γ t₀) :=
    localRealMobiusTransitionData_trans B Qmerged.initialTransition
  let Ssplit := P.appendSuffixSkeleton Qsplit ASplit
  let Smerged := P.appendSuffixSkeleton Qmerged AMerged
  refine ⟨Ssplit, Smerged, ?_⟩
  have hSuffixMobius :
      Qsplit.initialTransition.representative⁻¹ *
          PathLocalTransitionModelBasedWeakHandoffSkeleton.suffixInternalTransitionProduct
            Qsplit Qsplit.length =
        Qmerged.initialTransition.representative⁻¹ *
          PathLocalTransitionModelBasedWeakHandoffSkeleton.suffixInternalTransitionProduct
            Qmerged Qmerged.length := by
    simpa [
      PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalMobius_eq_initial_mul_suffixInternalTransitionProduct
        Qsplit,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalMobius_eq_initial_mul_suffixInternalTransitionProduct
        Qmerged]
      using Hsuffix.terminalMobius_eq
  have hMobius : Ssplit.terminalMobius = Smerged.terminalMobius := by
    dsimp [Ssplit, Smerged, ASplit, AMerged]
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.appendSuffixSkeleton_terminalMobius_eq P Qsplit
        (localRealMobiusTransitionData_trans B Qsplit.initialTransition),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.appendSuffixSkeleton_terminalMobius_eq P Qmerged
        (localRealMobiusTransitionData_trans B Qmerged.initialTransition)]
    calc
      (P.terminalMobius *
            (localRealMobiusTransitionData_trans B Qsplit.initialTransition).representative⁻¹) *
          PathLocalTransitionModelBasedWeakHandoffSkeleton.suffixInternalTransitionProduct
            Qsplit Qsplit.length =
          (P.terminalMobius * B.representative⁻¹) *
            (Qsplit.initialTransition.representative⁻¹ *
              PathLocalTransitionModelBasedWeakHandoffSkeleton.suffixInternalTransitionProduct
                Qsplit Qsplit.length) := by
            simp [localRealMobiusTransitionData_trans_representative,
              mul_assoc]
      _ = (P.terminalMobius * B.representative⁻¹) *
            (Qmerged.initialTransition.representative⁻¹ *
              PathLocalTransitionModelBasedWeakHandoffSkeleton.suffixInternalTransitionProduct
                Qmerged Qmerged.length) := by
            rw [hSuffixMobius]
      _ = (P.terminalMobius *
            (localRealMobiusTransitionData_trans B Qmerged.initialTransition).representative⁻¹) *
          PathLocalTransitionModelBasedWeakHandoffSkeleton.suffixInternalTransitionProduct
            Qmerged Qmerged.length := by
            simp [localRealMobiusTransitionData_trans_representative,
              mul_assoc]
  have hCenter : Ssplit.terminalCenter = Smerged.terminalCenter := by
    dsimp [Ssplit, Smerged]
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.appendSuffixSkeleton_terminalCenter P Qsplit ASplit,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.appendSuffixSkeleton_terminalCenter P Qmerged AMerged,
      Hsuffix.terminalCenter_eq]
  change
    realMobiusRepresentativeAction Ssplit.terminalMobius
        ((localModels.chartAt Ssplit.terminalCenter).toUpperHalfPlane (γ t₂)) =
      realMobiusRepresentativeAction Smerged.terminalMobius
        ((localModels.chartAt Smerged.terminalCenter).toUpperHalfPlane (γ t₂))
  rw [hMobius, hCenter]

omit [RiemannSurface X] in
/--
The top-column path and its reassociated-but-not-merged form have equal
terminal branch data.

This discharges the parenthesization part of the top cut transfer.  The only
remaining top-side move from this intermediate path to `homotopyStripCutPath`
is the genuine subpath merge
`(F.eval a).subpath 0 r₀` followed by `(F.eval a).subpath r₀ r₁`
to `(F.eval a).subpath 0 r₁`.

%%handwave
name: Reassociating the top column route preserves terminal branch data
statement: For every homotopy rectangle, there are continuation skeletons over the reassociated top raw-core route and the original parenthesized top raw-core route with the same terminal chart and accumulated Möbius transformation.
proof: Choose a skeleton over the reassociated path and transport it across associativity of path concatenation; endpoint casts do not alter the terminal branch data.
-/
theorem exists_terminalBranchDataEq_homotopyStripColumnTop_assocPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    ∃ (Sassoc :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripColumnTopAssocPathRawCore F a b r₀ r₁))
      (Scol :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripColumnTopPathRawCore F a b r₀ r₁)),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        Sassoc Scol := by
  classical
  let α := (F.eval a).subpath 0 r₀
  let β := (F.eval a).subpath r₀ r₁
  let δ := (F.evalAt r₁).subpath a b
  let σ := (F.eval b).subpath r₁ 1
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels α with ⟨Sα⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels β with ⟨Sβ⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels δ with ⟨Sδ⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels σ with ⟨Sσ⟩
  have hβsource : β 0 = (F.eval a) r₀ := by
    simpa using β.source
  have hδsource : δ 0 = (F.evalAt r₁) a := by
    exact δ.source
  let Aαβ :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt Sα.terminalCenter)
        (localModels.chartAt (Sβ.centerAt 0))
        ((F.eval a) r₀) :=
    Classical.choice
      (localModels.transition_localRealMobius
        Sα.terminalCenter (Sβ.centerAt 0) ((F.eval a) r₀)
        ⟨by simpa [α] using Sα.terminal_endpoint_mem_domain,
          by
            have hmem : β 0 ∈
                (localModels.chartAt (Sβ.centerAt 0)).domain := by
              simpa [Sβ.parameterAt_zero] using
                Sβ.sample_mem_model_domain (0 : Fin (Sβ.length + 1))
            rw [hβsource] at hmem
            exact hmem⟩)
  let Aβδ :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt Sβ.terminalCenter)
        (localModels.chartAt (Sδ.centerAt 0))
        ((F.evalAt r₁) a) :=
    Classical.choice
      (localModels.transition_localRealMobius
        Sβ.terminalCenter (Sδ.centerAt 0) ((F.evalAt r₁) a)
        ⟨by simpa [β] using Sβ.terminal_endpoint_mem_domain,
          by
            have hmem : δ 0 ∈
                (localModels.chartAt (Sδ.centerAt 0)).domain := by
              simpa [Sδ.parameterAt_zero] using
                Sδ.sample_mem_model_domain (0 : Fin (Sδ.length + 1))
            rw [hδsource] at hmem
            exact hmem⟩)
  rcases
    PathLocalTransitionModelBasedWeakHandoffSkeleton.appendSuffixSkeleton_assoc_terminalBranchDataEq
      Sα Sβ Sδ Aαβ Aβδ with
    ⟨Aassocδ, Aαβδ, Hassoc⟩
  rcases
    Hassoc.exists_terminalBranchDataEq_after_suffixSkeleton_exactAppend
      Sσ with
    ⟨Sassoc, Scol, Hfinal⟩
  exact ⟨Sassoc, Scol, by simpa [homotopyStripColumnTopAssocPathRawCore,
    homotopyStripColumnTopPathRawCore, homotopyRectangleBottomRightPath,
    α, β, δ, σ] using Hfinal⟩

omit [RiemannSurface X] in
/--
Top-column raw cut transfer from the generic subpath-merge boundary.

Reassociation has already been proved exactly; this theorem uses the remaining
one-dimensional merge for `(F.eval a).subpath 0 r₀` followed by
`(F.eval a).subpath r₀ r₁`, then appends the common horizontal piece and
upper suffix.

%%handwave
name: Top-column subpath merging preserves the raw-cut terminal value
statement: Assume arbitrary adjacent subpaths can be merged with equal terminal branch data and fixed-path terminal values are unique. Then for every homotopy rectangle there are skeletons over the decomposed top raw-core route and the raw cut at $r_1$ with equal terminal values.
proof: Reassociate the top route, merge the two adjacent row subpaths at $a$, append the common horizontal and suffix pieces, and use fixed-path uniqueness to identify the independently chosen intermediate skeletons.
-/
theorem exists_terminalValue_eq_homotopyStripColumnTop_rawCutPathRawCore_of_subpathMerge
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      PathLocalTransitionBasedWeakHandoffSubpathMergeBranchDataWitnessPrinciple
        g localModels)
    (hSamePath :
      ∀ {y : X} {path : Path (F (a, 0)) y}
        (S T :
          PathLocalTransitionModelBasedWeakHandoffSkeleton
            (F (a, 0)) g localModels path),
        S.terminalValue = T.terminalValue) :
    ∃ (Scol :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripColumnTopPathRawCore F a b r₀ r₁))
      (Sraw :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripCutPathRawCore F a b r₁)),
      Sraw.terminalValue = Scol.terminalValue := by
  classical
  let γ := F.eval a
  let α := γ.subpath 0 r₀
  let β := γ.subpath r₀ r₁
  let η := γ.subpath 0 r₁
  let δ := (F.evalAt r₁).subpath a b
  let σ := (F.eval b).subpath r₁ 1
  rcases hMerge γ 0 r₀ r₁ with ⟨Ssplit₀, Smerged₀, Hmerge₀⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels δ with ⟨Sδ⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels σ with ⟨Sσ⟩
  rcases
    Hmerge₀.exists_terminalBranchDataEq_after_suffixSkeleton_exactAppend
      Sδ with
    ⟨Ssplit₁, Smerged₁, Hmerge₁⟩
  rcases
    Hmerge₁.exists_terminalBranchDataEq_after_suffixSkeleton_exactAppend
      Sσ with
    ⟨Sassoc, Sraw, Hraw⟩
  rcases
    (by
      simpa [homotopyStripColumnTopAssocPathRawCore,
        homotopyStripColumnTopPathRawCore, homotopyRectangleBottomRightPath,
        γ, α, β, δ, σ] using
        (exists_terminalBranchDataEq_homotopyStripColumnTop_assocPathRawCore
          F a b r₀ r₁
          (g := g) (localModels := localModels))) with
    ⟨Sassoc₀, Scol, Hassoc⟩
  have hSameAssoc :
      Sassoc.terminalValue = Sassoc₀.terminalValue :=
    hSamePath Sassoc Sassoc₀
  exact
    ⟨Scol, Sraw,
      Hraw.terminalValue_eq.symm.trans
        (hSameAssoc.trans Hassoc.terminalValue_eq)⟩

omit [RiemannSurface X] in
/--
Top-column raw cut transfer from the monotone subpath-merge boundary.

This is the form used in the actual grid route, where `r₀ ≤ r₁` comes from
the monotone rectangle subdivision.

%%handwave
name: Monotone top-column merging preserves the raw-cut terminal value
statement: If ordered adjacent subpaths admit equal branch data and $r_0≤r_1$, then there are skeletons over the decomposed top raw-core route and the raw cut at $r_1$ with equal terminal values.
proof: Apply the generic top-column transfer using the monotone merge witness for the ordered parameters $0≤r_0≤r_1$.
-/
theorem exists_terminalValue_eq_homotopyStripColumnTop_rawCutPathRawCore_of_monotoneSubpathMerge
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      PathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple
        g localModels)
    (hSamePath :
      ∀ {y : X} {path : Path (F (a, 0)) y}
        (S T :
          PathLocalTransitionModelBasedWeakHandoffSkeleton
            (F (a, 0)) g localModels path),
        S.terminalValue = T.terminalValue) :
    ∃ (Scol :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripColumnTopPathRawCore F a b r₀ r₁))
      (Sraw :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripCutPathRawCore F a b r₁)),
      Sraw.terminalValue = Scol.terminalValue := by
  classical
  let γ := F.eval a
  let α := γ.subpath 0 r₀
  let β := γ.subpath r₀ r₁
  let δ := (F.evalAt r₁).subpath a b
  let σ := (F.eval b).subpath r₁ 1
  rcases hMerge γ 0 r₀ r₁ (by exact unitInterval.nonneg r₀) hr with
    ⟨Ssplit₀, Smerged₀, Hmerge₀⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels δ with ⟨Sδ⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels σ with ⟨Sσ⟩
  rcases
    Hmerge₀.exists_terminalBranchDataEq_after_suffixSkeleton_exactAppend
      Sδ with
    ⟨Ssplit₁, Smerged₁, Hmerge₁⟩
  rcases
    Hmerge₁.exists_terminalBranchDataEq_after_suffixSkeleton_exactAppend
      Sσ with
    ⟨Sassoc, Sraw, Hraw⟩
  rcases
    (by
      simpa [homotopyStripColumnTopAssocPathRawCore,
        homotopyStripColumnTopPathRawCore, homotopyRectangleBottomRightPath,
        γ, α, β, δ, σ] using
        (exists_terminalBranchDataEq_homotopyStripColumnTop_assocPathRawCore
          F a b r₀ r₁
          (g := g) (localModels := localModels))) with
    ⟨Sassoc₀, Scol, Hassoc⟩
  have hSameAssoc :
      Sassoc.terminalValue = Sassoc₀.terminalValue :=
    hSamePath Sassoc Sassoc₀
  exact
    ⟨Scol, Sraw,
      Hraw.terminalValue_eq.symm.trans
        (hSameAssoc.trans Hassoc.terminalValue_eq)⟩

omit [RiemannSurface X] in
/--
The bottom-column path and its reassociated-but-not-merged form have equal
terminal branch data.

This discharges the parenthesization part of the bottom cut transfer.  The
remaining bottom-side move is the subpath merge
`(F.eval b).subpath r₀ r₁` followed by `(F.eval b).subpath r₁ 1`
to `(F.eval b).subpath r₀ 1`.

%%handwave
name: Reassociating the bottom column route preserves terminal branch data
statement: For every homotopy rectangle, there are skeletons over the reassociated bottom raw-core route and the original bottom raw-core route with the same terminal chart and accumulated Möbius transformation.
proof: Choose a skeleton over one parenthesization and carry it through the associativity homotopy; the endpoint casts preserve its branch data.
-/
theorem exists_terminalBranchDataEq_homotopyStripColumnBottom_assocPathRawCore
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    ∃ (Sassoc :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripColumnBottomAssocPathRawCore F a b r₀ r₁))
      (Scol :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripColumnBottomPathRawCore F a b r₀ r₁)),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        Sassoc Scol := by
  classical
  let α := (F.eval a).subpath 0 r₀
  let δ := (F.evalAt r₀).subpath a b
  let ρ := (F.eval b).subpath r₀ r₁
  let σ := (F.eval b).subpath r₁ 1
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels α with ⟨Sα⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels δ with ⟨Sδ⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels ρ with ⟨Sρ⟩
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels σ with ⟨Sσ⟩
  have hδsource : δ 0 = (F.evalAt r₀) a := by
    exact δ.source
  have hρsource : ρ 0 = (F.eval b) r₀ := by
    simpa using ρ.source
  have hσsource : σ 0 = (F.eval b) r₁ := by
    simpa using σ.source
  let Aαδ :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt Sα.terminalCenter)
        (localModels.chartAt (Sδ.centerAt 0))
        ((F.evalAt r₀) a) :=
    Classical.choice
      (localModels.transition_localRealMobius
        Sα.terminalCenter (Sδ.centerAt 0) ((F.evalAt r₀) a)
        ⟨by simpa [α] using Sα.terminal_endpoint_mem_domain,
          by
            have hmem : δ 0 ∈
                (localModels.chartAt (Sδ.centerAt 0)).domain := by
              simpa [Sδ.parameterAt_zero] using
                Sδ.sample_mem_model_domain (0 : Fin (Sδ.length + 1))
            rw [hδsource] at hmem
            exact hmem⟩)
  let Aδρ :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt Sδ.terminalCenter)
        (localModels.chartAt (Sρ.centerAt 0))
        ((F.eval b) r₀) :=
    Classical.choice
      (localModels.transition_localRealMobius
        Sδ.terminalCenter (Sρ.centerAt 0) ((F.eval b) r₀)
        ⟨by simpa [δ] using Sδ.terminal_endpoint_mem_domain,
          by
            have hmem : ρ 0 ∈
                (localModels.chartAt (Sρ.centerAt 0)).domain := by
              simpa [Sρ.parameterAt_zero] using
                Sρ.sample_mem_model_domain (0 : Fin (Sρ.length + 1))
            rw [hρsource] at hmem
            exact hmem⟩)
  let Aρσ :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt Sρ.terminalCenter)
        (localModels.chartAt (Sσ.centerAt 0))
        ((F.eval b) r₁) :=
    Classical.choice
      (localModels.transition_localRealMobius
        Sρ.terminalCenter (Sσ.centerAt 0) ((F.eval b) r₁)
        ⟨by simpa [ρ] using Sρ.terminal_endpoint_mem_domain,
          by
            have hmem : σ 0 ∈
                (localModels.chartAt (Sσ.centerAt 0)).domain := by
              simpa [Sσ.parameterAt_zero] using
                Sσ.sample_mem_model_domain (0 : Fin (Sσ.length + 1))
            rw [hσsource] at hmem
            exact hmem⟩)
  rcases
    PathLocalTransitionModelBasedWeakHandoffSkeleton.appendSuffixSkeleton_assoc_terminalBranchDataEq
      Sα Sδ Sρ Aαδ Aδρ with
    ⟨Aαδ_ρ, Aα_δρ, Hmid⟩
  let Sαδ := Sα.appendSuffixSkeleton Sδ Aαδ
  rcases
    PathLocalTransitionModelBasedWeakHandoffSkeleton.appendSuffixSkeleton_assoc_terminalBranchDataEq
      Sαδ Sρ Sσ Aαδ_ρ Aρσ with
    ⟨Aleftσ, Aassocσ, Hassoc⟩
  let Acolσ :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt
          ((Sα.appendSuffixSkeleton (Sδ.appendSuffixSkeleton Sρ Aδρ)
            Aα_δρ).terminalCenter))
        (localModels.chartAt (Sσ.centerAt 0))
        ((F.eval b) r₁) :=
    localRealMobiusTransitionData_congr
      (by
        exact congrArg (fun c => localModels.chartAt c)
          Hmid.terminalCenter_eq.symm)
      rfl rfl Aleftσ
  let Hcol :=
    Hmid.appendSuffixSkeleton Sσ Aleftσ Acolσ rfl
  exact
    ⟨Sαδ.appendSuffixSkeleton (Sρ.appendSuffixSkeleton Sσ Aρσ) Aassocσ,
      (Sα.appendSuffixSkeleton (Sδ.appendSuffixSkeleton Sρ Aδρ)
        Aα_δρ).appendSuffixSkeleton Sσ Acolσ,
      by
        have H :
            PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
              (Sαδ.appendSuffixSkeleton (Sρ.appendSuffixSkeleton Sσ Aρσ) Aassocσ)
              ((Sα.appendSuffixSkeleton (Sδ.appendSuffixSkeleton Sρ Aδρ)
                Aα_δρ).appendSuffixSkeleton Sσ Acolσ) :=
          Hassoc.symm.trans Hcol
        simpa [homotopyStripColumnBottomAssocPathRawCore,
          homotopyStripColumnBottomPathRawCore, homotopyRectangleLeftTopPath,
          Sαδ, α, δ, ρ, σ] using H⟩

omit [RiemannSurface X] in
/--
Bottom-column raw cut transfer from the generic prefixed subpath-merge
boundary.

The merge is applied to the two upper-row subpaths after the common lower-left
prefix and horizontal piece have already been continued.

%%handwave
name: Prefixed bottom-column merging preserves the raw-cut terminal value
statement: Assume adjacent subpaths can be merged after an arbitrary prefix without changing terminal value, and fixed-path terminal values are unique. Then the decomposed bottom raw-core route and the raw cut at $r_0$ admit skeletons with equal terminal values.
proof: After the common lower-left and horizontal prefix, merge the two upper-row subpaths from $r_0$ through $r_1$ to $1$, then use reassociation and fixed-path uniqueness to match the constructed skeletons.
-/
theorem exists_terminalValue_eq_homotopyStripColumnBottom_rawCutPathRawCore_of_prefixedSubpathMerge
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      PathLocalTransitionBasedWeakHandoffPrefixedSubpathMergeValueWitnessPrinciple
        g localModels)
    (hSamePath :
      ∀ {y : X} {path : Path (F (a, 0)) y}
        (S T :
          PathLocalTransitionModelBasedWeakHandoffSkeleton
            (F (a, 0)) g localModels path),
        S.terminalValue = T.terminalValue) :
    ∃ (Scol :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripColumnBottomPathRawCore F a b r₀ r₁))
      (Sraw :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripCutPathRawCore F a b r₀)),
      Sraw.terminalValue = Scol.terminalValue := by
  classical
  let γ := F.eval b
  let α := (F.eval a).subpath 0 r₀
  let δ := (F.evalAt r₀).subpath a b
  let ρ := γ.subpath r₀ r₁
  let σ := γ.subpath r₁ 1
  let υ := γ.subpath r₀ 1
  let pref := α.trans δ
  rcases hMerge γ r₀ r₁ 1 pref with ⟨Ssplit, Sraw, Hmerge⟩
  rcases
    (by
      simpa [homotopyStripColumnBottomAssocPathRawCore,
        homotopyStripColumnBottomPathRawCore, homotopyRectangleLeftTopPath,
        γ, α, δ, ρ, σ, pref] using
        (exists_terminalBranchDataEq_homotopyStripColumnBottom_assocPathRawCore
          F a b r₀ r₁
          (g := g) (localModels := localModels))) with
    ⟨Sassoc, Scol, Hassoc⟩
  have hSameAssoc :
      Ssplit.terminalValue = Sassoc.terminalValue :=
    hSamePath Ssplit Sassoc
  exact
    ⟨Scol, Sraw,
      Hmerge.symm.trans (hSameAssoc.trans Hassoc.terminalValue_eq)⟩

omit [RiemannSurface X] in
/--
Bottom-column raw cut transfer from the monotone prefixed subpath-merge
boundary.

This is the ordered form used in the chart-grid route: `r₀ ≤ r₁ ≤ 1`.

%%handwave
name: Monotone prefixed bottom merging preserves the raw-cut terminal value
statement: If ordered adjacent subpaths can be merged after a prefix and $r_0≤r_1$, then the decomposed bottom raw-core route and the raw cut at $r_0$ admit skeletons with equal terminal values.
proof: Apply the prefixed bottom-column transfer to the ordered parameters $r_0≤r_1≤1$.
-/
theorem exists_terminalValue_eq_homotopyStripColumnBottom_rawCutPathRawCore_of_monotonePrefixedSubpathMerge
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      PathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple
        g localModels)
    (hSamePath :
      ∀ {y : X} {path : Path (F (a, 0)) y}
        (S T :
          PathLocalTransitionModelBasedWeakHandoffSkeleton
            (F (a, 0)) g localModels path),
        S.terminalValue = T.terminalValue) :
    ∃ (Scol :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripColumnBottomPathRawCore F a b r₀ r₁))
      (Sraw :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          (F (a, 0)) g localModels
          (homotopyStripCutPathRawCore F a b r₀)),
      Sraw.terminalValue = Scol.terminalValue := by
  classical
  let γ := F.eval b
  let α := (F.eval a).subpath 0 r₀
  let δ := (F.evalAt r₀).subpath a b
  let ρ := γ.subpath r₀ r₁
  let σ := γ.subpath r₁ 1
  let pref := α.trans δ
  rcases hMerge γ r₀ r₁ 1 pref hr (by exact unitInterval.le_one r₁) with
    ⟨Ssplit, Sraw, Hmerge⟩
  rcases
    (by
      simpa [homotopyStripColumnBottomAssocPathRawCore,
        homotopyStripColumnBottomPathRawCore, homotopyRectangleLeftTopPath,
        γ, α, δ, ρ, σ, pref] using
        (exists_terminalBranchDataEq_homotopyStripColumnBottom_assocPathRawCore
          F a b r₀ r₁
          (g := g) (localModels := localModels))) with
    ⟨Sassoc, Scol, Hassoc⟩
  have hSameAssoc :
      Ssplit.terminalValue = Sassoc.terminalValue :=
    hSamePath Ssplit Sassoc
  exact
    ⟨Scol, Sraw,
      Hmerge.symm.trans (hSameAssoc.trans Hassoc.terminalValue_eq)⟩

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
If a homotopy rectangle is contained in a set, then the lower-then-right
rectangle edge path is contained in that set.

%%handwave
name: The lower-right boundary path stays inside a containing set
statement: Let $a≤b$ and $r_0≤r_1$. If $F([a,b]×[r_0,r_1])⊆A$, then every point of the path traversing the rectangle’s lower edge and then its right edge lies in $A$.
proof: Split the concatenated path parameter at $1/2$; on each half, its affine coordinates lie in the stated horizontal and vertical intervals, so the rectangle inclusion applies.
-/
theorem homotopyRectangleBottomRightPath_mem_of_rect_subset
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {s : Set X}
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval | F z ∈ s}) :
    ∀ u, homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈ s := by
  intro u
  have hmem :
      homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
        Set.range (homotopyRectangleBottomRightPath F a b r₀ r₁) :=
    ⟨u, rfl⟩
  have hRange :
      Set.range (homotopyRectangleBottomRightPath F a b r₀ r₁) =
        Set.range ((F.eval a).subpath r₀ r₁) ∪
          Set.range ((F.evalAt r₁).subpath a b) := by
    change
      Set.range
          (((F.eval a).subpath r₀ r₁).trans
            ((F.evalAt r₁).subpath a b)) =
        Set.range ((F.eval a).subpath r₀ r₁) ∪
          Set.range ((F.evalAt r₁).subpath a b)
    exact
      Path.trans_range ((F.eval a).subpath r₀ r₁)
        ((F.evalAt r₁).subpath a b)
  rw [hRange] at hmem
  rcases hmem with hmem | hmem
  · have hSub :
        Set.range ((F.eval a).subpath r₀ r₁) =
          ((⇑(F.eval a)) '' Set.Icc r₀ r₁) :=
      Path.range_subpath_of_le (F.eval a) r₀ r₁ hr
    have hmemImage :
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          ((⇑(F.eval a)) '' Set.Icc r₀ r₁) := by
      rw [← hSub]
      exact hmem
    rcases hmemImage with ⟨v, hv, hEq⟩
    rw [← hEq]
    exact hRect ⟨⟨le_rfl, hab⟩, hv⟩
  · have hSub :
        Set.range ((F.evalAt r₁).subpath a b) =
          ((⇑(F.evalAt r₁)) '' Set.Icc a b) :=
      Path.range_subpath_of_le (F.evalAt r₁) a b hab
    have hmemImage :
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          ((⇑(F.evalAt r₁)) '' Set.Icc a b) := by
      rw [← hSub]
      exact hmem
    rcases hmemImage with ⟨v, hv, hEq⟩
    rw [← hEq]
    exact hRect ⟨hv, ⟨hr, le_rfl⟩⟩

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
If a homotopy rectangle is contained in a set, then the left-then-upper
rectangle edge path is contained in that set.

%%handwave
name: The left-upper boundary path stays inside a containing set
statement: Let $a≤b$ and $r_0≤r_1$. If $F([a,b]×[r_0,r_1])⊆A$, then every point of the path traversing the left edge and then the upper edge lies in $A$.
proof: Split the path at $1/2$ and verify that each affine pair lies in the rectangle before applying the assumed inclusion.
-/
theorem homotopyRectangleLeftTopPath_mem_of_rect_subset
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {s : Set X}
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval | F z ∈ s}) :
    ∀ u, homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈ s := by
  intro u
  have hmem :
      homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
        Set.range (homotopyRectangleLeftTopPath F a b r₀ r₁) :=
    ⟨u, rfl⟩
  have hRange :
      Set.range (homotopyRectangleLeftTopPath F a b r₀ r₁) =
        Set.range ((F.evalAt r₀).subpath a b) ∪
          Set.range ((F.eval b).subpath r₀ r₁) := by
    change
      Set.range
          (((F.evalAt r₀).subpath a b).trans
            ((F.eval b).subpath r₀ r₁)) =
        Set.range ((F.evalAt r₀).subpath a b) ∪
          Set.range ((F.eval b).subpath r₀ r₁)
    exact
      Path.trans_range ((F.evalAt r₀).subpath a b)
        ((F.eval b).subpath r₀ r₁)
  rw [hRange] at hmem
  rcases hmem with hmem | hmem
  · have hSub :
        Set.range ((F.evalAt r₀).subpath a b) =
          ((⇑(F.evalAt r₀)) '' Set.Icc a b) :=
      Path.range_subpath_of_le (F.evalAt r₀) a b hab
    have hmemImage :
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          ((⇑(F.evalAt r₀)) '' Set.Icc a b) := by
      rw [← hSub]
      exact hmem
    rcases hmemImage with ⟨v, hv, hEq⟩
    rw [← hEq]
    exact hRect ⟨hv, ⟨le_rfl, hr⟩⟩
  · have hSub :
        Set.range ((F.eval b).subpath r₀ r₁) =
          ((⇑(F.eval b)) '' Set.Icc r₀ r₁) :=
      Path.range_subpath_of_le (F.eval b) r₀ r₁ hr
    have hmemImage :
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          ((⇑(F.eval b)) '' Set.Icc r₀ r₁) := by
      rw [← hSub]
      exact hmem
    rcases hmemImage with ⟨v, hv, hEq⟩
    rw [← hEq]
    exact hRect ⟨⟨hab, le_rfl⟩, hv⟩

omit [RiemannSurface X] in
/--
A chart-contained homotopy rectangle contains both elementary rectangle edge
paths used in the column move.

%%handwave
name: Both elementary rectangle routes stay in one containing chart
statement: If $F([a,b]×[r_0,r_1])$ lies in the domain of a selected chart, with $a≤b$ and $r_0≤r_1$, then both the lower-right and left-upper rectangle paths lie entirely in that chart domain.
proof: Apply the two boundary-path containment theorems to the selected chart domain.
-/
theorem homotopyRectangle_paths_mem_chart_of_rect_subset
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (c : X)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain}) :
    (∀ u, homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
        (localModels.chartAt c).domain) ∧
      (∀ u, homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
        (localModels.chartAt c).domain) := by
  exact
    ⟨homotopyRectangleBottomRightPath_mem_of_rect_subset
        F a b r₀ r₁ hab hr hRect,
      homotopyRectangleLeftTopPath_mem_of_rect_subset
        F a b r₀ r₁ hab hr hRect⟩

omit [RiemannSurface X] in
/--
The two elementary paths across a chart-contained rectangle give the same
terminal value when appended to the same prefix skeleton whose terminal chart
is that rectangle chart.

%%handwave
name: Two routes across one chart rectangle have the same terminal value
statement: Suppose a prefix skeleton ends in the chart containing $F([a,b]×[r_0,r_1])$. Extending it along the lower-right and left-upper boundary routes yields skeletons whose terminal values are equal.
proof: Both routes remain in the terminal chart. Their extensions keep the same accumulated Möbius transformation and evaluate that same branch formula at their common endpoint $F(b,r_1)$.
-/
theorem exists_terminalExtensionAlongSkeleton_homotopyRectangle_terminalValue_eq
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels (homotopyStripColumnPrefix F a r₀))
    (c : X) (hcenter : S.terminalCenter = c)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain}) :
    ∃ (hBR : ∀ u,
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          (localModels.chartAt S.terminalCenter).domain)
      (hLT : ∀ u,
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          (localModels.chartAt S.terminalCenter).domain),
      (S.terminalExtensionAlongSkeleton
          (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR).terminalValue =
        (S.terminalExtensionAlongSkeleton
          (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT).terminalValue := by
  rcases
    homotopyRectangle_paths_mem_chart_of_rect_subset
      F a b r₀ r₁ hab hr g localModels c hRect with
    ⟨hBRc, hLTc⟩
  let hBR : ∀ u,
      homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
        (localModels.chartAt S.terminalCenter).domain := by
    intro u
    rw [hcenter]
    exact hBRc u
  let hLT : ∀ u,
      homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
        (localModels.chartAt S.terminalCenter).domain := by
    intro u
    rw [hcenter]
    exact hLTc u
  exact
    ⟨hBR, hLT,
      S.terminalExtensionAlongSkeleton_terminalValue_eq_of_same_endpoint
        (homotopyRectangleBottomRightPath F a b r₀ r₁)
        (homotopyRectangleLeftTopPath F a b r₀ r₁) hBR hLT⟩

omit [RiemannSurface X] in
/--
The two elementary paths across a chart-contained rectangle give the same
terminal branch data when appended to the same prefix skeleton whose terminal
chart is that rectangle chart.

%%handwave
name: Two routes across one chart rectangle have identical terminal branch data
statement: Suppose a prefix skeleton has terminal chart $c$ and the homotopy rectangle lies in chart $c$. Its extensions along the lower-right and left-upper boundary paths have the same terminal center and the same accumulated Möbius transformation.
proof: Use rectangle containment to construct both in-chart extensions. Each extension retains the prefix terminal center and transformation, so the two terminal branch data agree.
-/
theorem exists_terminalExtensionAlongSkeleton_homotopyRectangle_terminalBranchDataEq
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {prefPath : Path x₀ (F (a, r₀))}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels prefPath)
    (c : X) (hcenter : S.terminalCenter = c)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain}) :
    ∃ (hBR : ∀ u,
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          (localModels.chartAt S.terminalCenter).domain)
      (hLT : ∀ u,
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          (localModels.chartAt S.terminalCenter).domain),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        (S.terminalExtensionAlongSkeleton
          (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR)
        (S.terminalExtensionAlongSkeleton
          (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT) := by
  rcases
    homotopyRectangle_paths_mem_chart_of_rect_subset
      F a b r₀ r₁ hab hr g localModels c hRect with
    ⟨hBRc, hLTc⟩
  let hBR : ∀ u,
      homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
        (localModels.chartAt S.terminalCenter).domain := by
    intro u
    rw [hcenter]
    exact hBRc u
  let hLT : ∀ u,
      homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
        (localModels.chartAt S.terminalCenter).domain := by
    intro u
    rw [hcenter]
    exact hLTc u
  exact
    ⟨hBR, hLT,
      S.terminalExtensionAlongSkeleton_terminalBranchDataEq_of_same_endpoint
        (homotopyRectangleBottomRightPath F a b r₀ r₁)
        (homotopyRectangleLeftTopPath F a b r₀ r₁) hBR hLT⟩

omit [RiemannSurface X] in
/--
The rectangle terminal branch-data equality survives appending one further
common suffix path, provided the suffix is valid in the two terminal charts
obtained after the two rectangle-edge extensions.

%%handwave
name: A common in-chart suffix preserves rectangle branch-data equality
statement: After extending one prefix skeleton along the two boundary routes of a chart-contained rectangle, suppose a common suffix lies in both resulting terminal charts. Extending both skeletons along that suffix preserves equality of their terminal charts and accumulated transformations.
proof: The middle extensions already have identical terminal branch data. The suffix extension leaves each terminal transformation unchanged and preserves the equal terminal centers.
-/
theorem terminalExtensionAlongSkeleton_homotopyRectangle_suffix_terminalBranchDataEq
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {prefPath : Path x₀ (F (a, r₀))}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels prefPath)
    (hBR : ∀ u,
      homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
        (localModels.chartAt S.terminalCenter).domain)
    (hLT : ∀ u,
      homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
        (localModels.chartAt S.terminalCenter).domain)
    {y : X} (suffix : Path (F (b, r₁)) y)
    (hSuffixBR : ∀ u, suffix u ∈
      (localModels.chartAt
        ((S.terminalExtensionAlongSkeleton
          (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR).terminalCenter)).domain)
    (hSuffixLT : ∀ u, suffix u ∈
      (localModels.chartAt
        ((S.terminalExtensionAlongSkeleton
          (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT).terminalCenter)).domain) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
      ((S.terminalExtensionAlongSkeleton
        (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR).terminalExtensionAlongSkeleton
          suffix hSuffixBR)
      ((S.terminalExtensionAlongSkeleton
        (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT).terminalExtensionAlongSkeleton
          suffix hSuffixLT) := by
  have Hmiddle :
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        (S.terminalExtensionAlongSkeleton
          (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR)
        (S.terminalExtensionAlongSkeleton
          (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT) :=
    S.terminalExtensionAlongSkeleton_terminalBranchDataEq_of_same_endpoint
      (homotopyRectangleBottomRightPath F a b r₀ r₁)
      (homotopyRectangleLeftTopPath F a b r₀ r₁) hBR hLT
  exact
    PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq.terminalExtensionAlong
      Hmiddle suffix hSuffixBR hSuffixLT

omit [RiemannSurface X] in
/--
The rectangle terminal formula equality survives appending one further common
suffix path, provided the suffix is valid in the two terminal charts obtained
after the two rectangle-edge extensions.

This is the flat one-chart suffix step used by the full suffix transport
argument.  The actual upper suffix will be handled by subdividing it into
finitely many such local pieces.

%%handwave
name: A common in-chart suffix preserves the rectangle terminal value
statement: Under the same rectangle and suffix hypotheses, extending the two rectangle-edge skeletons along the common suffix gives equal terminal values.
proof: First obtain equality of the two final terminal branch data, then evaluate the resulting identical branch formulas at their common endpoint.
-/
theorem terminalExtensionAlongSkeleton_homotopyRectangle_suffix_terminalValue_eq
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {prefPath : Path x₀ (F (a, r₀))}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels prefPath)
    (hBR : ∀ u,
      homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
        (localModels.chartAt S.terminalCenter).domain)
    (hLT : ∀ u,
      homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
        (localModels.chartAt S.terminalCenter).domain)
    {y : X} (suffix : Path (F (b, r₁)) y)
    (hSuffixBR : ∀ u, suffix u ∈
      (localModels.chartAt
        ((S.terminalExtensionAlongSkeleton
          (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR).terminalCenter)).domain)
    (hSuffixLT : ∀ u, suffix u ∈
      (localModels.chartAt
        ((S.terminalExtensionAlongSkeleton
          (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT).terminalCenter)).domain) :
    ((S.terminalExtensionAlongSkeleton
        (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR).terminalExtensionAlongSkeleton
          suffix hSuffixBR).terminalValue =
      ((S.terminalExtensionAlongSkeleton
        (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT).terminalExtensionAlongSkeleton
          suffix hSuffixLT).terminalValue := by
  let SBR :=
    S.terminalExtensionAlongSkeleton
      (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR
  let SLT :=
    S.terminalExtensionAlongSkeleton
      (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT
  have hFormula : SBR.terminalFormulaAt y = SLT.terminalFormulaAt y := by
    dsimp [SBR, SLT]
    exact
      S.terminalExtensionAlongSkeleton_terminalFormulaAt_eq_of_same_endpoint
        (homotopyRectangleBottomRightPath F a b r₀ r₁)
        (homotopyRectangleLeftTopPath F a b r₀ r₁) hBR hLT y
  dsimp [SBR, SLT] at hSuffixBR hSuffixLT hFormula ⊢
  exact
    PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalExtensionAlongSkeleton_terminalValue_eq_of_terminalFormulaAt_eq
        (S.terminalExtensionAlongSkeleton
          (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR)
        (S.terminalExtensionAlongSkeleton
          (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT)
        suffix hSuffixBR hSuffixLT hFormula

omit [RiemannSurface X] in
/--
Exact decomposed-column terminal-value witness when the common upper suffix
also stays in the rectangle chart.

This is the fully exact one-chart version of the rectangle move: the output
skeletons live over `homotopyStripColumnTopPath` and
`homotopyStripColumnBottomPath` themselves, using the prefix/suffix cast
normal forms above.

%%handwave
name: A one-chart column with a one-chart suffix has equal route values
statement: Let a prefix skeleton end in chart $c$. If a homotopy rectangle and the common suffix from its upper-right corner lie in chart $c$, then the exact decomposed top and bottom column paths admit continuation skeletons with equal terminal values.
proof: Extend the prefix along the two rectangle boundary routes, append the common suffix inside chart $c$, use equality of the final values, and rewrite the concatenated paths as the exact decomposed column paths.
-/
theorem exists_terminalValue_eq_homotopyStripColumn_oneChartSuffix
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels (homotopyStripColumnPrefix F a r₀))
    (c : X) (hcenter : S.terminalCenter = c)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain})
    (hSuffix :
      ∀ u, homotopyStripColumnSuffix F b r₁ u ∈
        (localModels.chartAt c).domain) :
    ∃ (STop :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnTopPath F a b r₀ r₁))
      (SBottom :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnBottomPath F a b r₀ r₁)),
      STop.terminalValue = SBottom.terminalValue := by
  rcases
    exists_terminalExtensionAlongSkeleton_homotopyRectangle_terminalBranchDataEq
      (S := S) F a b r₀ r₁ hab hr c hcenter hRect with
    ⟨hBR, hLT, Hmiddle⟩
  let suffix := homotopyStripColumnSuffix F b r₁
  let SBR :=
    S.terminalExtensionAlongSkeleton
      (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR
  let SLT :=
    S.terminalExtensionAlongSkeleton
      (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT
  have hSuffixBR : ∀ u, suffix u ∈
      (localModels.chartAt SBR.terminalCenter).domain := by
    intro u
    dsimp [SBR]
    rw [S.terminalExtensionAlongSkeleton_terminalCenter
      (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR, hcenter]
    exact hSuffix u
  have hSuffixLT : ∀ u, suffix u ∈
      (localModels.chartAt SLT.terminalCenter).domain := by
    intro u
    dsimp [SLT]
    rw [S.terminalExtensionAlongSkeleton_terminalCenter
      (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT, hcenter]
    exact hSuffix u
  let STop : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
      (((homotopyStripColumnPrefix F a r₀).trans
          (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans suffix) :=
    SBR.terminalExtensionAlongSkeleton suffix hSuffixBR
  let SBottom : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
      (((homotopyStripColumnPrefix F a r₀).trans
          (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans suffix) :=
    SLT.terminalExtensionAlongSkeleton suffix hSuffixLT
  have hValue : STop.terminalValue = SBottom.terminalValue := by
    dsimp [STop, SBottom, SBR, SLT]
    exact
      (PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq.terminalExtensionAlong
        Hmiddle suffix hSuffixBR hSuffixLT).terminalValue_eq
  rw [homotopyStripColumnTopPath_eq_prefix_rectangle_suffix,
    homotopyStripColumnBottomPath_eq_prefix_rectangle_suffix]
  exact ⟨STop, SBottom, hValue⟩

omit [RiemannSurface X] in
/--
Exact decomposed-column terminal-value witness with a componentwise suffix
skeleton.

This is the exact-path version of the componentwise suffix route: the suffix
may be subdivided into many selected-chart pieces, but the resulting top and
bottom skeletons live over the honest decomposed column paths, not merely
homotopic reparameterizations.

%%handwave
name: A chart rectangle remains interchangeable before an arbitrary continued suffix
statement: Let a prefix skeleton end in chart $c$, let the homotopy rectangle lie in chart $c$, and let an arbitrary finite continuation skeleton cover the common suffix. Then the exact decomposed top and bottom column paths admit skeletons with equal terminal values.
proof: The two rectangle-edge extensions have identical terminal branch data. Transport that equality component by component along the given suffix skeleton, then use the path associativity identities to obtain skeletons on the exact top and bottom routes.
-/
theorem exists_terminalValue_eq_homotopyStripColumn_suffixSkeleton
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels (homotopyStripColumnPrefix F a r₀))
    (c : X) (hcenter : S.terminalCenter = c)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain})
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton
        (F (b, r₁)) g localModels
          (homotopyStripColumnSuffix F b r₁)) :
    ∃ (STop :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnTopPath F a b r₀ r₁))
      (SBottom :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnBottomPath F a b r₀ r₁)),
      STop.terminalValue = SBottom.terminalValue := by
  rcases
    exists_terminalExtensionAlongSkeleton_homotopyRectangle_terminalBranchDataEq
      (S := S) F a b r₀ r₁ hab hr c hcenter hRect with
    ⟨hBR, hLT, Hmiddle⟩
  rcases Hmiddle.exists_terminalValue_eq_after_suffixSkeleton_exactAppend C with
    ⟨STop, SBottom, hValue⟩
  rw [homotopyStripColumnTopPath_eq_prefix_rectangle_suffix,
    homotopyStripColumnBottomPath_eq_prefix_rectangle_suffix]
  exact ⟨STop, SBottom, hValue⟩

omit [RiemannSurface X] in
/--
Exact decomposed-column terminal-value witness in the one-chart case, with
the prefix skeleton chosen automatically.

The prefix continuation may end in any selected chart.  We first perform a
terminal chart change to the rectangle chart, then apply
`exists_terminalValue_eq_homotopyStripColumn_oneChartSuffix`.

%%handwave
name: A one-chart column and suffix admit equal-valued continuations
statement: If a homotopy rectangle and its common suffix lie in one selected chart $c$, then the decomposed top and bottom column paths admit continuation skeletons with equal terminal values, without a prescribed prefix skeleton.
proof: Choose a continuation skeleton along the common prefix, change its terminal chart to $c$ at the rectangle’s initial corner, and apply the one-chart rectangle-and-suffix comparison.
-/
theorem exists_terminalValue_eq_homotopyStripColumn_oneChartSuffix_unconditional
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (c : X)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain})
    (hSuffix :
      ∀ u, homotopyStripColumnSuffix F b r₁ u ∈
        (localModels.chartAt c).domain) :
    ∃ (STop :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnTopPath F a b r₀ r₁))
      (SBottom :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnBottomPath F a b r₀ r₁)),
      STop.terminalValue = SBottom.terminalValue := by
  classical
  let pref := homotopyStripColumnPrefix F a r₀
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels pref with
    ⟨S₀⟩
  have hc : F (a, r₀) ∈ (localModels.chartAt c).domain :=
    hRect ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hr⟩⟩
  let A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S₀.terminalCenter)
        (localModels.chartAt c)
        (F (a, r₀)) :=
    Classical.choice
      (localModels.transition_localRealMobius S₀.terminalCenter c
        (F (a, r₀)) ⟨S₀.terminal_endpoint_mem_domain, hc⟩)
  let S := S₀.terminalChartChangeSkeleton c hc A
  have hcenter : S.terminalCenter = c := by
    exact S₀.terminalChartChangeSkeleton_terminalCenter c hc A
  exact
    exists_terminalValue_eq_homotopyStripColumn_oneChartSuffix
      F a b r₀ r₁ hab hr S c hcenter hRect hSuffix

omit [RiemannSurface X] in
/--
Exact decomposed-column terminal-value witness for the terminal column
`r₁ = 1`.

Here the common suffix is constant at the endpoint, so it is controlled by
the same chart as the rectangle.

%%handwave
name: The final column has equal-valued top and bottom continuations
statement: If $r_1=1$ and the homotopy rectangle $[a,b]×[r_0,1]$ lies in one selected chart, then the decomposed top and bottom routes admit continuation skeletons with equal terminal values.
proof: At $r_1=1$ the common suffix is constant at the homotopy endpoint, hence lies in the rectangle chart. Apply the unconditional one-chart suffix comparison.
-/
theorem exists_terminalValue_eq_homotopyStripColumn_lastSuffix_unconditional
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁) (hr₁ : r₁ = 1)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (c : X)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain}) :
    ∃ (STop :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnTopPath F a b r₀ r₁))
      (SBottom :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnBottomPath F a b r₀ r₁)),
      STop.terminalValue = SBottom.terminalValue := by
  have hx : x ∈ (localModels.chartAt c).domain := by
    have hpoint : F (b, (1 : unitInterval)) ∈
        (localModels.chartAt c).domain := by
      have hmem : (b, (1 : unitInterval)) ∈
          Set.Icc a b ×ˢ Set.Icc r₀ r₁ := by
        constructor
        · exact ⟨hab, le_rfl⟩
        · rw [hr₁]
          exact ⟨unitInterval.le_one r₀, le_rfl⟩
      exact hRect hmem
    simpa using hpoint
  have hSuffix :
      ∀ u, homotopyStripColumnSuffix F b r₁ u ∈
        (localModels.chartAt c).domain := by
    intro u
    subst r₁
    simpa [homotopyStripColumnSuffix, Path.subpath] using hx
  exact
    exists_terminalValue_eq_homotopyStripColumn_oneChartSuffix_unconditional
      F a b r₀ r₁ hab hr c hRect hSuffix

omit [RiemannSurface X] in
/--
The rectangle branch-data equality survives an arbitrary finitely
subdivided common suffix.

The suffix is represented by its own based weak handoff skeleton.  This is
the componentwise version of the one-chart suffix lemma above: after the two
rectangle edge extensions have the same terminal branch data, finite suffix
transport moves that equality across every suffix segment.

%%handwave
name: Rectangle branch equality transports through a finite suffix skeleton
statement: Let a prefix skeleton end in chart $c$, let the rectangle lie in $c$, and let a finite continuation skeleton cover a common suffix from $F(b,r_1)$ to $y$. Then there exist based paths to $y$ and skeletons along them with identical terminal chart and accumulated Möbius transformation.
proof: Construct the two in-chart rectangle-edge extensions with equal branch data, then transport that equality through every component of the given suffix skeleton, including the necessary endpoint casts.
-/
theorem exists_terminalBranchDataEq_after_homotopyRectangle_suffixSkeleton
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {prefPath : Path x₀ (F (a, r₀))}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels prefPath)
    (c : X) (hcenter : S.terminalCenter = c)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain})
    {y : X} {suffix : Path (F (b, r₁)) y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton
        (F (b, r₁)) g localModels suffix) :
    ∃ (pBR pLT : Path x₀ y)
      (SBR :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels pBR)
      (SLT :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels pLT),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        SBR SLT := by
  rcases
    exists_terminalExtensionAlongSkeleton_homotopyRectangle_terminalBranchDataEq
      (S := S) F a b r₀ r₁ hab hr c hcenter hRect with
    ⟨hBR, hLT, Hmiddle⟩
  exact
    Hmiddle.exists_terminalBranchDataEq_after_suffixSkeleton_castEndpoints C

omit [RiemannSurface X] in
/--
The rectangle branch-data equality survives an arbitrary finitely
subdivided common suffix, with path homotopy bookkeeping.

The transported upper and lower paths are homotopic to the corresponding
rectangle-edge concatenations followed by the whole suffix.

%%handwave
name: Finite suffix transport retains the intended path homotopy classes
statement: Under the rectangle and suffix hypotheses, there are equal-branch-data skeletons on paths $p_{BR},p_{LT}:x_0⇝y$ such that $p_{BR}$ is homotopic to the prefix followed by the lower-right edge and suffix, while $p_{LT}$ is homotopic to the prefix followed by the left-upper edge and suffix.
proof: Start with equal branch data after the two rectangle edges and apply componentwise suffix transport with its concatenation and endpoint-cast homotopies recorded.
-/
theorem exists_terminalBranchDataEq_after_homotopyRectangle_suffixSkeleton_with_homotopy
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {prefPath : Path x₀ (F (a, r₀))}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels prefPath)
    (c : X) (hcenter : S.terminalCenter = c)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain})
    {y : X} {suffix : Path (F (b, r₁)) y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton
        (F (b, r₁)) g localModels suffix) :
    ∃ (pBR pLT : Path x₀ y)
      (SBR :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels pBR)
      (SLT :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels pLT),
      PathLocalTransitionModelBasedWeakHandoffSkeleton.TerminalBranchDataEq
        SBR SLT ∧
        pBR.Homotopic
          ((prefPath.trans
              (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans suffix) ∧
        pLT.Homotopic
          ((prefPath.trans
              (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans suffix) := by
  rcases
    exists_terminalExtensionAlongSkeleton_homotopyRectangle_terminalBranchDataEq
      (S := S) F a b r₀ r₁ hab hr c hcenter hRect with
    ⟨hBR, hLT, Hmiddle⟩
  exact
    Hmiddle.exists_terminalBranchDataEq_after_suffixSkeleton_castEndpoints_with_homotopy C

omit [RiemannSurface X] in
/--
Terminal-value form of
`exists_terminalBranchDataEq_after_homotopyRectangle_suffixSkeleton_with_homotopy`.

%%handwave
name: Finite suffix transport gives equal values in the intended path classes
statement: Under the rectangle and suffix hypotheses, there are skeletons with equal terminal values on paths homotopic respectively to the prefix–lower-right–suffix and prefix–left-upper–suffix routes.
proof: Use the branch-data form with path-homotopy bookkeeping and forget the equal terminal center and transformation after extracting the implied terminal-value equality.
-/
theorem exists_terminalValue_eq_after_homotopyRectangle_suffixSkeleton_with_homotopy
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {prefPath : Path x₀ (F (a, r₀))}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels prefPath)
    (c : X) (hcenter : S.terminalCenter = c)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain})
    {y : X} {suffix : Path (F (b, r₁)) y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton
        (F (b, r₁)) g localModels suffix) :
    ∃ (pBR pLT : Path x₀ y)
      (SBR :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels pBR)
      (SLT :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels pLT),
      SBR.terminalValue = SLT.terminalValue ∧
        pBR.Homotopic
          ((prefPath.trans
              (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans suffix) ∧
        pLT.Homotopic
          ((prefPath.trans
              (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans suffix) := by
  rcases
    exists_terminalBranchDataEq_after_homotopyRectangle_suffixSkeleton_with_homotopy
      F a b r₀ r₁ hab hr S c hcenter hRect C with
    ⟨pBR, pLT, SBR, SLT, H, hpBR, hpLT⟩
  exact ⟨pBR, pLT, SBR, SLT, H.terminalValue_eq, hpBR, hpLT⟩

omit [RiemannSurface X] in
/--
Terminal-value form of
`exists_terminalBranchDataEq_after_homotopyRectangle_suffixSkeleton`.

%%handwave
name: Finite suffix transport gives equal terminal values
statement: Under the rectangle and suffix hypotheses, there exist two based paths to the suffix endpoint and continuation skeletons along them whose terminal values are equal.
proof: Apply componentwise suffix transport to obtain equal terminal branch data and retain only the resulting equality of terminal values.
-/
theorem exists_terminalValue_eq_after_homotopyRectangle_suffixSkeleton
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {prefPath : Path x₀ (F (a, r₀))}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton
      x₀ g localModels prefPath)
    (c : X) (hcenter : S.terminalCenter = c)
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval |
          F z ∈ (localModels.chartAt c).domain})
    {y : X} {suffix : Path (F (b, r₁)) y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton
        (F (b, r₁)) g localModels suffix) :
    ∃ (pBR pLT : Path x₀ y)
      (SBR :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels pBR)
      (SLT :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels pLT),
      SBR.terminalValue = SLT.terminalValue := by
  rcases
    exists_terminalBranchDataEq_after_homotopyRectangle_suffixSkeleton
      F a b r₀ r₁ hab hr S c hcenter hRect C with
    ⟨pBR, pLT, SBR, SLT, H⟩
  exact ⟨pBR, pLT, SBR, SLT, H.terminalValue_eq⟩

/--
One rectangle column in a homotopy strip can be replaced by an elementary
grid-move walk between adjacent cut paths.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (i m : ℕ) →
      (∃ c : X,
        Set.Icc (t i) (t (i + 1)) ×ˢ
            Set.Icc (t m) (t (m + 1)) ⊆
          {z : unitInterval × unitInterval |
            F z ∈ (localModels.chartAt c).domain}) →
      Nonempty
        (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
          basedWeakHandoffAlong
          (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1)))
          (homotopyStripCutPath F (t i) (t (i + 1)) (t m)))

/--
One horizontal strip of a chart-subdivided path homotopy can be replaced by
an elementary grid-move walk.

This is the local sweep form of the remaining monodromy boundary: after
fixing a homotopy-time strip `[t i, t (i+1)]`, the path-parameter direction is
already covered by chart rectangles, and the output is the finite walk from
the lower row `F.eval (t i)` to the upper row `F.eval (t (i+1))`.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyChartStripMovePrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (∃ N, ∀ n ≥ N, t n = 1) →
      (i : ℕ) →
      (∀ m,
        ∃ c : X,
          Set.Icc (t i) (t (i + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval |
              F z ∈ (localModels.chartAt c).domain}) →
      Nonempty
        (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
          basedWeakHandoffAlong (F.eval (t i)) (F.eval (t (i + 1))))

omit [RiemannSurface X] in
/--
Compactness of the path-homotopy square gives a finite rectangular
subdivision whose every rectangle is contained in one selected local-model
domain.

This is the purely topological part of the homotopy-grid argument.  The
remaining analytic-continuation content is to turn replacement of one small
rectangle, with the common prefix and suffix held fixed, into an elementary
terminal-formula-preserving move.

%%handwave
name: A path homotopy admits a finite monotone chart grid
statement: For every endpoint-fixed homotopy $F:[0,1]^2→X$, there is a monotone sequence $(t_n)$ with $t_0=0$, eventually $t_n=1$, such that every rectangle $[t_n,t_{n+1}]×[t_m,t_{m+1}]$ is mapped into one selected local-model chart domain.
proof: The selected chart domains form an open cover of $X$. Apply compact rectangular subdivision of the homotopy square subordinate to this cover.
-/
theorem pathHomotopy_exists_monotone_localTransition_chart_grid
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
      Monotone t ∧
      (∃ N, ∀ n ≥ N, t n = 1) ∧
      ∀ n m,
        ∃ c : X,
          Set.Icc (t n) (t (n + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval |
              F z ∈ (localModels.chartAt c).domain} := by
  classical
  let U : X → Set X :=
    fun c => (localModels.chartAt c).domain
  have hUopen : ∀ c, IsOpen (U c) := by
    intro c
    exact (localModels.chartAt c).isOpen_domain
  have hUcover : Set.univ ⊆ ⋃ c : X, U c := by
    intro z _hz
    refine Set.mem_iUnion.mpr ⟨z, ?_⟩
    exact localModels.mem_chartAt_domain z
  rcases
    AnalyticContinuation.exists_monotone_rectangular_subdivision_subordinate_to_open_cover
      F F.continuous U hUopen hUcover with
    ⟨t, ht0, htmono, htEventually, htRect⟩
  exact ⟨t, ht0, htmono, htEventually, htRect⟩

omit [RiemannSurface X] in
/--
Endpoint-fixed homotopic paths admit a finite chart grid for any chosen
representing homotopy.

%%handwave
name: Homotopic paths admit a finite monotone chart grid
statement: For endpoint-fixed homotopic paths $p,q:x_0⇝x$, a chosen representing homotopy admits a monotone eventually constant subdivision whose every grid rectangle lies in one selected local-model chart.
proof: Apply the finite chart-grid theorem to a representative of the endpoint-fixed path homotopy.
-/
theorem pathHomotopic_exists_monotone_localTransition_chart_grid
    {x₀ x : X} {p q : Path x₀ x}
    (hpq : Path.Homotopic p q)
    (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
      Monotone t ∧
      (∃ N, ∀ n ≥ N, t n = 1) ∧
      ∀ n m,
        ∃ c : X,
          Set.Icc (t n) (t (n + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval |
              hpq.some z ∈ (localModels.chartAt c).domain} :=
  pathHomotopy_exists_monotone_localTransition_chart_grid hpq.some g localModels

/--
Chart-grid local replacement principle for based weak handoff continuation.

This is the sharpened remaining monodromy boundary after compactness of the
homotopy square has been discharged: given an endpoint-fixed homotopy already
subdivided so that each rectangle lies in a selected local-model domain, build
the finite elementary move walk by replacing one small rectangle at a time
while keeping the common prefix and suffix fixed.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyChartGridMovePrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (∃ N, ∀ n ≥ N, t n = 1) →
      (∀ n m,
        ∃ c : X,
          Set.Icc (t n) (t (n + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval |
              F z ∈ (localModels.chartAt c).domain}) →
      Nonempty
        (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
          basedWeakHandoffAlong p q)

omit [RiemannSurface X] in
/--
Concatenate a finite list of homotopy-strip walks.

%%handwave
name: A finite sequence of strip walks concatenates
statement: Let $F$ be a path homotopy and $(t_i)$ a subdivision. If for each $i<N$ there is an elementary-move walk from the row $F(t_i,-)$ to $F(t_{i+1},-)$, then there is such a walk from $F(t_0,-)$ to $F(t_N,-)$.
proof: Induct on $N$. Use the empty walk at $N=0$ and append the final strip walk to the induction hypothesis.
-/
theorem pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk_rows
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (t : ℕ → unitInterval) :
    ∀ N : ℕ,
      (∀ i, i < N →
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
            basedWeakHandoffAlong (F.eval (t i)) (F.eval (t (i + 1))))) →
      Nonempty
        (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
          basedWeakHandoffAlong (F.eval (t 0)) (F.eval (t N)))
  | 0, _ =>
      ⟨PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk.refl
        (F.eval (t 0))⟩
  | N + 1, hRows => by
      rcases
        pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk_rows
          F t N
          (fun i hi => hRows i (Nat.lt_trans hi (Nat.lt_succ_self N))) with
        ⟨W₀⟩
      rcases hRows N (Nat.lt_succ_self N) with ⟨W₁⟩
      exact ⟨W₀.trans W₁⟩

omit [RiemannSurface X] in
/--
Concatenate a finite descending list of column moves inside one homotopy
strip, from the cut at `t N` down to the cut at `t 0`.

%%handwave
name: A finite descending sequence of column walks concatenates
statement: Fix a homotopy strip $[t_i,t_{i+1}]$. If for every $m<N$ there is a move walk from the cut at $t_{m+1}$ down to the cut at $t_m$, then there is a walk from the cut at $t_N$ down to the cut at $t_0$.
proof: Induct on $N$, placing the last column walk before the accumulated walk through the preceding columns.
-/
theorem pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk_stripColumns
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (t : ℕ → unitInterval) (i : ℕ) :
    ∀ N : ℕ,
      (∀ m, m < N →
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
            basedWeakHandoffAlong
            (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1)))
            (homotopyStripCutPath F (t i) (t (i + 1)) (t m)))) →
      Nonempty
        (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
          basedWeakHandoffAlong
          (homotopyStripCutPath F (t i) (t (i + 1)) (t N))
          (homotopyStripCutPath F (t i) (t (i + 1)) (t 0)))
  | 0, _ =>
      ⟨PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk.refl
        (homotopyStripCutPath F (t i) (t (i + 1)) (t 0))⟩
  | N + 1, hColumns => by
      rcases hColumns N (Nat.lt_succ_self N) with ⟨W₀⟩
      rcases
        pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk_stripColumns
          F t i N
          (fun m hm => hColumns m (Nat.lt_trans hm (Nat.lt_succ_self N))) with
        ⟨W₁⟩
      exact ⟨W₀.trans W₁⟩

omit [RiemannSurface X] in
/--
Column moves across the rectangle subdivision imply the one-strip replacement
principle.

%%handwave
name: Column replacement yields replacement of an entire homotopy strip
statement: Suppose every chart-contained grid rectangle gives a move walk between its adjacent cuts. For a monotone subdivision eventually equal to $1$, each horizontal strip then gives a move walk from its lower row to its upper row.
proof: Choose $N$ with $t_N=1$, build and concatenate the column walks from the terminal cut down to $t_0=0$, and identify the endpoint cuts with the two boundary rows.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripMovePrinciple_of_columnMovePrinciple
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (hColumn :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple
        x₀ g localModels basedWeakHandoffAlong) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripMovePrinciple
      x₀ g localModels basedWeakHandoffAlong := by
  intro x p q F t ht0 htmono htEventually i hStrip
  rcases htEventually with ⟨N, hN⟩
  have hColumns :
      ∀ m, m < N →
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
            basedWeakHandoffAlong
            (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1)))
            (homotopyStripCutPath F (t i) (t (i + 1)) (t m))) := by
    intro m _hm
    exact hColumn F t ht0 htmono i m (hStrip m)
  rcases
    pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk_stripColumns
      (basedWeakHandoffAlong := basedWeakHandoffAlong) F t i N hColumns with
    ⟨W⟩
  have hStart :
      homotopyStripCutPath F (t i) (t (i + 1)) (t N) =
        F.eval (t i) := by
    rw [hN N le_rfl]
    exact homotopyStripCutPath_one F (t i) (t (i + 1))
  have hEnd :
      homotopyStripCutPath F (t i) (t (i + 1)) (t 0) =
        F.eval (t (i + 1)) := by
    rw [ht0]
    exact homotopyStripCutPath_zero F (t i) (t (i + 1))
  exact ⟨W.cast hStart.symm hEnd.symm⟩

omit [RiemannSurface X] in
/--
The strip-move principle implies the chart-grid local replacement principle.
All remaining mathematics is now local to one homotopy strip; the passage from
strips to the full homotopy square is finite concatenation.

%%handwave
name: Strip replacement yields replacement across the full homotopy grid
statement: Suppose every chart-subdivided horizontal strip gives a move walk between its two boundary rows. Then any finite chart grid for an endpoint-fixed homotopy gives a move walk from the source path $p$ to the target path $q$.
proof: Choose $N$ after which $t_N=1$, obtain a walk for every strip $i<N$, concatenate the row walks, and identify $F(t_0,-)$ and $F(t_N,-)$ with $p$ and $q$.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartGridMovePrinciple_of_stripMovePrinciple
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (hStrip :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripMovePrinciple
        x₀ g localModels basedWeakHandoffAlong) :
  PathLocalTransitionBasedWeakHandoffHomotopyChartGridMovePrinciple
      x₀ g localModels basedWeakHandoffAlong := by
  intro x p q F t ht0 htmono htEventually htRect
  have htEventually' : ∃ N, ∀ n ≥ N, t n = 1 := htEventually
  rcases htEventually with ⟨N, hN⟩
  have hRows :
      ∀ i, i < N →
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk
            basedWeakHandoffAlong (F.eval (t i)) (F.eval (t (i + 1)))) := by
    intro i _hi
    exact hStrip F t ht0 htmono htEventually' i (fun m => htRect i m)
  rcases
    pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk_rows
      (basedWeakHandoffAlong := basedWeakHandoffAlong) F t N hRows with
    ⟨W⟩
  have hStart : F.eval (t 0) = p := by
    rw [ht0]
    exact F.eval_zero
  have hEnd : F.eval (t N) = q := by
    rw [hN N le_rfl]
    exact F.eval_one
  exact ⟨W.cast hStart.symm hEnd.symm⟩

/--
The chart-grid local replacement principle implies the existing elementary
homotopy-grid boundary.
-/
def pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple_of_homotopyChartGridMovePrinciple
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (hChartGrid :
      PathLocalTransitionBasedWeakHandoffHomotopyChartGridMovePrinciple
        x₀ g localModels basedWeakHandoffAlong) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
      x₀ g localModels basedWeakHandoffAlong := by
  intro x p q hpq
  rcases pathHomotopic_exists_monotone_localTransition_chart_grid
      hpq g localModels with
    ⟨t, ht0, htmono, htEventually, htRect⟩
  exact hChartGrid hpq.some t ht0 htmono htEventually htRect

/--
Chart-controlled grid walks imply elementary grid-move walks.
-/
def pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple_of_fixedChartGridMoveWalkPrinciple
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (hFixed :
      PathLocalTransitionBasedWeakHandoffFixedChartGridMoveWalkPrinciple
        x₀ g localModels basedWeakHandoffAlong) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
      x₀ g localModels basedWeakHandoffAlong := by
  intro x p q hpq
  rcases hFixed hpq with ⟨W⟩
  exact ⟨W.toElementaryGridMoveWalk⟩

/--
%%handwave
name:
  Homotopy-grid invariance of analytic continuation
statement:
  Fix a local hyperbolic branch at $x_0$. If two paths
  $\gamma_0,\gamma_1:[0,1]\to X$ have the same endpoints and are homotopic
  relative to those endpoints, their chosen finite continuation chains can be
  joined by a finite sequence of elementary grid moves, each preserving the
  terminal branch formula.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
    Nonempty
      (PathLocalTransitionBasedWeakHandoffHomotopyGridWalk
        basedWeakHandoffAlong p q)

/--
Elementary grid-move walks imply the coarser finite homotopy-grid walk
principle.
-/
def pathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple_of_elementaryGridMoveWalkPrinciple
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (hElementary :
      PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
        x₀ g localModels basedWeakHandoffAlong) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple
      x₀ g localModels basedWeakHandoffAlong := by
  intro x p q hpq
  rcases hElementary hpq with ⟨W⟩
  exact ⟨W.toHomotopyGridWalk⟩

/--
The terminal branch obtained by choosing a fresh handoff skeleton along the
local terminal-sheet extension agrees with the old terminal branch extended
inside that sheet.
-/
def PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Prop :=
  ∀ {x : X} (p : Path x₀ x)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ (basedWeakHandoffAlong p).terminalSheet),
      (basedWeakHandoffAlong
          (p.trans ((basedWeakHandoffAlong p).terminalSheetPathInSet hy'))).terminalFormulaAt
          (PathHomotopyUniversalCover.endpoint y') =
        (basedWeakHandoffAlong p).terminalFormulaAt
          (PathHomotopyUniversalCover.endpoint y')

/--
Agreement data saying that the chosen skeleton for a terminal-sheet local
extension has kept the same terminal local model and accumulated Mobius
representative.

This is the geometric content behind terminal-sheet local extension: append a
path inside the terminal chart and choose the terminal self-transition by the
identity, so the terminal branch formula does not change.
-/
structure PathLocalTransitionModelBasedWeakHandoffTerminalExtensionAgreement
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet)
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
        (p.trans (S.terminalSheetPathInSet hy'))) where
  /-- The extended skeleton ends in the same terminal chart. -/
  terminalCenter_eq : T.terminalCenter = S.terminalCenter
  /-- The extended skeleton has the same accumulated terminal Mobius representative. -/
  terminalMobius_eq : T.terminalMobius = S.terminalMobius

/--
PSL-level terminal-extension agreement data.

For the PSL-valued continuation route, exact equality of the chosen
`SL(2, ℝ)` representative is stronger than needed.  The monodromy calculation
only uses that the selected terminal chart is unchanged and that the terminal
Mobius class agrees after projecting to PSL.
-/
structure PathLocalTransitionModelBasedWeakHandoffTerminalExtensionProjectionAgreement
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet)
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
        (p.trans (S.terminalSheetPathInSet hy'))) where
  /-- The extended skeleton ends in the same terminal chart. -/
  terminalCenter_eq : T.terminalCenter = S.terminalCenter
  /-- The extended skeleton has the same accumulated terminal Mobius PSL class. -/
  terminalMobius_projection_eq :
    realMobiusProjection T.terminalMobius =
      realMobiusProjection S.terminalMobius

end HyperbolicMetric

end

end JJMath
