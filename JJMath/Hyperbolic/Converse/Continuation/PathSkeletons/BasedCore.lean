import JJMath.Hyperbolic.Converse.Continuation.PathSkeletons.Intro

/-!
# Split path-skeleton continuation machinery
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

namespace PathLocalTransitionModelBasedWeakHandoffSkeleton

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

omit [RiemannSurface X] in
/--
Inserting one entry in a finite tuple only adds that entry to the associated
`List.ofFn`, up to permutation.

%%handwave
name:
  Inserting into a finite tuple permutes its entry list
statement:
  If $f:\{0,\ldots,n-1\}\to A$, $a\in A$, and $i\in\{0,\ldots,n\}$, then the list of entries of the tuple obtained by inserting $a$ at position $i$ is a permutation of $a$ followed by the list of entries of $f$.
proof:
  Induct on $n$ and split according to whether $i$ is the first position. In the successor case, expose the first entry, apply the induction hypothesis to the tail, and swap the old first entry past $a$.
-/
theorem ofFn_fin_insertNth_perm {α : Type*} :
    ∀ {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α),
      List.Perm (List.ofFn (Fin.insertNth i x f)) (x :: List.ofFn f)
  | 0, ⟨0, _⟩, x, f => by
      simp
  | n + 1, i, x, f => by
      cases i using Fin.cases with
      | zero =>
          simp
      | succ i =>
          rw [← Fin.cons_self_tail f]
          rw [Fin.insertNth_succ_cons, List.ofFn_cons, List.ofFn_cons]
          exact
            (List.Perm.cons (f 0)
              (ofFn_fin_insertNth_perm i x (Fin.tail f))).trans
              (List.Perm.swap (f 0) x (List.ofFn (Fin.tail f))).symm

/--
The accumulated Mobius representative after `n` handoffs of a based weak
handoff skeleton.  Past the actual length it stays constant; on the finite
range `0, …, length` it satisfies the expected recurrence.

%%handwave
name: The accumulated Möbius representative after n handoffs of a based weak handoff skeleton
statement:
  The accumulated Möbius representative after n handoffs of a based weak handoff skeleton. Past
  the actual length it stays constant; on the finite range 0, …, length it satisfies the
  expected recurrence.
-/
noncomputable def accumulatedMobiusNat
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ℕ → RealMobiusRepresentative
  | 0 => S.initialTransition.representative⁻¹
  | n + 1 =>
      if hn : n < S.length then
        accumulatedMobiusNat S n * (S.transitionAt ⟨n, hn⟩).representative⁻¹
      else
        accumulatedMobiusNat S n

omit [RiemannSurface X] in
/--
%%handwave
name:
  Initial value of the accumulated Möbius product
statement:
  The accumulated representative before any handoff is $M_0=T_0^{-1}$, where $T_0$ is the initial transition representative.
proof:
  This is the zero branch of the recursive definition.
-/
@[simp]
theorem accumulatedMobiusNat_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.accumulatedMobiusNat 0 = S.initialTransition.representative⁻¹ :=
  rfl

omit [RiemannSurface X] in
/-- The accumulated Mobius representative updates by the local handoff inverse.

%%handwave
name:
  Recurrence for accumulated Möbius representatives
statement:
  At every handoff $n$ before the last segment, the accumulated representative satisfies $M_{n+1}=M_nT_n^{-1}$, where $T_n$ is the transition from the chart on segment $n$ to the next chart.
proof:
  Since $n$ is within the skeleton length, the recursive definition takes its handoff branch.
-/
theorem accumulatedMobiusNat_succ_of_lt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {n : ℕ} (hn : n < S.length) :
    S.accumulatedMobiusNat (n + 1) =
      S.accumulatedMobiusNat n *
        (S.transitionAt ⟨n, hn⟩).representative⁻¹ := by
  simp [accumulatedMobiusNat, hn]

/-- The accumulated representative at a subdivision vertex.

%%handwave
name: The accumulated representative at a subdivision vertex
statement:
  The accumulated representative at a subdivision vertex.
-/
noncomputable def accumulatedMobiusAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (i : Fin (S.length + 1)) : RealMobiusRepresentative :=
  S.accumulatedMobiusNat i

omit [RiemannSurface X] in
/--
%%handwave
name:
  Accumulated representative at the first vertex
statement:
  At subdivision vertex $0$, the accumulated representative is $T_0^{-1}$, the inverse initial transition.
proof:
  Vertex-indexed accumulation at zero is the zero value of the natural-number recurrence.
-/
@[simp]
theorem accumulatedMobiusAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.accumulatedMobiusAt 0 = S.initialTransition.representative⁻¹ :=
  rfl

/-- The terminal center of a based weak handoff skeleton.

%%handwave
name: The terminal center of a based weak handoff skeleton
statement:
  The terminal center of a based weak handoff skeleton.
-/
def terminalCenter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    X :=
  S.centerAt (Fin.last S.length)

/-- The terminal accumulated Mobius representative.

%%handwave
name: The terminal accumulated Möbius representative
statement:
  The terminal accumulated Möbius representative.
-/
noncomputable def terminalMobius
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    RealMobiusRepresentative :=
  S.accumulatedMobiusAt (Fin.last S.length)

/-- The terminal value of the based weak handoff skeleton.

%%handwave
name: The terminal value of the based weak handoff skeleton
statement:
  The terminal value of the based weak handoff skeleton.
-/
noncomputable def terminalValue
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ℍ :=
  realMobiusRepresentativeAction S.terminalMobius
    ((localModels.chartAt S.terminalCenter).toUpperHalfPlane x)

/-- The terminal branch formula of a based weak handoff skeleton at a point.

%%handwave
name: The terminal branch formula of a based weak handoff skeleton at a point
statement:
  The terminal branch formula of a based weak handoff skeleton at a point.
-/
noncomputable def terminalFormulaAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (z : X) : ℍ :=
  realMobiusRepresentativeAction S.terminalMobius
    ((localModels.chartAt S.terminalCenter).toUpperHalfPlane z)

omit [RiemannSurface X] in
/--
%%handwave
name:
  The terminal branch formula evaluates to the terminal value
statement:
  For a continuation skeleton ending at $x$, evaluation of its terminal branch formula at $x$ is its terminal value: $F_{\mathrm{term}}(x)=v_{\mathrm{term}}$.
proof:
  Both sides are defined as $M_{\mathrm{term}}\cdot\phi_{c_{\mathrm{term}}}(x)$.
-/
@[simp]
theorem terminalFormulaAt_endpoint
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalFormulaAt x = S.terminalValue :=
  rfl

omit [RiemannSurface X] in
/--
Retarget a based weak handoff skeleton along source and target endpoint casts
of its underlying path.

This is the source-changing companion to `castTarget`; it is useful when a
path expression has endpoints that are propositionally, rather than
definitionally, the fixed endpoints of the public cut path.

%%handwave
name: Retarget a based weak handoff skeleton along source and target endpoint casts of its underlying path
statement:
  Retarget a based weak handoff skeleton along source and target endpoint casts of its
  underlying path. This is the source-changing companion to the endpoint-cast construction; it
  is useful when a path expression has endpoints that are propositionally, rather than
  definitionally, the fixed endpoints of the normalized cut path.
-/
def castEndpoints
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {x₀' x' : X} (hx₀ : x₀' = x₀) (hx : x' = x) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀' g localModels
      (p.cast hx₀ hx) where
  length := S.length
  length_pos := S.length_pos
  parameterAt := S.parameterAt
  parameterAt_zero := S.parameterAt_zero
  parameterAt_last := S.parameterAt_last
  parameterAt_mono := S.parameterAt_mono
  centerAt := S.centerAt
  sample_mem_model_domain := by
    intro i
    simpa [Path.cast_coe] using S.sample_mem_model_domain i
  path_segment_mem_model_domain := by
    intro k t ht_left ht_right
    simpa [Path.cast_coe] using
      S.path_segment_mem_model_domain k t ht_left ht_right
  terminal_endpoint_mem_domain := by
    simpa [hx] using S.terminal_endpoint_mem_domain
  transitionAt := by
    intro k
    exact
      localRealMobiusTransitionData_congr rfl rfl
        (by simp [Path.cast_coe]) (S.transitionAt k)
  initialTransition := by
    exact
      localRealMobiusTransitionData_congr
        (by rw [hx₀]) rfl hx₀ S.initialTransition

omit [RiemannSurface X] in
/-- Cast a based weak handoff skeleton across an equality of its path.

%%handwave
name: Cast a based weak handoff skeleton across an equality of its path
statement:
  Cast a based weak handoff skeleton across an equality of its path.
-/
def castPath
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {q : Path x₀ x} (hpq : p = q) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q := by
  subst hpq
  exact S

omit [RiemannSurface X] in
/--
%%handwave
name:
  Recasting both endpoints preserves the terminal center
statement:
  Replacing both endpoints of a path by equal points leaves the terminal chart center of its continuation skeleton unchanged.
proof:
  The endpoint recast copies the entire center sequence.
-/
@[simp]
theorem castEndpoints_terminalCenter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {x₀' x' : X} (hx₀ : x₀' = x₀) (hx : x' = x) :
    (S.castEndpoints hx₀ hx).terminalCenter = S.terminalCenter :=
  rfl

omit [RiemannSurface X] in
/--
%%handwave
name:
  Transport across an equal path preserves the terminal center
statement:
  If two based paths are equal, transporting a continuation skeleton across that equality does not change its terminal chart center.
proof:
  Substitute the path equality; the transported skeleton is then definitionally the original one.
-/
@[simp]
theorem castPath_terminalCenter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {q : Path x₀ x} (hpq : p = q) :
    (S.castPath hpq).terminalCenter = S.terminalCenter := by
  subst hpq
  rfl

omit [RiemannSurface X] in
/--
%%handwave
name:
  Recasting endpoints preserves every accumulated representative
statement:
  Replacing both path endpoints by equal points leaves every accumulated Möbius representative unchanged.
proof:
  Induct on the accumulation index. Transport of the initial and handoff transition data preserves their representatives, and the recursive products therefore agree both within and beyond the subdivision range.
-/
theorem castEndpoints_accumulatedMobiusNat
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {x₀' x' : X} (hx₀ : x₀' = x₀) (hx : x' = x) :
    ∀ n : ℕ,
      (S.castEndpoints hx₀ hx).accumulatedMobiusNat n =
        S.accumulatedMobiusNat n := by
  intro n
  induction n with
  | zero =>
      simp [castEndpoints, accumulatedMobiusNat]
  | succ n ih =>
      by_cases hn : n < S.length
      · have hnCast : n < (S.castEndpoints hx₀ hx).length := hn
        rw [(S.castEndpoints hx₀ hx).accumulatedMobiusNat_succ_of_lt hnCast,
          S.accumulatedMobiusNat_succ_of_lt hn, ih]
        simp [castEndpoints]
      · have hnCast : ¬ n < (S.castEndpoints hx₀ hx).length := hn
        simp [accumulatedMobiusNat, hn, hnCast, ih]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Recasting endpoints preserves the terminal Möbius representative
statement:
  Replacing both path endpoints by equal points leaves the terminal accumulated representative unchanged.
proof:
  Apply preservation of every accumulated representative at the unchanged terminal index.
-/
@[simp]
theorem castEndpoints_terminalMobius
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {x₀' x' : X} (hx₀ : x₀' = x₀) (hx : x' = x) :
    (S.castEndpoints hx₀ hx).terminalMobius = S.terminalMobius := by
  change
    (S.castEndpoints hx₀ hx).accumulatedMobiusNat
        (S.castEndpoints hx₀ hx).length =
      S.accumulatedMobiusNat S.length
  simpa [castEndpoints] using
    S.castEndpoints_accumulatedMobiusNat hx₀ hx S.length

omit [RiemannSurface X] in
/--
%%handwave
name:
  Transport across an equal path preserves the terminal Möbius representative
statement:
  Transporting a continuation skeleton across an equality of based paths leaves its terminal accumulated representative unchanged.
proof:
  After substituting the path equality, the transported skeleton is the original skeleton.
-/
@[simp]
theorem castPath_terminalMobius
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {q : Path x₀ x} (hpq : p = q) :
    (S.castPath hpq).terminalMobius = S.terminalMobius := by
  subst hpq
  rfl

omit [RiemannSurface X] in
/--
%%handwave
name:
  Recasting endpoints preserves the terminal value
statement:
  Replacing both endpoints of a path by equal points leaves the terminal value of its continuation skeleton unchanged.
proof:
  Endpoint recasting preserves the terminal center and terminal Möbius representative; replacing the equal target point in the final chart evaluation then makes the two formulas identical.
-/
@[simp]
theorem castEndpoints_terminalValue
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {x₀' x' : X} (hx₀ : x₀' = x₀) (hx : x' = x) :
    (S.castEndpoints hx₀ hx).terminalValue = S.terminalValue := by
  change
    realMobiusRepresentativeAction (S.castEndpoints hx₀ hx).terminalMobius
        ((localModels.chartAt
          (S.castEndpoints hx₀ hx).terminalCenter).toUpperHalfPlane x') =
      realMobiusRepresentativeAction S.terminalMobius
        ((localModels.chartAt S.terminalCenter).toUpperHalfPlane x)
  rw [S.castEndpoints_terminalMobius hx₀ hx,
    S.castEndpoints_terminalCenter hx₀ hx, hx]

omit [RiemannSurface X] in
/--
Matching terminal Mobius PSL classes and terminal charts identify the whole
terminal branch formula.  This is the comparison form needed by refinement
moves whose accumulated representatives agree only projectively.

%%handwave
name:
  Equal terminal projective class and chart give equal terminal formulas
statement:
  If two skeletons have the same terminal chart center and their terminal accumulated representatives have the same class in $\mathrm{PSL}_2(\mathbb R)$, then their terminal branch formulas agree at every $z\in X$.
proof:
  Identify the two terminal chart coordinates using equality of centers, then use that representatives with equal projective class act identically on $\mathbb H$.
-/
theorem terminalFormulaAt_eq_of_terminalMobius_projection_eq_terminalCenter_eq
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (hProjection :
      realMobiusProjection S.terminalMobius =
        realMobiusProjection T.terminalMobius)
    (hCenter : S.terminalCenter = T.terminalCenter)
    (z : X) :
    S.terminalFormulaAt z = T.terminalFormulaAt z := by
  change
    realMobiusRepresentativeAction S.terminalMobius
        ((localModels.chartAt S.terminalCenter).toUpperHalfPlane z) =
      realMobiusRepresentativeAction T.terminalMobius
        ((localModels.chartAt T.terminalCenter).toUpperHalfPlane z)
  rw [hCenter]
  exact realMobiusRepresentativeAction_eq_of_projection_eq hProjection _

omit [RiemannSurface X] in
/--
If the terminal chart of `T` is obtained from the terminal chart of `S` by a
real Mobius representative `A` at the endpoint, and the adjusted terminal
Mobius PSL class of `T` equals the terminal PSL class of `S`, then the two
terminal values agree.

%%handwave
name:
  Terminal values agree after a projectively compatible chart transition
statement:
  Let $S$ and $T$ end at the same point $x$. Suppose a real Möbius map $A$ relates their terminal chart coordinates by $\phi_T(x)=A\cdot\phi_S(x)$ and satisfies $[M_TA]=[M_S]$. Then $v_T=v_S$.
proof:
  Substitute the chart-transition formula into $v_T=M_T\cdot\phi_T(x)$, combine the two successive actions to obtain $(M_TA)\cdot\phi_S(x)$, and replace this action by that of $M_S$ using equality of projective classes.
-/
theorem terminalValue_eq_of_terminalTransitionProjection_eq
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (A : RealMobiusRepresentative)
    (hTransitionAtEndpoint :
      (localModels.chartAt T.terminalCenter).toUpperHalfPlane x =
        realMobiusRepresentativeAction A
          ((localModels.chartAt S.terminalCenter).toUpperHalfPlane x))
    (hProjection :
      realMobiusProjection (T.terminalMobius * A) =
        realMobiusProjection S.terminalMobius) :
    T.terminalValue = S.terminalValue := by
  change
    realMobiusRepresentativeAction T.terminalMobius
        ((localModels.chartAt T.terminalCenter).toUpperHalfPlane x) =
      realMobiusRepresentativeAction S.terminalMobius
        ((localModels.chartAt S.terminalCenter).toUpperHalfPlane x)
  rw [hTransitionAtEndpoint]
  rw [← realMobiusRepresentativeAction_mul]
  exact realMobiusRepresentativeAction_eq_of_projection_eq hProjection _

omit [RiemannSurface X] in
/--
The previous comparison specialized to an actual local transition datum at the
terminal endpoint.

%%handwave
name:
  Terminal values agree from compatible local transition data
statement:
  Let $A$ be local real Möbius transition data at the common endpoint from the terminal chart of $S$ to that of $T$. If $[M_TA]=[M_S]$, then $v_T=v_S$.
proof:
  The transition data give $\phi_T(x)=A\cdot\phi_S(x)$ on their neighborhood. Apply the projectively compatible terminal-chart comparison.
-/
theorem terminalValue_eq_of_terminalTransitionDataProjection_eq
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt T.terminalCenter)
        x)
    (hProjection :
      realMobiusProjection (T.terminalMobius * A.representative) =
        realMobiusProjection S.terminalMobius) :
    T.terminalValue = S.terminalValue :=
  S.terminalValue_eq_of_terminalTransitionProjection_eq T A.representative
    (A.transition_eq x A.mem_neighborhood) hProjection

omit [RiemannSurface X] in
/--
If the two terminal charts are related at the endpoint by a local real-Mobius
transition, then the terminal Mobius class must be compared after composing
with that terminal chart transition.

This is the transition-adjusted form of
`terminalValue_eq_holonomy_action_of_terminalProjection_eq`; it does not
require the selected terminal centers to coincide.

%%handwave
name:
  Holonomy comparison for terminal values across different charts
statement:
  Let $A$ relate the terminal chart coordinates of skeletons $S$ and $T$ at their common endpoint by $\phi_T(x)=A\cdot\phi_S(x)$. If $[M_TA]=\rho(\gamma)[M_S]$, then $v_T=\rho(\gamma)\cdot v_S$.
proof:
  Substitute the transition formula into $v_T$, combine the actions to obtain the class $[M_TA]$, replace it by $\rho(\gamma)[M_S]$, and use multiplicativity of the upper-half-plane action.
-/
theorem terminalValue_eq_holonomy_action_of_terminalTransitionProjection_eq
    {q : Path x₀ x}
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q)
    (holonomy : RealHolonomyRepresentation X x₀)
    (γ : FundamentalGroup X x₀)
    (A : RealMobiusRepresentative)
    (hTransitionAtEndpoint :
      (localModels.chartAt T.terminalCenter).toUpperHalfPlane x =
        realMobiusRepresentativeAction A
          ((localModels.chartAt S.terminalCenter).toUpperHalfPlane x))
    (hProjection :
      realMobiusProjection (T.terminalMobius * A) =
        holonomy γ * realMobiusProjection S.terminalMobius) :
    T.terminalValue =
      holonomy.upperHalfPlaneAction γ S.terminalValue := by
  change
    realMobiusRepresentativeAction T.terminalMobius
        ((localModels.chartAt T.terminalCenter).toUpperHalfPlane x) =
      holonomy.upperHalfPlaneAction γ
        (realMobiusRepresentativeAction S.terminalMobius
          ((localModels.chartAt S.terminalCenter).toUpperHalfPlane x))
  rw [hTransitionAtEndpoint]
  rw [← realMobiusRepresentativeAction_mul]
  rw [← realMobiusAction_realMobiusProjection (T.terminalMobius * A)]
  rw [hProjection]
  simp [RealHolonomyRepresentation.upperHalfPlaneAction, realMobiusAction_mul,
    realMobiusAction_realMobiusProjection]

omit [RiemannSurface X] in
/--
Every parameter of the unit interval lies in one of the closed subdivision
subintervals of a based weak handoff skeleton.

This is the finite-subdivision locator used by same-path refinement: to insert
a new vertex at `τ`, first find the old segment containing `τ`.

%%handwave
name:
  Every parameter lies in a subdivision segment
statement:
  If $0=t_0\le t_1\le\cdots\le t_n=1$ with $n>0$, then every $\tau\in[0,1]$ lies in some interval $[t_k,t_{k+1}]$ with $0\le k<n$.
proof:
  Choose the least index $j$ with $\tau\le t_j$, which exists because $t_n=1$. If $j=0$, use the first segment and $0\le\tau$. Otherwise minimality gives $t_{j-1}<\tau$, and $k=j-1$ yields $t_k\le\tau\le t_{k+1}$.
-/
theorem exists_segment_contains_parameter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) :
    ∃ k : Fin S.length,
      (S.parameterAt k.castSucc : ℝ) ≤ (τ : ℝ) ∧
        (τ : ℝ) ≤ (S.parameterAt k.succ : ℝ) := by
  classical
  let Q : ℕ → Prop := fun n =>
    ∃ hn : n ≤ S.length,
      (τ : ℝ) ≤
        (S.parameterAt ⟨n, Nat.lt_succ_of_le hn⟩ : ℝ)
  have hQexists : ∃ n, Q n := by
    refine ⟨S.length, le_rfl, ?_⟩
    have hlast :
        (⟨S.length, Nat.lt_succ_of_le le_rfl⟩ : Fin (S.length + 1)) =
          Fin.last S.length := by
      ext
      simp
    simpa [Q, hlast, S.parameterAt_last] using unitInterval.le_one τ
  let n := Nat.find hQexists
  have hnQ : Q n := Nat.find_spec hQexists
  rcases hnQ with ⟨hnle, hnτ⟩
  by_cases hn0 : n = 0
  · let k : Fin S.length := ⟨0, S.length_pos⟩
    refine ⟨k, ?_, ?_⟩
    · simpa [k, hn0, S.parameterAt_zero] using unitInterval.nonneg τ
    · have hmono : (S.parameterAt k.castSucc : ℝ) ≤
          (S.parameterAt k.succ : ℝ) :=
        S.parameterAt_mono k
      have hτ0 : (τ : ℝ) ≤ (S.parameterAt k.castSucc : ℝ) := by
        simpa [k, hn0] using hnτ
      exact le_trans hτ0 hmono
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    let k : Fin S.length := ⟨n - 1, by omega⟩
    let iPrev : Fin (S.length + 1) :=
      ⟨n - 1, Nat.lt_succ_of_le (by omega : n - 1 ≤ S.length)⟩
    let iCur : Fin (S.length + 1) :=
      ⟨n, Nat.lt_succ_of_le hnle⟩
    have hprev_lt : n - 1 < n := by omega
    have hnotQprev : ¬ Q (n - 1) :=
      Nat.find_min hQexists hprev_lt
    have hnot_le :
        ¬ (τ : ℝ) ≤ (S.parameterAt iPrev : ℝ) := by
      intro hle
      exact hnotQprev ⟨by omega, by simpa [iPrev] using hle⟩
    have hleft :
        (S.parameterAt iPrev : ℝ) ≤ (τ : ℝ) :=
      le_of_lt (lt_of_not_ge hnot_le)
    have hcast : k.castSucc = iPrev := by
      ext
      simp [k, iPrev]
    have hsucc : k.succ = iCur := by
      ext
      simp [k, iCur]
      omega
    refine ⟨k, ?_, ?_⟩
    · simpa [hcast]
        using hleft
    · simpa [hsucc, iCur]
        using hnτ

/-- The canonical-cover point represented by the terminal endpoint and path.

%%handwave
name: The canonical-cover point represented by the terminal endpoint and path
statement:
  The canonical-cover point represented by the terminal endpoint and path.
-/
def terminalCoverPoint
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathHomotopyUniversalCover X x₀ :=
  let _length : ℕ := S.length
  ⟨x, Path.Homotopic.Quotient.mk p⟩

omit [RiemannSurface X] in
/--
%%handwave
name:
  The terminal lift projects to the endpoint
statement:
  If the terminal lift of a continued path $p:x_0\rightsquigarrow x$ is represented by $(x,[p])$, then its projection to $X$ is $x$.
proof:
  This is the first projection of the defining pair $(x,[p])$.
-/
@[simp]
theorem endpoint_terminalCoverPoint
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathHomotopyUniversalCover.endpoint S.terminalCoverPoint = x :=
  rfl

omit [RiemannSurface X] in
/--
The terminal endpoint, viewed as a cover point, projects into the terminal
local-model domain.

%%handwave
name:
  The terminal lift projects into the terminal chart domain
statement:
  For a based continuation skeleton ending at $x$, the projection of its terminal lift belongs to the domain of the local model selected at the final subdivision vertex.
proof:
  The terminal lift projects to $x$, and membership of $x$ in the final selected chart domain is one of the skeleton conditions.
-/
theorem terminalCoverPoint_endpoint_mem_terminal_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathHomotopyUniversalCover.endpoint S.terminalCoverPoint ∈
      (localModels.chartAt S.terminalCenter).domain := by
  simpa [terminalCoverPoint, terminalCenter] using
    S.terminal_endpoint_mem_domain

/--
The canonical terminal sheet over the terminal local-model domain.

This is the local sheet on the canonical cover that will carry the terminal
branch formula attached to the representative path.

%%handwave
name: The canonical terminal sheet over the terminal local-model domain
statement:
  The canonical terminal sheet over the terminal local-model domain. This is the local sheet on
  the canonical cover that will carry the terminal branch formula attached to the representative
  path.
-/
noncomputable def terminalSheetChart
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathHomotopyUniversalCover.LocalSheetChart (X := X) x₀ :=
  PathHomotopyUniversalCover.localSheetChartAtWithin
    (x₀ := x₀) S.terminalCoverPoint
    S.terminalCoverPoint_endpoint_mem_terminal_domain
    (localModels.chartAt S.terminalCenter).isOpen_domain

/-- The terminal sheet neighborhood determined by the terminal model domain.

%%handwave
name: The terminal sheet neighborhood determined by the terminal model domain
statement:
  The terminal sheet neighborhood determined by the terminal model domain.
-/
noncomputable def terminalSheet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Set (PathHomotopyUniversalCover X x₀) :=
  S.terminalSheetChart.sheet

/-- The terminal sheet is open in the canonical cover.

%%handwave
name:
  Openness of the terminal sheet
statement:
  The sheet of the universal cover determined by the final local-model domain and the terminal lift is an open subset of the universal cover.
proof:
  A local sheet over an open base set is open; apply this to the final chart domain.
-/
theorem isOpen_terminalSheet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    IsOpen S.terminalSheet :=
  PathHomotopyUniversalCover.isOpen_localSheetChart_sheet S.terminalSheetChart

/-- The represented terminal path-class point lies in its terminal sheet.

%%handwave
name:
  The terminal lift belongs to its terminal sheet
statement:
  The lift $(x,[p])$ determined by a continued path belongs to the local sheet based at that lift over the terminal chart domain.
proof:
  The center of a local sheet lies in the sheet whenever its projection belongs to the chosen open base set; the terminal-domain condition supplies that membership.
-/
theorem terminalCoverPoint_mem_terminalSheet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalCoverPoint ∈ S.terminalSheet := by
  simpa [terminalSheet, terminalSheetChart] using
    PathHomotopyUniversalCover.localSheetChartAtWithin_mem
      (x₀ := x₀) S.terminalCoverPoint
      S.terminalCoverPoint_endpoint_mem_terminal_domain
      (localModels.chartAt S.terminalCenter).isOpen_domain

/-- Points in the terminal sheet project into the terminal local-model domain.

%%handwave
name:
  Projection of the terminal sheet lies in the terminal chart
statement:
  If $y$ belongs to the terminal sheet of a continuation skeleton, then $\pi(y)$ belongs to the domain of the local model selected at the final subdivision vertex.
proof:
  The local sheet was defined inside the inverse image of the final chart domain, so its endpoint projection has the required membership.
-/
theorem endpoint_mem_terminal_domain_of_mem_terminalSheet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    PathHomotopyUniversalCover.endpoint y' ∈
      (localModels.chartAt S.terminalCenter).domain := by
  exact
    PathHomotopyUniversalCover.localSheetChartAtWithin_sheet_subset_endpoint_preimage
      (x₀ := x₀) S.terminalCoverPoint
      S.terminalCoverPoint_endpoint_mem_terminal_domain
      (localModels.chartAt S.terminalCenter).isOpen_domain
      hy'

/-- The base of the terminal sheet chart is contained in the terminal model domain.

%%handwave
name:
  The base of the terminal sheet lies in the terminal chart
statement:
  The connected base neighborhood used to define the terminal sheet is contained in the final local-model domain.
proof:
  This is the defining containment of the local sheet chart obtained from the final chart domain.
-/
theorem terminalSheetChart_base_subset_terminal_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalSheetChart.base ⊆
      (localModels.chartAt S.terminalCenter).domain := by
  intro z hz
  simpa [terminalSheetChart] using
    PathHomotopyUniversalCover.localSheetChartAtWithin_base_subset
      (x₀ := x₀) S.terminalCoverPoint
      S.terminalCoverPoint_endpoint_mem_terminal_domain
      (localModels.chartAt S.terminalCenter).isOpen_domain hz

/--
The canonical local path in the base of the terminal sheet from the endpoint
of the continued path to the endpoint of a lift in that sheet.

%%handwave
name: The canonical local path in the base of the terminal sheet from the endpoint of the continued path to the endpoint of a lift in that sheet
statement:
  The canonical local path in the base of the terminal sheet from the endpoint of the continued
  path to the endpoint of a lift in that sheet.
-/
noncomputable def terminalSheetPathInSet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    Path x (PathHomotopyUniversalCover.endpoint y') :=
  PathHomotopyUniversalCover.pathInSet
    S.terminalSheetChart.center
    (⟨PathHomotopyUniversalCover.endpoint y',
      PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
        (by
          simpa [terminalSheet,
            PathHomotopyUniversalCover.LocalSheetChart.sheet] using
            hy')⟩ : S.terminalSheetChart.base)

/--
The canonical path used inside a terminal sheet stays in the terminal
local-model domain.

%%handwave
name:
  A path inside the terminal sheet base stays in the terminal chart
statement:
  Let $y$ lie in the terminal sheet and let $\sigma$ be the chosen path in its base from $x$ to $\pi(y)$. Then $\sigma(t)$ lies in the final local-model domain for every $t\in[0,1]$.
proof:
  The chosen path lies in the base of the local sheet chart, and that base is contained in the final local-model domain.
-/
theorem terminalSheetPathInSet_mem_terminal_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) (t : unitInterval) :
    S.terminalSheetPathInSet hy' t ∈
      (localModels.chartAt S.terminalCenter).domain := by
  let C := S.terminalSheetChart
  let xC : C.base :=
    ⟨PathHomotopyUniversalCover.endpoint y',
      PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
        (by
          simpa [terminalSheet,
            PathHomotopyUniversalCover.LocalSheetChart.sheet, C] using
            hy')⟩
  have hbase :
      S.terminalSheetPathInSet hy' t ∈ C.base := by
    change (PathHomotopyUniversalCover.pathInSet C.center xC) t ∈ C.base
    dsimp [PathHomotopyUniversalCover.pathInSet]
    exact ((PathConnectedSpace.somePath C.center xC) t).2
  have hsubset :
      C.base ⊆ (localModels.chartAt S.terminalCenter).domain := by
    simpa [C, terminalSheetChart] using
      PathHomotopyUniversalCover.localSheetChartAtWithin_base_subset
        (x₀ := x₀) S.terminalCoverPoint
        S.terminalCoverPoint_endpoint_mem_terminal_domain
        (localModels.chartAt S.terminalCenter).isOpen_domain
  exact hsubset hbase

omit [RiemannSurface X] in
/--
Subdivision parameters for the terminal-extension skeleton: the old
subdivision is compressed into the first half and one final endpoint is added
at `1`.

%%handwave
name: Subdivision parameters for the terminal-extension skeleton: the old subdivision is compressed into the first half and one final endpoint is added at 1
statement:
  Subdivision parameters for the terminal-extension skeleton: the old subdivision is compressed
  into the first half and one final endpoint is added at 1.
-/
noncomputable def terminalExtensionParameterAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Fin (S.length + 2) → unitInterval :=
  fun i =>
    if hi : (i : ℕ) < S.length + 1 then
      unitInterval.firstHalf (S.parameterAt ⟨i, hi⟩)
    else
      1

omit [RiemannSurface X] in
/--
Centers for the terminal-extension skeleton: the old centers are reused on
the compressed first half and the added endpoint uses the old terminal center.

%%handwave
name: Centers for the terminal-extension skeleton: the old centers are reused on the compressed first half and the added endpoint uses the old terminal center
statement:
  Centers for the terminal-extension skeleton: the old centers are reused on the compressed
  first half and the added endpoint uses the old terminal center.
-/
noncomputable def terminalExtensionCenterAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Fin (S.length + 2) → X :=
  fun i =>
    if hi : (i : ℕ) < S.length + 1 then
      S.centerAt ⟨i, hi⟩
    else
      S.terminalCenter

omit [RiemannSurface X] in
/--
%%handwave
name:
  Old vertices retain their halved subdivision parameters
statement:
  In the terminal extension of a skeleton with parameters $t_i$, every old vertex $i$ is assigned the parameter $t_i/2$.
proof:
  At an old vertex the first branch of the definition applies, giving the first-half rescaling $t\mapsto t/2$.
-/
@[simp]
theorem terminalExtensionParameterAt_castSucc
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (i : Fin (S.length + 1)) :
    S.terminalExtensionParameterAt i.castSucc =
      unitInterval.firstHalf (S.parameterAt i) := by
  change
    (if hi : (i : ℕ) < S.length + 1 then
      unitInterval.firstHalf (S.parameterAt ⟨i, hi⟩)
    else 1) = unitInterval.firstHalf (S.parameterAt i)
  rw [dif_pos i.isLt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Old vertices retain their chart centers under terminal extension
statement:
  In a terminally extended skeleton, the chart center attached to every old vertex $i$ is the original center $c_i$.
proof:
  The old-index branch of the definition returns the original center.
-/
@[simp]
theorem terminalExtensionCenterAt_castSucc
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (i : Fin (S.length + 1)) :
    S.terminalExtensionCenterAt i.castSucc = S.centerAt i := by
  change
    (if hi : (i : ℕ) < S.length + 1 then
      S.centerAt ⟨i, hi⟩
    else S.terminalCenter) = S.centerAt i
  rw [dif_pos i.isLt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  The final terminal-extension parameter is one
statement:
  The new last vertex of the terminally extended subdivision is assigned the parameter $1$.
proof:
  Its index is outside the old range, so the final branch of the definition applies.
-/
@[simp]
theorem terminalExtensionParameterAt_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalExtensionParameterAt (Fin.last (S.length + 1)) = 1 := by
  simp [terminalExtensionParameterAt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  The new final vertex uses the old terminal center
statement:
  The chart center at the new last vertex of a terminal extension is the original terminal center.
proof:
  The last index lies beyond the old vertices, where the extended center function is defined to be the old terminal center.
-/
@[simp]
theorem terminalExtensionCenterAt_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalExtensionCenterAt (Fin.last (S.length + 1)) =
      S.terminalCenter := by
  simp [terminalExtensionCenterAt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  The terminal-extension subdivision starts at zero
statement:
  The first parameter of a terminally extended subdivision is $0$.
proof:
  The original first parameter is $0$, and first-half rescaling fixes $0$.
-/
@[simp]
theorem terminalExtensionParameterAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalExtensionParameterAt 0 = 0 := by
  simp [terminalExtensionParameterAt, S.parameterAt_zero]

omit [RiemannSurface X] in
/--
%%handwave
name:
  The terminal extension keeps the initial center
statement:
  The first chart center of a terminally extended skeleton is the original first center.
proof:
  Zero is an old vertex, so the old-index branch of the center function applies.
-/
@[simp]
theorem terminalExtensionCenterAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalExtensionCenterAt 0 = S.centerAt 0 := by
  simp [terminalExtensionCenterAt]

omit [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Successor after casting to a larger finite type is the cast of the successor.

%%handwave
name:
  Successor commutes with finite-index inclusion
statement:
  For $k\in\{0,\ldots,n-1\}$, taking the successor after including $k$ into $\{0,\ldots,n\}$ gives the same element of $\{0,\ldots,n+1\}$ as first taking the successor and then including it.
proof:
  Both finite indices have the same underlying natural number $k+1$.
-/
theorem fin_castSucc_succ_eq_succ_castSucc {n : ℕ} (k : Fin n) :
    (k.castSucc : Fin (n + 1)).succ = (k.succ).castSucc := by
  ext
  rfl

omit [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The successor of the last element is the last element in the next finite type.

%%handwave
name:
  The successor of a finite last index is the next last index
statement:
  The successor of the index $n$ in $\{0,\ldots,n\}$ is the last index $n+1$ in $\{0,\ldots,n+1\}$.
proof:
  Both sides have underlying natural number $n+1$.
-/
theorem fin_last_succ_eq_last {n : ℕ} :
    (Fin.last n : Fin (n + 1)).succ = Fin.last (n + 1) := by
  ext
  rfl

omit [RiemannSurface X] in
/--
%%handwave
name:
  Right center of an old extended segment
statement:
  For every original segment $k$, the chart center at its right vertex in the terminal extension is $c_{k+1}$.
proof:
  Commute successor with inclusion of finite indices and apply the old-vertex center formula at $k+1$.
-/
@[simp]
theorem terminalExtensionCenterAt_old_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    S.terminalExtensionCenterAt ((k.castSucc : Fin (S.length + 1)).succ) =
      S.centerAt k.succ := by
  rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
  simpa using S.terminalExtensionCenterAt_castSucc k.succ

omit [RiemannSurface X] in
/--
%%handwave
name:
  The added terminal segment begins at one half
statement:
  The left endpoint parameter of the new final segment is $1/2$.
proof:
  It is the halved image of the original last parameter $t_n=1$.
-/
@[simp]
theorem terminalExtensionParameterAt_final_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalExtensionParameterAt
        ((Fin.last S.length : Fin (S.length + 1)).castSucc) =
      unitInterval.firstHalf 1 := by
  simp [S.parameterAt_last]

omit [RiemannSurface X] in
/--
%%handwave
name:
  The added terminal segment begins in the terminal chart
statement:
  The chart center at the left endpoint of the new final segment is the original terminal center.
proof:
  This vertex is the included original last vertex, whose center is the terminal center.
-/
@[simp]
theorem terminalExtensionCenterAt_final_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalExtensionCenterAt
        ((Fin.last S.length : Fin (S.length + 1)).castSucc) =
      S.terminalCenter := by
  simp [terminalCenter]

omit [RiemannSurface X] in
/--
%%handwave
name:
  The added terminal segment ends at one
statement:
  The right endpoint parameter of the new final segment is $1$.
proof:
  The successor of the old last index is the new last index, whose parameter is $1$.
-/
@[simp]
theorem terminalExtensionParameterAt_final_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalExtensionParameterAt
        ((Fin.last S.length : Fin (S.length + 1)).succ) = 1 := by
  rw [fin_last_succ_eq_last]
  exact S.terminalExtensionParameterAt_last

omit [RiemannSurface X] in
/-- The terminal-extension subdivision parameters are weakly increasing.

%%handwave
name:
  Monotonicity of terminal-extension parameters
statement:
  The sequence $t_0/2,\ldots,t_n/2,1$ obtained by terminal extension is weakly increasing.
proof:
  Between inherited vertices this follows from monotonicity of the original parameters after division by $2$. The final inequality is $1/2\le 1$ because $t_n=1$.
-/
theorem terminalExtensionParameterAt_mono
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ k : Fin (S.length + 1),
      (S.terminalExtensionParameterAt k.castSucc : ℝ) ≤
        (S.terminalExtensionParameterAt k.succ : ℝ) := by
  intro k
  by_cases hk : (k : ℕ) < S.length
  · let k₀ : Fin S.length := ⟨k, hk⟩
    have hleft :
        k.castSucc = (k₀.castSucc : Fin (S.length + 1)).castSucc := by
      ext
      rfl
    have hright : k.succ = (k₀.succ : Fin (S.length + 1)).castSucc := by
      ext
      rfl
    rw [hleft, hright, S.terminalExtensionParameterAt_castSucc k₀.castSucc,
      S.terminalExtensionParameterAt_castSucc k₀.succ]
    change ((S.parameterAt k₀.castSucc : ℝ) / 2) ≤
      ((S.parameterAt k₀.succ : ℝ) / 2)
    nlinarith [S.parameterAt_mono k₀]
  · have hk_last : k = Fin.last S.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    rw [S.terminalExtensionParameterAt_final_left,
      S.terminalExtensionParameterAt_final_right]
    norm_num

/--
Every sampled vertex of the terminal-extension subdivision lies in its
selected model domain.

%%handwave
name:
  Model-domain membership at every terminal-extension vertex
statement:
  For the path $p*\sigma$ obtained by appending a path inside the terminal sheet, every vertex of the subdivision $t_0/2,\ldots,t_n/2,1$ lies in the domain of its assigned local model.
proof:
  At an inherited vertex, evaluation reduces to $p(t_i)$ and the original sampling condition applies. At the new final vertex, the value is $\pi(y)$, which lies in the terminal chart because $y$ belongs to the terminal sheet.
-/
theorem terminalExtension_sample_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    ∀ i : Fin (S.length + 2),
      (p.trans (S.terminalSheetPathInSet hy'))
          (S.terminalExtensionParameterAt i) ∈
        (localModels.chartAt (S.terminalExtensionCenterAt i)).domain := by
  intro i
  by_cases hi : (i : ℕ) < S.length + 1
  · let j : Fin (S.length + 1) := ⟨i, hi⟩
    have hij : i = j.castSucc := by
      ext
      rfl
    rw [hij, S.terminalExtensionParameterAt_castSucc j,
      S.terminalExtensionCenterAt_castSucc j]
    rw [path_trans_firstHalf_apply]
    exact S.sample_mem_model_domain j
  · have hi_last : i = Fin.last (S.length + 1) := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ i.isLt)
        (Nat.le_of_not_gt hi)
    rw [hi_last]
    simpa [S.terminalExtensionParameterAt_last,
      S.terminalExtensionCenterAt_last] using
      S.endpoint_mem_terminal_domain_of_mem_terminalSheet hy'

/--
Every subinterval of the terminal-extension subdivision stays in the selected
model domain attached to its left vertex.

%%handwave
name:
  Model-domain containment along terminal-extension segments
statement:
  Each old segment of $p*\sigma$ on $[t_k/2,t_{k+1}/2]$ remains in the original chart centered at $c_k$, and the added segment on $[1/2,1]$ remains in the original terminal chart.
proof:
  On the first half, double the parameter and apply the original segment-containment condition. On the second half, reparameterize by $2t-1$ and use that $\sigma$ stays in the terminal chart domain.
-/
theorem terminalExtension_path_segment_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    ∀ k : Fin (S.length + 1), ∀ t : unitInterval,
      (S.terminalExtensionParameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (S.terminalExtensionParameterAt k.succ : ℝ) →
      (p.trans (S.terminalSheetPathInSet hy')) t ∈
        (localModels.chartAt (S.terminalExtensionCenterAt k.castSucc)).domain := by
  intro k t ht_left ht_right
  by_cases hk : (k : ℕ) < S.length
  · let k₀ : Fin S.length := ⟨k, hk⟩
    have hleft_index :
        k.castSucc = (k₀.castSucc : Fin (S.length + 1)).castSucc := by
      ext
      rfl
    have hright_index : k.succ = (k₀.succ : Fin (S.length + 1)).castSucc := by
      ext
      rfl
    rw [hleft_index, S.terminalExtensionParameterAt_castSucc k₀.castSucc] at ht_left
    rw [hright_index, S.terminalExtensionParameterAt_castSucc k₀.succ] at ht_right
    have ht_half : (t : ℝ) ≤ 1 / 2 :=
      le_trans ht_right (unitInterval.firstHalf_le_half (S.parameterAt k₀.succ))
    have h_lower :
        (S.parameterAt k₀.castSucc : ℝ) ≤
          (unitInterval.doubleOfLeHalf t ht_half : ℝ) := by
      change (S.parameterAt k₀.castSucc : ℝ) ≤ 2 * (t : ℝ)
      change ((S.parameterAt k₀.castSucc : ℝ) / 2) ≤ (t : ℝ) at ht_left
      nlinarith
    have h_upper :
        (unitInterval.doubleOfLeHalf t ht_half : ℝ) ≤
          (S.parameterAt k₀.succ : ℝ) := by
      change 2 * (t : ℝ) ≤ (S.parameterAt k₀.succ : ℝ)
      change (t : ℝ) ≤ ((S.parameterAt k₀.succ : ℝ) / 2) at ht_right
      nlinarith
    have hcenter :
        S.terminalExtensionCenterAt k.castSucc = S.centerAt k₀.castSucc := by
      rw [hleft_index]
      simp
    rw [path_trans_apply_of_le_half p (S.terminalSheetPathInSet hy') t ht_half,
      hcenter]
    exact S.path_segment_mem_model_domain k₀
      (unitInterval.doubleOfLeHalf t ht_half) h_lower h_upper
  · have hk_last : k = Fin.last S.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    rw [S.terminalExtensionParameterAt_final_left] at ht_left
    have ht_half : (1 / 2 : ℝ) ≤ t := by
      simpa using ht_left
    rw [path_trans_apply_of_half_le p (S.terminalSheetPathInSet hy') t ht_half]
    rw [S.terminalExtensionCenterAt_final_left]
    exact S.terminalSheetPathInSet_mem_terminal_domain hy'
      (unitInterval.doubleSubOneOfHalfLe t ht_half)

/-- The endpoint of the terminal-extension path lies in the terminal selected model.

%%handwave
name:
  Terminal endpoint of an extension lies in its assigned chart
statement:
  If $y$ belongs to the terminal sheet, then $\pi(y)$ lies in the local-model domain assigned to the new final vertex of the terminally extended skeleton.
proof:
  The final assigned center is the old terminal center, and every point of the terminal sheet projects into that chart domain.
-/
theorem terminalExtension_terminal_endpoint_mem_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    PathHomotopyUniversalCover.endpoint y' ∈
      (localModels.chartAt
        (S.terminalExtensionCenterAt (Fin.last (S.length + 1)))).domain := by
  simpa [S.terminalExtensionCenterAt_last] using
    S.endpoint_mem_terminal_domain_of_mem_terminalSheet hy'

/--
Append the canonical local path inside the terminal sheet to a based weak
handoff skeleton.

The old subdivision is compressed into the first half; the final subinterval
stays inside the terminal chart, so its handoff is the identity local
transition from that chart to itself.

%%handwave
name: Append the canonical local path inside the terminal sheet to a based weak handoff skeleton
statement:
  Append the canonical local path inside the terminal sheet to a based weak handoff skeleton.
  The old subdivision is compressed into the first half; the final subinterval stays inside the
  terminal chart, so its handoff is the identity local transition from that chart to itself.
-/
noncomputable def terminalExtensionSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
      (p.trans (S.terminalSheetPathInSet hy')) where
  length := S.length + 1
  length_pos := Nat.succ_pos S.length
  parameterAt := S.terminalExtensionParameterAt
  parameterAt_zero := S.terminalExtensionParameterAt_zero
  parameterAt_last := S.terminalExtensionParameterAt_last
  parameterAt_mono := S.terminalExtensionParameterAt_mono
  centerAt := S.terminalExtensionCenterAt
  sample_mem_model_domain := S.terminalExtension_sample_mem_model_domain hy'
  path_segment_mem_model_domain :=
    S.terminalExtension_path_segment_mem_model_domain hy'
  terminal_endpoint_mem_domain :=
    S.terminalExtension_terminal_endpoint_mem_domain hy'
  transitionAt := by
    intro k
    by_cases hk : (k : ℕ) < S.length
    · let k₀ : Fin S.length := ⟨k, hk⟩
      have hleft :
          k.castSucc = (k₀.castSucc : Fin (S.length + 1)).castSucc := by
        ext
        rfl
      have hright : k.succ = (k₀.succ : Fin (S.length + 1)).castSucc := by
        ext
        rfl
      have hU :
          localModels.chartAt (S.terminalExtensionCenterAt k.castSucc) =
            localModels.chartAt (S.centerAt k₀.castSucc) := by
        rw [hleft]
        simp
      have hV :
          localModels.chartAt (S.terminalExtensionCenterAt k.succ) =
            localModels.chartAt (S.centerAt k₀.succ) := by
        rw [hright]
        simp
      have hpath :
          (p.trans (S.terminalSheetPathInSet hy'))
              (S.terminalExtensionParameterAt k.succ) =
            p (S.parameterAt k₀.succ) :=
        by
          rw [hright, S.terminalExtensionParameterAt_castSucc]
          exact path_trans_firstHalf_apply p (S.terminalSheetPathInSet hy')
            (S.parameterAt k₀.succ)
      exact localRealMobiusTransitionData_congr hU hV hpath
        (S.transitionAt k₀)
    · have hk_last : k = Fin.last S.length := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
          (Nat.le_of_not_gt hk)
      subst k
      have hx :
          (p.trans (S.terminalSheetPathInSet hy'))
              (S.terminalExtensionParameterAt (Fin.last (S.length + 1))) ∈
            (localModels.chartAt S.terminalCenter).domain := by
        simpa [S.terminalExtensionCenterAt_last] using
          S.terminalExtension_sample_mem_model_domain hy'
            (Fin.last (S.length + 1))
      have hU :
          localModels.chartAt
              (S.terminalExtensionCenterAt
                ((Fin.last S.length : Fin (S.length + 1)).castSucc)) =
            localModels.chartAt S.terminalCenter := by
        simp [terminalCenter]
      have hV :
          localModels.chartAt
              (S.terminalExtensionCenterAt
                ((Fin.last S.length : Fin (S.length + 1)).succ)) =
            localModels.chartAt S.terminalCenter := by
        rw [fin_last_succ_eq_last]
        simp
      have hpoint :
          (p.trans (S.terminalSheetPathInSet hy'))
              (S.terminalExtensionParameterAt
                ((Fin.last S.length : Fin (S.length + 1)).succ)) =
            (p.trans (S.terminalSheetPathInSet hy'))
              (S.terminalExtensionParameterAt (Fin.last (S.length + 1))) := by
        rw [fin_last_succ_eq_last]
      exact localRealMobiusTransitionData_congr hU hV hpoint
        (localRealMobiusTransitionData_self
          (localModels.chartAt S.terminalCenter) hx)
  initialTransition := by
    exact localRealMobiusTransitionData_congr rfl
      (by simp [S.terminalExtensionCenterAt_zero]) rfl S.initialTransition

/--
%%handwave
name:
  Terminal extension preserves the terminal chart center
statement:
  Appending the canonical path inside the terminal sheet leaves the terminal chart center unchanged.
proof:
  The new last vertex is assigned the original terminal center by construction.
-/
@[simp]
theorem terminalExtensionSkeleton_terminalCenter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    (S.terminalExtensionSkeleton hy').terminalCenter = S.terminalCenter := by
  simp [terminalExtensionSkeleton, terminalCenter]

/--
Along the compressed old part of a terminal-extension skeleton, the
accumulated Mobius product agrees with the original skeleton.

%%handwave
name:
  Terminal extension preserves accumulated Möbius products on the old prefix
statement:
  Let $S^+$ be the skeleton obtained by appending a path inside the terminal sheet to a skeleton $S$ of length $n$. For every $j\le n$, the accumulated representatives agree: $M_j(S^+)=M_j(S)$.
proof:
  Induct on $j$. The initial transitions agree. At each old step, the extended skeleton transports exactly the original transition data, so the recurrence $M_{j+1}=M_jT_j^{-1}$ and the induction hypothesis give equality.
-/
theorem terminalExtensionSkeleton_accumulatedMobiusNat_eq_of_le
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    ∀ n : ℕ, n ≤ S.length →
      (S.terminalExtensionSkeleton hy').accumulatedMobiusNat n =
        S.accumulatedMobiusNat n := by
  intro n hn
  induction n with
  | zero =>
      simp [terminalExtensionSkeleton, accumulatedMobiusNat]
  | succ n ih =>
      have hnlt : n < S.length := Nat.succ_le_iff.mp hn
      have hnle : n ≤ S.length := Nat.le_of_lt hnlt
      let T := S.terminalExtensionSkeleton hy'
      have hTstep :
          T.accumulatedMobiusNat (n + 1) =
            T.accumulatedMobiusNat n *
              (T.transitionAt ⟨n, Nat.lt_succ_of_lt hnlt⟩).representative⁻¹ :=
        T.accumulatedMobiusNat_succ_of_lt (Nat.lt_succ_of_lt hnlt)
      have hSstep :
          S.accumulatedMobiusNat (n + 1) =
            S.accumulatedMobiusNat n *
              (S.transitionAt ⟨n, hnlt⟩).representative⁻¹ :=
        S.accumulatedMobiusNat_succ_of_lt hnlt
      have htrans :
          (T.transitionAt ⟨n, Nat.lt_succ_of_lt hnlt⟩).representative =
            (S.transitionAt ⟨n, hnlt⟩).representative := by
        simp [T, terminalExtensionSkeleton, hnlt]
      rw [hTstep, ih hnle, htrans, hSstep]

/--
%%handwave
name:
  Terminal extension preserves the terminal Möbius representative
statement:
  Appending the canonical path inside the terminal sheet does not change the accumulated terminal representative: $M_{\mathrm{term}}(S^+)=M_{\mathrm{term}}(S)$.
proof:
  The accumulated product through the old last vertex agrees with the original one. The single added handoff is the identity transition of the terminal chart with itself, so multiplying by its inverse changes nothing.
-/
@[simp]
theorem terminalExtensionSkeleton_terminalMobius_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    (S.terminalExtensionSkeleton hy').terminalMobius = S.terminalMobius := by
  let T := S.terminalExtensionSkeleton hy'
  have hprefix :
      T.accumulatedMobiusNat S.length = S.accumulatedMobiusNat S.length :=
    S.terminalExtensionSkeleton_accumulatedMobiusNat_eq_of_le hy' S.length le_rfl
  have hstep :
      T.accumulatedMobiusNat (S.length + 1) =
        T.accumulatedMobiusNat S.length *
          (T.transitionAt (Fin.last S.length)).representative⁻¹ := by
    exact T.accumulatedMobiusNat_succ_of_lt (Nat.lt_succ_self S.length)
  have htrans :
      (T.transitionAt (Fin.last S.length)).representative = 1 := by
    simp [T, terminalExtensionSkeleton, localRealMobiusTransitionData_self]
  change T.accumulatedMobiusNat (S.length + 1) =
    S.accumulatedMobiusNat S.length
  rw [hstep, htrans, hprefix]
  simp

omit [RiemannSurface X] in
/--
Two based weak handoff skeletons with the same endpoint determine the same
terminal branch data when their terminal selected chart and terminal Mobius
representative agree.
-/
structure TerminalBranchDataEq
    {q : Path x₀ x}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q) :
    Prop where
  /-- The terminal selected charts agree. -/
  terminalCenter_eq : S.terminalCenter = T.terminalCenter
  /-- The terminal accumulated Mobius representatives agree. -/
  terminalMobius_eq : S.terminalMobius = T.terminalMobius

end PathLocalTransitionModelBasedWeakHandoffSkeleton

end HyperbolicMetric

end

end JJMath
