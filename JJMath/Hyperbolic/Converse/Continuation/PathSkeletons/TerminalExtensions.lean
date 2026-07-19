import JJMath.Hyperbolic.Converse.Continuation.PathSkeletons.TerminalRefinement

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

namespace TerminalBranchDataEq

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x₁ y : X} {pS pT : Path x₀ x₁} {suffix : Path x₁ y}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}

omit [RiemannSurface X] in
/--
Exact suffix append preserves terminal branch data.

The two bridge transitions are allowed to live over the two equal terminal
charts, but they must have the same Mobius representative.  This is exactly
what transport across `terminalCenter_eq` supplies.

%%handwave
name:
  Appending the same suffix preserves equal terminal branch data
statement:
  Suppose two skeletons ending at $x_1$ have the same terminal chart center and terminal accumulated representative. Append a common suffix skeleton, using bridge transitions from the two terminal charts to the suffix's initial chart with the same representative. Then the two concatenated skeletons again have the same terminal center and terminal accumulated representative.
proof:
  Both appended skeletons end in the suffix's terminal chart. Their terminal products are obtained from the old terminal products by the equal bridge representative and the common suffix product, so the assumed equalities identify them.
-/
theorem appendSuffixSkeleton
    (H : TerminalBranchDataEq S T)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (AS :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁)
    (AT :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt T.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁)
    (hA : AT.representative = AS.representative) :
    TerminalBranchDataEq
      (S.appendSuffixSkeleton C AS)
      (T.appendSuffixSkeleton C AT) where
  terminalCenter_eq := by
    simp [PathLocalTransitionModelBasedWeakHandoffSkeleton.appendSuffixSkeleton_terminalCenter]
  terminalMobius_eq := by
    rw [appendSuffixSkeleton_terminalMobius_eq S C AS,
      appendSuffixSkeleton_terminalMobius_eq T C AT,
      H.terminalMobius_eq, hA]

omit [RiemannSurface X] in
/--
Exact suffix append, existential form.

Given terminal branch equality at a common endpoint and a componentwise suffix
skeleton, construct skeletons over the honest concatenations by the whole
suffix, with equal terminal branch data.

%%handwave
name:
  Equal terminal branch data extend across any common suffix
statement:
  If skeletons over $p_S,p_T:x_0\rightsquigarrow x_1$ have equal terminal branch data and $C$ is a skeleton over a suffix $\sigma:x_1\rightsquigarrow y$, then there exist skeletons over $p_S*\sigma$ and $p_T*\sigma$ with equal terminal centers and terminal accumulated representatives.
proof:
  Choose a local transition from the common terminal chart to the first suffix chart. Transport it across equality of the two terminal centers to obtain an identical bridge representative on the other side, then append the common suffix and apply preservation under suffix append.
-/
theorem exists_terminalBranchDataEq_after_suffixSkeleton_exactAppend
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (H : TerminalBranchDataEq S T) :
    ∃ (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels (pS.trans suffix))
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels (pT.trans suffix)),
      TerminalBranchDataEq S' T' := by
  classical
  have hC0 : x₁ ∈ (localModels.chartAt (C.centerAt 0)).domain := by
    simpa [C.parameterAt_zero, suffix.source] using
      C.sample_mem_model_domain (0 : Fin (C.length + 1))
  let AS :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁ :=
    Classical.choice
      (localModels.transition_localRealMobius
        S.terminalCenter (C.centerAt 0) x₁
        ⟨S.terminal_endpoint_mem_domain, hC0⟩)
  let AT :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt T.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁ :=
    localRealMobiusTransitionData_congr
      (by rw [H.terminalCenter_eq]) rfl rfl AS
  refine ⟨S.appendSuffixSkeleton C AS, T.appendSuffixSkeleton C AT, ?_⟩
  exact H.appendSuffixSkeleton C AS AT rfl

omit [RiemannSurface X] in
/-- Exact suffix append, terminal-value form.

%%handwave
name:
  Equal terminal values extend across any common suffix
statement:
  Under the hypotheses above, there exist skeletons over $p_S*\sigma$ and $p_T*\sigma$ whose terminal values are equal.
proof:
  Construct appended skeletons with equal terminal branch data; equal terminal centers and terminal representatives imply equality of terminal values.
-/
theorem exists_terminalValue_eq_after_suffixSkeleton_exactAppend
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (H : TerminalBranchDataEq S T) :
    ∃ (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels (pS.trans suffix))
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g localModels (pT.trans suffix)),
      S'.terminalValue = T'.terminalValue := by
  rcases H.exists_terminalBranchDataEq_after_suffixSkeleton_exactAppend C with
    ⟨S', T', H'⟩
  exact ⟨S', T', H'.terminalValue_eq⟩

end TerminalBranchDataEq

omit [RiemannSurface X] in
/--
%%handwave
name:
  Changing the terminal chart preserves the terminal value
statement:
  Let $A$ be local transition data at the endpoint from the terminal chart of a skeleton to another chart. After adjoining this chart change as the final handoff, the terminal value is unchanged.
proof:
  The new accumulated representative is $M A^{-1}$ and the new chart coordinate is $A\cdot\phi(x)$; associativity and cancellation give $(M A^{-1})\cdot(A\cdot\phi(x))=M\cdot\phi(x)$.
-/
@[simp]
theorem terminalChartChangeSkeleton_terminalValue_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (T :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x) :
    (S.terminalChartChangeSkeleton c hc T).terminalValue =
      S.terminalValue := by
  change
    realMobiusRepresentativeAction
        (S.terminalChartChangeSkeleton c hc T).terminalMobius
        ((localModels.chartAt
          (S.terminalChartChangeSkeleton c hc T).terminalCenter).toUpperHalfPlane x) =
      realMobiusRepresentativeAction S.terminalMobius
        ((localModels.chartAt S.terminalCenter).toUpperHalfPlane x)
  rw [S.terminalChartChangeSkeleton_terminalMobius_eq c hc T,
    S.terminalChartChangeSkeleton_terminalCenter c hc T]
  exact localRealMobiusTransitionData_accumulated_handoff
    T T.mem_neighborhood S.terminalMobius

omit [RiemannSurface X] in
/--
After a terminal chart change, the terminal branch formula agrees with the
old one on the actual neighborhood where the final local transition is valid.

%%handwave
name:
  A terminal chart change preserves the branch formula locally
statement:
  If $A$ is a local transition from the old terminal chart to a new chart, then after adjoining this transition the new and old terminal branch formulas agree at every point $z$ of the transition neighborhood.
proof:
  On that neighborhood the new coordinate is $A$ applied to the old coordinate, while the new accumulated representative is $M A^{-1}$; the two $A$ factors cancel.
-/
theorem terminalChartChangeSkeleton_terminalFormulaAt_eq_of_mem
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (T :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x)
    {z : X} (hz : z ∈ T.neighborhood) :
    (S.terminalChartChangeSkeleton c hc T).terminalFormulaAt z =
      S.terminalFormulaAt z := by
  change
    realMobiusRepresentativeAction
        (S.terminalChartChangeSkeleton c hc T).terminalMobius
        ((localModels.chartAt
          (S.terminalChartChangeSkeleton c hc T).terminalCenter).toUpperHalfPlane z) =
      realMobiusRepresentativeAction S.terminalMobius
        ((localModels.chartAt S.terminalCenter).toUpperHalfPlane z)
  rw [S.terminalChartChangeSkeleton_terminalMobius_eq c hc T,
    S.terminalChartChangeSkeleton_terminalCenter c hc T]
  exact localRealMobiusTransitionData_accumulated_handoff
    T hz S.terminalMobius

omit [RiemannSurface X] in
/--
The automatic endpoint transition from the terminal chart of one same-path
skeleton to the terminal chart of another.
-/
noncomputable def terminalChartChangeDataTo
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData
      (localModels.chartAt S.terminalCenter)
      (localModels.chartAt T.terminalCenter)
      x := by
  classical
  exact Classical.choice
    (localModels.transition_localRealMobius S.terminalCenter T.terminalCenter
      x ⟨S.terminal_endpoint_mem_domain, T.terminal_endpoint_mem_domain⟩)

omit [RiemannSurface X] in
/--
Change the terminal chart of `S` to the terminal chart of `T`, inserting only
a final zero-length handoff at the endpoint.
-/
noncomputable def terminalChartChangeSkeletonTo
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p :=
  S.terminalChartChangeSkeleton T.terminalCenter
    T.terminal_endpoint_mem_domain (S.terminalChartChangeDataTo T)

omit [RiemannSurface X] in
/--
%%handwave
name:
  Automatic chart change reaches the prescribed terminal center
statement:
  Changing the terminal chart of a skeleton $S$ to the terminal chart selected by a same-path skeleton $T$ produces a skeleton whose terminal center is the terminal center of $T$.
proof:
  The chart-change construction assigns the prescribed center to its new final vertex.
-/
@[simp]
theorem terminalChartChangeSkeletonTo_terminalCenter
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    (S.terminalChartChangeSkeletonTo T).terminalCenter = T.terminalCenter := by
  simp [terminalChartChangeSkeletonTo]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Automatic terminal chart change preserves the terminal value
statement:
  Replacing the terminal chart of $S$ by the terminal chart of another same-path skeleton leaves the terminal value of $S$ unchanged.
proof:
  Apply terminal-value invariance of a chart change to the automatically selected local transition at the common endpoint.
-/
@[simp]
theorem terminalChartChangeSkeletonTo_terminalValue_eq
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    (S.terminalChartChangeSkeletonTo T).terminalValue = S.terminalValue := by
  simp [terminalChartChangeSkeletonTo]

omit [RiemannSurface X] in
/--
The automatic chart-change-to skeleton has the same adjusted terminal PSL
class as the original skeleton.

%%handwave
name:
  Adjusted terminal class after automatic chart change
statement:
  If $A$ is the automatically chosen transition from the terminal chart of $S$ to that of $T$, then the chart-changed skeleton satisfies $[M_{S'}A]=[M_S]$.
proof:
  The chart-change construction sets $M_{S'}=M_SA^{-1}$; project to $\mathrm{PSL}_2(\mathbb R)$ and cancel $A^{-1}A$.
-/
theorem terminalChartChangeSkeletonTo_adjustedTerminalMobius_projection_eq
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    realMobiusProjection
        ((S.terminalChartChangeSkeletonTo T).terminalMobius *
          (S.terminalChartChangeDataTo T).representative) =
      realMobiusProjection S.terminalMobius := by
  simp [terminalChartChangeSkeletonTo]

omit [RiemannSurface X] in
/--
The automatic terminal chart change agrees with the old terminal branch on
the endpoint-transition neighborhood.

%%handwave
name:
  Local formula invariance under automatic terminal chart change
statement:
  On the neighborhood of the automatically chosen transition from the terminal chart of $S$ to that of a same-path skeleton $T$, the terminal formula of the chart-changed skeleton agrees with the terminal formula of $S$.
proof:
  This is local terminal-formula invariance for a chart change applied to the selected endpoint transition.
-/
theorem terminalChartChangeSkeletonTo_terminalFormulaAt_eq_of_mem
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {z : X} (hz : z ∈ (S.terminalChartChangeDataTo T).neighborhood) :
    (S.terminalChartChangeSkeletonTo T).terminalFormulaAt z =
      S.terminalFormulaAt z := by
  simpa [terminalChartChangeSkeletonTo] using
    S.terminalChartChangeSkeleton_terminalFormulaAt_eq_of_mem
      T.terminalCenter T.terminal_endpoint_mem_domain
      (S.terminalChartChangeDataTo T) hz

omit [RiemannSurface X] in
/--
Append a duplicate terminal vertex to a based weak handoff skeleton over the
same path.  The new final handoff is the identity transition in the terminal
chart, so terminal values are preserved.
-/
noncomputable def terminalStutterSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p where
  length := S.length + 1
  length_pos := Nat.succ_pos S.length
  parameterAt := S.terminalStutterParameterAt
  parameterAt_zero := S.terminalStutterParameterAt_zero
  parameterAt_last := S.terminalStutterParameterAt_last
  parameterAt_mono := S.terminalStutterParameterAt_mono
  centerAt := S.terminalStutterCenterAt
  sample_mem_model_domain := S.terminalStutter_sample_mem_model_domain
  path_segment_mem_model_domain := S.terminalStutter_path_segment_mem_model_domain
  terminal_endpoint_mem_domain := S.terminalStutter_terminal_endpoint_mem_domain
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
          localModels.chartAt (S.terminalStutterCenterAt k.castSucc) =
            localModels.chartAt (S.centerAt k₀.castSucc) := by
        rw [hleft]
        simp
      have hV :
          localModels.chartAt (S.terminalStutterCenterAt k.succ) =
            localModels.chartAt (S.centerAt k₀.succ) := by
        rw [hright]
        simp
      have hpath :
          p (S.terminalStutterParameterAt k.succ) =
            p (S.parameterAt k₀.succ) := by
        rw [hright, S.terminalStutterParameterAt_castSucc]
      exact localRealMobiusTransitionData_congr hU hV hpath
        (S.transitionAt k₀)
    · have hk_last : k = Fin.last S.length := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
          (Nat.le_of_not_gt hk)
      subst k
      have hx :
          p (S.terminalStutterParameterAt (Fin.last (S.length + 1))) ∈
            (localModels.chartAt S.terminalCenter).domain := by
        simpa [S.terminalStutterCenterAt_last] using
          S.terminalStutter_sample_mem_model_domain
            (Fin.last (S.length + 1))
      have hU :
          localModels.chartAt
              (S.terminalStutterCenterAt
                ((Fin.last S.length : Fin (S.length + 1)).castSucc)) =
            localModels.chartAt S.terminalCenter := by
        simp [terminalCenter]
      have hV :
          localModels.chartAt
              (S.terminalStutterCenterAt
                ((Fin.last S.length : Fin (S.length + 1)).succ)) =
            localModels.chartAt S.terminalCenter := by
        rw [fin_last_succ_eq_last]
        simp
      have hpoint :
          p (S.terminalStutterParameterAt
              ((Fin.last S.length : Fin (S.length + 1)).succ)) =
            p (S.terminalStutterParameterAt (Fin.last (S.length + 1))) := by
        rw [fin_last_succ_eq_last]
      exact localRealMobiusTransitionData_congr hU hV hpoint
        (localRealMobiusTransitionData_self
          (localModels.chartAt S.terminalCenter) hx)
  initialTransition := by
    exact localRealMobiusTransitionData_congr rfl
      (by simp [S.terminalStutterCenterAt_zero]) rfl S.initialTransition

omit [RiemannSurface X] in
/--
%%handwave
name:
  Terminal stuttering preserves the terminal center
statement:
  Adding a duplicate final vertex at parameter $1$ with the same terminal chart leaves the terminal center unchanged.
proof:
  The new last center is defined to be the old terminal center.
-/
@[simp]
theorem terminalStutterSkeleton_terminalCenter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterSkeleton.terminalCenter = S.terminalCenter := by
  simp [terminalStutterSkeleton, terminalCenter]

omit [RiemannSurface X] in
/--
Along the old part of a terminal-stutter skeleton, the accumulated Mobius
product agrees with the original skeleton.

%%handwave
name:
  Terminal stuttering preserves accumulated products on the old prefix
statement:
  If $S'$ is obtained from $S$ by duplicating the terminal vertex, then $M_j(S')=M_j(S)$ for every $j$ up to the original length.
proof:
  Induct on $j$; the initial transition and every old handoff representative are transported unchanged, so the same product recurrence applies.
-/
theorem terminalStutterSkeleton_accumulatedMobiusNat_eq_of_le
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ n : ℕ, n ≤ S.length →
      S.terminalStutterSkeleton.accumulatedMobiusNat n =
        S.accumulatedMobiusNat n := by
  intro n hn
  induction n with
  | zero =>
      simp [terminalStutterSkeleton, accumulatedMobiusNat]
  | succ n ih =>
      have hnlt : n < S.length := Nat.succ_le_iff.mp hn
      have hnle : n ≤ S.length := Nat.le_of_lt hnlt
      let T := S.terminalStutterSkeleton
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
        simp [T, terminalStutterSkeleton, hnlt]
      rw [hTstep, ih hnle, htrans, hSstep]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Terminal stuttering preserves the terminal Möbius representative
statement:
  Duplicating the terminal vertex with an identity handoff leaves the terminal accumulated representative unchanged.
proof:
  The accumulated product through the old final vertex is unchanged, and the added transition representative is the identity.
-/
@[simp]
theorem terminalStutterSkeleton_terminalMobius_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterSkeleton.terminalMobius = S.terminalMobius := by
  let T := S.terminalStutterSkeleton
  have hprefix :
      T.accumulatedMobiusNat S.length = S.accumulatedMobiusNat S.length :=
    S.terminalStutterSkeleton_accumulatedMobiusNat_eq_of_le S.length le_rfl
  have hstep :
      T.accumulatedMobiusNat (S.length + 1) =
        T.accumulatedMobiusNat S.length *
          (T.transitionAt (Fin.last S.length)).representative⁻¹ := by
    exact T.accumulatedMobiusNat_succ_of_lt (Nat.lt_succ_self S.length)
  have htrans :
      (T.transitionAt (Fin.last S.length)).representative = 1 := by
    simp [T, terminalStutterSkeleton, localRealMobiusTransitionData_self]
  change T.accumulatedMobiusNat (S.length + 1) =
    S.accumulatedMobiusNat S.length
  rw [hstep, htrans, hprefix]
  simp

omit [RiemannSurface X] in
/--
%%handwave
name:
  Terminal stuttering preserves the terminal value
statement:
  Adding a duplicate terminal vertex with identity transition does not alter the terminal value.
proof:
  Both the terminal center and terminal accumulated representative are preserved, so the defining endpoint evaluation is unchanged.
-/
@[simp]
theorem terminalStutterSkeleton_terminalValue_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterSkeleton.terminalValue = S.terminalValue := by
  simp [terminalValue]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Terminal stuttering preserves the complete terminal formula
statement:
  Adding a duplicate terminal vertex with identity transition leaves the terminal branch formula unchanged at every $z\in X$.
proof:
  The stutter preserves both the terminal center and the terminal accumulated representative; substitute these equalities in the formula.
-/
@[simp]
theorem terminalStutterSkeleton_terminalFormulaAt_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (z : X) :
    S.terminalStutterSkeleton.terminalFormulaAt z = S.terminalFormulaAt z := by
  exact
    S.terminalStutterSkeleton.terminalFormulaAt_eq_of_terminalMobius_eq_terminalCenter_eq
      S
      S.terminalStutterSkeleton_terminalMobius_eq
      S.terminalStutterSkeleton_terminalCenter
      z

omit [RiemannSurface X] in
/--
A skeleton over a path that is pointwise constant at the basepoint, with its
terminal chart and terminal Mobius normalized to match the initial branch of a
given suffix skeleton.

This is the initial-prefix analogue of terminal stuttering.  It is used when
a raw endpoint cut contains one or more constant basepoint pieces before the
actual path.
-/
noncomputable def constantPrefixSkeletonForInitialChart
    {x : X} {p : Path x₀ x}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {κ : Path x₀ x₀} (hκ : ∀ t : unitInterval, κ t = x₀) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels κ where
  length := 1
  length_pos := by omega
  parameterAt := fun i => if (i : ℕ) = 0 then 0 else 1
  parameterAt_zero := by simp
  parameterAt_last := by simp
  parameterAt_mono := by
    intro k
    fin_cases k
    simp
  centerAt := fun _ => C.centerAt 0
  sample_mem_model_domain := by
    intro i
    have hx₀_mem :
        x₀ ∈ (localModels.chartAt (C.centerAt 0)).domain := by
      simpa [C.parameterAt_zero, p.source] using
        C.sample_mem_model_domain (0 : Fin (C.length + 1))
    rw [hκ]
    exact hx₀_mem
  path_segment_mem_model_domain := by
    intro k t ht_left ht_right
    have hx₀_mem :
        x₀ ∈ (localModels.chartAt (C.centerAt 0)).domain := by
      simpa [C.parameterAt_zero, p.source] using
        C.sample_mem_model_domain (0 : Fin (C.length + 1))
    rw [hκ t]
    exact hx₀_mem
  terminal_endpoint_mem_domain := by
    have hx₀_mem :
        x₀ ∈ (localModels.chartAt (C.centerAt 0)).domain := by
      simpa [C.parameterAt_zero, p.source] using
        C.sample_mem_model_domain (0 : Fin (C.length + 1))
    simpa [terminalCenter] using hx₀_mem
  transitionAt := by
    intro k
    have hx₀_mem :
        x₀ ∈ (localModels.chartAt (C.centerAt 0)).domain := by
      simpa [C.parameterAt_zero, p.source] using
        C.sample_mem_model_domain (0 : Fin (C.length + 1))
    have hpoint :
        κ ((fun i : Fin (1 + 1) => if (i : ℕ) = 0 then 0 else 1) k.succ) =
          x₀ := hκ _
    exact
      localRealMobiusTransitionData_self
        (localModels.chartAt (C.centerAt 0))
        (by simpa [hpoint] using hx₀_mem)
  initialTransition := C.initialTransition

omit [RiemannSurface X] in
/--
%%handwave
name:
  Constant basepoint prefix ends in the suffix's initial chart
statement:
  The one-segment skeleton on a path constantly equal to $x_0$, normalized using a suffix skeleton $C$, has terminal center equal to the first chart center $c_0$ of $C$.
proof:
  Both vertices of the constant-prefix skeleton are assigned the center $c_0$.
-/
@[simp]
theorem constantPrefixSkeletonForInitialChart_terminalCenter
    {x : X} {p : Path x₀ x}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {κ : Path x₀ x₀} (hκ : ∀ t : unitInterval, κ t = x₀) :
    (C.constantPrefixSkeletonForInitialChart hκ).terminalCenter =
      C.centerAt 0 := by
  simp [constantPrefixSkeletonForInitialChart, terminalCenter]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Terminal product of the normalized constant prefix
statement:
  The terminal accumulated representative of the constant basepoint prefix normalized to a suffix $C$ is the inverse $T_0^{-1}$ of the initial transition representative of $C$.
proof:
  The prefix begins with the same initial transition as $C$ and has a single identity self-transition, so its terminal product is $T_0^{-1}1^{-1}=T_0^{-1}$.
-/
@[simp]
theorem constantPrefixSkeletonForInitialChart_terminalMobius_eq
    {x : X} {p : Path x₀ x}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {κ : Path x₀ x₀} (hκ : ∀ t : unitInterval, κ t = x₀) :
    (C.constantPrefixSkeletonForInitialChart hκ).terminalMobius =
      C.initialTransition.representative⁻¹ := by
  let K := C.constantPrefixSkeletonForInitialChart hκ
  have hstep :
      K.accumulatedMobiusNat 1 =
        K.accumulatedMobiusNat 0 *
          (K.transitionAt
            (⟨0, by simp [K, constantPrefixSkeletonForInitialChart]⟩ :
              Fin K.length)).representative⁻¹ := by
    exact K.accumulatedMobiusNat_succ_of_lt (by simp [K, constantPrefixSkeletonForInitialChart])
  change K.accumulatedMobiusNat 1 = C.initialTransition.representative⁻¹
  rw [hstep]
  simp [K, constantPrefixSkeletonForInitialChart, localRealMobiusTransitionData_self]

omit [RiemannSurface X] in
/--
Appending a suffix after a pointwise-constant basepoint prefix preserves the
suffix terminal value, provided the prefix is normalized to the suffix's
initial chart.

%%handwave
name:
  A constant basepoint prefix does not change terminal value
statement:
  If $\kappa:x_0\rightsquigarrow x_0$ is pointwise constant and $C$ is a skeleton over $p:x_0\rightsquigarrow x$, then there exists a skeleton over $\kappa*p$ with the same terminal value as $C$.
proof:
  Build the constant prefix using the initial chart and initial normalization of $C$, join it to $C$ by the identity transition, and compare the product with the factorization of $C$'s terminal representative. The terminal centers and representatives agree.
-/
theorem exists_terminalValue_eq_after_constantPrefix_trans
    {x : X} {p : Path x₀ x}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {κ : Path x₀ x₀} (hκ : ∀ t : unitInterval, κ t = x₀) :
    ∃ (S :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (κ.trans p)),
      S.terminalValue = C.terminalValue := by
  classical
  let K := C.constantPrefixSkeletonForInitialChart hκ
  have hx₀_mem :
      x₀ ∈ (localModels.chartAt (C.centerAt 0)).domain := by
    simpa [C.parameterAt_zero, p.source] using
      C.sample_mem_model_domain (0 : Fin (C.length + 1))
  let A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt K.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₀ :=
    localRealMobiusTransitionData_congr
      (by simp [K])
      rfl rfl
      (localRealMobiusTransitionData_self
        (localModels.chartAt (C.centerAt 0)) hx₀_mem)
  refine ⟨K.appendSuffixSkeleton C A, ?_⟩
  have hMobius :
      (K.appendSuffixSkeleton C A).terminalMobius =
        C.terminalMobius := by
    rw [appendSuffixSkeleton_terminalMobius_eq K C A,
      terminalMobius_eq_initial_mul_suffixInternalTransitionProduct C]
    simp [K, A, localRealMobiusTransitionData_self]
  have hCenter :
      (K.appendSuffixSkeleton C A).terminalCenter = C.terminalCenter := by
    simp [K]
  change
    realMobiusRepresentativeAction
        (K.appendSuffixSkeleton C A).terminalMobius
        ((localModels.chartAt
          (K.appendSuffixSkeleton C A).terminalCenter).toUpperHalfPlane x) =
      realMobiusRepresentativeAction C.terminalMobius
        ((localModels.chartAt C.terminalCenter).toUpperHalfPlane x)
  rw [hMobius, hCenter]

omit [RiemannSurface X] in
/--
Appending a pointwise-constant basepoint prefix preserves terminal branch
data, provided the prefix is normalized to the suffix's initial chart.

%%handwave
name:
  A constant basepoint prefix preserves terminal branch data
statement:
  Under the preceding hypotheses, there exists a skeleton over $\kappa*p$ whose terminal center and terminal accumulated representative equal those of $C$.
proof:
  Append $C$ to the normalized one-segment constant prefix through the identity transition. Direct product factorization shows equality of the terminal representatives, and both constructions end in the terminal chart of $C$.
-/
theorem exists_terminalBranchDataEq_after_constantPrefix_trans
    {x : X} {p : Path x₀ x}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {κ : Path x₀ x₀} (hκ : ∀ t : unitInterval, κ t = x₀) :
    ∃ (S :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (κ.trans p)),
      TerminalBranchDataEq S C := by
  classical
  let K := C.constantPrefixSkeletonForInitialChart hκ
  have hx₀_mem :
      x₀ ∈ (localModels.chartAt (C.centerAt 0)).domain := by
    simpa [C.parameterAt_zero, p.source] using
      C.sample_mem_model_domain (0 : Fin (C.length + 1))
  let A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt K.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₀ :=
    localRealMobiusTransitionData_congr
      (by simp [K])
      rfl rfl
      (localRealMobiusTransitionData_self
        (localModels.chartAt (C.centerAt 0)) hx₀_mem)
  refine ⟨K.appendSuffixSkeleton C A, ?_⟩
  constructor
  · simp [K]
  · rw [appendSuffixSkeleton_terminalMobius_eq K C A,
      terminalMobius_eq_initial_mul_suffixInternalTransitionProduct C]
    simp [K, A, localRealMobiusTransitionData_self]

omit [RiemannSurface X] in
/--
Appending a pointwise-constant terminal suffix preserves the terminal value.

%%handwave
name:
  A constant terminal suffix does not change terminal value
statement:
  If $\sigma:x\rightsquigarrow x$ is pointwise constant and $C$ is a skeleton over $p:x_0\rightsquigarrow x$, then there exists a skeleton over $p*\sigma$ with terminal value equal to that of $C$.
proof:
  Extend $C$ along $\sigma$ inside its terminal chart. The extension has the same terminal formula, and evaluation at the unchanged endpoint $x$ gives equality of terminal values.
-/
theorem exists_terminalValue_eq_after_constantSuffix_trans
    {x : X} {p : Path x₀ x}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {σ : Path x x} (hσ : ∀ t : unitInterval, σ t = x) :
    ∃ (S :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (p.trans σ)),
      S.terminalValue = C.terminalValue := by
  have hσmem :
      ∀ t : unitInterval,
        σ t ∈ (localModels.chartAt C.terminalCenter).domain := by
    intro t
    rw [hσ t]
    exact C.terminal_endpoint_mem_domain
  refine ⟨C.terminalExtensionAlongSkeleton σ hσmem, ?_⟩
  calc
    (C.terminalExtensionAlongSkeleton σ hσmem).terminalValue =
        (C.terminalExtensionAlongSkeleton σ hσmem).terminalFormulaAt x := by
          exact
            (C.terminalExtensionAlongSkeleton σ hσmem).terminalFormulaAt_endpoint.symm
    _ = C.terminalFormulaAt x := by
          exact C.terminalExtensionAlongSkeleton_terminalFormulaAt_eq σ hσmem x
    _ = C.terminalValue := C.terminalFormulaAt_endpoint

omit [RiemannSurface X] in
/--
Appending a pointwise-constant terminal suffix preserves terminal branch data.

%%handwave
name:
  A constant terminal suffix preserves terminal branch data
statement:
  If $\sigma:x\rightsquigarrow x$ is pointwise constant, then a skeleton over $p$ extends to one over $p*\sigma$ with the same terminal center and terminal accumulated representative.
proof:
  Since every point of $\sigma$ is the endpoint $x$, the suffix remains in the old terminal chart. The standard terminal extension along that chart preserves both terminal center and terminal representative.
-/
theorem exists_terminalBranchDataEq_after_constantSuffix_trans
    {x : X} {p : Path x₀ x}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {σ : Path x x} (hσ : ∀ t : unitInterval, σ t = x) :
    ∃ (S :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (p.trans σ)),
      TerminalBranchDataEq S C := by
  have hσmem :
      ∀ t : unitInterval,
        σ t ∈ (localModels.chartAt C.terminalCenter).domain := by
    intro t
    rw [hσ t]
    exact C.terminal_endpoint_mem_domain
  refine ⟨C.terminalExtensionAlongSkeleton σ hσmem, ?_⟩
  constructor
  · rw [C.terminalExtensionAlongSkeleton_terminalCenter σ hσmem]
  · rw [C.terminalExtensionAlongSkeleton_terminalMobius_eq σ hσmem]

omit [RiemannSurface X] in
/-- Iterate terminal-stutter refinements `n` times. -/
noncomputable def terminalStutterIterateSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ℕ → PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  | 0 => S
  | n + 1 => (terminalStutterIterateSkeleton S n).terminalStutterSkeleton

omit [RiemannSurface X] in
/--
%%handwave
name:
  Zero terminal stutters leave the skeleton unchanged
statement:
  Iterating the terminal-vertex duplication operation zero times returns the original skeleton.
proof:
  This is the zero clause of the iteration.
-/
@[simp]
theorem terminalStutterIterateSkeleton_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterIterateSkeleton 0 = S :=
  rfl

omit [RiemannSurface X] in
/--
%%handwave
name:
  Successor recursion for iterated terminal stuttering
statement:
  Applying $n+1$ terminal stutters is the same as applying $n$ stutters and then duplicating the resulting terminal vertex once more.
proof:
  This is the successor clause of the iteration.
-/
@[simp]
theorem terminalStutterIterateSkeleton_succ
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (n : ℕ) :
    S.terminalStutterIterateSkeleton (n + 1) =
      (S.terminalStutterIterateSkeleton n).terminalStutterSkeleton :=
  rfl

omit [RiemannSurface X] in
/-- Iterated terminal-stutter refinements preserve terminal value.

%%handwave
name:
  Iterated terminal stuttering preserves the terminal value
statement:
  For every $n\ge0$, duplicating the terminal vertex $n$ times leaves the terminal value unchanged.
proof:
  Induct on $n$ and use terminal-value invariance of one stutter in the successor step.
-/
theorem terminalStutterIterateSkeleton_terminalValue_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ n : ℕ,
      (S.terminalStutterIterateSkeleton n).terminalValue = S.terminalValue := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [terminalStutterIterateSkeleton_succ, ih]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Length after iterated terminal stuttering
statement:
  If a skeleton has length $\ell$, then after $n$ terminal stutters its length is $\ell+n$.
proof:
  Induct on $n$; each stutter adds exactly one segment.
-/
@[simp]
theorem terminalStutterIterateSkeleton_length
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ n : ℕ, (S.terminalStutterIterateSkeleton n).length = S.length + n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [terminalStutterIterateSkeleton_succ]
      simp [terminalStutterSkeleton, ih, Nat.add_assoc]

omit [RiemannSurface X] in
/--
Iterated terminal stutters preserve every original subdivision parameter in
the initial prefix.

%%handwave
name:
  Original parameters survive iterated terminal stuttering
statement:
  After any number $m$ of terminal stutters, every original parameter $t_j$ with $0\le j\le\ell$ remains the parameter at index $j$.
proof:
  Induct on $m$. One terminal stutter embeds all previous vertices unchanged, so the induction hypothesis transfers to the new skeleton.
-/
theorem terminalStutterIterateSkeleton_parameterAt_prefix
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m n
      (hnOld : n < S.length + 1)
      (hnNew : n < (S.terminalStutterIterateSkeleton m).length + 1),
      (S.terminalStutterIterateSkeleton m).parameterAt ⟨n, hnNew⟩ =
        S.parameterAt ⟨n, hnOld⟩ := by
  intro m
  induction m with
  | zero =>
      intro n hnOld hnNew
      rfl
  | succ m ih =>
      intro n hnOld hnNew
      let R := S.terminalStutterIterateSkeleton m
      have hnR : n < R.length + 1 := by
        rw [terminalStutterIterateSkeleton_length] at hnNew
        rw [terminalStutterIterateSkeleton_length]
        omega
      have hidx :
          (⟨n, hnNew⟩ : Fin ((S.terminalStutterIterateSkeleton (m + 1)).length + 1)) =
            ((⟨n, hnR⟩ : Fin (R.length + 1)).castSucc) := by
        ext
        rfl
      change R.terminalStutterSkeleton.parameterAt
          (⟨n, hnNew⟩ :
            Fin ((S.terminalStutterIterateSkeleton (m + 1)).length + 1)) =
        S.parameterAt ⟨n, hnOld⟩
      rw [hidx]
      change R.terminalStutterParameterAt
          ((⟨n, hnR⟩ : Fin (R.length + 1)).castSucc) =
        S.parameterAt ⟨n, hnOld⟩
      rw [R.terminalStutterParameterAt_castSucc ⟨n, hnR⟩]
      exact ih n hnOld hnR

omit [RiemannSurface X] in
/--
Every parameter added by iterated terminal stutters is the terminal parameter
`1`.

%%handwave
name:
  Every stuttered tail parameter equals one
statement:
  After iterating terminal stutters, every parameter whose index is at least the original length is $1$.
proof:
  Induct on the number of stutters. Existing tail vertices keep their value $1$, and the only new vertex is the last vertex, also assigned $1$.
-/
theorem terminalStutterIterateSkeleton_parameterAt_tail
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m n
      (_hTail : S.length ≤ n)
      (hnNew : n < (S.terminalStutterIterateSkeleton m).length + 1),
      (S.terminalStutterIterateSkeleton m).parameterAt ⟨n, hnNew⟩ = 1 := by
  intro m
  induction m with
  | zero =>
      intro n _hTail hnNew
      have hnNew' : n < S.length + 1 := by
        simpa using hnNew
      have hn_eq : n = S.length := by omega
      subst n
      simpa using S.parameterAt_last
  | succ m ih =>
      intro n hTail hnNew
      let R := S.terminalStutterIterateSkeleton m
      by_cases hnR : n < R.length + 1
      · have hidx :
            (⟨n, hnNew⟩ :
              Fin ((S.terminalStutterIterateSkeleton (m + 1)).length + 1)) =
              ((⟨n, hnR⟩ : Fin (R.length + 1)).castSucc) := by
          ext
          rfl
        change R.terminalStutterSkeleton.parameterAt
            (⟨n, hnNew⟩ :
              Fin ((S.terminalStutterIterateSkeleton (m + 1)).length + 1)) =
          1
        rw [hidx]
        change R.terminalStutterParameterAt
            ((⟨n, hnR⟩ : Fin (R.length + 1)).castSucc) =
          1
        rw [R.terminalStutterParameterAt_castSucc ⟨n, hnR⟩]
        exact ih n hTail hnR
      · have hn_last : n = R.length + 1 := by
          have hn_bound : n < R.length + 2 := by
            have hLenSucc :
                (S.terminalStutterIterateSkeleton (m + 1)).length =
                  R.length + 1 := by
              change R.terminalStutterSkeleton.length = R.length + 1
              simp [terminalStutterSkeleton]
            omega
          omega
        subst n
        have hidx :
            (⟨R.length + 1, hnNew⟩ :
              Fin ((S.terminalStutterIterateSkeleton (m + 1)).length + 1)) =
              (Fin.last (R.length + 1) :
                Fin (R.terminalStutterSkeleton.length + 1)) := by
          ext
          rfl
        change R.terminalStutterSkeleton.parameterAt
            (⟨R.length + 1, hnNew⟩ :
              Fin ((S.terminalStutterIterateSkeleton (m + 1)).length + 1)) =
          1
        rw [hidx]
        exact R.terminalStutterParameterAt_last

omit [RiemannSurface X] in
/--
If `T` has the same initial subdivision parameters as `S` and only terminal
duplicates after `S.length`, then iterated terminal stuttering of `S` aligns
its parameter list with `T`.

%%handwave
name:
  Terminal stuttering aligns a matching prefix with a terminal tail
statement:
  Suppose $\ell_S\le\ell_T$, the parameters of $S$ and $T$ agree through index $\ell_S$, and every remaining parameter of $T$ equals $1$. After $\ell_T-\ell_S$ terminal stutters, $S$ has length $\ell_T$ and agrees with $T$ at every subdivision parameter.
proof:
  The length formula gives the desired length. At an index in the old prefix use preservation of original parameters and the prefix hypothesis; at a tail index both the stuttered skeleton and $T$ have parameter $1$.
-/
theorem terminalStutterIterateSkeleton_parameterAt_eq_of_prefix_and_tail
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (hLe : S.length ≤ T.length)
    (hPrefix :
      ∀ n (hnS : n ≤ S.length) (hnT : n ≤ T.length),
        S.parameterAt ⟨n, Nat.lt_succ_of_le hnS⟩ =
          T.parameterAt ⟨n, Nat.lt_succ_of_le hnT⟩)
    (hTail :
      ∀ n (_hSn : S.length ≤ n) (hnT : n ≤ T.length),
        T.parameterAt ⟨n, Nat.lt_succ_of_le hnT⟩ = 1) :
    let U := S.terminalStutterIterateSkeleton (T.length - S.length)
    U.length = T.length ∧
      ∀ n (hnU : n ≤ U.length) (hnT : n ≤ T.length),
        U.parameterAt ⟨n, Nat.lt_succ_of_le hnU⟩ =
          T.parameterAt ⟨n, Nat.lt_succ_of_le hnT⟩ := by
  classical
  intro U
  have hLen : U.length = T.length := by
    simp [U]
    omega
  refine ⟨hLen, ?_⟩
  intro n hnU hnT
  by_cases hnPrefix : n ≤ S.length
  · have hnOld : n < S.length + 1 := Nat.lt_succ_of_le hnPrefix
    have hnNew : n < U.length + 1 := Nat.lt_succ_of_le hnU
    have hU :
        U.parameterAt ⟨n, hnNew⟩ =
          S.parameterAt ⟨n, hnOld⟩ := by
      simpa [U] using
        S.terminalStutterIterateSkeleton_parameterAt_prefix
          (T.length - S.length) n hnOld hnNew
    simpa using hU.trans (hPrefix n hnPrefix hnT)
  · have hSn : S.length ≤ n := by omega
    have hnNew : n < U.length + 1 := Nat.lt_succ_of_le hnU
    have hU :
        U.parameterAt ⟨n, hnNew⟩ = 1 := by
      simpa [U] using
        S.terminalStutterIterateSkeleton_parameterAt_tail
          (T.length - S.length) n hSn hnNew
    rw [hU, hTail n hSn hnT]

omit [RiemannSurface X] in
/--
The vertex at which an interior segment split is inserted.

For a segment `k`, this is the new vertex between the old vertices
`k.castSucc` and `k.succ`.
-/
def segmentSplitInsertVertex
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) : Fin (S.length + 2) :=
  (k.succ : Fin (S.length + 1)).castSucc

omit [RiemannSurface X] in
/--
Subdivision parameters after inserting a point `τ` into segment `k`.

The old vertices are embedded by `succAbove`, while the inserted vertex is
assigned parameter `τ`.
-/
noncomputable def segmentSplitParameterAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval) :
    Fin (S.length + 2) → unitInterval :=
  fun i =>
    if i = S.segmentSplitInsertVertex k then
      τ
    else
      S.parameterAt ((k.succ : Fin (S.length + 1)).predAbove i)

omit [RiemannSurface X] in
/--
Centers after inserting a point `τ` into segment `k`.  The inserted vertex
uses the same chart as the left half of the split segment.
-/
noncomputable def segmentSplitCenterAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    Fin (S.length + 2) → X :=
  fun i =>
    if i = S.segmentSplitInsertVertex k then
      S.centerAt k.castSucc
    else
      S.centerAt ((k.succ : Fin (S.length + 1)).predAbove i)

omit [RiemannSurface X] in
/--
%%handwave
name:
  A split assigns the inserted parameter to the new vertex
statement:
  Splitting segment $k$ at $\tau$ assigns parameter $\tau$ to the newly inserted vertex between $k$ and $k+1$.
proof:
  The inserted-index branch of the new parameter function returns $\tau$.
-/
@[simp]
theorem segmentSplitParameterAt_insert
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval) :
    S.segmentSplitParameterAt k τ (S.segmentSplitInsertVertex k) = τ := by
  simp [segmentSplitParameterAt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  A split assigns the left chart to the new vertex
statement:
  Splitting segment $k$ assigns its new vertex the original left chart center $c_k$.
proof:
  The inserted-index branch of the new center function returns $c_k$.
-/
@[simp]
theorem segmentSplitCenterAt_insert
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    S.segmentSplitCenterAt k (S.segmentSplitInsertVertex k) =
      S.centerAt k.castSucc := by
  simp [segmentSplitCenterAt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  A segment split preserves every old parameter
statement:
  Under the order-preserving inclusion of old vertices into the subdivision obtained by splitting segment $k$, the parameter attached to every old vertex $i$ remains $t_i$.
proof:
  An included old vertex is not the inserted vertex, and deleting the inserted position returns its original index.
-/
@[simp]
theorem segmentSplitParameterAt_old
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (i : Fin (S.length + 1)) :
    S.segmentSplitParameterAt k τ
        ((S.segmentSplitInsertVertex k).succAbove i) =
      S.parameterAt i := by
  unfold segmentSplitParameterAt segmentSplitInsertVertex
  rw [if_neg]
  · rw [Fin.predAbove_succAbove]
  · exact Fin.succAbove_ne _ _

omit [RiemannSurface X] in
/--
The parameter tuple of a segment split is the old parameter tuple with the
split parameter inserted at the new vertex.

%%handwave
name:
  Parameter tuple after splitting a segment
statement:
  The parameter tuple obtained by splitting segment $k$ at $\tau$ is exactly the old tuple $(t_0,\ldots,t_n)$ with $\tau$ inserted between $t_k$ and $t_{k+1}$.
proof:
  Compare the functions at the inserted index, where both give $\tau$, and at every other index, where deletion of the inserted position recovers the corresponding old parameter.
-/
theorem segmentSplitParameterAt_eq_insertNth
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval) :
    S.segmentSplitParameterAt k τ =
      Fin.insertNth (S.segmentSplitInsertVertex k) τ S.parameterAt := by
  funext i
  by_cases hi : i = S.segmentSplitInsertVertex k
  · subst i
    simp [segmentSplitParameterAt]
  · let old : Fin (S.length + 1) := (k.succ : Fin (S.length + 1)).predAbove i
    have hsucc :
        (S.segmentSplitInsertVertex k).succAbove old = i := by
      simpa [old, segmentSplitInsertVertex] using
        (Fin.succAbove_predAbove (p := (k.succ : Fin (S.length + 1)))
          (i := i) (by simpa [segmentSplitInsertVertex] using hi))
    rw [← hsucc]
    rw [S.segmentSplitParameterAt_old k τ old]
    rw [Fin.insertNth_apply_succAbove]

omit [RiemannSurface X] in
/--
%%handwave
name:
  A segment split preserves every old chart center
statement:
  Under the inclusion of old vertices into a split subdivision, every old center $c_i$ remains attached to the image of vertex $i$.
proof:
  The included old vertex is distinct from the inserted position, and deleting that position recovers index $i$.
-/
@[simp]
theorem segmentSplitCenterAt_old
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (i : Fin (S.length + 1)) :
    S.segmentSplitCenterAt k
        ((S.segmentSplitInsertVertex k).succAbove i) =
      S.centerAt i := by
  unfold segmentSplitCenterAt segmentSplitInsertVertex
  rw [if_neg]
  · rw [Fin.predAbove_succAbove]
  · exact Fin.succAbove_ne _ _

omit [RiemannSurface X] in
/-- The first old vertex remains the first vertex after a segment split.

%%handwave
name:
  A segment split keeps the first vertex fixed
statement:
  Inserting a vertex strictly after the left endpoint sends the old vertex $0$ to the new vertex $0$.
proof:
  The inserted position is $k+1>0$, so order-preserving insertion does not shift index $0$.
-/
theorem segmentSplitInsertVertex_succAbove_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    (S.segmentSplitInsertVertex k).succAbove (0 : Fin (S.length + 1)) =
      0 := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change (0 : ℕ) < (k : ℕ) + 1
    exact Nat.succ_pos _

omit [RiemannSurface X] in
/-- The last old vertex remains the last vertex after a segment split.

%%handwave
name:
  A segment split sends the old last vertex to the new last vertex
statement:
  If the original last vertex has index $n$, then after inserting one vertex its order-preserving image is the new last vertex of index $n+1$.
proof:
  The inserted position is at most $n$, so the old last index is shifted upward by one.
-/
theorem segmentSplitInsertVertex_succAbove_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    (S.segmentSplitInsertVertex k).succAbove (Fin.last S.length) =
      Fin.last (S.length + 1) := by
  rw [Fin.succAbove_of_le_castSucc]
  · exact fin_last_succ_eq_last
  · change (k : ℕ) + 1 ≤ S.length
    exact k.isLt

omit [RiemannSurface X] in
/-- The old left endpoint of the split segment embeds as the vertex before the insertion.

%%handwave
name:
  The old left endpoint precedes the inserted split vertex
statement:
  When a vertex is inserted at position $k+1$, the old left endpoint $k$ remains at position $k$.
proof:
  Since $k<k+1$, insertion does not shift that index.
-/
theorem segmentSplitInsertVertex_succAbove_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    (S.segmentSplitInsertVertex k).succAbove k.castSucc =
      (k.castSucc : Fin (S.length + 1)).castSucc := by
  rw [Fin.succAbove_of_castSucc_lt]
  change (k : ℕ) < (k : ℕ) + 1
  exact Nat.lt_succ_self _

omit [RiemannSurface X] in
/-- The old right endpoint of the split segment embeds as the vertex after the insertion.

%%handwave
name:
  The old right endpoint follows the inserted split vertex
statement:
  When a vertex is inserted at position $k+1$, the old right endpoint $k+1$ moves to position $k+2$.
proof:
  An old index at or beyond the inserted position is shifted upward by one.
-/
theorem segmentSplitInsertVertex_succAbove_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    (S.segmentSplitInsertVertex k).succAbove k.succ =
      (k.succ : Fin (S.length + 1)).succ := by
  rw [Fin.succAbove_of_le_castSucc]
  rfl

omit [RiemannSurface X] in
/-- Old vertices strictly before the split segment embed unchanged on the left.

%%handwave
name:
  Left endpoints before a split keep their indices
statement:
  If $j<k$, then the old left endpoint at index $j$ remains at index $j$ after inserting a vertex in segment $k$.
proof:
  The index $j$ lies strictly before the insertion position $k+1$, so it is not shifted.
-/
theorem segmentSplitInsertVertex_succAbove_before_castSucc
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (j : Fin (S.length + 1))
    (hj : (j : ℕ) < (k : ℕ)) :
    (S.segmentSplitInsertVertex k).succAbove
        ((⟨j, Nat.lt_trans hj k.isLt⟩ : Fin S.length).castSucc) =
      j.castSucc := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact_mod_cast Nat.lt_succ_of_lt hj

omit [RiemannSurface X] in
/-- Old right vertices strictly before the split segment embed unchanged.

%%handwave
name:
  Right endpoints before a split keep their indices
statement:
  If $j<k$, then the old right endpoint at index $j+1$ remains at index $j+1$ after inserting a vertex in segment $k$.
proof:
  Since $j+1<k+1$, this endpoint lies before the inserted position and is not shifted.
-/
theorem segmentSplitInsertVertex_succAbove_before_succ
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (j : Fin (S.length + 1))
    (hj : (j : ℕ) < (k : ℕ)) :
    (S.segmentSplitInsertVertex k).succAbove
        ((⟨j, Nat.lt_trans hj k.isLt⟩ : Fin S.length).succ) =
      j.succ := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact_mod_cast Nat.succ_lt_succ hj

omit [RiemannSurface X] in
/-- Old vertices strictly after the split segment embed by shifting one step.

%%handwave
name:
  Left endpoints after a split shift by one
statement:
  If $j>k+1$, the old vertex $j-1$ is sent to the new vertex $j$ when segment $k$ is split.
proof:
  The old index lies after the inserted position and hence is shifted upward by one.
-/
theorem segmentSplitInsertVertex_succAbove_after_castSucc
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (j : Fin (S.length + 1))
    (hj : (k : ℕ) + 1 < (j : ℕ)) :
    (S.segmentSplitInsertVertex k).succAbove
        ((⟨(j : ℕ) - 1, by omega⟩ : Fin S.length).castSucc) =
      j.castSucc := by
  rw [Fin.succAbove_of_le_castSucc]
  · ext
    simp
    omega
  · exact_mod_cast Nat.le_pred_of_lt hj

omit [RiemannSurface X] in
/-- Old right vertices strictly after the split segment embed by shifting one step.

%%handwave
name:
  Right endpoints after a split shift by one
statement:
  If $j>k+1$, the right endpoint following old vertex $j-1$ is sent to the right endpoint following new vertex $j$.
proof:
  Both indices lie beyond the inserted position, so order-preserving insertion adds one to the old index.
-/
theorem segmentSplitInsertVertex_succAbove_after_succ
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (j : Fin (S.length + 1))
    (hj : (k : ℕ) + 1 < (j : ℕ)) :
    (S.segmentSplitInsertVertex k).succAbove
        ((⟨(j : ℕ) - 1, by omega⟩ : Fin S.length).succ) =
      j.succ := by
  rw [Fin.succAbove_of_le_castSucc]
  · ext
    simp
    omega
  · change (k : ℕ) + 1 ≤ (j : ℕ) - 1 + 1
    omega

omit [RiemannSurface X] in
/--
%%handwave
name:
  Splitting a segment preserves the initial parameter
statement:
  The parameter at the first vertex remains $0$ after an interior segment split.
proof:
  The first old vertex remains first and retains its old parameter $t_0=0$.
-/
@[simp]
theorem segmentSplitParameterAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval) :
    S.segmentSplitParameterAt k τ 0 = 0 := by
  rw [← S.segmentSplitInsertVertex_succAbove_zero k,
    S.segmentSplitParameterAt_old k τ 0, S.parameterAt_zero]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Splitting a segment preserves the terminal parameter
statement:
  The parameter at the last vertex remains $1$ after an interior segment split.
proof:
  The old last vertex becomes the new last vertex and retains its parameter $t_n=1$.
-/
@[simp]
theorem segmentSplitParameterAt_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval) :
    S.segmentSplitParameterAt k τ (Fin.last (S.length + 1)) = 1 := by
  rw [← S.segmentSplitInsertVertex_succAbove_last k,
    S.segmentSplitParameterAt_old k τ (Fin.last S.length),
    S.parameterAt_last]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Splitting a segment preserves the initial chart center
statement:
  The chart center at vertex $0$ is unchanged by an interior segment split.
proof:
  The first old vertex remains first and keeps its center.
-/
@[simp]
theorem segmentSplitCenterAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    S.segmentSplitCenterAt k 0 = S.centerAt 0 := by
  rw [← S.segmentSplitInsertVertex_succAbove_zero k,
    S.segmentSplitCenterAt_old k 0]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Splitting a segment preserves the terminal chart center
statement:
  The chart center at the last vertex is unchanged by an interior segment split.
proof:
  The old last vertex becomes the new last vertex and retains its center.
-/
@[simp]
theorem segmentSplitCenterAt_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    S.segmentSplitCenterAt k (Fin.last (S.length + 1)) =
      S.terminalCenter := by
  rw [← S.segmentSplitInsertVertex_succAbove_last k,
    S.segmentSplitCenterAt_old k (Fin.last S.length)]
  rfl

omit [RiemannSurface X] in
/-- The inserted point of a segment split lies in the chart used on the left half.

%%handwave
name:
  The split point lies in the original segment chart
statement:
  If $t_k\le\tau\le t_{k+1}$, then $p(\tau)$ belongs to the domain of the chart centered at $c_k$.
proof:
  Apply the original skeleton's chart-domain containment along segment $k$ at the parameter $\tau$.
-/
theorem segmentSplit_insert_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    p τ ∈ (localModels.chartAt (S.centerAt k.castSucc)).domain :=
  S.path_segment_mem_model_domain k τ hτ_left hτ_right

omit [RiemannSurface X] in
/--
Every sampled vertex of a segment split lies in its selected model domain.

%%handwave
name:
  Every vertex of a split subdivision lies in its assigned chart
statement:
  After inserting $\tau\in[t_k,t_{k+1}]$, each old vertex still lies in its old chart domain, and the new vertex $p(\tau)$ lies in the chart assigned to the left half of segment $k$.
proof:
  At the inserted vertex use segment-domain containment for $p(\tau)$. Every other vertex is the image of a unique old vertex, where both parameter and center are unchanged, so use the original sampling condition.
-/
theorem segmentSplit_sample_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    ∀ i : Fin (S.length + 2),
      p (S.segmentSplitParameterAt k τ i) ∈
        (localModels.chartAt (S.segmentSplitCenterAt k i)).domain := by
  intro i
  by_cases hi : i = S.segmentSplitInsertVertex k
  · subst i
    simpa using S.segmentSplit_insert_mem_model_domain k τ hτ_left hτ_right
  · let old : Fin (S.length + 1) :=
      (k.succ : Fin (S.length + 1)).predAbove i
    have hsucc :
        (S.segmentSplitInsertVertex k).succAbove old = i := by
      simpa [old, segmentSplitInsertVertex] using
        (Fin.succAbove_predAbove (p := (k.succ : Fin (S.length + 1)))
          (i := i) (by simpa [segmentSplitInsertVertex] using hi))
    rw [← hsucc, S.segmentSplitParameterAt_old k τ old,
      S.segmentSplitCenterAt_old k old]
    exact S.sample_mem_model_domain old

omit [RiemannSurface X] in
/--
Every subinterval of a segment-split subdivision stays in the selected model
domain attached to its left vertex.

%%handwave
name:
  Every split subsegment remains in its assigned chart
statement:
  If segment $k$ is split at $\tau\in[t_k,t_{k+1}]$, then the two new intervals $[t_k,\tau]$ and $[\tau,t_{k+1}]$ both remain in the original chart for segment $k$, while every other segment retains its original chart-domain containment.
proof:
  For the two halves, their parameter intervals are contained in $[t_k,t_{k+1}]$. Before or after the split, identify the new interval with the corresponding old segment using the index-insertion formulas and apply its original containment property.
-/
theorem segmentSplit_path_segment_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    ∀ j : Fin (S.length + 1), ∀ t : unitInterval,
      (S.segmentSplitParameterAt k τ j.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (S.segmentSplitParameterAt k τ j.succ : ℝ) →
      p t ∈
        (localModels.chartAt (S.segmentSplitCenterAt k j.castSucc)).domain := by
  intro j t ht_left ht_right
  by_cases hj_left : j = k.castSucc
  · subst j
    have hleft_index := S.segmentSplitInsertVertex_succAbove_left k
    have hparam_left :
        S.segmentSplitParameterAt k τ (k.castSucc.castSucc) =
          S.parameterAt k.castSucc := by
      rw [← hleft_index, S.segmentSplitParameterAt_old k τ k.castSucc]
    have hcenter_left :
        S.segmentSplitCenterAt k (k.castSucc.castSucc) =
          S.centerAt k.castSucc := by
      rw [← hleft_index, S.segmentSplitCenterAt_old k k.castSucc]
    rw [hparam_left] at ht_left
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k] at ht_right
    change (t : ℝ) ≤
      (S.segmentSplitParameterAt k τ (S.segmentSplitInsertVertex k) : ℝ)
      at ht_right
    rw [S.segmentSplitParameterAt_insert k τ] at ht_right
    rw [hcenter_left]
    exact S.path_segment_mem_model_domain k t ht_left
      (le_trans ht_right hτ_right)
  by_cases hj_right : j = k.succ
  · subst j
    have hright_index := S.segmentSplitInsertVertex_succAbove_right k
    have hparam_right :
        S.segmentSplitParameterAt k τ (k.succ : Fin (S.length + 1)).succ =
          S.parameterAt k.succ := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ k.succ]
    change
      (S.segmentSplitParameterAt k τ (S.segmentSplitInsertVertex k) : ℝ) ≤
        (t : ℝ) at ht_left
    rw [S.segmentSplitParameterAt_insert k τ] at ht_left
    rw [hparam_right] at ht_right
    change p t ∈
      (localModels.chartAt
        (S.segmentSplitCenterAt k (S.segmentSplitInsertVertex k))).domain
    rw [S.segmentSplitCenterAt_insert k]
    exact S.path_segment_mem_model_domain k t
      (le_trans hτ_left ht_left) ht_right
  by_cases hj_before : (j : ℕ) < (k : ℕ)
  · let e : Fin S.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
    have hparam_left :
        S.segmentSplitParameterAt k τ j.castSucc = S.parameterAt e.castSucc := by
      rw [← hleft_index, S.segmentSplitParameterAt_old k τ e.castSucc]
    have hparam_right :
        S.segmentSplitParameterAt k τ j.succ = S.parameterAt e.succ := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ e.succ]
    have hcenter_left :
        S.segmentSplitCenterAt k j.castSucc = S.centerAt e.castSucc := by
      rw [← hleft_index, S.segmentSplitCenterAt_old k e.castSucc]
    rw [hparam_left] at ht_left
    rw [hparam_right] at ht_right
    rw [hcenter_left]
    exact S.path_segment_mem_model_domain e t ht_left ht_right
  · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hj_left (Fin.ext h)
    have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
      intro h
      exact hj_right (Fin.ext h)
    have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
      omega
    let e : Fin S.length := ⟨(j : ℕ) - 1, by omega⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc := by
      exact S.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ := by
      exact S.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
    have hparam_left :
        S.segmentSplitParameterAt k τ j.castSucc = S.parameterAt e.castSucc := by
      rw [← hleft_index, S.segmentSplitParameterAt_old k τ e.castSucc]
    have hparam_right :
        S.segmentSplitParameterAt k τ j.succ = S.parameterAt e.succ := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ e.succ]
    have hcenter_left :
        S.segmentSplitCenterAt k j.castSucc = S.centerAt e.castSucc := by
      rw [← hleft_index, S.segmentSplitCenterAt_old k e.castSucc]
    rw [hparam_left] at ht_left
    rw [hparam_right] at ht_right
    rw [hcenter_left]
    exact S.path_segment_mem_model_domain e t ht_left ht_right

omit [RiemannSurface X] in
/-- The subdivision parameters remain monotone after splitting one segment.

%%handwave
name:
  Inserting an interior parameter preserves monotonicity
statement:
  If $t_k\le\tau\le t_{k+1}$, then the sequence obtained from $t_0\le\cdots\le t_n$ by inserting $\tau$ between $t_k$ and $t_{k+1}$ remains weakly increasing.
proof:
  The two new inequalities are exactly $t_k\le\tau$ and $\tau\le t_{k+1}$. Every other adjacent pair is an unchanged adjacent pair from the old monotone sequence.
-/
theorem segmentSplitParameterAt_mono
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    ∀ j : Fin (S.length + 1),
      (S.segmentSplitParameterAt k τ j.castSucc : ℝ) ≤
        (S.segmentSplitParameterAt k τ j.succ : ℝ) := by
  intro j
  by_cases hj_left : j = k.castSucc
  · subst j
    have hleft_index := S.segmentSplitInsertVertex_succAbove_left k
    have hparam_left :
        S.segmentSplitParameterAt k τ (k.castSucc.castSucc) =
          S.parameterAt k.castSucc := by
      rw [← hleft_index, S.segmentSplitParameterAt_old k τ k.castSucc]
    rw [hparam_left]
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
    change (S.parameterAt k.castSucc : ℝ) ≤
      (S.segmentSplitParameterAt k τ (S.segmentSplitInsertVertex k) : ℝ)
    rw [S.segmentSplitParameterAt_insert k τ]
    exact hτ_left
  by_cases hj_right : j = k.succ
  · subst j
    have hright_index := S.segmentSplitInsertVertex_succAbove_right k
    have hparam_right :
        S.segmentSplitParameterAt k τ (k.succ : Fin (S.length + 1)).succ =
          S.parameterAt k.succ := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ k.succ]
    change
      (S.segmentSplitParameterAt k τ (S.segmentSplitInsertVertex k) : ℝ) ≤
        (S.segmentSplitParameterAt k τ
          ((k.succ : Fin (S.length + 1)).succ) : ℝ)
    rw [S.segmentSplitParameterAt_insert k τ, hparam_right]
    exact hτ_right
  by_cases hj_before : (j : ℕ) < (k : ℕ)
  · let e : Fin S.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
    have hparam_left :
        S.segmentSplitParameterAt k τ j.castSucc = S.parameterAt e.castSucc := by
      rw [← hleft_index, S.segmentSplitParameterAt_old k τ e.castSucc]
    have hparam_right :
        S.segmentSplitParameterAt k τ j.succ = S.parameterAt e.succ := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ e.succ]
    rw [hparam_left, hparam_right]
    exact S.parameterAt_mono e
  · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hj_left (Fin.ext h)
    have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
      intro h
      exact hj_right (Fin.ext h)
    have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
      omega
    let e : Fin S.length := ⟨(j : ℕ) - 1, by omega⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
    have hparam_left :
        S.segmentSplitParameterAt k τ j.castSucc = S.parameterAt e.castSucc := by
      rw [← hleft_index, S.segmentSplitParameterAt_old k τ e.castSucc]
    have hparam_right :
        S.segmentSplitParameterAt k τ j.succ = S.parameterAt e.succ := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ e.succ]
    rw [hparam_left, hparam_right]
    exact S.parameterAt_mono e

omit [RiemannSurface X] in
/-- The endpoint still lies in the terminal chart after a segment split.

%%handwave
name:
  Segment splitting preserves terminal-domain membership
statement:
  After splitting an interior segment, the endpoint $x$ still belongs to the domain of the chart assigned to the last vertex.
proof:
  The last chart center is unchanged, so this is the original terminal-domain condition.
-/
theorem segmentSplit_terminal_endpoint_mem_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    x ∈
      (localModels.chartAt
        (S.segmentSplitCenterAt k (Fin.last (S.length + 1)))).domain := by
  simpa [S.segmentSplitCenterAt_last k] using S.terminal_endpoint_mem_domain

omit [RiemannSurface X] in
/--
The new left handoff created by a segment split is the identity transition in
the chart already controlling the original segment.
-/
def segmentSplitLeftIdentityTransition
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData
      (localModels.chartAt (S.centerAt k.castSucc))
      (localModels.chartAt (S.centerAt k.castSucc))
      (p τ) :=
  localRealMobiusTransitionData_self
    (localModels.chartAt (S.centerAt k.castSucc))
    (S.segmentSplit_insert_mem_model_domain k τ hτ_left hτ_right)

omit [RiemannSurface X] in
/--
%%handwave
name:
  Representative of the left transition created by a segment split
statement:
  The handoff into the inserted vertex of a split segment is represented by the identity Möbius transformation.
proof:
  Both halves use the same chart, and the chosen self-transition is defined with representative $1$.
-/
@[simp]
theorem segmentSplitLeftIdentityTransition_representative
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    (S.segmentSplitLeftIdentityTransition k τ hτ_left hτ_right).representative =
      1 :=
  rfl

omit [RiemannSurface X] in
/--
The new right handoff created by a segment split is the original handoff for
the split segment.
-/
def segmentSplitRightOriginalTransition
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData
      (localModels.chartAt (S.centerAt k.castSucc))
      (localModels.chartAt (S.centerAt k.succ))
      (p (S.parameterAt k.succ)) :=
  S.transitionAt k

omit [RiemannSurface X] in
/--
%%handwave
name:
  Representative of the right transition created by a segment split
statement:
  The handoff out of the inserted vertex uses exactly the representative $T_k$ of the original handoff at the right endpoint of segment $k$.
proof:
  The right transition is defined to be the original transition data at $k$.
-/
@[simp]
theorem segmentSplitRightOriginalTransition_representative
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    (S.segmentSplitRightOriginalTransition k).representative =
      (S.transitionAt k).representative :=
  rfl

omit [RiemannSurface X] in
/--
The two transition factors created by a segment split multiply to the original
transition factor.

%%handwave
name:
  The two split handoffs reproduce the original transition factor
statement:
  If the original update is $M\mapsto MT_k^{-1}$, then the updates across the two halves of a split segment satisfy $(M1^{-1})T_k^{-1}=MT_k^{-1}$.
proof:
  Substitute the identity representative for the new left handoff and the original representative for the new right handoff, then simplify.
-/
theorem segmentSplit_transitionFactors_eq_original
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ)
    (M : RealMobiusRepresentative) :
    (M *
        (S.segmentSplitLeftIdentityTransition k τ hτ_left hτ_right).representative⁻¹) *
        (S.segmentSplitRightOriginalTransition k).representative⁻¹ =
      M * (S.transitionAt k).representative⁻¹ := by
  rw [S.segmentSplitLeftIdentityTransition_representative k τ hτ_left hτ_right,
    S.segmentSplitRightOriginalTransition_representative k]
  simp

omit [RiemannSurface X] in
/--
Transition data for every handoff of a segment-split skeleton.

The split segment contributes two transitions: an identity transition into the
inserted vertex and the original transition out of it. All other handoffs are
transported from the old skeleton.
-/
def segmentSplitTransitionAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    ∀ j : Fin (S.length + 1),
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.segmentSplitCenterAt k j.castSucc))
        (localModels.chartAt (S.segmentSplitCenterAt k j.succ))
        (p (S.segmentSplitParameterAt k τ j.succ)) := by
  intro j
  by_cases hj_left : j = k.castSucc
  · subst j
    have hleft_index := S.segmentSplitInsertVertex_succAbove_left k
    have hU :
        localModels.chartAt (S.segmentSplitCenterAt k k.castSucc.castSucc) =
          localModels.chartAt (S.centerAt k.castSucc) := by
      rw [← hleft_index, S.segmentSplitCenterAt_old k k.castSucc]
    have hV :
        localModels.chartAt
            (S.segmentSplitCenterAt k
              ((k.castSucc : Fin (S.length + 1)).succ)) =
          localModels.chartAt (S.centerAt k.castSucc) := by
      rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
      change
        localModels.chartAt
            (S.segmentSplitCenterAt k (S.segmentSplitInsertVertex k)) =
          localModels.chartAt (S.centerAt k.castSucc)
      rw [S.segmentSplitCenterAt_insert k]
    have hpoint :
        p (S.segmentSplitParameterAt k τ
            ((k.castSucc : Fin (S.length + 1)).succ)) =
          p τ := by
      rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
      change
        p (S.segmentSplitParameterAt k τ (S.segmentSplitInsertVertex k)) =
          p τ
      rw [S.segmentSplitParameterAt_insert k τ]
    exact
      localRealMobiusTransitionData_congr hU hV hpoint
        (S.segmentSplitLeftIdentityTransition k τ hτ_left hτ_right)
  by_cases hj_right : j = k.succ
  · subst j
    have hright_index := S.segmentSplitInsertVertex_succAbove_right k
    have hU :
        localModels.chartAt
            (S.segmentSplitCenterAt k
              ((k.succ : Fin (S.length + 1)).castSucc)) =
          localModels.chartAt (S.centerAt k.castSucc) := by
      change
        localModels.chartAt
            (S.segmentSplitCenterAt k (S.segmentSplitInsertVertex k)) =
          localModels.chartAt (S.centerAt k.castSucc)
      rw [S.segmentSplitCenterAt_insert k]
    have hV :
        localModels.chartAt
            (S.segmentSplitCenterAt k
              ((k.succ : Fin (S.length + 1)).succ)) =
          localModels.chartAt (S.centerAt k.succ) := by
      rw [← hright_index, S.segmentSplitCenterAt_old k k.succ]
    have hpoint :
        p (S.segmentSplitParameterAt k τ
            ((k.succ : Fin (S.length + 1)).succ)) =
          p (S.parameterAt k.succ) := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ k.succ]
    exact
      localRealMobiusTransitionData_congr hU hV hpoint
        (S.segmentSplitRightOriginalTransition k)
  by_cases hj_before : (j : ℕ) < (k : ℕ)
  · let e : Fin S.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
    have hU :
        localModels.chartAt (S.segmentSplitCenterAt k j.castSucc) =
          localModels.chartAt (S.centerAt e.castSucc) := by
      rw [← hleft_index, S.segmentSplitCenterAt_old k e.castSucc]
    have hV :
        localModels.chartAt (S.segmentSplitCenterAt k j.succ) =
          localModels.chartAt (S.centerAt e.succ) := by
      rw [← hright_index, S.segmentSplitCenterAt_old k e.succ]
    have hpoint :
        p (S.segmentSplitParameterAt k τ j.succ) =
          p (S.parameterAt e.succ) := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ e.succ]
    exact localRealMobiusTransitionData_congr hU hV hpoint (S.transitionAt e)
  · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hj_left (Fin.ext h)
    have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
      intro h
      exact hj_right (Fin.ext h)
    have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
      omega
    let e : Fin S.length := ⟨(j : ℕ) - 1, by omega⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
    have hU :
        localModels.chartAt (S.segmentSplitCenterAt k j.castSucc) =
          localModels.chartAt (S.centerAt e.castSucc) := by
      rw [← hleft_index, S.segmentSplitCenterAt_old k e.castSucc]
    have hV :
        localModels.chartAt (S.segmentSplitCenterAt k j.succ) =
          localModels.chartAt (S.centerAt e.succ) := by
      rw [← hright_index, S.segmentSplitCenterAt_old k e.succ]
    have hpoint :
        p (S.segmentSplitParameterAt k τ j.succ) =
          p (S.parameterAt e.succ) := by
      rw [← hright_index, S.segmentSplitParameterAt_old k τ e.succ]
    exact localRealMobiusTransitionData_congr hU hV hpoint (S.transitionAt e)

omit [RiemannSurface X] in
/--
Split a single segment of a based weak handoff skeleton.

The inserted vertex uses the chart controlling the left half of the old
segment.  The new handoffs are the identity at the inserted point followed by
the original transition at the old right endpoint.
-/
noncomputable def segmentSplitSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p where
  length := S.length + 1
  length_pos := Nat.succ_pos S.length
  parameterAt := S.segmentSplitParameterAt k τ
  parameterAt_zero := S.segmentSplitParameterAt_zero k τ
  parameterAt_last := S.segmentSplitParameterAt_last k τ
  parameterAt_mono := S.segmentSplitParameterAt_mono k τ hτ_left hτ_right
  centerAt := S.segmentSplitCenterAt k
  sample_mem_model_domain :=
    S.segmentSplit_sample_mem_model_domain k τ hτ_left hτ_right
  path_segment_mem_model_domain :=
    S.segmentSplit_path_segment_mem_model_domain k τ hτ_left hτ_right
  terminal_endpoint_mem_domain := S.segmentSplit_terminal_endpoint_mem_domain k
  transitionAt := S.segmentSplitTransitionAt k τ hτ_left hτ_right
  initialTransition := by
    exact localRealMobiusTransitionData_congr rfl
      (by simp [S.segmentSplitCenterAt_zero k]) rfl S.initialTransition

omit [RiemannSurface X] in
/--
%%handwave
name:
  Segment splitting preserves the terminal center
statement:
  Inserting an interior subdivision vertex leaves the terminal chart center unchanged.
proof:
  The old last vertex becomes the new last vertex and retains its center.
-/
@[simp]
theorem segmentSplitSkeleton_terminalCenter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    (S.segmentSplitSkeleton k τ hτ_left hτ_right).terminalCenter =
      S.terminalCenter := by
  simp [segmentSplitSkeleton, terminalCenter]

omit [RiemannSurface X] in
/--
%%handwave
name:
  The left split handoff is the identity
statement:
  In the split skeleton, the transition representative from the old left vertex to the inserted vertex is $1$.
proof:
  Both new vertices use the old left chart, so this transition is the chosen identity self-transition.
-/
@[simp]
theorem segmentSplitSkeleton_transitionAt_left_representative
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    ((S.segmentSplitSkeleton k τ hτ_left hτ_right).transitionAt k.castSucc).representative =
      1 := by
  simp [segmentSplitSkeleton, segmentSplitTransitionAt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  The right split handoff is the original handoff
statement:
  In the split skeleton, the transition representative from the inserted vertex to the old right vertex is the original representative $T_k$.
proof:
  This handoff is defined by transporting the original transition at segment $k$.
-/
@[simp]
theorem segmentSplitSkeleton_transitionAt_right_representative
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    ((S.segmentSplitSkeleton k τ hτ_left hτ_right).transitionAt
        (k.succ : Fin (S.length + 1))).representative =
      (S.transitionAt k).representative := by
  have hne : (k.succ : Fin (S.length + 1)) ≠ k.castSucc := by
    intro h
    have : (k : ℕ) + 1 = (k : ℕ) := by
      exact Fin.ext_iff.mp h
    omega
  simp [segmentSplitSkeleton, segmentSplitTransitionAt, hne]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Handoffs before a split retain their representatives
statement:
  Every handoff with index $j<k$ has the same representative after segment $k$ is split as it had in the original skeleton.
proof:
  Such a handoff lies before the inserted vertex, so the transition data are transported from the same old index without changing their representative.
-/
@[simp]
theorem segmentSplitSkeleton_transitionAt_before_representative
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ)
    (j : Fin (S.length + 1)) (hj : (j : ℕ) < (k : ℕ)) :
    ((S.segmentSplitSkeleton k τ hτ_left hτ_right).transitionAt j).representative =
      (S.transitionAt ⟨j, Nat.lt_trans hj k.isLt⟩).representative := by
  have hne_left : j ≠ k.castSucc := by
    intro h
    have : (j : ℕ) = (k : ℕ) := Fin.ext_iff.mp h
    omega
  have hne_right : j ≠ (k.succ : Fin (S.length + 1)) := by
    intro h
    have : (j : ℕ) = (k : ℕ) + 1 := Fin.ext_iff.mp h
    omega
  simp [segmentSplitSkeleton, segmentSplitTransitionAt, hne_left, hne_right, hj]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Handoffs after a split retain their shifted representatives
statement:
  Every new handoff with index $j>k+1$ has the same representative as the old handoff with index $j-1$.
proof:
  Past the inserted vertex, deleting its position shifts indices down by one, and the corresponding old transition data are transported unchanged.
-/
@[simp]
theorem segmentSplitSkeleton_transitionAt_after_representative
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ)
    (j : Fin (S.length + 1)) (hj : (k : ℕ) + 1 < (j : ℕ)) :
    ((S.segmentSplitSkeleton k τ hτ_left hτ_right).transitionAt j).representative =
      (S.transitionAt ⟨(j : ℕ) - 1, by omega⟩).representative := by
  have hne_left : j ≠ k.castSucc := by
    intro h
    have : (j : ℕ) = (k : ℕ) := Fin.ext_iff.mp h
    omega
  have hne_right : j ≠ (k.succ : Fin (S.length + 1)) := by
    intro h
    have : (j : ℕ) = (k : ℕ) + 1 := Fin.ext_iff.mp h
    omega
  have hnot_before : ¬(j : ℕ) < (k : ℕ) := by omega
  simp [segmentSplitSkeleton, segmentSplitTransitionAt, hne_left, hne_right,
    hnot_before]

omit [RiemannSurface X] in
/--
Before the split vertex, the accumulated Mobius products of the split skeleton
agree with the old ones.

%%handwave
name:
  Accumulated products agree before an inserted split vertex
statement:
  If segment $k$ is split, then $M_j(S')=M_j(S)$ for every $j\le k$.
proof:
  Induct on $j$. All initial and handoff representatives strictly before the split are unchanged, so the product recurrence gives equality.
-/
theorem segmentSplitSkeleton_accumulatedMobiusNat_eq_of_le_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    ∀ n : ℕ, n ≤ (k : ℕ) →
      (S.segmentSplitSkeleton k τ hτ_left hτ_right).accumulatedMobiusNat n =
        S.accumulatedMobiusNat n := by
  intro n hn
  induction n with
  | zero =>
      simp [segmentSplitSkeleton, accumulatedMobiusNat]
  | succ n ih =>
      have hn_before : n < (k : ℕ) := Nat.succ_le_iff.mp hn
      have hn_old : n < S.length := Nat.lt_trans hn_before k.isLt
      have hn_split : n < (S.segmentSplitSkeleton k τ hτ_left hτ_right).length := by
        simp [segmentSplitSkeleton]
        omega
      let T := S.segmentSplitSkeleton k τ hτ_left hτ_right
      let j : Fin (S.length + 1) := ⟨n, by omega⟩
      have hTstep :
          T.accumulatedMobiusNat (n + 1) =
            T.accumulatedMobiusNat n *
              (T.transitionAt j).representative⁻¹ := by
        simpa [T, j] using T.accumulatedMobiusNat_succ_of_lt hn_split
      have hSstep :
          S.accumulatedMobiusNat (n + 1) =
            S.accumulatedMobiusNat n *
              (S.transitionAt ⟨n, hn_old⟩).representative⁻¹ :=
        S.accumulatedMobiusNat_succ_of_lt hn_old
      have htrans :
          (T.transitionAt j).representative =
            (S.transitionAt ⟨n, hn_old⟩).representative := by
        simpa [T, j] using
          S.segmentSplitSkeleton_transitionAt_before_representative
            k τ hτ_left hτ_right j hn_before
      rw [hTstep, ih (Nat.le_of_lt hn_before), htrans, hSstep]

omit [RiemannSurface X] in
/--
After the inserted vertex, the split skeleton's accumulated Mobius product is
the old accumulated product with the vertex index shifted down by one.

%%handwave
name:
  Accumulated products agree after a split with shifted indices
statement:
  If $S'$ is obtained by splitting segment $k$, then for $k+1\le j\le\ell+1$ one has $M_j(S')=M_{j-1}(S)$.
proof:
  At $j=k+1$, the new identity handoff leaves $M_k$ unchanged. Induct thereafter: the next handoff representative in $S'$ is the corresponding old representative, including the original $k$th handoff at the right half, so both recurrences agree after shifting the index.
-/
theorem segmentSplitSkeleton_accumulatedMobiusNat_eq_tail
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    ∀ n : ℕ, (k : ℕ) + 1 ≤ n → n ≤ S.length + 1 →
      (S.segmentSplitSkeleton k τ hτ_left hτ_right).accumulatedMobiusNat n =
        S.accumulatedMobiusNat (n - 1) := by
  intro n hn_left hn_right
  induction n with
  | zero =>
      omega
  | succ n ih =>
      let T := S.segmentSplitSkeleton k τ hτ_left hτ_right
      by_cases hn_base : n = (k : ℕ)
      · subst n
        have hprefix :
            T.accumulatedMobiusNat (k : ℕ) =
              S.accumulatedMobiusNat (k : ℕ) := by
          exact
            S.segmentSplitSkeleton_accumulatedMobiusNat_eq_of_le_left
              k τ hτ_left hτ_right (k : ℕ) le_rfl
        have hn_split : (k : ℕ) < T.length := by
          simp [T, segmentSplitSkeleton]
        have hTstep :
            T.accumulatedMobiusNat ((k : ℕ) + 1) =
              T.accumulatedMobiusNat (k : ℕ) *
                (T.transitionAt k.castSucc).representative⁻¹ := by
          have h := T.accumulatedMobiusNat_succ_of_lt hn_split
          change T.accumulatedMobiusNat ((k : ℕ) + 1) =
            T.accumulatedMobiusNat (k : ℕ) *
              (T.transitionAt k.castSucc).representative⁻¹ at h
          exact h
        have htrans :
            (T.transitionAt k.castSucc).representative = 1 := by
          simp [T]
        change T.accumulatedMobiusNat ((k : ℕ) + 1) =
          S.accumulatedMobiusNat (((k : ℕ) + 1) - 1)
        rw [hTstep, htrans, hprefix]
        simp
      · have hn_tail_left : (k : ℕ) + 1 ≤ n := by omega
        have hn_tail_right : n ≤ S.length + 1 := by omega
        have hn_split : n < T.length := by
          simp [T, segmentSplitSkeleton]
          omega
        have hn_old_step : n - 1 < S.length := by omega
        let j : Fin (S.length + 1) := ⟨n, by omega⟩
        have hTstep :
            T.accumulatedMobiusNat (n + 1) =
              T.accumulatedMobiusNat n *
                (T.transitionAt j).representative⁻¹ := by
          have h := T.accumulatedMobiusNat_succ_of_lt hn_split
          change T.accumulatedMobiusNat (n + 1) =
            T.accumulatedMobiusNat n *
              (T.transitionAt j).representative⁻¹ at h
          exact h
        have hSstep :
            S.accumulatedMobiusNat n =
              S.accumulatedMobiusNat (n - 1) *
                (S.transitionAt ⟨n - 1, hn_old_step⟩).representative⁻¹ := by
          have hn_pos : 0 < n := by omega
          simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)] using
            (S.accumulatedMobiusNat_succ_of_lt (n := n - 1) hn_old_step)
        have htrans :
            (T.transitionAt j).representative =
              (S.transitionAt ⟨n - 1, hn_old_step⟩).representative := by
          by_cases hn_right_edge : n = (k : ℕ) + 1
          · subst n
            have hj_eq : j = (k.succ : Fin (S.length + 1)) := by
              ext
              simp [j]
            rw [hj_eq]
            simpa only [T] using
              S.segmentSplitSkeleton_transitionAt_right_representative
                k τ hτ_left hτ_right
          · have hn_after : (k : ℕ) + 1 < n := by omega
            simpa [T, j] using
              S.segmentSplitSkeleton_transitionAt_after_representative
                k τ hτ_left hτ_right j hn_after
        have ih' :
            T.accumulatedMobiusNat n =
              S.accumulatedMobiusNat (n - 1) :=
          ih hn_tail_left hn_tail_right
        have htarget_index : (n + 1) - 1 = n := by omega
        rw [hTstep, ih', htrans, ← hSstep]
        rw [htarget_index]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Segment splitting preserves the terminal Möbius representative
statement:
  Inserting an interior subdivision vertex leaves the terminal accumulated representative unchanged.
proof:
  At the new terminal index $\ell+1$, the shifted-tail formula gives $M_{\ell+1}(S')=M_\ell(S)$.
-/
@[simp]
theorem segmentSplitSkeleton_terminalMobius_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    (S.segmentSplitSkeleton k τ hτ_left hτ_right).terminalMobius =
      S.terminalMobius := by
  let T := S.segmentSplitSkeleton k τ hτ_left hτ_right
  have htail :
      T.accumulatedMobiusNat (S.length + 1) =
        S.accumulatedMobiusNat ((S.length + 1) - 1) := by
    simpa [T] using
      S.segmentSplitSkeleton_accumulatedMobiusNat_eq_tail
        k τ hτ_left hτ_right (S.length + 1) (by omega) le_rfl
  change T.accumulatedMobiusNat (S.length + 1) =
    S.accumulatedMobiusNat S.length
  simpa using htail

omit [RiemannSurface X] in
/--
%%handwave
name:
  Segment splitting preserves the terminal value
statement:
  Inserting a subdivision point inside a segment does not change the terminal value.
proof:
  Both terminal center and terminal accumulated representative are preserved, so the endpoint evaluation is unchanged.
-/
@[simp]
theorem segmentSplitSkeleton_terminalValue_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    (S.segmentSplitSkeleton k τ hτ_left hτ_right).terminalValue =
      S.terminalValue := by
  simp [terminalValue]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Segment splitting preserves the terminal formula
statement:
  Inserting a subdivision point inside a segment leaves the terminal branch formula unchanged at every $z\in X$.
proof:
  The split preserves the terminal chart center and terminal accumulated representative; substitute these equalities in the formula.
-/
@[simp]
theorem segmentSplitSkeleton_terminalFormulaAt_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ)
    (z : X) :
    (S.segmentSplitSkeleton k τ hτ_left hτ_right).terminalFormulaAt z =
      S.terminalFormulaAt z := by
  simp [terminalFormulaAt]

omit [RiemannSurface X] in
/--
Split a skeleton at an arbitrary unit-interval parameter, using the locator
lemma to choose a containing segment.
-/
noncomputable def splitAtParameterSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p :=
  let k := Classical.choose (S.exists_segment_contains_parameter τ)
  let hk := Classical.choose_spec (S.exists_segment_contains_parameter τ)
  S.segmentSplitSkeleton k τ hk.1 hk.2

omit [RiemannSurface X] in
/--
%%handwave
name:
  Splitting at an arbitrary parameter preserves the terminal value
statement:
  For every $\tau\in[0,1]$, inserting $\tau$ into a subdivision at a containing segment leaves the terminal value unchanged.
proof:
  Choose a segment $k$ with $t_k\le\tau\le t_{k+1}$ and apply terminal-value invariance of splitting that segment.
-/
@[simp]
theorem splitAtParameterSkeleton_terminalValue_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) :
    (S.splitAtParameterSkeleton τ).terminalValue = S.terminalValue := by
  classical
  simp [splitAtParameterSkeleton]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Splitting at an arbitrary parameter preserves the terminal formula
statement:
  For every $\tau\in[0,1]$, inserting $\tau$ into the subdivision leaves the terminal branch formula unchanged at every point $z\in X$.
proof:
  Locate a segment containing $\tau$ and apply terminal-formula invariance for an interior segment split.
-/
@[simp]
theorem splitAtParameterSkeleton_terminalFormulaAt_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) (z : X) :
    (S.splitAtParameterSkeleton τ).terminalFormulaAt z =
      S.terminalFormulaAt z := by
  classical
  simp [splitAtParameterSkeleton]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Splitting at one parameter adds one segment
statement:
  Inserting any parameter into a skeleton of length $\ell$ produces a skeleton of length $\ell+1$.
proof:
  The containing-segment split construction adds exactly one vertex and hence one segment.
-/
@[simp]
theorem splitAtParameterSkeleton_length
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) :
    (S.splitAtParameterSkeleton τ).length = S.length + 1 := by
  classical
  unfold splitAtParameterSkeleton
  simp [segmentSplitSkeleton]

omit [RiemannSurface X] in
/--
Split `S` at the first `m` sampled parameters of `T`, without changing the
chart attached to any old vertex.  This is the "plain duplicate" padding used
after mutual endpoint-chart insertion: endpoint-chart insertion adds two
copies of the other subdivision vertices, while this operation adds the
missing single copy of the original subdivision vertices.
-/
noncomputable def splitFirstVerticesOfSkeleton
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ℕ → PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  | 0 => S
  | m + 1 =>
      let R := splitFirstVerticesOfSkeleton S T m
      if h : m < T.length + 1 then
        R.splitAtParameterSkeleton (T.parameterAt ⟨m, h⟩)
      else
        R

omit [RiemannSurface X] in
/--
Splitting at the first `m` sampled vertices of `T` adds exactly one
subdivision interval per sampled vertex, as long as `m` is within the sampled
vertex range of `T`.

%%handwave
name:
  Length after inserting the first sampled parameters of another skeleton
statement:
  If the first $m$ vertex parameters of $T$ are successively inserted into $S$, with $m\le\ell_T+1$, then the resulting skeleton has length $\ell_S+m$.
proof:
  Induct on $m$. Each located parameter split adds one segment, so the successor step adds one to the previous length.
-/
theorem splitFirstVerticesOfSkeleton_length_of_le
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m : ℕ, m ≤ T.length + 1 →
      (S.splitFirstVerticesOfSkeleton T m).length = S.length + m := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [splitFirstVerticesOfSkeleton]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ T.length + 1 := by omega
      have hm_lt : m < T.length + 1 := by omega
      simp [splitFirstVerticesOfSkeleton, hm_lt, ih hm_prev,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

omit [RiemannSurface X] in
/-- Split `S` at every sampled parameter of `T`, adding one duplicate each. -/
noncomputable def splitAllVerticesOfSkeleton
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p :=
  S.splitFirstVerticesOfSkeleton T (T.length + 1)

omit [RiemannSurface X] in
/--
%%handwave
name:
  Length after inserting every sampled parameter of another skeleton
statement:
  Splitting $S$ at all $\ell_T+1$ vertex parameters of $T$ produces a skeleton of length $\ell_S+\ell_T+1$.
proof:
  Apply the preceding length formula with $m=\ell_T+1$.
-/
@[simp]
theorem splitAllVerticesOfSkeleton_length
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    (S.splitAllVerticesOfSkeleton T).length =
      S.length + (T.length + 1) := by
  simpa [splitAllVerticesOfSkeleton] using
    S.splitFirstVerticesOfSkeleton_length_of_le T (T.length + 1) le_rfl

omit [RiemannSurface X] in
/-- The subdivision parameters of a based weak handoff skeleton as a list. -/
def parameterList
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    List unitInterval :=
  List.ofFn S.parameterAt

omit [RiemannSurface X] in
/-- The parameter list of a weak handoff skeleton is weakly sorted.

%%handwave
name:
  Subdivision parameter lists are weakly sorted
statement:
  The list $(t_0,\ldots,t_\ell)$ of subdivision parameters of a continuation skeleton is weakly increasing.
proof:
  Consecutive entries satisfy $t_i\le t_{i+1}$ by the subdivision monotonicity condition, which is exactly the chain criterion for a sorted finite list.
-/
theorem parameterList_sortedLE
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.parameterList.SortedLE := by
  classical
  rw [parameterList, List.sortedLE_iff_isChain, List.isChain_ofFn]
  intro i hi
  exact S.parameterAt_mono ⟨i, by omega⟩

omit [RiemannSurface X] in
/--
Sortedness turns a permutation comparison of parameter lists into the
pointwise aligned-subdivision equality used by the continuation proof.

%%handwave
name:
  Permuted sorted parameter lists agree pointwise
statement:
  If the weakly increasing parameter lists of two skeletons are permutations of one another, then their entries at every common valid index $j$ are equal: $t_j(S)=t_j(T)$.
proof:
  Two sorted lists related by a permutation are equal as lists. Taking the $j$th optional entry and using the bounds on $j$ yields equality of the corresponding parameters.
-/
theorem parameterAt_eq_of_parameterList_perm
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (hPerm : List.Perm S.parameterList T.parameterList) :
    ∀ n (hnS : n ≤ S.length) (hnT : n ≤ T.length),
      S.parameterAt ⟨n, Nat.lt_succ_of_le hnS⟩ =
        T.parameterAt ⟨n, Nat.lt_succ_of_le hnT⟩ := by
  classical
  have hList : S.parameterList = T.parameterList :=
    List.Perm.eq_of_sortedLE S.parameterList_sortedLE T.parameterList_sortedLE hPerm
  intro n hnS hnT
  have hget := congrArg (fun l : List unitInterval => l[n]?) hList
  change S.parameterList[n]? = T.parameterList[n]? at hget
  have hSget :
      S.parameterList[n]? =
        some (S.parameterAt ⟨n, Nat.lt_succ_of_le hnS⟩) := by
    rw [parameterList, List.getElem?_ofFn]
    simp [Nat.lt_succ_of_le hnS]
  have hTget :
      T.parameterList[n]? =
        some (T.parameterAt ⟨n, Nat.lt_succ_of_le hnT⟩) := by
    rw [parameterList, List.getElem?_ofFn]
    simp [Nat.lt_succ_of_le hnT]
  rw [hSget, hTget] at hget
  exact Option.some.inj hget

omit [RiemannSurface X] in
/--
Splitting one segment inserts exactly the new split parameter into the
subdivision parameter list, up to permutation.

%%handwave
name:
  Parameter multiset of a single segment split
statement:
  Splitting a segment of $S$ at $\tau$ produces a parameter list that is a permutation of $\tau$ followed by the old parameter list.
proof:
  The new parameter tuple is obtained by inserting $\tau$ at one finite index. The list of a tuple after one insertion is a permutation of the inserted entry followed by the old list.
-/
theorem segmentSplitSkeleton_parameterList_perm
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    List.Perm
      (S.segmentSplitSkeleton k τ hτ_left hτ_right).parameterList
      (τ :: S.parameterList) := by
  classical
  change List.Perm (List.ofFn (S.segmentSplitParameterAt k τ))
    (τ :: List.ofFn S.parameterAt)
  rw [S.segmentSplitParameterAt_eq_insertNth k τ]
  exact ofFn_fin_insertNth_perm (S.segmentSplitInsertVertex k) τ S.parameterAt

omit [RiemannSurface X] in
/--
Splitting at an arbitrary located parameter inserts that parameter into the
subdivision parameter list, up to permutation.

%%handwave
name:
  Parameter multiset after splitting at an arbitrary parameter
statement:
  For every $\tau\in[0,1]$, the parameter list after splitting at $\tau$ is a permutation of $\tau$ followed by the original list.
proof:
  Choose a containing segment and apply the parameter-list formula for splitting that segment.
-/
theorem splitAtParameterSkeleton_parameterList_perm
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) :
    List.Perm (S.splitAtParameterSkeleton τ).parameterList
      (τ :: S.parameterList) := by
  classical
  unfold splitAtParameterSkeleton
  exact
    S.segmentSplitSkeleton_parameterList_perm
      (Classical.choose (S.exists_segment_contains_parameter τ)) τ
      (Classical.choose_spec (S.exists_segment_contains_parameter τ)).1
      (Classical.choose_spec (S.exists_segment_contains_parameter τ)).2

omit [RiemannSurface X] in
/--
The first `m` sampled parameters of a skeleton, listed in reverse recursive
order.  This is the natural bookkeeping order for repeated splits, since each
new split contributes its parameter at the head of the list up to permutation.
-/
def firstParameterListOfSkeleton
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ℕ → List unitInterval
  | 0 => []
  | m + 1 =>
      if h : m < T.length + 1 then
        T.parameterAt ⟨m, h⟩ :: T.firstParameterListOfSkeleton m
      else
        T.firstParameterListOfSkeleton m

omit [RiemannSurface X] in
/--
%%handwave
name:
  Successor formula for the recursive parameter prefix
statement:
  If $m$ is a valid vertex index, the recursively accumulated list of the first $m+1$ parameters is $t_m$ followed by the list of the first $m$ parameters.
proof:
  The validity inequality selects the cons branch of the recursive definition.
-/
@[simp]
theorem firstParameterListOfSkeleton_succ_of_lt
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {m : ℕ} (hm : m < T.length + 1) :
    T.firstParameterListOfSkeleton (m + 1) =
      T.parameterAt ⟨m, hm⟩ :: T.firstParameterListOfSkeleton m := by
  simp [firstParameterListOfSkeleton, hm]

omit [RiemannSurface X] in
/--
The recursive first-parameter list is a permutation of the actual ordered
prefix of the subdivision parameter tuple.

%%handwave
name:
  Recursive parameter prefix is a permutation of the ordered prefix
statement:
  For $m\le\ell+1$, the recursively accumulated first-$m$ parameter list is a permutation of $(t_0,\ldots,t_{m-1})$.
proof:
  Induct on $m$. The recursion adds $t_m$ at the front, while the ordered prefix appends it at the end; move this element across the list and use the induction hypothesis.
-/
theorem firstParameterListOfSkeleton_perm_prefix
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m : ℕ, ∀ hm : m ≤ T.length + 1,
      List.Perm (T.firstParameterListOfSkeleton m)
        (List.ofFn fun i : Fin m =>
          T.parameterAt ⟨i, by omega⟩) := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [firstParameterListOfSkeleton]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ T.length + 1 := by omega
      have hm_lt : m < T.length + 1 := by omega
      have hhead :
          T.firstParameterListOfSkeleton (m + 1) =
            T.parameterAt ⟨m, hm_lt⟩ ::
              T.firstParameterListOfSkeleton m := by
        simp [firstParameterListOfSkeleton, hm_lt]
      have htail :
          (List.ofFn fun i : Fin m =>
              T.parameterAt ⟨i, by omega⟩) ++
            [T.parameterAt ⟨m, hm_lt⟩] =
            (List.ofFn fun i : Fin (m + 1) =>
              T.parameterAt ⟨i, by omega⟩) := by
        rw [List.ofFn_succ']
        simp [List.concat_eq_append]
      rw [hhead]
      exact
        (List.Perm.cons _ (ih hm_prev)).trans
          ((List.perm_append_singleton
            (T.parameterAt ⟨m, hm_lt⟩)
            (List.ofFn fun i : Fin m =>
              T.parameterAt ⟨i, by omega⟩)).symm.trans
            (by rw [htail]))

omit [RiemannSurface X] in
/-- All recursively listed sampled parameters are a permutation of `parameterList`.

%%handwave
name:
  The complete recursive parameter list has the original parameter multiset
statement:
  Accumulating all $\ell+1$ sampled parameters recursively gives a list that is a permutation of $(t_0,\ldots,t_\ell)$.
proof:
  Specialize the prefix-permutation formula to the full number of vertices.
-/
theorem firstParameterListOfSkeleton_all_perm_parameterList
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    List.Perm (T.firstParameterListOfSkeleton (T.length + 1))
      T.parameterList := by
  simpa [parameterList] using
    T.firstParameterListOfSkeleton_perm_prefix (T.length + 1) le_rfl

omit [RiemannSurface X] in
/--
Repeated plain splitting inserts precisely the recursively listed sampled
parameters into the old parameter list, up to permutation.

%%handwave
name:
  Parameter multiset after inserting a sampled prefix
statement:
  After successively splitting $S$ at the first $m$ sampled parameters of $T$, the resulting parameter list is a permutation of the recursive first-$m$ parameter list of $T$ followed by the original list of $S$.
proof:
  Induct on $m$. The next split inserts $t_m(T)$ at the head up to permutation; compose this permutation with the induction hypothesis and the recursive prefix formula.
-/
theorem splitFirstVerticesOfSkeleton_parameterList_perm_of_le
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m : ℕ, m ≤ T.length + 1 →
      List.Perm (S.splitFirstVerticesOfSkeleton T m).parameterList
        (T.firstParameterListOfSkeleton m ++ S.parameterList) := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [splitFirstVerticesOfSkeleton, firstParameterListOfSkeleton]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ T.length + 1 := by omega
      have hm_lt : m < T.length + 1 := by omega
      let R := S.splitFirstVerticesOfSkeleton T m
      have hsplit :
          List.Perm
            (R.splitAtParameterSkeleton (T.parameterAt ⟨m, hm_lt⟩)).parameterList
            (T.parameterAt ⟨m, hm_lt⟩ :: R.parameterList) :=
        R.splitAtParameterSkeleton_parameterList_perm
          (T.parameterAt ⟨m, hm_lt⟩)
      have hih :
          List.Perm R.parameterList
            (T.firstParameterListOfSkeleton m ++ S.parameterList) :=
        ih hm_prev
      simpa [splitFirstVerticesOfSkeleton, firstParameterListOfSkeleton, hm_lt,
        R, List.cons_append] using
        hsplit.trans (List.Perm.cons _ hih)

omit [RiemannSurface X] in
/--
Splitting at every sampled parameter of `T` inserts exactly `T`'s parameter
list into `S`'s parameter list, up to permutation.

%%handwave
name:
  Parameter multiset after inserting every vertex of another skeleton
statement:
  After splitting $S$ at every vertex parameter of $T$, the resulting parameter list is a permutation of the parameter list of $T$ followed by that of $S$.
proof:
  Apply the sampled-prefix formula to all $\ell_T+1$ vertices, then replace the complete recursive prefix by its permutation-equivalent original parameter list.
-/
theorem splitAllVerticesOfSkeleton_parameterList_perm
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    List.Perm (S.splitAllVerticesOfSkeleton T).parameterList
      (T.parameterList ++ S.parameterList) := by
  have hsplit :
      List.Perm (S.splitAllVerticesOfSkeleton T).parameterList
        (T.firstParameterListOfSkeleton (T.length + 1) ++ S.parameterList) := by
    simpa [splitAllVerticesOfSkeleton] using
      S.splitFirstVerticesOfSkeleton_parameterList_perm_of_le T
        (T.length + 1) le_rfl
  exact hsplit.trans
    (List.Perm.append_right S.parameterList
      T.firstParameterListOfSkeleton_all_perm_parameterList)

omit [RiemannSurface X] in
/--
Centers after inserting a zero-length chart handoff at the right endpoint of
segment `k`.  The inserted vertex uses the chosen center `c`; all old vertices
are embedded exactly as in `segmentSplitCenterAt`.
-/
noncomputable def segmentEndpointChartInsertCenterAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X) :
    Fin (S.length + 2) → X :=
  fun i =>
    if i = S.segmentSplitInsertVertex k then
      c
    else
      S.centerAt ((k.succ : Fin (S.length + 1)).predAbove i)

omit [RiemannSurface X] in
/--
%%handwave
name:
  An endpoint chart insertion assigns the chosen center to its new vertex
statement:
  Inserting a zero-length chart handoff at the right endpoint of segment $k$ assigns the new duplicate vertex the chosen chart center $c$.
proof:
  The inserted-index branch of the center function is defined to return $c$.
-/
@[simp]
theorem segmentEndpointChartInsertCenterAt_insert
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X) :
    S.segmentEndpointChartInsertCenterAt k c
        (S.segmentSplitInsertVertex k) = c := by
  simp [segmentEndpointChartInsertCenterAt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Endpoint chart insertion preserves all old centers
statement:
  Under the order-preserving inclusion of old vertices, inserting a zero-length chart handoff leaves every original center $c_i$ unchanged.
proof:
  At any included old vertex, deleting the inserted position recovers its old index.
-/
@[simp]
theorem segmentEndpointChartInsertCenterAt_old
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X) (i : Fin (S.length + 1)) :
    S.segmentEndpointChartInsertCenterAt k c
        ((S.segmentSplitInsertVertex k).succAbove i) =
      S.centerAt i := by
  unfold segmentEndpointChartInsertCenterAt segmentSplitInsertVertex
  rw [if_neg]
  · rw [Fin.predAbove_succAbove]
  · exact Fin.succAbove_ne _ _

omit [RiemannSurface X] in
/--
%%handwave
name:
  Endpoint chart insertion preserves the initial center
statement:
  Inserting a chart at an interior segment endpoint does not change the chart center at vertex $0$.
proof:
  The first old vertex remains first and retains its center.
-/
@[simp]
theorem segmentEndpointChartInsertCenterAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X) :
    S.segmentEndpointChartInsertCenterAt k c 0 = S.centerAt 0 := by
  rw [← S.segmentSplitInsertVertex_succAbove_zero k,
    S.segmentEndpointChartInsertCenterAt_old k c 0]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Endpoint chart insertion preserves the terminal center
statement:
  Inserting a chart at an interior segment endpoint does not change the final chart center.
proof:
  The old last vertex becomes the new last vertex and retains the old terminal center.
-/
@[simp]
theorem segmentEndpointChartInsertCenterAt_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X) :
    S.segmentEndpointChartInsertCenterAt k c (Fin.last (S.length + 1)) =
      S.terminalCenter := by
  rw [← S.segmentSplitInsertVertex_succAbove_last k,
    S.segmentEndpointChartInsertCenterAt_old k c (Fin.last S.length)]
  rfl

omit [RiemannSurface X] in
/--
Every sampled vertex of an endpoint chart-insertion subdivision lies in its
selected model domain.

%%handwave
name:
  Every vertex after endpoint chart insertion lies in its assigned chart
statement:
  Suppose $p(t_{k+1})$ lies in the chosen chart centered at $c$. After duplicating $t_{k+1}$ and assigning $c$ to the new vertex, every sampled path point lies in the domain of its assigned chart.
proof:
  The new vertex uses the assumed membership of $p(t_{k+1})$ in the chart at $c$. Every other vertex keeps its old parameter and center, so the original sampling condition applies.
-/
theorem segmentEndpointChartInsert_sample_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc :
      p (S.parameterAt k.succ) ∈ (localModels.chartAt c).domain) :
    ∀ i : Fin (S.length + 2),
      p (S.segmentSplitParameterAt k (S.parameterAt k.succ) i) ∈
        (localModels.chartAt
          (S.segmentEndpointChartInsertCenterAt k c i)).domain := by
  intro i
  by_cases hi : i = S.segmentSplitInsertVertex k
  · subst i
    simpa using hc
  · let old : Fin (S.length + 1) :=
      (k.succ : Fin (S.length + 1)).predAbove i
    have hsucc :
        (S.segmentSplitInsertVertex k).succAbove old = i := by
      simpa [old, segmentSplitInsertVertex] using
        (Fin.succAbove_predAbove (p := (k.succ : Fin (S.length + 1)))
          (i := i) (by simpa [segmentSplitInsertVertex] using hi))
    rw [← hsucc, S.segmentSplitParameterAt_old k (S.parameterAt k.succ) old,
      S.segmentEndpointChartInsertCenterAt_old k c old]
    exact S.sample_mem_model_domain old

omit [RiemannSurface X] in
/--
Every subinterval of an endpoint chart-insertion subdivision stays in the
selected model domain attached to its left vertex.

%%handwave
name:
  Every segment after endpoint chart insertion remains in its assigned chart
statement:
  Duplicating $t_{k+1}$ with a new chart $c$ preserves all old segment-domain containments; the added zero-length interval at $t_{k+1}$ lies in the chart at $c$.
proof:
  The left half is the original segment $k$, the new interval has both endpoints $t_{k+1}$ and hence contains only that point, and all other intervals identify with old intervals after shifting indices.
-/
theorem segmentEndpointChartInsert_path_segment_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc :
      p (S.parameterAt k.succ) ∈ (localModels.chartAt c).domain) :
    ∀ j : Fin (S.length + 1), ∀ t : unitInterval,
      (S.segmentSplitParameterAt k (S.parameterAt k.succ) j.castSucc : ℝ) ≤
          (t : ℝ) →
      (t : ℝ) ≤
          (S.segmentSplitParameterAt k (S.parameterAt k.succ) j.succ : ℝ) →
      p t ∈
        (localModels.chartAt
          (S.segmentEndpointChartInsertCenterAt k c j.castSucc)).domain := by
  intro j t ht_left ht_right
  by_cases hj_left : j = k.castSucc
  · subst j
    have hleft_index := S.segmentSplitInsertVertex_succAbove_left k
    have hparam_left :
        S.segmentSplitParameterAt k (S.parameterAt k.succ)
            k.castSucc.castSucc =
          S.parameterAt k.castSucc := by
      rw [← hleft_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) k.castSucc]
    have hcenter_left :
        S.segmentEndpointChartInsertCenterAt k c k.castSucc.castSucc =
          S.centerAt k.castSucc := by
      rw [← hleft_index, S.segmentEndpointChartInsertCenterAt_old k c k.castSucc]
    rw [hparam_left] at ht_left
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k] at ht_right
    change (t : ℝ) ≤
      (S.segmentSplitParameterAt k (S.parameterAt k.succ)
        (S.segmentSplitInsertVertex k) : ℝ) at ht_right
    rw [S.segmentSplitParameterAt_insert k (S.parameterAt k.succ)] at ht_right
    rw [hcenter_left]
    exact S.path_segment_mem_model_domain k t ht_left ht_right
  by_cases hj_right : j = k.succ
  · subst j
    have hright_index := S.segmentSplitInsertVertex_succAbove_right k
    change
      (S.segmentSplitParameterAt k (S.parameterAt k.succ)
          (S.segmentSplitInsertVertex k) : ℝ) ≤ (t : ℝ) at ht_left
    rw [S.segmentSplitParameterAt_insert k (S.parameterAt k.succ)] at ht_left
    have hparam_right :
        S.segmentSplitParameterAt k (S.parameterAt k.succ)
            ((k.succ : Fin (S.length + 1)).succ) =
          S.parameterAt k.succ := by
      rw [← hright_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) k.succ]
    rw [hparam_right] at ht_right
    have ht_eq : t = S.parameterAt k.succ := by
      ext
      exact le_antisymm ht_right ht_left
    change p t ∈
      (localModels.chartAt
        (S.segmentEndpointChartInsertCenterAt k c
          (S.segmentSplitInsertVertex k))).domain
    rw [S.segmentEndpointChartInsertCenterAt_insert k c, ht_eq]
    exact hc
  by_cases hj_before : (j : ℕ) < (k : ℕ)
  · let e : Fin S.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
    have hparam_left :
        S.segmentSplitParameterAt k (S.parameterAt k.succ) j.castSucc =
          S.parameterAt e.castSucc := by
      rw [← hleft_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) e.castSucc]
    have hparam_right :
        S.segmentSplitParameterAt k (S.parameterAt k.succ) j.succ =
          S.parameterAt e.succ := by
      rw [← hright_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) e.succ]
    have hcenter_left :
        S.segmentEndpointChartInsertCenterAt k c j.castSucc =
          S.centerAt e.castSucc := by
      rw [← hleft_index, S.segmentEndpointChartInsertCenterAt_old k c e.castSucc]
    rw [hparam_left] at ht_left
    rw [hparam_right] at ht_right
    rw [hcenter_left]
    exact S.path_segment_mem_model_domain e t ht_left ht_right
  · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hj_left (Fin.ext h)
    have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
      intro h
      exact hj_right (Fin.ext h)
    have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
      omega
    let e : Fin S.length := ⟨(j : ℕ) - 1, by omega⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
    have hparam_left :
        S.segmentSplitParameterAt k (S.parameterAt k.succ) j.castSucc =
          S.parameterAt e.castSucc := by
      rw [← hleft_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) e.castSucc]
    have hparam_right :
        S.segmentSplitParameterAt k (S.parameterAt k.succ) j.succ =
          S.parameterAt e.succ := by
      rw [← hright_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) e.succ]
    have hcenter_left :
        S.segmentEndpointChartInsertCenterAt k c j.castSucc =
          S.centerAt e.castSucc := by
      rw [← hleft_index, S.segmentEndpointChartInsertCenterAt_old k c e.castSucc]
    rw [hparam_left] at ht_left
    rw [hparam_right] at ht_right
    rw [hcenter_left]
    exact S.path_segment_mem_model_domain e t ht_left ht_right

omit [RiemannSurface X] in
/-- The endpoint still lies in the terminal chart after an endpoint chart insertion.

%%handwave
name:
  Endpoint chart insertion preserves terminal-domain membership
statement:
  After inserting a zero-length chart handoff at an interior vertex, the endpoint $x$ remains in the domain of the final assigned chart.
proof:
  The terminal center is unchanged, so this is the original endpoint-domain condition.
-/
theorem segmentEndpointChartInsert_terminal_endpoint_mem_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X) :
    x ∈
      (localModels.chartAt
        (S.segmentEndpointChartInsertCenterAt k c
          (Fin.last (S.length + 1)))).domain := by
  simpa [S.segmentEndpointChartInsertCenterAt_last k c] using
    S.terminal_endpoint_mem_domain

omit [RiemannSurface X] in
/--
Transition data for every handoff of an endpoint chart-insertion skeleton.

The old handoff `U → W` at the right endpoint of segment `k` is replaced by
`U → c → W`; all other handoffs are transported from the old skeleton.
-/
def segmentEndpointChartInsertTransitionAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
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
    ∀ j : Fin (S.length + 1),
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt
          (S.segmentEndpointChartInsertCenterAt k c j.castSucc))
        (localModels.chartAt
          (S.segmentEndpointChartInsertCenterAt k c j.succ))
        (p (S.segmentSplitParameterAt k (S.parameterAt k.succ) j.succ)) := by
  intro j
  by_cases hj_left : j = k.castSucc
  · subst j
    have hleft_index := S.segmentSplitInsertVertex_succAbove_left k
    have hU :
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c k.castSucc.castSucc) =
          localModels.chartAt (S.centerAt k.castSucc) := by
      rw [← hleft_index, S.segmentEndpointChartInsertCenterAt_old k c k.castSucc]
    have hV :
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c
              ((k.castSucc : Fin (S.length + 1)).succ)) =
          localModels.chartAt c := by
      rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
      change
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c
              (S.segmentSplitInsertVertex k)) =
          localModels.chartAt c
      rw [S.segmentEndpointChartInsertCenterAt_insert k c]
    have hpoint :
        p (S.segmentSplitParameterAt k (S.parameterAt k.succ)
            ((k.castSucc : Fin (S.length + 1)).succ)) =
          p (S.parameterAt k.succ) := by
      rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
      change
        p (S.segmentSplitParameterAt k (S.parameterAt k.succ)
          (S.segmentSplitInsertVertex k)) =
          p (S.parameterAt k.succ)
      rw [S.segmentSplitParameterAt_insert k (S.parameterAt k.succ)]
    exact localRealMobiusTransitionData_congr hU hV hpoint Tleft
  by_cases hj_right : j = k.succ
  · subst j
    have hright_index := S.segmentSplitInsertVertex_succAbove_right k
    have hU :
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c
              ((k.succ : Fin (S.length + 1)).castSucc)) =
          localModels.chartAt c := by
      change
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c
              (S.segmentSplitInsertVertex k)) =
          localModels.chartAt c
      rw [S.segmentEndpointChartInsertCenterAt_insert k c]
    have hV :
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c
              ((k.succ : Fin (S.length + 1)).succ)) =
          localModels.chartAt (S.centerAt k.succ) := by
      rw [← hright_index, S.segmentEndpointChartInsertCenterAt_old k c k.succ]
    have hpoint :
        p (S.segmentSplitParameterAt k (S.parameterAt k.succ)
            ((k.succ : Fin (S.length + 1)).succ)) =
          p (S.parameterAt k.succ) := by
      rw [← hright_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) k.succ]
    exact localRealMobiusTransitionData_congr hU hV hpoint Tright
  by_cases hj_before : (j : ℕ) < (k : ℕ)
  · let e : Fin S.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
    have hU :
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c j.castSucc) =
          localModels.chartAt (S.centerAt e.castSucc) := by
      rw [← hleft_index, S.segmentEndpointChartInsertCenterAt_old k c e.castSucc]
    have hV :
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c j.succ) =
          localModels.chartAt (S.centerAt e.succ) := by
      rw [← hright_index, S.segmentEndpointChartInsertCenterAt_old k c e.succ]
    have hpoint :
        p (S.segmentSplitParameterAt k (S.parameterAt k.succ) j.succ) =
          p (S.parameterAt e.succ) := by
      rw [← hright_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) e.succ]
    exact localRealMobiusTransitionData_congr hU hV hpoint (S.transitionAt e)
  · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hj_left (Fin.ext h)
    have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
      intro h
      exact hj_right (Fin.ext h)
    have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
      omega
    let e : Fin S.length := ⟨(j : ℕ) - 1, by omega⟩
    have hleft_index :
        (S.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      S.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
    have hright_index :
        (S.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      S.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
    have hU :
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c j.castSucc) =
          localModels.chartAt (S.centerAt e.castSucc) := by
      rw [← hleft_index, S.segmentEndpointChartInsertCenterAt_old k c e.castSucc]
    have hV :
        localModels.chartAt
            (S.segmentEndpointChartInsertCenterAt k c j.succ) =
          localModels.chartAt (S.centerAt e.succ) := by
      rw [← hright_index, S.segmentEndpointChartInsertCenterAt_old k c e.succ]
    have hpoint :
        p (S.segmentSplitParameterAt k (S.parameterAt k.succ) j.succ) =
          p (S.parameterAt e.succ) := by
      rw [← hright_index,
        S.segmentSplitParameterAt_old k (S.parameterAt k.succ) e.succ]
    exact localRealMobiusTransitionData_congr hU hV hpoint (S.transitionAt e)

omit [RiemannSurface X] in
/--
Insert a zero-length chart handoff at the right endpoint of segment `k`.
-/
noncomputable def segmentEndpointChartInsertSkeleton
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
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p where
  length := S.length + 1
  length_pos := Nat.succ_pos S.length
  parameterAt := S.segmentSplitParameterAt k (S.parameterAt k.succ)
  parameterAt_zero := S.segmentSplitParameterAt_zero k (S.parameterAt k.succ)
  parameterAt_last := S.segmentSplitParameterAt_last k (S.parameterAt k.succ)
  parameterAt_mono :=
    S.segmentSplitParameterAt_mono k (S.parameterAt k.succ)
      (S.parameterAt_mono k) le_rfl
  centerAt := S.segmentEndpointChartInsertCenterAt k c
  sample_mem_model_domain :=
    S.segmentEndpointChartInsert_sample_mem_model_domain k c hc
  path_segment_mem_model_domain :=
    S.segmentEndpointChartInsert_path_segment_mem_model_domain k c hc
  terminal_endpoint_mem_domain :=
    S.segmentEndpointChartInsert_terminal_endpoint_mem_domain k c
  transitionAt :=
    S.segmentEndpointChartInsertTransitionAt k c Tleft Tright
  initialTransition := by
    exact localRealMobiusTransitionData_congr rfl
      (by simp [S.segmentEndpointChartInsertCenterAt_zero k c]) rfl
      S.initialTransition

omit [RiemannSurface X] in
/--
%%handwave
name:
  Endpoint chart insertion preserves the terminal center of the skeleton
statement:
  Replacing one handoff by two zero-length handoffs through a chosen intermediate chart leaves the terminal chart center unchanged.
proof:
  The original last vertex is preserved as the new last vertex with its original center.
-/
@[simp]
theorem segmentEndpointChartInsertSkeleton_terminalCenter
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
    (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).terminalCenter =
      S.terminalCenter := by
  simp [segmentEndpointChartInsertSkeleton, terminalCenter]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Left representative of an inserted endpoint chart
statement:
  The first of the two new handoffs through an inserted chart has precisely the chosen representative $A$ from the old left chart to the inserted chart.
proof:
  At the left new handoff the construction transports the chosen transition data without changing its representative.
-/
@[simp]
theorem segmentEndpointChartInsertSkeleton_transitionAt_left_representative
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
    ((S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).transitionAt
        k.castSucc).representative =
      Tleft.representative := by
  simp [segmentEndpointChartInsertSkeleton,
    segmentEndpointChartInsertTransitionAt]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Right representative of an inserted endpoint chart
statement:
  The second of the two new handoffs through an inserted chart has precisely the chosen representative $B$ from that chart to the old right chart.
proof:
  At the right new handoff the construction transports the chosen transition data without changing its representative.
-/
@[simp]
theorem segmentEndpointChartInsertSkeleton_transitionAt_right_representative
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
    ((S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).transitionAt
        (k.succ : Fin (S.length + 1))).representative =
      Tright.representative := by
  have hne : (k.succ : Fin (S.length + 1)) ≠ k.castSucc := by
    intro h
    have : (k : ℕ) + 1 = (k : ℕ) := by
      exact Fin.ext_iff.mp h
    omega
  simp [segmentEndpointChartInsertSkeleton,
    segmentEndpointChartInsertTransitionAt, hne]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Representatives before an inserted endpoint chart are unchanged
statement:
  Every handoff with index $j<k$ retains its original representative after a chart is inserted at the right endpoint of segment $k$.
proof:
  Such handoffs lie before the insertion and their old transition data are transported unchanged.
-/
@[simp]
theorem segmentEndpointChartInsertSkeleton_transitionAt_before_representative
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
    (j : Fin (S.length + 1)) (hj : (j : ℕ) < (k : ℕ)) :
    ((S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).transitionAt
        j).representative =
      (S.transitionAt ⟨j, Nat.lt_trans hj k.isLt⟩).representative := by
  have hne_left : j ≠ k.castSucc := by
    intro h
    have : (j : ℕ) = (k : ℕ) := Fin.ext_iff.mp h
    omega
  have hne_right : j ≠ (k.succ : Fin (S.length + 1)) := by
    intro h
    have : (j : ℕ) = (k : ℕ) + 1 := Fin.ext_iff.mp h
    omega
  simp [segmentEndpointChartInsertSkeleton,
    segmentEndpointChartInsertTransitionAt, hne_left, hne_right, hj]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Representatives after an inserted endpoint chart are shifted unchanged
statement:
  Every new handoff with index $j>k+1$ has the representative of the original handoff at index $j-1$.
proof:
  Past the duplicate vertex, deleting its position recovers the old index and the corresponding transition data are transported unchanged.
-/
@[simp]
theorem segmentEndpointChartInsertSkeleton_transitionAt_after_representative
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
    (j : Fin (S.length + 1)) (hj : (k : ℕ) + 1 < (j : ℕ)) :
    ((S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).transitionAt
        j).representative =
      (S.transitionAt ⟨(j : ℕ) - 1, by omega⟩).representative := by
  have hne_left : j ≠ k.castSucc := by
    intro h
    have : (j : ℕ) = (k : ℕ) := Fin.ext_iff.mp h
    omega
  have hne_right : j ≠ (k.succ : Fin (S.length + 1)) := by
    intro h
    have : (j : ℕ) = (k : ℕ) + 1 := Fin.ext_iff.mp h
    omega
  have hnot_before : ¬(j : ℕ) < (k : ℕ) := by omega
  simp [segmentEndpointChartInsertSkeleton,
    segmentEndpointChartInsertTransitionAt, hne_left, hne_right, hnot_before]

omit [RiemannSurface X] in
/--
Before the inserted endpoint chart, the accumulated Mobius products agree
with the old skeleton.

%%handwave
name:
  Accumulated products agree before an inserted endpoint chart
statement:
  If a chart is inserted at the right endpoint of segment $k$, then $M_j(S')=M_j(S)$ for every $j\le k$.
proof:
  Induct on $j$ using equality of the initial transition and of every handoff representative before the insertion.
-/
theorem segmentEndpointChartInsertSkeleton_accumulatedMobiusNat_eq_of_le_left
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
    ∀ n : ℕ, n ≤ (k : ℕ) →
      (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).accumulatedMobiusNat n =
        S.accumulatedMobiusNat n := by
  intro n hn
  induction n with
  | zero =>
      simp [segmentEndpointChartInsertSkeleton, accumulatedMobiusNat]
  | succ n ih =>
      have hn_before : n < (k : ℕ) := Nat.succ_le_iff.mp hn
      have hn_old : n < S.length := Nat.lt_trans hn_before k.isLt
      have hn_new :
          n <
            (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).length := by
        simp [segmentEndpointChartInsertSkeleton]
        omega
      let R := S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright
      let j : Fin (S.length + 1) := ⟨n, by omega⟩
      have hRstep :
          R.accumulatedMobiusNat (n + 1) =
            R.accumulatedMobiusNat n *
              (R.transitionAt j).representative⁻¹ := by
        simpa [R, j] using R.accumulatedMobiusNat_succ_of_lt hn_new
      have hSstep :
          S.accumulatedMobiusNat (n + 1) =
            S.accumulatedMobiusNat n *
              (S.transitionAt ⟨n, hn_old⟩).representative⁻¹ :=
        S.accumulatedMobiusNat_succ_of_lt hn_old
      have htrans :
          (R.transitionAt j).representative =
            (S.transitionAt ⟨n, hn_old⟩).representative := by
        simpa [R, j] using
          S.segmentEndpointChartInsertSkeleton_transitionAt_before_representative
            k c hc Tleft Tright j hn_before
      rw [hRstep, ih (Nat.le_of_lt hn_before), htrans, hSstep]

omit [RiemannSurface X] in
/--
After the inserted pair of zero-length handoffs, the accumulated Mobius
product has the same PSL class as the old accumulated product with the index
shifted down by one.

%%handwave
name:
  Projective accumulated products agree after compatible endpoint chart insertion
statement:
  Suppose an old handoff representative $T_k$ and two inserted representatives $A,B$ satisfy $[T_k]=[BA]$. If $S'$ inserts the intermediate chart, then for every $k+2\le j\le\ell+1$, $[M_j(S')]=[M_{j-1}(S)]$.
proof:
  At the first index after both new handoffs, expand the recurrences and replace $[(BA)^{-1}]$ by $[T_k^{-1}]$. Induct along the tail, where every later representative agrees with the corresponding old representative after shifting by one.
-/
theorem segmentEndpointChartInsertSkeleton_accumulatedMobiusNat_projection_eq_tail
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
    (hTransitionProjection :
      realMobiusProjection (S.transitionAt k).representative =
        realMobiusProjection (Tright.representative * Tleft.representative)) :
    ∀ n : ℕ, (k : ℕ) + 2 ≤ n → n ≤ S.length + 1 →
      realMobiusProjection
          ((S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).accumulatedMobiusNat n) =
        realMobiusProjection (S.accumulatedMobiusNat (n - 1)) := by
  intro n hn_left hn_right
  induction n with
  | zero =>
      omega
  | succ n ih =>
      let R := S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright
      by_cases hn_base : n = (k : ℕ) + 1
      · subst n
        have hprefix :
            R.accumulatedMobiusNat (k : ℕ) =
              S.accumulatedMobiusNat (k : ℕ) :=
          S.segmentEndpointChartInsertSkeleton_accumulatedMobiusNat_eq_of_le_left
            k c hc Tleft Tright (k : ℕ) le_rfl
        have hk_new : (k : ℕ) < R.length := by
          simp [R, segmentEndpointChartInsertSkeleton]
        have hks_new : (k : ℕ) + 1 < R.length := by
          simp [R, segmentEndpointChartInsertSkeleton]
        have hRstep₁ :
            R.accumulatedMobiusNat ((k : ℕ) + 1) =
              R.accumulatedMobiusNat (k : ℕ) *
                (R.transitionAt k.castSucc).representative⁻¹ := by
          have h := R.accumulatedMobiusNat_succ_of_lt hk_new
          change R.accumulatedMobiusNat ((k : ℕ) + 1) =
            R.accumulatedMobiusNat (k : ℕ) *
              (R.transitionAt k.castSucc).representative⁻¹ at h
          exact h
        have hRstep₂ :
            R.accumulatedMobiusNat ((k : ℕ) + 2) =
              R.accumulatedMobiusNat ((k : ℕ) + 1) *
                (R.transitionAt (k.succ : Fin (S.length + 1))).representative⁻¹ := by
          have h := R.accumulatedMobiusNat_succ_of_lt hks_new
          change R.accumulatedMobiusNat (((k : ℕ) + 1) + 1) =
            R.accumulatedMobiusNat ((k : ℕ) + 1) *
              (R.transitionAt (k.succ : Fin (S.length + 1))).representative⁻¹ at h
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        have hSstep :
            S.accumulatedMobiusNat ((k : ℕ) + 1) =
              S.accumulatedMobiusNat (k : ℕ) *
                (S.transitionAt k).representative⁻¹ := by
          have h := S.accumulatedMobiusNat_succ_of_lt k.isLt
          change S.accumulatedMobiusNat ((k : ℕ) + 1) =
            S.accumulatedMobiusNat (k : ℕ) *
              (S.transitionAt k).representative⁻¹ at h
          exact h
        have hleft :
            (R.transitionAt k.castSucc).representative =
              Tleft.representative := by
          simp [R]
        have hright :
            (R.transitionAt (k.succ : Fin (S.length + 1))).representative =
              Tright.representative := by
          simp [R]
        have htarget : ((k : ℕ) + 2) - 1 = (k : ℕ) + 1 := by omega
        change
          realMobiusProjection (R.accumulatedMobiusNat ((k : ℕ) + 2)) =
            realMobiusProjection (S.accumulatedMobiusNat (((k : ℕ) + 2) - 1))
        rw [htarget, hRstep₂, hRstep₁, hleft, hright, hprefix, hSstep]
        calc
          realMobiusProjection
              ((S.accumulatedMobiusNat (k : ℕ) * Tleft.representative⁻¹) *
                Tright.representative⁻¹) =
              realMobiusProjection
                (S.accumulatedMobiusNat (k : ℕ) *
                  (Tright.representative * Tleft.representative)⁻¹) := by
                simp [mul_assoc]
          _ =
              realMobiusProjection
                (S.accumulatedMobiusNat (k : ℕ) *
                  (S.transitionAt k).representative⁻¹) := by
                simp [hTransitionProjection]
      · have hn_tail_left : (k : ℕ) + 2 ≤ n := by omega
        have hn_tail_right : n ≤ S.length + 1 := by omega
        have hn_new : n < R.length := by
          simp [R, segmentEndpointChartInsertSkeleton]
          omega
        have hn_old_step : n - 1 < S.length := by omega
        let j : Fin (S.length + 1) := ⟨n, by omega⟩
        have hRstep :
            R.accumulatedMobiusNat (n + 1) =
              R.accumulatedMobiusNat n *
                (R.transitionAt j).representative⁻¹ := by
          have h := R.accumulatedMobiusNat_succ_of_lt hn_new
          change R.accumulatedMobiusNat (n + 1) =
            R.accumulatedMobiusNat n *
              (R.transitionAt j).representative⁻¹ at h
          exact h
        have hSstep :
            S.accumulatedMobiusNat n =
              S.accumulatedMobiusNat (n - 1) *
                (S.transitionAt ⟨n - 1, hn_old_step⟩).representative⁻¹ := by
          have hn_pos : 0 < n := by omega
          simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)] using
            (S.accumulatedMobiusNat_succ_of_lt (n := n - 1) hn_old_step)
        have htrans :
            (R.transitionAt j).representative =
              (S.transitionAt ⟨n - 1, hn_old_step⟩).representative := by
          have hn_after : (k : ℕ) + 1 < n := by omega
          simpa [R, j] using
            S.segmentEndpointChartInsertSkeleton_transitionAt_after_representative
              k c hc Tleft Tright j hn_after
        have ih' :
            realMobiusProjection (R.accumulatedMobiusNat n) =
              realMobiusProjection (S.accumulatedMobiusNat (n - 1)) :=
          ih hn_tail_left hn_tail_right
        have htarget : (n + 1) - 1 = n := by omega
        change
          realMobiusProjection (R.accumulatedMobiusNat (n + 1)) =
            realMobiusProjection (S.accumulatedMobiusNat ((n + 1) - 1))
        rw [htarget, hRstep]
        calc
          realMobiusProjection
              (R.accumulatedMobiusNat n *
                (R.transitionAt j).representative⁻¹) =
              realMobiusProjection (R.accumulatedMobiusNat n) *
                (realMobiusProjection (R.transitionAt j).representative)⁻¹ := by
                simp
          _ =
              realMobiusProjection (S.accumulatedMobiusNat (n - 1)) *
                (realMobiusProjection
                  (S.transitionAt ⟨n - 1, hn_old_step⟩).representative)⁻¹ := by
                rw [ih', htrans]
          _ =
              realMobiusProjection
                (S.accumulatedMobiusNat (n - 1) *
                  (S.transitionAt ⟨n - 1, hn_old_step⟩).representative⁻¹) := by
                simp
          _ = realMobiusProjection (S.accumulatedMobiusNat n) := by
                rw [← hSstep]

omit [RiemannSurface X] in
/--
Inserting a zero-length endpoint chart handoff preserves the terminal Mobius
PSL class.

%%handwave
name:
  Compatible endpoint chart insertion preserves the terminal projective class
statement:
  If the two transitions $A,B$ through an inserted chart satisfy $[BA]=[T_k]$, then the terminal accumulated classes before and after insertion agree: $[M_{\mathrm{term}}(S')]=[M_{\mathrm{term}}(S)]$.
proof:
  Apply the shifted-tail equality of accumulated projective products at the new final index $\ell+1$.
-/
theorem segmentEndpointChartInsertSkeleton_terminalMobius_projection_eq
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
    (hTransitionProjection :
      realMobiusProjection (S.transitionAt k).representative =
        realMobiusProjection (Tright.representative * Tleft.representative)) :
    realMobiusProjection
        (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).terminalMobius =
      realMobiusProjection S.terminalMobius := by
  let R := S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright
  have htail :
      realMobiusProjection (R.accumulatedMobiusNat (S.length + 1)) =
        realMobiusProjection (S.accumulatedMobiusNat ((S.length + 1) - 1)) := by
    simpa [R] using
      S.segmentEndpointChartInsertSkeleton_accumulatedMobiusNat_projection_eq_tail
        k c hc Tleft Tright hTransitionProjection
        (S.length + 1) (by omega) le_rfl
  change
    realMobiusProjection (R.accumulatedMobiusNat (S.length + 1)) =
      realMobiusProjection (S.accumulatedMobiusNat S.length)
  simpa using htail

omit [RiemannSurface X] in
/--
Inserting a zero-length endpoint chart handoff preserves the terminal branch
formula.

%%handwave
name:
  Compatible endpoint chart insertion preserves the terminal formula
statement:
  Under the factorization condition $[BA]=[T_k]$, inserting the chart between the two sides of handoff $k$ leaves the terminal branch formula unchanged at every $z\in X$.
proof:
  The terminal center is unchanged and the terminal accumulated representatives have equal projective classes, so their actions on the common terminal chart coordinate agree.
-/
theorem segmentEndpointChartInsertSkeleton_terminalFormulaAt_eq
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
    (hTransitionProjection :
      realMobiusProjection (S.transitionAt k).representative =
        realMobiusProjection (Tright.representative * Tleft.representative))
    (z : X) :
    (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).terminalFormulaAt z =
      S.terminalFormulaAt z := by
  let R := S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright
  exact
    R.terminalFormulaAt_eq_of_terminalMobius_projection_eq_terminalCenter_eq
      S
      (S.segmentEndpointChartInsertSkeleton_terminalMobius_projection_eq
        k c hc Tleft Tright hTransitionProjection)
      (S.segmentEndpointChartInsertSkeleton_terminalCenter
        k c hc Tleft Tright)
      z

omit [RiemannSurface X] in
/--
Inserting a zero-length endpoint chart handoff preserves terminal value.

%%handwave
name:
  Compatible endpoint chart insertion preserves terminal value
statement:
  Under the factorization condition $[BA]=[T_k]$, inserting an intermediate chart at a segment endpoint leaves the terminal value unchanged.
proof:
  Evaluate the preserved terminal branch formula at the endpoint $x$.
-/
theorem segmentEndpointChartInsertSkeleton_terminalValue_eq
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
    (hTransitionProjection :
      realMobiusProjection (S.transitionAt k).representative =
        realMobiusProjection (Tright.representative * Tleft.representative)) :
    (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).terminalValue =
      S.terminalValue := by
  simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalValue] using
    S.segmentEndpointChartInsertSkeleton_terminalFormulaAt_eq
      k c hc Tleft Tright hTransitionProjection x

omit [RiemannSurface X] in
/--
Split a skeleton at a located parameter and insert a chosen chart at the new
vertex.  This is the primitive alignment operation used to compare two
same-path handoff skeletons: after the split, the selected chart `c` is
inserted by a zero-length handoff at the inserted parameter.
-/
noncomputable def segmentSplitEndpointChartInsertSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ)
    (c : X)
    (hc : p τ ∈ (localModels.chartAt c).domain) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p := by
  classical
  let R := S.segmentSplitSkeleton k τ hτ_left hτ_right
  let j : Fin R.length := k.castSucc
  have hcR :
      p (R.parameterAt j.succ) ∈ (localModels.chartAt c).domain := by
    change
      p (S.segmentSplitParameterAt k τ
          ((k.castSucc : Fin (S.length + 1)).succ)) ∈
        (localModels.chartAt c).domain
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
    change
      p (S.segmentSplitParameterAt k τ
          (S.segmentSplitInsertVertex k)) ∈
        (localModels.chartAt c).domain
    simpa using hc
  let Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (R.centerAt j.castSucc))
        (localModels.chartAt c)
        (p (R.parameterAt j.succ)) :=
    Classical.choice
      (localModels.transition_localRealMobius
        (R.centerAt j.castSucc) c
        (p (R.parameterAt j.succ))
        ⟨R.path_segment_mem_model_domain j (R.parameterAt j.succ)
            (R.parameterAt_mono j) le_rfl,
          hcR⟩)
  let Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt c)
        (localModels.chartAt (R.centerAt j.succ))
        (p (R.parameterAt j.succ)) :=
    Classical.choice
      (localModels.transition_localRealMobius
        c (R.centerAt j.succ)
        (p (R.parameterAt j.succ))
        ⟨hcR, R.sample_mem_model_domain j.succ⟩)
  exact R.segmentEndpointChartInsertSkeleton j c hcR Tleft Tright

omit [RiemannSurface X] in
/--
Split a skeleton at an arbitrary parameter and insert a chosen chart at the
new vertex, choosing a containing segment by `exists_segment_contains_parameter`.
-/
noncomputable def splitAtParameterEndpointChartInsertSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) (c : X)
    (hc : p τ ∈ (localModels.chartAt c).domain) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p :=
  let k := Classical.choose (S.exists_segment_contains_parameter τ)
  let hk := Classical.choose_spec (S.exists_segment_contains_parameter τ)
  S.segmentSplitEndpointChartInsertSkeleton k τ hk.1 hk.2 c hc

omit [RiemannSurface X] in
/--
Insert the first `m` vertices of `T` into `S`, using the chart carried by
`T` at each inserted vertex.

The recursion is deliberately parameter-count based rather than list based:
`m = T.length + 1` inserts every sampled vertex of `T`.
-/
noncomputable def insertFirstVerticesOfSkeleton
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ℕ → PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  | 0 => S
  | m + 1 =>
      let R := insertFirstVerticesOfSkeleton S T m
      if h : m < T.length + 1 then
        R.splitAtParameterEndpointChartInsertSkeleton
          (T.parameterAt ⟨m, h⟩)
          (T.centerAt ⟨m, h⟩)
          (by simpa using T.sample_mem_model_domain ⟨m, h⟩)
      else
        R

omit [RiemannSurface X] in
/-- Insert every sampled vertex of `T` into `S`. -/
noncomputable def insertAllVerticesOfSkeleton
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p :=
  S.insertFirstVerticesOfSkeleton T (T.length + 1)

omit [RiemannSurface X] in
/--
%%handwave
name:
  Splitting and inserting a chart adds two segments
statement:
  Splitting a segment at $\tau$ and then inserting a zero-length chart handoff there increases the skeleton length from $\ell$ to $\ell+2$.
proof:
  The ordinary split adds one segment, and duplicating the new endpoint for the chart handoff adds one more.
-/
@[simp]
theorem segmentSplitEndpointChartInsertSkeleton_length
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ)
    (c : X)
    (hc : p τ ∈ (localModels.chartAt c).domain) :
    (S.segmentSplitEndpointChartInsertSkeleton
      k τ hτ_left hτ_right c hc).length = S.length + 2 := by
  unfold segmentSplitEndpointChartInsertSkeleton
  simp [segmentSplitSkeleton, segmentEndpointChartInsertSkeleton]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Arbitrary-parameter chart insertion adds two segments
statement:
  Locating any parameter $\tau$ and inserting a chosen chart there increases the skeleton length by two.
proof:
  Choose a containing segment and apply the length formula for a split followed by endpoint chart insertion.
-/
@[simp]
theorem splitAtParameterEndpointChartInsertSkeleton_length
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) (c : X)
    (hc : p τ ∈ (localModels.chartAt c).domain) :
    (S.splitAtParameterEndpointChartInsertSkeleton τ c hc).length =
      S.length + 2 := by
  classical
  unfold splitAtParameterEndpointChartInsertSkeleton
  simp

omit [RiemannSurface X] in
/--
Inserting the first `m` sampled vertices of `T` into `S` adds exactly two
subdivision intervals per inserted sampled vertex, as long as `m` is within
the sampled-vertex range of `T`.

%%handwave
name:
  Length after inserting the first charted vertices of another skeleton
statement:
  Inserting the first $m$ sampled vertices of $T$ into $S$, together with their chart centers, gives length $\ell_S+2m$ whenever $m\le\ell_T+1$.
proof:
  Induct on $m$. Each parameter split followed by chart insertion adds two segments.
-/
theorem insertFirstVerticesOfSkeleton_length_of_le
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m : ℕ, m ≤ T.length + 1 →
      (S.insertFirstVerticesOfSkeleton T m).length = S.length + 2 * m := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [insertFirstVerticesOfSkeleton]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ T.length + 1 := by omega
      have hm_lt : m < T.length + 1 := by omega
      simp [insertFirstVerticesOfSkeleton, hm_lt, ih hm_prev, Nat.mul_succ,
        Nat.add_comm, Nat.add_left_comm]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Length after inserting every charted vertex of another skeleton
statement:
  Inserting all $\ell_T+1$ sampled vertices and chart centers of $T$ into $S$ produces length $\ell_S+2(\ell_T+1)$.
proof:
  Specialize the preceding prefix-length formula to all vertices of $T$.
-/
@[simp]
theorem insertAllVerticesOfSkeleton_length
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    (S.insertAllVerticesOfSkeleton T).length =
      S.length + 2 * (T.length + 1) := by
  simpa [insertAllVerticesOfSkeleton] using
    S.insertFirstVerticesOfSkeleton_length_of_le T (T.length + 1) le_rfl

omit [RiemannSurface X] in
/--
Endpoint-chart insertion at the right endpoint of a segment duplicates that
endpoint parameter once in the subdivision parameter list.

%%handwave
name:
  Parameter multiset of an endpoint chart insertion
statement:
  Duplicating the right endpoint parameter $t_{k+1}$ to insert a chart produces a parameter list that is a permutation of $t_{k+1}$ followed by the original list.
proof:
  The new parameter tuple is obtained by inserting one additional copy of $t_{k+1}$; apply the finite-tuple insertion permutation.
-/
theorem segmentEndpointChartInsertSkeleton_parameterList_perm
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
    List.Perm
      (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright).parameterList
      (S.parameterAt k.succ :: S.parameterList) := by
  classical
  change List.Perm
    (List.ofFn (S.segmentSplitParameterAt k (S.parameterAt k.succ)))
    (S.parameterAt k.succ :: List.ofFn S.parameterAt)
  rw [S.segmentSplitParameterAt_eq_insertNth k (S.parameterAt k.succ)]
  exact
    ofFn_fin_insertNth_perm (S.segmentSplitInsertVertex k)
      (S.parameterAt k.succ) S.parameterAt

omit [RiemannSurface X] in
/--
Splitting at a parameter and then inserting a chosen endpoint chart adds two
copies of that parameter to the subdivision parameter list, up to permutation.

%%handwave
name:
  Parameter multiset of a split with chart insertion
statement:
  Splitting at $\tau$ and inserting a chart there yields a parameter list that is a permutation of $\tau,\tau$ followed by the original list.
proof:
  The split first inserts one copy of $\tau$, and the zero-length chart handoff inserts a second. Compose the two insertion permutations.
-/
theorem segmentSplitEndpointChartInsertSkeleton_parameterList_perm
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ)
    (c : X)
    (hc : p τ ∈ (localModels.chartAt c).domain) :
    List.Perm
      (S.segmentSplitEndpointChartInsertSkeleton
        k τ hτ_left hτ_right c hc).parameterList
      (τ :: τ :: S.parameterList) := by
  classical
  unfold segmentSplitEndpointChartInsertSkeleton
  let R := S.segmentSplitSkeleton k τ hτ_left hτ_right
  let j : Fin R.length := k.castSucc
  have hRparam : R.parameterAt j.succ = τ := by
    change
      S.segmentSplitParameterAt k τ
        ((k.castSucc : Fin (S.length + 1)).succ) = τ
    rw [fin_castSucc_succ_eq_succ_castSucc k]
    exact S.segmentSplitParameterAt_insert k τ
  have hcR :
      p (R.parameterAt j.succ) ∈ (localModels.chartAt c).domain := by
    rw [hRparam]
    exact hc
  let Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (R.centerAt j.castSucc))
        (localModels.chartAt c)
        (p (R.parameterAt j.succ)) :=
    Classical.choice
      (localModels.transition_localRealMobius
        (R.centerAt j.castSucc) c
        (p (R.parameterAt j.succ))
        ⟨R.path_segment_mem_model_domain j (R.parameterAt j.succ)
            (R.parameterAt_mono j) le_rfl,
          hcR⟩)
  let Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt c)
        (localModels.chartAt (R.centerAt j.succ))
        (p (R.parameterAt j.succ)) :=
    Classical.choice
      (localModels.transition_localRealMobius
        c (R.centerAt j.succ)
        (p (R.parameterAt j.succ))
        ⟨hcR, R.sample_mem_model_domain j.succ⟩)
  have hend :
      List.Perm
        (R.segmentEndpointChartInsertSkeleton j c hcR Tleft Tright).parameterList
        (R.parameterAt j.succ :: R.parameterList) :=
    R.segmentEndpointChartInsertSkeleton_parameterList_perm j c hcR Tleft Tright
  exact
    hend.trans
      ((by
        rw [hRparam]
        exact List.Perm.cons τ
          (S.segmentSplitSkeleton_parameterList_perm k τ hτ_left hτ_right)) :
        List.Perm (R.parameterAt j.succ :: R.parameterList)
          (τ :: τ :: S.parameterList))

omit [RiemannSurface X] in
/--
Arbitrary-parameter endpoint-chart insertion adds two copies of the selected
parameter to the subdivision parameter list, up to permutation.

%%handwave
name:
  Parameter multiset of arbitrary-parameter chart insertion
statement:
  For any $\tau\in[0,1]$, inserting a chosen chart at $\tau$ yields a parameter list that is a permutation of $\tau,\tau$ followed by the original list.
proof:
  Locate a segment containing $\tau$ and apply the split-with-chart-insertion parameter formula.
-/
theorem splitAtParameterEndpointChartInsertSkeleton_parameterList_perm
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) (c : X)
    (hc : p τ ∈ (localModels.chartAt c).domain) :
    List.Perm
      (S.splitAtParameterEndpointChartInsertSkeleton τ c hc).parameterList
      (τ :: τ :: S.parameterList) := by
  classical
  unfold splitAtParameterEndpointChartInsertSkeleton
  exact
    S.segmentSplitEndpointChartInsertSkeleton_parameterList_perm
      (Classical.choose (S.exists_segment_contains_parameter τ)) τ
      (Classical.choose_spec (S.exists_segment_contains_parameter τ)).1
      (Classical.choose_spec (S.exists_segment_contains_parameter τ)).2 c hc

omit [RiemannSurface X] in
/-- The first `m` sampled parameters, with two recursive copies of each. -/
def firstDoubleParameterListOfSkeleton
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ℕ → List unitInterval
  | 0 => []
  | m + 1 =>
      if h : m < T.length + 1 then
        T.parameterAt ⟨m, h⟩ ::
          T.parameterAt ⟨m, h⟩ ::
            T.firstDoubleParameterListOfSkeleton m
      else
        T.firstDoubleParameterListOfSkeleton m

omit [RiemannSurface X] in
/--
%%handwave
name:
  Successor formula for the doubled recursive parameter prefix
statement:
  If $m$ is a valid vertex index, the doubled recursive list through $m$ is $t_m,t_m$ followed by the doubled list through $m-1$.
proof:
  The validity inequality selects the branch that prepends two copies of $t_m$.
-/
@[simp]
theorem firstDoubleParameterListOfSkeleton_succ_of_lt
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {m : ℕ} (hm : m < T.length + 1) :
    T.firstDoubleParameterListOfSkeleton (m + 1) =
      T.parameterAt ⟨m, hm⟩ ::
        T.parameterAt ⟨m, hm⟩ ::
          T.firstDoubleParameterListOfSkeleton m := by
  simp [firstDoubleParameterListOfSkeleton, hm]

omit [RiemannSurface X] in
/--
The recursively doubled list is a permutation of two copies of the recursively
single-listed parameters.

%%handwave
name:
  The doubled recursive prefix consists of two ordinary prefixes
statement:
  For every $m\le\ell+1$, the doubled recursive list of the first $m$ parameters is a permutation of two concatenated copies of the ordinary recursive first-$m$ list.
proof:
  Induct on $m$. Both descriptions add two copies of the new parameter; commute these copies past the earlier prefix lists and use the induction permutation.
-/
theorem firstDoubleParameterListOfSkeleton_perm_firstParameterList_append
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m : ℕ, m ≤ T.length + 1 →
      List.Perm (T.firstDoubleParameterListOfSkeleton m)
        (T.firstParameterListOfSkeleton m ++
          T.firstParameterListOfSkeleton m) := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [firstDoubleParameterListOfSkeleton, firstParameterListOfSkeleton]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ T.length + 1 := by omega
      have hm_lt : m < T.length + 1 := by omega
      let a := T.parameterAt ⟨m, hm_lt⟩
      let L := T.firstParameterListOfSkeleton m
      have hdouble :
          T.firstDoubleParameterListOfSkeleton (m + 1) =
            a :: a :: T.firstDoubleParameterListOfSkeleton m := by
        simp [firstDoubleParameterListOfSkeleton, hm_lt, a]
      have hsingle :
          T.firstParameterListOfSkeleton (m + 1) = a :: L := by
        simp [firstParameterListOfSkeleton, hm_lt, a, L]
      rw [hdouble, hsingle]
      have htail :
          List.Perm (a :: T.firstDoubleParameterListOfSkeleton m)
            (L ++ a :: L) := by
        have h1 :
            List.Perm (a :: T.firstDoubleParameterListOfSkeleton m)
              (a :: (L ++ L)) :=
          List.Perm.cons _ (ih hm_prev)
        have h2 : List.Perm (a :: (L ++ L)) (L ++ a :: L) := by
          have h2' : List.Perm ((a :: L) ++ L) ((L ++ [a]) ++ L) :=
            List.Perm.append_right L
              (List.perm_append_singleton a L).symm
          simpa [List.append_assoc] using h2'
        exact h1.trans h2
      exact List.Perm.cons a htail

omit [RiemannSurface X] in
/-- All recursively doubled sampled parameters are two copies of `parameterList`.

%%handwave
name:
  The complete doubled parameter list contains two copies of every parameter
statement:
  The doubled recursive list through all vertices is a permutation of the original parameter list concatenated with itself.
proof:
  Apply the doubled-prefix formula at $m=\ell+1$ and replace each complete ordinary recursive prefix by the original parameter list up to permutation.
-/
theorem firstDoubleParameterListOfSkeleton_all_perm_parameterList_append
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    List.Perm (T.firstDoubleParameterListOfSkeleton (T.length + 1))
      (T.parameterList ++ T.parameterList) := by
  have hdouble :=
    T.firstDoubleParameterListOfSkeleton_perm_firstParameterList_append
      (T.length + 1) le_rfl
  exact hdouble.trans
    ((List.Perm.append
      T.firstParameterListOfSkeleton_all_perm_parameterList
      T.firstParameterListOfSkeleton_all_perm_parameterList) :
      List.Perm
        (T.firstParameterListOfSkeleton (T.length + 1) ++
          T.firstParameterListOfSkeleton (T.length + 1))
        (T.parameterList ++ T.parameterList))

omit [RiemannSurface X] in
/--
Repeated endpoint-chart insertion inserts two recursive copies of each sampled
parameter of `T` into `S`.

%%handwave
name:
  Parameter multiset after inserting a charted vertex prefix
statement:
  After inserting the first $m$ vertices of $T$ with their charts into $S$, the resulting parameter list is a permutation of the doubled recursive first-$m$ parameter list of $T$ followed by the original list of $S$.
proof:
  Induct on $m$. Each new charted insertion contributes two copies of $t_m(T)$; compose its permutation with the induction hypothesis and the doubled recursion formula.
-/
theorem insertFirstVerticesOfSkeleton_parameterList_perm_of_le
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m : ℕ, m ≤ T.length + 1 →
      List.Perm (S.insertFirstVerticesOfSkeleton T m).parameterList
        (T.firstDoubleParameterListOfSkeleton m ++ S.parameterList) := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [insertFirstVerticesOfSkeleton, firstDoubleParameterListOfSkeleton]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ T.length + 1 := by omega
      have hm_lt : m < T.length + 1 := by omega
      let R := S.insertFirstVerticesOfSkeleton T m
      have hsplit :
          List.Perm
            (R.splitAtParameterEndpointChartInsertSkeleton
              (T.parameterAt ⟨m, hm_lt⟩)
              (T.centerAt ⟨m, hm_lt⟩)
              (by simpa using T.sample_mem_model_domain ⟨m, hm_lt⟩)).parameterList
            (T.parameterAt ⟨m, hm_lt⟩ ::
              T.parameterAt ⟨m, hm_lt⟩ :: R.parameterList) :=
        R.splitAtParameterEndpointChartInsertSkeleton_parameterList_perm
          (T.parameterAt ⟨m, hm_lt⟩)
          (T.centerAt ⟨m, hm_lt⟩)
          (by simpa using T.sample_mem_model_domain ⟨m, hm_lt⟩)
      have hih :
          List.Perm R.parameterList
            (T.firstDoubleParameterListOfSkeleton m ++ S.parameterList) :=
        ih hm_prev
      simpa [insertFirstVerticesOfSkeleton, firstDoubleParameterListOfSkeleton,
        hm_lt, R, List.cons_append] using
        hsplit.trans (List.Perm.cons _
          (List.Perm.cons _ hih))

omit [RiemannSurface X] in
/--
Inserting every sampled vertex of `T` into `S` adds two copies of `T`'s
parameter list to `S`'s parameter list, up to permutation.

%%handwave
name:
  Parameter multiset after inserting every charted vertex of another skeleton
statement:
  After inserting all sampled vertices and chart centers of $T$ into $S$, the resulting parameter list is a permutation of two copies of $T$'s parameter list followed by the parameter list of $S$.
proof:
  Apply the prefix insertion formula to all vertices and replace the complete doubled recursive list by two copies of $T$'s original parameter list.
-/
theorem insertAllVerticesOfSkeleton_parameterList_perm
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    List.Perm (S.insertAllVerticesOfSkeleton T).parameterList
      ((T.parameterList ++ T.parameterList) ++ S.parameterList) := by
  have hinsert :
      List.Perm (S.insertAllVerticesOfSkeleton T).parameterList
        (T.firstDoubleParameterListOfSkeleton (T.length + 1) ++
          S.parameterList) := by
    simpa [insertAllVerticesOfSkeleton] using
      S.insertFirstVerticesOfSkeleton_parameterList_perm_of_le T
        (T.length + 1) le_rfl
  exact hinsert.trans
    (List.Perm.append_right S.parameterList
      T.firstDoubleParameterListOfSkeleton_all_perm_parameterList_append)

/--
Inside the canonical terminal sheet, the path class of a lift is the sheet
label followed by the chosen path in the terminal sheet base.

This is the cover-theoretic local path-class formula needed by the
componentwise continuation proof: once a terminal sheet has been fixed, moving
the endpoint inside that sheet only appends a local path in the simply
connected base neighborhood.

%%handwave
name:
  Path-class formula inside a terminal sheet
statement:
  Let $C$ be the local sheet determined by a continued path and let $y\in C$. If $\lambda_C$ is the path class labeling the sheet over its center and $\sigma_y$ is the chosen path in the sheet base from that center to $\pi(y)$, then $[y]=\lambda_C*[\sigma_y]$.
proof:
  Moving $y$ back along $\sigma_y$ gives the fiber point labeling the sheet, hence $[y]*[\sigma_y]^{-1}=\lambda_C$. Compose on the right with $[\sigma_y]$ and cancel the inverse pair.
-/
theorem pathClass_eq_terminalSheetChart_label_trans_pathInSet_of_mem_terminalSheet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    PathHomotopyUniversalCover.pathClass y' =
      Path.Homotopic.Quotient.trans
        ((PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
          (S.terminalSheetChart.center : X)) S.terminalSheetChart.fiberPoint)
        (Path.Homotopic.Quotient.mk
          (PathHomotopyUniversalCover.pathInSet
            S.terminalSheetChart.center
            (⟨PathHomotopyUniversalCover.endpoint y',
              PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
                (by
                  simpa [terminalSheet,
                    PathHomotopyUniversalCover.LocalSheetChart.sheet] using
                    hy')⟩ : S.terminalSheetChart.base))) := by
  let C := S.terminalSheetChart
  have hyC : y' ∈ C.sheet := by
    simpa [terminalSheet, C,
      PathHomotopyUniversalCover.LocalSheetChart.sheet] using hy'
  rcases hyC with ⟨hyBase, hlabelFiber⟩
  let xC : C.base :=
    ⟨PathHomotopyUniversalCover.endpoint y', hyBase⟩
  let localPath : Path (C.center : X) (xC : X) :=
    PathHomotopyUniversalCover.pathInSet C.center xC
  have hlabel :
      Path.Homotopic.Quotient.trans
          (PathHomotopyUniversalCover.pathClass y')
          (Path.Homotopic.Quotient.symm
            (Path.Homotopic.Quotient.mk localPath)) =
        (PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
          (C.center : X)) C.fiberPoint := by
    have hlabelQ :=
      congrArg
        (fun η =>
          (PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
            (C.center : X)) η)
        hlabelFiber
    change
      (PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
          (C.center : X))
          (((PathHomotopyUniversalCover.localTrivializationFiberEquiv
              (x₀ := x₀) C.center) ⟨y', hyBase⟩).2) =
        (PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
          (C.center : X)) C.fiberPoint at hlabelQ
    rw [PathHomotopyUniversalCover.fiberPathClassEquiv_localTrivializationFiberEquiv_snd]
      at hlabelQ
    change
      Path.Homotopic.Quotient.trans
          (PathHomotopyUniversalCover.pathClass y')
          (Path.Homotopic.Quotient.mk localPath.symm) =
        (PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
          (C.center : X)) C.fiberPoint at hlabelQ
    simpa [localPath, Path.Homotopic.Quotient.mk_symm] using hlabelQ
  calc
    PathHomotopyUniversalCover.pathClass y' =
        Path.Homotopic.Quotient.trans
          (PathHomotopyUniversalCover.pathClass y')
          (Path.Homotopic.Quotient.refl
            (PathHomotopyUniversalCover.endpoint y')) := by
          rw [Path.Homotopic.Quotient.trans_refl]
    _ =
        Path.Homotopic.Quotient.trans
          (PathHomotopyUniversalCover.pathClass y')
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm
              (Path.Homotopic.Quotient.mk localPath))
            (Path.Homotopic.Quotient.mk localPath)) := by
          rw [Path.Homotopic.Quotient.symm_trans]
    _ =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.trans
            (PathHomotopyUniversalCover.pathClass y')
            (Path.Homotopic.Quotient.symm
              (Path.Homotopic.Quotient.mk localPath)))
          (Path.Homotopic.Quotient.mk localPath) := by
          rw [Path.Homotopic.Quotient.trans_assoc]
    _ =
        Path.Homotopic.Quotient.trans
          ((PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
            (C.center : X)) C.fiberPoint)
          (Path.Homotopic.Quotient.mk localPath) := by
          rw [hlabel]

/--
At the terminal cover point itself, the terminal sheet label is exactly the
stored terminal path class.

%%handwave
name:
  The terminal sheet label is the terminal path class
statement:
  For the terminal lift $\widetilde p(1)$, the path-class label of its terminal sheet equals the stored class $[p]$.
proof:
  Apply the path-class formula inside the sheet to its center. The chosen path from the center to itself is homotopic to the constant path, so its class is the identity.
-/
theorem terminalCoverPoint_pathClass_eq_terminalSheetChart_label
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathHomotopyUniversalCover.pathClass S.terminalCoverPoint =
      (PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
        (S.terminalSheetChart.center : X)) S.terminalSheetChart.fiberPoint := by
  have h :=
    S.pathClass_eq_terminalSheetChart_label_trans_pathInSet_of_mem_terminalSheet
      S.terminalCoverPoint_mem_terminalSheet
  change
    PathHomotopyUniversalCover.pathClass S.terminalCoverPoint =
      Path.Homotopic.Quotient.trans
        ((PathHomotopyUniversalCover.fiberPathClassEquiv (x₀ := x₀)
          (S.terminalSheetChart.center : X)) S.terminalSheetChart.fiberPoint)
        (Path.Homotopic.Quotient.mk
          (PathHomotopyUniversalCover.pathInSet
            S.terminalSheetChart.center S.terminalSheetChart.center)) at h
  rw [PathHomotopyUniversalCover.pathInSet_self_eq_refl_of_simplyConnected,
    Path.Homotopic.Quotient.trans_refl] at h
  simpa using h

/--
Inside the canonical terminal sheet, the path class of a lift is the terminal
path class followed by the chosen local path in the terminal sheet base.

%%handwave
name:
  Path classes in the terminal sheet extend the terminal path class
statement:
  If $y$ belongs to the terminal sheet of $p$ and $\sigma_y$ is the chosen path in its base from $p(1)$ to $\pi(y)$, then $[y]=[p]*[\sigma_y]$.
proof:
  Replace the sheet label in the local path-class formula by the path class $[p]$ of the terminal lift.
-/
theorem pathClass_eq_terminalCoverPoint_pathClass_trans_pathInSet_of_mem_terminalSheet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    PathHomotopyUniversalCover.pathClass y' =
      Path.Homotopic.Quotient.trans
        (PathHomotopyUniversalCover.pathClass S.terminalCoverPoint)
        (Path.Homotopic.Quotient.mk
          (PathHomotopyUniversalCover.pathInSet
            S.terminalSheetChart.center
            (⟨PathHomotopyUniversalCover.endpoint y',
              PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
                (by
                  simpa [terminalSheet,
                    PathHomotopyUniversalCover.LocalSheetChart.sheet] using
                    hy')⟩ : S.terminalSheetChart.base))) := by
  rw [S.terminalCoverPoint_pathClass_eq_terminalSheetChart_label]
  exact
    S.pathClass_eq_terminalSheetChart_label_trans_pathInSet_of_mem_terminalSheet hy'

/--
Equivalently, a lift in the terminal sheet is represented by the original
continued path followed by the chosen local path in the terminal sheet base.

%%handwave
name:
  Concatenating the terminal-sheet path represents a point in the sheet
statement:
  If $y$ lies in the terminal sheet of $p$ and $\sigma_y$ is the chosen base path to $\pi(y)$, then the concatenated path represents $y$: $[y]=[p*\sigma_y]$.
proof:
  The preceding formula gives $[y]=[p]*[\sigma_y]$, and multiplication of endpoint-fixed path classes is represented by path concatenation.
-/
theorem pathClass_eq_mk_path_trans_terminalSheet_pathInSet_of_mem_terminalSheet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    PathHomotopyUniversalCover.pathClass y' =
      Path.Homotopic.Quotient.mk
        (p.trans
          (PathHomotopyUniversalCover.pathInSet
            S.terminalSheetChart.center
            (⟨PathHomotopyUniversalCover.endpoint y',
              PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
                (by
                  simpa [terminalSheet,
                    PathHomotopyUniversalCover.LocalSheetChart.sheet] using
                    hy')⟩ : S.terminalSheetChart.base))) := by
  rw [S.pathClass_eq_terminalCoverPoint_pathClass_trans_pathInSet_of_mem_terminalSheet
    hy']
  change
    Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk p)
        (Path.Homotopic.Quotient.mk
          (PathHomotopyUniversalCover.pathInSet
            S.terminalSheetChart.center
            (⟨PathHomotopyUniversalCover.endpoint y',
              PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
                (by
                  simpa [terminalSheet,
                    PathHomotopyUniversalCover.LocalSheetChart.sheet] using
                    hy')⟩ : S.terminalSheetChart.base))) =
      Path.Homotopic.Quotient.mk
        (p.trans
          (PathHomotopyUniversalCover.pathInSet
            S.terminalSheetChart.center
            (⟨PathHomotopyUniversalCover.endpoint y',
              PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
                (by
                  simpa [terminalSheet,
                    PathHomotopyUniversalCover.LocalSheetChart.sheet] using
                    hy')⟩ : S.terminalSheetChart.base)))
  rw [← Path.Homotopic.Quotient.mk_trans]

/--
The previous path-class formula, using the named terminal-sheet local path.

%%handwave
name:
  Named terminal-sheet extension represents the chosen lift
statement:
  For $y$ in the terminal sheet of $p$, let $\sigma_y$ denote its canonical path inside the sheet base. Then $[y]=[p*\sigma_y]$.
proof:
  This is the concatenation formula above after identifying the named path $\sigma_y$ with the canonical path used there.
-/
theorem pathClass_eq_mk_path_trans_terminalSheetPathInSet_of_mem_terminalSheet
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    PathHomotopyUniversalCover.pathClass y' =
      Path.Homotopic.Quotient.mk
        (p.trans (S.terminalSheetPathInSet hy')) := by
  simpa [terminalSheetPathInSet] using
    S.pathClass_eq_mk_path_trans_terminalSheet_pathInSet_of_mem_terminalSheet
      hy'

omit [RiemannSurface X] in
/-- Homotopic representative paths give the same terminal cover point.

%%handwave
name:
  Homotopic paths determine the same terminal lift
statement:
  If two paths $p,q:x_0\rightsquigarrow x$ are homotopic relative to endpoints, then their terminal lifts $(x,[p])$ and $(x,[q])$ in the path-homotopy cover are equal.
proof:
  The endpoint coordinates agree, and endpoint-fixed homotopy is precisely equality of the quotient path classes.
-/
theorem terminalCoverPoint_eq_of_homotopic
    {q : Path x₀ x}
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q)
    (hpq : Path.Homotopic p q) :
    S.terminalCoverPoint = T.terminalCoverPoint := by
  exact Sigma.ext rfl
    (heq_of_eq ((Path.Homotopic.Quotient.eq).mpr hpq))

omit [RiemannSurface X] in
/--
If a path represents the stored path class of a cover point, its terminal
cover point is that cover point.

%%handwave
name:
  A representative path recovers its cover point
statement:
  Let $y$ be a point of the path-homotopy universal cover and let $p:x_0\rightsquigarrow\pi(y)$ satisfy $[p]=[y]$. Then the terminal lift $(\pi(y),[p])$ equals $y$.
proof:
  The two pairs have the same endpoint and, by assumption, the same path-class coordinate.
-/
theorem terminalCoverPoint_eq_of_mk_eq_pathClass
    {y' : PathHomotopyUniversalCover X x₀}
    {p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')}
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p')
    (hclass :
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y') :
    S.terminalCoverPoint = y' := by
  cases y' with
  | mk x q =>
      exact Sigma.ext rfl (heq_of_eq hclass)

/--
If `p'` represents a point of the terminal sheet of `p`, then `p'` is
endpoint-fixed homotopic to `p` followed by the canonical local terminal-sheet
path.

%%handwave
name:
  Representatives in a terminal sheet are homotopic to terminal-sheet extensions
statement:
  If $y$ lies in the terminal sheet of $p$ and a path $p':x_0\rightsquigarrow\pi(y)$ represents $y$, then $p'$ is endpoint-fixed homotopic to $p*\sigma_y$, where $\sigma_y$ is the canonical path in the sheet base.
proof:
  The hypothesis gives $[p']=[y]$, while the terminal-sheet path-class formula gives $[y]=[p*\sigma_y]$. Equality of quotient path classes is equivalent to endpoint-fixed homotopy.
-/
theorem homotopic_to_path_trans_terminalSheetPathInSet_of_mk_eq_pathClass
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet)
    {p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')}
    (hclass :
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y') :
    Path.Homotopic p' (p.trans (S.terminalSheetPathInSet hy')) := by
  exact
    (Path.Homotopic.Quotient.eq).mp
      (hclass.trans
        (S.pathClass_eq_mk_path_trans_terminalSheetPathInSet_of_mem_terminalSheet
          hy'))

/--
Loop-precomposition of a terminal cover point is the deck action by the
corresponding fundamental-group element.

%%handwave
name:
  Prepending a loop realizes the deck action
statement:
  Let $\gamma\in\pi_1(X,x_0)$ and let a loop $L$ represent $\gamma^{-1}$. For every path $p:x_0\rightsquigarrow x$, the terminal lift of $L*p$ is $\gamma\cdot(x,[p])$.
proof:
  By definition, the deck action sends $(x,[p])$ to $(x,[L]*[p])$. The quotient class of a concatenated path is the product of the quotient classes, so this pair is exactly the terminal lift of $L*p$.
-/
theorem terminalCoverPoint_loopTrans_eq_deckAction
    (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
        (loop.trans p))
    (hloop :
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹) :
    T.terminalCoverPoint =
      (canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint := by
  dsimp [terminalCoverPoint, canonicalContinuationCover,
    SimplyConnectedCover.deckAction,
    PathHomotopyUniversalCover.deckHomeomorphism_apply,
    PathHomotopyUniversalCover.deckAction,
    PathHomotopyUniversalCover.endpoint,
    PathHomotopyUniversalCover.pathClass]
  change
    (⟨x, Path.Homotopic.Quotient.mk (loop.trans p)⟩ :
        PathHomotopyUniversalCover X x₀) =
      ⟨x,
        Path.Homotopic.Quotient.trans
          (FundamentalGroup.toPath γ⁻¹)
          (Path.Homotopic.Quotient.mk p)⟩
  rw [← hloop, ← Path.Homotopic.Quotient.mk_trans]

end PathLocalTransitionModelBasedWeakHandoffSkeleton

end HyperbolicMetric

end

end JJMath
