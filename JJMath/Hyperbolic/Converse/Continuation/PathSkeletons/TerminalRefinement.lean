import JJMath.Hyperbolic.Converse.Continuation.PathSkeletons.BasedCore

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

variable
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {q r : Path x₀ x}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q}
    {U : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels r}

omit [RiemannSurface X] in
/-- Reflexivity of terminal branch data equality.

%%handwave
name:
  Reflexivity of terminal branch agreement
statement:
  Every continuation skeleton has the same terminal chart center and terminal accumulated representative as itself.
proof:
  Both required equalities are reflexive.
-/
theorem refl
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    TerminalBranchDataEq S S where
  terminalCenter_eq := rfl
  terminalMobius_eq := rfl

omit [RiemannSurface X] in
/-- Symmetry of terminal branch data equality.

%%handwave
name:
  Symmetry of terminal branch agreement
statement:
  If skeleton $S$ has the same terminal center and terminal representative as $T$, then $T$ has the same terminal data as $S$.
proof:
  Reverse each of the two equalities.
-/
theorem symm (H : TerminalBranchDataEq S T) :
    TerminalBranchDataEq T S where
  terminalCenter_eq := H.terminalCenter_eq.symm
  terminalMobius_eq := H.terminalMobius_eq.symm

omit [RiemannSurface X] in
/-- Transitivity of terminal branch data equality.

%%handwave
name:
  Transitivity of terminal branch agreement
statement:
  If $S$ and $T$ have equal terminal branch data and so do $T$ and $U$, then $S$ and $U$ have equal terminal branch data.
proof:
  Compose the equalities of terminal centers and of terminal representatives separately.
-/
theorem trans (HST : TerminalBranchDataEq S T) (HTU : TerminalBranchDataEq T U) :
    TerminalBranchDataEq S U where
  terminalCenter_eq := HST.terminalCenter_eq.trans HTU.terminalCenter_eq
  terminalMobius_eq := HST.terminalMobius_eq.trans HTU.terminalMobius_eq

omit [RiemannSurface X] in
/-- Equal terminal branch data give equal terminal formulae everywhere.

%%handwave
name:
  Equal terminal branch data determine the same formula
statement:
  If two skeletons have the same terminal center $c$ and terminal representative $M$, then their terminal formulas agree at every $z\in X$.
proof:
  Both formulas are $M\cdot\phi_c(z)$ after substituting the two equalities.
-/
theorem terminalFormulaAt_eq (H : TerminalBranchDataEq S T) (z : X) :
    S.terminalFormulaAt z = T.terminalFormulaAt z := by
  change
    realMobiusRepresentativeAction S.terminalMobius
        ((localModels.chartAt S.terminalCenter).toUpperHalfPlane z) =
      realMobiusRepresentativeAction T.terminalMobius
        ((localModels.chartAt T.terminalCenter).toUpperHalfPlane z)
  rw [H.terminalMobius_eq, H.terminalCenter_eq]

omit [RiemannSurface X] in
/-- Equal terminal branch data give equal terminal values.

%%handwave
name:
  Equal terminal branch data determine the same value
statement:
  Skeletons ending at the same point with equal terminal centers and terminal representatives have equal terminal values.
proof:
  Evaluate their equal terminal formulas at the common endpoint.
-/
theorem terminalValue_eq (H : TerminalBranchDataEq S T) :
    S.terminalValue = T.terminalValue := by
  simpa using H.terminalFormulaAt_eq x

omit [RiemannSurface X] in
/-- Endpoint casts preserve terminal branch-data equality.

%%handwave
name:
  Recasting endpoints preserves terminal branch agreement
statement:
  If two skeletons have equal terminal branch data, replacing their common source and target by equal points preserves that agreement.
proof:
  Endpoint recasting leaves each terminal center and terminal representative unchanged, so the original equalities still apply.
-/
theorem castEndpoints
    (H : TerminalBranchDataEq S T)
    {x₀' x' : X} (hx₀ : x₀' = x₀) (hx : x' = x) :
    TerminalBranchDataEq (S.castEndpoints hx₀ hx) (T.castEndpoints hx₀ hx) where
  terminalCenter_eq := by
    simp [H.terminalCenter_eq]
  terminalMobius_eq := by
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.castEndpoints_terminalMobius,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.castEndpoints_terminalMobius,
      H.terminalMobius_eq]

omit [RiemannSurface X] in
/-- Path casts preserve terminal branch-data equality.

%%handwave
name:
  Transport across equal paths preserves terminal branch agreement
statement:
  If two skeletons have equal terminal branch data, transporting each across an equality of its underlying path preserves that agreement.
proof:
  Path transport leaves terminal centers and terminal representatives unchanged; substitute these invariance equalities.
-/
theorem castPath
    (H : TerminalBranchDataEq S T)
    {qS qT : Path x₀ x} (hpS : p = qS) (hpT : q = qT) :
    TerminalBranchDataEq (S.castPath hpS) (T.castPath hpT) where
  terminalCenter_eq := by
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.castPath_terminalCenter,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.castPath_terminalCenter,
      H.terminalCenter_eq]
  terminalMobius_eq := by
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.castPath_terminalMobius,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.castPath_terminalMobius,
      H.terminalMobius_eq]

end TerminalBranchDataEq

omit [RiemannSurface X] in
/--
Append a supplied path lying in the terminal chart to a based weak handoff
skeleton.

This is the exact-path variant of `terminalExtensionSkeleton`: the old
subdivision is compressed into the first half, and the new final segment is
the given local path rather than the canonical path chosen inside a sheet.
-/
noncomputable def terminalExtensionAlongSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
      (p.trans ρ) where
  length := S.length + 1
  length_pos := Nat.succ_pos S.length
  parameterAt := S.terminalExtensionParameterAt
  parameterAt_zero := S.terminalExtensionParameterAt_zero
  parameterAt_last := S.terminalExtensionParameterAt_last
  parameterAt_mono := S.terminalExtensionParameterAt_mono
  centerAt := S.terminalExtensionCenterAt
  sample_mem_model_domain := by
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
        S.terminalExtensionCenterAt_last] using hρ 1
  path_segment_mem_model_domain := by
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
      rw [path_trans_apply_of_le_half p ρ t ht_half, hcenter]
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
      rw [path_trans_apply_of_half_le p ρ t ht_half]
      rw [S.terminalExtensionCenterAt_final_left]
      exact hρ (unitInterval.doubleSubOneOfHalfLe t ht_half)
  terminal_endpoint_mem_domain := by
    simpa [S.terminalExtensionCenterAt_last] using hρ 1
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
          (p.trans ρ) (S.terminalExtensionParameterAt k.succ) =
            p (S.parameterAt k₀.succ) := by
        rw [hright, S.terminalExtensionParameterAt_castSucc]
        exact path_trans_firstHalf_apply p ρ (S.parameterAt k₀.succ)
      exact localRealMobiusTransitionData_congr hU hV hpath
        (S.transitionAt k₀)
    · have hk_last : k = Fin.last S.length := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
          (Nat.le_of_not_gt hk)
      subst k
      have hx :
          (p.trans ρ)
              (S.terminalExtensionParameterAt (Fin.last (S.length + 1))) ∈
            (localModels.chartAt S.terminalCenter).domain := by
        simpa [S.terminalExtensionParameterAt_last] using hρ 1
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
          (p.trans ρ)
              (S.terminalExtensionParameterAt
                ((Fin.last S.length : Fin (S.length + 1)).succ)) =
            (p.trans ρ)
              (S.terminalExtensionParameterAt (Fin.last (S.length + 1))) := by
        rw [fin_last_succ_eq_last]
      exact localRealMobiusTransitionData_congr hU hV hpoint
        (localRealMobiusTransitionData_self
          (localModels.chartAt S.terminalCenter) hx)
  initialTransition := by
    exact localRealMobiusTransitionData_congr rfl
      (by simp [S.terminalExtensionCenterAt_zero]) rfl S.initialTransition

omit [RiemannSurface X] in
/--
%%handwave
name:
  Exact extension inside the terminal chart preserves its center
statement:
  If a path $\rho:x\rightsquigarrow y$ remains in the terminal chart of a skeleton $S$, then the skeleton obtained by appending $\rho$ has the same terminal chart center as $S$.
proof:
  The new final segment is assigned the old terminal center at both endpoints.
-/
@[simp]
theorem terminalExtensionAlongSkeleton_terminalCenter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain) :
    (S.terminalExtensionAlongSkeleton ρ hρ).terminalCenter =
      S.terminalCenter := by
  simp [terminalExtensionAlongSkeleton, terminalCenter]

omit [RiemannSurface X] in
/--
Along the compressed old part of an exact terminal extension, the accumulated
Mobius product agrees with the original skeleton.

%%handwave
name:
  Exact terminal extension preserves accumulated products on the old prefix
statement:
  If $S'$ appends a path inside the terminal chart of $S$, then $M_j(S')=M_j(S)$ for every $j$ up to the original length.
proof:
  Induct on $j$. All old handoff representatives are transported unchanged into the compressed first half, so the same recurrence applies.
-/
theorem terminalExtensionAlongSkeleton_accumulatedMobiusNat_eq_of_le
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain) :
    ∀ n : ℕ, n ≤ S.length →
      (S.terminalExtensionAlongSkeleton ρ hρ).accumulatedMobiusNat n =
        S.accumulatedMobiusNat n := by
  intro n hn
  induction n with
  | zero =>
      simp [terminalExtensionAlongSkeleton, accumulatedMobiusNat]
  | succ n ih =>
      have hnlt : n < S.length := Nat.succ_le_iff.mp hn
      have hnle : n ≤ S.length := Nat.le_of_lt hnlt
      let T := S.terminalExtensionAlongSkeleton ρ hρ
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
        simp [T, terminalExtensionAlongSkeleton, hnlt]
      rw [hTstep, ih hnle, htrans, hSstep]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Exact extension inside the terminal chart preserves the terminal representative
statement:
  Appending any path that remains in the terminal chart leaves the terminal accumulated representative unchanged.
proof:
  The product through the old final vertex is unchanged, and the single new handoff is the identity self-transition of the terminal chart.
-/
@[simp]
theorem terminalExtensionAlongSkeleton_terminalMobius_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain) :
    (S.terminalExtensionAlongSkeleton ρ hρ).terminalMobius =
      S.terminalMobius := by
  let T := S.terminalExtensionAlongSkeleton ρ hρ
  have hprefix :
      T.accumulatedMobiusNat S.length = S.accumulatedMobiusNat S.length :=
    S.terminalExtensionAlongSkeleton_accumulatedMobiusNat_eq_of_le
      ρ hρ S.length le_rfl
  have hstep :
      T.accumulatedMobiusNat (S.length + 1) =
        T.accumulatedMobiusNat S.length *
          (T.transitionAt (Fin.last S.length)).representative⁻¹ := by
    exact T.accumulatedMobiusNat_succ_of_lt (Nat.lt_succ_self S.length)
  have htrans :
      (T.transitionAt (Fin.last S.length)).representative = 1 := by
    simp [T, terminalExtensionAlongSkeleton, localRealMobiusTransitionData_self]
  change T.accumulatedMobiusNat (S.length + 1) =
    S.accumulatedMobiusNat S.length
  rw [hstep, htrans, hprefix]
  simp

omit [RiemannSurface X] in
/--
Exact terminal extension preserves the terminal branch formula on the
terminal chart.

%%handwave
name:
  Exact extension inside the terminal chart preserves the terminal formula
statement:
  Appending a path inside the terminal chart leaves the terminal branch formula unchanged at every $z\in X$.
proof:
  The extension preserves both the terminal chart center and the terminal accumulated representative; substitute these equalities in the formula.
-/
theorem terminalExtensionAlongSkeleton_terminalFormulaAt_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain)
    (z : X) :
    (S.terminalExtensionAlongSkeleton ρ hρ).terminalFormulaAt z =
      S.terminalFormulaAt z := by
  change
    realMobiusRepresentativeAction
        (S.terminalExtensionAlongSkeleton ρ hρ).terminalMobius
        ((localModels.chartAt
          (S.terminalExtensionAlongSkeleton ρ hρ).terminalCenter).toUpperHalfPlane z) =
      realMobiusRepresentativeAction S.terminalMobius
        ((localModels.chartAt S.terminalCenter).toUpperHalfPlane z)
  rw [S.terminalExtensionAlongSkeleton_terminalMobius_eq ρ hρ,
    S.terminalExtensionAlongSkeleton_terminalCenter ρ hρ]

omit [RiemannSurface X] in
/--
Exact terminal extension along a common local suffix preserves equality of
terminal branch data.

%%handwave
name:
  Common exact terminal extension preserves terminal branch agreement
statement:
  If two skeletons have equal terminal branch data and a common suffix path lies in both terminal charts, then extending both skeletons along that suffix yields skeletons with equal terminal centers and terminal representatives.
proof:
  Each extension preserves its original terminal center and representative, after which the original terminal-data equalities apply.
-/
theorem TerminalBranchDataEq.terminalExtensionAlong
    {q : Path x₀ x}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q}
    (H : TerminalBranchDataEq S T)
    {y : X} (ρ : Path x y)
    (hρS : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain)
    (hρT : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt T.terminalCenter).domain) :
    TerminalBranchDataEq
      (S.terminalExtensionAlongSkeleton ρ hρS)
      (T.terminalExtensionAlongSkeleton ρ hρT) where
  terminalCenter_eq := by
    rw [S.terminalExtensionAlongSkeleton_terminalCenter ρ hρS,
      T.terminalExtensionAlongSkeleton_terminalCenter ρ hρT,
      H.terminalCenter_eq]
  terminalMobius_eq := by
    rw [S.terminalExtensionAlongSkeleton_terminalMobius_eq ρ hρS,
      T.terminalExtensionAlongSkeleton_terminalMobius_eq ρ hρT,
      H.terminalMobius_eq]

omit [RiemannSurface X] in
/--
If two terminal branch formulae agree at the endpoint of a shared local path,
then exact extension along that path preserves the equality of terminal
values.

%%handwave
name:
  Endpoint formula agreement gives equal values after a common local extension
statement:
  Let a path $\rho:x\rightsquigarrow y$ lie in the terminal charts of skeletons $S$ and $T$. If their original terminal formulas agree at $y$, then the terminal values of the two extensions along $\rho$ are equal.
proof:
  The terminal value of each extension is its terminal formula at $y$, and extension preserves that formula. Insert the assumed equality between the two original formula values.
-/
theorem terminalExtensionAlongSkeleton_terminalValue_eq_of_terminalFormulaAt_eq
    {q : Path x₀ x}
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q)
    {y : X} (ρ : Path x y)
    (hρS : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain)
    (hρT : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt T.terminalCenter).domain)
    (hFormula : S.terminalFormulaAt y = T.terminalFormulaAt y) :
    (S.terminalExtensionAlongSkeleton ρ hρS).terminalValue =
      (T.terminalExtensionAlongSkeleton ρ hρT).terminalValue := by
  calc
    (S.terminalExtensionAlongSkeleton ρ hρS).terminalValue =
        (S.terminalExtensionAlongSkeleton ρ hρS).terminalFormulaAt y := by
          exact
            ((S.terminalExtensionAlongSkeleton ρ hρS).terminalFormulaAt_endpoint).symm
    _ = S.terminalFormulaAt y := by
          exact S.terminalExtensionAlongSkeleton_terminalFormulaAt_eq ρ hρS y
    _ = T.terminalFormulaAt y := hFormula
    _ = (T.terminalExtensionAlongSkeleton ρ hρT).terminalFormulaAt y := by
          exact (T.terminalExtensionAlongSkeleton_terminalFormulaAt_eq ρ hρT y).symm
    _ = (T.terminalExtensionAlongSkeleton ρ hρT).terminalValue := by
          exact
            (T.terminalExtensionAlongSkeleton ρ hρT).terminalFormulaAt_endpoint

omit [RiemannSurface X] in
/--
Two exact terminal extensions of the same skeleton to the same endpoint have
the same terminal value whenever both extension paths stay in the terminal
chart.

%%handwave
name:
  Local extensions to the same endpoint have equal terminal values
statement:
  If two paths $\rho,\sigma:x\rightsquigarrow y$ both stay in the terminal chart of a skeleton $S$, then extending $S$ along either path gives the same terminal value.
proof:
  Both extended terminal formulas equal the original formula, so both terminal values equal its value at the common endpoint $y$.
-/
theorem terminalExtensionAlongSkeleton_terminalValue_eq_of_same_endpoint
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y : X} (ρ σ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain)
    (hσ : ∀ t : unitInterval, σ t ∈
      (localModels.chartAt S.terminalCenter).domain) :
    (S.terminalExtensionAlongSkeleton ρ hρ).terminalValue =
      (S.terminalExtensionAlongSkeleton σ hσ).terminalValue := by
  calc
    (S.terminalExtensionAlongSkeleton ρ hρ).terminalValue =
        (S.terminalExtensionAlongSkeleton ρ hρ).terminalFormulaAt y := by
          exact
            ((S.terminalExtensionAlongSkeleton ρ hρ).terminalFormulaAt_endpoint).symm
    _ = S.terminalFormulaAt y := by
          exact S.terminalExtensionAlongSkeleton_terminalFormulaAt_eq ρ hρ y
    _ = (S.terminalExtensionAlongSkeleton σ hσ).terminalFormulaAt y := by
          exact (S.terminalExtensionAlongSkeleton_terminalFormulaAt_eq σ hσ y).symm
    _ = (S.terminalExtensionAlongSkeleton σ hσ).terminalValue := by
          exact
            (S.terminalExtensionAlongSkeleton σ hσ).terminalFormulaAt_endpoint

omit [RiemannSurface X] in
/--
Two exact terminal extensions of the same skeleton to the same endpoint have
the same terminal branch formula everywhere, provided both extension paths
stay in the terminal chart.

%%handwave
name:
  Local extensions to the same endpoint have identical terminal formulas
statement:
  If $\rho$ and $\sigma$ are two paths from $x$ to $y$ lying in the terminal chart of $S$, then the two extended skeletons have equal terminal formulas at every $z\in X$.
proof:
  The terminal formula after either extension is the original terminal formula of $S$.
-/
theorem terminalExtensionAlongSkeleton_terminalFormulaAt_eq_of_same_endpoint
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y : X} (ρ σ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain)
    (hσ : ∀ t : unitInterval, σ t ∈
      (localModels.chartAt S.terminalCenter).domain)
    (z : X) :
    (S.terminalExtensionAlongSkeleton ρ hρ).terminalFormulaAt z =
      (S.terminalExtensionAlongSkeleton σ hσ).terminalFormulaAt z := by
  calc
    (S.terminalExtensionAlongSkeleton ρ hρ).terminalFormulaAt z =
        S.terminalFormulaAt z := by
          exact S.terminalExtensionAlongSkeleton_terminalFormulaAt_eq ρ hρ z
    _ = (S.terminalExtensionAlongSkeleton σ hσ).terminalFormulaAt z := by
          exact (S.terminalExtensionAlongSkeleton_terminalFormulaAt_eq σ hσ z).symm

omit [RiemannSurface X] in
/--
Two exact terminal extensions of the same skeleton to the same endpoint have
the same terminal branch data.

%%handwave
name:
  Local extensions to the same endpoint have equal terminal branch data
statement:
  If $\rho,\sigma:x\rightsquigarrow y$ both lie in the terminal chart of $S$, then extending along $\rho$ and along $\sigma$ produces the same terminal center and terminal representative.
proof:
  Each extension preserves the terminal center and terminal representative of $S$, so the two results agree.
-/
theorem terminalExtensionAlongSkeleton_terminalBranchDataEq_of_same_endpoint
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y : X} (ρ σ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt S.terminalCenter).domain)
    (hσ : ∀ t : unitInterval, σ t ∈
      (localModels.chartAt S.terminalCenter).domain) :
    TerminalBranchDataEq
      (S.terminalExtensionAlongSkeleton ρ hρ)
      (S.terminalExtensionAlongSkeleton σ hσ) where
  terminalCenter_eq := by
    rw [S.terminalExtensionAlongSkeleton_terminalCenter ρ hρ,
      S.terminalExtensionAlongSkeleton_terminalCenter σ hσ]
  terminalMobius_eq := by
    rw [S.terminalExtensionAlongSkeleton_terminalMobius_eq ρ hρ,
      S.terminalExtensionAlongSkeleton_terminalMobius_eq σ hσ]

omit [RiemannSurface X] in
/--
Subdivision parameters for the terminal-stutter skeleton: the old subdivision
is kept and a duplicate terminal vertex is appended at `1`.
-/
noncomputable def terminalStutterParameterAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    Fin (S.length + 2) → unitInterval :=
  fun i =>
    if hi : (i : ℕ) < S.length + 1 then
      S.parameterAt ⟨i, hi⟩
    else
      1

omit [RiemannSurface X] in
/--
Centers for the terminal-stutter skeleton: the old centers are kept and the
duplicate terminal vertex uses the old terminal center.
-/
noncomputable def terminalStutterCenterAt
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
name: Old parameters survive terminal stuttering
statement: Every original vertex $i$ keeps its parameter $t_i$ after a duplicate terminal vertex is appended.
proof: The old-index branch of the stutter parameter function returns the original parameter.
-/
@[simp]
theorem terminalStutterParameterAt_castSucc
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (i : Fin (S.length + 1)) :
    S.terminalStutterParameterAt i.castSucc = S.parameterAt i := by
  change
    (if hi : (i : ℕ) < S.length + 1 then S.parameterAt ⟨i, hi⟩ else 1) =
      S.parameterAt i
  rw [dif_pos i.isLt]

omit [RiemannSurface X] in
/--
%%handwave
name: Old centers survive terminal stuttering
statement: Every original vertex $i$ keeps its chart center $c_i$ after a duplicate terminal vertex is appended.
proof: The old-index branch of the stutter center function returns the original center.
-/
@[simp]
theorem terminalStutterCenterAt_castSucc
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (i : Fin (S.length + 1)) :
    S.terminalStutterCenterAt i.castSucc = S.centerAt i := by
  change
    (if hi : (i : ℕ) < S.length + 1 then S.centerAt ⟨i, hi⟩ else
      S.terminalCenter) = S.centerAt i
  rw [dif_pos i.isLt]

omit [RiemannSurface X] in
/--
%%handwave
name: The stuttered last parameter is one
statement: The new last vertex appended by terminal stuttering has parameter $1$.
proof: The last index lies beyond the old vertex range, where the parameter is defined to be $1$.
-/
@[simp]
theorem terminalStutterParameterAt_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterParameterAt (Fin.last (S.length + 1)) = 1 := by
  simp [terminalStutterParameterAt]

omit [RiemannSurface X] in
/--
%%handwave
name: The stuttered last center is the terminal center
statement: The duplicate last vertex appended by terminal stuttering uses the original terminal chart center.
proof: Beyond the old vertex range, the center function is defined to be the old terminal center.
-/
@[simp]
theorem terminalStutterCenterAt_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterCenterAt (Fin.last (S.length + 1)) =
      S.terminalCenter := by
  simp [terminalStutterCenterAt]

omit [RiemannSurface X] in
/--
%%handwave
name: Terminal stuttering preserves the initial parameter
statement: The first parameter remains $0$ after appending a duplicate terminal vertex.
proof: The original first vertex is retained and has parameter $t_0=0$.
-/
@[simp]
theorem terminalStutterParameterAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterParameterAt 0 = 0 := by
  simp [terminalStutterParameterAt, S.parameterAt_zero]

omit [RiemannSurface X] in
/--
%%handwave
name: Terminal stuttering preserves the initial center
statement: The first chart center is unchanged after appending a duplicate terminal vertex.
proof: The original first vertex is retained with its center.
-/
@[simp]
theorem terminalStutterCenterAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterCenterAt 0 = S.centerAt 0 := by
  simp [terminalStutterCenterAt]

omit [RiemannSurface X] in
/--
%%handwave
name: Left parameters of old segments survive terminal stuttering
statement: The left endpoint of every old segment $k$ retains parameter $t_k$ after terminal stuttering.
proof: It is an included old vertex, so the old-parameter formula applies.
-/
@[simp]
theorem terminalStutterParameterAt_old_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    S.terminalStutterParameterAt (k.castSucc.castSucc) =
      S.parameterAt k.castSucc := by
  simp

omit [RiemannSurface X] in
/--
%%handwave
name: Left centers of old segments survive terminal stuttering
statement: The left endpoint of every old segment $k$ retains center $c_k$ after terminal stuttering.
proof: It is an included old vertex, so the old-center formula applies.
-/
@[simp]
theorem terminalStutterCenterAt_old_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    S.terminalStutterCenterAt (k.castSucc.castSucc) =
      S.centerAt k.castSucc := by
  simp

omit [RiemannSurface X] in
/--
%%handwave
name: Right parameters of old segments survive terminal stuttering
statement: The right endpoint of every old segment $k$ retains parameter $t_{k+1}$ after terminal stuttering.
proof: Successor commutes with inclusion of the old finite index, after which the old-parameter formula applies.
-/
@[simp]
theorem terminalStutterParameterAt_old_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    S.terminalStutterParameterAt ((k.castSucc : Fin (S.length + 1)).succ) =
      S.parameterAt k.succ := by
  rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
  simpa using S.terminalStutterParameterAt_castSucc k.succ

omit [RiemannSurface X] in
/--
%%handwave
name: Right centers of old segments survive terminal stuttering
statement: The right endpoint of every old segment $k$ retains center $c_{k+1}$ after terminal stuttering.
proof: Commute successor with inclusion and apply preservation of old centers.
-/
@[simp]
theorem terminalStutterCenterAt_old_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    S.terminalStutterCenterAt ((k.castSucc : Fin (S.length + 1)).succ) =
      S.centerAt k.succ := by
  rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
  simpa using S.terminalStutterCenterAt_castSucc k.succ

omit [RiemannSurface X] in
/--
%%handwave
name: The added stutter segment begins at one
statement: The left endpoint parameter of the added zero-length terminal segment is $1$.
proof: It is the original final parameter $t_\ell=1$.
-/
@[simp]
theorem terminalStutterParameterAt_final_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterParameterAt
        ((Fin.last S.length : Fin (S.length + 1)).castSucc) = 1 := by
  simp [S.parameterAt_last]

omit [RiemannSurface X] in
/--
%%handwave
name: The added stutter segment begins in the terminal chart
statement: The left endpoint of the added terminal segment uses the original terminal center.
proof: It is the original last vertex.
-/
@[simp]
theorem terminalStutterCenterAt_final_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterCenterAt
        ((Fin.last S.length : Fin (S.length + 1)).castSucc) =
      S.terminalCenter := by
  simp [terminalCenter]

omit [RiemannSurface X] in
/--
%%handwave
name: The added stutter segment ends at one
statement: The right endpoint parameter of the added zero-length terminal segment is $1$.
proof: This endpoint is the new last vertex, whose parameter is $1$.
-/
@[simp]
theorem terminalStutterParameterAt_final_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterParameterAt
        ((Fin.last S.length : Fin (S.length + 1)).succ) = 1 := by
  rw [fin_last_succ_eq_last]
  exact S.terminalStutterParameterAt_last

omit [RiemannSurface X] in
/--
%%handwave
name: The added stutter segment ends in the terminal chart
statement: The right endpoint of the added terminal segment uses the original terminal center.
proof: It is the new last vertex, whose center is defined to be the old terminal center.
-/
@[simp]
theorem terminalStutterCenterAt_final_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    S.terminalStutterCenterAt
        ((Fin.last S.length : Fin (S.length + 1)).succ) =
      S.terminalCenter := by
  rw [fin_last_succ_eq_last]
  exact S.terminalStutterCenterAt_last

omit [RiemannSurface X] in
/--
Centers for a terminal chart-change skeleton: the old centers are kept and the
new duplicate terminal vertex uses the chosen terminal chart center `c`.
-/
noncomputable def terminalChartChangeCenterAt
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) :
    Fin (S.length + 2) → X :=
  fun i =>
    if hi : (i : ℕ) < S.length + 1 then
      S.centerAt ⟨i, hi⟩
    else
      c

omit [RiemannSurface X] in
/--
%%handwave
name: Old centers survive a terminal chart change
statement: Every original vertex $i$ keeps its chart center $c_i$ when a duplicate terminal vertex with a new chart is appended.
proof: The old-index branch of the new center function returns $c_i$.
-/
@[simp]
theorem terminalChartChangeCenterAt_castSucc
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (i : Fin (S.length + 1)) :
    S.terminalChartChangeCenterAt c i.castSucc = S.centerAt i := by
  change
    (if hi : (i : ℕ) < S.length + 1 then S.centerAt ⟨i, hi⟩ else c) =
      S.centerAt i
  rw [dif_pos i.isLt]

omit [RiemannSurface X] in
/--
%%handwave
name: A terminal chart change ends at the chosen center
statement: The new last vertex of a terminal chart change has the prescribed center $c$.
proof: The last index lies beyond the old range, where the center function is defined to be $c$.
-/
@[simp]
theorem terminalChartChangeCenterAt_last
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) :
    S.terminalChartChangeCenterAt c (Fin.last (S.length + 1)) = c := by
  simp [terminalChartChangeCenterAt]

omit [RiemannSurface X] in
/--
%%handwave
name: A terminal chart change preserves the initial center
statement: The first chart center is unchanged by appending a terminal chart change.
proof: Vertex $0$ is an old vertex and retains its center.
-/
@[simp]
theorem terminalChartChangeCenterAt_zero
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) :
    S.terminalChartChangeCenterAt c 0 = S.centerAt 0 := by
  simp [terminalChartChangeCenterAt]

omit [RiemannSurface X] in
/--
%%handwave
name: Old left centers survive a terminal chart change
statement: The left endpoint of every original segment $k$ keeps center $c_k$ after terminal chart change.
proof: It is an included old vertex.
-/
@[simp]
theorem terminalChartChangeCenterAt_old_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (k : Fin S.length) :
    S.terminalChartChangeCenterAt c (k.castSucc.castSucc) =
      S.centerAt k.castSucc := by
  simp

omit [RiemannSurface X] in
/--
%%handwave
name: Old right centers survive a terminal chart change
statement: The right endpoint of every original segment $k$ keeps center $c_{k+1}$ after terminal chart change.
proof: Commute successor with inclusion and apply preservation of old centers.
-/
@[simp]
theorem terminalChartChangeCenterAt_old_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (k : Fin S.length) :
    S.terminalChartChangeCenterAt c
        ((k.castSucc : Fin (S.length + 1)).succ) =
      S.centerAt k.succ := by
  rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
  simpa using S.terminalChartChangeCenterAt_castSucc c k.succ

omit [RiemannSurface X] in
/--
%%handwave
name: A terminal chart change begins at the old terminal center
statement: The left endpoint of the added zero-length terminal segment uses the original terminal chart center.
proof: It is the original last vertex.
-/
@[simp]
theorem terminalChartChangeCenterAt_final_left
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) :
    S.terminalChartChangeCenterAt c
        ((Fin.last S.length : Fin (S.length + 1)).castSucc) =
      S.terminalCenter := by
  simp [terminalCenter]

omit [RiemannSurface X] in
/--
%%handwave
name: A terminal chart change ends at the new center
statement: The right endpoint of the added zero-length terminal segment uses the prescribed new center $c$.
proof: It is the new last vertex.
-/
@[simp]
theorem terminalChartChangeCenterAt_final_right
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) :
    S.terminalChartChangeCenterAt c
        ((Fin.last S.length : Fin (S.length + 1)).succ) =
      c := by
  rw [fin_last_succ_eq_last]
  exact S.terminalChartChangeCenterAt_last c

omit [RiemannSurface X] in
/-- The terminal-stutter subdivision parameters are weakly increasing.

%%handwave
name: Monotonicity of terminal-stutter parameters
statement: Appending one more copy of the final parameter gives a weakly increasing sequence $t_0\le\cdots\le t_\ell=1\le1$.
proof: Old adjacent pairs use the original monotonicity; the only new comparison is $1\le1$.
-/
theorem terminalStutterParameterAt_mono
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ k : Fin (S.length + 1),
      (S.terminalStutterParameterAt k.castSucc : ℝ) ≤
        (S.terminalStutterParameterAt k.succ : ℝ) := by
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
    rw [hleft, hright, S.terminalStutterParameterAt_castSucc k₀.castSucc,
      S.terminalStutterParameterAt_castSucc k₀.succ]
    exact S.parameterAt_mono k₀
  · have hk_last : k = Fin.last S.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    rw [S.terminalStutterParameterAt_final_left,
      S.terminalStutterParameterAt_final_right]

omit [RiemannSurface X] in
/--
Every sampled vertex of the terminal-stutter subdivision lies in its selected
model domain.

%%handwave
name: Vertex chart membership after terminal stuttering
statement: Every old sampled point remains in its old chart domain, and the duplicated endpoint remains in the terminal chart domain.
proof: Use the original sampling condition at old vertices and the terminal endpoint condition at the new last vertex.
-/
theorem terminalStutter_sample_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ i : Fin (S.length + 2),
      p (S.terminalStutterParameterAt i) ∈
        (localModels.chartAt (S.terminalStutterCenterAt i)).domain := by
  intro i
  by_cases hi : (i : ℕ) < S.length + 1
  · let j : Fin (S.length + 1) := ⟨i, hi⟩
    have hij : i = j.castSucc := by
      ext
      rfl
    rw [hij, S.terminalStutterParameterAt_castSucc j,
      S.terminalStutterCenterAt_castSucc j]
    exact S.sample_mem_model_domain j
  · have hi_last : i = Fin.last (S.length + 1) := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ i.isLt)
        (Nat.le_of_not_gt hi)
    rw [hi_last]
    simpa [S.terminalStutterParameterAt_last, S.terminalStutterCenterAt_last,
      p.target] using S.terminal_endpoint_mem_domain

omit [RiemannSurface X] in
/--
Every subinterval of the terminal-stutter subdivision stays in the selected
model domain attached to its left vertex.

%%handwave
name: Segment chart containment after terminal stuttering
statement: Every old segment retains its chart-domain containment, while the added interval $[1,1]$ consists only of the endpoint $x$ in the terminal chart.
proof: Old intervals reduce to the original ones. On the final interval the inequalities force $t=1$, so apply the terminal endpoint condition.
-/
theorem terminalStutter_path_segment_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ k : Fin (S.length + 1), ∀ t : unitInterval,
      (S.terminalStutterParameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (S.terminalStutterParameterAt k.succ : ℝ) →
      p t ∈
        (localModels.chartAt (S.terminalStutterCenterAt k.castSucc)).domain := by
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
    rw [hleft_index, S.terminalStutterParameterAt_castSucc k₀.castSucc]
      at ht_left
    rw [hright_index, S.terminalStutterParameterAt_castSucc k₀.succ]
      at ht_right
    have hcenter :
        S.terminalStutterCenterAt k.castSucc = S.centerAt k₀.castSucc := by
      rw [hleft_index]
      simp
    rw [hcenter]
    exact S.path_segment_mem_model_domain k₀ t ht_left ht_right
  · have hk_last : k = Fin.last S.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    rw [S.terminalStutterParameterAt_final_left] at ht_left
    have ht_eq_one : t = 1 := by
      ext
      exact le_antisymm (unitInterval.le_one t) ht_left
    rw [ht_eq_one, p.target, S.terminalStutterCenterAt_final_left]
    exact S.terminal_endpoint_mem_domain

omit [RiemannSurface X] in
/-- The endpoint of the terminal-stutter path lies in the terminal selected model.

%%handwave
name: Endpoint membership after terminal stuttering
statement: The endpoint $x$ belongs to the chart assigned to the new last vertex of a terminal stutter.
proof: That chart is the original terminal chart, for which endpoint membership is already known.
-/
theorem terminalStutter_terminal_endpoint_mem_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    x ∈
      (localModels.chartAt
        (S.terminalStutterCenterAt (Fin.last (S.length + 1)))).domain := by
  simpa [S.terminalStutterCenterAt_last] using S.terminal_endpoint_mem_domain

omit [RiemannSurface X] in
/--
Every sampled vertex of a terminal chart-change subdivision lies in its
selected model domain.

%%handwave
name: Vertex chart membership after terminal chart change
statement: If $x$ lies in the chosen new chart centered at $c$, then after appending a terminal chart-change vertex every sampled point lies in its assigned chart domain.
proof: Old vertices use the original sampling condition; the new last vertex is $x$ and uses the assumed new-chart membership.
-/
theorem terminalChartChange_sample_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain) :
    ∀ i : Fin (S.length + 2),
      p (S.terminalStutterParameterAt i) ∈
        (localModels.chartAt (S.terminalChartChangeCenterAt c i)).domain := by
  intro i
  by_cases hi : (i : ℕ) < S.length + 1
  · let j : Fin (S.length + 1) := ⟨i, hi⟩
    have hij : i = j.castSucc := by
      ext
      rfl
    rw [hij, S.terminalStutterParameterAt_castSucc,
      S.terminalChartChangeCenterAt_castSucc]
    exact S.sample_mem_model_domain j
  · have hi_last : i = Fin.last (S.length + 1) := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ i.isLt)
        (Nat.le_of_not_gt hi)
    rw [hi_last]
    simpa [S.terminalStutterParameterAt_last, S.terminalChartChangeCenterAt_last,
      p.target] using hc

omit [RiemannSurface X] in
/--
Every subinterval of a terminal chart-change subdivision stays in the selected
model domain attached to its left vertex.

%%handwave
name: Segment chart containment after terminal chart change
statement: Every old segment keeps its original chart-domain containment, and the added zero-length interval at $1$ lies in the old terminal chart attached to its left endpoint.
proof: Old intervals reduce to the original skeleton. On the final interval the bounds force $t=1$, and the left chart is the old terminal chart containing $x$.
-/
theorem terminalChartChange_path_segment_mem_model_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) :
    ∀ k : Fin (S.length + 1), ∀ t : unitInterval,
      (S.terminalStutterParameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (S.terminalStutterParameterAt k.succ : ℝ) →
      p t ∈
        (localModels.chartAt
          (S.terminalChartChangeCenterAt c k.castSucc)).domain := by
  intro k t ht_left ht_right
  by_cases hk : (k : ℕ) < S.length
  · let k₀ : Fin S.length := ⟨k, hk⟩
    have hleft_index :
        k.castSucc = (k₀.castSucc : Fin (S.length + 1)).castSucc := by
      ext
      rfl
    have hright_index : k.succ =
        (k₀.succ : Fin (S.length + 1)).castSucc := by
      ext
      rfl
    rw [hleft_index, S.terminalStutterParameterAt_castSucc k₀.castSucc]
      at ht_left
    rw [hright_index, S.terminalStutterParameterAt_castSucc k₀.succ]
      at ht_right
    have hcenter :
        S.terminalChartChangeCenterAt c k.castSucc =
          S.centerAt k₀.castSucc := by
      rw [hleft_index]
      simp
    rw [hcenter]
    exact S.path_segment_mem_model_domain k₀ t ht_left ht_right
  · have hk_last : k = Fin.last S.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    rw [S.terminalStutterParameterAt_final_left] at ht_left
    have ht_eq_one : t = 1 := by
      ext
      exact le_antisymm (unitInterval.le_one t) ht_left
    rw [ht_eq_one, p.target, S.terminalChartChangeCenterAt_final_left]
    exact S.terminal_endpoint_mem_domain

omit [RiemannSurface X] in
/-- The endpoint of a terminal chart-change path lies in the new terminal model.

%%handwave
name: Endpoint membership in the changed terminal chart
statement: If $x$ lies in the chart centered at $c$, then it belongs to the chart assigned to the new final vertex of the terminal chart-change subdivision.
proof: The new final center is $c$, so this is exactly the assumed membership.
-/
theorem terminalChartChange_terminal_endpoint_mem_domain
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain) :
    x ∈
      (localModels.chartAt
        (S.terminalChartChangeCenterAt c (Fin.last (S.length + 1)))).domain := by
  simpa [S.terminalChartChangeCenterAt_last] using hc

omit [RiemannSurface X] in
/--
Append a duplicate terminal vertex but change the selected terminal chart to
`c`, using a local real-Mobius transition at the endpoint to perform the final
zero-length handoff.
-/
noncomputable def terminalChartChangeSkeleton
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (T :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p where
  length := S.length + 1
  length_pos := Nat.succ_pos S.length
  parameterAt := S.terminalStutterParameterAt
  parameterAt_zero := S.terminalStutterParameterAt_zero
  parameterAt_last := S.terminalStutterParameterAt_last
  parameterAt_mono := S.terminalStutterParameterAt_mono
  centerAt := S.terminalChartChangeCenterAt c
  sample_mem_model_domain :=
    S.terminalChartChange_sample_mem_model_domain c hc
  path_segment_mem_model_domain :=
    S.terminalChartChange_path_segment_mem_model_domain c
  terminal_endpoint_mem_domain :=
    S.terminalChartChange_terminal_endpoint_mem_domain c hc
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
          localModels.chartAt
              (S.terminalChartChangeCenterAt c k.castSucc) =
            localModels.chartAt (S.centerAt k₀.castSucc) := by
        rw [hleft]
        simp
      have hV :
          localModels.chartAt
              (S.terminalChartChangeCenterAt c k.succ) =
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
      have hU :
          localModels.chartAt
              (S.terminalChartChangeCenterAt c
                ((Fin.last S.length : Fin (S.length + 1)).castSucc)) =
            localModels.chartAt S.terminalCenter := by
        simp [terminalCenter]
      have hV :
          localModels.chartAt
              (S.terminalChartChangeCenterAt c
                ((Fin.last S.length : Fin (S.length + 1)).succ)) =
            localModels.chartAt c := by
        rw [fin_last_succ_eq_last]
        simp
      have hpoint :
          p (S.terminalStutterParameterAt
              ((Fin.last S.length : Fin (S.length + 1)).succ)) = x := by
        rw [S.terminalStutterParameterAt_final_right, p.target]
      exact localRealMobiusTransitionData_congr hU hV hpoint T
  initialTransition := by
    exact localRealMobiusTransitionData_congr rfl
      (by simp [S.terminalChartChangeCenterAt_zero]) rfl S.initialTransition

omit [RiemannSurface X] in
/--
%%handwave
name: Terminal chart change selects the prescribed center
statement: Appending a zero-length handoff from the old terminal chart to a chart centered at $c$ makes $c$ the new terminal center.
proof: The new duplicate final vertex is assigned center $c$.
-/
@[simp]
theorem terminalChartChangeSkeleton_terminalCenter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (T :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x) :
    (S.terminalChartChangeSkeleton c hc T).terminalCenter = c := by
  simp [terminalChartChangeSkeleton, terminalCenter]

omit [RiemannSurface X] in
/--
Along the old part of a terminal chart-change skeleton, the accumulated Mobius
product agrees with the original skeleton.

%%handwave
name: Terminal chart change preserves accumulated products on the old prefix
statement: If $S'$ is obtained by a final chart change, then $M_j(S')=M_j(S)$ for every $j$ up to the old length.
proof: Induct on $j$; the initial transition and every old handoff representative are transported unchanged.
-/
theorem terminalChartChangeSkeleton_accumulatedMobiusNat_eq_of_le
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (T :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x) :
    ∀ n : ℕ, n ≤ S.length →
      (S.terminalChartChangeSkeleton c hc T).accumulatedMobiusNat n =
        S.accumulatedMobiusNat n := by
  intro n hn
  induction n with
  | zero =>
      simp [terminalChartChangeSkeleton, accumulatedMobiusNat]
  | succ n ih =>
      have hnlt : n < S.length := Nat.succ_le_iff.mp hn
      have hnle : n ≤ S.length := Nat.le_of_lt hnlt
      let R := S.terminalChartChangeSkeleton c hc T
      have hRstep :
          R.accumulatedMobiusNat (n + 1) =
            R.accumulatedMobiusNat n *
              (R.transitionAt ⟨n, Nat.lt_succ_of_lt hnlt⟩).representative⁻¹ :=
        R.accumulatedMobiusNat_succ_of_lt (Nat.lt_succ_of_lt hnlt)
      have hSstep :
          S.accumulatedMobiusNat (n + 1) =
            S.accumulatedMobiusNat n *
              (S.transitionAt ⟨n, hnlt⟩).representative⁻¹ :=
        S.accumulatedMobiusNat_succ_of_lt hnlt
      have htrans :
          (R.transitionAt ⟨n, Nat.lt_succ_of_lt hnlt⟩).representative =
            (S.transitionAt ⟨n, hnlt⟩).representative := by
        simp [R, terminalChartChangeSkeleton, hnlt]
      rw [hRstep, ih hnle, htrans, hSstep]

omit [RiemannSurface X] in
/--
%%handwave
name: Terminal representative after a chart change
statement: If the final chart change is represented by $A$, then the new terminal accumulated representative is $M'=MA^{-1}$.
proof: The accumulated product through the old last vertex is $M$, and the single new handoff updates it by right multiplication with $A^{-1}$.
-/
@[simp]
theorem terminalChartChangeSkeleton_terminalMobius_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (T :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x) :
    (S.terminalChartChangeSkeleton c hc T).terminalMobius =
      S.terminalMobius * T.representative⁻¹ := by
  let R := S.terminalChartChangeSkeleton c hc T
  have hprefix :
      R.accumulatedMobiusNat S.length = S.accumulatedMobiusNat S.length :=
    S.terminalChartChangeSkeleton_accumulatedMobiusNat_eq_of_le
      c hc T S.length le_rfl
  have hstep :
      R.accumulatedMobiusNat (S.length + 1) =
        R.accumulatedMobiusNat S.length *
          (R.transitionAt (Fin.last S.length)).representative⁻¹ := by
    exact R.accumulatedMobiusNat_succ_of_lt (Nat.lt_succ_self S.length)
  have htrans :
      (R.transitionAt (Fin.last S.length)).representative =
        T.representative := by
    simp [R, terminalChartChangeSkeleton]
  change R.accumulatedMobiusNat (S.length + 1) =
    S.accumulatedMobiusNat S.length * T.representative⁻¹
  rw [hstep, hprefix, htrans]

omit [RiemannSurface X] in
/--
After a terminal chart change by `T`, adjusting the new terminal Mobius class
back by `T.representative` recovers the old terminal PSL class.

%%handwave
name: Adjusted terminal class after a chart change
statement: If a terminal chart change has representative $A$ and new terminal representative $M'$, then $[M'A]=[M]$ in $\mathrm{PSL}_2(\mathbb R)$.
proof: Substitute $M'=MA^{-1}$ and cancel $A^{-1}A$ after projecting to the projective group.
-/
theorem terminalChartChangeSkeleton_adjustedTerminalMobius_projection_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (T :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x) :
    realMobiusProjection
        ((S.terminalChartChangeSkeleton c hc T).terminalMobius *
          T.representative) =
      realMobiusProjection S.terminalMobius := by
  rw [S.terminalChartChangeSkeleton_terminalMobius_eq c hc T]
  simp [mul_assoc]

omit [RiemannSurface X] in
/--
Synchronized terminal chart changes preserve literal terminal branch-data
equality, when the target-side transition datum is obtained from the
source-side datum by transporting across the equality of terminal centers.

%%handwave
name: Synchronized terminal chart changes preserve branch agreement
statement: Suppose skeletons $S,T$ have equal terminal centers and terminal representatives. Change both terminal charts to the same chart $c$, using the same transition representative after transporting across the equality of source charts. The resulting skeletons again have equal terminal branch data.
proof: Both new terminal centers are $c$. Their new representatives are the old equal representatives multiplied by the inverse of the same transition representative.
-/
theorem TerminalBranchDataEq.terminalChartChange
    {q : Path x₀ x}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q}
    (H : TerminalBranchDataEq S T)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x) :
    TerminalBranchDataEq
      (S.terminalChartChangeSkeleton c hc A)
      (T.terminalChartChangeSkeleton c hc
        (localRealMobiusTransitionData_congr
          (by rw [H.terminalCenter_eq]) rfl rfl A)) where
  terminalCenter_eq := by
    rw [S.terminalChartChangeSkeleton_terminalCenter c hc A,
      T.terminalChartChangeSkeleton_terminalCenter c hc
        (localRealMobiusTransitionData_congr
          (by rw [H.terminalCenter_eq]) rfl rfl A)]
  terminalMobius_eq := by
    rw [S.terminalChartChangeSkeleton_terminalMobius_eq c hc A,
      T.terminalChartChangeSkeleton_terminalMobius_eq c hc
        (localRealMobiusTransitionData_congr
          (by rw [H.terminalCenter_eq]) rfl rfl A),
      localRealMobiusTransitionData_congr_representative,
      H.terminalMobius_eq]

omit [RiemannSurface X] in
/--
One local suffix step preserves terminal branch-data equality: first change
both terminal charts to the chart containing the suffix segment, then append
the suffix segment exactly.

%%handwave
name: A synchronized chart change and local extension preserve branch agreement
statement: Starting from equal terminal branch data, change both terminal charts to a common chart $c$ through matching transition representatives and then append the same path $\rho$ lying in that chart. The two resulting skeletons have equal terminal branch data.
proof: The synchronized chart change preserves terminal agreement, and common exact extension within the new terminal chart preserves it again.
-/
theorem TerminalBranchDataEq.terminalChartChangeThenExtension
    {q : Path x₀ x}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q}
    (H : TerminalBranchDataEq S T)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x)
    {y : X} (ρ : Path x y)
    (hρS : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt
        ((S.terminalChartChangeSkeleton c hc A).terminalCenter)).domain)
    (hρT : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt
        ((T.terminalChartChangeSkeleton c hc
          (localRealMobiusTransitionData_congr
            (by rw [H.terminalCenter_eq]) rfl rfl A)).terminalCenter)).domain) :
    TerminalBranchDataEq
      ((S.terminalChartChangeSkeleton c hc A).terminalExtensionAlongSkeleton
        ρ hρS)
      ((T.terminalChartChangeSkeleton c hc
        (localRealMobiusTransitionData_congr
          (by rw [H.terminalCenter_eq]) rfl rfl A)).terminalExtensionAlongSkeleton
        ρ hρT) :=
  (H.terminalChartChange c hc A).terminalExtensionAlong ρ hρS hρT

omit [RiemannSurface X] in
/--
One local suffix step from a simple chart-containment hypothesis.  The
post-chart-change terminal centers are definitionally reduced to the chosen
suffix chart by the terminal chart-change theorem.

%%handwave
name: Local suffix extension from containment in the chosen chart
statement: Under equal terminal branch data, if a path $\rho$ lies in a chosen chart $c$ containing the common endpoint, then there are the required chart-membership witnesses after synchronized change to $c$, and extending both sides along $\rho$ preserves terminal branch agreement.
proof: The terminal center after each chart change is $c$, so the given containment supplies both membership witnesses. Apply synchronized chart change followed by extension.
-/
theorem TerminalBranchDataEq.terminalChartChangeThenExtension_of_mem
    {q : Path x₀ x}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q}
    (H : TerminalBranchDataEq S T)
    (c : X) (hc : x ∈ (localModels.chartAt c).domain)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt c)
        x)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈ (localModels.chartAt c).domain) :
    ∃ (hρS : ∀ t : unitInterval, ρ t ∈
          (localModels.chartAt
            ((S.terminalChartChangeSkeleton c hc A).terminalCenter)).domain)
      (hρT : ∀ t : unitInterval, ρ t ∈
          (localModels.chartAt
            ((T.terminalChartChangeSkeleton c hc
              (localRealMobiusTransitionData_congr
                (by rw [H.terminalCenter_eq]) rfl rfl A)).terminalCenter)).domain),
      TerminalBranchDataEq
        ((S.terminalChartChangeSkeleton c hc A).terminalExtensionAlongSkeleton
          ρ hρS)
        ((T.terminalChartChangeSkeleton c hc
          (localRealMobiusTransitionData_congr
            (by rw [H.terminalCenter_eq]) rfl rfl A)).terminalExtensionAlongSkeleton
          ρ hρT) := by
  let hρS : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt
        ((S.terminalChartChangeSkeleton c hc A).terminalCenter)).domain := by
    intro t
    rw [S.terminalChartChangeSkeleton_terminalCenter c hc A]
    exact hρ t
  let hρT : ∀ t : unitInterval, ρ t ∈
      (localModels.chartAt
        ((T.terminalChartChangeSkeleton c hc
          (localRealMobiusTransitionData_congr
            (by rw [H.terminalCenter_eq]) rfl rfl A)).terminalCenter)).domain := by
    intro t
    rw [T.terminalChartChangeSkeleton_terminalCenter c hc
      (localRealMobiusTransitionData_congr
        (by rw [H.terminalCenter_eq]) rfl rfl A)]
    exact hρ t
  exact
    ⟨hρS, hρT,
      H.terminalChartChangeThenExtension c hc A ρ hρS hρT⟩

omit [RiemannSurface X] in
/--
One suffix step specialized to a segment of a based weak handoff skeleton
for the suffix path.  The suffix skeleton supplies the chart containing that
closed segment.

%%handwave
name: Terminal branch agreement propagates across one suffix segment
statement: Suppose two skeletons agree in terminal branch data at the left endpoint of segment $k$ of a suffix skeleton. After changing both terminal charts to the chart controlling that segment and extending both along the subpath from $t_k$ to $t_{k+1}$, the resulting skeletons agree in terminal branch data at the right endpoint.
proof: The suffix skeleton guarantees that the whole segment lies in the chart centered at $c_k$. Apply synchronized chart change and local extension using that containment.
-/
theorem TerminalBranchDataEq.terminalSuffixSegment_of_suffixSkeleton
    {x₁ y : X} {suffix : Path x₁ y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (k : Fin C.length)
    {pS pT : Path x₀ (suffix (C.parameterAt k.castSucc))}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}
    (H : TerminalBranchDataEq S T)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt k.castSucc))
        (suffix (C.parameterAt k.castSucc))) :
    ∃ (hρS : ∀ t : unitInterval,
          (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) t ∈
            (localModels.chartAt
              ((S.terminalChartChangeSkeleton (C.centerAt k.castSucc)
                (C.path_segment_mem_model_domain k (C.parameterAt k.castSucc)
                  le_rfl (C.parameterAt_mono k)) A).terminalCenter)).domain)
      (hρT : ∀ t : unitInterval,
          (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) t ∈
            (localModels.chartAt
              ((T.terminalChartChangeSkeleton (C.centerAt k.castSucc)
                (C.path_segment_mem_model_domain k (C.parameterAt k.castSucc)
                  le_rfl (C.parameterAt_mono k))
                (localRealMobiusTransitionData_congr
                  (by rw [H.terminalCenter_eq]) rfl rfl A)).terminalCenter)).domain),
      TerminalBranchDataEq
        ((S.terminalChartChangeSkeleton (C.centerAt k.castSucc)
          (C.path_segment_mem_model_domain k (C.parameterAt k.castSucc)
            le_rfl (C.parameterAt_mono k)) A).terminalExtensionAlongSkeleton
          (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) hρS)
        ((T.terminalChartChangeSkeleton (C.centerAt k.castSucc)
          (C.path_segment_mem_model_domain k (C.parameterAt k.castSucc)
            le_rfl (C.parameterAt_mono k))
          (localRealMobiusTransitionData_congr
            (by rw [H.terminalCenter_eq]) rfl rfl A)).terminalExtensionAlongSkeleton
          (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) hρT) := by
  let c := C.centerAt k.castSucc
  let hc : suffix (C.parameterAt k.castSucc) ∈ (localModels.chartAt c).domain :=
    C.path_segment_mem_model_domain k (C.parameterAt k.castSucc)
      le_rfl (C.parameterAt_mono k)
  have hseg : ∀ t : unitInterval,
      (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) t ∈
        (localModels.chartAt c).domain := by
    intro t
    have hmem :
        (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) t ∈
          Set.range (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) :=
      ⟨t, rfl⟩
    have hSub :
        Set.range (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) =
          ((⇑suffix) '' Set.Icc (C.parameterAt k.castSucc) (C.parameterAt k.succ)) :=
      Path.range_subpath_of_le suffix
        (C.parameterAt k.castSucc) (C.parameterAt k.succ)
        (C.parameterAt_mono k)
    rw [hSub] at hmem
    rcases hmem with ⟨u, hu, hEq⟩
    rw [← hEq]
    exact C.path_segment_mem_model_domain k u hu.1 hu.2
  simpa [c, hc] using
    H.terminalChartChangeThenExtension_of_mem c hc A
      (suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)) hseg

omit [RiemannSurface X] in
/--
Finite suffix transport for terminal branch data.

Starting from two based weak handoff skeletons with equal terminal branch data
at the first vertex of a suffix skeleton, one can transport that equality
across every componentwise suffix segment.  At each new vertex we first change
both terminal charts to the suffix segment chart and then append that segment
inside the chart.  The output deliberately keeps only the terminal invariant;
path reassociation/reparametrization is handled separately by the homotopy-grid
bookkeeping.

%%handwave
name: Terminal branch agreement propagates across a finite suffix skeleton
statement: If two skeletons agree in terminal branch data at the first vertex of a suffix skeleton $C$, then there exist skeletons ending at its last sampled point that again agree in terminal branch data.
proof: Induct over the suffix segments. At each step choose a local transition from the current common terminal chart to the chart controlling the next suffix segment, then propagate agreement across that segment.
-/
theorem TerminalBranchDataEq.exists_terminalBranchDataEq_after_suffixSkeleton
    {x₁ y : X} {suffix : Path x₁ y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    {pS pT : Path x₀ (suffix (C.parameterAt 0))}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}
    (H : TerminalBranchDataEq S T) :
    ∃ (pS' pT' :
          Path x₀ (suffix (C.parameterAt (Fin.last C.length))))
      (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS')
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT'),
      TerminalBranchDataEq S' T' := by
  classical
  have hgo :
      ∀ n (hn : n ≤ C.length),
        ∃ (pS' pT' :
              Path x₀
                (suffix
                  (C.parameterAt ⟨n, Nat.lt_succ_of_le hn⟩)))
          (S' :
            PathLocalTransitionModelBasedWeakHandoffSkeleton
              x₀ g localModels pS')
          (T' :
            PathLocalTransitionModelBasedWeakHandoffSkeleton
              x₀ g localModels pT'),
          TerminalBranchDataEq S' T' := by
    intro n hn
    induction n with
    | zero =>
        have hindex :
            (⟨0, Nat.lt_succ_of_le hn⟩ : Fin (C.length + 1)) = 0 := by
          ext
          rfl
        simpa [hindex] using
          (⟨pS, pT, S, T, H⟩ :
            ∃ (pS' pT' : Path x₀ (suffix (C.parameterAt 0)))
              (S' :
                PathLocalTransitionModelBasedWeakHandoffSkeleton
                  x₀ g localModels pS')
              (T' :
                PathLocalTransitionModelBasedWeakHandoffSkeleton
                  x₀ g localModels pT'),
              TerminalBranchDataEq S' T')
    | succ n ih =>
        have hnle : n ≤ C.length := Nat.le_of_succ_le hn
        have hnlt : n < C.length := Nat.lt_of_succ_le hn
        rcases ih hnle with ⟨pS₀, pT₀, S₀, T₀, H₀⟩
        let k : Fin C.length := ⟨n, hnlt⟩
        have hleft :
            (⟨n, Nat.lt_succ_of_le hnle⟩ : Fin (C.length + 1)) =
              k.castSucc := by
          ext
          rfl
        have hright :
            (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (C.length + 1)) =
              k.succ := by
          ext
          rfl
        let c := C.centerAt k.castSucc
        let z := suffix (C.parameterAt k.castSucc)
        have hzS : z ∈ (localModels.chartAt S₀.terminalCenter).domain := by
          simpa [z] using S₀.terminal_endpoint_mem_domain
        have hzc : z ∈ (localModels.chartAt c).domain := by
          simpa [z, c] using
            C.path_segment_mem_model_domain k (C.parameterAt k.castSucc)
              le_rfl (C.parameterAt_mono k)
        let A :
            HyperbolicLocalChart.LocalRealMobiusTransitionData
              (localModels.chartAt S₀.terminalCenter)
            (localModels.chartAt (C.centerAt k.castSucc))
            (suffix (C.parameterAt k.castSucc)) :=
          Classical.choice
            (localModels.transition_localRealMobius
              S₀.terminalCenter (C.centerAt k.castSucc)
              (suffix (C.parameterAt k.castSucc))
              ⟨by simpa [z] using hzS, by simpa [z, c] using hzc⟩)
        rcases H₀.terminalSuffixSegment_of_suffixSkeleton C k A with
          ⟨hρS, hρT, Hnext⟩
        rw [hright]
        exact ⟨_, _, _, _, Hnext⟩
  simpa using hgo C.length le_rfl

omit [RiemannSurface X] in
/--
Finite suffix transport, terminal-value form.

%%handwave
name: Terminal value agreement propagates across a finite suffix skeleton
statement: Under the preceding hypotheses, there exist transported skeletons at the final sampled point of the suffix whose terminal values are equal.
proof: Finite suffix transport gives equal terminal branch data at the final point; evaluate the resulting equal terminal formulas there.
-/
theorem TerminalBranchDataEq.exists_terminalValue_eq_after_suffixSkeleton
    {x₁ y : X} {suffix : Path x₁ y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    {pS pT : Path x₀ (suffix (C.parameterAt 0))}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}
    (H : TerminalBranchDataEq S T) :
    ∃ (pS' pT' :
          Path x₀ (suffix (C.parameterAt (Fin.last C.length))))
      (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS')
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT'),
      S'.terminalValue = T'.terminalValue := by
  rcases H.exists_terminalBranchDataEq_after_suffixSkeleton C with
    ⟨pS', pT', S', T', H'⟩
  exact ⟨pS', pT', S', T', H'.terminalValue_eq⟩

omit [RiemannSurface X] in
/--
Finite suffix transport with homotopy bookkeeping.

Besides preserving terminal branch data, the transported paths are homotopic
to the original paths followed by the corresponding suffix subpath.  This is
the one-dimensional reparameterization information needed to connect finite
componentwise suffix transport back to exact concatenation by the whole
suffix.

%%handwave
name: Finite suffix transport with path-homotopy control
statement: Under initial terminal branch agreement, there are transported skeletons at the last suffix vertex with equal terminal branch data, whose underlying paths are respectively homotopic to the original paths concatenated with the suffix subpath from the first to the last sampled parameter.
proof: Induct across suffix segments. Propagate terminal agreement one segment at a time and compose the induction homotopy with the new segment; associativity of concatenation and composition of adjacent subpaths identify the result with the longer suffix subpath.
-/
theorem TerminalBranchDataEq.exists_terminalBranchDataEq_after_suffixSkeleton_with_homotopy
    {x₁ y : X} {suffix : Path x₁ y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    {pS pT : Path x₀ (suffix (C.parameterAt 0))}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}
    (H : TerminalBranchDataEq S T) :
    ∃ (pS' pT' :
          Path x₀ (suffix (C.parameterAt (Fin.last C.length))))
      (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS')
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT'),
      TerminalBranchDataEq S' T' ∧
        pS'.Homotopic
          (pS.trans
            (suffix.subpath (C.parameterAt 0)
              (C.parameterAt (Fin.last C.length)))) ∧
        pT'.Homotopic
          (pT.trans
            (suffix.subpath (C.parameterAt 0)
              (C.parameterAt (Fin.last C.length)))) := by
  classical
  have hgo :
      ∀ n (hn : n ≤ C.length),
        ∃ (pS' pT' :
              Path x₀
                (suffix
                  (C.parameterAt ⟨n, Nat.lt_succ_of_le hn⟩)))
          (S' :
            PathLocalTransitionModelBasedWeakHandoffSkeleton
              x₀ g localModels pS')
          (T' :
            PathLocalTransitionModelBasedWeakHandoffSkeleton
              x₀ g localModels pT'),
          TerminalBranchDataEq S' T' ∧
            pS'.Homotopic
              (pS.trans
                (suffix.subpath (C.parameterAt 0)
                  (C.parameterAt ⟨n, Nat.lt_succ_of_le hn⟩))) ∧
            pT'.Homotopic
              (pT.trans
                (suffix.subpath (C.parameterAt 0)
                  (C.parameterAt ⟨n, Nat.lt_succ_of_le hn⟩))) := by
    intro n hn
    induction n with
    | zero =>
        have hindex :
            (⟨0, Nat.lt_succ_of_le hn⟩ : Fin (C.length + 1)) = 0 := by
          ext
          rfl
        have hS :
            pS.Homotopic
              (pS.trans
                (suffix.subpath (C.parameterAt 0)
                  (C.parameterAt ⟨0, Nat.lt_succ_of_le hn⟩))) := by
          simpa [hindex] using (Path.Homotopic.trans_refl pS).symm
        have hT :
            pT.Homotopic
              (pT.trans
                (suffix.subpath (C.parameterAt 0)
                  (C.parameterAt ⟨0, Nat.lt_succ_of_le hn⟩))) := by
          simpa [hindex] using (Path.Homotopic.trans_refl pT).symm
        exact ⟨pS, pT, S, T, H, hS, hT⟩
    | succ n ih =>
        have hnle : n ≤ C.length := Nat.le_of_succ_le hn
        have hnlt : n < C.length := Nat.lt_of_succ_le hn
        rcases ih hnle with ⟨pS₀, pT₀, S₀, T₀, H₀, hS₀, hT₀⟩
        let k : Fin C.length := ⟨n, hnlt⟩
        have hleft :
            (⟨n, Nat.lt_succ_of_le hnle⟩ : Fin (C.length + 1)) =
              k.castSucc := by
          ext
          rfl
        have hright :
            (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (C.length + 1)) =
              k.succ := by
          ext
          rfl
        let c := C.centerAt k.castSucc
        let z := suffix (C.parameterAt k.castSucc)
        have hzS : z ∈ (localModels.chartAt S₀.terminalCenter).domain := by
          simpa [z] using S₀.terminal_endpoint_mem_domain
        have hzc : z ∈ (localModels.chartAt c).domain := by
          simpa [z, c] using
            C.path_segment_mem_model_domain k (C.parameterAt k.castSucc)
              le_rfl (C.parameterAt_mono k)
        let A :
            HyperbolicLocalChart.LocalRealMobiusTransitionData
              (localModels.chartAt S₀.terminalCenter)
            (localModels.chartAt (C.centerAt k.castSucc))
            (suffix (C.parameterAt k.castSucc)) :=
          Classical.choice
            (localModels.transition_localRealMobius
              S₀.terminalCenter (C.centerAt k.castSucc)
              (suffix (C.parameterAt k.castSucc))
              ⟨by simpa [z] using hzS, by simpa [z, c] using hzc⟩)
        rcases H₀.terminalSuffixSegment_of_suffixSkeleton C k A with
          ⟨hρS, hρT, Hnext⟩
        let seg := suffix.subpath (C.parameterAt k.castSucc) (C.parameterAt k.succ)
        let sub₀ := suffix.subpath (C.parameterAt 0) (C.parameterAt k.castSucc)
        let sub₁ := suffix.subpath (C.parameterAt 0) (C.parameterAt k.succ)
        have hS₀' : pS₀.Homotopic (pS.trans sub₀) := by
          simpa [sub₀, hleft] using hS₀
        have hT₀' : pT₀.Homotopic (pT.trans sub₀) := by
          simpa [sub₀, hleft] using hT₀
        have hSnext :
            (pS₀.trans seg).Homotopic (pS.trans sub₁) := by
          have h₁ :
              (pS₀.trans seg).Homotopic ((pS.trans sub₀).trans seg) :=
            Path.Homotopic.hcomp hS₀' (Path.Homotopic.refl seg)
          have h₂ :
              ((pS.trans sub₀).trans seg).Homotopic
                (pS.trans (sub₀.trans seg)) :=
            Path.Homotopic.trans_assoc pS sub₀ seg
          have h₃ :
              (pS.trans (sub₀.trans seg)).Homotopic (pS.trans sub₁) :=
            Path.Homotopic.hcomp (Path.Homotopic.refl pS)
              (by
                simpa [sub₀, sub₁, seg] using
                  (⟨Path.Homotopy.subpathTransSubpath suffix
                    (C.parameterAt 0) (C.parameterAt k.castSucc)
                    (C.parameterAt k.succ)⟩ :
                    (suffix.subpath (C.parameterAt 0)
                        (C.parameterAt k.castSucc)).trans
                        (suffix.subpath (C.parameterAt k.castSucc)
                          (C.parameterAt k.succ)) |>.Homotopic
                      (suffix.subpath (C.parameterAt 0)
                        (C.parameterAt k.succ))))
          exact h₁.trans (h₂.trans h₃)
        have hTnext :
            (pT₀.trans seg).Homotopic (pT.trans sub₁) := by
          have h₁ :
              (pT₀.trans seg).Homotopic ((pT.trans sub₀).trans seg) :=
            Path.Homotopic.hcomp hT₀' (Path.Homotopic.refl seg)
          have h₂ :
              ((pT.trans sub₀).trans seg).Homotopic
                (pT.trans (sub₀.trans seg)) :=
            Path.Homotopic.trans_assoc pT sub₀ seg
          have h₃ :
              (pT.trans (sub₀.trans seg)).Homotopic (pT.trans sub₁) :=
            Path.Homotopic.hcomp (Path.Homotopic.refl pT)
              (by
                simpa [sub₀, sub₁, seg] using
                  (⟨Path.Homotopy.subpathTransSubpath suffix
                    (C.parameterAt 0) (C.parameterAt k.castSucc)
                    (C.parameterAt k.succ)⟩ :
                    (suffix.subpath (C.parameterAt 0)
                        (C.parameterAt k.castSucc)).trans
                        (suffix.subpath (C.parameterAt k.castSucc)
                          (C.parameterAt k.succ)) |>.Homotopic
                      (suffix.subpath (C.parameterAt 0)
                        (C.parameterAt k.succ))))
          exact h₁.trans (h₂.trans h₃)
        rw [hright]
        exact ⟨_, _, _, _, Hnext, hSnext, hTnext⟩
  simpa using hgo C.length le_rfl

omit [RiemannSurface X] in
/--
Finite suffix transport with the natural endpoint types.

This is a wrapper around
`exists_terminalBranchDataEq_after_suffixSkeleton`: the initial and final
endpoint equalities of the suffix skeleton are handled by `castTarget`, so
callers can work with paths ending at the honest source and target of the
suffix path.

%%handwave
name: Finite suffix transport between the actual suffix endpoints
statement: If two skeletons at the source $x_1$ of a suffix path have equal terminal branch data, then there exist skeletons at its actual target $y$ whose terminal branch data are equal.
proof: Recast the initial skeleton endpoints along $t_0=0$, apply finite suffix transport to the sampled endpoints, and recast the outputs along $t_\ell=1$ to the actual target.
-/
theorem TerminalBranchDataEq.exists_terminalBranchDataEq_after_suffixSkeleton_castEndpoints
    {x₁ y : X} {suffix : Path x₁ y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    {pS pT : Path x₀ x₁}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}
    (H : TerminalBranchDataEq S T) :
    ∃ (pS' pT' : Path x₀ y)
      (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS')
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT'),
      TerminalBranchDataEq S' T' := by
  have h0 : suffix (C.parameterAt 0) = x₁ := by
    rw [C.parameterAt_zero, suffix.source]
  have H0 :
      TerminalBranchDataEq (S.castTarget h0) (T.castTarget h0) := by
    exact
      { terminalCenter_eq := by
          simpa using H.terminalCenter_eq
        terminalMobius_eq := by
          rw [S.castTarget_terminalMobius h0,
            T.castTarget_terminalMobius h0, H.terminalMobius_eq] }
  rcases H0.exists_terminalBranchDataEq_after_suffixSkeleton C with
    ⟨qS, qT, S₁, T₁, H₁⟩
  have hlast : y = suffix (C.parameterAt (Fin.last C.length)) := by
    rw [C.parameterAt_last, suffix.target]
  exact
    ⟨qS.cast rfl hlast, qT.cast rfl hlast,
      S₁.castTarget hlast, T₁.castTarget hlast,
      { terminalCenter_eq := by
          simpa using H₁.terminalCenter_eq
        terminalMobius_eq := by
          rw [S₁.castTarget_terminalMobius hlast,
            T₁.castTarget_terminalMobius hlast, H₁.terminalMobius_eq] }⟩

omit [RiemannSurface X] in
/--
Finite suffix transport with natural endpoints and homotopy bookkeeping.

This is the endpoint-normalized form of
`exists_terminalBranchDataEq_after_suffixSkeleton_with_homotopy`: the output
paths end at the honest target of the suffix, and the transported paths are
homotopic to concatenation by the whole suffix.

%%handwave
name: Finite suffix transport between actual endpoints with homotopy control
statement: Under equal terminal branch data at the source of a suffix $\sigma$, there exist skeletons over paths to its target with equal terminal branch data, and those paths are homotopic to the original paths concatenated with $\sigma$.
proof: Normalize the source and target endpoint types in the finite transport with homotopy control. The full sampled subpath from $0$ to $1$ is homotopic to $\sigma$, and endpoint recasting preserves terminal branch agreement.
-/
theorem TerminalBranchDataEq.exists_terminalBranchDataEq_after_suffixSkeleton_castEndpoints_with_homotopy
    {x₁ y : X} {suffix : Path x₁ y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    {pS pT : Path x₀ x₁}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}
    (H : TerminalBranchDataEq S T) :
    ∃ (pS' pT' : Path x₀ y)
      (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS')
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT'),
      TerminalBranchDataEq S' T' ∧
        pS'.Homotopic (pS.trans suffix) ∧
        pT'.Homotopic (pT.trans suffix) := by
  have h0 : suffix (C.parameterAt 0) = x₁ := by
    rw [C.parameterAt_zero, suffix.source]
  have H0 :
      TerminalBranchDataEq (S.castTarget h0) (T.castTarget h0) := by
    exact
      { terminalCenter_eq := by
          simpa using H.terminalCenter_eq
        terminalMobius_eq := by
          rw [S.castTarget_terminalMobius h0,
            T.castTarget_terminalMobius h0, H.terminalMobius_eq] }
  rcases H0.exists_terminalBranchDataEq_after_suffixSkeleton_with_homotopy C with
    ⟨qS, qT, S₁, T₁, H₁, hqS, hqT⟩
  have hlast : y = suffix (C.parameterAt (Fin.last C.length)) := by
    rw [C.parameterAt_last, suffix.target]
  let sub :=
    suffix.subpath (C.parameterAt 0) (C.parameterAt (Fin.last C.length))
  have hprefixS :
      ((pS.cast rfl h0).cast rfl h0.symm) = pS := by
    ext u
    rfl
  have hprefixT :
      ((pT.cast rfl h0).cast rfl h0.symm) = pT := by
    ext u
    rfl
  have hsub : (sub.cast h0.symm hlast) = suffix := by
    ext u
    simp [sub, Path.subpath, C.parameterAt_zero, C.parameterAt_last]
  have htargetS :
      (((pS.cast rfl h0).trans sub).cast rfl hlast) =
        pS.trans suffix := by
    calc
      (((pS.cast rfl h0).trans sub).cast rfl hlast)
          =
            ((pS.cast rfl h0).cast rfl h0.symm).trans
              (sub.cast h0.symm hlast) := by
            rw [Path.cast_trans]
      _ = pS.trans suffix := by
            rw [hprefixS, hsub]
  have htargetT :
      (((pT.cast rfl h0).trans sub).cast rfl hlast) =
        pT.trans suffix := by
    calc
      (((pT.cast rfl h0).trans sub).cast rfl hlast)
          =
            ((pT.cast rfl h0).cast rfl h0.symm).trans
              (sub.cast h0.symm hlast) := by
            rw [Path.cast_trans]
      _ = pT.trans suffix := by
            rw [hprefixT, hsub]
  have hqS' :
      (qS.cast rfl hlast).Homotopic (pS.trans suffix) := by
    simpa [sub, htargetS] using
      (Path.Homotopic.pathCast hqS rfl hlast)
  have hqT' :
      (qT.cast rfl hlast).Homotopic (pT.trans suffix) := by
    simpa [sub, htargetT] using
      (Path.Homotopic.pathCast hqT rfl hlast)
  exact
    ⟨qS.cast rfl hlast, qT.cast rfl hlast,
      S₁.castTarget hlast, T₁.castTarget hlast,
      { terminalCenter_eq := by
          simpa using H₁.terminalCenter_eq
        terminalMobius_eq := by
          rw [S₁.castTarget_terminalMobius hlast,
            T₁.castTarget_terminalMobius hlast, H₁.terminalMobius_eq] },
      hqS', hqT'⟩

omit [RiemannSurface X] in
/--
Finite suffix transport with natural endpoints, terminal values, and
homotopy bookkeeping.

%%handwave
name: Equal terminal values after suffix transport with homotopy control
statement: Under equal terminal branch data at the source of a suffix $\sigma$, there exist paths to its target, homotopic to the original paths concatenated with $\sigma$, whose continuation skeletons have equal terminal values.
proof: Use endpoint-normalized suffix transport with homotopy control and replace equal terminal branch data by the resulting equality of terminal values.
-/
theorem TerminalBranchDataEq.exists_terminalValue_eq_after_suffixSkeleton_castEndpoints_with_homotopy
    {x₁ y : X} {suffix : Path x₁ y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    {pS pT : Path x₀ x₁}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}
    (H : TerminalBranchDataEq S T) :
    ∃ (pS' pT' : Path x₀ y)
      (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS')
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT'),
      S'.terminalValue = T'.terminalValue ∧
        pS'.Homotopic (pS.trans suffix) ∧
        pT'.Homotopic (pT.trans suffix) := by
  rcases H.exists_terminalBranchDataEq_after_suffixSkeleton_castEndpoints_with_homotopy C with
    ⟨pS', pT', S', T', H', hpS', hpT'⟩
  exact ⟨pS', pT', S', T', H'.terminalValue_eq, hpS', hpT'⟩

omit [RiemannSurface X] in
/--
Finite suffix transport with natural endpoints, terminal-value form.

%%handwave
name: Equal terminal values after transport along a suffix
statement: If two skeletons at the source of a suffix path agree in terminal branch data, then there exist skeletons over paths to the target of the suffix with equal terminal values.
proof: Apply endpoint-normalized finite suffix transport and evaluate the equal terminal branch data at the common endpoint.
-/
theorem TerminalBranchDataEq.exists_terminalValue_eq_after_suffixSkeleton_castEndpoints
    {x₁ y : X} {suffix : Path x₁ y}
    (C :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    {pS pT : Path x₀ x₁}
    {S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS}
    {T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT}
    (H : TerminalBranchDataEq S T) :
    ∃ (pS' pT' : Path x₀ y)
      (S' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pS')
      (T' :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels pT'),
      S'.terminalValue = T'.terminalValue := by
  rcases H.exists_terminalBranchDataEq_after_suffixSkeleton_castEndpoints C with
    ⟨pS', pT', S', T', H'⟩
  exact ⟨pS', pT', S', T', H'.terminalValue_eq⟩

omit [RiemannSurface X] in
/--
Subdivision parameters for appending an already-subdivided suffix skeleton to
a prefix skeleton over the exact concatenated path `p.trans suffix`.

The prefix subdivision is compressed into the first half.  The suffix
subdivision is compressed into the second half, with a duplicated vertex at
`1 / 2` for the handoff from the prefix terminal chart to the first suffix
chart.
-/
noncomputable def appendSuffixParameterAt
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    Fin (S.length + C.length + 2) → unitInterval :=
  fun i =>
    if hi : (i : ℕ) < S.length + 1 then
      unitInterval.firstHalf (S.parameterAt ⟨i, hi⟩)
    else
      unitInterval.secondHalf
        (C.parameterAt ⟨(i : ℕ) - (S.length + 1), by omega⟩)

omit [RiemannSurface X] in
/--
Centers for exact suffix append: prefix centers on the first half and suffix
centers on the second half.
-/
noncomputable def appendSuffixCenterAt
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    Fin (S.length + C.length + 2) → X :=
  fun i =>
    if hi : (i : ℕ) < S.length + 1 then
      S.centerAt ⟨i, hi⟩
    else
      C.centerAt ⟨(i : ℕ) - (S.length + 1), by omega⟩

omit [RiemannSurface X] in
/--
%%handwave
name: Prefix parameters in an exact suffix append
statement: In the subdivision of $p*\sigma$, every prefix parameter $t_i$ appears in the first half as $t_i/2$.
proof: The prefix-index branch of the appended parameter function applies first-half rescaling.
-/
@[simp]
theorem appendSuffixParameterAt_left
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (i : Fin (S.length + 1)) :
    appendSuffixParameterAt S C
        (⟨i, by omega⟩ : Fin (S.length + C.length + 2)) =
      unitInterval.firstHalf (S.parameterAt i) := by
  simp [appendSuffixParameterAt, i.isLt]

omit [RiemannSurface X] in
/--
%%handwave
name: Prefix centers in an exact suffix append
statement: Every prefix vertex in an exact suffix append keeps its original chart center.
proof: The prefix-index branch of the appended center function returns the prefix center.
-/
@[simp]
theorem appendSuffixCenterAt_left
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (i : Fin (S.length + 1)) :
    appendSuffixCenterAt S C
        (⟨i, by omega⟩ : Fin (S.length + C.length + 2)) =
      S.centerAt i := by
  simp [appendSuffixCenterAt, i.isLt]

omit [RiemannSurface X] in
/--
%%handwave
name: Suffix parameters in an exact suffix append
statement: In the subdivision of $p*\sigma$, every suffix parameter $u_j$ appears in the second half as $(1+u_j)/2$.
proof: Subtracting the prefix offset recovers $j$, and the suffix branch applies second-half rescaling.
-/
@[simp]
theorem appendSuffixParameterAt_right
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (j : Fin (C.length + 1)) :
    appendSuffixParameterAt S C
        (⟨S.length + 1 + (j : ℕ), by omega⟩ :
          Fin (S.length + C.length + 2)) =
      unitInterval.secondHalf (C.parameterAt j) := by
  have hnot : ¬ S.length + 1 + (j : ℕ) < S.length + 1 := by
    omega
  have hsub : S.length + 1 + (j : ℕ) - (S.length + 1) = (j : ℕ) := by
    omega
  simp [appendSuffixParameterAt, hnot, hsub]

omit [RiemannSurface X] in
/--
%%handwave
name: Suffix centers in an exact suffix append
statement: Every suffix vertex in an exact append carries its original suffix chart center.
proof: Removing the prefix offset recovers its suffix index, and the suffix branch returns that center.
-/
@[simp]
theorem appendSuffixCenterAt_right
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (j : Fin (C.length + 1)) :
    appendSuffixCenterAt S C
        (⟨S.length + 1 + (j : ℕ), by omega⟩ :
          Fin (S.length + C.length + 2)) =
      C.centerAt j := by
  have hnot : ¬ S.length + 1 + (j : ℕ) < S.length + 1 := by
    omega
  have hsub : S.length + 1 + (j : ℕ) - (S.length + 1) = (j : ℕ) := by
    omega
  simp [appendSuffixCenterAt, hnot, hsub]

omit [RiemannSurface X] in
/--
%%handwave
name: Exact suffix append begins at zero
statement: The first parameter of the appended subdivision is $0$.
proof: It is the first-half image of the prefix parameter $t_0=0$.
-/
@[simp]
theorem appendSuffixParameterAt_zero
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    appendSuffixParameterAt S C 0 = 0 := by
  simpa [S.parameterAt_zero] using
    appendSuffixParameterAt_left S C (0 : Fin (S.length + 1))

omit [RiemannSurface X] in
/--
%%handwave
name: Exact suffix append begins in the prefix's first chart
statement: The first center of the appended skeleton is the first center of the prefix skeleton.
proof: The first vertex belongs to the prefix block and retains its center.
-/
@[simp]
theorem appendSuffixCenterAt_zero
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    appendSuffixCenterAt S C 0 = S.centerAt 0 := by
  simpa using appendSuffixCenterAt_left S C (0 : Fin (S.length + 1))

omit [RiemannSurface X] in
/--
%%handwave
name: Exact suffix append ends at one
statement: The last parameter of the appended subdivision is $1$.
proof: It is the second-half image of the suffix's last parameter $u_m=1$.
-/
@[simp]
theorem appendSuffixParameterAt_last
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    appendSuffixParameterAt S C (Fin.last (S.length + C.length + 1)) = 1 := by
  have hidx :
      (Fin.last (S.length + C.length + 1) : Fin (S.length + C.length + 2)) =
        (⟨S.length + 1 + C.length, by omega⟩ :
          Fin (S.length + C.length + 2)) := by
    ext
    simp
    omega
  rw [hidx]
  simpa [C.parameterAt_last] using
    appendSuffixParameterAt_right S C (Fin.last C.length)

omit [RiemannSurface X] in
/--
%%handwave
name: Exact suffix append ends in the suffix's terminal chart
statement: The last center of the appended skeleton is the terminal center of the suffix skeleton.
proof: The new last vertex is the suffix's last vertex after applying the prefix index offset.
-/
@[simp]
theorem appendSuffixCenterAt_last
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    appendSuffixCenterAt S C (Fin.last (S.length + C.length + 1)) =
      C.terminalCenter := by
  have hidx :
      (Fin.last (S.length + C.length + 1) : Fin (S.length + C.length + 2)) =
        (⟨S.length + 1 + C.length, by omega⟩ :
          Fin (S.length + C.length + 2)) := by
    ext
    simp
    omega
  rw [hidx]
  simpa [terminalCenter] using
    appendSuffixCenterAt_right S C (Fin.last C.length)

omit [RiemannSurface X] in
/--
%%handwave
name: Concatenation at an appended prefix vertex recovers the prefix path
statement: At every prefix vertex, $(p*\sigma)(t_i/2)=p(t_i)$.
proof: This is the defining first-half evaluation formula for path concatenation.
-/
@[simp]
theorem path_trans_appendSuffixParameterAt_left
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (i : Fin (S.length + 1)) :
    (p.trans suffix)
        (appendSuffixParameterAt S C
          (⟨i, by omega⟩ : Fin (S.length + C.length + 2))) =
      p (S.parameterAt i) := by
  rw [appendSuffixParameterAt_left S C i]
  exact path_trans_firstHalf_apply p suffix (S.parameterAt i)

omit [RiemannSurface X] in
/--
%%handwave
name: Concatenation at an appended suffix vertex recovers the suffix path
statement: At every suffix vertex, $(p*\sigma)((1+u_j)/2)=\sigma(u_j)$.
proof: This is the defining second-half evaluation formula for path concatenation.
-/
@[simp]
theorem path_trans_appendSuffixParameterAt_right
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (j : Fin (C.length + 1)) :
    (p.trans suffix)
        (appendSuffixParameterAt S C
          (⟨S.length + 1 + (j : ℕ), by omega⟩ :
            Fin (S.length + C.length + 2))) =
      suffix (C.parameterAt j) := by
  rw [appendSuffixParameterAt_right S C j]
  exact path_trans_secondHalf_apply p suffix (C.parameterAt j)

omit [RiemannSurface X] in
/-- The exact-append subdivision parameters are weakly increasing.

%%handwave
name: Monotonicity of exact-append subdivision parameters
statement: If $(t_i)$ and $(u_j)$ are weakly increasing subdivisions from $0$ to $1$, then the combined sequence $(t_i/2)$ followed by $((1+u_j)/2)$ is weakly increasing.
proof: First-half and second-half rescaling preserve the two original orders. At the bridge, the last prefix value and first suffix value are both $1/2$.
-/
theorem appendSuffixParameterAt_mono
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    ∀ k : Fin (S.length + C.length + 1),
      (appendSuffixParameterAt S C k.castSucc : ℝ) ≤
        (appendSuffixParameterAt S C k.succ : ℝ) := by
  intro k
  by_cases hk_left : (k : ℕ) < S.length
  · let kp : Fin S.length := ⟨k, hk_left⟩
    have hleft :
        (k.castSucc : Fin (S.length + C.length + 2)) =
          (⟨(kp.castSucc : Fin (S.length + 1)), by omega⟩ :
            Fin (S.length + C.length + 2)) := by
      ext
      rfl
    have hright :
        (k.succ : Fin (S.length + C.length + 2)) =
          (⟨(kp.succ : Fin (S.length + 1)), by omega⟩ :
            Fin (S.length + C.length + 2)) := by
      ext
      rfl
    rw [hleft, hright, appendSuffixParameterAt_left S C kp.castSucc,
      appendSuffixParameterAt_left S C kp.succ]
    change ((S.parameterAt kp.castSucc : ℝ) / 2) ≤
      ((S.parameterAt kp.succ : ℝ) / 2)
    nlinarith [S.parameterAt_mono kp]
  · by_cases hk_bridge : (k : ℕ) = S.length
    · have hleft :
          (k.castSucc : Fin (S.length + C.length + 2)) =
            (⟨(Fin.last S.length : Fin (S.length + 1)), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        simp [hk_bridge]
      have hright :
          (k.succ : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (0 : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        simp [hk_bridge]
      rw [hleft, hright]
      simp [appendSuffixParameterAt, C.parameterAt_zero]
      have hle :
          (S.parameterAt (⟨S.length, by omega⟩ : Fin (S.length + 1)) : ℝ) ≤
            1 := unitInterval.le_one _
      nlinarith
    · have hk_suffix : S.length + 1 ≤ (k : ℕ) := by
        omega
      let j : Fin C.length := ⟨(k : ℕ) - (S.length + 1), by omega⟩
      have hleft :
          (k.castSucc : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (j.castSucc : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        change (k : ℕ) = S.length + 1 + ((k : ℕ) - (S.length + 1))
        omega
      have hright :
          (k.succ : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (j.succ : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        change (k : ℕ) + 1 =
          S.length + 1 + (((k : ℕ) - (S.length + 1)) + 1)
        omega
      rw [hleft, hright, appendSuffixParameterAt_right S C j.castSucc,
        appendSuffixParameterAt_right S C j.succ]
      change (1 + (C.parameterAt j.castSucc : ℝ)) / 2 ≤
        (1 + (C.parameterAt j.succ : ℝ)) / 2
      nlinarith [C.parameterAt_mono j]

omit [RiemannSurface X] in
/-- Every exact-append subdivision vertex lies in its assigned chart domain.

%%handwave
name: Vertex chart membership for exact suffix append
statement: Every vertex of the combined subdivision of $p*\sigma$ lies in its assigned prefix or suffix chart domain.
proof: Prefix vertices evaluate to the original prefix samples and suffix vertices to the original suffix samples; apply the corresponding sampling condition.
-/
theorem appendSuffix_sample_mem_model_domain
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    ∀ i : Fin (S.length + C.length + 2),
      (p.trans suffix) (appendSuffixParameterAt S C i) ∈
        (localModels.chartAt (appendSuffixCenterAt S C i)).domain := by
  intro i
  by_cases hi : (i : ℕ) < S.length + 1
  · let j : Fin (S.length + 1) := ⟨i, hi⟩
    have hij :
        i =
          (⟨(j : ℕ), by omega⟩ :
            Fin (S.length + C.length + 2)) := by
      ext
      rfl
    rw [hij, appendSuffixParameterAt_left S C j,
      appendSuffixCenterAt_left S C j]
    rw [path_trans_firstHalf_apply]
    exact S.sample_mem_model_domain j
  · let j : Fin (C.length + 1) :=
      ⟨(i : ℕ) - (S.length + 1), by omega⟩
    have hij :
        i =
          (⟨S.length + 1 + (j : ℕ), by omega⟩ :
            Fin (S.length + C.length + 2)) := by
      ext
      change (i : ℕ) = S.length + 1 + ((i : ℕ) - (S.length + 1))
      omega
    rw [hij, appendSuffixParameterAt_right S C j,
      appendSuffixCenterAt_right S C j]
    rw [path_trans_secondHalf_apply]
    exact C.sample_mem_model_domain j

omit [RiemannSurface X] in
/-- Each exact-append subinterval lies in the chart assigned to its left vertex.

%%handwave
name: Segment chart containment for exact suffix append
statement: Each first-half subinterval of $p*\sigma$ lies in its prefix chart, each second-half subinterval lies in its suffix chart, and the bridge interval is the single concatenation point in the prefix terminal chart.
proof: Undo the first- or second-half reparameterization and apply the corresponding segment-containment condition. At the bridge both bounds force $t=1/2$, where the concatenation equals the prefix endpoint.
-/
theorem appendSuffix_path_segment_mem_model_domain
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    ∀ k : Fin (S.length + C.length + 1), ∀ t : unitInterval,
      (appendSuffixParameterAt S C k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (appendSuffixParameterAt S C k.succ : ℝ) →
      (p.trans suffix) t ∈
        (localModels.chartAt (appendSuffixCenterAt S C k.castSucc)).domain := by
  intro k t ht_left ht_right
  by_cases hk_left : (k : ℕ) < S.length
  · let kp : Fin S.length := ⟨k, hk_left⟩
    have hleft :
        (k.castSucc : Fin (S.length + C.length + 2)) =
          (⟨(kp.castSucc : Fin (S.length + 1)), by omega⟩ :
            Fin (S.length + C.length + 2)) := by
      ext
      rfl
    have hright :
        (k.succ : Fin (S.length + C.length + 2)) =
          (⟨(kp.succ : Fin (S.length + 1)), by omega⟩ :
            Fin (S.length + C.length + 2)) := by
      ext
      rfl
    rw [hleft, appendSuffixParameterAt_left S C kp.castSucc] at ht_left
    rw [hright, appendSuffixParameterAt_left S C kp.succ] at ht_right
    have ht_half : (t : ℝ) ≤ 1 / 2 :=
      le_trans ht_right (unitInterval.firstHalf_le_half (S.parameterAt kp.succ))
    have h_lower :
        (S.parameterAt kp.castSucc : ℝ) ≤
          (unitInterval.doubleOfLeHalf t ht_half : ℝ) := by
      change (S.parameterAt kp.castSucc : ℝ) ≤ 2 * (t : ℝ)
      change ((S.parameterAt kp.castSucc : ℝ) / 2) ≤ (t : ℝ) at ht_left
      nlinarith
    have h_upper :
        (unitInterval.doubleOfLeHalf t ht_half : ℝ) ≤
          (S.parameterAt kp.succ : ℝ) := by
      change 2 * (t : ℝ) ≤ (S.parameterAt kp.succ : ℝ)
      change (t : ℝ) ≤ ((S.parameterAt kp.succ : ℝ) / 2) at ht_right
      nlinarith
    rw [path_trans_apply_of_le_half p suffix t ht_half]
    have hcenter :
        appendSuffixCenterAt S C k.castSucc = S.centerAt kp.castSucc := by
      rw [hleft, appendSuffixCenterAt_left S C kp.castSucc]
    rw [hcenter]
    exact S.path_segment_mem_model_domain kp
      (unitInterval.doubleOfLeHalf t ht_half) h_lower h_upper
  · by_cases hk_bridge : (k : ℕ) = S.length
    · have hleft :
          (k.castSucc : Fin (S.length + C.length + 2)) =
            (⟨(Fin.last S.length : Fin (S.length + 1)), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        simp [hk_bridge]
      have hright :
          (k.succ : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (0 : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        simp [hk_bridge]
      rw [hleft] at ht_left
      rw [hright] at ht_right
      have hleft_param :
          appendSuffixParameterAt S C
              (⟨(Fin.last S.length : Fin (S.length + 1)), by omega⟩ :
                Fin (S.length + C.length + 2)) =
            unitInterval.firstHalf (S.parameterAt (Fin.last S.length)) := by
        exact appendSuffixParameterAt_left S C (Fin.last S.length)
      have hright_param :
          appendSuffixParameterAt S C
              (⟨S.length + 1 + (0 : ℕ), by omega⟩ :
                Fin (S.length + C.length + 2)) =
            unitInterval.secondHalf (C.parameterAt (0 : Fin (C.length + 1))) := by
        exact appendSuffixParameterAt_right S C (0 : Fin (C.length + 1))
      rw [hleft_param, S.parameterAt_last, unitInterval.firstHalf_one] at ht_left
      rw [hright_param, C.parameterAt_zero, unitInterval.secondHalf_zero] at ht_right
      have hle : (t : ℝ) ≤ 1 / 2 := by simpa using ht_right
      have hge : (1 / 2 : ℝ) ≤ t := by simpa using ht_left
      have ht_half : (t : ℝ) ≤ 1 / 2 := hle
      have ht_double : unitInterval.doubleOfLeHalf t ht_half = 1 := by
        ext
        have ht_eq : (t : ℝ) = 1 / 2 := le_antisymm hle hge
        simp [unitInterval.coe_doubleOfLeHalf, ht_eq]
      rw [path_trans_apply_of_le_half p suffix t ht_half]
      have hcenter :
          appendSuffixCenterAt S C k.castSucc = S.terminalCenter := by
        rw [hleft, appendSuffixCenterAt_left S C (Fin.last S.length)]
        rfl
      rw [hcenter, ht_double]
      simpa using S.terminal_endpoint_mem_domain
    · have hk_suffix : S.length + 1 ≤ (k : ℕ) := by
        omega
      let j : Fin C.length := ⟨(k : ℕ) - (S.length + 1), by omega⟩
      have hleft :
          (k.castSucc : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (j.castSucc : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        change (k : ℕ) = S.length + 1 + ((k : ℕ) - (S.length + 1))
        omega
      have hright :
          (k.succ : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (j.succ : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        change (k : ℕ) + 1 =
          S.length + 1 + (((k : ℕ) - (S.length + 1)) + 1)
        omega
      rw [hleft, appendSuffixParameterAt_right S C j.castSucc] at ht_left
      rw [hright, appendSuffixParameterAt_right S C j.succ] at ht_right
      have ht_half : (1 / 2 : ℝ) ≤ t :=
        le_trans (unitInterval.half_le_secondHalf (C.parameterAt j.castSucc))
          ht_left
      have h_lower :
          (C.parameterAt j.castSucc : ℝ) ≤
            (unitInterval.doubleSubOneOfHalfLe t ht_half : ℝ) := by
        change (C.parameterAt j.castSucc : ℝ) ≤ 2 * (t : ℝ) - 1
        change (1 + (C.parameterAt j.castSucc : ℝ)) / 2 ≤ (t : ℝ) at ht_left
        nlinarith
      have h_upper :
          (unitInterval.doubleSubOneOfHalfLe t ht_half : ℝ) ≤
            (C.parameterAt j.succ : ℝ) := by
        change 2 * (t : ℝ) - 1 ≤ (C.parameterAt j.succ : ℝ)
        change (t : ℝ) ≤ (1 + (C.parameterAt j.succ : ℝ)) / 2 at ht_right
        nlinarith
      rw [path_trans_apply_of_half_le p suffix t ht_half]
      have hcenter :
          appendSuffixCenterAt S C k.castSucc = C.centerAt j.castSucc := by
        rw [hleft, appendSuffixCenterAt_right S C j.castSucc]
      rw [hcenter]
      exact C.path_segment_mem_model_domain j
        (unitInterval.doubleSubOneOfHalfLe t ht_half) h_lower h_upper

omit [RiemannSurface X] in
/-- Transition data for the exact append of a suffix skeleton. -/
noncomputable def appendSuffixTransitionAt
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    ∀ k : Fin (S.length + C.length + 1),
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (appendSuffixCenterAt S C k.castSucc))
        (localModels.chartAt (appendSuffixCenterAt S C k.succ))
        ((p.trans suffix) (appendSuffixParameterAt S C k.succ)) := by
  intro k
  by_cases hk_left : (k : ℕ) < S.length
  · let kp : Fin S.length := ⟨k, hk_left⟩
    have hleft :
        (k.castSucc : Fin (S.length + C.length + 2)) =
          (⟨(kp.castSucc : Fin (S.length + 1)), by omega⟩ :
            Fin (S.length + C.length + 2)) := by
      ext
      rfl
    have hright :
        (k.succ : Fin (S.length + C.length + 2)) =
          (⟨(kp.succ : Fin (S.length + 1)), by omega⟩ :
            Fin (S.length + C.length + 2)) := by
      ext
      rfl
    have hU :
        localModels.chartAt (appendSuffixCenterAt S C k.castSucc) =
          localModels.chartAt (S.centerAt kp.castSucc) := by
      rw [hleft, appendSuffixCenterAt_left S C kp.castSucc]
    have hV :
        localModels.chartAt (appendSuffixCenterAt S C k.succ) =
          localModels.chartAt (S.centerAt kp.succ) := by
      rw [hright, appendSuffixCenterAt_left S C kp.succ]
    have hx :
        (p.trans suffix) (appendSuffixParameterAt S C k.succ) =
          p (S.parameterAt kp.succ) := by
      rw [hright, appendSuffixParameterAt_left S C kp.succ]
      exact path_trans_firstHalf_apply p suffix (S.parameterAt kp.succ)
    exact localRealMobiusTransitionData_congr hU hV hx (S.transitionAt kp)
  · by_cases hk_bridge : (k : ℕ) = S.length
    · have hleft :
          (k.castSucc : Fin (S.length + C.length + 2)) =
            (⟨(Fin.last S.length : Fin (S.length + 1)), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        simp [hk_bridge]
      have hright :
          (k.succ : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (0 : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        simp [hk_bridge]
      have hU :
          localModels.chartAt (appendSuffixCenterAt S C k.castSucc) =
            localModels.chartAt S.terminalCenter := by
        rw [hleft, appendSuffixCenterAt_left S C (Fin.last S.length)]
        rfl
      have hV :
          localModels.chartAt (appendSuffixCenterAt S C k.succ) =
            localModels.chartAt (C.centerAt 0) := by
        rw [hright]
        simp [appendSuffixCenterAt]
      have hx :
          (p.trans suffix) (appendSuffixParameterAt S C k.succ) = x₁ := by
        rw [hright]
        simp [appendSuffixParameterAt, C.parameterAt_zero]
        have hhalf :
            (⟨(2 : ℝ)⁻¹, by norm_num⟩ : unitInterval) =
              unitInterval.secondHalf (0 : unitInterval) := by
          ext
          norm_num [unitInterval.secondHalf]
        rw [hhalf]
        simpa [suffix.source] using
          path_trans_secondHalf_apply p suffix (0 : unitInterval)
      exact localRealMobiusTransitionData_congr hU hV hx A
    · let j : Fin C.length := ⟨(k : ℕ) - (S.length + 1), by omega⟩
      have hleft :
          (k.castSucc : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (j.castSucc : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        change (k : ℕ) = S.length + 1 + ((k : ℕ) - (S.length + 1))
        omega
      have hright :
          (k.succ : Fin (S.length + C.length + 2)) =
            (⟨S.length + 1 + (j.succ : ℕ), by omega⟩ :
              Fin (S.length + C.length + 2)) := by
        ext
        change (k : ℕ) + 1 =
          S.length + 1 + (((k : ℕ) - (S.length + 1)) + 1)
        omega
      have hU :
          localModels.chartAt (appendSuffixCenterAt S C k.castSucc) =
            localModels.chartAt (C.centerAt j.castSucc) := by
        rw [hleft, appendSuffixCenterAt_right S C j.castSucc]
      have hV :
          localModels.chartAt (appendSuffixCenterAt S C k.succ) =
            localModels.chartAt (C.centerAt j.succ) := by
        rw [hright, appendSuffixCenterAt_right S C j.succ]
      have hx :
          (p.trans suffix) (appendSuffixParameterAt S C k.succ) =
            suffix (C.parameterAt j.succ) := by
        rw [hright, appendSuffixParameterAt_right S C j.succ]
        exact path_trans_secondHalf_apply p suffix (C.parameterAt j.succ)
      exact localRealMobiusTransitionData_congr hU hV hx (C.transitionAt j)

omit [RiemannSurface X] in
/--
Append a subdivided suffix skeleton to a prefix skeleton over the exact
concatenated path `p.trans suffix`.

The construction keeps the prefix subdivision, inserts one midpoint bridge
transition into the first chart of the suffix skeleton, and then follows the
suffix skeleton's subdivision on the second half of the concatenated path.
-/
noncomputable def appendSuffixSkeleton
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
      (p.trans suffix) where
  length := S.length + C.length + 1
  length_pos := by omega
  parameterAt := appendSuffixParameterAt S C
  parameterAt_zero := appendSuffixParameterAt_zero S C
  parameterAt_last := appendSuffixParameterAt_last S C
  parameterAt_mono := appendSuffixParameterAt_mono S C
  centerAt := appendSuffixCenterAt S C
  sample_mem_model_domain := appendSuffix_sample_mem_model_domain S C
  path_segment_mem_model_domain :=
    appendSuffix_path_segment_mem_model_domain S C
  terminal_endpoint_mem_domain := by
    simpa [appendSuffixCenterAt_last S C] using
      C.terminal_endpoint_mem_domain
  transitionAt := appendSuffixTransitionAt S C A
  initialTransition := by
    have hV :
        localModels.chartAt (appendSuffixCenterAt S C 0) =
          localModels.chartAt (S.centerAt 0) := by
      rw [appendSuffixCenterAt_zero S C]
    exact localRealMobiusTransitionData_congr rfl hV rfl S.initialTransition

omit [RiemannSurface X] in
/--
%%handwave
name: Exact suffix append ends in the suffix terminal chart
statement: Appending a subdivided suffix skeleton $C$ to a prefix skeleton produces a skeleton whose terminal center is the terminal center of $C$.
proof: The last combined vertex is the last suffix vertex.
-/
@[simp]
theorem appendSuffixSkeleton_terminalCenter
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    (S.appendSuffixSkeleton C A).terminalCenter = C.terminalCenter := by
  simp [appendSuffixSkeleton, terminalCenter]

omit [RiemannSurface X] in
/--
%%handwave
name: Prefix handoff representatives in an exact suffix append
statement: Every handoff belonging to the prefix block retains its original representative after exact suffix append.
proof: The transition construction transports the prefix transition data without changing representatives.
-/
@[simp]
theorem appendSuffixSkeleton_transitionAt_prefix_representative
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁)
    (k : Fin S.length) :
    ((S.appendSuffixSkeleton C A).transitionAt
        (⟨(k : ℕ), by omega⟩ : Fin (S.length + C.length + 1))).representative =
      (S.transitionAt k).representative := by
  simp [appendSuffixSkeleton, appendSuffixTransitionAt, k.isLt]

omit [RiemannSurface X] in
/--
%%handwave
name: Bridge representative in an exact suffix append
statement: The handoff between the prefix terminal chart and the first suffix chart has the prescribed bridge representative $A$.
proof: The bridge case of the transition construction uses the supplied transition data.
-/
@[simp]
theorem appendSuffixSkeleton_transitionAt_bridge_representative
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    ((S.appendSuffixSkeleton C A).transitionAt
        (⟨S.length, by omega⟩ : Fin (S.length + C.length + 1))).representative =
      A.representative := by
  simp [appendSuffixSkeleton, appendSuffixTransitionAt]

omit [RiemannSurface X] in
/--
%%handwave
name: Suffix handoff representatives in an exact append
statement: Every internal suffix handoff retains its original representative after exact append, with the prefix offset added to its index.
proof: In the suffix-index case, the transition construction transports the corresponding suffix transition data unchanged.
-/
@[simp]
theorem appendSuffixSkeleton_transitionAt_suffix_representative
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁)
    (j : Fin C.length) :
    ((S.appendSuffixSkeleton C A).transitionAt
        (⟨S.length + 1 + (j : ℕ), by omega⟩ :
          Fin (S.length + C.length + 1))).representative =
      (C.transitionAt j).representative := by
  have hnot_left : ¬ S.length + 1 + (j : ℕ) < S.length := by omega
  have hnot_bridge : S.length + 1 + (j : ℕ) ≠ S.length := by omega
  have hindex :
      (⟨S.length + 1 + (j : ℕ) - (S.length + 1), by omega⟩ :
        Fin C.length) = j := by
    ext
    simp
  simp [appendSuffixSkeleton, appendSuffixTransitionAt, hnot_left,
    hnot_bridge]
  exact congrArg (fun idx : Fin C.length => (C.transitionAt idx).representative)
    hindex

omit [RiemannSurface X] in
/-- Product of the internal transition representatives of a suffix skeleton. -/
noncomputable def suffixInternalTransitionProduct
    {x₁ y : X} {suffix : Path x₁ y}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    ℕ → RealMobiusRepresentative
  | 0 => 1
  | n + 1 =>
      if hn : n < C.length then
        suffixInternalTransitionProduct C n *
          (C.transitionAt ⟨n, hn⟩).representative⁻¹
      else
        suffixInternalTransitionProduct C n

omit [RiemannSurface X] in
/--
%%handwave
name: Empty internal suffix product
statement: The product of the first zero internal suffix transition inverses is $1$.
proof: This is the zero clause of the recursive product.
-/
@[simp]
theorem suffixInternalTransitionProduct_zero
    {x₁ y : X} {suffix : Path x₁ y}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    suffixInternalTransitionProduct C 0 = 1 :=
  rfl

omit [RiemannSurface X] in
/--
%%handwave
name: Recurrence for the internal suffix transition product
statement: If $n<\ell_C$, then $P_{n+1}=P_nT_n^{-1}$ for the product $P_n$ of the first $n$ internal suffix handoffs.
proof: The index bound selects the multiplication branch of the recursive definition.
-/
theorem suffixInternalTransitionProduct_succ_of_lt
    {x₁ y : X} {suffix : Path x₁ y}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    {n : ℕ} (hn : n < C.length) :
    suffixInternalTransitionProduct C (n + 1) =
      suffixInternalTransitionProduct C n *
        (C.transitionAt ⟨n, hn⟩).representative⁻¹ := by
  simp [suffixInternalTransitionProduct, hn]

omit [RiemannSurface X] in
/--
The accumulated representative of a suffix skeleton is its initial handoff
followed by the internal transition product.

%%handwave
name: Factorization of accumulated representatives into initial and internal parts
statement: For every $n\le\ell_C$, the accumulated representative of a suffix skeleton is $M_n=T_0^{-1}P_n$, where $T_0$ is its initial transition and $P_n$ is the product of the first $n$ internal transition inverses.
proof: Induct on $n$. The zero case is $T_0^{-1}1$; the successor case follows by the recurrences for $M_n$ and $P_n$ and associativity.
-/
theorem accumulatedMobiusNat_eq_initial_mul_suffixInternalTransitionProduct
    {x₁ y : X} {suffix : Path x₁ y}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    ∀ n : ℕ, n ≤ C.length →
      C.accumulatedMobiusNat n =
        C.initialTransition.representative⁻¹ *
          suffixInternalTransitionProduct C n := by
  intro n hn
  induction n with
  | zero =>
      simp [suffixInternalTransitionProduct]
  | succ n ih =>
      have hnlt : n < C.length := Nat.succ_le_iff.mp hn
      have hnle : n ≤ C.length := Nat.le_of_lt hnlt
      rw [C.accumulatedMobiusNat_succ_of_lt hnlt, ih hnle,
        suffixInternalTransitionProduct_succ_of_lt C hnlt]
      simp [mul_assoc]

omit [RiemannSurface X] in
/--
Terminal form of
`accumulatedMobiusNat_eq_initial_mul_suffixInternalTransitionProduct`.

%%handwave
name: Factorization of the terminal suffix representative
statement: For a suffix skeleton of length $\ell$, its terminal representative is $M_{\mathrm{term}}=T_0^{-1}P_\ell$.
proof: Specialize the accumulated-factorization formula to the terminal index $\ell$.
-/
theorem terminalMobius_eq_initial_mul_suffixInternalTransitionProduct
    {x₁ y : X} {suffix : Path x₁ y}
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix) :
    C.terminalMobius =
      C.initialTransition.representative⁻¹ *
        suffixInternalTransitionProduct C C.length := by
  simpa [terminalMobius] using
    accumulatedMobiusNat_eq_initial_mul_suffixInternalTransitionProduct
      C C.length le_rfl

omit [RiemannSurface X] in
/-- On the prefix part, exact append has the same accumulated Mobius product.

%%handwave
name: Exact suffix append preserves prefix accumulated products
statement: If $S*C$ denotes exact append, then $M_n(S*C)=M_n(S)$ for every $n\le\ell_S$.
proof: Induct on $n$ using the unchanged initial transition and prefix handoff representatives.
-/
theorem appendSuffixSkeleton_accumulatedMobiusNat_eq_prefix_of_le
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    ∀ n : ℕ, n ≤ S.length →
      (S.appendSuffixSkeleton C A).accumulatedMobiusNat n =
        S.accumulatedMobiusNat n := by
  intro n hn
  induction n with
  | zero =>
      simp [appendSuffixSkeleton, accumulatedMobiusNat]
  | succ n ih =>
      have hnlt : n < S.length := Nat.succ_le_iff.mp hn
      have hnle : n ≤ S.length := Nat.le_of_lt hnlt
      let App := S.appendSuffixSkeleton C A
      have hAppStep :
          App.accumulatedMobiusNat (n + 1) =
            App.accumulatedMobiusNat n *
              (App.transitionAt
                ⟨n, by change n < S.length + C.length + 1; omega⟩).representative⁻¹ :=
        App.accumulatedMobiusNat_succ_of_lt
          (by change n < S.length + C.length + 1; omega)
      have hSStep :
          S.accumulatedMobiusNat (n + 1) =
            S.accumulatedMobiusNat n *
              (S.transitionAt ⟨n, hnlt⟩).representative⁻¹ :=
        S.accumulatedMobiusNat_succ_of_lt hnlt
      have htrans :
          (App.transitionAt
              ⟨n, by change n < S.length + C.length + 1; omega⟩).representative =
            (S.transitionAt ⟨n, hnlt⟩).representative := by
        simpa [App] using
          appendSuffixSkeleton_transitionAt_prefix_representative
            S C A (⟨n, hnlt⟩ : Fin S.length)
      rw [hAppStep, ih hnle, htrans, hSStep]

omit [RiemannSurface X] in
/-- Accumulated Mobius immediately after the exact-append bridge transition.

%%handwave
name: Accumulated representative immediately after the suffix bridge
statement: If $A$ is the bridge transition, then immediately after crossing it the combined accumulated representative is $M_{\ell_S}(S)A^{-1}$.
proof: The accumulation through the prefix equals the prefix terminal product, and the next update multiplies by the inverse bridge representative.
-/
theorem appendSuffixSkeleton_accumulatedMobiusNat_bridge
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    (S.appendSuffixSkeleton C A).accumulatedMobiusNat (S.length + 1) =
      S.terminalMobius * A.representative⁻¹ := by
  let App := S.appendSuffixSkeleton C A
  have hstep :
      App.accumulatedMobiusNat (S.length + 1) =
        App.accumulatedMobiusNat S.length *
          (App.transitionAt
            ⟨S.length, by change S.length < S.length + C.length + 1; omega⟩).representative⁻¹ :=
    App.accumulatedMobiusNat_succ_of_lt
      (by change S.length < S.length + C.length + 1; omega)
  have hprefix :
      App.accumulatedMobiusNat S.length = S.terminalMobius := by
    simpa [App, terminalMobius] using
      appendSuffixSkeleton_accumulatedMobiusNat_eq_prefix_of_le
        S C A S.length le_rfl
  have hbridge :
      (App.transitionAt
          ⟨S.length, by change S.length < S.length + C.length + 1; omega⟩).representative =
        A.representative := by
    change
      ((S.appendSuffixSkeleton C A).transitionAt
          ⟨S.length, by change S.length < S.length + C.length + 1; omega⟩).representative =
        A.representative
    exact appendSuffixSkeleton_transitionAt_bridge_representative S C A
  rw [hstep, hprefix, hbridge]

omit [RiemannSurface X] in
/--
After `m` suffix transitions, the exact append accumulation is the prefix
terminal product, the bridge transition, and the first `m` internal suffix
transitions.

%%handwave
name: Accumulated representative along the appended suffix
statement: After the bridge and the first $m$ suffix handoffs, the combined representative is $M_{\mathrm{term}}(S)A^{-1}P_m(C)$.
proof: Induct on $m$. The base case is the bridge formula; each successor multiplies by the inverse of the next unchanged suffix transition representative.
-/
theorem appendSuffixSkeleton_accumulatedMobiusNat_suffixProduct
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    ∀ m : ℕ, m ≤ C.length →
      (S.appendSuffixSkeleton C A).accumulatedMobiusNat (S.length + 1 + m) =
        (S.terminalMobius * A.representative⁻¹) *
          suffixInternalTransitionProduct C m := by
  intro m hm
  induction m with
  | zero =>
      simp [appendSuffixSkeleton_accumulatedMobiusNat_bridge S C A]
  | succ m ih =>
      have hmlt : m < C.length := Nat.succ_le_iff.mp hm
      have hmle : m ≤ C.length := Nat.le_of_lt hmlt
      let App := S.appendSuffixSkeleton C A
      have hstep :
          App.accumulatedMobiusNat (S.length + 1 + (m + 1)) =
            App.accumulatedMobiusNat (S.length + 1 + m) *
              (App.transitionAt
                (⟨S.length + 1 + m, by omega⟩ :
                  Fin (S.length + C.length + 1))).representative⁻¹ := by
        have hsucc :
            S.length + 1 + (m + 1) = S.length + 1 + m + 1 := by omega
        rw [hsucc]
        exact App.accumulatedMobiusNat_succ_of_lt
          (by change S.length + 1 + m < S.length + C.length + 1; omega)
      have htrans :
          (App.transitionAt
              (⟨S.length + 1 + m, by omega⟩ :
                Fin (S.length + C.length + 1))).representative =
            (C.transitionAt ⟨m, hmlt⟩).representative := by
        simpa [App] using
          appendSuffixSkeleton_transitionAt_suffix_representative
            S C A (⟨m, hmlt⟩ : Fin C.length)
      rw [hstep, ih hmle, htrans,
        suffixInternalTransitionProduct_succ_of_lt C hmlt]
      simp [mul_assoc]

omit [RiemannSurface X] in
/-- Terminal Mobius formula for exact append.

%%handwave
name: Terminal representative of an exact suffix append
statement: If a prefix skeleton $S$ is joined to a suffix skeleton $C$ through bridge representative $A$, then $M_{\mathrm{term}}(S*C)=M_{\mathrm{term}}(S)A^{-1}P_{\ell_C}(C)$.
proof: Specialize the accumulation formula along the appended suffix to all $\ell_C$ internal suffix handoffs.
-/
theorem appendSuffixSkeleton_terminalMobius_eq
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    (S.appendSuffixSkeleton C A).terminalMobius =
      (S.terminalMobius * A.representative⁻¹) *
        suffixInternalTransitionProduct C C.length := by
  have hidx : S.length + 1 + C.length = S.length + C.length + 1 := by
    omega
  simpa [terminalMobius, appendSuffixSkeleton, hidx, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    appendSuffixSkeleton_accumulatedMobiusNat_suffixProduct
      S C A C.length le_rfl

omit [RiemannSurface X] in
/--
On the prefix part, the internal transition product of an exact append is the
prefix internal transition product.

%%handwave
name: Internal product of an exact append on its prefix
statement: Through any $n\le\ell_S$ prefix handoffs, the internal transition product of the combined skeleton equals $P_n(S)$.
proof: Induct on $n$ using equality of the prefix handoff representatives in the appended skeleton.
-/
theorem suffixInternalTransitionProduct_appendSuffixSkeleton_eq_prefix_of_le
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    ∀ n : ℕ, n ≤ S.length →
      suffixInternalTransitionProduct (S.appendSuffixSkeleton C A) n =
        suffixInternalTransitionProduct S n := by
  intro n hn
  induction n with
  | zero =>
      simp [suffixInternalTransitionProduct]
  | succ n ih =>
      have hnlt : n < S.length := Nat.succ_le_iff.mp hn
      have hnle : n ≤ S.length := Nat.le_of_lt hnlt
      let App := S.appendSuffixSkeleton C A
      have hAppStep :
          suffixInternalTransitionProduct App (n + 1) =
            suffixInternalTransitionProduct App n *
              (App.transitionAt
                ⟨n, by change n < S.length + C.length + 1; omega⟩).representative⁻¹ :=
        suffixInternalTransitionProduct_succ_of_lt App
          (by change n < S.length + C.length + 1; omega)
      have hSStep :
          suffixInternalTransitionProduct S (n + 1) =
            suffixInternalTransitionProduct S n *
              (S.transitionAt ⟨n, hnlt⟩).representative⁻¹ :=
        suffixInternalTransitionProduct_succ_of_lt S hnlt
      have htrans :
          (App.transitionAt
              ⟨n, by change n < S.length + C.length + 1; omega⟩).representative =
            (S.transitionAt ⟨n, hnlt⟩).representative := by
        simpa [App] using
          appendSuffixSkeleton_transitionAt_prefix_representative
            S C A (⟨n, hnlt⟩ : Fin S.length)
      rw [hAppStep, ih hnle, htrans, hSStep]

omit [RiemannSurface X] in
/--
Internal transition product immediately after the exact-append bridge.

%%handwave
name: Internal product immediately after the suffix bridge
statement: Immediately after the bridge transition $A$, the combined internal product is $P_{\ell_S}(S)A^{-1}$.
proof: The internal product through the prefix is unchanged, and the bridge recurrence appends $A^{-1}$.
-/
theorem suffixInternalTransitionProduct_appendSuffixSkeleton_bridge
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    suffixInternalTransitionProduct (S.appendSuffixSkeleton C A) (S.length + 1) =
      suffixInternalTransitionProduct S S.length * A.representative⁻¹ := by
  let App := S.appendSuffixSkeleton C A
  have hstep :
      suffixInternalTransitionProduct App (S.length + 1) =
        suffixInternalTransitionProduct App S.length *
          (App.transitionAt
            ⟨S.length, by change S.length < S.length + C.length + 1; omega⟩).representative⁻¹ :=
    suffixInternalTransitionProduct_succ_of_lt App
      (by change S.length < S.length + C.length + 1; omega)
  have hprefix :
      suffixInternalTransitionProduct App S.length =
        suffixInternalTransitionProduct S S.length :=
    suffixInternalTransitionProduct_appendSuffixSkeleton_eq_prefix_of_le
      S C A S.length le_rfl
  have hbridge :
      (App.transitionAt
          ⟨S.length, by change S.length < S.length + C.length + 1; omega⟩).representative =
        A.representative := by
    change
      ((S.appendSuffixSkeleton C A).transitionAt
          ⟨S.length, by change S.length < S.length + C.length + 1; omega⟩).representative =
        A.representative
    exact appendSuffixSkeleton_transitionAt_bridge_representative S C A
  rw [hstep, hprefix, hbridge]

omit [RiemannSurface X] in
/--
After `m` suffix transitions, the internal transition product of an exact
append factors as prefix product, bridge transition, and the first `m`
internal suffix transitions.

%%handwave
name: Internal transition product along the appended suffix
statement: After $m$ internal suffix handoffs, the combined internal product is $P_{\ell_S}(S)A^{-1}P_m(C)$.
proof: Induct on $m$, starting from the bridge formula and appending each unchanged suffix transition inverse.
-/
theorem suffixInternalTransitionProduct_appendSuffixSkeleton_suffixProduct
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    ∀ m : ℕ, m ≤ C.length →
      suffixInternalTransitionProduct (S.appendSuffixSkeleton C A)
          (S.length + 1 + m) =
        (suffixInternalTransitionProduct S S.length * A.representative⁻¹) *
          suffixInternalTransitionProduct C m := by
  intro m hm
  induction m with
  | zero =>
      simp [suffixInternalTransitionProduct_appendSuffixSkeleton_bridge S C A]
  | succ m ih =>
      have hmlt : m < C.length := Nat.succ_le_iff.mp hm
      have hmle : m ≤ C.length := Nat.le_of_lt hmlt
      let App := S.appendSuffixSkeleton C A
      have hstep :
          suffixInternalTransitionProduct App (S.length + 1 + (m + 1)) =
            suffixInternalTransitionProduct App (S.length + 1 + m) *
              (App.transitionAt
                (⟨S.length + 1 + m, by omega⟩ :
                  Fin (S.length + C.length + 1))).representative⁻¹ := by
        have hsucc :
            S.length + 1 + (m + 1) = S.length + 1 + m + 1 := by omega
        rw [hsucc]
        exact suffixInternalTransitionProduct_succ_of_lt App
          (by change S.length + 1 + m < S.length + C.length + 1; omega)
      have htrans :
          (App.transitionAt
              (⟨S.length + 1 + m, by omega⟩ :
                Fin (S.length + C.length + 1))).representative =
            (C.transitionAt ⟨m, hmlt⟩).representative := by
        simpa [App] using
          appendSuffixSkeleton_transitionAt_suffix_representative
            S C A (⟨m, hmlt⟩ : Fin C.length)
      rw [hstep, ih hmle, htrans,
        suffixInternalTransitionProduct_succ_of_lt C hmlt]
      simp [mul_assoc]

omit [RiemannSurface X] in
/-- Terminal internal transition product formula for exact append.

%%handwave
name: Terminal internal product of an exact suffix append
statement: The complete internal transition product of $S*C$ is $P_{\ell_S}(S)A^{-1}P_{\ell_C}(C)$.
proof: Specialize the suffix-product factorization to all internal handoffs of $C$.
-/
theorem suffixInternalTransitionProduct_appendSuffixSkeleton_terminal
    {x₁ y : X} {p : Path x₀ x₁} {suffix : Path x₁ y}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (C : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels suffix)
    (A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (C.centerAt 0))
        x₁) :
    suffixInternalTransitionProduct (S.appendSuffixSkeleton C A)
        (S.appendSuffixSkeleton C A).length =
      (suffixInternalTransitionProduct S S.length * A.representative⁻¹) *
        suffixInternalTransitionProduct C C.length := by
  have hidx : S.length + 1 + C.length = (S.appendSuffixSkeleton C A).length := by
    simp [appendSuffixSkeleton]
    omega
  rw [← hidx]
  exact
    suffixInternalTransitionProduct_appendSuffixSkeleton_suffixProduct
      S C A C.length le_rfl

omit [RiemannSurface X] in
/--
Exact append is associative at the level of terminal values.

The two skeletons live over differently parenthesized concatenated paths, but
their terminal chart and accumulated Mobius product agree.  This discharges
the purely algebraic part of cut reparameterization; subpath merging is a
separate geometric boundary.

%%handwave
name: Associativity of exact suffix append for terminal values
statement: Given compatible skeletons $S,C,D$ and bridge transitions, the skeletons formed as $(S*C)*D$ and $S*(C*D)$ have equal terminal values, even though their underlying concatenated paths have different parentheses.
proof: Expand both terminal representatives using the exact-append product formula. Expand the internal product of $C*D$ into the product for $C$, its bridge, and the product for $D$; associativity makes the representatives equal. Both constructions end in the terminal chart of $D$.
-/
theorem appendSuffixSkeleton_assoc_terminalValue_eq
    {x₁ x₂ x₃ : X} {p : Path x₀ x₁} {q : Path x₁ x₂}
    {r : Path x₂ x₃}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (Q : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels q)
    (R : PathLocalTransitionModelBasedWeakHandoffSkeleton x₂ g localModels r)
    (ASQ :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (Q.centerAt 0))
        x₁)
    (AQR :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt Q.terminalCenter)
        (localModels.chartAt (R.centerAt 0))
        x₂) :
    ∃ (ASQ_R :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt
              ((S.appendSuffixSkeleton Q ASQ).terminalCenter))
            (localModels.chartAt (R.centerAt 0))
            x₂)
      (AS_QR :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt S.terminalCenter)
            (localModels.chartAt
              ((Q.appendSuffixSkeleton R AQR).centerAt 0))
            x₁),
      (((S.appendSuffixSkeleton Q ASQ).appendSuffixSkeleton R ASQ_R).terminalValue =
        (S.appendSuffixSkeleton (Q.appendSuffixSkeleton R AQR) AS_QR).terminalValue) := by
  classical
  let SQ := S.appendSuffixSkeleton Q ASQ
  let QR := Q.appendSuffixSkeleton R AQR
  let ASQ_R :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt SQ.terminalCenter)
        (localModels.chartAt (R.centerAt 0))
        x₂ :=
    localRealMobiusTransitionData_congr
      (by simp [SQ]) rfl rfl AQR
  let AS_QR :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (QR.centerAt 0))
        x₁ :=
    localRealMobiusTransitionData_congr
      rfl
      (by
        change
          localModels.chartAt (appendSuffixCenterAt Q R 0) =
            localModels.chartAt (Q.centerAt 0)
        rw [appendSuffixCenterAt_zero Q R])
      rfl ASQ
  refine ⟨ASQ_R, AS_QR, ?_⟩
  have hMobius :
      (SQ.appendSuffixSkeleton R ASQ_R).terminalMobius =
        (S.appendSuffixSkeleton QR AS_QR).terminalMobius := by
    rw [appendSuffixSkeleton_terminalMobius_eq SQ R ASQ_R,
      appendSuffixSkeleton_terminalMobius_eq S QR AS_QR,
      appendSuffixSkeleton_terminalMobius_eq S Q ASQ,
      suffixInternalTransitionProduct_appendSuffixSkeleton_terminal Q R AQR]
    simp [SQ, QR, ASQ_R, AS_QR, mul_assoc]
  have hCenter :
      (SQ.appendSuffixSkeleton R ASQ_R).terminalCenter =
        (S.appendSuffixSkeleton QR AS_QR).terminalCenter := by
    simp [SQ, QR]
  change
    realMobiusRepresentativeAction
        (SQ.appendSuffixSkeleton R ASQ_R).terminalMobius
        ((localModels.chartAt
          (SQ.appendSuffixSkeleton R ASQ_R).terminalCenter).toUpperHalfPlane x₃) =
      realMobiusRepresentativeAction
        (S.appendSuffixSkeleton QR AS_QR).terminalMobius
        ((localModels.chartAt
          (S.appendSuffixSkeleton QR AS_QR).terminalCenter).toUpperHalfPlane x₃)
  rw [hMobius, hCenter]

omit [RiemannSurface X] in
/--
Exact append is associative at the level of terminal branch data.

This stronger form can be followed by a common suffix, which is exactly what
the cut-path reassociation bookkeeping needs.

%%handwave
name: Associativity of exact suffix append for terminal branch data
statement: Under the same compatibility hypotheses, $(S*C)*D$ and $S*(C*D)$ have the same terminal chart center and terminal accumulated representative.
proof: Both end in the terminal chart of $D$. The representative calculation is the same factorization-and-associativity argument used for terminal values, now retained as literal equality of terminal branch data.
-/
theorem appendSuffixSkeleton_assoc_terminalBranchDataEq
    {x₁ x₂ x₃ : X} {p : Path x₀ x₁} {q : Path x₁ x₂}
    {r : Path x₂ x₃}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (Q : PathLocalTransitionModelBasedWeakHandoffSkeleton x₁ g localModels q)
    (R : PathLocalTransitionModelBasedWeakHandoffSkeleton x₂ g localModels r)
    (ASQ :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (Q.centerAt 0))
        x₁)
    (AQR :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt Q.terminalCenter)
        (localModels.chartAt (R.centerAt 0))
        x₂) :
    ∃ (ASQ_R :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt
              ((S.appendSuffixSkeleton Q ASQ).terminalCenter))
            (localModels.chartAt (R.centerAt 0))
            x₂)
      (AS_QR :
          HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt S.terminalCenter)
            (localModels.chartAt
              ((Q.appendSuffixSkeleton R AQR).centerAt 0))
            x₁),
      TerminalBranchDataEq
        ((S.appendSuffixSkeleton Q ASQ).appendSuffixSkeleton R ASQ_R)
        (S.appendSuffixSkeleton (Q.appendSuffixSkeleton R AQR) AS_QR) := by
  classical
  let SQ := S.appendSuffixSkeleton Q ASQ
  let QR := Q.appendSuffixSkeleton R AQR
  let ASQ_R :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt SQ.terminalCenter)
        (localModels.chartAt (R.centerAt 0))
        x₂ :=
    localRealMobiusTransitionData_congr
      (by simp [SQ]) rfl rfl AQR
  let AS_QR :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt (QR.centerAt 0))
        x₁ :=
    localRealMobiusTransitionData_congr
      rfl
      (by
        change
          localModels.chartAt (appendSuffixCenterAt Q R 0) =
            localModels.chartAt (Q.centerAt 0)
        rw [appendSuffixCenterAt_zero Q R])
      rfl ASQ
  refine ⟨ASQ_R, AS_QR, ?_⟩
  constructor
  · simp [SQ, QR]
  · rw [appendSuffixSkeleton_terminalMobius_eq SQ R ASQ_R,
      appendSuffixSkeleton_terminalMobius_eq S QR AS_QR,
      appendSuffixSkeleton_terminalMobius_eq S Q ASQ,
      suffixInternalTransitionProduct_appendSuffixSkeleton_terminal Q R AQR]
    simp [SQ, QR, ASQ_R, AS_QR, mul_assoc]

end PathLocalTransitionModelBasedWeakHandoffSkeleton

end HyperbolicMetric

end

end JJMath
