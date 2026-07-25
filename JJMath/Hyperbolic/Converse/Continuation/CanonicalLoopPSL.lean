import JJMath.Hyperbolic.Converse.Continuation.TerminalSheetPSL

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Local terminal-sheet overlap is enough for normalized canonical-loop transport
on a preconnected overlap of the two fixed loop terminal charts.

This removes the artificial requirement that terminal-sheet extension keep the
same selected terminal chart.  Source and target terminal extensions are
compared by the adjusted PSL transition forced by agreement of the two
terminal formulae on an upstairs open sheet overlap.

%%handwave
name: Local constancy of normalized loop transport from terminal-sheet overlap
statement: Let $p:x_0\rightsquigarrow x$, let $\gamma\in\pi_1(X,x_0)$, and let $L_\gamma$ represent $\gamma^{-1}$. If $y$ lies in the terminal sheet for $p$ and $\gamma y$ lies in the terminal sheet for $L_\gamma*p$, and if a preconnected set $W$ contains $x$ and $\pi(y)$ inside the overlap of the two original terminal charts, then $N_\gamma(y)=N_\gamma(\widetilde p(1))$. No equality of the terminal charts selected after extending the paths is required.
proof: Extend $p$ and $L_\gamma*p$ to paths $q$ and $r$ representing $y$ and $\gamma y$. Compare the four terminal charts by transition data: from $p$ to $q$, from $L_\gamma*p$ to $r$, from $L_\gamma*q$ to $r$, and from $q$ to $L_\gamma*q$. Constancy on $W$ identifies the direct transition at $\pi(y)$ with the one at $x$, while transition composition gives the cocycle identity $d a_q b=c a_p$. Agreement of the developing formula on each terminal-sheet overlap gives $m_Qb=m_S$ and $m_Rc=m_T$, and homotopy of $L_\gamma*q$ with $r$ gives $m_Rd=m_{LQ}$. These identities reduce $m_{LQ}a_qm_Q^{-1}$ to $m_Ta_pm_S^{-1}$, which is precisely the desired equality of normalized projections.
%%
-/
theorem canonicalLoopNormalizedProjectionAt_eq_of_preconnectedOverlap_of_terminalSheetOverlap
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
    (y : PathHomotopyUniversalCover X x₀)
    (hy : y ∈ (C.basedWeakHandoffAlong p).terminalSheet)
    (hdeck :
      PathHomotopyUniversalCover.deckAction γ y ∈
        (C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)).terminalSheet)
    (W : Set X) (hWpre : IsPreconnected W)
    (hxW : x ∈ W) (hyW : PathHomotopyUniversalCover.endpoint y ∈ W)
    (hWsub :
      W ⊆
        (localModels.chartAt
            ((C.basedWeakHandoffAlong p).terminalCenter)).domain ∩
          (localModels.chartAt
            ((C.basedWeakHandoffAlong
              ((C.canonicalLoopFor γ).trans p)).terminalCenter)).domain) :
    C.canonicalLoopNormalizedProjectionAt γ y =
      C.canonicalLoopNormalizedProjectionAt γ
        (C.basedWeakHandoffAlong p).terminalCoverPoint := by
  classical
  let L := C.canonicalLoopFor γ
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (L.trans p)
  let σ := S.terminalSheetPathInSet hy
  let q : Path x₀ (PathHomotopyUniversalCover.endpoint y) := p.trans σ
  let τ := T.terminalSheetPathInSet
    (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck
  let r : Path x₀ (PathHomotopyUniversalCover.endpoint y) := (L.trans p).trans τ
  let Lq : Path x₀ (PathHomotopyUniversalCover.endpoint y) := L.trans q
  let Q := C.basedWeakHandoffAlong q
  let R := C.basedWeakHandoffAlong r
  let LQ := C.basedWeakHandoffAlong Lq
  have hqClass :
      Path.Homotopic.Quotient.mk q =
        PathHomotopyUniversalCover.pathClass y := by
    simpa [q, σ, S] using
      (S.pathClass_eq_mk_path_trans_terminalSheetPathInSet_of_mem_terminalSheet
        hy).symm
  have hyPoint :
      (⟨PathHomotopyUniversalCover.endpoint y,
          Path.Homotopic.Quotient.mk q⟩ :
        PathHomotopyUniversalCover X x₀) = y := by
    cases y with
    | mk y qy =>
        exact Sigma.ext rfl (heq_of_eq hqClass)
  have hAtY :
      C.canonicalLoopNormalizedProjectionAt γ y =
        C.canonicalLoopNormalizedTerminalProjection γ q := by
    simpa [hyPoint] using C.canonicalLoopNormalizedProjectionAt_mk γ q
  have hAtBase :
      C.canonicalLoopNormalizedProjectionAt γ S.terminalCoverPoint =
        C.canonicalLoopNormalizedTerminalProjection γ p := by
    simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCoverPoint]
      using C.canonicalLoopNormalizedProjectionAt_mk γ p
  have hQpoint : Q.terminalCoverPoint = y := by
    exact Q.terminalCoverPoint_eq_of_mk_eq_pathClass hqClass
  have hyQ : y ∈ Q.terminalSheet := by
    simpa [Q, hQpoint] using Q.terminalCoverPoint_mem_terminalSheet
  have hrClass :
      Path.Homotopic.Quotient.mk r =
        PathHomotopyUniversalCover.pathClass
          (PathHomotopyUniversalCover.deckAction γ y) := by
    simpa [r, τ, T] using
      (T.pathClass_eq_mk_path_trans_terminalSheetPathInSet_of_mem_terminalSheet
        hdeck).symm
  have hRpoint :
      R.terminalCoverPoint = PathHomotopyUniversalCover.deckAction γ y := by
    exact
      R.terminalCoverPoint_eq_of_mk_eq_pathClass
        (y' := PathHomotopyUniversalCover.deckAction γ y)
        (by
          simpa [PathHomotopyUniversalCover.endpoint_deckAction] using hrClass)
  have hdeckR :
      PathHomotopyUniversalCover.deckAction γ y ∈ R.terminalSheet := by
    simpa [R, hRpoint] using R.terminalCoverPoint_mem_terminalSheet
  have hLqClass :
      Path.Homotopic.Quotient.mk Lq =
        PathHomotopyUniversalCover.pathClass
          (PathHomotopyUniversalCover.deckAction γ y) := by
    calc
      Path.Homotopic.Quotient.mk Lq
          =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk L)
          (Path.Homotopic.Quotient.mk q) := by
          simp [Lq, q, Path.Homotopic.Quotient.mk_trans]
      _ =
        Path.Homotopic.Quotient.trans
          (FundamentalGroup.toPath γ⁻¹)
          (PathHomotopyUniversalCover.pathClass y) := by
          rw [C.canonicalLoopFor_spec γ, hqClass]
      _ =
        PathHomotopyUniversalCover.pathClass
          (PathHomotopyUniversalCover.deckAction γ y) := by
          rfl
  have hLq_r : Path.Homotopic Lq r := by
    simpa [Lq, r, τ, T] using
      T.homotopic_to_path_trans_terminalSheetPathInSet_of_mk_eq_pathClass
        hdeck hLqClass
  let B := C.terminalSheetTransitionDataAt p q y hy hyQ
  let Ctr := C.terminalSheetTransitionDataAt (L.trans p) r
    (PathHomotopyUniversalCover.deckAction γ y) hdeck hdeckR
  let D := C.terminalTransitionDataBetween Lq r
  let Aq := C.terminalTransitionDataBetween q Lq
  let Az :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt T.terminalCenter)
        (PathHomotopyUniversalCover.endpoint y) := by
    have hS :
        PathHomotopyUniversalCover.endpoint y ∈
          (localModels.chartAt S.terminalCenter).domain :=
      S.endpoint_mem_terminal_domain_of_mem_terminalSheet hy
    have hT :
        PathHomotopyUniversalCover.endpoint y ∈
          (localModels.chartAt T.terminalCenter).domain := by
      have hTdeck :
          PathHomotopyUniversalCover.endpoint
              (PathHomotopyUniversalCover.deckAction γ y) ∈
            (localModels.chartAt T.terminalCenter).domain :=
        T.endpoint_mem_terminal_domain_of_mem_terminalSheet hdeck
      simpa [PathHomotopyUniversalCover.endpoint_deckAction] using hTdeck
    exact Classical.choice
      (localModels.transition_localRealMobius S.terminalCenter T.terminalCenter
        (PathHomotopyUniversalCover.endpoint y) ⟨hS, hT⟩)
  let Ap := C.terminalTransitionDataBetween p (L.trans p)
  have hWexists :
      ∀ ⦃z : X⦄, z ∈ W →
        Nonempty
          (HyperbolicLocalChart.LocalRealMobiusTransitionData
            (localModels.chartAt S.terminalCenter)
            (localModels.chartAt T.terminalCenter) z) := by
    intro z hz
    have hzOverlap :
        z ∈
          (localModels.chartAt S.terminalCenter).domain ∩
            (localModels.chartAt T.terminalCenter).domain := by
      simpa [S, T, L] using hWsub hz
    exact
      localModels.transition_localRealMobius S.terminalCenter
        T.terminalCenter z hzOverlap
  have hAz :
      realMobiusProjection Az.representative =
        realMobiusProjection Ap.representative :=
    localRealMobiusTransitionData_projection_eq_of_preconnected
      hWpre hWexists hxW hyW Ap Az
  have hSource :
      realMobiusProjection (Q.terminalMobius * B.representative) =
        realMobiusProjection S.terminalMobius := by
    simpa [Q, S, B,
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalSheetTransitionRepresentativeAt]
      using C.terminalSheetTransitionAdjustedProjection_eq_of_mem_inter
        p q y hy hyQ
  have hTarget :
      realMobiusProjection (R.terminalMobius * Ctr.representative) =
        realMobiusProjection T.terminalMobius := by
    simpa [R, T, Ctr,
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalSheetTransitionRepresentativeAt]
      using C.terminalSheetTransitionAdjustedProjection_eq_of_mem_inter
        (L.trans p) r (PathHomotopyUniversalCover.deckAction γ y)
        hdeck hdeckR
  have hHomAdjusted :
      realMobiusProjection (R.terminalMobius * D.representative) =
        realMobiusProjection LQ.terminalMobius := by
    simpa [Lq, r, LQ, R, D,
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween]
      using
        C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
          Lq r hLq_r
  let BAq := localRealMobiusTransitionData_trans B Aq
  let DBAq := localRealMobiusTransitionData_trans BAq D
  let AzCtr := localRealMobiusTransitionData_trans Az Ctr
  have hBAq :
      realMobiusProjection BAq.representative =
        realMobiusProjection (Aq.representative * B.representative) :=
    localRealMobiusTransitionData_projection_eq_trans B Aq BAq
  have hDBAq :
      realMobiusProjection DBAq.representative =
        realMobiusProjection (D.representative * BAq.representative) :=
    localRealMobiusTransitionData_projection_eq_trans BAq D DBAq
  have hAzCtr :
      realMobiusProjection AzCtr.representative =
        realMobiusProjection (Ctr.representative * Az.representative) :=
    localRealMobiusTransitionData_projection_eq_trans Az Ctr AzCtr
  have hDirect :
      realMobiusProjection DBAq.representative =
        realMobiusProjection AzCtr.representative :=
    localRealMobiusTransitionData_projection_eq DBAq AzCtr
  have hCocycle :
      realMobiusProjection D.representative *
          realMobiusProjection Aq.representative *
          realMobiusProjection B.representative =
        realMobiusProjection Ctr.representative *
          realMobiusProjection Az.representative := by
    calc
      realMobiusProjection D.representative *
          realMobiusProjection Aq.representative *
          realMobiusProjection B.representative
          =
        realMobiusProjection D.representative *
          (realMobiusProjection Aq.representative *
            realMobiusProjection B.representative) := by
          simp [mul_assoc]
      _ =
        realMobiusProjection D.representative *
          realMobiusProjection BAq.representative := by
          rw [hBAq]
          simp
      _ =
        realMobiusProjection DBAq.representative := by
          rw [hDBAq]
          simp
      _ =
        realMobiusProjection AzCtr.representative := hDirect
      _ =
        realMobiusProjection Ctr.representative *
          realMobiusProjection Az.representative := by
          rw [hAzCtr]
          simp
  let mS := realMobiusProjection S.terminalMobius
  let mT := realMobiusProjection T.terminalMobius
  let mQ := realMobiusProjection Q.terminalMobius
  let mR := realMobiusProjection R.terminalMobius
  let mLQ := realMobiusProjection LQ.terminalMobius
  let b := realMobiusProjection B.representative
  let c := realMobiusProjection Ctr.representative
  let d := realMobiusProjection D.representative
  let aq := realMobiusProjection Aq.representative
  let az := realMobiusProjection Az.representative
  let ap := realMobiusProjection Ap.representative
  have hSource' : mQ * b = mS := by
    simpa [mQ, b, mS, realMobiusProjection, mul_assoc] using hSource
  have hTarget' : mR * c = mT := by
    simpa [mR, c, mT, realMobiusProjection, mul_assoc] using hTarget
  have hHom' : mR * d = mLQ := by
    simpa [mR, d, mLQ, realMobiusProjection, mul_assoc] using hHomAdjusted
  have hAz' : az = ap := by
    simpa [az, ap] using hAz
  have hCocycle' : d * aq * b = c * az := by
    simpa [d, aq, b, c, az, mul_assoc] using hCocycle
  have hSourceInv : mQ⁻¹ = b * mS⁻¹ := by
    rw [← hSource']
    group
  have hNormalized :
      C.canonicalLoopNormalizedTerminalProjection γ q =
        C.canonicalLoopNormalizedTerminalProjection γ p := by
    calc
      C.canonicalLoopNormalizedTerminalProjection γ q
          = mLQ * aq * mQ⁻¹ := by
          simp [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.canonicalLoopNormalizedTerminalProjection,
            PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween,
            L, q, Lq, Q, LQ, mLQ, aq, mQ, Aq]
      _ = (mR * d) * aq * (b * mS⁻¹) := by
          rw [hHom', hSourceInv]
      _ = mR * (d * aq * b) * mS⁻¹ := by
          group
      _ = mR * (c * az) * mS⁻¹ := by
          rw [hCocycle']
      _ = (mR * c) * az * mS⁻¹ := by
          group
      _ = mT * az * mS⁻¹ := by
          rw [hTarget']
      _ = mT * ap * mS⁻¹ := by
          rw [hAz']
      _ = C.canonicalLoopNormalizedTerminalProjection γ p := by
          simp [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.canonicalLoopNormalizedTerminalProjection,
            PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween,
            L, S, T, mT, ap, mS, Ap]
  calc
    C.canonicalLoopNormalizedProjectionAt γ y
        = C.canonicalLoopNormalizedTerminalProjection γ q := hAtY
    _ = C.canonicalLoopNormalizedTerminalProjection γ p := hNormalized
    _ = C.canonicalLoopNormalizedProjectionAt γ S.terminalCoverPoint :=
        hAtBase.symm

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL


namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Terminal-sheet overlap alone makes the normalized canonical-loop projection
locally constant on the canonical cover.

The proof shrinks around each upstairs point to a local sheet whose base lies
inside the two relevant terminal chart domains.  On that small preconnected
base patch, terminal chart transitions are constant in PSL, while arbitrary
selected terminal-sheet extensions are compared by the adjusted local
terminal-sheet overlap lemma.

%%handwave
name: Terminal-sheet overlap alone makes the normalized canonical-loop projection locally constant on the canonical cover
statement:
  Terminal-sheet overlap alone makes the normalized canonical-loop projection locally constant
  on the canonical cover. The proof shrinks around each upstairs point to a local sheet whose
  base lies inside the two relevant terminal chart domains. On that small preconnected base
  patch, terminal chart transitions are constant in PSL, while arbitrary selected terminal-sheet
  extensions are compared by the adjusted local terminal-sheet overlap lemma.
-/
noncomputable def toLocalConstancyOnCoverDataPSL_of_terminalSheetOverlap
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL
      C where
  canonicalLoopNormalizedProjectionAt_locallyConstant := by
    intro γ
    rw [IsLocallyConstant.iff_exists_open]
    intro y
    let p : Path x₀ (PathHomotopyUniversalCover.endpoint y) :=
      Quot.out (PathHomotopyUniversalCover.pathClass y)
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)
    have hp_class :
        Path.Homotopic.Quotient.mk p =
          PathHomotopyUniversalCover.pathClass y := by
      exact Quot.out_eq (PathHomotopyUniversalCover.pathClass y)
    have hSpoint : S.terminalCoverPoint = y := by
      exact S.terminalCoverPoint_eq_of_mk_eq_pathClass hp_class
    have hTpoint :
        T.terminalCoverPoint =
          PathHomotopyUniversalCover.deckAction γ S.terminalCoverPoint := by
      exact
        S.terminalCoverPoint_loopTrans_eq_deckAction γ
          (C.canonicalLoopFor γ) T (C.canonicalLoopFor_spec γ)
    have hyS : y ∈ S.terminalSheet := by
      simpa [S, hSpoint] using S.terminalCoverPoint_mem_terminalSheet
    have hyTdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈ T.terminalSheet := by
      simpa [T, hSpoint, hTpoint] using T.terminalCoverPoint_mem_terminalSheet
    let N : Set X := S.terminalSheetChart.base ∩ T.terminalSheetChart.base
    have hyN : PathHomotopyUniversalCover.endpoint y ∈ N := by
      refine ⟨?_, ?_⟩
      · simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
          PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
            (x₀ := x₀) hyS
      · have hbase :
            PathHomotopyUniversalCover.endpoint
                (PathHomotopyUniversalCover.deckAction γ y) ∈
              T.terminalSheetChart.base := by
          simpa [T, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
            PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
              (x₀ := x₀) hyTdeck
        simpa [PathHomotopyUniversalCover.endpoint_deckAction] using hbase
    have hN : IsOpen N :=
      S.terminalSheetChart.base_open.inter T.terminalSheetChart.base_open
    let E := PathHomotopyUniversalCover.localSheetChartAtWithin
      (x₀ := x₀) y hyN hN
    have hyE : y ∈ E.sheet :=
      PathHomotopyUniversalCover.localSheetChartAtWithin_mem
        (x₀ := x₀) y hyN hN
    have hEopen : IsOpen E.sheet :=
      PathHomotopyUniversalCover.isOpen_localSheetChart_sheet E
    refine ⟨E.sheet, hEopen, hyE, ?_⟩
    intro z hzE
    have hEbaseN : E.base ⊆ N :=
      PathHomotopyUniversalCover.localSheetChartAtWithin_base_subset
        (x₀ := x₀) y hyN hN
    have hEbaseS : E.base ⊆ S.terminalSheetChart.base := by
      intro w hw
      exact (hEbaseN hw).1
    have hEbaseT : E.base ⊆ T.terminalSheetChart.base := by
      intro w hw
      exact (hEbaseN hw).2
    have hES : E.sheet ⊆ S.terminalSheet :=
      PathHomotopyUniversalCover.localSheetChartAtWithin_sheet_subset_of_mem_localSheet
        (x₀ := x₀) S.terminalSheetChart hyS hyN hN hEbaseS
    let Dγ : PathHomotopyUniversalCover.LocalSheetChart (X := X) x₀ :=
      { T.terminalSheetChart with
        fiberPoint :=
          PathHomotopyUniversalCover.deckActionFiber γ⁻¹
            T.terminalSheetChart.fiberPoint }
    have hyDγ : y ∈ Dγ.sheet := by
      have h :=
        (PathHomotopyUniversalCover.deckAction_mem_localSheet_iff
          (x₀ := x₀) (γ := γ) (a := T.terminalSheetChart.center)
          (η := T.terminalSheetChart.fiberPoint) (y := y)).mp
          (by
            simpa [T, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet,
              PathHomotopyUniversalCover.LocalSheetChart.sheet] using hyTdeck)
      simpa [Dγ, PathHomotopyUniversalCover.LocalSheetChart.sheet] using h
    have hEDγ : E.sheet ⊆ Dγ.sheet :=
      PathHomotopyUniversalCover.localSheetChartAtWithin_sheet_subset_of_mem_localSheet
        (x₀ := x₀) Dγ hyDγ hyN hN (by
          intro w hw
          simpa [Dγ] using hEbaseT hw)
    have hzS : z ∈ S.terminalSheet := hES hzE
    have hzDγ : z ∈ Dγ.sheet := hEDγ hzE
    have hzDeck :
        PathHomotopyUniversalCover.deckAction γ z ∈ T.terminalSheet := by
      have h :=
        (PathHomotopyUniversalCover.deckAction_mem_localSheet_iff
          (x₀ := x₀) (γ := γ) (a := T.terminalSheetChart.center)
          (η := T.terminalSheetChart.fiberPoint) (y := z)).mpr
          (by
            simpa [Dγ, PathHomotopyUniversalCover.LocalSheetChart.sheet] using hzDγ)
      simpa [T, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet,
        PathHomotopyUniversalCover.LocalSheetChart.sheet] using h
    have hWpre : IsPreconnected E.base := by
      have hpre :
          IsPreconnected (Set.univ : Set E.base) := isPreconnected_univ
      have hImage :=
        hpre.image (fun w : E.base => (w : X))
          continuous_subtype_val.continuousOn
      simpa using hImage
    have hxW :
        PathHomotopyUniversalCover.endpoint S.terminalCoverPoint ∈ E.base := by
      simpa [S, hSpoint] using
        PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
          (x₀ := x₀) hyE
    have hzW : PathHomotopyUniversalCover.endpoint z ∈ E.base :=
      PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
        (x₀ := x₀) hzE
    have hWsub :
        E.base ⊆
          (localModels.chartAt S.terminalCenter).domain ∩
            (localModels.chartAt T.terminalCenter).domain := by
      intro w hw
      exact
        ⟨S.terminalSheetChart_base_subset_terminal_domain (hEbaseS hw),
          T.terminalSheetChart_base_subset_terminal_domain (hEbaseT hw)⟩
    have hConst :=
      C.canonicalLoopNormalizedProjectionAt_eq_of_preconnectedOverlap_of_terminalSheetOverlap
        γ p z hzS hzDeck E.base hWpre
        (by
          simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
            using hxW)
        hzW hWsub
    simpa [S, hSpoint] using hConst

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
On the canonical cover, local constancy of the normalized canonical-loop
projection implies global constancy.

%%handwave
name: On the canonical cover, local constancy of the normalized canonical-loop projection implies global constancy
statement:
  On the canonical cover, local constancy of the normalized canonical-loop projection implies
  global constancy.
-/
noncomputable def toConstancyOnCoverDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverDataPSL
      C where
  canonicalLoopNormalizedProjectionAt_eq_base := by
    intro γ y
    exact
      (D.canonicalLoopNormalizedProjectionAt_locallyConstant γ).apply_eq_of_preconnectedSpace
        y (PathHomotopyUniversalCover.baseLift x₀)

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Constancy on the canonical cover gives path-representative normalized
projection propagation from the base normalization path.

%%handwave
name: Constancy on the canonical cover gives path-representative normalized projection propagation from the base normalization path
statement:
  Constancy on the canonical cover gives path-representative normalized projection propagation
  from the base normalization path.
-/
noncomputable def toNormalizedProjectionPropagationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationDataPSL
      C where
  canonicalLoopNormalizedProjection_propagates_from_base :=
    C.canonicalLoopNormalizedProjection_propagates_from_base_of_const_on_cover
      D.canonicalLoopNormalizedProjectionAt_eq_base

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Normalized propagation gives canonical-loop covariance.

%%handwave
name: Normalized propagation gives canonical-loop covariance
statement:
  Normalized propagation gives canonical-loop covariance.
-/
noncomputable def toCanonicalLoopCovarianceDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceDataPSL
      C where
  canonicalLoopTransitionProjection_equivariant :=
    C.canonicalLoopTransitionProjection_equivariant_of_normalizedProjection_propagates_from_base
      D.canonicalLoopNormalizedProjection_propagates_from_base

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Canonical-loop covariance gives the reduced arbitrary-loop covariance
boundary.

%%handwave
name: Canonical-loop covariance gives the reduced arbitrary-loop covariance principle
statement:
  Canonical-loop covariance gives the reduced arbitrary-loop covariance principle.
-/
noncomputable def toReducedDerivedHolonomyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL
      C where
  automaticTerminalTransitionProjection_equivariant :=
    C.automaticTerminalTransitionProjection_equivariant_of_canonicalLoop_covariance
      (fun γ => C.derivedHolonomyProjection γ)
      D.canonicalLoopTransitionProjection_equivariant

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Reduced derived-holonomy data fill the older three-field derived-holonomy
record by supplying the identity law automatically.

%%handwave
name: Reduced derived-holonomy data fill the older three-field derived-holonomy data by supplying the identity law automatically
statement:
  Reduced derived-holonomy data fill the older three-field derived-holonomy data by supplying
  the identity law automatically.
-/
noncomputable def toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL
        C) :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      C where
  derivedHolonomy_one := C.derivedHolonomyProjection_one
  derivedHolonomy_mul :=
    C.derivedHolonomyProjection_mul_of_automaticTerminalTransitionProjection_equivariant
      D.automaticTerminalTransitionProjection_equivariant
  automaticTerminalTransitionProjection_equivariant :=
    D.automaticTerminalTransitionProjection_equivariant

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Deck equivariance of the single-valued upstairs map gives PSL loop
equivariance of terminal values.

%%handwave
name: Deck equivariance of the single-valued upstairs map gives PSL loop equivariance of terminal values
statement:
  Deck equivariance of the single-valued upstairs map gives PSL loop equivariance of terminal
  values.
-/
noncomputable def toCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL
      C.toCanonicalSheetAnalyticContinuationValueData where
  holonomy := C.holonomy
  terminal_path_equivariant := by
    intro γ loop x p hloop
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (loop.trans p)
    have hT :
        T.terminalCoverPoint =
          (canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint :=
      PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCoverPoint_loopTrans_eq_deckAction
        γ loop S T hloop
    calc
      (C.toCanonicalSheetAnalyticContinuationValueData).terminalValue
          (loop.trans p) =
          C.dev T.terminalCoverPoint := by
            simpa [PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData.terminalValue,
              T] using C.terminalValue_eq_dev_terminalCoverPoint (loop.trans p)
      _ = C.dev ((canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint) := by
            rw [hT]
      _ = C.holonomy.upperHalfPlaneAction γ (C.dev S.terminalCoverPoint) := by
            exact C.dev_equivariant γ S.terminalCoverPoint
      _ = C.holonomy.upperHalfPlaneAction γ
            ((C.toCanonicalSheetAnalyticContinuationValueData).terminalValue p) := by
            simpa [PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData.terminalValue,
              S] using
              congrArg (C.holonomy.upperHalfPlaneAction γ)
                (C.terminalValue_eq_dev_terminalCoverPoint p).symm

/--
Cover-level PSL continuation directly gives PSL path-class monodromy through
the canonical-terminal-sheet route.

%%handwave
name: Cover-level PSL continuation directly gives PSL path-class monodromy through the canonical-terminal-sheet route
statement:
  Cover-level PSL continuation directly gives PSL path-class monodromy through the
  canonical-terminal-sheet route.
-/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  C.toCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL
    |>.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL

/--
PSL monodromy data for canonical-terminal-sheet agreement, with the
single-valued upstairs map constructed from the stored path class.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Terminal-sheet agreement data. -/
  agreementContinuation :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels
  /-- PSL-valued real holonomy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Deck transformations act through PSL holonomy on the constructed upstairs map. -/
  dev_equivariant :
    ∀ (γ : FundamentalGroup X x₀)
      (y : (canonicalContinuationCover x₀).total),
      agreementContinuation.dev
          ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomy.upperHalfPlaneAction γ (agreementContinuation.dev y)

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Agreement monodromy data give the single-valued canonical-cover PSL
continuation record.

%%handwave
name: Agreement monodromy data give the single-valued canonical-cover PSL continuation data
statement:
  Agreement monodromy data give the single-valued canonical-cover PSL continuation data.
-/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (M :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels where
  basedWeakHandoffAlong := M.agreementContinuation.basedWeakHandoffAlong
  dev := M.agreementContinuation.dev
  holonomy := M.holonomy
  dev_eq_on_terminalSheet := by
    intro x p y' hy'
    exact M.agreementContinuation.dev_eq_on_terminalSheet p y' hy'
  dev_equivariant := M.dev_equivariant

/--
Agreement monodromy data give PSL path-class monodromy through the constructed
canonical-cover map.

%%handwave
name: Agreement monodromy data give PSL path-class monodromy through the constructed canonical-cover map
statement:
  Agreement monodromy data give PSL path-class monodromy through the constructed canonical-cover
  map.
-/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (M :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  M.toCanonicalCoverAnalyticContinuationDataPSL
    |>.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Agreement plus path-level PSL loop equivariance gives agreement monodromy for
the constructed canonical-cover map.

%%handwave
name: Agreement plus path-level PSL loop equivariance gives agreement monodromy for the constructed canonical-cover map
statement:
  Agreement plus path-level PSL loop equivariance gives agreement monodromy for the constructed
  canonical-cover map.
-/
noncomputable def toAgreementMonodromyDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels where
  agreementContinuation := C
  holonomy := E.holonomy
  dev_equivariant := by
    intro γ y
    exact C.dev_deckAction_eq_of_terminal_path_equivariant
      E.holonomy E.terminal_path_equivariant γ y

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Automatic endpoint-transition monodromy data fill the transition-adjusted
terminal-Mobius covariance record.

%%handwave
name: Automatic endpoint-transition monodromy data fill the transition-adjusted terminal-Möbius covariance data
statement:
  Automatic endpoint-transition monodromy data fill the transition-adjusted terminal-Möbius
  covariance data.
-/
noncomputable def toTerminalTransitionProjectionEquivarianceDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
      C where
  holonomy := E.holonomy
  terminalTransitionRepresentative := fun γ loop {x} p hloop =>
    C.terminalTransitionRepresentative γ loop (x := x) p hloop
  terminalTransitionAtEndpoint := by
    intro γ loop x p hloop
    exact C.terminalTransitionAtEndpoint γ loop (x := x) p hloop
  terminalTransitionProjection_equivariant := by
    intro γ loop x p hloop
    exact E.automaticTerminalTransitionProjection_equivariant γ loop p hloop

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/-- The derived loop-terminal assignment packaged as a PSL holonomy representation.

%%handwave
name: The derived loop-terminal assignment packaged as a PSL holonomy representation
statement:
  The derived loop-terminal assignment packaged as a PSL holonomy representation.
-/
noncomputable def toRealHolonomyRepresentation
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        C) :
    RealHolonomyRepresentation X x₀ where
  toMonoidHom :=
    { toFun := fun γ ↦ C.derivedHolonomyProjection γ
      map_one' := D.derivedHolonomy_one
      map_mul' := D.derivedHolonomy_mul }

/--
Derived-holonomy monodromy/cocycle data fill the ordinary automatic
endpoint-transition terminal-Mobius covariance record.

%%handwave
name: Derived-holonomy monodromy/cocycle data fill the ordinary automatic endpoint-transition terminal-Möbius covariance data
statement:
  Derived-holonomy monodromy/cocycle data fill the ordinary automatic endpoint-transition
  terminal-Möbius covariance data.
-/
noncomputable def toAutomaticTerminalTransitionProjectionEquivarianceDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
      C where
  holonomy := D.toRealHolonomyRepresentation
  automaticTerminalTransitionProjection_equivariant := by
    intro γ loop x p hloop
    change
      realMobiusProjection
          (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            C.terminalTransitionRepresentative γ loop p hloop) =
        C.derivedHolonomyProjection γ *
          realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius)
    exact D.automaticTerminalTransitionProjection_equivariant γ loop p hloop

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Transition-adjusted terminal-Mobius PSL covariance gives value-level PSL loop
equivariance.

%%handwave
name: Transition-adjusted terminal-Möbius PSL covariance gives value-level PSL loop equivariance
statement:
  Transition-adjusted terminal-Möbius PSL covariance gives value-level PSL loop equivariance.
-/
noncomputable def toValueEquivarianceDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      C where
  holonomy := E.holonomy
  terminal_path_equivariant := by
    intro γ loop x p hloop
    simp only [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalValue]
    exact
      (C.basedWeakHandoffAlong p).terminalValue_eq_holonomy_action_of_terminalTransitionProjection_eq
        (C.basedWeakHandoffAlong (loop.trans p))
        E.holonomy γ
        (E.terminalTransitionRepresentative γ loop p hloop)
        (E.terminalTransitionAtEndpoint γ loop p hloop)
        (E.terminalTransitionProjection_equivariant γ loop p hloop)

/--
Transition-adjusted terminal-Mobius PSL covariance gives agreement monodromy
for the constructed canonical-cover map.

%%handwave
name: Transition-adjusted terminal-Möbius PSL covariance gives agreement monodromy for the constructed canonical-cover map
statement:
  Transition-adjusted terminal-Möbius PSL covariance gives agreement monodromy for the
  constructed canonical-cover map.
-/
noncomputable def toAgreementMonodromyDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  E.toValueEquivarianceDataPSL.toAgreementMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL


namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL

namespace PathLocalTransitionChainTerminalBranchAnalyticContinuationValueEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels}

end PathLocalTransitionChainTerminalBranchAnalyticContinuationValueEquivarianceDataPSL

namespace PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL


end HyperbolicMetric

end

end JJMath
