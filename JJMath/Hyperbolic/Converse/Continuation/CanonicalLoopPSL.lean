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
A pointwise preconnected terminal-chart overlap transports the terminal
transition class after terminal-sheet extensions.

This is the pointwise calculation used by both the global preconnected-overlap
package and the local/germ monodromy argument: no global component statement is
needed, only one preconnected overlap containing the original endpoint and the
transported endpoint.

%%handwave
name: Constancy of the terminal transition class under terminal-sheet extension
statement: Let $X$ be a Riemann surface equipped with compatible hyperbolic local models, let $\gamma\in\pi_1(X,x_0)$, and let $p:x_0\rightsquigarrow x$. Write $L_\gamma$ for the chosen loop representing $\gamma^{-1}$. If a point $y$ of the universal cover lies in the terminal sheet for $p$, while $\gamma y$ lies in the terminal sheet for $L_\gamma*p$, extend both paths inside those sheets to paths $p_y$ and $(L_\gamma*p)_{\gamma y}$ ending at $\pi(y)$. Assume terminal-sheet extension preserves the terminal chart and Möbius representative. If a preconnected set $W$ contains both $x$ and $\pi(y)$ and lies in the overlap of the two original terminal charts, then $[A(p_y,(L_\gamma*p)_{\gamma y})]=[A(p,L_\gamma*p)]$ in $\mathrm{PSL}_2(\mathbb R)$.
proof: Transport the transition data at $\pi(y)$ along the two terminal-sheet agreements so that its source and target are the original terminal charts. Every point of $W$ admits transition data between these two charts, so [the projective class of such transition data is constant on a preconnected overlap](lean:JJMath.HyperbolicMetric.localRealMobiusTransitionData_projection_eq_of_preconnected). Applying this at $x$ and $\pi(y)$ gives the asserted equality.
%%
-/
theorem terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq_of_preconnectedOverlap
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hExtension :
      PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
        x₀ g localModels C.basedWeakHandoffAlong)
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
    realMobiusProjection
        (C.terminalTransitionRepresentativeBetween
          (p.trans
            ((C.basedWeakHandoffAlong p).terminalSheetPathInSet hy))
          (((C.canonicalLoopFor γ).trans p).trans
            ((C.basedWeakHandoffAlong
              ((C.canonicalLoopFor γ).trans p)).terminalSheetPathInSet
                (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck))) =
      realMobiusProjection
        (C.terminalTransitionRepresentativeBetween p
          ((C.canonicalLoopFor γ).trans p)) := by
  classical
  let L := C.canonicalLoopFor γ
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (L.trans p)
  let σ := S.terminalSheetPathInSet hy
  let q : Path x₀ (PathHomotopyUniversalCover.endpoint y) := p.trans σ
  let τ := T.terminalSheetPathInSet
    (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck
  let r : Path x₀ (PathHomotopyUniversalCover.endpoint y) := (L.trans p).trans τ
  rcases hExtension p hy with ⟨hSourceExt⟩
  rcases hExtension (L.trans p) hdeck with ⟨hTargetExt⟩
  let Tx := C.terminalTransitionDataBetween p (L.trans p)
  let Ty₀ := C.terminalTransitionDataBetween q r
  let Ty :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt T.terminalCenter)
        (PathHomotopyUniversalCover.endpoint y) :=
    localRealMobiusTransitionData_congr
      (congrArg localModels.chartAt hSourceExt.terminalCenter_eq).symm
      (congrArg localModels.chartAt hTargetExt.terminalCenter_eq).symm
      rfl Ty₀
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
  have hConst :
      realMobiusProjection Ty.representative =
        realMobiusProjection Tx.representative :=
    localRealMobiusTransitionData_projection_eq_of_preconnected
      hWpre hWexists hxW hyW Tx Ty
  simpa [Tx, Ty, Ty₀, q, r, L, S, T,
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween]
    using hConst

/--
A pointwise preconnected terminal-chart overlap gives equality of the
normalized canonical-loop projection at the transported cover point and at the
source terminal cover point.

%%handwave
name: Local constancy of normalized loop transport under terminal-sheet extension
statement: In the setting above, assume terminal-sheet extension preserves the terminal chart and Möbius representative. Let $y$ lie in the terminal sheet for $p:x_0\rightsquigarrow x$, and suppose $\gamma y$ lies in the terminal sheet for $L_\gamma*p$. If a preconnected set $W$ contains $x$ and $\pi(y)$ and is contained in the overlap of the two original terminal charts, then the normalized projective transport associated with $\gamma$ has the same value at $y$ as at the terminal lift $\widetilde p(1)$: $N_\gamma(y)=N_\gamma(\widetilde p(1))$.
proof: Extend $p$ inside its terminal sheet to a path $q$ representing $y$, and extend $L_\gamma*p$ to a path $r$ representing $\gamma y$. The path $L_\gamma*q$ is homotopic to $r$. Homotopy invariance identifies the adjusted target terms, terminal-sheet agreement identifies the source and target Möbius classes, and [the transition classes for the extended and original pairs coincide](lean:JJMath.HyperbolicMetric.PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq_of_preconnectedOverlap). Substitution in the numerator and denominator of $N_\gamma$ proves the equality.
%%
-/
theorem canonicalLoopNormalizedProjectionAt_eq_of_preconnectedOverlap
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hExtension :
      PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
        x₀ g localModels C.basedWeakHandoffAlong)
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
  let L := C.canonicalLoopFor γ
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (L.trans p)
  let σ := S.terminalSheetPathInSet hy
  let q : Path x₀ (PathHomotopyUniversalCover.endpoint y) := p.trans σ
  let τ := T.terminalSheetPathInSet
    (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck
  let r : Path x₀ (PathHomotopyUniversalCover.endpoint y) := (L.trans p).trans τ
  let Lq : Path x₀ (PathHomotopyUniversalCover.endpoint y) := L.trans q
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
  have hLq_r :
      Path.Homotopic Lq r := by
    simpa [Lq, r, τ, T] using
      T.homotopic_to_path_trans_terminalSheetPathInSet_of_mk_eq_pathClass
        hdeck hLqClass
  rcases hExtension p hy with ⟨hSourceExt⟩
  rcases hExtension (L.trans p) hdeck with ⟨hTargetExt⟩
  let Mq := (C.basedWeakHandoffAlong q).terminalMobius
  let MLq := (C.basedWeakHandoffAlong Lq).terminalMobius
  let Mr := (C.basedWeakHandoffAlong r).terminalMobius
  have hSourceMobius :
      realMobiusProjection Mq =
        realMobiusProjection S.terminalMobius := by
    simpa [Mq, q, σ, S] using
      congrArg realMobiusProjection hSourceExt.terminalMobius_eq
  have hTargetMobius :
      realMobiusProjection Mr =
        realMobiusProjection T.terminalMobius := by
    simpa [Mr, r, τ, T] using
      congrArg realMobiusProjection hTargetExt.terminalMobius_eq
  have hHomAdjusted :
      realMobiusProjection
          (Mr * C.terminalTransitionRepresentativeBetween Lq r) =
        realMobiusProjection MLq := by
    simpa [Lq, r, MLq, Mr] using
      C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
        Lq r hLq_r
  have hViaExtension :
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween q Lq) =
        realMobiusProjection
          (Mr * C.terminalTransitionRepresentativeBetween q r) := by
    calc
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween q Lq)
          =
        realMobiusProjection MLq *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween q Lq) := by
          simp
      _ =
        realMobiusProjection
            (Mr * C.terminalTransitionRepresentativeBetween Lq r) *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween q Lq) := by
          rw [hHomAdjusted]
      _ =
        realMobiusProjection
          ((Mr * C.terminalTransitionRepresentativeBetween Lq r) *
            C.terminalTransitionRepresentativeBetween q Lq) := by
          simp [mul_assoc]
      _ =
        realMobiusProjection
          (Mr * C.terminalTransitionRepresentativeBetween q r) := by
          exact
            (C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
              q Lq r Mr).symm
  have hTransport :=
    C.terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq_of_preconnectedOverlap
      hExtension γ p y hy hdeck W hWpre hxW hyW hWsub
  have hNumerator :
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween q Lq) =
        realMobiusProjection
          (T.terminalMobius *
            C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
    calc
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween q Lq)
          =
        realMobiusProjection
          (Mr * C.terminalTransitionRepresentativeBetween q r) := hViaExtension
      _ =
        realMobiusProjection Mr *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween q r) := by
          simp
      _ =
        realMobiusProjection T.terminalMobius *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween q r) := by
          rw [hTargetMobius]
      _ =
        realMobiusProjection T.terminalMobius *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
          rw [hTransport]
      _ =
        realMobiusProjection
          (T.terminalMobius *
            C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
          simp
  have hNormalized :
      C.canonicalLoopNormalizedTerminalProjection γ q =
        C.canonicalLoopNormalizedTerminalProjection γ p := by
    calc
      C.canonicalLoopNormalizedTerminalProjection γ q
          =
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween q Lq) *
          (realMobiusProjection Mq)⁻¹ := by
          simp [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.canonicalLoopNormalizedTerminalProjection,
            L, q, Lq, Mq, MLq]
      _ =
        realMobiusProjection
            (T.terminalMobius *
              C.terminalTransitionRepresentativeBetween p (L.trans p)) *
          (realMobiusProjection S.terminalMobius)⁻¹ := by
          rw [hNumerator, hSourceMobius]
      _ =
        C.canonicalLoopNormalizedTerminalProjection γ p := by
          simp [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.canonicalLoopNormalizedTerminalProjection,
            L, S, T]
  calc
    C.canonicalLoopNormalizedProjectionAt γ y
        = C.canonicalLoopNormalizedTerminalProjection γ q := hAtY
    _ = C.canonicalLoopNormalizedTerminalProjection γ p := hNormalized
    _ = C.canonicalLoopNormalizedProjectionAt γ S.terminalCoverPoint :=
        hAtBase.symm

/--
PSL-level terminal-extension agreement is enough for the pointwise
preconnected-overlap transport of terminal transition classes.

%%handwave
name: Constancy of the terminal transition class from projective sheet agreement
statement: Let $\gamma\in\pi_1(X,x_0)$, let $p:x_0\rightsquigarrow x$, and let $L_\gamma$ represent $\gamma^{-1}$. Suppose $y$ lies in the terminal sheet for $p$ and $\gamma y$ lies in the terminal sheet for $L_\gamma*p$. Extend these paths inside their terminal sheets to $p_y$ and $(L_\gamma*p)_{\gamma y}$. If extension preserves the terminal center and the projective class of the terminal Möbius map, and if a preconnected set $W$ contains $x$ and $\pi(y)$ inside the overlap of the two original terminal charts, then $[A(p_y,(L_\gamma*p)_{\gamma y})]=[A(p,L_\gamma*p)]$ in $\mathrm{PSL}_2(\mathbb R)$.
proof: Use equality of terminal centers to regard the two transition data as transitions between fixed source and target charts. The assumed projective agreement is sufficient for this change of representatives. The class of transition data between two fixed charts is constant on the preconnected set $W$, so comparison at $x$ and $\pi(y)$ gives the formula.
%%
-/
theorem terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq_of_preconnectedOverlap_of_projectionAgreement
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hExtension :
      PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrinciple
        x₀ g localModels C.basedWeakHandoffAlong)
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
    realMobiusProjection
        (C.terminalTransitionRepresentativeBetween
          (p.trans
            ((C.basedWeakHandoffAlong p).terminalSheetPathInSet hy))
          (((C.canonicalLoopFor γ).trans p).trans
            ((C.basedWeakHandoffAlong
              ((C.canonicalLoopFor γ).trans p)).terminalSheetPathInSet
                (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck))) =
      realMobiusProjection
        (C.terminalTransitionRepresentativeBetween p
          ((C.canonicalLoopFor γ).trans p)) := by
  classical
  let L := C.canonicalLoopFor γ
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (L.trans p)
  let σ := S.terminalSheetPathInSet hy
  let q : Path x₀ (PathHomotopyUniversalCover.endpoint y) := p.trans σ
  let τ := T.terminalSheetPathInSet
    (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck
  let r : Path x₀ (PathHomotopyUniversalCover.endpoint y) := (L.trans p).trans τ
  rcases hExtension p hy with ⟨hSourceExt⟩
  rcases hExtension (L.trans p) hdeck with ⟨hTargetExt⟩
  let Tx := C.terminalTransitionDataBetween p (L.trans p)
  let Ty₀ := C.terminalTransitionDataBetween q r
  let Ty :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S.terminalCenter)
        (localModels.chartAt T.terminalCenter)
        (PathHomotopyUniversalCover.endpoint y) :=
    localRealMobiusTransitionData_congr
      (congrArg localModels.chartAt hSourceExt.terminalCenter_eq).symm
      (congrArg localModels.chartAt hTargetExt.terminalCenter_eq).symm
      rfl Ty₀
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
  have hConst :
      realMobiusProjection Ty.representative =
        realMobiusProjection Tx.representative :=
    localRealMobiusTransitionData_projection_eq_of_preconnected
      hWpre hWexists hxW hyW Tx Ty
  simpa [Tx, Ty, Ty₀, q, r, L, S, T,
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween]
    using hConst

/--
PSL-level terminal-extension agreement is enough for local normalized
canonical-loop transport on a preconnected terminal-chart overlap.

%%handwave
name: Local constancy of normalized loop transport from projective sheet agreement
statement: Let $p:x_0\rightsquigarrow x$ and $\gamma\in\pi_1(X,x_0)$. Suppose $y$ belongs to the terminal sheet for $p$, while $\gamma y$ belongs to the terminal sheet for $L_\gamma*p$, where $L_\gamma$ represents $\gamma^{-1}$. Assume terminal-sheet extension preserves the terminal center and the projective class of the terminal Möbius map. If $x$ and $\pi(y)$ lie in a preconnected subset of the overlap of the two original terminal charts, then $N_\gamma(y)=N_\gamma(\widetilde p(1))$.
proof: Represent $y$ by a terminal-sheet extension $q$ of $p$ and $\gamma y$ by an extension $r$ of $L_\gamma*p$. Homotopy invariance compares $L_\gamma*q$ with $r$. Projective terminal-sheet agreement identifies the source and target Möbius factors, while [the extended transition class equals the original transition class](lean:JJMath.HyperbolicMetric.PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq_of_preconnectedOverlap_of_projectionAgreement). The defining quotient for $N_\gamma$ therefore has the same numerator and denominator for $q$ and $p$.
%%
-/
theorem canonicalLoopNormalizedProjectionAt_eq_of_preconnectedOverlap_of_projectionAgreement
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hExtension :
      PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrinciple
        x₀ g localModels C.basedWeakHandoffAlong)
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
  let L := C.canonicalLoopFor γ
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong (L.trans p)
  let σ := S.terminalSheetPathInSet hy
  let q : Path x₀ (PathHomotopyUniversalCover.endpoint y) := p.trans σ
  let τ := T.terminalSheetPathInSet
    (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck
  let r : Path x₀ (PathHomotopyUniversalCover.endpoint y) := (L.trans p).trans τ
  let Lq : Path x₀ (PathHomotopyUniversalCover.endpoint y) := L.trans q
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
  have hLq_r :
      Path.Homotopic Lq r := by
    simpa [Lq, r, τ, T] using
      T.homotopic_to_path_trans_terminalSheetPathInSet_of_mk_eq_pathClass
        hdeck hLqClass
  rcases hExtension p hy with ⟨hSourceExt⟩
  rcases hExtension (L.trans p) hdeck with ⟨hTargetExt⟩
  let Mq := (C.basedWeakHandoffAlong q).terminalMobius
  let MLq := (C.basedWeakHandoffAlong Lq).terminalMobius
  let Mr := (C.basedWeakHandoffAlong r).terminalMobius
  have hSourceMobius :
      realMobiusProjection Mq =
        realMobiusProjection S.terminalMobius := by
    simpa [Mq, q, σ, S] using hSourceExt.terminalMobius_projection_eq
  have hTargetMobius :
      realMobiusProjection Mr =
        realMobiusProjection T.terminalMobius := by
    simpa [Mr, r, τ, T] using hTargetExt.terminalMobius_projection_eq
  have hHomAdjusted :
      realMobiusProjection
          (Mr * C.terminalTransitionRepresentativeBetween Lq r) =
        realMobiusProjection MLq := by
    simpa [Lq, r, MLq, Mr] using
      C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
        Lq r hLq_r
  have hViaExtension :
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween q Lq) =
        realMobiusProjection
          (Mr * C.terminalTransitionRepresentativeBetween q r) := by
    calc
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween q Lq)
          =
        realMobiusProjection MLq *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween q Lq) := by
          simp
      _ =
        realMobiusProjection
            (Mr * C.terminalTransitionRepresentativeBetween Lq r) *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween q Lq) := by
          rw [hHomAdjusted]
      _ =
        realMobiusProjection
          ((Mr * C.terminalTransitionRepresentativeBetween Lq r) *
            C.terminalTransitionRepresentativeBetween q Lq) := by
          simp [mul_assoc]
      _ =
        realMobiusProjection
          (Mr * C.terminalTransitionRepresentativeBetween q r) := by
          exact
            (C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
              q Lq r Mr).symm
  have hTransport :=
    C.terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq_of_preconnectedOverlap_of_projectionAgreement
      hExtension γ p y hy hdeck W hWpre hxW hyW hWsub
  have hNumerator :
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween q Lq) =
        realMobiusProjection
          (T.terminalMobius *
            C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
    calc
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween q Lq)
          =
        realMobiusProjection
          (Mr * C.terminalTransitionRepresentativeBetween q r) := hViaExtension
      _ =
        realMobiusProjection Mr *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween q r) := by
          simp
      _ =
        realMobiusProjection T.terminalMobius *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween q r) := by
          rw [hTargetMobius]
      _ =
        realMobiusProjection T.terminalMobius *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
          rw [hTransport]
      _ =
        realMobiusProjection
          (T.terminalMobius *
            C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
          simp
  have hNormalized :
      C.canonicalLoopNormalizedTerminalProjection γ q =
        C.canonicalLoopNormalizedTerminalProjection γ p := by
    calc
      C.canonicalLoopNormalizedTerminalProjection γ q
          =
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween q Lq) *
          (realMobiusProjection Mq)⁻¹ := by
          simp [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.canonicalLoopNormalizedTerminalProjection,
            L, q, Lq, Mq, MLq]
      _ =
        realMobiusProjection
            (T.terminalMobius *
              C.terminalTransitionRepresentativeBetween p (L.trans p)) *
          (realMobiusProjection S.terminalMobius)⁻¹ := by
          rw [hNumerator, hSourceMobius]
      _ =
        C.canonicalLoopNormalizedTerminalProjection γ p := by
          simp [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.canonicalLoopNormalizedTerminalProjection,
            L, S, T]
  calc
    C.canonicalLoopNormalizedProjectionAt γ y
        = C.canonicalLoopNormalizedTerminalProjection γ q := hAtY
    _ = C.canonicalLoopNormalizedTerminalProjection γ p := hNormalized
    _ = C.canonicalLoopNormalizedProjectionAt γ S.terminalCoverPoint :=
        hAtBase.symm

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

/--
Upstairs preconnected-overlap data imply terminal-sheet transport.
-/
noncomputable def toTerminalSheetTransportDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
      C :=
  D.toPreconnectedOverlapDataPSL.toTerminalSheetTransportDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Same-component overlap data imply terminal-sheet transport of the normalized
canonical-loop transition class.
-/
noncomputable def toTerminalSheetTransportDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
      C :=
  D.toPreconnectedOverlapDataPSL.toTerminalSheetTransportDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
An explicit path in the terminal-chart overlap implies terminal-sheet
transport.
-/
noncomputable def toTerminalSheetTransportDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
      C :=
  D.toSameOverlapComponentDataPSL.toTerminalSheetTransportDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Upstairs overlap-path data imply terminal-sheet transport.
-/
noncomputable def toTerminalSheetTransportDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
      C :=
  D.toOverlapConnectingPathDataPSL.toTerminalSheetTransportDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Terminal-sheet overlap-path data imply terminal-sheet transport of the
normalized canonical-loop transition class.
-/
noncomputable def toTerminalSheetTransportDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
      C :=
  D.toSameOverlapComponentDataPSL.toTerminalSheetTransportDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Terminal-sheet transport data imply local-sheet constancy of the normalized
canonical-loop projection.
-/
noncomputable def toLocalSheetConstancyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyDataPSL
      C where
  canonicalLoopNormalizedProjectionAt_eq_on_deck_terminalSheets := by
    intro γ x p y hy hdeck
    let L := C.canonicalLoopFor γ
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (L.trans p)
    have hdeckPH :
        PathHomotopyUniversalCover.deckAction γ y ∈ T.terminalSheet := by
      simpa [T, L, canonicalContinuationCover, SimplyConnectedCover.deckAction,
        PathHomotopyUniversalCover.deckHomeomorphism_apply] using hdeck
    let σ := S.terminalSheetPathInSet hy
    let q : Path x₀ (PathHomotopyUniversalCover.endpoint y) := p.trans σ
    let τ := T.terminalSheetPathInSet
      (y' := PathHomotopyUniversalCover.deckAction γ y) hdeckPH
    let r : Path x₀ (PathHomotopyUniversalCover.endpoint y) := (L.trans p).trans τ
    let Lq : Path x₀ (PathHomotopyUniversalCover.endpoint y) := L.trans q
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
    have hLq_r :
        Path.Homotopic Lq r := by
      simpa [Lq, r, τ, T] using
        T.homotopic_to_path_trans_terminalSheetPathInSet_of_mk_eq_pathClass
          hdeckPH hLqClass
    rcases D.terminalSheetExtensionAgreement p hy with ⟨hSourceExt⟩
    rcases D.terminalSheetExtensionAgreement (L.trans p) hdeckPH with ⟨hTargetExt⟩
    let Mq := (C.basedWeakHandoffAlong q).terminalMobius
    let MLq := (C.basedWeakHandoffAlong Lq).terminalMobius
    let Mr := (C.basedWeakHandoffAlong r).terminalMobius
    have hSourceMobius :
        realMobiusProjection Mq =
          realMobiusProjection S.terminalMobius := by
      simpa [Mq, q, σ, S] using
        congrArg realMobiusProjection hSourceExt.terminalMobius_eq
    have hTargetMobius :
        realMobiusProjection Mr =
          realMobiusProjection T.terminalMobius := by
      simpa [Mr, r, τ, T] using
        congrArg realMobiusProjection hTargetExt.terminalMobius_eq
    have hHomAdjusted :
        realMobiusProjection
            (Mr * C.terminalTransitionRepresentativeBetween Lq r) =
          realMobiusProjection MLq := by
      simpa [Lq, r, MLq, Mr] using
        C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
          Lq r hLq_r
    have hViaExtension :
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween q Lq) =
          realMobiusProjection
            (Mr * C.terminalTransitionRepresentativeBetween q r) := by
      calc
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween q Lq)
            =
          realMobiusProjection MLq *
            realMobiusProjection
              (C.terminalTransitionRepresentativeBetween q Lq) := by
            simp
        _ =
          realMobiusProjection
              (Mr * C.terminalTransitionRepresentativeBetween Lq r) *
            realMobiusProjection
              (C.terminalTransitionRepresentativeBetween q Lq) := by
            rw [hHomAdjusted]
        _ =
          realMobiusProjection
            ((Mr * C.terminalTransitionRepresentativeBetween Lq r) *
              C.terminalTransitionRepresentativeBetween q Lq) := by
            simp [mul_assoc]
        _ =
          realMobiusProjection
            (Mr * C.terminalTransitionRepresentativeBetween q r) := by
            exact
              (C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
                q Lq r Mr).symm
    have hTransport :=
      D.terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq
        γ p y hy hdeckPH
    have hNumerator :
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween q Lq) =
          realMobiusProjection
            (T.terminalMobius *
              C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
      calc
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween q Lq)
            =
          realMobiusProjection
            (Mr * C.terminalTransitionRepresentativeBetween q r) := hViaExtension
        _ =
          realMobiusProjection Mr *
            realMobiusProjection
              (C.terminalTransitionRepresentativeBetween q r) := by
            simp
        _ =
          realMobiusProjection T.terminalMobius *
            realMobiusProjection
              (C.terminalTransitionRepresentativeBetween q r) := by
            rw [hTargetMobius]
        _ =
          realMobiusProjection T.terminalMobius *
            realMobiusProjection
              (C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
            rw [hTransport]
        _ =
          realMobiusProjection
            (T.terminalMobius *
              C.terminalTransitionRepresentativeBetween p (L.trans p)) := by
            simp
    have hNormalized :
        C.canonicalLoopNormalizedTerminalProjection γ q =
          C.canonicalLoopNormalizedTerminalProjection γ p := by
      calc
        C.canonicalLoopNormalizedTerminalProjection γ q
            =
          realMobiusProjection
              (MLq * C.terminalTransitionRepresentativeBetween q Lq) *
            (realMobiusProjection Mq)⁻¹ := by
            simp [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.canonicalLoopNormalizedTerminalProjection,
              L, q, Lq, Mq, MLq]
        _ =
          realMobiusProjection
              (T.terminalMobius *
                C.terminalTransitionRepresentativeBetween p (L.trans p)) *
            (realMobiusProjection S.terminalMobius)⁻¹ := by
            rw [hNumerator, hSourceMobius]
        _ =
          C.canonicalLoopNormalizedTerminalProjection γ p := by
            simp [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.canonicalLoopNormalizedTerminalProjection,
              L, S, T]
    calc
      C.canonicalLoopNormalizedProjectionAt γ y
          = C.canonicalLoopNormalizedTerminalProjection γ q := hAtY
      _ = C.canonicalLoopNormalizedTerminalProjection γ p := hNormalized
      _ = C.canonicalLoopNormalizedProjectionAt γ S.terminalCoverPoint :=
          hAtBase.symm

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Local sheet constancy gives local constancy on the canonical cover.
-/
noncomputable def toLocalConstancyOnCoverDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyDataPSL
        C) :
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
    let U : Set (PathHomotopyUniversalCover X x₀) :=
      S.terminalSheet ∩
        ((canonicalContinuationCover x₀).deckAction γ) ⁻¹' T.terminalSheet
    have hDeckCont :
        Continuous ((canonicalContinuationCover x₀).deckAction γ) := by
      exact ((canonicalContinuationCover x₀).deckTransformation γ).continuous_toFun
    have hUopen : IsOpen U := by
      exact S.isOpen_terminalSheet.inter
        (T.isOpen_terminalSheet.preimage hDeckCont)
    have hp_class :
        Path.Homotopic.Quotient.mk p =
          PathHomotopyUniversalCover.pathClass y := by
      exact Quot.out_eq (PathHomotopyUniversalCover.pathClass y)
    have hSpoint : S.terminalCoverPoint = y := by
      exact S.terminalCoverPoint_eq_of_mk_eq_pathClass hp_class
    have hTpoint :
        T.terminalCoverPoint =
          (canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint := by
      exact
        S.terminalCoverPoint_loopTrans_eq_deckAction γ
          (C.canonicalLoopFor γ) T (C.canonicalLoopFor_spec γ)
    have hyU : y ∈ U := by
      refine ⟨?_, ?_⟩
      · simpa [S, hSpoint] using S.terminalCoverPoint_mem_terminalSheet
      · simpa [T, hSpoint, hTpoint] using T.terminalCoverPoint_mem_terminalSheet
    refine ⟨U, hUopen, hyU, ?_⟩
    intro z hz
    have hz_eq :=
      D.canonicalLoopNormalizedProjectionAt_eq_on_deck_terminalSheets γ p z
        hz.1 hz.2
    simpa [S, hSpoint] using hz_eq

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Terminal-sheet extension agreement is enough to make the normalized
canonical-loop projection locally constant on the canonical cover.

The neighborhood is not the whole overlap of two selected terminal sheets.
Instead, around each cover point we shrink to a fresh local sheet chart whose
base lies in the overlap of the two terminal sheet-chart bases.  This removes
the former global same-component/good-cover requirement from the local
monodromy step.
-/
noncomputable def toLocalConstancyOnCoverDataPSL_of_terminalSheetExtensionAgreement
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hExtension :
      PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
        x₀ g localModels C.basedWeakHandoffAlong) :
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
      C.canonicalLoopNormalizedProjectionAt_eq_of_preconnectedOverlap
        hExtension γ p z hzS hzDeck E.base hWpre
        (by
          simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
            using hxW)
        hzW hWsub
    simpa [S, hSpoint] using hConst

/--
PSL-level terminal-sheet extension agreement is enough to make the normalized
canonical-loop projection locally constant on the canonical cover.

This is the projective-strength version of
`toLocalConstancyOnCoverDataPSL_of_terminalSheetExtensionAgreement`: exact
equality of the accumulated `SL(2, ℝ)` representative has been replaced by
equality after projection to PSL.
-/
noncomputable def toLocalConstancyOnCoverDataPSL_of_terminalSheetExtensionProjectionAgreement
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hExtension :
      PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrinciple
        x₀ g localModels C.basedWeakHandoffAlong) :
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
      C.canonicalLoopNormalizedProjectionAt_eq_of_preconnectedOverlap_of_projectionAgreement
        hExtension γ p z hzS hzDeck E.base hWpre
        (by
          simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.endpoint_terminalCoverPoint]
            using hxW)
        hzW hWsub
    simpa [S, hSpoint] using hConst

/--
Terminal-sheet overlap alone makes the normalized canonical-loop projection
locally constant on the canonical cover.

The proof shrinks around each upstairs point to a local sheet whose base lies
inside the two relevant terminal chart domains.  On that small preconnected
base patch, terminal chart transitions are constant in PSL, while arbitrary
selected terminal-sheet extensions are compared by the adjusted local
terminal-sheet overlap lemma.
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
Agreement monodromy data expose path-level PSL loop equivariance of terminal
values.
-/
noncomputable def toValueEquivarianceDataPSL
    (M :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      M.agreementContinuation :=
  M.agreementContinuation.toValueEquivarianceDataPSL_of_dev_equivariant
    M.holonomy M.dev_equivariant

/--
Agreement monodromy data force terminal-formula projection rigidity, using the
unconditional nonempty-open terminal-coordinate agreement sets.
-/
noncomputable def toTerminalFormulaProjectionRigidityDataPSL
    (M :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityDataPSL
      M.agreementContinuation :=
  M.agreementContinuation.toTerminalFormulaNonemptyOpenAgreementDataPSL
    |>.toTerminalFormulaThreePointRichnessDataPSL
    |>.toTerminalFormulaActionFaithfulnessDataPSL
    |>.toTerminalFormulaProjectionFaithfulnessDataPSL
    |>.toTerminalFormulaProjectionRigidityDataPSL

/--
Agreement monodromy data identify the deck holonomy with the loop-terminal
derived PSL class and give terminal-Mobius projection rigidity.
-/
noncomputable def toValueProjectionRigidityDataPSL
    (M :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL
      M.agreementContinuation :=
  M.toTerminalFormulaProjectionRigidityDataPSL.toValueProjectionRigidityDataPSL
    M.toValueEquivarianceDataPSL

/--
Agreement monodromy data yield the derived-holonomy automatic endpoint
transition covariance package.
-/
noncomputable def toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    (M :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      M.agreementContinuation :=
  M.toValueProjectionRigidityDataPSL
    |>.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

/--
Agreement monodromy data give automatic endpoint-transition terminal-Mobius
PSL covariance.
-/
noncomputable def toAutomaticTerminalTransitionProjectionEquivarianceDataPSL
    (M :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
      M.agreementContinuation :=
  let D := M.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
  { holonomy :=
      { toMonoidHom :=
        { toFun := fun γ ↦ M.agreementContinuation.derivedHolonomyProjection γ
          map_one' := D.derivedHolonomy_one
          map_mul' := D.derivedHolonomy_mul } }
    automaticTerminalTransitionProjection_equivariant := by
      intro γ loop x p hloop
      change
        realMobiusProjection
            (((M.agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
              M.agreementContinuation.terminalTransitionRepresentative γ loop p hloop) =
          M.agreementContinuation.derivedHolonomyProjection γ *
            realMobiusProjection
              ((M.agreementContinuation.basedWeakHandoffAlong p).terminalMobius)
      exact D.automaticTerminalTransitionProjection_equivariant γ loop p hloop }

/--
Agreement monodromy data give transition-adjusted terminal-Mobius PSL
covariance.
-/
noncomputable def toTerminalTransitionProjectionEquivarianceDataPSL
    (M :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
      M.agreementContinuation :=
  let E := M.toAutomaticTerminalTransitionProjectionEquivarianceDataPSL
  { holonomy := E.holonomy
    terminalTransitionRepresentative := fun γ loop {x} p hloop =>
      M.agreementContinuation.terminalTransitionRepresentative γ loop (x := x) p hloop
    terminalTransitionAtEndpoint := by
      intro γ loop x p hloop
      exact M.agreementContinuation.terminalTransitionAtEndpoint γ loop (x := x) p hloop
    terminalTransitionProjection_equivariant := by
      intro γ loop x p hloop
      exact E.automaticTerminalTransitionProjection_equivariant γ loop p hloop }

/--
Agreement monodromy data give the single-valued canonical-cover PSL
continuation record.
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

/--
Cover-level PSL continuation also gives canonical-sheet agreement monodromy:
the agreement data are obtained by forgetting to terminal-sheet compatibility,
and deck equivariance for the quotient-defined upstairs map follows from the
terminal-value equivariance read off from the original cover-level map.
-/
noncomputable def toCanonicalSheetAgreementMonodromyDataPSL
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels where
  agreementContinuation := C.toCanonicalSheetAgreementData
  holonomy := C.holonomy
  dev_equivariant := by
    intro γ y
    refine
      C.toCanonicalSheetAgreementData.dev_deckAction_eq_of_terminal_path_equivariant
        C.holonomy ?_ γ y
    intro δ loop x p hloop
    simpa [
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalValue,
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData.terminalValue,
      toCanonicalSheetAgreementData]
      using
        C.toCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL.terminal_path_equivariant
          δ loop p hloop

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

/--
Automatic endpoint-transition monodromy data give path-level PSL loop
equivariance.
-/
noncomputable def toValueEquivarianceDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      C :=
  { holonomy := E.holonomy
    terminal_path_equivariant := by
      intro γ loop x p hloop
      simp only [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalValue]
      exact
        (C.basedWeakHandoffAlong p).terminalValue_eq_holonomy_action_of_terminalTransitionProjection_eq
          (C.basedWeakHandoffAlong (loop.trans p))
          E.holonomy γ
          (C.terminalTransitionRepresentative γ loop (x := x) p hloop)
          (C.terminalTransitionAtEndpoint γ loop (x := x) p hloop)
          (E.automaticTerminalTransitionProjection_equivariant γ loop p hloop) }

/--
Automatic endpoint-transition monodromy data give agreement monodromy for the
constructed canonical-cover map.
-/
noncomputable def toAgreementMonodromyDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  E.toValueEquivarianceDataPSL.toAgreementMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/-- The derived loop-terminal assignment packaged as a PSL holonomy representation. -/
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

/--
Derived-holonomy monodromy/cocycle data give agreement monodromy for the
constructed canonical-cover map.
-/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.toAutomaticTerminalTransitionProjectionEquivarianceDataPSL.toAgreementMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Reduced derived-holonomy data give automatic endpoint-transition PSL
covariance.
-/
noncomputable def toAutomaticTerminalTransitionProjectionEquivarianceDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
      C :=
  D.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    |>.toAutomaticTerminalTransitionProjectionEquivarianceDataPSL

/--
Reduced derived-holonomy data give agreement monodromy for the constructed
canonical-cover map.
-/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    |>.toAgreementMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Coherent terminal-extension agreement gives local constancy of the normalized
canonical-loop projection for the agreement data induced by the same coherent
choice of handoff skeletons.
-/
noncomputable def toLocalConstancyOnCoverDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL
      D.toCanonicalSheetAgreementData :=
  D.toCanonicalSheetAgreementData.toLocalConstancyOnCoverDataPSL_of_terminalSheetExtensionAgreement
    D.terminalSheetExtensionAgreement

/--
Coherent elementary-grid/terminal-extension-agreement data produce PSL
monodromy for their induced canonical-sheet agreement data.
-/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.toLocalConstancyOnCoverDataPSL
    |>.toConstancyOnCoverDataPSL
    |>.toNormalizedProjectionPropagationDataPSL
    |>.toCanonicalLoopCovarianceDataPSL
    |>.toReducedDerivedHolonomyDataPSL
    |>.toAgreementMonodromyDataPSL

/--
Coherent elementary-grid/terminal-extension-agreement data produce the
single-valued PSL continuation record on the canonical cover.
-/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Coherent elementary-grid/terminal-extension-agreement data produce PSL
path-class monodromy.
-/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Coherent PSL terminal-extension agreement gives local constancy of the
normalized canonical-loop projection for the agreement data induced by the
same coherent choice of handoff skeletons.
-/
noncomputable def toLocalConstancyOnCoverDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL
      D.toCanonicalSheetAgreementData :=
  D.toCanonicalSheetAgreementData.toLocalConstancyOnCoverDataPSL_of_terminalSheetExtensionProjectionAgreement
    D.terminalSheetExtensionProjectionAgreement

/--
Coherent elementary-grid/PSL-terminal-extension-agreement data produce PSL
monodromy for their induced canonical-sheet agreement data.
-/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.toLocalConstancyOnCoverDataPSL
    |>.toConstancyOnCoverDataPSL
    |>.toNormalizedProjectionPropagationDataPSL
    |>.toCanonicalLoopCovarianceDataPSL
    |>.toReducedDerivedHolonomyDataPSL
    |>.toAgreementMonodromyDataPSL

/--
Coherent elementary-grid/PSL-terminal-extension-agreement data produce the
single-valued PSL continuation record on the canonical cover.
-/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Coherent elementary-grid/PSL-terminal-extension-agreement data produce PSL
path-class monodromy.
-/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

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
-/
noncomputable def toAgreementMonodromyDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  E.toValueEquivarianceDataPSL.toAgreementMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
The older same-terminal-chart covariance data are a special case of the
transition-adjusted terminal covariance data, using the identity transition.
-/
noncomputable def toTerminalTransitionProjectionEquivarianceDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
      C where
  holonomy := E.holonomy
  terminalTransitionRepresentative := fun _γ _loop {_x} _p _hloop => 1
  terminalTransitionAtEndpoint := by
    intro γ loop x p hloop
    rw [E.terminalCenter_equivariant γ loop p hloop]
    simp [realMobiusRepresentativeAction_one]
  terminalTransitionProjection_equivariant := by
    intro γ loop x p hloop
    simpa using E.terminalProjection_equivariant γ loop p hloop

/--
Terminal-Mobius PSL covariance gives value-level PSL loop equivariance for
terminal-sheet agreement data.
-/
noncomputable def toValueEquivarianceDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      C :=
  PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL.ofTerminalProjectionEquivarianceData
    E

/--
Terminal-Mobius PSL covariance gives agreement monodromy for the constructed
canonical-cover map.
-/
noncomputable def toAgreementMonodromyDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  E.toValueEquivarianceDataPSL.toAgreementMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL

/--
Coherent elementary-grid/local-extension data together with terminal-Mobius
PSL covariance for the terminal-sheet agreement data it constructs.

This is weaker than a theorem giving terminal-projection covariance for every
possible agreement continuation: it binds the covariance to the actual
selected continuation package.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Coherent elementary grid walks and terminal-sheet local extension. -/
  elementaryGridLocalExtension :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
      x₀ g localModels
  /-- Terminal-Mobius PSL covariance for the induced agreement data. -/
  terminalProjectionEquivariance :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL
      elementaryGridLocalExtension.toCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The bound data produce terminal-sheet agreement monodromy. -/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.terminalProjectionEquivariance.toAgreementMonodromyDataPSL

/-- The bound data produce the canonical-cover PSL continuation record. -/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/-- The bound data produce path-class PSL monodromy. -/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL

/--
Coherent elementary-grid/terminal-extension-agreement data together with
terminal-Mobius PSL covariance for the terminal-sheet agreement data it
constructs.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Coherent elementary grid walks and terminal-sheet extension agreement. -/
  elementaryGridExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
      x₀ g localModels
  /-- Terminal-Mobius PSL covariance for the induced agreement data. -/
  terminalProjectionEquivariance :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL
      elementaryGridExtensionAgreement.toCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Forget terminal-extension agreement to local-extension data. -/
noncomputable def toElementaryGridLocalExtensionTerminalProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
      x₀ g localModels where
  elementaryGridLocalExtension :=
    D.elementaryGridExtensionAgreement.toElementaryGridLocalExtensionData
  terminalProjectionEquivariance := D.terminalProjectionEquivariance

/-- The bound data produce terminal-sheet agreement monodromy. -/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.terminalProjectionEquivariance.toAgreementMonodromyDataPSL

/-- The bound data produce the canonical-cover PSL continuation record. -/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/-- The bound data produce path-class PSL monodromy. -/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL

/--
Coherent elementary-grid/local-extension data together with
transition-adjusted terminal-Mobius PSL covariance for the terminal-sheet
agreement data it constructs.

This is the natural componentwise boundary: loop-prepending may land in a
different selected terminal chart, and the chart transition at the endpoint is
included in the PSL comparison.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Coherent elementary grid walks and terminal-sheet local extension. -/
  elementaryGridLocalExtension :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
      x₀ g localModels
  /-- Transition-adjusted terminal-Mobius PSL covariance for the induced agreement data. -/
  terminalTransitionProjectionEquivariance :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
      elementaryGridLocalExtension.toCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The bound transition-adjusted data produce terminal-sheet agreement monodromy. -/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.terminalTransitionProjectionEquivariance.toAgreementMonodromyDataPSL

/-- The bound transition-adjusted data produce the canonical-cover PSL continuation record. -/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/-- The bound transition-adjusted data produce path-class PSL monodromy. -/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL

/--
Coherent elementary-grid/terminal-extension-agreement data together with
transition-adjusted terminal-Mobius PSL covariance for the terminal-sheet
agreement data it constructs.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Coherent elementary grid walks and terminal-sheet extension agreement. -/
  elementaryGridExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
      x₀ g localModels
  /-- Transition-adjusted terminal-Mobius PSL covariance for the induced agreement data. -/
  terminalTransitionProjectionEquivariance :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
      elementaryGridExtensionAgreement.toCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Forget terminal-extension agreement to transition-adjusted local-extension data. -/
noncomputable def toElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
      x₀ g localModels where
  elementaryGridLocalExtension :=
    D.elementaryGridExtensionAgreement.toElementaryGridLocalExtensionData
  terminalTransitionProjectionEquivariance :=
    D.terminalTransitionProjectionEquivariance

/-- The bound transition-adjusted data produce terminal-sheet agreement monodromy. -/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.terminalTransitionProjectionEquivariance.toAgreementMonodromyDataPSL

/-- The bound transition-adjusted data produce the canonical-cover PSL continuation record. -/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/-- The bound transition-adjusted data produce path-class PSL monodromy. -/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL

/--
Coherent elementary-grid/local-extension data together with automatic
endpoint-transition terminal-Mobius PSL covariance for the terminal-sheet
agreement data it constructs.

This is the preferred componentwise boundary: the local-transition atlas
supplies the endpoint chart transition, so callers only prove the resulting
PSL monodromy equality.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Coherent elementary grid walks and terminal-sheet local extension. -/
  elementaryGridLocalExtension :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
      x₀ g localModels
  /-- Automatic endpoint-transition terminal-Mobius PSL covariance for the induced agreement data. -/
  automaticTerminalTransitionProjectionEquivariance :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
      elementaryGridLocalExtension.toCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Automatic-transition bound data forget to transition-adjusted bound data. -/
noncomputable def toTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
      x₀ g localModels where
  elementaryGridLocalExtension := D.elementaryGridLocalExtension
  terminalTransitionProjectionEquivariance :=
    D.automaticTerminalTransitionProjectionEquivariance.toTerminalTransitionProjectionEquivarianceDataPSL

/-- The automatic-transition bound data produce terminal-sheet agreement monodromy. -/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.automaticTerminalTransitionProjectionEquivariance.toAgreementMonodromyDataPSL

/-- The automatic-transition bound data produce the canonical-cover PSL continuation record. -/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/-- The automatic-transition bound data produce path-class PSL monodromy. -/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL

/--
Coherent elementary-grid/terminal-extension-agreement data together with
automatic endpoint-transition terminal-Mobius PSL covariance for the
terminal-sheet agreement data it constructs.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Coherent elementary grid walks and terminal-sheet extension agreement. -/
  elementaryGridExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
      x₀ g localModels
  /-- Automatic endpoint-transition terminal-Mobius PSL covariance for the induced agreement data. -/
  automaticTerminalTransitionProjectionEquivariance :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
      elementaryGridExtensionAgreement.toCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Forget terminal-extension agreement to automatic-transition local-extension data. -/
noncomputable def toElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
      x₀ g localModels where
  elementaryGridLocalExtension :=
    D.elementaryGridExtensionAgreement.toElementaryGridLocalExtensionData
  automaticTerminalTransitionProjectionEquivariance :=
    D.automaticTerminalTransitionProjectionEquivariance

/-- Automatic-transition bound data forget to transition-adjusted bound data. -/
noncomputable def toTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
      x₀ g localModels where
  elementaryGridExtensionAgreement := D.elementaryGridExtensionAgreement
  terminalTransitionProjectionEquivariance :=
    D.automaticTerminalTransitionProjectionEquivariance.toTerminalTransitionProjectionEquivarianceDataPSL

/-- The automatic-transition bound data produce terminal-sheet agreement monodromy. -/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.automaticTerminalTransitionProjectionEquivariance.toAgreementMonodromyDataPSL

/-- The automatic-transition bound data produce the canonical-cover PSL continuation record. -/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/-- The automatic-transition bound data produce path-class PSL monodromy. -/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL

/--
Coherent elementary-grid/local-extension data together with derived-holonomy
automatic endpoint-transition terminal-Mobius PSL covariance for the
terminal-sheet agreement data it constructs.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Coherent elementary grid walks and terminal-sheet local extension. -/
  elementaryGridLocalExtension :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
      x₀ g localModels
  /-- Derived-holonomy automatic endpoint-transition PSL covariance for the induced agreement data. -/
  automaticTerminalTransitionProjectionDerivedHolonomy :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      elementaryGridLocalExtension.toCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Derived-holonomy bound data forget to automatic-transition bound data. -/
noncomputable def toAutomaticTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
      x₀ g localModels where
  elementaryGridLocalExtension := D.elementaryGridLocalExtension
  automaticTerminalTransitionProjectionEquivariance :=
    D.automaticTerminalTransitionProjectionDerivedHolonomy.toAutomaticTerminalTransitionProjectionEquivarianceDataPSL

/-- Derived-holonomy bound data forget to transition-adjusted bound data. -/
noncomputable def toTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
      x₀ g localModels :=
  D.toAutomaticTerminalTransitionProjectionDataPSL.toTerminalTransitionProjectionDataPSL

/-- The derived-holonomy bound data produce terminal-sheet agreement monodromy. -/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.automaticTerminalTransitionProjectionDerivedHolonomy.toAgreementMonodromyDataPSL

/-- The derived-holonomy bound data produce the canonical-cover PSL continuation record. -/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/-- The derived-holonomy bound data produce path-class PSL monodromy. -/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

/--
Coherent elementary-grid/terminal-extension-agreement data together with
derived-holonomy automatic endpoint-transition terminal-Mobius PSL covariance
for the terminal-sheet agreement data it constructs.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Coherent elementary grid walks and terminal-sheet extension agreement. -/
  elementaryGridExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
      x₀ g localModels
  /-- Derived-holonomy automatic endpoint-transition PSL covariance for the induced agreement data. -/
  automaticTerminalTransitionProjectionDerivedHolonomy :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      elementaryGridExtensionAgreement.toCanonicalSheetAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Forget terminal-extension agreement to derived-holonomy local-extension data. -/
noncomputable def toElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      x₀ g localModels where
  elementaryGridLocalExtension :=
    D.elementaryGridExtensionAgreement.toElementaryGridLocalExtensionData
  automaticTerminalTransitionProjectionDerivedHolonomy :=
    D.automaticTerminalTransitionProjectionDerivedHolonomy

/-- Derived-holonomy bound data forget to automatic-transition bound data. -/
noncomputable def toAutomaticTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
      x₀ g localModels where
  elementaryGridExtensionAgreement := D.elementaryGridExtensionAgreement
  automaticTerminalTransitionProjectionEquivariance :=
    D.automaticTerminalTransitionProjectionDerivedHolonomy.toAutomaticTerminalTransitionProjectionEquivarianceDataPSL

/-- Derived-holonomy bound data forget to transition-adjusted bound data. -/
noncomputable def toTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
      x₀ g localModels :=
  D.toAutomaticTerminalTransitionProjectionDataPSL.toTerminalTransitionProjectionDataPSL

/-- The derived-holonomy bound data produce terminal-sheet agreement monodromy. -/
noncomputable def toAgreementMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
      x₀ g localModels :=
  D.automaticTerminalTransitionProjectionDerivedHolonomy.toAgreementMonodromyDataPSL

/-- The derived-holonomy bound data produce the canonical-cover PSL continuation record. -/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/-- The derived-holonomy bound data produce path-class PSL monodromy. -/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels :=
  D.toAgreementMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
The older same-terminal-chart bound data are a special case of the
transition-adjusted bound data.
-/
noncomputable def toTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
      x₀ g localModels where
  elementaryGridLocalExtension := D.elementaryGridLocalExtension
  terminalTransitionProjectionEquivariance :=
    D.terminalProjectionEquivariance.toTerminalTransitionProjectionEquivarianceDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
The older same-terminal-chart terminal-extension bound data are a special case
of the transition-adjusted bound data.
-/
noncomputable def toTerminalTransitionProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
      x₀ g localModels where
  elementaryGridExtensionAgreement := D.elementaryGridExtensionAgreement
  terminalTransitionProjectionEquivariance :=
    D.terminalProjectionEquivariance.toTerminalTransitionProjectionEquivarianceDataPSL

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL

/--
PSL monodromy data for value-level finite-chain terminal continuation of a
local-transition atlas.
-/
structure PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Value-level finite-chain terminal continuation data. -/
  chainTerminalContinuation :
    PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
      x₀ g localModels
  /-- PSL-valued real holonomy obtained from loop monodromy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Loop-precomposition of paths gives the PSL action on chain values. -/
  chain_terminal_path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      chainTerminalContinuation.terminalValue (loop.trans p) =
        holonomy.upperHalfPlaneAction γ
          (chainTerminalContinuation.terminalValue p)

/--
PSL loop-equivariance data for already constructed value-level finite-chain
terminal continuation of a local-transition atlas.
-/
structure PathLocalTransitionChainTerminalBranchAnalyticContinuationValueEquivarianceDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (chainTerminalContinuation :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels) where
  /-- PSL-valued real holonomy obtained from loop monodromy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Loop-precomposition of paths gives the PSL action on chain values. -/
  chain_terminal_path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      chainTerminalContinuation.terminalValue (loop.trans p) =
        holonomy.upperHalfPlaneAction γ
          (chainTerminalContinuation.terminalValue p)

namespace PathLocalTransitionChainTerminalBranchAnalyticContinuationValueEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels}

/--
Value-level finite-chain continuation plus PSL loop equivariance give the
PSL finite-chain monodromy package.
-/
def toPathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL
    (E :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueEquivarianceDataPSL
        C) :
    PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL
      x₀ g localModels where
  chainTerminalContinuation := C
  holonomy := E.holonomy
  chain_terminal_path_equivariant := E.chain_terminal_path_equivariant

end PathLocalTransitionChainTerminalBranchAnalyticContinuationValueEquivarianceDataPSL

namespace PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Value-level finite-chain PSL monodromy data descend to PSL path-class
monodromy data.
-/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (M :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL
        x₀ g localModels) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels where
  pathClassContinuation :=
    M.chainTerminalContinuation.toPathClassLocalTransitionAnalyticContinuationData
  holonomy := M.holonomy
  pathClass_equivariant := by
    intro γ x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction hloop : FundamentalGroup.toPath γ⁻¹ using
          Path.Homotopic.Quotient.ind with
        | mk loop =>
            rw [← Path.Homotopic.Quotient.mk_trans]
            change
              M.chainTerminalContinuation.terminalValueAt x
                  (Path.Homotopic.Quotient.mk (loop.trans p)) =
                M.holonomy.upperHalfPlaneAction γ
                  (M.chainTerminalContinuation.terminalValueAt x
                    (Path.Homotopic.Quotient.mk p))
            rw [
              PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData.terminalValueAt_mk,
              PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData.terminalValueAt_mk]
            exact M.chain_terminal_path_equivariant γ loop p hloop.symm

end PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL

/--
Analytic continuation along actual paths from the basepoint.

This is the representative-path boundary before quotienting by endpoint-fixed
homotopy.  The invariance fields are the mathematical content that lets the
continued values and local branch witnesses descend to path-homotopy classes.
-/
structure PathAnalyticContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The value obtained by continuing along a representative path. -/
  valueAlong : ∀ {x : X}, Path x₀ x → ℍ
  /-- The selected local model controlling the branch near this path. -/
  centerAlong : ∀ {x : X}, Path x₀ x → X
  /-- The real Mobius postcomposition relating the branch to the selected model. -/
  mobiusAlong : ∀ {x : X}, Path x₀ x → RealMobiusRepresentative
  /-- The sheet neighborhood on the path-homotopy cover for this representative path. -/
  neighborhoodAlong :
    ∀ {x : X}, Path x₀ x → Set (PathHomotopyUniversalCover X x₀)
  /-- Continued values are invariant under endpoint-fixed path homotopy. -/
  value_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      valueAlong p = valueAlong q
  /-- The selected local model descends through endpoint-fixed path homotopy. -/
  center_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      centerAlong p = centerAlong q
  /-- The real Mobius branch representative descends through path homotopy. -/
  mobius_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      mobiusAlong p = mobiusAlong q
  /-- The sheet neighborhood descends through path homotopy. -/
  neighborhood_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      neighborhoodAlong p = neighborhoodAlong q
  /-- The representative-path sheet is open. -/
  isOpen_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x), IsOpen (neighborhoodAlong p)
  /-- The representative path lies in its sheet. -/
  mem_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x),
      (⟨x, Path.Homotopic.Quotient.mk p⟩ :
        PathHomotopyUniversalCover X x₀) ∈ neighborhoodAlong p
  /-- Points in the representative-path sheet project into the selected model domain. -/
  endpoint_mem_model_domain :
    ∀ {x : X} (p : Path x₀ x) y', y' ∈ neighborhoodAlong p →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt (centerAlong p)).domain
  /--
  On each representative-path sheet, continuation agrees with the selected
  local model up to real Mobius action.
  -/
  value_eq_on_neighborhood :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ neighborhoodAlong p →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      valueAlong p' =
        realMobiusRepresentativeAction (mobiusAlong p)
          ((localModels.chartAt (centerAlong p)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

end HyperbolicMetric

end

end JJMath
