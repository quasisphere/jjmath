import JJMath.Hyperbolic.Converse.Continuation.FinalAdaptersA

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
The selected terminal-sheet homotopy principle constructs selected
terminal-sheet agreement by choosing arbitrary based weak handoff skeletons.

%%handwave
name: Terminal-sheet homotopy compatibility produces canonical-sheet agreement
statement:
  If terminal branch values are compatible with homotopic local extensions
  for every pathwise family of skeletons, then choosing one skeleton along
  each based path produces canonical-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedTerminalSheetHomotopyPrinciple
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPrinciple :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
      X chosenLocalModels := by
  intro x₀ g
  let basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p :=
    fun {_} p =>
      Classical.choice
        (exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
          (chosenLocalModels g) p)
  exact
    ⟨pathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData_of_terminalSheetHomotopyPrinciple
      basedWeakHandoffAlong
      (hPrinciple x₀ g basedWeakHandoffAlong)⟩

/--
Selected reduced derived-holonomy covariance supplies the older derived
automatic endpoint-transition PSL covariance record.

%%handwave
name: Reduced covariance recovers a real projective holonomy representation
statement:
  If all adjusted terminal classes transform by the derived loop-terminal
  assignment $H$, then canonical-sheet agreement forces $H(1)=1$ and
  $H(\gamma\delta)=H(\gamma)H(\delta)$, so the reduced covariance data extend
  to covariance under a real projective holonomy representation.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL_of_selectedReducedDerivedHolonomyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL⟩

/--
Selected canonical-loop covariance supplies reduced derived-holonomy
covariance by recovering arbitrary loop representatives from the canonical
ones.

%%handwave
name: Canonical-loop covariance implies covariance for every representative
statement:
  If $[M_{L_\gamma*p}A]=H(\gamma)[M_p]$ holds for the fixed representative
  $L_\gamma$, then endpoint-fixed homotopy invariance of adjusted terminal
  classes gives the same identity for every loop representing $\gamma^{-1}$.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL_of_selectedCanonicalLoopCovarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toReducedDerivedHolonomyDataPSL⟩

/--
Selected normalized canonical-loop projection propagation supplies
canonical-loop covariance.

%%handwave
name: Path-independent normalized transport gives canonical-loop covariance
statement:
  If
  $N_\gamma(p)=[M_{L_\gamma*p}A][M_p]^{-1}$ is independent of $p$, then
  evaluating it on the base normalization path identifies it with
  $H(\gamma)$ and yields
  $[M_{L_\gamma*p}A]=H(\gamma)[M_p]$.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL_of_selectedNormalizedProjectionPropagationTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPropagation :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hPropagation x₀ g C with ⟨E⟩
  exact ⟨E.toCanonicalLoopCovarianceDataPSL⟩

/--
Selected canonical-cover constancy supplies normalized canonical-loop
projection propagation.

%%handwave
name: Coverwise constancy gives pathwise normalized transport
statement:
  If $N_\gamma$ is constant on the canonical cover, then evaluating it at
  the terminal lift represented by any based path $p$ and at the base lift
  gives $N_\gamma(p)=N_\gamma(p_0)$.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedConstancyOnCoverTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hConstancy :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hConstancy x₀ g C with ⟨E⟩
  exact ⟨E.toNormalizedProjectionPropagationDataPSL⟩

/--
Selected local constancy on the canonical cover supplies global constancy
there.

%%handwave
name: Local constancy on the canonical cover implies global constancy
statement:
  For each loop class $\gamma$, a locally constant normalized transport
  $N_\gamma:\widetilde X_{x_0}\to\mathrm{PSL}_2(\mathbb R)$ is constant
  because the canonical path-homotopy cover is preconnected.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL_of_selectedLocalConstancyOnCoverTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hLocal x₀ g C with ⟨E⟩
  exact ⟨E.toConstancyOnCoverDataPSL⟩

/--
Selected local constancy on the canonical cover is unconditional for
canonical-terminal-sheet agreement data.

This is the terminal-sheet-overlap route: no selected terminal-extension
chart-coherence hypothesis is required.

%%handwave
name: Terminal-sheet overlap makes normalized loop transport locally constant
statement:
  For every canonical-sheet continuation and loop class $\gamma$, terminal
  branch agreement on overlapping sheets implies that the normalized
  canonical-loop transport $N_\gamma$ is constant on a neighborhood of each
  point of the canonical cover.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL_of_terminalSheetOverlap
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  exact ⟨C.toLocalConstancyOnCoverDataPSL_of_terminalSheetOverlap⟩

/--
Selected local constancy on the canonical cover supplies normalized
canonical-loop projection propagation.

%%handwave
name: Local constancy gives path-independent normalized loop transport
statement:
  Local constancy of $N_\gamma$ on the preconnected canonical cover first
  gives global constancy, which then gives
  $N_\gamma(p)=N_\gamma(p_0)$ for every based path $p$.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedLocalConstancyOnCoverTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedConstancyOnCoverTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL_of_selectedLocalConstancyOnCoverTheoremPSL
      hLocal)

/--
Selected derived-holonomy automatic endpoint-transition covariance gives
selected automatic endpoint-transition terminal-Mobius covariance.

%%handwave
name: Derived loop holonomy gives ordinary terminal covariance
statement:
  If the derived loop-terminal assignment is multiplicative and adjusted
  terminal classes transform by it, then it defines a real projective
  holonomy representation $\rho$ satisfying
  $[M_{\gamma*p}A_{\gamma,p}]=\rho(\gamma)[M_p]$.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toAutomaticTerminalTransitionProjectionEquivarianceDataPSL⟩

/--
Automatic endpoint-transition covariance is a special case of the
transition-adjusted terminal-Mobius covariance theorem.

%%handwave
name: Canonical endpoint transitions supply transition-adjusted covariance
statement:
  Covariance for the terminal-chart transition canonically selected by the
  local atlas gives transition-adjusted covariance by choosing that
  representative and using its defining endpoint chart identity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toTerminalTransitionProjectionEquivarianceDataPSL⟩

/--
Derived-holonomy automatic endpoint-transition covariance is a special case
of transition-adjusted terminal-Mobius covariance.

%%handwave
name: Derived holonomy supplies transition-adjusted terminal covariance
statement:
  Covariance under the holonomy derived from loop-terminal classes first
  gives covariance for the canonical endpoint transitions and hence the
  general transition-adjusted terminal covariance data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
      hEquivariance)

/--
Selected terminal-sheet agreement plus selected transition-adjusted
terminal-Mobius PSL covariance give selected terminal-sheet agreement
monodromy.

%%handwave
name: Sheet agreement and terminal covariance give equivariant continuation
statement:
  Canonical-sheet agreement defines a single-valued map on the canonical
  cover; if adjusted terminal classes obey real projective covariance, then
  this map is deck-equivariant under the same holonomy representation.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalTransitionProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hAgreement x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toAgreementMonodromyDataPSL⟩

/--
Selected terminal-sheet agreement monodromy gives selected path-class PSL
monodromy.

%%handwave
name: Equivariant sheet continuation descends to path-class monodromy
statement:
  A deck-equivariant developing value obtained from canonical-sheet
  agreement determines path-class values $V(x,[p])$ with local terminal
  formulae and
  $V(x,\gamma^{-1}[p])=\rho(\gamma)V(x,[p])$.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreementMonodromyPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hAgreement x₀ g with ⟨M⟩
  exact ⟨M.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL⟩

/--
Selected terminal-sheet agreement plus selected transition-adjusted
terminal-Mobius PSL covariance give selected path-class PSL monodromy.

%%handwave
name: Sheet agreement and terminal covariance yield path-class monodromy
statement:
  Canonical-sheet agreement together with
  $[M_{\gamma*p}A_{\gamma,p}]=\rho(\gamma)[M_p]$ makes the induced cover map
  equivariant and therefore gives real-projective monodromy for the descended
  path-class continuation values.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalTransitionProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreementMonodromyPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalTransitionProjectionEquivariancePSL
      hAgreement hEquivariance)

/--
Selected PSL path-class local-transition monodromy data imply selected
PSL-valued reduced continuation fields.

%%handwave
name: Path-class monodromy produces equivariant canonical-cover fields
statement:
  Path-class values with local transition formulae and real projective
  monodromy define a deck-equivariant map on the canonical cover; local model
  agreement then supplies its continuity, holomorphicity, nonvanishing
  derivative, and metric-pullback identity.
-/
def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL.toDerivedRegularityFieldsPSL

end HyperbolicMetric

end

end JJMath
