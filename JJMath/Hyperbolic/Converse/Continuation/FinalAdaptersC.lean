import JJMath.Hyperbolic.Converse.Continuation.FinalAdaptersB

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
Selected terminal-sheet agreement plus selected transition-adjusted
terminal-Mobius PSL covariance imply selected PSL-valued reduced continuation
fields.

%%handwave
name: Sheet agreement and projective covariance produce developing fields
statement:
  If pathwise continuation branches agree on canonical terminal sheets and
  their transition-adjusted terminal classes satisfy
  $[M_{\gamma*p}A_{\gamma,p}]=\rho(\gamma)[M_p]$, then for every $x_0,g$
  they define a deck-equivariant developing map on the canonical cover,
  locally modeled on the selected atlas.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalTransitionProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalTransitionProjectionEquivariancePSL
      hAgreement hEquivariance)

/--
Selected terminal-sheet homotopy plus transition-adjusted terminal-Mobius PSL
covariance imply selected PSL-valued reduced continuation fields.

%%handwave
name: Terminal-sheet homotopy and projective covariance produce developing fields
statement:
  If continuation is compatible with homotopic extensions inside terminal
  sheets and adjusted terminal classes transform by real projective holonomy,
  then choosing one skeleton along each path yields a deck-equivariant
  developing map with local model agreement on the canonical cover.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedTerminalTransitionProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPrinciple :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalTransitionProjectionEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedTerminalSheetHomotopyPrinciple
      hPrinciple)
    hEquivariance

/--
Selected terminal-sheet homotopy plus local constancy on the canonical cover of
the normalized canonical-loop projection imply selected PSL-valued reduced
continuation fields.

%%handwave
name: Terminal-sheet homotopy and locally constant loop transport produce developing fields
statement:
  If terminal-sheet homotopy compatibility holds and every normalized
  canonical-loop transport $N_\gamma$ is locally constant on the canonical
  cover, then these transports yield real projective holonomy and a
  deck-equivariant developing map locally modeled on the selected atlas.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedLocalConstancyOnCoverPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPrinciple :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
        X chosenLocalModels)
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedTerminalTransitionProjectionEquivariancePSL
    hPrinciple
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
      (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL_of_selectedReducedDerivedHolonomyTheoremPSL
        (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL_of_selectedCanonicalLoopCovarianceTheoremPSL
          (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL_of_selectedNormalizedProjectionPropagationTheoremPSL
            (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedLocalConstancyOnCoverTheoremPSL
              hLocal)))))

/--
Selected finite homotopy-grid walks and same-path terminal-value uniqueness
imply selected PSL-valued reduced continuation fields.

The monodromy/local-constancy input is supplied unconditionally by
terminal-sheet overlap on the canonical cover.

%%handwave
name: Grid invariance and pathwise uniqueness produce developing fields
statement:
  If homotopic paths are related by terminal-value-preserving grid walks and
  all skeletons over one path have the same terminal value, then terminal
  continuation descends to a deck-equivariant developing map on the canonical
  cover; terminal-sheet overlap supplies the required local constancy of loop
  transport.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hUnique :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedLocalConstancyOnCoverPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
      hGrid hUnique)
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL_of_terminalSheetOverlap
      chosenLocalModels)
