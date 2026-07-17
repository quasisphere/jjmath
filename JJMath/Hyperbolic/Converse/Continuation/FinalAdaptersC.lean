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
Selected value-level finite-chain PSL monodromy data imply selected
PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathChainTerminalBranchValueMonodromyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedPathChainTerminalBranchValueMonodromyTheoremPSL
      h)

/--
Selected bound elementary-grid/local-extension terminal-projection data imply
selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridLocalExtensionTerminalProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridLocalExtensionTerminalProjectionDataPSL
      h)

/--
Selected bound elementary-grid/terminal-extension-agreement terminal-projection
data imply selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridExtensionAgreementTerminalProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionAgreementTerminalProjectionDataPSL
      h)

/--
Selected coherent elementary-grid/PSL-terminal-extension-agreement data imply
selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridExtensionProjectionAgreementData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionProjectionAgreementDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionProjectionAgreementData
      h)

/--
Selected bound elementary-grid/local-extension transition-adjusted
terminal-projection data imply selected PSL-valued reduced continuation
fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
      h)

/--
Selected bound elementary-grid/terminal-extension-agreement transition-adjusted
terminal-projection data imply selected PSL-valued reduced continuation
fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
      h)

/--
Selected bound elementary-grid/local-extension automatic endpoint-transition
terminal-projection data imply selected PSL-valued reduced continuation
fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
      h)

/--
Selected bound elementary-grid/terminal-extension-agreement automatic
endpoint-transition terminal-projection data imply selected PSL-valued reduced
continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
      h)

/--
Selected bound elementary-grid/local-extension derived-holonomy automatic
endpoint-transition terminal-projection data imply selected PSL-valued reduced
continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      h)

/--
Selected bound elementary-grid/terminal-extension-agreement derived-holonomy
automatic endpoint-transition terminal-projection data imply selected
PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      h)

/--
Selected value-level finite-chain continuation plus selected PSL loop
equivariance imply selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathChainTerminalBranchValueContinuation_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hContinuation :
      SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathChainTerminalBranchValueMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheoremPSL_of_selectedValueContinuation_and_selectedValueEquivariancePSL
      hContinuation hEquivariance)

/--
Selected path-class local-transition continuation plus PSL loop equivariance
imply the selected PSL-valued reduced continuation fields.
-/
def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassContinuation_and_selectedPathClassEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hContinuation :
      SelectedLocalTransitionModelAnalyticContinuationPathClassContinuationTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathClassEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedPathClassContinuation_and_selectedPathClassEquivariancePSL
      hContinuation hEquivariance)

/--
Selected terminal-sheet agreement plus selected path-level PSL loop
equivariance imply selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
      hAgreement hEquivariance)

/--
Selected terminal-sheet agreement plus selected terminal-Mobius PSL covariance
imply selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedPathClassMonodromyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalProjectionEquivariancePSL
      hAgreement hEquivariance)

/--
Selected terminal-sheet agreement plus selected transition-adjusted
terminal-Mobius PSL covariance imply selected PSL-valued reduced continuation
fields.
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
Selected terminal-sheet homotopy plus path-level PSL loop equivariance imply
selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPrinciple :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedTerminalSheetHomotopyPrinciple
      hPrinciple)
    hEquivariance

/--
Selected terminal-sheet homotopy plus transition-adjusted terminal-Mobius PSL
covariance imply selected PSL-valued reduced continuation fields.
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
Selected terminal-sheet homotopy plus local-sheet constancy of the normalized
canonical-loop projection imply selected PSL-valued reduced continuation
fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedLocalSheetConstancyPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPrinciple :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
        X chosenLocalModels)
    (hLocalSheet :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedLocalConstancyOnCoverPSL
    hPrinciple
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL_of_selectedLocalSheetConstancyTheoremPSL
      hLocalSheet)

/--
Selected terminal-sheet homotopy plus terminal-sheet transport of the
normalized canonical-loop projection imply selected PSL-valued reduced
continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedTerminalSheetTransportPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPrinciple :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
        X chosenLocalModels)
    (hTransport :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedLocalSheetConstancyPSL
    hPrinciple
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL_of_selectedTerminalSheetTransportTheoremPSL
      hTransport)

/--
Selected finite homotopy-grid walks, terminal-sheet local extension, and
path-level PSL loop equivariance imply selected PSL-valued reduced
continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedTerminalSheetLocalExtension_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedAgreementValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedLocalExtension
      hGrid hLocal)
    hEquivariance

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and path-level PSL loop equivariance imply selected PSL-valued reduced
continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedAgreementValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison
      hGrid hComparison)
    hEquivariance

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and path-class PSL equivariance imply selected PSL-valued reduced continuation
fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedPathClassEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathClassEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedAgreementValueEquivariancePSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedCanonicalSheetValueEquivarianceTheoremPSL
      (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueEquivarianceTheoremPSL_of_selectedPathClassEquivarianceTheoremPSL
        hEquivariance))

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and transition-adjusted terminal-Mobius PSL covariance imply selected
PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedTerminalTransitionProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedTerminalSheetHomotopyPrinciple_and_selectedTerminalTransitionProjectionEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison
      hGrid hComparison)
    hEquivariance

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and derived-holonomy automatic endpoint-transition PSL covariance imply
selected PSL-valued reduced continuation fields.

This is the same route as the transition-adjusted terminal-Mobius covariance
constructor, but with the holonomy fixed to the loop-terminal class derived
from the continuation data.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedTerminalTransitionProjectionEquivariancePSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
      hEquivariance)

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and reduced derived-holonomy PSL covariance imply selected PSL-valued reduced
continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedReducedDerivedHolonomyPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyPSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL_of_selectedReducedDerivedHolonomyTheoremPSL
      hEquivariance)

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and canonical-loop PSL covariance imply selected PSL-valued reduced
continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedCanonicalLoopCovariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedReducedDerivedHolonomyPSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL_of_selectedCanonicalLoopCovarianceTheoremPSL
      hEquivariance)

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and normalized canonical-loop projection propagation imply selected PSL-valued
reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedNormalizedProjectionPropagationPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hPropagation :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedCanonicalLoopCovariancePSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL_of_selectedNormalizedProjectionPropagationTheoremPSL
      hPropagation)

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and canonical-cover constancy of the normalized canonical-loop projection
imply selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedConstancyOnCoverPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hConstancy :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedNormalizedProjectionPropagationPSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedConstancyOnCoverTheoremPSL
      hConstancy)

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and local constancy on the canonical cover of the normalized canonical-loop
projection imply selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedLocalConstancyOnCoverPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedConstancyOnCoverPSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL_of_selectedLocalConstancyOnCoverTheoremPSL
      hLocal)

/--
Selected finite homotopy-grid walks and same-path common-refinement
comparisons imply selected PSL-valued reduced continuation fields.

The monodromy/local-constancy input is now supplied unconditionally by
terminal-sheet overlap on the canonical cover.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedLocalConstancyOnCoverPSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL_of_terminalSheetOverlap
      chosenLocalModels)

/--
Selected finite homotopy-grid walks and same-path terminal-value uniqueness
imply selected PSL-valued reduced continuation fields.

The monodromy/local-constancy input is supplied unconditionally by
terminal-sheet overlap on the canonical cover.
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

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and local-sheet constancy of the normalized canonical-loop projection imply
selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedLocalSheetConstancyPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hLocalSheet :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedLocalConstancyOnCoverPSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL_of_selectedLocalSheetConstancyTheoremPSL
      hLocalSheet)

/--
Selected finite homotopy-grid walks, same-path common-refinement comparisons,
and terminal-sheet transport of the normalized canonical-loop projection imply
selected PSL-valued reduced continuation fields.
-/
noncomputable def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedTerminalSheetTransportPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels)
    (hTransport :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison_and_selectedLocalSheetConstancyPSL
    hGrid hComparison
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL_of_selectedTerminalSheetTransportTheoremPSL
      hTransport)

/--
Selected reduced local-transition canonical-cover fields imply ordinary
selected local-transition continuation fields.
-/
def selectedLocalTransitionModelContinuationFieldTheorem_of_derivedRegularityCanonicalCoverMetricFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationFieldTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationFieldTheorem_of_canonicalCoverMetricFieldTheorem
    (selectedLocalTransitionModelContinuationCanonicalCoverMetricFieldTheorem_of_derivedRegularityCanonicalCoverMetricFieldTheorem
      h)

/-- The arbitrary local-transition field theorem specializes to a selected atlas. -/
def selectedLocalTransitionModelContinuationFieldTheorem_of_fieldTheorem
    (h : AnalyticContinuationFromLocalTransitionModelsFieldTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelContinuationFieldTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The arbitrary canonical-cover local-transition theorem specializes to a
selected atlas.
-/
def selectedLocalTransitionModelContinuationCanonicalCoverMetricFieldTheorem_of_fieldTheorem
    (h :
      AnalyticContinuationFromLocalTransitionModelsCanonicalCoverMetricFieldTheorem
        X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelContinuationCanonicalCoverMetricFieldTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The arbitrary derived-regularity local-transition theorem specializes to a
selected atlas.
-/
def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem_of_fieldTheorem
    (h :
      AnalyticContinuationFromLocalTransitionModelsDerivedRegularityCanonicalCoverMetricFieldTheorem
        X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The arbitrary local-transition monodromy theorem specializes to a selected
atlas.
-/
def selectedLocalTransitionModelAnalyticContinuationMonodromyTheorem_of_monodromyTheorem
    (h :
      AnalyticContinuationFromLocalTransitionModelsMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelAnalyticContinuationMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The arbitrary local-transition monodromy theorem gives the selected reduced
field theorem for any selected local-transition atlas.
-/
def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem_of_monodromyTheorem
    (h :
      AnalyticContinuationFromLocalTransitionModelsMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem_of_selectedMonodromyTheorem
    (selectedLocalTransitionModelAnalyticContinuationMonodromyTheorem_of_monodromyTheorem
      h chosenLocalModels)

/-- The arbitrary local-transition theorem specializes to a selected atlas. -/
def selectedLocalTransitionModelContinuationTheorem_of_theorem
    (h : AnalyticContinuationFromLocalTransitionModelsTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelContinuationTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The old global-overlap continuation theorem gives local-transition
continuation for every atlas that came with global overlap representatives.
-/
@[reducible] def analyticContinuationFromLocalModelsTheorem_to_localTransitionContinuation
    (h : AnalyticContinuationFromLocalModelsTheorem X) :
    ∀ (x₀ : X) (g : HyperbolicMetric X)
      (localModels : HyperbolicLocalModelAtlas X g),
      Nonempty
        (ContinuationFromLocalTransitionModels
          x₀ g localModels.toLocalTransitionAtlas) := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    ContinuationFromLocalTransitionModels.ofGlobalContinuation

/--
The reduced continuation boundary also implies the ordinary local-model
continuation theorem.
-/
def analyticContinuationFromLocalModelsTheorem_of_derivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X) :
    AnalyticContinuationFromLocalModelsTheorem X :=
  analyticContinuationFromLocalModelsTheorem_of_analyticContinuationFromLocalModelsFieldTheorem
    (analyticContinuationFromLocalModelsFieldTheorem_of_derivedRegularityFieldTheorem h)

/--
Forget the fixed local-model provenance and keep continuation from
curvature-derived local constructions, provided the fixed local model atlas is
the one obtained from those local constructions.
-/
def continuationFromCurvatureLocalConstructions_of_continuationFromLocalModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localCurvatureConstructions :
      g.HasCurvatureLiouvilleDevelopingConstructionAtlas}
    {localModels : HyperbolicLocalModelAtlas X g}
    (C : ContinuationFromLocalModels x₀ g localModels)
    (hlocal :
      localModels =
        localModelsFromCurvatureConstructions g localCurvatureConstructions) :
    ContinuationFromCurvatureLocalConstructions x₀ g localCurvatureConstructions where
  continuationData := C.toHyperbolicDevelopingContinuationData
  continuation_uses_curvature_constructions := by
    calc
      C.toHyperbolicDevelopingContinuationData.localModels
          = C.continuationPipeline.continuationData.localModels := by
            rfl
      _ = C.continuationPipeline.localModels :=
            C.continuationPipeline.continuation_uses_localModels
      _ = localModels := C.continuation_uses_localModels
      _ = localModelsFromCurvatureConstructions g localCurvatureConstructions := hlocal

/--
Continuation for arbitrary local model atlases specializes to continuation for
curvature-derived local constructions.
-/
def analyticContinuationFromLocalSolvingTheorem_of_analyticContinuationFromLocalModelsTheorem
    (h : AnalyticContinuationFromLocalModelsTheorem X) :
    AnalyticContinuationFromLocalSolvingTheorem X :=
  fun x₀ g localCurvatureConstructions ↦
    h x₀ g (localModelsFromCurvatureConstructions g localCurvatureConstructions) |>.map
      fun C ↦
        continuationFromCurvatureLocalConstructions_of_continuationFromLocalModels
          C rfl

/--
Explicit continuation fields for arbitrary local model atlases specialize to
continuation for curvature-derived local constructions.
-/
def analyticContinuationFromLocalSolvingTheorem_of_analyticContinuationFromLocalModelsFieldTheorem
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X) :
    AnalyticContinuationFromLocalSolvingTheorem X :=
  analyticContinuationFromLocalSolvingTheorem_of_analyticContinuationFromLocalModelsTheorem
    (analyticContinuationFromLocalModelsTheorem_of_analyticContinuationFromLocalModelsFieldTheorem h)

/--
Reduced continuation fields for arbitrary local model atlases specialize to
continuation for curvature-derived local constructions.
-/
def analyticContinuationFromLocalSolvingTheorem_of_derivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X) :
    AnalyticContinuationFromLocalSolvingTheorem X :=
  analyticContinuationFromLocalSolvingTheorem_of_analyticContinuationFromLocalModelsTheorem
    (analyticContinuationFromLocalModelsTheorem_of_derivedRegularityFieldTheorem h)

theorem hasLocalModelContinuationPipeline_of_continuationFromLocalModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (h : Nonempty (ContinuationFromLocalModels x₀ g localModels)) :
    g.HasLocalModelContinuationPipeline x₀ :=
  h.map ContinuationFromLocalModels.toHyperbolicLocalModelContinuationPipeline

theorem hasDevelopingContinuationData_of_continuationFromLocalModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (h : Nonempty (ContinuationFromLocalModels x₀ g localModels)) :
    g.HasDevelopingContinuationData x₀ :=
  h.map ContinuationFromLocalModels.toHyperbolicDevelopingContinuationData

theorem admitsLiftedDevelopingMap_of_continuationFromLocalModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (h : Nonempty (ContinuationFromLocalModels x₀ g localModels)) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  h.map ContinuationFromLocalModels.toLiftedHyperbolicDevelopingMap

theorem admitsDevelopingMap_of_continuationFromLocalModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (h : Nonempty (ContinuationFromLocalModels x₀ g localModels)) :
    g.AdmitsDevelopingMap x₀ :=
  h.map ContinuationFromLocalModels.toHyperbolicDevelopingMap

theorem admitsLiftedDevelopingMap_of_continuationFromLocalTransitionModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (h : Nonempty (ContinuationFromLocalTransitionModels x₀ g localModels)) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  h.map ContinuationFromLocalTransitionModels.toLiftedHyperbolicDevelopingMap

theorem admitsDevelopingMap_of_continuationFromLocalTransitionModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (h : Nonempty (ContinuationFromLocalTransitionModels x₀ g localModels)) :
    g.AdmitsDevelopingMap x₀ :=
  h.map ContinuationFromLocalTransitionModels.toHyperbolicDevelopingMap

theorem admitsProjectivizedDevelopingMap_of_continuationFromLocalTransitionModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (h : Nonempty (ContinuationFromLocalTransitionModels x₀ g localModels)) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_admitsLiftedDevelopingMap
    (admitsLiftedDevelopingMap_of_continuationFromLocalTransitionModels h)

theorem admitsLiftedDevelopingMap_of_selectedLocalTransitionModelContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationTheorem
        X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_continuationFromLocalTransitionModels
    (h x₀ g)

theorem admitsDevelopingMap_of_selectedLocalTransitionModelContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationTheorem
        X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_continuationFromLocalTransitionModels
    (h x₀ g)

theorem admitsProjectivizedDevelopingMap_of_selectedLocalTransitionModelContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationTheorem
        X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_continuationFromLocalTransitionModels
    (h x₀ g)

theorem admitsLiftedDevelopingMap_of_selectedLocalTransitionModelContinuationFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationFieldTheorem
        X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_selectedLocalTransitionModelContinuationTheorem
    (selectedLocalTransitionModelContinuationTheorem_of_fieldTheorem h)
    x₀ g

theorem admitsDevelopingMap_of_selectedLocalTransitionModelContinuationFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationFieldTheorem
        X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_selectedLocalTransitionModelContinuationTheorem
    (selectedLocalTransitionModelContinuationTheorem_of_fieldTheorem h)
    x₀ g

theorem admitsProjectivizedDevelopingMap_of_selectedLocalTransitionModelContinuationFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationFieldTheorem
        X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_selectedLocalTransitionModelContinuationTheorem
    (selectedLocalTransitionModelContinuationTheorem_of_fieldTheorem h)
    x₀ g

/--
PSL-valued selected reduced continuation fields give an ordinary developing
map, without requiring an `SL(2, ℝ)` holonomy lift.
-/
theorem admitsDevelopingMap_of_selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
        X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsDevelopingMap x₀ :=
  h x₀ g |>.map
    HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL.toHyperbolicDevelopingMap

/--
PSL-valued selected reduced continuation fields give a projectivized
developing map by projectivizing the PSL-valued developing map directly.
-/
theorem admitsProjectivizedDevelopingMap_of_selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
        X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_admitsDevelopingMap
    (admitsDevelopingMap_of_selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      h x₀ g)

theorem hasLocalModelContinuationPipeline_of_analyticContinuationFromLocalModelsTheorem
    (h : AnalyticContinuationFromLocalModelsTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_continuationFromLocalModels
    (h x₀ g localModels)

theorem hasDevelopingContinuationData_of_analyticContinuationFromLocalModelsTheorem
    (h : AnalyticContinuationFromLocalModelsTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.HasDevelopingContinuationData x₀ :=
  hasDevelopingContinuationData_of_continuationFromLocalModels
    (h x₀ g localModels)

theorem admitsLiftedDevelopingMap_of_analyticContinuationFromLocalModelsTheorem
    (h : AnalyticContinuationFromLocalModelsTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_continuationFromLocalModels
    (h x₀ g localModels)

theorem admitsDevelopingMap_of_analyticContinuationFromLocalModelsTheorem
    (h : AnalyticContinuationFromLocalModelsTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_continuationFromLocalModels
    (h x₀ g localModels)

theorem hasLocalModelContinuationPipeline_of_analyticContinuationFromLocalModelsFieldTheorem
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_analyticContinuationFromLocalModelsTheorem
    (analyticContinuationFromLocalModelsTheorem_of_analyticContinuationFromLocalModelsFieldTheorem h)
    x₀ g localModels

theorem hasDevelopingContinuationData_of_analyticContinuationFromLocalModelsFieldTheorem
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.HasDevelopingContinuationData x₀ :=
  hasDevelopingContinuationData_of_analyticContinuationFromLocalModelsTheorem
    (analyticContinuationFromLocalModelsTheorem_of_analyticContinuationFromLocalModelsFieldTheorem h)
    x₀ g localModels

theorem admitsLiftedDevelopingMap_of_analyticContinuationFromLocalModelsFieldTheorem
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_analyticContinuationFromLocalModelsTheorem
    (analyticContinuationFromLocalModelsTheorem_of_analyticContinuationFromLocalModelsFieldTheorem h)
    x₀ g localModels

theorem admitsDevelopingMap_of_analyticContinuationFromLocalModelsFieldTheorem
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_analyticContinuationFromLocalModelsTheorem
    (analyticContinuationFromLocalModelsTheorem_of_analyticContinuationFromLocalModelsFieldTheorem h)
    x₀ g localModels

theorem hasLocalModelContinuationPipeline_of_analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_analyticContinuationFromLocalModelsFieldTheorem
    (analyticContinuationFromLocalModelsFieldTheorem_of_derivedRegularityFieldTheorem h)
    x₀ g localModels

theorem hasDevelopingContinuationData_of_analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.HasDevelopingContinuationData x₀ :=
  hasDevelopingContinuationData_of_analyticContinuationFromLocalModelsFieldTheorem
    (analyticContinuationFromLocalModelsFieldTheorem_of_derivedRegularityFieldTheorem h)
    x₀ g localModels

theorem admitsLiftedDevelopingMap_of_analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_analyticContinuationFromLocalModelsFieldTheorem
    (analyticContinuationFromLocalModelsFieldTheorem_of_derivedRegularityFieldTheorem h)
    x₀ g localModels

theorem admitsDevelopingMap_of_analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X)
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_analyticContinuationFromLocalModelsFieldTheorem
    (analyticContinuationFromLocalModelsFieldTheorem_of_derivedRegularityFieldTheorem h)
    x₀ g localModels

/--
Explicit continuation fields only for a fixed selected local model atlas.

This is the smaller continuation target needed by packages that have already
chosen their local curvature-solving atlas.
-/
def SelectedLocalModelContinuationFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (HyperbolicDevelopingContinuationDataFields x₀ g (chosenLocalModels g))

/--
Reduced continuation fields only for a fixed selected local model atlas.

This is the selected-atlas version of
`AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem`: the
canonical cover, canonical pulled-back metric, and developing-map regularity
are no longer separate selected-continuation obligations.
-/
def SelectedLocalModelContinuationDerivedRegularityFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g (chosenLocalModels g))

/--
The monodromy boundary only for a fixed selected local model atlas.

This is the selected-atlas version of `AnalyticContinuationMonodromyTheorem`.
It asks for the actual path-continuation output: sheetwise local formulas on
the canonical cover plus real Mobius deck equivariance.
-/
def SelectedLocalModelAnalyticContinuationMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty (AnalyticContinuationMonodromyData x₀ g (chosenLocalModels g))

/--
The path-class monodromy boundary only for a fixed selected local model atlas.
-/
def SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathClassAnalyticContinuationMonodromyData
        x₀ g (chosenLocalModels g))

/--
Selected path-class continuation before loop monodromy/equivariance is
imposed.
-/
def SelectedLocalModelAnalyticContinuationPathClassContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathClassAnalyticContinuationData x₀ g (chosenLocalModels g))

/--
Selected loop-equivariance theorem for already constructed path-class
continuation data.
-/
def SelectedLocalModelAnalyticContinuationPathClassEquivarianceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (pathClassContinuation :
      PathClassAnalyticContinuationData x₀ g (chosenLocalModels g)),
    Nonempty
      (PathClassAnalyticContinuationEquivarianceData
        pathClassContinuation)

/--
Selected path-class continuation plus selected loop equivariance give selected
path-class monodromy.
-/
def selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathClassContinuation_and_selectedPathClassEquivariance
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (hContinuation :
      SelectedLocalModelAnalyticContinuationPathClassContinuationTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalModelAnalyticContinuationPathClassEquivarianceTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hContinuation x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact
    ⟨E.toPathClassAnalyticContinuationMonodromyData⟩

/--
The representative-path monodromy boundary only for a fixed selected local
model atlas.
-/
def SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathAnalyticContinuationMonodromyData
        x₀ g (chosenLocalModels g))

/--
Selected representative-path continuation before loop monodromy/equivariance
is imposed.
-/
def SelectedLocalModelAnalyticContinuationPathContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathAnalyticContinuationData x₀ g (chosenLocalModels g))

/--
Selected loop-equivariance theorem for already constructed representative-path
continuation data.
-/
def SelectedLocalModelAnalyticContinuationPathEquivarianceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (pathContinuation :
      PathAnalyticContinuationData x₀ g (chosenLocalModels g)),
    Nonempty
      (PathAnalyticContinuationEquivarianceData
        pathContinuation)

/--
Selected representative-path continuation plus selected loop equivariance give
selected representative-path monodromy.
-/
def selectedLocalModelAnalyticContinuationPathMonodromyTheorem_of_selectedPathContinuation_and_selectedPathEquivariance
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (hContinuation :
      SelectedLocalModelAnalyticContinuationPathContinuationTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalModelAnalyticContinuationPathEquivarianceTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hContinuation x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact
    ⟨E.toPathAnalyticContinuationMonodromyData⟩

/--
The terminal-branch representative-path monodromy boundary only for a fixed
selected local model atlas.
-/
def SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathTerminalBranchAnalyticContinuationMonodromyData
        x₀ g (chosenLocalModels g))

/--
The finite-chain terminal-branch representative-path monodromy boundary only
for a fixed selected local model atlas.
-/
def SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathChainTerminalBranchAnalyticContinuationMonodromyData
        x₀ g (chosenLocalModels g))

/--
The finite-chain terminal-branch representative-path monodromy boundary only
for a fixed selected local model atlas, with only value-level homotopy descent
of terminal branches.
-/
def SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathChainTerminalBranchAnalyticContinuationValueMonodromyData
        x₀ g (chosenLocalModels g))

/--
Selected finite-chain terminal-branch value-continuation theorem before loop
monodromy/equivariance is imposed.
-/
def SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathChainTerminalBranchAnalyticContinuationValueData
        x₀ g (chosenLocalModels g))

/--
Selected loop-equivariance theorem for value-level finite-chain terminal
continuation data.
-/
def SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueEquivarianceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (chainTerminalContinuation :
      PathChainTerminalBranchAnalyticContinuationValueData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathChainTerminalBranchAnalyticContinuationValueEquivarianceData
        chainTerminalContinuation)

/--
Selected value-continuation plus selected loop equivariance give selected
value-level finite-chain terminal-branch monodromy.
-/
def selectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem_of_selectedValueContinuation_and_selectedValueEquivariance
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (hContinuation :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueEquivarianceTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hContinuation x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact
    ⟨E.toPathChainTerminalBranchAnalyticContinuationValueMonodromyData⟩

/--
An arbitrary-atlas value-continuation theorem restricts to any selected local
model atlas.
-/
def selectedLocalModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem_of_valueContinuationTheorem
    (h :
      AnalyticContinuationPathChainTerminalBranchValueContinuationTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact h x₀ g (chosenLocalModels g)

/--
An arbitrary-atlas value-equivariance theorem restricts to any selected local
model atlas.
-/
def selectedLocalModelAnalyticContinuationPathChainTerminalBranchValueEquivarianceTheorem_of_valueEquivarianceTheorem
    (h :
      AnalyticContinuationPathChainTerminalBranchValueEquivarianceTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueEquivarianceTheorem
      X chosenLocalModels := by
  intro x₀ g C
  exact h x₀ g (chosenLocalModels g) C

/--
Selected finite-chain terminal-branch monodromy data imply selected
terminal-branch monodromy data.
-/
def selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathChainTerminalBranchAnalyticContinuationMonodromyData.toPathTerminalBranchAnalyticContinuationMonodromyData

/--
Selected strong finite-chain terminal-branch monodromy data imply the weaker
selected value-level finite-chain monodromy boundary.
-/
def selectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathChainTerminalBranchAnalyticContinuationMonodromyData.toPathChainTerminalBranchAnalyticContinuationValueMonodromyData

/--
Selected terminal-branch monodromy data imply selected representative-path
monodromy data.
-/
def selectedLocalModelAnalyticContinuationPathMonodromyTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathTerminalBranchAnalyticContinuationMonodromyData.toPathAnalyticContinuationMonodromyData

/--
Selected representative-path monodromy data imply selected path-class
monodromy data.
-/
def selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathAnalyticContinuationMonodromyData.toPathClassAnalyticContinuationMonodromyData

/--
Selected terminal-branch monodromy data imply selected path-class monodromy
data.
-/
def selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathTerminalBranchAnalyticContinuationMonodromyData.toPathClassAnalyticContinuationMonodromyData

/--
Selected finite-chain terminal-branch monodromy data imply selected
representative-path monodromy data.
-/
def selectedLocalModelAnalyticContinuationPathMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
      X chosenLocalModels :=
  selectedLocalModelAnalyticContinuationPathMonodromyTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
      h)

/--
Selected finite-chain terminal-branch monodromy data imply selected path-class
monodromy data.
-/
def selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
      X chosenLocalModels :=
  selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
      h)

/--
Selected value-level finite-chain terminal-branch monodromy data imply
selected path-class monodromy data.
-/
noncomputable def selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathChainTerminalBranchValueMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathChainTerminalBranchAnalyticContinuationValueMonodromyData.toPathClassAnalyticContinuationMonodromyData

/--
Selected path-class monodromy data imply selected cover-level monodromy data.
-/
def selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathClassMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathClassAnalyticContinuationMonodromyData.toAnalyticContinuationMonodromyData

/--
Selected representative-path monodromy data imply selected cover-level
monodromy data.
-/
def selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationMonodromyTheorem
      X chosenLocalModels :=
  selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathClassMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathMonodromyTheorem h)

/--
Selected terminal-branch monodromy data imply selected cover-level monodromy
data.
-/
def selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathTerminalBranchAnalyticContinuationMonodromyData.toAnalyticContinuationMonodromyData

/--
Selected finite-chain terminal-branch monodromy data imply selected cover-level
monodromy data.
-/
def selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationMonodromyTheorem
      X chosenLocalModels :=
  selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
      h)

/--
Selected value-level finite-chain terminal-branch monodromy data imply
selected cover-level monodromy data.
-/
noncomputable def selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathChainTerminalBranchValueMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelAnalyticContinuationMonodromyTheorem
      X chosenLocalModels :=
  selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathClassMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathChainTerminalBranchValueMonodromyTheorem
      h)

/--
Continuation theorem only for a fixed selected local model atlas.
-/
def SelectedLocalModelContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty (ContinuationFromLocalModels x₀ g (chosenLocalModels g))

/--
Explicit selected-atlas continuation fields fold into the selected-atlas
continuation package.
-/
def selectedLocalModelContinuationTheorem_of_selectedFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationFieldTheorem X chosenLocalModels) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      HyperbolicDevelopingContinuationDataFields.toContinuationFromLocalModels

/--
Reduced selected-atlas continuation fields fold into the original selected
field theorem.
-/
def selectedLocalModelContinuationFieldTheorem_of_selectedDerivedRegularityFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelContinuationDerivedRegularityFieldTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity.toHyperbolicDevelopingContinuationDataFields

/--
Selected-atlas monodromy data imply the selected reduced continuation fields.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      AnalyticContinuationMonodromyData.toDerivedRegularityFields

/--
Selected-atlas path-class monodromy data imply the selected reduced
continuation fields.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathClassMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedMonodromyTheorem
    (selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathClassMonodromyTheorem h)

/--
Selected-atlas representative-path monodromy data imply the selected reduced
continuation fields.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathClassMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathMonodromyTheorem h)

/--
Selected-atlas terminal-branch monodromy data imply the selected reduced
continuation fields.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedMonodromyTheorem
    (selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathTerminalBranchMonodromyTheorem h)

/--
Selected-atlas finite-chain terminal-branch monodromy data imply the selected
reduced continuation fields.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
      h)

/--
Selected-atlas value-level finite-chain terminal-branch monodromy data imply
the selected reduced continuation fields.
-/
noncomputable def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathChainTerminalBranchValueMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedMonodromyTheorem
    (selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathChainTerminalBranchValueMonodromyTheorem
      h)

/-- Selected-atlas monodromy data imply the selected explicit field theorem. -/
def selectedLocalModelContinuationFieldTheorem_of_selectedMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  selectedLocalModelContinuationFieldTheorem_of_selectedDerivedRegularityFieldTheorem
    (selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedMonodromyTheorem h)

/-- Selected-atlas path-class monodromy data imply the selected explicit field theorem. -/
def selectedLocalModelContinuationFieldTheorem_of_selectedPathClassMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  selectedLocalModelContinuationFieldTheorem_of_selectedMonodromyTheorem
    (selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathClassMonodromyTheorem h)

/-- Selected-atlas representative-path monodromy data imply the selected explicit field theorem. -/
def selectedLocalModelContinuationFieldTheorem_of_selectedPathMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  selectedLocalModelContinuationFieldTheorem_of_selectedPathClassMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathMonodromyTheorem h)

/-- Selected-atlas terminal-branch monodromy data imply the selected explicit field theorem. -/
def selectedLocalModelContinuationFieldTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  selectedLocalModelContinuationFieldTheorem_of_selectedDerivedRegularityFieldTheorem
    (selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathTerminalBranchMonodromyTheorem h)

/-- Selected-atlas finite-chain terminal-branch monodromy data imply the selected explicit field theorem. -/
def selectedLocalModelContinuationFieldTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  selectedLocalModelContinuationFieldTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
      h)

/--
Selected-atlas value-level finite-chain terminal-branch monodromy data imply
the selected explicit field theorem.
-/
noncomputable def selectedLocalModelContinuationFieldTheorem_of_selectedPathChainTerminalBranchValueMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  selectedLocalModelContinuationFieldTheorem_of_selectedDerivedRegularityFieldTheorem
    (selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathChainTerminalBranchValueMonodromyTheorem
      h)

/--
Reduced selected-atlas continuation fields fold into the selected-atlas
continuation package.
-/
def selectedLocalModelContinuationTheorem_of_selectedDerivedRegularityFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelContinuationDerivedRegularityFieldTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  selectedLocalModelContinuationTheorem_of_selectedFieldTheorem
    (selectedLocalModelContinuationFieldTheorem_of_selectedDerivedRegularityFieldTheorem h)

/-- Selected-atlas monodromy data imply selected-atlas continuation. -/
def selectedLocalModelContinuationTheorem_of_selectedMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  selectedLocalModelContinuationTheorem_of_selectedDerivedRegularityFieldTheorem
    (selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedMonodromyTheorem h)

/-- Selected-atlas path-class monodromy data imply selected-atlas continuation. -/
def selectedLocalModelContinuationTheorem_of_selectedPathClassMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  selectedLocalModelContinuationTheorem_of_selectedMonodromyTheorem
    (selectedLocalModelAnalyticContinuationMonodromyTheorem_of_selectedPathClassMonodromyTheorem h)

/-- Selected-atlas representative-path monodromy data imply selected-atlas continuation. -/
def selectedLocalModelContinuationTheorem_of_selectedPathMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  selectedLocalModelContinuationTheorem_of_selectedPathClassMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_selectedPathMonodromyTheorem h)

/-- Selected-atlas terminal-branch monodromy data imply selected-atlas continuation. -/
def selectedLocalModelContinuationTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  selectedLocalModelContinuationTheorem_of_selectedDerivedRegularityFieldTheorem
    (selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathTerminalBranchMonodromyTheorem h)

/-- Selected-atlas finite-chain terminal-branch monodromy data imply selected-atlas continuation. -/
def selectedLocalModelContinuationTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h :
      SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  selectedLocalModelContinuationTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
      h)

/--
The all-local-model field theorem specializes to any selected local model atlas.
-/
def selectedLocalModelContinuationFieldTheorem_of_fieldTheorem
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model reduced field theorem specializes to any selected local
model atlas.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_derivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model monodromy boundary specializes to a selected local model
atlas.
-/
def selectedLocalModelAnalyticContinuationMonodromyTheorem_of_monodromyTheorem
    (h : AnalyticContinuationMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model path-class monodromy boundary specializes to a selected
local model atlas.
-/
def selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_pathClassMonodromyTheorem
    (h : AnalyticContinuationPathClassMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathClassMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model path-class continuation boundary specializes to a selected
local model atlas.
-/
def selectedLocalModelAnalyticContinuationPathClassContinuationTheorem_of_pathClassContinuationTheorem
    (h : AnalyticContinuationPathClassContinuationTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathClassContinuationTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model path-class equivariance boundary specializes to a selected
local model atlas.
-/
def selectedLocalModelAnalyticContinuationPathClassEquivarianceTheorem_of_pathClassEquivarianceTheorem
    (h : AnalyticContinuationPathClassEquivarianceTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathClassEquivarianceTheorem
      X chosenLocalModels :=
  fun x₀ g C ↦ h x₀ g (chosenLocalModels g) C

/--
The all-local-model representative-path continuation boundary specializes to a
selected local model atlas.
-/
def selectedLocalModelAnalyticContinuationPathContinuationTheorem_of_pathContinuationTheorem
    (h : AnalyticContinuationPathContinuationTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathContinuationTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model representative-path equivariance boundary specializes to a
selected local model atlas.
-/
def selectedLocalModelAnalyticContinuationPathEquivarianceTheorem_of_pathEquivarianceTheorem
    (h : AnalyticContinuationPathEquivarianceTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathEquivarianceTheorem
      X chosenLocalModels :=
  fun x₀ g C ↦ h x₀ g (chosenLocalModels g) C

/--
The all-local-model representative-path monodromy boundary specializes to a
selected local model atlas.
-/
def selectedLocalModelAnalyticContinuationPathMonodromyTheorem_of_pathMonodromyTheorem
    (h : AnalyticContinuationPathMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model terminal-branch monodromy boundary specializes to a
selected local model atlas.
-/
def selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_pathTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathTerminalBranchMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model finite-chain terminal-branch monodromy boundary
specializes to a selected local model atlas.
-/
def selectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem
      X chosenLocalModels :=
  fun x₀ g ↦ h x₀ g (chosenLocalModels g)

/--
The all-local-model monodromy boundary gives the selected reduced field theorem
for any selected atlas.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_monodromyTheorem
    (h : AnalyticContinuationMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedMonodromyTheorem
    (selectedLocalModelAnalyticContinuationMonodromyTheorem_of_monodromyTheorem
      h chosenLocalModels)

/--
The all-local-model path-class monodromy boundary gives the selected reduced
field theorem for any selected atlas.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_pathClassMonodromyTheorem
    (h : AnalyticContinuationPathClassMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathClassMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathClassMonodromyTheorem_of_pathClassMonodromyTheorem
      h chosenLocalModels)

/--
The all-local-model representative-path monodromy boundary gives the selected
reduced field theorem for any selected atlas.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_pathMonodromyTheorem
    (h : AnalyticContinuationPathMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathMonodromyTheorem_of_pathMonodromyTheorem
      h chosenLocalModels)

/--
The all-local-model terminal-branch monodromy boundary gives the selected
reduced field theorem for any selected atlas.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_pathTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathTerminalBranchMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathTerminalBranchMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathTerminalBranchMonodromyTheorem_of_pathTerminalBranchMonodromyTheorem
      h chosenLocalModels)

/--
The all-local-model finite-chain terminal-branch monodromy boundary gives the
selected reduced field theorem for any selected atlas.
-/
def selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_pathChainTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchMonodromyTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationDerivedRegularityFieldTheorem
      X chosenLocalModels :=
  selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_selectedPathChainTerminalBranchMonodromyTheorem
    (selectedLocalModelAnalyticContinuationPathChainTerminalBranchMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
      h chosenLocalModels)

/--
The all-local-model reduced field theorem also gives the original selected
field theorem for any selected atlas.
-/
def selectedLocalModelContinuationFieldTheorem_of_derivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationFieldTheorem X chosenLocalModels :=
  selectedLocalModelContinuationFieldTheorem_of_selectedDerivedRegularityFieldTheorem
    (selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_derivedRegularityFieldTheorem
      h chosenLocalModels)

/-- The all-local-model field theorem gives continuation for any selected atlas. -/
def selectedLocalModelContinuationTheorem_of_fieldTheorem
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  selectedLocalModelContinuationTheorem_of_selectedFieldTheorem
    (selectedLocalModelContinuationFieldTheorem_of_fieldTheorem h chosenLocalModels)

/-- The all-local-model reduced field theorem gives continuation for any selected atlas. -/
def selectedLocalModelContinuationTheorem_of_derivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X)
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g) :
    SelectedLocalModelContinuationTheorem X chosenLocalModels :=
  selectedLocalModelContinuationTheorem_of_selectedDerivedRegularityFieldTheorem
    (selectedLocalModelContinuationDerivedRegularityFieldTheorem_of_derivedRegularityFieldTheorem
      h chosenLocalModels)

theorem hasLocalModelContinuationPipeline_of_selectedLocalModelContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationTheorem X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_continuationFromLocalModels (h x₀ g)

theorem hasDevelopingContinuationData_of_selectedLocalModelContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationTheorem X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.HasDevelopingContinuationData x₀ :=
  hasDevelopingContinuationData_of_continuationFromLocalModels (h x₀ g)

theorem admitsLiftedDevelopingMap_of_selectedLocalModelContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationTheorem X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_continuationFromLocalModels (h x₀ g)

theorem admitsDevelopingMap_of_selectedLocalModelContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationTheorem X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_continuationFromLocalModels (h x₀ g)

theorem hasLocalModelContinuationPipeline_of_selectedLocalModelContinuationFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationFieldTheorem X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_selectedLocalModelContinuationTheorem
    (selectedLocalModelContinuationTheorem_of_selectedFieldTheorem h) x₀ g

theorem hasDevelopingContinuationData_of_selectedLocalModelContinuationFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationFieldTheorem X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.HasDevelopingContinuationData x₀ :=
  hasDevelopingContinuationData_of_selectedLocalModelContinuationTheorem
    (selectedLocalModelContinuationTheorem_of_selectedFieldTheorem h) x₀ g

theorem admitsLiftedDevelopingMap_of_selectedLocalModelContinuationFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationFieldTheorem X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_selectedLocalModelContinuationTheorem
    (selectedLocalModelContinuationTheorem_of_selectedFieldTheorem h) x₀ g

theorem admitsDevelopingMap_of_selectedLocalModelContinuationFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X), HyperbolicLocalModelAtlas X g}
    (h : SelectedLocalModelContinuationFieldTheorem X chosenLocalModels)
    (x₀ : X) (g : HyperbolicMetric X) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_selectedLocalModelContinuationTheorem
    (selectedLocalModelContinuationTheorem_of_selectedFieldTheorem h) x₀ g

end HyperbolicMetric

end

end JJMath
