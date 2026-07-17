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
Selected canonical-sheet value continuation forgets to selected terminal-sheet
agreement.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedCanonicalSheetBasedWeakHandoffValueContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hContinuation :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueContinuationTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hContinuation x₀ g with ⟨C⟩
  exact ⟨C.toCanonicalSheetAgreementData⟩

/--
Selected terminal-sheet agreement fills the selected canonical-sheet value
continuation record by forgetting only the redundant agreement wrapper.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueContinuationTheorem_of_selectedCanonicalSheetAgreementTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueContinuationTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hAgreement x₀ g with ⟨C⟩
  exact ⟨C.toCanonicalSheetAnalyticContinuationValueData⟩

/--
Selected terminal-Mobius PSL covariance gives selected path-level PSL loop
equivariance for terminal-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedTerminalProjectionEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact
    ⟨PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL.ofTerminalProjectionEquivarianceData
      E⟩

/--
Selected transition-adjusted terminal-Mobius PSL covariance gives selected
path-level PSL loop equivariance for terminal-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedTerminalTransitionProjectionEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toValueEquivarianceDataPSL⟩

/--
Selected automatic endpoint-transition terminal-Mobius PSL covariance gives
selected path-level PSL loop equivariance for terminal-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toValueEquivarianceDataPSL⟩

/--
Selected value-projection rigidity gives selected
derived-holonomy value-projection data; the value/derived holonomy
identification is the base-loop specialization of the projection equality.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRigidity :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hRigidity x₀ g C with ⟨E⟩
  exact ⟨E.toDerivedHolonomyValueProjectionDataPSL⟩

/--
Selected terminal-formula projection faithfulness gives selected
terminal-formula projection rigidity: deck equivariance first compares the
two terminal formulae pointwise, and faithfulness identifies the PSL classes.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionFaithfulnessTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hFaithfulness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hFaithfulness x₀ g C with ⟨F⟩
  exact ⟨F.toTerminalFormulaProjectionRigidityDataPSL⟩

/--
Selected terminal-coordinate action faithfulness gives selected
terminal-formula projection faithfulness.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL_of_selectedTerminalFormulaActionFaithfulnessTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hActionFaithfulness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hActionFaithfulness x₀ g C with ⟨F⟩
  exact ⟨F.toTerminalFormulaProjectionFaithfulnessDataPSL⟩

/--
Selected three-point richness gives selected terminal-coordinate action
faithfulness.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRichness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hRichness x₀ g C with ⟨T⟩
  exact ⟨T.toTerminalFormulaActionFaithfulnessDataPSL⟩

/--
Selected nonempty-open terminal agreement gives selected three-point richness.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreementTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hOpen :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hOpen x₀ g C with ⟨O⟩
  exact ⟨O.toTerminalFormulaThreePointRichnessDataPSL⟩

/--
Selected nonempty-open terminal agreement gives selected terminal-coordinate
action faithfulness.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreementTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hOpen :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreementTheoremPSL
      hOpen)

/--
Selected three-point richness gives selected terminal-formula projection
faithfulness.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRichness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL_of_selectedTerminalFormulaActionFaithfulnessTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
      hRichness)

/--
Selected nonempty-open terminal agreement gives selected terminal-formula
projection faithfulness.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreementTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hOpen :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreementTheoremPSL
      hOpen)

/--
Selected terminal-coordinate action faithfulness gives selected
terminal-formula projection rigidity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL_of_selectedTerminalFormulaActionFaithfulnessTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hActionFaithfulness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionFaithfulnessTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL_of_selectedTerminalFormulaActionFaithfulnessTheoremPSL
      hActionFaithfulness)

/--
Selected three-point richness gives selected terminal-formula projection
rigidity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRichness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL_of_selectedTerminalFormulaActionFaithfulnessTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
      hRichness)

/--
Selected nonempty-open terminal agreement gives selected terminal-formula
projection rigidity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreementTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hOpen :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreementTheoremPSL
      hOpen)

/--
Selected terminal-formula projection rigidity plus selected value equivariance
give selected value-projection rigidity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionRigidity_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRigidity :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hRigidity x₀ g C with ⟨R⟩
  rcases hValue x₀ g C with ⟨E⟩
  exact ⟨R.toValueProjectionRigidityDataPSL E⟩

/--
Selected terminal-formula projection faithfulness plus selected value
equivariance give selected value-projection rigidity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionFaithfulness_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hFaithfulness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionRigidity_and_selectedValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionFaithfulnessTheoremPSL
      hFaithfulness)
    hValue

/--
Selected terminal-coordinate action faithfulness plus selected value
equivariance give selected value-projection rigidity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaActionFaithfulness_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hActionFaithfulness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionFaithfulness_and_selectedValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL_of_selectedTerminalFormulaActionFaithfulnessTheoremPSL
      hActionFaithfulness)
    hValue

/--
Selected three-point richness and selected value equivariance give selected
value-projection rigidity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaThreePointRichness_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRichness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaActionFaithfulness_and_selectedValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL_of_selectedTerminalFormulaThreePointRichnessTheoremPSL
      hRichness)
    hValue

/--
Selected nonempty-open terminal agreement and selected value equivariance give
selected value-projection rigidity.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreement_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hOpen :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaThreePointRichness_and_selectedValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreementTheoremPSL
      hOpen)
    hValue

/--
Selected path-level PSL loop equivariance alone gives selected value-projection
rigidity: terminal-formula projection rigidity is unconditional for
terminal-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedValueEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionRigidity_and_selectedValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
      X chosenLocalModels)
    hValue

/--
Selected terminal-formula projection rigidity plus selected value equivariance
give selected derived-holonomy value-projection data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedTerminalFormulaProjectionRigidity_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRigidity :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionRigidity_and_selectedValueEquivariancePSL
      hRigidity hValue)

/--
Selected terminal-formula projection faithfulness plus selected value
equivariance give selected derived-holonomy value-projection data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedTerminalFormulaProjectionFaithfulness_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hFaithfulness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaProjectionFaithfulness_and_selectedValueEquivariancePSL
      hFaithfulness hValue)

/--
Selected terminal-coordinate action faithfulness plus selected value
equivariance give selected derived-holonomy value-projection data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedTerminalFormulaActionFaithfulness_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hActionFaithfulness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaActionFaithfulness_and_selectedValueEquivariancePSL
      hActionFaithfulness hValue)

/--
Selected three-point richness and selected value equivariance give selected
derived-holonomy value-projection data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedTerminalFormulaThreePointRichness_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRichness :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaThreePointRichness_and_selectedValueEquivariancePSL
      hRichness hValue)

/--
Selected nonempty-open terminal agreement and selected value equivariance give
selected derived-holonomy value-projection data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreement_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hOpen :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
        X chosenLocalModels)
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedTerminalFormulaNonemptyOpenAgreement_and_selectedValueEquivariancePSL
      hOpen hValue)

/--
Selected value-projection rigidity gives selected derived-holonomy automatic
endpoint-transition covariance.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRigidity :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hRigidity x₀ g C with ⟨E⟩
  exact ⟨E.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL⟩

/--
Selected value-equivariance/projection-rigidity data give selected
derived-holonomy automatic endpoint-transition covariance.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL_of_selectedDerivedHolonomyValueProjectionTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hProjection :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hProjection x₀ g C with ⟨E⟩
  exact
    ⟨E.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL⟩

/--
Selected reduced derived-holonomy covariance supplies the older derived
automatic endpoint-transition PSL covariance record.
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
Selected local-sheet constancy supplies local constancy on the canonical
cover.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL_of_selectedLocalSheetConstancyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hLocalSheet :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hLocalSheet x₀ g C with ⟨E⟩
  exact ⟨E.toLocalConstancyOnCoverDataPSL⟩

/--
Selected PSL-level terminal-sheet extension agreement gives local constancy
of the normalized canonical-loop projection on the canonical cover.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL_of_selectedTerminalSheetExtensionProjectionAgreement
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hExtension :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  exact
    ⟨C.toLocalConstancyOnCoverDataPSL_of_terminalSheetExtensionProjectionAgreement
      (hExtension x₀ g C.basedWeakHandoffAlong)⟩

/--
Selected local constancy on the canonical cover is unconditional for
canonical-terminal-sheet agreement data.

This is the terminal-sheet-overlap route: no selected terminal-extension
chart-coherence hypothesis is required.
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
Selected terminal-sheet transport supplies local-sheet constancy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL_of_selectedTerminalSheetTransportTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hTransport :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hTransport x₀ g C with ⟨E⟩
  exact ⟨E.toLocalSheetConstancyDataPSL⟩

/--
Selected local-sheet constancy supplies normalized canonical-loop projection
propagation.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedLocalSheetConstancyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hLocalSheet :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedConstancyOnCoverTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL_of_selectedLocalConstancyOnCoverTheoremPSL
      (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL_of_selectedLocalSheetConstancyTheoremPSL
        hLocalSheet))

/--
Selected terminal-sheet transport supplies normalized canonical-loop
projection propagation.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedTerminalSheetTransportTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hTransport :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL_of_selectedLocalSheetConstancyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL_of_selectedTerminalSheetTransportTheoremPSL
      hTransport)

/--
Selected local constancy on the canonical cover supplies normalized
canonical-loop projection propagation.
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
Selected normalized canonical-loop projection propagation supplies reduced
derived-holonomy covariance.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL_of_selectedNormalizedProjectionPropagationTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPropagation :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL_of_selectedCanonicalLoopCovarianceTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL_of_selectedNormalizedProjectionPropagationTheoremPSL
      hPropagation)

/--
Selected canonical-loop covariance supplies the older derived automatic
endpoint-transition PSL covariance record.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL_of_selectedCanonicalLoopCovarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL_of_selectedReducedDerivedHolonomyTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL_of_selectedCanonicalLoopCovarianceTheoremPSL
      hEquivariance)

/--
Selected value-equivariance/projection-rigidity data give selected automatic
endpoint-transition terminal-Mobius covariance.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedDerivedHolonomyValueProjectionTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hProjection :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hProjection x₀ g C with ⟨E⟩
  exact
    ⟨E.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      |>.toAutomaticTerminalTransitionProjectionEquivarianceDataPSL⟩

/--
Selected value-equivariance/projection-rigidity data give selected path-level
PSL loop equivariance for terminal-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedDerivedHolonomyValueProjectionTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hProjection :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hProjection x₀ g C with ⟨E⟩
  exact ⟨E.valueEquivariance⟩

/--
Selected value-projection rigidity gives selected automatic
endpoint-transition terminal-Mobius covariance.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRigidity :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hRigidity x₀ g C with ⟨E⟩
  exact
    ⟨E.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      |>.toAutomaticTerminalTransitionProjectionEquivarianceDataPSL⟩

/--
Selected value-projection rigidity gives selected path-level PSL loop
equivariance for terminal-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRigidity :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hRigidity x₀ g C with ⟨E⟩
  exact ⟨E.valueEquivariance⟩

/--
Selected derived-holonomy automatic endpoint-transition covariance gives
selected automatic endpoint-transition terminal-Mobius covariance.
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
Selected derived-holonomy automatic endpoint-transition covariance gives
selected path-level PSL loop equivariance for terminal-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
      hEquivariance)

/--
Automatic endpoint-transition covariance is a special case of the
transition-adjusted terminal-Mobius covariance theorem.
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
The older same-terminal-chart covariance theorem is a special case of the
transition-adjusted terminal-Mobius covariance theorem.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedTerminalProjectionEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toTerminalTransitionProjectionEquivarianceDataPSL⟩

/--
Selected path-level PSL loop equivariance alone gives selected automatic
endpoint-transition terminal-Mobius covariance: the projection-rigidity part
is derived from unconditional nonempty-open terminal agreement.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedValueEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedValueProjectionRigidityTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL_of_selectedValueEquivarianceTheoremPSL
      hValue)

/--
Selected path-level PSL loop equivariance alone gives selected
transition-adjusted terminal-Mobius covariance.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedValueEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL_of_selectedValueEquivarianceTheoremPSL
      hValue)

/--
Selected value-level PSL loop equivariance forgets to selected path-level PSL
loop equivariance for terminal-sheet agreement data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL_of_selectedCanonicalSheetValueEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  rcases hEquivariance x₀ g C.toCanonicalSheetAnalyticContinuationValueData with ⟨E⟩
  exact
    ⟨PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL.ofCanonicalSheetValueEquivarianceDataPSL
      E⟩

/--
Selected path-class PSL equivariance restricts to selected canonical-terminal
sheet value equivariance.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueEquivarianceTheoremPSL_of_selectedPathClassEquivarianceTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathClassEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueEquivarianceTheoremPSL
      X chosenLocalModels := by
  intro x₀ g C
  let T :=
    C.toPathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
  let P := T.toPathClassLocalTransitionAnalyticContinuationData
  rcases hEquivariance x₀ g P with ⟨E⟩
  refine
    ⟨PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL.mk
      E.holonomy ?_⟩
  intro γ loop x p hloop
  have h :=
    E.pathClass_equivariant γ x (Path.Homotopic.Quotient.mk p)
  rw [← hloop] at h
  rw [← Path.Homotopic.Quotient.mk_trans] at h
  change
    T.terminalValueAt x (Path.Homotopic.Quotient.mk (loop.trans p)) =
      E.holonomy.upperHalfPlaneAction γ
        (T.terminalValueAt x (Path.Homotopic.Quotient.mk p)) at h
  rw [
    PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData.terminalValueAt_mk,
    PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData.terminalValueAt_mk] at h
  simpa [T,
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData.terminalValue]
    using h

/--
Selected canonical-terminal-sheet based weak handoff continuation plus selected
PSL loop equivariance give selected path-class PSL monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetBasedWeakHandoffValueContinuation_and_selectedCanonicalSheetValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hContinuation :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueContinuationTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hContinuation x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact
    ⟨E.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL⟩

/--
Selected terminal-sheet agreement plus selected PSL value equivariance gives
selected single-valued canonical-cover PSL continuation.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hAgreement x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toCanonicalCoverAnalyticContinuationDataPSL⟩

/--
Selected terminal-sheet homotopy plus selected PSL value equivariance gives
selected single-valued canonical-cover PSL continuation.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedTerminalSheetHomotopyPrinciple_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPrinciple :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedTerminalSheetHomotopyPrinciple
      hPrinciple)
    hEquivariance

/--
Selected finite-grid/local-extension data plus selected PSL value equivariance
gives selected single-valued canonical-cover PSL continuation.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedHomotopyGridLocalExtensionData_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedHomotopyGridLocalExtensionData
      hData)
    hEquivariance

/--
Selected elementary-grid/local-extension data plus selected PSL value
equivariance gives selected single-valued canonical-cover PSL continuation.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridLocalExtensionData_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedElementaryGridLocalExtensionData
      hData)
    hEquivariance

/--
Selected single-valued canonical-cover PSL continuation gives selected
path-class PSL monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalCoverBasedWeakHandoffPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hCover :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hCover x₀ g with ⟨C⟩
  exact ⟨C.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL⟩

/--
Selected single-valued canonical-cover PSL continuation gives selected
terminal-sheet agreement monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalCoverBasedWeakHandoffPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hCover :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hCover x₀ g with ⟨C⟩
  exact ⟨C.toCanonicalSheetAgreementMonodromyDataPSL⟩

/--
Selected terminal-sheet agreement plus selected path-level PSL loop
equivariance give selected terminal-sheet agreement monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hAgreement x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toAgreementMonodromyDataPSL⟩

/--
Selected terminal-sheet agreement plus selected terminal-Mobius PSL covariance
give selected terminal-sheet agreement monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hAgreement x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toAgreementMonodromyDataPSL⟩

/--
Selected terminal-sheet agreement plus selected transition-adjusted
terminal-Mobius PSL covariance give selected terminal-sheet agreement
monodromy.
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
Selected terminal-sheet agreement plus selected automatic endpoint-transition
terminal-Mobius PSL covariance give selected terminal-sheet agreement
monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAutomaticTerminalTransitionProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hAgreement x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact ⟨E.toAgreementMonodromyDataPSL⟩

/--
Selected terminal-sheet agreement plus selected derived-holonomy automatic
endpoint-transition terminal-Mobius covariance give selected terminal-sheet
agreement monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
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
Selected terminal-sheet agreement plus selected path-level PSL loop
equivariance give selected path-class PSL monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreementMonodromyPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAgreementValueEquivariancePSL
      hAgreement hEquivariance)

/--
Selected terminal-sheet agreement plus selected terminal-Mobius PSL covariance
give selected path-class PSL monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreementMonodromyPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedTerminalProjectionEquivariancePSL
      hAgreement hEquivariance)

/--
Selected terminal-sheet agreement plus selected transition-adjusted
terminal-Mobius PSL covariance give selected path-class PSL monodromy.
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
Selected terminal-sheet agreement plus selected automatic endpoint-transition
terminal-Mobius PSL covariance give selected path-class PSL monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAutomaticTerminalTransitionProjectionEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreementMonodromyPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAutomaticTerminalTransitionProjectionEquivariancePSL
      hAgreement hEquivariance)

/--
Selected terminal-sheet agreement plus selected derived-holonomy automatic
endpoint-transition terminal-Mobius covariance give selected path-class PSL
monodromy.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedCanonicalSheetAgreementMonodromyPSL
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL_of_selectedCanonicalSheetAgreement_and_selectedAutomaticTerminalTransitionProjectionDerivedHolonomyPSL
      hAgreement hEquivariance)

/--
Selected value-level finite-chain continuation plus selected PSL loop
equivariance give selected value-level finite-chain PSL monodromy.
-/
def selectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheoremPSL_of_selectedValueContinuation_and_selectedValueEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hContinuation :
      SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hContinuation x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact
    ⟨E.toPathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL⟩

/--
Selected explicit handoff-chain continuation data imply selected value-level
finite-chain continuation data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem_of_selectedHandoffChainValueContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathHandoffChainTerminalBranchValueContinuationTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionHandoffChainTerminalBranchAnalyticContinuationValueData.toPathLocalTransitionChainTerminalBranchAnalyticContinuationValueData

/--
Selected based weak handoff terminal continuation data imply selected
path-class continuation data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassContinuationTheorem_of_selectedBasedWeakHandoffValueContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalBranchValueContinuationTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassContinuationTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData.toPathClassLocalTransitionAnalyticContinuationData

/--
Selected canonical-terminal-sheet based weak handoff data imply selected
based weak handoff terminal continuation data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalBranchValueContinuationTheorem_of_selectedCanonicalSheetValueContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueContinuationTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalBranchValueContinuationTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData.toPathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData

/--
Selected canonical-terminal-sheet based weak handoff data imply selected
path-class continuation data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassContinuationTheorem_of_selectedCanonicalSheetBasedWeakHandoffValueContinuationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueContinuationTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassContinuationTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathClassContinuationTheorem_of_selectedBasedWeakHandoffValueContinuationTheorem
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalBranchValueContinuationTheorem_of_selectedCanonicalSheetValueContinuationTheorem
      h)

/--
Selected value-level finite-chain PSL monodromy data imply selected
path-class PSL monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedPathChainTerminalBranchValueMonodromyTheoremPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/local-extension terminal-projection data imply
selected path-class PSL monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridLocalExtensionTerminalProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/terminal-extension-agreement terminal-projection
data imply selected path-class PSL monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionAgreementTerminalProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected coherent elementary-grid/PSL-terminal-extension-agreement data imply
selected path-class PSL monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionProjectionAgreementData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionProjectionAgreementDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/local-extension transition-adjusted
terminal-projection data imply selected path-class PSL monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/terminal-extension-agreement transition-adjusted
terminal-projection data imply selected path-class PSL monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/local-extension automatic endpoint-transition
terminal-projection data imply selected path-class PSL monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/terminal-extension-agreement automatic
endpoint-transition terminal-projection data imply selected path-class PSL
monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/local-extension derived-holonomy automatic
endpoint-transition terminal-projection data imply selected path-class PSL
monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/terminal-extension-agreement derived-holonomy
automatic endpoint-transition terminal-projection data imply selected
path-class PSL monodromy data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

/--
Selected bound elementary-grid/local-extension terminal-projection data imply
selected single-valued canonical-cover PSL continuation data directly.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridLocalExtensionTerminalProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalProjectionDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Selected bound elementary-grid/terminal-extension-agreement terminal-projection
data imply selected single-valued canonical-cover PSL continuation data
directly.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridExtensionAgreementTerminalProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalProjectionDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Selected bound elementary-grid/local-extension transition-adjusted
terminal-projection data imply selected single-valued canonical-cover PSL
continuation data directly.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionTerminalTransitionProjectionDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Selected bound elementary-grid/terminal-extension-agreement
transition-adjusted terminal-projection data imply selected single-valued
canonical-cover PSL continuation data directly.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementTerminalTransitionProjectionDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Selected bound elementary-grid/local-extension automatic endpoint-transition
terminal-projection data imply selected single-valued canonical-cover PSL
continuation data directly.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Selected bound elementary-grid/terminal-extension-agreement automatic
endpoint-transition terminal-projection data imply selected single-valued
canonical-cover PSL continuation data directly.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Selected bound elementary-grid/local-extension derived-holonomy automatic
endpoint-transition terminal-projection data imply selected single-valued
canonical-cover PSL continuation data directly.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Selected bound elementary-grid/terminal-extension-agreement derived-holonomy
automatic endpoint-transition terminal-projection data imply selected
single-valued canonical-cover PSL continuation data directly.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem_of_selectedElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      ∀ (x₀ : X) (g : HyperbolicMetric X),
        Nonempty
          (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
            x₀ g (chosenLocalModels g))) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL.toCanonicalCoverAnalyticContinuationDataPSL

/--
Local-transition continuation only for a fixed selected local model atlas.
-/
def SelectedLocalTransitionModelContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (ContinuationFromLocalTransitionModels
        x₀ g (chosenLocalModels g))

/-- Explicit continuation fields imply the local-model continuation theorem. -/
def analyticContinuationFromLocalModelsTheorem_of_analyticContinuationFromLocalModelsFieldTheorem
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X) :
    AnalyticContinuationFromLocalModelsTheorem X :=
  fun x₀ g localModels ↦
    h x₀ g localModels |>.map
      HyperbolicDevelopingContinuationDataFields.toContinuationFromLocalModels

/-- Explicit local-transition fields imply local-transition continuation. -/
def analyticContinuationFromLocalTransitionModelsTheorem_of_fieldTheorem
    (h : AnalyticContinuationFromLocalTransitionModelsFieldTheorem X) :
    AnalyticContinuationFromLocalTransitionModelsTheorem X :=
  fun x₀ g localModels ↦
    h x₀ g localModels |>.map
      fun F ↦
        ({ continuationFields := F } :
          ContinuationFromLocalTransitionModels x₀ g localModels)

/-- Selected local-transition fields imply selected local-transition continuation. -/
def selectedLocalTransitionModelContinuationTheorem_of_fieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationFieldTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationTheorem X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      fun F ↦
        ({ continuationFields := F } :
          ContinuationFromLocalTransitionModels
            x₀ g (chosenLocalModels g))

/--
Selected canonical-cover local-transition fields imply ordinary selected
local-transition continuation fields.
-/
def selectedLocalTransitionModelContinuationFieldTheorem_of_canonicalCoverMetricFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationCanonicalCoverMetricFieldTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationFieldTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric.toHyperbolicDevelopingLocalTransitionContinuationDataFields

/--
Selected reduced local-transition canonical-cover fields imply selected
canonical-cover local-transition fields.
-/
def selectedLocalTransitionModelContinuationCanonicalCoverMetricFieldTheorem_of_derivedRegularityCanonicalCoverMetricFieldTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationCanonicalCoverMetricFieldTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity.toHyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric

/--
Selected lifted reduced local-transition fields imply selected PSL-valued
reduced local-transition fields.
-/
def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_lifted
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL.ofLifted

/--
Selected local-transition monodromy data imply selected reduced continuation
fields.
-/
def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem_of_selectedMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem
      X chosenLocalModels :=
  fun x₀ g ↦
    h x₀ g |>.map
      LocalTransitionAnalyticContinuationMonodromyData.toDerivedRegularityFields

/--
Selected local-transition monodromy data imply selected PSL-valued reduced
continuation fields.
-/
def selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedMonodromyTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (h :
      SelectedLocalTransitionModelAnalyticContinuationMonodromyTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
      X chosenLocalModels :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_lifted
    (selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem_of_selectedMonodromyTheorem
      h)

/--
Selected PSL path-class local-transition monodromy data imply selected
PSL-valued reduced continuation fields.
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
