import JJMath.Hyperbolic.Schwarzian.Theorems.Curvature

/-!
# Split Schwarzian theorem wrappers and hyperbolic specialization
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
The strengthened metric-data atlas route with Schwarzian uniqueness stated in
the sharper value-only two-jet form.  The derivative part of local one-jet
agreement is recovered formally from equality on an open neighborhood.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_valueTwoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hSecond :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem)
    (hValueTwoJet :
      PointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_twoJetUniqueness
    hBranch hAffine hSecond
    (pointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem_of_value
      hValueTwoJet)

/--
The strengthened metric-data atlas route with value-local two-jet uniqueness
reduced to the plain scalar Schwarzian identity principle plus the two
actual-Schwarzian equation bridges for branches and real-Mobius
postcomposition.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_actualSchwarzian_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hSecond :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem)
    (hActual :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem)
    (hPostActual :
      RealMobiusPostcompositionActualSchwarzianEquationTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_valueTwoJetUniqueness
    hBranch hAffine hSecond
    (pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem_of_actualSchwarzian
      hActual hPostActual hScalar)

/--
The same scalar-uniqueness route with the postcomposition actual-Schwarzian
equation obtained from pure real-Mobius actual-Schwarzian invariance.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_actualSchwarzianInvariant_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hSecond :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem)
    (hActual :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem)
    (hInv :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_actualSchwarzian_scalarUniqueness
    hBranch hAffine hSecond hActual
    (realMobiusPostcompositionActualSchwarzianEquationTheorem_of_invariant
      hActual hInv)
    hScalar

/--
The scalar-uniqueness route with the branch actual-Schwarzian equation derived
from second- and third-derivative identifications.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_secondThirdDerivative_actualSchwarzianInvariant_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hSecondJet :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem)
    (hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeIdentificationTheorem)
    (hThird :
      LocalUpperHalfPlaneDevelopingMapThirdDerivativeIdentificationTheorem)
    (hInv :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_actualSchwarzianInvariant_scalarUniqueness
    hBranch hAffine hSecondJet
    (localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_second_third
      hSecond hThird)
    hInv hScalar

/--
The scalar-uniqueness route with branch actual-Schwarzian compatibility derived
from first- and second-derivative `HasDerivAt` regularity.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_firstSecondDerivative_actualSchwarzianInvariant_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hSecondJet :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hInv :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_actualSchwarzianInvariant_scalarUniqueness
    hBranch hAffine hSecondJet
    (localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_first_second_derivative
      hFirstDeriv hSecondDeriv)
    hInv hScalar

/--
The strengthened metric-data atlas route with the metric second-jet bridge
proved from the first-Wirtinger pullback formula.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_firstWirtinger_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFormula :
      PointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_twoJetUniqueness
    hBranch hAffine
    (pointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem_of_pullbackFirstWirtingerFormula
      hFormula)
    hTwoJet

/--
The strengthened metric-data atlas route with the first-Wirtinger comparison
formula split into the branch pullback calculation and real-Mobius
postcomposition invariance.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_postcomposition_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hPost :
      RealMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_firstWirtinger_twoJetUniqueness
    hBranch hAffine
    (pointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem_of_branchFormula_postcomposition
      hFirst hPost)
    hTwoJet

/--
The strengthened metric-data atlas route with real-Mobius postcomposition
reduced to expression invariance of the first-Wirtinger pullback term.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_expressionInvariant_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hInv :
      RealMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_postcomposition_twoJetUniqueness
    hBranch hAffine hFirst
    (realMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem_of_expressionInvariant
      hInv)
    hTwoJet

/--
The strengthened metric-data atlas route with real-Mobius postcomposition
reduced to the second-derivative chain rule and the one-variable multiplier
identity.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_secondChainRule_multiplierIdentity_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem)
    (hMultiplier :
      RealMobiusFirstWirtingerMultiplierIdentityTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_expressionInvariant_twoJetUniqueness
    hBranch hAffine hFirst
    (realMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem_of_secondChainRule_multiplierIdentity
      hSecondChain hMultiplier)
    hTwoJet

/--
The strengthened metric-data atlas route with the scalar real-Mobius
multiplier identity reduced to denominator algebra.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_secondChainRule_denominatorAlgebra_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem)
    (hDenAlg :
      RealMobiusFirstWirtingerDenominatorAlgebraTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_secondChainRule_multiplierIdentity_twoJetUniqueness
    hBranch hAffine hFirst hSecondChain
    (realMobiusFirstWirtingerMultiplierIdentityTheorem_of_denominatorAlgebra
      hDenAlg)
    hTwoJet

/--
The strengthened metric-data atlas route with real-Mobius postcomposition
reduced only to the second-order branch chain rule.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_secondChainRule_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_expressionInvariant_twoJetUniqueness
    hBranch hAffine hFirst
    (realMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem_of_secondChainRule
      hSecondChain)
    hTwoJet

/--
The strengthened metric-data atlas route with the second-order real-Mobius
chain rule obtained from differentiability of branch derivatives.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hBranchDeriv :
      LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_secondChainRule_twoJetUniqueness
    hBranch hAffine hFirst
    (realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
      hBranchDeriv)
    hTwoJet

/--
Current sharp real-transition route: the real-Mobius postcomposition calculus
is formal from branch-derivative differentiability, and the remaining
Schwarzian identity-principle input is only value-local two-jet uniqueness.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_valueTwoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hBranchDeriv :
      LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem)
    (hValueTwoJet :
      PointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_twoJetUniqueness
    hBranch hAffine hFirst hBranchDeriv
    (pointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem_of_value
      hValueTwoJet)

/--
Sharp scalar-uniqueness route for real transitions: branch pullback
first-Wirtinger, differentiability of branch derivatives, actual-Schwarzian
compatibility, real-Mobius actual-Schwarzian compatibility, and the scalar
two-jet Schwarzian identity principle imply the real branch atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_actualSchwarzian_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hBranchDeriv :
      LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem)
    (hActual :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem)
    (hPostActual :
      RealMobiusPostcompositionActualSchwarzianEquationTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_valueTwoJetUniqueness
    hBranch hAffine hFirst hBranchDeriv
    (pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem_of_actualSchwarzian
      hActual hPostActual hScalar)

/--
Sharp scalar-uniqueness route where real-Mobius actual-Schwarzian
postcomposition is supplied as an invariance theorem rather than as a
coefficient equation.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_actualSchwarzianInvariant_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hBranchDeriv :
      LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem)
    (hActual :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem)
    (hInv :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_actualSchwarzian_scalarUniqueness
    hBranch hAffine hFirst hBranchDeriv hActual
    (realMobiusPostcompositionActualSchwarzianEquationTheorem_of_invariant
      hActual hInv)
    hScalar

/--
Sharp scalar-uniqueness route with branch actual-Schwarzian compatibility
obtained from second- and third-derivative identification.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_secondThirdDerivative_actualSchwarzianInvariant_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hBranchDeriv :
      LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem)
    (hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeIdentificationTheorem)
    (hThird :
      LocalUpperHalfPlaneDevelopingMapThirdDerivativeIdentificationTheorem)
    (hInv :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_actualSchwarzianInvariant_scalarUniqueness
    hBranch hAffine hFirst hBranchDeriv
    (localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_second_third
      hSecond hThird)
    hInv hScalar

/--
Sharpest current real-transition route: first-Wirtinger pullback, first- and
second-derivative `HasDerivAt` regularity, real-Mobius actual-Schwarzian
invariance, and scalar two-jet Schwarzian uniqueness.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_firstSecondDerivative_actualSchwarzianInvariant_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hInv :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_actualSchwarzianInvariant_scalarUniqueness
    hBranch hAffine hFirst
    (localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
      hFirstDeriv)
    (localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_first_second_derivative
      hFirstDeriv hSecondDeriv)
    hInv hScalar

/--
Same sharp real-transition route, with actual-Schwarzian invariance reduced to
the third-order real-Mobius chain rule and the zero-Schwarzian theorem for real
Mobius maps.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_firstSecondDerivative_thirdChain_zero_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hThirdChain :
      RealMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem)
    (hZero :
      RealMobiusActualSchwarzianZeroTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_firstSecondDerivative_actualSchwarzianInvariant_scalarUniqueness
    hBranch hAffine hFirst hFirstDeriv hSecondDeriv
    (realMobiusPostcompositionActualSchwarzianInvariantTheorem_of_thirdChainRule_zero
      (realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
        (localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
      hFirstDeriv))
      hThirdChain hZero)
    hScalar

/--
Same route after proving that real Mobius transformations have zero
Schwarzian; the only remaining Mobius-Schwarzian calculus input is the
third-order postcomposition chain rule.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_firstSecondDerivative_thirdChain_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hThirdChain :
      RealMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_firstSecondDerivative_thirdChain_zero_scalarUniqueness
    hBranch hAffine hFirst hFirstDeriv hSecondDeriv hThirdChain
    realMobiusActualSchwarzianZeroTheorem hScalar

/--
Current sharp real-transition route after closing the real-Mobius Schwarzian
calculus: first-Wirtinger pullback, first/second branch derivative
regularity, and scalar Schwarzian two-jet uniqueness imply the real branch
atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_firstSecondDerivative_scalarUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_firstSecondDerivative_thirdChain_scalarUniqueness
    hBranch hAffine hFirst hFirstDeriv hSecondDeriv
    (realMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem_of_first_secondDerivative
      hFirstDeriv hSecondDeriv)
    hScalar

/--
Sharper real-transition route: branch continuity is now internal, and affine
derivative continuity follows from first-derivative regularity.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_scalarUniqueness
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_firstSecondDerivative_scalarUniqueness
    localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem
    (localUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem_of_firstDerivative
      hFirstDeriv)
    hFirst hFirstDeriv hSecondDeriv hScalar

/--
Same sharp route, but using the explicit C³ scalar Schwarzian identity
principle.  The C³ hypotheses for both compared scalar maps are supplied from
the branch first/second derivative regularity package.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_c3ScalarUniqueness
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem := by
  let hActual : LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem :=
    localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_first_second_derivative
      hFirstDeriv hSecondDeriv
  let hInv : RealMobiusPostcompositionActualSchwarzianInvariantTheorem :=
    realMobiusPostcompositionActualSchwarzianInvariantTheorem_of_thirdChainRule_zero
      (realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
        (localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
          hFirstDeriv))
      (realMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem_of_first_secondDerivative
        hFirstDeriv hSecondDeriv)
      realMobiusActualSchwarzianZeroTheorem
  exact
    hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_branchFirstWirtinger_branchDerivative_valueTwoJetUniqueness
      localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem
      (localUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem_of_firstDerivative
        hFirstDeriv)
      hFirst
      (localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
        hFirstDeriv)
      (pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem_of_actualSchwarzian_c3
        hActual
        (realMobiusPostcompositionActualSchwarzianEquationTheorem_of_invariant
          hActual hInv)
        hFirstDeriv hSecondDeriv hScalar)

/--
Same route with scalar uniqueness factored into the Riccati pre-Schwarzian
step and the final integration step.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianUniqueness
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hPre :
      ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem)
    (hInt :
      ScalarPreSchwarzianValueDerivativeLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_c3ScalarUniqueness
    hFirst hFirstDeriv hSecondDeriv
    (scalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem_of_preSchwarzian
      hPre hInt)

/--
Same route after closing the final integration step for equal
pre-Schwarzians.  The remaining scalar boundary is the Riccati step which
turns Schwarzian equality into local pre-Schwarzian equality.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianRiccati
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hPre :
      ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianUniqueness
    hFirst hFirstDeriv hSecondDeriv hPre
    scalarPreSchwarzianValueDerivativeLocalUniquenessTheorem_of_derivativeQuotient

/--
Same route after proving the Schwarzian-to-pre-Schwarzian Riccati algebra.
The remaining scalar boundary is only zero-uniqueness for the resulting
linear first-order equation.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianRiccatiZero
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hZero :
      ScalarPreSchwarzianRiccatiZeroLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianRiccati
    hFirst hFirstDeriv hSecondDeriv
    (scalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem_of_riccatiZero
      hZero)

/--
Same route after reducing zero-uniqueness for the pre-Schwarzian Riccati
equation to the existence of a local integrating factor on a ball.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianIntegratingFactor
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hIF :
      ScalarPreSchwarzianRiccatiIntegratingFactorBallExistenceTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianRiccatiZero
    hFirst hFirstDeriv hSecondDeriv
    (scalarPreSchwarzianRiccatiZeroLocalUniquenessTheorem_of_integratingFactor
      hIF)

/--
Same route after reducing the local integrating-factor boundary to local
primitive existence for the scalar pre-Schwarzian Riccati coefficient.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianPrimitive
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hPrim :
      ScalarPreSchwarzianRiccatiPrimitiveBallExistenceTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianIntegratingFactor
    hFirst hFirstDeriv hSecondDeriv
    (scalarPreSchwarzianRiccatiIntegratingFactorBallExistenceTheorem_of_primitive
      hPrim)

/--
Same real-transition route with the scalar Schwarzian identity-principle part
closed.  The remaining inputs are the branch first-Wirtinger pullback formula
and the first/second derivative regularity packages.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_scalarClosed
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_preSchwarzianRiccati
    hFirst hFirstDeriv hSecondDeriv
    scalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem_proved

/--
Same route with the branch first-Wirtinger formula obtained from the
squared-density derivative formula.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_densityDerivative_firstSecondDerivative_scalarClosed
    (hDensity :
      LocalUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem)
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchFirstWirtinger_firstSecondDerivative_scalarClosed
    (localUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem_of_densitySqDerivative
      hDensity)
    hFirstDeriv hSecondDeriv

/--
Same route with the squared-density derivative formula derived from
first-derivative branch regularity.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_firstSecondDerivative_scalarClosed
    (hFirstDeriv :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecondDeriv :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_densityDerivative_firstSecondDerivative_scalarClosed
    (localUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem_of_firstDerivative
      hFirstDeriv)
    hFirstDeriv hSecondDeriv

/--
Same route with actual branch regularity obtained from the symbolic
projective derivative fields of the underlying projective branch.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_projectiveFirstSecondDerivative_scalarClosed
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricData_projectiveFirstSecondDerivative_scalarClosed
    hyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem
    hProjFirst hProjSecond

/-- Public closed form of the metric-recovering Schwarzian ball pre-atlas theorem. -/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved

/-- Public closed form of the metric-recovering Schwarzian pre-atlas theorem. -/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_ballPreAtlas
    hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem

/-- Public closed form of the metric-recovering Schwarzian normalization-atlas theorem. -/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_proved

/--
Adding the real-transition uniqueness theorem to the proved
metric-Schwarzian Frobenius construction gives real upper-half-plane branch
atlases in each coordinate domain.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_proved
    hTransition

/--
Adding only the off-diagonal real-transition uniqueness theorem to the proved
metric-Schwarzian Frobenius construction gives real upper-half-plane branch
atlases in each coordinate domain.  The diagonal transitions are identities.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_offDiagonal
    (hOff :
      MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_offDiagonal
    hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_proved
    hOff

/--
Adding only the overlapping off-diagonal real-transition uniqueness theorem to
the proved metric-Schwarzian Frobenius construction gives real
upper-half-plane branch atlases in each coordinate domain.  Empty overlaps are
discharged vacuously.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_overlappingOffDiagonal
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_offDiagonal
    (metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_overlappingOffDiagonal
      hOverlap)

/--
For the proved metric-Schwarzian Frobenius construction, connected-overlap
extension is now the only remaining local input for real upper-half-plane
branch atlases.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_extension
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_extension
    hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem
    hExtend

/--
For the proved metric-Schwarzian Frobenius construction, it is enough to prove
that the pointed real-Mobius equality locus is clopen in the branch overlap.
The propagation from a nonempty clopen equality locus across a preconnected
overlap is now handled by mathlib connectedness.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_equalitySetClopen
    (hClopen : PointedRealMobiusTransitionEqualitySetIsClopenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_extension
    (pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySetClopen
      hClopen)

/--
The same local real branch-atlas conclusion follows from the separate closed
and open equality-locus targets.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_equalitySet_closed_open
    (hClosed : PointedRealMobiusTransitionEqualitySetIsClosedTheorem)
    (hOpen : PointedRealMobiusTransitionEqualitySetIsOpenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_extension
    (pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySet_closed_open
      hClosed hOpen)

/--
For the proved metric-Schwarzian Frobenius construction, branch-domain
continuity and openness of the pointed equality locus are enough for real
upper-half-plane branch atlases.  Closedness follows formally from continuity
and the proved continuity of fixed real-Mobius actions.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_equalitySetOpen
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hOpen : PointedRealMobiusTransitionEqualitySetIsOpenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_equalitySet_closed_open
    (pointedRealMobiusTransitionEqualitySetIsClosedTheorem_of_branch_continuity
      hBranch)
    hOpen

/--
The mathematically sharper real-transition route uses the one-jet equality
locus.  Value continuity, derivative continuity, and one-jet openness are
enough for local real upper-half-plane branch atlases.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_oneJetEqualitySet
    (hValue : PointedRealMobiusTransitionEqualitySetContinuityTheorem)
    (hDeriv : PointedRealMobiusTransitionOneJetDerivativeContinuityTheorem)
    (hOpen : PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_extension
    (pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySet_closed_open
      (pointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_continuity
        hValue hDeriv)
      hOpen)

/--
Using branch-domain continuity for the value part, it remains to provide
derivative continuity and local one-jet openness.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_oneJetEqualitySet
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hDeriv : PointedRealMobiusTransitionOneJetDerivativeContinuityTheorem)
    (hOpen : PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_oneJetEqualitySet
    (pointedRealMobiusTransitionEqualitySetContinuityTheorem_of_branch_and_action_continuity
      hBranch realMobiusRepresentativeActionContinuousTheorem)
    hDeriv hOpen

/--
It is enough to prove `C¹` regularity of the complex-valued branch maps,
continuity of the one-jet derivative functions, and openness of the one-jet
equality locus.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContDiff_oneJetEqualitySet
    (hBranchContDiff : LocalUpperHalfPlaneDevelopingMapComplexContDiffOnDomainTheorem)
    (hDeriv : PointedRealMobiusTransitionOneJetDerivativeContinuityTheorem)
    (hOpen : PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_oneJetEqualitySet
    (localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContDiffOn
      hBranchContDiff)
    hDeriv hOpen

/--
With branch `C¹` regularity, branch derivative continuity, postcomposition
derivative continuity, and one-jet openness, the real branch-atlas conclusion
follows.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_derivativeContinuitySplit
    (hBranchContDiff : LocalUpperHalfPlaneDevelopingMapComplexContDiffOnDomainTheorem)
    (hBranchDeriv : LocalUpperHalfPlaneDevelopingMapComplexDerivativeContinuousOnDomainTheorem)
    (hPost :
      PointedRealMobiusTransitionPostcompositionDerivativeContinuityTheorem)
    (hOpen : PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContDiff_oneJetEqualitySet
    hBranchContDiff
    (pointedRealMobiusTransitionOneJetDerivativeContinuityTheorem_of_branch_and_postcomposition
      hBranchDeriv hPost)
    hOpen

/--
The branch derivative-continuity input can be supplied by continuity of the
stored affine derivative, since the branch package identifies the actual
complex derivative with that stored affine derivative on the domain.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_affineDerivativeContinuity
    (hBranchContDiff : LocalUpperHalfPlaneDevelopingMapComplexContDiffOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hPost :
      PointedRealMobiusTransitionPostcompositionDerivativeContinuityTheorem)
    (hOpen : PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_derivativeContinuitySplit
    hBranchContDiff
    (localUpperHalfPlaneDevelopingMapComplexDerivativeContinuousOnDomainTheorem_of_affineDerivativeContinuous
      hAffineDeriv)
    hPost hOpen

/--
With branch `C¹` regularity and stored affine derivative continuity,
postcomposition derivative continuity is formal: it follows from the branch
chain rule and continuity of the real-Mobius derivative multiplier.  Thus only
one-jet openness remains as the local uniqueness input.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_affineDerivativeContinuity_oneJetOpen
    (hBranchContDiff : LocalUpperHalfPlaneDevelopingMapComplexContDiffOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hOpen : PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_affineDerivativeContinuity
    hBranchContDiff hAffineDeriv
    (pointedRealMobiusTransitionPostcompositionDerivativeContinuityTheorem_of_branch_continuity
      (localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContDiffOn
        hBranchContDiff)
      hAffineDeriv)
    hOpen

/--
Branch-domain continuity, stored affine derivative continuity, and local
one-jet uniqueness give the real branch-atlas conclusion.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_oneJetLocalUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hLocal : PointedRealMobiusTransitionOneJetLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_extension
    (pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_branch_continuity_localUniqueness
      hBranch hAffineDeriv hLocal)

/--
Coefficient agreement plus the coefficient-aware Schwarzian one-jet uniqueness
core gives the real branch-atlas conclusion.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_oneJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_oneJetLocalUniqueness
    hBranch hAffineDeriv
    (pointedRealMobiusTransitionOneJetLocalUniquenessTheorem_of_coefficientAgreement
      hCoeff hUnique)

/--
The older coefficient-agreement route with the one-jet uniqueness input
factored into metric second-jet recovery and two-jet Schwarzian uniqueness.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_metricSecondJet_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hSecond :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_oneJetUniqueness
    hBranch hAffineDeriv hCoeff
    (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_metricSecondJet_twoJetUniqueness
      hSecond hTwoJet)

/--
The older coefficient-agreement route with the metric second-jet bridge proved
from the first-Wirtinger pullback formula.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_firstWirtinger_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hFormula :
      PointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_metricSecondJet_twoJetUniqueness
    hBranch hAffineDeriv hCoeff
    (pointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem_of_pullbackFirstWirtingerFormula
      hFormula)
    hTwoJet

/--
The older coefficient-agreement route with the first-Wirtinger comparison
formula split into the branch pullback calculation and real-Mobius
postcomposition invariance.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_postcomposition_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hPost :
      RealMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_firstWirtinger_twoJetUniqueness
    hBranch hAffineDeriv hCoeff
    (pointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem_of_branchFormula_postcomposition
      hFirst hPost)
    hTwoJet

/--
The older coefficient-agreement route with real-Mobius postcomposition reduced
to expression invariance of the first-Wirtinger pullback term.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_expressionInvariant_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hInv :
      RealMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_postcomposition_twoJetUniqueness
    hBranch hAffineDeriv hCoeff hFirst
    (realMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem_of_expressionInvariant
      hInv)
    hTwoJet

/--
The older coefficient-agreement route with real-Mobius postcomposition reduced
to the second-derivative chain rule and the one-variable multiplier identity.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_secondChainRule_multiplierIdentity_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem)
    (hMultiplier :
      RealMobiusFirstWirtingerMultiplierIdentityTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_expressionInvariant_twoJetUniqueness
    hBranch hAffineDeriv hCoeff hFirst
    (realMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem_of_secondChainRule_multiplierIdentity
      hSecondChain hMultiplier)
    hTwoJet

/--
The older coefficient-agreement route with the scalar real-Mobius multiplier
identity reduced to denominator algebra.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_secondChainRule_denominatorAlgebra_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem)
    (hDenAlg :
      RealMobiusFirstWirtingerDenominatorAlgebraTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_secondChainRule_multiplierIdentity_twoJetUniqueness
    hBranch hAffineDeriv hCoeff hFirst hSecondChain
    (realMobiusFirstWirtingerMultiplierIdentityTheorem_of_denominatorAlgebra
      hDenAlg)
    hTwoJet

/--
The older coefficient-agreement route with real-Mobius postcomposition reduced
only to the second-order branch chain rule.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_secondChainRule_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_expressionInvariant_twoJetUniqueness
    hBranch hAffineDeriv hCoeff hFirst
    (realMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem_of_secondChainRule
      hSecondChain)
    hTwoJet

/--
The older coefficient-agreement route with the second-order real-Mobius chain
rule obtained from differentiability of branch derivatives.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_branchDerivative_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hBranchDeriv :
      LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_coefficientAgreement_branchFirstWirtinger_secondChainRule_twoJetUniqueness
    hBranch hAffineDeriv hCoeff hFirst
    (realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
      hBranchDeriv)
    hTwoJet

/--
The same real branch-atlas conclusion with the open one-jet-locus hypothesis
replaced by the ambient local uniqueness/identity-principle statement.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_affineDerivativeContinuity_oneJetLocalUniqueness
    (hBranchContDiff : LocalUpperHalfPlaneDevelopingMapComplexContDiffOnDomainTheorem)
    (hAffineDeriv : LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hLocal : PointedRealMobiusTransitionOneJetLocalUniquenessTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_branchContinuity_affineDerivativeContinuity_oneJetLocalUniqueness
    (localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContDiffOn
      hBranchContDiff)
    hAffineDeriv hLocal

/--
Frobenius two-jet normalizations plus metric recovery from the normalized
two-jet give genuine local upper-half-plane developing maps.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetNormalizations
    (hNorm : HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem := by
  intro u z hu hz
  rcases hNorm u hu hz with ⟨S, _a, _P, N, hNz⟩
  exact ⟨S, N.normalized.toLocalUpperHalfPlaneDevelopingMap
    (hRecovery S N hu), hNz⟩

/--
The hyperbolic holomorphic-Schwarzian theorem, Frobenius existence, explicit
normal-form Schwarzian invariance, upper-half-plane landing, and two-jet metric
recovery give genuine local upper-half-plane developing maps.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusSchwarzianLanding
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetNormalizations
    (hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_schwarzian
      hS hFrob hSchwarzian hUpper)
    hRecovery

/--
The holomorphic-Schwarzian theorem, Frobenius existence, upper-half-plane
landing, and two-jet metric recovery give genuine local upper-half-plane
developing maps; explicit Schwarzian invariance is now proved internally.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusLanding
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusSchwarzianLanding
    hS hFrob localProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem
    hUpper hRecovery

/--
The sharper Frobenius route to genuine local upper-half-plane developing maps:
the remaining upper-half-plane input is only the explicit normal-form lift and
derivative-identification data on the landing ball.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_normalFormLift
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hLift : LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetNormalizations
    (hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_normalFormLift
      hS hFrob hLift)
    hRecovery

/--
The derivative-identification Frobenius route to genuine local upper-half-plane
developing maps: after the landing/lift construction, actual derivative
identification for the explicit normal-form affine branch supplies the
normalization.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivativeIdentification
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hDeriv : LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetNormalizations
    (hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_derivativeIdentification
      hS hFrob hDeriv)
    hRecovery

/--
The canonical third-derivative Frobenius normal-form route gives genuine local
upper-half-plane developing maps once metric recovery for the normalized
two-jet is supplied.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hThird :
      LocalProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetNormalizations
    (hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_canonicalThirdDerivativeIdentification
      hS hFrob hThird)
    hRecovery

/--
The sharp Frobenius route to genuine local upper-half-plane developing maps,
expressed in terms of the intrinsic quotient-rule target for the Frobenius
developing ratio.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_affineHasDerivAt
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hBase : LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetNormalizations
    (hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_affineHasDerivAt
      hS hFrob hBase)
    hRecovery

/--
The proved Frobenius normal-form pipeline gives genuine local
upper-half-plane developing maps once metric recovery for the normalized
two-jet is supplied.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_provedNormalForm
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    hS hFrob
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    hRecovery

/--
Metric-Schwarzian data, Frobenius existence, the proved normal-form pipeline,
and metric-Schwarzian two-jet recovery give local upper-half-plane developing
maps.  This keeps the original metric-Schwarzian coefficient identification
attached to the chosen Schwarzian coefficient, so metric recovery can use the
canonical pullback formula route without an external corrected-Riccati input.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian
    (hMetric : HyperbolicLiouvilleProducesMetricSchwarzianDataTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hRecovery : HyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem := by
  intro u z hu hz
  rcases hMetric u hu with ⟨M⟩
  rcases hFrob M.toLocalSchwarzianData hz with ⟨a, ⟨P⟩⟩
  have hzP : z ∈ P.toLocalProjectiveDevelopingMap.domain := by
    simpa [CenteredNormalizedSchwarzianFrobeniusPair.toLocalProjectiveDevelopingMap,
      CenteredNormalizedSchwarzianFrobeniusPair.toLocalSchwarzianODEChart,
      LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap] using
      mem_centeredBallDomain_center P.radius_pos
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu
      (P.toLocalProjectiveDevelopingMap.domain_subset hzP) with ⟨J⟩
  rcases
      (localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_canonicalThirdDerivativeIdentification
        localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem)
        P hzP J with
    ⟨N, _hNJ, hNz⟩
  exact ⟨M.toLocalSchwarzianData,
    N.normalized.toLocalUpperHalfPlaneDevelopingMap
      (hRecovery M N hu), hNz⟩

/--
The metric-Schwarzian local-map route with the canonical Poincare pullback
formula as its only pullback-side input.  The corrected Wirtinger-Riccati
uniqueness data are built internally from the formula package and the
metric-Schwarzian coefficient identification.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_canonicalPullbackLiouvilleFormula
    (hPullback : HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian
    hyperbolicLiouvilleProducesMetricSchwarzianDataTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    (hyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem_of_canonicalPullbackLiouvilleFormula
      hPullback)

/--
The metric-Schwarzian local-map route fed by the derivative-identified
canonical pullback package.  This bypasses the older separate corrected
Riccati input by deriving the canonical Poincare pullback formula first.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_canonicalPullbackLiouvilleFormula
    (hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_derivIdentified hD)

/--
The metric-Schwarzian local-map route fed by derivative algebra for the
normalized branch.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_derivativeAlgebra
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_derivIdentified
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra hAlg)

/--
The metric-Schwarzian local-map route fed by actual affine derivative algebra.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_canonicalPullbackLiouvilleFormula
    (hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_core
      (hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_affineDerivativeAlgebra hA))

/--
The metric-Schwarzian local-map route fed by actual affine `HasDerivAt`
pullback data.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_derivativeAlgebra
    (hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_affineDerivative hA)

/--
The metric-Schwarzian local-map route fed by regularity and the bundled
derivative-identification package.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_regularity_derivativeIdentification
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_derivativeAlgebra
    (hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_regularity_and_derivativeIdentification
      hReg hId)

/--
The metric-Schwarzian local-map route fed by regularity and the three concrete
ordinary-derivative identifications for the affine branch and its first two
derivative branches.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_regularity_first_second_third
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_derivativeAlgebra
    (hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_regularity_first_second_third
      hReg hFirst hSecond hThird)

/--
With the holomorphic-Schwarzian and Frobenius parts discharged, the sharp
derivative-identified pullback/canonical-Riccati boundary alone gives genuine
local upper-half-plane developing maps.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentifiedCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_provedNormalForm
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    B.recoversMetric

/--
With the holomorphic-Schwarzian and Frobenius parts discharged, the
derivative-identified pullback/corrected-Wirtinger boundary gives genuine local
upper-half-plane developing maps.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_provedNormalForm
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    B.recoversMetric

/--
With the holomorphic-Schwarzian and Frobenius parts discharged, the two
unbundled local-map inputs are exactly the derivative-identified Poincare
pullback calculation and the corrected Frechet-Wirtinger Riccati theorem.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hPullback : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    (hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
      hPullback hRiccati)

/--
With the Schwarzian/Frobenius/normal-form route discharged, actual affine
`HasDerivAt` pullback data and corrected Frechet-Wirtinger Riccati data give
local upper-half-plane developing maps.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_affineDerivative_and_wirtingerRiccati
    (hAffine : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivative hAffine)
    hRiccati

/--
With the Schwarzian/Frobenius/normal-form route discharged, actual affine
derivative algebra, the Poincare Laplacian identity, and corrected
Frechet-Wirtinger Riccati data give local upper-half-plane developing maps.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_affineDerivativeAlgebra_laplacian_wirtingerRiccati
    (hAffine : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivativeAlgebra_and_laplacian
      hAffine hLap)
    hRiccati

/--
With the Schwarzian/Frobenius/normal-form route discharged, actual affine
derivative algebra and corrected Frechet-Wirtinger Riccati data give local
upper-half-plane developing maps.  The Poincare Laplacian calculation is
provided by the explicit mixed-expression pullback proof.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_affineDerivativeAlgebra_and_wirtingerRiccati
    (hAffine : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivativeAlgebra
      hAffine)
    hRiccati

/--
With the Schwarzian/Frobenius/normal-form route discharged, the local map is
obtained from derivative algebra for the normalized branch, the Poincare
Laplacian identity, and corrected Frechet-Wirtinger Riccati data.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivativeAlgebra_laplacian_wirtingerRiccati
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra_and_laplacian
      hAlg hLap)
    hRiccati

/--
With the Schwarzian/Frobenius/normal-form route discharged, derivative algebra
for the normalized branch and corrected Frechet-Wirtinger Riccati data give
local upper-half-plane developing maps.  The Poincare Laplacian calculation is
supplied internally through the affine-derivative algebra conversion.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivativeAlgebra_and_wirtingerRiccati
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra hAlg)
    hRiccati

/--
With the Schwarzian/Frobenius/normal-form route discharged, the local map is
obtained from regularity of the normalized branch, derivative identification
for its affine branch, the Poincare Laplacian identity, and corrected
Frechet-Wirtinger Riccati data.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_regularity_derivativeIdentification_laplacian_wirtingerRiccati
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_derivativeIdentification_and_laplacian
      hReg hId hLap)
    hRiccati

/--
With the Schwarzian/Frobenius/normal-form route discharged, regularity,
derivative identification, and corrected Frechet-Wirtinger Riccati data give
local upper-half-plane developing maps.  The Poincare Laplacian calculation is
supplied internally by the derivative-algebra route.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_regularity_derivativeIdentification_wirtingerRiccati
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_derivativeIdentification
      hReg hId)
    hRiccati

/--
With the Schwarzian/Frobenius/normal-form route discharged, the local map is
obtained from branch regularity, the three affine derivative-identification
levels, the Poincare Laplacian identity, and corrected Frechet-Wirtinger
Riccati data.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_regularity_first_second_third_laplacian_wirtingerRiccati
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_first_second_third_laplacian
      hReg hFirst hSecond hThird hLap)
    hRiccati

/--
With the Schwarzian/Frobenius/normal-form route discharged, branch regularity,
the three affine derivative-identification levels, and corrected
Frechet-Wirtinger Riccati data give local upper-half-plane developing maps.
The Poincare Laplacian calculation is supplied internally.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_regularity_first_second_third_wirtingerRiccati
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_first_second_third
      hReg hFirst hSecond hThird)
    hRiccati

/--
The sharper Frobenius route expressed in terms of the individual
Frobenius-solution derivative theorem.  Mathlib's quotient rule then proves the
developing-ratio derivative, and the normal-form chain-rule bridge handles the
upper-half-plane normalization.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_solutionHasDerivAt
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_affineHasDerivAt
    hS hFrob
    (localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem_of_solutionHasDerivAt
      hSolDeriv)
    hRecovery

/--
The sharp Frobenius route expressed in terms of the scalar termwise-derivative
power-series boundary.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_scalarFormalPowerSeriesDeriv
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_solutionHasDerivAt
    hS hFrob
    (centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
      hScalarDeriv)
    hRecovery

/--
The canonical Frobenius route with scalar termwise differentiation already
discharged inside the normal-form package.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_termwiseDifferentiation
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    hS hFrob
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    hRecovery

/--
The constant-curvature Schwarzian theorem specializes to the hyperbolic
Liouville equation.
-/
def hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_constantCurvature
    (h : ConstantCurvatureProducesHolomorphicSchwarzianTheorem) :
    HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem :=
  fun u hu ↦
    h u (-1)
      ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)

/--
The constant-curvature unscaled Liouville Schwarzian theorem specializes to the
hyperbolic unscaled theorem.
-/
def hyperbolicLiouvilleProducesHalfSchwarzianDataTheorem_of_constantCurvature
    (h : ConstantCurvatureProducesHalfSchwarzianDataTheorem) :
    HyperbolicLiouvilleProducesHalfSchwarzianDataTheorem :=
  fun u hu ↦
    h u (-1)
      ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)

/--
The constant-curvature Frechet/Wirtinger derivative package specializes to the
hyperbolic Liouville equation.
-/
def hyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem_of_constantCurvature
    (h : ConstantCurvatureProducesWirtingerDerivativePackageTheorem) :
    HyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem :=
  fun u hu ↦
    h u (-1)
      ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)

/--
The hyperbolic Wirtinger package theorem now follows from the named analytic
axioms by specializing the constant-curvature theorem to `K = -1`.
-/
theorem hyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem :
    HyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem :=
  hyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem_of_constantCurvature
    constantCurvatureProducesWirtingerDerivativePackageTheorem

/--
The constant-curvature local Schwarzian ODE chart theorem specializes to the
hyperbolic Liouville equation.
-/
def hyperbolicLiouvilleProducesLocalSchwarzianODEChartsTheorem_of_constantCurvature
    (h : ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem) :
    HyperbolicLiouvilleProducesLocalSchwarzianODEChartsTheorem :=
  fun u {z} hu hz ↦
    h u (-1) (z := z)
      ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)
      hz

/--
The constant-curvature local projective developing-map theorem specializes to
the hyperbolic Liouville equation.
-/
def hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_constantCurvature
    (h : ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  fun u {z} hu hz ↦
    h u (-1) (z := z)
      ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)
      hz

/-- Local Schwarzian ODE charts projectivize in the hyperbolic specialization. -/
def hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_ODECharts
    (h : HyperbolicLiouvilleProducesLocalSchwarzianODEChartsTheorem) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem := by
  intro u z hu hz
  rcases h u hu hz with ⟨S, C, hCz⟩
  exact ⟨S, C.toLocalProjectiveDevelopingMap, hCz⟩

/--
The hyperbolic holomorphic-Schwarzian theorem plus local
projective-developing-map solvability gives local projective developing maps.
-/
def hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_schwarzian
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hDev : HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem := by
  intro u z hu hz
  rcases hS u hu with ⟨S⟩
  rcases hDev S hz with ⟨D, hDz⟩
  exact ⟨S, D, hDz⟩

/--
The hyperbolic holomorphic-Schwarzian theorem plus Frobenius-pair existence
gives local projective developing maps.
-/
def hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_schwarzian hS
    (holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_frobeniusPairExistence hFrob)

/--
Hyperbolic Frechet/Wirtinger derivative packages plus Frobenius-pair existence
give local projective developing maps.
-/
def hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_wirtingerDerivativePackage
    (hW : HyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius
    (hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_wirtingerDerivativePackage hW)
    hFrob

/--
Local projective developing maps plus hyperbolic branch selection give genuine
upper-half-plane local developing maps.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_projective
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hBranch : HyperbolicProjectiveDevelopingMapLiftsToUpperHalfPlaneTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem := by
  intro u z hu hz
  rcases hProj u hu hz with ⟨S, D, hDz⟩
  rcases hBranch S D hu hDz with ⟨H, hHD, hHz⟩
  exact ⟨S, H, hHz⟩

/--
Local projective developing maps plus the sharper Mobius-normalization theorem
give genuine upper-half-plane local developing maps recovering the metric.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_projectiveNormalization
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hNorm : HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem := by
  intro u z hu hz
  rcases hProj u hu hz with ⟨S, D, hDz⟩
  rcases hNorm S D hu hDz with ⟨N, hNz⟩
  exact ⟨S, N.normalized, hNz⟩

/--
The hyperbolic holomorphic-Schwarzian theorem, Frobenius existence, and the
metric-recovering Mobius-normalization theorem give local `ℍ`-valued
developing maps recovering the metric.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusNormalization
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hNorm : HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_projectiveNormalization
    (hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS hFrob)
    hNorm

/--
Local projective developing maps plus precise 2-jet normalization and the
metric-recovery uniqueness theorem give genuine upper-half-plane local
developing maps recovering the metric.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetNormalization
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_projectiveNormalization
    hProj
    (hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
      hJet hRecovery)

/--
Local projective developing maps plus precise 2-jet normalization and the
bundled Riccati analytic boundary give genuine upper-half-plane local
developing maps recovering the metric.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetRiccatiAnalyticBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric

/--
Local projective developing maps plus precise 2-jet normalization and the
derivative-identified canonical pullback/Riccati boundary give genuine
upper-half-plane local developing maps recovering the metric.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetDerivIdentifiedBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetRiccatiAnalyticBoundary
    hProj hJet B.toRiccatiAnalyticBoundary

/--
Local projective developing maps plus precise 2-jet normalization and the
derivative-identified pullback/corrected-Wirtinger boundary give genuine
upper-half-plane local developing maps recovering the metric.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric

/--
The hyperbolic holomorphic-Schwarzian theorem, Frobenius existence, precise
2-jet normalization, and metric-recovery uniqueness give local `ℍ`-valued
developing maps recovering the metric.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetNormalization
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetNormalization
    (hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS hFrob)
    hJet hRecovery

/--
The hyperbolic holomorphic-Schwarzian theorem, Frobenius existence, precise
2-jet normalization, and the bundled Riccati analytic boundary give local
`ℍ`-valued developing maps recovering the metric.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetRiccatiAnalyticBoundary
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_twoJetRiccatiAnalyticBoundary
    (hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS hFrob)
    hJet B

/-- Genuine local upper-half-plane developing maps forget to projective maps. -/
def hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_upperHalfPlane
    (h : HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem := by
  intro u z hu hz
  rcases h u hu hz with ⟨S, H, hHz⟩
  exact ⟨S, H.toLocalProjectiveDevelopingMap, hHz⟩

/--
Local Schwarzian ODE charts plus hyperbolic branch selection give genuine
upper-half-plane local developing maps.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_ODECharts
    (hCharts : HyperbolicLiouvilleProducesLocalSchwarzianODEChartsTheorem)
    (hBranch : HyperbolicProjectiveDevelopingMapLiftsToUpperHalfPlaneTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_projective
    (hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_ODECharts hCharts)
    hBranch

/--
Constant-curvature projective developing maps, specialized to the hyperbolic
Liouville equation, plus branch selection give local `ℍ`-valued developing maps.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_constantCurvature
    (hProj : ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem)
    (hBranch : HyperbolicProjectiveDevelopingMapLiftsToUpperHalfPlaneTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_projective
    (hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_constantCurvature hProj)
    hBranch

/--
Constant-curvature projective developing maps, specialized to the hyperbolic
Liouville equation, plus Mobius normalization give metric-recovering
upper-half-plane local developing maps.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_constantCurvatureNormalization
    (hProj : ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem)
    (hNorm : HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_projectiveNormalization
    (hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_constantCurvature hProj)
    hNorm

/--
The constant-curvature holomorphic-Schwarzian theorem, Frobenius existence, and
metric-recovering Mobius normalization give the hyperbolic local developing maps.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_constantCurvatureFrobeniusNormalization
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hNorm : HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_constantCurvatureNormalization
    (constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS hFrob)
    hNorm

/--
The constant-curvature holomorphic-Schwarzian theorem, Frobenius existence,
precise 2-jet normalization, and the bundled Riccati analytic boundary give
the hyperbolic local developing maps.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_constantCurvatureFrobeniusTwoJetRiccatiAnalyticBoundary
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetRiccatiAnalyticBoundary
    (hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_constantCurvature hS)
    hFrob hJet B

/--
The constant-curvature Frechet/Wirtinger package, Frobenius existence, precise
2-jet normalization, and the bundled Riccati analytic boundary give the
hyperbolic local developing maps.
-/
def hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_wirtingerDerivativePackageFrobeniusTwoJetRiccatiAnalyticBoundary
    (hW : ConstantCurvatureProducesWirtingerDerivativePackageTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetRiccatiAnalyticBoundary
    (hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_wirtingerDerivativePackage
      (hyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem_of_constantCurvature hW))
    hFrob hJet B

/--
Bundled local Schwarzian analytic boundary for producing real
upper-half-plane branch atlases from a hyperbolic Liouville factor.

The fields isolate the remaining mathematical obligations after the
mathlib-backed Frobenius coefficient estimates, coefficient Taylor expansion,
Riccati primitive, and product-rule steps: holomorphic Schwarzian data, the
finite two-jet normalization with ball-domain shrinking, and real-transition
uniqueness.
-/
structure HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- The Riccati analytic boundary gives metric recovery for the normalized 2-jet. -/
  riccatiBoundary : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems
  /-- Metric-recovering upper-half-plane branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem

end

end JJMath
