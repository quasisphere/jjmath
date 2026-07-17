import JJMath.Hyperbolic.Converse.Setup.OverlapStability.FirstOrderStability

/-!
# Split overlap-stability setup declarations
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
Canonical-frame at-point persistence obtained from direct one-jet local
stability for holomorphic local isometries.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransition_canonicalFirstOrderMatch_persists_atPoint_of_holomorphicLocalIsometryOneJetStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X)
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {A : RealMobiusRepresentative} {y : X}
    (hyCanon : HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A y) :
    ∃ W : Set X,
      IsOpen W ∧ y ∈ W ∧
        ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
          V.toUpperHalfPlane z =
              realMobiusRepresentativeAction A (U.toUpperHalfPlane z) ∧
            HyperbolicLocalChartPointedFirstOrderMatch U V A z :=
  pointedHyperbolicLocalChartRealMobiusTransition_canonicalFirstOrderMatch_persists_atPoint_of_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryOneJetStability
      h)
    hyCanon

/--
One-jet local persistence and one-jet equality-locus openness are
interchangeable theorem targets.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_iff_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem
        X ↔
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X :=
  ⟨pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_oneJetLocalPersistence,
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_oneJetEqualitySetOpen⟩

/--
One-jet local persistence gives the older value-only local-persistence target
once value equality is known to force the first-order match.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_valueForcesFirstOrder_oneJetLocalPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X)
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X := by
  intro g U V A x₀ hpoint y hyU hyV hyEq
  rcases hLocal g U V A x₀ hpoint y hyU hyV hyEq
      (hFirst g U V A x₀ hpoint y hyU hyV hyEq) with
    ⟨W, hWopen, hyW, hW⟩
  refine ⟨W, hWopen, hyW, ?_⟩
  intro z hzW hzU hzV
  exact (hW z hzW hzU hzV).1

/--
The one-jet open-locus target gives value-only local persistence under the
same first-order-at-value-equality auxiliary input.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_valueForcesFirstOrder_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X :=
  pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_valueForcesFirstOrder_oneJetLocalPersistence
    hFirst
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_oneJetEqualitySetOpen
      hOpen)

/--
Assemble the corrected one-jet local-isometry package from concrete metric
frame data, chart continuity, one-jet openness, and the auxiliary
value-implies-frame statement.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  ⟨{ coordinateDerivativeData :=
      hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
        hDeriv hPull
     chartContinuous := hChart
     oneJetLocalPersistence :=
      pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_oneJetEqualitySetOpen
        hOpen
     valueEqualityForcesFirstOrder := hValueFirst }⟩

/--
The same corrected one-jet local-isometry package, with derivative
nonvanishing extracted from the Poincare pullback squared-density formula.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen
    (hyperbolicLocalChartCoordinateDerivativeNonzeroTheorem_of_pullbackSquaredDensityFormula
      hPull)
    hPull hChart hOpen hValueFirst

/--
Assemble the corrected one-jet local-isometry package from the cross-chart
open-loci proof of one-jet openness.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_crossChartOpenLoci
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOpen :
      HyperbolicLocalChartCrossChartOneJetOpenLociTheorems X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen
    hDeriv hPull hChart
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_crossChartOpenLoci
      hOpen)
    hValueFirst

/--
Cross-chart open loci plus the Poincare pullback squared-density formula
assemble the corrected one-jet local-isometry package.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_crossChartOpenLoci_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOpen :
      HyperbolicLocalChartCrossChartOneJetOpenLociTheorems X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen_pullbackSquaredDensityFormula
    hPull hChart
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_crossChartOpenLoci
      hOpen)
    hValueFirst

/--
Assemble the corrected one-jet local-isometry package from the cross-chart
local-persistence proof of one-jet openness.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_crossChartLocalPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hLocal :
      HyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen
    hDeriv hPull hChart
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_crossChartLocalPersistence
      hLocal)
    hValueFirst

/--
Cross-chart local persistence plus the Poincare pullback squared-density
formula assemble the corrected one-jet local-isometry package.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_crossChartLocalPersistence_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hLocal :
      HyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen_pullbackSquaredDensityFormula
    hPull hChart
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_crossChartLocalPersistence
      hLocal)
    hValueFirst

/--
Assemble the corrected one-jet local-isometry package from the component
stability theorems proved from the actual holomorphic local-isometry fields.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryComponentStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_crossChartLocalPersistence
    hDeriv hPull hChart
    (hyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems_of_holomorphicLocalIsometryComponentStability
      hStability)
    hValueFirst

/--
Component stability for holomorphic local isometries plus the Poincare
pullback squared-density formula assemble the corrected one-jet package.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryComponentStability_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_crossChartLocalPersistence_pullbackSquaredDensityFormula
    hPull hChart
    (hyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems_of_holomorphicLocalIsometryComponentStability
      hStability)
    hValueFirst

/--
Assemble the corrected one-jet local-isometry package from the direct one-jet
local-stability theorem proved from actual holomorphic local-isometry fields.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryOneJetStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  ⟨{ coordinateDerivativeData :=
      hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
        hDeriv hPull
     chartContinuous := hChart
     oneJetLocalPersistence :=
      pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_holomorphicLocalIsometryOneJetStability
        hStability
     valueEqualityForcesFirstOrder := hValueFirst }⟩

/--
Direct one-jet stability for holomorphic local isometries plus the Poincare
pullback squared-density formula assemble the corrected one-jet package.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryOneJetStability_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryOneJetStability
    (hyperbolicLocalChartCoordinateDerivativeNonzeroTheorem_of_pullbackSquaredDensityFormula
      hPull)
    hPull hChart hStability hValueFirst

/--
Direct one-jet stability plus the Poincare pullback squared-density formula
assemble the corrected one-jet local-isometry package; chart continuity and
the stored local-isometry fields are automatic.
-/
def hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetStability_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hStability :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryOneJetStability_pullbackSquaredDensityFormula
    hPull
    hyperbolicLocalChartContinuousOnDomainTheorem
    (hyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems_of_stability
      hStability)
    hValueFirst

/--
The corrected one-jet local-isometry package forgets to the older value-only
package once value equality is known to force the first-order match.
-/
def hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_oneJet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X :=
  h.elim fun H ↦
    ⟨{ coordinateDerivativeData := H.coordinateDerivativeData
       chartContinuous := H.chartContinuous
       localPersistence :=
        pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_valueForcesFirstOrder_oneJetLocalPersistence
          H.valueEqualityForcesFirstOrder H.oneJetLocalPersistence }⟩

/-- Clopen equality-locus target for local-chart pointed comparisons. -/
def PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsClopen (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A)

/-- Closedness plus openness gives the local-chart clopen equality-locus target. -/
def pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem_of_closed_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem X := by
  intro g U V A x₀ hpoint
  exact ⟨hClosed g U V A x₀ hpoint, hOpen g U V A x₀ hpoint⟩

/--
If the pointed equality locus is clopen in the overlap, then preconnectedness
propagates a pointed local-chart real-Mobius comparison across the whole
overlap.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X := by
  intro g U V A x₀ hpoint hconn x hxU hxV
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A
  haveI : PreconnectedSpace overlap := Subtype.preconnectedSpace hconn
  have hE : IsClopen E := hClopen g U V A x₀ hpoint
  have hx₀_overlap : x₀ ∈ overlap := ⟨hpoint.mem_left, hpoint.mem_right⟩
  have hx₀_E : (⟨x₀, hx₀_overlap⟩ : overlap) ∈ E := by
    simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet]
      using hpoint.value_match
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨x₀, hx₀_overlap⟩, hx₀_E⟩
  have hx_overlap : x ∈ overlap := ⟨hxU, hxV⟩
  have hx_E : (⟨x, hx_overlap⟩ : overlap) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet] using hx_E

/--
If the pointed equality locus is clopen in the full overlap, then a pointed
comparison propagates on the connected overlap component containing the
pointed match.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_equalitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X := by
  intro g U V A x₀ hpoint x hxU hxV hxComponent
  let overlap : Set X := U.domain ∩ V.domain
  let component : Set X := connectedComponentIn overlap x₀
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A
  let incl : component → overlap := fun y =>
    ⟨(y : X), connectedComponentIn_subset overlap x₀ y.property⟩
  let Ecomponent : Set component := incl ⁻¹' E
  haveI : PreconnectedSpace component :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have hincl : Continuous incl :=
    Continuous.subtype_mk continuous_subtype_val
      (fun y => connectedComponentIn_subset overlap x₀ y.property)
  have hE : IsClopen E := hClopen g U V A x₀ hpoint
  have hEcomponent : IsClopen Ecomponent :=
    ⟨hE.1.preimage hincl, hE.2.preimage hincl⟩
  have hx₀_overlap : x₀ ∈ overlap := ⟨hpoint.mem_left, hpoint.mem_right⟩
  have hx₀_component : x₀ ∈ component :=
    mem_connectedComponentIn hx₀_overlap
  have hx₀_Ecomponent :
      (⟨x₀, hx₀_component⟩ : component) ∈ Ecomponent := by
    simpa [Ecomponent, incl, E,
      pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet] using
      hpoint.value_match
  have hE_univ : Ecomponent = Set.univ :=
    IsClopen.eq_univ hEcomponent
      ⟨⟨x₀, hx₀_component⟩, hx₀_Ecomponent⟩
  have hx_component : x ∈ component := by
    simpa [component, overlap] using hxComponent
  have hx_Ecomponent : (⟨x, hx_component⟩ : component) ∈ Ecomponent := by
    rw [hE_univ]
    exact Set.mem_univ _
  simpa [Ecomponent, incl, E,
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet] using
    hx_Ecomponent

/--
Closedness and openness of the local-chart equality locus imply
connected-overlap extension of pointed matches.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySet_closed_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySetClopen
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem_of_closed_open
      hClosed hOpen)

/-- Closedness and openness of the equality locus imply componentwise extension. -/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_equalitySet_closed_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_equalitySetClopen
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem_of_closed_open
      hClosed hOpen)

/--
Openness of the equality locus is the only remaining topological input for
connected-overlap propagation: closedness is now obtained from the stored
continuity of hyperbolic local charts.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySet_closed_open
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    hOpen

/--
Openness of the equality locus plus stored chart continuity is enough for
componentwise pointed-match propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_equalitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_equalitySet_closed_open
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    hOpen

/-- Closedness target for the corrected one-jet equality locus. -/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsClosed
          (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet
            U V A)

/--
Closed value-equality loci and closed first-order-frame loci give closedness
of the corrected one-jet equality locus.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_valueClosed_firstOrderClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
        X)
    (hFirstClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem
      X := by
  intro g U V A x₀ hpoint
  have hValue :
      IsClosed (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A) :=
    hValueClosed g U V A x₀ hpoint
  have hFirst :
      IsClosed
        (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet
          U V A) :=
    hFirstClosed g U V A x₀ hpoint
  simpa [pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet,
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet,
    pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet,
    Set.setOf_and] using hValue.inter hFirst

/--
First-order-frame closedness is the only remaining closedness input for the
corrected one-jet locus, since value-equality loci are closed by continuity.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_firstOrderClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirstClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_valueClosed_firstOrderClosed
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    hFirstClosed

/--
If value equality for a pointed comparison forces the oriented first-order
frame match, then the corrected one-jet locus is the old value-equality
locus.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet_eq_equalitySet_of_valueEqualityForcesFirstOrder
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X)
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {A : RealMobiusRepresentative} {x₀ : X}
    (hpoint : HyperbolicLocalChartPointedRealMobiusTransition U V A x₀) :
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet U V A =
      pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact
      ⟨hx,
        hValueFirst g U V A x₀ hpoint (x : X)
          x.property.1 x.property.2 hx⟩

/--
The corrected one-jet equality locus is closed once value equality determines
the oriented first-order frame.  Closedness then comes from the already-proved
continuity of the value equality locus.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_valueEqualityForcesFirstOrder
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem
      X := by
  intro g U V A x₀ hpoint
  rw [
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet_eq_equalitySet_of_valueEqualityForcesFirstOrder
      hValueFirst hpoint]
  exact
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
      g U V A x₀ hpoint

/-- Clopen target for the corrected one-jet equality locus. -/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsClopen
          (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet
            U V A)

/-- Closedness plus openness gives the one-jet clopen-locus target. -/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_closed_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
      X := by
  intro g U V A x₀ hpoint
  exact ⟨hClosed g U V A x₀ hpoint, hOpen g U V A x₀ hpoint⟩

/--
Value equality forcing the first-order frame supplies the closed side of the
corrected one-jet locus, so openness alone gives the clopen theorem.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_valueEqualityForcesFirstOrder_and_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_closed_open
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_valueEqualityForcesFirstOrder
      hValueFirst)
    hOpen

/--
First-order-frame closedness supplies the closed side of the corrected
one-jet locus; one-jet openness supplies the open side.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_firstOrderClosed_and_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirstClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_closed_open
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_firstOrderClosed
      hFirstClosed)
    hOpen

/--
Connected-overlap extension target for corrected one-jet pointed comparisons.

This is the strengthened propagation statement needed by the selected
one-jet route: the value equality and the oriented first-order frame match
both propagate across a preconnected overlap.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
    HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
      IsPreconnected (U.domain ∩ V.domain) →
        ∀ x, x ∈ U.domain → x ∈ V.domain →
          V.toUpperHalfPlane x =
              realMobiusRepresentativeAction A (U.toUpperHalfPlane x) ∧
            HyperbolicLocalChartPointedFirstOrderMatch U V A x

/--
Componentwise one-jet extension target for pointed hyperbolic local-chart
matches.

The conclusion is restricted to the connected component of the common domain
which contains the pointed transition.  This avoids the false demand that one
Mobius representative control every connected component of a disconnected
overlap.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
    HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
      ∀ x, x ∈ U.domain → x ∈ V.domain →
        x ∈ connectedComponentIn (U.domain ∩ V.domain) x₀ →
          V.toUpperHalfPlane x =
              realMobiusRepresentativeAction A (U.toUpperHalfPlane x) ∧
            HyperbolicLocalChartPointedFirstOrderMatch U V A x

/--
If the corrected one-jet equality locus is clopen in the overlap, then
preconnectedness propagates the pointed one-jet comparison across the whole
overlap.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X := by
  intro g U V A x₀ hpoint hconn x hxU hxV
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet U V A
  haveI : PreconnectedSpace overlap := Subtype.preconnectedSpace hconn
  have hE : IsClopen E := hClopen g U V A x₀ hpoint
  have hx₀_overlap : x₀ ∈ overlap := ⟨hpoint.mem_left, hpoint.mem_right⟩
  have hx₀_E : (⟨x₀, hx₀_overlap⟩ : overlap) ∈ E := by
    simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet]
      using And.intro hpoint.value_match hpoint.first_order_match
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨x₀, hx₀_overlap⟩, hx₀_E⟩
  have hx_overlap : x ∈ overlap := ⟨hxU, hxV⟩
  have hx_E : (⟨x, hx_overlap⟩ : overlap) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet]
    using hx_E

/--
If the corrected one-jet equality locus is clopen in the full overlap, then
one-jet agreement propagates on the connected overlap component containing
the pointed match.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_oneJetEqualitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X := by
  intro g U V A x₀ hpoint x hxU hxV hxComponent
  let overlap : Set X := U.domain ∩ V.domain
  let component : Set X := connectedComponentIn overlap x₀
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet U V A
  let incl : component → overlap := fun y =>
    ⟨(y : X), connectedComponentIn_subset overlap x₀ y.property⟩
  let Ecomponent : Set component := incl ⁻¹' E
  haveI : PreconnectedSpace component :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have hincl : Continuous incl :=
    Continuous.subtype_mk continuous_subtype_val
      (fun y => connectedComponentIn_subset overlap x₀ y.property)
  have hE : IsClopen E := hClopen g U V A x₀ hpoint
  have hEcomponent : IsClopen Ecomponent :=
    ⟨hE.1.preimage hincl, hE.2.preimage hincl⟩
  have hx₀_overlap : x₀ ∈ overlap := ⟨hpoint.mem_left, hpoint.mem_right⟩
  have hx₀_component : x₀ ∈ component :=
    mem_connectedComponentIn hx₀_overlap
  have hx₀_Ecomponent :
      (⟨x₀, hx₀_component⟩ : component) ∈ Ecomponent := by
    simpa [Ecomponent, incl, E,
      pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet] using
      And.intro hpoint.value_match hpoint.first_order_match
  have hE_univ : Ecomponent = Set.univ :=
    IsClopen.eq_univ hEcomponent
      ⟨⟨x₀, hx₀_component⟩, hx₀_Ecomponent⟩
  have hx_component : x ∈ component := by
    simpa [component, overlap] using hxComponent
  have hx_Ecomponent : (⟨x, hx_component⟩ : component) ∈ Ecomponent := by
    rw [hE_univ]
    exact Set.mem_univ _
  simpa [Ecomponent, incl, E,
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet] using
    hx_Ecomponent

/--
Closedness and openness of the corrected one-jet equality locus imply
connected-overlap one-jet propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySet_closed_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_closed_open
      hClosed hOpen)

/-- Closedness and openness also give componentwise one-jet propagation. -/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_oneJetEqualitySet_closed_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_oneJetEqualitySetClopen
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_closed_open
      hClosed hOpen)

/--
Value equality forcing the first-order frame supplies closedness, so one-jet
openness is enough for connected-overlap one-jet propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_valueEqualityForcesFirstOrder_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_valueEqualityForcesFirstOrder_and_open
      hValueFirst hOpen)

/--
Value equality forcing the first-order frame plus one-jet openness gives
componentwise one-jet propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_valueEqualityForcesFirstOrder_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_oneJetEqualitySetClopen
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_valueEqualityForcesFirstOrder_and_open
      hValueFirst hOpen)

/--
First-order-frame closedness and one-jet openness give connected-overlap
one-jet propagation.  This is the honest topological split of the corrected
one-jet clopen argument.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirstClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_firstOrderClosed_and_open
      hFirstClosed hOpen)

/--
First-order-frame closedness and one-jet openness give componentwise one-jet
propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirstClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_oneJetEqualitySetClopen
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_firstOrderClosed_and_open
      hFirstClosed hOpen)

/-- One-jet propagation forgets to the older value-only propagation target. -/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
      X := by
  intro g U V A x₀ hpoint hconn x hxU hxV
  exact (hExtend g U V A x₀ hpoint hconn x hxU hxV).1

/-- Componentwise one-jet propagation forgets to componentwise value propagation. -/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_oneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X := by
  intro g U V A x₀ hpoint x hxU hxV hxComponent
  exact (hExtend g U V A x₀ hpoint x hxU hxV hxComponent).1

end HyperbolicMetric

end

end JJMath
