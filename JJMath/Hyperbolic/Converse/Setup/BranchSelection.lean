import JJMath.Hyperbolic.Converse.Setup.OverlapStability

/-!
# Split partial-converse setup declarations
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
The Poincare pullback squared-density formula supplies the pointed frame data
needed to turn concrete first-order closedness plus one-jet openness into
connected-overlap one-jet propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed
      hPull hConcrete)
    hOpen

/--
The Poincare pullback squared-density formula supplies the pointed frame data
needed to turn concrete first-order closedness plus one-jet openness into
componentwise one-jet propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed
      hPull hConcrete)
    hOpen

/--
Concrete first-order closedness plus one-jet openness gives componentwise
one-jet propagation, with the Poincare pullback formula discharged.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hConcrete hOpen

/--
Concrete first-order closedness plus actual holomorphic local-isometry
first-order stability gives componentwise one-jet propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_concreteFirstOrderClosed_and_holomorphicLocalIsometryFirstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hConcrete
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryFirstOrderStability
      hFirst)

/--
Continuity of the concrete coordinate-derivative comparison maps supplies the
closedness input for connected-overlap one-jet propagation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hPull
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
      hDeriv)
    hOpen

/--
Continuity of each chart-coordinate derivative is enough for the
connected-overlap one-jet propagation theorem, once the corrected one-jet
equality locus is open.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    hPull
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem_of_chartDerivativeContinuity
      hyperbolicLocalChartContinuousOnDomainTheorem hDeriv)
    hOpen

/--
Continuity of each chart-coordinate derivative plus one-jet openness gives
connected-overlap one-jet propagation, with the Poincare pullback formula
discharged.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hDeriv hOpen

/--
The same chart-derivative/open-one-jet package gives componentwise one-jet
propagation, without requiring the whole overlap to be preconnected.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed
      hPull
      (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
        (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem_of_chartDerivativeContinuity
          hyperbolicLocalChartContinuousOnDomainTheorem hDeriv)))
    hOpen

/--
Continuity of each chart-coordinate derivative plus one-jet openness gives
componentwise one-jet propagation, with the Poincare pullback formula
discharged.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hDeriv hOpen

/--
Concrete first-order closedness plus one-jet openness gives connected-overlap
one-jet propagation, with the Poincare pullback formula discharged.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hConcrete hOpen

/--
Concrete derivative-continuity plus one-jet openness gives connected-overlap
one-jet propagation, with both closedness and the pullback formula discharged.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
      hDeriv)
    hOpen

/--
The same chart-derivative/open-one-jet package also gives the older value-only
connected-overlap extension theorem.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetExtension
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
      hPull hDeriv hOpen)

/--
The chart-derivative/open-one-jet package also gives the older value-only
connected-overlap extension theorem, with the Poincare pullback formula
discharged.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetExtension
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_chartDerivativeContinuity_and_oneJetEqualitySetOpen
      hDeriv hOpen)

/--
Pointed real-isometry matching plus connected-overlap extension prove that two
hyperbolic local charts differ by one real Mobius transformation on a
preconnected nonempty overlap.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_extension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X := by
  intro g U V hne hconn
  rcases hne with ⟨x₀, hx₀U, hx₀V⟩
  rcases hPoint g U V x₀ hx₀U hx₀V with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  exact hExtend g U V A x₀ hA hconn

/--
Pointed matching plus a clopen equality-locus theorem prove local-chart real
Mobius transitions on preconnected nonempty overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_extension
    hPoint
    (pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySetClopen
      hClopen)

/--
Pointed matching plus closedness and openness of the equality locus prove
local-chart real Mobius transitions on preconnected nonempty overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySet_closed_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySetClopen
    hPoint
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClopenTheorem_of_closed_open
      hClosed hOpen)

/--
Pointed matching plus openness of the equality locus proves local-chart real
Mobius transitions on preconnected nonempty overlaps.  Closedness is supplied
by local-chart continuity.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
        X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySet_closed_open
    hPoint
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    hOpen

/--
Pointed matching, continuity of the compared maps, and openness of the
equality locus prove local-chart real Mobius transitions on preconnected
nonempty overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySet_continuity_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hCont :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySet_closed_open
    hPoint
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
      hCont)
    hOpen

/--
Pointed matching, chart-domain continuity, and openness of the equality locus
prove local-chart real Mobius transitions on preconnected nonempty overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_chartContinuity_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySet_continuity_open
    hPoint
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem_of_chart_continuity
      hChart)
    hOpen

/--
Pointed matching, chart-domain continuity, and local persistence of equality
prove local-chart real Mobius transitions on preconnected nonempty overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_chartContinuity_localPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_chartContinuity_open
    hPoint hChart
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem_of_localPersistence
      hLocal)

/--
Coordinate derivative data, together with closedness and openness of the
local-chart equality locus, proves local-chart real Mobius transitions on
preconnected nonempty overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_coordinateDerivativeData_equalitySet_closed_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_equalitySet_closed_open
    (hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_coordinateDerivativeData_proved
      hDeriv)
    hClosed hOpen

/--
Coordinate derivative data, continuity of the compared maps, and openness of
the equality locus prove local-chart real Mobius transitions on preconnected
nonempty overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_coordinateDerivativeData_equalitySet_continuity_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hCont :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_coordinateDerivativeData_equalitySet_closed_open
    hDeriv
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
      hCont)
    hOpen

/--
Coordinate derivative data, chart-domain continuity, and openness of the
equality locus prove local-chart real Mobius transitions on preconnected
nonempty overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_coordinateDerivativeData_chartContinuity_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_coordinateDerivativeData_equalitySet_continuity_open
    hDeriv
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem_of_chart_continuity
      hChart)
    hOpen

/--
Coordinate derivative data, chart-domain continuity, and local persistence of
equality prove local-chart real Mobius transitions on preconnected nonempty
overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_coordinateDerivativeData_chartContinuity_localPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_coordinateDerivativeData_chartContinuity_open
    hDeriv hChart
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem_of_localPersistence
      hLocal)

/--
The bundled analytic local-isometry consequences imply real-Mobius transitions
on all preconnected nonempty local-chart overlaps.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_analyticLocalIsometryConsequences
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X := by
  rcases h with ⟨H⟩
  exact
    hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_coordinateDerivativeData_chartContinuity_localPersistence
      H.coordinateDerivativeData H.chartContinuous H.localPersistence

/--
The same real-transition consequence, with the pullback squared-density
formula exposed as a concrete named input.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_analyticLocalIsometryConsequences
    (hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula
      hDeriv hPull hChart hLocal)

/--
The same real-transition consequence, with derivative nonvanishing extracted
from the Poincare pullback squared-density formula.
-/
def hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pullbackSquaredDensityFormula_proved
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X) :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_analyticLocalIsometryConsequences
    (hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_proved
      hPull hChart hLocal)

/--
Preconnectedness of the actual selected surface overlaps.

The surface transition theorem asks for one real Mobius representative on the
whole overlap of two shrunk surface charts.  This condition isolates the
necessary shrinking/topological input: once the selected overlap is
preconnected, local hyperbolic-chart uniqueness can choose a single
representative there.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X, x ≠ y →
      Set.Nonempty
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
      IsPreconnected
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)

/--
Pointwise version of selected surface-overlap preconnectedness for one
Liouville metric formula atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedFor
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) : Prop :=
  ∀ (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X, x ≠ y →
      Set.Nonempty
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
      IsPreconnected
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)

/--
For selected surface overlaps, a pointed transition plus preconnectedness and
the connected-overlap extension theorem give the full real-Mobius transition.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem_of_pointed_extension_overlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X := by
  intro g metricFormulaAtlas preData x y hxy hne
  let U :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  let V :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
  rcases hPoint g metricFormulaAtlas preData x y hxy hne with ⟨x₀, A, hpoint⟩
  change U.HasRealMobiusTransition V
  refine ⟨A, ?_⟩
  intro z hzU hzV
  exact
    hExtend g U V A x₀ hpoint
      (hOverlapPreconnected g metricFormulaAtlas preData x y hxy hne)
      z hzU hzV

/--
Pointwise version of the selected-overlap pointed transition bridge.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionFor_of_pointed_extension_overlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hPoint :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedFor
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionFor
      metricFormulaAtlas := by
  intro preData x y hxy hne
  let U :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  let V :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
  rcases hPoint preData x y hxy hne with ⟨x₀, A, hpoint⟩
  change U.HasRealMobiusTransition V
  refine ⟨A, ?_⟩
  intro z hzU hzV
  exact
    hExtend g U V A x₀ hpoint
      (hOverlapPreconnected preData x y hxy hne)
      z hzU hzV

/--
Preconnectedness of the selected overlaps for one concrete surface branch
predata object.

This is the sharp topological target: the construction should choose/shrink
the surface branches so that the actual overlaps used downstream are
preconnected.  It is intentionally a property of the selected predata, not of
every arbitrary possible predata.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y : X, x ≠ y →
    Set.Nonempty
      ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
    IsPreconnected
      ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)

/--
Trivial componentwise topology of the selected surface overlaps.

For analytic continuation one should work on the connected component of the
overlap containing the transition point.  On a locally path-connected surface,
those components of open overlaps are open; they are preconnected by
definition of `connectedComponentIn`.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y p : X,
    IsOpen
      (connectedComponentIn
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)
        p) ∧
      IsPreconnected
        (connectedComponentIn
          ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
            (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)
          p)

/--
%%handwave
name: Components of selected branch overlaps are open and preconnected
statement:
  On a locally path-connected surface, for any two selected local upper-half-plane chart domains $U_x,U_y$ and any point $p$, the component of $p$ in $U_x\cap U_y$ is open and preconnected.
proof:
  The intersection $U_x\cap U_y$ is open. In a locally path-connected space its component containing $p$ is open, and every connected component in a set is preconnected.
-/
theorem surfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [LocPathConnectedSpace X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood preData := by
  intro x y p
  exact
    ⟨((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).isOpen_domain.inter
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).isOpen_domain).connectedComponentIn,
      isPreconnected_connectedComponentIn⟩

/--
A selected surface real branch predata object whose nonempty off-diagonal
overlaps are preconnected.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected coordinate branch atlases and open restricted domains. -/
  preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas
  /-- The selected off-diagonal overlaps are preconnected whenever nonempty. -/
  overlap_preconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapPreconnected preData

/--
Selected predata with preconnected overlaps and chart-compatible coordinate
pullback formulae.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedPreData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected predata with preconnected overlaps. -/
  preconnectedPreData :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
      metricFormulaAtlas
  /-- The selected coordinate pullback formulae agree with ambient charts. -/
  coordinate_eqOn_chartAt :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEqOnChartAt
      preconnectedPreData.preData

/--
Pointed real-Mobius comparisons propagate on the actual selected overlaps of
one preconnected-overlap predata object.

This is the selected-predata form of the connected-overlap propagation
theorem: it is only required for the hyperbolic local charts which occur in
the chosen surface branch predata.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas) :
    Prop :=
  ∀ x y : X, x ≠ y →
    Set.Nonempty
      ((((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
    ∀ (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
        A x₀ →
      ∀ z,
        z ∈
          (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain →
        z ∈
          (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain →
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).toUpperHalfPlane z =
          realMobiusRepresentativeAction A
            ((((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).toUpperHalfPlane z)

/--
One-jet version of selected-overlap propagation for one concrete selected
predata object.

The conclusion retains both the value equality and the pointed first-order
frame match at every point of the selected overlap.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas) :
    Prop :=
  ∀ x y : X, x ≠ y →
    Set.Nonempty
      ((((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
    ∀ (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
        A x₀ →
      ∀ z,
        z ∈
          (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain →
        z ∈
          (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain →
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).toUpperHalfPlane z =
            realMobiusRepresentativeAction A
              ((((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).toUpperHalfPlane z) ∧
          HyperbolicLocalChartPointedFirstOrderMatch
            (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
            (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
            A z

/--
Componentwise selected-overlap propagation for one concrete surface predata
object.

This is the selected-predata version of the honest analytic-continuation
boundary: a pointed transition propagates only on the connected component of
the selected overlap which contains the pointed transition.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y : X,
    ∀ (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
        A x₀ →
      ∀ z,
        z ∈
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain →
        z ∈
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain →
        z ∈
          connectedComponentIn
            ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
              (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)
            x₀ →
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).toUpperHalfPlane z =
          realMobiusRepresentativeAction A
            ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).toUpperHalfPlane z)

/--
Componentwise one-jet selected-overlap propagation for one concrete surface
predata object.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlapComponents
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y : X,
    ∀ (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
        A x₀ →
      ∀ z,
        z ∈
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain →
        z ∈
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain →
        z ∈
          connectedComponentIn
            ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
              (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)
            x₀ →
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).toUpperHalfPlane z =
            realMobiusRepresentativeAction A
              ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).toUpperHalfPlane z) ∧
          HyperbolicLocalChartPointedFirstOrderMatch
            (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
            (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
            A z

/--
Pointed real-Mobius transition data at every point of every selected
off-diagonal overlap.

This is stronger than the older nonempty-overlap target because the pointed
transition is required at the overlap point where a local transition chart is
being built.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y : X, x ≠ y →
    ∀ p : X,
      p ∈
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain →
      p ∈
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain →
      ∃ A : RealMobiusRepresentative,
        HyperbolicLocalChartPointedRealMobiusTransition
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
          A p

/--
The selected surface branch predata has local real-Mobius transitions on all
selected overlaps.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y : X,
    HyperbolicLocalChart.HasLocalRealMobiusTransition
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)

/--
Selected surface branch predata with local real-Mobius transitions gives the
natural local-transition local-model atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreData_toHyperbolicLocalModelLocalTransitionAtlas
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hTransition :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
        preData) :
    HyperbolicLocalModelLocalTransitionAtlas X g where
  chartAt x :=
    ((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart
  mem_chartAt_domain := by
    intro x
    change x ∈
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula).domain
    exact
      ((preData.toSurfaceSchwarzianPointedBranchPreData).toRestrictedMetricFormulaAtlas).mem_formulaAt_domain
        x
  transition_localRealMobius := hTransition

/--
Selected surface branch data with the natural local-transition compatibility.

This is the replacement local output for the componentwise route: it keeps the
actual selected branch predata and asks only for local real-Mobius transition
data on its overlaps.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected coordinate branch atlases and open restricted domains. -/
  preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas
  /-- The selected shrunk local surface charts have local real-Mobius transitions. -/
  local_transition :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
      preData

namespace SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/-- The local-transition local-model atlas produced by the selected branches. -/
def toHyperbolicLocalModelLocalTransitionAtlas
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
        metricFormulaAtlas) :
    HyperbolicLocalModelLocalTransitionAtlas X g :=
  surfaceRealUpperHalfPlaneBranchAtlasPreData_toHyperbolicLocalModelLocalTransitionAtlas
    S.preData S.local_transition

/--
%%handwave
name: Local transition models from selected real branches
statement:
  If each chart of a local metric-formula atlas has a selected upper-half-plane branch and the selected branches are related locally on overlaps by real Mobius transformations, then the metric admits an atlas of upper-half-plane local models with local real-Mobius transitions.
proof:
  Assemble the selected branches and their local transition witnesses into the corresponding local-model atlas.
-/
theorem hasUpperHalfPlaneLocalTransitionModels
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
        metricFormulaAtlas) :
    g.HasUpperHalfPlaneLocalTransitionModels :=
  ⟨S.toHyperbolicLocalModelLocalTransitionAtlas⟩

end SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection

/--
The old global-transition branch data forgets to the local-transition selected
branch package.
-/
def surfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection_of_surfaceRealUpperHalfPlaneBranchAtlasData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (B : SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
      metricFormulaAtlas where
  preData := B.preData
  local_transition := fun x y ↦
    HyperbolicLocalChart.hasLocalRealMobiusTransition_of_hasRealMobiusTransition
      (B.transition_realMobius x y)

/--
The one-jet selected-overlap propagation statement forgets to the value-only
propagation needed by surface branch-atlas assembly.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_oneJet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    {preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas}
    (hOneJet :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps
        preconnectedPreData) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      preconnectedPreData := by
  intro x y hxy hne A x₀ hpoint z hzU hzV
  exact (hOneJet x y hxy hne A x₀ hpoint z hzU hzV).1

/-- Componentwise one-jet propagation forgets to componentwise value propagation. -/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents_of_oneJet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    {preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas}
    (hOneJet :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlapComponents
        preData) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
      preData := by
  intro x y A x₀ hpoint z hzU hzV hzComponent
  exact (hOneJet x y A x₀ hpoint z hzU hzV hzComponent).1

/--
The global pointed connected-overlap propagation theorem implies its selected
predata version.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_global
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      preconnectedPreData := by
  intro x y hxy hne A x₀ hpoint z hzU hzV
  exact
    hExtend g
      (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      A x₀ hpoint
      (preconnectedPreData.overlap_preconnected x y hxy hne)
      z hzU hzV

/--
The global componentwise pointed propagation theorem implies its selected
predata version.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents_of_global
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
      preData := by
  intro x y A x₀ hpoint z hzU hzV hzComponent
  exact
    hExtend g
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      A x₀ hpoint z hzU hzV hzComponent

/--
The global pointed one-jet connected-overlap propagation theorem implies its
selected predata version.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps_of_global
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps
      preconnectedPreData := by
  intro x y hxy hne A x₀ hpoint z hzU hzV
  exact
    hExtend g
      (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      A x₀ hpoint
      (preconnectedPreData.overlap_preconnected x y hxy hne)
      z hzU hzV

/--
The global componentwise one-jet propagation theorem implies its selected
predata version.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlapComponents_of_global
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnOverlapComponentTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlapComponents
      preData := by
  intro x y A x₀ hpoint z hzU hzV hzComponent
  exact
    hExtend g
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      A x₀ hpoint z hzU hzV hzComponent

/--
Global pointed real-Mobius matching for hyperbolic local charts gives pointed
transitions at every point of every selected off-diagonal overlap.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints_of_localChartPointedTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints
      preData := by
  intro x y _hxy p hpU hpV
  exact
    hPoint g
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      p hpU hpV

/--
Pointed transitions at overlap points plus componentwise propagation produce
local real-Mobius transitions on the selected surface overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions_of_pointedTransitionsAtOverlapPoints_and_componentExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hComponents :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
        preData)
    (hPointAt :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints
        preData)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
        preData) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
      preData := by
  intro x y
  by_cases hxy : x = y
  · subst y
    exact
      HyperbolicLocalChart.hasLocalRealMobiusTransition_self
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  · intro p hp
    let U :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
    let V :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
    have hpU : p ∈ U.domain := hp.1
    have hpV : p ∈ V.domain := hp.2
    rcases hPointAt x y hxy p hpU hpV with ⟨A, hpoint⟩
    let overlap : Set X := U.domain ∩ V.domain
    let component : Set X := connectedComponentIn overlap p
    refine ⟨
      { neighborhood := component
        isOpen_neighborhood := by
          simpa [component, overlap, U, V] using (hComponents x y p).1
        mem_neighborhood := by
          exact mem_connectedComponentIn hp
        subset_overlap := by
          intro z hz
          exact connectedComponentIn_subset overlap p hz
        representative := A
        transition_eq := ?_ }⟩
    intro z hz
    have hzOverlap : z ∈ overlap :=
      connectedComponentIn_subset overlap p hz
    exact
      hExtend x y A p hpoint z hzOverlap.1 hzOverlap.2
        (by simpa [component, overlap, U, V] using hz)

/--
Global pointed matching and componentwise propagation produce local
real-Mobius transitions on the selected surface overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions_of_localChartPointedTransitions_and_componentExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hComponents :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
        preData)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
        preData) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
      preData :=
  surfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions_of_pointedTransitionsAtOverlapPoints_and_componentExtension
    preData hComponents
    (surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints_of_localChartPointedTransitions
      preData hPoint)
    hExtend

/--
Componentwise selected-overlap propagation assembles the local-transition
selected branch package.
-/
def surfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection_of_preData_componentExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hComponents :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
        preData)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
        preData) :
    SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
      metricFormulaAtlas where
  preData := preData
  local_transition :=
    surfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions_of_localChartPointedTransitions_and_componentExtension
      preData hComponents hPoint hExtend

/--
Branch-predata selection for the canonical chart-at curvature atlas.

This is the local branch-choice target with no good-cover or preconnected
overlap condition.
-/
def CanonicalChartedCurvatureBranchPreDataSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreData
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas))

/--
Local-transition branch selection for the canonical chart-at curvature atlas.

The selected branches are required only to have local real-Mobius transition
data on overlaps; representatives may vary from one overlap component to
another.
-/
def CanonicalChartedCurvatureLocalTransitionSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas))

/--
Canonical branch predata, pointed matching, and componentwise propagation
produce local-transition selected branch data.
-/
noncomputable def canonicalChartedCurvatureLocalTransitionSelectionTheorem_of_branchPreDataSelection_pointedTransitions_componentExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocPathConnectedSpace X]
    (hSelection :
      CanonicalChartedCurvatureBranchPreDataSelectionTheorem X)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X) :
    CanonicalChartedCurvatureLocalTransitionSelectionTheorem X := by
  intro g
  rcases hSelection g with ⟨preData⟩
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection_of_preData_componentExtension
      preData
      (surfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood preData)
      hPoint
      (surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents_of_global
        preData hExtend)⟩

/--
The global one-jet extension theorem also gives the older selected value-only
propagation statement.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_global_oneJet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      preconnectedPreData :=
  surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_oneJet
    (surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps_of_global
      preconnectedPreData hExtend)

/--
Global target asserting that the surface branch predata can be chosen with
preconnected selected overlaps.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas)

/--
The preconnected-overlap property for the predata obtained from a specific
choice of coordinate real branch atlases and restricted-domain openness.

This is the sharp selector-level form of the surface shrinking target: rather
than asking every possible predata object to have preconnected overlaps, it
asks for one concrete choice of coordinate branches whose resulting shrunk
surface overlaps have the required preconnectedness.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor)
    (restricted_domain_open :
      ∀ x : X, IsOpen
        {y : X | y ∈ (metricFormulaAtlas.formulaAt x).domain ∧
          (metricFormulaAtlas.formulaAt x).coordinate y ∈
            ((realBranchAtlasAt x).branchNear
              ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
                (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
                  (metricFormulaAtlas.mem_formulaAt_domain x)⟩).domain}) :
    Prop :=
  let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
    { realBranchAtlasAt := realBranchAtlasAt
      restricted_domain_open := restricted_domain_open }
  SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapPreconnected preData

/--
A concrete selector package for the desired surface predata.

It records the actual coordinate real branch atlases chosen at every surface
point, the openness of their restricted surface domains, and preconnectedness
of the nonempty off-diagonal overlaps for this selected predata.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected real branch atlas in each local coordinate. -/
  realBranchAtlasAt :
    ∀ x : X,
      LocalRealUpperHalfPlaneBranchAtlas
        (metricFormulaAtlas.formulaAt x).conformalFactor
  /-- The selected restricted surface domains are open. -/
  restricted_domain_open :
    ∀ x : X, IsOpen
      {y : X | y ∈ (metricFormulaAtlas.formulaAt x).domain ∧
        (metricFormulaAtlas.formulaAt x).coordinate y ∈
          ((realBranchAtlasAt x).branchNear
            ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
              (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
                (metricFormulaAtlas.mem_formulaAt_domain x)⟩).domain}
  /-- The nonempty off-diagonal overlaps of this selected predata are preconnected. -/
  overlap_preconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected
      metricFormulaAtlas realBranchAtlasAt restricted_domain_open

/--
A concrete selected surface predata object whose overlaps are preconnected
and whose chosen coordinate pullback formulae are chart-compatible.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected real branch atlases, open restricted domains, and preconnected overlaps. -/
  selection :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      metricFormulaAtlas
  /-- The selected coordinate pullback formulae agree with ambient charts. -/
  coordinate_eqOn_chartAt :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEqOnChartAt
      ({ realBranchAtlasAt := selection.realBranchAtlasAt
         restricted_domain_open := selection.restricted_domain_open } :
        SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)

/--
A concrete selected surface predata object whose overlaps are preconnected
and whose chosen coordinate pullback formulae are locally chart-compatible at
each point of their domains.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected real branch atlases, open restricted domains, and preconnected overlaps. -/
  selection :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      metricFormulaAtlas
  /-- The selected coordinate pullback formulae are locally ambient-chart coordinates. -/
  coordinate_eventuallyEqOn_chartAt :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEventuallyEqOnChartAt
      ({ realBranchAtlasAt := selection.realBranchAtlasAt
         restricted_domain_open := selection.restricted_domain_open } :
        SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)

/--
A concrete selected surface predata object whose overlaps are preconnected,
whose coordinate pullback formulae are chart-compatible, and whose pointed
comparisons propagate on those selected overlaps.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected chart-compatible predata. -/
  chartedSelection :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
      metricFormulaAtlas
  /-- Pointed comparisons propagate on the selected overlaps. -/
  selected_pointed_extension :
    let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
      { realBranchAtlasAt := chartedSelection.selection.realBranchAtlasAt
        restricted_domain_open := chartedSelection.selection.restricted_domain_open }
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      { preData := preData
        overlap_preconnected := by
          simpa [preData,
            SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected]
            using chartedSelection.selection.overlap_preconnected }

/--
A concrete locally charted selected surface predata object whose pointed
comparisons propagate on its selected overlaps.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected locally chart-compatible predata. -/
  locallyChartedSelection :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
      metricFormulaAtlas
  /-- Pointed comparisons propagate on the selected overlaps. -/
  selected_pointed_extension :
    let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
      { realBranchAtlasAt := locallyChartedSelection.selection.realBranchAtlasAt
        restricted_domain_open := locallyChartedSelection.selection.restricted_domain_open }
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      { preData := preData
        overlap_preconnected := by
          simpa [preData,
            SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected]
            using locallyChartedSelection.selection.overlap_preconnected }

/--
A concrete selected surface predata object whose overlaps are preconnected and
whose pointed comparisons propagate on those selected overlaps.

Unlike the charted and locally charted variants, this package does not require
the selected coordinate pullback maps to be ambient `chartAt` coordinates.  It
is the natural target for the coordinate-pullback pointed route, where pointed
Mobius comparisons are obtained from the closed derivative-frame construction
instead.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected real branch atlases, open restricted domains, and preconnected overlaps. -/
  selection :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      metricFormulaAtlas
  /-- Pointed comparisons propagate on the selected overlaps. -/
  selected_pointed_extension :
    let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
      { realBranchAtlasAt := selection.realBranchAtlasAt
        restricted_domain_open := selection.restricted_domain_open }
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      { preData := preData
        overlap_preconnected := by
          simpa [preData,
            SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected]
            using selection.overlap_preconnected }

/--
The precise canonical overlap-selection target for the charted-curvature
route: for each metric, choose one preconnected-overlap selector for the
chart-at curvature formula atlas.

This is weaker and more geometric than a global selector theorem over every
Liouville formula atlas; it is the target needed by the selected one-jet
route once the curvature atlas is fixed to ambient `chartAt` coordinates.
-/
def CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas))

/--
Canonical selected-overlap target with propagation already attached to the
selected predata.

This is the sharp local boundary for the coordinate-pullback pointed route:
choose one preconnected-overlap selector for the chart-at curvature atlas and
prove pointed transition propagation only on the overlaps of that chosen
selector.
-/
def CanonicalChartedCurvaturePreconnectedOverlapSelectionWithPropagationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas))

/--
Strong canonical surface-overlap preconnectedness for the chart-at curvature
atlas.

This specializes the older global preconnectedness hypothesis to the canonical
atlas.  It is still universal in the branch predata, so the sharper
shrink-and-select target below should be preferred when proving the actual
canonical overlap construction.
-/
def CanonicalChartedCurvatureSurfaceOverlapPreconnectedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedFor
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas)

/--
%%handwave
name: Domain of a selected surface branch chart
statement:
  Let a local metric formula at $x$ have surface domain $U_x$, coordinate $\phi_x$, and selected coordinate branch domain $V_x$. The associated surface upper-half-plane chart has domain $\{y\in U_x:\phi_x(y)\in V_x\}$.
proof:
  The surface formula is restricted by definition to the inverse image of the chosen coordinate branch domain.
-/
@[simp]
theorem surfaceRealUpperHalfPlaneBranchAtlasPreData_solutionAt_toHyperbolicLocalChart_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (x : X) :
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain =
      {y : X | y ∈ (metricFormulaAtlas.formulaAt x).domain ∧
        (metricFormulaAtlas.formulaAt x).coordinate y ∈
          ((preData.realBranchAtlasAt x).branchNear
            ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
              (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
                (metricFormulaAtlas.mem_formulaAt_domain x)⟩).domain} :=
  rfl

/--
%%handwave
name: Explicit overlap of two selected surface branch charts
statement:
  If selected charts at $x,y$ have formula domains $U_x,U_y$, coordinates $\phi_x,\phi_y$, and branch domains $V_x,V_y$, then their surface-domain overlap is
  $$\{z:z\in U_x,\ \phi_x(z)\in V_x,\ z\in U_y,\ \phi_y(z)\in V_y\}.$$
proof:
  Substitute the inverse-image description of each selected chart domain and rearrange the four membership conditions.
-/
theorem surfaceRealUpperHalfPlaneBranchAtlasPreData_solutionAt_toHyperbolicLocalChart_domain_inter
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (x y : X) :
    ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) =
      {z : X |
        z ∈ (metricFormulaAtlas.formulaAt x).domain ∧
        (metricFormulaAtlas.formulaAt x).coordinate z ∈
          ((preData.realBranchAtlasAt x).branchNear
            ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
              (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
                (metricFormulaAtlas.mem_formulaAt_domain x)⟩).domain ∧
        z ∈ (metricFormulaAtlas.formulaAt y).domain ∧
        (metricFormulaAtlas.formulaAt y).coordinate z ∈
          ((preData.realBranchAtlasAt y).branchNear
            ⟨(metricFormulaAtlas.formulaAt y).coordinate y,
              (metricFormulaAtlas.formulaAt y).coordinate_mem_conformalFactor_domain y
                (metricFormulaAtlas.mem_formulaAt_domain y)⟩).domain} := by
  rw [surfaceRealUpperHalfPlaneBranchAtlasPreData_solutionAt_toHyperbolicLocalChart_domain
    preData x,
    surfaceRealUpperHalfPlaneBranchAtlasPreData_solutionAt_toHyperbolicLocalChart_domain
      preData y]
  ext z
  simp [Set.mem_inter_iff, and_assoc, and_left_comm]

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/-- The surface predata object determined by a concrete selector package. -/
def toPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas where
  realBranchAtlasAt := S.realBranchAtlasAt
  restricted_domain_open := S.restricted_domain_open

/-- A concrete selector package gives the selected preconnected-overlap predata. -/
def toPreconnectedOverlapPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
      metricFormulaAtlas where
  preData := S.toPreData
  overlap_preconnected := by
    simpa [toPreData,
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected]
      using S.overlap_preconnected

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/-- Forget chart-compatibility from a charted selector. -/
def toPreconnectedOverlapSelection
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      metricFormulaAtlas :=
  S.selection

/-- The surface predata object determined by a charted selector. -/
def toPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
  S.selection.toPreData

/-- A charted selector gives selected preconnected-overlap predata. -/
def toPreconnectedOverlapPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
      metricFormulaAtlas :=
  S.selection.toPreconnectedOverlapPreData

/-- A charted selector gives the bundled charted predata package. -/
def toPreconnectedOverlapChartedPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedPreData
      metricFormulaAtlas where
  preconnectedPreData := S.toPreconnectedOverlapPreData
  coordinate_eqOn_chartAt := by
    simpa [toPreData, toPreconnectedOverlapPreData,
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection.toPreconnectedOverlapPreData]
      using S.coordinate_eqOn_chartAt

/-- A charted selector gives the weaker locally charted selector. -/
def toLocallyChartedSelection
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
      metricFormulaAtlas where
  selection := S.selection
  coordinate_eventuallyEqOn_chartAt := by
    exact
      surfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEventuallyEqOnChartAt_of_coordinateEqOnChartAt
        S.coordinate_eqOn_chartAt

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/-- Forget local chart-compatibility from a locally charted selector. -/
def toPreconnectedOverlapSelection
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      metricFormulaAtlas :=
  S.selection

/-- The surface predata object determined by a locally charted selector. -/
def toPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
  S.selection.toPreData

/-- A locally charted selector gives selected preconnected-overlap predata. -/
def toPreconnectedOverlapPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
      metricFormulaAtlas :=
  S.selection.toPreconnectedOverlapPreData

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/--
A charted selector together with the global pointed connected-overlap
propagation theorem gives a charted selector with propagation on its own
selected overlaps.
-/
def ofChartedSelectionAndGlobalPointedExtension
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
      metricFormulaAtlas where
  chartedSelection := S
  selected_pointed_extension := by
    simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection.toPreconnectedOverlapPreData]
      using
        (surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_global
          S.toPreconnectedOverlapPreData hExtend)

/--
A charted selector together with the global pointed one-jet connected-overlap
propagation theorem gives propagation on its own selected overlaps.
-/
def ofChartedSelectionAndGlobalPointedOneJetExtension
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
      metricFormulaAtlas where
  chartedSelection := S
  selected_pointed_extension := by
    simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection.toPreconnectedOverlapPreData]
      using
        (surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_global_oneJet
          S.toPreconnectedOverlapPreData hExtend)

/-- Forget selected propagation from a charted selector with propagation. -/
def toChartedSelection
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
      metricFormulaAtlas :=
  S.chartedSelection

/-- A charted selector with propagation gives selected preconnected-overlap predata. -/
def toPreconnectedOverlapPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
      metricFormulaAtlas :=
  S.chartedSelection.toPreconnectedOverlapPreData

/-- A charted selector with propagation gives the bundled charted predata package. -/
def toPreconnectedOverlapChartedPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedPreData
      metricFormulaAtlas :=
  S.chartedSelection.toPreconnectedOverlapChartedPreData

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/--
A locally charted selector together with the global pointed one-jet
connected-overlap propagation theorem gives propagation on its own selected
overlaps.
-/
def ofLocallyChartedSelectionAndGlobalPointedOneJetExtension
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation
      metricFormulaAtlas where
  locallyChartedSelection := S
  selected_pointed_extension := by
    simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection.toPreconnectedOverlapPreData]
      using
        (surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_global_oneJet
          S.toPreconnectedOverlapPreData hExtend)

/-- Forget selected propagation from a locally charted selector with propagation. -/
def toLocallyChartedSelection
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
      metricFormulaAtlas :=
  S.locallyChartedSelection

/-- A locally charted selector with propagation gives selected preconnected-overlap predata. -/
def toPreconnectedOverlapPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
      metricFormulaAtlas :=
  S.locallyChartedSelection.toPreconnectedOverlapPreData

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/-- Forget selected propagation from a selector with propagation. -/
def toPreconnectedOverlapSelection
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      metricFormulaAtlas :=
  S.selection

/-- A selector with propagation gives selected preconnected-overlap predata. -/
def toPreconnectedOverlapPreData
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
      metricFormulaAtlas :=
  S.selection.toPreconnectedOverlapPreData

/-- The selected pointed propagation, restated using the standard predata coercion. -/
def selectedPointedExtension
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      S.toPreconnectedOverlapPreData := by
  simpa [toPreconnectedOverlapPreData,
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection.toPreconnectedOverlapPreData]
    using S.selected_pointed_extension

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation

/--
Selected pointed-transition propagation for each canonical chart-at
curvature-overlap selector.

This separates the geometric shrinking/selection problem from the analytic
identity-principle problem: once a particular selected predata object has been
chosen, propagation is required only on its own selected preconnected overlaps.
-/
def CanonicalChartedCurvatureSelectedOverlapPointedTransitionExtendsTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (selection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas)),
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      selection.toPreconnectedOverlapPreData

/--
Selected pointed-transition propagation for the actual witnesses chosen by a
canonical chart-at curvature-overlap selection theorem.

This is the sharper boundary used by the canonical route: after the overlap
selection theorem has supplied its selected predata object, the analytic
propagation hypothesis is required only for that object.
-/
noncomputable def CanonicalChartedCurvatureChosenSelectedOverlapPointedTransitionExtendsTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X) :
    Prop :=
  ∀ (g : HyperbolicMetric X),
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
      ((Classical.choice (hSelection g)).toPreconnectedOverlapPreData)

/--
Selected one-jet pointed-transition propagation for the actual witnesses
chosen by a canonical chart-at curvature-overlap selection theorem.

This is sharper than the value-only chosen propagation boundary: on each
selected overlap it propagates both real-Mobius value agreement and the
oriented first-order frame match.
-/
noncomputable def CanonicalChartedCurvatureChosenSelectedOverlapPointedOneJetTransitionExtendsTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X) :
    Prop :=
  ∀ (g : HyperbolicMetric X),
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps
      ((Classical.choice (hSelection g)).toPreconnectedOverlapPreData)

/--
Canonical selected overlaps plus selected pointed propagation give the
canonical selector-with-propagation boundary.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionWithPropagationTheorem_of_selection_and_selectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hExtend :
      CanonicalChartedCurvatureSelectedOverlapPointedTransitionExtendsTheorem
        X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionWithPropagationTheorem
      X := by
  intro g
  rcases hSelection g with ⟨S⟩
  exact
    ⟨{ selection := S
       selected_pointed_extension := by
        simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection.toPreconnectedOverlapPreData]
          using hExtend g S }⟩

/--
Canonical selected overlaps plus pointed propagation for the chosen selected
predata give the canonical selector-with-propagation boundary.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionWithPropagationTheorem_of_selection_and_chosenSelectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hExtend :
      CanonicalChartedCurvatureChosenSelectedOverlapPointedTransitionExtendsTheorem
        hSelection) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionWithPropagationTheorem
      X := by
  intro g
  exact
    ⟨{ selection := Classical.choice (hSelection g)
       selected_pointed_extension := by
        simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection.toPreconnectedOverlapPreData]
          using hExtend g }⟩

/--
The broad selected-propagation theorem supplies propagation for the chosen
selected predata of any canonical selection theorem.
-/
noncomputable def canonicalChartedCurvatureChosenSelectedOverlapPointedTransitionExtendsTheorem_of_selectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hExtend :
      CanonicalChartedCurvatureSelectedOverlapPointedTransitionExtendsTheorem
        X) :
    CanonicalChartedCurvatureChosenSelectedOverlapPointedTransitionExtendsTheorem
      hSelection := by
  intro g
  exact hExtend g (Classical.choice (hSelection g))

/--
Chosen selected-overlap one-jet propagation forgets to the value-only chosen
propagation boundary.
-/
noncomputable def canonicalChartedCurvatureChosenSelectedOverlapPointedTransitionExtendsTheorem_of_chosenSelectedPointedOneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X}
    (hOneJet :
      CanonicalChartedCurvatureChosenSelectedOverlapPointedOneJetTransitionExtendsTheorem
        hSelection) :
    CanonicalChartedCurvatureChosenSelectedOverlapPointedTransitionExtendsTheorem
      hSelection := by
  intro g
  exact
    surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_oneJet
      (hOneJet g)

/--
The global pointed one-jet connected-overlap theorem supplies one-jet
propagation for the chosen selected predata of any canonical selection
theorem.
-/
noncomputable def canonicalChartedCurvatureChosenSelectedOverlapPointedOneJetTransitionExtendsTheorem_of_globalOneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hOneJet :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    CanonicalChartedCurvatureChosenSelectedOverlapPointedOneJetTransitionExtendsTheorem
      hSelection := by
  intro g
  exact
    surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps_of_global
      ((Classical.choice (hSelection g)).toPreconnectedOverlapPreData)
      hOneJet

/--
Global selector target for constructing one preconnected-overlap surface
predata object for each Liouville metric formula atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
        metricFormulaAtlas)

/--
Global selector target for constructing one preconnected-overlap,
chart-compatible surface predata object for each Liouville metric formula
atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas)

/--
Global selector target for constructing one preconnected-overlap, locally
chart-compatible surface predata object for each Liouville metric formula
atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
        metricFormulaAtlas)

/-- A charted selector theorem gives the weaker locally charted selector theorem. -/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem_of_chartedSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
      X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact ⟨S.toLocallyChartedSelection⟩

/--
The global preconnected-overlap selector theorem specializes to the canonical
chart-at curvature atlas needed by the selected one-jet route.
-/
def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_selectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem
        X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X := by
  intro g
  exact
    hSelection g
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas)

/--
The global surface-overlap preconnectedness theorem specializes to the
canonical chart-at curvature atlas.
-/
def canonicalChartedCurvatureSurfaceOverlapPreconnectedTheorem_of_surfaceOverlapPreconnectedTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOverlap :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X) :
    CanonicalChartedCurvatureSurfaceOverlapPreconnectedTheorem X := by
  intro g
  exact
    hOverlap g
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas)

/--
Global selector target for constructing one chart-compatible selected predata
object, with propagation on its own selected overlaps, for each Liouville
metric formula atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
        metricFormulaAtlas)

/--
Global selector target for constructing one locally chart-compatible selected
predata object, with propagation on its own selected overlaps, for each
Liouville metric formula atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation
        metricFormulaAtlas)

/--
Selected one-jet local uniqueness target for the actual charted surface
overlap data.

This is deliberately not a statement about arbitrary `HyperbolicLocalChart`s.
It says that each chart-compatible selected predata object has enough
one-jet identity-principle input on its own selected preconnected overlaps to
propagate any pointed value-and-frame comparison across the selected overlap.
The conclusion is the value equality needed by the surface branch-atlas
assembly; the intended proof route is the one-jet clopen argument on the
selected overlap component.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g},
    (selection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas) →
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps
        selection.toPreconnectedOverlapPreData

/--
Selected one-jet local uniqueness target for locally charted selected surface
overlap data.

This is the pointwise-coordinate version of
`SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem`:
the identity-principle argument only receives the selected overlaps and local
ambient-coordinate compatibility at points of those overlaps.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g},
    (selection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
        metricFormulaAtlas) →
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps
        selection.toPreconnectedOverlapPreData

/--
The local-coordinate selected one-jet uniqueness target implies the older
domainwise-charted target by forgetting a charted selector to a locally
charted selector.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_locallyCharted
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X := by
  intro g metricFormulaAtlas S
  simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection.toLocallyChartedSelection,
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection.toPreconnectedOverlapPreData]
    using hUnique S.toLocallyChartedSelection

/--
Global connected-overlap one-jet propagation gives the selected charted
one-jet uniqueness target for every selected predata object.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_oneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X := by
  intro g metricFormulaAtlas S
  exact
    surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps_of_global
      S.toPreconnectedOverlapPreData hExtend

/--
Global connected-overlap one-jet propagation gives the locally charted
selected one-jet uniqueness target.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_oneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X := by
  intro g metricFormulaAtlas S
  exact
    surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedOneJetTransitionExtendsOnOverlaps_of_global
      S.toPreconnectedOverlapPreData hExtend

/--
One-jet clopen propagation on arbitrary local-chart overlaps implies the
selected charted one-jet uniqueness target.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_oneJetEqualitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_oneJetExtension
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
      hClopen)

/--
The locally charted selected one-jet uniqueness target is likewise obtained
from one-jet clopen propagation on local-chart overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_oneJetEqualitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_oneJetExtension
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
      hClopen)

/--
Selected charted one-jet uniqueness can be driven by the actual analytic
boundary: value equality determines the oriented first-order frame, and the
corrected one-jet locus is open.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_valueEqualityForcesFirstOrder_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_oneJetExtension
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_valueEqualityForcesFirstOrder_and_oneJetEqualitySetOpen
      hValueFirst hOpen)

/--
The locally charted selected one-jet uniqueness target has the same reduced
analytic boundary.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_valueEqualityForcesFirstOrder_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_oneJetExtension
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_valueEqualityForcesFirstOrder_and_oneJetEqualitySetOpen
      hValueFirst hOpen)

/--
Selected charted one-jet uniqueness from first-order-frame closedness and
one-jet openness.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirstClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_oneJetExtension
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
      hFirstClosed hOpen)

/--
The locally charted selected one-jet uniqueness target has the same
first-order-closed plus one-jet-open boundary.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirstClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_oneJetExtension
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
      hFirstClosed hOpen)

/--
Selected charted one-jet uniqueness from the concrete derivative-closed
first-order locus, the Poincare pullback formula, and one-jet openness.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed
      hPull hConcrete)
    hOpen

/--
Locally charted selected one-jet uniqueness from the same concrete
derivative-closed boundary.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_firstOrderClosed_and_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed
      hPull hConcrete)
    hOpen

/--
Selected charted one-jet uniqueness from derivative continuity of the concrete
first-order comparison, the Poincare pullback formula, and one-jet openness.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hPull
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
      hDeriv)
    hOpen

/--
Locally charted selected one-jet uniqueness from the same concrete derivative
continuity boundary.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hPull
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
      hDeriv)
    hOpen

/--
Selected charted one-jet uniqueness from continuity of the coordinate
derivative on each hyperbolic local chart.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    hPull
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem_of_chartDerivativeContinuity
      hyperbolicLocalChartContinuousOnDomainTheorem hDeriv)
    hOpen

/--
Selected charted one-jet uniqueness from chart-derivative continuity and
one-jet openness, with the Poincare pullback formula discharged.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hDeriv hOpen

/--
The same chart-derivative continuity bridge at the locally charted selected
overlap boundary.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    hPull
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem_of_chartDerivativeContinuity
      hyperbolicLocalChartContinuousOnDomainTheorem hDeriv)
    hOpen

/--
Locally charted selected one-jet uniqueness from chart-derivative continuity
and one-jet openness, with the Poincare pullback formula discharged.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_pullbackSquaredDensityFormula_chartDerivativeContinuity_and_oneJetEqualitySetOpen
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hDeriv hOpen

/--
Selected charted one-jet uniqueness from concrete derivative-closed
first-order loci and one-jet openness, with the Poincare pullback formula
discharged.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hConcrete hOpen

/--
Locally charted selected one-jet uniqueness from the same concrete closedness
boundary, with the Poincare pullback formula discharged.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hConcrete hOpen

/--
Selected charted one-jet uniqueness from continuity of the concrete
coordinate-derivative comparison maps, with closedness and the pullback
formula discharged.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
      hDeriv)
    hOpen

/--
Locally charted selected one-jet uniqueness from concrete derivative
continuity, with closedness and the pullback formula discharged.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
      hDeriv)
    hOpen

/--
Selected charted one-jet uniqueness from concrete first-order closedness and
actual holomorphic local-isometry first-order stability.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_concreteFirstOrderClosed_and_holomorphicLocalIsometryFirstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hConcrete
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryFirstOrderStability
      hFirst)

/--
Locally charted selected one-jet uniqueness from concrete first-order
closedness and actual holomorphic local-isometry first-order stability.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_concreteFirstOrderClosed_and_holomorphicLocalIsometryFirstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_concreteFirstOrderClosed_and_oneJetEqualitySetOpen
    hConcrete
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryFirstOrderStability
      hFirst)

/--
Selected charted one-jet uniqueness from concrete derivative continuity and
actual holomorphic local-isometry first-order stability.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_concreteFirstOrderDerivativeContinuity_and_holomorphicLocalIsometryFirstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    hDeriv
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryFirstOrderStability
      hFirst)

/--
Locally charted selected one-jet uniqueness from concrete derivative
continuity and actual holomorphic local-isometry first-order stability.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_concreteFirstOrderDerivativeContinuity_and_holomorphicLocalIsometryFirstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_concreteFirstOrderDerivativeContinuity_and_oneJetEqualitySetOpen
    hDeriv
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryFirstOrderStability
      hFirst)

/--
A charted selector with propagation gives the ordinary charted selector
theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem_of_withPropagation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact ⟨S.toChartedSelection⟩

/--
A charted selector theorem plus the global pointed connected-overlap
propagation theorem gives the selected charted selector-with-propagation
theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem_of_chartedSelection_and_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem
      X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact
    ⟨SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation.ofChartedSelectionAndGlobalPointedExtension
      S hExtend⟩

/--
A charted selector theorem plus selected one-jet local uniqueness gives the
selected charted selector-with-propagation theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem_of_chartedSelection_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem
      X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact
    ⟨{ chartedSelection := S
       selected_pointed_extension := by
        exact
          surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_oneJet
            (by
              simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection.toPreconnectedOverlapPreData]
                using hUnique S) }⟩

/--
A charted selector theorem plus global one-jet connected-overlap propagation
gives the selected charted selector-with-propagation theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem_of_chartedSelection_and_pointedOneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem_of_chartedSelection_and_selectedOneJetLocalUniqueness
    hSelection
    (surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_oneJetExtension
      hExtend)

/--
A locally charted selector theorem plus selected one-jet local uniqueness gives
the locally charted selector-with-propagation theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagationTheorem_of_locallyChartedSelection_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
        X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagationTheorem
      X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact
    ⟨{ locallyChartedSelection := S
       selected_pointed_extension := by
        exact
          surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_oneJet
            (by
              simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection.toPreconnectedOverlapPreData]
                using hUnique S) }⟩

/--
A locally charted selector theorem plus global one-jet connected-overlap
propagation gives the locally charted selector-with-propagation theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagationTheorem_of_locallyChartedSelection_and_pointedOneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagationTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagationTheorem_of_locallyChartedSelection_and_selectedOneJetLocalUniqueness
    hSelection
    (surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_oneJetExtension
      hExtend)

/--
A charted selector theorem gives the ordinary preconnected-overlap selector
theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_chartedSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact ⟨S.toPreconnectedOverlapSelection⟩

/--
A global charted selector theorem also specializes to the canonical chart-at
curvature overlap-selection target.
-/
def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_chartedSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_selectionTheorem
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_chartedSelection
      hSelection)

/--
For one Liouville metric formula atlas, a preconnected-overlap selector becomes
chart-compatible when every coordinate pullback formula agrees with the
ambient `chartAt` on its domain.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection_of_selection_and_coordinateEqOnChartAt_for
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
        metricFormulaAtlas)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
      metricFormulaAtlas where
  selection := S
  coordinate_eqOn_chartAt := by
    intro x x₀ hx₀
    let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
      S.toPreData
    exact
      hChart g
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula)
        x₀ hx₀

/--
Global bridge from ordinary preconnected-overlap selection to charted
selection, using the global coordinate-pullback chart-compatibility theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem_of_selection_and_coordinateEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
      X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection_of_selection_and_coordinateEqOnChartAt_for
      S hChart⟩

/--
For one Liouville metric formula atlas, a preconnected-overlap selector
becomes locally chart-compatible when every coordinate pullback formula is
locally the ambient coordinate near each point of its domain.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection_of_selection_and_coordinateEventuallyEqOnChartAt_for
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
        metricFormulaAtlas)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
      metricFormulaAtlas where
  selection := S
  coordinate_eventuallyEqOn_chartAt := by
    intro x x₀ hx₀
    let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
      S.toPreData
    exact
      hChart g
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula)
        x₀ hx₀

/--
Global bridge from ordinary preconnected-overlap selection to locally charted
selection, using the local coordinate-pullback compatibility theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem_of_selection_and_coordinateEventuallyEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
      X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection_of_selection_and_coordinateEventuallyEqOnChartAt_for
      S hChart⟩

/--
The concrete selector theorem constructs the preconnected-overlap surface
predata required by the downstream atlas assembly.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem_of_selection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact ⟨S.toPreconnectedOverlapPreData⟩

/--
For one chosen Liouville metric formula atlas, local real branch existence,
restricted-domain openness, and preconnectedness of selected overlaps build
the concrete selector package.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection_of_localRealBranches_openness_overlapPreconnected_for
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hLocal :
      ∀ x : X,
        Nonempty
          (LocalRealUpperHalfPlaneBranchAtlas
            (metricFormulaAtlas.formulaAt x).conformalFactor))
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
        metricFormulaAtlas)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedFor
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      metricFormulaAtlas :=
  let realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor :=
    fun x ↦ Classical.choice (hLocal x)
  { realBranchAtlasAt := realBranchAtlasAt
    restricted_domain_open := hOpen realBranchAtlasAt
    overlap_preconnected := by
      simpa [SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected]
        using
          hOverlapPreconnected
            { realBranchAtlasAt := realBranchAtlasAt
              restricted_domain_open := hOpen realBranchAtlasAt } }

/--
Local real branch existence, restricted-domain openness, and the broad
preconnected-overlap theorem build the concrete selector theorem.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X := by
  intro g metricFormulaAtlas
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection_of_localRealBranches_openness_overlapPreconnected_for
      (fun x ↦
        hLocal (metricFormulaAtlas.formulaAt x).conformalFactor
          (metricFormulaAtlas.formulaAt x).solves_liouville)
      (hOpen g metricFormulaAtlas)
      (hOverlapPreconnected g metricFormulaAtlas)⟩

/--
Global theorem target for solving any Liouville formula atlas by Schwarzian
branches.
-/
def LocalSolvingFromSchwarzianBranchDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty (LocalSolvingFromSchwarzianBranchData g metricFormulaAtlas)

/--
Global theorem target for solving any Liouville formula atlas by pointed
Schwarzian branches.
-/
def LocalSolvingFromPointedSchwarzianBranchDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty (LocalSolvingFromPointedSchwarzianBranchData g metricFormulaAtlas)

/--
Global theorem target for producing local developing-solution atlases from any
Liouville formula atlas.
-/
def LocalDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (_metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty (LocalLiouvilleDevelopingSolutionAtlas X g)

/-- Raw surface branch data is exactly the data needed for Schwarzian local solving. -/
def localSolvingFromSchwarzianBranchDataTheorem_of_surfaceSchwarzianBranchDataTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : SurfaceSchwarzianBranchDataTheorem X) :
    LocalSolvingFromSchwarzianBranchDataTheorem X :=
  fun g metricFormulaAtlas ↦
    let B := Classical.choice (h g metricFormulaAtlas)
    ⟨{ branchData := B }⟩

/-- Pointed branch data is enough for local solving after shrinking domains. -/
def localSolvingFromPointedSchwarzianBranchDataTheorem_of_surfaceSchwarzianPointedBranchDataTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : SurfaceSchwarzianPointedBranchDataTheorem X) :
    LocalSolvingFromPointedSchwarzianBranchDataTheorem X :=
  fun g metricFormulaAtlas ↦
    let B := Classical.choice (h g metricFormulaAtlas)
    ⟨{ branchData := B }⟩

/-- Surface real branch-atlas data forgets to pointed Schwarzian branch data. -/
def surfaceSchwarzianPointedBranchDataTheorem_of_surfaceRealUpperHalfPlaneBranchAtlasDataTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X) :
    SurfaceSchwarzianPointedBranchDataTheorem X :=
  fun g metricFormulaAtlas ↦
    let B := Classical.choice (h g metricFormulaAtlas)
    ⟨B.toSurfaceSchwarzianPointedBranchData⟩

/--
Coordinate real branch existence plus surface assembly gives the surface
real-branch data theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_and_surfaceAssembly
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal : HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hAssembly : SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  fun g metricFormulaAtlas ↦
    hAssembly g metricFormulaAtlas
      (fun x ↦ hLocal (metricFormulaAtlas.formulaAt x).conformalFactor
        (metricFormulaAtlas.formulaAt x).solves_liouville)

/--
Coordinate-preimage openness implies openness of the branch-domain restrictions
selected from coordinate real branch atlases.
-/
def surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem_of_coordinatePreimageOpenness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreimage : LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X := by
  intro g metricFormulaAtlas realBranchAtlasAt x
  let p : (metricFormulaAtlas.formulaAt x).conformalFactor.coordinateDomain :=
    ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
      (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
        (metricFormulaAtlas.mem_formulaAt_domain x)⟩
  let H := (realBranchAtlasAt x).branchNear p
  have hOpenH : IsOpen H.domain := by
    simpa [LocalUpperHalfPlaneDevelopingMap.domain] using H.projective.isOpen_domain
  exact hPreimage g metricFormulaAtlas x H.domain hOpenH

/--
Pointwise chart-compatibility supplies surface-domain openness for one chosen
Liouville metric formula atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor metricFormulaAtlas := by
  intro realBranchAtlasAt x
  let p : (metricFormulaAtlas.formulaAt x).conformalFactor.coordinateDomain :=
    ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
      (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
        (metricFormulaAtlas.mem_formulaAt_domain x)⟩
  let H := (realBranchAtlasAt x).branchNear p
  have hOpenH : IsOpen H.domain := by
    simpa [LocalUpperHalfPlaneDevelopingMap.domain] using H.projective.isOpen_domain
  rcases hChart x with ⟨hSub, hEq⟩
  exact
    isOpen_formulaCoordinate_preimage_of_eqOn_chartAt
      (metricFormulaAtlas.formulaAt x).isOpen_domain hSub hEq hOpenH

/--
The canonical chart-at curvature atlas, rewritten as a Liouville atlas, has
coordinates given by the ambient `chartAt` maps on their domains.
-/
def canonicalChartedCurvatureCoordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas) := by
  intro x
  exact ⟨fun _ hy ↦ hy, fun _ _ ↦ rfl⟩

/--
For one chosen Liouville metric formula atlas, local real branches and
surface-domain openness build the raw branch predata, with no overlap
connectedness condition.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreData_of_localRealBranches_openness_for
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hLocal :
      ∀ x : X,
        Nonempty
          (LocalRealUpperHalfPlaneBranchAtlas
            (metricFormulaAtlas.formulaAt x).conformalFactor))
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
  let realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor :=
    fun x ↦ Classical.choice (hLocal x)
  { realBranchAtlasAt := realBranchAtlasAt
    restricted_domain_open := hOpen realBranchAtlasAt }

/--
For the canonical chart-at curvature atlas, local real Liouville branches
alone select the raw branch predata.  The surface-domain openness is supplied
by the fact that the formula coordinates are the ambient charts on their
domains.
-/
noncomputable def canonicalChartedCurvatureBranchPreDataSelectionTheorem_of_localRealBranches
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem) :
    CanonicalChartedCurvatureBranchPreDataSelectionTheorem X := by
  intro g
  let metricFormulaAtlas :=
    ((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas)
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasPreData_of_localRealBranches_openness_for
      (metricFormulaAtlas := metricFormulaAtlas)
      (fun x ↦
        hLocal (metricFormulaAtlas.formulaAt x).conformalFactor
          (metricFormulaAtlas.formulaAt x).solves_liouville)
      (surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
        (canonicalChartedCurvatureCoordinateChartedOnDomain g))⟩

/--
One selected family of coordinate real branches for the canonical chart-at
curvature atlas, with preconnected overlaps for the induced surface domains.

This is the genuinely selected topological target: it asks for one good
branch choice per metric, rather than requiring every possible branch predata
over the canonical atlas to have preconnected overlaps.
-/
structure CanonicalChartedCurvaturePreconnectedOverlapBranchSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) where
  /-- The selected coordinate real branch atlases. -/
  realBranchAtlasAt :
    ∀ x : X,
      LocalRealUpperHalfPlaneBranchAtlas
        (((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor
  /-- The selected induced surface overlaps are preconnected whenever nonempty. -/
  overlap_preconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas)
      realBranchAtlasAt
      ((surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
        (canonicalChartedCurvatureCoordinateChartedOnDomain g)) realBranchAtlasAt)

/--
Global selected branch/topology target for the canonical chart-at curvature
atlas.
-/
def CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty (CanonicalChartedCurvaturePreconnectedOverlapBranchSelection g)

/--
Selected canonical branch/topology data built by explicitly shrinking local
coordinate real-branch atlases.

This is the constructive shape of the remaining charted-overlap selection
problem: first choose the analytic local real branches, then choose smaller
branch domains whose induced surface overlaps are preconnected.
-/
structure CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) where
  /-- The original coordinate real branch atlases before shrinking. -/
  realBranchAtlasAt :
    ∀ x : X,
      LocalRealUpperHalfPlaneBranchAtlas
        (((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor
  /-- The explicit shrink of each coordinate real branch atlas. -/
  shrinkDataAt :
    ∀ x : X, (realBranchAtlasAt x).toBranchAtlas.ShrinkData
  /--
  The shrunk selected surface overlaps are preconnected whenever nonempty.
  -/
  overlap_preconnected :
    let metricFormulaAtlas :=
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas)
    let shrunkRealBranchAtlasAt :
        ∀ x : X,
          LocalRealUpperHalfPlaneBranchAtlas
            (metricFormulaAtlas.formulaAt x).conformalFactor :=
      fun x ↦ (realBranchAtlasAt x).shrink (shrinkDataAt x)
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected
      metricFormulaAtlas
      shrunkRealBranchAtlasAt
      ((surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
        (canonicalChartedCurvatureCoordinateChartedOnDomain g))
          shrunkRealBranchAtlasAt)

/--
Pure shrink data for one already chosen canonical coordinate real-branch
family.

This separates the topological shrinking problem from the analytic local
branch-existence theorem.
-/
structure CanonicalChartedCurvatureBranchShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor) where
  /-- The explicit shrink of each coordinate real branch atlas. -/
  shrinkDataAt :
    ∀ x : X, (realBranchAtlasAt x).toBranchAtlas.ShrinkData
  /--
  The shrunk selected surface overlaps are preconnected whenever nonempty.
  -/
  overlap_preconnected :
    let metricFormulaAtlas :=
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas)
    let shrunkRealBranchAtlasAt :
        ∀ x : X,
          LocalRealUpperHalfPlaneBranchAtlas
            (metricFormulaAtlas.formulaAt x).conformalFactor :=
      fun x ↦ (realBranchAtlasAt x).shrink (shrinkDataAt x)
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected
      metricFormulaAtlas
      shrunkRealBranchAtlasAt
    ((surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
        (canonicalChartedCurvatureCoordinateChartedOnDomain g))
          shrunkRealBranchAtlasAt)

/--
Ball-shaped shrink data for one already chosen canonical coordinate real-branch
family.

This is the sharper geometric boundary for charted overlap selection: each
coordinate branch is shrunk to a ball around its base coordinate, so
coordinate-side branch overlaps are automatically preconnected.  The remaining
field is exactly the surface-overlap preconnectedness needed by the selected
overlap route.
-/
structure CanonicalChartedCurvatureBranchBallShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor) where
  /-- The explicit ball shrink of each coordinate real branch atlas. -/
  ballShrinkDataAt :
    ∀ x : X, (realBranchAtlasAt x).toBranchAtlas.BallShrinkData
  /--
  The ball-shrunk selected surface overlaps are preconnected whenever nonempty.
  -/
  overlap_preconnected :
    let metricFormulaAtlas :=
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas)
    let shrunkRealBranchAtlasAt :
        ∀ x : X,
          LocalRealUpperHalfPlaneBranchAtlas
            (metricFormulaAtlas.formulaAt x).conformalFactor :=
      fun x ↦ (realBranchAtlasAt x).shrink ((ballShrinkDataAt x).toShrinkData)
    SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected
      metricFormulaAtlas
      shrunkRealBranchAtlasAt
      ((surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
        (canonicalChartedCurvatureCoordinateChartedOnDomain g))
          shrunkRealBranchAtlasAt)

end HyperbolicMetric

end

end JJMath
