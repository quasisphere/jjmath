import JJMath.Hyperbolic.Converse.Setup.OverlapStability.LocalExtension

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
Closedness of the concrete value-plus-coordinate-derivative locus gives
closedness of the abstract first-order-frame locus.  The Poincare pullback
squared-density formula has already been proved for hyperbolic local charts.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_concreteFirstOrderClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hConcrete

/--
Continuity of the concrete derivative-comparison maps gives first-order
closedness, with the Poincare pullback formula discharged.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_concreteFirstOrderDerivativeContinuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_concreteFirstOrderClosed
    (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
      hDeriv)

/--
Local persistence target for the first-order frame-match part of a pointed
comparison.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        ∀ y, y ∈ U.domain → y ∈ V.domain →
          HyperbolicLocalChartPointedFirstOrderMatch U V A y →
            ∃ W : Set X,
              IsOpen W ∧ y ∈ W ∧
                ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
                  HyperbolicLocalChartPointedFirstOrderMatch U V A z

/--
Local persistence target for one-jet equality of hyperbolic local charts.

If the real-Mobius comparison has the same value and oriented first-order
frame at a point of the overlap, then that one-jet equality persists on a
small neighborhood in the overlap.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        ∀ y, y ∈ U.domain → y ∈ V.domain →
          V.toUpperHalfPlane y =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane y) →
          HyperbolicLocalChartPointedFirstOrderMatch U V A y →
            ∃ W : Set X,
              IsOpen W ∧ y ∈ W ∧
                ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
                  V.toUpperHalfPlane z =
                      realMobiusRepresentativeAction A (U.toUpperHalfPlane z) ∧
                    HyperbolicLocalChartPointedFirstOrderMatch U V A z

/--
Auxiliary target saying that, for a pointed comparison, any further value
coincidence in the overlap automatically has the same oriented first-order
frame.

This is separated from one-jet local persistence because value equality alone
is not the intrinsic local uniqueness datum for hyperbolic local isometries.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        ∀ y, y ∈ U.domain → y ∈ V.domain →
          V.toUpperHalfPlane y =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane y) →
            HyperbolicLocalChartPointedFirstOrderMatch U V A y

/--
Bundled analytic consequences of the holomorphic local-isometry fields in
`HyperbolicLocalChart`.

This is the remaining local analytic input in its most compact form: local
isometries supply normalized derivative data, continuity on chart domains, and
local persistence of pointed real-Mobius equality.
-/
structure HyperbolicLocalChartAnalyticLocalIsometryConsequences
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  /-- Local isometries give the normalized coordinate derivative data at each point. -/
  coordinateDerivativeData :
    HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X
  /-- Local isometries are continuous on their chart domains. -/
  chartContinuous :
    HyperbolicLocalChartContinuousOnDomainTheorem X
  /-- A pointed real-Mobius equality persists locally on the overlap. -/
  localPersistence :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X

/--
Bundled analytic local-isometry consequences in the corrected one-jet form.

The main local uniqueness field is the value-plus-oriented-frame persistence
statement.  The final field is the extra condition needed to recover the older
value-only local-persistence interface when downstream code still asks for it.
-/
structure HyperbolicLocalChartAnalyticOneJetLocalIsometryConsequences
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  /-- Local isometries give the normalized coordinate derivative data at each point. -/
  coordinateDerivativeData :
    HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X
  /-- Local isometries are continuous on their chart domains. -/
  chartContinuous :
    HyperbolicLocalChartContinuousOnDomainTheorem X
  /-- A pointed value-and-frame comparison persists locally on the overlap. -/
  oneJetLocalPersistence :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem X
  /-- Value equality for a pointed comparison determines the oriented first-order match. -/
  valueEqualityForcesFirstOrder :
    PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
      X

/-- Prop-level target for the bundled local-isometry consequences. -/
def HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (HyperbolicLocalChartAnalyticLocalIsometryConsequences X)

/-- Prop-level target for the corrected one-jet local-isometry consequences. -/
def HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (HyperbolicLocalChartAnalyticOneJetLocalIsometryConsequences X)

/--
Assemble the bundled local-isometry consequences from the separated concrete
analytic ingredients.  This isolates the pullback squared-density formula as a
named input rather than burying it inside the pointed-frame package.
-/
def hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X) :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X :=
  ⟨{ coordinateDerivativeData :=
      hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
        hDeriv hPull
     chartContinuous := hChart
     localPersistence := hLocal }⟩

/--
Assemble the bundled local-isometry consequences from the Poincare pullback
squared-density formula alone, together with chart continuity and local
persistence.  Derivative nonvanishing follows from positivity of the source
conformal density.
-/
def hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_proved
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X) :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula
    (hyperbolicLocalChartCoordinateDerivativeNonzeroTheorem_of_pullbackSquaredDensityFormula
      hPull)
    hPull hChart hLocal

/--
Local persistence of pointed real-Mobius equality makes the local-chart
equality locus open.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem_of_localPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X := by
  intro g U V A x₀ hpoint
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A
  rw [isOpen_iff_forall_mem_open]
  intro y hyE
  rcases hLocal g U V A x₀ hpoint (y : X) y.property.1 y.property.2
      (by
        simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet]
          using hyE) with
    ⟨W, hWopen, hyW, hWeq⟩
  refine ⟨Subtype.val ⁻¹' W, ?_, hWopen.preimage continuous_subtype_val, hyW⟩
  intro z hzW
  exact hWeq (z : X) hzW z.property.1 z.property.2

/--
One-jet local persistence makes the one-jet equality locus open.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_oneJetLocalPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X := by
  intro g U V A x₀ hpoint
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet U V A
  rw [isOpen_iff_forall_mem_open]
  intro y hyE
  rcases hLocal g U V A x₀ hpoint (y : X) y.property.1 y.property.2
      (by
        simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet]
          using hyE.1)
      (by
        simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet]
          using hyE.2) with
    ⟨W, hWopen, hyW, hWeq⟩
  refine ⟨Subtype.val ⁻¹' W, ?_, hWopen.preimage continuous_subtype_val, hyW⟩
  intro z hzW
  exact hWeq (z : X) hzW z.property.1 z.property.2

/--
Openness of the first-order frame-match locus gives openness of the one-jet
locus, since first-order frame matching already includes the value equation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_firstOrderOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X := by
  intro g U V A x₀ hpoint
  rw [pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet_eq_firstOrderMatchSet]
  exact hOpen g U V A x₀ hpoint

/--
Local persistence of first-order frame matching gives one-jet local
persistence: the persisted frame relation supplies the persisted value
relation as well.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_firstOrderLocalPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem
      X := by
  intro g U V A x₀ hpoint y hyU hyV _hyEq hyFirst
  rcases hLocal g U V A x₀ hpoint y hyU hyV hyFirst with
    ⟨W, hWopen, hyW, hW⟩
  refine ⟨W, hWopen, hyW, ?_⟩
  intro z hzW hzU hzV
  have hzFirst := hW z hzW hzU hzV
  exact ⟨hzFirst.value_eq, hzFirst⟩

/--
Openness of the value equality locus and openness of the first-order match
locus imply openness of the one-jet equality locus.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueOpen_firstOrderOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
        X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X := by
  intro g U V A x₀ hpoint
  have hValueOpen :
      IsOpen (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A) :=
    hValue g U V A x₀ hpoint
  have hFirstOpen :
      IsOpen (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet U V A) :=
    hFirst g U V A x₀ hpoint
  simpa [pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet,
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet,
    pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet,
    Set.setOf_and] using hValueOpen.inter hFirstOpen

/--
Value local persistence and first-order-match openness imply openness of the
one-jet equality locus.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueLocalPersistence_firstOrderOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueOpen_firstOrderOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem_of_localPersistence
      hValueLocal)
    hFirst

/--
First-order local persistence makes the first-order match locus open.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem_of_firstOrderLocalPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem
      X := by
  intro g U V A x₀ hpoint
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet U V A
  rw [isOpen_iff_forall_mem_open]
  intro y hyE
  rcases hLocal g U V A x₀ hpoint (y : X) y.property.1 y.property.2
      (by
        simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet]
          using hyE) with
    ⟨W, hWopen, hyW, hWeq⟩
  refine ⟨Subtype.val ⁻¹' W, ?_, hWopen.preimage continuous_subtype_val, hyW⟩
  intro z hzW
  exact hWeq (z : X) hzW z.property.1 z.property.2

/--
Openness of the first-order match locus gives first-order local persistence.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem_of_firstOrderMatchSetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
      X := by
  intro g U V A x₀ hpoint y hyU hyV hyFirst
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet U V A
  have hyOverlap : y ∈ overlap := ⟨hyU, hyV⟩
  have hyE : (⟨y, hyOverlap⟩ : overlap) ∈ E := by
    simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet]
      using hyFirst
  have hEopen : IsOpen E := hOpen g U V A x₀ hpoint
  rw [isOpen_iff_forall_mem_open] at hEopen
  rcases hEopen (⟨y, hyOverlap⟩ : overlap) hyE with
    ⟨O, hOsub, hOopen, hyO⟩
  rcases isOpen_induced_iff.mp hOopen with ⟨W, hWopen, hWpre⟩
  refine ⟨W, hWopen, ?_, ?_⟩
  · have hyW : (⟨y, hyOverlap⟩ : overlap) ∈ Subtype.val ⁻¹' W := by
      rw [hWpre]
      exact hyO
    exact hyW
  · intro z hzW hzU hzV
    have hzOverlap : z ∈ overlap := ⟨hzU, hzV⟩
    have hzO : (⟨z, hzOverlap⟩ : overlap) ∈ O := by
      have hzPre : (⟨z, hzOverlap⟩ : overlap) ∈ Subtype.val ⁻¹' W := hzW
      rwa [hWpre] at hzPre
    have hzE : (⟨z, hzOverlap⟩ : overlap) ∈ E := hOsub hzO
    simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet]
      using hzE

/--
First-order local persistence and first-order match-locus openness are
interchangeable theorem targets.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem_iff_firstOrderMatchSetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
        X ↔
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem
        X :=
  ⟨pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem_of_firstOrderLocalPersistence,
    pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem_of_firstOrderMatchSetOpen⟩

/--
Value and first-order local persistence together make the one-jet equality
locus open.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueLocalPersistence_firstOrderLocalPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValueLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X)
    (hFirstLocal :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueLocalPersistence_firstOrderOpen
    hValueLocal
    (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem_of_firstOrderLocalPersistence
      hFirstLocal)

/--
Cross-chart open-locus inputs for the pointed comparison of two holomorphic
hyperbolic local charts: the value equality locus is open and the oriented
first-order-frame match locus is open.
-/
structure HyperbolicLocalChartCrossChartOneJetOpenLociTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  valueOpen :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X
  firstOrderOpen :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem
      X

/--
The general cross-chart proof that the one-jet equality locus is open: it is
the intersection of the open value-equality locus and the open
first-order-frame match locus.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_crossChartOpenLoci
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartCrossChartOneJetOpenLociTheorems X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueOpen_firstOrderOpen
    h.valueOpen h.firstOrderOpen

/--
Cross-chart local-persistence inputs for pointed comparisons.  These are often
the analytic form one proves: value agreement and oriented first-order-frame
agreement each persist locally on the overlap.
-/
structure HyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  valueLocalPersistence :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X
  firstOrderLocalPersistence :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
      X

/--
Global target saying that the analytic propositions stored in each
`HyperbolicLocalChart` actually hold.

The chart record stores these fields as propositions rather than proofs, so
this is the precise boundary needed before one can use the analytic
local-isometry hypotheses in downstream arguments.
-/
def HyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g),
    U.holomorphic_on_domain ∧ U.local_biholomorph_on_domain ∧
      U.pulls_back_metric_on_domain

/--
%%handwave
name: Analytic local-isometry properties of a hyperbolic chart
statement:
  Every hyperbolic local chart is holomorphic on its domain, has nonvanishing complex derivative there, and pulls the given conformal metric back from the Poincare metric.
proof:
  These three properties are precisely the holomorphicity, local-biholomorphism, and metric-pullback data carried by the local-isometry package of the chart.
-/
theorem hyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    HyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem X := by
  intro g U
  exact
    ⟨U.local_isometry.holomorphic_on_domain,
      U.local_isometry.local_biholomorph_on_domain,
      U.local_isometry.pulls_back_metric_on_domain⟩

/--
Holomorphicity-field target for the selected upper-half-plane branches in a
pointed surface branch predata object.
-/
def SurfaceSchwarzianPointedBranchPreDataSelectedBranchesHolomorphicTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (B : SurfaceSchwarzianPointedBranchPreData metricFormulaAtlas)
    (x : X),
      LocalUpperHalfPlaneMapHolomorphicOn
        (B.branchAt x).domain (B.branchAt x).upperHalfPlaneMap

/--
Local stability of value agreement from the actual holomorphic local-isometry
fields stored in two `HyperbolicLocalChart`s.

The chart record currently stores holomorphicity, local biholomorphism, and
metric pullback as abstract propositions.  This target is the exact analytic
theorem that should be proved from those fields for the value component of a
pointed comparison.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      U.holomorphic_on_domain →
      U.local_biholomorph_on_domain →
      U.pulls_back_metric_on_domain →
      V.holomorphic_on_domain →
      V.local_biholomorph_on_domain →
      V.pulls_back_metric_on_domain →
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        ∀ y, y ∈ U.domain → y ∈ V.domain →
          V.toUpperHalfPlane y =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane y) →
            ∃ W : Set X,
              IsOpen W ∧ y ∈ W ∧
                ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
                  V.toUpperHalfPlane z =
                    realMobiusRepresentativeAction A (U.toUpperHalfPlane z)

/--
Local stability of the oriented first-order-frame match from the actual
holomorphic local-isometry fields stored in two `HyperbolicLocalChart`s.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      U.holomorphic_on_domain →
      U.local_biholomorph_on_domain →
      U.pulls_back_metric_on_domain →
      V.holomorphic_on_domain →
      V.local_biholomorph_on_domain →
      V.pulls_back_metric_on_domain →
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        ∀ y, y ∈ U.domain → y ∈ V.domain →
          HyperbolicLocalChartPointedFirstOrderMatch U V A y →
            ∃ W : Set X,
              IsOpen W ∧ y ∈ W ∧
                ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
                  HyperbolicLocalChartPointedFirstOrderMatch U V A z

/--
Direct one-jet local stability from the actual holomorphic local-isometry
hypotheses.

This is the intrinsic local uniqueness target: value agreement alone is not
stable for hyperbolic local isometries because the target stabilizer of a
point can rotate tangent directions.  Value plus the oriented first-order
frame is the correct local datum.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      U.holomorphic_on_domain →
      U.local_biholomorph_on_domain →
      U.pulls_back_metric_on_domain →
      V.holomorphic_on_domain →
      V.local_biholomorph_on_domain →
      V.pulls_back_metric_on_domain →
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        ∀ y, y ∈ U.domain → y ∈ V.domain →
          V.toUpperHalfPlane y =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane y) →
          HyperbolicLocalChartPointedFirstOrderMatch U V A y →
            ∃ W : Set X,
              IsOpen W ∧ y ∈ W ∧
                ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
                  V.toUpperHalfPlane z =
                      realMobiusRepresentativeAction A (U.toUpperHalfPlane z) ∧
                    HyperbolicLocalChartPointedFirstOrderMatch U V A z

/--
The two component-stability theorems obtained from the actual holomorphic
local-isometry hypotheses.
-/
structure HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  fieldsHold :
    HyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem X
  valueStability :
    PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
      X
  firstOrderStability :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
      X

/--
The direct one-jet local-stability theorem obtained from the actual
holomorphic local-isometry hypotheses.
-/
structure HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  fieldsHold :
    HyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem X
  oneJetStability :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem
      X

/--
Package component stability with the now-proved fact that every
`HyperbolicLocalChart` satisfies its stored holomorphic local-isometry fields.
-/
def hyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems_of_stability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
      X where
  fieldsHold := hyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem
  valueStability := hValue
  firstOrderStability := hFirst

/--
Package direct one-jet stability with the now-proved fact that every
`HyperbolicLocalChart` satisfies its stored holomorphic local-isometry fields.
-/
def hyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems_of_stability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hStability :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
      X where
  fieldsHold := hyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem
  oneJetStability := hStability

/--
First-order-frame stability alone gives direct one-jet stability.  The
first-order match predicate already includes the value equation, so the
persisted frame match supplies both persisted one-jet components.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_firstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem
      X := by
  intro g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull hpoint y hyU
    hyV _hyValue hyFirst
  rcases hFirst g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull
      hpoint y hyU hyV hyFirst with
    ⟨W, hWOpen, hyW, hW⟩
  refine ⟨W, hWOpen, hyW, ?_⟩
  intro z hzW hzU hzV
  have hzFirst := hW z hzW hzU hzV
  exact ⟨hzFirst.value_eq, hzFirst⟩

/--
Package first-order-frame stability with the automatic local-isometry fields
as the direct one-jet-stability package used downstream.
-/
def hyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems_of_firstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
      X where
  fieldsHold := hyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem
  oneJetStability :=
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_firstOrderStability
      hFirst

/--
Value stability and first-order-frame stability combine to give direct
one-jet stability: intersect the two local neighborhoods and keep both
conclusions on the overlap.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_components
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X)
    (hFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem
      X := by
  intro g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull hpoint y hyU
    hyV hyValue hyFirst
  rcases hValue g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull
      hpoint y hyU hyV hyValue with
    ⟨WValue, hWValueOpen, hyWValue, hWValue⟩
  rcases hFirst g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull
      hpoint y hyU hyV hyFirst with
    ⟨WFirst, hWFirstOpen, hyWFirst, hWFirst⟩
  refine
    ⟨WValue ∩ WFirst, hWValueOpen.inter hWFirstOpen, ⟨hyWValue, hyWFirst⟩,
      ?_⟩
  intro z hzW hzU hzV
  exact ⟨hWValue z hzW.1 hzU hzV, hWFirst z hzW.2 hzU hzV⟩

/--
The component-stability package is strong enough to supply the direct
one-jet-stability package used by the assembly route.
-/
def hyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems_of_componentStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X) :
    HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
      X where
  fieldsHold := h.fieldsHold
  oneJetStability :=
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_components
      h.valueStability h.firstOrderStability

/--
The value component-stability theorem gives the existing value-local-
persistence target by applying the stored chart hypotheses.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_valueStabilityFromHolomorphicLocalIsometry
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFields :
      HyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem X)
    (h :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X := by
  intro g U V A x₀ hpoint y hyU hyV hyValue
  rcases hFields g U with ⟨hUhol, hUbih, hUpull⟩
  rcases hFields g V with ⟨hVhol, hVbih, hVpull⟩
  exact
    h g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull hpoint y hyU
      hyV hyValue

/--
The older value-local-persistence package can be assembled from the Poincare
pullback squared-density formula and the value-stability theorem for actual
holomorphic local isometries; chart continuity and the stored local-isometry
fields are now automatic.
-/
def hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_valueStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_proved
    hPull
    hyperbolicLocalChartContinuousOnDomainTheorem
    (pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_valueStabilityFromHolomorphicLocalIsometry
      hyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem
      hValue)

/--
The first-order component-stability theorem gives the existing first-order
local-persistence target by applying the stored chart hypotheses.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem_of_firstOrderStabilityFromHolomorphicLocalIsometry
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFields :
      HyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem X)
    (h :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
      X := by
  intro g U V A x₀ hpoint y hyU hyV hyFirst
  rcases hFields g U with ⟨hUhol, hUbih, hUpull⟩
  rcases hFields g V with ⟨hVhol, hVbih, hVpull⟩
  exact
    h g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull hpoint y hyU
      hyV hyFirst

/--
Actual holomorphic local-isometry first-order stability gives first-order
local persistence; the stored local-isometry fields have already been proved
for every hyperbolic local chart.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem_of_holomorphicLocalIsometryFirstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem_of_firstOrderStabilityFromHolomorphicLocalIsometry
    hyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem h

/--
Actual holomorphic local-isometry component stability gives the cross-chart
local-persistence package.
-/
def hyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems_of_holomorphicLocalIsometryComponentStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X) :
    HyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems X :=
  { valueLocalPersistence :=
      pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_valueStabilityFromHolomorphicLocalIsometry
        h.fieldsHold h.valueStability
    firstOrderLocalPersistence :=
      pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem_of_firstOrderStabilityFromHolomorphicLocalIsometry
        h.fieldsHold h.firstOrderStability }

/--
The direct one-jet stability theorem gives the existing one-jet local-
persistence target by applying the stored chart hypotheses.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_oneJetStabilityFromHolomorphicLocalIsometry
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFields :
      HyperbolicLocalChartHolomorphicLocalIsometryFieldsHoldTheorem X)
    (h :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem
      X := by
  intro g U V A x₀ hpoint y hyU hyV hyValue hyFirst
  rcases hFields g U with ⟨hUhol, hUbih, hUpull⟩
  rcases hFields g V with ⟨hVhol, hVbih, hVpull⟩
  exact
    h g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull hpoint y hyU
      hyV hyValue hyFirst

/--
Actual holomorphic local-isometry one-jet stability gives the one-jet local-
persistence theorem.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_holomorphicLocalIsometryOneJetStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_oneJetStabilityFromHolomorphicLocalIsometry
    h.fieldsHold h.oneJetStability

/-- Local persistence of the two components gives the corresponding open loci. -/
def hyperbolicLocalChartCrossChartOneJetOpenLociTheorems_of_localPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems X) :
    HyperbolicLocalChartCrossChartOneJetOpenLociTheorems X :=
  { valueOpen :=
      pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem_of_localPersistence
        h.valueLocalPersistence
    firstOrderOpen :=
      pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem_of_firstOrderLocalPersistence
        h.firstOrderLocalPersistence }

/--
The same cross-chart one-jet openness theorem in local-persistence form.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_crossChartLocalPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_crossChartOpenLoci
    (hyperbolicLocalChartCrossChartOneJetOpenLociTheorems_of_localPersistence
      h)

/--
Actual holomorphic local-isometry component stability gives openness of the
one-jet equality locus for pointed cross-chart comparisons.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryComponentStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_crossChartLocalPersistence
    (hyperbolicLocalChartCrossChartOneJetLocalPersistenceTheorems_of_holomorphicLocalIsometryComponentStability
      h)

/--
Actual holomorphic local-isometry first-order stability gives openness of the
corrected one-jet equality locus.  The first-order match predicate already
contains the value equation.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryFirstOrderStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_firstOrderOpen
    (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem_of_firstOrderLocalPersistence
      (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchLocalPersistenceTheorem_of_holomorphicLocalIsometryFirstOrderStability
        h))

/--
Actual holomorphic local-isometry one-jet stability gives openness of the
one-jet equality locus.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryOneJetStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_oneJetLocalPersistence
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_holomorphicLocalIsometryOneJetStability
      h)

/--
Openness of the equality locus is exactly the topological form of local
persistence: an open equality locus in the overlap gives an ambient open
neighborhood on which the equality persists, after intersecting back with the
two chart domains.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_equalitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X := by
  intro g U V A x₀ hpoint y hyU hyV hyEq
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A
  have hyOverlap : y ∈ overlap := ⟨hyU, hyV⟩
  have hyE : (⟨y, hyOverlap⟩ : overlap) ∈ E := by
    simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet] using hyEq
  have hEopen : IsOpen E := hOpen g U V A x₀ hpoint
  rw [isOpen_iff_forall_mem_open] at hEopen
  rcases hEopen (⟨y, hyOverlap⟩ : overlap) hyE with
    ⟨O, hOsub, hOopen, hyO⟩
  rcases isOpen_induced_iff.mp hOopen with ⟨W, hWopen, hWpre⟩
  refine ⟨W, hWopen, ?_, ?_⟩
  · have hyW : (⟨y, hyOverlap⟩ : overlap) ∈ Subtype.val ⁻¹' W := by
      rw [hWpre]
      exact hyO
    exact hyW
  · intro z hzW hzU hzV
    have hzOverlap : z ∈ overlap := ⟨hzU, hzV⟩
    have hzO : (⟨z, hzOverlap⟩ : overlap) ∈ O := by
      have hzPre : (⟨z, hzOverlap⟩ : overlap) ∈ Subtype.val ⁻¹' W := hzW
      rwa [hWpre] at hzPre
    have hzE : (⟨z, hzOverlap⟩ : overlap) ∈ E := hOsub hzO
    simpa [E, pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet] using hzE

/--
Local persistence of pointed equality and openness of the equality locus are
interchangeable theorem targets.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_iff_equalitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem X ↔
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem X :=
  ⟨pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem_of_localPersistence,
    pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_equalitySetOpen⟩

/--
The analytic local-isometry consequence package can be assembled from the
Poincare pullback squared-density formula and the identity-principle openness
target; chart continuity is now automatic.
-/
def hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_equalitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
        X) :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X :=
  hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_proved
    hPull
    hyperbolicLocalChartContinuousOnDomainTheorem
    (pointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem_of_equalitySetOpen
      hOpen)

/--
Openness of the one-jet equality locus gives one-jet local persistence.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem
      X := by
  intro g U V A x₀ hpoint y hyU hyV hyEq hyFirst
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet U V A
  have hyOverlap : y ∈ overlap := ⟨hyU, hyV⟩
  have hyE : (⟨y, hyOverlap⟩ : overlap) ∈ E := by
    exact ⟨hyEq, hyFirst⟩
  have hEopen : IsOpen E := hOpen g U V A x₀ hpoint
  rw [isOpen_iff_forall_mem_open] at hEopen
  rcases hEopen (⟨y, hyOverlap⟩ : overlap) hyE with
    ⟨O, hOsub, hOopen, hyO⟩
  rcases isOpen_induced_iff.mp hOopen with ⟨W, hWopen, hWpre⟩
  refine ⟨W, hWopen, ?_, ?_⟩
  · have hyW : (⟨y, hyOverlap⟩ : overlap) ∈ Subtype.val ⁻¹' W := by
      rw [hWpre]
      exact hyO
    exact hyW
  · intro z hzW hzU hzV
    have hzOverlap : z ∈ overlap := ⟨hzU, hzV⟩
    have hzO : (⟨z, hzOverlap⟩ : overlap) ∈ O := by
      have hzPre : (⟨z, hzOverlap⟩ : overlap) ∈ Subtype.val ⁻¹' W := hzW
      rwa [hWpre] at hzPre
    have hzE : (⟨z, hzOverlap⟩ : overlap) ∈ E := hOsub hzO
    exact hzE

/--
%%handwave
name: Local persistence of a real-Mobius one-jet from openness
statement:
  Suppose the locus where a fixed real Mobius transformation \(A\) matches the value and oriented first-order data of hyperbolic local charts \(U,V\) is open in their overlap. If the match holds at \(y\) and \(A\) is the transformation selected by a pointed comparison, then there is an open surface neighborhood \(W\) of \(y\) on which both matching conditions hold at every point of \(W\cap\operatorname{dom}(U)\cap\operatorname{dom}(V)\).
proof:
  Openness of the equality locus gives one-jet local persistence in the overlap subspace. Apply that persistence statement to the given pointed comparison and the matching point \(y\).
-/
theorem pointedHyperbolicLocalChartRealMobiusTransition_valueAndFirstOrderMatch_persists_of_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {A : RealMobiusRepresentative} {x₀ y : X}
    (hpoint : HyperbolicLocalChartPointedRealMobiusTransition U V A x₀)
    (hyU : y ∈ U.domain) (hyV : y ∈ V.domain)
    (hyValue :
      V.toUpperHalfPlane y =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane y))
    (hyFirst : HyperbolicLocalChartPointedFirstOrderMatch U V A y) :
    ∃ W : Set X,
      IsOpen W ∧ y ∈ W ∧
        ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
          V.toUpperHalfPlane z =
              realMobiusRepresentativeAction A (U.toUpperHalfPlane z) ∧
            HyperbolicLocalChartPointedFirstOrderMatch U V A z :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalPersistenceTheorem_of_oneJetEqualitySetOpen
    hOpen g U V A x₀ hpoint y hyU hyV hyValue hyFirst

/--
%%handwave
name: At-point persistence of a real-Mobius one-jet from openness
statement:
  Suppose the real-Mobius one-jet equality locus of two hyperbolic local charts is open. If \(y\) belongs to both chart domains and \(V(y)=A(U(y))\) with matching oriented first-order data, then these two conditions persist on an open surface neighborhood of \(y\) inside the common domain.
proof:
  Package the domain memberships, value equality, and first-order equality at \(y\) as the pointed comparison based at \(y\), then apply pointwise persistence from openness.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransition_valueAndFirstOrderMatch_persists_atPoint_of_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {A : RealMobiusRepresentative} {y : X}
    (hyU : y ∈ U.domain) (hyV : y ∈ V.domain)
    (hyValue :
      V.toUpperHalfPlane y =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane y))
    (hyFirst : HyperbolicLocalChartPointedFirstOrderMatch U V A y) :
    ∃ W : Set X,
      IsOpen W ∧ y ∈ W ∧
        ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
          V.toUpperHalfPlane z =
              realMobiusRepresentativeAction A (U.toUpperHalfPlane z) ∧
            HyperbolicLocalChartPointedFirstOrderMatch U V A z := by
  let hpoint : HyperbolicLocalChartPointedRealMobiusTransition U V A y :=
    { mem_left := hyU
      mem_right := hyV
      value_match := hyValue
      first_order_match := hyFirst }
  exact
    pointedHyperbolicLocalChartRealMobiusTransition_valueAndFirstOrderMatch_persists_of_oneJetEqualitySetOpen
      hOpen hpoint hyU hyV hyValue hyFirst

/--
%%handwave
name: Persistence of canonical first-order matching from one-jet openness
statement:
  Suppose the real-Mobius one-jet equality locus is open. If two hyperbolic local charts have a canonical normalized coordinate-frame match with \(A\) at \(y\), then on some open neighborhood of \(y\) their values and intrinsic oriented first-order data continue to match through \(A\) wherever both charts are defined.
proof:
  The canonical frame data contain both domain memberships and the value equation, and they induce the intrinsic first-order match. Apply at-point persistence of the one-jet equality.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransition_canonicalFirstOrderMatch_persists_atPoint_of_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {A : RealMobiusRepresentative} {y : X}
    (hyCanon : HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A y) :
    ∃ W : Set X,
      IsOpen W ∧ y ∈ W ∧
        ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
          V.toUpperHalfPlane z =
              realMobiusRepresentativeAction A (U.toUpperHalfPlane z) ∧
            HyperbolicLocalChartPointedFirstOrderMatch U V A z := by
  rcases hyCanon with ⟨DU, DV, hmap⟩
  let hyCanon' :
      HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A y :=
    ⟨DU, DV, hmap⟩
  exact
    pointedHyperbolicLocalChartRealMobiusTransition_valueAndFirstOrderMatch_persists_atPoint_of_oneJetEqualitySetOpen
      hOpen DU.mem_domain DV.mem_domain
      hyCanon'.value_eq
      (HyperbolicLocalChartPointedFirstOrderMatch_of_canonical hyCanon')


end HyperbolicMetric

end

end JJMath
