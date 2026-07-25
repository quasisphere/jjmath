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
Local persistence target for one-jet equality of hyperbolic local charts.

If the real-Mobius comparison has the same value and oriented first-order
frame at a point of the overlap, then that one-jet equality persists on a
small neighborhood in the overlap.

%%handwave
name: Local persistence of one-jet equality of hyperbolic local charts
statement:
  Local persistence of one-jet equality of hyperbolic local charts. If the real-Möbius
  comparison has the same value and oriented first-order frame at a point of the overlap, then
  that one-jet equality persists on a small neighborhood in the overlap.
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
One-jet local persistence makes the one-jet equality locus open.

%%handwave
name: One-jet local persistence makes the one-jet equality locus open
statement:
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
Global target saying that the analytic propositions stored in each
`HyperbolicLocalChart` actually hold.

The chart record stores these fields as propositions rather than proofs, so
this is the precise boundary needed before one can use the analytic
local-isometry hypotheses in downstream arguments.

%%handwave
name: Assertion that the analytic propositions stored in each hyperbolic local chart actually hold
statement:
  Every hyperbolic local chart is holomorphic and locally biholomorphic on
  its domain and pulls the given hyperbolic metric back from the Poincaré
  metric.
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
Direct one-jet local stability from the actual holomorphic local-isometry
hypotheses.

This is the intrinsic local uniqueness target: value agreement alone is not
stable for hyperbolic local isometries because the target stabilizer of a
point can rotate tangent directions.  Value plus the oriented first-order
frame is the correct local datum.

%%handwave
name: Direct one-jet local stability from the actual holomorphic local-isometry hypotheses
statement:
  If two holomorphic local hyperbolic isometries have, at a point of their
  overlap, the same value and oriented first-order frame after postcomposition
  by a fixed real Möbius transformation, then these two equalities persist on
  a neighborhood of that point in the overlap.
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
Package direct one-jet stability with the now-proved fact that every
`HyperbolicLocalChart` satisfies its stored holomorphic local-isometry fields.

%%handwave
name: Package direct one-jet stability with the now-proved fact that every hyperbolic local chart satisfies its stored holomorphic local-isometry fields
statement:
  Package direct one-jet stability with the now-proved fact that every hyperbolic local chart
  satisfies its stored holomorphic local-isometry fields.
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
The direct one-jet stability theorem gives the existing one-jet local-
persistence target by applying the stored chart hypotheses.

%%handwave
name: The direct one-jet stability theorem gives the existing one-jet local- persistence target by applying the stored chart hypotheses
statement:
  The direct one-jet stability theorem gives the existing one-jet local- persistence target by
  applying the stored chart hypotheses.
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

%%handwave
name: Actual holomorphic local-isometry one-jet stability gives the one-jet local- persistence theorem
statement:
  Actual holomorphic local-isometry one-jet stability gives the one-jet local- persistence
  theorem.
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

/--
Actual holomorphic local-isometry one-jet stability gives openness of the
one-jet equality locus.

%%handwave
name: Actual holomorphic local-isometry one-jet stability gives openness of the one-jet equality locus
statement:
  Actual holomorphic local-isometry one-jet stability gives openness of the one-jet equality
  locus.
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
Openness of the one-jet equality locus gives one-jet local persistence.

%%handwave
name: Openness of the one-jet equality locus gives one-jet local persistence
statement:
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

end HyperbolicMetric

end

end JJMath
