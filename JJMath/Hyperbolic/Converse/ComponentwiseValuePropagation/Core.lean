import JJMath.Hyperbolic.Converse.Assembly.BoundaryPackages
import JJMath.Hyperbolic.Converse.ChartDerivativeContinuity
import JJMath.Hyperbolic.Converse.OneJetOpen

/-!
# Split selected/componentwise converse route
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
The concrete first-order relation in the fixed source coordinate stored by
the left chart.  This is the common-coordinate replacement for the older
moving-`chartAt` concrete first-order relation.
-/
def HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch
    {g : HyperbolicMetric X} (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x : X) : Prop :=
  hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x =
    realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x) *
      hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U x

/--
A fixed-left-source first-order match implies the older ambient-coordinate
concrete first-order match.  The same source chart-transition derivative is
introduced on both sides, so no moving chart continuity is involved.
-/
theorem hyperbolicLocalChartConcreteFirstOrderMatch_of_leftSourceConcreteFirstOrderMatch
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative}
    {x : X} (hxU : x ∈ U.domain) (hxV : x ∈ V.domain)
    (hLeft :
      HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch U V A x) :
    HyperbolicLocalChartConcreteFirstOrderMatch U V A x := by
  let τ' : ℂ :=
    deriv
      (fun z : ℂ ↦
        U.local_isometry.chart ((chartAt ℂ x).symm z))
      ((chartAt ℂ x) x)
  have hV :
      hyperbolicLocalChartCoordinateDerivativeAt V x =
        hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x * τ' := by
    simpa [τ'] using
      hyperbolicLocalChartCoordinateDerivativeAt_eq_leftSourceCoordinateDerivativeAt_mul_chartTransitionDerivative
        U V hxU hxV
  have hU :
      hyperbolicLocalChartCoordinateDerivativeAt U x =
        hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U x * τ' := by
    simpa [τ'] using
      hyperbolicLocalChartCoordinateDerivativeAt_eq_leftSourceCoordinateDerivativeAt_mul_chartTransitionDerivative
        U U hxU hxU
  dsimp [HyperbolicLocalChartConcreteFirstOrderMatch]
  rw [hV, hU]
  dsimp [HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch] at hLeft
  rw [hLeft]
  ring

/--
If the value equality persists in the fixed source coordinate of `U`, then
the fixed-left-source first-order equation follows by differentiating that
local equality.
-/
theorem hyperbolicLocalChartLeftSourceConcreteFirstOrderMatch_of_eventuallyEq_realMobius
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative}
    {x : X} (hxU : x ∈ U.domain) (_hxV : x ∈ V.domain)
    (hEq :
      (fun z : ℂ =>
          (V.toUpperHalfPlane (U.local_isometry.chart.symm z) : ℂ)) =ᶠ[
            nhds (U.local_isometry.coordinate x)]
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane (U.local_isometry.chart.symm z)) : ℂ))) :
    HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch U V A x := by
  let z₀ : ℂ := U.local_isometry.coordinate x
  let F : ℂ → ℂ := hyperbolicLocalChartLeftSourceCoordinateExpression U U
  let M : ℂ → ℂ := fun w =>
    (realMobiusRepresentativeAction A
      ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  have hxSource : x ∈ U.local_isometry.chart.source :=
    U.local_isometry.domain_subset_chart_source hxU
  have hsymm_z₀ :
      U.local_isometry.chart.symm z₀ = x := by
    dsimp [z₀]
    rw [U.local_isometry.coordinate_eq_chart hxU]
    exact U.local_isometry.chart.left_inv hxSource
  have hF_point : F z₀ = (U.toUpperHalfPlane x : ℂ) := by
    dsimp [F, z₀, hyperbolicLocalChartLeftSourceCoordinateExpression]
    rw [hsymm_z₀]
  have hF_diff : DifferentiableAt ℂ F z₀ := by
    simpa [F, z₀] using
      hyperbolicLocalChartLeftSourceCoordinateExpression_differentiableAt
        U U hxU hxU
  have hM_diff : DifferentiableAt ℂ M (U.toUpperHalfPlane x : ℂ) := by
    simpa [M] using
      realMobiusRepresentativeAction_differentiableAt A
        (U.toUpperHalfPlane x)
  have hchain :
      deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane (U.local_isometry.chart.symm z)) : ℂ))
          z₀ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x) *
          deriv F z₀ := by
    have hcomp := deriv_comp_of_eq z₀ hM_diff hF_diff hF_point
    calc
      deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane (U.local_isometry.chart.symm z)) : ℂ))
          z₀ =
        deriv (fun z : ℂ => M (F z)) z₀ := by
          congr 1
          ext z
          simp [M, F, hyperbolicLocalChartLeftSourceCoordinateExpression]
      _ = deriv M (U.toUpperHalfPlane x : ℂ) * deriv F z₀ := by
          simpa [Function.comp_def, hF_point] using hcomp
      _ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x) *
          deriv F z₀ := by
          rfl
  have hderiv_eq :
      deriv
          (fun z : ℂ =>
            (V.toUpperHalfPlane (U.local_isometry.chart.symm z) : ℂ))
          (U.local_isometry.coordinate x) =
        deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane (U.local_isometry.chart.symm z)) : ℂ))
          (U.local_isometry.coordinate x) :=
    Filter.EventuallyEq.deriv_eq hEq
  dsimp [HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch,
    hyperbolicLocalChartLeftSourceCoordinateDerivativeAt,
    hyperbolicLocalChartLeftSourceCoordinateExpression]
  simpa [F, z₀] using hderiv_eq.trans hchain

/--
The value-plus-left-source-first-order locus for a pointed real-Mobius
comparison of two hyperbolic local charts.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet
    {g : HyperbolicMetric X} (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) :
    Set {x : X // x ∈ U.domain ∩ V.domain} :=
  {x |
    V.toUpperHalfPlane (x : X) =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane (x : X)) ∧
      HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch U V A (x : X)}

/--
Continuity target for the two derivative-comparison maps in the fixed
left-source coordinate.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        Continuous
          (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
            hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V (x : X)) ∧
        Continuous
          (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
            realMobiusRepresentativeDerivativeAt A
                (U.toUpperHalfPlane (x : X)) *
              hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U (x : X))

/--
Closedness target for the fixed-left-source value-plus-first-order locus.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsClosedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsClosed
          (pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet
            U V A)

/--
Derivative continuity in the fixed left-source coordinate makes the
value-plus-first-order locus closed.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsClosedTheorem
      X := by
  intro g U V A x₀ hpoint
  have hValueClosed :
      IsClosed
        (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A) :=
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
      g U V A x₀ hpoint
  rcases hDeriv g U V A x₀ hpoint with ⟨hLeft, hRight⟩
  have hDerivativeClosed :
      IsClosed
        {x : {x : X // x ∈ U.domain ∩ V.domain} |
          hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V (x : X) =
            realMobiusRepresentativeDerivativeAt A
                (U.toUpperHalfPlane (x : X)) *
              hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U
                (x : X)} :=
    isClosed_eq hLeft hRight
  simpa [
    pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet,
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet,
    HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch, Set.setOf_and] using
    hValueClosed.inter hDerivativeClosed

/--
Continuity of fixed-left-source derivatives gives the exact derivative
continuity needed for the value-plus-first-order comparison locus.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem_of_leftSourceCoordinateDerivativeContinuity
    (hDeriv :
      HyperbolicLocalChartLeftSourceCoordinateDerivativeContinuousOnOverlapTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem
      X := by
  intro g U V A x₀ _hpoint
  let overlap : Set X := U.domain ∩ V.domain
  let toUDomain : overlap → {x : X // x ∈ U.domain} :=
    fun x ↦ ⟨x, x.property.1⟩
  let toSelfOverlap :
      overlap → {x : X // x ∈ U.domain ∩ U.domain} :=
    fun x ↦ ⟨x, ⟨x.property.1, x.property.1⟩⟩
  have htoU : Continuous toUDomain :=
    continuous_subtype_val.subtype_mk (fun x ↦ x.property.1)
  have htoSelfOverlap : Continuous toSelfOverlap :=
    continuous_subtype_val.subtype_mk
      (fun x ↦ ⟨x.property.1, x.property.1⟩)
  have hLeft :
      Continuous
        (fun x : overlap ↦
          hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V (x : X)) :=
    hDeriv g U V
  have hUValue :
      Continuous (fun x : overlap ↦ U.toUpperHalfPlane (x : X)) :=
    (hyperbolicLocalChartContinuousOnDomainTheorem g U).comp htoU
  have hMobiusDeriv :
      Continuous (fun p : ℍ ↦ realMobiusRepresentativeDerivativeAt A p) := by
    simpa [realMobiusRepresentativeDerivativeAt] using
      realMobiusRepresentativeAction_deriv_continuous A
  have hMobiusOnU :
      Continuous
        (fun x : overlap ↦
          realMobiusRepresentativeDerivativeAt A
            (U.toUpperHalfPlane (x : X))) :=
    hMobiusDeriv.comp hUValue
  have hUDeriv :
      Continuous
        (fun x : overlap ↦
          hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U (x : X)) :=
    (hDeriv g U U).comp htoSelfOverlap
  exact ⟨hLeft, hMobiusOnU.mul hUDeriv⟩

/--
The fixed-left-source derivative-continuity boundary is unconditional on a
Riemann surface: it follows from chart-transition regularity and holomorphic
local maps.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem
    [ComplexOneManifold X] :
    PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem_of_leftSourceCoordinateDerivativeContinuity
    hyperbolicLocalChartLeftSourceCoordinateDerivativeContinuousOnOverlapTheorem

/--
Openness target for the fixed-left-source value-plus-first-order locus.  This
is where the local analytic identity principle should enter, stated without
moving source charts.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsOpenTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsOpen
          (pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet
            U V A)

/--
Intrinsic one-jet openness opens the fixed-left-source concrete first-order
locus.  At a point of the locus, the fixed-source derivative equation first
gives the intrinsic one-jet; the resulting local value equality is then
differentiated again in the same fixed source coordinate.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsOpenTheorem_of_oneJetEqualitySetOpen
    [ComplexOneManifold X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsOpenTheorem
      X := by
  intro g U V A x₀ hpoint
  let overlap : Set X := U.domain ∩ V.domain
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet
      U V A
  rw [isOpen_iff_forall_mem_open]
  intro y hyE
  have hyValue :
      V.toUpperHalfPlane (y : X) =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane (y : X)) := by
    simpa [E,
      pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet]
      using hyE.1
  have hyLeft :
      HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch U V A (y : X) := by
    simpa [E,
      pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet]
      using hyE.2
  have hyConcrete :
      HyperbolicLocalChartConcreteFirstOrderMatch U V A (y : X) :=
    hyperbolicLocalChartConcreteFirstOrderMatch_of_leftSourceConcreteFirstOrderMatch
      y.property.1 y.property.2 hyLeft
  let hData :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X :=
    hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem
  rcases hData g U (y : X) y.property.1 with ⟨DU⟩
  rcases hData g V (y : X) y.property.2 with ⟨DV⟩
  have hyFirst :
      HyperbolicLocalChartPointedFirstOrderMatch U V A (y : X) :=
    HyperbolicLocalChartPointedFirstOrderMatch_of_concreteFirstOrderMatch
      DU DV hyValue hyConcrete
  rcases
      pointedHyperbolicLocalChartRealMobiusTransition_valueAndFirstOrderMatch_persists_atPoint_of_oneJetEqualitySetOpen
        hOpen y.property.1 y.property.2 hyValue hyFirst with
    ⟨W, hWopen, hyW, hW⟩
  refine ⟨Subtype.val ⁻¹' W, ?_, hWopen.preimage continuous_subtype_val, hyW⟩
  intro z hzW
  have hzPersist :
      V.toUpperHalfPlane (z : X) =
          realMobiusRepresentativeAction A (U.toUpperHalfPlane (z : X)) ∧
        HyperbolicLocalChartPointedFirstOrderMatch U V A (z : X) :=
    hW (z : X) hzW z.property.1 z.property.2
  refine ⟨hzPersist.1, ?_⟩
  have hEvent :
      (fun w : ℂ =>
          (V.toUpperHalfPlane (U.local_isometry.chart.symm w) : ℂ)) =ᶠ[
            nhds (U.local_isometry.coordinate (z : X))]
        (fun w : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane (U.local_isometry.chart.symm w)) : ℂ)) := by
    let e : OpenPartialHomeomorph X ℂ := U.local_isometry.chart
    have hzSource : (z : X) ∈ e.source :=
      U.local_isometry.domain_subset_chart_source z.property.1
    have hsurface :
        (W ∩ U.domain) ∩ V.domain ∈ nhds (z : X) := by
      exact ((hWopen.inter U.isOpen_domain).inter V.isOpen_domain).mem_nhds
        ⟨⟨hzW, z.property.1⟩, z.property.2⟩
    have hpre :
        ∀ᶠ w in nhds (U.local_isometry.coordinate (z : X)),
          e.symm w ∈ (W ∩ U.domain) ∩ V.domain := by
      have ht :
          ∀ᶠ w in nhds (e (z : X)),
            e.symm w ∈ (W ∩ U.domain) ∩ V.domain :=
        (e.tendsto_symm hzSource) hsurface
      simpa [e, U.local_isometry.coordinate_eq_chart z.property.1] using ht
    filter_upwards [hpre] with w hw
    have hval := (hW (e.symm w) hw.1.1 hw.1.2 hw.2).1
    simpa [e] using congrArg (fun p : ℍ => (p : ℂ)) hval
  exact
    hyperbolicLocalChartLeftSourceConcreteFirstOrderMatch_of_eventuallyEq_realMobius
      z.property.1 z.property.2 hEvent

/--
Boundary saying that the pointed transition chosen at `x₀` satisfies the
fixed-left-source first-order equation at the base point.  This replaces any
need to compare continuously varying `chartAt` derivatives.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderAtPointedTransitionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch U V A x₀

/--
The pointed real-Mobius first-order condition implies the fixed-left-source
concrete first-order equation.  The only cancellation needed is the nonzero
derivative of the transition from `chartAt` to the stored left source chart.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderAtPointedTransitionTheorem
    [ComplexOneManifold X] :
    PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderAtPointedTransitionTheorem
      X := by
  intro g U V A x₀ hpoint
  let τ : ℂ :=
    deriv
      (fun z : ℂ ↦
        U.local_isometry.chart ((chartAt ℂ x₀).symm z))
      ((chartAt ℂ x₀) x₀)
  have hτ_ne : τ ≠ 0 := by
    simpa [τ] using
      hyperbolicLocalChart_chartAt_to_storedChartTransitionDerivative_ne
        U hpoint.mem_left
  have hConcrete :
      HyperbolicLocalChartConcreteFirstOrderMatch U V A x₀ :=
    hpoint.first_order_match.concreteFirstOrderMatch
  have hV :
      hyperbolicLocalChartCoordinateDerivativeAt V x₀ =
        hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x₀ * τ := by
    simpa [τ] using
      hyperbolicLocalChartCoordinateDerivativeAt_eq_leftSourceCoordinateDerivativeAt_mul_chartTransitionDerivative
        U V hpoint.mem_left hpoint.mem_right
  have hU :
      hyperbolicLocalChartCoordinateDerivativeAt U x₀ =
        hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U x₀ * τ := by
    simpa [τ] using
      hyperbolicLocalChartCoordinateDerivativeAt_eq_leftSourceCoordinateDerivativeAt_mul_chartTransitionDerivative
        U U hpoint.mem_left hpoint.mem_left
  dsimp [HyperbolicLocalChartConcreteFirstOrderMatch] at hConcrete
  dsimp [HyperbolicLocalChartLeftSourceConcreteFirstOrderMatch]
  have hmul :
      hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x₀ * τ =
        (realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
          hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U x₀) * τ := by
    calc
      hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x₀ * τ =
          hyperbolicLocalChartCoordinateDerivativeAt V x₀ := hV.symm
      _ =
          realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
            hyperbolicLocalChartCoordinateDerivativeAt U x₀ := hConcrete
      _ =
          realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
            (hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U x₀ * τ) := by
          rw [hU]
      _ =
          (realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
            hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U U x₀) * τ := by
          ring
  exact mul_right_cancel₀ hτ_ne hmul

/--
Closedness, openness, and base-point membership of the fixed-left-source
first-order locus propagate value equality on the connected overlap
component.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_leftSourceConcreteFirstOrderMatchSet_closed_open_and_pointedFirstOrder
    (hClosed :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsClosedTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsOpenTheorem
        X)
    (hPoint :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderAtPointedTransitionTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X := by
  intro g U V A x₀ hpoint x hxU hxV hxComponent
  let overlap : Set X := U.domain ∩ V.domain
  let component : Set X := connectedComponentIn overlap x₀
  let E : Set overlap :=
    pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet
      U V A
  let incl : component → overlap := fun y =>
    ⟨(y : X), connectedComponentIn_subset overlap x₀ y.property⟩
  let Ecomponent : Set component := incl ⁻¹' E
  haveI : PreconnectedSpace component :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have hincl : Continuous incl :=
    Continuous.subtype_mk continuous_subtype_val
      (fun y => connectedComponentIn_subset overlap x₀ y.property)
  have hE : IsClopen E :=
    ⟨hClosed g U V A x₀ hpoint, hOpen g U V A x₀ hpoint⟩
  have hEcomponent : IsClopen Ecomponent :=
    ⟨hE.1.preimage hincl, hE.2.preimage hincl⟩
  have hx₀_overlap : x₀ ∈ overlap := ⟨hpoint.mem_left, hpoint.mem_right⟩
  have hx₀_component : x₀ ∈ component :=
    mem_connectedComponentIn hx₀_overlap
  have hx₀_E : (⟨x₀, hx₀_overlap⟩ : overlap) ∈ E := by
    simpa [E,
      pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet] using
      And.intro hpoint.value_match (hPoint g U V A x₀ hpoint)
  have hx₀_Ecomponent :
      (⟨x₀, hx₀_component⟩ : component) ∈ Ecomponent := by
    simpa [Ecomponent, incl, E] using hx₀_E
  have hE_univ : Ecomponent = Set.univ :=
    IsClopen.eq_univ hEcomponent
      ⟨⟨x₀, hx₀_component⟩, hx₀_Ecomponent⟩
  have hx_component : x ∈ component := by
    simpa [component, overlap] using hxComponent
  have hx_Ecomponent : (⟨x, hx_component⟩ : component) ∈ Ecomponent := by
    rw [hE_univ]
    exact Set.mem_univ _
  have hx_overlap : x ∈ overlap := ⟨hxU, hxV⟩
  have hx_E : (⟨x, hx_overlap⟩ : overlap) ∈ E := by
    change incl ⟨x, hx_component⟩ ∈ E at hx_Ecomponent
    simpa [incl] using hx_Ecomponent
  exact
    (by
      simpa [E,
        pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSet]
        using hx_E.1)

/--
The fixed-left-source route with derivative continuity supplying the closed
side of the clopen argument.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_leftSourceConcreteFirstOrderDerivativeContinuity_open_and_pointedFirstOrder
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem
        X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsOpenTheorem
        X)
    (hPoint :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderAtPointedTransitionTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_leftSourceConcreteFirstOrderMatchSet_closed_open_and_pointedFirstOrder
    (pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
      hDeriv)
    hOpen hPoint

/--
The fixed-left-source route with the open side supplied by intrinsic one-jet
openness.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_leftSourceConcreteFirstOrder_oneJetEqualitySetOpen_and_pointedFirstOrder
    [ComplexOneManifold X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    (hPoint :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderAtPointedTransitionTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_leftSourceConcreteFirstOrderDerivativeContinuity_open_and_pointedFirstOrder
    pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderDerivativeContinuityTheorem
    (pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderMatchSetIsOpenTheorem_of_oneJetEqualitySetOpen
      hOpen)
    hPoint

/--
With one-jet openness proved, fixed-left-source componentwise propagation now
only needs the pointed first-order bridge.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_leftSourceConcreteFirstOrder_pointedFirstOrder
    [ComplexOneManifold X]
    (hPoint :
      PointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderAtPointedTransitionTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_leftSourceConcreteFirstOrder_oneJetEqualitySetOpen_and_pointedFirstOrder
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
    hPoint

/--
The fixed-left-source componentwise value-propagation theorem is now
unconditional on Riemann surfaces.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
    [ComplexOneManifold X] :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem_of_leftSourceConcreteFirstOrder_pointedFirstOrder
    pointedHyperbolicLocalChartRealMobiusTransitionLeftSourceConcreteFirstOrderAtPointedTransitionTheorem

end HyperbolicMetric

end

end JJMath
