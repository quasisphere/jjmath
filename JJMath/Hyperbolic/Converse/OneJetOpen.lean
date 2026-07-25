import JJMath.Hyperbolic.Converse.LocalInverseTransition

/-!
# The one-jet openness boundary

This file isolates the remaining analytic input behind the `oneJetOpen`
component of the componentwise continuation route.

The theorem needed by the existing route is an openness statement for the locus
where a fixed real Mobius transition matches a pair of hyperbolic local charts
to first order.  The basepointed transition hypothesis is only used to choose
the real Mobius map globally; the local openness argument itself is an
at-the-point rigidity statement for holomorphic hyperbolic local isometries.

The reductions below keep that distinction explicit: once the at-point local
rigidity theorem is supplied, the existing public `oneJetOpen` theorem follows.
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Value-level local rigidity input for the one-jet openness step.

This is the geometric statement suggested by the induced-isometry argument:
if the fixed real Mobius comparison has the correct value and oriented
first-order data at a point, then the value equality already persists locally.
The derivative part of one-jet persistence is then formal, by differentiating
this local equality.

%%handwave
name: Local value rigidity from a pointed one-jet match
statement:
  If holomorphic local hyperbolic isometries $U,V$ have the same value and
  oriented first-order frame at $y$ after postcomposition of $U$ by a fixed
  real Möbius transformation $A$, then $V=A\circ U$ on a neighborhood of
  $y$ inside their common domain.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (y : X),
      U.holomorphic_on_domain →
      U.local_biholomorph_on_domain →
      U.pulls_back_metric_on_domain →
      V.holomorphic_on_domain →
      V.local_biholomorph_on_domain →
      V.pulls_back_metric_on_domain →
      y ∈ U.domain →
      y ∈ V.domain →
      V.toUpperHalfPlane y =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane y) →
      HyperbolicLocalChartPointedFirstOrderMatch U V A y →
        ∃ W : Set X,
          IsOpen W ∧ y ∈ W ∧
            ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
              V.toUpperHalfPlane z =
                realMobiusRepresentativeAction A (U.toUpperHalfPlane z)

/--
%%handwave
name: First-order matching obtained by differentiating a local Mobius identity
statement:
  Let \(x\in\operatorname{dom}(U)\cap\operatorname{dom}(V)\). If, in the ambient coordinate at \(x\), the germs of \(V\) and \(A\circ U\) agree for a real Mobius transformation \(A\), then
  \[
    V'(x)=A'(U(x))U'(x)
  \]
  in that coordinate.
proof:
  Equal germs have equal derivatives. Apply the complex chain rule to the derivative of \(A\circ U\).
-/
theorem hyperbolicLocalChartConcreteFirstOrderMatch_of_eventuallyEq_realMobius_atPoint
    [ComplexOneManifold X] {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {A : RealMobiusRepresentative} {x : X}
    (hxU : x ∈ U.domain) (_hxV : x ∈ V.domain)
    (hEq :
      (fun z : ℂ =>
          (V.toUpperHalfPlane ((chartAt ℂ x).symm z) : ℂ)) =ᶠ[
            nhds ((chartAt ℂ x) x)]
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane ((chartAt ℂ x).symm z)) : ℂ))) :
    HyperbolicLocalChartConcreteFirstOrderMatch U V A x := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z₀ : ℂ := e x
  let F : ℂ → ℂ := fun z => (U.toUpperHalfPlane (e.symm z) : ℂ)
  let M : ℂ → ℂ := fun w =>
    (realMobiusRepresentativeAction A
      ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  have hsymm_z₀ : e.symm z₀ = x := by
    dsimp [e, z₀]
    exact (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hF_point : F z₀ = (U.toUpperHalfPlane x : ℂ) := by
    dsimp [F, z₀]
    rw [hsymm_z₀]
  have hF_diff : DifferentiableAt ℂ F z₀ := by
    simpa [F, e, z₀] using
      U.coordinateExpressionAt_differentiableAt hxU
  have hM_diff : DifferentiableAt ℂ M (U.toUpperHalfPlane x : ℂ) := by
    simpa [M] using
      realMobiusRepresentativeAction_differentiableAt A
        (U.toUpperHalfPlane x)
  have hchain :
      deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane (e.symm z)) : ℂ))
          z₀ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x) *
          deriv F z₀ := by
    have hcomp := deriv_comp_of_eq z₀ hM_diff hF_diff hF_point
    calc
      deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane (e.symm z)) : ℂ))
          z₀ =
        deriv (fun z : ℂ => M (F z)) z₀ := by
          congr 1
          ext z
          simp [M, F]
      _ = deriv M (U.toUpperHalfPlane x : ℂ) * deriv F z₀ := by
          simpa [Function.comp_def, hF_point] using hcomp
      _ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x) *
          deriv F z₀ := by
          rfl
  have hderiv_eq :
      deriv
          (fun z : ℂ =>
            (V.toUpperHalfPlane ((chartAt ℂ x).symm z) : ℂ))
          ((chartAt ℂ x) x) =
        deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane ((chartAt ℂ x).symm z)) : ℂ))
          ((chartAt ℂ x) x) :=
    Filter.EventuallyEq.deriv_eq hEq
  dsimp [HyperbolicLocalChartConcreteFirstOrderMatch,
    hyperbolicLocalChartCoordinateDerivativeAt,
    hyperbolicLocalChartCoordinateExpressionAt]
  simpa [e, z₀, F] using hderiv_eq.trans hchain

/-- Pointwise local rigidity input for the one-jet openness step.

Mathematically, this says: if two holomorphic hyperbolic local isometries into
`ℍ`, after applying a fixed real Mobius transformation to one of them, have the
same value and first derivative at a point, then that equality persists on a
neighborhood of the point.  This is the actual analytic boundary; it is the
local uniqueness theorem for the hyperbolic local-isometry equation.

%%handwave
name: Pointwise local rigidity of hyperbolic chart one-jets
statement:
  If holomorphic local hyperbolic isometries $U,V$ agree at $y$ to first
  order after postcomposition of $U$ by a fixed real Möbius transformation
  $A$, then both the value equality and the first-order frame equality hold
  throughout a neighborhood of $y$ in their overlap.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (y : X),
      U.holomorphic_on_domain →
      U.local_biholomorph_on_domain →
      U.pulls_back_metric_on_domain →
      V.holomorphic_on_domain →
      V.local_biholomorph_on_domain →
      V.pulls_back_metric_on_domain →
      y ∈ U.domain →
      y ∈ V.domain →
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
%%handwave
name: Full one-jet rigidity from value rigidity
statement:
  On a complex one-manifold, suppose that value and first-order matching at a point imply the local value identity \(V=A\circ U\). Then, after shrinking to that neighborhood, both the value identity and the intrinsic first-order matching hold at every common point.
proof:
  Differentiate the persistent value identity at each point to obtain the concrete coordinate derivative relation. The Poincare pullback formula supplies the nonzero coordinate derivative data that convert this relation back into intrinsic oriented first-order matching.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem_of_valueAtPointLocalRigidity
    [ComplexOneManifold X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem X := by
  intro g U V A y hUhol hUbih hUpull hVhol hVbih hVpull hyU hyV hyValue hyFirst
  rcases hValue g U V A y hUhol hUbih hUpull hVhol hVbih hVpull
      hyU hyV hyValue hyFirst with
    ⟨W, hWOpen, hyW, hWValue⟩
  refine ⟨W, hWOpen, hyW, ?_⟩
  intro z hzW hzU hzV
  have hzValue :
      V.toUpperHalfPlane z =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane z) :=
    hWValue z hzW hzU hzV
  have hEvent :
      (fun w : ℂ =>
          (V.toUpperHalfPlane ((chartAt ℂ z).symm w) : ℂ)) =ᶠ[
            nhds ((chartAt ℂ z) z)]
        (fun w : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane ((chartAt ℂ z).symm w)) : ℂ)) := by
    let e : OpenPartialHomeomorph X ℂ := chartAt ℂ z
    let z₀ : ℂ := e z
    have hsurface :
        (W ∩ U.domain) ∩ V.domain ∈ nhds z := by
      exact ((hWOpen.inter U.isOpen_domain).inter V.isOpen_domain).mem_nhds
        ⟨⟨hzW, hzU⟩, hzV⟩
    have hpre :
        ∀ᶠ w in nhds z₀, e.symm w ∈ (W ∩ U.domain) ∩ V.domain :=
      (e.tendsto_symm (mem_chart_source ℂ z)) hsurface
    filter_upwards [hpre] with w hw
    have hval := hWValue (e.symm w) hw.1.1 hw.1.2 hw.2
    exact congrArg (fun p : ℍ => (p : ℂ)) hval
  have hConcrete :
      HyperbolicLocalChartConcreteFirstOrderMatch U V A z :=
    hyperbolicLocalChartConcreteFirstOrderMatch_of_eventuallyEq_realMobius_atPoint
      hzU hzV hEvent
  let hData :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X :=
    hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem
  rcases hData g U z hzU with ⟨DU⟩
  rcases hData g V z hzV with ⟨DV⟩
  exact ⟨hzValue,
    HyperbolicLocalChartPointedFirstOrderMatch_of_concreteFirstOrderMatch
      DU DV hzValue hConcrete⟩

/--
%%handwave
name: Basepointed one-jet stability from pointwise rigidity
statement:
  If a pointed real-Mobius one-jet match of two hyperbolic charts persists locally at every overlap point, then it satisfies the corresponding basepointed local-stability property.
proof:
  Apply pointwise rigidity at the point under consideration. The additional distinguished base point used to select the transformation is irrelevant to this local conclusion.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_atPointLocalRigidity
    (hRigidity :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem X := by
  intro g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull hpoint y hyU hyV hval hfirst
  exact
    hRigidity g U V A y hUhol hUbih hUpull hVhol hVbih hVpull hyU hyV hval hfirst

/--
%%handwave
name: Openness of the one-jet equality locus from pointwise rigidity
statement:
  If value and first-order matching with a fixed real Mobius transformation persist locally at each matching point, then the joint one-jet equality locus in the overlap of two hyperbolic charts is open.
proof:
  Pointwise rigidity gives the required local stability for holomorphic local isometries. The general stability-to-openness argument then supplies an open neighborhood of every point in the equality locus.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_atPointLocalRigidity
    (hRigidity :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryOneJetStability
    (hyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems_of_stability
      (pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_atPointLocalRigidity
        hRigidity))

/--
%%handwave
name: Openness of the one-jet equality locus from value rigidity
statement:
  On a complex one-manifold, if a pointed one-jet match implies local equality of chart values up to the fixed real Mobius transformation, then the locus of value and first-order matching is open.
proof:
  Persistent value equality differentiates to persistent first-order equality, giving pointwise one-jet rigidity. Apply openness of the equality locus from that pointwise rigidity.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueAtPointLocalRigidity
    [ComplexOneManifold X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_atPointLocalRigidity
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem_of_valueAtPointLocalRigidity
      hValue)

/--
%%handwave
name: Local value rigidity for hyperbolic chart one-jets
statement:
  Let \(U,V\) be hyperbolic local charts on a complex one-manifold, containing \(y\). If a real Mobius transformation \(A\) satisfies \(V(y)=A(U(y))\) and matches the oriented first-order data at \(y\), then \(V=A\circ U\) on a neighborhood of \(y\) inside the common chart domain.
proof:
  Pass to a fixed surface coordinate and invert the \(U\)-coordinate locally. The transition to \(V\) preserves the Poincare metric and has the same one-jet as \(A\), so local Schwarzian rigidity identifies the transition with \(A\). Pull the identity back to the surface.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem
    [ComplexOneManifold X] :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem
      X := by
  intro g U V A y _hUhol _hUbih _hUpull _hVhol _hVbih _hVpull
    hyU hyV hyValue hyFirst
  exact
    hyperbolicLocalChart_realMobiusTransition_value_eq_near_of_oneJet
      U V A hyU hyV hyValue hyFirst

/--
%%handwave
name: Openness of real-Mobius one-jet matching for hyperbolic charts
statement:
  For two hyperbolic local charts on a complex one-manifold and a fixed real Mobius transformation, the subset of their overlap where their values and oriented first-order data match is open.
proof:
  Local value rigidity holds for every matching point. The value identity can be differentiated to recover local first-order matching, so the one-jet equality locus is open.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
    [ComplexOneManifold X] :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueAtPointLocalRigidity
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem



namespace HyperbolicLocalChartOneJetOpenClassificationBoundaryTheorems

end HyperbolicLocalChartOneJetOpenClassificationBoundaryTheorems

end HyperbolicMetric

end

end JJMath
