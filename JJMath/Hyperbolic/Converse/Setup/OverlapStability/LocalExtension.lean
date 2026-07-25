import JJMath.Hyperbolic.Converse.Setup.ChartFrames

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
Componentwise extension target for pointed hyperbolic local-chart matches.

This is the natural local-uniqueness boundary for analytic continuation on
possibly disconnected overlaps: the pointed match propagates exactly on the
connected component of `U.domain ∩ V.domain` containing the pointed match.

%%handwave
name: Componentwise extension of pointed hyperbolic local-chart matches
statement:
  If a real Möbius transformation $A$ matches hyperbolic local charts $U,V$
  to first order at $x_0$, then $V(x)=A(U(x))$ for every $x$ in the connected
  component of $\operatorname{dom}U\cap\operatorname{dom}V$ containing
  $x_0$.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
    HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
      ∀ x, x ∈ U.domain → x ∈ V.domain →
        x ∈ connectedComponentIn (U.domain ∩ V.domain) x₀ →
          V.toUpperHalfPlane x =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane x)

/--
The equality locus of a pointed real-Mobius comparison of two hyperbolic local
charts, viewed as a subset of the common overlap.

%%handwave
name: The equality locus of a pointed real-Möbius comparison of two hyperbolic local charts, viewed as a subset of the common overlap
statement:
  For charts $U,V$ and a real Möbius transformation $A$, define the relative
  equality locus
  $\{x\in\operatorname{dom}U\cap\operatorname{dom}V:V(x)=A(U(x))\}$.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) :
    Set {x : X // x ∈ U.domain ∩ V.domain} :=
  {x | V.toUpperHalfPlane (x : X) =
      realMobiusRepresentativeAction A (U.toUpperHalfPlane (x : X))}

/--
The one-jet equality locus of a real-Mobius comparison of two hyperbolic local
charts, viewed as a subset of the common overlap.

This is the corrected local uniqueness locus: value equality alone does not
determine a holomorphic hyperbolic local isometry, but value plus the oriented
first-order frame does.

%%handwave
name: The one-jet equality locus of a real-Möbius comparison of two hyperbolic local charts, viewed as a subset of the common overlap
statement:
  For charts $U,V$ and a real Möbius transformation $A$, define the relative
  one-jet equality locus by the simultaneous conditions
  $V(x)=A(U(x))$ and equality of the corresponding normalized first-order
  frames.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) :
    Set {x : X // x ∈ U.domain ∩ V.domain} :=
  {x | V.toUpperHalfPlane (x : X) =
          realMobiusRepresentativeAction A (U.toUpperHalfPlane (x : X)) ∧
      HyperbolicLocalChartPointedFirstOrderMatch U V A (x : X)}

/--
Continuity target for hyperbolic local charts on their domains.

For the present lightweight chart structure this is a theorem target, because
the holomorphicity/local-isometry fields are still abstract propositions.

%%handwave
name: Continuity of hyperbolic local charts on their domains
statement:
  Every hyperbolic local chart $U$ defines a continuous map
  $\operatorname{dom}U\to\mathbb H$.
-/
def HyperbolicLocalChartContinuousOnDomainTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g),
    Continuous (fun x : {x : X // x ∈ U.domain} ↦ U.toUpperHalfPlane (x : X))

/--
%%handwave
name: Continuity of a hyperbolic local chart on its domain
statement:
  Every hyperbolic local chart \(U\) defines a continuous map \(U:\operatorname{dom}(U)\to\mathbb H\).
proof:
  The stored surface coordinate is continuous on the chart domain. Its values lie in the coordinate domain of the stored holomorphic upper-half-plane map, which is continuous there. Compose the two maps and use the stored coordinate formula for \(U\).
-/
theorem hyperbolicLocalChartContinuousOnDomainTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    HyperbolicLocalChartContinuousOnDomainTheorem X := by
  intro g U
  let L := U.local_isometry
  have hCoordinate : ContinuousOn L.coordinate U.domain :=
    (L.chart.continuousOn_toFun.mono L.domain_subset_chart_source).congr
      L.coordinate_eq_chart
  have hCoordinateSubtype :
      Continuous (fun x : {x : X // x ∈ U.domain} ↦ L.coordinate (x : X)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hCoordinate)
  let toCoordinateDomain :
      {x : X // x ∈ U.domain} → {z : ℂ // z ∈ L.coordinateDomain} :=
    fun x ↦ ⟨L.coordinate (x : X), L.coordinate_mem_domain (x : X) x.property⟩
  have hToCoordinateDomain : Continuous toCoordinateDomain :=
    hCoordinateSubtype.subtype_mk
      (fun x ↦ L.coordinate_mem_domain (x : X) x.property)
  have hLocalMapVal :
      ContinuousOn (fun z : ℂ ↦ (L.localMap z : ℂ))
        L.coordinateDomain := by
    intro z hz
    exact (L.holomorphic_on_domain z hz).continuousAt.continuousWithinAt
  have hLocalMapValSubtype :
      Continuous
        (fun z : {z : ℂ // z ∈ L.coordinateDomain} ↦
          (L.localMap (z : ℂ) : ℂ)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hLocalMapVal)
  have hLocalMapSubtype :
      Continuous
        (fun z : {z : ℂ // z ∈ L.coordinateDomain} ↦
          L.localMap (z : ℂ)) := by
    exact continuous_induced_rng.mpr (by
      simpa [Function.comp_def] using hLocalMapValSubtype)
  have hComp :
      Continuous
        (fun x : {x : X // x ∈ U.domain} ↦
          L.localMap (L.coordinate (x : X))) := by
    simpa [toCoordinateDomain] using
      hLocalMapSubtype.comp hToCoordinateDomain
  exact
    hComp.congr
      (fun x ↦ (L.toUpperHalfPlane_eq (x : X) x.property).symm)

/--
Continuity target for the two maps whose equality defines the local-chart
real-Mobius equality locus.

%%handwave
name: Continuity of the two maps whose equality defines the local-chart real-Möbius equality locus
statement:
  For hyperbolic local charts $U,V$ and a pointed comparison by $A$, both
  $x\mapsto V(x)$ and $x\mapsto A(U(x))$ are continuous on their common
  domain.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        Continuous
          (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
            V.toUpperHalfPlane (x : X)) ∧
        Continuous
          (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
            realMobiusRepresentativeAction A (U.toUpperHalfPlane (x : X)))

/--
Continuity of local charts on their domains, together with continuity of the
real Mobius action, gives continuity of the two maps compared in the equality
locus.

%%handwave
name: Continuity of local charts on their domains, together with continuity of the real Möbius action, gives continuity of the two maps compared in the equality locus
statement:
  Continuity of local charts on their domains, together with continuity of the real Möbius
  action, gives continuity of the two maps compared in the equality locus.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem_of_chart_continuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart : HyperbolicLocalChartContinuousOnDomainTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem X := by
  intro g U V A x₀ _hpoint
  let overlap : Set X := U.domain ∩ V.domain
  let toUDomain : overlap → {x : X // x ∈ U.domain} :=
    fun x ↦ ⟨x, x.property.1⟩
  let toVDomain : overlap → {x : X // x ∈ V.domain} :=
    fun x ↦ ⟨x, x.property.2⟩
  have htoU : Continuous toUDomain := by
    exact continuous_subtype_val.subtype_mk (fun x ↦ x.property.1)
  have htoV : Continuous toVDomain := by
    exact continuous_subtype_val.subtype_mk (fun x ↦ x.property.2)
  have hU :
      Continuous
        (fun x : overlap ↦ U.toUpperHalfPlane (x : X)) := by
    exact (hChart g U).comp htoU
  have hV :
      Continuous
        (fun x : overlap ↦ V.toUpperHalfPlane (x : X)) := by
    exact (hChart g V).comp htoV
  exact ⟨hV, (realMobiusRepresentativeAction_continuous A).comp hU⟩

/--
%%handwave
name: Continuity of a real-Mobius comparison on a chart overlap
statement:
  Let \(U,V\) be hyperbolic local charts and \(A\) a real Mobius transformation. On \(\operatorname{dom}(U)\cap\operatorname{dom}(V)\), both \(x\mapsto V(x)\) and \(x\mapsto A(U(x))\) are continuous.
proof:
  Restrict the continuous chart maps to the overlap, and compose the restriction of \(U\) with the continuous real Mobius action.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem_of_chart_continuity
    hyperbolicLocalChartContinuousOnDomainTheorem

/--
Closedness target for the local-chart equality locus.

This should follow from continuity of the local chart maps and of the real
Mobius action.

%%handwave
name: Closedness of the local-chart equality locus
statement:
  For every pointed real Möbius comparison of $U$ and $V$, the locus
  $\{x:V(x)=A(U(x))\}$ is closed relative to
  $\operatorname{dom}U\cap\operatorname{dom}V$.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsClosed (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A)

/-- Continuity of the two compared maps makes the equality locus closed.

%%handwave
name: Continuity of the two compared maps makes the equality locus closed
statement:
  Continuity of the two compared maps makes the equality locus closed.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCont :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem X := by
  intro g U V A x₀ hpoint
  rcases hCont g U V A x₀ hpoint with ⟨hV, hA⟩
  simpa [pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet] using
    isClosed_eq hV hA

/--
%%handwave
name: Closedness of a real-Mobius equality locus
statement:
  For hyperbolic local charts \(U,V\) and a real Mobius transformation \(A\), the set
  \[
    \{x\in\operatorname{dom}(U)\cap\operatorname{dom}(V):V(x)=A(U(x))\}
  \]
  is closed relative to the chart overlap.
proof:
  It is the equality locus of the two continuous maps \(x\mapsto V(x)\) and \(x\mapsto A(U(x))\), hence is closed because the upper half-plane is Hausdorff.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem

/--
Openness target for the one-jet equality locus of a pointed comparison.

This is the mathematically natural local identity-principle target: a
holomorphic hyperbolic local isometry is locally determined by its value and
oriented first-order frame.

%%handwave
name: Openness of the one-jet equality locus of a pointed comparison
statement:
  For every pointed real Möbius comparison of hyperbolic local charts $U,V$,
  the locus where both $V(x)=A(U(x))$ and their normalized first-order
  frames agree is open in $\operatorname{dom}U\cap\operatorname{dom}V$.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsOpen
          (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet
            U V A)

end HyperbolicMetric

end

end JJMath
