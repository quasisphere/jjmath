import JJMath.Hyperbolic.Converse.Setup

/-!
# Chart-derivative continuity

This file isolates the chart-derivative continuity boundary used by the
componentwise one-jet route.

The genuinely analytic part is harmless: in the coordinate stored inside a
`HyperbolicLocalChart`, the derivative of the local upper-half-plane map is
continuous.  The route we want downstream should use this fixed stored
coordinate data directly.
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
The derivative of a hyperbolic local chart in the coordinate stored in its
local-isometry data.
-/
def hyperbolicLocalChartStoredCoordinateDerivativeAt
    {g : HyperbolicMetric X} (U : HyperbolicLocalChart X g) (x : X) : ℂ :=
  deriv (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ))
    (U.local_isometry.coordinate x)

end HyperbolicMetric

namespace HyperbolicLocalChart

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {g : HyperbolicMetric X} (U : HyperbolicLocalChart X g)

/--
%%handwave
name: Continuity of the stored coordinate
statement:
  Let \(U\) be a hyperbolic local chart on \(X\). The coordinate map stored by \(U\), restricted to the domain of \(U\), is continuous.
proof:
  Pointwise continuity follows from the continuity of the stored coordinate relative to the chart domain, using the standard criterion for continuity of a map defined on a subspace.
-/
theorem storedCoordinate_continuousOnDomain :
    Continuous
      (fun x : {x : X // x ∈ U.domain} ↦
        U.local_isometry.coordinate (x : X)) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact
    (continuousWithinAt_iff_continuousAt_restrict
      U.local_isometry.coordinate x.property).mp
      (U.coordinate_continuousWithinAt x.property)

/--
%%handwave
name: Continuity of the derivative of a stored local map
statement:
  Let \(U\) be a hyperbolic local chart and let \(f\) be its holomorphic complex coordinate map. The derivative \(f'\) is continuous on the coordinate domain of \(U\).
proof:
  Holomorphicity makes \(f\) differentiable on the open coordinate domain, hence \(C^1\) there. The derivative of a \(C^1\) function is continuous.
-/
theorem storedLocalMap_deriv_continuousOn_coordinateDomain :
    ContinuousOn
      (deriv (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ)))
      U.local_isometry.coordinateDomain := by
  have hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ))
        U.local_isometry.coordinateDomain := by
    intro z hz
    exact (U.local_isometry.holomorphic_on_domain z hz).differentiableWithinAt
  have hcontDiff :
      ContDiffOn ℂ (1 : WithTop ℕ∞)
        (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ))
        U.local_isometry.coordinateDomain :=
    hdiff.contDiffOn U.local_isometry.isOpen_coordinateDomain
  exact
    hcontDiff.continuousOn_deriv_of_isOpen
      U.local_isometry.isOpen_coordinateDomain le_rfl

/--
%%handwave
name: Continuity of the stored-coordinate derivative
statement:
  Let \(U\) be a hyperbolic local chart with stored coordinate \(z_U\) and holomorphic local map \(f_U\). Then \(x \mapsto f_U'(z_U(x))\) is continuous on the domain of \(U\).
proof:
  The derivative \(f_U'\) is continuous on the coordinate domain, and the stored coordinate \(z_U\) is continuous on the chart domain. Compose these two maps.
-/
theorem storedCoordinateDerivative_continuousOnDomain :
    Continuous
      (fun x : {x : X // x ∈ U.domain} ↦
        HyperbolicMetric.hyperbolicLocalChartStoredCoordinateDerivativeAt U
          (x : X)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hderivAt :
      ContinuousAt
        (deriv (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ)))
        (U.local_isometry.coordinate (x : X)) :=
    U.storedLocalMap_deriv_continuousOn_coordinateDomain.continuousAt
      (U.local_isometry.isOpen_coordinateDomain.mem_nhds
        (U.local_isometry.coordinate_mem_domain (x : X) x.property))
  have hcoordAt :
      ContinuousAt
        (fun y : {y : X // y ∈ U.domain} ↦
          U.local_isometry.coordinate (y : X)) x :=
    U.storedCoordinate_continuousOnDomain.continuousAt
  simpa [Function.comp_def,
    HyperbolicMetric.hyperbolicLocalChartStoredCoordinateDerivativeAt] using
    (ContinuousAt.comp'
      (f := fun y : {y : X // y ∈ U.domain} ↦
        U.local_isometry.coordinate (y : X))
      hderivAt hcoordAt)

end HyperbolicLocalChart

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
The target local chart written in the fixed source coordinate stored by the
left chart `U`.  This is the common-coordinate expression needed for honest
first-order comparisons on an overlap; no moving `chartAt` appears here.
-/
def hyperbolicLocalChartLeftSourceCoordinateExpression
    {g : HyperbolicMetric X} (U V : HyperbolicLocalChart X g) : ℂ → ℂ :=
  fun z : ℂ ↦ (V.toUpperHalfPlane (U.local_isometry.chart.symm z) : ℂ)

/--
Derivative of `V` after writing it in the fixed source coordinate stored by
`U`.
-/
def hyperbolicLocalChartLeftSourceCoordinateDerivativeAt
    {g : HyperbolicMetric X} (U V : HyperbolicLocalChart X g) (x : X) : ℂ :=
  deriv (hyperbolicLocalChartLeftSourceCoordinateExpression U V)
    (U.local_isometry.coordinate x)

/--
The fixed source-coordinate overlap on which `V` written in `U`'s source
coordinate is the honest coordinate expression of the overlap map.
-/
def hyperbolicLocalChartLeftSourceCoordinateOverlap
    {g : HyperbolicMetric X} (U V : HyperbolicLocalChart X g) : Set ℂ :=
  U.local_isometry.chart.target ∩
    U.local_isometry.chart.symm ⁻¹' (U.domain ∩ V.domain)

/--
%%handwave
name: Openness of a fixed source-coordinate overlap
statement:
  For hyperbolic local charts \(U\) and \(V\), the set of points in the coordinate range of \(U\) whose inverse images lie in \(\operatorname{dom}(U)\cap\operatorname{dom}(V)\) is open in \(\mathbb C\).
proof:
  The common surface domain is open, and the inverse of the stored chart of \(U\) is continuous on its open target. Intersect its inverse image with that target.
-/
theorem hyperbolicLocalChartLeftSourceCoordinateOverlap_isOpen
    {g : HyperbolicMetric X} (U V : HyperbolicLocalChart X g) :
    IsOpen (hyperbolicLocalChartLeftSourceCoordinateOverlap U V) := by
  simpa [hyperbolicLocalChartLeftSourceCoordinateOverlap] using
    U.local_isometry.chart.isOpen_inter_preimage_symm
      (U.isOpen_domain.inter V.isOpen_domain)

/--
%%handwave
name: A common point belongs to the fixed coordinate overlap
statement:
  If \(x\in\operatorname{dom}(U)\cap\operatorname{dom}(V)\), then the stored \(U\)-coordinate \(z_U(x)\) lies in the fixed source-coordinate overlap of \(U\) and \(V\).
proof:
  The chart sends \(x\) into its target, and applying its inverse to \(z_U(x)\) returns \(x\). These are exactly the two membership conditions defining the coordinate overlap.
-/
theorem hyperbolicLocalChart_coordinate_mem_leftSourceCoordinateOverlap
    {g : HyperbolicMetric X} (U V : HyperbolicLocalChart X g)
    {x : X} (hxU : x ∈ U.domain) (hxV : x ∈ V.domain) :
    U.local_isometry.coordinate x ∈
      hyperbolicLocalChartLeftSourceCoordinateOverlap U V := by
  have hxSource : x ∈ U.local_isometry.chart.source :=
    U.local_isometry.domain_subset_chart_source hxU
  have hcoord : U.local_isometry.coordinate x = U.local_isometry.chart x :=
    U.local_isometry.coordinate_eq_chart hxU
  have htarget :
      U.local_isometry.coordinate x ∈ U.local_isometry.chart.target := by
    rw [hcoord]
    exact U.local_isometry.chart.map_source hxSource
  have hsymm :
      U.local_isometry.chart.symm (U.local_isometry.coordinate x) = x := by
    rw [hcoord]
    exact U.local_isometry.chart.left_inv hxSource
  exact ⟨htarget, by simpa [hsymm] using And.intro hxU hxV⟩

/--
Regularity target for fixed-source coordinate expressions.  This is the
mathematical derivative-continuity input: the target chart written in the
left chart's fixed coordinate is `C¹` on the coordinate overlap.
-/
def HyperbolicLocalChartLeftSourceCoordinateExpressionContDiffOnTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g),
    ContDiffOn ℂ (1 : WithTop ℕ∞)
      (hyperbolicLocalChartLeftSourceCoordinateExpression U V)
      (hyperbolicLocalChartLeftSourceCoordinateOverlap U V)

/--
%%handwave
name: First-order regularity of a hyperbolic chart in a fixed source coordinate
statement:
  Let \(U,V\) be hyperbolic local charts on a complex one-manifold. On the fixed \(U\)-coordinate image of \(\operatorname{dom}(U)\cap\operatorname{dom}(V)\), the expression \(z\mapsto V(U^{-1}(z))\) is \(C^1\).
proof:
  The change from the stored coordinate of \(U\) to that of \(V\) is \(C^1\), because transitions between complex-manifold charts are smooth. Its image lies in the coordinate domain of the holomorphic local map defining \(V\); composing with that map gives the asserted regularity.
-/
theorem hyperbolicLocalChartLeftSourceCoordinateExpressionContDiffOnTheorem
    [ComplexOneManifold X] :
    HyperbolicLocalChartLeftSourceCoordinateExpressionContDiffOnTheorem X := by
  intro g U V
  let S : Set ℂ := hyperbolicLocalChartLeftSourceCoordinateOverlap U V
  let τ : ℂ → ℂ := fun z ↦
    V.local_isometry.chart (U.local_isometry.chart.symm z)
  have hLocalDiff :
      DifferentiableOn ℂ
        (fun z : ℂ ↦ (V.local_isometry.localMap z : ℂ))
        V.local_isometry.coordinateDomain := by
    intro z hz
    exact (V.local_isometry.holomorphic_on_domain z hz).differentiableWithinAt
  have hLocalContDiff :
      ContDiffOn ℂ (1 : WithTop ℕ∞)
        (fun z : ℂ ↦ (V.local_isometry.localMap z : ℂ))
        V.local_isometry.coordinateDomain :=
    hLocalDiff.contDiffOn V.local_isometry.isOpen_coordinateDomain
  have hUsymm :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        U.local_isometry.chart.symm U.local_isometry.chart.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas U.local_isometry.chart_mem_atlas)
  have hUsymmS :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        U.local_isometry.chart.symm S :=
    hUsymm.mono (by
      intro z hz
      exact hz.1)
  have hVchart :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        V.local_isometry.chart V.local_isometry.chart.source :=
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas V.local_isometry.chart_mem_atlas)
  have hMapsChart :
      S ⊆ U.local_isometry.chart.symm ⁻¹' V.local_isometry.chart.source := by
    intro z hz
    exact V.local_isometry.domain_subset_chart_source hz.2.2
  have hτMD :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        (V.local_isometry.chart ∘ U.local_isometry.chart.symm) S :=
    hVchart.comp hUsymmS hMapsChart
  have hτ :
      ContDiffOn ℂ (1 : WithTop ℕ∞) τ S := by
    simpa [τ, Function.comp_def] using hτMD.contDiffOn
  have hMapsLocal :
      S ⊆ τ ⁻¹' V.local_isometry.coordinateDomain := by
    intro z hz
    have hyV : U.local_isometry.chart.symm z ∈ V.domain := hz.2.2
    have hcoord :
        V.local_isometry.coordinate (U.local_isometry.chart.symm z) =
          V.local_isometry.chart (U.local_isometry.chart.symm z) :=
      V.local_isometry.coordinate_eq_chart hyV
    simpa [τ, hcoord] using
      V.local_isometry.coordinate_mem_domain
        (U.local_isometry.chart.symm z) hyV
  have hComp :
      ContDiffOn ℂ (1 : WithTop ℕ∞)
        (fun z : ℂ ↦
          (V.local_isometry.localMap
            (V.local_isometry.chart (U.local_isometry.chart.symm z)) : ℂ))
        S := by
    simpa [τ, Function.comp_def] using
      hLocalContDiff.comp hτ hMapsLocal
  exact hComp.congr (by
    intro z hz
    have hyV : U.local_isometry.chart.symm z ∈ V.domain := hz.2.2
    have hto :=
      V.local_isometry.toUpperHalfPlane_eq
        (U.local_isometry.chart.symm z) hyV
    have hcoord :
        V.local_isometry.coordinate (U.local_isometry.chart.symm z) =
          V.local_isometry.chart (U.local_isometry.chart.symm z) :=
      V.local_isometry.coordinate_eq_chart hyV
    dsimp [hyperbolicLocalChartLeftSourceCoordinateExpression]
    rw [hto, hcoord])

/--
%%handwave
name: Differentiability in a fixed source coordinate
statement:
  If \(x\in\operatorname{dom}(U)\cap\operatorname{dom}(V)\), then the map \(z\mapsto V(U^{-1}(z))\) is complex differentiable at the stored coordinate \(z_U(x)\).
proof:
  The map is \(C^1\) on the open fixed source-coordinate overlap, and \(z_U(x)\) belongs to that overlap. Differentiability within the overlap therefore upgrades to differentiability at the point.
-/
theorem hyperbolicLocalChartLeftSourceCoordinateExpression_differentiableAt
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) {x : X}
    (hxU : x ∈ U.domain) (hxV : x ∈ V.domain) :
    DifferentiableAt ℂ
      (hyperbolicLocalChartLeftSourceCoordinateExpression U V)
      (U.local_isometry.coordinate x) := by
  have hCont :
      ContDiffOn ℂ (1 : WithTop ℕ∞)
        (hyperbolicLocalChartLeftSourceCoordinateExpression U V)
        (hyperbolicLocalChartLeftSourceCoordinateOverlap U V) :=
    hyperbolicLocalChartLeftSourceCoordinateExpressionContDiffOnTheorem g U V
  have hxCoord :
      U.local_isometry.coordinate x ∈
        hyperbolicLocalChartLeftSourceCoordinateOverlap U V :=
    hyperbolicLocalChart_coordinate_mem_leftSourceCoordinateOverlap U V hxU hxV
  have hDiffWithin :
      DifferentiableWithinAt ℂ
        (hyperbolicLocalChartLeftSourceCoordinateExpression U V)
        (hyperbolicLocalChartLeftSourceCoordinateOverlap U V)
        (U.local_isometry.coordinate x) :=
    hCont.differentiableOn (by norm_num) (U.local_isometry.coordinate x)
      hxCoord
  exact
    hDiffWithin.differentiableAt
      ((hyperbolicLocalChartLeftSourceCoordinateOverlap_isOpen U V).mem_nhds
        hxCoord)

/--
%%handwave
name: Factorization of a chart derivative through a fixed source coordinate
statement:
  Let \(x\in\operatorname{dom}(U)\cap\operatorname{dom}(V)\). If \(e\) is the ambient chart at \(x\), then
  \[
    (V\circ e^{-1})'(e(x))=(V\circ U^{-1})'(z_U(x))\,(U\circ e^{-1})'(e(x)).
  \]
proof:
  Near \(e(x)\), the ambient expression for \(V\) is the composition of its expression in the fixed \(U\)-coordinate with the transition \(U\circ e^{-1}\). Both factors are differentiable, so the formula is the complex chain rule.
-/
theorem hyperbolicLocalChartCoordinateDerivativeAt_eq_leftSourceCoordinateDerivativeAt_mul_chartTransitionDerivative
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) {x : X}
    (hxU : x ∈ U.domain) (hxV : x ∈ V.domain) :
    hyperbolicLocalChartCoordinateDerivativeAt V x =
      hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x *
        deriv
          (fun z : ℂ ↦
            U.local_isometry.chart ((chartAt ℂ x).symm z))
          ((chartAt ℂ x) x) := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z₀ : ℂ := e x
  let τ : ℂ → ℂ := fun z ↦ U.local_isometry.chart (e.symm z)
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ x
  have hsymm_z₀ : e.symm z₀ = x := by
    dsimp [z₀, e]
    exact (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hxU_source : x ∈ U.local_isometry.chart.source :=
    U.local_isometry.domain_subset_chart_source hxU
  have hτ_point : τ z₀ = U.local_isometry.coordinate x := by
    dsimp [τ]
    rw [hsymm_z₀]
    exact (U.local_isometry.coordinate_eq_chart hxU).symm
  have hdomain :
      ∀ᶠ z in nhds z₀, e.symm z ∈ U.domain ∩ V.domain :=
    (e.tendsto_symm (mem_chart_source ℂ x))
      ((U.isOpen_domain.inter V.isOpen_domain).mem_nhds ⟨hxU, hxV⟩)
  have hExpr :
      Filter.EventuallyEq (nhds z₀)
        (hyperbolicLocalChartCoordinateExpressionAt V x)
        (fun z : ℂ ↦
          hyperbolicLocalChartLeftSourceCoordinateExpression U V (τ z)) := by
    filter_upwards [hdomain] with z hz
    have hsource :
        e.symm z ∈ U.local_isometry.chart.source :=
      U.local_isometry.domain_subset_chart_source hz.1
    dsimp [hyperbolicLocalChartCoordinateExpressionAt,
      hyperbolicLocalChartLeftSourceCoordinateExpression, τ]
    rw [U.local_isometry.chart.left_inv hsource]
  have hτ_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) τ z₀ := by
    have hchart_mdiff :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
          U.local_isometry.chart (e.symm z₀) := by
      rw [hsymm_z₀]
      exact mdifferentiableAt_atlas
        U.local_isometry.chart_mem_atlas hxU_source
    dsimp [τ]
    exact
      hchart_mdiff.comp z₀
        (mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) hz₀_target)
  have hτ_diff : DifferentiableAt ℂ τ z₀ := hτ_mdiff.differentiableAt
  have hLeft_diff :
      DifferentiableAt ℂ
        (hyperbolicLocalChartLeftSourceCoordinateExpression U V)
        (U.local_isometry.coordinate x) :=
    hyperbolicLocalChartLeftSourceCoordinateExpression_differentiableAt
      U V hxU hxV
  have hchain :
      deriv
          (fun z : ℂ ↦
            hyperbolicLocalChartLeftSourceCoordinateExpression U V (τ z))
          z₀ =
        hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x *
          deriv τ z₀ := by
    have hcomp := deriv_comp_of_eq z₀ hLeft_diff hτ_diff hτ_point
    simpa [hyperbolicLocalChartLeftSourceCoordinateDerivativeAt,
      Function.comp_def, hτ_point] using hcomp
  calc
    hyperbolicLocalChartCoordinateDerivativeAt V x =
        deriv (hyperbolicLocalChartCoordinateExpressionAt V x) z₀ := by
          rfl
    _ =
        deriv
          (fun z : ℂ ↦
            hyperbolicLocalChartLeftSourceCoordinateExpression U V (τ z))
          z₀ :=
          Filter.EventuallyEq.deriv_eq hExpr
    _ =
        hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x *
          deriv τ z₀ := hchain
    _ =
        hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V x *
          deriv
            (fun z : ℂ ↦
              U.local_isometry.chart ((chartAt ℂ x).symm z))
            ((chartAt ℂ x) x) := by
          rfl

/--
%%handwave
name: Nonvanishing derivative of the transition to a stored chart
statement:
  Let \(x\in\operatorname{dom}(U)\), and let \(e\) be the ambient complex chart at \(x\). The coordinate transition \(U\circ e^{-1}\) has nonzero derivative at \(e(x)\).
proof:
  The conformal density transition law expresses the positive metric density in the \(e\)-coordinate as the density in the stored \(U\)-coordinate times the squared norm of this derivative. A zero derivative would force the positive density to vanish.
-/
theorem hyperbolicLocalChart_chartAt_to_storedChartTransitionDerivative_ne
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) {x : X}
    (hxU : x ∈ U.domain) :
    deriv
        (fun z : ℂ ↦
          U.local_isometry.chart ((chartAt ℂ x).symm z))
        ((chartAt ℂ x) x) ≠ 0 := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z₀ : ℂ := e x
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ x
  have hsymm_z₀ : e.symm z₀ = x := by
    dsimp [z₀, e]
    exact (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hxU_source : x ∈ U.local_isometry.chart.source :=
    U.local_isometry.domain_subset_chart_source hxU
  have hstored_source :
      e.symm z₀ ∈ U.local_isometry.chart.source := by
    simpa [hsymm_z₀] using hxU_source
  have htransition :=
    g.toConformalMetric.densitySq_transition
      e (chart_mem_atlas ℂ x)
      U.local_isometry.chart U.local_isometry.chart_mem_atlas
      hz₀_target hstored_source
  have hpos :
      0 < g.toConformalMetric.densitySqInChart
        e (chart_mem_atlas ℂ x) z₀ :=
    g.toConformalMetric.positive_densitySqInChart
      e (chart_mem_atlas ℂ x) hz₀_target
  intro hzero
  rw [hzero, Complex.normSq_zero, mul_zero] at htransition
  rw [htransition] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/--
Continuity target for the fixed-left-source derivative itself, before adding
the real-Mobius multiplier on the right side of the first-order equation.
-/
def HyperbolicLocalChartLeftSourceCoordinateDerivativeContinuousOnOverlapTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g),
    Continuous
      (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
        hyperbolicLocalChartLeftSourceCoordinateDerivativeAt U V (x : X))

/--
%%handwave
name: Continuous fixed-coordinate derivatives from first-order regularity
statement:
  Suppose every fixed-coordinate expression \(z\mapsto V(U^{-1}(z))\) is \(C^1\) on its coordinate overlap. Then \(x\mapsto (V\circ U^{-1})'(z_U(x))\) is continuous on \(\operatorname{dom}(U)\cap\operatorname{dom}(V)\).
proof:
  The derivative of the \(C^1\) coordinate expression is continuous on the open coordinate overlap. Compose it with the continuous stored coordinate of \(U\), restricted to the surface overlap.
-/
theorem hyperbolicLocalChartLeftSourceCoordinateDerivativeContinuousOnOverlapTheorem_of_contDiffOn
    (hContDiff :
      HyperbolicLocalChartLeftSourceCoordinateExpressionContDiffOnTheorem X) :
    HyperbolicLocalChartLeftSourceCoordinateDerivativeContinuousOnOverlapTheorem
      X := by
  intro g U V
  rw [continuous_iff_continuousAt]
  intro x
  have hDerivOn :
      ContinuousOn
        (deriv (hyperbolicLocalChartLeftSourceCoordinateExpression U V))
        (hyperbolicLocalChartLeftSourceCoordinateOverlap U V) :=
    (hContDiff g U V).continuousOn_deriv_of_isOpen
      (hyperbolicLocalChartLeftSourceCoordinateOverlap_isOpen U V) le_rfl
  have hxCoord :
      U.local_isometry.coordinate (x : X) ∈
        hyperbolicLocalChartLeftSourceCoordinateOverlap U V :=
    hyperbolicLocalChart_coordinate_mem_leftSourceCoordinateOverlap U V
      x.property.1 x.property.2
  have hDerivAt :
      ContinuousAt
        (deriv (hyperbolicLocalChartLeftSourceCoordinateExpression U V))
        (U.local_isometry.coordinate (x : X)) :=
    hDerivOn.continuousAt
      ((hyperbolicLocalChartLeftSourceCoordinateOverlap_isOpen U V).mem_nhds
        hxCoord)
  let toUDomain :
      {x : X // x ∈ U.domain ∩ V.domain} → {x : X // x ∈ U.domain} :=
    fun y ↦ ⟨(y : X), y.property.1⟩
  have htoU : Continuous toUDomain :=
    continuous_subtype_val.subtype_mk (fun y ↦ y.property.1)
  have hCoordAt :
      ContinuousAt
        (fun y : {y : X // y ∈ U.domain ∩ V.domain} ↦
          U.local_isometry.coordinate (y : X)) x :=
    (U.storedCoordinate_continuousOnDomain.comp htoU).continuousAt
  simpa [hyperbolicLocalChartLeftSourceCoordinateDerivativeAt,
    Function.comp_def] using
    (ContinuousAt.comp'
      (f := fun y : {y : X // y ∈ U.domain ∩ V.domain} ↦
        U.local_isometry.coordinate (y : X))
      hDerivAt hCoordAt)

/--
%%handwave
name: Continuity of fixed-coordinate derivatives on chart overlaps
statement:
  For hyperbolic local charts \(U,V\) on a complex one-manifold, the function \(x\mapsto (V\circ U^{-1})'(z_U(x))\) is continuous on \(\operatorname{dom}(U)\cap\operatorname{dom}(V)\).
proof:
  Fixed-coordinate expressions are \(C^1\) on their coordinate overlaps, so apply the continuity result for their derivatives along the surface overlap.
-/
theorem hyperbolicLocalChartLeftSourceCoordinateDerivativeContinuousOnOverlapTheorem
    [ComplexOneManifold X] :
    HyperbolicLocalChartLeftSourceCoordinateDerivativeContinuousOnOverlapTheorem
      X :=
  hyperbolicLocalChartLeftSourceCoordinateDerivativeContinuousOnOverlapTheorem_of_contDiffOn
    hyperbolicLocalChartLeftSourceCoordinateExpressionContDiffOnTheorem

end HyperbolicMetric

end

end JJMath
