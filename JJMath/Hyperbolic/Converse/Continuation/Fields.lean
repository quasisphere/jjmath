import JJMath.Hyperbolic.Converse.LocalInverseTransition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Sort
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]


namespace ContinuationFromLocalModels

end ContinuationFromLocalModels

/--
Local agreement boundary for a continued developing map and a local-model
atlas whose transition data is only local on overlaps.

%%handwave
name: Local agreement principle for a continued developing map and a local-model atlas whose transition data is only local on overlaps
statement:
  A map $\operatorname{dev}:\widetilde X\to\mathbb H$ locally agrees with
  a transition atlas when every $y\in\widetilde X$ has a neighborhood on
  which $\operatorname{dev}=A\circ U\circ\pi$ for some local model $U$ and
  real Möbius transformation $A$.
-/
def HyperbolicDevelopingAgreesWithLocalTransitionModels
    {x₀ : X} {g : HyperbolicMetric X}
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (cover : SimplyConnectedCover X x₀) (dev : cover.total → ℍ) : Prop :=
  ∀ y, ∃ U : Set cover.total,
    IsOpen U ∧ y ∈ U ∧
      ∃ (x : X) (A : RealMobiusRepresentative),
        (∀ y', y' ∈ U → cover.projection y' ∈ (localModels.chartAt x).domain) ∧
          ∀ y', y' ∈ U →
            dev y' =
              realMobiusRepresentativeAction A
                ((localModels.chartAt x).toUpperHalfPlane (cover.projection y'))

namespace HyperbolicDevelopingAgreesWithLocalTransitionModels

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {cover : SimplyConnectedCover X x₀} {dev : cover.total → ℍ}

omit [RiemannSurface X] in
/-- Local agreement with local-transition models forces pointwise continuity.

%%handwave
name: Local model agreement makes the developing map continuous at every point
statement: Let $dev$ on a simply connected cover agree near each lift $y$ with a real Möbius transformation composed with a local hyperbolic chart of the projected point. Then $dev$ is continuous at $y$.
proof: The cover projection, local chart, and real Möbius action are continuous. Their composite is continuous at $y$, and the assumed neighborhood equality transfers continuity to $dev$.
-/
theorem continuousAt
    (h : HyperbolicDevelopingAgreesWithLocalTransitionModels localModels cover dev)
    (y : cover.total) :
    ContinuousAt dev y := by
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let localModelFun : cover.total → ℍ := fun y' =>
    realMobiusRepresentativeAction A
      ((localModels.chartAt x).toUpperHalfPlane (cover.projection y'))
  have hy_domain : cover.projection y ∈ (localModels.chartAt x).domain :=
    hdomain y hyU
  have hpost :
      ContinuousAt
        (fun x' : X =>
          realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane x'))
        (cover.projection y) :=
    (localModels.chartAt x).realMobius_postcomp_continuousAt A hy_domain
  have hlocal : ContinuousAt localModelFun y := by
    exact hpost.comp (cover.projection_continuousAt y)
  have heq : dev =ᶠ[nhds y] localModelFun := by
    filter_upwards [hUopen.mem_nhds hyU] with y' hy'
    exact hagree y' hy'
  exact hlocal.congr_of_eventuallyEq heq

omit [RiemannSurface X] in
/-- Local agreement with local-transition models forces continuity.

%%handwave
name: Local model agreement makes the developing map continuous
statement: If a developing map agrees locally everywhere with Möbius-transformed hyperbolic model charts, then it is continuous on the entire cover.
proof: Apply the pointwise continuity result at every point.
-/
theorem continuous
    (h : HyperbolicDevelopingAgreesWithLocalTransitionModels localModels cover dev) :
    Continuous dev := by
  rw [continuous_iff_continuousAt]
  intro y
  exact h.continuousAt y

end HyperbolicDevelopingAgreesWithLocalTransitionModels

namespace HyperbolicDevelopingLocalTransitionContinuationDataFields

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end HyperbolicDevelopingLocalTransitionContinuationDataFields

namespace ContinuationFromLocalTransitionModels

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end ContinuationFromLocalTransitionModels

/-- The canonical first field of continuation data: the path-homotopy universal cover.

%%handwave
name: The canonical first field of continuation data: the path-homotopy universal cover
statement:
  For a basepoint $x_0\in X$, take the simply connected cover whose fiber
  over $x$ consists of endpoint-fixed homotopy classes of paths from $x_0$
  to $x$.
-/
def canonicalContinuationCover (x₀ : X) : SimplyConnectedCover X x₀ :=
  PathHomotopyUniversalCover.simplyConnectedCoverOfRiemannSurface

/-- The canonical pulled-back metric on the path-homotopy continuation cover.

%%handwave
name: The canonical pulled-back metric on the path-homotopy continuation cover
statement:
  For the canonical projection $\pi:\widetilde X_{x_0}\to X$, define the
  canonical cover metric by $\widetilde g=\pi^*g$.
-/
def canonicalContinuationCoverMetric (x₀ : X) (g : HyperbolicMetric X) :
    ConformalMetric (canonicalContinuationCover x₀).total :=
  PathHomotopyUniversalCover.pullbackConformalMetric (x₀ := x₀) g.toConformalMetric

/-- The canonical cover metric is the pullback of the base metric.

%%handwave
name: The canonical cover metric is the pullback of the base metric
statement: For the canonical path-homotopy cover $π:X̃→X$, the canonical cover metric satisfies $π^*g=g̃$.
proof: This is the defining pullback property of the canonical cover metric, expressed in compatible source and target charts.
-/
theorem canonicalContinuationCoverMetric_pullback
    (x₀ : X) (g : HyperbolicMetric X) :
    PullsBackMetric
      (canonicalContinuationCover x₀).projection
      g.toConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  PathHomotopyUniversalCover.pullsBackMetric_endpoint_pullbackConformalMetric
    (x₀ := x₀) g.toConformalMetric

namespace HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric

namespace HyperbolicDevelopingContinuationDataFields

end HyperbolicDevelopingContinuationDataFields

/--
Real-Mobius postcomposition of a local model has nonzero derivative in the
ambient surface coordinate.

%%handwave
name: A Möbius-transformed hyperbolic chart has nonzero coordinate derivative
statement: Let $U$ be a hyperbolic local chart, $A$ a real Möbius representative, and $x∈U$. The derivative at the ambient coordinate of $x$ of $z↦A·U((chart_x)^{-1}(z))$ is nonzero.
proof: The local hyperbolic coordinate has nonzero derivative, and the real Möbius action has nonzero complex derivative on $ℍ$. The chain rule makes their product nonzero.
-/
theorem hyperbolicLocalChart_realMobius_postcomp_coordinateExpressionAt_deriv_ne_zero
    {g : HyperbolicMetric X} (U : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) {x₀ : X} (hx₀ : x₀ ∈ U.domain) :
    deriv
      (fun z : ℂ =>
        (realMobiusRepresentativeAction A
          (U.toUpperHalfPlane ((chartAt ℂ x₀).symm z)) : ℂ))
      ((chartAt ℂ x₀) x₀) ≠ 0 := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let z₀ : ℂ := e x₀
  let F : ℂ → ℂ := fun z => (U.toUpperHalfPlane (e.symm z) : ℂ)
  let M : ℂ → ℂ := fun w =>
    (realMobiusRepresentativeAction A (UpperHalfPlane.ofComplex w) : ℂ)
  have hsymm_z₀ : e.symm z₀ = x₀ := by
    dsimp [z₀, e]
    exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
  have hF_point : F z₀ = (U.toUpperHalfPlane x₀ : ℂ) := by
    dsimp [F]
    rw [hsymm_z₀]
  have hF_diff : DifferentiableAt ℂ F z₀ := by
    simpa [F, e, z₀] using U.coordinateExpressionAt_differentiableAt hx₀
  have hM_diff :
      DifferentiableAt ℂ M (U.toUpperHalfPlane x₀ : ℂ) := by
    simpa [M] using
      realMobiusRepresentativeAction_differentiableAt A
        (U.toUpperHalfPlane x₀)
  have hF_deriv_ne : deriv F z₀ ≠ 0 := by
    have hne :=
      (hyperbolicLocalChart_pullbackSquaredDensityFormulaAt U hx₀).coordinateDerivative_ne_zero
        hx₀
    simpa [F, e, z₀, hyperbolicLocalChartCoordinateDerivativeAt] using hne
  have hM_deriv_ne : deriv M (U.toUpperHalfPlane x₀ : ℂ) ≠ 0 := by
    simpa [M] using
      realMobiusRepresentativeAction_standardChart_deriv_ne_zero A
        (U.toUpperHalfPlane x₀)
  have hchain :
      deriv
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane (e.symm z)) : ℂ))
        z₀ =
        deriv M (U.toUpperHalfPlane x₀ : ℂ) * deriv F z₀ := by
    have hcomp :=
      deriv_comp_of_eq z₀ hM_diff hF_diff hF_point
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
      _ = deriv M (U.toUpperHalfPlane x₀ : ℂ) * deriv F z₀ := by
            simpa [Function.comp_def, hF_point] using hcomp
  dsimp [e, z₀] at hchain
  rw [hchain]
  exact mul_ne_zero hM_deriv_ne hF_deriv_ne

/--
A local hyperbolic chart, after real-Mobius postcomposition, satisfies the
concrete chartwise pullback-metric identity at the base point.

This is the metric analogue of the local regularity lemmas above: the witness
is the actual ambient coordinate expression, restricted to the part of the
coordinate chart landing in the local-model domain.

%%handwave
name: A Möbius-transformed hyperbolic chart pulls back the Poincaré metric
statement: For a hyperbolic local chart $U$, real Möbius representative $A$, and $x∈U$, the map $z↦A·U(z)$ pulls the Poincaré conformal metric back to $g$ at $x$ in the ambient source chart and any target chart.
proof: The hyperbolic chart pulls the Poincaré metric back to $g$, while the real Möbius action preserves the Poincaré metric. Compose the two chartwise pullback identities.
-/
theorem hyperbolicLocalChart_realMobius_postcomp_pullsBackMetricInChartsAt_chartAt
    {g : HyperbolicMetric X} (U : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) {x₀ : X} (hx₀ : x₀ ∈ U.domain)
    (targetChart : OpenPartialHomeomorph ℍ ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ ℍ) :
    PullsBackMetricInChartsAt
      (fun x : X => realMobiusRepresentativeAction A (U.toUpperHalfPlane x))
      upperHalfPlaneConformalMetric g.toConformalMetric
      (chartAt ℂ x₀) (chart_mem_atlas ℂ x₀)
      targetChart targetChart_mem_atlas x₀ := by
  intro hx₀_source _himage
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let z₀ : ℂ := e x₀
  let c : OpenPartialHomeomorph ℍ ℂ :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      UpperHalfPlane.coe UpperHalfPlane.isOpenEmbedding_coe
  have htarget_eq : targetChart = c := by
    simpa [c] using targetChart_mem_atlas
  subst targetChart
  let localMap : ℂ → ℂ := fun z =>
    (realMobiusRepresentativeAction A
      (U.toUpperHalfPlane (e.symm z)) : ℂ)
  let coordDomain : Set ℂ := e.target ∩ e.symm ⁻¹' U.domain
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact e.map_source hx₀_source
  have hsymm_z₀ : e.symm z₀ = x₀ := by
    dsimp [z₀, e]
    exact e.left_inv hx₀_source
  refine
    ⟨coordDomain, localMap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e.isOpen_inter_preimage_symm U.isOpen_domain
  · refine ⟨hz₀_target, ?_⟩
    change e.symm z₀ ∈ U.domain
    rw [hsymm_z₀]
    exact hx₀
  · intro z hz
    exact hz.1
  · intro z hz
    exact e.map_target hz.1
  · intro z _hz
    simp
  · intro z _hz
    simpa [localMap, c] using
      (mem_chart_target ℂ
        (realMobiusRepresentativeAction A
          (U.toUpperHalfPlane (e.symm z))))
  · intro z _hz
    simp [localMap, e]
  · simpa [localMap, e, z₀] using
      U.realMobius_postcomp_coordinateExpressionAt_differentiableAt A hx₀
  · let F : ℂ → ℂ := fun z => (U.toUpperHalfPlane (e.symm z) : ℂ)
    let M : ℂ → ℂ := fun w =>
      (realMobiusRepresentativeAction A (UpperHalfPlane.ofComplex w) : ℂ)
    let p : ℍ := U.toUpperHalfPlane x₀
    have hF_point : F z₀ = (p : ℂ) := by
      dsimp [F, p]
      rw [hsymm_z₀]
    have hF_diff : DifferentiableAt ℂ F z₀ := by
      simpa [F, e, z₀] using U.coordinateExpressionAt_differentiableAt hx₀
    have hM_diff : DifferentiableAt ℂ M (p : ℂ) := by
      simpa [M, p] using realMobiusRepresentativeAction_differentiableAt A p
    have hchain :
        deriv localMap z₀ = deriv M (p : ℂ) * deriv F z₀ := by
      have hcomp := deriv_comp_of_eq z₀ hM_diff hF_diff hF_point
      calc
        deriv localMap z₀ = deriv (fun z : ℂ => M (F z)) z₀ := by
          congr 1
          ext z
          simp [localMap, M, F]
        _ = deriv M (p : ℂ) * deriv F z₀ := by
          simpa [Function.comp_def, hF_point] using hcomp
    have hnorm :
        Complex.normSq (deriv localMap z₀) =
          Complex.normSq (deriv M (p : ℂ)) *
            Complex.normSq (deriv F z₀) := by
      rw [hchain]
      exact Complex.normSq_mul _ _
    have hlocalPull := hyperbolicLocalChart_pullbackSquaredDensityFormulaAt U hx₀
    have hsource :
        g.toConformalMetric.densitySqInChart e (chart_mem_atlas ℂ x₀) z₀ =
          ((p : ℂ).im ^ 2)⁻¹ * Complex.normSq (deriv F z₀) := by
      calc
        g.toConformalMetric.densitySqInChart e (chart_mem_atlas ℂ x₀) z₀ =
            Complex.normSq (deriv F z₀) / ((p : ℂ).im ^ 2) := by
          simpa [F, e, z₀, p, hyperbolicLocalChartCoordinateDerivativeAt,
            hyperbolicLocalChartCoordinateExpressionAt,
            hyperbolicLocalChartCoordinateDensitySqAt] using hlocalPull.symm
        _ = ((p : ℂ).im ^ 2)⁻¹ * Complex.normSq (deriv F z₀) := by
          rw [div_eq_mul_inv, mul_comm]
    have hmobius :
        ((p : ℂ).im ^ 2)⁻¹ =
          ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
            Complex.normSq (deriv M (p : ℂ)) := by
      have hmetric := realMobiusRepresentativeAction_deriv_hyperbolicNormSq A p
      calc
        ((p : ℂ).im ^ 2)⁻¹ =
            Complex.normSq (deriv M (p : ℂ)) /
              ((realMobiusRepresentativeAction A p : ℂ).im ^ 2) := by
          simpa [one_div, M] using hmetric.symm
        _ =
            ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
              Complex.normSq (deriv M (p : ℂ)) := by
          rw [div_eq_mul_inv, mul_comm]
    have hmetric_final :
        g.toConformalMetric.densitySqInChart e (chart_mem_atlas ℂ x₀) z₀ =
          ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
            Complex.normSq (deriv localMap z₀) := by
      calc
        g.toConformalMetric.densitySqInChart e (chart_mem_atlas ℂ x₀) z₀ =
            ((p : ℂ).im ^ 2)⁻¹ * Complex.normSq (deriv F z₀) := hsource
        _ =
            (((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
                Complex.normSq (deriv M (p : ℂ))) *
              Complex.normSq (deriv F z₀) := by
          rw [hmobius]
        _ =
            ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
              (Complex.normSq (deriv M (p : ℂ)) *
                Complex.normSq (deriv F z₀)) := by
          ring
        _ =
            ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
              Complex.normSq (deriv localMap z₀) := by
          rw [hnorm]
    simpa [upperHalfPlaneConformalMetric, poincareDensitySqInChart,
      localMap, e, z₀, p, hsymm_z₀, c] using hmetric_final

/--
An analytic one-variable complex map with nonzero derivative has the concrete
local-homeomorphism branch data required by developing-map regularity.

%%handwave
name: A holomorphic function with nonzero derivative has a local biholomorphic branch
statement: Let $f:ℂ→ℂ$ be analytic at $z_0$, with $f′(z_0)≠0$, and let $S$ be a neighborhood of $z_0$. Then there is an open partial homeomorphism branch through $z_0$, contained in $S$, equal to $f$ on its source, differentiable there, and with nonzero derivative throughout.
proof: Apply the holomorphic inverse function theorem at $z_0$, then shrink the source by intersecting with $S$ and with a neighborhood on which the derivative remains nonzero.
-/
theorem analyticAt_local_biholomorphism_branch
    {f : ℂ → ℂ} {z₀ : ℂ} {S : Set ℂ}
    (hf : AnalyticAt ℂ f z₀) (hderiv : deriv f z₀ ≠ 0)
    (hS : S ∈ nhds z₀) :
    ∃ branch : OpenPartialHomeomorph ℂ ℂ,
      z₀ ∈ branch.source ∧
        branch.source ⊆ S ∧
        ∀ z ∈ branch.source,
          branch z = f z ∧ DifferentiableAt ℂ branch z ∧ deriv branch z ≠ 0 := by
  classical
  let hstrict : HasStrictDerivAt f (deriv f z₀) z₀ :=
    hf.hasStrictDerivAt
  let e₀ : OpenPartialHomeomorph ℂ ℂ :=
    (hstrict.hasStrictFDerivAt_equiv hderiv).toOpenPartialHomeomorph f
  have hz₀e₀ : z₀ ∈ e₀.source :=
    (hstrict.hasStrictFDerivAt_equiv hderiv).mem_toOpenPartialHomeomorph_source
  have hdiff_event :
      ∀ᶠ z in nhds z₀, DifferentiableAt ℂ f z :=
    hf.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hderiv_event :
      ∀ᶠ z in nhds z₀, deriv f z ≠ 0 :=
    hf.deriv.continuousAt.eventually_ne hderiv
  rcases mem_nhds_iff.mp hS with ⟨S₀, hS₀_sub, hS₀_open, hz₀S₀⟩
  rcases eventually_nhds_iff.mp (hdiff_event.and hderiv_event) with
    ⟨W, hW, hWopen, hz₀W⟩
  let branch : OpenPartialHomeomorph ℂ ℂ := e₀.restrOpen (W ∩ S₀) (hWopen.inter hS₀_open)
  refine ⟨branch, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hz₀e₀, hz₀W, hz₀S₀⟩
  · intro z hz
    have hz' : z ∈ e₀.source ∩ (W ∩ S₀) := by
      simpa [branch, OpenPartialHomeomorph.restrOpen_source] using hz
    exact hS₀_sub hz'.2.2
  · intro z hz
    have hz' : z ∈ e₀.source ∩ (W ∩ S₀) := by
      simpa [branch, OpenPartialHomeomorph.restrOpen_source] using hz
    have hz_props := hW z hz'.2.1
    refine ⟨?_, ?_, ?_⟩
    · simp [branch, e₀]
    · simpa [branch, e₀] using hz_props.1
    · simpa [branch, e₀] using hz_props.2

/--
On the canonical path-homotopy cover, local agreement with local-transition
models makes the developing-map coordinate expression analytic at every point.

%%handwave
name: Local-transition agreement makes each developing coordinate expression analytic
statement: If $dev$ on the canonical cover agrees locally with local-transition hyperbolic charts, then for every lift $y$ its complex coordinate expression is analytic at the source coordinate of $y$.
proof: On a neighborhood of $y$, replace $dev$ by a Möbius-transformed local hyperbolic chart after projection. This composite is analytic in the canonical coordinates, and local equality transfers analyticity.
-/
theorem canonicalLocalTransitionAgreement_dev_coordinateExpression_analyticAt
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev)
    (y : (canonicalContinuationCover x₀).total) :
    AnalyticAt ℂ
      (HyperbolicDevelopingMapCoordinateExpression
        (canonicalContinuationCover x₀) dev y)
      ((chartAt ℂ y) y) := by
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let e : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ :=
    chartAt ℂ y
  let z₀ : ℂ := e y
  let xᵧ : X := (canonicalContinuationCover x₀).projection y
  let b : OpenPartialHomeomorph X ℂ := chartAt ℂ xᵧ
  let localExpr : ℂ → ℂ := fun z =>
    (realMobiusRepresentativeAction A
      ((localModels.chartAt x).toUpperHalfPlane (b.symm z)) : ℂ)
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ y
  have hsymm_z₀ : e.symm z₀ = y := by
    dsimp [z₀, e]
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hy_domain : xᵧ ∈ (localModels.chartAt x).domain := by
    dsimp [xᵧ]
    exact hdomain y hyU
  have hz₀_base :
      z₀ = b xᵧ := by
    dsimp [z₀, e, xᵧ, b, canonicalContinuationCover]
    exact
      PathHomotopyUniversalCover.chartAt_apply_eq_chartAt_endpoint_apply
        (x₀ := x₀) y y (mem_chart_source ℂ y)
  have hbtarget : b xᵧ ∈ b.target := by
    dsimp [b]
    exact mem_chart_target ℂ xᵧ
  have hb_symm :
      b.symm (b xᵧ) = xᵧ := by
    dsimp [b]
    exact (chartAt ℂ xᵧ).left_inv (mem_chart_source ℂ xᵧ)
  let s : Set ℂ := b.target ∩ b.symm ⁻¹' (localModels.chartAt x).domain
  have hs_nhds : s ∈ nhds z₀ := by
    have htarget : b.target ∈ nhds (b xᵧ) :=
      b.open_target.mem_nhds hbtarget
    have hpre :
        b.symm ⁻¹' (localModels.chartAt x).domain ∈ nhds (b xᵧ) :=
      (b.continuousAt_symm hbtarget).preimage_mem_nhds
        (by simpa [hb_symm] using
          (localModels.chartAt x).isOpen_domain.mem_nhds hy_domain)
    simpa [s, hz₀_base] using Filter.inter_mem htarget hpre
  have hlocal_diffOn : DifferentiableOn ℂ localExpr s := by
    intro z hz
    have hz_target : z ∈ b.target := hz.1
    have hz_domain : b.symm z ∈ (localModels.chartAt x).domain := hz.2
    exact
      ((localModels.chartAt x).realMobius_postcomp_coordinateExpression_differentiableAt
        A b (chart_mem_atlas ℂ xᵧ) hz_target hz_domain).differentiableWithinAt
  have hlocal_analytic : AnalyticAt ℂ localExpr z₀ :=
    hlocal_diffOn.analyticAt hs_nhds
  have hUpre : e.symm ⁻¹' U ∈ nhds z₀ :=
    (e.continuousAt_symm hz₀_target).preimage_mem_nhds
      (by simpa [hsymm_z₀] using hUopen.mem_nhds hyU)
  have htarget : e.target ∈ nhds z₀ :=
    e.open_target.mem_nhds hz₀_target
  have heq :
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y =ᶠ[nhds z₀]
        localExpr := by
    filter_upwards [htarget, hUpre] with z hz_target hzU
    have hprojection :
        (canonicalContinuationCover x₀).projection (e.symm z) =
          b.symm z := by
      dsimp [e, b, xᵧ, canonicalContinuationCover]
      exact
        PathHomotopyUniversalCover.endpoint_chartAt_symm_eq_chartAt_endpoint_symm
          (x₀ := x₀) y hz_target
    calc
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y z =
          (dev (e.symm z) : ℂ) := by
        rfl
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((canonicalContinuationCover x₀).projection (e.symm z))) : ℂ) := by
        rw [hagree (e.symm z) hzU]
      _ = localExpr z := by
        dsimp [localExpr]
        rw [hprojection]
  exact hlocal_analytic.congr heq.symm

/--
On the canonical path-homotopy cover, local agreement with local-transition
models forces chartwise holomorphicity of the continued map.

%%handwave
name: Local-transition agreement makes the developing map holomorphic
statement: If $dev$ on the canonical cover agrees locally with local-transition models, then its coordinate expression is complex differentiable at every lift.
proof: Analyticity of the coordinate expression at each lift implies the required pointwise complex differentiability.
-/
theorem canonicalLocalTransitionAgreement_dev_holomorphic
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) dev := by
  intro y
  simpa [HyperbolicDevelopingMapCoordinateExpression] using
    (canonicalLocalTransitionAgreement_dev_coordinateExpression_analyticAt h y).differentiableAt

/--
On the canonical path-homotopy cover, local agreement with local-transition
models forces the nonzero-derivative part of developing-map regularity.

%%handwave
name: Local-transition agreement gives a nonvanishing developing derivative
statement: If $dev$ agrees locally with local-transition hyperbolic models on the canonical cover, then its coordinate derivative is nonzero at every lift.
proof: Use the local equality with a Möbius-transformed hyperbolic chart and the nonzero derivative of that model expression.
-/
theorem canonicalLocalTransitionAgreement_dev_local_biholomorphic
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapLocallyBiholomorphic
      (canonicalContinuationCover x₀) dev := by
  intro y
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let e : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ :=
    chartAt ℂ y
  let z₀ : ℂ := e y
  let xᵧ : X := (canonicalContinuationCover x₀).projection y
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ y
  have hsymm_z₀ : e.symm z₀ = y := by
    dsimp [z₀, e]
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hy_domain : xᵧ ∈ (localModels.chartAt x).domain := by
    dsimp [xᵧ]
    exact hdomain y hyU
  have hz₀_base :
      z₀ = (chartAt ℂ xᵧ) xᵧ := by
    dsimp [z₀, e, xᵧ, canonicalContinuationCover]
    exact
      PathHomotopyUniversalCover.chartAt_apply_eq_chartAt_endpoint_apply
        (x₀ := x₀) y y (mem_chart_source ℂ y)
  have hlocal_deriv_ne :
      deriv
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ))
        z₀ ≠ 0 := by
    have hlocal_base :=
      hyperbolicLocalChart_realMobius_postcomp_coordinateExpressionAt_deriv_ne_zero
        (localModels.chartAt x) A hy_domain
    simpa [hz₀_base] using hlocal_base
  have hUpre : e.symm ⁻¹' U ∈ nhds z₀ :=
    (e.continuousAt_symm hz₀_target).preimage_mem_nhds
      (by simpa [hsymm_z₀] using hUopen.mem_nhds hyU)
  have htarget : e.target ∈ nhds z₀ :=
    e.open_target.mem_nhds hz₀_target
  have heq :
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y =ᶠ[nhds z₀]
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ)) := by
    filter_upwards [htarget, hUpre] with z hz_target hzU
    have hprojection :
        (canonicalContinuationCover x₀).projection (e.symm z) =
          (chartAt ℂ xᵧ).symm z := by
      dsimp [e, xᵧ, canonicalContinuationCover]
      exact
        PathHomotopyUniversalCover.endpoint_chartAt_symm_eq_chartAt_endpoint_symm
          (x₀ := x₀) y hz_target
    calc
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y z =
          (dev (e.symm z) : ℂ) := by
        rfl
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((canonicalContinuationCover x₀).projection (e.symm z))) : ℂ) := by
        rw [hagree (e.symm z) hzU]
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ) := by
        rw [hprojection]
  have hderiv_eq :=
    Filter.EventuallyEq.deriv_eq heq
  rw [hderiv_eq]
  exact hlocal_deriv_ne

/--
On the canonical path-homotopy cover, local agreement with local-transition
models supplies the concrete local-homeomorphism branch data.

%%handwave
name: Local-transition agreement supplies local biholomorphic branches
statement: If $dev$ agrees locally with local-transition models, then around every lift its coordinate expression agrees with an open partial homeomorphism whose derivative is everywhere nonzero on the chosen source.
proof: Combine analytic coordinate expressions with their nonzero derivative and apply the analytic inverse-function branch theorem, shrinking inside the coordinate domain.
-/
theorem canonicalLocalTransitionAgreement_dev_local_biholomorphism_data
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapLocalBiholomorphismData
      (canonicalContinuationCover x₀) dev := by
  intro y
  exact analyticAt_local_biholomorphism_branch
    (canonicalLocalTransitionAgreement_dev_coordinateExpression_analyticAt h y)
    (canonicalLocalTransitionAgreement_dev_local_biholomorphic h y)
    ((chartAt ℂ y).open_target.mem_nhds (mem_chart_target ℂ y))

/--
On the canonical cover, local agreement with local-transition models gives the
actual chartwise pullback-metric identity for the continued developing map in
any source chart.

%%handwave
name: Local-transition agreement gives the metric identity in arbitrary coordinates
statement: Under local-transition model agreement, $dev$ pulls the Poincaré metric back to the canonical cover metric at every point in every compatible source and target chart.
proof: Establish the identity in the canonical source chart and transport it through a change of source chart within the complex atlas.
-/
theorem canonicalLocalTransitionAgreement_dev_pullsBackMetricInChartsAt
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev)
    (sourceChart : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ)
    (sourceChart_mem_atlas :
      sourceChart ∈ atlas ℂ (canonicalContinuationCover x₀).total)
    (targetChart : OpenPartialHomeomorph ℍ ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ ℍ)
    (y : (canonicalContinuationCover x₀).total) :
    PullsBackMetricInChartsAt dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g)
      sourceChart sourceChart_mem_atlas
      targetChart targetChart_mem_atlas y := by
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let localChart : HyperbolicLocalChart X g := localModels.chartAt x
  let localModelOnBase : X → ℍ := fun x' =>
    realMobiusRepresentativeAction A (localChart.toUpperHalfPlane x')
  let localModelOnCover : (canonicalContinuationCover x₀).total → ℍ := fun y' =>
    localModelOnBase ((canonicalContinuationCover x₀).projection y')
  have hy_domain :
      (canonicalContinuationCover x₀).projection y ∈ localChart.domain := by
    exact hdomain y hyU
  have hprojection_chart :
      (canonicalContinuationCover x₀).projection y ∈
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y)).source :=
    mem_chart_source ℂ ((canonicalContinuationCover x₀).projection y)
  have hbase :
      PullsBackMetricInChartsAt localModelOnBase upperHalfPlaneConformalMetric
        g.toConformalMetric
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        targetChart targetChart_mem_atlas
        ((canonicalContinuationCover x₀).projection y) := by
    simpa [localModelOnBase, localChart] using
      hyperbolicLocalChart_realMobius_postcomp_pullsBackMetricInChartsAt_chartAt
        (X := X) localChart A hy_domain targetChart targetChart_mem_atlas
  have hprojection_pullback :
      PullsBackMetricInChartsAt
        (canonicalContinuationCover x₀).projection
        g.toConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        sourceChart sourceChart_mem_atlas
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        y :=
    (canonicalContinuationCoverMetric_pullback x₀ g).in_charts_at
      sourceChart sourceChart_mem_atlas
      (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
      (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
      y
  have hlocalModel :
      PullsBackMetricInChartsAt localModelOnCover upperHalfPlaneConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        sourceChart sourceChart_mem_atlas
        targetChart targetChart_mem_atlas y := by
    simpa [localModelOnCover, localModelOnBase] using
      PullsBackMetricInChartsAt.comp
        (F := localModelOnBase)
        (G := (canonicalContinuationCover x₀).projection)
        hprojection_chart hbase hprojection_pullback
  have heq : localModelOnCover =ᶠ[nhds y] dev := by
    filter_upwards [hUopen.mem_nhds hyU] with y' hy'
    exact (hagree y' hy').symm
  exact PullsBackMetricInChartsAt.congr_of_eventuallyEq_nhds hlocalModel heq

/--
%%handwave
name:
  Metric recovery for the continued developing map
statement:
  Let $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$ locally have the
  form $A\cdot F\circ\pi$, where $A\in\mathrm{PSL}_2(\mathbb R)$ and each
  local branch $F$ satisfies $F^{*}g_{\mathbb H}=g$. Then
  $\operatorname{dev}^{*}g_{\mathbb H}=\pi^{*}g$ on
  $\widetilde X_{x_0}$.
proof:
  Work in arbitrary source and target charts and substitute the local formula
  for $\operatorname{dev}$. Real Möbius transformations preserve
  $g_{\mathbb H}$, and the local pullback identity for $F$ leaves the
  conformal factor of $\pi^{*}g$; locality then gives the global identity.
-/
theorem canonicalLocalTransitionAgreement_dev_pullsBackMetric
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    PullsBackMetric dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) where
  in_charts := by
    intro sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas y
    exact canonicalLocalTransitionAgreement_dev_pullsBackMetricInChartsAt
      h sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas y

/--
On the canonical path-homotopy cover, local agreement with local-transition
models supplies the full developing-map regularity package.

%%handwave
name: Local-transition agreement supplies full developing-map regularity
statement: If $dev$ on the canonical cover agrees locally with local-transition hyperbolic models, then it is continuous and holomorphic, has nonzero derivative everywhere, and admits explicit local biholomorphic branches.
proof: Assemble continuity from local agreement, coordinate analyticity, derivative nonvanishing, and the local inverse branches into the regularity record.
-/
theorem canonicalLocalTransitionAgreement_dev_regular
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) dev where
  continuous := h.continuous
  chartwise_holomorphic := canonicalLocalTransitionAgreement_dev_holomorphic h
  local_biholomorphic := canonicalLocalTransitionAgreement_dev_local_biholomorphic h
  local_biholomorphism_data :=
    canonicalLocalTransitionAgreement_dev_local_biholomorphism_data h

namespace HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity

/--
PSL-valued local-transition continuation fields on the canonical cover.

This is the natural continuation endpoint for projective holonomy: analytic
continuation supplies a single-valued developing map, a real projective
holonomy representation, deck equivariance for the PSL action on `ℍ`, and
local agreement with the selected local-transition models.  Regularity and
metric recovery are derived from local agreement.
-/
structure HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- Real projective holonomy obtained by monodromy of the local-transition models. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Equivariance with respect to deck transformations and PSL holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomy.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local-transition models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Local-transition model agreement supplies the pullback metric identity.

%%handwave
name: Projective local-transition regularity includes the metric pullback
statement: For such a projective package, $dev^*g_{ℍ}$ is the canonical cover metric.
proof: Apply the metric identity derived from the package’s local model agreement.
-/
theorem pullback_metric
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    PullsBackMetric F.dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  canonicalLocalTransitionAgreement_dev_pullsBackMetric F.agrees_with_local_models

/-- Local-transition model agreement assembles the full regularity record.

%%handwave
name: Local-transition model agreement assembles the full regularity data
statement:
  Local agreement with Möbius transforms of hyperbolic charts makes the
  continued map continuous and holomorphic, with nonzero derivative and a
  local biholomorphic branch at every cover point.
-/
def dev_regular
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_regular F.agrees_with_local_models

/-- PSL-valued reduced fields fold directly into the ordinary developing-map record.

%%handwave
name: PSL-valued reduced fields fold directly into the ordinary developing-map data
statement:
  A continued map on the canonical cover with local-model agreement and
  $\mathrm{PSL}_2(\mathbb R)$-equivariance determines a hyperbolic developing
  map with the pulled-back cover metric, derived regularity, holonomy, and
  metric-pullback identity.
-/
def toHyperbolicDevelopingMap
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    HyperbolicDevelopingMap X x₀ g where
  cover := canonicalContinuationCover x₀
  dev := F.dev
  coverMetric := canonicalContinuationCoverMetric x₀ g
  coverMetric_pullback := canonicalContinuationCoverMetric_pullback x₀ g
  dev_regular := F.dev_regular
  holonomy := F.holonomy
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant

end HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL

/--
Local sheetwise continuation data on the canonical cover for a
local-transition atlas.

This is the componentwise-overlap analogue of
`CanonicalCoverLocalContinuationData`: every sheet is explicitly one selected
upper-half-plane local model, postcomposed by a real Mobius representative.
-/
structure CanonicalCoverLocalTransitionContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The single-valued map obtained by continuing local models to the cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- The local model used near a point of the cover. -/
  centerAt : (canonicalContinuationCover x₀).total → X
  /-- The real Mobius postcomposition relating the branch to the chosen model. -/
  mobiusAt : (canonicalContinuationCover x₀).total → RealMobiusRepresentative
  /-- A cover-neighborhood on which the displayed branch formula is valid. -/
  neighborhoodAt :
    (canonicalContinuationCover x₀).total →
      Set (canonicalContinuationCover x₀).total
  /-- The branch formula holds on an open neighborhood. -/
  isOpen_neighborhoodAt :
    ∀ y, IsOpen (neighborhoodAt y)
  /-- The neighborhood is centered at the requested point. -/
  mem_neighborhoodAt :
    ∀ y, y ∈ neighborhoodAt y
  /-- Points in the sheet project into the domain of the selected local model. -/
  projection_mem_model_domain :
    ∀ y y', y' ∈ neighborhoodAt y →
      (canonicalContinuationCover x₀).projection y' ∈
        (localModels.chartAt (centerAt y)).domain
  /-- On each sheet, the continued map is the selected model up to real Mobius action. -/
  dev_eq_on_neighborhood :
    ∀ y y', y' ∈ neighborhoodAt y →
      dev y' =
        realMobiusRepresentativeAction (mobiusAt y)
          ((localModels.chartAt (centerAt y)).toUpperHalfPlane
            ((canonicalContinuationCover x₀).projection y'))

namespace CanonicalCoverLocalTransitionContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
The sheetwise local-transition continuation boundary supplies the local
agreement predicate consumed by the regularity and metric-pullback derivations.

%%handwave
name: The sheetwise local-transition continuation principle supplies the local agreement predicate consumed by the regularity and metric-pullback derivations
statement:
  If each cover point $y$ has an open sheet on which the continued map equals
  $A_y\circ U_y\circ\pi$, then the continued map locally agrees everywhere
  with the selected local-transition atlas.
-/
def agreesWithLocalTransitionModels
    (C : CanonicalCoverLocalTransitionContinuationData x₀ g localModels) :
    HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
      (canonicalContinuationCover x₀) C.dev := by
  intro y
  refine ⟨C.neighborhoodAt y, C.isOpen_neighborhoodAt y,
    C.mem_neighborhoodAt y, C.centerAt y, C.mobiusAt y, ?_, ?_⟩
  · exact C.projection_mem_model_domain y
  · exact C.dev_eq_on_neighborhood y

end CanonicalCoverLocalTransitionContinuationData

namespace LocalTransitionAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end LocalTransitionAnalyticContinuationMonodromyData

/--
Analytic continuation indexed by endpoint and path-homotopy class for a
local-transition atlas.

This is the componentwise-overlap analogue of
`PathClassAnalyticContinuationData`.  The stored local sheet formula only asks
for a selected local model and a real Mobius postcomposition near each point
of the path-homotopy cover; regularity and metric recovery are derived later
from these formulas.
-/
structure PathClassLocalTransitionAnalyticContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The continued value associated to an endpoint and path-homotopy class. -/
  valueAt : ∀ x : X, Path.Homotopic.Quotient x₀ x → ℍ
  /-- The selected local model controlling the branch near this path class. -/
  centerAt : ∀ x : X, Path.Homotopic.Quotient x₀ x → X
  /-- The real Mobius postcomposition relating the branch to the selected model. -/
  mobiusAt :
    ∀ x : X, Path.Homotopic.Quotient x₀ x → RealMobiusRepresentative
  /--
  A neighborhood of the corresponding path-homotopy-cover point on which the
  branch formula is valid.
  -/
  neighborhoodAt :
    ∀ x : X, Path.Homotopic.Quotient x₀ x →
      Set (PathHomotopyUniversalCover X x₀)
  /-- The branch neighborhood is open in the path-homotopy cover. -/
  isOpen_neighborhoodAt :
    ∀ x q, IsOpen (neighborhoodAt x q)
  /-- The branch neighborhood contains the path-class point it describes. -/
  mem_neighborhoodAt :
    ∀ x q, (⟨x, q⟩ : PathHomotopyUniversalCover X x₀) ∈ neighborhoodAt x q
  /-- Points in the branch neighborhood project into the selected model domain. -/
  endpoint_mem_model_domain :
    ∀ x q y', y' ∈ neighborhoodAt x q →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt (centerAt x q)).domain
  /--
  On the branch neighborhood, path-class values are the selected local model up
  to real Mobius action.
  -/
  value_eq_on_neighborhood :
    ∀ x q y', y' ∈ neighborhoodAt x q →
      valueAt (PathHomotopyUniversalCover.endpoint y')
          (PathHomotopyUniversalCover.pathClass y') =
        realMobiusRepresentativeAction (mobiusAt x q)
          ((localModels.chartAt (centerAt x q)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

namespace PathClassLocalTransitionAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The cover-level developing map determined by path-class continuation data.

%%handwave
name: The cover-level developing map determined by path-class continuation data
statement:
  For a cover point $(x,[p])$, define the continued map by the path-class
  value $\operatorname{dev}(x,[p])=V(x,[p])$.
-/
def dev
    (C :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  fun y =>
    C.valueAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/--
Path-class local-transition continuation data fold into the sheetwise
continuation data on the canonical cover.

%%handwave
name: Path-class local-transition continuation data fold into the sheetwise continuation data on the canonical cover
statement:
  Path-class continuation values, terminal centers, accumulated Möbius
  transformations, and continuation neighborhoods define the corresponding
  single-valued fields on the canonical cover by evaluation at $(x,[p])$.
-/
def toCanonicalCoverLocalTransitionContinuationData
    (C :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels) :
    CanonicalCoverLocalTransitionContinuationData x₀ g localModels where
  dev := C.dev
  centerAt := fun y =>
    C.centerAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  mobiusAt := fun y =>
    C.mobiusAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  neighborhoodAt := fun y =>
    C.neighborhoodAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  isOpen_neighborhoodAt := by
    intro y
    exact C.isOpen_neighborhoodAt
      (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  mem_neighborhoodAt := by
    intro y
    exact C.mem_neighborhoodAt
      (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  projection_mem_model_domain := by
    intro y y' hy'
    simpa [canonicalContinuationCover] using
      C.endpoint_mem_model_domain
        (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) y' hy'
  dev_eq_on_neighborhood := by
    intro y y' hy'
    simpa [dev, canonicalContinuationCover] using
      C.value_eq_on_neighborhood
        (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) y' hy'

end PathClassLocalTransitionAnalyticContinuationData


/--
PSL-valued path-class monodromy data for a local-transition atlas.
-/
structure PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Continuation data indexed by path-homotopy classes. -/
  pathClassContinuation :
    PathClassLocalTransitionAnalyticContinuationData x₀ g localModels
  /-- PSL-valued real holonomy obtained from monodromy around loops. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Loop action on path classes matches the PSL action on continued values. -/
  pathClass_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (x : X)
      (q : Path.Homotopic.Quotient x₀ x),
      pathClassContinuation.valueAt x
          (Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹) q) =
        holonomy.upperHalfPlaneAction γ
          (pathClassContinuation.valueAt x q)


namespace PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
PSL path-class monodromy data give the PSL-valued reduced continuation fields
on the canonical cover.

%%handwave
name: PSL path-class monodromy data give the PSL-valued reduced continuation fields on the canonical cover
statement:
  A path-class continuation satisfying
  $V(x,\gamma^{-1}\!\cdot[p])=\rho(\gamma)V(x,[p])$ yields a continued map
  on the canonical cover equivariant under deck transformations by the real
  projective holonomy $\rho$.
-/
def toDerivedRegularityFieldsPSL
    (M :
      PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
        x₀ g localModels) :
    HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
      x₀ g localModels where
  dev := M.pathClassContinuation.dev
  holonomy := M.holonomy
  equivariant := by
    intro γ y
    simpa [PathClassLocalTransitionAnalyticContinuationData.dev,
      canonicalContinuationCover, SimplyConnectedCover.deckAction,
      PathHomotopyUniversalCover.deckHomeomorphism_apply,
      PathHomotopyUniversalCover.deckAction,
      PathHomotopyUniversalCover.endpoint,
      PathHomotopyUniversalCover.pathClass] using
      M.pathClass_equivariant γ (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y)
  agrees_with_local_models :=
    M.pathClassContinuation.toCanonicalCoverLocalTransitionContinuationData
      |>.agreesWithLocalTransitionModels

end PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end HyperbolicMetric

end

end JJMath
