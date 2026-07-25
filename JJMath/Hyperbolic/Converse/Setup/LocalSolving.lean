import JJMath.Hyperbolic.Converse.Setup.Statements

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
Surface-domain openness for one chosen Liouville metric formula atlas.

This is the pointwise version of
`SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem`.

%%handwave
name: Surface-domain openness for one chosen Liouville metric formula atlas
statement:
  For every choice of local real Liouville branches in a fixed metric-formula
  atlas and every center $x$, the surface points whose formula coordinates
  lie in the selected branch domain form an open subset of $X$.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) : Prop :=
  ∀ (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor),
    ∀ x : X, IsOpen
      {y : X | y ∈ (metricFormulaAtlas.formulaAt x).domain ∧
        (metricFormulaAtlas.formulaAt x).coordinate y ∈
          ((realBranchAtlasAt x).branchNear
            ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
              (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
                (metricFormulaAtlas.mem_formulaAt_domain x)⟩).domain}

/--
Pointwise chart-compatibility predicate for a chosen Liouville metric formula
atlas.

%%handwave
name: Pointwise chart-compatibility predicate for a chosen Liouville metric formula atlas
statement:
  A local Liouville metric-formula atlas is chart-compatible when, at every
  center $x$, its formula domain lies in the ambient chart domain and its
  coordinate agrees there with the ambient complex chart at $x$.
-/
def LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) : Prop :=
  ∀ x : X,
    (metricFormulaAtlas.formulaAt x).domain ⊆ (chartAt ℂ x).source ∧
      Set.EqOn (metricFormulaAtlas.formulaAt x).coordinate
        (chartAt ℂ x) (metricFormulaAtlas.formulaAt x).domain

/--
The charted curvature expansion carried by a hyperbolic metric.

For each point we use the ambient chart `chartAt ℂ x` and the logarithmic
density `logDensityFromDensitySq` of the metric in that chart.  The stored
smoothness of the metric gives the required regularity of the logarithmic
density, positivity gives `exp (2u) = densitySq`, and
`g.curvature_minus_one` is exactly the local curvature equation for this
choice of `u`.

%%handwave
name: The charted curvature expansion carried by a hyperbolic metric
statement:
  At $x\in X$, use the ambient complex chart $\varphi_x$ and the logarithmic
  conformal density $u=\frac12\log\rho_g^2$ to define the local curvature
  formula for $g$. Positivity gives $e^{2u}=\rho_g^2$, and $K_g=-1$ gives
  the corresponding Liouville equation.
-/
noncomputable def localCurvatureMetricFormulaInChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) (x : X) :
    LocalCurvatureMetricFormula X g where
  domain := (chartAt ℂ x).source
  isOpen_domain := (chartAt ℂ x).open_source
  coordinate := chartAt ℂ x
  chart := chartAt ℂ x
  chart_mem_atlas := chart_mem_atlas ℂ x
  domain_subset_chart_source := fun _ hy ↦ hy
  coordinate_eq_chart := fun _ _ ↦ rfl
  conformalFactor :=
    let ρ : ℂ → ℝ :=
      g.toConformalMetric.densitySqInChart
        (chartAt ℂ x) (chart_mem_atlas ℂ x)
    { coordinateDomain := (chartAt ℂ x).target
      isOpen_coordinateDomain := (chartAt ℂ x).open_target
      logDensity := logDensityFromDensitySq ρ
      logDensity_contDiffOn := by
        have hρ : ContDiffOn ℝ ⊤ ρ ((chartAt ℂ x).target) :=
          g.smooth (chartAt ℂ x) (chart_mem_atlas ℂ x)
        have hlog :
            ContDiffOn ℝ ⊤ (fun z : ℂ ↦ Real.log (ρ z))
              ((chartAt ℂ x).target) :=
          hρ.log (fun z hz ↦
            ne_of_gt
              (g.toConformalMetric.positive_densitySqInChart
                (chartAt ℂ x) (chart_mem_atlas ℂ x) hz))
        have hlogDiv :
            ContDiffOn ℝ ⊤ (fun z : ℂ ↦ Real.log (ρ z) / 2)
              ((chartAt ℂ x).target) :=
          hlog.div_const 2
        simpa [logDensityFromDensitySq] using hlogDiv.of_le le_top
      twice_differentiable_on_domain := by
        have hρ : ContDiffOn ℝ ⊤ ρ ((chartAt ℂ x).target) :=
          g.smooth (chartAt ℂ x) (chart_mem_atlas ℂ x)
        have hlog :
            ContDiffOn ℝ ⊤ (fun z : ℂ ↦ Real.log (ρ z))
              ((chartAt ℂ x).target) :=
          hρ.log (fun z hz ↦
            ne_of_gt
              (g.toConformalMetric.positive_densitySqInChart
                (chartAt ℂ x) (chart_mem_atlas ℂ x) hz))
        have hlogDiv :
            ContDiffOn ℝ ⊤ (fun z : ℂ ↦ Real.log (ρ z) / 2)
              ((chartAt ℂ x).target) :=
          hlog.div_const 2
        simpa [logDensityFromDensitySq] using hlogDiv.of_le le_top }
  coordinate_mem_conformalFactor_domain := by
    intro y hy
    exact (chartAt ℂ x).map_source hy
  curvature_minus_one := by
    intro z hz
    change
      gaussianCurvatureOfDensitySq
        (g.toConformalMetric.densitySqInChart
          (chartAt ℂ x) (chart_mem_atlas ℂ x)) z = -1
    simpa [ConformalMetric.gaussianCurvatureInChart] using
      g.curvature_minus_one (chartAt ℂ x) (chart_mem_atlas ℂ x) z hz
  densitySqInChart_eq_conformalFactor := by
    intro y hy
    let ρ : ℂ → ℝ :=
      g.toConformalMetric.densitySqInChart
        (chartAt ℂ x) (chart_mem_atlas ℂ x)
    have htarget : (chartAt ℂ x) y ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source hy
    have hpos : 0 < ρ ((chartAt ℂ x) y) :=
      g.toConformalMetric.positive_densitySqInChart
        (chartAt ℂ x) (chart_mem_atlas ℂ x) htarget
    have hlog :
        ρ ((chartAt ℂ x) y) =
          Real.exp (Real.log (ρ ((chartAt ℂ x) y))) :=
      (Real.exp_log hpos).symm
    calc
      ρ ((chartAt ℂ x) y)
          = Real.exp (Real.log (ρ ((chartAt ℂ x) y))) := hlog
      _ = Real.exp (2 * (Real.log (ρ ((chartAt ℂ x) y)) / 2)) := by
            ring_nf

/-- The curvature formula atlas obtained from the ambient complex charts.

%%handwave
name: The curvature formula atlas obtained from the ambient complex charts
statement:
  Assigning to each $x\in X$ the curvature formula built from the ambient
  chart $\varphi_x$ and the conformal density of $g$ defines a local
  Liouville metric-formula atlas for $g$.
-/
noncomputable def localCurvatureMetricFormulaAtlasInChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) :
    LocalCurvatureMetricFormulaAtlas X g where
  formulaAt x := localCurvatureMetricFormulaInChartAt g x
  mem_formulaAt_domain x := mem_chart_source ℂ x

/--
%%handwave
name: Openness of coordinate preimages on a formula domain
statement:
  Let $U$ be open and contained in the source of a chart $\phi$, and suppose a coordinate map $\psi$ agrees with $\phi$ on $U$. For every open $V\subseteq\mathbb C$, the set $\{y\in U:\psi(y)\in V\}$ is open.
proof:
  The chart is continuous on its source, hence $\psi$ is continuous on $U$ by the pointwise equality. The intersection of the open set $U$ with the inverse image of $V$ is therefore open.
-/
theorem isOpen_formulaCoordinate_preimage_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} {U : Set X} (hU : IsOpen U)
    {coordinate : X → ℂ}
    (hSub : U ⊆ (chartAt ℂ x).source)
    (hEq : Set.EqOn coordinate (chartAt ℂ x) U)
    {V : Set ℂ} (hV : IsOpen V) :
    IsOpen {y : X | y ∈ U ∧ coordinate y ∈ V} := by
  have hCont : ContinuousOn coordinate U :=
    ((chartAt ℂ x).continuousOn_toFun.mono hSub).congr hEq
  simpa [Set.preimage, Set.inter_def] using
    hCont.isOpen_inter_preimage hU hV

end HyperbolicMetric

end

end JJMath
