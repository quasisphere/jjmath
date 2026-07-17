import JJMath.PotentialTheory.EnergyMethod.WeakCorrection

/-!
# Energy method: Regularity

First variation, regularity upgrade, and assembly of Green functions.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization

/--
%%handwave
name:
  The cutoff model satisfies the punctured chart flux identity
statement:
  In every chart, the metric gradient flux of the logarithmic cutoff model
  satisfies the coordinate divergence integration-by-parts identity against
  every compactly supported test in the punctured chart region.
proof:
  The cutoff model is smooth on the punctured surface, so its coordinate
  representative is smooth on the punctured chart region.  Apply the local
  coordinate flux integration-by-parts theorem for the background metric.
-/
theorem logarithmicCutoffPoleModel_punctured_chart_flux_identity
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e {x : X | x ≠ p})) :
    ∫ z in surfaceChartRegion e {x : X | x ≠ p},
        (fderiv ℝ
            (fun w : ℂ ↦
              surfaceMetricGradientFluxInChart g.metric e φ.toFun w 0)
            z (1 : ℂ) +
          fderiv ℝ
            (fun w : ℂ ↦
              surfaceMetricGradientFluxInChart g.metric e φ.toFun w 1)
            z Complex.I) * η z =
      -∫ z in surfaceChartRegion e {x : X | x ≠ p},
        ∑ i : Fin 2,
          surfaceMetricGradientFluxInChart g.metric e φ.toFun z i *
            fderiv ℝ (η : ℂ → ℝ) z (complexCoordinateVector i) := by
  let Ω : Set ℂ := surfaceChartRegion e {x : X | x ≠ p}
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, surfaceChartRegion] using
      e.isOpen_inter_preimage_symm (isOpen_ne (x := p))
  have hΩ_subset : Ω ⊆ e.target := by
    intro z hz
    exact hz.1
  have hη_diff : ∀ z ∈ Ω, DifferentiableAt ℝ (η : ℂ → ℝ) z := by
    intro z _hz
    exact (η.smooth.differentiable (by simp)) z
  have hη_cont : ContinuousOn (η : ℂ → ℝ) Ω :=
    η.smooth.continuous.continuousOn
  have hDη_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (η : ℂ → ℝ) z
            (complexCoordinateVector i)) Ω := by
    intro i
    simpa using
      ((η.smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const).continuousOn
  simpa [Ω] using
    surfaceMetricGradientFluxInChart_integral_by_parts_of_local_contDiffOn
      g.metric e he φ.toFun hΩ_open hΩ_subset
      (by simpa [Ω, surfaceChartRegion] using φ.smooth_away_pole e he)
      (η : ℂ → ℝ) η.support_subset η.compact_support
      hη_diff hη_cont hDη_cont

/--
%%handwave
name:
  The cutoff weak-gradient chart integrand is the metric flux contraction
statement:
  On the punctured chart region, the density-weighted inverse-metric pairing
  of the cutoff model's exterior derivative with a coordinate test
  differential is the contraction of the metric gradient flux with that test
  differential.
proof:
  The cutoff model is smooth off the pole, so its exterior derivative in the
  chart is the ordinary derivative of its coordinate representative.  Expanding
  the inverse-metric contraction and using symmetry of the inverse Gram matrix
  gives the flux formula.
-/
theorem logarithmicCutoffPoleModel_punctured_chart_gradient_integrand_eq_flux
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e {x : X | x ≠ p}))
    {z : ℂ} (hz : z ∈ surfaceChartRegion e {x : X | x ≠ p}) :
    surfaceMetricWeakGradientCoordinatePairingInChart g e z
        (surfaceExteriorDerivative φ.toFun (e.symm z))
        (fderiv ℝ (η : ℂ → ℝ) z) *
          surfaceMetricVolumeDensityInChart g.metric e z =
      ∑ i : Fin 2,
        surfaceMetricGradientFluxInChart g.metric e φ.toFun z i *
          fderiv ℝ (η : ℂ → ℝ) z (complexCoordinateVector i) := by
  have hU_open : IsOpen {x : X | x ≠ p} :=
    isOpen_ne (x := p)
  have hz' : z ∈ e.target ∩ e.symm ⁻¹' {x : X | x ≠ p} := by
    simpa [surfaceChartRegion] using hz
  have hdf :
      ∀ i : Fin 2,
        surfaceExteriorDerivative φ.toFun (e.symm z)
            (surfaceChartTangentMap e z (complexCoordinateVector i)) =
          surfaceFunctionChartDerivativeComponent e φ.toFun z i := by
    intro i
    exact
      surfaceExteriorDerivative_apply_chartTangentMap_of_isSmoothOnSurface_open
        hU_open e he φ.toFun φ.smooth_away_pole z hz'
        (complexCoordinateVector i)
  simp only [surfaceMetricWeakGradientCoordinatePairingInChart,
    surfaceMetricGradientFluxInChart, surfaceFunctionChartDerivativeComponent,
    Fin.sum_univ_two]
  rw [hdf 0, hdf 1]
  simp only [surfaceFunctionChartDerivativeComponent]
  rw [surfaceMetricInverseGramCoeffInChart_symm g.metric e z 0 1]
  ring_nf

/--
%%handwave
name:
  The cutoff flux contraction is integrable against punctured chart tests
statement:
  For every compactly supported coordinate test on a punctured chart region,
  the contraction of the cutoff model's metric flux with the test differential
  is integrable.
proof:
  The cutoff model is smooth on the punctured chart region, so the flux is
  smooth there.  The test differential has compact support contained in the
  same region, and the standard compact-support integrability lemma applies.
-/
theorem logarithmicCutoffPoleModel_punctured_chart_flux_contraction_integrable
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e {x : X | x ≠ p})) :
    Integrable
      (fun z : ℂ ↦
        ∑ i : Fin 2,
          surfaceMetricGradientFluxInChart g.metric e φ.toFun z i *
            fderiv ℝ (η : ℂ → ℝ) z (complexCoordinateVector i))
      (MeasureTheory.volume.restrict
        (surfaceChartRegion e {x : X | x ≠ p})) := by
  let Ω : Set ℂ := surfaceChartRegion e {x : X | x ≠ p}
  let F : Fin 2 → ℂ → ℝ :=
    fun i z ↦ surfaceMetricGradientFluxInChart g.metric e φ.toFun z i
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, surfaceChartRegion] using
      e.isOpen_inter_preimage_symm (isOpen_ne (x := p))
  have hΩ_subset : Ω ⊆ e.target := by
    intro z hz
    exact hz.1
  have hf_chart :
      ContDiffOn ℝ ∞ (fun w : ℂ ↦ φ.toFun (e.symm w)) Ω := by
    simpa [Ω, surfaceChartRegion] using φ.smooth_away_pole e he
  have hF_cont : ∀ i : Fin 2, ContinuousOn (F i) Ω := by
    intro i
    exact
      (surfaceMetricGradientFluxInChart_contDiffOn_of_local_contDiffOn
        g.metric e he φ.toFun hΩ_open hΩ_subset hf_chart i).continuousOn
  have hDF_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (F i) z (complexCoordinateVector i))
          Ω := by
    intro i
    have hflux :
        ContDiffOn ℝ ∞ (F i) Ω :=
      surfaceMetricGradientFluxInChart_contDiffOn_of_local_contDiffOn
        g.metric e he φ.toFun hΩ_open hΩ_subset hf_chart i
    have hderiv :
        ContDiffOn ℝ ∞ (fderiv ℝ (F i)) Ω :=
      hflux.fderiv_of_isOpen hΩ_open (by simp)
    exact (hderiv.clm_apply
      (contDiffOn_const (c := complexCoordinateVector i))).continuousOn
  have hη_cont : ContinuousOn (η : ℂ → ℝ) Ω :=
    η.smooth.continuous.continuousOn
  have hDη_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (η : ℂ → ℝ) z
            (complexCoordinateVector i)) Ω := by
    intro i
    simpa using
      ((η.smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const).continuousOn
  have hparts :=
    euclidean_component_products_integrable_of_tsupport_subset_isCompact
      Ω hΩ_open F (η : ℂ → ℝ) η.support_subset η.compact_support
      hF_cont hDF_cont hη_cont hDη_cont
  have hsum :
      Integrable
        (fun z : ℂ ↦
          ∑ i : Fin 2,
            F i z * fderiv ℝ (η : ℂ → ℝ) z
              (complexCoordinateVector i))
        MeasureTheory.volume := by
    exact integrable_finsetSum (s := Finset.univ)
      (fun i _hi ↦ hparts.2.1 i)
  simpa [Ω, F] using hsum.restrict

/--
%%handwave
name:
  The cutoff flux divergence is the stored source in punctured charts
statement:
  On the punctured chart region, the coordinate divergence of the cutoff
  model's metric flux, tested against a coordinate function, equals the
  stored source times the Riemannian density.
proof:
  The density cancels in the divergence-form Laplacian, the local
  divergence-form Laplacian agrees with the global one on the smooth punctured
  region, and the stored source is defined to be that Laplacian away from the
  pole.
-/
theorem logarithmicCutoffPoleModel_punctured_chart_divergence_integrand_eq_source
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e {x : X | x ≠ p}))
    {z : ℂ} (hz : z ∈ surfaceChartRegion e {x : X | x ≠ p}) :
    (fderiv ℝ
        (fun w : ℂ ↦
          surfaceMetricGradientFluxInChart g.metric e φ.toFun w 0)
        z (1 : ℂ) +
      fderiv ℝ
        (fun w : ℂ ↦
          surfaceMetricGradientFluxInChart g.metric e φ.toFun w 1)
        z Complex.I) * η z =
      φ.source (e.symm z) * η z *
        surfaceMetricVolumeDensityInChart g.metric e z := by
  let U : Set X := {x : X | x ≠ p}
  let ηsurf : X → ℝ := fun x ↦ η (e x)
  have hz_target : z ∈ e.target := hz.1
  have hx_source : e.symm z ∈ e.source := e.map_target hz_target
  have hxU : e.symm z ∈ U := hz.2
  have hηsurf :
      ηsurf (e.symm z) = η z := by
    simp [ηsurf, e.right_inv hz_target]
  have hdensity :=
    surfaceDivergenceFormLaplaceBeltramiInChart_mul_volumeDensity
      g.metric e he φ.toFun ηsurf z hz_target
  have hchart :
      surfaceDivergenceFormLaplaceBeltramiInChart g.metric e φ.toFun z =
        surfaceDivergenceFormLaplaceBeltrami g.metric φ.toFun (e.symm z) := by
    have hglobal :=
      surfaceDivergenceFormLaplaceBeltrami_eq_inChart_of_mem_source_of_isSmoothOnSurface_open
        g.metric (isOpen_ne (x := p)) φ.smooth_away_pole e he
        (e.symm z) hxU hx_source
    simpa [e.right_inv hz_target] using hglobal.symm
  have hoperator :
      surfaceDivergenceFormLaplaceBeltrami g.metric φ.toFun (e.symm z) =
        g.laplaceBeltrami φ.toFun (e.symm z) := by
    exact (congrFun (congrFun
      (BackgroundSurfaceMetricOnSurface.laplaceBeltrami_eq_divergence g)
      φ.toFun) (e.symm z)).symm
  have hsource :
      g.laplaceBeltrami φ.toFun (e.symm z) = φ.source (e.symm z) :=
    φ.source_eq_laplace (e.symm z) hxU
  calc
    (fderiv ℝ
        (fun w : ℂ ↦
          surfaceMetricGradientFluxInChart g.metric e φ.toFun w 0)
        z (1 : ℂ) +
      fderiv ℝ
        (fun w : ℂ ↦
          surfaceMetricGradientFluxInChart g.metric e φ.toFun w 1)
        z Complex.I) * η z
        =
      surfaceDivergenceFormLaplaceBeltramiInChart g.metric e φ.toFun z *
        η z * surfaceMetricVolumeDensityInChart g.metric e z := by
        simpa [hηsurf, mul_assoc] using hdensity.symm
    _ =
      φ.source (e.symm z) * η z *
        surfaceMetricVolumeDensityInChart g.metric e z := by
        rw [hchart, hoperator, hsource]

/--
%%handwave
name:
  Smooth functions on open surface regions have their classical weak gradient
statement:
  If a scalar function is smooth on an open surface region, then its classical
  exterior differential represents its weak gradient on that region.
proof:
  Work in a surface coordinate chart.  The coordinate representative is smooth
  on the coordinate image of the region, and a compactly supported coordinate
  test has support there.  Euclidean integration by parts gives the weak
  derivative identity, and the classical exterior differential identifies the
  coordinate derivative.
-/
theorem isWeakGradientOnRegion_surfaceExteriorDerivative_of_isSmoothOnSurface_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel ∞ X]
    {U : Set X} (hU_open : IsOpen U) {f : X → ℝ}
    (hf : IsSmoothOnSurface U f) :
    IsWeakGradientOnRegion U f (surfaceExteriorDerivative f) := by
  intro e he φ v
  let Ω : Set ℂ := surfaceChartRegion e U
  let u : ℂ → ℝ := fun z ↦ f (e.symm z)
  let dφ : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  let du : ℂ → ℝ := fun z ↦ fderiv ℝ u z v
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, surfaceChartRegion] using e.isOpen_inter_preimage_symm hU_open
  have hf_smooth_Ω : ContDiffOn ℝ ∞ u Ω := by
    simpa [Ω, surfaceChartRegion, u] using hf e he
  have hφ_support_Ω : tsupport (φ : ℂ → ℝ) ⊆ Ω :=
    φ.support_subset
  have hdφ_support_Ω : tsupport dφ ⊆ Ω := by
    simpa [dφ] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : ℂ → ℝ)) v).trans hφ_support_Ω
  have hφ_cont : ContinuousOn (φ : ℂ → ℝ) Ω :=
    φ.smooth.continuous.continuousOn
  have hdφ_cont : ContinuousOn dφ Ω := by
    simpa [dφ] using
      ((φ.smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const).continuousOn
  have hu_cont : ContinuousOn u Ω :=
    hf_smooth_Ω.continuousOn
  have hdu_cont : ContinuousOn du Ω := by
    have hderiv :
        ContDiffOn ℝ ∞ (fderiv ℝ u) Ω :=
      hf_smooth_Ω.fderiv_of_isOpen hΩ_open (by simp)
    simpa [du] using
      (hderiv.clm_apply (contDiffOn_const (c := v))).continuousOn
  have hdφ_compact : IsCompact (tsupport dφ) :=
    φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (by
        simpa [dφ] using
          tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (φ : ℂ → ℝ)) v)
  have hduφ_int :
      Integrable (fun z : ℂ ↦ du z * φ z) MeasureTheory.volume := by
    refine integrable_of_continuousOn_of_tsupport_subset_isCompact
      (s := Ω) (hdu_cont.mul hφ_cont) hΩ_open ?_ ?_
    · exact (tsupport_mul_subset_right).trans hφ_support_Ω
    · exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right
  have hudφ_int :
      Integrable (fun z : ℂ ↦ u z * dφ z) MeasureTheory.volume := by
    refine integrable_of_continuousOn_of_tsupport_subset_isCompact
      (s := Ω) (hu_cont.mul hdφ_cont) hΩ_open ?_ ?_
    · exact (tsupport_mul_subset_right).trans hdφ_support_Ω
    · exact hdφ_compact.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right
  have huφ_int :
      Integrable (fun z : ℂ ↦ u z * φ z) MeasureTheory.volume := by
    refine integrable_of_continuousOn_of_tsupport_subset_isCompact
      (s := Ω) (hu_cont.mul hφ_cont) hΩ_open ?_ ?_
    · exact (tsupport_mul_subset_right).trans hφ_support_Ω
    · exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right
  have hu_diff :
      ∀ z ∈ tsupport (φ : ℂ → ℝ), DifferentiableAt ℝ u z := by
    intro z hz
    have hzΩ : z ∈ Ω := hφ_support_Ω hz
    exact
      (hf_smooth_Ω.contDiffAt (hΩ_open.mem_nhds hzΩ)).differentiableAt
        (by simp)
  have hφ_diff :
      ∀ z ∈ tsupport u, DifferentiableAt ℝ (φ : ℂ → ℝ) z := by
    intro z _hz
    exact (φ.smooth.differentiable (by simp)) z
  have hibp :
      ∫ z : ℂ, u z * dφ z ∂MeasureTheory.volume =
        -∫ z : ℂ, du z * φ z ∂MeasureTheory.volume := by
    simpa [u, du, dφ] using
      (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := MeasureTheory.volume) (f := u) (g := (φ : ℂ → ℝ)) (v := v)
        hduφ_int hudφ_int huφ_int hu_diff hφ_diff)
  have hleft_int :
      Integrable
        (fun z ↦ f (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
        (MeasureTheory.volume.restrict Ω) := by
    simpa [u, dφ] using hudφ_int.restrict (s := Ω)
  have hright_eq :
      (fun z : ℂ ↦ du z * φ z) =ᵐ[MeasureTheory.volume.restrict Ω]
        fun z ↦
          surfaceExteriorDerivative f (e.symm z)
            (surfaceChartTangentMap e z v) * φ z := by
    refine ae_restrict_of_forall_mem hΩ_open.measurableSet ?_
    intro z hzΩ
    have hz' : z ∈ e.target ∩ e.symm ⁻¹' U := by
      simpa [Ω, surfaceChartRegion] using hzΩ
    have hdu_eq :
        surfaceExteriorDerivative f (e.symm z)
            (surfaceChartTangentMap e z v) =
          fderiv ℝ (fun w : ℂ ↦ f (e.symm w)) z v :=
      surfaceExteriorDerivative_apply_chartTangentMap_of_isSmoothOnSurface_open
        hU_open e he f hf z hz' v
    simp [du, u, hdu_eq]
  have hright_int :
      Integrable
        (fun z ↦
          surfaceExteriorDerivative f (e.symm z)
            (surfaceChartTangentMap e z v) * φ z)
        (MeasureTheory.volume.restrict Ω) := by
    exact (hduφ_int.restrict (s := Ω)).congr hright_eq
  refine ⟨hleft_int, hright_int, ?_⟩
  have hleft_full_set :
      ∫ z : ℂ, u z * dφ z ∂MeasureTheory.volume =
        ∫ z in Ω, u z * dφ z ∂MeasureTheory.volume := by
    exact integral_eq_setIntegral_of_tsupport_subset
      ((tsupport_mul_subset_right).trans hdφ_support_Ω)
  have hright_full_set :
      ∫ z : ℂ, du z * φ z ∂MeasureTheory.volume =
        ∫ z in Ω, du z * φ z ∂MeasureTheory.volume := by
    exact integral_eq_setIntegral_of_tsupport_subset
      ((tsupport_mul_subset_right).trans hφ_support_Ω)
  calc
    ∫ z in surfaceChartRegion e U,
        f (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
        ∂MeasureTheory.volume =
      ∫ z in Ω, u z * dφ z ∂MeasureTheory.volume := by
        rfl
    _ = ∫ z : ℂ, u z * dφ z ∂MeasureTheory.volume := hleft_full_set.symm
    _ = -∫ z : ℂ, du z * φ z ∂MeasureTheory.volume := hibp
    _ = -∫ z in Ω, du z * φ z ∂MeasureTheory.volume := by
        rw [hright_full_set]
    _ = -∫ z in Ω,
          surfaceExteriorDerivative f (e.symm z)
            (surfaceChartTangentMap e z v) * φ z
          ∂MeasureTheory.volume := by
        rw [integral_congr_ae hright_eq]
    _ = -∫ z in surfaceChartRegion e U,
          surfaceExteriorDerivative f (e.symm z)
            (surfaceChartTangentMap e z v) * φ z
          ∂MeasureTheory.volume := by
        rfl

/--
%%handwave
name:
  Locally smooth surface functions are continuous on their region
statement:
  A scalar function smooth on an open surface region is continuous on that
  region.
proof:
  Local manifold smoothness gives continuity at every point of the region.
-/
theorem isSmoothOnSurface_continuousOn_of_isOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {U : Set X} (hU_open : IsOpen U) {f : X → ℝ}
    (hf : IsSmoothOnSurface U f) :
    ContinuousOn f U := by
  intro x hx
  exact
    (isSmoothOnSurface_contMDiffAt_of_mem hU_open hf hx).continuousAt.continuousWithinAt

/--
%%handwave
name:
  Locally smooth functions are square-integrable on compact subregions
statement:
  If a scalar function is smooth on an open surface region, then it is
  \(L^2\) on every compact subset of that region for the background area
  measure.
proof:
  The function is continuous, hence bounded, on the compact set, and the
  background area measure is finite on compact sets.
-/
theorem isSmoothOnSurface_memLp_restrict_compact_of_isSmoothOnSurface_open
    {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {U : Set X} (hU_open : IsOpen U) {f : X → ℝ}
    (hf : IsSmoothOnSurface U f)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    MemLp f 2 (g.volume.restrict K) := by
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  have hK_meas : MeasurableSet K := hK.measurableSet
  haveI : IsFiniteMeasure (g.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hcontK : ContinuousOn f K :=
    (isSmoothOnSurface_continuousOn_of_isOpen hU_open hf).mono hKU
  have hf_aesm :
      AEStronglyMeasurable f (g.volume.restrict K) :=
    hcontK.aestronglyMeasurable_of_isCompact hK hK_meas
  rcases hK.exists_bound_of_continuousOn hcontK with ⟨C, hC⟩
  exact
    MemLp.of_bound (μ := g.volume.restrict K) (p := (2 : ℝ≥0∞))
      hf_aesm C
      (by
        filter_upwards [ae_restrict_mem hK_meas] with x hx
        exact hC x hx)

/--
%%handwave
name:
  The exterior derivative section is continuous at a smooth point
statement:
  If a scalar function is smooth as a manifold map at a point, then its
  exterior derivative, regarded as a section of the cotangent total space, is
  continuous at that point.
proof:
  In tangent coordinates, continuity of the derivative section is the standard
  continuity of the manifold derivative of a smooth map.
-/
theorem surfaceExteriorDerivative_totalSpace_continuousAt_of_contMDiffAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {f : X → ℝ} {x₀ : X}
    (hf : ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f x₀) :
    ContinuousAt
      (fun x : X ↦
        (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
          (surfaceExteriorDerivative f x) :
            SurfaceDifferentialTotalSpace X ℝ)) x₀ := by
  have hsec :
      ContMDiffAt SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) 0
        (fun x : X ↦
          (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
            (surfaceExteriorDerivative f x) :
              SurfaceDifferentialTotalSpace X ℝ)) x₀ := by
    rw [contMDiffAt_hom_bundle]
    constructor
    · exact contMDiffAt_id
    · have hmf :
          ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℂ →L[ℝ] ℝ) 0
            (inTangentCoordinates SurfaceRealModel 𝓘(ℝ, ℝ)
              (id : X → X) f
              (fun x : X ↦
                (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f x : ℂ →L[ℝ] ℝ))
              x₀) x₀ := by
        exact hf.mfderiv_const (m := 0) (by norm_num)
      have hcoord :
          (inTangentCoordinates SurfaceRealModel 𝓘(ℝ, ℝ)
              (id : X → X) f
              (fun x : X ↦
                (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f x : ℂ →L[ℝ] ℝ))
              x₀) =
            (fun x : X ↦
              ContinuousLinearMap.inCoordinates ℂ (TangentSpace SurfaceRealModel)
                ℝ (Bundle.Trivial X ℝ) x₀ x x₀ x
                (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f x)) := by
        funext x
        ext v
        simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, SurfaceRealModel,
          TangentBundle.continuousLinearMapAt_model_space,
          ContinuousLinearMap.comp_apply]
        rfl
      simpa [surfaceExteriorDerivative, hcoord] using hmf
  exact hsec.continuousAt

/--
%%handwave
name:
  The exterior derivative section is continuous on a smooth open region
statement:
  If a scalar function is smooth on an open surface region, then its exterior
  derivative is continuous as a cotangent total-space section on that region.
proof:
  Apply pointwise local smoothness and the continuity of the derivative
  section at smooth points.
-/
theorem surfaceExteriorDerivative_totalSpace_continuousOn_of_isSmoothOnSurface_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {U : Set X} (hU_open : IsOpen U) {f : X → ℝ}
    (hf : IsSmoothOnSurface U f) :
    ContinuousOn
      (fun x : X ↦
        (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
          (surfaceExteriorDerivative f x) :
            SurfaceDifferentialTotalSpace X ℝ)) U := by
  intro x hx
  exact
    (surfaceExteriorDerivative_totalSpace_continuousAt_of_contMDiffAt
      (isSmoothOnSurface_contMDiffAt_of_mem hU_open hf hx)).continuousWithinAt

/--
%%handwave
name:
  Locally smooth differentials are square-integrable on compact subregions
statement:
  If a scalar function is smooth on an open surface region, then its exterior
  differential is Hilbert--Schmidt \(L^2\) on every compact subset of that
  region.
proof:
  The exterior derivative section and its metric square norm are continuous
  on the compact set.  Compactness and finite background area measure give
  integrability.
-/
theorem surfaceExteriorDerivative_memHilbertSchmidtL2_restrict_compact_of_isSmoothOnSurface_open
    {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {U : Set X} (hU_open : IsOpen U) {f : X → ℝ}
    (hf : IsSmoothOnSurface U f)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric
      (g.volume.restrict K)
      (SurfaceCotangentField.ofCoordinateField (surfaceExteriorDerivative f)) := by
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  let M :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  letI :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := SurfaceRealModel) (X := X) (E := ℝ) M
  letI :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := SurfaceRealModel) (X := X) (E := ℝ) M
  change HilbertBundleSectionMemL2 G (g.volume.restrict K)
    (SurfaceCotangentField.ofCoordinateField (surfaceExteriorDerivative f))
  have hK_meas : MeasurableSet K := hK.measurableSet
  have hsec_contK :
      ContinuousOn
        (fun x : X ↦
          (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
            ((SurfaceCotangentField.ofCoordinateField
              (surfaceExteriorDerivative f)) x) :
              SurfaceDifferentialTotalSpace X ℝ)) K := by
    simpa [SurfaceCotangentField.ofCoordinateField] using
      (surfaceExteriorDerivative_totalSpace_continuousOn_of_isSmoothOnSurface_open
        hU_open hf).mono hKU
  refine ⟨?_, ?_⟩
  · simpa [HilbertBundleSectionOnSurface.toTotalSpace] using
      hsec_contK.aemeasurable hK_meas
  · let ψ : X → ℝ := fun x ↦
      G.fiberNormSq x
        ((SurfaceCotangentField.ofCoordinateField
          (surfaceExteriorDerivative f)) x)
    have hψ_contK : ContinuousOn ψ K := by
      have hnorm_contK :
          ContinuousOn
            (fun x : X ↦
              ‖((SurfaceCotangentField.ofCoordinateField
                  (surfaceExteriorDerivative f)) x)‖ ^ 2) K := by
        simpa using (ContinuousOn.inner_bundle hsec_contK hsec_contK)
      have hψ_eq :
          ψ =
            fun x : X ↦
              ‖((SurfaceCotangentField.ofCoordinateField
                  (surfaceExteriorDerivative f)) x)‖ ^ 2 := by
        funext x
        change
          G.fiberNormSq x
              ((SurfaceCotangentField.ofCoordinateField
                (surfaceExteriorDerivative f)) x) =
            ‖((SurfaceCotangentField.ofCoordinateField
                (surfaceExteriorDerivative f)) x)‖ ^ 2
        rw [show
            G.fiberNormSq x
                ((SurfaceCotangentField.ofCoordinateField
                  (surfaceExteriorDerivative f)) x) =
              inner ℝ
                ((SurfaceCotangentField.ofCoordinateField
                  (surfaceExteriorDerivative f)) x)
                ((SurfaceCotangentField.ofCoordinateField
                  (surfaceExteriorDerivative f)) x) by
            exact G.fiberNormSq_eq_inner x
              ((SurfaceCotangentField.ofCoordinateField
                (surfaceExteriorDerivative f)) x)]
        exact real_inner_self_eq_norm_sq
          ((SurfaceCotangentField.ofCoordinateField
            (surfaceExteriorDerivative f)) x)
      simpa [hψ_eq] using hnorm_contK
    haveI : IsFiniteMeasureOnCompacts g.volume :=
      BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
    have hψ_int_on : IntegrableOn ψ K g.volume :=
      ContinuousOn.integrableOn_compact hK hψ_contK
    simpa [ψ] using hψ_int_on

/--
%%handwave
name:
  The cutoff model is locally Sobolev off the pole
statement:
  Away from the pole, the logarithmic cutoff model is a local \(W^{1,2}\)
  function whose weak differential is its classical exterior differential.
proof:
  On the punctured surface the model is smooth.  Compact subsets of the
  punctured surface therefore see a smooth function and a smooth cotangent
  field, hence both are square-integrable for the smooth background area
  measure.
-/
theorem logarithmicCutoffPoleModel_isIntrinsicLocalSobolevH1On_punctured
    {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p) :
    IsIntrinsicLocalSobolevH1OnSurface g {x : X | x ≠ p}
      φ.toFun (surfaceExteriorDerivative φ.toFun) := by
  have hU_open : IsOpen {x : X | x ≠ p} := isOpen_ne (x := p)
  refine ⟨?_, ?_⟩
  · exact
      isWeakGradientOnRegion_surfaceExteriorDerivative_of_isSmoothOnSurface_open
        hU_open φ.smooth_away_pole
  · intro K hK hKU
    exact
      ⟨isSmoothOnSurface_memLp_restrict_compact_of_isSmoothOnSurface_open
          (g := g) hU_open φ.smooth_away_pole hK hKU,
        surfaceExteriorDerivative_memHilbertSchmidtL2_restrict_compact_of_isSmoothOnSurface_open
          (g := g) hU_open φ.smooth_away_pole hK hKU⟩

/--
%%handwave
name:
  The cutoff model satisfies the punctured chart weak source identity
statement:
  In every chart and for every compactly supported test inside the punctured
  chart region, the gradient pairing of the cutoff model equals minus the
  pairing with its stored smooth source.
proof:
  The test support avoids the pole, where the cutoff model is smooth and its
  stored source agrees with the Laplace-Beltrami operator.  Apply the
  divergence-form integration-by-parts identity on the chart-supported
  region and then substitute the stored source formula.
-/
theorem logarithmicCutoffPoleModel_punctured_chart_weak_source_identity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e {x : X | x ≠ p})) :
    Integrable
        (fun z ↦
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (surfaceExteriorDerivative φ.toFun (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e {x : X | x ≠ p})) ∧
      Integrable
        (fun z ↦
          φ.source (e.symm z) * η z *
            surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e {x : X | x ≠ p})) ∧
        ∫ z in surfaceChartRegion e {x : X | x ≠ p},
            surfaceMetricWeakGradientCoordinatePairingInChart g e z
              (surfaceExteriorDerivative φ.toFun (e.symm z))
              (fderiv ℝ (η : ℂ → ℝ) z) *
                surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          -∫ z in surfaceChartRegion e {x : X | x ≠ p},
            φ.source (e.symm z) * η z *
              surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
  let Ω : Set ℂ := surfaceChartRegion e {x : X | x ≠ p}
  let fluxTerm : ℂ → ℝ :=
    fun z ↦
      ∑ i : Fin 2,
        surfaceMetricGradientFluxInChart g.metric e φ.toFun z i *
          fderiv ℝ (η : ℂ → ℝ) z (complexCoordinateVector i)
  let gradTerm : ℂ → ℝ :=
    fun z ↦
      surfaceMetricWeakGradientCoordinatePairingInChart g e z
        (surfaceExteriorDerivative φ.toFun (e.symm z))
        (fderiv ℝ (η : ℂ → ℝ) z) *
          surfaceMetricVolumeDensityInChart g.metric e z
  let sourceTerm : ℂ → ℝ :=
    fun z ↦
      φ.source (e.symm z) * η z *
        surfaceMetricVolumeDensityInChart g.metric e z
  let divTerm : ℂ → ℝ :=
    fun z ↦
      (fderiv ℝ
          (fun w : ℂ ↦
            surfaceMetricGradientFluxInChart g.metric e φ.toFun w 0)
          z (1 : ℂ) +
        fderiv ℝ
          (fun w : ℂ ↦
            surfaceMetricGradientFluxInChart g.metric e φ.toFun w 1)
          z Complex.I) * η z
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, surfaceChartRegion] using
      e.isOpen_inter_preimage_symm (isOpen_ne (x := p))
  have hflux_int :
      Integrable fluxTerm (MeasureTheory.volume.restrict Ω) := by
    simpa [Ω, fluxTerm] using
      logarithmicCutoffPoleModel_punctured_chart_flux_contraction_integrable
        φ e he η
  have hgrad_int :
      Integrable gradTerm (MeasureTheory.volume.restrict Ω) := by
    refine hflux_int.congr ?_
    filter_upwards [ae_restrict_mem hΩ_open.measurableSet] with z hz
    exact
      (logarithmicCutoffPoleModel_punctured_chart_gradient_integrand_eq_flux
        φ e he η hz).symm
  have hsource_int :
      Integrable sourceTerm (MeasureTheory.volume.restrict Ω) := by
    have hneg :=
      logarithmicCutoffPoleModel_negative_chartTest_source_integrable
        φ e he η
    have hpos := hneg.neg
    refine hpos.congr ?_
    filter_upwards [] with z
    simp [sourceTerm]
  have hgrad_eq_flux :
      ∫ z in Ω, gradTerm z ∂MeasureTheory.volume =
        ∫ z in Ω, fluxTerm z ∂MeasureTheory.volume := by
    refine setIntegral_congr_fun hΩ_open.measurableSet ?_
    intro z hz
    exact
      logarithmicCutoffPoleModel_punctured_chart_gradient_integrand_eq_flux
        φ e he η hz
  have hdiv_eq_source :
      ∫ z in Ω, divTerm z ∂MeasureTheory.volume =
        ∫ z in Ω, sourceTerm z ∂MeasureTheory.volume := by
    refine setIntegral_congr_fun hΩ_open.measurableSet ?_
    intro z hz
    exact
      logarithmicCutoffPoleModel_punctured_chart_divergence_integrand_eq_source
        φ e he η hz
  have hflux_identity :
      ∫ z in Ω, divTerm z ∂MeasureTheory.volume =
        -∫ z in Ω, fluxTerm z ∂MeasureTheory.volume := by
    simpa [Ω, divTerm, fluxTerm] using
      logarithmicCutoffPoleModel_punctured_chart_flux_identity φ e he η
  have hflux_rev :
      ∫ z in Ω, fluxTerm z ∂MeasureTheory.volume =
        -∫ z in Ω, divTerm z ∂MeasureTheory.volume := by
    rw [hflux_identity]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simpa [Ω, gradTerm] using hgrad_int
  · simpa [Ω, sourceTerm] using hsource_int
  · calc
      ∫ z in Ω, gradTerm z ∂MeasureTheory.volume =
          ∫ z in Ω, fluxTerm z ∂MeasureTheory.volume := hgrad_eq_flux
      _ = -∫ z in Ω, divTerm z ∂MeasureTheory.volume := hflux_rev
      _ = -∫ z in Ω, sourceTerm z ∂MeasureTheory.volume := by
        rw [hdiv_eq_source]

/--
%%handwave
name:
  The cutoff model satisfies the local weak source equation
statement:
  On the punctured surface, the logarithmic cutoff model satisfies the weak
  Laplace-Beltrami equation with its stored smooth source.
proof:
  Use the model smoothness away from the pole and integrate by parts in
  surface charts.  The stored source agrees there with the background
  Laplace-Beltrami operator.
-/
theorem logarithmicCutoffPoleModel_isWeakLaplaceBeltramiSourceOn_punctured
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p) :
    IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
      φ.toFun φ.source := by
  refine ⟨?_, ?_⟩
  · simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  · refine ⟨surfaceExteriorDerivative φ.toFun, ?_, ?_⟩
    · exact logarithmicCutoffPoleModel_isIntrinsicLocalSobolevH1On_punctured φ
    · intro e he η
      exact
        logarithmicCutoffPoleModel_punctured_chart_weak_source_identity
          φ e he η

/--
%%handwave
name:
  Local energy Green potential
statement:
  The Green candidate associated to a cutoff model and a local finite-energy
  correction is \(G=\phi+h\).
-/
def localEnergyGreenPotential {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g) : X → ℝ :=
  fun x ↦ φ.toFun x + h.toFun x

/--
%%handwave
name:
  Source cancellation makes the local energy potential weakly harmonic
statement:
  If the cutoff model and the local correction solve weak Laplace-Beltrami
  equations on the punctured surface with opposite sources, then their sum is
  weakly harmonic there.
proof:
  Add the two weak identities.  The source terms cancel and the weak
  gradients add to the weak gradient of the sum.
-/
theorem localEnergyGreenPotential_weaklyHarmonicOn_punctured_of_source_cancellation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g)
    (hφ_source :
      IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
        φ.toFun φ.source)
    (hh_source :
      IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
        h.toFun (fun x : X ↦ -φ.source x)) :
    IsWeaklyHarmonicOnSurface g {x : X | x ≠ p}
      (localEnergyGreenPotential φ h) := by
  simpa [localEnergyGreenPotential] using
    (weaklyHarmonicOnSurface_of_source_cancellation
      (g := g) (U := {x : X | x ≠ p})
      (u := φ.toFun) (v := h.toFun) (F := φ.source)
      hφ_source hh_source)

/--
%%handwave
name:
  Source cancellation and Weyl regularity make the local energy potential harmonic
statement:
  On a conformal surface, if the cutoff model and the local correction have
  cancelling weak sources on the punctured surface and the sum has pointwise
  Weyl representatives in charts, then the local energy potential is
  harmonic off the pole.
proof:
  Source cancellation gives weak harmonicity of the sum.  Weyl's lemma then
  upgrades weak harmonicity to ordinary harmonicity in surface charts.
-/
theorem localEnergyGreenPotential_harmonicOn_punctured_of_source_cancellation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g)
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hφ_source :
      IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
        φ.toFun φ.source)
    (hh_source :
      IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
        h.toFun (fun x : X ↦ -φ.source x))
    (hpointwise :
      HasPointwiseWeylRepresentativesInCharts {x : X | x ≠ p}
        (localEnergyGreenPotential φ h)) :
    IsHarmonicOnSurface {x : X | x ≠ p}
      (localEnergyGreenPotential φ h) := by
  have hpointwise' :
      HasPointwiseWeylRepresentativesInCharts {x : X | x ≠ p}
        (fun x : X ↦ φ.toFun x + h.toFun x) := by
    simpa [localEnergyGreenPotential] using hpointwise
  simpa [localEnergyGreenPotential] using
    (weyl_harmonicOnSurface_of_source_cancellation
      (g := g) (U := {x : X | x ≠ p})
      (u := φ.toFun) (v := h.toFun) (F := φ.source)
      hconformal hφ_source hh_source hpointwise')

/--
%%handwave
name:
  Logarithmically corrected regular potentials are punctured-harmonic
statement:
  If a regular representative is harmonic away from the pole, then in every
  pointed coordinate its sum with the coordinate logarithm is harmonic on the
  punctured coordinate neighborhood.
proof:
  Restrict the harmonic representative to the punctured coordinate
  neighborhood and add the harmonic coordinate logarithm.
-/
theorem regularLocalEnergyGreenPotential_corrected_harmonicOn_punctured_coordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (_φ : LogarithmicCutoffPoleModel g p)
    (_h : GreenSobolevH10LocalCorrection g) (G : X → ℝ)
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    (χ : PointedSurfaceCoordinate X p) :
    IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p})
      (fun x : X ↦
        G x + Real.log ‖χ.chart x - χ.chart p‖) := by
  have hgreen :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) G :=
    harmonicOnSurface_mono (by
      intro x hx
      exact hx.2) hharmonic
  have hlog :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p})
        (fun x : X ↦ Real.log ‖χ.chart x - χ.chart p‖) :=
    coordinateLogDistance_harmonicOnSurface χ.chart χ.chart_mem_atlas
      (by
        intro x hx
        exact hx.1)
      (by
        intro x hx hEq
        exact hx.2 (χ.chart.injOn hx.1 χ.base_mem_source hEq))
  exact harmonicOnSurface_add hgreen hlog

/--
%%handwave
name:
  Model-coordinate cancellation for regular potentials
statement:
  On the inner punctured model disk, a Weyl-regular representative of
  \(\phi+h\), after adding the model logarithm, agrees almost everywhere
  with the scalar correction representative.
proof:
  In the model coordinate the cutoff pole model is exactly the negative
  logarithm.  The representative agrees almost everywhere with the local
  energy potential off the pole, so the logarithmic terms cancel.
-/
theorem regularLocalEnergyGreenPotential_modelCoordinate_corrected_ae_eq_correction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g) (G : X → ℝ)
    (hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ h (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w))) :
    let χ : PointedSurfaceCoordinate X p := φ.coordinate
    (fun z : ℂ ↦
        G (χ.chart.symm z) +
          Real.log ‖z - χ.chart p‖)
      =ᵐ[MeasureTheory.volume.restrict
        ((χ.chart.target ∩ χ.chart.symm ⁻¹' {x : X | x ≠ p}) ∩
          {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius})]
        (fun z : ℂ ↦ h.toFun (χ.chart.symm z)) := by
  classical
  let χ : PointedSurfaceCoordinate X p := φ.coordinate
  let Ω₀ : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' {x : X | x ≠ p}
  let Ω : Set ℂ := Ω₀ ∩ {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius}
  have hΩ_subset : Ω ⊆ Ω₀ := Set.inter_subset_left
  have hrepΩ₀ :
      (fun w : ℂ ↦ localEnergyGreenPotential φ h (χ.chart.symm w))
        =ᵐ[MeasureTheory.volume.restrict Ω₀]
        (fun w : ℂ ↦ G (χ.chart.symm w)) := by
    simpa [χ, Ω₀] using hrep χ.chart χ.chart_mem_atlas
  have hrepΩ :
      (fun w : ℂ ↦ localEnergyGreenPotential φ h (χ.chart.symm w))
        =ᵐ[MeasureTheory.volume.restrict Ω]
        (fun w : ℂ ↦ G (χ.chart.symm w)) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hΩ_subset hrepΩ₀
  have hΩ₀_open : IsOpen Ω₀ := by
    simpa [Ω₀] using
      χ.chart.isOpen_inter_preimage_symm
        (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  have hball_open :
      IsOpen {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius} := by
    have hcont : Continuous fun z : ℂ ↦ ‖z - χ.chart p‖ :=
      (continuous_id.sub continuous_const).norm
    simpa [Set.preimage] using
      hcont.isOpen_preimage (Set.Iio φ.innerRadius) isOpen_Iio
  have hΩ_meas : MeasurableSet Ω := (hΩ₀_open.inter hball_open).measurableSet
  filter_upwards [hrepΩ.symm, ae_restrict_mem hΩ_meas] with z hzrep hzΩ
  have hz_target : z ∈ χ.chart.target := hzΩ.1.1
  have hsymm_source : χ.chart.symm z ∈ χ.chart.source :=
    χ.chart.map_target hz_target
  have hsymm_ne : χ.chart.symm z ≠ p := by
    simpa using hzΩ.1.2
  have hz_radius :
      ‖χ.chart (χ.chart.symm z) - χ.chart p‖ < φ.innerRadius := by
    simpa [χ.chart.right_inv hz_target] using hzΩ.2
  have hφ_eq :
      φ.toFun (χ.chart.symm z) =
        -Real.log ‖z - χ.chart p‖ := by
    have hmodel :=
      φ.model_eq_negative_log_near_pole
        (χ.chart.symm z) hsymm_source hz_radius hsymm_ne
    simpa [χ, χ.chart.right_inv hz_target] using hmodel
  calc
    G (χ.chart.symm z) + Real.log ‖z - χ.chart p‖
        = localEnergyGreenPotential φ h (χ.chart.symm z) +
            Real.log ‖z - χ.chart p‖ := by rw [hzrep]
    _ = h.toFun (χ.chart.symm z) := by
          simp [localEnergyGreenPotential, hφ_eq]

/--
%%handwave
name:
  Model-coordinate pointwise cancellation from harmonic representatives
statement:
  If the correction has a harmonic representative in the model chart and the
  scalar correction agrees almost everywhere with it on the inner punctured
  model disk, then the logarithmically corrected regular potential agrees
  pointwise with that harmonic representative on the same disk.
proof:
  The preceding cancellation gives almost-everywhere agreement between the
  corrected regular potential and the correction.  Combining this with the
  assumed almost-everywhere agreement with the harmonic representative gives
  almost-everywhere agreement of two harmonic functions on an open planar
  region.  Harmonic representatives are unique from almost-everywhere
  agreement on open sets.
-/
theorem regularLocalEnergyGreenPotential_modelCoordinate_corrected_eqOn_of_harmonic_correction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g) (G H : X → ℝ)
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    (hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ h (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w)))
    (hH : IsHarmonicOnSurface φ.coordinate.chart.source H)
    (hHrep :
      let χ : PointedSurfaceCoordinate X p := φ.coordinate
      (fun z : ℂ ↦ h.toFun (χ.chart.symm z))
        =ᵐ[MeasureTheory.volume.restrict
          ((χ.chart.target ∩ χ.chart.symm ⁻¹' {x : X | x ≠ p}) ∩
            {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius})]
          (fun z : ℂ ↦ H (χ.chart.symm z))) :
    let χ : PointedSurfaceCoordinate X p := φ.coordinate
    ((χ.chart.target ∩ χ.chart.symm ⁻¹' {x : X | x ≠ p}) ∩
        {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius}).EqOn
      (fun z : ℂ ↦
        G (χ.chart.symm z) +
          Real.log ‖z - χ.chart p‖)
      (fun z : ℂ ↦ H (χ.chart.symm z)) := by
  classical
  let χ : PointedSurfaceCoordinate X p := φ.coordinate
  let Ω₀ : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' {x : X | x ≠ p}
  let Ω : Set ℂ := Ω₀ ∩ {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius}
  have hΩ₀_open : IsOpen Ω₀ := by
    simpa [Ω₀] using
      χ.chart.isOpen_inter_preimage_symm
        (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  have hball_open :
      IsOpen {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius} := by
    have hcont : Continuous fun z : ℂ ↦ ‖z - χ.chart p‖ :=
      (continuous_id.sub continuous_const).norm
    simpa [Set.preimage] using
      hcont.isOpen_preimage (Set.Iio φ.innerRadius) isOpen_Iio
  have hΩ_open : IsOpen Ω := hΩ₀_open.inter hball_open
  have hcorr_surf :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p})
        (fun x : X ↦ G x + Real.log ‖χ.chart x - χ.chart p‖) :=
    regularLocalEnergyGreenPotential_corrected_harmonicOn_punctured_coordinate
      φ h G hharmonic χ
  have hcorr_planar :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦
          G (χ.chart.symm z) +
            Real.log ‖z - χ.chart p‖) Ω := by
    have hχ := hcorr_surf χ.chart χ.chart_mem_atlas
    have hraw :
        InnerProductSpace.HarmonicOnNhd
          (fun z : ℂ ↦
            G (χ.chart.symm z) +
              Real.log ‖χ.chart (χ.chart.symm z) - χ.chart p‖) Ω := by
      refine (hχ.mono ?_)
      intro z hzΩ
      have hz_target : z ∈ χ.chart.target := hzΩ.1.1
      have hsymm_source : χ.chart.symm z ∈ χ.chart.source :=
        χ.chart.map_target hz_target
      have hsymm_ne : χ.chart.symm z ≠ p := by
        simpa [Ω, Ω₀] using hzΩ.1.2
      refine ⟨hz_target, hsymm_source, hsymm_ne⟩
    intro z hzΩ
    have hevent :
        (fun y : ℂ ↦
          G (χ.chart.symm y) + Real.log ‖y - χ.chart p‖)
          =ᶠ[𝓝 z]
        (fun y : ℂ ↦
          G (χ.chart.symm y) +
            Real.log ‖χ.chart (χ.chart.symm y) - χ.chart p‖) := by
      filter_upwards [hΩ_open.mem_nhds hzΩ] with y hyΩ
      have hy_target : y ∈ χ.chart.target := hyΩ.1.1
      simp [χ.chart.right_inv hy_target]
    exact (InnerProductSpace.harmonicAt_congr_nhds hevent).2
      (hraw z hzΩ)
  have hH_planar :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ H (χ.chart.symm z)) Ω := by
    have hχ := hH χ.chart χ.chart_mem_atlas
    refine (hχ.mono ?_)
    intro z hzΩ
    have hz_target : z ∈ χ.chart.target := hzΩ.1.1
    exact ⟨hz_target, χ.chart.map_target hz_target⟩
  have hae_corr :
      (fun z : ℂ ↦
          G (χ.chart.symm z) +
            Real.log ‖z - χ.chart p‖)
        =ᵐ[MeasureTheory.volume.restrict Ω]
        (fun z : ℂ ↦ h.toFun (χ.chart.symm z)) := by
    simpa [χ, Ω₀, Ω] using
      regularLocalEnergyGreenPotential_modelCoordinate_corrected_ae_eq_correction
        φ h G hrep
  have hae_H :
      (fun z : ℂ ↦ h.toFun (χ.chart.symm z))
        =ᵐ[MeasureTheory.volume.restrict Ω]
        (fun z : ℂ ↦ H (χ.chart.symm z)) := by
    simpa [χ, Ω₀, Ω] using hHrep
  exact
    harmonicOnNhd_eqOn_of_ae_eq_on_isOpen hΩ_open
      hcorr_planar hH_planar (hae_corr.trans hae_H)

/--
%%handwave
name:
  Local model-coordinate pointwise cancellation from harmonic representatives
statement:
  If the correction has a harmonic representative on a neighbourhood of the
  pole and agrees almost everywhere with it there, then the model-coordinate
  logarithmically corrected regular potential agrees pointwise with that
  representative on the inner punctured part of the neighbourhood.
proof:
  On the model coordinate disk, the pole model is the negative logarithm, so
  the corrected regular potential agrees almost everywhere with the
  correction.  The correction also agrees almost everywhere with the harmonic
  representative.  Since both sides are harmonic on the open punctured
  coordinate region, a.e. equality upgrades to pointwise equality.
-/
theorem regularLocalEnergyGreenPotential_modelCoordinate_corrected_eqOn_of_local_harmonic_correction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g) (G H : X → ℝ)
    {U : Set X}
    (hU_open : IsOpen U)
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    (hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ h (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w)))
    (hH : IsHarmonicOnSurface U H)
    (hHrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun z : ℂ ↦ h.toFun (e.symm z))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' U)]
          (fun z : ℂ ↦ H (e.symm z))) :
    let χ : PointedSurfaceCoordinate X p := φ.coordinate
    (((χ.chart.target ∩ χ.chart.symm ⁻¹' {x : X | x ≠ p}) ∩
        {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius}) ∩
        χ.chart.symm ⁻¹' U).EqOn
      (fun z : ℂ ↦
        G (χ.chart.symm z) +
          Real.log ‖z - χ.chart p‖)
      (fun z : ℂ ↦ H (χ.chart.symm z)) := by
  classical
  let χ : PointedSurfaceCoordinate X p := φ.coordinate
  let Ω₀ : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' {x : X | x ≠ p}
  let Ωball : Set ℂ := Ω₀ ∩ {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius}
  let Ω : Set ℂ := Ωball ∩ χ.chart.symm ⁻¹' U
  have hΩ₀_open : IsOpen Ω₀ := by
    simpa [Ω₀] using
      χ.chart.isOpen_inter_preimage_symm
        (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  have hball_open :
      IsOpen {z : ℂ | ‖z - χ.chart p‖ < φ.innerRadius} := by
    have hcont : Continuous fun z : ℂ ↦ ‖z - χ.chart p‖ :=
      (continuous_id.sub continuous_const).norm
    simpa [Set.preimage] using
      hcont.isOpen_preimage (Set.Iio φ.innerRadius) isOpen_Iio
  have hΩball_open : IsOpen Ωball := hΩ₀_open.inter hball_open
  have hU_pre_open : IsOpen (χ.chart.symm ⁻¹' U ∩ χ.chart.target) := by
    simpa [Set.inter_comm] using
      χ.chart.isOpen_inter_preimage_symm hU_open
  have hΩ_open : IsOpen Ω := by
    have hΩ_eq :
        Ω = (χ.chart.symm ⁻¹' U ∩ χ.chart.target) ∩ Ωball := by
      ext z
      simp [Ω, Ωball, Ω₀, and_assoc, and_left_comm, and_comm]
    rw [hΩ_eq]
    exact hU_pre_open.inter hΩball_open
  have hΩ_subset_Ωball : Ω ⊆ Ωball := Set.inter_subset_left
  have hcorr_surf :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p})
        (fun x : X ↦ G x + Real.log ‖χ.chart x - χ.chart p‖) :=
    regularLocalEnergyGreenPotential_corrected_harmonicOn_punctured_coordinate
      φ h G hharmonic χ
  have hcorr_planar :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦
          G (χ.chart.symm z) +
            Real.log ‖z - χ.chart p‖) Ω := by
    have hχ := hcorr_surf χ.chart χ.chart_mem_atlas
    have hraw :
        InnerProductSpace.HarmonicOnNhd
          (fun z : ℂ ↦
            G (χ.chart.symm z) +
              Real.log ‖χ.chart (χ.chart.symm z) - χ.chart p‖) Ω := by
      refine (hχ.mono ?_)
      intro z hzΩ
      have hz_target : z ∈ χ.chart.target := hzΩ.1.1.1
      have hsymm_source : χ.chart.symm z ∈ χ.chart.source :=
        χ.chart.map_target hz_target
      have hsymm_ne : χ.chart.symm z ≠ p := by
        simpa [Ω, Ωball, Ω₀] using hzΩ.1.1.2
      exact ⟨hz_target, hsymm_source, hsymm_ne⟩
    intro z hzΩ
    have hevent :
        (fun y : ℂ ↦
          G (χ.chart.symm y) + Real.log ‖y - χ.chart p‖)
          =ᶠ[𝓝 z]
        (fun y : ℂ ↦
          G (χ.chart.symm y) +
            Real.log ‖χ.chart (χ.chart.symm y) - χ.chart p‖) := by
      filter_upwards [hΩ_open.mem_nhds hzΩ] with y hyΩ
      have hy_target : y ∈ χ.chart.target := hyΩ.1.1.1
      simp [χ.chart.right_inv hy_target]
    exact (InnerProductSpace.harmonicAt_congr_nhds hevent).2
      (hraw z hzΩ)
  have hH_planar :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ H (χ.chart.symm z)) Ω := by
    have hχ := hH χ.chart χ.chart_mem_atlas
    refine (hχ.mono ?_)
    intro z hzΩ
    have hz_target : z ∈ χ.chart.target := hzΩ.1.1.1
    have hzU : χ.chart.symm z ∈ U := by
      simpa [Ω] using hzΩ.2
    exact ⟨hz_target, hzU⟩
  have hae_corr_ball :
      (fun z : ℂ ↦
          G (χ.chart.symm z) +
            Real.log ‖z - χ.chart p‖)
        =ᵐ[MeasureTheory.volume.restrict Ωball]
        (fun z : ℂ ↦ h.toFun (χ.chart.symm z)) := by
    simpa [χ, Ω₀, Ωball] using
      regularLocalEnergyGreenPotential_modelCoordinate_corrected_ae_eq_correction
        φ h G hrep
  have hae_corr :
      (fun z : ℂ ↦
          G (χ.chart.symm z) +
            Real.log ‖z - χ.chart p‖)
        =ᵐ[MeasureTheory.volume.restrict Ω]
        (fun z : ℂ ↦ h.toFun (χ.chart.symm z)) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hΩ_subset_Ωball
      hae_corr_ball
  have hΩ_subset_U :
      Ω ⊆ χ.chart.target ∩ χ.chart.symm ⁻¹' U := by
    intro z hzΩ
    exact ⟨hzΩ.1.1.1, hzΩ.2⟩
  have hae_H_base :
      (fun z : ℂ ↦ h.toFun (χ.chart.symm z))
        =ᵐ[MeasureTheory.volume.restrict
          (χ.chart.target ∩ χ.chart.symm ⁻¹' U)]
        (fun z : ℂ ↦ H (χ.chart.symm z)) :=
    hHrep χ.chart χ.chart_mem_atlas
  have hae_H :
      (fun z : ℂ ↦ h.toFun (χ.chart.symm z))
        =ᵐ[MeasureTheory.volume.restrict Ω]
        (fun z : ℂ ↦ H (χ.chart.symm z)) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hΩ_subset_U
      hae_H_base
  simpa [χ, Ω₀, Ωball, Ω] using
    harmonicOnNhd_eqOn_of_ae_eq_on_isOpen hΩ_open
      hcorr_planar hH_planar (hae_corr.trans hae_H)

/--
%%handwave
name:
  Local Riesz correction data give a local weak Green correction
statement:
  The local correction packaged with pure Riesz source data satisfies the
  local weak Green-correction definition.
proof:
  The local Sobolev and punctured opposite-source fields are part of the
  data.  The smooth-test pairing follows by combining the stored Dirichlet
  pairing identity with the Riesz Euler identity and the stored source
  compatibility.
-/
theorem greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_isLocalWeakGreenCorrection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source) :
    IsLocalWeakGreenCorrection φ hdata.correction := by
  refine
    { localSobolev := hdata.localSobolev
      smooth_test_pairing := ?_
      punctured_opposite_source := hdata.punctured_opposite_source }
  intro η
  calc
    greenLocalCorrectionSmoothTestDirichletPairing g hdata.correction η =
        inner ℝ
          (greenSobolevH10RieszRepresentative
            ((greenSobolevH10SmoothCompactSupportCore g).extendSource source))
          (hdata.test η) := hdata.dirichlet_pairing_eq_inner η
    _ = greenSobolevH10SmoothCompactSupportSource source (hdata.test η) :=
        greenSobolevH10SmoothCompactSupportEnergy_rieszRepresentative_eulerLagrange
          source (hdata.test η)
    _ = greenSmoothTestSourcePairing φ η :=
        hdata.source_eq_source_pairing η

/--
%%handwave
name:
  Pure Riesz local correction data give a weakly harmonic punctured potential
statement:
  The local energy potential associated to the pure Riesz correction is
  weakly harmonic on the punctured surface.
proof:
  The cutoff model has weak Laplace-Beltrami source equal to its smooth
  source term, while the correction data carry the opposite source.  Adding
  the two weak equations cancels the source.
-/
theorem greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_weaklyHarmonicOn_punctured
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X] [T1Space X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source) :
    IsWeaklyHarmonicOnSurface g {x : X | x ≠ p}
      (localEnergyGreenPotential φ hdata.correction) :=
  localEnergyGreenPotential_weaklyHarmonicOn_punctured_of_source_cancellation
    φ hdata.correction
    (logarithmicCutoffPoleModel_isWeakLaplaceBeltramiSourceOn_punctured φ)
    hdata.punctured_opposite_source

/--
%%handwave
name:
  Pure Riesz corrections are weakly harmonic near the pole
statement:
  The local correction produced by the pure Riesz construction is weakly
  harmonic on a punctured neighbourhood of the pole.
proof:
  The cutoff source vanishes in a neighbourhood of the pole because its
  support avoids the pole.  Restrict the correction's opposite-source weak
  equation to the punctured part of that neighbourhood and replace the source
  by zero there.
-/
theorem greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_correction_weaklyHarmonicOn_poleNhd
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X] [T1Space X] [MeasurableEq X]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source) :
    ∃ U : Set X,
      IsOpen U ∧ p ∈ U ∧
        IsWeaklyHarmonicOnSurface g (U ∩ {x : X | x ≠ p})
          hdata.correction.toFun := by
  rcases mem_nhds_iff.mp
      (LogarithmicCutoffPoleModel.eventually_source_eq_zero_at_pole φ) with
    ⟨U, hU_subset_zero, hU_open, hpU⟩
  let V : Set X := U ∩ {x : X | x ≠ p}
  have hV_open : IsOpen V := by
    simpa [V] using hU_open.inter (isOpen_ne (x := p))
  have hV_subset_punctured : V ⊆ {x : X | x ≠ p} := by
    intro x hx
    exact hx.2
  have hweak_V_source :
      IsWeakLaplaceBeltramiSourceOnSurface g V
        hdata.correction.toFun (fun x : X ↦ -φ.source x) :=
    hdata.punctured_opposite_source.mono_set hV_open hV_subset_punctured
  have hweak_V_zero :
      IsWeakLaplaceBeltramiSourceOnSurface g V
        hdata.correction.toFun (fun _ : X ↦ 0) :=
    hweak_V_source.congr_source (by
      intro x hxV
      have hxU : x ∈ U := hxV.1
      rw [hU_subset_zero hxU]
      simp)
  refine ⟨U, hU_open, hpU, ?_⟩
  simpa [V] using
    weaklyHarmonicOnSurface_of_weakLaplaceBeltramiSource_zero
      hweak_V_zero

/--
%%handwave
name:
  Pure Riesz corrections are weakly harmonic on a full pole neighbourhood
statement:
  The local correction produced by the pure Riesz construction is weakly
  harmonic on a neighbourhood of the pole, without deleting the pole.
proof:
  The cutoff source vanishes on a neighbourhood of the pole.  The Riesz
  smooth-test identity localizes to every compactly supported chart test in
  that neighbourhood, so the correction satisfies the zero-source weak
  equation there.
-/
theorem greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_correction_weaklyHarmonicOn_full_poleNhd
    {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source) :
    ∃ U : Set X,
      IsOpen U ∧ p ∈ U ∧
        IsWeaklyHarmonicOnSurface g U hdata.correction.toFun := by
  rcases mem_nhds_iff.mp
      (LogarithmicCutoffPoleModel.eventually_source_eq_zero_at_pole φ) with
    ⟨U, hU_subset_zero, hU_open, hpU⟩
  have hweak :
      IsLocalWeakGreenCorrection φ hdata.correction := by
    simpa [greenSobolevH10SmoothCompactSupportLocalRieszCorrection] using
      greenSobolevH10SmoothCompactSupportLocalRieszCorrection_isLocalWeakGreenCorrection
        hdata
  have hzero_source :
      IsWeakLaplaceBeltramiSourceOnSurface g U
        hdata.correction.toFun (fun _ : X ↦ 0) := by
    refine ⟨hU_open, hdata.correction.weakGradient, ?_, ?_⟩
    · exact hdata.localSobolev.mono_set (Set.subset_univ U)
    · intro e he η
      let Ω : Set ℂ := surfaceChartRegion e U
      rcases
          localCorrection_chartTest_source_identity_of_smoothTestPairing
            φ hdata.correction hdata.localSobolev hweak.smooth_test_pairing
            e he η with
        ⟨hgrad_int, hsource_int, hidentity⟩
      have hzero_int :
          ∫ z in Ω,
              (fun x : X ↦ -φ.source x) (e.symm z) * η z *
                surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume = 0 := by
        rw [← integral_zero]
        have hΩ_meas : MeasurableSet Ω := by
          simpa [Ω, surfaceChartRegion] using
            (e.isOpen_inter_preimage_symm hU_open).measurableSet
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem hΩ_meas] with z hzΩ
        have hzU : e.symm z ∈ U := by
          simpa [Ω, surfaceChartRegion] using hzΩ.2
        have hsrc_zero : φ.source (e.symm z) = 0 := hU_subset_zero hzU
        simp [hsrc_zero]
      refine ⟨hgrad_int, ?_, ?_⟩
      · simpa using
          (integrable_zero :
            Integrable
              (fun _z : ℂ ↦ (0 : ℝ))
              (MeasureTheory.volume.restrict Ω))
      · calc
          ∫ z in surfaceChartRegion e U,
              surfaceMetricWeakGradientCoordinatePairingInChart g e z
                (hdata.correction.weakGradient (e.symm z))
                (fderiv ℝ (η : ℂ → ℝ) z) *
                  surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume =
              -∫ z in surfaceChartRegion e U,
                (fun x : X ↦ -φ.source x) (e.symm z) * η z *
                  surfaceMetricVolumeDensityInChart g.metric e z
                ∂MeasureTheory.volume := hidentity
          _ = 0 := by
              simpa [Ω] using congrArg Neg.neg hzero_int
          _ = -∫ z in surfaceChartRegion e U,
                (fun _x : X ↦ 0) (e.symm z) * η z *
                  surfaceMetricVolumeDensityInChart g.metric e z
                ∂MeasureTheory.volume := by
              simp
  refine ⟨U, hU_open, hpU, ?_⟩
  exact
    weaklyHarmonicOnSurface_of_weakLaplaceBeltramiSource_zero
      hzero_source

/--
%%handwave
name:
  Pure Riesz corrections have punctured regular representatives near the pole
statement:
  Near the pole, away from the pole itself, the pure Riesz correction has a
  pointwise harmonic representative which agrees almost everywhere with the
  scalar correction in every chart.
proof:
  The cutoff source vanishes near the pole, so the correction is weakly
  harmonic on a punctured pole neighbourhood.  Apply Weyl's lemma on that
  region.
-/
theorem greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_correction_regularOn_punctured_poleNhd
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X] [T1Space X] [MeasurableEq X]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source) :
    ∃ U : Set X, ∃ H : X → ℝ,
      IsOpen U ∧ p ∈ U ∧
        (∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
          (fun z : ℂ ↦ hdata.correction.toFun (e.symm z))
            =ᵐ[MeasureTheory.volume.restrict
              (e.target ∩ e.symm ⁻¹' (U ∩ {x : X | x ≠ p}))]
            (fun z : ℂ ↦ H (e.symm z))) ∧
          IsHarmonicOnSurface (U ∩ {x : X | x ≠ p}) H := by
  rcases
      greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_correction_weaklyHarmonicOn_poleNhd
        hdata with
    ⟨U, hU_open, hpU, hweak⟩
  rcases
      surfaceWeylHarmonicRepresentative_of_weaklyHarmonicOnSurface
        hconformal hweak with
    ⟨H, hrep, hharmonic⟩
  exact ⟨U, H, hU_open, hpU, hrep, hharmonic⟩

/--
%%handwave
name:
  Pure Riesz corrections have regular representatives near the pole
statement:
  Near the pole, the pure Riesz correction has a pointwise harmonic
  representative which agrees almost everywhere with the scalar correction
  in every chart.
proof:
  The cutoff source vanishes in a full neighbourhood of the pole, so the
  correction is weakly harmonic there.  Weyl's lemma gives the harmonic
  representative on that neighbourhood.
-/
theorem greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_correction_regularOn_full_poleNhd
    {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source) :
    ∃ U : Set X, ∃ H : X → ℝ,
      IsOpen U ∧ p ∈ U ∧
        (∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
          (fun z : ℂ ↦ hdata.correction.toFun (e.symm z))
            =ᵐ[MeasureTheory.volume.restrict
              (e.target ∩ e.symm ⁻¹' U)]
            (fun z : ℂ ↦ H (e.symm z))) ∧
          IsHarmonicOnSurface U H := by
  rcases
      greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_correction_weaklyHarmonicOn_full_poleNhd
        hdata with
    ⟨U, hU_open, hpU, hweak⟩
  rcases
      surfaceWeylHarmonicRepresentative_of_weaklyHarmonicOnSurface
        hconformal hweak with
    ⟨H, hrep, hharmonic⟩
  exact ⟨U, H, hU_open, hpU, hrep, hharmonic⟩

/--
%%handwave
name:
  Weakly harmonic local energy potentials have regular representatives
statement:
  A weakly harmonic local energy potential on the punctured surface has a
  pointwise harmonic representative which agrees with the Sobolev potential
  locally in every chart away from the pole.
proof:
  Apply Euclidean Weyl's lemma in each holomorphic chart to get harmonic
  representatives on chart regions.  On chart overlaps the representatives
  agree almost everywhere with the same Sobolev function, hence agree
  pointwise by harmonicity and continuity.  Glue the compatible chart
  representatives to a global surface function.
-/
theorem exists_regularLocalEnergyPotentialRepresentative_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X] [MeasurableEq X]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g)
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hweak :
      IsWeaklyHarmonicOnSurface g {x : X | x ≠ p}
        (localEnergyGreenPotential φ h)) :
    ∃ G : X → ℝ,
      (∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ h (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w))) ∧
        IsHarmonicOnSurface {x : X | x ≠ p} G := by
  exact
    surfaceWeylHarmonicRepresentative_of_weaklyHarmonicOnSurface
      hconformal hweak

/--
%%handwave
name:
  Punctured pointed-coordinate filters agree
statement:
  The neighborhood filter of the puncture restricted to a pointed coordinate
  source and with the puncture removed is the ordinary punctured neighborhood
  filter.
proof:
  The coordinate source is an open neighborhood of the marked point, so
  intersecting the punctured neighborhood filter with it does not change the
  filter.
-/
theorem pointedCoordinate_punctured_nhdsWithin_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) :
    𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p = 𝓝[≠] p := by
  have hsource_mem : χ.chart.source ∈ 𝓝[{x : X | x ≠ p}] p :=
    mem_nhdsWithin_of_mem_nhds
      (χ.chart.open_source.mem_nhds χ.base_mem_source)
  simpa using nhdsWithin_inter_of_mem hsource_mem

/--
%%handwave
name:
  Pointed-coordinate logarithmic distances differ by a bounded amount
statement:
  For two pointed coordinates at the same pole, the two logarithmic coordinate
  distances differ by a bounded amount near the puncture.
proof:
  The transition maps between the coordinates are locally Lipschitz up to a
  constant in both directions.  Taking logarithms gives upper and lower
  bounds for the difference of the logarithmic distances.
-/
theorem pointedCoordinate_log_distance_difference_eventually_bounded
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ ψ : PointedSurfaceCoordinate X p) :
    ∃ M : ℝ,
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        ‖Real.log ‖χ.chart x - χ.chart p‖ -
          Real.log ‖ψ.chart x - ψ.chart p‖‖ ≤ M := by
  rcases pointedCoordinate_distances_eventually_le_mul X χ ψ with
    ⟨Cχψ, hCχψ_one, hCχψ⟩
  rcases pointedCoordinate_distances_eventually_le_mul X ψ χ with
    ⟨Cψχ, hCψχ_one, hCψχ⟩
  refine ⟨max (Real.log Cχψ) (Real.log Cψχ), ?_⟩
  have hCχψ_pos : 0 < Cχψ := lt_of_lt_of_le zero_lt_one hCχψ_one
  have hCψχ_pos : 0 < Cψχ := lt_of_lt_of_le zero_lt_one hCψχ_one
  have hCχψ_on_χ :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        x ∈ χ.chart.source ∧
          ‖χ.chart x - χ.chart p‖ ≤
            Cχψ * ‖ψ.chart x - ψ.chart p‖ := by
    have hpunct :
        ∀ᶠ x in 𝓝[≠] p,
          x ∈ χ.chart.source ∧
            ‖χ.chart x - χ.chart p‖ ≤
              Cχψ * ‖ψ.chart x - ψ.chart p‖ := by
      simpa [pointedCoordinate_punctured_nhdsWithin_eq ψ] using hCχψ
    simpa [pointedCoordinate_punctured_nhdsWithin_eq χ] using hpunct
  have hψ_source_on_χ :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        x ∈ ψ.chart.source :=
    (pointedCoordinate_eventually_mem_inner_ball X ψ χ zero_lt_one).mono
      (fun _ hx ↦ hx.1)
  filter_upwards
    [hCχψ_on_χ, hCψχ, hψ_source_on_χ, self_mem_nhdsWithin]
    with x hxχ_le hxψ_le hxψ_source hxχ
  have hxχ_source : x ∈ χ.chart.source := hxχ.1
  have hxne : x ≠ p := hxχ.2
  have hxψ_source' : x ∈ ψ.chart.source := hxψ_source
  have hχ_ne : χ.chart x ≠ χ.chart p := by
    intro hEq
    exact hxne (χ.chart.injOn hxχ_source χ.base_mem_source hEq)
  have hψ_ne : ψ.chart x ≠ ψ.chart p := by
    intro hEq
    exact hxne (ψ.chart.injOn hxψ_source' ψ.base_mem_source hEq)
  have hχ_pos : 0 < ‖χ.chart x - χ.chart p‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hχ_ne)
  have hψ_pos : 0 < ‖ψ.chart x - ψ.chart p‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hψ_ne)
  have hupper :
      Real.log ‖χ.chart x - χ.chart p‖ -
          Real.log ‖ψ.chart x - ψ.chart p‖ ≤ Real.log Cχψ := by
    have hlog_le :
        Real.log ‖χ.chart x - χ.chart p‖ ≤
          Real.log Cχψ + Real.log ‖ψ.chart x - ψ.chart p‖ := by
      calc
        Real.log ‖χ.chart x - χ.chart p‖
            ≤ Real.log (Cχψ * ‖ψ.chart x - ψ.chart p‖) :=
              Real.log_le_log hχ_pos hxχ_le.2
        _ = Real.log Cχψ + Real.log ‖ψ.chart x - ψ.chart p‖ := by
              rw [Real.log_mul hCχψ_pos.ne' hψ_pos.ne']
    linarith
  have hlower_aux :
      Real.log ‖ψ.chart x - ψ.chart p‖ -
          Real.log ‖χ.chart x - χ.chart p‖ ≤ Real.log Cψχ := by
    have hlog_le :
        Real.log ‖ψ.chart x - ψ.chart p‖ ≤
          Real.log Cψχ + Real.log ‖χ.chart x - χ.chart p‖ := by
      calc
        Real.log ‖ψ.chart x - ψ.chart p‖
            ≤ Real.log (Cψχ * ‖χ.chart x - χ.chart p‖) :=
              Real.log_le_log hψ_pos hxψ_le.2
        _ = Real.log Cψχ + Real.log ‖χ.chart x - χ.chart p‖ := by
              rw [Real.log_mul hCψχ_pos.ne' hχ_pos.ne']
    linarith
  have habs :
      |Real.log ‖χ.chart x - χ.chart p‖ -
          Real.log ‖ψ.chart x - ψ.chart p‖| ≤
        max (Real.log Cχψ) (Real.log Cψχ) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [hlower_aux, le_max_right (Real.log Cχψ) (Real.log Cψχ)]
    · linarith [hupper, le_max_left (Real.log Cχψ) (Real.log Cψχ)]
  simpa [Real.norm_eq_abs] using habs

/--
%%handwave
name:
  Regular pure Riesz potentials have the logarithmic singularity
statement:
  The Weyl-regular representative of the pure Riesz energy potential has the
  standard removable logarithmic singularity at the pole.
proof:
  Near the pole the cutoff model is exactly the negative logarithm.  The
  regular representative of the correction part is harmonic on the punctured
  model chart and has finite pure energy, so the logarithmically corrected
  potential extends harmonically across the pole.
-/
theorem greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_regular_logarithmic_singularity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [RiemannSurface X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (_hcap : HasPureDirichletCapacityAtInfinity g)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source)
    (G : X → ℝ)
    (hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ hdata.correction (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w)))
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ H : X → ℝ,
        IsHarmonicOnSurface χ.chart.source H ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            G x + Real.log ‖χ.chart x - χ.chart p‖ = H x := by
  classical
  rcases
      greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_correction_regularOn_full_poleNhd
        hconformal hdata with
    ⟨U, Hcorr, hU_open, hpU, hHcorr_rep, hHcorr_harmonic⟩
  let ψ : PointedSurfaceCoordinate X p := φ.coordinate
  have hmodel_eqOn :
      (((ψ.chart.target ∩ ψ.chart.symm ⁻¹' {x : X | x ≠ p}) ∩
          {z : ℂ | ‖z - ψ.chart p‖ < φ.innerRadius}) ∩
          ψ.chart.symm ⁻¹' U).EqOn
        (fun z : ℂ ↦
          G (ψ.chart.symm z) +
            Real.log ‖z - ψ.chart p‖)
        (fun z : ℂ ↦ Hcorr (ψ.chart.symm z)) := by
    simpa [ψ] using
      regularLocalEnergyGreenPotential_modelCoordinate_corrected_eqOn_of_local_harmonic_correction
        φ hdata.correction G Hcorr hU_open hharmonic hrep
        hHcorr_harmonic hHcorr_rep
  have hmodel_eq_event :
      ∀ᶠ x in 𝓝[ψ.chart.source ∩ {x : X | x ≠ p}] p,
        G x + Real.log ‖ψ.chart x - ψ.chart p‖ = Hcorr x := by
    have hdist_cont :
        ContinuousAt
          (fun x : X ↦ ‖ψ.chart x - ψ.chart p‖) p :=
      (ψ.chart.continuousAt ψ.base_mem_source).sub continuousAt_const |>.norm
    have hball_nhds :
        {x : X | ‖ψ.chart x - ψ.chart p‖ < φ.innerRadius} ∈ 𝓝 p :=
      hdist_cont.preimage_mem_nhds
        (Iio_mem_nhds (by simpa using φ.innerRadius_pos))
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hpU),
        mem_nhdsWithin_of_mem_nhds hball_nhds,
        self_mem_nhdsWithin]
      with x hxU hxradius hxpunct
    have hxsource : x ∈ ψ.chart.source := hxpunct.1
    have hxne : x ≠ p := hxpunct.2
    have hzΩ :
        ψ.chart x ∈
          (((ψ.chart.target ∩ ψ.chart.symm ⁻¹' {x : X | x ≠ p}) ∩
              {z : ℂ | ‖z - ψ.chart p‖ < φ.innerRadius}) ∩
              ψ.chart.symm ⁻¹' U) := by
      refine ⟨⟨⟨ψ.chart.map_source hxsource, ?_⟩, ?_⟩, ?_⟩
      · simpa [ψ.chart.left_inv hxsource] using hxne
      · simpa using hxradius
      · simpa [ψ.chart.left_inv hxsource] using hxU
    have heq := hmodel_eqOn hzΩ
    simpa [ψ.chart.left_inv hxsource] using heq
  intro χ
  let corrected : X → ℝ := fun x : X ↦
    G x + Real.log ‖χ.chart x - χ.chart p‖
  have hcorr_harm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) corrected := by
    simpa [corrected] using
      regularLocalEnergyGreenPotential_corrected_harmonicOn_punctured_coordinate
        φ hdata.correction G hharmonic χ
  rcases pointedCoordinate_log_distance_difference_local_harmonic_extension
      X χ ψ with
    ⟨V, Hratio, hV_open, hpV, hVχ, hHratio_harm, hratio_event⟩
  let N : Set X := V ∩ U
  let Hlocal : X → ℝ := fun x : X ↦ Hcorr x + Hratio x
  have hN_open : IsOpen N := hV_open.inter hU_open
  have hpN : p ∈ N := ⟨hpV, hpU⟩
  have hNχ : N ⊆ χ.chart.source := by
    intro x hx
    exact hVχ hx.1
  have hHlocal_harm : IsHarmonicOnSurface N Hlocal := by
    have hcorr_N : IsHarmonicOnSurface N Hcorr :=
      harmonicOnSurface_mono (fun x hx ↦ hx.2) hHcorr_harmonic
    have hratio_N : IsHarmonicOnSurface N Hratio :=
      harmonicOnSurface_mono (fun x hx ↦ hx.1) hHratio_harm
    simpa [Hlocal] using harmonicOnSurface_add hcorr_N hratio_N
  have hmodel_on_χ :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        G x + Real.log ‖ψ.chart x - ψ.chart p‖ = Hcorr x := by
    have hpunct :
        ∀ᶠ x in 𝓝[≠] p,
          G x + Real.log ‖ψ.chart x - ψ.chart p‖ = Hcorr x := by
      simpa [pointedCoordinate_punctured_nhdsWithin_eq ψ] using hmodel_eq_event
    simpa [pointedCoordinate_punctured_nhdsWithin_eq χ] using hpunct
  have heq_local :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        corrected x = Hlocal x := by
    filter_upwards [hmodel_on_χ, hratio_event] with x hmodel hratio
    let lχ : ℝ := Real.log ‖χ.chart x - χ.chart p‖
    let lψ : ℝ := Real.log ‖ψ.chart x - ψ.chart p‖
    calc
      corrected x = (G x + lψ) + (lχ - lψ) := by
        dsimp [corrected, lχ, lψ]
        ring
      _ = Hcorr x + Hratio x := by
        rw [hmodel, hratio]
      _ = Hlocal x := rfl
  rcases bounded_harmonicOn_punctured_pointed_coordinate_local_extension_globalizes
      X χ corrected Hlocal hcorr_harm hN_open hpN hNχ hHlocal_harm heq_local with
    ⟨Hχ, hHχ, heqχ⟩
  exact ⟨Hχ, hHχ, by simpa [corrected] using heqχ⟩

end Uniformization

end JJMath
