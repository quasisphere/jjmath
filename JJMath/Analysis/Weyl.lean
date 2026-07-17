import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.MeanValue
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.Ascoli
import JJMath.Uniformization.Perron
import JJMath.Analysis.Sobolev
import JJMath.Analysis.Sobolev.ACL
import JJMath.Uniformization.Subharmonic

/-!
# Weyl's lemma on surface charts

This file isolates the local regularity input needed for the Green-function
energy method.  The intended route is deliberately narrow: first show that the
energy Green candidate is weakly harmonic on the punctured surface, then apply
Weyl's lemma in conformal surface coordinates to obtain ordinary harmonicity.
-/

namespace JJMath

open MeasureTheory
open ContinuousLinearMap
open scoped Manifold Topology ENNReal ContDiff Convolution Interval

namespace Uniformization

/--
%%handwave
name:
  Coordinate metric pairing for a weak gradient and a test differential
statement:
  In a surface chart, the metric weak-gradient/test pairing is the inverse
  metric coefficient contraction \(g^{ij}\xi_i\partial_j\eta\).
-/
noncomputable def surfaceMetricWeakGradientCoordinatePairingInChart {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ)
    (ξ : ℂ →L[ℝ] ℝ) (dη : ℂ →L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    surfaceMetricInverseGramCoeffInChart g.metric e z i j *
      ξ (surfaceChartTangentMap e z (complexCoordinateVector i)) *
        dη (complexCoordinateVector j)

private theorem surfaceMetricWeakGradientCoordinatePairingInChart_add_left
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ)
    (ξ₁ ξ₂ : ℂ →L[ℝ] ℝ) (dη : ℂ →L[ℝ] ℝ) :
    surfaceMetricWeakGradientCoordinatePairingInChart g e z (ξ₁ + ξ₂) dη =
      surfaceMetricWeakGradientCoordinatePairingInChart g e z ξ₁ dη +
        surfaceMetricWeakGradientCoordinatePairingInChart g e z ξ₂ dη := by
  simp only [surfaceMetricWeakGradientCoordinatePairingInChart,
    ContinuousLinearMap.add_apply]
  calc
    ∑ i : Fin 2, ∑ j : Fin 2,
        surfaceMetricInverseGramCoeffInChart g.metric e z i j *
            (ξ₁ (surfaceChartTangentMap e z (complexCoordinateVector i)) +
              ξ₂ (surfaceChartTangentMap e z (complexCoordinateVector i))) *
          dη (complexCoordinateVector j)
        = ∑ i : Fin 2,
            ((∑ j : Fin 2,
                surfaceMetricInverseGramCoeffInChart g.metric e z i j *
                    ξ₁ (surfaceChartTangentMap e z (complexCoordinateVector i)) *
                  dη (complexCoordinateVector j)) +
              (∑ j : Fin 2,
                surfaceMetricInverseGramCoeffInChart g.metric e z i j *
                    ξ₂ (surfaceChartTangentMap e z (complexCoordinateVector i)) *
                  dη (complexCoordinateVector j))) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
    _ = (∑ i : Fin 2, ∑ j : Fin 2,
            surfaceMetricInverseGramCoeffInChart g.metric e z i j *
                ξ₁ (surfaceChartTangentMap e z (complexCoordinateVector i)) *
              dη (complexCoordinateVector j)) +
          (∑ i : Fin 2, ∑ j : Fin 2,
            surfaceMetricInverseGramCoeffInChart g.metric e z i j *
                ξ₂ (surfaceChartTangentMap e z (complexCoordinateVector i)) *
              dη (complexCoordinateVector j)) := by
            rw [Finset.sum_add_distrib]

/--
%%handwave
name:
  Intrinsic local Sobolev regularity on a surface
statement:
  A function is locally \(W^{1,2}\) on a surface region if its distributional
  weak gradient is represented by a cotangent field whose intrinsic
  Hilbert--Schmidt norm is square-integrable on compact subsets of the
  region, and the function itself is square-integrable on those compact
  subsets.
-/
def IsIntrinsicLocalSobolevH1OnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    (g : BackgroundSurfaceMetricOnSurface X) (U : Set X) (u : X → ℝ)
    (du : X → ℂ →L[ℝ] ℝ) : Prop :=
  IsWeakGradientOnRegion U u du ∧
    ∀ K : Set X, IsCompact K → K ⊆ U →
      MemLp u 2 (g.volume.restrict K) ∧
        SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric
          (g.volume.restrict K)
          (SurfaceCotangentField.ofCoordinateField du)

/--
%%handwave
name:
  Intrinsic local Sobolev regularity restricts to smaller regions
statement:
  If a function is locally \(W^{1,2}\) on a surface region, then it is locally
  \(W^{1,2}\) on every smaller region, with the same weak gradient.
proof:
  Weak gradients restrict to smaller regions, and compact subsets of the
  smaller region are compact subsets of the larger region.
-/
theorem IsIntrinsicLocalSobolevH1OnSurface.mono_set {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {V U : Set X}
    {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (hlocal : IsIntrinsicLocalSobolevH1OnSurface g U u du)
    (hVU : V ⊆ U) :
    IsIntrinsicLocalSobolevH1OnSurface g V u du := by
  refine ⟨hlocal.1.mono_set hVU, ?_⟩
  intro K hK hKV
  exact hlocal.2 K hK (hKV.trans hVU)

private theorem surfaceCotangentFieldMemHilbertSchmidtL2_add
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel 1 X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : SmoothRiemannianMetricOnSurface X} {μ : Measure X}
    {du dv : X → ℂ →L[ℝ] ℝ}
    (hdu :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g μ
        (SurfaceCotangentField.ofCoordinateField du))
    (hdv :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g μ
        (SurfaceCotangentField.ofCoordinateField dv)) :
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g μ
      (SurfaceCotangentField.ofCoordinateField (du + dv)) := by
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.toManifoldMetric
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.toManifoldMetric
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber
        (I := SurfaceRealModel) (X := X) (E := ℝ)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  letI (x : X) :
      InnerProductSpace ℝ
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  have hG_inner :
      ∀ (x : X)
        (A B : ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x),
        G.fiberInner x A B = inner ℝ A B := by
    intro x A B
    rfl
  have hadd :
      HilbertBundleSectionMemL2 G μ
        (SurfaceCotangentField.ofCoordinateField du +
          SurfaceCotangentField.ofCoordinateField dv) :=
    hilbertBundleSectionMemL2_add
      (I := SurfaceRealModel) (G := G) hG_inner μ hdu hdv
  simpa [SurfaceDifferentialFieldMemHilbertSchmidtL2,
    ManifoldDifferentialFieldMemHilbertSchmidtL2,
    SurfaceCotangentField.ofCoordinateField, Pi.add_apply, G] using hadd

/--
%%handwave
name:
  Weak Laplace-Beltrami equation with source
statement:
  A locally \(W^{1,2}\) function satisfies the weak Laplace-Beltrami equation
  with source \(F\) on an open surface region if its weak gradient satisfies
  the integration-by-parts identity against every compactly supported smooth
  test function whose support lies in the region.
-/
def IsWeakLaplaceBeltramiSourceOnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    (g : BackgroundSurfaceMetricOnSurface X) (U : Set X)
    (u F : X → ℝ) : Prop :=
  IsOpen U ∧
    ∃ du : X → ℂ →L[ℝ] ℝ,
      IsIntrinsicLocalSobolevH1OnSurface g U u du ∧
        ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
          ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction
              (surfaceChartRegion e U),
            Integrable
                (fun z ↦
                  surfaceMetricWeakGradientCoordinatePairingInChart g e z
                    (du (e.symm z))
                    (fderiv ℝ (η : ℂ → ℝ) z) *
                      surfaceMetricVolumeDensityInChart g.metric e z)
                (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
              Integrable
                (fun z ↦
                  F (e.symm z) * η z *
                    surfaceMetricVolumeDensityInChart g.metric e z)
                (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
                ∫ z in surfaceChartRegion e U,
                    surfaceMetricWeakGradientCoordinatePairingInChart g e z
                      (du (e.symm z))
                      (fderiv ℝ (η : ℂ → ℝ) z) *
                        surfaceMetricVolumeDensityInChart g.metric e z
                    ∂MeasureTheory.volume =
                  -∫ z in surfaceChartRegion e U,
                    F (e.symm z) * η z *
                      surfaceMetricVolumeDensityInChart g.metric e z
                    ∂MeasureTheory.volume

/--
%%handwave
name:
  Weak Laplace-Beltrami source equations restrict to smaller regions
statement:
  A weak Laplace-Beltrami equation on an open surface region remains valid on
  every smaller open surface region, with the same weak gradient and source.
proof:
  A compactly supported coordinate test in the smaller region is also a test
  in the larger region.  The test and its derivative vanish outside the
  smaller coordinate region, so the chart integrals over the larger and
  smaller regions agree.
-/
theorem IsWeakLaplaceBeltramiSourceOnSurface.mono_set {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {V U : Set X}
    {u F : X → ℝ}
    (hweak : IsWeakLaplaceBeltramiSourceOnSurface g U u F)
    (hV_open : IsOpen V) (hVU : V ⊆ U) :
    IsWeakLaplaceBeltramiSourceOnSurface g V u F := by
  rcases hweak with ⟨_hU_open, du, hlocal, htest⟩
  refine ⟨hV_open, du, hlocal.mono_set hVU, ?_⟩
  intro e he η
  let ΩV : Set ℂ := surfaceChartRegion e V
  let ΩU : Set ℂ := surfaceChartRegion e U
  have hΩVU : ΩV ⊆ ΩU := by
    intro z hz
    exact ⟨hz.1, hVU hz.2⟩
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction ΩU :=
    η.mono hΩVU
  rcases htest e he ψ with ⟨hgradΩ, hsourceΩ, heqΩ⟩
  let gradTerm : ℂ → ℝ :=
    fun z ↦
      surfaceMetricWeakGradientCoordinatePairingInChart g e z
        (du (e.symm z))
        (fderiv ℝ (η : ℂ → ℝ) z) *
          surfaceMetricVolumeDensityInChart g.metric e z
  let sourceTerm : ℂ → ℝ :=
    fun z ↦
      F (e.symm z) * η z *
        surfaceMetricVolumeDensityInChart g.metric e z
  have hgrad_int_V :
      Integrable gradTerm (MeasureTheory.volume.restrict ΩV) := by
    have hres := hgradΩ.restrict (s := ΩV)
    simpa [gradTerm, ψ, ΩV, ΩU,
      Measure.restrict_restrict_of_subset hΩVU] using hres
  have hsource_int_V :
      Integrable sourceTerm (MeasureTheory.volume.restrict ΩV) := by
    have hres := hsourceΩ.restrict (s := ΩV)
    simpa [sourceTerm, ψ, ΩV, ΩU,
      Measure.restrict_restrict_of_subset hΩVU] using hres
  have hgrad_zero_V : ∀ z : ℂ, z ∉ ΩV → gradTerm z = 0 := by
    intro z hzV
    have hdη_zero : fderiv ℝ (η : ℂ → ℝ) z = 0 := by
      ext v
      have hz_not :
          z ∉ tsupport (fun y : ℂ ↦ fderiv ℝ (η : ℂ → ℝ) y v) := by
        intro hz
        exact hzV <| η.support_subset <|
          (tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (η : ℂ → ℝ)) v) hz
      exact
        image_eq_zero_of_notMem_tsupport
          (f := fun y : ℂ ↦ fderiv ℝ (η : ℂ → ℝ) y v) hz_not
    simp [gradTerm, hdη_zero, surfaceMetricWeakGradientCoordinatePairingInChart]
  have hsource_zero_V : ∀ z : ℂ, z ∉ ΩV → sourceTerm z = 0 := by
    intro z hzV
    have hz_not : z ∉ tsupport (η : ℂ → ℝ) := by
      intro hz
      exact hzV (η.support_subset hz)
    have hη_zero : η z = 0 := image_eq_zero_of_notMem_tsupport hz_not
    simp [sourceTerm, hη_zero]
  have hgrad_zero_U : ∀ z : ℂ, z ∉ ΩU → gradTerm z = 0 := by
    intro z hzU
    exact hgrad_zero_V z (fun hzV ↦ hzU (hΩVU hzV))
  have hsource_zero_U : ∀ z : ℂ, z ∉ ΩU → sourceTerm z = 0 := by
    intro z hzU
    exact hsource_zero_V z (fun hzV ↦ hzU (hΩVU hzV))
  have hgrad_V_eq_U :
      ∫ z in ΩV, gradTerm z ∂MeasureTheory.volume =
        ∫ z in ΩU, gradTerm z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgrad_zero_V,
      setIntegral_eq_integral_of_forall_compl_eq_zero hgrad_zero_U]
  have hsource_V_eq_U :
      ∫ z in ΩV, sourceTerm z ∂MeasureTheory.volume =
        ∫ z in ΩU, sourceTerm z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsource_zero_V,
      setIntegral_eq_integral_of_forall_compl_eq_zero hsource_zero_U]
  refine ⟨?_, ?_, ?_⟩
  · simpa [gradTerm, ΩV] using hgrad_int_V
  · simpa [sourceTerm, ΩV] using hsource_int_V
  · calc
      ∫ z in surfaceChartRegion e V,
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (du (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z
          ∂MeasureTheory.volume
          = ∫ z in ΩV, gradTerm z ∂MeasureTheory.volume := rfl
      _ = ∫ z in ΩU, gradTerm z ∂MeasureTheory.volume := hgrad_V_eq_U
      _ = -∫ z in ΩU, sourceTerm z ∂MeasureTheory.volume := by
            simpa [gradTerm, sourceTerm, ψ, ΩU] using heqΩ
      _ = -∫ z in ΩV, sourceTerm z ∂MeasureTheory.volume := by
            rw [hsource_V_eq_U]
      _ = -∫ z in surfaceChartRegion e V,
          F (e.symm z) * η z *
            surfaceMetricVolumeDensityInChart g.metric e z
          ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Weak Laplace-Beltrami sources may be changed on the region
statement:
  If two source functions agree on the open region of a weak
  Laplace-Beltrami equation, either source may be used in the weak equation.
proof:
  In each chart region the pulled-back source terms agree pointwise, hence
  almost everywhere, so their integrability and integrals are identical.
-/
theorem IsWeakLaplaceBeltramiSourceOnSurface.congr_source {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X}
    {u F F' : X → ℝ}
    (hweak : IsWeakLaplaceBeltramiSourceOnSurface g U u F)
    (hFF' : ∀ x ∈ U, F x = F' x) :
    IsWeakLaplaceBeltramiSourceOnSurface g U u F' := by
  rcases hweak with ⟨hU_open, du, hlocal, htest⟩
  refine ⟨hU_open, du, hlocal, ?_⟩
  intro e he η
  rcases htest e he η with ⟨hgrad, hsource, heq⟩
  let Ω : Set ℂ := surfaceChartRegion e U
  let sourceTerm : ℂ → ℝ :=
    fun z ↦
      F (e.symm z) * η z *
        surfaceMetricVolumeDensityInChart g.metric e z
  let sourceTerm' : ℂ → ℝ :=
    fun z ↦
      F' (e.symm z) * η z *
        surfaceMetricVolumeDensityInChart g.metric e z
  have hΩ_meas : MeasurableSet Ω := by
    simpa [Ω, surfaceChartRegion] using
      (e.isOpen_inter_preimage_symm hU_open).measurableSet
  have hsource_ae :
      sourceTerm =ᵐ[MeasureTheory.volume.restrict Ω] sourceTerm' := by
    refine ae_restrict_of_forall_mem hΩ_meas ?_
    intro z hz
    have hxU : e.symm z ∈ U := by
      simpa [Ω, surfaceChartRegion] using hz.2
    simp [sourceTerm, sourceTerm', hFF' (e.symm z) hxU]
  refine ⟨hgrad, ?_, ?_⟩
  · exact hsource.congr hsource_ae
  · calc
      ∫ z in surfaceChartRegion e U,
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (du (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z
          ∂MeasureTheory.volume
          = -∫ z in surfaceChartRegion e U,
              F (e.symm z) * η z *
                surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume := heq
      _ = -∫ z in surfaceChartRegion e U,
              F' (e.symm z) * η z *
                surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume := by
            congr 1
            exact integral_congr_ae hsource_ae

/--
%%handwave
name:
  Weakly harmonic surface function
statement:
  A locally \(W^{1,2}\) function is weakly harmonic on an open surface region
  if its weak gradient pairs to zero with the gradients of all compactly
  supported smooth test functions inside the region.
-/
def IsWeaklyHarmonicOnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    (g : BackgroundSurfaceMetricOnSurface X) (U : Set X)
    (u : X → ℝ) : Prop :=
  IsOpen U ∧
    ∃ du : X → ℂ →L[ℝ] ℝ,
      IsIntrinsicLocalSobolevH1OnSurface g U u du ∧
        ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
          ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction
              (surfaceChartRegion e U),
            Integrable
                (fun z ↦
                  surfaceMetricWeakGradientCoordinatePairingInChart g e z
                    (du (e.symm z))
                    (fderiv ℝ (η : ℂ → ℝ) z) *
                      surfaceMetricVolumeDensityInChart g.metric e z)
                (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
              ∫ z in surfaceChartRegion e U,
                  surfaceMetricWeakGradientCoordinatePairingInChart g e z
                    (du (e.symm z))
                    (fderiv ℝ (η : ℂ → ℝ) z) *
                      surfaceMetricVolumeDensityInChart g.metric e z
                  ∂MeasureTheory.volume = 0

/--
%%handwave
name:
  Weakly harmonic regions are open
statement:
  The region in the definition of weak harmonicity is open.
-/
theorem IsWeaklyHarmonicOnSurface.isOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hweak : IsWeaklyHarmonicOnSurface g U u) :
    IsOpen U :=
  hweak.1

/--
%%handwave
name:
  Weakly harmonic functions have local Sobolev representatives
statement:
  A weakly harmonic function carries a chosen locally \(W^{1,2}\) weak
  gradient satisfying the zero-source test identity.
-/
theorem IsWeaklyHarmonicOnSurface.exists_localSobolev_gradient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hweak : IsWeaklyHarmonicOnSurface g U u) :
    ∃ du : X → ℂ →L[ℝ] ℝ,
      IsIntrinsicLocalSobolevH1OnSurface g U u du ∧
        ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
          ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction
              (surfaceChartRegion e U),
            Integrable
                (fun z ↦
                  surfaceMetricWeakGradientCoordinatePairingInChart g e z
                    (du (e.symm z))
                    (fderiv ℝ (η : ℂ → ℝ) z) *
                      surfaceMetricVolumeDensityInChart g.metric e z)
                (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
              ∫ z in surfaceChartRegion e U,
                  surfaceMetricWeakGradientCoordinatePairingInChart g e z
                    (du (e.symm z))
                    (fderiv ℝ (η : ℂ → ℝ) z) *
                      surfaceMetricVolumeDensityInChart g.metric e z
                  ∂MeasureTheory.volume = 0 :=
  hweak.2

/--
%%handwave
name:
  Zero-source weak equations are weakly harmonic
statement:
  A weak Laplace-Beltrami equation whose source is identically zero is a
  weak harmonic equation.
proof:
  The source term in the weak integration-by-parts identity is the integral
  of the zero function, hence vanishes.
-/
theorem weaklyHarmonicOnSurface_of_weakLaplaceBeltramiSource_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hweak :
      IsWeakLaplaceBeltramiSourceOnSurface g U u (fun _ : X ↦ 0)) :
    IsWeaklyHarmonicOnSurface g U u := by
  rcases hweak with ⟨hU_open, du, hlocal, htest⟩
  refine ⟨hU_open, du, hlocal, ?_⟩
  intro e he η
  rcases htest e he η with ⟨hgrad, _hsource, hzero⟩
  refine ⟨hgrad, ?_⟩
  calc
    ∫ z in surfaceChartRegion e U,
        surfaceMetricWeakGradientCoordinatePairingInChart g e z
          (du (e.symm z))
          (fderiv ℝ (η : ℂ → ℝ) z) *
            surfaceMetricVolumeDensityInChart g.metric e z
        ∂MeasureTheory.volume
        = -∫ z in surfaceChartRegion e U,
          (fun _ : X ↦ 0) (e.symm z) * η z *
            surfaceMetricVolumeDensityInChart g.metric e z
          ∂MeasureTheory.volume := hzero
    _ = 0 := by simp

/--
%%handwave
name:
  Euclidean cotangent pairing
statement:
  The Euclidean pairing of two covectors on the complex coordinate plane is
  the sum of their products on the coordinate directions \(1\) and \(i\).
-/
noncomputable def euclideanCotangentPairing
    (ξ η : ℂ →L[ℝ] ℝ) : ℝ :=
  ξ 1 * η 1 + ξ Complex.I * η Complex.I

/--
%%handwave
name:
  Euclidean weak harmonicity
statement:
  A locally weakly differentiable function on a coordinate region is weakly
  harmonic if its weak derivative has zero Euclidean divergence against every
  compactly supported smooth coordinate test.
-/
def IsEuclideanWeaklyHarmonicOn (Ω : Set ℂ) (u : ℂ → ℝ) : Prop :=
  IsOpen Ω ∧
    ∃ du : ℂ → ℂ →L[ℝ] ℝ,
      IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
        ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
          Integrable
              (fun z ↦
                euclideanCotangentPairing (du z)
                  (fderiv ℝ (η : ℂ → ℝ) z))
              (MeasureTheory.volume.restrict Ω) ∧
            ∫ z in Ω,
                euclideanCotangentPairing (du z)
                  (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0

/--
%%handwave
name:
  Euclidean weakly harmonic regions are open
statement:
  The region in the Euclidean weak-harmonicity definition is open.
-/
theorem IsEuclideanWeaklyHarmonicOn.isOpen
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u) :
    IsOpen Ω :=
  hweak.1

/--
%%handwave
name:
  Euclidean weakly harmonic functions have weak gradients
statement:
  A Euclidean weakly harmonic function carries a weak derivative satisfying
  the zero-divergence identity.
-/
theorem IsEuclideanWeaklyHarmonicOn.exists_weakDerivative
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u) :
    ∃ du : ℂ → ℂ →L[ℝ] ℝ,
      IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
        ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
          Integrable
              (fun z ↦
                euclideanCotangentPairing (du z)
                  (fderiv ℝ (η : ℂ → ℝ) z))
              (MeasureTheory.volume.restrict Ω) ∧
            ∫ z in Ω,
                euclideanCotangentPairing (du z)
                  (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0 :=
  hweak.2

/--
%%handwave
name:
  Euclidean weakly harmonic functions are locally integrable
statement:
  A Euclidean weakly harmonic function is locally integrable on its open
  region.
proof:
  The weak-derivative part of the weak harmonicity hypothesis is the standard
  scalar weak-derivative identity.  Local integrability follows by testing in
  a fixed nonzero coordinate direction.
-/
theorem IsEuclideanWeaklyHarmonicOn.locallyIntegrableOn
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u) :
    LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ) := by
  rcases hweak with ⟨hΩ_open, du, hdu, _hzero⟩
  exact
    kinnunenWeakDerivative_function_locallyIntegrableOn_of_nonzero_direction
      hΩ_open
      (by
        simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
          IsWeakDerivativeOnEuclideanRegionWithValues] using hdu)
      (show (1 : ℂ) ≠ 0 by norm_num)

/--
%%handwave
name:
  Euclidean weak gradients are locally integrable in each direction
statement:
  For a Euclidean weakly harmonic function, every directional component of
  its weak derivative is locally integrable on the region.
proof:
  This is the local integrability theorem for the scalar weak-derivative
  identity applied to the weak derivative stored in the weak harmonicity
  hypothesis.
-/
theorem IsEuclideanWeaklyHarmonicOn.weakDerivative_locallyIntegrableOn
    {Ω : Set ℂ} {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u)
    (hdu : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (v : ℂ) :
    LocallyIntegrableOn (fun z ↦ du z v) Ω
      (MeasureTheory.volume : Measure ℂ) := by
  exact
    kinnunenWeakDerivative_directionalDerivative_locallyIntegrableOn
      hweak.isOpen
      (by
        simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
          IsWeakDerivativeOnEuclideanRegionWithValues] using hdu)
      v

/--
%%handwave
name:
  Euclidean mollification
statement:
  The mollification of a function by a compactly supported smooth bump is
  its convolution with the normalized bump.
-/
noncomputable def euclideanMollification
    (φ : ContDiffBump (0 : ℂ)) (u : ℂ → ℝ) : ℂ → ℝ :=
  (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
    (MeasureTheory.volume : Measure ℂ)] u : ℂ → ℝ)

/--
%%handwave
name:
  Mollifications are smooth
statement:
  Convolution of a locally integrable function with a compactly supported
  smooth bump is smooth.
proof:
  This is the standard differentiability theorem for convolution with a
  compactly supported smooth kernel.
-/
theorem euclideanMollification_contDiff
    (φ : ContDiffBump (0 : ℂ)) {u : ℂ → ℝ}
    (hu : LocallyIntegrable u (MeasureTheory.volume : Measure ℂ)) :
    ContDiff ℝ ∞ (euclideanMollification φ u) := by
  dsimp [euclideanMollification]
  exact
    φ.hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) φ.contDiff_normed hu

/--
%%handwave
name:
  Reflected mollifier zero-divergence identity
statement:
  If the support of a reflected mollifier stays inside a Euclidean weakly
  harmonic region, then inserting that reflected mollifier into the weak
  harmonic identity gives a zero global integral.
proof:
  The reflected mollifier is a smooth compactly supported test function on
  the region.  Since its support is contained in the region, the restricted
  integral from the weak formulation is equal to the corresponding global
  integral.
-/
theorem euclideanWeakHarmonic_reflectedMollifier_zeroDivergence
    {Q Ω : Set ℂ} {φ : ContDiffBump (0 : ℂ)}
    (hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {du : ℂ → ℂ →L[ℝ] ℝ}
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0) :
    ∀ z ∈ Q,
      ∫ y : ℂ,
          euclideanCotangentPairing (du y)
            (fderiv ℝ
              (fun y : ℂ ↦
                φ.normed (MeasureTheory.volume : Measure ℂ) (z - y)) y)
          ∂(MeasureTheory.volume : Measure ℂ) = 0 := by
  intro z hzQ
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    scalarWeakSobolev_reflectedMollifierTest z hzQ hthickening
  have hψ_zero := (hzero ψ).2
  have hglobal :
      ∫ y in Ω,
          euclideanCotangentPairing (du y)
            (fderiv ℝ (ψ : ℂ → ℝ) y) ∂MeasureTheory.volume =
        ∫ y : ℂ,
          euclideanCotangentPairing (du y)
            (fderiv ℝ (ψ : ℂ → ℝ) y)
          ∂(MeasureTheory.volume : Measure ℂ) := by
    exact
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := (MeasureTheory.volume : Measure ℂ))
        (s := Ω)
        (f := fun y : ℂ ↦
          euclideanCotangentPairing (du y)
            (fderiv ℝ (ψ : ℂ → ℝ) y))
        fun y hyΩ ↦ by
          have hyψ : y ∉ tsupport (ψ : ℂ → ℝ) :=
            fun hyψ ↦ hyΩ (ψ.support_subset hyψ)
          have hderiv_zero : fderiv ℝ (ψ : ℂ → ℝ) y = 0 :=
            fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (ψ : ℂ → ℝ)) hyψ
          simp [euclideanCotangentPairing, hderiv_zero]
  have htarget :
      (fun y : ℂ ↦
          euclideanCotangentPairing (du y)
            (fderiv ℝ (ψ : ℂ → ℝ) y)) =
        fun y : ℂ ↦
          euclideanCotangentPairing (du y)
            (fderiv ℝ
              (fun y : ℂ ↦
                φ.normed (MeasureTheory.volume : Measure ℂ) (z - y)) y) := by
    rfl
  rw [hglobal] at hψ_zero
  simpa [htarget] using hψ_zero

/--
%%handwave
name:
  Differentiating a Euclidean mollification
statement:
  On a compact set whose mollifier support stays inside the weak-derivative
  region, the classical directional derivative of the mollification equals
  the mollification of the weak directional derivative.
proof:
  This is the standard reflected-mollifier identity: use the reflected kernel
  as a weak-derivative test, then identify the derivative of convolution with
  convolution against the derivative of the kernel.
-/
theorem euclideanMollification_directionalDerivative_eq_convolution_weakDerivative_on_compact
    {Q Ω : Set ℂ} (hQ : IsCompact Q)
    {φ : ContDiffBump (0 : ℂ)}
    (hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    {v : ℂ}
    (hu_int : Integrable u (MeasureTheory.volume : Measure ℂ))
    (hdu_int : Integrable (fun z ↦ du z v)
      (MeasureTheory.volume : Measure ℂ)) :
    ∀ z ∈ Q,
      fderiv ℝ (euclideanMollification φ u) z v =
        ((φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
          (MeasureTheory.volume : Measure ℂ)] (fun y : ℂ ↦ du y v) :
          ℂ → ℝ) z) := by
  intro z hzQ
  let k : ℂ → ℝ := φ.normed (MeasureTheory.volume : Measure ℂ)
  have hkernel :=
    scalarWeakSobolev_mollifier_derivativeKernel_convolution_eq_weakDerivative_convolution_on_compact
      (Q := Q) (Ω := Ω) (φ := φ) hQ hthickening
      (by
        simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
          IsWeakDerivativeOnEuclideanRegionWithValues] using hweak)
      (h := v) hu_int hdu_int z hzQ
  have hclassical :
      fderiv ℝ (euclideanMollification φ u) z =
        (((fderiv ℝ k) ⋆[
          (lsmul ℝ ℝ).precompL ℂ,
          (MeasureTheory.volume : Measure ℂ)] u :
          ℂ → ℂ →L[ℝ] ℝ) z) := by
    exact
      (φ.hasCompactSupport_normed.hasFDerivAt_convolution_left
        (lsmul ℝ ℝ) φ.contDiff_normed hu_int.locallyIntegrable z).fderiv
  calc
    fderiv ℝ (euclideanMollification φ u) z v
        =
        (((fderiv ℝ k) ⋆[
          (lsmul ℝ ℝ).precompL ℂ,
          (MeasureTheory.volume : Measure ℂ)] u :
          ℂ → ℂ →L[ℝ] ℝ) z) v := by
          rw [hclassical]
    _ =
        ((φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
          (MeasureTheory.volume : Measure ℂ)] (fun y : ℂ ↦ du y v) :
          ℂ → ℝ) z) := by
          simpa [k] using hkernel

private theorem euclidean_derivativeKernel_convolution_apply_eq_integral
    (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ}
    (hg_int : Integrable g (MeasureTheory.volume : Measure ℂ))
    (z v : ℂ) :
    ((((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ))) ⋆[
        (lsmul ℝ ℝ).precompL ℂ,
        (MeasureTheory.volume : Measure ℂ)] g :
        ℂ → ℂ →L[ℝ] ℝ) z) v) =
      ∫ y : ℂ,
        fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ)) (z - y) v * g y
        ∂(MeasureTheory.volume : Measure ℂ) := by
  let k : ℂ → ℝ := φ.normed (MeasureTheory.volume : Measure ℂ)
  have hleft_exists :
      ConvolutionExistsAt (fderiv ℝ k) g z
        ((lsmul ℝ ℝ).precompL ℂ) (MeasureTheory.volume : Measure ℂ) := by
    have hk_support : HasCompactSupport (fderiv ℝ k) :=
      φ.hasCompactSupport_normed.fderiv (𝕜 := ℝ)
    have hk_smooth : ContDiff ℝ ∞ k := by
      simpa [k] using
        (φ.contDiff_normed (μ := (MeasureTheory.volume : Measure ℂ)) (n := ⊤))
    have hk_cont : Continuous (fderiv ℝ k) :=
      hk_smooth.continuous_fderiv (by simp)
    exact
      HasCompactSupport.convolutionExists_left
        (μ := (MeasureTheory.volume : Measure ℂ))
        (f := fderiv ℝ k) (g := g)
        (L := (lsmul ℝ ℝ).precompL ℂ)
        hk_support hk_cont hg_int.locallyIntegrable z
  rw [MeasureTheory.convolution_eq_swap]
  rw [ContinuousLinearMap.integral_apply hleft_exists.integrable_swap v]
  rfl

private theorem euclidean_fderiv_normed_convolution_apply_eq_derivativeKernel
    (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ}
    (hg_int : Integrable g (MeasureTheory.volume : Measure ℂ))
    (z v : ℂ) :
    fderiv ℝ
        (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
          (MeasureTheory.volume : Measure ℂ)] g : ℂ → ℝ) z v =
      ((((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ))) ⋆[
        (lsmul ℝ ℝ).precompL ℂ,
        (MeasureTheory.volume : Measure ℂ)] g :
        ℂ → ℂ →L[ℝ] ℝ) z) v) := by
  let k : ℂ → ℝ := φ.normed (MeasureTheory.volume : Measure ℂ)
  have hclassical :
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)] g : ℂ → ℝ) z =
        (((fderiv ℝ k) ⋆[
          (lsmul ℝ ℝ).precompL ℂ,
          (MeasureTheory.volume : Measure ℂ)] g :
          ℂ → ℂ →L[ℝ] ℝ) z) := by
    exact
      (φ.hasCompactSupport_normed.hasFDerivAt_convolution_left
        (lsmul ℝ ℝ) φ.contDiff_normed hg_int.locallyIntegrable z).fderiv
  rw [hclassical]

private theorem euclidean_reflectedKernel_fderiv_apply
    (φ : ContDiffBump (0 : ℂ)) (z y v : ℂ) :
    fderiv ℝ
        (fun y : ℂ ↦
          φ.normed (MeasureTheory.volume : Measure ℂ) (z - y)) y v =
      -fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ)) (z - y) v := by
  let k : ℂ → ℝ := φ.normed (MeasureTheory.volume : Measure ℂ)
  change fderiv ℝ (fun y : ℂ ↦ k (z - y)) y v =
    -fderiv ℝ k (z - y) v
  have hk_smooth : ContDiff ℝ ∞ k := by
    simpa [k] using
      (φ.contDiff_normed (μ := (MeasureTheory.volume : Measure ℂ)) (n := ⊤))
  have hk : DifferentiableAt ℝ k (z - y) :=
    (hk_smooth.differentiable (by simp)) (z - y)
  have hinner : HasFDerivAt (fun y : ℂ ↦ z - y) (-1 : ℂ →L[ℝ] ℂ) y := by
    simpa using (hasFDerivAt_id y).const_sub z
  have hcomp :
      HasFDerivAt (fun y : ℂ ↦ k (z - y))
        ((fderiv ℝ k (z - y)).comp (-1 : ℂ →L[ℝ] ℂ)) y :=
    hk.hasFDerivAt.comp y hinner
  rw [hcomp.fderiv]
  simp

private theorem euclidean_derivativeKernel_mul_integrable
    (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ}
    (hg_int : Integrable g (MeasureTheory.volume : Measure ℂ))
    (z v : ℂ) :
    Integrable
      (fun y : ℂ ↦
        fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ)) (z - y) v * g y)
      (MeasureTheory.volume : Measure ℂ) := by
  let k : ℂ → ℝ := φ.normed (MeasureTheory.volume : Measure ℂ)
  have hleft_exists :
      ConvolutionExistsAt (fderiv ℝ k) g z
        ((lsmul ℝ ℝ).precompL ℂ) (MeasureTheory.volume : Measure ℂ) := by
    have hk_support : HasCompactSupport (fderiv ℝ k) :=
      φ.hasCompactSupport_normed.fderiv (𝕜 := ℝ)
    have hk_smooth : ContDiff ℝ ∞ k := by
      simpa [k] using
        (φ.contDiff_normed (μ := (MeasureTheory.volume : Measure ℂ)) (n := ⊤))
    have hk_cont : Continuous (fderiv ℝ k) :=
      hk_smooth.continuous_fderiv (by simp)
    exact
      HasCompactSupport.convolutionExists_left
        (μ := (MeasureTheory.volume : Measure ℂ))
        (f := fderiv ℝ k) (g := g)
        (L := (lsmul ℝ ℝ).precompL ℂ)
        hk_support hk_cont hg_int.locallyIntegrable z
  have hclm :
      Integrable
        (fun y : ℂ ↦
          ((lsmul ℝ ℝ).precompL ℂ) (fderiv ℝ k (z - y)) (g y))
        (MeasureTheory.volume : Measure ℂ) :=
    hleft_exists.integrable_swap
  have happ := hclm.apply_continuousLinearMap v
  simpa [k, smul_eq_mul] using happ

private theorem euclidean_derivativeKernel_zero_of_notMem_cthickening
    {Q : Set ℂ} (φ : ContDiffBump (0 : ℂ)) {z y v : ℂ}
    (hzQ : z ∈ Q) (hy : y ∉ Metric.cthickening φ.rOut Q) :
    fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ)) (z - y) v = 0 := by
  let k : ℂ → ℝ := φ.normed (MeasureTheory.volume : Measure ℂ)
  have hnot :
      z - y ∉ tsupport (fun x : ℂ ↦ fderiv ℝ k x v) := by
    intro hx
    have hxk : z - y ∈ tsupport k :=
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := k) v) hx
    have hdist : dist y z ≤ φ.rOut := by
      rw [show k = φ.normed (MeasureTheory.volume : Measure ℂ) from rfl] at hxk
      rw [φ.tsupport_normed_eq (μ := (MeasureTheory.volume : Measure ℂ))] at hxk
      simpa [k, dist_eq_norm, norm_sub_rev] using hxk
    exact hy (Metric.mem_cthickening_of_dist_le y z φ.rOut Q hzQ hdist)
  simpa [k] using
    image_eq_zero_of_notMem_tsupport
      (f := fun x : ℂ ↦ fderiv ℝ k x v) hnot

/--
%%handwave
name:
  Mollified weak gradients have zero Euclidean divergence
statement:
  If a reflected mollifier stays inside a Euclidean weakly harmonic region, then
  the two coordinate convolutions of the weak gradient have zero classical
  divergence at the center.
proof:
  Insert the reflected mollifier into the weak zero-divergence identity.  The
  derivative of \(y\mapsto\varphi(z-y)\) is \(-D\varphi(z-y)\).  Splitting the
  two coordinate integrals and identifying them with derivatives of convolution
  gives the desired zero divergence.
-/
theorem euclideanWeakHarmonic_mollifiedWeakGradient_divergence_eq_zero
    {Q Ω : Set ℂ} {φ : ContDiffBump (0 : ℂ)}
    (hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {du : ℂ → ℂ →L[ℝ] ℝ}
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hdu_one_int : Integrable (fun z : ℂ ↦ du z (1 : ℂ))
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_int : Integrable (fun z : ℂ ↦ du z Complex.I)
      (MeasureTheory.volume : Measure ℂ)) :
    ∀ z ∈ Q,
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ du y (1 : ℂ)) : ℂ → ℝ) z (1 : ℂ) +
        fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ du y Complex.I) : ℂ → ℝ) z Complex.I = 0 := by
  intro z hzQ
  let k : ℂ → ℝ := φ.normed (MeasureTheory.volume : Measure ℂ)
  have hweak :=
    euclideanWeakHarmonic_reflectedMollifier_zeroDivergence
      hthickening hzero z hzQ
  have hD_one :
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ du y (1 : ℂ)) : ℂ → ℝ) z (1 : ℂ) =
        ∫ y : ℂ,
          fderiv ℝ k (z - y) (1 : ℂ) * du y (1 : ℂ)
          ∂(MeasureTheory.volume : Measure ℂ) := by
    calc
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ du y (1 : ℂ)) : ℂ → ℝ) z (1 : ℂ)
          =
          ((((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ))) ⋆[
            (lsmul ℝ ℝ).precompL ℂ,
            (MeasureTheory.volume : Measure ℂ)] (fun y : ℂ ↦ du y (1 : ℂ)) :
            ℂ → ℂ →L[ℝ] ℝ) z) (1 : ℂ)) :=
            euclidean_fderiv_normed_convolution_apply_eq_derivativeKernel
              φ hdu_one_int z (1 : ℂ)
      _ = ∫ y : ℂ,
            fderiv ℝ k (z - y) (1 : ℂ) * du y (1 : ℂ)
            ∂(MeasureTheory.volume : Measure ℂ) := by
          simpa [k] using
            euclidean_derivativeKernel_convolution_apply_eq_integral
              φ hdu_one_int z (1 : ℂ)
  have hD_I :
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ du y Complex.I) : ℂ → ℝ) z Complex.I =
        ∫ y : ℂ,
          fderiv ℝ k (z - y) Complex.I * du y Complex.I
          ∂(MeasureTheory.volume : Measure ℂ) := by
    calc
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ du y Complex.I) : ℂ → ℝ) z Complex.I
          =
          ((((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ))) ⋆[
            (lsmul ℝ ℝ).precompL ℂ,
            (MeasureTheory.volume : Measure ℂ)] (fun y : ℂ ↦ du y Complex.I) :
            ℂ → ℂ →L[ℝ] ℝ) z) Complex.I) :=
            euclidean_fderiv_normed_convolution_apply_eq_derivativeKernel
              φ hdu_I_int z Complex.I
      _ = ∫ y : ℂ,
            fderiv ℝ k (z - y) Complex.I * du y Complex.I
            ∂(MeasureTheory.volume : Measure ℂ) := by
          simpa [k] using
            euclidean_derivativeKernel_convolution_apply_eq_integral
              φ hdu_I_int z Complex.I
  have hint_one :
      Integrable
        (fun y : ℂ ↦ fderiv ℝ k (z - y) (1 : ℂ) * du y (1 : ℂ))
        (MeasureTheory.volume : Measure ℂ) := by
    simpa [k] using
      euclidean_derivativeKernel_mul_integrable
        φ hdu_one_int z (1 : ℂ)
  have hint_I :
      Integrable
        (fun y : ℂ ↦ fderiv ℝ k (z - y) Complex.I * du y Complex.I)
        (MeasureTheory.volume : Measure ℂ) := by
    simpa [k] using
      euclidean_derivativeKernel_mul_integrable
        φ hdu_I_int z Complex.I
  have hraw_neg_zero :
      ∫ y : ℂ,
          (-(du y (1 : ℂ) * fderiv ℝ k (z - y) (1 : ℂ)) +
            -(du y Complex.I * fderiv ℝ k (z - y) Complex.I))
          ∂(MeasureTheory.volume : Measure ℂ) = 0 := by
    simpa [k, euclideanCotangentPairing,
      euclidean_reflectedKernel_fderiv_apply] using hweak
  have hsum_neg_zero :
      ∫ y : ℂ,
          - (fderiv ℝ k (z - y) (1 : ℂ) * du y (1 : ℂ) +
            fderiv ℝ k (z - y) Complex.I * du y Complex.I)
          ∂(MeasureTheory.volume : Measure ℂ) = 0 := by
    convert hraw_neg_zero using 2
    funext y
    ring_nf
  have hsum_zero :
      ∫ y : ℂ,
          (fderiv ℝ k (z - y) (1 : ℂ) * du y (1 : ℂ) +
            fderiv ℝ k (z - y) Complex.I * du y Complex.I)
          ∂(MeasureTheory.volume : Measure ℂ) = 0 := by
    have hsum_int := hint_one.add hint_I
    rw [integral_neg (f := fun y : ℂ ↦
      fderiv ℝ k (z - y) (1 : ℂ) * du y (1 : ℂ) +
        fderiv ℝ k (z - y) Complex.I * du y Complex.I)] at hsum_neg_zero
    linarith
  calc
    fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ du y (1 : ℂ)) : ℂ → ℝ) z (1 : ℂ) +
        fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ du y Complex.I) : ℂ → ℝ) z Complex.I
        =
        ∫ y : ℂ,
          fderiv ℝ k (z - y) (1 : ℂ) * du y (1 : ℂ)
          ∂(MeasureTheory.volume : Measure ℂ) +
        ∫ y : ℂ,
          fderiv ℝ k (z - y) Complex.I * du y Complex.I
          ∂(MeasureTheory.volume : Measure ℂ) := by
          rw [hD_one, hD_I]
    _ =
        ∫ y : ℂ,
          (fderiv ℝ k (z - y) (1 : ℂ) * du y (1 : ℂ) +
            fderiv ℝ k (z - y) Complex.I * du y Complex.I)
          ∂(MeasureTheory.volume : Measure ℂ) := by
          rw [integral_add hint_one hint_I]
    _ = 0 := hsum_zero

/--
%%handwave
name:
  Localized mollified weak gradients have zero Euclidean divergence
statement:
  If a cutoff is equal to one on a region containing the reflected mollifier
  support around \(Q\), then the two coordinate convolutions of the
  cutoff-localized weak gradient have zero classical divergence on \(Q\).
proof:
  The original weak harmonic identity is tested against the reflected
  mollifier.  On the set where the reflected derivative kernel can be
  nonzero, the cutoff derivative agrees with the original weak derivative;
  outside that set the derivative kernel vanishes.  Thus the zero-divergence
  integral for the original weak gradient is also the zero-divergence integral
  for the cutoff-localized weak gradient, whose components are globally
  integrable.
-/
theorem euclideanWeakHarmonic_mollifiedCutoffWeakGradient_divergence_eq_zero
    {Q P Ω : Set ℂ} {φ : ContDiffBump (0 : ℂ)}
    (hthickeningP : Metric.cthickening φ.rOut Q ⊆ P)
    (hPΩ : P ⊆ Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ))
    (hdu_one_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z (1 : ℂ)) Ω
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z Complex.I) Ω
      (MeasureTheory.volume : Measure ℂ)) :
    ∀ z ∈ Q,
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦
              scalarWeakSobolevCutoffDerivative (χ : ℂ → ℝ) u du y (1 : ℂ)) :
            ℂ → ℝ) z (1 : ℂ) +
        fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦
              scalarWeakSobolevCutoffDerivative (χ : ℂ → ℝ) u du y Complex.I) :
            ℂ → ℝ) z Complex.I = 0 := by
  intro z hzQ
  let k : ℂ → ℝ := φ.normed (MeasureTheory.volume : Measure ℂ)
  let locD : ℂ → ℂ →L[ℝ] ℝ :=
    scalarWeakSobolevCutoffDerivative (χ : ℂ → ℝ) u du
  have hlocD_one_int : Integrable (fun y : ℂ ↦ locD y (1 : ℂ))
      (MeasureTheory.volume : Measure ℂ) := by
    simpa [locD] using
      scalarWeakSobolevCutoff_derivative_integrable χ hu_loc hdu_one_loc
  have hlocD_I_int : Integrable (fun y : ℂ ↦ locD y Complex.I)
      (MeasureTheory.volume : Measure ℂ) := by
    simpa [locD] using
      scalarWeakSobolevCutoff_derivative_integrable χ hu_loc hdu_I_loc
  have hweak :=
    euclideanWeakHarmonic_reflectedMollifier_zeroDivergence
      (hthickeningP.trans hPΩ) hzero z hzQ
  have hD_one :
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ locD y (1 : ℂ)) : ℂ → ℝ) z (1 : ℂ) =
        ∫ y : ℂ,
          fderiv ℝ k (z - y) (1 : ℂ) * locD y (1 : ℂ)
          ∂(MeasureTheory.volume : Measure ℂ) := by
    calc
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ locD y (1 : ℂ)) : ℂ → ℝ) z (1 : ℂ)
          =
          ((((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ))) ⋆[
            (lsmul ℝ ℝ).precompL ℂ,
            (MeasureTheory.volume : Measure ℂ)] (fun y : ℂ ↦ locD y (1 : ℂ)) :
            ℂ → ℂ →L[ℝ] ℝ) z) (1 : ℂ)) :=
            euclidean_fderiv_normed_convolution_apply_eq_derivativeKernel
              φ hlocD_one_int z (1 : ℂ)
      _ = ∫ y : ℂ,
            fderiv ℝ k (z - y) (1 : ℂ) * locD y (1 : ℂ)
            ∂(MeasureTheory.volume : Measure ℂ) := by
          simpa [k] using
            euclidean_derivativeKernel_convolution_apply_eq_integral
              φ hlocD_one_int z (1 : ℂ)
  have hD_I :
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ locD y Complex.I) : ℂ → ℝ) z Complex.I =
        ∫ y : ℂ,
          fderiv ℝ k (z - y) Complex.I * locD y Complex.I
          ∂(MeasureTheory.volume : Measure ℂ) := by
    calc
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦ locD y Complex.I) : ℂ → ℝ) z Complex.I
          =
          ((((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure ℂ))) ⋆[
            (lsmul ℝ ℝ).precompL ℂ,
            (MeasureTheory.volume : Measure ℂ)] (fun y : ℂ ↦ locD y Complex.I) :
            ℂ → ℂ →L[ℝ] ℝ) z) Complex.I) :=
            euclidean_fderiv_normed_convolution_apply_eq_derivativeKernel
              φ hlocD_I_int z Complex.I
      _ = ∫ y : ℂ,
            fderiv ℝ k (z - y) Complex.I * locD y Complex.I
            ∂(MeasureTheory.volume : Measure ℂ) := by
          simpa [k] using
            euclidean_derivativeKernel_convolution_apply_eq_integral
              φ hlocD_I_int z Complex.I
  have hint_one :
      Integrable
        (fun y : ℂ ↦ fderiv ℝ k (z - y) (1 : ℂ) * locD y (1 : ℂ))
        (MeasureTheory.volume : Measure ℂ) := by
    simpa [k] using
      euclidean_derivativeKernel_mul_integrable
        φ hlocD_one_int z (1 : ℂ)
  have hint_I :
      Integrable
        (fun y : ℂ ↦ fderiv ℝ k (z - y) Complex.I * locD y Complex.I)
        (MeasureTheory.volume : Measure ℂ) := by
    simpa [k] using
      euclidean_derivativeKernel_mul_integrable
        φ hlocD_I_int z Complex.I
  have hraw_orig_neg_zero :
      ∫ y : ℂ,
          (-(du y (1 : ℂ) * fderiv ℝ k (z - y) (1 : ℂ)) +
            -(du y Complex.I * fderiv ℝ k (z - y) Complex.I))
          ∂(MeasureTheory.volume : Measure ℂ) = 0 := by
    simpa [k, euclideanCotangentPairing,
      euclidean_reflectedKernel_fderiv_apply] using hweak
  have hraw_loc_eq_orig :
      (∫ y : ℂ,
          (-(locD y (1 : ℂ) * fderiv ℝ k (z - y) (1 : ℂ)) +
            -(locD y Complex.I * fderiv ℝ k (z - y) Complex.I))
          ∂(MeasureTheory.volume : Measure ℂ)) =
        ∫ y : ℂ,
          (-(du y (1 : ℂ) * fderiv ℝ k (z - y) (1 : ℂ)) +
            -(du y Complex.I * fderiv ℝ k (z - y) Complex.I))
          ∂(MeasureTheory.volume : Measure ℂ) := by
    refine integral_congr_ae ?_
    exact ae_of_all (MeasureTheory.volume : Measure ℂ) fun y ↦ by
      by_cases hyP : y ∈ P
      · have hloc_one : locD y (1 : ℂ) = du y (1 : ℂ) := by
          simpa [locD] using
            χ.cutoffDerivative_eq_on (u := u) (du := du)
              (h := (1 : ℂ)) y hyP
        have hloc_I : locD y Complex.I = du y Complex.I := by
          simpa [locD] using
            χ.cutoffDerivative_eq_on (u := u) (du := du)
              (h := Complex.I) y hyP
        simp [hloc_one, hloc_I]
      · have hycth : y ∉ Metric.cthickening φ.rOut Q := fun hy ↦
          hyP (hthickeningP hy)
        have hzero_one :
            fderiv ℝ k (z - y) (1 : ℂ) = 0 := by
          simpa [k] using
            euclidean_derivativeKernel_zero_of_notMem_cthickening
              (Q := Q) φ (z := z) (y := y) (v := (1 : ℂ)) hzQ hycth
        have hzero_I :
            fderiv ℝ k (z - y) Complex.I = 0 := by
          simpa [k] using
            euclidean_derivativeKernel_zero_of_notMem_cthickening
              (Q := Q) φ (z := z) (y := y) (v := Complex.I) hzQ hycth
        simp [hzero_one, hzero_I]
  have hraw_loc_neg_zero :
      ∫ y : ℂ,
          (-(locD y (1 : ℂ) * fderiv ℝ k (z - y) (1 : ℂ)) +
            -(locD y Complex.I * fderiv ℝ k (z - y) Complex.I))
          ∂(MeasureTheory.volume : Measure ℂ) = 0 := by
    rw [hraw_loc_eq_orig]
    exact hraw_orig_neg_zero
  have hsum_neg_zero :
      ∫ y : ℂ,
          - (fderiv ℝ k (z - y) (1 : ℂ) * locD y (1 : ℂ) +
            fderiv ℝ k (z - y) Complex.I * locD y Complex.I)
          ∂(MeasureTheory.volume : Measure ℂ) = 0 := by
    convert hraw_loc_neg_zero using 2
    funext y
    ring_nf
  have hsum_zero :
      ∫ y : ℂ,
          (fderiv ℝ k (z - y) (1 : ℂ) * locD y (1 : ℂ) +
            fderiv ℝ k (z - y) Complex.I * locD y Complex.I)
          ∂(MeasureTheory.volume : Measure ℂ) = 0 := by
    rw [integral_neg (f := fun y : ℂ ↦
      fderiv ℝ k (z - y) (1 : ℂ) * locD y (1 : ℂ) +
        fderiv ℝ k (z - y) Complex.I * locD y Complex.I)] at hsum_neg_zero
    linarith
  calc
    fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦
              scalarWeakSobolevCutoffDerivative (χ : ℂ → ℝ) u du y (1 : ℂ)) :
            ℂ → ℝ) z (1 : ℂ) +
        fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure ℂ)]
            (fun y : ℂ ↦
              scalarWeakSobolevCutoffDerivative (χ : ℂ → ℝ) u du y Complex.I) :
            ℂ → ℝ) z Complex.I
        =
        ∫ y : ℂ,
          fderiv ℝ k (z - y) (1 : ℂ) * locD y (1 : ℂ)
          ∂(MeasureTheory.volume : Measure ℂ) +
        ∫ y : ℂ,
          fderiv ℝ k (z - y) Complex.I * locD y Complex.I
          ∂(MeasureTheory.volume : Measure ℂ) := by
          rw [hD_one, hD_I]
    _ =
        ∫ y : ℂ,
          (fderiv ℝ k (z - y) (1 : ℂ) * locD y (1 : ℂ) +
            fderiv ℝ k (z - y) Complex.I * locD y Complex.I)
          ∂(MeasureTheory.volume : Measure ℂ) := by
          rw [integral_add hint_one hint_I]
    _ = 0 := hsum_zero

private theorem euclidean_gradientDivergence_eq_laplacian
    (F : ℂ → ℝ) {z : ℂ} (hF : ContDiffAt ℝ 2 F z) :
    fderiv ℝ (fun w : ℂ ↦ fderiv ℝ F w (1 : ℂ)) z (1 : ℂ) +
        fderiv ℝ (fun w : ℂ ↦ fderiv ℝ F w Complex.I) z Complex.I =
      Laplacian.laplacian F z := by
  have hFderiv : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEval_one :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ F w (1 : ℂ)) z =
        (fderiv ℝ (fderiv ℝ F) z).flip (1 : ℂ) := by
    rw [fderiv_clm_apply hFderiv (differentiableAt_const (1 : ℂ))]
    ext v
    simp [ContinuousLinearMap.flip_apply]
  have hEval_I :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ F w Complex.I) z =
        (fderiv ℝ (fderiv ℝ F) z).flip Complex.I := by
    rw [fderiv_clm_apply hFderiv (differentiableAt_const Complex.I)]
    ext v
    simp [ContinuousLinearMap.flip_apply]
  rw [hEval_one, hEval_I, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  change ((fderiv ℝ (fderiv ℝ F) z).flip (1 : ℂ)) (1 : ℂ) +
      ((fderiv ℝ (fderiv ℝ F) z).flip Complex.I) Complex.I =
    iteratedFDeriv ℝ 2 F z ![(1 : ℂ), (1 : ℂ)] +
      iteratedFDeriv ℝ 2 F z ![Complex.I, Complex.I]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) F z (1 : ℂ) (1 : ℂ)]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) F z Complex.I Complex.I]
  simp [bilinearIteratedFDerivTwo, ContinuousLinearMap.flip_apply]

/--
%%handwave
name:
  Mollifications of weakly harmonic functions have zero Laplacian
statement:
  On a compact neighborhood where the mollifier support remains in the weakly
  harmonic region, the mollification has vanishing classical Euclidean
  Laplacian at the center.
proof:
  The first derivatives of the mollification agree near the center with the
  convolutions of the two weak-gradient components.  The weak zero-divergence
  identity gives zero divergence for those convolutions, and the Euclidean
  formula for the Laplacian identifies this divergence with the Laplacian of
  the mollification.
-/
theorem euclideanMollification_laplacian_eq_zero_of_weaklyHarmonicOn_compact_nhds
    {Q Ω : Set ℂ} (hQ : IsCompact Q) {z : ℂ} (hQ_nhds : Q ∈ 𝓝 z)
    {φ : ContDiffBump (0 : ℂ)}
    (hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_int : Integrable u (MeasureTheory.volume : Measure ℂ))
    (hdu_one_int : Integrable (fun z : ℂ ↦ du z (1 : ℂ))
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_int : Integrable (fun z : ℂ ↦ du z Complex.I)
      (MeasureTheory.volume : Measure ℂ)) :
    Laplacian.laplacian (euclideanMollification φ u) z = 0 := by
  let m : ℂ → ℝ := euclideanMollification φ u
  let convOne : ℂ → ℝ :=
    (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure ℂ)]
      (fun y : ℂ ↦ du y (1 : ℂ)) : ℂ → ℝ)
  let convI : ℂ → ℝ :=
    (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure ℂ)]
      (fun y : ℂ ↦ du y Complex.I) : ℂ → ℝ)
  have hm_smooth : ContDiff ℝ ∞ m := by
    simpa [m] using euclideanMollification_contDiff φ hu_int.locallyIntegrable
  have hm_two : ContDiffAt ℝ 2 m z :=
    (hm_smooth.contDiffAt).of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)
  have hdir_one :
      ∀ w ∈ Q, fderiv ℝ m w (1 : ℂ) = convOne w := by
    intro w hw
    simpa [m, convOne] using
      euclideanMollification_directionalDerivative_eq_convolution_weakDerivative_on_compact
        (Q := Q) (Ω := Ω) hQ hthickening hweak
        (v := (1 : ℂ)) hu_int hdu_one_int w hw
  have hdir_I :
      ∀ w ∈ Q, fderiv ℝ m w Complex.I = convI w := by
    intro w hw
    simpa [m, convI] using
      euclideanMollification_directionalDerivative_eq_convolution_weakDerivative_on_compact
        (Q := Q) (Ω := Ω) hQ hthickening hweak
        (v := Complex.I) hu_int hdu_I_int w hw
  have hdir_one_event :
      (fun w : ℂ ↦ fderiv ℝ m w (1 : ℂ)) =ᶠ[𝓝 z] convOne := by
    filter_upwards [hQ_nhds] with w hw
    exact hdir_one w hw
  have hdir_I_event :
      (fun w : ℂ ↦ fderiv ℝ m w Complex.I) =ᶠ[𝓝 z] convI := by
    filter_upwards [hQ_nhds] with w hw
    exact hdir_I w hw
  have hfderiv_one :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w (1 : ℂ)) z =
        fderiv ℝ convOne z :=
    hdir_one_event.fderiv_eq
  have hfderiv_I :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w Complex.I) z =
        fderiv ℝ convI z :=
    hdir_I_event.fderiv_eq
  have hzQ : z ∈ Q := mem_of_mem_nhds hQ_nhds
  have hconv_div_zero :
      fderiv ℝ convOne z (1 : ℂ) + fderiv ℝ convI z Complex.I = 0 := by
    simpa [convOne, convI] using
      euclideanWeakHarmonic_mollifiedWeakGradient_divergence_eq_zero
        (Q := Q) (Ω := Ω) (φ := φ) hthickening hzero
        hdu_one_int hdu_I_int z hzQ
  have hm_div_zero :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w (1 : ℂ)) z (1 : ℂ) +
          fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w Complex.I) z Complex.I = 0 := by
    rw [hfderiv_one, hfderiv_I]
    exact hconv_div_zero
  calc
    Laplacian.laplacian (euclideanMollification φ u) z
        = Laplacian.laplacian m z := by rfl
    _ =
        fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w (1 : ℂ)) z (1 : ℂ) +
          fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w Complex.I) z Complex.I :=
        (euclidean_gradientDivergence_eq_laplacian m hm_two).symm
    _ = 0 := hm_div_zero

/--
%%handwave
name:
  Cutoff-local mollifications have zero Laplacian
statement:
  On a compact neighborhood whose reflected mollifier support lies in a set
  where a cutoff is identically one, the cutoff-localized mollification of a
  weakly harmonic function has vanishing Euclidean Laplacian.
proof:
  The product rule gives a weak derivative for the cutoff-localized function.
  The directional derivatives of its mollification are therefore the
  convolutions of the cutoff-localized weak-gradient components.  The
  localized zero-divergence identity makes their divergence vanish, and this
  divergence is the Euclidean Laplacian of the mollification.
-/
theorem euclideanMollification_cutoff_laplacian_eq_zero_of_weaklyHarmonicOn_compact_nhds
    {Q P Ω : Set ℂ} (hQ : IsCompact Q) {z : ℂ} (hQ_nhds : Q ∈ 𝓝 z)
    {φ : ContDiffBump (0 : ℂ)}
    (hthickeningP : Metric.cthickening φ.rOut Q ⊆ P)
    (hPΩ : P ⊆ Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ))
    (hdu_one_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z (1 : ℂ)) Ω
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z Complex.I) Ω
      (MeasureTheory.volume : Measure ℂ)) :
    Laplacian.laplacian
      (euclideanMollification φ (fun y : ℂ ↦ χ y * u y)) z = 0 := by
  let uχ : ℂ → ℝ := fun y ↦ χ y * u y
  let duχ : ℂ → ℂ →L[ℝ] ℝ :=
    scalarWeakSobolevCutoffDerivative (χ : ℂ → ℝ) u du
  let m : ℂ → ℝ := euclideanMollification φ uχ
  let convOne : ℂ → ℝ :=
    (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure ℂ)]
      (fun y : ℂ ↦ duχ y (1 : ℂ)) : ℂ → ℝ)
  let convI : ℂ → ℝ :=
    (φ.normed (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure ℂ)]
      (fun y : ℂ ↦ duχ y Complex.I) : ℂ → ℝ)
  have huχ_int : Integrable uχ (MeasureTheory.volume : Measure ℂ) := by
    simpa [uχ] using
      scalarWeakSobolevCutoff_value_integrable χ hu_loc
  have hduχ_one_int : Integrable (fun y : ℂ ↦ duχ y (1 : ℂ))
      (MeasureTheory.volume : Measure ℂ) := by
    simpa [duχ] using
      scalarWeakSobolevCutoff_derivative_integrable χ hu_loc hdu_one_loc
  have hduχ_I_int : Integrable (fun y : ℂ ↦ duχ y Complex.I)
      (MeasureTheory.volume : Measure ℂ) := by
    simpa [duχ] using
      scalarWeakSobolevCutoff_derivative_integrable χ hu_loc hdu_I_loc
  have hweakχK :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Ω uχ duχ := by
    simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionWithValues, uχ, duχ] using
      scalarWeakSobolevCutoffDerivative_weakDerivative χ
        (by
          simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
            IsWeakDerivativeOnEuclideanRegionWithValues] using hweak)
        hu_loc
  have hweakχ : IsWeakDerivativeOnEuclideanRegionWithValues Ω uχ duχ := by
    simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionWithValues] using hweakχK
  have hm_smooth : ContDiff ℝ ∞ m := by
    simpa [m] using euclideanMollification_contDiff φ huχ_int.locallyIntegrable
  have hm_two : ContDiffAt ℝ 2 m z :=
    (hm_smooth.contDiffAt).of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)
  have hthickeningΩ : Metric.cthickening φ.rOut Q ⊆ Ω :=
    hthickeningP.trans hPΩ
  have hdir_one :
      ∀ w ∈ Q, fderiv ℝ m w (1 : ℂ) = convOne w := by
    intro w hw
    simpa [m, convOne, uχ, duχ] using
      euclideanMollification_directionalDerivative_eq_convolution_weakDerivative_on_compact
        (Q := Q) (Ω := Ω) hQ hthickeningΩ hweakχ
        (v := (1 : ℂ)) huχ_int hduχ_one_int w hw
  have hdir_I :
      ∀ w ∈ Q, fderiv ℝ m w Complex.I = convI w := by
    intro w hw
    simpa [m, convI, uχ, duχ] using
      euclideanMollification_directionalDerivative_eq_convolution_weakDerivative_on_compact
        (Q := Q) (Ω := Ω) hQ hthickeningΩ hweakχ
        (v := Complex.I) huχ_int hduχ_I_int w hw
  have hdir_one_event :
      (fun w : ℂ ↦ fderiv ℝ m w (1 : ℂ)) =ᶠ[𝓝 z] convOne := by
    filter_upwards [hQ_nhds] with w hw
    exact hdir_one w hw
  have hdir_I_event :
      (fun w : ℂ ↦ fderiv ℝ m w Complex.I) =ᶠ[𝓝 z] convI := by
    filter_upwards [hQ_nhds] with w hw
    exact hdir_I w hw
  have hfderiv_one :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w (1 : ℂ)) z =
        fderiv ℝ convOne z :=
    hdir_one_event.fderiv_eq
  have hfderiv_I :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w Complex.I) z =
        fderiv ℝ convI z :=
    hdir_I_event.fderiv_eq
  have hzQ : z ∈ Q := mem_of_mem_nhds hQ_nhds
  have hconv_div_zero :
      fderiv ℝ convOne z (1 : ℂ) + fderiv ℝ convI z Complex.I = 0 := by
    simpa [convOne, convI, duχ] using
      euclideanWeakHarmonic_mollifiedCutoffWeakGradient_divergence_eq_zero
        (Q := Q) (P := P) (Ω := Ω) (φ := φ) hthickeningP hPΩ χ hzero
        hu_loc hdu_one_loc hdu_I_loc z hzQ
  have hm_div_zero :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w (1 : ℂ)) z (1 : ℂ) +
          fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w Complex.I) z Complex.I = 0 := by
    rw [hfderiv_one, hfderiv_I]
    exact hconv_div_zero
  calc
    Laplacian.laplacian
        (euclideanMollification φ (fun y : ℂ ↦ χ y * u y)) z
        = Laplacian.laplacian m z := by rfl
    _ =
        fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w (1 : ℂ)) z (1 : ℂ) +
          fderiv ℝ (fun w : ℂ ↦ fderiv ℝ m w Complex.I) z Complex.I :=
        (euclidean_gradientDivergence_eq_laplacian m hm_two).symm
    _ = 0 := hm_div_zero

/--
%%handwave
name:
  Cutoff-local mollifications are harmonic
statement:
  If an open set lies in a compact set whose reflected mollifier support lies
  where a cutoff is one, then the cutoff-localized mollification of a weakly
  harmonic function is classically harmonic on that open set.
proof:
  Smoothness follows from convolution with a smooth compactly supported
  kernel and the cutoff-localized integrability.  The previous theorem gives
  zero Laplacian at each point of a neighborhood inside the protected compact
  set.
-/
theorem euclideanMollification_cutoff_harmonicOnNhd_of_weaklyHarmonicOn_compact_open
    {V Q P Ω : Set ℂ} (hQ : IsCompact Q) (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    {φ : ContDiffBump (0 : ℂ)}
    (hthickeningP : Metric.cthickening φ.rOut Q ⊆ P)
    (hPΩ : P ⊆ Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ))
    (hdu_one_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z (1 : ℂ)) Ω
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z Complex.I) Ω
      (MeasureTheory.volume : Measure ℂ)) :
    InnerProductSpace.HarmonicOnNhd
      (euclideanMollification φ (fun y : ℂ ↦ χ y * u y)) V := by
  have huχ_int :
      Integrable (fun y : ℂ ↦ χ y * u y)
        (MeasureTheory.volume : Measure ℂ) :=
    scalarWeakSobolevCutoff_value_integrable χ hu_loc
  have hm_smooth :
      ContDiff ℝ ∞ (euclideanMollification φ (fun y : ℂ ↦ χ y * u y)) :=
    euclideanMollification_contDiff φ huχ_int.locallyIntegrable
  intro z hzV
  have hm_two :
      ContDiffAt ℝ 2 (euclideanMollification φ (fun y : ℂ ↦ χ y * u y)) z :=
    (hm_smooth.contDiffAt).of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)
  refine ⟨hm_two, ?_⟩
  filter_upwards [hV_open.mem_nhds hzV] with w hwV
  have hQ_nhds : Q ∈ 𝓝 w :=
    Filter.mem_of_superset (hV_open.mem_nhds hwV) hVQ
  exact
    euclideanMollification_cutoff_laplacian_eq_zero_of_weaklyHarmonicOn_compact_nhds
      (Q := Q) (P := P) (Ω := Ω) hQ hQ_nhds hthickeningP hPΩ χ
      hweak hzero hu_loc hdu_one_loc hdu_I_loc

/--
%%handwave
name:
  Mean value identity for cutoff-local mollifications
statement:
  On every circle whose closed disk lies in the protected open set, the
  cutoff-localized weakly harmonic mollification equals its circle average.
proof:
  The previous theorem makes the cutoff-localized mollification harmonic on
  the protected open set.  Restrict harmonicity to the closed disk and apply
  the harmonic mean-value theorem.
-/
theorem euclideanMollification_cutoff_circleAverage_eq_of_weaklyHarmonicOn_compact_open
    {V Q P Ω : Set ℂ} (hQ : IsCompact Q) (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    {φ : ContDiffBump (0 : ℂ)}
    (hthickeningP : Metric.cthickening φ.rOut Q ⊆ P)
    (hPΩ : P ⊆ Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ))
    (hdu_one_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z (1 : ℂ)) Ω
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z Complex.I) Ω
      (MeasureTheory.volume : Measure ℂ))
    {c : ℂ} {R : ℝ}
    (hclosedBall : Metric.closedBall c |R| ⊆ V) :
    Real.circleAverage
        (euclideanMollification φ (fun y : ℂ ↦ χ y * u y)) c R =
      euclideanMollification φ (fun y : ℂ ↦ χ y * u y) c := by
  have hharm :
      InnerProductSpace.HarmonicOnNhd
        (euclideanMollification φ (fun y : ℂ ↦ χ y * u y)) V :=
    euclideanMollification_cutoff_harmonicOnNhd_of_weaklyHarmonicOn_compact_open
      (V := V) (Q := Q) (P := P) (Ω := Ω) hQ hV_open hVQ
      hthickeningP hPΩ χ hweak hzero hu_loc hdu_one_loc hdu_I_loc
  exact HarmonicOnNhd.circleAverage_eq (hharm.mono hclosedBall)

/--
%%handwave
name:
  Cutoff-local standard mollifiers converge almost everywhere
statement:
  For a locally integrable function multiplied by a compactly supported
  smooth cutoff, the standard normalized mollifications converge almost
  everywhere to the cutoff-localized function.
proof:
  The cutoff makes the product globally integrable, hence locally integrable.
  The standard bump functions have radii tending to zero and fixed inner-to-
  outer radius ratio, so the Lebesgue differentiation theorem for normalized
  bump convolutions applies.
-/
theorem euclideanMollification_cutoff_standardMollifier_tendsto_ae
    {P Ω : Set ℂ} (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ}
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ)) :
    ∀ᵐ z ∂(MeasureTheory.volume : Measure ℂ),
      Filter.Tendsto
        (fun n : ℕ ↦
          euclideanMollification
            (scalarWeakSobolevStandardMollifier ℂ n)
            (fun y : ℂ ↦ χ y * u y) z)
        Filter.atTop (𝓝 (χ z * u z)) := by
  have huχ_int :
      Integrable (fun y : ℂ ↦ χ y * u y)
        (MeasureTheory.volume : Measure ℂ) :=
    scalarWeakSobolevCutoff_value_integrable χ hu_loc
  have hratio :
      ∀ᶠ n : ℕ in Filter.atTop,
        (scalarWeakSobolevStandardMollifier ℂ n).rOut ≤
          (2 : ℝ) * (scalarWeakSobolevStandardMollifier ℂ n).rIn := by
    exact Filter.Eventually.of_forall fun n ↦ by
      rw [scalarWeakSobolevStandardMollifier_fixed_ratio ℂ n]
  simpa [euclideanMollification] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (MeasureTheory.volume : Measure ℂ))
      (φ := fun n : ℕ ↦ scalarWeakSobolevStandardMollifier ℂ n)
      (l := Filter.atTop)
      (K := (2 : ℝ))
      (scalarWeakSobolevStandardMollifier_rOut_tendsto_zero ℂ)
      hratio huχ_int.locallyIntegrable

/--
%%handwave
name:
  Cutoff-local standard mollifiers converge on the one set
statement:
  On the set where the cutoff is identically one, the standard mollifications
  of the cutoff-localized function converge almost everywhere to the original
  function.
proof:
  Restrict the almost-everywhere convergence of the cutoff-localized
  mollifications to the one set.  There the cutoff value is one, so the
  limiting product is the original function.
-/
theorem euclideanMollification_cutoff_standardMollifier_tendsto_ae_on_one_set
    {P Ω : Set ℂ} (hP_meas : MeasurableSet P)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ}
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict P : Measure ℂ),
      Filter.Tendsto
        (fun n : ℕ ↦
          euclideanMollification
            (scalarWeakSobolevStandardMollifier ℂ n)
            (fun y : ℂ ↦ χ y * u y) z)
        Filter.atTop (𝓝 (u z)) := by
  have hglobal :=
    euclideanMollification_cutoff_standardMollifier_tendsto_ae χ hu_loc
  have hrestrict :
      ∀ᵐ z ∂(MeasureTheory.volume.restrict P : Measure ℂ),
        Filter.Tendsto
          (fun n : ℕ ↦
            euclideanMollification
              (scalarWeakSobolevStandardMollifier ℂ n)
              (fun y : ℂ ↦ χ y * u y) z)
          Filter.atTop (𝓝 (χ z * u z)) :=
    ae_mono (Measure.restrict_le_self (μ := MeasureTheory.volume) (s := P))
      hglobal
  filter_upwards [hrestrict, ae_restrict_mem hP_meas] with z hz hzP
  simpa [χ.eq_one_on z hzP] using hz

/--
%%handwave
name:
  Cutoff-local standard mollifiers converge in local \(L^1\)
statement:
  On every compact set \(Q\) with a compact collar contained in the cutoff
  one set, the standard mollifications of the cutoff-localized function
  converge to the original function in \(L^1(Q)\).
proof:
  The cutoff-localized function is globally integrable.  Apply local
  \(L^1\)-convergence of standard mollifiers to it on \(Q\), using the
  compact collar inside the one set.  Since the cutoff equals one on \(Q\),
  the \(L^1(Q)\)-limit is the original function.
-/
theorem euclideanMollification_cutoff_standardMollifier_tendsto_l1_on_compact_one_set
    {Q P Ω : Set ℂ} (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ}
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          (fun z ↦
            euclideanMollification
              (scalarWeakSobolevStandardMollifier ℂ n)
              (fun y : ℂ ↦ χ y * u y) z - u z)
          1 (MeasureTheory.volume.restrict Q))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  let W : ℂ → ℝ := fun z ↦ χ z * u z
  let μQ : Measure ℂ := MeasureTheory.volume.restrict Q
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
  have hW_int :
      Integrable W (MeasureTheory.volume : Measure ℂ) := by
    simpa [W] using scalarWeakSobolevCutoff_value_integrable χ hu_loc
  have hW_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun z ↦
              (((scalarWeakSobolevStandardMollifier ℂ n).normed
                    (MeasureTheory.volume : Measure ℂ) ⋆[lsmul ℝ ℝ,
                    (MeasureTheory.volume : Measure ℂ)] W : ℂ → ℝ) z) -
                W z)
            1 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [μQ] using
      scalarWeakSobolev_standardMollifier_value_eLpNorm_one_tendsto_zero_of_global_integrable
        hQ hP hQP hW_int
  refine hW_tendsto.congr' ?_
  filter_upwards [] with n
  exact
    eLpNorm_congr_ae
      (ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
        simp [W, euclideanMollification, χ.eq_one_on z (hQP_subset hzQ)])

/--
%%handwave
name:
  Cutoff-local standard mollifiers are \(L^1\)-Cauchy on compact sets
statement:
  On every compact set \(Q\) with a compact collar contained in the cutoff
  one set and in the weakly harmonic region, the cutoff-local standard
  mollifier sequence is Cauchy in \(L^1(Q)\).
proof:
  The sequence converges in \(L^1(Q)\) to the original function.  Apply the
  triangle inequality to
  \((u_m-u)-(u_n-u)\), after choosing the one-index errors smaller than
  one third of the requested tolerance.
-/
theorem euclideanMollification_cutoff_standardMollifier_l1_cauchy_on_compact_one_set
    {Q P Ω : Set ℂ} (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ}
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
        eLpNorm
          (fun z ↦
            euclideanMollification
              (scalarWeakSobolevStandardMollifier ℂ m)
              (fun y : ℂ ↦ χ y * u y) z -
            euclideanMollification
              (scalarWeakSobolevStandardMollifier ℂ n)
              (fun y : ℂ ↦ χ y * u y) z)
          1 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let W : ℂ → ℝ := fun z ↦ χ z * u z
  let μQ : Measure ℂ := MeasureTheory.volume.restrict Q
  let η : ℝ := ε / 3
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
  have hQΩ : Q ⊆ Ω := hQP_subset.trans hPΩ
  have hW_int :
      Integrable W (MeasureTheory.volume : Measure ℂ) := by
    simpa [W] using scalarWeakSobolevCutoff_value_integrable χ hu_loc
  have huQ_on : IntegrableOn u Q (MeasureTheory.volume : Measure ℂ) :=
    hu_loc.integrableOn_compact_subset hQΩ hQ
  have huQ_int : Integrable u μQ := by
    simpa [IntegrableOn, μQ] using huQ_on
  have hF_int : ∀ k : ℕ,
      Integrable
        (euclideanMollification
          (scalarWeakSobolevStandardMollifier ℂ k) W)
        (MeasureTheory.volume : Measure ℂ) := by
    intro k
    have hφ_int :
        Integrable
          ((scalarWeakSobolevStandardMollifier ℂ k).normed
            (MeasureTheory.volume : Measure ℂ))
          (MeasureTheory.volume : Measure ℂ) :=
      (scalarWeakSobolevStandardMollifier ℂ k).integrable_normed
    simpa [euclideanMollification] using
      hφ_int.integrable_convolution (L := lsmul ℝ ℝ) hW_int
  have hconv :
      Filter.Tendsto
        (fun k : ℕ ↦
          eLpNorm
            (fun z ↦
              euclideanMollification
                (scalarWeakSobolevStandardMollifier ℂ k) W z - u z)
            1 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [W, μQ] using
      euclideanMollification_cutoff_standardMollifier_tendsto_l1_on_compact_one_set
        hQ hP hQP χ hu_loc
  have hsmall :
      ∀ᶠ k : ℕ in Filter.atTop,
        eLpNorm
          (fun z ↦
            euclideanMollification
              (scalarWeakSobolevStandardMollifier ℂ k) W z - u z)
          1 μQ ≤ ENNReal.ofReal η :=
    hconv.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr hη_pos))
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  refine ⟨N, fun m n hm hn ↦ ?_⟩
  let Fm : ℂ → ℝ :=
    euclideanMollification (scalarWeakSobolevStandardMollifier ℂ m) W
  let Fn : ℂ → ℝ :=
    euclideanMollification (scalarWeakSobolevStandardMollifier ℂ n) W
  have hFm_meas : AEStronglyMeasurable Fm μQ :=
    (hF_int m).aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hFn_meas : AEStronglyMeasurable Fn μQ :=
    (hF_int n).aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hu_meas : AEStronglyMeasurable u μQ := huQ_int.aestronglyMeasurable
  have hm_small :
      eLpNorm (fun z ↦ Fm z - u z) 1 μQ ≤ ENNReal.ofReal η := by
    simpa [Fm] using hN m hm
  have hn_small :
      eLpNorm (fun z ↦ Fn z - u z) 1 μQ ≤ ENNReal.ofReal η := by
    simpa [Fn] using hN n hn
  have htri :
      eLpNorm (fun z ↦ Fm z - Fn z) 1 μQ ≤
        eLpNorm (fun z ↦ Fm z - u z) 1 μQ +
          eLpNorm (fun z ↦ Fn z - u z) 1 μQ := by
    calc
      eLpNorm (fun z ↦ Fm z - Fn z) 1 μQ
          =
          eLpNorm
            ((fun z ↦ Fm z - u z) - fun z ↦ Fn z - u z) 1 μQ := by
            congr 1
            funext z
            change Fm z - Fn z = (Fm z - u z) - (Fn z - u z)
            ring
      _ ≤ eLpNorm (fun z ↦ Fm z - u z) 1 μQ +
          eLpNorm (fun z ↦ Fn z - u z) 1 μQ := by
            exact eLpNorm_sub_le
              (μ := μQ) (p := (1 : ℝ≥0∞))
              (hFm_meas.sub hu_meas) (hFn_meas.sub hu_meas) (by norm_num)
  have hsum_le :
      ENNReal.ofReal η + ENNReal.ofReal η ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hη_nonneg hη_nonneg]
    exact ENNReal.ofReal_le_ofReal (by
      dsimp [η]
      linarith)
  calc
    eLpNorm
        (fun z ↦
          euclideanMollification
            (scalarWeakSobolevStandardMollifier ℂ m)
            (fun y : ℂ ↦ χ y * u y) z -
          euclideanMollification
            (scalarWeakSobolevStandardMollifier ℂ n)
            (fun y : ℂ ↦ χ y * u y) z)
        1 (MeasureTheory.volume.restrict Q)
        = eLpNorm (fun z ↦ Fm z - Fn z) 1 μQ := by
          rfl
    _ ≤ eLpNorm (fun z ↦ Fm z - u z) 1 μQ +
          eLpNorm (fun z ↦ Fn z - u z) 1 μQ := htri
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal η :=
          add_le_add hm_small hn_small
    _ ≤ ENNReal.ofReal ε := hsum_le

/--
%%handwave
name:
  Two \(L^1\)-limits of one approximating sequence agree almost everywhere
statement:
  If the same sequence converges in \(L^1\) to two functions with respect to
  a measure, then the two limiting functions agree almost everywhere.
proof:
  The \(L^1\)-seminorm of the difference of the two limits is bounded by the
  sum of the two approximation errors.  The right hand side tends to zero,
  hence the \(L^1\)-seminorm of the difference is zero, and therefore the
  difference vanishes almost everywhere.
-/
theorem ae_eq_of_eLpNorm_one_tendsto_zero_of_common_approx
    {μ : Measure ℂ} {F : ℕ → ℂ → ℝ} {u f : ℂ → ℝ}
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n) μ)
    (hu_meas : AEStronglyMeasurable u μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hFu :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z ↦ F n z - u z) 1 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (hFf :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z ↦ F n z - f z) 1 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    u =ᵐ[μ] f := by
  have hbound :
      ∀ n : ℕ,
        eLpNorm (fun z ↦ u z - f z) 1 μ ≤
          eLpNorm (fun z ↦ F n z - f z) 1 μ +
            eLpNorm (fun z ↦ F n z - u z) 1 μ := by
    intro n
    calc
      eLpNorm (fun z ↦ u z - f z) 1 μ
          =
          eLpNorm
            ((fun z ↦ F n z - f z) - fun z ↦ F n z - u z) 1 μ := by
            congr 1
            funext z
            change u z - f z = (F n z - f z) - (F n z - u z)
            ring
      _ ≤ eLpNorm (fun z ↦ F n z - f z) 1 μ +
          eLpNorm (fun z ↦ F n z - u z) 1 μ := by
            exact eLpNorm_sub_le
              (μ := μ) (p := (1 : ℝ≥0∞))
              ((hF_meas n).sub hf_meas) ((hF_meas n).sub hu_meas) (by norm_num)
  have hsum_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ F n z - f z) 1 μ +
            eLpNorm (fun z ↦ F n z - u z) 1 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using hFf.add hFu
  have hnorm_zero :
      eLpNorm (fun z ↦ u z - f z) 1 μ = 0 := by
    apply bot_unique
    exact ge_of_tendsto hsum_tendsto (Filter.Eventually.of_forall hbound)
  have hdiff_zero :
      (fun z ↦ u z - f z) =ᵐ[μ] 0 := by
    exact
      (eLpNorm_eq_zero_iff (hu_meas.sub hf_meas)
        (by norm_num : (1 : ℝ≥0∞) ≠ 0)).1 hnorm_zero
  exact hdiff_zero.mono fun z hz ↦ sub_eq_zero.mp hz

/--
%%handwave
name:
  Smaller measures preserve \(L^1\)-convergence to zero
statement:
  If a sequence has \(L^1\)-seminorms tending to zero with respect to a
  measure, then the same holds with respect to any smaller measure.
proof:
  The \(L^1\)-seminorm is monotone in the measure.  Compare each term with
  the seminorm for the larger measure and use the same eventual bound.
-/
theorem tendsto_eLpNorm_one_zero_of_measure_le
    {μ ν : Measure ℂ} {F : ℕ → ℂ → ℝ}
    (hνμ : ν ≤ μ)
    (hF :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (F n) 1 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ ↦ eLpNorm (F n) 1 ν)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  rw [ENNReal.tendsto_atTop_zero] at hF ⊢
  intro ε hε
  rcases hF ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  exact (eLpNorm_mono_measure (F n) hνμ).trans (hN n hn)

/--
%%handwave
name:
  Restricting preserves \(L^1\)-convergence to zero
statement:
  If \(L^1\)-seminorms tend to zero on a set, they also tend to zero on
  every smaller set.
proof:
  The restricted measure of the smaller set is bounded by the restricted
  measure of the larger set, so this is the measure-monotonicity result.
-/
theorem tendsto_eLpNorm_one_zero_restrict_mono
    {A B : Set ℂ} {F : ℕ → ℂ → ℝ}
    (hAB : A ⊆ B)
    (hF :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (F n) 1
          (MeasureTheory.volume.restrict B))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ ↦ eLpNorm (F n) 1
        (MeasureTheory.volume.restrict A))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
  tendsto_eLpNorm_one_zero_of_measure_le
    (Measure.restrict_mono hAB le_rfl) hF

/--
%%handwave
name:
  Uniform convergence on a compact set gives \(L^1\)-convergence
statement:
  If real-valued functions converge uniformly on a compact set, then their
  \(L^1\)-seminorms relative to the limit on that compact set tend to zero.
proof:
  Uniform convergence gives a constant error bound on the compact set.  Since
  compact sets have finite measure, the \(L^1\)-seminorm is bounded by this
  error times the measure of the compact set, and the error can be chosen
  arbitrarily small.
-/
theorem eLpNorm_one_tendsto_zero_of_tendstoUniformlyOn_compact
    {K : Set ℂ} (hK : IsCompact K)
    {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    (hconv : TendstoUniformlyOn F f Filter.atTop K) :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm (fun z ↦ F n z - f z) 1
          (MeasureTheory.volume.restrict K))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  let μK : Measure ℂ := MeasureTheory.volume.restrict K
  have hμK_ne_top : μK Set.univ ≠ (∞ : ℝ≥0∞) := by
    simpa [μK] using hK.measure_ne_top (μ := MeasureTheory.volume)
  have hK_meas : MeasurableSet K := hK.measurableSet
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hε_top : ε = (∞ : ℝ≥0∞)
  · exact ⟨0, fun n hn ↦ by simp [hε_top]⟩
  let M : ℝ := (μK Set.univ).toReal
  let δ : ℝ := ε.toReal / (M + 1)
  have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have hM1_pos : 0 < M + 1 := by linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact div_pos (ENNReal.toReal_pos hε.ne' hε_top) hM1_pos
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hδM_le : δ * M ≤ ε.toReal := by
    have hfrac_le_one : M / (M + 1) ≤ 1 := by
      rw [div_le_iff₀ hM1_pos]
      linarith
    calc
      δ * M = ε.toReal * (M / (M + 1)) := by
        rw [show δ = ε.toReal / (M + 1) by rfl]
        field_simp [hM1_pos.ne']
      _ ≤ ε.toReal * 1 :=
        mul_le_mul_of_nonneg_left hfrac_le_one ENNReal.toReal_nonneg
      _ = ε.toReal := by ring
  have hconst_le :
      eLpNorm (fun _ : ℂ ↦ δ) 1 μK ≤ ε := by
    calc
      eLpNorm (fun _ : ℂ ↦ δ) 1 μK
          = ENNReal.ofReal δ * μK Set.univ := by
            rw [eLpNorm_const' (μ := μK) (p := (1 : ℝ≥0∞)) (c := δ)
              (by norm_num : (1 : ℝ≥0∞) ≠ 0)
              (by norm_num : (1 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))]
            simp [Real.enorm_eq_ofReal hδ_nonneg, ENNReal.rpow_one]
      _ = ENNReal.ofReal δ * ENNReal.ofReal M := by
            rw [ENNReal.ofReal_toReal hμK_ne_top]
      _ = ENNReal.ofReal (δ * M) := by
            rw [ENNReal.ofReal_mul hδ_nonneg]
      _ ≤ ε := by
            rw [ENNReal.ofReal_le_iff_le_toReal hε_top]
            exact hδM_le
  have hunif_event :
      ∀ᶠ n : ℕ in Filter.atTop, ∀ z ∈ K, dist (f z) (F n z) < δ :=
    (Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ_pos
  rcases Filter.eventually_atTop.1 hunif_event with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  have hpoint :
      ∀ᵐ z ∂μK, ‖F n z - f z‖ ≤ δ := by
    refine ae_restrict_of_forall_mem hK_meas ?_
    intro z hzK
    have hdist : dist (f z) (F n z) < δ := hN n hn z hzK
    rw [Real.dist_eq] at hdist
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact le_of_lt hdist
  exact (eLpNorm_mono_ae_real (μ := μK) (p := (1 : ℝ≥0∞)) hpoint).trans hconst_le

/--
%%handwave
name:
  A compact-uniform limit and an \(L^1\)-limit agree almost everywhere
statement:
  If one sequence converges in \(L^1\) to a function and uniformly on a
  compact set to another function, then the two limits agree almost
  everywhere on that compact set.
proof:
  Uniform convergence on the compact set gives \(L^1\)-convergence to the
  uniform limit.  The two \(L^1\)-limits of the same sequence are therefore
  equal almost everywhere.
-/
theorem ae_eq_of_tendstoUniformlyOn_compact_and_eLpNorm_one_tendsto_zero
    {K : Set ℂ} (hK : IsCompact K)
    {F : ℕ → ℂ → ℝ} {u f : ℂ → ℝ}
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict K))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict K))
    (hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict K))
    (hFu :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z ↦ F n z - u z) 1
          (MeasureTheory.volume.restrict K))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (huniform : TendstoUniformlyOn F f Filter.atTop K) :
    u =ᵐ[MeasureTheory.volume.restrict K] f := by
  exact
    ae_eq_of_eLpNorm_one_tendsto_zero_of_common_approx
      hF_meas hu_meas hf_meas hFu
      (eLpNorm_one_tendsto_zero_of_tendstoUniformlyOn_compact hK huniform)

/--
%%handwave
name:
  \(L^1\)-convergence gives an eventual \(L^1\)-bound
statement:
  If a sequence converges to a locally integrable function in \(L^1\), then
  the \(L^1\)-seminorms of the sequence are eventually bounded by a finite
  constant.
proof:
  The triangle inequality bounds each \(L^1\)-seminorm by the approximation
  error plus the \(L^1\)-seminorm of the limit.  The approximation error is
  eventually at most one, and the limit has finite \(L^1\)-seminorm.
-/
theorem eventually_eLpNorm_one_le_const_of_tendsto_eLpNorm_one_sub
    {μ : Measure ℂ} {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n) μ)
    (hu_meas : AEStronglyMeasurable u μ)
    (hu_lt_top : eLpNorm u 1 μ < (∞ : ℝ≥0∞))
    (hFu :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z ↦ F n z - u z) 1 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ C : ℝ≥0∞,
      C < (∞ : ℝ≥0∞) ∧
        ∀ᶠ n : ℕ in Filter.atTop, eLpNorm (F n) 1 μ ≤ C := by
  let C : ℝ≥0∞ := 1 + eLpNorm u 1 μ
  have hC_lt_top : C < (∞ : ℝ≥0∞) := by
    exact ENNReal.add_lt_top.2 ⟨by norm_num, hu_lt_top⟩
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (fun z ↦ F n z - u z) 1 μ ≤ (1 : ℝ≥0∞) := by
    rcases ENNReal.tendsto_atTop_zero.mp hFu 1 (by norm_num) with ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  refine ⟨C, hC_lt_top, ?_⟩
  filter_upwards [hsmall] with n hn
  have htri :
      eLpNorm (F n) 1 μ ≤
        eLpNorm (fun z ↦ F n z - u z) 1 μ + eLpNorm u 1 μ := by
    calc
      eLpNorm (F n) 1 μ
          =
          eLpNorm ((fun z ↦ F n z - u z) + u) 1 μ := by
            congr 1
            funext z
            change F n z = (F n z - u z) + u z
            ring
      _ ≤ eLpNorm (fun z ↦ F n z - u z) 1 μ + eLpNorm u 1 μ :=
            eLpNorm_add_le ((hF_meas n).sub hu_meas) hu_meas (by norm_num)
  exact htri.trans (add_le_add hn le_rfl)

/--
%%handwave
name:
  A point in an open plane region has a compact collar
statement:
  Around every point of an open plane region there are an open neighbourhood,
  a compact set containing that neighbourhood, and a larger compact set still
  inside the region, with a positive closed-thickening margin between the two
  compact sets.
proof:
  Choose a ball around the point contained in the open region.  Take a small
  open ball, its closed ball, and a larger closed ball.  The smaller closed
  ball lies in the interior of the larger one, so compactness supplies a
  positive closed-thickening still contained in that interior, hence in the
  larger compact set.
-/
theorem exists_compact_collar_for_point_of_isOpen
    {Ω : Set ℂ} (hΩ_open : IsOpen Ω) {z : ℂ} (hzΩ : z ∈ Ω) :
    ∃ V Q P : Set ℂ,
      z ∈ V ∧ IsOpen V ∧ IsCompact Q ∧ V ⊆ Q ∧ IsCompact P ∧
        (∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P) ∧ P ⊆ Ω := by
  rcases Metric.mem_nhds_iff.mp (hΩ_open.mem_nhds hzΩ) with
    ⟨R, hR_pos, hballΩ⟩
  let r : ℝ := R / 4
  let s : ℝ := R / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt_s : r < s := by
    dsimp [r, s]
    linarith
  have hs_lt_R : s < R := by
    dsimp [s]
    linarith
  let V : Set ℂ := Metric.ball z r
  let Q : Set ℂ := Metric.closedBall z r
  let P : Set ℂ := Metric.closedBall z s
  have hV_open : IsOpen V := by
    simp [V]
  have hQ_compact : IsCompact Q := by
    simpa [Q] using isCompact_closedBall z r
  have hP_compact : IsCompact P := by
    simpa [P] using isCompact_closedBall z s
  have hVQ : V ⊆ Q := by
    simpa [V, Q] using Metric.ball_subset_closedBall
  have hQ_ball_s : Q ⊆ Metric.ball z s := by
    simpa [Q] using Metric.closedBall_subset_ball (x := z) hr_lt_s
  rcases hQ_compact.exists_cthickening_subset_open Metric.isOpen_ball hQ_ball_s with
    ⟨δ, hδ_pos, hδ_ball⟩
  have hδP : Metric.cthickening δ Q ⊆ P := by
    intro x hx
    exact Metric.ball_subset_closedBall (hδ_ball hx)
  have hPΩ : P ⊆ Ω := by
    exact (Metric.closedBall_subset_ball (x := z) hs_lt_R).trans hballΩ
  refine ⟨V, Q, P, ?_, hV_open, hQ_compact, hVQ, hP_compact, ?_, hPΩ⟩
  · simpa [V] using Metric.mem_ball_self (x := z) hr_pos
  · exact ⟨δ, hδ_pos, hδP⟩

/--
%%handwave
name:
  Small standard mollifiers are cutoff-locally harmonic
statement:
  If a compact neighborhood of \(Q\) lies in the one set of a cutoff, then
  all sufficiently small standard mollifications of the cutoff-localized weak
  solution are harmonic on every open subset of \(Q\).
proof:
  The outer radii of the standard mollifiers tend to zero.  Once the radius
  is smaller than the compact collar separating \(Q\) from the one set, the
  reflected mollifier support lies inside that one set, so the cutoff-local
  harmonicity theorem applies.
-/
theorem eventually_euclideanMollification_cutoff_standardMollifier_harmonicOnNhd
    {V Q P Ω : Set ℂ} (hQ : IsCompact Q) (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ))
    (hdu_one_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z (1 : ℂ)) Ω
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z Complex.I) Ω
      (MeasureTheory.volume : Measure ℂ)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      InnerProductSpace.HarmonicOnNhd
        (euclideanMollification
          (scalarWeakSobolevStandardMollifier ℂ n)
          (fun y : ℂ ↦ χ y * u y)) V := by
  let δ : ℝ := Classical.choose hQP
  have hδ_pos : 0 < δ := (Classical.choose_spec hQP).1
  have hδP : Metric.cthickening δ Q ⊆ P := (Classical.choose_spec hQP).2
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        (scalarWeakSobolevStandardMollifier ℂ n).rOut ≤ δ := by
    exact
      (scalarWeakSobolevStandardMollifier_rOut_tendsto_zero ℂ).eventually
        (eventually_le_nhds hδ_pos)
  filter_upwards [hsmall] with n hnsmall
  have hthickeningP :
      Metric.cthickening (scalarWeakSobolevStandardMollifier ℂ n).rOut Q ⊆ P :=
    (Metric.cthickening_mono hnsmall Q).trans hδP
  exact
    euclideanMollification_cutoff_harmonicOnNhd_of_weaklyHarmonicOn_compact_open
      (V := V) (Q := Q) (P := P) (Ω := Ω) hQ hV_open hVQ
      hthickeningP hPΩ χ hweak hzero hu_loc hdu_one_loc hdu_I_loc

/--
%%handwave
name:
  Small standard mollifiers satisfy the cutoff-local mean value identity
statement:
  Under the same compact-collar hypotheses, all sufficiently small standard
  cutoff-local mollifications satisfy the circle mean-value identity on every
  circle whose closed disk lies in the protected open set.
proof:
  Apply eventual cutoff-local harmonicity of the standard mollifications and
  then the harmonic mean-value theorem.
-/
theorem eventually_euclideanMollification_cutoff_standardMollifier_circleAverage_eq
    {V Q P Ω : Set ℂ} (hQ : IsCompact Q) (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ))
    (hdu_one_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z (1 : ℂ)) Ω
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_loc : LocallyIntegrableOn (fun z : ℂ ↦ du z Complex.I) Ω
      (MeasureTheory.volume : Measure ℂ))
    {c : ℂ} {R : ℝ}
    (hclosedBall : Metric.closedBall c |R| ⊆ V) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.circleAverage
          (euclideanMollification
            (scalarWeakSobolevStandardMollifier ℂ n)
            (fun y : ℂ ↦ χ y * u y)) c R =
        euclideanMollification
          (scalarWeakSobolevStandardMollifier ℂ n)
          (fun y : ℂ ↦ χ y * u y) c := by
  have hharm_eventually :=
    eventually_euclideanMollification_cutoff_standardMollifier_harmonicOnNhd
      (V := V) (Q := Q) (P := P) (Ω := Ω) hQ hV_open hVQ hQP hPΩ χ
      hweak hzero hu_loc hdu_one_loc hdu_I_loc
  filter_upwards [hharm_eventually] with n hn
  exact HarmonicOnNhd.circleAverage_eq (hn.mono hclosedBall)

/--
%%handwave
name:
  Local harmonic mollifier sequence for a weakly harmonic function
statement:
  On a compact collar inside a weakly harmonic Euclidean region, there is a
  cutoff-local standard-mollifier sequence which is eventually harmonic on
  any protected open subset and converges almost everywhere to the original
  function on the cutoff one set.
proof:
  Choose a smooth cutoff equal to one on the compact collar.  The weak
  harmonicity hypothesis supplies the weak derivative, the zero-divergence
  identity, and local integrability of the function and coordinate weak
  derivatives.  Apply eventual cutoff-local harmonicity of standard
  mollifiers and their almost-everywhere convergence on the one set.
-/
theorem exists_cutoff_standardMollifier_harmonicOnNhd_and_tendsto_ae_of_weaklyHarmonicOn
    {V Q P Ω : Set ℂ} {u : ℂ → ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u)
    (hQ : IsCompact Q) (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) :
    ∃ χ : ScalarWeakSobolevCutoff P Ω,
      (∀ᶠ n : ℕ in Filter.atTop,
        InnerProductSpace.HarmonicOnNhd
          (euclideanMollification
            (scalarWeakSobolevStandardMollifier ℂ n)
            (fun y : ℂ ↦ χ y * u y)) V) ∧
        (∀ᵐ z ∂(MeasureTheory.volume.restrict P : Measure ℂ),
          Filter.Tendsto
            (fun n : ℕ ↦
              euclideanMollification
                (scalarWeakSobolevStandardMollifier ℂ n)
                (fun y : ℂ ↦ χ y * u y) z)
            Filter.atTop (𝓝 (u z))) := by
  rcases hweak.exists_weakDerivative with ⟨du, hdu, hzero⟩
  rcases exists_scalarWeakSobolevCutoff hP hPΩ hweak.isOpen with ⟨χ⟩
  have hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ) :=
    hweak.locallyIntegrableOn
  have hdu_one_loc :
      LocallyIntegrableOn (fun z : ℂ ↦ du z (1 : ℂ)) Ω
        (MeasureTheory.volume : Measure ℂ) :=
    hweak.weakDerivative_locallyIntegrableOn hdu (1 : ℂ)
  have hdu_I_loc :
      LocallyIntegrableOn (fun z : ℂ ↦ du z Complex.I) Ω
        (MeasureTheory.volume : Measure ℂ) :=
    hweak.weakDerivative_locallyIntegrableOn hdu Complex.I
  refine ⟨χ, ?_, ?_⟩
  · exact
      eventually_euclideanMollification_cutoff_standardMollifier_harmonicOnNhd
        (V := V) (Q := Q) (P := P) (Ω := Ω) hQ hV_open hVQ hQP hPΩ χ
        hdu hzero hu_loc hdu_one_loc hdu_I_loc
  · exact
      euclideanMollification_cutoff_standardMollifier_tendsto_ae_on_one_set
        hP.measurableSet χ hu_loc

/--
%%handwave
name:
  Local harmonic mollifier sequence with \(L^1\)-convergence
statement:
  On a compact collar inside a weakly harmonic Euclidean region, there is a
  cutoff-local standard-mollifier sequence which is eventually harmonic on
  any protected open subset, converges almost everywhere to the original
  function on the cutoff one set, and converges to it in \(L^1\) on the
  compact protected set.
proof:
  Use the cutoff-local harmonic mollifier sequence already constructed.
  The weakly harmonic function is locally integrable, so the cutoff-local
  \(L^1\)-convergence theorem applies to the same cutoff.
-/
theorem exists_cutoff_standardMollifier_harmonicOnNhd_and_tendsto_ae_and_l1_of_weaklyHarmonicOn
    {V Q P Ω : Set ℂ} {u : ℂ → ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u)
    (hQ : IsCompact Q) (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) :
    ∃ χ : ScalarWeakSobolevCutoff P Ω,
      (∀ᶠ n : ℕ in Filter.atTop,
        InnerProductSpace.HarmonicOnNhd
          (euclideanMollification
            (scalarWeakSobolevStandardMollifier ℂ n)
            (fun y : ℂ ↦ χ y * u y)) V) ∧
        (∀ᵐ z ∂(MeasureTheory.volume.restrict P : Measure ℂ),
          Filter.Tendsto
            (fun n : ℕ ↦
              euclideanMollification
                (scalarWeakSobolevStandardMollifier ℂ n)
                (fun y : ℂ ↦ χ y * u y) z)
            Filter.atTop (𝓝 (u z))) ∧
          Filter.Tendsto
            (fun n : ℕ ↦
              eLpNorm
                (fun z ↦
                  euclideanMollification
                    (scalarWeakSobolevStandardMollifier ℂ n)
                    (fun y : ℂ ↦ χ y * u y) z - u z)
                1 (MeasureTheory.volume.restrict Q))
            Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  rcases
    exists_cutoff_standardMollifier_harmonicOnNhd_and_tendsto_ae_of_weaklyHarmonicOn
      (V := V) (Q := Q) (P := P) (Ω := Ω) hweak hQ hV_open hVQ hP hQP hPΩ with
    ⟨χ, hharm, hae⟩
  have hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ) :=
    hweak.locallyIntegrableOn
  refine ⟨χ, hharm, hae, ?_⟩
  exact
    euclideanMollification_cutoff_standardMollifier_tendsto_l1_on_compact_one_set
      hQ hP hQP χ hu_loc

/--
%%handwave
name:
  Local harmonic mollifier sequence around a point
statement:
  Around every point of a weakly harmonic Euclidean region, there is a compact
  collar and a cutoff-local standard-mollifier sequence which is eventually
  harmonic on a neighbourhood of the point, converges almost everywhere on
  the cutoff one set, and converges in \(L^1\) on the protected compact set.
proof:
  Apply the compact-collar construction at the point and then apply the
  local harmonic mollifier construction on that collar.
-/
theorem exists_local_cutoff_standardMollifier_harmonicOnNhd_and_tendsto_ae_and_l1_of_weaklyHarmonicOn
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u) {z : ℂ} (hzΩ : z ∈ Ω) :
    ∃ V Q P : Set ℂ, ∃ χ : ScalarWeakSobolevCutoff P Ω,
      z ∈ V ∧ IsOpen V ∧ IsCompact Q ∧ V ⊆ Q ∧ V ⊆ Ω ∧ IsCompact P ∧
        P ⊆ Ω ∧
          (∀ᶠ n : ℕ in Filter.atTop,
            InnerProductSpace.HarmonicOnNhd
              (euclideanMollification
                (scalarWeakSobolevStandardMollifier ℂ n)
                (fun y : ℂ ↦ χ y * u y)) V) ∧
            (∀ᵐ w ∂(MeasureTheory.volume.restrict P : Measure ℂ),
              Filter.Tendsto
                (fun n : ℕ ↦
                  euclideanMollification
                    (scalarWeakSobolevStandardMollifier ℂ n)
                    (fun y : ℂ ↦ χ y * u y) w)
                Filter.atTop (𝓝 (u w))) ∧
              Filter.Tendsto
                (fun n : ℕ ↦
                  eLpNorm
                    (fun w ↦
                      euclideanMollification
                        (scalarWeakSobolevStandardMollifier ℂ n)
                        (fun y : ℂ ↦ χ y * u y) w - u w)
                    1 (MeasureTheory.volume.restrict Q))
                Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  rcases exists_compact_collar_for_point_of_isOpen hweak.isOpen hzΩ with
    ⟨V, Q, P, hzV, hV_open, hQ, hVQ, hP, hQP, hPΩ⟩
  have hVΩ : V ⊆ Ω :=
    hVQ.trans ((subset_of_exists_cthickening_subset hQP).trans hPΩ)
  rcases
    exists_cutoff_standardMollifier_harmonicOnNhd_and_tendsto_ae_and_l1_of_weaklyHarmonicOn
      (V := V) (Q := Q) (P := P) (Ω := Ω) hweak hQ hV_open hVQ hP hQP hPΩ with
    ⟨χ, hharm, hae, hl1⟩
  exact
    ⟨V, Q, P, χ, hzV, hV_open, hQ, hVQ, hVΩ, hP, hPΩ, hharm, hae, hl1⟩

/--
%%handwave
name:
  Harmonic representatives are unique from almost-everywhere agreement
statement:
  Two harmonic functions on an open plane region which agree almost
  everywhere on that region agree pointwise throughout the region.
proof:
  Harmonic functions are continuous.  On an open set for Lebesgue measure,
  continuous functions which agree almost everywhere agree everywhere.
-/
theorem harmonicOnNhd_eqOn_of_ae_eq_on_isOpen
    {U : Set ℂ} (hU_open : IsOpen U) {f g : ℂ → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f U)
    (hg : InnerProductSpace.HarmonicOnNhd g U)
    (hae : f =ᵐ[MeasureTheory.volume.restrict U] g) :
    U.EqOn f g :=
  MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU_open hf.continuousOn hg.continuousOn

/--
%%handwave
name:
  Harmonic representatives agree on overlaps
statement:
  If two harmonic functions agree almost everywhere with the same weak
  function on two open regions, then they agree pointwise on the overlap.
proof:
  Restrict the two almost-everywhere identities to the overlap.  The two
  harmonic functions then agree almost everywhere there, and uniqueness of
  continuous harmonic representatives on an open set gives pointwise
  agreement.
-/
theorem harmonicOnNhd_eqOn_inter_of_ae_eq_to_common
    {U V : Set ℂ} (hU_open : IsOpen U) (hV_open : IsOpen V)
    {u f g : ℂ → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f U)
    (hg : InnerProductSpace.HarmonicOnNhd g V)
    (huf : u =ᵐ[MeasureTheory.volume.restrict U] f)
    (hug : u =ᵐ[MeasureTheory.volume.restrict V] g) :
    (U ∩ V).EqOn f g := by
  have hW_open : IsOpen (U ∩ V) := hU_open.inter hV_open
  have hfu :
      f =ᵐ[MeasureTheory.volume.restrict (U ∩ V)] u :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (by intro z hz; exact hz.1) huf.symm
  have hug' :
      u =ᵐ[MeasureTheory.volume.restrict (U ∩ V)] g :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (by intro z hz; exact hz.2) hug
  exact
    harmonicOnNhd_eqOn_of_ae_eq_on_isOpen hW_open
      (hf.mono Set.inter_subset_left) (hg.mono Set.inter_subset_right)
      (hfu.trans hug')

/--
%%handwave
name:
  Local mollifications are harmonic
statement:
  If an open set lies in a compact set whose mollifier support remains inside
  the weakly harmonic region, then the mollification is classically harmonic
  on that open set.
proof:
  Smoothness follows from convolution with the smooth compactly supported
  kernel.  For the Laplacian condition, each nearby point still has the compact
  set as a neighborhood, so the pointwise zero-Laplacian theorem applies
  throughout a neighborhood.
-/
theorem euclideanMollification_harmonicOnNhd_of_weaklyHarmonicOn_compact_open
    {V Q Ω : Set ℂ} (hQ : IsCompact Q) (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    {φ : ContDiffBump (0 : ℂ)}
    (hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_int : Integrable u (MeasureTheory.volume : Measure ℂ))
    (hdu_one_int : Integrable (fun z : ℂ ↦ du z (1 : ℂ))
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_int : Integrable (fun z : ℂ ↦ du z Complex.I)
      (MeasureTheory.volume : Measure ℂ)) :
    InnerProductSpace.HarmonicOnNhd (euclideanMollification φ u) V := by
  have hm_smooth : ContDiff ℝ ∞ (euclideanMollification φ u) :=
    euclideanMollification_contDiff φ hu_int.locallyIntegrable
  intro z hzV
  have hm_two : ContDiffAt ℝ 2 (euclideanMollification φ u) z :=
    (hm_smooth.contDiffAt).of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)
  refine ⟨hm_two, ?_⟩
  filter_upwards [hV_open.mem_nhds hzV] with w hwV
  have hQ_nhds : Q ∈ 𝓝 w :=
    Filter.mem_of_superset (hV_open.mem_nhds hwV) hVQ
  exact
    euclideanMollification_laplacian_eq_zero_of_weaklyHarmonicOn_compact_nhds
      (Q := Q) (Ω := Ω) hQ hQ_nhds hthickening hweak hzero
      hu_int hdu_one_int hdu_I_int

/--
%%handwave
name:
  Mean value identity for local mollifications
statement:
  On every circle whose closed disk lies in the protected open set, the
  weakly harmonic mollification equals its circle average.
proof:
  The previous theorem makes the mollification harmonic on the protected open
  set.  Restrict harmonicity to the closed disk and apply the harmonic
  mean-value theorem.
-/
theorem euclideanMollification_circleAverage_eq_of_weaklyHarmonicOn_compact_open
    {V Q Ω : Set ℂ} (hQ : IsCompact Q) (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    {φ : ContDiffBump (0 : ℂ)}
    (hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hzero :
      ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
        Integrable
            (fun z ↦
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z))
            (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω,
              euclideanCotangentPairing (du z)
                (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0)
    (hu_int : Integrable u (MeasureTheory.volume : Measure ℂ))
    (hdu_one_int : Integrable (fun z : ℂ ↦ du z (1 : ℂ))
      (MeasureTheory.volume : Measure ℂ))
    (hdu_I_int : Integrable (fun z : ℂ ↦ du z Complex.I)
      (MeasureTheory.volume : Measure ℂ))
    {c : ℂ} {R : ℝ}
    (hclosedBall : Metric.closedBall c |R| ⊆ V) :
    Real.circleAverage (euclideanMollification φ u) c R =
      euclideanMollification φ u c := by
  have hharm :
      InnerProductSpace.HarmonicOnNhd (euclideanMollification φ u) V :=
    euclideanMollification_harmonicOnNhd_of_weaklyHarmonicOn_compact_open
      (V := V) (Q := Q) (Ω := Ω) hQ hV_open hVQ hthickening hweak hzero
      hu_int hdu_one_int hdu_I_int
  exact HarmonicOnNhd.circleAverage_eq (hharm.mono hclosedBall)

/--
%%handwave
name:
  Euclidean Weyl harmonic representative
statement:
  A Euclidean weakly harmonic function has a harmonic representative which
  agrees with it almost everywhere on the coordinate region.
-/
structure EuclideanWeylHarmonicRepresentative
    (Ω : Set ℂ) (u : ℂ → ℝ) where
  /-- The harmonic representative. -/
  toFun : ℂ → ℝ
  /-- The representative is harmonic on the coordinate region. -/
  harmonicOn : InnerProductSpace.HarmonicOnNhd toFun Ω
  /-- The representative agrees with the original weak solution almost everywhere. -/
  ae_eq : u =ᵐ[MeasureTheory.volume.restrict Ω] toFun

namespace EuclideanWeylHarmonicRepresentative

instance {Ω : Set ℂ} {u : ℂ → ℝ} :
    CoeFun (EuclideanWeylHarmonicRepresentative Ω u) (fun _ ↦ ℂ → ℝ) where
  coe h := h.toFun

/--
%%handwave
name:
  Harmonic functions are their own Weyl representatives
statement:
  A harmonic function is a Weyl representative of itself.
-/
def of_harmonicOn
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u Ω) :
    EuclideanWeylHarmonicRepresentative Ω u where
  toFun := u
  harmonicOn := hu
  ae_eq := by rfl

/--
%%handwave
name:
  A harmonic almost-everywhere representative is a Weyl representative
statement:
  If a harmonic function agrees almost everywhere with a weak solution on the
  region, then it is a Weyl representative of that weak solution.
-/
def of_harmonicOn_ae_eq
    {Ω : Set ℂ} {u f : ℂ → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f Ω)
    (hae : u =ᵐ[MeasureTheory.volume.restrict Ω] f) :
    EuclideanWeylHarmonicRepresentative Ω u where
  toFun := f
  harmonicOn := hf
  ae_eq := hae

/--
%%handwave
name:
  Pointwise representatives are harmonic
statement:
  If the original weak solution agrees locally with a harmonic Weyl
  representative at every point of the region, then the original
  representative itself is harmonic there.
proof:
  Harmonicity is invariant under equality in a neighbourhood of each point.
-/
theorem harmonicOnNhd_of_eventuallyEq
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hrep : EuclideanWeylHarmonicRepresentative Ω u)
    (hpointwise : ∀ z ∈ Ω, u =ᶠ[𝓝 z] hrep.toFun) :
    InnerProductSpace.HarmonicOnNhd u Ω := by
  intro z hz
  exact
    (InnerProductSpace.harmonicAt_congr_nhds
      (hpointwise z hz)).2 (hrep.harmonicOn z hz)

/--
%%handwave
name:
  Weyl representatives are unique on open regions
statement:
  Two harmonic representatives of the same weak solution on an open plane
  region agree pointwise throughout that region.
proof:
  Both representatives agree almost everywhere with the weak solution, hence
  almost everywhere with each other.  Harmonic representatives are continuous,
  so almost-everywhere agreement on the open region is pointwise agreement.
-/
theorem eqOn_of_isOpen
    {Ω : Set ℂ} {u : ℂ → ℝ} (hΩ_open : IsOpen Ω)
    (hrep₁ hrep₂ : EuclideanWeylHarmonicRepresentative Ω u) :
    Ω.EqOn hrep₁.toFun hrep₂.toFun := by
  have hae : hrep₁.toFun =ᵐ[MeasureTheory.volume.restrict Ω] hrep₂.toFun :=
    hrep₁.ae_eq.symm.trans hrep₂.ae_eq
  exact
    harmonicOnNhd_eqOn_of_ae_eq_on_isOpen hΩ_open
      hrep₁.harmonicOn hrep₂.harmonicOn hae

end EuclideanWeylHarmonicRepresentative

/--
%%handwave
name:
  Weyl representatives agree across chart overlaps
statement:
  Harmonic representatives obtained in two overlapping surface charts agree
  pointwise after composing one of them with the holomorphic coordinate
  transition.
proof:
  The representative in the second chart, composed with the transition map,
  is harmonic because coordinate changes are analytic.  Its almost-everywhere
  agreement with the same weak surface function pulls back across the
  transition by nonsingularity of chart changes.  Thus the two harmonic
  functions agree almost everywhere on the overlap, and uniqueness of
  harmonic representatives upgrades this to pointwise agreement.
-/
theorem euclideanWeylHarmonicRepresentative_eqOn_surfaceChartOverlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [ComplexOneManifold X]
    (g : SmoothRiemannianMetricOnSurface X)
    {U : Set X} (hU_open : IsOpen U) {u : X → ℝ}
    (e e' : OpenPartialHomeomorph X ℂ)
    (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X)
    (hrep :
      EuclideanWeylHarmonicRepresentative
        (e.target ∩ e.symm ⁻¹' U)
        (fun z : ℂ ↦ u (e.symm z)))
    (hrep' :
      EuclideanWeylHarmonicRepresentative
        (e'.target ∩ e'.symm ⁻¹' U)
        (fun z : ℂ ↦ u (e'.symm z))) :
    (surfaceChartOverlapDomain e' e ∩
        (e.target ∩ e.symm ⁻¹' U)).EqOn
      hrep.toFun
      (fun z : ℂ ↦ hrep'.toFun (surfaceChartTransition e' e z)) := by
  let Ω : Set ℂ := e.target ∩ e.symm ⁻¹' U
  let Ω' : Set ℂ := e'.target ∩ e'.symm ⁻¹' U
  let D : Set ℂ := surfaceChartOverlapDomain e' e
  let R : Set ℂ := surfaceChartOverlapRange e' e
  let W : Set ℂ := D ∩ Ω
  let T : ℂ → ℂ := surfaceChartTransition e' e
  have hΩ_open : IsOpen Ω := by
    simpa [Ω] using e.isOpen_inter_preimage_symm hU_open
  have hΩ'_open : IsOpen Ω' := by
    simpa [Ω'] using e'.isOpen_inter_preimage_symm hU_open
  have hD_open : IsOpen D := by
    simpa [D] using surfaceChartOverlapDomain_isOpen e' e
  have hR_open : IsOpen R := by
    simpa [R] using surfaceChartOverlapRange_isOpen e' e
  have hW_open : IsOpen W := hD_open.inter hΩ_open
  have hW_meas : MeasurableSet W := hW_open.measurableSet
  have hR_meas : MeasurableSet R := hR_open.measurableSet
  have hrep_harm_W :
      InnerProductSpace.HarmonicOnNhd hrep.toFun W :=
    hrep.harmonicOn.mono (by
      intro z hz
      exact hz.2)
  have hrep'_comp_harm_W :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ hrep'.toFun (T z)) W := by
    intro z hz
    have hzD : z ∈ D := hz.1
    have hzΩ : z ∈ Ω := hz.2
    have hz_target : z ∈ e.target := by
      simpa [D, surfaceChartOverlapDomain] using hzD.1
    have hx_source' : e.symm z ∈ e'.source := by
      simpa [D, surfaceChartOverlapDomain] using hzD.2
    have hTΩ' : T z ∈ Ω' := by
      have hT_target : T z ∈ e'.target := by
        simpa [T, surfaceChartTransition] using e'.mapsTo hx_source'
      have hsymm : e'.symm (T z) = e.symm z := by
        simpa [T, surfaceChartTransition] using e'.left_inv hx_source'
      refine ⟨hT_target, ?_⟩
      simpa [hsymm, Ω] using hzΩ.2
    have h_at : InnerProductSpace.HarmonicAt hrep'.toFun (T z) :=
      hrep'.harmonicOn (T z) hTΩ'
    have htransition :
        AnalyticAt ℂ T z := by
      simpa [T, surfaceChartTransition] using
        chartTransition_analyticAt e he e' he' hz_target hx_source'
    simpa [T, Function.comp_def] using
      harmonicAt_comp_analyticAt h_at htransition
  have hrep_ae_W :
      hrep.toFun =ᵐ[MeasureTheory.volume.restrict W]
        (fun z : ℂ ↦ u (e.symm z)) := by
    exact
      ae_restrict_of_ae_restrict_of_subset
        (by intro z hz; exact hz.2)
        hrep.ae_eq.symm
  have hrep'_ae_on_R :
      ∀ᵐ y ∂MeasureTheory.volume.restrict R,
        y ∈ Ω' → u (e'.symm y) = hrep'.toFun y := by
    have hglobal :
        ∀ᵐ y ∂MeasureTheory.volume,
          y ∈ Ω' → u (e'.symm y) = hrep'.toFun y := by
      simpa [Ω'] using ae_imp_of_ae_restrict hrep'.ae_eq
    rw [ae_restrict_iff' hR_meas]
    filter_upwards [hglobal] with y hy hyR hyΩ'
    exact hy hyΩ'
  have hrep'_pull_D :
      ∀ᵐ z ∂MeasureTheory.volume.restrict D,
        T z ∈ Ω' → u (e'.symm (T z)) = hrep'.toFun (T z) := by
    simpa [D, R, T] using
      surfaceChartTransition_ae_restrict_overlapDomain_of_ae_restrict_overlapRange
        X g e' e he' he hrep'_ae_on_R
  have hrep'_pull_W :
      (fun z : ℂ ↦ u (e.symm z)) =ᵐ[
          MeasureTheory.volume.restrict W]
        (fun z : ℂ ↦ hrep'.toFun (T z)) := by
    have hpull_W :
        ∀ᵐ z ∂MeasureTheory.volume.restrict W,
          T z ∈ Ω' → u (e'.symm (T z)) = hrep'.toFun (T z) :=
      ae_restrict_of_ae_restrict_of_subset
        (by intro z hz; exact hz.1) hrep'_pull_D
    filter_upwards [hpull_W, ae_restrict_mem hW_meas] with z hz_pull hzW
    have hzD : z ∈ D := hzW.1
    have hzΩ : z ∈ Ω := hzW.2
    have hx_source' : e.symm z ∈ e'.source := by
      simpa [D, surfaceChartOverlapDomain] using hzD.2
    have hTΩ' : T z ∈ Ω' := by
      have hT_target : T z ∈ e'.target := by
        simpa [T, surfaceChartTransition] using e'.mapsTo hx_source'
      have hsymm : e'.symm (T z) = e.symm z := by
        simpa [T, surfaceChartTransition] using e'.left_inv hx_source'
      refine ⟨hT_target, ?_⟩
      simpa [hsymm, Ω] using hzΩ.2
    have hsymm : e'.symm (T z) = e.symm z := by
      simpa [T, surfaceChartTransition] using e'.left_inv hx_source'
    simpa [hsymm] using hz_pull hTΩ'
  exact
    harmonicOnNhd_eqOn_of_ae_eq_on_isOpen hW_open
      hrep_harm_W hrep'_comp_harm_W
      (hrep_ae_W.trans hrep'_pull_W)

/--
%%handwave
name:
  Local Euclidean Weyl harmonic representative
statement:
  A local Euclidean Weyl representative at a point is a harmonic function on
  an open neighbourhood of that point, contained in the original region, and
  agreeing almost everywhere there with the weak solution.
-/
structure LocalEuclideanWeylHarmonicRepresentative
    (Ω : Set ℂ) (u : ℂ → ℝ) (z : ℂ) where
  /-- The neighbourhood on which this local representative is defined. -/
  carrier : Set ℂ
  /-- The marked point lies in the carrier. -/
  mem_carrier : z ∈ carrier
  /-- The carrier is open. -/
  isOpen_carrier : IsOpen carrier
  /-- The carrier lies in the ambient weakly harmonic region. -/
  carrier_subset : carrier ⊆ Ω
  /-- The local harmonic representative. -/
  toFun : ℂ → ℝ
  /-- The representative is harmonic on the carrier. -/
  harmonicOn : InnerProductSpace.HarmonicOnNhd toFun carrier
  /-- The representative agrees with the weak solution almost everywhere on the carrier. -/
  ae_eq : u =ᵐ[MeasureTheory.volume.restrict carrier] toFun

namespace LocalEuclideanWeylHarmonicRepresentative

instance {Ω : Set ℂ} {u : ℂ → ℝ} {z : ℂ} :
    CoeFun (LocalEuclideanWeylHarmonicRepresentative Ω u z) (fun _ ↦ ℂ → ℝ) where
  coe h := h.toFun

/--
%%handwave
name:
  A harmonic local almost-everywhere representative is a local Weyl representative
statement:
  A harmonic function on an open neighbourhood of a point gives a local Weyl
  representative when it agrees almost everywhere with the weak solution on
  that neighbourhood.
-/
def of_harmonicOn_ae_eq
    {Ω V : Set ℂ} {u f : ℂ → ℝ} {z : ℂ}
    (hzV : z ∈ V) (hV_open : IsOpen V) (hVΩ : V ⊆ Ω)
    (hf : InnerProductSpace.HarmonicOnNhd f V)
    (hae : u =ᵐ[MeasureTheory.volume.restrict V] f) :
    LocalEuclideanWeylHarmonicRepresentative Ω u z where
  carrier := V
  mem_carrier := hzV
  isOpen_carrier := hV_open
  carrier_subset := hVΩ
  toFun := f
  harmonicOn := hf
  ae_eq := hae

/--
%%handwave
name:
  Global Weyl representatives localize
statement:
  A global Weyl representative on an open region gives a local Weyl
  representative at every point of that region.
-/
def of_global
    {Ω : Set ℂ} {u : ℂ → ℝ} {z : ℂ}
    (hΩ_open : IsOpen Ω)
    (hrep : EuclideanWeylHarmonicRepresentative Ω u)
    (hzΩ : z ∈ Ω) :
    LocalEuclideanWeylHarmonicRepresentative Ω u z :=
  of_harmonicOn_ae_eq hzΩ hΩ_open (fun _ hx ↦ hx)
    hrep.harmonicOn hrep.ae_eq

/--
%%handwave
name:
  Local Weyl representatives agree on overlaps
statement:
  Any two local Weyl representatives of the same weak solution agree
  pointwise on the intersection of their carriers.
proof:
  Both harmonic functions agree almost everywhere with the weak solution on
  their respective carriers.  Restrict these identities to the overlap and
  use uniqueness of harmonic representatives there.
-/
theorem eqOn_inter
    {Ω : Set ℂ} {u : ℂ → ℝ} {z w : ℂ}
    (hrep₁ : LocalEuclideanWeylHarmonicRepresentative Ω u z)
    (hrep₂ : LocalEuclideanWeylHarmonicRepresentative Ω u w) :
    (hrep₁.carrier ∩ hrep₂.carrier).EqOn hrep₁.toFun hrep₂.toFun := by
  exact
    harmonicOnNhd_eqOn_inter_of_ae_eq_to_common
      hrep₁.isOpen_carrier hrep₂.isOpen_carrier
      hrep₁.harmonicOn hrep₂.harmonicOn hrep₁.ae_eq hrep₂.ae_eq

/--
%%handwave
name:
  Local Weyl representatives have equal values on common points
statement:
  At any point belonging to the carriers of two local Weyl representatives
  of the same weak solution, the two representative values are equal.
-/
theorem eq_of_mem_inter
    {Ω : Set ℂ} {u : ℂ → ℝ} {z w x : ℂ}
    (hrep₁ : LocalEuclideanWeylHarmonicRepresentative Ω u z)
    (hrep₂ : LocalEuclideanWeylHarmonicRepresentative Ω u w)
    (hx₁ : x ∈ hrep₁.carrier) (hx₂ : x ∈ hrep₂.carrier) :
    hrep₁.toFun x = hrep₂.toFun x :=
  eqOn_inter hrep₁ hrep₂ ⟨hx₁, hx₂⟩

end LocalEuclideanWeylHarmonicRepresentative

/--
%%handwave
name:
  Gluing local Euclidean Weyl representatives
statement:
  Given a local harmonic representative at every point of the region, choose
  one at each point and define the glued function by the value of the chosen
  local representative there.
-/
noncomputable def localEuclideanWeylRepresentativeGlue
    (Ω : Set ℂ) (u : ℂ → ℝ)
    (hlocal :
      ∀ z ∈ Ω, Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z)) :
    ℂ → ℝ := by
  classical
  exact fun z ↦
    if hz : z ∈ Ω then
      (Classical.choice (hlocal z hz)).toFun z
    else 0

/--
%%handwave
name:
  The glued representative agrees with each local representative
statement:
  On the carrier of any chosen local representative, the glued function
  agrees pointwise with that representative.
proof:
  At a point in the carrier, the glued function is defined using the local
  representative chosen at that point.  The two local representatives agree
  on the overlap of their carriers.
-/
theorem localEuclideanWeylRepresentativeGlue_eqOn_carrier
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hlocal :
      ∀ z ∈ Ω, Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z))
    {z : ℂ} (hzΩ : z ∈ Ω) :
    (Classical.choice (hlocal z hzΩ)).carrier.EqOn
      (localEuclideanWeylRepresentativeGlue Ω u hlocal)
      (Classical.choice (hlocal z hzΩ)).toFun := by
  classical
  intro y hy
  have hyΩ : y ∈ Ω :=
    (Classical.choice (hlocal z hzΩ)).carrier_subset hy
  rw [localEuclideanWeylRepresentativeGlue, dif_pos hyΩ]
  exact
    LocalEuclideanWeylHarmonicRepresentative.eq_of_mem_inter
      (Classical.choice (hlocal y hyΩ))
      (Classical.choice (hlocal z hzΩ))
      (Classical.choice (hlocal y hyΩ)).mem_carrier hy

/--
%%handwave
name:
  The glued local Weyl representative is harmonic
statement:
  If every point of a region has a local harmonic representative, then the
  glued representative is harmonic on the whole region.
proof:
  Near any point, the glued function agrees with the chosen local harmonic
  representative on its open carrier.  Harmonicity is invariant under
  equality in a neighbourhood.
-/
theorem localEuclideanWeylRepresentativeGlue_harmonicOnNhd
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hlocal :
      ∀ z ∈ Ω, Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z)) :
    InnerProductSpace.HarmonicOnNhd
      (localEuclideanWeylRepresentativeGlue Ω u hlocal) Ω := by
  classical
  intro z hzΩ
  let hrep := Classical.choice (hlocal z hzΩ)
  have heq :
      localEuclideanWeylRepresentativeGlue Ω u hlocal =ᶠ[𝓝 z] hrep.toFun := by
    filter_upwards [hrep.isOpen_carrier.mem_nhds hrep.mem_carrier] with y hy
    simpa [hrep] using
      localEuclideanWeylRepresentativeGlue_eqOn_carrier hlocal hzΩ hy
  exact
    (InnerProductSpace.harmonicAt_congr_nhds heq).2
      (hrep.harmonicOn z hrep.mem_carrier)

/--
%%handwave
name:
  The glued local Weyl representative agrees almost everywhere
statement:
  If every point of a region has a local harmonic representative, then the
  glued representative agrees almost everywhere with the weak solution on the
  whole region.
proof:
  The local carriers form a neighbourhood cover of the region.  Second
  countability gives a countable subcover.  On each carrier, the local
  almost-everywhere identity and pointwise agreement with the glued function
  give almost-everywhere agreement with the glued function; the countable
  cover combines these identities over the whole region.
-/
theorem localEuclideanWeylRepresentativeGlue_ae_eq
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hlocal :
      ∀ z ∈ Ω, Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z)) :
    u =ᵐ[MeasureTheory.volume.restrict Ω]
      localEuclideanWeylRepresentativeGlue Ω u hlocal := by
  classical
  let localSet : ℂ → Set ℂ := fun z ↦
    if hz : z ∈ Ω then
      (Classical.choice (hlocal z hz)).carrier
    else ∅
  have hnhds : ∀ z ∈ Ω, localSet z ∈ 𝓝[Ω] z := by
    intro z hzΩ
    let hrep := Classical.choice (hlocal z hzΩ)
    have hmem : hrep.carrier ∈ 𝓝 z :=
      hrep.isOpen_carrier.mem_nhds hrep.mem_carrier
    simpa [localSet, hzΩ, hrep] using
      mem_nhdsWithin_of_mem_nhds hmem
  rcases TopologicalSpace.countable_cover_nhdsWithin hnhds with
    ⟨T, hTΩ, hT_countable, hcover⟩
  have hcover_ae :
      ∀ᵐ y ∂MeasureTheory.volume.restrict (⋃ z ∈ T, localSet z),
        u y = localEuclideanWeylRepresentativeGlue Ω u hlocal y := by
    rw [MeasureTheory.ae_restrict_biUnion_iff localSet hT_countable
      (fun y : ℂ ↦ u y = localEuclideanWeylRepresentativeGlue Ω u hlocal y)]
    intro z hzT
    have hzΩ : z ∈ Ω := hTΩ hzT
    let hrep := Classical.choice (hlocal z hzΩ)
    have hpoint :
        hrep.carrier.EqOn hrep.toFun
          (localEuclideanWeylRepresentativeGlue Ω u hlocal) := by
      intro y hy
      exact
        (localEuclideanWeylRepresentativeGlue_eqOn_carrier hlocal hzΩ hy).symm
    have hglue :
        hrep.toFun =ᵐ[MeasureTheory.volume.restrict hrep.carrier]
          localEuclideanWeylRepresentativeGlue Ω u hlocal :=
      hpoint.aeEq_restrict hrep.isOpen_carrier.measurableSet
    have hae :
        u =ᵐ[MeasureTheory.volume.restrict hrep.carrier]
          localEuclideanWeylRepresentativeGlue Ω u hlocal :=
      hrep.ae_eq.trans hglue
    simpa [localSet, hzΩ, hrep] using hae
  exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset hcover hcover_ae

/--
%%handwave
name:
  Local Weyl representatives glue to a global representative
statement:
  If every point of a Euclidean region has a local harmonic representative
  agreeing almost everywhere with the weak solution, then the weak solution
  has a global harmonic representative on the region.
proof:
  Glue the chosen local representatives.  Overlap uniqueness makes the glued
  function locally equal to each chosen representative, hence harmonic.  A
  countable subcover of the local carriers combines the almost-everywhere
  identities into global almost-everywhere agreement.
-/
theorem euclideanWeylHarmonicRepresentative_of_local_representatives
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hlocal :
      ∀ z ∈ Ω, Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z)) :
    Nonempty (EuclideanWeylHarmonicRepresentative Ω u) := by
  refine
    ⟨EuclideanWeylHarmonicRepresentative.of_harmonicOn_ae_eq
      (localEuclideanWeylRepresentativeGlue_harmonicOnNhd hlocal) ?_⟩
  exact localEuclideanWeylRepresentativeGlue_ae_eq hlocal

/--
%%handwave
name:
  Pointwise Euclidean Weyl representative
statement:
  A weak solution has a pointwise Euclidean Weyl representative on a region
  if it has a harmonic Weyl representative with which it agrees in a
  neighbourhood of every point of the region.
-/
def HasPointwiseEuclideanWeylRepresentative
    (Ω : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ∃ hrep : EuclideanWeylHarmonicRepresentative Ω u,
    ∀ z ∈ Ω, u =ᶠ[𝓝 z] hrep.toFun

/--
%%handwave
name:
  Pointwise Euclidean Weyl representatives are harmonic
statement:
  A function with a pointwise Euclidean Weyl representative is harmonic on
  the region.
-/
theorem harmonicOnNhd_of_pointwiseEuclideanWeylRepresentative
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hrep : HasPointwiseEuclideanWeylRepresentative Ω u) :
    InnerProductSpace.HarmonicOnNhd u Ω := by
  rcases hrep with ⟨v, hv⟩
  exact v.harmonicOnNhd_of_eventuallyEq hv

/--
%%handwave
name:
  Harmonic functions have pointwise Weyl representatives
statement:
  A harmonic function has itself as a pointwise Euclidean Weyl representative.
-/
theorem pointwiseEuclideanWeylRepresentative_of_harmonicOn
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u Ω) :
    HasPointwiseEuclideanWeylRepresentative Ω u := by
  refine ⟨EuclideanWeylHarmonicRepresentative.of_harmonicOn hu, ?_⟩
  intro z _hz
  simp [EuclideanWeylHarmonicRepresentative.of_harmonicOn]

/--
%%handwave
name:
  Harmonic common \(L^1\)-limits give Weyl representatives
statement:
  If one approximating sequence converges in \(L^1\) both to the weak
  solution and to a harmonic function, then the harmonic function is a Weyl
  representative of the weak solution.
proof:
  The two \(L^1\)-limits of the same sequence agree almost everywhere.  Use
  the harmonic limit as the representative.
-/
theorem euclideanWeylHarmonicRepresentative_of_harmonic_common_l1_approx
    {Ω : Set ℂ} {F : ℕ → ℂ → ℝ} {u f : ℂ → ℝ}
    (hf_harm : InnerProductSpace.HarmonicOnNhd f Ω)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict Ω))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict Ω))
    (hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict Ω))
    (hFu :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z ↦ F n z - u z) 1
          (MeasureTheory.volume.restrict Ω))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (hFf :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z ↦ F n z - f z) 1
          (MeasureTheory.volume.restrict Ω))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Nonempty (EuclideanWeylHarmonicRepresentative Ω u) := by
  refine ⟨EuclideanWeylHarmonicRepresentative.of_harmonicOn_ae_eq hf_harm ?_⟩
  exact
    ae_eq_of_eLpNorm_one_tendsto_zero_of_common_approx
      hF_meas hu_meas hf_meas hFu hFf

/--
%%handwave
name:
  Harmonic common local \(L^1\)-limits give local Weyl representatives
statement:
  On an open neighbourhood of a point, if one approximating sequence
  converges in \(L^1\) both to the weak solution and to a harmonic function,
  then that harmonic function is a local Weyl representative.
proof:
  The two \(L^1\)-limits of the same sequence agree almost everywhere on the
  neighbourhood.  Package the harmonic function and this almost-everywhere
  identity as a local representative.
-/
theorem localEuclideanWeylHarmonicRepresentative_of_harmonic_common_l1_approx
    {Ω V : Set ℂ} {z : ℂ} {F : ℕ → ℂ → ℝ} {u f : ℂ → ℝ}
    (hzV : z ∈ V) (hV_open : IsOpen V) (hVΩ : V ⊆ Ω)
    (hf_harm : InnerProductSpace.HarmonicOnNhd f V)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V))
    (hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict V))
    (hFu :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (hFf :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - f w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z) := by
  refine
    ⟨LocalEuclideanWeylHarmonicRepresentative.of_harmonicOn_ae_eq
      hzV hV_open hVΩ hf_harm ?_⟩
  exact
    ae_eq_of_eLpNorm_one_tendsto_zero_of_common_approx
      hF_meas hu_meas hf_meas hFu hFf

/--
%%handwave
name:
  Harmonic local \(L^1\)-limits on a protected piece give local representatives
statement:
  If the approximating sequence converges to the weak solution in \(L^1\) on
  a larger protected set and to a harmonic function in \(L^1\) on the open
  neighbourhood, then the harmonic limit is a local Weyl representative.
proof:
  Restrict the \(L^1\)-convergence to the weak solution from the protected
  set to the smaller neighbourhood, then apply the common-local-limit
  representative criterion.
-/
theorem localEuclideanWeylHarmonicRepresentative_of_harmonic_common_l1_approx_on_superset
    {Ω V Q : Set ℂ} {z : ℂ} {F : ℕ → ℂ → ℝ} {u f : ℂ → ℝ}
    (hzV : z ∈ V) (hV_open : IsOpen V) (hVΩ : V ⊆ Ω) (hVQ : V ⊆ Q)
    (hf_harm : InnerProductSpace.HarmonicOnNhd f V)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V))
    (hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict V))
    (hFuQ :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (hFfV :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - f w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z) := by
  exact
    localEuclideanWeylHarmonicRepresentative_of_harmonic_common_l1_approx
      hzV hV_open hVΩ hf_harm hF_meas hu_meas hf_meas
      (tendsto_eLpNorm_one_zero_restrict_mono (A := V) (B := Q)
        hVQ hFuQ)
      hFfV

/--
%%handwave
name:
  Harmonic subsequential local \(L^1\)-limits give local representatives
statement:
  If a sequence converges to the weak solution in \(L^1\) on a larger
  protected set, and a subsequence converges in \(L^1\) on the neighbourhood
  to a harmonic function, then that harmonic limit is a local Weyl
  representative.
proof:
  Compose the convergence to the weak solution with the subsequence and apply
  the common-local-limit representative criterion.
-/
theorem localEuclideanWeylHarmonicRepresentative_of_harmonic_subsequence_l1_approx_on_superset
    {Ω V Q : Set ℂ} {z : ℂ} {G : ℕ → ℂ → ℝ} {φ : ℕ → ℕ}
    {u f : ℂ → ℝ}
    (hzV : z ∈ V) (hV_open : IsOpen V) (hVΩ : V ⊆ Ω) (hVQ : V ⊆ Q)
    (hf_harm : InnerProductSpace.HarmonicOnNhd f V)
    (hφ : StrictMono φ)
    (hG_meas : ∀ n : ℕ, AEStronglyMeasurable (G n)
      (MeasureTheory.volume.restrict V))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V))
    (hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict V))
    (hGuQ :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ G n w - u w) 1
          (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (hGφfV :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ G (φ n) w - f w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z) := by
  exact
    localEuclideanWeylHarmonicRepresentative_of_harmonic_common_l1_approx_on_superset
      (F := fun n : ℕ ↦ G (φ n)) hzV hV_open hVΩ hVQ hf_harm
      (fun n ↦ hG_meas (φ n)) hu_meas hf_meas
      (hGuQ.comp hφ.tendsto_atTop) hGφfV

/--
%%handwave
name:
  Cutoff standard mollifications are measurable
statement:
  The standard mollifications of a cutoff-localized locally integrable
  function are almost everywhere strongly measurable on every measurable
  region.
proof:
  The cutoff-localized function is globally integrable.  Convolution with the
  smooth compactly supported standard mollifier is smooth, hence continuous
  and almost everywhere strongly measurable.
-/
theorem euclideanMollification_cutoff_standardMollifier_aestronglyMeasurable
    {P Ω V : Set ℂ} (χ : ScalarWeakSobolevCutoff P Ω)
    {u : ℂ → ℝ}
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ))
    (n : ℕ) :
    AEStronglyMeasurable
      (euclideanMollification
        (scalarWeakSobolevStandardMollifier ℂ n)
        (fun y : ℂ ↦ χ y * u y))
      (MeasureTheory.volume.restrict V) := by
  have huχ_int :
      Integrable (fun y : ℂ ↦ χ y * u y)
        (MeasureTheory.volume : Measure ℂ) :=
    scalarWeakSobolevCutoff_value_integrable χ hu_loc
  have hcont :
      Continuous
        (euclideanMollification
          (scalarWeakSobolevStandardMollifier ℂ n)
          (fun y : ℂ ↦ χ y * u y)) :=
    (euclideanMollification_contDiff
      (scalarWeakSobolevStandardMollifier ℂ n)
      huχ_int.locallyIntegrable).continuous
  exact hcont.aestronglyMeasurable

/--
%%handwave
name:
  Changing an \(L^1\)-limit on a null set preserves \(L^1\)-convergence
statement:
  If two candidate limits agree almost everywhere, convergence in \(L^1\) to
  one is the same as convergence in \(L^1\) to the other.
proof:
  The two difference functions agree almost everywhere for every index, so
  their \(L^1\)-seminorms are equal termwise.
-/
theorem tendsto_eLpNorm_one_zero_congr_ae_limit
    {μ : Measure ℂ} {F : ℕ → ℂ → ℝ} {u f : ℂ → ℝ}
    (huf : u =ᵐ[μ] f)
    (hFu :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - f w) 1 μ)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  refine hFu.congr fun n ↦ ?_
  have hdiff :
      (fun w : ℂ ↦ F n w - u w) =ᵐ[μ]
        (fun w : ℂ ↦ F n w - f w) := by
    filter_upwards [huf] with w hw
    rw [hw]
  exact eLpNorm_congr_ae (p := (1 : ℝ≥0∞)) hdiff

/--
%%handwave
name:
  Equicontinuity is invariant under pointwise equality
statement:
  If two indexed families of functions agree pointwise, then equicontinuity of
  one family on a set implies equicontinuity of the other family on that set.
-/
theorem equicontinuousOn_congr_pointwise
    {ι X Y : Type} [TopologicalSpace X] [UniformSpace Y]
    {S : Set X} {F G : ι → X → Y}
    (hFG : ∀ i x, F i x = G i x)
    (hF : EquicontinuousOn F S) :
    EquicontinuousOn G S := by
  intro x hx U hU
  filter_upwards [hF x hx U hU] with y hy i
  simpa [hFG i x, hFG i y] using hy i

/--
%%handwave
name:
  Real-valued compact-open Arzelà-Ascoli extraction
statement:
  A sequence of real-valued continuous functions on a locally compact
  sigma-compact space has a compact-open convergent subsequence if it is
  pointwise relatively compact and equicontinuous on every member of a compact
  exhaustion.
proof:
  Mathlib's Arzelà-Ascoli theorem gives compactness of the closure of the
  sequence in the compact-open topology.  Since the compact-open function
  space is second countable, compactness gives a convergent subsequence.
-/
theorem realContinuousMap_subsequence_tendsto_of_equicontinuousOn_compactExhaustion
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [SecondCountableTopology X] (K : CompactExhaustion X)
    (G : ℕ → C(X, ℝ))
    (hpointwise : ∀ x : X, ∃ Q : Set ℝ, IsCompact Q ∧
      ∀ n : ℕ, G n x ∈ Q)
    (heq : ∀ m : ℕ,
      EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) (K m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : C(X, ℝ), Filter.Tendsto (fun n : ℕ ↦ G (φ n)) Filter.atTop (𝓝 g) := by
  haveI : SecondCountableTopology C(X, ℝ) := inferInstance
  have hclosedEmbedding :
      Topology.IsClosedEmbedding
        (ContinuousMap.toUniformOnFunIsCompact :
          C(X, ℝ) → UniformOnFun X ℝ {S : Set X | IsCompact S}) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
  have hcompactClosure : IsCompact (closure (Set.range G)) := by
    refine
      ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
        (𝔖 := {S : Set X | IsCompact S})
        (F := fun g : C(X, ℝ) ↦ fun x : X ↦ g x)
        (fun S hS ↦ hS) ?_ ?_ ?_
    · simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using hclosedEmbedding
    · intro S hS
      obtain ⟨m, hmS⟩ := K.exists_superset_of_isCompact hS
      let chooseIndex : Set.range G → ℕ := fun g ↦ Classical.choose g.property
      have hchoose : ∀ g : Set.range G, G (chooseIndex g) = g := fun g ↦
        Classical.choose_spec g.property
      have hseqS :
          EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) S :=
        (heq m).mono hmS
      have hcomp :
          EquicontinuousOn
            ((fun n : ℕ ↦ fun x : X ↦ G n x) ∘ chooseIndex) S :=
        hseqS.comp chooseIndex
      refine equicontinuousOn_congr_pointwise ?_ hcomp
      intro g x
      simpa [Function.comp_def] using congrArg (fun h : C(X, ℝ) ↦ h x) (hchoose g)
    · intro S hS x hx
      rcases hpointwise x with ⟨Q, hQcompact, hQmem⟩
      refine ⟨Q, hQcompact, ?_⟩
      intro g hg
      rcases hg with ⟨n, rfl⟩
      exact hQmem n
  have hmem : ∀ n : ℕ, G n ∈ closure (Set.range G) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  rcases hcompactClosure.tendsto_subseq hmem with
    ⟨g, _hg, φ, hφ, hφ_tendsto⟩
  exact ⟨φ, hφ, g, by simpa [Function.comp_def] using hφ_tendsto⟩

/--
%%handwave
name:
  Real-valued locally uniform Arzelà-Ascoli extraction
statement:
  Under the same compact-exhaustion hypotheses, the compact-open convergent
  subsequence converges locally uniformly.
proof:
  On weakly locally compact spaces, mathlib identifies compact-open
  convergence of continuous maps with locally uniform convergence.
-/
theorem realContinuousMap_subsequence_tendstoLocallyUniformly_of_equicontinuousOn_compactExhaustion
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [SecondCountableTopology X] (K : CompactExhaustion X)
    (G : ℕ → C(X, ℝ))
    (hpointwise : ∀ x : X, ∃ Q : Set ℝ, IsCompact Q ∧
      ∀ n : ℕ, G n x ∈ Q)
    (heq : ∀ m : ℕ,
      EquicontinuousOn (fun n : ℕ ↦ fun x : X ↦ G n x) (K m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : C(X, ℝ),
        TendstoLocallyUniformly
          (fun n : ℕ ↦ fun x : X ↦ G (φ n) x)
          (fun x : X ↦ g x) Filter.atTop := by
  rcases
    realContinuousMap_subsequence_tendsto_of_equicontinuousOn_compactExhaustion
      K G hpointwise heq with
    ⟨φ, hφ, g, hg⟩
  exact ⟨φ, hφ, g, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hg⟩

/--
%%handwave
name:
  Eventually bounded real sequences have compact range
statement:
  If a real sequence is eventually bounded in absolute value, then its whole
  range is contained in a compact subset of the real line.
proof:
  Put the finitely many exceptional initial values into a finite compact set
  and put the tail into a closed interval.
-/
theorem exists_compact_range_of_eventually_abs_le
    {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ᶠ n : ℕ in Filter.atTop, |a n| ≤ C) :
    ∃ Q : Set ℝ, IsCompact Q ∧ ∀ n : ℕ, a n ∈ Q := by
  rcases Filter.eventually_atTop.mp ha with ⟨N, hN⟩
  let Q : Set ℝ :=
    (Set.range fun k : Fin N ↦ a k.1) ∪ Metric.closedBall (0 : ℝ) C
  refine ⟨Q, ?_, ?_⟩
  · have hfinite : (Set.range fun k : Fin N ↦ a k.1).Finite :=
      Set.finite_range _
    exact hfinite.isCompact.union (isCompact_closedBall (0 : ℝ) C)
  · intro n
    by_cases hn : n < N
    · exact Or.inl ⟨⟨n, hn⟩, rfl⟩
    · have hNn : N ≤ n := le_of_not_gt hn
      have htail : |a n| ≤ C := hN n hNn
      exact Or.inr (by simpa [Metric.mem_closedBall, Real.dist_eq] using htail)

/--
%%handwave
name:
  Harmonic functions are integrable on compact closed disks
statement:
  If a harmonicity region contains a closed disk, then the absolute value of
  a harmonic function is integrable on that disk.
proof:
  Harmonic functions are continuous on their harmonicity region.  Restrict
  this continuity to the compact disk and use compact integrability of
  continuous functions.
-/
theorem harmonic_abs_integrable_closedBall
    {V : Set ℂ} {x : V} {r : ℝ} {f : ℂ → ℝ}
    (hball : Metric.closedBall x.1 r ⊆ V)
    (hf : InnerProductSpace.HarmonicOnNhd f V) :
    Integrable (fun z : ℂ ↦ |f z|)
      (MeasureTheory.volume.restrict (Metric.closedBall x.1 r)) := by
  let K : Set ℂ := Metric.closedBall x.1 r
  have hK_compact : IsCompact K := by
    simpa [K] using isCompact_closedBall x.1 r
  have hf_cont : ContinuousOn f K :=
    hf.continuousOn.mono (by simpa [K] using hball)
  have habs_cont : ContinuousOn (fun z : ℂ ↦ |f z|) K :=
    continuous_abs.comp_continuousOn hf_cont
  have h_int_on : IntegrableOn (fun z : ℂ ↦ |f z|) K
      (MeasureTheory.volume : Measure ℂ) :=
    ContinuousOn.integrableOn_compact hK_compact habs_cont
  simpa [IntegrableOn, K] using h_int_on

/--
%%handwave
name:
  The closed-disk \(L^1\)-seminorm is the integral of the absolute value
statement:
  For a harmonic function on a region containing a closed disk, the exponent
  one extended \(L^p\)-seminorm over the disk has real value equal to the
  integral of the absolute value over that disk.
proof:
  The previous compact-integrability result makes the \(L^1\)-seminorm
  finite.  Mathlib identifies exponent-one \(L^p\)-seminorms with the
  lower integral of the extended norm, and the Bochner integral identity
  converts that lower integral back to the ordinary integral of the norm.
-/
theorem harmonic_eLpNorm_one_closedBall_toReal_eq_integral_abs
    {V : Set ℂ} {x : V} {r : ℝ} {f : ℂ → ℝ}
    (hball : Metric.closedBall x.1 r ⊆ V)
    (hf : InnerProductSpace.HarmonicOnNhd f V) :
    (eLpNorm f 1
      (MeasureTheory.volume.restrict
        (Metric.closedBall x.1 r))).toReal =
      ∫ z in Metric.closedBall x.1 r, |f z| ∂MeasureTheory.volume := by
  let K : Set ℂ := Metric.closedBall x.1 r
  let μ : Measure ℂ := MeasureTheory.volume.restrict K
  have hf_cont : ContinuousOn f K :=
    hf.continuousOn.mono (by simpa [K] using hball)
  have hf_meas : AEStronglyMeasurable f μ :=
    hf_cont.aestronglyMeasurable (by
      simpa [K] using (isCompact_closedBall x.1 r).measurableSet)
  calc
    (eLpNorm f 1
        (MeasureTheory.volume.restrict
          (Metric.closedBall x.1 r))).toReal
        = (∫⁻ z, ‖f z‖ₑ ∂μ).toReal := by
            simp [μ, K, eLpNorm_one_eq_lintegral_enorm]
    _ = ∫ z, ‖f z‖ ∂μ := by
            exact (integral_norm_eq_lintegral_enorm hf_meas).symm
    _ = ∫ z in Metric.closedBall x.1 r, |f z| ∂MeasureTheory.volume := by
            simp [μ, K, Real.norm_eq_abs]

private theorem annulusRadialSet_eq_zero {r : ℝ} :
    {z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r} =
      Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (r / 2) := by
  ext z
  simp [Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm]
  constructor
  · intro hz
    exact ⟨hz.2, hz.1⟩
  · intro hz
    exact ⟨hz.2, hz.1⟩

private theorem annulus_polar_indicator_zero
    {r : ℝ} (_hr : 0 < r) {f : ℂ → ℝ} :
    (∫ z in (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (r / 2)),
        |f z| ∂MeasureTheory.volume) =
      ∫ p in Complex.polarCoord.target,
        p.1 * (({z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r}.indicator
          (fun z : ℂ ↦ |f z|)) (Complex.polarCoord.symm p)) ∂MeasureTheory.volume := by
  have hpolar :=
    Complex.integral_comp_polarCoord_symm
      (fun z : ℂ ↦ ({z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r}.indicator
          (fun z : ℂ ↦ |f z|)) z)
  calc
    ∫ z in (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (r / 2)),
        |f z| ∂MeasureTheory.volume
        =
      ∫ z : ℂ, ({z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r}.indicator
          (fun z : ℂ ↦ |f z|)) z ∂MeasureTheory.volume := by
          rw [← annulusRadialSet_eq_zero (r := r)]
          exact (integral_indicator
            ((isClosed_le continuous_const continuous_norm).inter
              (isClosed_le continuous_norm continuous_const)).measurableSet).symm
    _ =
      ∫ p in Complex.polarCoord.target,
        p.1 * (({z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r}.indicator
          (fun z : ℂ ↦ |f z|)) (Complex.polarCoord.symm p)) ∂MeasureTheory.volume := by
          simpa [smul_eq_mul, Complex.polarCoord_target,
            Complex.polarCoord_symm_apply] using hpolar.symm

private theorem annulus_polar_indicator_to_product
    {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} :
      ∫ p in Complex.polarCoord.target,
        p.1 * (({z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r}.indicator
          (fun z : ℂ ↦ |f z|)) (Complex.polarCoord.symm p)) ∂MeasureTheory.volume
    =
      ∫ p in Set.Icc (r / 2) r ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * |f (Complex.polarCoord.symm p)| ∂MeasureTheory.volume := by
  let B : Set (ℝ × ℝ) := Set.Icc (r / 2) r ×ˢ Set.univ
  have hB_meas : MeasurableSet B := measurableSet_Icc.prod MeasurableSet.univ
  have htarget_meas : MeasurableSet Complex.polarCoord.target :=
    Complex.polarCoord.open_target.measurableSet
  calc
    ∫ p in Complex.polarCoord.target,
        p.1 * (({z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r}.indicator
          (fun z : ℂ ↦ |f z|)) (Complex.polarCoord.symm p)) ∂MeasureTheory.volume
      =
    ∫ p in Complex.polarCoord.target,
        B.indicator (fun p : ℝ × ℝ ↦
          p.1 * |f (Complex.polarCoord.symm p)|) p ∂MeasureTheory.volume := by
      refine setIntegral_congr_fun htarget_meas ?_
      intro p hp
      have hp_pos : 0 < p.1 := by
        simpa [Complex.polarCoord_target] using hp.1
      by_cases hpB : p ∈ B
      · have hrad : ‖Complex.polarCoord.symm p‖ ∈ Set.Icc (r / 2) r := by
          have hpIcc : p.1 ∈ Set.Icc (r / 2) r := hpB.1
          simpa [Complex.norm_polarCoord_symm, abs_of_pos hp_pos] using hpIcc
        have hmem :
            Complex.polarCoord.symm p ∈
              {z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r} := hrad
        change
          p.1 *
              ({z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r}.indicator
                (fun z : ℂ ↦ |f z|) (Complex.polarCoord.symm p)) =
            B.indicator
              (fun p : ℝ × ℝ ↦ p.1 * |f (Complex.polarCoord.symm p)|) p
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpB]
      · have hrad_not : ¬ ‖Complex.polarCoord.symm p‖ ∈ Set.Icc (r / 2) r := by
          intro hrad
          apply hpB
          refine ⟨?_, trivial⟩
          simpa [Complex.norm_polarCoord_symm, abs_of_pos hp_pos] using hrad
        have hnotmem :
            Complex.polarCoord.symm p ∉
              {z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r} := hrad_not
        change
          p.1 *
              ({z : ℂ | ‖z‖ ∈ Set.Icc (r / 2) r}.indicator
                (fun z : ℂ ↦ |f z|) (Complex.polarCoord.symm p)) =
            B.indicator
              (fun p : ℝ × ℝ ↦ p.1 * |f (Complex.polarCoord.symm p)|) p
        rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hpB]
        simp
    _ =
      ∫ p in Complex.polarCoord.target ∩ B,
        p.1 * |f (Complex.polarCoord.symm p)| ∂MeasureTheory.volume := by
      rw [setIntegral_indicator hB_meas]
    _ =
      ∫ p in Set.Icc (r / 2) r ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * |f (Complex.polarCoord.symm p)| ∂MeasureTheory.volume := by
      have hset :
          Complex.polarCoord.target ∩ B =
            Set.Icc (r / 2) r ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        ext p
        constructor
        · intro hp
          rcases hp with ⟨hpT, hpB⟩
          have hpT' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
            simpa [Complex.polarCoord_target] using hpT
          exact ⟨hpB.1, hpT'.2⟩
        · intro hp
          refine ⟨?_, ?_⟩
          · have hp_pos : 0 < p.1 := (half_pos hr).trans_le hp.1.1
            simpa [Complex.polarCoord_target] using ⟨hp_pos, hp.2⟩
          · exact ⟨hp.1, trivial⟩
      rw [hset]

private theorem annulus_product_fubini
    {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) r)) :
      ∫ p in Set.Icc (r / 2) r ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * |f (Complex.polarCoord.symm p)| ∂MeasureTheory.volume
    =
      ∫ ρ in Set.Icc (r / 2) r,
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ρ * |f (Complex.polarCoord.symm (ρ, θ))| ∂MeasureTheory.volume
        ∂MeasureTheory.volume := by
  let rect : Set (ℝ × ℝ) :=
    Set.Icc (r / 2) r ×ˢ Set.Icc (-Real.pi) Real.pi
  let F : ℝ × ℝ → ℝ := fun p ↦ p.1 * |f (Complex.polarCoord.symm p)|
  have hsymm_cont :
      Continuous (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
    simpa [Complex.polarCoord] using
      (Complex.equivRealProdCLM.symm.continuous.comp
        continuous_polarCoord_symm)
  have hmaps :
      Set.MapsTo (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p)
        rect (Metric.closedBall (0 : ℂ) r) := by
    intro p hp
    have hp_nonneg : 0 ≤ p.1 := (half_pos hr).le.trans hp.1.1
    have hp_abs : |p.1| = p.1 := abs_of_nonneg hp_nonneg
    simpa [rect, Metric.mem_closedBall, dist_eq_norm,
      Complex.norm_polarCoord_symm, hp_abs] using hp.1.2
  have hF_cont : ContinuousOn F rect := by
    have hf_comp :
        ContinuousOn
          (fun p : ℝ × ℝ ↦ f (Complex.polarCoord.symm p)) rect :=
      hf.comp hsymm_cont.continuousOn hmaps
    dsimp [F]
    exact continuous_fst.continuousOn.mul
      (continuous_abs.comp_continuousOn hf_comp)
  have hF_int_rect :
      IntegrableOn F rect MeasureTheory.volume :=
    hF_cont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hsubset :
      Set.Icc (r / 2) r ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ rect :=
    Set.prod_mono (fun _ hx ↦ hx) Set.Ioo_subset_Icc_self
  have hF_int :
      IntegrableOn F
        (Set.Icc (r / 2) r ×ˢ Set.Ioo (-Real.pi) Real.pi)
        MeasureTheory.volume :=
    hF_int_rect.mono_set hsubset
  change
    ∫ p in Set.Icc (r / 2) r ×ˢ Set.Ioo (-Real.pi) Real.pi,
        F p ∂MeasureTheory.volume =
      ∫ ρ in Set.Icc (r / 2) r,
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          F (ρ, θ) ∂MeasureTheory.volume
        ∂MeasureTheory.volume
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact
    setIntegral_prod (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      (f := F) hF_int

private theorem polarCoord_symm_eq_circleMap (ρ θ : ℝ) :
    Complex.polarCoord.symm (ρ, θ) = circleMap (0 : ℂ) ρ θ := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

private theorem angular_integral_eq_circleAverage (ρ : ℝ) (f : ℂ → ℝ) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ρ * |f (Complex.polarCoord.symm (ρ, θ))| ∂MeasureTheory.volume =
      Real.circleAverage (fun z : ℂ ↦ |f z|) 0 ρ *
        (2 * Real.pi * ρ) := by
  let g : ℝ → ℝ := fun θ ↦ ρ * |f (circleMap (0 : ℂ) ρ θ)|
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hset_interval :
      ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ρ * |f (Complex.polarCoord.symm (ρ, θ))| ∂MeasureTheory.volume =
        ∫ θ in (-Real.pi)..Real.pi,
          ρ * |f (Complex.polarCoord.symm (ρ, θ))| := by
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  have hshift :
      ∫ θ in (-Real.pi)..Real.pi, g θ =
        ∫ θ in 0..2 * Real.pi, g (θ + -Real.pi) := by
    have hend : 2 * Real.pi + -Real.pi = Real.pi := by ring
    simpa [hend] using
      (intervalIntegral.integral_comp_add_right
        (f := g) (a := (0 : ℝ)) (b := 2 * Real.pi) (-Real.pi)).symm
  let I : ℝ :=
    ∫ θ in 0..2 * Real.pi,
      |f (circleMap (0 : ℂ) ρ (θ + -Real.pi))|
  have hconst :
      ∫ θ in 0..2 * Real.pi,
          g (θ + -Real.pi) =
        ρ * I := by
    simp [g, I]
  have hca :
      Real.circleAverage (fun z : ℂ ↦ |f z|) 0 ρ =
        (2 * Real.pi)⁻¹ * I := by
    simpa [Real.circleAverage_eq_integral_add, smul_eq_mul, I]
      using
        (Real.circleAverage_eq_integral_add
          (f := fun z : ℂ ↦ |f z|) (c := (0 : ℂ)) (R := ρ)
          (-Real.pi))
  have hI :
      I = (2 * Real.pi) *
        Real.circleAverage (fun z : ℂ ↦ |f z|) 0 ρ := by
    rw [hca]
    field_simp [mul_ne_zero two_ne_zero Real.pi_ne_zero]
  calc
    ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ρ * |f (Complex.polarCoord.symm (ρ, θ))| ∂MeasureTheory.volume
        =
      ∫ θ in (-Real.pi)..Real.pi,
        ρ * |f (Complex.polarCoord.symm (ρ, θ))| := hset_interval
    _ = ∫ θ in (-Real.pi)..Real.pi, g θ := by
      congr with θ
      rw [polarCoord_symm_eq_circleMap]
    _ = ∫ θ in 0..2 * Real.pi, g (θ + -Real.pi) := hshift
    _ = ρ * I := hconst
    _ = ρ * ((2 * Real.pi) *
        Real.circleAverage (fun z : ℂ ↦ |f z|) 0 ρ) := by rw [hI]
    _ = Real.circleAverage (fun z : ℂ ↦ |f z|) 0 ρ *
        (2 * Real.pi * ρ) := by ring

private theorem annulus_integral_abs_eq_setIntegral_circleAverage_mul_radius_zero
    {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) r)) :
    ∫ z in (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (r / 2)),
        |f z| ∂MeasureTheory.volume =
      ∫ ρ in Set.Ioo (r / 2) r,
        Real.circleAverage (fun z : ℂ ↦ |f z|) 0 ρ *
          (2 * Real.pi * ρ) ∂MeasureTheory.volume := by
  calc
    ∫ z in (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (r / 2)),
        |f z| ∂MeasureTheory.volume
        =
      ∫ p in Set.Icc (r / 2) r ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * |f (Complex.polarCoord.symm p)| ∂MeasureTheory.volume := by
      rw [annulus_polar_indicator_zero (r := r) hr (f := f)]
      exact annulus_polar_indicator_to_product (r := r) hr (f := f)
    _ =
      ∫ ρ in Set.Icc (r / 2) r,
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ρ * |f (Complex.polarCoord.symm (ρ, θ))| ∂MeasureTheory.volume
        ∂MeasureTheory.volume := annulus_product_fubini (r := r) hr hf
    _ =
      ∫ ρ in Set.Icc (r / 2) r,
        Real.circleAverage (fun z : ℂ ↦ |f z|) 0 ρ *
          (2 * Real.pi * ρ) ∂MeasureTheory.volume := by
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro ρ _hρ
      exact angular_integral_eq_circleAverage ρ f
    _ =
      ∫ ρ in Set.Ioo (r / 2) r,
        Real.circleAverage (fun z : ℂ ↦ |f z|) 0 ρ *
          (2 * Real.pi * ρ) ∂MeasureTheory.volume := by
      rw [integral_Icc_eq_integral_Ioo]

/--
%%handwave
name:
  Annular area integral in polar coordinates
statement:
  On a Euclidean annulus, the area integral of the absolute value of a
  continuous function is the radial integral of its circle averages, weighted
  by the Euclidean Jacobian.
proof:
  This is the polar-coordinate change of variables, with the boundary circles
  ignored because they have area measure zero.
-/
theorem annulus_integral_abs_eq_setIntegral_circleAverage_mul_radius
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hf : ContinuousOn f (Metric.closedBall c r)) :
    ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
        |f z| ∂MeasureTheory.volume =
      ∫ ρ in Set.Ioo (r / 2) r,
        Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ *
          (2 * Real.pi * ρ) ∂MeasureTheory.volume := by
  let g : ℂ → ℝ := fun z ↦ f (z + c)
  have hg_cont : ContinuousOn g (Metric.closedBall (0 : ℂ) r) := by
    refine hf.comp (by fun_prop) ?_
    intro z hz
    simpa [Metric.mem_closedBall, dist_eq_norm, g] using hz
  have hcenter :=
    annulus_integral_abs_eq_setIntegral_circleAverage_mul_radius_zero
      (r := r) hr (f := g) hg_cont
  have htranslate :
      ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
          |f z| ∂MeasureTheory.volume =
        ∫ z in (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (r / 2)),
          |g z| ∂MeasureTheory.volume := by
    let T : ℂ → ℂ := fun z ↦ z + c
    have hT_meas : MeasurableEmbedding T :=
      (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
    have hmap :=
      hT_meas.setIntegral_map
        (μ := MeasureTheory.volume)
        (g := fun z : ℂ ↦ |f z|)
        (s := Metric.closedBall c r \ Metric.ball c (r / 2))
    have hmap_eq :
        Measure.map T MeasureTheory.volume = MeasureTheory.volume := by
      simpa [T] using
        (map_add_right_eq_self (MeasureTheory.volume : Measure ℂ) c)
    rw [hmap_eq] at hmap
    have hpre :
        T ⁻¹' (Metric.closedBall c r \ Metric.ball c (r / 2)) =
          Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (r / 2) := by
      ext z
      simp [T, Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm]
    simpa [T, g, hpre] using hmap
  calc
    ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
        |f z| ∂MeasureTheory.volume
        =
      ∫ z in (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (r / 2)),
        |g z| ∂MeasureTheory.volume := htranslate
    _ =
      ∫ ρ in Set.Ioo (r / 2) r,
        Real.circleAverage (fun z : ℂ ↦ |g z|) 0 ρ *
          (2 * Real.pi * ρ) ∂MeasureTheory.volume := hcenter
    _ =
      ∫ ρ in Set.Ioo (r / 2) r,
        Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ *
          (2 * Real.pi * ρ) ∂MeasureTheory.volume := by
      refine setIntegral_congr_fun measurableSet_Ioo ?_
      intro ρ _hρ
      change
        Real.circleAverage (fun z : ℂ ↦ |f (z + c)|) 0 ρ *
            (2 * Real.pi * ρ) =
          Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ *
            (2 * Real.pi * ρ)
      rw [Real.circleAverage_map_add_const
        (f := fun z : ℂ ↦ |f z|) (c := c) (R := ρ)]

/--
%%handwave
name:
  A circle average is controlled by an annular area integral at some radius
statement:
  For a positive Euclidean disk radius, there is a geometric constant such
  that every continuous function on the closed disk has some radius in the
  outer annulus whose circle average of the absolute value is bounded by that
  constant times the area integral of the absolute value over the annulus.
proof:
  This is the polar-coordinate averaging step on the outer annulus.
  Integrating circle averages over the annulus recovers the annular area
  integral with the radial Jacobian, so one radius has circle average no
  larger than the annular average.
-/
theorem exists_radius_circleAverage_abs_le_const_mul_integral_abs_annulus_uniform_center
    {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ c : ℂ, ∀ f : ℂ → ℝ,
        ContinuousOn f (Metric.closedBall c r) →
          ∃ ρ : ℝ, r / 2 < ρ ∧ ρ < r ∧
            Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ ≤
              A *
                ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
                  |f z| ∂MeasureTheory.volume := by
  let I : Set ℝ := Set.Ioo (r / 2) r
  let weight : ℝ → ℝ := fun ρ ↦ 2 * Real.pi * ρ
  have hhalf_pos : 0 < r / 2 := half_pos hr
  have hI_nonempty : r / 2 < r := by linarith
  have hweight_cont_Icc : ContinuousOn weight (Set.Icc (r / 2) r) := by
    fun_prop
  have hweight_int_Icc :
      IntegrableOn weight (Set.Icc (r / 2) r) MeasureTheory.volume :=
    hweight_cont_Icc.integrableOn_compact isCompact_Icc
  have hweight_int :
      IntegrableOn weight I MeasureTheory.volume :=
    hweight_int_Icc.mono_set Set.Ioo_subset_Icc_self
  have hweight_nonneg_on : ∀ ρ ∈ I, 0 ≤ weight ρ := by
    intro ρ hρ
    have hρ_pos : 0 < ρ := hhalf_pos.trans hρ.1
    exact mul_nonneg (mul_pos zero_lt_two Real.pi_pos).le hρ_pos.le
  have hweight_nonneg_ae :
      0 ≤ᵐ[MeasureTheory.volume.restrict I] weight := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    exact ae_of_all MeasureTheory.volume hweight_nonneg_on
  have hweight_pos_on : ∀ ρ ∈ I, 0 < weight ρ := by
    intro ρ hρ
    have hρ_pos : 0 < ρ := hhalf_pos.trans hρ.1
    exact mul_pos (mul_pos zero_lt_two Real.pi_pos) hρ_pos
  have hI_subset_support :
      I ⊆ Function.support weight ∩ I := by
    intro ρ hρ
    exact ⟨(hweight_pos_on ρ hρ).ne', hρ⟩
  have hmeasure_support_pos :
      0 < MeasureTheory.volume (Function.support weight ∩ I) :=
    ((MeasureTheory.Measure.measure_Ioo_pos
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)).mpr hI_nonempty).trans_le
      (MeasureTheory.measure_mono hI_subset_support)
  have hweight_integral_pos :
      0 < ∫ ρ in I, weight ρ ∂MeasureTheory.volume :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      hweight_nonneg_ae hweight_int).2 hmeasure_support_pos
  let A : ℝ := (∫ ρ in I, weight ρ ∂MeasureTheory.volume)⁻¹
  refine ⟨A, inv_nonneg.mpr hweight_integral_pos.le, ?_⟩
  intro c f hf
  let avg : ℝ → ℝ := fun ρ ↦ Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ
  have habs_cont_radial :
      ContinuousOn (fun z : ℂ ↦ |f z|)
        {z : ℂ | ‖z - c‖ ∈ Set.Icc (r / 2) r} := by
    refine continuous_abs.comp_continuousOn (hf.mono ?_)
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hz.2
  have havg_cont_Icc : ContinuousOn avg (Set.Icc (r / 2) r) := by
    exact Real.ContinuousOn.circleAverage habs_cont_radial
      (fun ρ hρ ↦ hhalf_pos.le.trans hρ.1)
  have havg_cont_I : ContinuousOn avg I :=
    havg_cont_Icc.mono Set.Ioo_subset_Icc_self
  have hprod_cont_Icc :
      ContinuousOn (fun ρ ↦ avg ρ * weight ρ) (Set.Icc (r / 2) r) :=
    havg_cont_Icc.mul hweight_cont_Icc
  have hprod_int :
      IntegrableOn (fun ρ ↦ avg ρ * weight ρ) I MeasureTheory.volume :=
    (hprod_cont_Icc.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  rcases exists_eq_const_mul_setIntegral_of_nonneg
      (s := I) (f := avg) (g := weight) (μ := MeasureTheory.volume)
      (isConnected_Ioo hI_nonempty) measurableSet_Ioo havg_cont_I
      hweight_int hprod_int hweight_nonneg_on with
    ⟨ρ, hρI, hmean⟩
  refine ⟨ρ, hρI.1, hρI.2, ?_⟩
  have hpolar :=
    annulus_integral_abs_eq_setIntegral_circleAverage_mul_radius
      (c := c) (r := r) hr hf
  have hannulus_eq :
      ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
          |f z| ∂MeasureTheory.volume =
        avg ρ * ∫ ρ in I, weight ρ ∂MeasureTheory.volume := by
    calc
      ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
          |f z| ∂MeasureTheory.volume
          = ∫ ρ in I, avg ρ * weight ρ ∂MeasureTheory.volume := by
              simpa [I, avg, weight, mul_assoc] using hpolar
      _ = avg ρ * ∫ ρ in I, weight ρ ∂MeasureTheory.volume := hmean
  have havg_eq :
      avg ρ =
        A *
          ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
            |f z| ∂MeasureTheory.volume := by
    rw [hannulus_eq]
    dsimp [A]
    field_simp [ne_of_gt hweight_integral_pos]
  exact le_of_eq havg_eq

/--
%%handwave
name:
  A circle average is controlled by a centered annular area integral
statement:
  For a fixed positive radius and centre, there is a geometric constant such
  that every continuous function on the closed disk has some radius in the
  outer annulus whose circle average of the absolute value is bounded by that
  constant times the area integral over the annulus.
proof:
  Apply the centre-uniform annular averaging estimate.
-/
theorem exists_radius_circleAverage_abs_le_const_mul_integral_abs_annulus
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ f : ℂ → ℝ,
        ContinuousOn f (Metric.closedBall c r) →
          ∃ ρ : ℝ, r / 2 < ρ ∧ ρ < r ∧
            Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ ≤
              A *
                ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
                  |f z| ∂MeasureTheory.volume := by
  rcases exists_radius_circleAverage_abs_le_const_mul_integral_abs_annulus_uniform_center
      (r := r) hr with
    ⟨A, hA_nonneg, hA_bound⟩
  exact ⟨A, hA_nonneg, hA_bound c⟩

/--
%%handwave
name:
  A circle average is controlled by a disk integral at some radius
statement:
  For a positive Euclidean disk radius, there is a geometric constant such
  that every continuous function on the closed disk has some smaller circle
  whose average of the absolute value is bounded by that constant times the
  integral of the absolute value over the disk.
proof:
  This is the polar-coordinate averaging step.  Integrating the circle
  averages over a radial annulus recovers the disk integral with the radial
  Jacobian; hence one radius in the annulus has average no larger than the
  annular average.
-/
theorem exists_radius_circleAverage_abs_le_const_mul_integral_abs_closedBall
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ f : ℂ → ℝ,
        ContinuousOn f (Metric.closedBall c r) →
          ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧
            Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ ≤
              A * ∫ z in Metric.closedBall c r, |f z| ∂MeasureTheory.volume := by
  rcases exists_radius_circleAverage_abs_le_const_mul_integral_abs_annulus
      (c := c) hr with
    ⟨A, hA_nonneg, hA_bound⟩
  refine ⟨A, hA_nonneg, ?_⟩
  intro f hf
  rcases hA_bound f hf with ⟨ρ, hρ_half, hρ_lt, hcircle⟩
  have hclosed_int :
      IntegrableOn (fun z : ℂ ↦ |f z|)
        (Metric.closedBall c r) MeasureTheory.volume := by
    have hK : IsCompact (Metric.closedBall c r) :=
      isCompact_closedBall c r
    exact ContinuousOn.integrableOn_compact hK
      (continuous_abs.comp_continuousOn hf)
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Metric.closedBall c r)]
        (fun z : ℂ ↦ |f z|) :=
    Filter.Eventually.of_forall fun z ↦ abs_nonneg (f z)
  have hannulus_subset :
      (Metric.closedBall c r \ Metric.ball c (r / 2)) ⊆
        Metric.closedBall c r :=
    fun z hz ↦ hz.1
  have hannulus_le_closed :
      ∫ z in (Metric.closedBall c r \ Metric.ball c (r / 2)),
          |f z| ∂MeasureTheory.volume ≤
        ∫ z in Metric.closedBall c r, |f z| ∂MeasureTheory.volume :=
    setIntegral_mono_set hclosed_int hnonneg
      (Filter.Eventually.of_forall hannulus_subset)
  refine ⟨ρ, ?_, hρ_lt, ?_⟩
  · exact (half_pos hr).trans hρ_half
  · exact hcircle.trans
      (mul_le_mul_of_nonneg_left hannulus_le_closed hA_nonneg)

/--
%%handwave
name:
  Harmonic center values are bounded by circle averages of absolute values
statement:
  If a harmonic function is harmonic on a closed disk around a point, then
  the absolute value at the center is bounded by the circle average of the
  absolute value on the boundary circle.
proof:
  The harmonic mean-value theorem identifies the center value with the circle
  average of the function.  The absolute value of a circle average is at most
  the circle average of the absolute value.
-/
theorem harmonic_center_abs_le_circleAverage_abs
    {V : Set ℂ} {x : V} {ρ : ℝ} {f : ℂ → ℝ}
    (hρ_pos : 0 < ρ)
    (hball : Metric.closedBall x.1 ρ ⊆ V)
    (hf : InnerProductSpace.HarmonicOnNhd f V) :
    |f x.1| ≤ Real.circleAverage (fun z : ℂ ↦ |f z|) x.1 ρ := by
  have hρ_abs : |ρ| = ρ := abs_of_pos hρ_pos
  have hharm_closed :
      InnerProductSpace.HarmonicOnNhd f (Metric.closedBall x.1 |ρ|) := by
    rw [hρ_abs]
    exact hf.mono hball
  have hmean : Real.circleAverage f x.1 ρ = f x.1 :=
    HarmonicOnNhd.circleAverage_eq hharm_closed
  calc
    |f x.1| = |Real.circleAverage f x.1 ρ| := by rw [hmean]
    _ ≤ Real.circleAverage (fun z : ℂ ↦ |f z|) x.1 ρ :=
      Real.abs_circleAverage_le_circleAverage_abs

/--
%%handwave
name:
  Integral form of the interior \(L^1\)-to-value estimate
statement:
  If a closed Euclidean ball around a point is contained in a harmonicity
  region, then evaluation at the centre is bounded by a geometric constant
  times the integral of the absolute value over that closed ball.
proof:
  Choose a radius whose boundary circle average is controlled by the disk
  integral, using the polar-coordinate averaging estimate.  The harmonic
  mean-value theorem bounds the center value by that circle average.
-/
theorem exists_harmonic_center_abs_le_const_mul_integral_abs_closedBall
    {V : Set ℂ} {x : V} {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.closedBall x.1 r ⊆ V) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ f : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd f V →
          |f x.1| ≤
            A * ∫ z in Metric.closedBall x.1 r, |f z| ∂MeasureTheory.volume := by
  rcases exists_radius_circleAverage_abs_le_const_mul_integral_abs_closedBall
      (c := x.1) hr with
    ⟨A, hA_nonneg, hA_bound⟩
  refine ⟨A, hA_nonneg, ?_⟩
  intro f hf
  have hf_cont : ContinuousOn f (Metric.closedBall x.1 r) :=
    hf.continuousOn.mono hball
  rcases hA_bound f hf_cont with ⟨ρ, hρ_pos, hρ_lt_r, hcircle⟩
  have hρ_subset :
      Metric.closedBall x.1 ρ ⊆ V :=
    (Metric.closedBall_subset_closedBall hρ_lt_r.le).trans hball
  exact
    (harmonic_center_abs_le_circleAverage_abs
      (x := x) hρ_pos hρ_subset hf).trans hcircle

/--
%%handwave
name:
  Interior \(L^1\)-to-value estimate for harmonic functions
statement:
  If a closed Euclidean ball around a point is contained in a harmonicity
  region, then evaluation at the centre is bounded by a geometric constant
  times the \(L^1\)-norm over that closed ball.
proof:
  Apply the integral form of the mean-value estimate, then identify the
  closed-disk \(L^1\)-seminorm with the ordinary integral of the absolute
  value.
-/
theorem exists_harmonic_pointwise_l1_closedBall_constant
    {V : Set ℂ} {x : V} {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.closedBall x.1 r ⊆ V) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ f : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd f V →
          |f x.1| ≤
            A * (eLpNorm f 1
              (MeasureTheory.volume.restrict
                (Metric.closedBall x.1 r))).toReal := by
  rcases exists_harmonic_center_abs_le_const_mul_integral_abs_closedBall
      (x := x) hr hball with
    ⟨A, hA_nonneg, hA_bound⟩
  refine ⟨A, hA_nonneg, ?_⟩
  intro f hf
  rw [harmonic_eLpNorm_one_closedBall_toReal_eq_integral_abs
    (x := x) hball hf]
  exact hA_bound f hf

/--
%%handwave
name:
  Locally \(L^1\)-bounded harmonic families are eventually pointwise bounded
statement:
  At each point of an open plane region, a locally \(L^1\)-bounded harmonic
  sequence is eventually bounded in absolute value.
proof:
  This is the pointwise part of the interior harmonic estimate.  Choose a
  compact disk around the point and apply the mean-value or Poisson bound to
  control the value by the \(L^1\)-norm on that disk.
-/
theorem harmonic_locallyL1_bounded_eventually_abs_le_at_point
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hlocal_bound :
      ∀ K : Set ℂ, IsCompact K → K ⊆ V →
        ∃ C : ℝ≥0∞, C < (∞ : ℝ≥0∞) ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            eLpNorm (F n) 1 (MeasureTheory.volume.restrict K) ≤ C)
    (x : V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in Filter.atTop, |F n x.1| ≤ C := by
  rcases Metric.mem_nhds_iff.mp (hV_open.mem_nhds x.2) with
    ⟨R, hR_pos, hR_subset⟩
  let r : ℝ := R / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt_R : r < R := by
    dsimp [r]
    linarith
  have hclosed_subset_ball :
      Metric.closedBall x.1 r ⊆ Metric.ball x.1 R :=
    Metric.closedBall_subset_ball hr_lt_R
  have hclosed_subset_V : Metric.closedBall x.1 r ⊆ V :=
    hclosed_subset_ball.trans hR_subset
  rcases exists_harmonic_pointwise_l1_closedBall_constant
      (x := x) hr_pos hclosed_subset_V with
    ⟨A, hA_nonneg, hA_bound⟩
  let K : Set ℂ := Metric.closedBall x.1 r
  have hK_compact : IsCompact K := by
    simpa [K] using isCompact_closedBall x.1 r
  have hKV : K ⊆ V := by
    simpa [K] using hclosed_subset_V
  rcases hlocal_bound K hK_compact hKV with
    ⟨C, hC_lt_top, hC_event⟩
  refine ⟨A * C.toReal, mul_nonneg hA_nonneg ENNReal.toReal_nonneg, ?_⟩
  have hC_ne_top : C ≠ (∞ : ℝ≥0∞) := ne_of_lt hC_lt_top
  filter_upwards [hC_event] with n hn
  have hnorm_toReal :
      (eLpNorm (F n) 1 (MeasureTheory.volume.restrict K)).toReal ≤ C.toReal :=
    ENNReal.toReal_mono hC_ne_top hn
  have hval :
      |F n x.1| ≤
        A * (eLpNorm (F n) 1
          (MeasureTheory.volume.restrict K)).toReal := by
    simpa [K] using hA_bound (F n) (hharm n)
  exact hval.trans (mul_le_mul_of_nonneg_left hnorm_toReal hA_nonneg)

/--
%%handwave
name:
  Locally \(L^1\)-bounded harmonic families have pointwise compact range
statement:
  At each point of an open plane region, the values of a locally
  \(L^1\)-bounded harmonic sequence lie in a compact subset of the real line.
proof:
  The pointwise interior estimate gives an eventual absolute-value bound.
  Add the finitely many exceptional initial values to the closed interval
  containing the tail.
-/
theorem harmonic_locallyL1_bounded_pointwise_compactRange
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hlocal_bound :
      ∀ K : Set ℂ, IsCompact K → K ⊆ V →
        ∃ C : ℝ≥0∞, C < (∞ : ℝ≥0∞) ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            eLpNorm (F n) 1 (MeasureTheory.volume.restrict K) ≤ C) :
    ∀ x : V, ∃ Q : Set ℝ, IsCompact Q ∧
      ∀ n : ℕ, F n x.1 ∈ Q := by
  intro x
  rcases harmonic_locallyL1_bounded_eventually_abs_le_at_point
      hV_open hharm hlocal_bound x with
    ⟨C, _hC, hCevent⟩
  exact exists_compact_range_of_eventually_abs_le hCevent

/--
%%handwave
name:
  Equicontinuity from finite initial data and an equicontinuous tail
statement:
  A sequence of functions is equicontinuous at a point if its finite initial
  segment is equicontinuous there and its tail is equicontinuous there.
proof:
  Given an entourage, intersect the neighbourhoods supplied by the finite
  initial segment and by the tail.  Each index is either before the cutoff or
  in the tail.
-/
theorem equicontinuousAt_nat_of_fin_initial_and_tail
    {X Y : Type} [TopologicalSpace X] [UniformSpace Y]
    {F : ℕ → X → Y} {x : X} (N : ℕ)
    (hinit : EquicontinuousAt
      (fun k : Fin N ↦ F k.1) x)
    (htail : EquicontinuousAt
      (fun n : {n : ℕ // N ≤ n} ↦ F n.1) x) :
    EquicontinuousAt F x := by
  intro U hU
  filter_upwards [hinit U hU, htail U hU] with y hy_init hy_tail n
  by_cases hn : n < N
  · exact hy_init ⟨n, hn⟩
  · exact hy_tail ⟨n, le_of_not_gt hn⟩

/--
%%handwave
name:
  The norm of a real-linear functional on the plane is controlled by two
  coordinate values
statement:
  The operator norm of a real-linear functional on the complex plane is at
  most the sum of the absolute values of its values on the two coordinate
  directions.
proof:
  Decompose a vector into its two real coordinate directions.  The triangle
  inequality and the elementary bounds of each coordinate by the Euclidean
  norm give the estimate.
-/
theorem complexToRealContinuousLinearMap_norm_le_abs_apply_one_add_abs_apply_I
    (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (1 : ℂ)| + |L Complex.I| := by
  refine L.opNorm_le_bound
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
  intro z
  have hz_decomp :
      z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
    exact Complex.ext (by simp) (by simp)
  have hL_decomp :
      L z = z.re * L (1 : ℂ) + z.im * L Complex.I := by
    calc
      L z = L ((z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I) := by
        exact congrArg L hz_decomp
      _ = L ((z.re : ℝ) • (1 : ℂ)) + L ((z.im : ℝ) • Complex.I) := by
        exact L.map_add _ _
      _ = z.re • L (1 : ℂ) + z.im • L Complex.I := by
        exact congrArg₂ (fun a b : ℝ ↦ a + b)
          (ContinuousLinearMap.map_smul L (z.re : ℝ) (1 : ℂ))
          (ContinuousLinearMap.map_smul L (z.im : ℝ) Complex.I)
      _ = z.re * L (1 : ℂ) + z.im * L Complex.I := by
        simp [smul_eq_mul]
  calc
    ‖L z‖ = |L z| := Real.norm_eq_abs (L z)
    _ = |z.re * L (1 : ℂ) + z.im * L Complex.I| := by
      rw [hL_decomp]
    _ ≤ |z.re * L (1 : ℂ)| + |z.im * L Complex.I| :=
      abs_add_le _ _
    _ = |z.re| * |L (1 : ℂ)| + |z.im| * |L Complex.I| := by
      rw [abs_mul, abs_mul]
    _ ≤ ‖z‖ * |L (1 : ℂ)| + ‖z‖ * |L Complex.I| :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          (Complex.abs_re_le_norm z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right
          (Complex.abs_im_le_norm z) (abs_nonneg _))
    _ = (|L (1 : ℂ)| + |L Complex.I|) * ‖z‖ := by
      ring

/--
%%handwave
name:
  Poisson representation on a protected disk
statement:
  If a harmonic function is defined on a region containing a closed disk, then
  every point in the open disk is recovered from the circle average of its
  boundary values against the Poisson kernel.
proof:
  This is the Poisson integral formula for harmonic functions, applied after
  restricting harmonicity to the closed disk.
-/
theorem harmonic_circleAverage_poissonKernel_mul_eq_of_mem_ball
    {V : Set ℂ} {y : V} {ρ : ℝ} {f : ℂ → ℝ}
    (hball : Metric.closedBall y.1 ρ ⊆ V)
    (hf : InnerProductSpace.HarmonicOnNhd f V)
    {w : ℂ} (hw : w ∈ Metric.ball y.1 ρ) :
    Real.circleAverage (fun z : ℂ ↦ poissonKernel y.1 w z * f z) y.1 ρ =
      f w := by
  have hf_closed :
      InnerProductSpace.HarmonicOnNhd f (Metric.closedBall y.1 ρ) :=
    hf.mono hball
  simpa [Pi.smul_apply, smul_eq_mul] using
    (InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
      (c := y.1) (R := ρ) hf_closed hw)

private theorem deriv_poissonKernel_line_quotient_at_zero
    (I V ρ : ℝ) (hρ_pos : 0 < ρ) :
    deriv
        (fun t : ℝ ↦
          (ρ ^ 2 - t ^ 2 * V) /
            (ρ ^ 2 - 2 * t * I + t ^ 2 * V))
        0 =
      2 * I / ρ ^ 2 := by
  have hn :
      HasDerivAt (fun t : ℝ ↦ ρ ^ 2 - t ^ 2 * V) 0 0 := by
    have ht2 : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * 0) 0 := by
      simpa [Pi.pow_apply] using
        ((hasDerivAt_id' (0 : ℝ)).pow 2 :
          HasDerivAt ((fun t : ℝ ↦ t) ^ 2)
            ((2 : ℕ) * (0 : ℝ) ^ (2 - 1) * (1 : ℝ)) 0)
    have ht2V : HasDerivAt (fun t : ℝ ↦ t ^ 2 * V) ((2 * 0) * V) 0 :=
      ht2.mul_const V
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := ρ ^ 2)).sub ht2V
  have hd :
      HasDerivAt
        (fun t : ℝ ↦ ρ ^ 2 - 2 * t * I + t ^ 2 * V)
        (-2 * I + 0) 0 := by
    have hlinear : HasDerivAt (fun t : ℝ ↦ 2 * t * I) (2 * I) 0 := by
      simpa [mul_assoc] using
        ((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).mul_const I
    have ht2 : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * 0) 0 := by
      simpa [Pi.pow_apply] using
        ((hasDerivAt_id' (0 : ℝ)).pow 2 :
          HasDerivAt ((fun t : ℝ ↦ t) ^ 2)
            ((2 : ℕ) * (0 : ℝ) ^ (2 - 1) * (1 : ℝ)) 0)
    have ht2V : HasDerivAt (fun t : ℝ ↦ t ^ 2 * V) ((2 * 0) * V) 0 :=
      ht2.mul_const V
    simpa using
      ((hasDerivAt_const (x := (0 : ℝ)) (c := ρ ^ 2)).sub hlinear).add ht2V
  have hden_ne :
      (fun t : ℝ ↦ ρ ^ 2 - 2 * t * I + t ^ 2 * V) 0 ≠ 0 := by
    simpa using (sq_pos_of_pos hρ_pos).ne'
  have hderiv := hn.div hd hden_ne
  convert hderiv.deriv using 1
  field_simp [hρ_pos.ne']
  ring

/--
%%handwave
name:
  Centre derivative formula for the Poisson kernel
statement:
  On a circle of radius \(\rho\), the directional derivative at the centre, in
  the pole variable, of the Poisson kernel is
  \(2\langle z-c,v\rangle/\rho^2\).
proof:
  Differentiate the explicit Poisson-kernel formula at the centre.  The
  numerator has zero first derivative there, and the derivative of the
  denominator gives the radial linear functional.
-/
theorem poissonKernel_center_directionalFderiv_eq_two_mul_real_inner_div_radius_sq
    (c z v : ℂ) {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hz : z ∈ Metric.sphere c ρ) :
    fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v =
      2 * inner ℝ (z - c) v / ρ ^ 2 := by
  have hdiff : DifferentiableAt ℝ (fun w : ℂ ↦ poissonKernel c w z) c := by
    change DifferentiableAt ℝ
      (fun w : ℂ ↦
        (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) /
          ‖(z - c) - (w - c)‖ ^ 2) c
    have hn : DifferentiableAt ℝ
        (fun w : ℂ ↦ ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) c := by
      have hsub : DifferentiableAt ℝ (fun w : ℂ ↦ w - c) c := by
        fun_prop
      exact (hsub.norm_sq ℝ).const_sub (‖z - c‖ ^ 2)
    have hd : DifferentiableAt ℝ
        (fun w : ℂ ↦ ‖(z - c) - (w - c)‖ ^ 2) c := by
      have hsub : DifferentiableAt ℝ
          (fun w : ℂ ↦ (z - c) - (w - c)) c := by
        fun_prop
      exact hsub.norm_sq ℝ
    have hden_ne :
        (fun w : ℂ ↦ ‖(z - c) - (w - c)‖ ^ 2) c ≠ 0 := by
      have hzc : ‖z - c‖ = ρ := by
        rw [Metric.mem_sphere, dist_eq_norm] at hz
        exact hz
      simpa [hzc, hρ_pos.ne'] using (sq_pos_of_pos hρ_pos).ne'
    change DifferentiableAt ℝ
      (fun w : ℂ ↦
        (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) *
          (‖(z - c) - (w - c)‖ ^ 2)⁻¹) c
    exact hn.mul (hd.inv hden_ne)
  rw [← hdiff.lineDeriv_eq_fderiv]
  unfold lineDeriv
  change
    deriv
        (fun t : ℝ ↦ poissonKernel c (c + t • v) z)
        0 =
      2 * inner ℝ (z - c) v / ρ ^ 2
  have hzc : ‖z - c‖ = ρ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hline :
      (fun t : ℝ ↦ poissonKernel c (c + t • v) z) =
        fun t : ℝ ↦
          (ρ ^ 2 - t ^ 2 * ‖v‖ ^ 2) /
            (ρ ^ 2 - 2 * t * inner ℝ (z - c) v + t ^ 2 * ‖v‖ ^ 2) := by
    funext t
    have hwc : c + t • v - c = t • v := by
      abel
    have htv_norm_sq : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      calc
        ‖t • v‖ ^ 2 = inner ℝ (t • v) (t • v) := by
          exact (real_inner_self_eq_norm_sq (t • v)).symm
        _ = t * inner ℝ (t • v) v := by
          exact real_inner_smul_right (t • v) v t
        _ = t * (t * inner ℝ v v) := by
          have hleft : inner ℝ (t • v) v = t * inner ℝ v v :=
            real_inner_smul_left v v t
          rw [hleft]
        _ = t ^ 2 * ‖v‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
          ring
    have hnum : ‖c + t • v - c‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      rw [hwc, htv_norm_sq]
    have hden :
        ‖(z - c) - ((c + t • v) - c)‖ ^ 2 =
          ρ ^ 2 - 2 * t * inner ℝ (z - c) v + t ^ 2 * ‖v‖ ^ 2 := by
      rw [hwc, norm_sub_sq_real, hzc, htv_norm_sq]
      simp
      ring
    rw [poissonKernel_def, hnum, hden, hzc]
  rw [hline]
  exact
    deriv_poissonKernel_line_quotient_at_zero
      (inner ℝ (z - c) v) (‖v‖ ^ 2) ρ hρ_pos

private theorem poissonKernel_line_eq_quotient
    (c z v : ℂ) {ρ : ℝ} (hz : z ∈ Metric.sphere c ρ) :
    (fun t : ℝ ↦ poissonKernel c (c + t • v) z) =
      fun t : ℝ ↦
        (ρ ^ 2 - t ^ 2 * ‖v‖ ^ 2) /
          (ρ ^ 2 - 2 * t * inner ℝ (z - c) v + t ^ 2 * ‖v‖ ^ 2) := by
  funext t
  have hzc : ‖z - c‖ = ρ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hwc : c + t • v - c = t • v := by
    abel
  have htv_norm_sq : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
    calc
      ‖t • v‖ ^ 2 = inner ℝ (t • v) (t • v) := by
        exact (real_inner_self_eq_norm_sq (t • v)).symm
      _ = t * inner ℝ (t • v) v := by
        exact real_inner_smul_right (t • v) v t
      _ = t * (t * inner ℝ v v) := by
        have hleft : inner ℝ (t • v) v = t * inner ℝ v v :=
          real_inner_smul_left v v t
        rw [hleft]
      _ = t ^ 2 * ‖v‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
        ring
  have hnum : ‖c + t • v - c‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
    rw [hwc, htv_norm_sq]
  have hden :
      ‖(z - c) - ((c + t • v) - c)‖ ^ 2 =
        ρ ^ 2 - 2 * t * inner ℝ (z - c) v + t ^ 2 * ‖v‖ ^ 2 := by
    rw [hwc, norm_sub_sq_real, hzc, htv_norm_sq]
    simp
    ring
  rw [poissonKernel_def, hnum, hden, hzc]

private noncomputable def poissonLineQuot (ρ I V t : ℝ) : ℝ :=
  (ρ ^ 2 - t ^ 2 * V) /
    (ρ ^ 2 - 2 * t * I + t ^ 2 * V)

private noncomputable def poissonLineQuotDeriv (ρ I V t : ℝ) : ℝ :=
  ((-2 * t * V) * (ρ ^ 2 - 2 * t * I + t ^ 2 * V) -
      (ρ ^ 2 - t ^ 2 * V) * (-2 * I + 2 * t * V)) /
    (ρ ^ 2 - 2 * t * I + t ^ 2 * V) ^ 2

private theorem poissonLineQuot_hasDerivAt
    {ρ I V t : ℝ}
    (hden : ρ ^ 2 - 2 * t * I + t ^ 2 * V ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ poissonLineQuot ρ I V s)
      (poissonLineQuotDeriv ρ I V t) t := by
  unfold poissonLineQuot poissonLineQuotDeriv
  have hn :
      HasDerivAt (fun s : ℝ ↦ ρ ^ 2 - s ^ 2 * V) (-2 * t * V) t := by
    have hs2 : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
      simpa [Pi.pow_apply] using
        ((hasDerivAt_id' t).pow 2 :
          HasDerivAt ((fun s : ℝ ↦ s) ^ 2)
            ((2 : ℕ) * t ^ (2 - 1) * (1 : ℝ)) t)
    have hs2V : HasDerivAt (fun s : ℝ ↦ s ^ 2 * V) ((2 * t) * V) t :=
      hs2.mul_const V
    simpa using (hasDerivAt_const (x := t) (c := ρ ^ 2)).sub hs2V
  have hd :
      HasDerivAt
        (fun s : ℝ ↦ ρ ^ 2 - 2 * s * I + s ^ 2 * V)
        (-2 * I + 2 * t * V) t := by
    have hlinear : HasDerivAt (fun s : ℝ ↦ 2 * s * I) (2 * I) t := by
      simpa [mul_assoc] using
        ((hasDerivAt_id' t).const_mul (2 : ℝ)).mul_const I
    have hs2 : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
      simpa [Pi.pow_apply] using
        ((hasDerivAt_id' t).pow 2 :
          HasDerivAt ((fun s : ℝ ↦ s) ^ 2)
            ((2 : ℕ) * t ^ (2 - 1) * (1 : ℝ)) t)
    have hs2V : HasDerivAt (fun s : ℝ ↦ s ^ 2 * V) ((2 * t) * V) t :=
      hs2.mul_const V
    simpa using
      ((hasDerivAt_const (x := t) (c := ρ ^ 2)).sub hlinear).add hs2V
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hn.div hd hden

private theorem poissonLine_den_ne_of_sphere_of_norm_smul_lt
    {c z v : ℂ} {ρ t : ℝ} (hz : z ∈ Metric.sphere c ρ)
    (ht : ‖t • v‖ < ρ) :
    ρ ^ 2 - 2 * t * inner ℝ (z - c) v + t ^ 2 * ‖v‖ ^ 2 ≠ 0 := by
  have hzc : ‖z - c‖ = ρ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have htv_norm_sq : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
    calc
      ‖t • v‖ ^ 2 = inner ℝ (t • v) (t • v) := by
        exact (real_inner_self_eq_norm_sq (t • v)).symm
      _ = t * inner ℝ (t • v) v := by
        exact real_inner_smul_right (t • v) v t
      _ = t * (t * inner ℝ v v) := by
        have hleft : inner ℝ (t • v) v = t * inner ℝ v v :=
          real_inner_smul_left v v t
        rw [hleft]
      _ = t ^ 2 * ‖v‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
        ring
  have hden_norm :
      ρ ^ 2 - 2 * t * inner ℝ (z - c) v + t ^ 2 * ‖v‖ ^ 2 =
        ‖(z - c) - t • v‖ ^ 2 := by
    rw [norm_sub_sq_real, hzc, htv_norm_sq]
    have hinner : inner ℝ (z - c) (t • v) = t * inner ℝ (z - c) v :=
      real_inner_smul_right (z - c) v t
    rw [hinner]
    ring
  have hvec_ne : (z - c) - t • v ≠ 0 := by
    intro hzero
    have hz_eq : z - c = t • v := by
      simpa [sub_eq_zero] using hzero
    have hρ_eq : ρ = ‖t • v‖ := by
      rw [← hzc, hz_eq]
    linarith
  rw [hden_norm]
  exact (sq_pos_of_pos (norm_pos_iff.mpr hvec_ne)).ne'

private theorem hasDerivAt_poissonKernel_line_of_sphere
    (c z v : ℂ) {ρ t : ℝ} (hz : z ∈ Metric.sphere c ρ)
    (ht : ‖t • v‖ < ρ) :
    HasDerivAt (fun s : ℝ ↦ poissonKernel c (c + s • v) z)
      (poissonLineQuotDeriv ρ (inner ℝ (z - c) v) (‖v‖ ^ 2) t) t := by
  rw [poissonKernel_line_eq_quotient c z v hz]
  exact poissonLineQuot_hasDerivAt
    (poissonLine_den_ne_of_sphere_of_norm_smul_lt
      (c := c) (z := z) (v := v) hz ht)

private theorem norm_smul_lt_of_mem_Icc
    {v : ℂ} {ε ρ t : ℝ}
    (hεv : ε * ‖v‖ < ρ) (ht : t ∈ Set.Icc (-ε) ε) :
    ‖t • v‖ < ρ := by
  have habs : |t| ≤ ε := by
    rw [abs_le]
    exact ⟨ht.1, ht.2⟩
  calc
    ‖t • v‖ = |t| * ‖v‖ := by
      simp [Real.norm_eq_abs]
    _ ≤ ε * ‖v‖ :=
      mul_le_mul_of_nonneg_right habs (norm_nonneg v)
    _ < ρ := hεv

private theorem continuousOn_poissonLineQuotDeriv_circle_strip
    (c v : ℂ) {ρ ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hεv : ε * ‖v‖ < ρ) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        poissonLineQuotDeriv ρ
          (inner ℝ (circleMap c ρ p.2 - c) v) (‖v‖ ^ 2) p.1)
      (Set.Icc (-ε) ε ×ˢ Set.uIcc 0 (2 * Real.pi)) := by
  unfold poissonLineQuotDeriv
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop [continuous_circleMap]
  · fun_prop [continuous_circleMap]
  · intro p hp
    have hsphere :
        circleMap c ρ p.2 ∈ Metric.sphere c ρ := by
      have hρ_pos : 0 < ρ := by
        have hmul_nonneg : 0 ≤ ε * ‖v‖ :=
          mul_nonneg hε_nonneg (norm_nonneg v)
        exact lt_of_le_of_lt hmul_nonneg hεv
      exact circleMap_mem_sphere c hρ_pos.le p.2
    have ht_norm : ‖p.1 • v‖ < ρ :=
      norm_smul_lt_of_mem_Icc hεv hp.1
    have hden :=
      poissonLine_den_ne_of_sphere_of_norm_smul_lt
        (c := c) (z := circleMap c ρ p.2)
        (v := v) (ρ := ρ) (t := p.1) hsphere ht_norm
    exact pow_ne_zero 2 hden

private theorem continuousOn_poissonKernel_line_mul_circle
    (c v : ℂ) {ρ t : ℝ} (hρ_pos : 0 < ρ)
    (ht : ‖t • v‖ < ρ) {f : ℂ → ℝ}
    (hf_cont : ContinuousOn f (Metric.sphere c ρ)) :
    ContinuousOn
      (fun θ : ℝ ↦
        poissonKernel c (c + t • v) (circleMap c ρ θ) *
          f (circleMap c ρ θ))
      (Set.uIcc 0 (2 * Real.pi)) := by
  have hsphere : ∀ θ, circleMap c ρ θ ∈ Metric.sphere c ρ :=
    fun θ ↦ circleMap_mem_sphere c hρ_pos.le θ
  have hquot :
      ContinuousOn
        (fun θ : ℝ ↦
          poissonLineQuot ρ (inner ℝ (circleMap c ρ θ - c) v)
            (‖v‖ ^ 2) t)
        (Set.uIcc 0 (2 * Real.pi)) := by
    unfold poissonLineQuot
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop [continuous_circleMap]
    · fun_prop [continuous_circleMap]
    · intro θ _hθ
      exact poissonLine_den_ne_of_sphere_of_norm_smul_lt
        (c := c) (z := circleMap c ρ θ) (v := v)
        (ρ := ρ) (t := t) (hsphere θ) ht
  have hF_eq :
      Set.EqOn
        (fun θ : ℝ ↦
          poissonKernel c (c + t • v) (circleMap c ρ θ) *
            f (circleMap c ρ θ))
        (fun θ : ℝ ↦
          poissonLineQuot ρ (inner ℝ (circleMap c ρ θ - c) v)
            (‖v‖ ^ 2) t *
            f (circleMap c ρ θ))
        (Set.uIcc 0 (2 * Real.pi)) := by
    intro θ _hθ
    have hk := congrFun
      (poissonKernel_line_eq_quotient c (circleMap c ρ θ) v (hsphere θ)) t
    change
      poissonKernel c (c + t • v) (circleMap c ρ θ) *
          f (circleMap c ρ θ) =
        poissonLineQuot ρ (inner ℝ (circleMap c ρ θ - c) v) (‖v‖ ^ 2) t *
          f (circleMap c ρ θ)
    rw [hk]
    rfl
  exact (hquot.mul
    (hf_cont.comp (continuous_circleMap c ρ).continuousOn
      (fun θ _ ↦ hsphere θ))).congr hF_eq

private theorem norm_smul_lt_of_mem_ball
    {v : ℂ} {ε ρ t : ℝ} (hεv : ε * ‖v‖ < ρ)
    (ht : t ∈ Metric.ball (0 : ℝ) ε) :
    ‖t • v‖ < ρ := by
  have ht_abs : |t| < ε := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ht
  have htIcc : t ∈ Set.Icc (-ε) ε := by
    rw [Set.mem_Icc]
    exact ⟨(abs_lt.mp ht_abs).1.le, (abs_lt.mp ht_abs).2.le⟩
  exact norm_smul_lt_of_mem_Icc hεv htIcc

private theorem hasDerivAt_circleAverage_poissonKernel_line
    (c v : ℂ) {ρ : ℝ} (hρ_pos : 0 < ρ) {f : ℂ → ℝ}
    (hf_cont : ContinuousOn f (Metric.sphere c ρ)) :
    HasDerivAt
      (fun t : ℝ ↦
        Real.circleAverage
          (fun z : ℂ ↦ poissonKernel c (c + t • v) z * f z) c ρ)
      (Real.circleAverage
        (fun z : ℂ ↦
          poissonLineQuotDeriv ρ (inner ℝ (z - c) v) (‖v‖ ^ 2) 0 * f z)
        c ρ)
      0 := by
  let ε : ℝ := ρ / (2 * (‖v‖ + 1))
  have hden_pos : 0 < 2 * (‖v‖ + 1) := by
    nlinarith [norm_nonneg v]
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_nonneg : 0 ≤ ε := hε_pos.le
  have hεv : ε * ‖v‖ < ρ := by
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    rw [div_lt_iff₀ hden_pos]
    nlinarith [hρ_pos, norm_nonneg v]
  let F : ℝ → ℝ → ℝ := fun t θ ↦
    poissonKernel c (c + t • v) (circleMap c ρ θ) *
      f (circleMap c ρ θ)
  let F' : ℝ → ℝ → ℝ := fun t θ ↦
    poissonLineQuotDeriv ρ
        (inner ℝ (circleMap c ρ θ - c) v) (‖v‖ ^ 2) t *
      f (circleMap c ρ θ)
  have hprod_cont :
      ContinuousOn
        (fun p : ℝ × ℝ ↦
          poissonLineQuotDeriv ρ
            (inner ℝ (circleMap c ρ p.2 - c) v) (‖v‖ ^ 2) p.1)
        (Set.Icc (-ε) ε ×ˢ Set.uIcc 0 (2 * Real.pi)) :=
    continuousOn_poissonLineQuotDeriv_circle_strip c v hε_nonneg hεv
  have hF_meas :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        AEStronglyMeasurable (F t)
          (MeasureTheory.volume.restrict (Ι 0 (2 * Real.pi))) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε_pos] with t ht
    have ht_norm : ‖t • v‖ < ρ :=
      norm_smul_lt_of_mem_ball hεv ht
    have hcont :
        ContinuousOn (F t) (Set.uIcc 0 (2 * Real.pi)) := by
      simpa [F] using
        continuousOn_poissonKernel_line_mul_circle c v hρ_pos ht_norm hf_cont
    exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (F 0) MeasureTheory.volume 0 (2 * Real.pi) := by
    have ht0 : ‖(0 : ℝ) • v‖ < ρ := by
      simpa using hρ_pos
    have hcont :
        ContinuousOn (F 0) (Set.uIcc 0 (2 * Real.pi)) := by
      simpa [F] using
        continuousOn_poissonKernel_line_mul_circle c v hρ_pos ht0 hf_cont
    exact hcont.intervalIntegrable
  have hF'_cont :
      ContinuousOn (F' 0) (Set.uIcc 0 (2 * Real.pi)) := by
    have hpath :
        ContinuousOn (fun θ : ℝ ↦ ((0 : ℝ), θ))
          (Set.uIcc 0 (2 * Real.pi)) := by
      fun_prop
    have hmaps :
        Set.MapsTo (fun θ : ℝ ↦ ((0 : ℝ), θ))
          (Set.uIcc 0 (2 * Real.pi))
          (Set.Icc (-ε) ε ×ˢ Set.uIcc 0 (2 * Real.pi)) := by
      intro θ hθ
      exact ⟨by simp [hε_nonneg], hθ⟩
    have hmodel :
        ContinuousOn
          (fun θ : ℝ ↦
            poissonLineQuotDeriv ρ
              (inner ℝ (circleMap c ρ θ - c) v) (‖v‖ ^ 2) 0)
          (Set.uIcc 0 (2 * Real.pi)) := by
      simpa using hprod_cont.comp hpath hmaps
    exact hmodel.mul
      (hf_cont.comp (continuous_circleMap c ρ).continuousOn
        (fun θ _ ↦ circleMap_mem_sphere c hρ_pos.le θ))
  have hF'_meas :
      AEStronglyMeasurable (F' 0)
        (MeasureTheory.volume.restrict (Ι 0 (2 * Real.pi))) :=
    (hF'_cont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  rcases (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hprod_cont with
    ⟨C, hC⟩
  let C₀ : ℝ := max 0 C
  let bound : ℝ → ℝ := fun θ ↦ C₀ * |f (circleMap c ρ θ)|
  have hbound_int :
      IntervalIntegrable bound MeasureTheory.volume 0 (2 * Real.pi) := by
    have hbound_cont :
        ContinuousOn bound (Set.uIcc 0 (2 * Real.pi)) := by
      exact continuousOn_const.mul
        ((hf_cont.comp (continuous_circleMap c ρ).continuousOn
          (fun θ _ ↦ circleMap_mem_sphere c hρ_pos.le θ)).abs)
    exact hbound_cont.intervalIntegrable
  have hbound :
      ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Ι 0 (2 * Real.pi) →
        ∀ x ∈ Metric.ball (0 : ℝ) ε, ‖F' x θ‖ ≤ bound θ := by
    refine Filter.Eventually.of_forall ?_
    intro θ hθ x hx
    have hxIcc : x ∈ Set.Icc (-ε) ε := by
      have hx_abs : |x| < ε := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
      rw [Set.mem_Icc]
      exact ⟨(abs_lt.mp hx_abs).1.le, (abs_lt.mp hx_abs).2.le⟩
    have hθu : θ ∈ Set.uIcc 0 (2 * Real.pi) :=
      Set.uIoc_subset_uIcc hθ
    have hmodel_bound :
        ‖poissonLineQuotDeriv ρ
          (inner ℝ (circleMap c ρ θ - c) v) (‖v‖ ^ 2) x‖ ≤ C₀ := by
      exact (hC (x, θ) ⟨hxIcc, hθu⟩).trans (le_max_right 0 C)
    calc
      ‖F' x θ‖ =
          |poissonLineQuotDeriv ρ
            (inner ℝ (circleMap c ρ θ - c) v) (‖v‖ ^ 2) x| *
            |f (circleMap c ρ θ)| := by
            simp [F', Real.norm_eq_abs]
      _ ≤ C₀ * |f (circleMap c ρ θ)| :=
          mul_le_mul_of_nonneg_right hmodel_bound (abs_nonneg _)
      _ = bound θ := rfl
  have hdiff :
      ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Ι 0 (2 * Real.pi) →
        ∀ x ∈ Metric.ball (0 : ℝ) ε,
          HasDerivAt (fun t : ℝ ↦ F t θ) (F' x θ) x := by
    refine Filter.Eventually.of_forall ?_
    intro θ _hθ x hx
    have hz : circleMap c ρ θ ∈ Metric.sphere c ρ :=
      circleMap_mem_sphere c hρ_pos.le θ
    have hx_norm : ‖x • v‖ < ρ :=
      norm_smul_lt_of_mem_ball hεv hx
    have hker :=
      hasDerivAt_poissonKernel_line_of_sphere c (circleMap c ρ θ) v
        hz hx_norm
    simpa [F, F'] using hker.mul_const (f (circleMap c ρ θ))
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := 0) (b := 2 * Real.pi)
      (F := F) (F' := F') (x₀ := (0 : ℝ))
      (s := Metric.ball (0 : ℝ) ε) (bound := bound)
      (Metric.ball_mem_nhds (0 : ℝ) hε_pos)
      hF_meas hF_int hF'_meas hbound hbound_int hdiff
  simpa [Real.circleAverage, F, F'] using
    hparam.2.const_mul ((2 * Real.pi)⁻¹)

/--
%%handwave
name:
  Differentiated Poisson representation at the centre
statement:
  The directional derivative at the centre of a harmonic function is the
  circle average of the boundary values multiplied by the corresponding
  centre derivative of the Poisson kernel.
proof:
  Differentiate the Poisson representation along the line through the centre
  in the given direction.  The parameter derivative passes through the circle
  integral by dominated differentiation, using a compact bound for the
  differentiated Poisson kernel while the pole stays in a smaller disk.
-/
theorem harmonic_center_directionalFderiv_eq_circleAverage_poissonKernel_directionalFderiv_mul
    {V : Set ℂ} {y : V} {ρ : ℝ} {f : ℂ → ℝ} (v : ℂ)
    (hρ_pos : 0 < ρ)
    (hball : Metric.closedBall y.1 ρ ⊆ V)
    (hf : InnerProductSpace.HarmonicOnNhd f V) :
    fderiv ℝ f y.1 v =
      Real.circleAverage
        (fun z : ℂ ↦
          fderiv ℝ (fun w : ℂ ↦ poissonKernel y.1 w z) y.1 v * f z)
        y.1 ρ := by
  have hf_cont_sphere : ContinuousOn f (Metric.sphere y.1 ρ) :=
    hf.continuousOn.mono (by
      intro z hz
      exact hball (Metric.sphere_subset_closedBall hz))
  have hcircle :=
    hasDerivAt_circleAverage_poissonKernel_line
      (c := y.1) (v := v) hρ_pos hf_cont_sphere
  have hyV : y.1 ∈ V :=
    hball (Metric.mem_closedBall_self hρ_pos.le)
  have hf_diff : DifferentiableAt ℝ f y.1 :=
    (hf y.1 hyV).1.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hline_map : HasDerivAt (fun t : ℝ ↦ y.1 + t • v) v 0 := by
    have hsmul : HasDerivAt (fun t : ℝ ↦ t • v) v 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v)
    simpa using hsmul.const_add y.1
  have hf_line :
      HasDerivAt (fun t : ℝ ↦ f (y.1 + t • v)) (fderiv ℝ f y.1 v) 0 := by
    have hf_diff' :
        HasFDerivAt f (fderiv ℝ f y.1) (y.1 + (0 : ℝ) • v) := by
      simpa using hf_diff.hasFDerivAt
    have hcomp := hf_diff'.comp_hasDerivAt 0 hline_map
    simpa [Function.comp_def] using hcomp
  let circleLine : ℝ → ℝ := fun t ↦
    Real.circleAverage
      (fun z : ℂ ↦ poissonKernel y.1 (y.1 + t • v) z * f z) y.1 ρ
  have hrep_eventually :
      circleLine =ᶠ[𝓝 (0 : ℝ)] fun t : ℝ ↦ f (y.1 + t • v) := by
    by_cases hv : ‖v‖ = 0
    · filter_upwards [Filter.Eventually.of_forall (fun _ : ℝ ↦ True.intro)] with t _ht
      have htv : t • v = 0 := by
        simp [norm_eq_zero.mp hv]
      have hw : y.1 + t • v ∈ Metric.ball y.1 ρ := by
        simpa [htv, Metric.mem_ball, dist_self] using hρ_pos
      simpa [circleLine] using
        harmonic_circleAverage_poissonKernel_mul_eq_of_mem_ball
          (y := y) hball hf hw
    · let ε : ℝ := ρ / (‖v‖ + 1)
      have hden_pos : 0 < ‖v‖ + 1 := by
        nlinarith [norm_nonneg v]
      have hε_pos : 0 < ε := by
        dsimp [ε]
        positivity
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε_pos] with t ht
      have ht_abs : |t| < ε := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ht
      have htv_lt : ‖t • v‖ < ρ := by
        have hv_pos : 0 < ‖v‖ :=
          lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
        calc
          ‖t • v‖ = |t| * ‖v‖ := by
            simp [Real.norm_eq_abs]
          _ < ε * ‖v‖ :=
            mul_lt_mul_of_pos_right ht_abs hv_pos
          _ < ρ := by
            dsimp [ε]
            rw [div_mul_eq_mul_div]
            rw [div_lt_iff₀ hden_pos]
            nlinarith [hρ_pos, norm_nonneg v]
      have hw : y.1 + t • v ∈ Metric.ball y.1 ρ := by
        simpa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using htv_lt
      simpa [circleLine] using
        harmonic_circleAverage_poissonKernel_mul_eq_of_mem_ball
          (y := y) hball hf hw
  have hcircle_line :
      HasDerivAt circleLine
        (Real.circleAverage
          (fun z : ℂ ↦
            poissonLineQuotDeriv ρ (inner ℝ (z - y.1) v) (‖v‖ ^ 2) 0 * f z)
          y.1 ρ) 0 := by
    simpa [circleLine] using hcircle
  have hmodel_eq :
      Real.circleAverage
          (fun z : ℂ ↦
            poissonLineQuotDeriv ρ (inner ℝ (z - y.1) v) (‖v‖ ^ 2) 0 * f z)
          y.1 ρ =
        Real.circleAverage
          (fun z : ℂ ↦
            fderiv ℝ (fun w : ℂ ↦ poissonKernel y.1 w z) y.1 v * f z)
          y.1 ρ := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hzρ : z ∈ Metric.sphere y.1 ρ := by
      simpa [abs_of_pos hρ_pos] using hz
    change
      poissonLineQuotDeriv ρ (inner ℝ (z - y.1) v) (‖v‖ ^ 2) 0 * f z =
        fderiv ℝ (fun w : ℂ ↦ poissonKernel y.1 w z) y.1 v * f z
    rw [poissonKernel_center_directionalFderiv_eq_two_mul_real_inner_div_radius_sq
      y.1 z v hρ_pos hzρ]
    unfold poissonLineQuotDeriv
    field_simp [hρ_pos.ne']
    ring
  have hline_from_circle :
      HasDerivAt (fun t : ℝ ↦ f (y.1 + t • v))
        (Real.circleAverage
          (fun z : ℂ ↦
            poissonLineQuotDeriv ρ (inner ℝ (z - y.1) v) (‖v‖ ^ 2) 0 * f z)
          y.1 ρ) 0 :=
    hcircle_line.congr_of_eventuallyEq hrep_eventually.symm
  exact (hf_line.unique hline_from_circle).trans hmodel_eq

/--
%%handwave
name:
  Poisson-kernel derivative domination under a circle bound
statement:
  If the centre derivative of the Poisson kernel is bounded in absolute value
  by \(B\) on a circle, then the circle average of the differentiated Poisson
  integrand is bounded by \(B\) times the circle average of the absolute value
  of the boundary data.
proof:
  Take the absolute value of the circle average, dominate it by the circle
  average of the absolute value, and use positivity of circle averaging with
  the assumed pointwise kernel bound.
-/
theorem circleAverage_poissonKernel_directionalFderiv_mul_abs_le_const_mul_circleAverage_abs
    {c : ℂ} {ρ B : ℝ} {f : ℂ → ℝ} (v : ℂ)
    (_hB_nonneg : 0 ≤ B) (hρ_pos : 0 < ρ)
    (hf_cont : ContinuousOn f (Metric.sphere c ρ))
    (hkernel :
      ∀ z ∈ Metric.sphere c ρ,
        |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v| ≤ B) :
    |Real.circleAverage
        (fun z : ℂ ↦
          fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v * f z)
        c ρ| ≤
      B * Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ := by
  have habs_int : CircleIntegrable (fun z : ℂ ↦ |f z|) c ρ :=
    hf_cont.abs.circleIntegrable hρ_pos.le
  have hmodel_cont :
      ContinuousOn
        (fun z : ℂ ↦ |(2 * inner ℝ (z - c) v / ρ ^ 2) * f z|)
        (Metric.sphere c ρ) := by
    fun_prop
  have hmodel_int :
      CircleIntegrable
        (fun z : ℂ ↦ |(2 * inner ℝ (z - c) v / ρ ^ 2) * f z|)
        c ρ :=
    hmodel_cont.circleIntegrable hρ_pos.le
  have hprod_abs_eq :
      Set.EqOn
        (fun z : ℂ ↦
          |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v * f z|)
        (fun z : ℂ ↦ |(2 * inner ℝ (z - c) v / ρ ^ 2) * f z|)
        (Metric.sphere c |ρ|) := by
    intro z hz
    have hzρ : z ∈ Metric.sphere c ρ := by
      simpa [abs_of_pos hρ_pos] using hz
    change
      |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v * f z| =
        |(2 * inner ℝ (z - c) v / ρ ^ 2) * f z|
    rw [poissonKernel_center_directionalFderiv_eq_two_mul_real_inner_div_radius_sq
      c z v hρ_pos hzρ]
  have hprod_abs_int :
      CircleIntegrable
        (fun z : ℂ ↦
          |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v * f z|)
        c ρ :=
    (circleIntegrable_congr hprod_abs_eq).2 hmodel_int
  have hBabs_int :
      CircleIntegrable (fun z : ℂ ↦ B * |f z|) c ρ := by
    simpa [smul_eq_mul] using habs_int.const_fun_smul (a := B)
  have hpoint :
      ∀ z ∈ Metric.sphere c |ρ|,
        |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v * f z| ≤
          B * |f z| := by
    intro z hz
    have hzρ : z ∈ Metric.sphere c ρ := by
      simpa [abs_of_pos hρ_pos] using hz
    calc
      |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v * f z|
          =
          |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v| * |f z| := by
            rw [abs_mul]
      _ ≤ B * |f z| :=
          mul_le_mul_of_nonneg_right (hkernel z hzρ) (abs_nonneg _)
  calc
    |Real.circleAverage
        (fun z : ℂ ↦
          fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v * f z)
        c ρ| ≤
      Real.circleAverage
        (fun z : ℂ ↦
          |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v * f z|)
        c ρ :=
        Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun z : ℂ ↦ B * |f z|) c ρ :=
        Real.circleAverage_mono hprod_abs_int hBabs_int hpoint
    _ = B * Real.circleAverage (fun z : ℂ ↦ |f z|) c ρ := by
        simpa [smul_eq_mul] using
          (Real.circleAverage_fun_smul (a := B)
            (f := fun z : ℂ ↦ |f z|) (c := c) (R := ρ))

/--
%%handwave
name:
  Poisson-kernel derivative domination
statement:
  If the directional derivative in the pole variable of the Poisson kernel is
  bounded by a constant on a circle, then the directional derivative at the
  centre of a harmonic function is bounded by that constant times the circle
  average of the absolute value of the function.
proof:
  Differentiate the Poisson representation at the centre, take absolute
  values, and use positivity of circle averaging together with the assumed
  kernel bound.
-/
theorem harmonic_center_directionalFderiv_le_const_mul_circleAverage_abs_of_poissonKernel_bound
    {V : Set ℂ} {y : V} {ρ B : ℝ} {f : ℂ → ℝ} (v : ℂ)
    (hB_nonneg : 0 ≤ B) (hρ_pos : 0 < ρ)
    (hball : Metric.closedBall y.1 ρ ⊆ V)
    (hf : InnerProductSpace.HarmonicOnNhd f V)
    (hkernel :
      ∀ z ∈ Metric.sphere y.1 ρ,
        |fderiv ℝ (fun w : ℂ ↦ poissonKernel y.1 w z) y.1 v| ≤ B) :
    |fderiv ℝ f y.1 v| ≤
      B * Real.circleAverage (fun z : ℂ ↦ |f z|) y.1 ρ := by
  rw [
    harmonic_center_directionalFderiv_eq_circleAverage_poissonKernel_directionalFderiv_mul
      (v := v) hρ_pos hball hf]
  have hf_cont_sphere : ContinuousOn f (Metric.sphere y.1 ρ) :=
    hf.continuousOn.mono (by
      intro z hz
      exact hball (Metric.sphere_subset_closedBall hz))
  exact
    circleAverage_poissonKernel_directionalFderiv_mul_abs_le_const_mul_circleAverage_abs
      (v := v) hB_nonneg hρ_pos hf_cont_sphere hkernel

/--
%%handwave
name:
  Centre derivative of the Poisson kernel
statement:
  On a circle of radius \(\rho\), the directional derivative at the centre, in
  the pole variable, of the Poisson kernel is bounded by
  \(2\lVert v\rVert/\rho\).
proof:
  Differentiate the explicit Poisson-kernel formula at the centre.  The
  derivative of the numerator vanishes at the centre, while differentiating
  the denominator contributes the radial linear functional, whose absolute
  value is bounded by \(2\lVert v\rVert\rho\).
-/
theorem poissonKernel_center_directionalFderiv_abs_le_two_mul_norm_div_radius
    (c z v : ℂ) {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hz : z ∈ Metric.sphere c ρ) :
    |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v| ≤
      2 * ‖v‖ / ρ := by
  have hnorm : ‖z - c‖ = ρ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hinner_le :
      |inner ℝ (z - c) v| ≤ ρ * ‖v‖ := by
    simpa [hnorm] using abs_real_inner_le_norm (z - c) v
  have hden_pos : 0 < ρ ^ 2 :=
    sq_pos_of_pos hρ_pos
  rw [poissonKernel_center_directionalFderiv_eq_two_mul_real_inner_div_radius_sq
    c z v hρ_pos hz]
  calc
    |2 * inner ℝ (z - c) v / ρ ^ 2|
        = (2 / ρ ^ 2) * |inner ℝ (z - c) v| := by
            rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
              abs_of_pos hden_pos]
            ring
    _ ≤ (2 / ρ ^ 2) * (ρ * ‖v‖) :=
      mul_le_mul_of_nonneg_left hinner_le
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hden_pos.le)
    _ = 2 * ‖v‖ / ρ := by
      field_simp [hρ_pos.ne']

/--
%%handwave
name:
  Uniform bound for centre derivatives of the Poisson kernel
statement:
  For a fixed direction and a protected disk radius, the directional
  derivative at the centre, in the pole variable, of the Poisson kernel is
  uniformly bounded on all concentric circles whose radii lie in the outer
  half of the disk.
proof:
  Use the explicit Poisson-kernel formula.  On the outer half-annulus the
  boundary radius is bounded below and above by fixed multiples of the
  protected radius, so the denominator in the differentiated kernel has a
  uniform positive lower bound and the numerator is uniformly controlled by
  the fixed direction and the protected radius.
-/
theorem exists_poissonKernel_center_directionalFderiv_abs_le_const_on_annulus
    (v : ℂ) {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (c z : ℂ) (ρ : ℝ),
        δ / 2 < ρ →
          ρ < δ →
            z ∈ Metric.sphere c ρ →
              |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v| ≤ B := by
  refine ⟨4 * ‖v‖ / δ, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg v)) hδ_pos.le
  intro c z ρ hρ_half hρ_lt hz
  have hρ_pos : 0 < ρ :=
    (half_pos hδ_pos).trans hρ_half
  have htwo_div_le_four_div : 2 / ρ ≤ 4 / δ := by
    rw [div_le_div_iff₀ hρ_pos hδ_pos]
    nlinarith [hρ_half]
  calc
    |fderiv ℝ (fun w : ℂ ↦ poissonKernel c w z) c v| ≤
        2 * ‖v‖ / ρ :=
      poissonKernel_center_directionalFderiv_abs_le_two_mul_norm_div_radius
        c z v hρ_pos hz
    _ = (2 / ρ) * ‖v‖ := by ring
    _ ≤ (4 / δ) * ‖v‖ :=
      mul_le_mul_of_nonneg_right htwo_div_le_four_div (norm_nonneg v)
    _ = 4 * ‖v‖ / δ := by ring

/--
%%handwave
name:
  Centered directional derivatives are controlled by outer circle averages
statement:
  At the centre of a protected disk, each fixed directional derivative of a
  harmonic function is bounded by a geometric constant times the circle
  average of the absolute value on any concentric circle whose radius lies in
  the outer half of the disk.
proof:
  This is the Poisson-kernel derivative estimate, or equivalently the Cauchy
  estimate for a local harmonic conjugate, with the radius bounded below by
  half the protected disk radius.
-/
theorem exists_harmonic_center_directionalFderiv_circleAverage_abs_constant_on_annulus
    (v : ℂ) {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {V : Set ℂ} (y : V),
        Metric.closedBall y.1 δ ⊆ V →
          ∀ f : ℂ → ℝ,
            InnerProductSpace.HarmonicOnNhd f V →
              ∀ ρ : ℝ,
                δ / 2 < ρ →
                  ρ < δ →
                    |fderiv ℝ f y.1 v| ≤
                      B * Real.circleAverage (fun z : ℂ ↦ |f z|) y.1 ρ := by
  rcases exists_poissonKernel_center_directionalFderiv_abs_le_const_on_annulus
      (v := v) hδ_pos with
    ⟨B, hB_nonneg, hB_bound⟩
  refine ⟨B, hB_nonneg, ?_⟩
  intro V y hball f hf ρ hρ_half hρ_lt
  have hρ_pos : 0 < ρ :=
    (half_pos hδ_pos).trans hρ_half
  have hballρ : Metric.closedBall y.1 ρ ⊆ V := by
    intro z hz
    exact hball (Metric.closedBall_subset_closedBall hρ_lt.le hz)
  exact
    harmonic_center_directionalFderiv_le_const_mul_circleAverage_abs_of_poissonKernel_bound
      (v := v) (B := B) hB_nonneg hρ_pos hballρ hf
      (fun z hz ↦ hB_bound y.1 z ρ hρ_half hρ_lt hz)

/--
%%handwave
name:
  Centered interior directional derivative estimate
statement:
  At the centre of a protected closed disk, each fixed directional derivative
  of a harmonic function is bounded by a geometric constant times the
  integral of the absolute value on that disk.
proof:
  This is the local analytic estimate obtained by differentiating the
  Poisson representation, or equivalently by Cauchy estimates for a local
  harmonic conjugate.
-/
theorem exists_harmonic_center_directionalFderiv_integral_abs_constant
    (v : ℂ) {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ {V : Set ℂ} (y : V),
        Metric.closedBall y.1 δ ⊆ V →
          ∀ f : ℂ → ℝ,
            InnerProductSpace.HarmonicOnNhd f V →
              |fderiv ℝ f y.1 v| ≤
                G * ∫ z in Metric.closedBall y.1 δ, |f z| ∂MeasureTheory.volume := by
  rcases exists_harmonic_center_directionalFderiv_circleAverage_abs_constant_on_annulus
      (v := v) hδ_pos with
    ⟨B, hB_nonneg, hB_bound⟩
  rcases exists_radius_circleAverage_abs_le_const_mul_integral_abs_annulus_uniform_center
      (r := δ) hδ_pos with
    ⟨A, hA_nonneg, hA_bound⟩
  refine ⟨B * A, mul_nonneg hB_nonneg hA_nonneg, ?_⟩
  intro V y hball f hf
  rcases hA_bound y.1 f (hf.continuousOn.mono hball) with
    ⟨ρ, hρ_half, hρ_lt, hcircle_y⟩
  have hderiv_circle :
      |fderiv ℝ f y.1 v| ≤
        B * Real.circleAverage (fun z : ℂ ↦ |f z|) y.1 ρ :=
    hB_bound y hball f hf ρ hρ_half hρ_lt
  have hclosed_int :
      IntegrableOn (fun z : ℂ ↦ |f z|)
        (Metric.closedBall y.1 δ) MeasureTheory.volume := by
    simpa [IntegrableOn] using
      harmonic_abs_integrable_closedBall (x := y) hball hf
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Metric.closedBall y.1 δ)]
        (fun z : ℂ ↦ |f z|) :=
    Filter.Eventually.of_forall fun z ↦ abs_nonneg (f z)
  have hannulus_subset :
      (Metric.closedBall y.1 δ \ Metric.ball y.1 (δ / 2)) ⊆
        Metric.closedBall y.1 δ :=
    fun z hz ↦ hz.1
  have hannulus_le_closed :
      ∫ z in (Metric.closedBall y.1 δ \ Metric.ball y.1 (δ / 2)),
          |f z| ∂MeasureTheory.volume ≤
        ∫ z in Metric.closedBall y.1 δ, |f z| ∂MeasureTheory.volume :=
    setIntegral_mono_set hclosed_int hnonneg
      (Filter.Eventually.of_forall hannulus_subset)
  calc
    |fderiv ℝ f y.1 v|
        ≤ B * Real.circleAverage (fun z : ℂ ↦ |f z|) y.1 ρ :=
          hderiv_circle
    _ ≤ B *
        (A *
          ∫ z in
              (Metric.closedBall y.1 δ \ Metric.ball y.1 (δ / 2)),
            |f z| ∂MeasureTheory.volume) := by
          exact mul_le_mul_of_nonneg_left hcircle_y hB_nonneg
    _ = (B * A) *
        ∫ z in
            (Metric.closedBall y.1 δ \ Metric.ball y.1 (δ / 2)),
          |f z| ∂MeasureTheory.volume := by ring
    _ ≤ (B * A) *
        ∫ z in Metric.closedBall y.1 δ, |f z| ∂MeasureTheory.volume := by
          exact mul_le_mul_of_nonneg_left hannulus_le_closed
            (mul_nonneg hB_nonneg hA_nonneg)

/--
%%handwave
name:
  Interior directional derivative estimate from a closed-disk \(L^1\)-integral
statement:
  On a smaller closed disk inside a protected closed disk, each fixed
  directional derivative of a harmonic function is bounded by a geometric
  constant times the integral of the absolute value on the protected disk.
proof:
  This is the scalar directional form of the interior derivative estimate.
  It follows from differentiating the Poisson or mean-value representation
  and bounding the resulting kernel on the smaller disk.
-/
theorem exists_harmonic_directionalFderiv_closedBall_integral_abs_constant
    {V : Set ℂ} {x : V} {r ρ : ℝ} (v : ℂ)
    (_hρ_pos : 0 < ρ) (hρ_lt_r : ρ < r)
    (hball : Metric.closedBall x.1 r ⊆ V) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ f : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd f V →
          ∀ y : ℂ,
            y ∈ Metric.closedBall x.1 ρ →
              |fderiv ℝ f y v| ≤
                G * ∫ z in Metric.closedBall x.1 r, |f z| ∂MeasureTheory.volume := by
  let δ : ℝ := (r - ρ) / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have hδ_add_ρ_le : δ + ρ ≤ r := by
    dsimp [δ]
    linarith
  rcases exists_harmonic_center_directionalFderiv_integral_abs_constant
      (δ := δ) (v := v) hδ_pos with
    ⟨G, hG_nonneg, hG_bound⟩
  refine ⟨G, hG_nonneg, ?_⟩
  intro f hf y hy
  have hyV : y ∈ V :=
    hball (Metric.closedBall_subset_closedBall hρ_lt_r.le hy)
  let yV : V := ⟨y, hyV⟩
  have hsmall_big :
      Metric.closedBall y δ ⊆ Metric.closedBall x.1 r := by
    refine Metric.closedBall_subset_closedBall' ?_
    have hdist_yx : dist y x.1 ≤ ρ := by
      simpa [Metric.mem_closedBall] using hy
    calc
      δ + dist y x.1 ≤ δ + ρ := by gcongr
      _ ≤ r := hδ_add_ρ_le
  have hsmall_V : Metric.closedBall yV.1 δ ⊆ V := by
    simpa [yV] using hsmall_big.trans hball
  have hcenter :
      |fderiv ℝ f y v| ≤
        G * ∫ z in Metric.closedBall y δ, |f z| ∂MeasureTheory.volume := by
    simpa [yV] using hG_bound yV hsmall_V f hf
  have hbig_int :
      IntegrableOn (fun z : ℂ ↦ |f z|)
        (Metric.closedBall x.1 r) MeasureTheory.volume := by
    simpa [IntegrableOn] using
      harmonic_abs_integrable_closedBall (x := x) hball hf
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Metric.closedBall x.1 r)]
        (fun z : ℂ ↦ |f z|) :=
    Filter.Eventually.of_forall fun z ↦ abs_nonneg (f z)
  have hsmall_le_big :
      ∫ z in Metric.closedBall y δ, |f z| ∂MeasureTheory.volume ≤
        ∫ z in Metric.closedBall x.1 r, |f z| ∂MeasureTheory.volume :=
    setIntegral_mono_set hbig_int hnonneg
      (Filter.Eventually.of_forall hsmall_big)
  exact hcenter.trans (mul_le_mul_of_nonneg_left hsmall_le_big hG_nonneg)

/--
%%handwave
name:
  Interior derivative estimate from a closed-disk \(L^1\)-integral
statement:
  On a smaller closed disk inside a protected closed disk, the norm of the
  derivative of a harmonic function is bounded by a geometric constant times
  the integral of the absolute value on the protected disk.
proof:
  This is the derivative form of the interior harmonic estimate.  Poisson
  kernel derivative bounds, or equivalently Cauchy estimates for a local
  harmonic conjugate, control the gradient on the smaller disk by the
  \(L^1\)-integral on the larger disk.
-/
theorem exists_harmonic_fderiv_closedBall_integral_abs_constant
    {V : Set ℂ} {x : V} {r ρ : ℝ}
    (hρ_pos : 0 < ρ) (hρ_lt_r : ρ < r)
    (hball : Metric.closedBall x.1 r ⊆ V) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ f : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd f V →
          ∀ y : ℂ,
            y ∈ Metric.closedBall x.1 ρ →
              ‖fderiv ℝ f y‖ ≤
                G * ∫ z in Metric.closedBall x.1 r, |f z| ∂MeasureTheory.volume := by
  rcases exists_harmonic_directionalFderiv_closedBall_integral_abs_constant
      (x := x) (v := (1 : ℂ)) hρ_pos hρ_lt_r hball with
    ⟨G₁, hG₁_nonneg, hG₁_bound⟩
  rcases exists_harmonic_directionalFderiv_closedBall_integral_abs_constant
      (x := x) (v := Complex.I) hρ_pos hρ_lt_r hball with
    ⟨G₂, hG₂_nonneg, hG₂_bound⟩
  refine ⟨G₁ + G₂, add_nonneg hG₁_nonneg hG₂_nonneg, ?_⟩
  intro f hf y hy
  let I : ℝ := ∫ z in Metric.closedBall x.1 r, |f z| ∂MeasureTheory.volume
  have hdir₁ :
      |fderiv ℝ f y (1 : ℂ)| ≤ G₁ * I := by
    simpa [I] using hG₁_bound f hf y hy
  have hdir₂ :
      |fderiv ℝ f y Complex.I| ≤ G₂ * I := by
    simpa [I] using hG₂_bound f hf y hy
  calc
    ‖fderiv ℝ f y‖
        ≤ |fderiv ℝ f y (1 : ℂ)| + |fderiv ℝ f y Complex.I| :=
      complexToRealContinuousLinearMap_norm_le_abs_apply_one_add_abs_apply_I
        (fderiv ℝ f y)
    _ ≤ G₁ * I + G₂ * I := add_le_add hdir₁ hdir₂
    _ = (G₁ + G₂) * I := by ring

/--
%%handwave
name:
  Integral form of the interior Lipschitz estimate
statement:
  On a smaller closed ball inside a protected closed ball, a harmonic
  function has a Lipschitz constant bounded by a geometric constant times the
  integral of its absolute value on the protected ball.
proof:
  Apply the interior derivative estimate on the smaller closed ball, and
  integrate the derivative bound along the segment between two points using
  the convex-set mean-value theorem.
-/
theorem exists_harmonic_lipschitz_closedBall_integral_abs_constant
    {V : Set ℂ} {x : V} {r ρ : ℝ}
    (hρ_pos : 0 < ρ) (hρ_lt_r : ρ < r)
    (hball : Metric.closedBall x.1 r ⊆ V) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ f : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd f V →
          ∀ y z : V,
            y.1 ∈ Metric.closedBall x.1 ρ →
              z.1 ∈ Metric.closedBall x.1 ρ →
                |f y.1 - f z.1| ≤
                  L *
                    (∫ w in Metric.closedBall x.1 r, |f w| ∂MeasureTheory.volume) *
                    dist y z := by
  rcases exists_harmonic_fderiv_closedBall_integral_abs_constant
      (x := x) hρ_pos hρ_lt_r hball with
    ⟨G, hG_nonneg, hG_bound⟩
  refine ⟨G, hG_nonneg, ?_⟩
  intro f hf y z hyρ hzρ
  let S : Set ℂ := Metric.closedBall x.1 ρ
  let I : ℝ := ∫ w in Metric.closedBall x.1 r, |f w| ∂MeasureTheory.volume
  let C : ℝ := G * I
  have hS_subset_V : S ⊆ V := by
    intro w hw
    exact hball (Metric.closedBall_subset_closedBall hρ_lt_r.le hw)
  have hdiff : ∀ w ∈ S, DifferentiableAt ℝ f w := by
    intro w hw
    exact
      ((hf w (hS_subset_V hw)).1.differentiableAt
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
  have hderiv_bound : ∀ w ∈ S, ‖fderiv ℝ f w‖ ≤ C := by
    intro w hw
    simpa [C, I, S] using hG_bound f hf w hw
  have hconvex : Convex ℝ S := by
    simpa [S] using
      (convex_closedBall x.1 ρ :
        Convex ℝ (Metric.closedBall x.1 ρ))
  have hmvt :
      ‖f y.1 - f z.1‖ ≤ C * ‖y.1 - z.1‖ := by
    simpa [S] using
      hconvex.norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ) (f := f) hdiff hderiv_bound
        (by simpa [S] using hzρ) (by simpa [S] using hyρ)
  simpa [C, I, Real.norm_eq_abs, dist_eq_norm, Subtype.dist_eq] using hmvt

/--
%%handwave
name:
  Interior Lipschitz estimate from a closed-ball \(L^1\)-norm
statement:
  On a smaller closed ball inside a protected closed ball, a harmonic
  function has a Lipschitz constant bounded by a geometric constant times its
  \(L^1\)-norm on the protected ball.
proof:
  Apply the integral form of the Lipschitz estimate, then identify the
  closed-disk \(L^1\)-seminorm with the ordinary integral of the absolute
  value.
-/
theorem exists_harmonic_lipschitz_closedBall_l1_constant
    {V : Set ℂ} {x : V} {r ρ : ℝ}
    (hρ_pos : 0 < ρ) (hρ_lt_r : ρ < r)
    (hball : Metric.closedBall x.1 r ⊆ V) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ f : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd f V →
          ∀ y z : V,
            y.1 ∈ Metric.closedBall x.1 ρ →
              z.1 ∈ Metric.closedBall x.1 ρ →
                |f y.1 - f z.1| ≤
                  L *
                    (eLpNorm f 1
                      (MeasureTheory.volume.restrict
                        (Metric.closedBall x.1 r))).toReal *
                    dist y z := by
  rcases exists_harmonic_lipschitz_closedBall_integral_abs_constant
      (x := x) hρ_pos hρ_lt_r hball with
    ⟨L, hL_nonneg, hL_bound⟩
  refine ⟨L, hL_nonneg, ?_⟩
  intro f hf y z hyρ hzρ
  rw [harmonic_eLpNorm_one_closedBall_toReal_eq_integral_abs
    (x := x) hball hf]
  exact hL_bound f hf y z hyρ hzρ

/--
%%handwave
name:
  Uniform closed-ball \(L^1\)-bounds give local harmonic equicontinuity
statement:
  If a family of harmonic functions has a common \(L^1\)-bound on a closed
  ball compactly contained in the region, then the family is equicontinuous at
  the centre of the ball.
proof:
  This is the local interior harmonic estimate: Poisson-kernel or Cauchy
  estimates bound oscillation near the centre by the common \(L^1\)-bound on
  the protected closed ball.
-/
theorem harmonic_closedBall_l1_bounded_equicontinuousAt
    {V : Set ℂ} {x : V} {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.closedBall x.1 r ⊆ V)
    {ι : Type} {F : ι → ℂ → ℝ}
    (hharm : ∀ i : ι, InnerProductSpace.HarmonicOnNhd (F i) V)
    {C : ℝ≥0∞} (hC_lt_top : C < (∞ : ℝ≥0∞))
    (hbound :
      ∀ i : ι,
        eLpNorm (F i) 1
          (MeasureTheory.volume.restrict (Metric.closedBall x.1 r)) ≤ C) :
    EquicontinuousAt (fun i : ι ↦ fun y : V ↦ F i y.1) x := by
  let ρ : ℝ := r / 2
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_r : ρ < r := by
    dsimp [ρ]
    linarith
  rcases exists_harmonic_lipschitz_closedBall_l1_constant
      (x := x) hρ_pos hρ_lt_r hball with
    ⟨L, hL_nonneg, hL_bound⟩
  intro U hU
  rcases Metric.mem_uniformity_dist.mp hU with ⟨ε, hε_pos, hεU⟩
  let B : ℝ := L * C.toReal
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hL_nonneg ENNReal.toReal_nonneg
  let δ : ℝ := min ρ (ε / (B + 1))
  have hB1_pos : 0 < B + 1 := by linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hρ_pos (div_pos hε_pos hB1_pos)
  have hδ_le_ρ : δ ≤ ρ := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_eps : δ ≤ ε / (B + 1) := by
    dsimp [δ]
    exact min_le_right _ _
  have hBδ_le : B * δ ≤ B * (ε / (B + 1)) :=
    mul_le_mul_of_nonneg_left hδ_le_eps hB_nonneg
  have hB_eps_lt : B * (ε / (B + 1)) < ε := by
    have hcalc : B * (ε / (B + 1)) = ε - ε / (B + 1) := by
      field_simp [hB1_pos.ne']
      ring
    have hfrac_pos : 0 < ε / (B + 1) := div_pos hε_pos hB1_pos
    rw [hcalc]
    linarith
  have hxρ : x.1 ∈ Metric.closedBall x.1 ρ := by
    simp [Metric.mem_closedBall, hρ_pos.le]
  filter_upwards [Metric.ball_mem_nhds x hδ_pos] with y hy i
  have hdist_sub : dist x y < δ := by
    simpa [Metric.mem_ball, dist_comm] using hy
  have hdist_val_le : dist x.1 y.1 ≤ ρ := by
    have hdist_sub_le : dist x y ≤ δ := le_of_lt hdist_sub
    have hdist_val_sub : dist x.1 y.1 ≤ δ := by
      simpa using hdist_sub_le
    exact hdist_val_sub.trans hδ_le_ρ
  have hyρ : y.1 ∈ Metric.closedBall x.1 ρ := by
    simpa [Metric.mem_closedBall, dist_comm] using hdist_val_le
  have hC_ne_top : C ≠ (∞ : ℝ≥0∞) := ne_of_lt hC_lt_top
  have hnorm_toReal :
      (eLpNorm (F i) 1
        (MeasureTheory.volume.restrict (Metric.closedBall x.1 r))).toReal ≤
        C.toReal :=
    ENNReal.toReal_mono hC_ne_top (hbound i)
  have hosc :
      |F i x.1 - F i y.1| ≤
        L *
          (eLpNorm (F i) 1
            (MeasureTheory.volume.restrict
              (Metric.closedBall x.1 r))).toReal *
          dist x y :=
    hL_bound (F i) (hharm i) x y hxρ hyρ
  have hosc_C :
      |F i x.1 - F i y.1| ≤ B * dist x y := by
    refine hosc.trans ?_
    have hmul :
        L *
          (eLpNorm (F i) 1
            (MeasureTheory.volume.restrict
              (Metric.closedBall x.1 r))).toReal ≤ B := by
      dsimp [B]
      exact mul_le_mul_of_nonneg_left hnorm_toReal hL_nonneg
    exact mul_le_mul_of_nonneg_right hmul dist_nonneg
  have hsmall : B * dist x y < ε := by
    calc
      B * dist x y ≤ B * δ :=
        mul_le_mul_of_nonneg_left (le_of_lt hdist_sub) hB_nonneg
      _ ≤ B * (ε / (B + 1)) := hBδ_le
      _ < ε := hB_eps_lt
  exact hεU (by
    simpa [Real.dist_eq] using hosc_C.trans_lt hsmall)

/--
%%handwave
name:
  Interior \(L^1\)-equicontinuity for harmonic families
statement:
  A locally \(L^1\)-bounded family of harmonic functions on an open plane
  region is equicontinuous at each point of that region.
proof:
  Choose a compact disk collar around the point.  The local \(L^1\)-bound on
  that collar and the Poisson-kernel interior estimates give a common local
  modulus of continuity for all functions in the family.
-/
theorem harmonic_locallyL1_bounded_equicontinuousAt
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hlocal_bound :
      ∀ K : Set ℂ, IsCompact K → K ⊆ V →
        ∃ C : ℝ≥0∞, C < (∞ : ℝ≥0∞) ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            eLpNorm (F n) 1 (MeasureTheory.volume.restrict K) ≤ C)
    (x : V) :
    EquicontinuousAt (fun n : ℕ ↦ fun y : V ↦ F n y.1) x := by
  rcases Metric.mem_nhds_iff.mp (hV_open.mem_nhds x.2) with
    ⟨R, hR_pos, hR_subset⟩
  let r : ℝ := R / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt_R : r < R := by
    dsimp [r]
    linarith
  have hclosed_subset_ball :
      Metric.closedBall x.1 r ⊆ Metric.ball x.1 R :=
    Metric.closedBall_subset_ball hr_lt_R
  have hclosed_subset_V : Metric.closedBall x.1 r ⊆ V :=
    hclosed_subset_ball.trans hR_subset
  let K : Set ℂ := Metric.closedBall x.1 r
  have hK_compact : IsCompact K := by
    simpa [K] using isCompact_closedBall x.1 r
  have hKV : K ⊆ V := by
    simpa [K] using hclosed_subset_V
  rcases hlocal_bound K hK_compact hKV with
    ⟨C, hC_lt_top, hC_event⟩
  rcases Filter.eventually_atTop.mp hC_event with ⟨N, hN⟩
  have htail :
      EquicontinuousAt
        (fun n : {n : ℕ // N ≤ n} ↦ fun y : V ↦ F n.1 y.1) x := by
    refine
      harmonic_closedBall_l1_bounded_equicontinuousAt
        (x := x) hr_pos hclosed_subset_V
        (F := fun n : {n : ℕ // N ≤ n} ↦ F n.1)
        (fun n ↦ hharm n.1) hC_lt_top ?_
    intro n
    simpa [K] using hN n.1 n.2
  have hinit :
      EquicontinuousAt
        (fun k : Fin N ↦ fun y : V ↦ F k.1 y.1) x := by
    rw [equicontinuousAt_finite]
    intro k
    have hcont :
        Continuous (fun y : V ↦ F k.1 y.1) :=
      continuousOn_iff_continuous_restrict.mp (hharm k.1).continuousOn
    exact hcont.continuousAt
  exact
    equicontinuousAt_nat_of_fin_initial_and_tail
      (F := fun n : ℕ ↦ fun y : V ↦ F n y.1) N hinit htail

/--
%%handwave
name:
  Locally \(L^1\)-bounded harmonic families are equicontinuous on compact
  exhaustion pieces
statement:
  On every compact member of a compact exhaustion of an open plane region, a
  locally \(L^1\)-bounded harmonic sequence is equicontinuous.
proof:
  This is the equicontinuity part of the interior harmonic estimate.  Cover
  each compact exhaustion piece by finitely many disks with collars inside
  the region.  Local \(L^1\)-bounds on the collars and Poisson-kernel
  estimates give a common modulus of continuity on the piece.
-/
theorem harmonic_locallyL1_bounded_equicontinuousOn_compactExhaustion
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hlocal_bound :
      ∀ K : Set ℂ, IsCompact K → K ⊆ V →
        ∃ C : ℝ≥0∞, C < (∞ : ℝ≥0∞) ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            eLpNorm (F n) 1 (MeasureTheory.volume.restrict K) ≤ C)
    (K : CompactExhaustion V) :
    ∀ m : ℕ,
      EquicontinuousOn
        (fun n : ℕ ↦ fun x : V ↦ F n x.1) (K m) := by
  intro m x _hx
  exact
    (harmonic_locallyL1_bounded_equicontinuousAt
      hV_open hharm hlocal_bound x).equicontinuousWithinAt (K m)

/--
%%handwave
name:
  Locally \(L^1\)-bounded harmonic families give Ascoli data
statement:
  A locally \(L^1\)-bounded sequence of harmonic functions on an open plane
  region is pointwise bounded and equicontinuous on each member of a compact
  exhaustion of the region.
proof:
  This is the remaining analytic estimate: interior mean-value and Poisson
  bounds control point values and moduli of continuity on compact collars by
  the \(L^1\)-norm on a slightly larger compact set.
-/
theorem harmonic_locallyL1_bounded_compactExhaustion_ascoli_data
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hlocal_bound :
      ∀ K : Set ℂ, IsCompact K → K ⊆ V →
        ∃ C : ℝ≥0∞, C < (∞ : ℝ≥0∞) ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            eLpNorm (F n) 1 (MeasureTheory.volume.restrict K) ≤ C)
    (K : CompactExhaustion V) :
    (∀ x : V, ∃ Q : Set ℝ, IsCompact Q ∧
      ∀ n : ℕ, F n x.1 ∈ Q) ∧
      ∀ m : ℕ,
        EquicontinuousOn
          (fun n : ℕ ↦ fun x : V ↦ F n x.1) (K m) := by
  exact
    ⟨harmonic_locallyL1_bounded_pointwise_compactRange
        hV_open hharm hlocal_bound,
      harmonic_locallyL1_bounded_equicontinuousOn_compactExhaustion
        hV_open hharm hlocal_bound K⟩

/--
%%handwave
name:
  Locally \(L^1\)-bounded harmonic families have locally uniform subsequences
statement:
  If a sequence of harmonic functions on an open plane region is eventually
  bounded in \(L^1\) on every compact subset, then some subsequence converges
  locally uniformly on that region.
proof:
  This is the remaining normal-family extraction input.  The local
  \(L^1\)-bounds give local sup-norm and equicontinuity bounds on compact
  collars.  A diagonal Arzela-Ascoli extraction over a countable compact
  exhaustion gives a locally uniformly convergent subsequence.
-/
theorem exists_locallyUniform_subsequence_limit_of_harmonic_locallyL1_bounded
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hlocal_bound :
      ∀ K : Set ℂ, IsCompact K → K ⊆ V →
        ∃ C : ℝ≥0∞, C < (∞ : ℝ≥0∞) ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            eLpNorm (F n) 1 (MeasureTheory.volume.restrict K) ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ f : ℂ → ℝ,
      StrictMono φ ∧
        TendstoLocallyUniformlyOn
          (fun n : ℕ ↦ F (φ n)) f Filter.atTop V := by
  classical
  letI : LocallyCompactSpace V := hV_open.locallyCompactSpace
  letI : SigmaCompactSpace V := inferInstance
  let K : CompactExhaustion V := CompactExhaustion.choice V
  let G : ℕ → C(V, ℝ) := fun n ↦
    ⟨fun x : V ↦ F n x.1,
      continuousOn_iff_continuous_restrict.mp (hharm n).continuousOn⟩
  rcases harmonic_locallyL1_bounded_compactExhaustion_ascoli_data
      hV_open hharm hlocal_bound K with
    ⟨hpointwise, heq⟩
  rcases
    realContinuousMap_subsequence_tendstoLocallyUniformly_of_equicontinuousOn_compactExhaustion
      K G hpointwise heq with
    ⟨φ, hφ, g, hconv_sub⟩
  have hconv_sub' :
      TendstoLocallyUniformly
        (fun n : ℕ ↦ fun x : V ↦ F (φ n) x.1)
        (fun x : V ↦ g x) Filter.atTop := by
    simpa [G] using hconv_sub
  let f : ℂ → ℝ := fun z ↦ if hz : z ∈ V then g ⟨z, hz⟩ else 0
  refine ⟨φ, f, hφ, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  exact hconv_sub'.congr_right fun x ↦ by
    simp [f, x.2]

/--
%%handwave
name:
  Locally \(L^1\)-bounded harmonic families have normal harmonic subsequences
statement:
  If a sequence of harmonic functions on an open plane region is eventually
  bounded in \(L^1\) on every compact subset, then some subsequence converges
  locally uniformly to a harmonic function on that region.
proof:
  First extract a locally uniformly convergent subsequence.  The existing
  theorem that locally uniform limits of harmonic functions are harmonic then
  makes the limit harmonic.
-/
theorem exists_harmonic_locallyUniform_subsequence_limit_of_harmonic_locallyL1_bounded
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hlocal_bound :
      ∀ K : Set ℂ, IsCompact K → K ⊆ V →
        ∃ C : ℝ≥0∞, C < (∞ : ℝ≥0∞) ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            eLpNorm (F n) 1 (MeasureTheory.volume.restrict K) ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ f : ℂ → ℝ,
      StrictMono φ ∧
        InnerProductSpace.HarmonicOnNhd f V ∧
          TendstoLocallyUniformlyOn
            (fun n : ℕ ↦ F (φ n)) f Filter.atTop V := by
  rcases
    exists_locallyUniform_subsequence_limit_of_harmonic_locallyL1_bounded
      hV_open hharm hlocal_bound with
    ⟨φ, f, hφ, hconv⟩
  have hharm_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        InnerProductSpace.HarmonicOnNhd (F (φ n)) V :=
    Filter.Eventually.of_forall fun n ↦ hharm (φ n)
  exact
    ⟨φ, f, hφ,
      harmonicOnNhd_of_tendstoLocallyUniformlyOn hV_open hharm_event hconv,
      hconv⟩

/--
%%handwave
name:
  \(L^1\)-convergent harmonic sequences are locally \(L^1\)-bounded
statement:
  If a sequence converges in \(L^1\) to a locally integrable function on an
  open region, then on every compact subset of the region the \(L^1\)-norms
  of the sequence are eventually bounded by a finite constant.
proof:
  Restrict the convergence to the compact set.  The locally integrable limit
  is integrable on that compact set, so the triangle inequality gives a
  finite eventual bound.
-/
theorem harmonic_l1_convergent_eventually_l1_bounded_on_compacts
    {V : Set ℂ} {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_loc : LocallyIntegrableOn u V (MeasureTheory.volume : Measure ℂ))
    (hFuV :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ V →
      ∃ C : ℝ≥0∞, C < (∞ : ℝ≥0∞) ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          eLpNorm (F n) 1 (MeasureTheory.volume.restrict K) ≤ C := by
  intro K hK hKV
  have hFuK :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict K))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_eLpNorm_one_zero_restrict_mono (A := K) (B := V) hKV hFuV
  have hF_measK :
      ∀ n : ℕ, AEStronglyMeasurable (F n)
        (MeasureTheory.volume.restrict K) := by
    intro n
    exact (hF_meas n).mono_measure (Measure.restrict_mono hKV le_rfl)
  have hu_intK : Integrable u (MeasureTheory.volume.restrict K) := by
    have hu_onK : IntegrableOn u K (MeasureTheory.volume : Measure ℂ) :=
      hu_loc.integrableOn_compact_subset hKV hK
    simpa [IntegrableOn] using hu_onK
  have hu_measK :
      AEStronglyMeasurable u (MeasureTheory.volume.restrict K) :=
    hu_intK.aestronglyMeasurable
  have hu_lt_top :
      eLpNorm u 1 (MeasureTheory.volume.restrict K) < (∞ : ℝ≥0∞) :=
    (memLp_one_iff_integrable.mpr hu_intK).eLpNorm_lt_top
  exact
    eventually_eLpNorm_one_le_const_of_tendsto_eLpNorm_one_sub
      hF_measK hu_measK hu_lt_top hFuK

/--
%%handwave
name:
  Harmonic \(L^1\)-limits have locally uniform harmonic subsequential limits
statement:
  If harmonic functions on an open plane region converge in \(L^1\) to a
  locally integrable function, then some subsequence converges locally
  uniformly to a harmonic function on that region.
proof:
  The \(L^1\)-convergence and local integrability give eventual \(L^1\)-bounds
  on every compact subset.  Apply the normal-family compactness theorem for
  locally \(L^1\)-bounded harmonic families.
-/
theorem exists_harmonic_locallyUniform_subsequence_limit_of_harmonic_l1_convergent
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_loc : LocallyIntegrableOn u V (MeasureTheory.volume : Measure ℂ))
    (hFuV :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ φ : ℕ → ℕ, ∃ f : ℂ → ℝ,
      StrictMono φ ∧
        InnerProductSpace.HarmonicOnNhd f V ∧
          TendstoLocallyUniformlyOn
            (fun n : ℕ ↦ F (φ n)) f Filter.atTop V := by
  exact
    exists_harmonic_locallyUniform_subsequence_limit_of_harmonic_locallyL1_bounded
      hV_open hharm
      (harmonic_l1_convergent_eventually_l1_bounded_on_compacts
        hF_meas hu_loc hFuV)

/--
%%handwave
name:
  Locally uniform harmonic subsequential limits give local representatives
statement:
  Suppose a harmonic subsequence converges locally uniformly to a harmonic
  function on an open set, while the original sequence converges in \(L^1\)
  to the weak solution on a larger protected set.  Then the weak solution has
  a local Weyl representative at any point of the open set.
proof:
  Around the point choose an open neighbourhood contained in a compact collar.
  Locally uniform convergence becomes uniform convergence on the compact
  collar, and the \(L^1\)-convergence to the weak solution restricts to the
  same collar.  The two limits therefore agree almost everywhere on the
  collar, hence on the smaller neighbourhood.
-/
theorem localEuclideanWeylHarmonicRepresentative_of_locallyUniform_subsequence_l1_on_superset
    {Ω V Q : Set ℂ} {z : ℂ} {F : ℕ → ℂ → ℝ} {φ : ℕ → ℕ}
    {u f : ℂ → ℝ}
    (hzV : z ∈ V) (hV_open : IsOpen V) (hVΩ : V ⊆ Ω) (hVQ : V ⊆ Q)
    (hf_harm : InnerProductSpace.HarmonicOnNhd f V)
    (hφ : StrictMono φ)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V))
    (hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict V))
    (hFuQ :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (hFφf :
      TendstoLocallyUniformlyOn
        (fun n : ℕ ↦ F (φ n)) f Filter.atTop V) :
    Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z) := by
  rcases exists_compact_collar_for_point_of_isOpen hV_open hzV with
    ⟨W, K, P, hzW, hW_open, hK_compact, hWK, _hP_compact, hKP, hPV⟩
  have hKV : K ⊆ V :=
    (subset_of_exists_cthickening_subset hKP).trans hPV
  have hWΩ : W ⊆ Ω :=
    hWK.trans (hKV.trans hVΩ)
  have hWKV : W ⊆ V := hWK.trans hKV
  have hFuK :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict K))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_eLpNorm_one_zero_restrict_mono
      (A := K) (B := Q) (hKV.trans hVQ) hFuQ
  have hFφuK :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F (φ n) w - u w) 1
          (MeasureTheory.volume.restrict K))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    hFuK.comp hφ.tendsto_atTop
  have hF_measK :
      ∀ n : ℕ, AEStronglyMeasurable (F (φ n))
        (MeasureTheory.volume.restrict K) := by
    intro n
    exact (hF_meas (φ n)).mono_measure (Measure.restrict_mono hKV le_rfl)
  have hu_measK : AEStronglyMeasurable u (MeasureTheory.volume.restrict K) :=
    hu_meas.mono_measure (Measure.restrict_mono hKV le_rfl)
  have hf_measK : AEStronglyMeasurable f (MeasureTheory.volume.restrict K) :=
    hf_meas.mono_measure (Measure.restrict_mono hKV le_rfl)
  have hFφfK :
      TendstoUniformlyOn (fun n : ℕ ↦ F (φ n)) f Filter.atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      hK_compact).mp (hFφf.mono hKV)
  have haeK :
      u =ᵐ[MeasureTheory.volume.restrict K] f :=
    ae_eq_of_tendstoUniformlyOn_compact_and_eLpNorm_one_tendsto_zero
      hK_compact hF_measK hu_measK hf_measK hFφuK hFφfK
  have haeW :
      u =ᵐ[MeasureTheory.volume.restrict W] f :=
    ae_mono (Measure.restrict_mono hWK le_rfl) haeK
  exact
    ⟨LocalEuclideanWeylHarmonicRepresentative.of_harmonicOn_ae_eq
      hzW hW_open hWΩ (hf_harm.mono hWKV) haeW⟩

/--
%%handwave
name:
  Harmonic \(L^1\)-limits have harmonic representatives
statement:
  If measurable harmonic functions on an open plane region converge in
  \(L^1\), then the \(L^1\)-limit agrees almost everywhere with a harmonic
  function on that region.
proof:
  Extract a locally uniformly convergent harmonic subsequence.  The preceding
  local representative construction gives a local harmonic representative at
  every point, and the local representatives glue to a global harmonic
  almost-everywhere representative.
-/
theorem exists_harmonic_ae_representative_of_harmonic_l1_convergent
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_loc : LocallyIntegrableOn u V (MeasureTheory.volume : Measure ℂ))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V))
    (hFuV :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ f : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd f V ∧
        u =ᵐ[MeasureTheory.volume.restrict V] f := by
  rcases
    exists_harmonic_locallyUniform_subsequence_limit_of_harmonic_l1_convergent
      hV_open hharm hF_meas hu_loc hFuV with
    ⟨φ, f, hφ, hf_harm, hFφf⟩
  have hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict V) :=
    hf_harm.continuousOn.aestronglyMeasurable hV_open.measurableSet
  have hlocal :
      ∀ z ∈ V, Nonempty (LocalEuclideanWeylHarmonicRepresentative V u z) := by
    intro z hzV
    exact
      localEuclideanWeylHarmonicRepresentative_of_locallyUniform_subsequence_l1_on_superset
        (Ω := V) (V := V) (Q := V) (F := F) (φ := φ) (u := u) (f := f)
        hzV hV_open (subset_rfl) (subset_rfl) hf_harm hφ
        hF_meas hu_meas hf_meas hFuV hFφf
  rcases euclideanWeylHarmonicRepresentative_of_local_representatives
      hlocal with
    ⟨hrep⟩
  exact ⟨hrep.toFun, hrep.harmonicOn, hrep.ae_eq⟩

/--
%%handwave
name:
  \(L^1\)-closedness of harmonic functions
statement:
  If every member of a sequence is harmonic on an open plane region and the
  sequence converges in \(L^1\) there, then the sequence has a harmonic
  \(L^1\)-limit on that region.
proof:
  This is the remaining analytic closedness input.  Local \(L^1\)-bounds for
  harmonic functions give normal-family compactness on compact subsets; the
  locally uniform subsequential limit is harmonic, and uniqueness of the
  \(L^1\)-limit identifies it with the given \(L^1\)-limit almost everywhere.
-/
theorem exists_harmonic_l1_limit_of_harmonic_l1_convergent
    {V : Set ℂ} (hV_open : IsOpen V)
    {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (hharm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F n) V)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_loc : LocallyIntegrableOn u V (MeasureTheory.volume : Measure ℂ))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V))
    (hFuV :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ f : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd f V ∧
        Filter.Tendsto
          (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - f w) 1
            (MeasureTheory.volume.restrict V))
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  rcases
    exists_harmonic_ae_representative_of_harmonic_l1_convergent
      hV_open hharm hF_meas hu_loc hu_meas hFuV with
    ⟨f, hf_harm, huf⟩
  exact
    ⟨f, hf_harm,
      tendsto_eLpNorm_one_zero_congr_ae_limit huf hFuV⟩

/--
%%handwave
name:
  Eventually harmonic \(L^1\)-limits reduce to harmonic \(L^1\)-closedness
statement:
  If a sequence is eventually harmonic on an open plane neighbourhood and
  converges in \(L^1\) on a larger protected set, then a subsequence converges
  in \(L^1\) on the neighbourhood to a harmonic function.
proof:
  Discard the finite initial segment on which harmonicity may fail.  The
  convergence on the protected set restricts to the neighbourhood and is
  preserved along the tail subsequence.  Apply \(L^1\)-closedness of harmonic
  functions to that tail.
-/
theorem exists_harmonic_l1_subsequence_limit_of_eventually_harmonic_l1_convergent_on_superset
    {V Q : Set ℂ} (hV_open : IsOpen V) (hVQ : V ⊆ Q)
    {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (hharm :
      ∀ᶠ n : ℕ in Filter.atTop,
        InnerProductSpace.HarmonicOnNhd (F n) V)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_loc : LocallyIntegrableOn u V (MeasureTheory.volume : Measure ℂ))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V))
    (hFuQ :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ φ : ℕ → ℕ, ∃ f : ℂ → ℝ,
      StrictMono φ ∧
        InnerProductSpace.HarmonicOnNhd f V ∧
          Filter.Tendsto
            (fun n : ℕ ↦ eLpNorm (fun w ↦ F (φ n) w - f w) 1
              (MeasureTheory.volume.restrict V))
            Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  rcases Filter.eventually_atTop.mp hharm with ⟨N, hN⟩
  let φ : ℕ → ℕ := fun n ↦ N + n
  have hφ : StrictMono φ := by
    intro a b hab
    exact Nat.add_lt_add_left hab N
  have hharmφ :
      ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (F (φ n)) V := by
    intro n
    exact hN (φ n) (Nat.le_add_right N n)
  have hFuV :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_eLpNorm_one_zero_restrict_mono (A := V) (B := Q) hVQ hFuQ
  have hFφuV :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F (φ n) w - u w) 1
          (MeasureTheory.volume.restrict V))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    hFuV.comp hφ.tendsto_atTop
  rcases
    exists_harmonic_l1_limit_of_harmonic_l1_convergent
      (V := V) hV_open (F := fun n : ℕ ↦ F (φ n)) (u := u)
      hharmφ (fun n ↦ hF_meas (φ n)) hu_loc hu_meas hFφuV with
    ⟨f, hf_harm, hFφfV⟩
  exact ⟨φ, f, hφ, hf_harm, hFφfV⟩

/--
%%handwave
name:
  Eventually harmonic \(L^1\)-convergent sequences give local representatives
statement:
  If a sequence is eventually harmonic on a neighbourhood and converges to
  the weak solution in \(L^1\) on a larger protected set, then the weak
  solution has a local Weyl representative at the marked point.
proof:
  Apply \(L^1\)-closedness of harmonic functions to get a harmonic
  subsequential limit, then use the subsequential common-limit criterion.
-/
theorem localEuclideanWeylHarmonicRepresentative_of_eventually_harmonic_l1_convergent_on_superset
    {Ω V Q : Set ℂ} {z : ℂ} {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (hzV : z ∈ V) (hV_open : IsOpen V) (hVΩ : V ⊆ Ω) (hVQ : V ⊆ Q)
    (hharm :
      ∀ᶠ n : ℕ in Filter.atTop,
        InnerProductSpace.HarmonicOnNhd (F n) V)
    (hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict V))
    (hu_loc : LocallyIntegrableOn u V (MeasureTheory.volume : Measure ℂ))
    (hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V))
    (hFuQ :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun w ↦ F n w - u w) 1
          (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z) := by
  rcases
    exists_harmonic_l1_subsequence_limit_of_eventually_harmonic_l1_convergent_on_superset
      hV_open hVQ hharm hF_meas hu_loc hu_meas hFuQ with
    ⟨φ, f, hφ, hf_harm, hFφf⟩
  have hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict V) :=
    hf_harm.continuousOn.aestronglyMeasurable hV_open.measurableSet
  exact
    localEuclideanWeylHarmonicRepresentative_of_harmonic_subsequence_l1_approx_on_superset
      hzV hV_open hVΩ hVQ hf_harm hφ hF_meas hu_meas hf_meas hFuQ hFφf

/--
%%handwave
name:
  Weakly harmonic functions have local Euclidean Weyl representatives
statement:
  Around each point of a Euclidean weakly harmonic region, there is a local
  harmonic representative agreeing almost everywhere with the weak solution.
proof:
  Choose a compact collar around the point and the cutoff-local standard
  mollifier sequence.  The sequence is eventually harmonic on the protected
  neighbourhood and converges to the weak solution in local \(L^1\).  The
  remaining analytic compactness step extracts a locally uniform harmonic
  limit on a smaller neighbourhood; the common-limit criterion identifies
  that harmonic limit almost everywhere with the weak solution.
-/
theorem localEuclideanWeylHarmonicRepresentative_of_weaklyHarmonicOn
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u)
    {z : ℂ} (hzΩ : z ∈ Ω) :
    Nonempty (LocalEuclideanWeylHarmonicRepresentative Ω u z) := by
  rcases
    exists_local_cutoff_standardMollifier_harmonicOnNhd_and_tendsto_ae_and_l1_of_weaklyHarmonicOn
      hweak hzΩ with
    ⟨V, Q, P, χ, hzV, hV_open, _hQ, hVQ, hVΩ, _hP, _hPΩ,
      hharm, _hae, hl1⟩
  let F : ℕ → ℂ → ℝ := fun n ↦
    euclideanMollification
      (scalarWeakSobolevStandardMollifier ℂ n)
      (fun y : ℂ ↦ χ y * u y)
  have hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℂ) :=
    hweak.locallyIntegrableOn
  have hF_meas :
      ∀ n : ℕ, AEStronglyMeasurable (F n)
        (MeasureTheory.volume.restrict V) := by
    intro n
    exact
      euclideanMollification_cutoff_standardMollifier_aestronglyMeasurable
        (V := V) χ hu_loc n
  have hu_meas : AEStronglyMeasurable u (MeasureTheory.volume.restrict V) :=
    (hu_loc.mono_set hVΩ).aestronglyMeasurable
  exact
    localEuclideanWeylHarmonicRepresentative_of_eventually_harmonic_l1_convergent_on_superset
      (F := F) hzV hV_open hVΩ hVQ hharm hF_meas
      (hu_loc.mono_set hVΩ) hu_meas hl1

/--
%%handwave
name:
  Euclidean Weyl lemma
statement:
  A Euclidean weakly harmonic function on an open coordinate region has a
  harmonic representative on that region.
proof:
  Convolve locally with a standard mollifier.  The weak harmonic identity
  passes to the mollifications and makes them classically harmonic.  The
  mollifications converge to the original function in \(L^1_{\mathrm{loc}}\);
  the mean-value property and local convergence identify the original
  representative with a smooth harmonic function.
-/
theorem euclidean_weyl_harmonicRepresentative_of_weaklyHarmonicOn
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hweak : IsEuclideanWeaklyHarmonicOn Ω u) :
    Nonempty (EuclideanWeylHarmonicRepresentative Ω u) := by
  exact
    euclideanWeylHarmonicRepresentative_of_local_representatives
      (fun z hzΩ ↦
        localEuclideanWeylHarmonicRepresentative_of_weaklyHarmonicOn
          hweak hzΩ)

/--
%%handwave
name:
  Weakly harmonic chart regions are open
statement:
  If a surface region is weakly harmonic, then its image in any holomorphic
  coordinate chart is an open subset of the coordinate plane.
proof:
  The surface region is open by definition of weak harmonicity, and an open
  partial homeomorphism carries this to openness of the corresponding chart
  region.
-/
theorem chartRegion_isOpen_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hweak : IsWeaklyHarmonicOnSurface g U u)
    (e : OpenPartialHomeomorph X ℂ) :
    IsOpen (e.target ∩ e.symm ⁻¹' U) :=
  e.isOpen_inter_preimage_symm hweak.isOpen

theorem surface_localSobolev_chartPullback_isWeakDerivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    {du : X → ℂ →L[ℝ] ℝ}
    (hlocal : IsIntrinsicLocalSobolevH1OnSurface g U u du)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      (e.target ∩ e.symm ⁻¹' U)
      (fun z : ℂ ↦ u (e.symm z))
      (SurfaceCotangentField.chartPullback
        (SurfaceCotangentField.ofCoordinateField du) e) := by
  intro φ v
  let ψ : SmoothCompactlySupportedCoordinateFunction (surfaceChartRegion e U) :=
    { toFun := φ.toFun
      smooth := φ.smooth
      support_subset := by
        simpa [surfaceChartRegion] using φ.support_subset
      compact_support := by
        simpa using φ.compact_support }
  have h := hlocal.1 e he ψ v
  simpa [ψ, surfaceChartRegion, SurfaceCotangentField.chartPullback,
    SurfaceCotangentField.evalChart, SurfaceCotangentField.ofCoordinateField,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

private theorem surfaceMetricCoordinateCotangentPairingInChart_mul_volumeDensity_eq_euclidean
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (hconformal : SurfaceMetricConformalToComplexStructure metric)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (z : ℂ) (hz : z ∈ e.target)
    (ξ η : ℂ →L[ℝ] ℝ) :
    surfaceMetricCoordinateCotangentPairingInChart metric e z ξ η *
        surfaceMetricVolumeDensityInChart metric e z =
      euclideanCotangentPairing
        (ξ.comp (surfaceChartTangentMap e z))
        (η.comp (surfaceChartTangentMap e z)) := by
  let ρ : ℝ := surfaceMetricVolumeDensityInChart metric e z
  let A : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e z
  let G : Fin 2 → Fin 2 → ℝ :=
    fun i j ↦ surfaceMetricInverseGramCoeffInChart metric e z i j
  let Xc : Fin 2 → ℝ := fun i ↦ ξ (A (complexCoordinateVector i))
  let Yc : Fin 2 → ℝ := fun i ↦ η (A (complexCoordinateVector i))
  have hcoeff : ∀ i j : Fin 2, ρ * G i j = if i = j then 1 else 0 := by
    intro i j
    simpa [ρ, G] using hconformal e he z hz i j
  calc
        surfaceMetricCoordinateCotangentPairingInChart metric e z ξ η *
        surfaceMetricVolumeDensityInChart metric e z
        = ∑ i : Fin 2, ∑ j : Fin 2,
            (ρ * G i j) * Xc i * Yc j := by
            simp [surfaceMetricCoordinateCotangentPairingInChart, ρ, G, Xc, Yc]
            ring
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
          (if i = j then 1 else 0 : ℝ) * Xc i * Yc j := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [hcoeff i j]
    _ = Xc 0 * Yc 0 + Xc 1 * Yc 1 := by
          simp [Fin.sum_univ_two]
    _ = euclideanCotangentPairing
          (ξ.comp (surfaceChartTangentMap e z))
          (η.comp (surfaceChartTangentMap e z)) := by
          simp [euclideanCotangentPairing, Xc, Yc, A]

theorem surfaceMetricWeakGradientCoordinatePairingInChart_mul_volumeDensity_eq_euclidean
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (z : ℂ) (hz : z ∈ e.target)
    (ξ dη : ℂ →L[ℝ] ℝ) :
    surfaceMetricWeakGradientCoordinatePairingInChart g e z ξ dη *
        surfaceMetricVolumeDensityInChart g.metric e z =
      euclideanCotangentPairing
        (ξ.comp (surfaceChartTangentMap e z)) dη := by
  let ρ : ℝ := surfaceMetricVolumeDensityInChart g.metric e z
  let A : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e z
  let G : Fin 2 → Fin 2 → ℝ :=
    fun i j ↦ surfaceMetricInverseGramCoeffInChart g.metric e z i j
  let Xc : Fin 2 → ℝ := fun i ↦ ξ (A (complexCoordinateVector i))
  let Yc : Fin 2 → ℝ := fun i ↦ dη (complexCoordinateVector i)
  have hcoeff : ∀ i j : Fin 2, ρ * G i j = if i = j then 1 else 0 := by
    intro i j
    simpa [BackgroundSurfaceMetricConformalToComplexStructure, ρ, G] using
      hconformal e he z hz i j
  calc
    surfaceMetricWeakGradientCoordinatePairingInChart g e z ξ dη *
        surfaceMetricVolumeDensityInChart g.metric e z
        = ∑ i : Fin 2, ∑ j : Fin 2,
            (ρ * G i j) * Xc i * Yc j := by
            simp [surfaceMetricWeakGradientCoordinatePairingInChart, ρ, G, Xc, Yc]
            ring
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
          (if i = j then 1 else 0 : ℝ) * Xc i * Yc j := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [hcoeff i j]
    _ = Xc 0 * Yc 0 + Xc 1 * Yc 1 := by
          simp [Fin.sum_univ_two]
    _ = euclideanCotangentPairing
          (ξ.comp (surfaceChartTangentMap e z)) dη := by
          simp [euclideanCotangentPairing, Xc, Yc, A]

/--
%%handwave
name:
  Conformal charts preserve the weak harmonic identity
statement:
  In a conformal holomorphic chart, the coordinate representative of a
  weakly harmonic surface function has a Euclidean weak derivative satisfying
  the zero-divergence identity.
proof:
  Pull the surface weak gradient through the chart inverse.  The weak
  derivative identity follows from the surface local Sobolev condition.
  For the divergence identity, extend compactly supported coordinate tests by
  zero to surface tests and use conformality to identify the metric
  density-weighted inverse pairing with the Euclidean cotangent pairing.
-/
theorem exists_euclideanWeakDerivative_zeroDivergence_chart_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hweak : IsWeaklyHarmonicOnSurface g U u)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    ∃ du : ℂ → ℂ →L[ℝ] ℝ,
      IsWeakDerivativeOnEuclideanRegionWithValues
          (e.target ∩ e.symm ⁻¹' U)
          (fun z : ℂ ↦ u (e.symm z)) du ∧
        ∀ η : SmoothCompactlySupportedManifoldCoordinateFunction
            (e.target ∩ e.symm ⁻¹' U),
          Integrable
              (fun z ↦
                euclideanCotangentPairing (du z)
                  (fderiv ℝ (η : ℂ → ℝ) z))
              (MeasureTheory.volume.restrict (e.target ∩ e.symm ⁻¹' U)) ∧
            ∫ z in e.target ∩ e.symm ⁻¹' U,
                euclideanCotangentPairing (du z)
                  (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume = 0 := by
  rcases hweak.exists_localSobolev_gradient with ⟨du, hlocal, hzero⟩
  let D : ℂ → ℂ →L[ℝ] ℝ :=
    SurfaceCotangentField.chartPullback
      (SurfaceCotangentField.ofCoordinateField du) e
  refine ⟨D, ?_, ?_⟩
  · exact surface_localSobolev_chartPullback_isWeakDerivative hlocal e he
  · intro η
    let Ω : Set ℂ := surfaceChartRegion e U
    let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
      { toFun := η.toFun
        smooth := η.smooth
        support_subset := by
          simpa [Ω, surfaceChartRegion] using η.support_subset
        compact_support := by
          simpa using η.compact_support }
    rcases hzero e he ψ with ⟨hmetric_int, hmetric_zero⟩
    let metricIntegrand : ℂ → ℝ := fun z ↦
      surfaceMetricWeakGradientCoordinatePairingInChart g e z
        (du (e.symm z))
        (fderiv ℝ (η : ℂ → ℝ) z) *
          surfaceMetricVolumeDensityInChart g.metric e z
    let euclideanIntegrand : ℂ → ℝ := fun z ↦
      euclideanCotangentPairing (D z)
        (fderiv ℝ (η : ℂ → ℝ) z)
    have hΩ_open : IsOpen Ω := by
      simpa [Ω, surfaceChartRegion] using
        e.isOpen_inter_preimage_symm hweak.isOpen
    have hfun_ae : euclideanIntegrand =ᵐ[
        MeasureTheory.volume.restrict Ω] metricIntegrand := by
      filter_upwards
        [MeasureTheory.self_mem_ae_restrict
          (μ := MeasureTheory.volume) hΩ_open.measurableSet] with z hzΩ
      have hz_target : z ∈ e.target := hzΩ.1
      have hpoint :=
        surfaceMetricWeakGradientCoordinatePairingInChart_mul_volumeDensity_eq_euclidean
          g hconformal e he z hz_target
          (du (e.symm z)) (fderiv ℝ (η : ℂ → ℝ) z)
      simpa [euclideanIntegrand, metricIntegrand, D,
        SurfaceCotangentField.chartPullback,
        SurfaceCotangentField.ofCoordinateField] using hpoint.symm
    have hmetric_int' :
        Integrable metricIntegrand
          (MeasureTheory.volume.restrict Ω) := by
      simpa [metricIntegrand, ψ, Ω] using hmetric_int
    refine ⟨?_, ?_⟩
    · simpa [euclideanIntegrand, Ω, surfaceChartRegion] using
        hmetric_int'.congr hfun_ae.symm
    · calc
        ∫ z in e.target ∩ e.symm ⁻¹' U,
            euclideanCotangentPairing (D z)
              (fderiv ℝ (η : ℂ → ℝ) z) ∂MeasureTheory.volume
            = ∫ z, euclideanIntegrand z
                ∂(MeasureTheory.volume.restrict Ω) := by
                simp [euclideanIntegrand, Ω, surfaceChartRegion]
        _ = ∫ z, metricIntegrand z
                ∂(MeasureTheory.volume.restrict Ω) :=
                integral_congr_ae hfun_ae
        _ = 0 := by
                simpa [metricIntegrand, ψ, Ω] using hmetric_zero

/--
%%handwave
name:
  Surface weak harmonicity becomes Euclidean weak harmonicity in charts
statement:
  In a conformal holomorphic chart, a weakly harmonic surface function has a
  Euclidean weakly harmonic coordinate representative.
proof:
  Restrict the surface weak gradient to the coordinate chart and pull it back
  through the chart inverse.  Coordinate test functions with compact support
  in the chart region extend by zero to smooth compactly supported surface
  tests.  Conformality identifies the density-weighted inverse-metric pairing
  with the Euclidean cotangent pairing, so the surface zero-divergence
  identity is exactly the Euclidean weak-harmonic identity.
-/
theorem euclideanWeaklyHarmonicOn_chart_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hweak : IsWeaklyHarmonicOnSurface g U u)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    IsEuclideanWeaklyHarmonicOn
      (e.target ∩ e.symm ⁻¹' U)
      (fun z : ℂ ↦ u (e.symm z)) := by
  refine ⟨chartRegion_isOpen_of_weaklyHarmonicOnSurface hweak e, ?_⟩
  exact
    exists_euclideanWeakDerivative_zeroDivergence_chart_of_weaklyHarmonicOnSurface
      hconformal hweak e he

/--
%%handwave
name:
  Weyl representative in a conformal surface chart
statement:
  In a conformal holomorphic chart, a weakly harmonic surface function has a
  harmonic coordinate representative.
proof:
  Convert the surface weak-harmonic identity to Euclidean weak harmonicity in
  the chart and apply the Euclidean Weyl representative theorem.
-/
theorem weyl_harmonicRepresentative_chart_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hweak : IsWeaklyHarmonicOnSurface g U u)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    Nonempty
      (EuclideanWeylHarmonicRepresentative
        (e.target ∩ e.symm ⁻¹' U)
        (fun z : ℂ ↦ u (e.symm z))) :=
  euclidean_weyl_harmonicRepresentative_of_weaklyHarmonicOn
    (euclideanWeaklyHarmonicOn_chart_of_weaklyHarmonicOnSurface
      hconformal hweak e he)

/--
%%handwave
name:
  Compatible chart representatives for a weakly harmonic surface function
statement:
  A family of Weyl representatives in all holomorphic charts is compatible
  when representatives in overlapping charts agree after coordinate change.
-/
structure SurfaceWeylChartRepresentativeFamily {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [ComplexOneManifold X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (U : Set X) (u : X → ℝ) where
  /-- The harmonic representative in each chart. -/
  chartRep :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
      EuclideanWeylHarmonicRepresentative
        (e.target ∩ e.symm ⁻¹' U)
        (fun z : ℂ ↦ u (e.symm z))
  /-- Representatives in overlapping charts agree through the transition map. -/
  overlap_eqOn :
    ∀ (e e' : OpenPartialHomeomorph X ℂ)
      (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X),
      (surfaceChartOverlapDomain e' e ∩
          (e.target ∩ e.symm ⁻¹' U)).EqOn
        (chartRep e he).toFun
        (fun z : ℂ ↦
          (chartRep e' he').toFun (surfaceChartTransition e' e z))

/--
%%handwave
name:
  Weakly harmonic functions have compatible chart representatives
statement:
  A weakly harmonic function on a conformal surface has harmonic
  representatives in all charts, and these representatives are compatible on
  overlaps.
proof:
  Apply the chart form of Weyl's lemma in every chart.  Compatibility on
  overlaps follows from uniqueness of harmonic representatives and
  nonsingularity of holomorphic coordinate changes for area measure.
-/
theorem
    surfaceWeylChartRepresentativeFamily_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [ComplexOneManifold X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hweak : IsWeaklyHarmonicOnSurface g U u) :
    Nonempty (SurfaceWeylChartRepresentativeFamily g.metric U u) := by
  classical
  let reps :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        EuclideanWeylHarmonicRepresentative
          (e.target ∩ e.symm ⁻¹' U)
          (fun z : ℂ ↦ u (e.symm z)) :=
    fun e he ↦
      Classical.choice
        (weyl_harmonicRepresentative_chart_of_weaklyHarmonicOnSurface
          hconformal hweak e he)
  refine
    ⟨{ chartRep := reps
       overlap_eqOn := ?_ }⟩
  intro e e' he he'
  exact
    euclideanWeylHarmonicRepresentative_eqOn_surfaceChartOverlap
      g.metric hweak.isOpen e e' he he' (reps e he) (reps e' he')

/--
%%handwave
name:
  Gluing compatible chart representatives
statement:
  A compatible family of harmonic chart representatives determines a global
  pointwise representative by evaluating the representative in the preferred
  chart centered at each point.
-/
noncomputable def surfaceWeylChartRepresentativeGlue {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [ComplexOneManifold X]
    {metric : SmoothRiemannianMetricOnSurface X}
    {U : Set X} {u : X → ℝ}
    (family : SurfaceWeylChartRepresentativeFamily metric U u) :
    X → ℝ := by
  classical
  exact fun x ↦
    if hx : x ∈ U then
      (family.chartRep (chartAt ℂ x) (chart_mem_atlas ℂ x)).toFun
        ((chartAt ℂ x) x)
    else 0

/--
%%handwave
name:
  The glued representative equals each chart representative
statement:
  On the coordinate region of any chart, the glued representative agrees
  pointwise with the harmonic representative chosen in that chart.
proof:
  At a point \(x\) in the region, the glued value is defined using the
  preferred chart at \(x\).  Compatibility on the overlap of the given chart
  with this preferred chart identifies the two representative values.
-/
theorem surfaceWeylChartRepresentativeGlue_eq_chartRep {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [ComplexOneManifold X]
    {metric : SmoothRiemannianMetricOnSurface X}
    {U : Set X} {u : X → ℝ}
    (family : SurfaceWeylChartRepresentativeFamily metric U u)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {z : ℂ} (hz : z ∈ e.target ∩ e.symm ⁻¹' U) :
    surfaceWeylChartRepresentativeGlue family (e.symm z) =
      (family.chartRep e he).toFun z := by
  classical
  let x : X := e.symm z
  have hxU : x ∈ U := by
    simpa [x] using hz.2
  have hx_chart_source : x ∈ (chartAt ℂ x).source :=
    mem_chart_source ℂ x
  have hzD : z ∈ surfaceChartOverlapDomain (chartAt ℂ x) e := by
    refine ⟨hz.1, ?_⟩
    simpa [x] using hx_chart_source
  have hcompat :=
    family.overlap_eqOn e (chartAt ℂ x) he (chart_mem_atlas ℂ x)
      ⟨hzD, hz⟩
  have hT :
      surfaceChartTransition (chartAt ℂ x) e z = (chartAt ℂ x) x := by
    simp [surfaceChartTransition, x]
  simpa [surfaceWeylChartRepresentativeGlue, hxU, x, hT] using hcompat.symm

/--
%%handwave
name:
  The glued representative is harmonic
statement:
  The function obtained by gluing a compatible family of harmonic chart
  representatives is harmonic on the surface region.
proof:
  In any chart, the glued function agrees near each point with the harmonic
  representative chosen in that chart.  Harmonicity is invariant under
  equality in a neighbourhood.
-/
theorem surfaceWeylChartRepresentativeGlue_harmonicOnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [ComplexOneManifold X]
    {metric : SmoothRiemannianMetricOnSurface X}
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (family : SurfaceWeylChartRepresentativeFamily metric U u) :
    IsHarmonicOnSurface U (surfaceWeylChartRepresentativeGlue family) := by
  intro e he z hz
  let Ω : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hΩ_open : IsOpen Ω := by
    simpa [Ω] using e.isOpen_inter_preimage_symm hU_open
  have heq :
      (fun w : ℂ ↦ surfaceWeylChartRepresentativeGlue family (e.symm w))
        =ᶠ[𝓝 z] (family.chartRep e he).toFun := by
    filter_upwards [hΩ_open.mem_nhds (by simpa [Ω] using hz)] with w hw
    exact surfaceWeylChartRepresentativeGlue_eq_chartRep family e he
      (by simpa [Ω] using hw)
  exact
    (InnerProductSpace.harmonicAt_congr_nhds heq).2
      ((family.chartRep e he).harmonicOn z hz)

/--
%%handwave
name:
  The glued representative has the expected chart almost-everywhere value
statement:
  In every chart, the glued representative agrees almost everywhere with the
  original weak function on the coordinate region.
proof:
  The chart representative agrees almost everywhere with the weak function by
  construction, and the glued representative agrees pointwise with the chart
  representative on the same coordinate region.
-/
theorem surfaceWeylChartRepresentativeGlue_chart_ae_eq {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [ComplexOneManifold X]
    {metric : SmoothRiemannianMetricOnSurface X}
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (family : SurfaceWeylChartRepresentativeFamily metric U u)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    (fun z : ℂ ↦ u (e.symm z))
      =ᵐ[MeasureTheory.volume.restrict (e.target ∩ e.symm ⁻¹' U)]
      (fun z : ℂ ↦ surfaceWeylChartRepresentativeGlue family (e.symm z)) := by
  let Ω : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hΩ_meas : MeasurableSet Ω := by
    simpa [Ω] using (e.isOpen_inter_preimage_symm hU_open).measurableSet
  have hpoint :
      (family.chartRep e he).toFun
        =ᵐ[MeasureTheory.volume.restrict Ω]
        (fun z : ℂ ↦ surfaceWeylChartRepresentativeGlue family (e.symm z)) := by
    refine ae_restrict_of_forall_mem hΩ_meas ?_
    intro z hz
    exact (surfaceWeylChartRepresentativeGlue_eq_chartRep family e he
      (by simpa [Ω] using hz)).symm
  have hae :
      (fun z : ℂ ↦ u (e.symm z))
        =ᵐ[MeasureTheory.volume.restrict Ω]
        (family.chartRep e he).toFun := by
    simpa [Ω] using (family.chartRep e he).ae_eq
  exact hae.trans hpoint

/--
%%handwave
name:
  A compatible chart family gives a global Weyl representative
statement:
  A compatible family of harmonic chart representatives glues to a global
  harmonic representative which agrees almost everywhere with the original
  weak function in every chart.
-/
theorem surfaceWeylHarmonicRepresentative_of_chartRepresentativeFamily
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [ComplexOneManifold X]
    {metric : SmoothRiemannianMetricOnSurface X}
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (family : SurfaceWeylChartRepresentativeFamily metric U u) :
    ∃ G : X → ℝ,
      (∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun z : ℂ ↦ u (e.symm z))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' U)]
          (fun z : ℂ ↦ G (e.symm z))) ∧
        IsHarmonicOnSurface U G := by
  refine ⟨surfaceWeylChartRepresentativeGlue family, ?_, ?_⟩
  · intro e he
    exact surfaceWeylChartRepresentativeGlue_chart_ae_eq hU_open family e he
  · exact surfaceWeylChartRepresentativeGlue_harmonicOnSurface hU_open family

/--
%%handwave
name:
  Weakly harmonic surface functions have global Weyl representatives
statement:
  A weakly harmonic function on a conformal surface has a global harmonic
  representative which agrees with it almost everywhere in every chart.
proof:
  First construct the compatible family of chart representatives by Weyl's
  lemma in charts and overlap uniqueness.  Then glue the compatible family.
-/
theorem surfaceWeylHarmonicRepresentative_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [ComplexOneManifold X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hweak : IsWeaklyHarmonicOnSurface g U u) :
    ∃ G : X → ℝ,
      (∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun z : ℂ ↦ u (e.symm z))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' U)]
          (fun z : ℂ ↦ G (e.symm z))) ∧
        IsHarmonicOnSurface U G := by
  rcases
      surfaceWeylChartRepresentativeFamily_of_weaklyHarmonicOnSurface
        hconformal hweak with
    ⟨family⟩
  exact
    surfaceWeylHarmonicRepresentative_of_chartRepresentativeFamily
      hweak.isOpen family

/--
%%handwave
name:
  Chart form of Weyl's lemma on a conformal surface
statement:
  In a holomorphic chart, a weakly harmonic locally \(W^{1,2}\) surface
  function for a conformal background metric has a harmonic coordinate
  representative.
proof:
  Restrict to the chart image over the region.  The local Sobolev and
  zero-source identities from the surface weak formulation give the
  distributional Euclidean Laplace equation for the coordinate representative,
  because conformality makes the metric divergence form equal to the
  Euclidean one.  The Euclidean Weyl lemma then gives harmonicity on the
  chart region.
-/
theorem weyl_harmonicOnNhd_chart_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (_hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (_hweak : IsWeaklyHarmonicOnSurface g U u)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    HasPointwiseEuclideanWeylRepresentative
      (e.target ∩ e.symm ⁻¹' U)
      (fun z : ℂ ↦ u (e.symm z)) →
    InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ ↦ u (e.symm z))
      (e.target ∩ e.symm ⁻¹' U) := by
  intro hpointwise
  exact harmonicOnNhd_of_pointwiseEuclideanWeylRepresentative hpointwise

/--
%%handwave
name:
  Pointwise Weyl representatives in every chart
statement:
  A surface weak solution has pointwise Weyl representatives in charts if in
  every holomorphic chart its coordinate representative has a harmonic Weyl
  representative agreeing with it locally at each point.
-/
def HasPointwiseWeylRepresentativesInCharts {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
    HasPointwiseEuclideanWeylRepresentative
      (e.target ∩ e.symm ⁻¹' U)
      (fun z : ℂ ↦ u (e.symm z))

/--
%%handwave
name:
  Weyl's lemma on a conformal surface
statement:
  For a background metric conformal to the complex structure, a weakly
  harmonic locally \(W^{1,2}\) function on an open surface region is harmonic
  in holomorphic coordinates.
proof:
  Work on a coordinate disk compactly contained in the region.  Conformality
  converts the metric weak equation to the ordinary Euclidean distributional
  Laplace equation.  Weyl's lemma on the plane gives a smooth harmonic
  representative on the disk.  These local representatives agree with the
  chosen surface representative and therefore give harmonicity in every
  surface coordinate.
tags:
  milestone
-/
theorem weyl_harmonicOnSurface_of_weaklyHarmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hweak : IsWeaklyHarmonicOnSurface g U u)
    (hpointwise : HasPointwiseWeylRepresentativesInCharts U u) :
    IsHarmonicOnSurface U u := by
  intro e he
  exact
    weyl_harmonicOnNhd_chart_of_weaklyHarmonicOnSurface
      hconformal hweak e he (hpointwise e he)

/--
%%handwave
name:
  Weak zero-source equations are harmonic
statement:
  For a conformal background metric, a weak Laplace-Beltrami equation with
  zero source is harmonic in holomorphic coordinates.
proof:
  A zero-source weak equation is weakly harmonic, and Weyl's lemma upgrades
  weak harmonicity to coordinate harmonicity.
-/
theorem weyl_harmonicOnSurface_of_weakLaplaceBeltramiSource_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hweak :
      IsWeakLaplaceBeltramiSourceOnSurface g U u (fun _ : X ↦ 0))
    (hpointwise : HasPointwiseWeylRepresentativesInCharts U u) :
    IsHarmonicOnSurface U u :=
  weyl_harmonicOnSurface_of_weaklyHarmonicOnSurface hconformal
    (weaklyHarmonicOnSurface_of_weakLaplaceBeltramiSource_zero hweak)
    hpointwise

/--
%%handwave
name:
  Source cancellation gives weak harmonicity
statement:
  If two locally Sobolev functions have weak Laplace-Beltrami sources which
  are negatives of one another, their sum is weakly harmonic.
proof:
  Add the two weak identities.  The source integrals cancel and the weak
  gradients add to the weak gradient of the sum.
-/
theorem weaklyHarmonicOnSurface_of_source_cancellation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel 1 X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X}
    {u v F : X → ℝ}
    (hu :
      IsWeakLaplaceBeltramiSourceOnSurface g U u F)
    (hv :
      IsWeakLaplaceBeltramiSourceOnSurface g U v (fun x ↦ -F x)) :
    IsWeaklyHarmonicOnSurface g U (fun x ↦ u x + v x) := by
  rcases hu with ⟨hU_open, du, hlocal_u, htest_u⟩
  rcases hv with ⟨_hU_open_v, dv, hlocal_v, htest_v⟩
  refine ⟨hU_open, du + dv, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [Pi.add_apply] using
        (IsWeakGradientOnRegion.add hlocal_u.1 hlocal_v.1)
    · intro K hK hKU
      rcases hlocal_u.2 K hK hKU with ⟨hu_l2, hdu_l2⟩
      rcases hlocal_v.2 K hK hKU with ⟨hv_l2, hdv_l2⟩
      have huv_l2 : MemLp (u + v) 2 (g.volume.restrict K) := hu_l2.add hv_l2
      have hduv_l2 :
          SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric
            (g.volume.restrict K)
            (SurfaceCotangentField.ofCoordinateField (du + dv)) :=
        surfaceCotangentFieldMemHilbertSchmidtL2_add hdu_l2 hdv_l2
      exact ⟨by simpa [Pi.add_apply] using huv_l2, hduv_l2⟩
  · intro e he η
    rcases htest_u e he η with ⟨hgrad_u, hsource_u, hEq_u⟩
    rcases htest_v e he η with ⟨hgrad_v, hsource_v, hEq_v⟩
    let Ω : Set ℂ := surfaceChartRegion e U
    let μΩ : Measure ℂ := MeasureTheory.volume.restrict Ω
    let grad_u : ℂ → ℝ :=
      fun z ↦
        surfaceMetricWeakGradientCoordinatePairingInChart g e z
          (du (e.symm z))
          (fderiv ℝ (η : ℂ → ℝ) z) *
            surfaceMetricVolumeDensityInChart g.metric e z
    let grad_v : ℂ → ℝ :=
      fun z ↦
        surfaceMetricWeakGradientCoordinatePairingInChart g e z
          (dv (e.symm z))
          (fderiv ℝ (η : ℂ → ℝ) z) *
            surfaceMetricVolumeDensityInChart g.metric e z
    let grad_sum : ℂ → ℝ :=
      fun z ↦
        surfaceMetricWeakGradientCoordinatePairingInChart g e z
          ((du + dv) (e.symm z))
          (fderiv ℝ (η : ℂ → ℝ) z) *
            surfaceMetricVolumeDensityInChart g.metric e z
    let source_u : ℂ → ℝ :=
      fun z ↦ F (e.symm z) * η z *
        surfaceMetricVolumeDensityInChart g.metric e z
    let source_v : ℂ → ℝ :=
      fun z ↦ (-F (e.symm z)) * η z *
        surfaceMetricVolumeDensityInChart g.metric e z
    have hgrad_u' : Integrable grad_u μΩ := by
      simpa [grad_u, μΩ, Ω] using hgrad_u
    have hgrad_v' : Integrable grad_v μΩ := by
      simpa [grad_v, μΩ, Ω] using hgrad_v
    have hsource_u' : Integrable source_u μΩ := by
      simpa [source_u, μΩ, Ω] using hsource_u
    have hsource_v' : Integrable source_v μΩ := by
      simpa [source_v, μΩ, Ω] using hsource_v
    have hgrad_sum_eq :
        grad_sum = fun z ↦ grad_u z + grad_v z := by
      ext z
      simp [grad_sum, grad_u, grad_v,
        surfaceMetricWeakGradientCoordinatePairingInChart_add_left]
      ring
    have hgrad_sum_int : Integrable grad_sum μΩ := by
      simpa [hgrad_sum_eq] using hgrad_u'.add hgrad_v'
    have hEq_u' :
        ∫ z, grad_u z ∂μΩ = -∫ z, source_u z ∂μΩ := by
      simpa [grad_u, source_u, μΩ, Ω] using hEq_u
    have hEq_v' :
        ∫ z, grad_v z ∂μΩ = -∫ z, source_v z ∂μΩ := by
      simpa [grad_v, source_v, μΩ, Ω] using hEq_v
    have hsource_cancel :
        ∫ z, source_u z ∂μΩ + ∫ z, source_v z ∂μΩ = 0 := by
      calc
        ∫ z, source_u z ∂μΩ + ∫ z, source_v z ∂μΩ
            = ∫ z, source_u z + source_v z ∂μΩ := by
                rw [integral_add hsource_u' hsource_v']
        _ = ∫ z, (0 : ℝ) ∂μΩ := by
              congr 1
              ext z
              simp [source_u, source_v]
        _ = 0 := by simp
    refine ⟨?_, ?_⟩
    · simpa [grad_sum, μΩ, Ω] using hgrad_sum_int
    · calc
        ∫ z in surfaceChartRegion e U,
            surfaceMetricWeakGradientCoordinatePairingInChart g e z
              ((du + dv) (e.symm z))
              (fderiv ℝ (η : ℂ → ℝ) z) *
                surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume
            = ∫ z, grad_sum z ∂μΩ := rfl
        _ = ∫ z, grad_u z ∂μΩ + ∫ z, grad_v z ∂μΩ := by
              simpa [hgrad_sum_eq] using
                integral_add hgrad_u' hgrad_v'
        _ = -∫ z, source_u z ∂μΩ + -∫ z, source_v z ∂μΩ := by
              rw [hEq_u', hEq_v']
        _ = 0 := by
              calc
                -∫ z, source_u z ∂μΩ + -∫ z, source_v z ∂μΩ
                    = -(∫ z, source_u z ∂μΩ + ∫ z, source_v z ∂μΩ) := by ring
                _ = 0 := by simp [hsource_cancel]

/--
%%handwave
name:
  Source cancellation gives harmonicity
statement:
  On a conformal surface, if two locally Sobolev functions have cancelling
  weak Laplace-Beltrami sources, then their sum is harmonic.
proof:
  The cancellation statement first gives weak harmonicity of the sum.  Weyl's
  lemma then upgrades weak harmonicity to coordinate harmonicity.
-/
theorem weyl_harmonicOnSurface_of_source_cancellation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel 1 X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X}
    {u v F : X → ℝ}
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (hu :
      IsWeakLaplaceBeltramiSourceOnSurface g U u F)
    (hv :
      IsWeakLaplaceBeltramiSourceOnSurface g U v (fun x ↦ -F x))
    (hpointwise :
      HasPointwiseWeylRepresentativesInCharts U (fun x ↦ u x + v x)) :
    IsHarmonicOnSurface U (fun x ↦ u x + v x) :=
  weyl_harmonicOnSurface_of_weaklyHarmonicOnSurface hconformal
    (weaklyHarmonicOnSurface_of_source_cancellation hu hv)
    hpointwise

end Uniformization

end JJMath
