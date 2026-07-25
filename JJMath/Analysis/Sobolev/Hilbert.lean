import JJMath.Analysis.Sobolev.Bundle
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.VectorBundle.Constructions

/-!
# Hilbert structure for surface Sobolev spaces

This file records the Hilbert-space input for the representative-level
\(W^{1,2}\) spaces and their zero-trace subspace.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff Bundle

namespace Uniformization

noncomputable section


/--
%%handwave
name:
  The zero section is square-integrable
statement:
  The zero section of a continuous Hilbert bundle is square-integrable.
proof:
  The zero total-space section is measurable, its fiberwise square norm is identically zero, and the zero function is integrable.
-/
theorem hilbertBundleSectionMemL2_zero
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) :
    HilbertBundleSectionMemL2 G μ (0 : HilbertBundleSectionOnSurface X V) := by
  refine ⟨?_, ?_⟩
  · change AEMeasurable (Bundle.zeroSection F V) μ
    exact (Bundle.contMDiff_zeroSection (𝕜 := ℝ)
      (IB := I) (F := F) (E := V) (n := 1)).continuous.aemeasurable
  · have hzero :
        (fun x : X ↦ G.fiberNormSq x ((0 : HilbertBundleSectionOnSurface X V) x)) =
          fun _ : X ↦ (0 : ℝ) := by
      funext x
      rw [G.fiberNormSq_eq_inner, hG_inner]
      simp
    rw [hzero]
    exact integrable_zero X ℝ μ

/--
%%handwave
name:
  Square \(L^2\)-norm of a bundle section
statement:
  The square \(L^2\)-norm of a square-integrable section is the integral over
  the base of the fiberwise square norm.
-/
noncomputable def squareIntegrableHilbertBundleSectionL2NormSq
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (s : SquareIntegrableHilbertBundleSection G μ) : ℝ :=
  ∫ x, G.fiberNormSq x (s.toSection x) ∂μ

/--
%%handwave
name:
  \(L^2\)-norm of a bundle section
statement:
  The \(L^2\)-norm of a square-integrable section is the square root of its
  integrated fiberwise square norm.
-/
noncomputable def squareIntegrableHilbertBundleSectionL2Norm
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (s : SquareIntegrableHilbertBundleSection G μ) : ℝ :=
  Real.sqrt (squareIntegrableHilbertBundleSectionL2NormSq G μ s)

/--
%%handwave
name:
  Bundle \(L^2\)-norm as a scalar \(L^2\)-norm
statement:
  The \(L^2\)-norm of a square-integrable Hilbert-bundle section is the scalar
  \(L^2\)-norm of its pointwise fiber norm.
proof:
  Rewrite the fiberwise square norm as the square of the ordinary norm and compare the defining integral formulas for the two real norms.
-/
theorem squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : SquareIntegrableHilbertBundleSection G μ) :
    squareIntegrableHilbertBundleSectionL2Norm G μ s =
      lpNorm (fun x : X ↦ ‖s.toSection x‖) 2 μ := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  have hnorm_ae :
      (fun x : X ↦ √(G.fiberNormSq x (s.toSection x))) =ᵐ[μ]
        fun x : X ↦ ‖s.toSection x‖ := by
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x), Real.sqrt_sq (norm_nonneg _)]
  have hnorm_aestr :
      AEStronglyMeasurable (fun x : X ↦ ‖s.toSection x‖) μ := by
    have hsqrt_aestr :
        AEStronglyMeasurable (fun x : X ↦ √(G.fiberNormSq x (s.toSection x))) μ :=
      (s.memL2.integrable_normSq.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
    exact (aestronglyMeasurable_congr hnorm_ae).1 hsqrt_aestr
  unfold squareIntegrableHilbertBundleSectionL2Norm
  unfold squareIntegrableHilbertBundleSectionL2NormSq
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hnorm_aestr]
  have hint_eq :
      ∫ x, G.fiberNormSq x (s.toSection x) ∂μ =
        ∫ x, ‖(‖s.toSection x‖ : ℝ)‖ ^ (2 : ℝ≥0∞).toReal ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x)]
    simp
  rw [hint_eq, Real.sqrt_eq_rpow]
  norm_num

/--
%%handwave
name:
  Pointwise norms of square-integrable sections are square-integrable
statement:
  The pointwise fiber norm of a square-integrable Hilbert-bundle section is a
  scalar \(L^2\)-function.
proof:
  Strong measurability follows from the measurable bundle section and continuity of the norm; integrability of its square is precisely the bundle square-integrability assumption.
-/
theorem squareIntegrableHilbertBundleSection_norm_memLp
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : SquareIntegrableHilbertBundleSection G μ) :
    MemLp (fun x : X ↦ ‖s.toSection x‖) 2 μ := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  have hnorm_ae :
      (fun x : X ↦ √(G.fiberNormSq x (s.toSection x))) =ᵐ[μ]
        fun x : X ↦ ‖s.toSection x‖ := by
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x), Real.sqrt_sq (norm_nonneg _)]
  have hnorm_aestr :
      AEStronglyMeasurable (fun x : X ↦ ‖s.toSection x‖) μ := by
    have hsqrt_aestr :
        AEStronglyMeasurable
          (fun x : X ↦ √(G.fiberNormSq x (s.toSection x))) μ :=
      (s.memL2.integrable_normSq.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
    exact (aestronglyMeasurable_congr hnorm_ae).1 hsqrt_aestr
  have hnorm_sq_int :
      Integrable (fun x : X ↦ ‖s.toSection x‖ ^ 2) μ := by
    refine s.memL2.integrable_normSq.congr ?_
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x)]
  exact (memLp_two_iff_integrable_sq hnorm_aestr).2 hnorm_sq_int

/--
%%handwave
name:
  Extended norm of the pointwise fiber norm
statement:
  For a square-integrable bundle section \(s\), the extended \(L^2\)-norm of \(x\mapsto\|s(x)\|_x\) is the finite extended-real image of its real \(L^2\)-norm.
proof:
  Square both quantities, identify both with the integral of the fiberwise square norm, and use nonnegativity to take square roots.
-/
private theorem squareIntegrableHilbertBundleSection_eLpNorm_norm_eq_ofReal_l2Norm
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : SquareIntegrableHilbertBundleSection G μ) :
    eLpNorm (fun x : X ↦ ‖s.toSection x‖) 2 μ =
      ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ s) := by
  have hs_memLp :
      MemLp (fun x : X ↦ ‖s.toSection x‖) 2 μ :=
    squareIntegrableHilbertBundleSection_norm_memLp (I := I) (G := G) hG_inner μ s
  rw [← MeasureTheory.ofReal_lpNorm hs_memLp]
  congr 1
  exact (squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
            (I := I) (G := G) hG_inner μ s).symm



/--
%%handwave
name:
  Removing a density bounded below
statement:
  Let \(K\) be measurable and suppose \(0<c\le\delta\) almost everywhere on \(K\), with \(c<\infty\).  If \(f\in L^p((\delta\,d\nu)|_K)\), then \(f\in L^p(\nu|_K)\).
proof:
  The density bound gives \(\nu|_K\le c^{-1}(\delta\,d\nu)|_K\); monotonicity of \(L^p\)-membership under a bounded measure comparison proves the claim.
-/
private theorem memLp_of_withDensity_lower_bound_on_restrict
    {α E : Type} [MeasurableSpace α] [TopologicalSpace E] [ContinuousENorm E]
    {ν : Measure α} {δ : α → ℝ≥0∞} {K : Set α} {c : ℝ≥0∞}
    (hK : MeasurableSet K) (hc0 : c ≠ 0) (hctop : c ≠ (⊤ : ℝ≥0∞))
    (hδ : ∀ᵐ x ∂ν.restrict K, c ≤ δ x)
    {f : α → E} {p : ℝ≥0∞}
    (hf : MemLp f p ((ν.withDensity δ).restrict K)) :
    MemLp f p (ν.restrict K) := by
  have hweighted_eq : (ν.withDensity δ).restrict K = (ν.restrict K).withDensity δ :=
    restrict_withDensity hK δ
  have hconst_le : c • ν.restrict K ≤ (ν.withDensity δ).restrict K := by
    rw [hweighted_eq, ← withDensity_const (μ := ν.restrict K) c]
    exact withDensity_mono hδ
  have hmeasure_le : ν.restrict K ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
    calc
      ν.restrict K = (1 : ℝ≥0∞) • ν.restrict K := by simp
      _ = (c⁻¹ * c) • ν.restrict K := by
            rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = c⁻¹ • (c • ν.restrict K) := by rw [smul_smul]
      _ ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
            apply Measure.le_iff.2
            intro s hs
            rw [Measure.smul_apply, Measure.smul_apply]
            exact mul_le_mul_right (Measure.le_iff.1 hconst_le s hs) _

  exact hf.of_measure_le_smul (by simpa [ENNReal.inv_ne_top] using hc0) hmeasure_le

/--
%%handwave
name:
  \(L^2\)-norm comparison under a density lower bound
statement:
  If \(0<c\le\delta\) almost everywhere on a measurable \(K\), then
  \[
    \|f\|_{L^2(\nu|_K)}\le c^{-1/2}\|f\|_{L^2((\delta\,d\nu)|_K)}.
  \]
proof:
  Use the measure inequality \(\nu|_K\le c^{-1}(\delta\,d\nu)|_K\) and the scaling formula for the extended \(L^2\)-norm.
-/
private theorem eLpNorm_two_of_withDensity_lower_bound_on_restrict_le
    {α E : Type} [MeasurableSpace α] [TopologicalSpace E] [ContinuousENorm E]
    {ν : Measure α} {δ : α → ℝ≥0∞} {K : Set α} {c : ℝ≥0∞}
    (hK : MeasurableSet K) (hc0 : c ≠ 0) (hctop : c ≠ (⊤ : ℝ≥0∞))
    (hδ : ∀ᵐ x ∂ν.restrict K, c ≤ δ x)
    (f : α → E) :
    eLpNorm f 2 (ν.restrict K) ≤
      c⁻¹ ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 ((ν.withDensity δ).restrict K) := by
  have hweighted_eq : (ν.withDensity δ).restrict K = (ν.restrict K).withDensity δ :=
    restrict_withDensity hK δ
  have hconst_le : c • ν.restrict K ≤ (ν.withDensity δ).restrict K := by
    rw [hweighted_eq, ← withDensity_const (μ := ν.restrict K) c]
    exact withDensity_mono hδ
  have hmeasure_le : ν.restrict K ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
    calc
      ν.restrict K = (1 : ℝ≥0∞) • ν.restrict K := by simp
      _ = (c⁻¹ * c) • ν.restrict K := by
            rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = c⁻¹ • (c • ν.restrict K) := by rw [smul_smul]
      _ ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
            apply Measure.le_iff.2
            intro s hs
            rw [Measure.smul_apply, Measure.smul_apply]
            exact mul_le_mul_right (Measure.le_iff.1 hconst_le s hs) _
  calc
    eLpNorm f 2 (ν.restrict K) ≤
        eLpNorm f 2 (c⁻¹ • ((ν.withDensity δ).restrict K)) :=
      eLpNorm_mono_measure f hmeasure_le
    _ = c⁻¹ ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 ((ν.withDensity δ).restrict K) := by
          rw [eLpNorm_smul_measure_of_ne_zero]
          · rfl
          · exact ENNReal.inv_ne_zero.2 hctop

/--
%%handwave
name:
  Almost-everywhere measurability of an inverse chart
statement:
  For a smooth positive manifold measure, the inverse chart is almost everywhere measurable with respect to the chart pushforward measure.
proof:
  The inverse chart is measurable for restricted Lebesgue measure, and the chart pushforward is absolutely continuous with respect to that measure.
-/
private theorem smoothPositiveMeasureOnManifold_chart_symm_aemeasurable
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
  rcases hμ.chart_density e he with ⟨_ρ, _hρ_smooth, _hρ_pos, hmap⟩
  have hsymm_vol :
      AEMeasurable e.symm (MeasureTheory.volume.restrict e.target) :=
    openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume
  have h_ac :
      Measure.map e (μ.restrict e.source) ≪
        MeasureTheory.volume.restrict e.target := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _
  exact hsymm_vol.mono_ac h_ac

/--
%%handwave
name:
  Pushing a chart measure back through the inverse chart
statement:
  For a chart (e), pushing (e_ast\(mu|_{\mathrm{source}}\)) forward by (e^{-1}) recovers \(mu|_{\mathrm{source}}\).
proof:
  Compose the two almost-everywhere measurable maps and use the chart left-inverse identity on the source.
-/
private theorem smoothPositiveMeasureOnManifold_chart_map_symm_map
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
      μ.restrict e.source := by
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) :=
    smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap :
      Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
        Measure.map (fun x : X ↦ e.symm (e x)) (μ.restrict e.source) := by
    simpa [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable hsymm_aemeas he_aemeas)
  have hleft :
      (fun x : X ↦ e.symm (e x)) =ᵐ[μ.restrict e.source] fun x ↦ x :=
    ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦
      e.left_inv hx
  calc
    Measure.map e.symm (Measure.map e (μ.restrict e.source))
        = Measure.map (fun x : X ↦ e.symm (e x)) (μ.restrict e.source) := hmap
    _ = Measure.map (fun x : X ↦ x) (μ.restrict e.source) :=
        Measure.map_congr hleft
    _ = μ.restrict e.source := by rw [Measure.map_id']

/--
%%handwave
name:
  Lebesgue measure is dominated by a smooth positive chart measure
statement:
  On a chart target, restricted Lebesgue measure is absolutely continuous with respect to the pushforward of a smooth positive manifold measure.
proof:
  The pushforward has a smooth strictly positive density relative to Lebesgue measure, so every set null for it is Lebesgue-null.
-/
private theorem smoothPositiveMeasureOnManifold_chart_volume_ac_map
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    MeasureTheory.volume.restrict e.target ≪
      Measure.map e (μ.restrict e.source) := by
  obtain ⟨ρ, hρ_smooth, hρ_pos, hmap⟩ := hμ.chart_density e he
  rw [hmap]
  have hρ_aemeas :
      AEMeasurable (fun z : H ↦ ENNReal.ofReal (ρ z))
        (MeasureTheory.volume.restrict e.target) := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hρ_smooth.continuousOn.aemeasurable e.open_target.measurableSet)
  have hρ_ne_zero :
      ∀ᵐ z ∂MeasureTheory.volume.restrict e.target,
        ENNReal.ofReal (ρ z) ≠ 0 := by
    exact ae_restrict_of_forall_mem e.open_target.measurableSet fun z hz ↦
      ne_of_gt (ENNReal.ofReal_pos.mpr (hρ_pos z hz))
  exact withDensity_absolutelyContinuous' hρ_aemeas hρ_ne_zero

/--
%%handwave
name:
  Strong measurability of a chart pullback
statement:
  If (f) is almost everywhere strongly measurable on the manifold and (K) lies in a chart target, then \(f\circ e^{-1}\) is almost everywhere strongly measurable for Lebesgue measure restricted to (K).
proof:
  Pull strong measurability through the inverse chart for the chart measure, transfer it by absolute continuity to Lebesgue measure, and restrict to (K).
-/
private theorem smoothPositiveMeasureOnManifold_chartPullback_aestronglyMeasurable
    {H X β : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace β]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (K : Set H) (hK : K ⊆ e.target) {f : X → β}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun z : H ↦ f (e.symm z))
      (MeasureTheory.volume.restrict K) := by
  let ν : Measure H := Measure.map e (μ.restrict e.source)
  have hf_source : AEStronglyMeasurable f (μ.restrict e.source) := hf.restrict
  have hsymm : AEMeasurable e.symm ν := by
    simpa [ν] using
      smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap_symm : Measure.map e.symm ν = μ.restrict e.source := by
    simpa [ν] using
      smoothPositiveMeasureOnManifold_chart_map_symm_map μ hμ e he
  have hpull_ν : AEStronglyMeasurable (fun z : H ↦ f (e.symm z)) ν := by
    have hf_map : AEStronglyMeasurable f (Measure.map e.symm ν) := by
      simpa [hmap_symm] using hf_source
    simpa [Function.comp_def] using hf_map.comp_aemeasurable hsymm
  have hvol_ac : MeasureTheory.volume.restrict e.target ≪ ν := by
    simpa [ν] using
      smoothPositiveMeasureOnManifold_chart_volume_ac_map μ hμ e he
  have hpull_target :
      AEStronglyMeasurable (fun z : H ↦ f (e.symm z))
        (MeasureTheory.volume.restrict e.target) :=
    MeasureTheory.AEStronglyMeasurable.mono_ac hvol_ac hpull_ν
  exact hpull_target.mono_measure (Measure.restrict_mono hK le_rfl)

/--
%%handwave
name:
  Local \(L^2\) integrability of chart pullbacks
statement:
  If (f\in L^2(mu)) and (K) is compactly contained in a chart region, then (f\circ e^{-1}in L^2(K,dx)).
proof:
  The smooth positive chart density has a positive minimum on (K); remove that density using the resulting lower bound and the chart change-of-variables formula.
-/
private theorem smoothPositiveMeasureOnManifold_chartPullback_memLp_two_restrict_compact
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold I 1 X]
    [TopologicalSpace F] [ContinuousENorm F]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (K : Set H) (hK_region : K ⊆ manifoldChartRegion e (Set.univ : Set X))
    (hK_compact : IsCompact K) {f : X → F} (hf : MemLp f 2 μ) :
    MemLp (fun z : H ↦ f (e.symm z)) 2 (MeasureTheory.volume.restrict K) := by
  classical
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hK_target : K ⊆ e.target := by
    intro z hz
    exact (hK_region hz).1
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  rcases K.eq_empty_or_nonempty with hK_empty | hK_nonempty
  · have hzero : MeasureTheory.volume.restrict K = 0 := by
      simp [hK_empty]
    rw [hzero]
    exact memLp_measure_zero
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases hK_compact.exists_sInf_image_eq_and_le hK_nonempty hρ_cont_K with
    ⟨z₀, hz₀K, _hz₀_inf, hz₀_min⟩
  let c : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  have hc_pos : 0 < ρ z₀ := hρ_pos z₀ (hK_target hz₀K)
  have hc0 : c ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc_pos)
  have hctop : c ≠ (⊤ : ℝ≥0∞) := by
    simp [c]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K, c ≤ δ z := by
    filter_upwards [ae_restrict_mem hK_meas] with z hzK
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK)
  let μs : Measure X := μ.restrict e.source
  let Fpull : H → F := fun z ↦ f (e.symm z)
  have he_aemeas : AEMeasurable e μs := by
    simpa [μs] using openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μs) := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e μs) = μs := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_map_symm_map μ hμ e he
  have hf_source : MemLp f 2 μs := by
    simpa [μs] using hf.restrict e.source
  have hf_aestr_source : AEStronglyMeasurable f μs := by
    simpa [μs] using hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hf_aestr_map_symm :
      AEStronglyMeasurable f (Measure.map e.symm (Measure.map e μs)) := by
    simpa [hmap_symm] using hf_aestr_source
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μs) := by
    simpa [Fpull, Function.comp_def] using
      hf_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hcomp_eq :
      (fun x : X ↦ Fpull (e x)) =ᵐ[μs] f := by
    filter_upwards [show ∀ᵐ x ∂μs, x ∈ e.source from by
      simpa [μs] using
        (ae_restrict_mem e.open_source.measurableSet :
          ∀ᵐ x ∂μ.restrict e.source, x ∈ e.source)] with x hx_source
    simp [Fpull, e.left_inv hx_source]
  have hcomp_mem : MemLp (fun x : X ↦ Fpull (e x)) 2 μs :=
    (memLp_congr_ae hcomp_eq).2 hf_source
  have hF_map : MemLp Fpull 2 (Measure.map e μs) :=
    (memLp_map_measure_iff hFpull_aestr he_aemeas).2 hcomp_mem
  have hF_weighted : MemLp Fpull 2 (ν.withDensity δ) := by
    simpa [ν, δ, μs, hmap] using hF_map
  have hF_weighted_K : MemLp Fpull 2 ((ν.withDensity δ).restrict K) :=
    hF_weighted.restrict K
  have hF_νK : MemLp Fpull 2 (ν.restrict K) :=
    memLp_of_withDensity_lower_bound_on_restrict
      (ν := ν) (δ := δ) (K := K) (c := c)
      hK_meas hc0 hctop hδ_lower hF_weighted_K
  simpa [Fpull, ν, Measure.restrict_restrict_of_subset hK_target] using hF_νK

/--
%%handwave
name:
  Uniform local chart pullback estimate
statement:
  For a compact \(K\) in a chart region there is \(C<\infty\) such that
  \[
    \|f\circ e^{-1}\|_{L^2(K,dx)}\le C\|f\|_{L^2\(\mu\)}
  \]
  for every almost everywhere strongly measurable \(f\).
proof:
  Take the positive minimum of the smooth chart density on (K), apply the density norm comparison, and use change of variables plus restriction monotonicity.
-/
private theorem smoothPositiveMeasureOnManifold_chartPullback_eLpNorm_two_restrict_compact_le
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold I 1 X]
    [TopologicalSpace F] [ContinuousENorm F]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (K : Set H) (hK_region : K ⊆ manifoldChartRegion e (Set.univ : Set X))
    (hK_compact : IsCompact K) :
    ∃ C : NNReal,
      ∀ f : X → F, AEStronglyMeasurable f μ →
        eLpNorm (fun z : H ↦ f (e.symm z)) 2
            (MeasureTheory.volume.restrict K) ≤
          (C : ℝ≥0∞) * eLpNorm f 2 μ := by
  classical
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hK_target : K ⊆ e.target := by
    intro z hz
    exact (hK_region hz).1
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  rcases K.eq_empty_or_nonempty with hK_empty | hK_nonempty
  · refine ⟨0, ?_⟩
    intro f hf
    have hzero : MeasureTheory.volume.restrict K = 0 := by
      simp [hK_empty]
    simp [hzero]
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases hK_compact.exists_sInf_image_eq_and_le hK_nonempty hρ_cont_K with
    ⟨z₀, hz₀K, _hz₀_inf, hz₀_min⟩
  let c : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  let Cₑ : ℝ≥0∞ := c⁻¹ ^ q
  have hc_pos : 0 < ρ z₀ := hρ_pos z₀ (hK_target hz₀K)
  have hc0 : c ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc_pos)
  have hctop : c ≠ (⊤ : ℝ≥0∞) := by
    simp [c]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K, c ≤ δ z := by
    filter_upwards [ae_restrict_mem hK_meas] with z hzK
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK)
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hCₑ_ne_top : Cₑ ≠ (⊤ : ℝ≥0∞) := by
    exact (ENNReal.rpow_lt_top_of_nonneg hq_nonneg
      (by simpa using (ENNReal.inv_ne_top.2 hc0))).ne
  refine ⟨Cₑ.toNNReal, ?_⟩
  intro f hf_aestr
  let μs : Measure X := μ.restrict e.source
  let Fpull : H → F := fun z ↦ f (e.symm z)
  have he_aemeas : AEMeasurable e μs := by
    simpa [μs] using openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μs) := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e μs) = μs := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_map_symm_map μ hμ e he
  have hf_aestr_source : AEStronglyMeasurable f μs := by
    simpa [μs] using hf_aestr.mono_measure Measure.restrict_le_self
  have hf_aestr_map_symm :
      AEStronglyMeasurable f (Measure.map e.symm (Measure.map e μs)) := by
    simpa [hmap_symm] using hf_aestr_source
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μs) := by
    simpa [Fpull, Function.comp_def] using
      hf_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hweighted_full :
      eLpNorm Fpull 2 (ν.withDensity δ) = eLpNorm f 2 μs := by
    calc
      eLpNorm Fpull 2 (ν.withDensity δ)
          = eLpNorm Fpull 2 (Measure.map e μs) := by
              simp [ν, δ, μs, hmap]
      _ = eLpNorm (fun x : X ↦ Fpull (e x)) 2 μs := by
              exact eLpNorm_map_measure hFpull_aestr he_aemeas
      _ = eLpNorm f 2 μs := by
              apply eLpNorm_congr_ae
              filter_upwards [show ∀ᵐ x ∂μs, x ∈ e.source from by
                simpa [μs] using
                  (ae_restrict_mem e.open_source.measurableSet :
                    ∀ᵐ x ∂μ.restrict e.source, x ∈ e.source)] with x hx_source
              simp [Fpull, e.left_inv hx_source]
  have hrestrict_le :
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict K) ≤
        eLpNorm Fpull 2 (ν.withDensity δ) :=
    eLpNorm_mono_measure Fpull Measure.restrict_le_self
  have hsource_le :
      eLpNorm f 2 μs ≤ eLpNorm f 2 μ :=
    eLpNorm_mono_measure f Measure.restrict_le_self
  have hνK_eq : ν.restrict K = MeasureTheory.volume.restrict K := by
    simpa [ν] using Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume) hK_target
  have hcompare :
      eLpNorm Fpull 2 (ν.restrict K) ≤
        Cₑ * eLpNorm Fpull 2 ((ν.withDensity δ).restrict K) := by
    simpa [Cₑ, q] using
      eLpNorm_two_of_withDensity_lower_bound_on_restrict_le
        (ν := ν) (δ := δ) (K := K) (c := c)
        hK_meas hc0 hctop hδ_lower Fpull
  calc
    eLpNorm (fun z : H ↦ f (e.symm z)) 2
        (MeasureTheory.volume.restrict K)
        = eLpNorm Fpull 2 (ν.restrict K) := by
            simp [Fpull, hνK_eq]
    _ ≤ Cₑ * eLpNorm Fpull 2 ((ν.withDensity δ).restrict K) := hcompare
    _ ≤ Cₑ * eLpNorm Fpull 2 (ν.withDensity δ) :=
        mul_le_mul_right hrestrict_le Cₑ
    _ = Cₑ * eLpNorm f 2 μs := by
        rw [hweighted_full]
    _ ≤ Cₑ * eLpNorm f 2 μ :=
        mul_le_mul_right hsource_le Cₑ
    _ = (Cₑ.toNNReal : ℝ≥0∞) * eLpNorm f 2 μ := by
        rw [ENNReal.coe_toNNReal hCₑ_ne_top]

/--
%%handwave
name:
  Hom-bundle coordinates preserve differential evaluation
statement:
  If a differential fiber is written in a local Hom-bundle trivialization and
  a tangent vector is written in the corresponding tangent-bundle
  trivialization, evaluating in local coordinates agrees with evaluating the
  original differential on the original tangent vector.
proof:
  The Hom-bundle trivialization is induced by the tangent-bundle
  trivialization on the source and the trivial target-bundle trivialization on
  the target.  Therefore applying the transported Hom map to the transported
  tangent vector cancels the two inverse coordinate maps.
-/
theorem manifoldDifferentialBundle_trivialization_eval_eq
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ y : X)
    (hy : y ∈
      (trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).baseSet)
    (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) y)
    (ξ : TangentSpace I y) :
    (((trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀
        ).continuousLinearMapAt ℝ y) A)
      (((trivializationAt H (TangentSpace I : X → Type) x₀
        ).continuousLinearMapAt ℝ y) ξ) =
      A ξ := by
  let eT := trivializationAt H (TangentSpace I : X → Type) x₀
  let eE := trivializationAt E (Bundle.Trivial X E) x₀
  let eD := trivializationAt (H →L[ℝ] E)
    (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀
  have hyTE : y ∈ eT.baseSet ∩ eE.baseSet := by
    simpa [eT, eE, eD, ManifoldDifferentialBundleFiber,
      hom_trivializationAt_baseSet] using hy
  have hyT : y ∈ eT.baseSet := hyTE.1
  have hyD : y ∈ (eT.continuousLinearMap (RingHom.id ℝ) eE).baseSet := by
    simpa [Bundle.Trivialization.baseSet_continuousLinearMap] using hyTE
  change
    ((eT.continuousLinearMap (RingHom.id ℝ) eE).continuousLinearMapAt ℝ y A)
      (eT.continuousLinearMapAt ℝ y ξ) = A ξ
  rw [Bundle.Trivialization.continuousLinearMapAt_apply]
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hyD]
  change
    eE.continuousLinearMapAt ℝ y
      (A (eT.symmL ℝ y (eT.continuousLinearMapAt ℝ y ξ))) = A ξ
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt eT hyT ξ]
  simp [eE]

/--
%%handwave
name:
  Continuity of a coordinate tangent vector in the bundle
statement:
  For a fixed model vector \(u\), the total-space vector \(z\mapsto(e^{-1}(z),D(e^{-1})(z)u)\) is continuous on the chart target.
proof:
  This is the defining continuity of the tangent-bundle chart trivialization applied to the constant coordinate vector (u).
-/
private theorem manifoldChartCoordinateVector_continuousOn_id {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] [IsManifold (𝓘(ℝ, H)) 1 X]
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) (u : H) :
    ContinuousOn
      (fun z : H ↦ (Bundle.TotalSpace.mk' H (e.symm z)
        (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z u) :
          TangentBundle (𝓘(ℝ, H)) X)) e.target := by
  let I : ModelWithCorners ℝ H H := 𝓘(ℝ, H)
  have hsymm : ContMDiffOn I I 1 e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := 1) _he)
  have hbaseVec : ContMDiffOn I I.tangent ∞
      (fun z : H ↦ (⟨z, u⟩ : TangentBundle I H)) e.target := by
    change ContMDiffOn I I.tangent ∞
        ((tangentBundleModelSpaceHomeomorph I).symm ∘
          fun z : H ↦ ((z, u) : ModelProd H H)) e.target
    refine (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := I)).contMDiffOn.comp (t := Set.univ) ?_ ?_
    · rw [← modelWithCornersSelf_prod]
      apply ContDiffOn.contMDiffOn
      fun_prop
    · intro z hz
      simp
  have htangent : ContinuousOn
      (tangentMapWithin I I e.symm e.target)
      (Bundle.TotalSpace.proj ⁻¹' e.target) := by
    exact hsymm.continuousOn_tangentMapWithin (n := 1) (by norm_num)
      e.open_target.uniqueMDiffOn
  have hcomp : ContinuousOn
      ((tangentMapWithin I I e.symm e.target) ∘
        (fun z : H ↦ (⟨z, u⟩ : TangentBundle I H))) e.target := by
    exact htangent.comp hbaseVec.continuousOn
      (fun z hz => by simpa using hz)
  refine hcomp.congr ?_
  intro z hz
  have hmd : MDifferentiableWithinAt I I e.symm e.target z :=
    mdifferentiableOn_atlas_symm (I := I) _he z hz
  simp [tangentMapWithin, manifoldChartTangentVector, mfderivWithin,
    writtenInExtChartAt, I, hmd]
  rfl

/--
%%handwave
name:
  Coordinate tangent vectors are locally bounded in tangent coordinates
statement:
  Near any coordinate point in a chart, a fixed coordinate tangent vector,
  transported to a fixed tangent-bundle trivialization, has bounded model
  norm.
proof:
  In the tangent trivialization centered at the base point, the transported
  coordinate tangent vector is the derivative of the coordinate transition
  from the given chart to the centered chart.  The transition is \(C^1\), so
  this derivative varies continuously and is locally bounded.
-/
theorem manifoldChartTangentVector_in_trivialization_locally_bounded
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) (v : H) :
    ∀ z₀ ∈ manifoldChartRegion e (Set.univ : Set X),
      ∃ U ∈ 𝓝 z₀, ∃ C : NNReal,
        ∀ z ∈ U,
          ‖((trivializationAt H (TangentSpace I : X → Type) (e.symm z₀)
              ).continuousLinearMapAt ℝ (e.symm z))
            (manifoldChartTangentVector (I := I) e z v)‖ ≤ (C : ℝ) := by
  classical
  have hI : I = 𝓘(ℝ, H) :=
    IsIdentityManifoldModel.eq_identity (H := H) (I := I)
  subst I
  intro z₀ hz₀
  rcases hz₀ with ⟨hz₀_target, _hz₀_univ⟩
  let x₀ : X := e.symm z₀
  let eT := trivializationAt H (TangentSpace (𝓘(ℝ, H)) : X → Type) x₀
  let F : H → TangentBundle (𝓘(ℝ, H)) X := fun z ↦
    (Bundle.TotalSpace.mk' H (e.symm z)
      (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v) :
      TangentBundle (𝓘(ℝ, H)) X)
  let f : H → H := fun z ↦ (eT (F z)).2
  have hF_contOn : ContinuousOn F e.target := by
    simpa [F] using
      manifoldChartCoordinateVector_continuousOn_id (X := X) e _he v
  have hF_contAt : ContinuousAt F z₀ :=
    hF_contOn.continuousAt (e.open_target.mem_nhds hz₀_target)
  have hx₀T : x₀ ∈ eT.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have hFz₀_source : F z₀ ∈ eT.source := by
    rw [eT.mem_source]
    simpa [F, x₀] using hx₀T
  have heT_contAt : ContinuousAt eT (F z₀) :=
    eT.continuousOn.continuousAt (eT.open_source.mem_nhds hFz₀_source)
  have hf_contAt : ContinuousAt f z₀ := by
    exact continuous_snd.continuousAt.comp (heT_contAt.comp hF_contAt)
  have hbase_event :
      ∀ᶠ z in 𝓝 z₀, e.symm z ∈ eT.baseSet := by
    exact (e.symm.continuousAt hz₀_target).preimage_mem_nhds
      (eT.open_baseSet.mem_nhds hx₀T)
  have hnorm_event :
      ∀ᶠ z in 𝓝 z₀, ‖f z‖ < ‖f z₀‖ + 1 := by
    exact hf_contAt.norm.preimage_mem_nhds
      (Iio_mem_nhds (by linarith [norm_nonneg (f z₀)]))
  let U : Set H :=
    {z : H | e.symm z ∈ eT.baseSet} ∩
      {z : H | ‖f z‖ < ‖f z₀‖ + 1}
  have hU : U ∈ 𝓝 z₀ := Filter.inter_mem hbase_event hnorm_event
  refine ⟨U, hU, ⟨‖f z₀‖ + 1, by positivity⟩, ?_⟩
  intro z hz
  have hzbase : e.symm z ∈ eT.baseSet := hz.1
  have hzbound : ‖f z‖ < ‖f z₀‖ + 1 := hz.2
  have hlin :
      eT.continuousLinearMapAt ℝ (e.symm z)
        (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v) = f z := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply]
    rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hzbase]
  rw [hlin]
  exact le_of_lt hzbound

/--
%%handwave
name:
  Coordinate evaluation is locally bounded
statement:
  Around each point in a coordinate chart, evaluation of a vector-valued
  differential on a fixed coordinate tangent direction is bounded by a local
  constant times the Hilbert--Schmidt fiber norm.
proof:
  In local bundle coordinates, the differential fiber norm is locally
  equivalent to the model Hilbert--Schmidt norm, and the coordinate tangent
  vector has locally bounded model coordinates.  Model evaluation is a
  continuous bilinear map, so these two local bounds give the estimate.
-/
theorem manifoldDifferentialCoordinateEvaluation_locally_pointwise_norm_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X)
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) (v : H) :
    ∀ z₀ ∈ manifoldChartRegion e (Set.univ : Set X),
      ∃ U ∈ 𝓝 z₀, ∃ C : NNReal,
        ∀ z ∈ U,
          ∀ A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z),
            ‖A (manifoldChartTangentVector (I := I) e z v)‖ ≤
              (C : ℝ) *
                Real.sqrt
                  ((manifoldDifferentialHilbertBundleGeometry
                    (I := I) (X := X) (E := E) g).fiberNormSq (e.symm z) A) := by
  classical
  intro z₀ hz₀
  rcases hz₀ with ⟨hz₀_target, _hz₀_univ⟩
  let x₀ : X := e.symm z₀
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := E) g
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  have hG_inner :
      ∀ (x : X)
        (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        G.fiberInner x A B = inner ℝ A B := by
    intro x A B
    rfl
  have hsqrt_eq :
      ∀ (x : X)
        (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        Real.sqrt (G.fiberNormSq x A) = ‖A‖ := by
    intro x A
    have hnormsq : G.fiberNormSq x A = ‖A‖ ^ 2 := by
      rw [G.fiberNormSq_eq_inner, hG_inner]
      exact real_inner_self_eq_norm_sq A
    rw [hnormsq, Real.sqrt_sq (norm_nonneg _)]
  let eD :=
    trivializationAt (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀
  let eT := trivializationAt H (TangentSpace I : X → Type) x₀
  rcases eventually_norm_trivializationAt_lt
      (F := H →L[ℝ] E)
      (E := ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀ with
    ⟨CD, hCD_pos, hD_event⟩
  have hx₀D : x₀ ∈ eD.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have hD_event_z :
      ∀ᶠ z in 𝓝 z₀, ‖eD.continuousLinearMapAt ℝ (e.symm z)‖ < CD := by
    exact (e.symm.continuousAt hz₀_target).eventually hD_event
  have hD_base_z :
      ∀ᶠ z in 𝓝 z₀, e.symm z ∈ eD.baseSet := by
    exact (e.symm.continuousAt hz₀_target).eventually
      (eD.open_baseSet.mem_nhds hx₀D)
  rcases manifoldChartTangentVector_in_trivialization_locally_bounded
      (I := I) (X := X) e _he v z₀ ⟨hz₀_target, trivial⟩ with
    ⟨UT, hUT, CT, hCT⟩
  let U : Set H :=
    {z : H | ‖eD.continuousLinearMapAt ℝ (e.symm z)‖ < CD} ∩
      {z : H | e.symm z ∈ eD.baseSet} ∩ UT
  have hU : U ∈ 𝓝 z₀ := by
    exact Filter.inter_mem (Filter.inter_mem hD_event_z hD_base_z) hUT
  refine ⟨U, hU, ⟨CD * (CT : ℝ), mul_nonneg hCD_pos.le CT.2⟩, ?_⟩
  intro z hz A
  have hDlt : ‖eD.continuousLinearMapAt ℝ (e.symm z)‖ < CD := hz.1.1
  have hyD : e.symm z ∈ eD.baseSet := hz.1.2
  have hTbound :
      ‖(eT.continuousLinearMapAt ℝ (e.symm z))
          (manifoldChartTangentVector (I := I) e z v)‖ ≤ (CT : ℝ) := by
    simpa [eT, x₀] using hCT z hz.2
  let ξ : TangentSpace I (e.symm z) :=
    manifoldChartTangentVector (I := I) e z v
  let D :
      ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z) →L[ℝ]
        (H →L[ℝ] E) :=
    eD.continuousLinearMapAt ℝ (e.symm z)
  let η : H := eT.continuousLinearMapAt ℝ (e.symm z) ξ
  have heval :
      (D A) η = A ξ := by
    simpa [D, η, ξ, eD, eT, x₀] using
      manifoldDifferentialBundle_trivialization_eval_eq
        (I := I) (X := X) (E := E) x₀ (e.symm z) hyD A ξ
  have hmain : ‖A ξ‖ ≤ (CD * (CT : ℝ)) * ‖A‖ := by
    calc
      ‖A ξ‖ = ‖(D A) η‖ := by rw [heval]
      _ ≤ ‖D A‖ * ‖η‖ := (D A).le_opNorm η
      _ ≤ (‖D‖ * ‖A‖) * ‖η‖ := by
        gcongr
        exact D.le_opNorm A
      _ ≤ (CD * ‖A‖) * ‖η‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hDlt.le (norm_nonneg A))
          (norm_nonneg η)
      _ ≤ (CD * ‖A‖) * (CT : ℝ) := by
        exact mul_le_mul_of_nonneg_left hTbound
          (mul_nonneg hCD_pos.le (norm_nonneg A))
      _ = (CD * (CT : ℝ)) * ‖A‖ := by ring
  change ‖A ξ‖ ≤ (CD * (CT : ℝ)) * Real.sqrt (G.fiberNormSq (e.symm z) A)
  simpa [hsqrt_eq] using hmain

/--
%%handwave
name:
  Compact coordinate evaluation is pointwise controlled
statement:
  On a compact coordinate support, evaluation of a vector-valued differential
  on a fixed coordinate tangent direction is bounded pointwise by a uniform
  constant times the Hilbert--Schmidt fiber norm.
proof:
  Fiberwise, evaluation on a tangent vector is bounded by the
  Hilbert--Schmidt norm times the length of that tangent vector.  In a fixed
  chart, the coordinate tangent vector and the Riemannian metric vary
  continuously, so this length is bounded on compact subsets of the chart.
-/
theorem manifoldDifferentialCompactEvaluation_pointwise_norm_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (K : Set H) (v : H),
      K ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact K →
      ∃ C : NNReal,
        ∀ z ∈ K,
          ∀ A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z),
            ‖A (manifoldChartTangentVector (I := I) e z v)‖ ≤
              (C : ℝ) *
                Real.sqrt
                  ((manifoldDifferentialHilbertBundleGeometry
                    (I := I) (X := X) (E := E) g).fiberNormSq (e.symm z) A) := by
  classical
  intro e he K v hK_region hK_compact
  have hlocal :
      ∀ z ∈ K,
        ∃ U ∈ 𝓝 z, ∃ C : NNReal,
          ∀ z' ∈ U,
            ∀ A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z'),
              ‖A (manifoldChartTangentVector (I := I) e z' v)‖ ≤
                (C : ℝ) *
                  Real.sqrt
                    ((manifoldDifferentialHilbertBundleGeometry
                      (I := I) (X := X) (E := E) g).fiberNormSq (e.symm z') A) := by
    intro z hz
    exact manifoldDifferentialCoordinateEvaluation_locally_pointwise_norm_le
      (I := I) (X := X) (E := E) g e he v z (hK_region hz)
  choose U hU C hC using hlocal
  rcases hK_compact.elim_nhds_subcover' U hU with ⟨t, hcover⟩
  let Cmax : NNReal := t.sup fun z : K ↦ C z z.2
  refine ⟨Cmax, ?_⟩
  intro z hz A
  rcases Set.mem_iUnion.mp (hcover hz) with ⟨z₀, hz₀⟩
  rcases Set.mem_iUnion.mp hz₀ with ⟨hz₀t, hzU⟩
  have hpoint := hC z₀ z₀.2 z hzU A
  have hC_le : C z₀ z₀.2 ≤ Cmax := by
    exact Finset.le_sup (s := t) (f := fun z : K ↦ C z z.2) hz₀t
  have hC_le_real : ((C z₀ z₀.2 : NNReal) : ℝ) ≤ (Cmax : ℝ) := by
    exact_mod_cast hC_le
  exact hpoint.trans
    (mul_le_mul_of_nonneg_right hC_le_real (Real.sqrt_nonneg _))

/--
%%handwave
name:
  Compact coordinate evaluation is measurable
statement:
  The coordinate evaluation of a square-integrable differential section on a
  fixed chart direction is strongly measurable on every compact coordinate
  support.
proof:
  In local bundle coordinates, the section is measurable, the coordinate
  tangent vector is a measurable tangent-bundle section, and evaluation in the
  Hom bundle is continuous.
-/
theorem manifoldDifferentialCompactEvaluation_aestronglyMeasurable
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (K : Set H) (v : H),
      K ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact K →
      ∀ w : SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ,
        AEStronglyMeasurable
          (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
          (MeasureTheory.volume.restrict K) := by
  classical
  have hI : I = 𝓘(ℝ, H) := IsIdentityManifoldModel.eq_identity (H := H) (I := I)
  subst I
  intro e he K v hK_region hK_compact w
  let totalPull : H → ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E :=
    fun z ↦ HilbertBundleSectionOnSurface.toTotalSpace
      (F := H →L[ℝ] E) w.toSection (e.symm z)
  have hK_target : K ⊆ e.target := fun z hz ↦ (hK_region hz).1
  have htotal_K :
      AEStronglyMeasurable totalPull (MeasureTheory.volume.restrict K) := by
    have htotal_μ :
        AEStronglyMeasurable
          (HilbertBundleSectionOnSurface.toTotalSpace
            (F := H →L[ℝ] E) w.toSection) μ :=
      w.memL2.aemeasurable.aestronglyMeasurable
    simpa [totalPull] using
      smoothPositiveMeasureOnManifold_chartPullback_aestronglyMeasurable
        (I := 𝓘(ℝ, H)) μ _hμ e he K hK_target htotal_μ
  have hlocal :
      ∀ z₀ : K,
        ∃ U ∈ 𝓝 ((z₀ : K) : H), MeasurableSet U ∧
          AEStronglyMeasurable
            (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
            (MeasureTheory.volume.restrict (K ∩ U)) := by
    intro z₀
    let x₀ : X := e.symm ((z₀ : K) : H)
    let eD := trivializationAt (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := 𝓘(ℝ, H)) (X := X) (E := E)) x₀
    let eT := trivializationAt H (TangentSpace (𝓘(ℝ, H)) : X → Type) x₀
    let U : Set H := e.target ∩ e.symm ⁻¹' (eD.baseSet ∩ eT.baseSet)
    have hz₀_target : ((z₀ : K) : H) ∈ e.target := hK_target z₀.2
    have hx₀D : x₀ ∈ eD.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt' x₀
    have hx₀T : x₀ ∈ eT.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt' x₀
    have hz₀U : ((z₀ : K) : H) ∈ U := by
      exact ⟨hz₀_target, by simpa [x₀] using And.intro hx₀D hx₀T⟩
    have hU_open : IsOpen U := by
      simpa [U] using
        e.isOpen_inter_preimage_symm (eD.open_baseSet.inter eT.open_baseSet)
    have hU_meas : MeasurableSet U := hU_open.measurableSet
    let S : Set H := K ∩ U
    have hS_meas : MeasurableSet S := hK_compact.measurableSet.inter hU_meas
    have htotal_S : AEStronglyMeasurable totalPull (MeasureTheory.volume.restrict S) :=
      htotal_K.mono_set (by intro z hz; exact hz.1)
    have hdefault_source : totalPull ((z₀ : K) : H) ∈ eD.source := by
      rw [eD.mem_source]
      simpa [totalPull, x₀] using hx₀D
    let defaultD : eD.source := ⟨totalPull ((z₀ : K) : H), hdefault_source⟩
    let totalDSubtype : H → eD.source := fun z ↦
      if hz : z ∈ S then
        ⟨totalPull z, by
          rw [eD.mem_source]
          simpa [totalPull] using hz.2.2.1⟩
      else defaultD
    have hval_eq :
        (fun z : H ↦
          ((totalDSubtype z : eD.source) :
            ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)) =ᵐ[
              MeasureTheory.volume.restrict S] totalPull := by
      filter_upwards [ae_restrict_mem hS_meas] with z hzS
      simp [totalDSubtype, hzS]
    have hval_aestr :
        AEStronglyMeasurable
          (fun z : H ↦
            ((totalDSubtype z : eD.source) :
              ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E))
          (MeasureTheory.volume.restrict S) :=
      htotal_S.congr hval_eq.symm
    have hsub_aestr :
        AEStronglyMeasurable totalDSubtype (MeasureTheory.volume.restrict S) := by
      have hsubtype :
          Topology.IsEmbedding
            (fun p : eD.source ↦
              ((p : eD.source) :
                ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)) :=
        Topology.IsEmbedding.subtypeVal
      exact hsubtype.aestronglyMeasurable_comp_iff.1 hval_aestr
    let coordD : eD.source → H →L[ℝ] E := fun p ↦
      (eD ((p : eD.source) :
        ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)).2
    have hcoordD_cont : Continuous coordD := by
      have heD_restrict :
          Continuous
            (eD.source.restrict
              (fun p : ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E ↦
                eD p)) :=
        eD.continuousOn.restrict
      exact continuous_snd.comp heD_restrict
    let dcoord : H → H →L[ℝ] E := fun z ↦
      eD.continuousLinearMapAt ℝ (e.symm z) (w.toSection (e.symm z))
    have hD_raw :
        AEStronglyMeasurable
          (fun z : H ↦ coordD (totalDSubtype z))
          (MeasureTheory.volume.restrict S) :=
      hcoordD_cont.comp_aestronglyMeasurable hsub_aestr
    have hDcoord :
        AEStronglyMeasurable dcoord (MeasureTheory.volume.restrict S) := by
      refine hD_raw.congr ?_
      filter_upwards [ae_restrict_mem hS_meas] with z hzS
      have hzD : e.symm z ∈ eD.baseSet := hzS.2.2.1
      simp only [coordD, totalDSubtype, dcoord, totalPull, dif_pos hzS]
      change
        (eD (Bundle.TotalSpace.mk' (H →L[ℝ] E) (e.symm z)
          (w.toSection (e.symm z)))).2 =
          eD.continuousLinearMapAt ℝ (e.symm z) (w.toSection (e.symm z))
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hzD]
    let ξ : (z : H) → TangentSpace (𝓘(ℝ, H)) (e.symm z) := fun z ↦
      manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v
    let F : H → TangentBundle (𝓘(ℝ, H)) X := fun z ↦
      (Bundle.TotalSpace.mk' H (e.symm z) (ξ z) :
        TangentBundle (𝓘(ℝ, H)) X)
    let tcoord : H → H := fun z ↦
      eT.continuousLinearMapAt ℝ (e.symm z) (ξ z)
    have hF_contOn : ContinuousOn F e.target := by
      simpa [F, ξ] using
        manifoldChartCoordinateVector_continuousOn_id (X := X) e he v
    have heT_coord_contOn :
        ContinuousOn
          (fun q : TangentBundle (𝓘(ℝ, H)) X ↦ (eT q).2)
          eT.source := by
      exact continuous_snd.continuousOn.comp eT.continuousOn
        (fun q hq ↦ Set.mem_univ _)
    have hF_maps : Set.MapsTo F U eT.source := by
      intro z hz
      rw [eT.mem_source]
      simpa [F, ξ] using hz.2.2
    have hT_raw_contOn :
        ContinuousOn (fun z : H ↦ (eT (F z)).2) U :=
      heT_coord_contOn.comp (hF_contOn.mono (by intro z hz; exact hz.1)) hF_maps
    have hT_contOn : ContinuousOn tcoord U := by
      refine hT_raw_contOn.congr ?_
      intro z hz
      have hzT : e.symm z ∈ eT.baseSet := hz.2.2
      change
        eT.continuousLinearMapAt ℝ (e.symm z) (ξ z) =
          (eT (Bundle.TotalSpace.mk' H (e.symm z) (ξ z))).2
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hzT]
    have hTcoord :
        AEStronglyMeasurable tcoord (MeasureTheory.volume.restrict S) := by
      exact (hT_contOn.mono (by intro z hz; exact hz.2)).aestronglyMeasurable hS_meas
    let L : (H →L[ℝ] E) →L[ℝ] H →L[ℝ] E :=
      ContinuousLinearMap.flip
        (ContinuousLinearMap.apply ℝ E :
          H →L[ℝ] (H →L[ℝ] E) →L[ℝ] E)
    have happly :
        AEStronglyMeasurable
          (fun z : H ↦ dcoord z (tcoord z))
          (MeasureTheory.volume.restrict S) := by
      simpa [L] using
        (ContinuousLinearMap.aestronglyMeasurable_comp₂ L hDcoord hTcoord)
    have heval_eq :
        (fun z : H ↦ dcoord z (tcoord z)) =ᵐ[
          MeasureTheory.volume.restrict S]
          fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v := by
      filter_upwards [ae_restrict_mem hS_meas] with z hzS
      have hzD : e.symm z ∈ eD.baseSet := hzS.2.2.1
      simpa [dcoord, tcoord, ξ, ManifoldDifferentialField.evalChart,
        SquareIntegrableManifoldDifferentialField.toField] using
        manifoldDifferentialBundle_trivialization_eval_eq
          (I := 𝓘(ℝ, H)) (X := X) (E := E) x₀ (e.symm z) hzD
          (w.toSection (e.symm z))
          (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v)
    refine ⟨U, hU_open.mem_nhds hz₀U, hU_meas, ?_⟩
    exact happly.congr heval_eq
  choose U hU_nhds _hU_meas hU_eval using hlocal
  rcases hK_compact.elim_nhds_subcover'
      (fun z hz ↦ U ⟨z, hz⟩)
      (fun z hz ↦ hU_nhds ⟨z, hz⟩) with
    ⟨t, hcover⟩
  let coverSet : Set H :=
    ⋃ z₀ : {z : K // z ∈ t}, K ∩ U z₀.1
  have hK_eq : K = coverSet := by
    ext z
    constructor
    · intro hzK
      rcases Set.mem_iUnion.mp (hcover hzK) with ⟨z₀, hz₀⟩
      rcases Set.mem_iUnion.mp hz₀ with ⟨hz₀t, hzU⟩
      exact Set.mem_iUnion.mpr ⟨⟨z₀, hz₀t⟩, ⟨hzK, hzU⟩⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨z₀, hzS⟩
      exact hzS.1
  rw [hK_eq]
  rw [aestronglyMeasurable_iUnion_iff]
  intro z₀
  exact hU_eval z₀.1

/--
%%handwave
name:
  Compact coordinate evaluation is controlled by the Hilbert--Schmidt norm
statement:
  On a compact coordinate support, evaluating a differential section on a
  fixed chart tangent direction is a bounded map from intrinsic
  \(L^2\)-differential sections to coordinate \(L^2\)-functions.
proof:
  The chart density of the smooth positive measure is bounded below on the
  compact support.  The chart tangent vector has bounded length there, and
  evaluation on a tangent vector is bounded by the Hilbert--Schmidt norm
  times this length.  The coordinate \(L^2\) bound follows from the density
  comparison.
-/
theorem manifoldDifferentialCompactEvaluation_eLpNorm_two_on_support_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (K : Set H) (v : H),
      K ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact K →
      ∃ C : NNReal,
        ∀ w : SquareIntegrableManifoldDifferentialField
          (I := I) (X := X) (E := E) g μ,
          MemLp
            (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
            2
            (MeasureTheory.volume.restrict K) ∧
          eLpNorm
            (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
            2
            (MeasureTheory.volume.restrict K) ≤
            (C : ℝ≥0∞) *
              ENNReal.ofReal
                (squareIntegrableHilbertBundleSectionL2Norm
                  (manifoldDifferentialHilbertBundleGeometry
                    (I := I) (X := X) (E := E) g) μ w) := by
  classical
  intro e he K v hK_region hK_compact
  rcases manifoldDifferentialCompactEvaluation_pointwise_norm_le
      (I := I) (X := X) (E := E) g e he K v hK_region hK_compact with
    ⟨Ceval, hCeval⟩
  rcases smoothPositiveMeasureOnManifold_chartPullback_eLpNorm_two_restrict_compact_le
      (I := I) (X := X) (F := ℝ) μ _hμ e he K hK_region hK_compact with
    ⟨Cchart, hCchart⟩
  refine ⟨Ceval * Cchart, ?_⟩
  intro w
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := E) g
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  let fNorm : X → ℝ := fun x ↦ ‖w.toSection x‖
  let fPull : H → ℝ := fun z ↦ fNorm (e.symm z)
  let fEval : H → E := fun z ↦
    ManifoldDifferentialField.evalChart w.toField e z v
  have hG_inner :
      ∀ (x : X)
        (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        G.fiberInner x A B = inner ℝ A B := by
    intro x A B
    rfl
  have hG_norm :
      ∀ (x : X)
        (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        G.fiberNormSq x A = ‖A‖ ^ 2 := by
    intro x A
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq A
  have hsqrt_eq :
      ∀ (x : X)
        (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        Real.sqrt (G.fiberNormSq x A) = ‖A‖ := by
    intro x A
    rw [hG_norm x A, Real.sqrt_sq (norm_nonneg _)]
  have hf_memLp : MemLp fNorm 2 μ := by
    simpa [fNorm, G] using
      squareIntegrableHilbertBundleSection_norm_memLp
        (I := I) (G := G) hG_inner μ w
  have hfPull_memLp : MemLp fPull 2 (MeasureTheory.volume.restrict K) := by
    simpa [fPull, fNorm] using
      smoothPositiveMeasureOnManifold_chartPullback_memLp_two_restrict_compact
        (I := I) (X := X) (F := ℝ) μ _hμ e he K hK_region hK_compact hf_memLp
  have hfPull_bound :
      eLpNorm fPull 2 (MeasureTheory.volume.restrict K) ≤
        (Cchart : ℝ≥0∞) *
          eLpNorm fNorm 2 μ := by
    simpa [fPull] using hCchart fNorm hf_memLp.aestronglyMeasurable
  have hfNorm_l2 :
      eLpNorm fNorm 2 μ =
        ENNReal.ofReal
          (squareIntegrableHilbertBundleSectionL2Norm G μ w) := by
    simpa [fNorm, G] using
      squareIntegrableHilbertBundleSection_eLpNorm_norm_eq_ofReal_l2Norm
        (I := I) (G := G) hG_inner μ w
  have hfEval_aestr : AEStronglyMeasurable fEval (MeasureTheory.volume.restrict K) := by
    simpa [fEval] using
      manifoldDifferentialCompactEvaluation_aestronglyMeasurable
        (I := I) (X := X) (E := E) g μ _hμ e he K v hK_region hK_compact w
  have hpoint :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        ‖fEval z‖ ≤ (Ceval : ℝ) * ‖fPull z‖ := by
    filter_upwards [ae_restrict_mem hK_compact.measurableSet] with z hzK
    have h :=
      hCeval z hzK
        (w.toSection (e.symm z) :
          ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z))
    calc
      ‖fEval z‖ ≤
          (Ceval : ℝ) *
            Real.sqrt
              (G.fiberNormSq (e.symm z)
                (w.toSection (e.symm z) :
                  ManifoldDifferentialBundleFiber
                    (I := I) (X := X) (E := E) (e.symm z))) := by
            simpa [fEval, G, ManifoldDifferentialField.evalChart,
              SquareIntegrableManifoldDifferentialField.toField] using h
      _ = (Ceval : ℝ) * ‖fPull z‖ := by
            rw [hsqrt_eq]
            simp [fPull, fNorm]
  have hfEval_memLp : MemLp fEval 2 (MeasureTheory.volume.restrict K) :=
    MemLp.of_le_mul hfPull_memLp hfEval_aestr hpoint
  have hEval_bound :
      eLpNorm fEval 2 (MeasureTheory.volume.restrict K) ≤
        ENNReal.ofReal (Ceval : ℝ) *
          eLpNorm fPull 2 (MeasureTheory.volume.restrict K) :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint 2
  refine ⟨by simpa [fEval] using hfEval_memLp, ?_⟩
  calc
    eLpNorm
        (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
        2
        (MeasureTheory.volume.restrict K)
        = eLpNorm fEval 2 (MeasureTheory.volume.restrict K) := rfl
    _ ≤ ENNReal.ofReal (Ceval : ℝ) *
          eLpNorm fPull 2 (MeasureTheory.volume.restrict K) := hEval_bound
    _ ≤ ENNReal.ofReal (Ceval : ℝ) *
          ((Cchart : ℝ≥0∞) * eLpNorm fNorm 2 μ) :=
        mul_le_mul_right hfPull_bound (ENNReal.ofReal (Ceval : ℝ))
    _ = ENNReal.ofReal (Ceval : ℝ) *
          ((Cchart : ℝ≥0∞) *
            ENNReal.ofReal
              (squareIntegrableHilbertBundleSectionL2Norm G μ w)) := by
        rw [hfNorm_l2]
    _ = ((Ceval * Cchart : NNReal) : ℝ≥0∞) *
          ENNReal.ofReal
            (squareIntegrableHilbertBundleSectionL2Norm G μ w) := by
        simp [mul_assoc]

namespace SurfaceDifferentialCoordinateHilbertFiber

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end SurfaceDifferentialCoordinateHilbertFiber

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
set_option maxHeartbeats 600000 in
set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in
end

end Uniformization

end JJMath
