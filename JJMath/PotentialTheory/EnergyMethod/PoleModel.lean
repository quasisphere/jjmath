import JJMath.Analysis.Sobolev
import JJMath.Uniformization.GreenFunctionCore
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Energy method: PoleModel

Logarithmic pole models and smooth surface-test preliminaries for the energy method.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization

/-- Smooth compactly supported surface tests are closed under scalar multiplication. -/
noncomputable def SmoothCompactlySupportedGlobalSurfaceFunction.smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℝ) (F : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    SmoothCompactlySupportedGlobalSurfaceFunction X where
  toFun := c • F.toFun
  gradient := c • F.gradient
  smooth := by
    intro e he
    simpa [Pi.smul_apply] using (F.smooth e he).const_smul c
  gradient_eq := by
    intro e he z hz v
    have hFdiff :
        DifferentiableAt ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z :=
      surfaceFunctionChartRepresentative_differentiableAt e he F.toFun F.smooth z hz
    calc
      (c • F.gradient) (e.symm z) (surfaceChartTangentMap e z v)
          = c * F.gradient (e.symm z) (surfaceChartTangentMap e z v) := by
              simp
      _ = c * fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z v := by
              rw [F.gradient_eq e he z hz v]
      _ = (c • fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z) v := by
              simp
      _ = fderiv ℝ (c • fun w : ℂ ↦ F.toFun (e.symm w)) z v := by
              rw [fderiv_const_smul hFdiff c]
      _ = fderiv ℝ (fun w : ℂ ↦ (c • F.toFun) (e.symm w)) z v := by
              rfl
  compact_support := by
    have hF : HasCompactSupport F.toFun := by
      simpa [HasCompactSupportOnSurface, HasCompactSupport] using F.compact_support
    have hsmul : HasCompactSupport (c • F.toFun) := by
      simpa [Pi.smul_apply] using hF.smul_left (f := fun _ : X ↦ c)
    simpa [HasCompactSupportOnSurface, HasCompactSupport, tsupport,
      Function.support] using hsmul

/--
%%handwave
name:
  Smooth compactly supported primitives have their classical weak gradient
statement:
  A smooth compactly supported scalar function on a surface is weakly
  differentiated by its stored classical differential.
proof:
  In each coordinate chart, apply the Euclidean integration-by-parts theorem
  to the coordinate representative of the function and the compactly
  supported coordinate test.  The stored differential is identified with the
  coordinate derivative by the defining classical differential identity.
-/
theorem SmoothCompactlySupportedGlobalSurfaceFunction.isWeakGradientOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (F : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    IsWeakGradientOnSurface μ F.toFun F.gradient := by
  intro e he φ v
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  let u : ℂ → ℝ := fun z ↦ F.toFun (e.symm z)
  let dφ : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  let du : ℂ → ℝ := fun z ↦ fderiv ℝ u z v
  have hΩ_eq : Ω = e.target := by
    ext z
    simp [Ω, surfaceChartRegion]
  have hΩ_open : IsOpen Ω := by
    simpa [hΩ_eq] using e.open_target
  have hF_smooth_target : ContDiffOn ℝ ∞ u e.target := by
    simpa [u, Set.preimage_univ] using F.smooth e he
  have hφ_support_target :
      tsupport (φ : ℂ → ℝ) ⊆ e.target := by
    intro z hz
    exact (φ.support_subset hz).1
  have hφ_support_Ω :
      tsupport (φ : ℂ → ℝ) ⊆ Ω := by
    simpa [hΩ_eq] using hφ_support_target
  have hdφ_support_target : tsupport dφ ⊆ e.target := by
    simpa [dφ] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : ℂ → ℝ)) v).trans hφ_support_target
  have hdφ_support_Ω : tsupport dφ ⊆ Ω := by
    simpa [hΩ_eq] using hdφ_support_target
  have hφ_cont : ContinuousOn (φ : ℂ → ℝ) e.target :=
    φ.smooth.continuous.continuousOn
  have hdφ_cont : ContinuousOn dφ e.target := by
    simpa [dφ] using
      ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have hu_cont : ContinuousOn u e.target := by
    exact hF_smooth_target.continuousOn
  have hdu_cont : ContinuousOn du e.target := by
    have hderiv :
        ContDiffOn ℝ ∞ (fderiv ℝ u) e.target := by
      exact hF_smooth_target.fderiv_of_isOpen e.open_target (by simp)
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
      (s := e.target) ((hdu_cont.mul hφ_cont)) e.open_target ?_ ?_
    · exact (tsupport_mul_subset_right).trans hφ_support_target
    · exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right
  have hudφ_int :
      Integrable (fun z : ℂ ↦ u z * dφ z) MeasureTheory.volume := by
    refine integrable_of_continuousOn_of_tsupport_subset_isCompact
      (s := e.target) ((hu_cont.mul hdφ_cont)) e.open_target ?_ ?_
    · exact (tsupport_mul_subset_right).trans hdφ_support_target
    · exact hdφ_compact.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right
  have huφ_int :
      Integrable (fun z : ℂ ↦ u z * φ z) MeasureTheory.volume := by
    refine integrable_of_continuousOn_of_tsupport_subset_isCompact
      (s := e.target) ((hu_cont.mul hφ_cont)) e.open_target ?_ ?_
    · exact (tsupport_mul_subset_right).trans hφ_support_target
    · exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right
  have hu_diff :
      ∀ z ∈ tsupport (φ : ℂ → ℝ), DifferentiableAt ℝ u z := by
    intro z hz
    have hz_target : z ∈ e.target := hφ_support_target hz
    exact
      (hF_smooth_target.contDiffAt
        (e.open_target.mem_nhds hz_target)).differentiableAt
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
        (fun z ↦ F.toFun (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
        (MeasureTheory.volume.restrict Ω) := by
    simpa [u, dφ] using hudφ_int.restrict (s := Ω)
  have hright_eq :
      (fun z : ℂ ↦ du z * φ z) =ᵐ[MeasureTheory.volume.restrict Ω]
        fun z ↦
          F.gradient (e.symm z) (surfaceChartTangentMap e z v) * φ z := by
    refine ae_restrict_of_forall_mem (by simpa [hΩ_eq] using e.open_target.measurableSet) ?_
    intro z hzΩ
    have hz_target : z ∈ e.target := by
      simpa [hΩ_eq] using hzΩ
    simp [du, u, F.gradient_eq e he z hz_target v]
  have hright_int :
      Integrable
        (fun z ↦
          F.gradient (e.symm z) (surfaceChartTangentMap e z v) * φ z)
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
    ∫ z in surfaceChartRegion e (Set.univ : Set X),
        F.toFun (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
        ∂MeasureTheory.volume =
      ∫ z in Ω, u z * dφ z ∂MeasureTheory.volume := by
        rfl
    _ = ∫ z : ℂ, u z * dφ z ∂MeasureTheory.volume := hleft_full_set.symm
    _ = -∫ z : ℂ, du z * φ z ∂MeasureTheory.volume := hibp
    _ = -∫ z in Ω, du z * φ z ∂MeasureTheory.volume := by
        rw [hright_full_set]
    _ = -∫ z in Ω,
          F.gradient (e.symm z) (surfaceChartTangentMap e z v) * φ z
          ∂MeasureTheory.volume := by
        rw [integral_congr_ae hright_eq]
    _ = -∫ z in surfaceChartRegion e (Set.univ : Set X),
          F.gradient (e.symm z) (surfaceChartTangentMap e z v) * φ z
          ∂MeasureTheory.volume := by
        rfl

/--
%%handwave
name:
  Smooth compactly supported primitives are locally square-integrable
statement:
  A smooth scalar function is square-integrable on every compact subset of a
  smooth background surface.
proof:
  The function is continuous on the compact set, hence bounded there, and the
  background area measure is finite on compact sets.
-/
theorem SmoothCompactlySupportedGlobalSurfaceFunction.memLp_restrict_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    {K : Set X} (_hK : IsCompact K) :
    MemLp F.toFun 2 (g.volume.restrict K) := by
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  have hcont : Continuous F.toFun :=
    isSmoothOnSurface_univ_continuous F.smooth
  have hsupport : HasCompactSupport F.toFun := by
    simpa [HasCompactSupportOnSurface] using F.compact_support
  exact
    (hcont.memLp_of_hasCompactSupport (μ := g.volume)
      (p := (2 : ℝ≥0∞)) hsupport).mono_measure Measure.restrict_le_self

/--
%%handwave
name:
  Smooth primitives are locally Sobolev from local gradient \(L^2\)
statement:
  If the stored classical differential of a smooth compactly supported
  primitive is locally square-integrable in coordinate norm, then the
  primitive is locally \(W^{1,2}\) with that weak gradient.
proof:
  The weak-gradient identity is the chartwise integration-by-parts formula
  for smooth functions.  The value is locally \(L^2\) by compactness and
  continuity, and the gradient \(L^2\) condition is the supplied hypothesis.
-/
theorem SmoothCompactlySupportedGlobalSurfaceFunction.isLocalSobolevH1OnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hgrad :
      ∀ K : Set X, IsCompact K →
        MemLp F.gradient 2 (g.volume.restrict K)) :
    IsLocalSobolevH1OnSurface g.volume (Set.univ : Set X)
      F.toFun F.gradient := by
  refine ⟨?_, ?_⟩
  · exact F.isWeakGradientOnSurface g.volume
  · intro K hK _hK_subset
    exact ⟨F.memLp_restrict_compact hK, hgrad K hK⟩

/--
%%handwave
name:
  Logarithmic cutoff pole model
statement:
  A logarithmic cutoff pole model at \(p\) is a compactly supported function
  \(\phi=-\chi\log |z-z(p)|\) in a coordinate chart: the cutoff is equal to
  one near \(p\), the model is smooth away from \(p\), and its
  Laplace-Beltrami term is smooth and compactly supported away from \(p\).
-/
structure LogarithmicCutoffPoleModel {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) (p : X) where
  /-- The cutoff logarithmic model. -/
  toFun : X → ℝ
  /-- The cutoff function. -/
  cutoff : X → ℝ
  /-- A pointed coordinate used to write the local logarithm. -/
  coordinate : PointedSurfaceCoordinate X p
  /-- A radius on which the cutoff is one and the logarithmic model is exact. -/
  innerRadius : ℝ
  /-- The inner radius is positive. -/
  innerRadius_pos : 0 < innerRadius
  /-- The cutoff is smooth away from the pole. -/
  cutoff_smooth_away_pole : IsSmoothOnSurface {x : X | x ≠ p} cutoff
  /-- The model is smooth away from the pole. -/
  smooth_away_pole : IsSmoothOnSurface {x : X | x ≠ p} toFun
  /-- The model has compact support. -/
  compact_support : HasCompactSupportOnSurface toFun
  /-- Near the pole the cutoff is exactly one. -/
  cutoff_eq_one_near_pole :
    ∀ x ∈ coordinate.chart.source,
      ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
        x ≠ p →
          cutoff x = 1
  /-- Near the pole the model is exactly \(-\log |z-z(p)|\). -/
  model_eq_negative_log_near_pole :
    ∀ x ∈ coordinate.chart.source,
      ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
        x ≠ p →
          toFun x = -Real.log ‖coordinate.chart x - coordinate.chart p‖
  /-- Wherever the cutoff is nonzero, the coordinate logarithm formula is valid. -/
  model_eq_cutoff_negative_log :
    ∀ x : X, x ≠ p → cutoff x ≠ 0 →
      x ∈ coordinate.chart.source ∧
        toFun x = -cutoff x * Real.log ‖coordinate.chart x - coordinate.chart p‖
  /-- The stored source term is the background Laplacian of the model away from the pole. -/
  source : X → ℝ
  /-- The source agrees with \(\Delta_g\phi\) on the punctured surface. -/
  source_eq_laplace :
    ∀ x : X, x ≠ p → g.laplaceBeltrami toFun x = source x
  /-- The source is compactly supported. -/
  source_compact_support : HasCompactSupportOnSurface source
  /-- The source support avoids the pole. -/
  source_support_away_pole :
    closure {x : X | source x ≠ 0} ⊆ {x : X | x ≠ p}
  /-- The source is smooth on the whole surface. -/
  source_smooth : IsSmoothOnSurface (Set.univ : Set X) source

/--
%%handwave
name:
  The cutoff source vanishes near the pole
statement:
  The smooth source term of a cutoff logarithmic pole model is identically
  zero in a neighbourhood of the pole.
proof:
  The closure of the source support is assumed to avoid the pole.  The
  complement of that closed set is therefore a neighbourhood of the pole, and
  on this complement the source cannot be nonzero.
-/
theorem LogarithmicCutoffPoleModel.eventually_source_eq_zero_at_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p) :
    ∀ᶠ x in 𝓝 p, φ.source x = 0 := by
  have hp_not :
      p ∉ closure {x : X | φ.source x ≠ 0} := by
    intro hp_closure
    exact (φ.source_support_away_pole hp_closure) rfl
  have hnhds :
      (closure {x : X | φ.source x ≠ 0})ᶜ ∈ 𝓝 p :=
    isClosed_closure.isOpen_compl.mem_nhds hp_not
  filter_upwards [hnhds] with x hx
  by_contra hx_ne
  exact hx (subset_closure hx_ne)

/--
%%handwave
name:
  Cutoff logarithmic pole core
statement:
  A cutoff logarithmic pole core is the geometric part of a pole model: a
  compactly supported cutoff logarithm which is exactly
  \(-\log |z-z(p)|\) near the pole and is smooth away from the pole.
-/
structure LogarithmicCutoffPoleCore (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] (p : X) where
  /-- The cutoff logarithmic function. -/
  toFun : X → ℝ
  /-- The smooth cutoff. -/
  cutoff : X → ℝ
  /-- A coordinate centered at the pole. -/
  coordinate : PointedSurfaceCoordinate X p
  /-- A radius on which the cutoff is one and the logarithmic model is exact. -/
  innerRadius : ℝ
  /-- The inner radius is positive. -/
  innerRadius_pos : 0 < innerRadius
  /-- The cutoff is smooth away from the pole. -/
  cutoff_smooth_away_pole : IsSmoothOnSurface {x : X | x ≠ p} cutoff
  /-- The cutoff logarithm is smooth away from the pole. -/
  smooth_away_pole : IsSmoothOnSurface {x : X | x ≠ p} toFun
  /-- The cutoff logarithm has compact support. -/
  compact_support : HasCompactSupportOnSurface toFun
  /-- Near the pole the cutoff is exactly one. -/
  cutoff_eq_one_near_pole :
    ∀ x ∈ coordinate.chart.source,
      ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
        x ≠ p →
          cutoff x = 1
  /-- Near the pole the model is exactly \(-\log |z-z(p)|\). -/
  model_eq_negative_log_near_pole :
    ∀ x ∈ coordinate.chart.source,
      ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
        x ≠ p →
          toFun x = -Real.log ‖coordinate.chart x - coordinate.chart p‖
  /-- Wherever the cutoff is nonzero, the coordinate logarithm formula is valid. -/
  model_eq_cutoff_negative_log :
    ∀ x : X, x ≠ p → cutoff x ≠ 0 →
      x ∈ coordinate.chart.source ∧
        toFun x = -cutoff x * Real.log ‖coordinate.chart x - coordinate.chart p‖

/--
%%handwave
name:
  Smooth real functions are smooth in surface coordinates
statement:
  A smooth real-valued function on the underlying real smooth surface is smooth
  when expressed in every complex surface coordinate.
proof:
  Compose the smooth function with the inverse of a surface chart.  The inverse
  chart is smooth for the real surface structure, so ordinary smoothness in
  coordinates follows.
-/
theorem isSmoothOnSurface_of_contMDiff
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] {u : X → ℝ}
    (hu : ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞ u) :
    IsSmoothOnSurface (Set.univ : Set X) u := by
  intro e he
  have hsymm : ContMDiffOn SurfaceRealModel SurfaceRealModel ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) he)
  have hcomp : ContMDiffOn SurfaceRealModel 𝓘(ℝ, ℝ) ∞
      (fun z : ℂ ↦ u (e.symm z)) e.target := by
    exact hu.contMDiffOn.comp (t := Set.univ) hsymm
      (fun _ _ ↦ by simp)
  have hcd : ContDiffOn ℝ ∞ (fun z : ℂ ↦ u (e.symm z)) e.target := by
    simpa [SurfaceRealModel] using (contMDiffOn_iff_contDiffOn.mp hcomp)
  simpa using hcd

/--
%%handwave
name:
  Smooth coordinate cutoff near a point
statement:
  Around every point of a Riemann surface there is a pointed
  coordinate and a smooth compactly supported cutoff, supported in that
  coordinate chart and identically one on a smaller coordinate disk.
proof:
  Choose the chart at the point.  A smooth bump function subordinate to this
  chart gives the cutoff; shrinking the inner radius makes the bump equal to
  one on the required coordinate disk.
-/
theorem exists_pointedCoordinate_smooth_cutoff_eq_one_near_pole
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    ∃ (cutoff : X → ℝ) (coordinate : PointedSurfaceCoordinate X p)
      (innerRadius : ℝ),
      0 < innerRadius ∧
        IsSmoothOnSurface {x : X | x ≠ p} cutoff ∧
        HasCompactSupportOnSurface cutoff ∧
        closure {x : X | cutoff x ≠ 0} ⊆ coordinate.chart.source ∧
        (∀ x ∈ coordinate.chart.source,
          ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
            x ≠ p →
              cutoff x = 1) := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  let b : SmoothBumpFunction SurfaceRealModel p := Classical.arbitrary _
  let coordinate : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  refine ⟨fun x ↦ b x, coordinate, b.rIn, b.rIn_pos, ?_, ?_, ?_, ?_⟩
  · have hs_univ : IsSmoothOnSurface (Set.univ : Set X) (fun x ↦ b x) :=
      isSmoothOnSurface_of_contMDiff (X := X) (u := fun x ↦ b x) b.contMDiff
    intro e he
    exact (hs_univ e he).mono (by
      intro z hz
      exact ⟨hz.1, by simp⟩)
  · simpa [HasCompactSupportOnSurface] using b.hasCompactSupport
  · simpa [coordinate] using b.tsupport_subset_chartAt_source
  · intro x hx_source hx_radius _hx_ne
    have hx_source' : x ∈ (chartAt ℂ p).source := by
      simpa [coordinate] using hx_source
    have hdist_lt :
        dist (extChartAt SurfaceRealModel p x) (extChartAt SurfaceRealModel p p) < b.rIn := by
      simpa [coordinate, SurfaceRealModel, dist_eq_norm] using hx_radius
    exact b.one_of_dist_le hx_source' (le_of_lt hdist_lt)

/--
%%handwave
name:
  Smooth compactly supported cutoff test near a point
statement:
  Around every point of a Riemann surface there is a smooth
  compactly supported surface test function, supported in one pointed
  coordinate chart, which is identically one on a smaller coordinate disk.
proof:
  Take a smooth bump function in the real smooth surface structure and store
  its exterior derivative as the surface differential.
-/
theorem exists_smoothCompactlySupportedGlobalSurfaceFunction_eq_one_near_pole
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    ∃ (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
      (coordinate : PointedSurfaceCoordinate X p)
      (innerRadius : ℝ),
      0 < innerRadius ∧
        closure {x : X | F.toFun x ≠ 0} ⊆ coordinate.chart.source ∧
        (∀ x : X, 0 ≤ F.toFun x ∧ F.toFun x ≤ 1) ∧
        (∀ x ∈ coordinate.chart.source,
          ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
              F.toFun x = 1) := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  let b : SmoothBumpFunction SurfaceRealModel p := Classical.arbitrary _
  let coordinate : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  have hb_smooth :
      IsSmoothOnSurface (Set.univ : Set X) (fun x : X ↦ b x) :=
    isSmoothOnSurface_of_contMDiff (X := X) (u := fun x ↦ b x)
      b.contMDiff
  let F : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    { toFun := fun x : X ↦ b x
      gradient := surfaceExteriorDerivative (fun x : X ↦ b x)
      smooth := hb_smooth
      gradient_eq := by
        intro e he z hz v
        exact
          surfaceExteriorDerivative_apply_chartTangentMap_of_smooth e he
            (fun x : X ↦ b x) hb_smooth z hz v
      compact_support := by
        simpa [HasCompactSupportOnSurface] using b.hasCompactSupport }
  refine ⟨F, coordinate, b.rIn, b.rIn_pos, ?_, ?_, ?_⟩
  · simpa [F, coordinate] using b.tsupport_subset_chartAt_source
  · intro x
    exact ⟨b.nonneg, b.le_one⟩
  · intro x hx_source hx_radius
    have hx_source' : x ∈ (chartAt ℂ p).source := by
      simpa [coordinate] using hx_source
    have hdist_lt :
        dist (extChartAt SurfaceRealModel p x) (extChartAt SurfaceRealModel p p) < b.rIn := by
      simpa [coordinate, SurfaceRealModel, dist_eq_norm] using hx_radius
    exact b.one_of_dist_le hx_source' (le_of_lt hdist_lt)

/--
%%handwave
name:
  Smooth compactly supported cutoff test with prescribed small support
statement:
  Given a neighbourhood of a point on a Riemann surface, there is a
  smooth compactly supported surface test supported inside that neighbourhood,
  taking values between \(0\) and \(1\), and identically one on a smaller
  coordinate disk about the point.
proof:
  Use that smooth bump functions centered at the point have supports forming
  a neighbourhood basis.  Choose one whose closed support lies in the
  prescribed neighbourhood and store its exterior derivative as the surface
  differential.
-/
theorem exists_smoothCompactlySupportedGlobalSurfaceFunction_eq_one_near_pole_of_mem_nhds
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) {s : Set X} (hs : s ∈ 𝓝 p) :
    ∃ (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
      (coordinate : PointedSurfaceCoordinate X p)
      (innerRadius : ℝ),
      0 < innerRadius ∧
        closure {x : X | F.toFun x ≠ 0} ⊆ s ∧
        closure {x : X | F.toFun x ≠ 0} ⊆ coordinate.chart.source ∧
        (∀ x : X, 0 ≤ F.toFun x ∧ F.toFun x ≤ 1) ∧
        (∀ x ∈ coordinate.chart.source,
          ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
              F.toFun x = 1) := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  rcases
      (SmoothBumpFunction.nhds_basis_tsupport (I := SurfaceRealModel) p).mem_iff.mp
        hs with
    ⟨b, _hb_true, hb_subset_s⟩
  let coordinate : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  have hb_smooth :
      IsSmoothOnSurface (Set.univ : Set X) (fun x : X ↦ b x) :=
    isSmoothOnSurface_of_contMDiff (X := X) (u := fun x ↦ b x)
      b.contMDiff
  let F : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    { toFun := fun x : X ↦ b x
      gradient := surfaceExteriorDerivative (fun x : X ↦ b x)
      smooth := hb_smooth
      gradient_eq := by
        intro e he z hz v
        exact
          surfaceExteriorDerivative_apply_chartTangentMap_of_smooth e he
            (fun x : X ↦ b x) hb_smooth z hz v
      compact_support := by
        simpa [HasCompactSupportOnSurface] using b.hasCompactSupport }
  refine ⟨F, coordinate, b.rIn, b.rIn_pos, ?_, ?_, ?_, ?_⟩
  · simpa [F, tsupport, Function.support] using hb_subset_s
  · simpa [F, coordinate] using b.tsupport_subset_chartAt_source
  · intro x
    exact ⟨b.nonneg, b.le_one⟩
  · intro x hx_source hx_radius
    have hx_source' : x ∈ (chartAt ℂ p).source := by
      simpa [coordinate] using hx_source
    have hdist_lt :
        dist (extChartAt SurfaceRealModel p x) (extChartAt SurfaceRealModel p p) < b.rIn := by
      simpa [coordinate, SurfaceRealModel, dist_eq_norm] using hx_radius
    exact b.one_of_dist_le hx_source' (le_of_lt hdist_lt)

/--
%%handwave
name:
  Smooth cutoff supported where a punctured-neighbourhood property holds
statement:
  If a property holds throughout a punctured neighbourhood of a point, then
  there is a smooth compactly supported cutoff which is one near the point and
  whose closed support is contained in the point together with the region
  where the property holds.
proof:
  Rewrite the punctured-neighbourhood statement as an ordinary neighbourhood
  statement with the implication “away from the point, the property holds.”
  Then choose a bump function with closed support inside that neighbourhood.
-/
theorem exists_smoothCompactlySupportedGlobalSurfaceFunction_eq_one_near_pole_of_eventually_nhdsWithin
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) {P : X → Prop}
    (hP : ∀ᶠ x in 𝓝[≠] p, P x) :
    ∃ (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
      (coordinate : PointedSurfaceCoordinate X p)
      (innerRadius : ℝ),
      0 < innerRadius ∧
        closure {x : X | F.toFun x ≠ 0} ⊆ {x : X | x = p ∨ P x} ∧
        closure {x : X | F.toFun x ≠ 0} ⊆ coordinate.chart.source ∧
        (∀ x : X, 0 ≤ F.toFun x ∧ F.toFun x ≤ 1) ∧
        (∀ x ∈ coordinate.chart.source,
          ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
              F.toFun x = 1) := by
  let E : Set X := {x : X | x ≠ p → P x}
  have hE : E ∈ 𝓝 p := by
    simpa [E] using eventually_nhdsWithin_iff.mp hP
  rcases
      exists_smoothCompactlySupportedGlobalSurfaceFunction_eq_one_near_pole_of_mem_nhds
        X p hE with
    ⟨F, coordinate, innerRadius, hinner_pos, hsupport_E,
      hsupport_source, hbounds, hF_eq_one⟩
  refine
    ⟨F, coordinate, innerRadius, hinner_pos, ?_, hsupport_source,
      hbounds, hF_eq_one⟩
  intro x hx_support
  have hxE : x ≠ p → P x := hsupport_E hx_support
  by_cases hxp : x = p
  · exact Or.inl hxp
  · exact Or.inr (hxE hxp)

/--
%%handwave
name:
  A cutoff equal to one near the pole has complementary support away from the pole
statement:
  If a smooth cutoff is identically one on a coordinate disk around a point,
  then the closed support of \(1-F\) does not contain that point.
proof:
  The coordinate disk is a neighbourhood of the point, and \(1-F\) vanishes
  on this neighbourhood.  Hence the point is not in the closure of the set on
  which \(1-F\) is nonzero.
-/
theorem one_sub_cutoff_support_away_pole_of_eq_one_near_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (coordinate : PointedSurfaceCoordinate X p) {innerRadius : ℝ}
    (hinner_pos : 0 < innerRadius)
    (hF_eq_one :
      ∀ x ∈ coordinate.chart.source,
        ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
          F.toFun x = 1) :
    closure {x : X | (1 : ℝ) - F.toFun x ≠ 0} ⊆ {x : X | x ≠ p} := by
  let N : Set X :=
    coordinate.chart.source ∩
      {x : X | ‖coordinate.chart x - coordinate.chart p‖ < innerRadius}
  have hsource_nhds : coordinate.chart.source ∈ 𝓝 p :=
    coordinate.chart.open_source.mem_nhds coordinate.base_mem_source
  have hdist_cont :
      ContinuousAt
        (fun x : X ↦ ‖coordinate.chart x - coordinate.chart p‖) p :=
    (coordinate.chart.continuousAt coordinate.base_mem_source).sub
        continuousAt_const |>.norm
  have hball_nhds :
      {x : X | ‖coordinate.chart x - coordinate.chart p‖ < innerRadius} ∈
        𝓝 p :=
    hdist_cont.preimage_mem_nhds
      (Iio_mem_nhds (by simpa using hinner_pos))
  have hN_nhds : N ∈ 𝓝 p :=
    Filter.inter_mem hsource_nhds hball_nhds
  have hp_not_closure :
      p ∉ closure {x : X | (1 : ℝ) - F.toFun x ≠ 0} := by
    intro hp_closure
    rcases mem_closure_iff_nhds.mp hp_closure N hN_nhds with
      ⟨y, hyN, hy_support⟩
    have hFy : F.toFun y = 1 :=
      hF_eq_one y hyN.1 hyN.2
    exact hy_support (by simp [hFy])
  intro x hx_closure hxp
  subst x
  exact hp_not_closure hx_closure

/--
%%handwave
name:
  Harmonic surface functions are smooth
statement:
  A harmonic real-valued function on a surface region is smooth on that
  region.
proof:
  In a complex coordinate, harmonicity gives harmonicity at every point of
  the coordinate image.  Plane harmonic functions are real analytic, hence
  smooth.
-/
theorem harmonicOnSurface_isSmoothOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ}
    (hu : IsHarmonicOnSurface U u) :
    IsSmoothOnSurface U u := by
  intro e he z hz
  exact (HarmonicAt.analyticAt (hu e he z hz)).contDiffAt.contDiffWithinAt

/--
%%handwave
name:
  Pointed coordinate logarithm is smooth away from the point
statement:
  In a pointed coordinate, the negative logarithm of the coordinate distance
  to the point is smooth on the punctured coordinate chart.
proof:
  The coordinate logarithm is harmonic on the chart away from the center,
  because it is the logarithmic potential of the coordinate center.  Harmonic
  functions on plane coordinate images are real analytic, hence smooth.
-/
theorem pointedCoordinate_negative_log_isSmoothOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (coordinate : PointedSurfaceCoordinate X p) :
    IsSmoothOnSurface ({x : X | x ≠ p} ∩ coordinate.chart.source)
      (fun x ↦ -Real.log ‖coordinate.chart x - coordinate.chart p‖) := by
  have hlog_harm :
      IsHarmonicOnSurface ({x : X | x ≠ p} ∩ coordinate.chart.source)
        (fun x ↦ Real.log ‖coordinate.chart x - coordinate.chart p‖) := by
    refine coordinateLogDistance_harmonicOnSurface
      coordinate.chart coordinate.chart_mem_atlas ?_ ?_
    · intro x hx
      exact hx.2
    · intro x hx h_eq
      exact hx.1 (coordinate.chart.injOn hx.2 coordinate.base_mem_source h_eq)
  have hlog_smooth :
      IsSmoothOnSurface ({x : X | x ≠ p} ∩ coordinate.chart.source)
        (fun x ↦ Real.log ‖coordinate.chart x - coordinate.chart p‖) :=
    harmonicOnSurface_isSmoothOnSurface hlog_harm
  intro e he
  simpa using (hlog_smooth e he).neg

/--
%%handwave
name:
  Multiplication by a supported smooth function localizes smoothness
statement:
  Let a smooth function have closed support contained in an open set.  If a
  second function is smooth on that open set, then their product is smooth on
  the original region.
proof:
  In coordinates, argue locally.  Near points in the closed support both
  factors are smooth, so the product rule applies.  Away from the closed
  support the first factor vanishes in a neighborhood, so the product is
  locally zero.
-/
theorem isSmoothOnSurface_mul_of_left_support_subset_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U V : Set X} {u v : X → ℝ}
    (hV_open : IsOpen V)
    (hu : IsSmoothOnSurface U u)
    (hv : IsSmoothOnSurface (U ∩ V) v)
    (hsupport : closure {x : X | u x ≠ 0} ⊆ V) :
    IsSmoothOnSurface U (fun x ↦ u x * v x) := by
  intro e he
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' U
  change ContDiffOn ℝ ∞
    (fun z : ℂ ↦ u (e.symm z) * v (e.symm z)) S
  have huS : ContDiffOn ℝ ∞ (fun z : ℂ ↦ u (e.symm z)) S := by
    simpa [S] using hu e he
  have hvUV :
      ContDiffOn ℝ ∞ (fun z : ℂ ↦ v (e.symm z))
        (e.target ∩ e.symm ⁻¹' (U ∩ V)) :=
    hv e he
  refine contDiffOn_of_locally_contDiffOn (s := S)
    (f := fun z : ℂ ↦ u (e.symm z) * v (e.symm z)) ?_
  intro z hz
  by_cases hz_support : e.symm z ∈ closure {x : X | u x ≠ 0}
  · let W : Set ℂ := e.target ∩ e.symm ⁻¹' V
    refine ⟨W, ?_, ?_, ?_⟩
    · simpa [W] using e.isOpen_inter_preimage_symm hV_open
    · exact ⟨hz.1, hsupport hz_support⟩
    · have hu_local :
          ContDiffOn ℝ ∞ (fun z : ℂ ↦ u (e.symm z)) (S ∩ W) :=
        huS.mono Set.inter_subset_left
      have hv_local :
          ContDiffOn ℝ ∞ (fun z : ℂ ↦ v (e.symm z)) (S ∩ W) := by
        refine hvUV.mono ?_
        intro w hw
        exact ⟨hw.1.1, ⟨hw.1.2, hw.2.2⟩⟩
      exact hu_local.mul hv_local
  · let W : Set ℂ := e.target ∩ e.symm ⁻¹' (closure {x : X | u x ≠ 0})ᶜ
    refine ⟨W, ?_, ?_, ?_⟩
    · simpa [W] using
        e.isOpen_inter_preimage_symm
          (show IsOpen (closure {x : X | u x ≠ 0})ᶜ from isClosed_closure.isOpen_compl)
    · exact ⟨hz.1, hz_support⟩
    · refine (contDiffOn_const :
        ContDiffOn ℝ ∞ (fun _ : ℂ ↦ (0 : ℝ)) (S ∩ W)).congr ?_
      intro w hw
      have hw_not_support : e.symm w ∉ closure {x : X | u x ≠ 0} := hw.2.2
      have hu_zero : u (e.symm w) = 0 := by
        by_contra hne
        exact hw_not_support (subset_closure hne)
      simp [hu_zero]

/--
%%handwave
name:
  Localized smooth product as a compactly supported surface test
statement:
  If a smooth factor has closed support contained in an open set where a
  compactly supported factor is smooth, then their product is a smooth
  compactly supported surface test.
proof:
  Smoothness follows from the local product argument: near the first factor's
  support both factors are smooth, and off that support the product is locally
  zero.  Compact support is inherited from the compactly supported factor.
-/
noncomputable def SmoothCompactlySupportedGlobalSurfaceFunction.mul_of_left_support_subset_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {V : Set X} {u v : X → ℝ}
    (hV_open : IsOpen V)
    (hu : IsSmoothOnSurface (Set.univ : Set X) u)
    (hv : IsSmoothOnSurface V v)
    (hv_compact : HasCompactSupportOnSurface v)
    (hsupport : closure {x : X | u x ≠ 0} ⊆ V) :
    SmoothCompactlySupportedGlobalSurfaceFunction X where
  toFun := fun x : X ↦ u x * v x
  gradient := surfaceExteriorDerivative (fun x : X ↦ u x * v x)
  smooth := by
    refine isSmoothOnSurface_mul_of_left_support_subset_open
      hV_open hu ?_ hsupport
    simpa using hv
  gradient_eq := by
    intro e he z hz w
    exact
      surfaceExteriorDerivative_apply_chartTangentMap_of_smooth e he
        (fun x : X ↦ u x * v x)
        (by
          refine isSmoothOnSurface_mul_of_left_support_subset_open
            hV_open hu ?_ hsupport
          simpa using hv)
        z hz w
  compact_support := by
    exact hasCompactSupportOnSurface_mul_left hv_compact

/--
%%handwave
name:
  Product of compactly supported smooth surface tests
statement:
  The pointwise product of two compactly supported smooth surface test
  functions is again a compactly supported smooth surface test function.
proof:
  Apply the localized smooth-product construction with the open set equal to
  the whole surface.
-/
noncomputable def SmoothCompactlySupportedGlobalSurfaceFunction.mul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (F G : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    SmoothCompactlySupportedGlobalSurfaceFunction X :=
  SmoothCompactlySupportedGlobalSurfaceFunction.mul_of_left_support_subset_open
    (V := Set.univ)
    isOpen_univ
    F.smooth
    (by simpa using G.smooth)
    G.compact_support
    (by intro x _hx; exact Set.mem_univ x)

/--
%%handwave
name:
  Smoothness of a cutoff coordinate logarithm
statement:
  If a smooth cutoff is supported in a pointed coordinate chart, then the
  product of the cutoff with the negative coordinate logarithm is smooth away
  from the pole.
proof:
  On the support of the cutoff the expression is written in a single
  holomorphic coordinate, where the logarithm of the distance to the center is
  smooth away from the center.  Off the support the product is locally zero.
-/
theorem pointedCoordinate_cutoff_negative_log_smooth_away_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (cutoff : X → ℝ) (coordinate : PointedSurfaceCoordinate X p)
    (hcutoff_smooth : IsSmoothOnSurface {x : X | x ≠ p} cutoff)
    (hsupport_source : closure {x : X | cutoff x ≠ 0} ⊆ coordinate.chart.source) :
    IsSmoothOnSurface {x : X | x ≠ p}
      (fun x ↦ cutoff x *
        (-Real.log ‖coordinate.chart x - coordinate.chart p‖)) := by
  exact isSmoothOnSurface_mul_of_left_support_subset_open
    coordinate.chart.open_source hcutoff_smooth
    (pointedCoordinate_negative_log_isSmoothOnSurface coordinate)
    hsupport_source

/--
%%handwave
name:
  Existence of cutoff logarithmic pole core data
statement:
  Around every point of a Riemann surface there is a pointed
  coordinate, a compactly supported smooth cutoff, and the associated cutoff
  logarithm.  The cutoff is one on a smaller coordinate disk, and the cutoff
  logarithm is exactly \(-\log |z-z(p)|\) there.
proof:
  Use
  [a smooth compactly supported coordinate cutoff which is identically one near
  the point](lean:JJMath.Uniformization.exists_pointedCoordinate_smooth_cutoff_eq_one_near_pole).
  Then
  [multiplying this cutoff by the negative coordinate logarithm is smooth away
  from the point](lean:JJMath.Uniformization.pointedCoordinate_cutoff_negative_log_smooth_away_pole).
  The compact support and the two displayed formulas follow directly from the
  support of the cutoff and the definition of the product.
-/
theorem exists_logarithmicCutoffPoleCore_data
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    ∃ (toFun cutoff : X → ℝ) (coordinate : PointedSurfaceCoordinate X p)
      (innerRadius : ℝ),
      0 < innerRadius ∧
        IsSmoothOnSurface {x : X | x ≠ p} cutoff ∧
        IsSmoothOnSurface {x : X | x ≠ p} toFun ∧
        HasCompactSupportOnSurface toFun ∧
        (∀ x ∈ coordinate.chart.source,
          ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
            x ≠ p →
              cutoff x = 1) ∧
        (∀ x ∈ coordinate.chart.source,
          ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
            x ≠ p →
              toFun x = -Real.log ‖coordinate.chart x - coordinate.chart p‖) ∧
        (∀ x : X, x ≠ p → cutoff x ≠ 0 →
          x ∈ coordinate.chart.source ∧
            toFun x = -cutoff x * Real.log ‖coordinate.chart x - coordinate.chart p‖) := by
  rcases exists_pointedCoordinate_smooth_cutoff_eq_one_near_pole X p with
    ⟨cutoff, coordinate, innerRadius, hinner_pos, hcutoff_smooth,
      hcutoff_compact, hsupport_source, hcutoff_eq_one⟩
  let toFun : X → ℝ := fun x ↦ cutoff x *
    (-Real.log ‖coordinate.chart x - coordinate.chart p‖)
  have hmodel_smooth : IsSmoothOnSurface {x : X | x ≠ p} toFun := by
    simpa [toFun] using
      (pointedCoordinate_cutoff_negative_log_smooth_away_pole
        (X := X) (p := p) cutoff coordinate hcutoff_smooth hsupport_source)
  have hmodel_compact : HasCompactSupportOnSurface toFun := by
    simpa [toFun] using
      (hasCompactSupportOnSurface_mul_right
        (X := X) (u := cutoff)
        (v := fun x ↦ -Real.log ‖coordinate.chart x - coordinate.chart p‖)
        hcutoff_compact)
  refine ⟨toFun, cutoff, coordinate, innerRadius, hinner_pos,
    hcutoff_smooth, hmodel_smooth, hmodel_compact, hcutoff_eq_one, ?_, ?_⟩
  · intro x hx_source hx_radius hx_ne
    have hcutoff_one := hcutoff_eq_one x hx_source hx_radius hx_ne
    simp [toFun, hcutoff_one]
  · intro x hx_ne hcutoff_ne
    have hx_closure : x ∈ closure {y : X | cutoff y ≠ 0} :=
      subset_closure hcutoff_ne
    have hx_source : x ∈ coordinate.chart.source :=
      hsupport_source hx_closure
    refine ⟨hx_source, ?_⟩
    simp [toFun]

/--
%%handwave
name:
  Existence of cutoff logarithmic pole cores
statement:
  Every point of a Riemann surface admits a compactly supported
  cutoff logarithmic pole core.
proof:
  Package the cutoff logarithmic pole data into the structure recording the
  chosen coordinate, cutoff, inner radius, logarithmic formula, and smoothness
  and compact-support properties.
-/
theorem exists_logarithmicCutoffPoleCore
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    Nonempty (LogarithmicCutoffPoleCore X p) := by
  rcases exists_logarithmicCutoffPoleCore_data X p with
    ⟨toFun, cutoff, coordinate, innerRadius, hinner_pos,
      hcutoff_smooth, hmodel_smooth, hmodel_compact, hcutoff_eq_one,
      hmodel_eq_negative_log, hmodel_eq_cutoff⟩
  exact ⟨
    { toFun := toFun
      cutoff := cutoff
      coordinate := coordinate
      innerRadius := innerRadius
      innerRadius_pos := hinner_pos
      cutoff_smooth_away_pole := hcutoff_smooth
      smooth_away_pole := hmodel_smooth
      compact_support := hmodel_compact
      cutoff_eq_one_near_pole := hcutoff_eq_one
      model_eq_negative_log_near_pole := hmodel_eq_negative_log
      model_eq_cutoff_negative_log := hmodel_eq_cutoff }⟩

/--
%%handwave
name:
  Laplace source of a cutoff logarithmic pole core
statement:
  The canonical source associated to a cutoff logarithmic pole core is the
  divergence-form Laplace-Beltrami operator applied to the core away from the
  pole, extended by zero at the pole.
-/
noncomputable def logarithmicCutoffPoleCore_laplaceBeltramiSource
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p) : X → ℝ := by
  classical
  exact fun x ↦
    if x = p then 0 else surfaceDivergenceFormLaplaceBeltrami metric φ.toFun x

/--
%%handwave
name:
  Cutoff pole core source agrees with the punctured Laplacian
statement:
  Away from the pole, the canonical source associated to a cutoff logarithmic
  pole core is exactly the divergence-form Laplace-Beltrami operator applied
  to the core.
proof:
  This is the definition of the canonical source, since the zero-extension
  branch is used only at the pole.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltramiSource_eq_away
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p) :
    ∀ x : X, x ≠ p →
      surfaceDivergenceFormLaplaceBeltrami metric φ.toFun x =
        logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ x := by
  classical
  intro x hx
  simp [logarithmicCutoffPoleCore_laplaceBeltramiSource, hx]

/--
%%handwave
name:
  Vanishing near a point removes the point from the closed support
statement:
  If a real-valued function is identically zero on some neighborhood of a
  point, then the closed support of the function does not contain that point.
proof:
  A point in the closure of the nonzero set has every neighborhood meeting the
  nonzero set.  The neighborhood on which the function is zero cannot meet the
  nonzero set, giving a contradiction.
-/
theorem closure_support_subset_compl_of_eventuallyEq_zero
    {X : Type} [TopologicalSpace X] {f : X → ℝ} {p : X}
    (hf : f =ᶠ[𝓝 p] fun _ : X ↦ (0 : ℝ)) :
    closure {x : X | f x ≠ 0} ⊆ {x : X | x ≠ p} := by
  intro x hx hxp
  subst x
  rcases mem_closure_iff_nhds.mp hx {x : X | f x = 0} hf with
    ⟨y, hy_zero, hy_nonzero⟩
  exact hy_nonzero hy_zero

/--
%%handwave
name:
  Gluing smoothness across an isolated zero neighborhood
statement:
  If a surface function is smooth away from a point and is identically zero on
  a neighborhood of that point, then it is smooth on the whole surface.
proof:
  In any coordinate chart, points away from the distinguished point are handled
  by the punctured smoothness statement, since the punctured set is locally a
  relative neighborhood in the chart.  At points mapping to the distinguished
  point, the coordinate representative agrees near the point with the constant
  zero function.
-/
theorem isSmoothOnSurface_univ_of_smooth_away_point_of_eventuallyEq_zero
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    {f : X → ℝ} {p : X}
    (hsmooth : IsSmoothOnSurface {x : X | x ≠ p} f)
    (hzero : f =ᶠ[𝓝 p] fun _ : X ↦ (0 : ℝ)) :
    IsSmoothOnSurface (Set.univ : Set X) f := by
  intro e he
  rw [Set.preimage_univ, Set.inter_univ]
  intro z hz_target
  by_cases hz_p : e.symm z = p
  · have hcoord_zero :
        (fun w : ℂ ↦ f (e.symm w)) =ᶠ[𝓝 z] fun _ : ℂ ↦ (0 : ℝ) := by
      have hzero_at :
          f =ᶠ[𝓝 (e.symm z)] fun _ : X ↦ (0 : ℝ) := by
        simpa [hz_p] using hzero
      exact (e.continuousAt_symm hz_target).tendsto.eventually hzero_at
    have hz_zero : f (e.symm z) = 0 := hcoord_zero.self_of_nhds
    exact
      (contDiffAt_const (𝕜 := ℝ) (x := z) (c := (0 : ℝ))).contDiffWithinAt
        |>.congr_of_eventuallyEq
          (eventually_nhdsWithin_of_eventually_nhds hcoord_zero) hz_zero
  · have hpunc_open : IsOpen ({x : X | x ≠ p}) := by
      simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
    have hpunc_mem : {x : X | x ≠ p} ∈ 𝓝 (e.symm z) :=
      hpunc_open.mem_nhds hz_p
    have hpreimage_mem :
        e.symm ⁻¹' {x : X | x ≠ p} ∈ 𝓝 z :=
      (e.continuousAt_symm hz_target).preimage_mem_nhds hpunc_mem
    have hrelative :
        e.target ∩ e.symm ⁻¹' {x : X | x ≠ p} ∈ 𝓝[e.target] z :=
      inter_mem_nhdsWithin _ hpreimage_mem
    exact (hsmooth e he z ⟨hz_target, hz_p⟩).mono_of_mem_nhdsWithin hrelative

/--
%%handwave
name:
  Coordinate derivatives vanish for locally zero functions
statement:
  If a surface function is identically zero near a coordinate point, then all
  coordinate first derivatives vanish at that point.
proof:
  The coordinate representative agrees near the point with the constant zero
  function, so its Fréchet derivative is the derivative of that constant.
-/
theorem surfaceFunctionChartDerivativeComponent_eq_zero_of_eventuallyEq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) {z : ℂ}
    (hzero :
      (fun w : ℂ ↦ f (e.symm w)) =ᶠ[𝓝 z] fun _ : ℂ ↦ (0 : ℝ))
    (i : Fin 2) :
    surfaceFunctionChartDerivativeComponent e f z i = 0 := by
  have hderiv :
      fderiv ℝ (fun w : ℂ ↦ f (e.symm w)) z = 0 := by
    simpa using hzero.fderiv_eq
  simp [surfaceFunctionChartDerivativeComponent,
    surfaceFunctionChartDirectionalDerivative, hderiv]

/--
%%handwave
name:
  Coordinate metric flux vanishes for locally zero functions
statement:
  If a surface function is identically zero near a coordinate point, then its
  metric gradient flux vanishes at that coordinate point.
proof:
  The flux is a smooth metric coefficient times a linear combination of first
  coordinate derivatives of the function, and all those derivatives vanish.
-/
theorem surfaceMetricGradientFluxInChart_eq_zero_of_eventuallyEq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) {z : ℂ}
    (hzero :
      (fun w : ℂ ↦ f (e.symm w)) =ᶠ[𝓝 z] fun _ : ℂ ↦ (0 : ℝ))
    (i : Fin 2) :
    surfaceMetricGradientFluxInChart metric e f z i = 0 := by
  have hderiv :
      ∀ j : Fin 2, surfaceFunctionChartDerivativeComponent e f z j = 0 :=
    surfaceFunctionChartDerivativeComponent_eq_zero_of_eventuallyEq_zero
      e f hzero
  simp [surfaceMetricGradientFluxInChart, hderiv]

/--
%%handwave
name:
  Coordinate Laplace-Beltrami term vanishes for locally zero functions
statement:
  If a surface function is identically zero near a coordinate point, then its
  divergence-form Laplace-Beltrami expression in that coordinate vanishes at
  the point.
proof:
  Near the point the coordinate first derivatives vanish, hence the metric
  gradient flux is locally zero.  The divergence of a locally zero flux also
  vanishes.
-/
theorem surfaceDivergenceFormLaplaceBeltramiInChart_eq_zero_of_eventuallyEq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) {z : ℂ}
    (hzero :
      (fun w : ℂ ↦ f (e.symm w)) =ᶠ[𝓝 z] fun _ : ℂ ↦ (0 : ℝ)) :
    surfaceDivergenceFormLaplaceBeltramiInChart metric e f z = 0 := by
  have hderiv_event :
      fderiv ℝ (fun w : ℂ ↦ f (e.symm w))
        =ᶠ[𝓝 z] fun _ : ℂ ↦ (0 : ℂ →L[ℝ] ℝ) := by
    simpa using hzero.fderiv
  have hflux_event :
      ∀ i : Fin 2,
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w i)
          =ᶠ[𝓝 z] fun _ : ℂ ↦ (0 : ℝ) := by
    intro i
    filter_upwards [hderiv_event] with w hw
    have hcomp :
        ∀ j : Fin 2, surfaceFunctionChartDerivativeComponent e f w j = 0 := by
      intro j
      simp [surfaceFunctionChartDerivativeComponent,
        surfaceFunctionChartDirectionalDerivative, hw]
    simp [surfaceMetricGradientFluxInChart, hcomp]
  have hflux0_deriv :
      fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
        z = 0 := by
    simpa using (hflux_event 0).fderiv_eq
  have hflux1_deriv :
      fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
        z = 0 := by
    simpa using (hflux_event 1).fderiv_eq
  simp [surfaceDivergenceFormLaplaceBeltramiInChart, hflux0_deriv,
    hflux1_deriv]

/--
%%handwave
name:
  Laplace-Beltrami term vanishes for locally zero functions
statement:
  If a surface function is identically zero near a point, then its
  divergence-form Laplace-Beltrami term vanishes at that point.
proof:
  Write the global operator in the preferred chart at the point.  The inverse
  chart carries the local zero statement to a local zero statement for the
  coordinate representative, so the coordinate divergence-form expression
  vanishes.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_eq_zero_of_eventuallyEq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X) (f : X → ℝ) {x : X}
    (hzero : f =ᶠ[𝓝 x] fun _ : X ↦ (0 : ℝ)) :
    surfaceDivergenceFormLaplaceBeltrami metric f x = 0 := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hx_source : x ∈ e.source := by
    simp [e]
  have hz_target : e x ∈ e.target := e.map_source hx_source
  have hleft : e.symm (e x) = x := e.left_inv hx_source
  have hchart_zero :
      (fun w : ℂ ↦ f (e.symm w)) =ᶠ[𝓝 (e x)] fun _ : ℂ ↦ (0 : ℝ) := by
    have hzero_at :
        f =ᶠ[𝓝 (e.symm (e x))] fun _ : X ↦ (0 : ℝ) := by
      simpa [hleft] using hzero
    exact (e.continuousAt_symm hz_target).tendsto.eventually hzero_at
  simpa [surfaceDivergenceFormLaplaceBeltrami, e] using
    surfaceDivergenceFormLaplaceBeltramiInChart_eq_zero_of_eventuallyEq_zero
      metric e f hchart_zero

/--
%%handwave
name:
  Cutoff pole core source vanishes off the model support
statement:
  Away from the pole and away from the closed support of the cutoff
  logarithmic model, the canonical source is locally zero.
proof:
  Outside the closed support of the model, the model itself vanishes on a
  neighborhood.  At every nearby point which is not the pole, the
  divergence-form Laplace-Beltrami term of the locally zero model vanishes,
  and the canonical source agrees with that term.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltramiSource_eventuallyEq_zero_of_notMem_model_support
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X) {p x : X}
    (φ : LogarithmicCutoffPoleCore X p)
    (hx_support : x ∉ closure {y : X | φ.toFun y ≠ 0}) (hx_ne : x ≠ p) :
    logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ
      =ᶠ[𝓝 x] fun _ : X ↦ (0 : ℝ) := by
  have hsupport_nhds :
      (closure {y : X | φ.toFun y ≠ 0})ᶜ ∈ 𝓝 x :=
    isClosed_closure.isOpen_compl.mem_nhds hx_support
  have hpunc_nhds : {y : X | y ≠ p} ∈ 𝓝 x := by
    have hpunc_open : IsOpen ({y : X | y ≠ p}) := by
      simpa using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
    exact hpunc_open.mem_nhds hx_ne
  filter_upwards [hsupport_nhds, hpunc_nhds] with y hy_support hy_ne
  have hmodel_zero :
      φ.toFun =ᶠ[𝓝 y] fun _ : X ↦ (0 : ℝ) := by
    have hy_nhds :
        (closure {z : X | φ.toFun z ≠ 0})ᶜ ∈ 𝓝 y :=
      isClosed_closure.isOpen_compl.mem_nhds hy_support
    filter_upwards [hy_nhds] with z hz_support
    by_contra hz_ne
    exact hz_support (subset_closure hz_ne)
  have hlaplace :
      surfaceDivergenceFormLaplaceBeltrami metric φ.toFun y = 0 :=
    surfaceDivergenceFormLaplaceBeltrami_eq_zero_of_eventuallyEq_zero
      metric φ.toFun hmodel_zero
  simp [logarithmicCutoffPoleCore_laplaceBeltramiSource, hy_ne, hlaplace]

/--
%%handwave
name:
  Cutoff pole core source has no support outside the model support
statement:
  The closed support of the canonical source is contained in the closed
  support of the cutoff logarithmic model, with the pole adjoined.
proof:
  Away from the closed support of the model the model is locally zero, so its
  divergence-form Laplacian is locally zero.  The pole is adjoined because the
  model need not be smooth there before the logarithmic harmonicity argument
  is applied.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltramiSource_support_subset_model_support_union_pole
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p) :
    closure {x : X |
        logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ x ≠ 0}
      ⊆ closure {x : X | φ.toFun x ≠ 0} ∪ {p} := by
  intro x hx_closure
  by_contra hx_not
  have hx_support : x ∉ closure {y : X | φ.toFun y ≠ 0} := by
    intro hx
    exact hx_not (Or.inl hx)
  have hx_ne : x ≠ p := by
    intro hxp
    exact hx_not (Or.inr (by simp [hxp]))
  have hsource_zero :=
    logarithmicCutoffPoleCore_laplaceBeltramiSource_eventuallyEq_zero_of_notMem_model_support
      metric φ hx_support hx_ne
  rcases mem_closure_iff_nhds.mp hx_closure
      {y : X | logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ y = 0}
      hsource_zero with
    ⟨y, hy_zero, hy_nonzero⟩
  exact hy_nonzero hy_zero

/--
%%handwave
name:
  Cutoff pole core source has compact support
statement:
  For a conformal smooth background metric, the canonical Laplace-Beltrami
  source of a cutoff logarithmic pole core has compact support.
proof:
  Outside the compact support of the cutoff logarithm the core is locally
  zero, so its divergence-form Laplacian is locally zero.  Near the pole the
  core is the pure logarithm in a conformal coordinate, hence harmonic on the
  punctured coordinate disk, and the zero extension contributes no support at
  the pole.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltramiSource_compact_support
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p)
    (_hconformal : SurfaceMetricConformalToComplexStructure metric) :
    HasCompactSupportOnSurface
      (logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ) := by
  have hsubset :=
    logarithmicCutoffPoleCore_laplaceBeltramiSource_support_subset_model_support_union_pole
      metric φ
  have hcompact :
      IsCompact (closure {x : X | φ.toFun x ≠ 0} ∪ {p}) :=
    φ.compact_support.union isCompact_singleton
  exact hcompact.of_isClosed_subset isClosed_closure hsubset

/--
%%handwave
name:
  Conformal metric flux is the Euclidean gradient
statement:
  In a conformal holomorphic coordinate, the divergence-form metric flux
  \(\rho g^{ij}\partial_j f\) is the ordinary Euclidean coordinate gradient
  of \(f\).
proof:
  This is the defining coefficient identity for a conformal background metric:
  \(\rho g^{ij}=\delta^{ij}\).
-/
theorem surfaceMetricGradientFluxInChart_eq_derivativeComponent_of_conformal
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (hconformal : SurfaceMetricConformalToComplexStructure metric)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (f : X → ℝ) {z : ℂ} (hz : z ∈ e.target) :
    ∀ i : Fin 2,
      surfaceMetricGradientFluxInChart metric e f z i =
        surfaceFunctionChartDerivativeComponent e f z i := by
  intro i
  have hcoeff :
      ∀ j : Fin 2,
        surfaceMetricVolumeDensityInChart metric e z *
            surfaceMetricInverseGramCoeffInChart metric e z i j =
          if i = j then 1 else 0 :=
    hconformal e he z hz i
  fin_cases i
  · have h00 :
        surfaceMetricVolumeDensityInChart metric e z *
            surfaceMetricInverseGramCoeffInChart metric e z 0 0 = 1 := by
      simpa using hcoeff 0
    have h01 :
        surfaceMetricVolumeDensityInChart metric e z *
            surfaceMetricInverseGramCoeffInChart metric e z 0 1 = 0 := by
      simpa using hcoeff 1
    change surfaceMetricGradientFluxInChart metric e f z 0 =
      surfaceFunctionChartDerivativeComponent e f z 0
    rw [surfaceMetricGradientFluxInChart_zero]
    rw [mul_add, ← mul_assoc, ← mul_assoc, h00, h01]
    ring
  · have h10 :
        surfaceMetricVolumeDensityInChart metric e z *
            surfaceMetricInverseGramCoeffInChart metric e z 1 0 = 0 := by
      simpa using hcoeff 0
    have h11 :
        surfaceMetricVolumeDensityInChart metric e z *
            surfaceMetricInverseGramCoeffInChart metric e z 1 1 = 1 := by
      simpa using hcoeff 1
    change surfaceMetricGradientFluxInChart metric e f z 1 =
      surfaceFunctionChartDerivativeComponent e f z 1
    rw [surfaceMetricGradientFluxInChart_one]
    rw [mul_add, ← mul_assoc, ← mul_assoc, h10, h11]
    ring

/--
%%handwave
name:
  Divergence of the Euclidean gradient is the complex-plane Laplacian
statement:
  For a twice continuously differentiable real-valued function on the complex
  plane, the sum of the coordinate derivatives of the two coordinate first
  derivatives is the standard Euclidean Laplacian.
proof:
  This is Mathlib's formula for the Laplacian on \(\mathbb C\) with the
  orthonormal basis \(1,i\), together with the identification of second
  Fréchet derivatives with derivatives of the first derivative map.
-/
theorem surfaceCoordinateGradientDivergence_eq_laplacian
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
  Conformal Laplace-Beltrami operator kills harmonic functions
statement:
  On an open surface region, a function that is harmonic for the complex
  structure has zero divergence-form Laplace-Beltrami operator for every
  conformal smooth background metric.
proof:
  In holomorphic coordinates conformality identifies the coefficient tensor
  \(\rho g^{ij}\) with the Euclidean identity.  The divergence-form operator
  is therefore the Euclidean Laplacian multiplied by the positive factor
  \(\rho^{-1}\), and the Euclidean Laplacian of a harmonic function vanishes.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_eq_zero_of_conformal_harmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (hconformal : SurfaceMetricConformalToComplexStructure metric)
    {U : Set X} (_hU_open : IsOpen U) {f : X → ℝ}
    (hf_harmonic : IsHarmonicOnSurface U f) :
    ∀ x ∈ U, surfaceDivergenceFormLaplaceBeltrami metric f x = 0 := by
  intro x hxU
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z : ℂ := e x
  let F : ℂ → ℝ := fun w ↦ f (e.symm w)
  have he : e ∈ atlas ℂ X := by
    simp [e]
  have hx_source : x ∈ e.source := by
    simp [e]
  have hz_target : z ∈ e.target := by
    exact e.map_source hx_source
  have hleft : e.symm z = x := by
    exact e.left_inv hx_source
  have hzU : z ∈ e.target ∩ e.symm ⁻¹' U := by
    exact ⟨hz_target, by simpa [z, hleft] using hxU⟩
  have hharm : InnerProductSpace.HarmonicAt F z := by
    simpa [F] using hf_harmonic e he z hzU
  have hlap_zero : Laplacian.laplacian F z = 0 :=
    hharm.2.self_of_nhds
  have hflux_event :
      ∀ i : Fin 2,
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w i)
          =ᶠ[𝓝 z]
        (fun w : ℂ ↦ surfaceFunctionChartDerivativeComponent e f w i) := by
    intro i
    filter_upwards [e.open_target.mem_nhds hz_target] with w hw
    exact surfaceMetricGradientFluxInChart_eq_derivativeComponent_of_conformal
      metric hconformal e he f hw i
  have hD0 :
      fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
          z (1 : ℂ) =
        fderiv ℝ (fun w : ℂ ↦ fderiv ℝ F w (1 : ℂ)) z (1 : ℂ) := by
    have h :
        fderiv ℝ
            (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0) z =
          fderiv ℝ
            (fun w : ℂ ↦ surfaceFunctionChartDerivativeComponent e f w 0) z :=
      (hflux_event (0 : Fin 2)).fderiv_eq
    simpa [F, surfaceFunctionChartDerivativeComponent,
      surfaceFunctionChartDirectionalDerivative] using
      congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L (1 : ℂ)) h
  have hD1 :
      fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
          z Complex.I =
        fderiv ℝ (fun w : ℂ ↦ fderiv ℝ F w Complex.I) z Complex.I := by
    have h :
        fderiv ℝ
            (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1) z =
          fderiv ℝ
            (fun w : ℂ ↦ surfaceFunctionChartDerivativeComponent e f w 1) z :=
      (hflux_event (1 : Fin 2)).fderiv_eq
    simpa [F, surfaceFunctionChartDerivativeComponent,
      surfaceFunctionChartDirectionalDerivative] using
      congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L Complex.I) h
  have hdiv_eq :
      fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
          z (1 : ℂ) +
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
          z Complex.I =
        Laplacian.laplacian F z := by
    rw [hD0, hD1]
    exact surfaceCoordinateGradientDivergence_eq_laplacian F hharm.1
  simp [surfaceDivergenceFormLaplaceBeltrami,
    surfaceDivergenceFormLaplaceBeltramiInChart, e, z, F, hdiv_eq, hlap_zero]

/--
%%handwave
name:
  The conformal Laplace-Beltrami operator kills the local logarithm
statement:
  In the inner coordinate disk of a cutoff logarithmic pole core, a conformal
  background metric has zero divergence-form Laplace-Beltrami term on the
  punctured disk.
proof:
  In a holomorphic coordinate for a conformal metric, the tensor
  \(\rho g^{ij}\) in divergence form is the Euclidean identity.  On the inner
  disk the cutoff model is the pure logarithm \(-\log |z-z(p)|\), whose
  Euclidean Laplacian vanishes away from the center.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltrami_eq_zero_on_inner_punctured_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p)
    (hconformal : SurfaceMetricConformalToComplexStructure metric) :
    ∀ x ∈ φ.coordinate.chart.source,
      ‖φ.coordinate.chart x - φ.coordinate.chart p‖ < φ.innerRadius →
        x ≠ p →
          surfaceDivergenceFormLaplaceBeltrami metric φ.toFun x = 0 := by
  intro x hx_source hx_radius hx_ne
  let U : Set X :=
    (φ.coordinate.chart.source ∩
      φ.coordinate.chart ⁻¹'
        Metric.ball (φ.coordinate.chart p) φ.innerRadius) ∩
      {y : X | y ≠ p}
  have hball_open :
      IsOpen (φ.coordinate.chart.source ∩
        φ.coordinate.chart ⁻¹'
          Metric.ball (φ.coordinate.chart p) φ.innerRadius) :=
    φ.coordinate.chart.isOpen_inter_preimage Metric.isOpen_ball
  have hU_open : IsOpen U := by
    exact hball_open.inter (by
      simpa using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p}))
  have hU_source : U ⊆ φ.coordinate.chart.source := by
    intro y hy
    exact hy.1.1
  have hU_avoid : ∀ y ∈ U, φ.coordinate.chart y ≠ φ.coordinate.chart p := by
    intro y hy h_eq
    exact hy.2 (φ.coordinate.chart.injOn hy.1.1 φ.coordinate.base_mem_source h_eq)
  have hlog_harm :
      IsHarmonicOnSurface U
        (fun y : X ↦ Real.log ‖φ.coordinate.chart y - φ.coordinate.chart p‖) :=
    coordinateLogDistance_harmonicOnSurface
      φ.coordinate.chart φ.coordinate.chart_mem_atlas hU_source hU_avoid
  have hneg_harm :
      IsHarmonicOnSurface U
        (fun y : X ↦ -Real.log ‖φ.coordinate.chart y - φ.coordinate.chart p‖) := by
    simpa using harmonicOnSurface_neg hlog_harm
  have hφ_harm :
      IsHarmonicOnSurface U φ.toFun :=
    harmonicOnSurface_congr_on_open hU_open hneg_harm (by
      intro y hy
      have hy_radius :
          ‖φ.coordinate.chart y - φ.coordinate.chart p‖ < φ.innerRadius := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy.1.2
      exact φ.model_eq_negative_log_near_pole y hy.1.1 hy_radius hy.2)
  have hxU : x ∈ U := by
    refine ⟨⟨hx_source, ?_⟩, hx_ne⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hx_radius
  exact
    surfaceDivergenceFormLaplaceBeltrami_eq_zero_of_conformal_harmonicOnSurface
      metric hconformal hU_open hφ_harm x hxU

/--
%%handwave
name:
  Cutoff pole core source vanishes near the pole
statement:
  For a conformal smooth background metric, the canonical source associated to
  a cutoff logarithmic pole core is identically zero on a neighborhood of the
  pole.
proof:
  In the pole coordinate the metric is conformal, so the divergence-form
  Laplace-Beltrami operator is a positive smooth factor times the Euclidean
  Laplacian.  On a sufficiently small punctured coordinate disk the model is
  the pure logarithm, whose Euclidean Laplacian vanishes away from the center;
  at the center the canonical source is defined to be zero.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltramiSource_eventuallyEq_zero_at_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p)
    (hconformal : SurfaceMetricConformalToComplexStructure metric) :
    logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ
      =ᶠ[𝓝 p] fun _ : X ↦ (0 : ℝ) := by
  have hsource_nhds : φ.coordinate.chart.source ∈ 𝓝 p :=
    φ.coordinate.chart.open_source.mem_nhds φ.coordinate.base_mem_source
  have hdist_cont :
      ContinuousAt
        (fun x : X ↦ ‖φ.coordinate.chart x - φ.coordinate.chart p‖) p :=
    (φ.coordinate.chart.continuousAt φ.coordinate.base_mem_source).sub
        continuousAt_const |>.norm
  have hball_nhds :
      {x : X |
        ‖φ.coordinate.chart x - φ.coordinate.chart p‖ < φ.innerRadius} ∈ 𝓝 p :=
    hdist_cont.preimage_mem_nhds
      (Iio_mem_nhds (by simpa using φ.innerRadius_pos))
  filter_upwards [hsource_nhds, hball_nhds] with x hx_source hx_radius
  by_cases hx_ne : x ≠ p
  · have hlaplace :=
      logarithmicCutoffPoleCore_laplaceBeltrami_eq_zero_on_inner_punctured_disk
        metric φ hconformal x hx_source hx_radius hx_ne
    simp [logarithmicCutoffPoleCore_laplaceBeltramiSource, hx_ne, hlaplace]
  · simp [logarithmicCutoffPoleCore_laplaceBeltramiSource, not_not.mp hx_ne]

/--
%%handwave
name:
  Cutoff pole core source support avoids the pole
statement:
  For a conformal smooth background metric, the closed support of the
  canonical Laplace-Beltrami source of a cutoff logarithmic pole core does not
  contain the pole.
proof:
  In the pole coordinate the metric is conformal, so the Laplace-Beltrami
  operator is a smooth positive factor times the Euclidean Laplacian.  On a
  smaller punctured coordinate disk the core is the pure logarithm, whose
  Euclidean Laplacian vanishes away from the center.  Thus the canonical
  source is zero on a whole neighborhood of the pole.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltramiSource_support_away_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p)
    (hconformal : SurfaceMetricConformalToComplexStructure metric) :
    closure {x : X |
        logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ x ≠ 0}
      ⊆ {x : X | x ≠ p} := by
  exact closure_support_subset_compl_of_eventuallyEq_zero
    (logarithmicCutoffPoleCore_laplaceBeltramiSource_eventuallyEq_zero_at_pole
      metric φ hconformal)

/--
%%handwave
name:
  Local smoothness of coordinate derivative components
statement:
  If the coordinate representative of a surface function is smooth on an open
  subset of a chart image, then each first coordinate derivative component is
  smooth there.
proof:
  The derivative map of a smooth coordinate representative is smooth on the
  open set, and evaluation on a fixed coordinate vector preserves smoothness.
-/
theorem surfaceFunctionChartDerivativeComponent_contDiffOn_of_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ)
    {S : Set ℂ} (hS_open : IsOpen S)
    (hf : ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) S)
    (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e f z i) S := by
  have hfderiv :
      ContDiffOn ℝ ∞
        (fderiv ℝ (fun w : ℂ ↦ f (e.symm w))) S :=
    hf.fderiv_of_isOpen hS_open (by simp)
  simpa [surfaceFunctionChartDerivativeComponent,
    surfaceFunctionChartDirectionalDerivative] using
      hfderiv.clm_apply (contDiffOn_const (c := complexCoordinateVector i))

/--
%%handwave
name:
  Local smoothness of the metric flux
statement:
  In a fixed chart, the metric gradient flux of a locally smooth coordinate
  representative is smooth on every open subset of the chart image.
proof:
  The flux is built from the smooth volume density, smooth inverse metric
  coefficients, and the smooth first coordinate derivatives of the function.
-/
theorem surfaceMetricGradientFluxInChart_contDiffOn_of_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (f : X → ℝ) {S : Set ℂ} (hS_open : IsOpen S) (hS_subset : S ⊆ e.target)
    (hf : ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) S)
    (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℂ ↦ surfaceMetricGradientFluxInChart metric e f z i) S := by
  have hρ : ContDiffOn ℝ ∞
      (surfaceMetricVolumeDensityInChart metric e) S :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e he).1.mono
      hS_subset
  have hsum : ContDiffOn ℝ ∞
      (fun z : ℂ ↦
        ∑ j : Fin 2,
          surfaceMetricInverseGramCoeffInChart metric e z i j *
            surfaceFunctionChartDerivativeComponent e f z j) S := by
    simpa using
      (ContDiffOn.sum (s := Finset.univ)
        (fun j _ ↦
          ((surfaceMetricInverseGramCoeffInChart_contDiffOn
                metric e he i j).mono hS_subset).mul
            (surfaceFunctionChartDerivativeComponent_contDiffOn_of_contDiffOn
              e f hS_open hf j)))
  simpa [surfaceMetricGradientFluxInChart] using hρ.mul hsum

/--
%%handwave
name:
  Local smoothness of the fixed-chart divergence-form expression
statement:
  In a fixed chart, the divergence-form Laplace-Beltrami expression of a
  locally smooth coordinate representative is smooth on every open subset of
  the chart image.
proof:
  The coordinate expression is \(\rho^{-1}\) times the Euclidean divergence of
  the metric flux.  The flux is smooth locally, so its coordinate derivatives
  are smooth locally, and the positive smooth volume density may be inverted.
-/
theorem surfaceDivergenceFormLaplaceBeltramiInChart_contDiffOn_of_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (f : X → ℝ) {S : Set ℂ} (hS_open : IsOpen S) (hS_subset : S ⊆ e.target)
    (hf : ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) S) :
    ContDiffOn ℝ ∞
      (fun z : ℂ ↦ surfaceDivergenceFormLaplaceBeltramiInChart metric e f z) S := by
  have hρ_inv : ContDiffOn ℝ ∞
      (fun z : ℂ ↦ (surfaceMetricVolumeDensityInChart metric e z)⁻¹) S := by
    exact ((surfaceMetricVolumeDensityInChart_smooth_positive X metric e he).1.mono
      hS_subset).inv (by
        intro z hz
        exact ne_of_gt
          ((surfaceMetricVolumeDensityInChart_smooth_positive X metric e he).2
            z (hS_subset hz)))
  have hflux0 :
      ContDiffOn ℝ ∞
        (fun z : ℂ ↦ surfaceMetricGradientFluxInChart metric e f z 0) S :=
    surfaceMetricGradientFluxInChart_contDiffOn_of_contDiffOn
      metric e he f hS_open hS_subset hf 0
  have hflux1 :
      ContDiffOn ℝ ∞
        (fun z : ℂ ↦ surfaceMetricGradientFluxInChart metric e f z 1) S :=
    surfaceMetricGradientFluxInChart_contDiffOn_of_contDiffOn
      metric e he f hS_open hS_subset hf 1
  have hD0 : ContDiffOn ℝ ∞
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
          z (1 : ℂ)) S := by
    have hderiv :
        ContDiffOn ℝ ∞
          (fderiv ℝ
            (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)) S :=
      hflux0.fderiv_of_isOpen hS_open (by simp)
    exact hderiv.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hD1 : ContDiffOn ℝ ∞
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
          z Complex.I) S := by
    have hderiv :
        ContDiffOn ℝ ∞
          (fderiv ℝ
            (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)) S :=
      hflux1.fderiv_of_isOpen hS_open (by simp)
    exact hderiv.clm_apply (contDiffOn_const (c := Complex.I))
  simpa [surfaceDivergenceFormLaplaceBeltramiInChart] using
    hρ_inv.mul (hD0.add hD1)

/--
%%handwave
name:
  Local chart formula for the divergence-form Laplace-Beltrami operator
statement:
  On an open region where a function is smooth, the global divergence-form
  Laplace-Beltrami operator agrees with the fixed-chart coordinate expression
  on every chart source.
proof:
  The global operator is defined using a preferred chart at the point.  On the
  overlap with any other chart, the divergence-form coordinate expression is
  invariant under holomorphic coordinate changes.  This invariance is local in
  the smooth function, so smoothness on the open region is enough.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_eq_inChart_of_mem_source_of_isSmoothOnSurface_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X)
    {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : IsSmoothOnSurface U f)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    ∀ x ∈ U, x ∈ e.source →
      surfaceDivergenceFormLaplaceBeltrami metric f x =
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f (e x) := by
  intro x hxU hx
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hc_atlas : c ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hx_c_source : x ∈ c.source := mem_chart_source ℂ x
  have hz_target : c x ∈ c.target := c.map_source hx_c_source
  have hleft : c.symm (c x) = x := c.left_inv hx_c_source
  have hx_overlap : c.symm (c x) ∈ e.source := by
    simpa [hleft] using hx
  have hxU_chart : c.symm (c x) ∈ U := by
    simpa [hleft] using hxU
  have hoverlap :=
    surfaceDivergenceFormLaplaceBeltramiInChart_eq_on_overlap_of_mem_open
      metric c e hc_atlas he hU f hf hz_target hx_overlap hxU_chart
  simpa [surfaceDivergenceFormLaplaceBeltrami, c, hleft] using hoverlap

/--
%%handwave
name:
  Divergence-form Laplace-Beltrami preserves smoothness locally
statement:
  On an open surface region, applying the divergence-form Laplace-Beltrami
  operator of a smooth background metric to a smooth function gives another
  smooth function.
proof:
  In every coordinate chart the operator has smooth coefficients and is a
  second-order linear differential operator.  Differentiating the smooth
  coordinate representative and multiplying by the smooth metric coefficients
  therefore gives a smooth coordinate representative for the result.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_isSmoothOnSurface_of_isSmoothOnSurface_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X) {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : IsSmoothOnSurface U f) :
    IsSmoothOnSurface U (surfaceDivergenceFormLaplaceBeltrami metric f) := by
  intro e he
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hU
  have hS_subset : S ⊆ e.target := by
    intro z hz
    exact hz.1
  have hf_chart :
      ContDiffOn ℝ ∞ (fun z : ℂ ↦ f (e.symm z)) S := by
    simpa [S] using hf e he
  have hinChart :
      ContDiffOn ℝ ∞
        (fun z : ℂ ↦ surfaceDivergenceFormLaplaceBeltramiInChart metric e f z)
        S :=
    surfaceDivergenceFormLaplaceBeltramiInChart_contDiffOn_of_contDiffOn
      metric e he f hS_open hS_subset hf_chart
  refine hinChart.congr ?_
  intro z hz
  have hx_source : e.symm z ∈ e.source := e.map_target hz.1
  have hglobal :=
    surfaceDivergenceFormLaplaceBeltrami_eq_inChart_of_mem_source_of_isSmoothOnSurface_open
      metric hU hf e he (e.symm z) hz.2 hx_source
  simpa [S, e.right_inv hz.1] using hglobal

/--
%%handwave
name:
  Cutoff pole core source is smooth away from the pole
statement:
  For a smooth background metric, the canonical source associated to a cutoff
  logarithmic pole core is smooth on the punctured surface.
proof:
  Away from the pole the cutoff logarithmic model is smooth.  Applying the
  divergence-form Laplace-Beltrami operator in any coordinate chart only
  differentiates this smooth representative and multiplies by smooth metric
  coefficients.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltramiSource_smooth_away_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p) :
    IsSmoothOnSurface {x : X | x ≠ p}
      (logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ) := by
  have hpunc_open : IsOpen ({x : X | x ≠ p}) := by
    simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  have hlaplace_smooth :
      IsSmoothOnSurface {x : X | x ≠ p}
        (surfaceDivergenceFormLaplaceBeltrami metric φ.toFun) :=
    surfaceDivergenceFormLaplaceBeltrami_isSmoothOnSurface_of_isSmoothOnSurface_open
      metric hpunc_open φ.smooth_away_pole
  intro e he
  exact (hlaplace_smooth e he).congr (by
    intro z hz
    have hx_ne : e.symm z ≠ p := hz.2
    simp [logarithmicCutoffPoleCore_laplaceBeltramiSource, hx_ne])

/--
%%handwave
name:
  Cutoff pole core source is smooth
statement:
  For a conformal smooth background metric, the canonical Laplace-Beltrami
  source of a cutoff logarithmic pole core is smooth on the whole surface.
proof:
  Away from the pole this is the divergence-form Laplace-Beltrami operator
  applied to a smooth function, hence smooth in every coordinate chart.  Near
  the pole the source vanishes on a neighborhood by conformality and the
  harmonicity of the pure logarithm, so the zero extension is smooth there.
-/
theorem logarithmicCutoffPoleCore_laplaceBeltramiSource_smooth
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p)
    (hconformal : SurfaceMetricConformalToComplexStructure metric) :
    IsSmoothOnSurface (Set.univ : Set X)
      (logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ) := by
  exact isSmoothOnSurface_univ_of_smooth_away_point_of_eventuallyEq_zero
    (logarithmicCutoffPoleCore_laplaceBeltramiSource_smooth_away_pole metric φ)
    (logarithmicCutoffPoleCore_laplaceBeltramiSource_eventuallyEq_zero_at_pole
      metric φ hconformal)

/--
%%handwave
name:
  Laplace source of a cutoff logarithmic pole core is regular
statement:
  For a conformal background metric, the divergence-form Laplace-Beltrami
  operator applied to a cutoff logarithmic pole core has, away from the pole,
  a smooth compactly supported representative whose support stays away from
  the pole.
proof:
  Use the canonical source, which
  [agrees with the punctured Laplace-Beltrami expression](lean:JJMath.Uniformization.logarithmicCutoffPoleCore_laplaceBeltramiSource_eq_away).
  Conformality and the logarithmic form near the pole show that this source
  [has compact support](lean:JJMath.Uniformization.logarithmicCutoffPoleCore_laplaceBeltramiSource_compact_support),
  that its
  [closed support avoids the pole](lean:JJMath.Uniformization.logarithmicCutoffPoleCore_laplaceBeltramiSource_support_away_pole),
  and that it
  [is smooth on the whole surface](lean:JJMath.Uniformization.logarithmicCutoffPoleCore_laplaceBeltramiSource_smooth).
-/
theorem logarithmicCutoffPoleCore_laplaceBeltrami_source_regular
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X) {p : X}
    (φ : LogarithmicCutoffPoleCore X p)
    (hconformal : SurfaceMetricConformalToComplexStructure metric) :
    ∃ source : X → ℝ,
      (∀ x : X, x ≠ p →
        surfaceDivergenceFormLaplaceBeltrami metric φ.toFun x = source x) ∧
        HasCompactSupportOnSurface source ∧
        closure {x : X | source x ≠ 0} ⊆ {x : X | x ≠ p} ∧
        IsSmoothOnSurface (Set.univ : Set X) source := by
  refine ⟨logarithmicCutoffPoleCore_laplaceBeltramiSource metric φ, ?_, ?_, ?_, ?_⟩
  · exact logarithmicCutoffPoleCore_laplaceBeltramiSource_eq_away metric φ
  · exact logarithmicCutoffPoleCore_laplaceBeltramiSource_compact_support
      metric φ hconformal
  · exact logarithmicCutoffPoleCore_laplaceBeltramiSource_support_away_pole
      metric φ hconformal
  · exact logarithmicCutoffPoleCore_laplaceBeltramiSource_smooth
      metric φ hconformal

/--
%%handwave
name:
  Canonical cutoff logarithmic pole data exists
statement:
  For the canonical Laplace-Beltrami operator of a conformal smooth
  background metric, every point admits a compactly supported logarithmic
  cutoff model whose Laplacian away from the pole is a smooth compactly
  supported source supported away from the pole.
proof:
  First choose the cutoff logarithmic pole core.  Applying the
  divergence-form Laplace-Beltrami operator to this core gives a smooth
  compactly supported source by the regular-source construction, and the two
  pieces of data are then assembled into the canonical tuple.
-/
theorem exists_logarithmicCutoffPoleModel_canonical_data
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [RiemannSurface X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (hconformal : SurfaceMetricConformalToComplexStructure metric) (p : X) :
    ∃ (toFun cutoff : X → ℝ) (coordinate : PointedSurfaceCoordinate X p)
      (innerRadius : ℝ) (source : X → ℝ),
      0 < innerRadius ∧
        IsSmoothOnSurface {x : X | x ≠ p} cutoff ∧
        IsSmoothOnSurface {x : X | x ≠ p} toFun ∧
        HasCompactSupportOnSurface toFun ∧
        (∀ x ∈ coordinate.chart.source,
          ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
            x ≠ p →
              cutoff x = 1) ∧
        (∀ x ∈ coordinate.chart.source,
          ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
            x ≠ p →
              toFun x = -Real.log ‖coordinate.chart x - coordinate.chart p‖) ∧
        (∀ x : X, x ≠ p → cutoff x ≠ 0 →
          x ∈ coordinate.chart.source ∧
            toFun x = -cutoff x * Real.log ‖coordinate.chart x - coordinate.chart p‖) ∧
        (∀ x : X, x ≠ p →
          surfaceDivergenceFormLaplaceBeltrami metric toFun x = source x) ∧
        HasCompactSupportOnSurface source ∧
        closure {x : X | source x ≠ 0} ⊆ {x : X | x ≠ p} ∧
        IsSmoothOnSurface (Set.univ : Set X) source := by
  rcases exists_logarithmicCutoffPoleCore X p with ⟨φ⟩
  rcases logarithmicCutoffPoleCore_laplaceBeltrami_source_regular
      metric φ hconformal with
    ⟨source, hsource_eq_laplace, hsource_compact, hsource_away,
      hsource_smooth⟩
  exact ⟨φ.toFun, φ.cutoff, φ.coordinate, φ.innerRadius, source,
    φ.innerRadius_pos,
    φ.cutoff_smooth_away_pole,
    φ.smooth_away_pole,
    φ.compact_support,
    φ.cutoff_eq_one_near_pole,
    φ.model_eq_negative_log_near_pole,
    φ.model_eq_cutoff_negative_log,
    hsource_eq_laplace,
    hsource_compact,
    hsource_away,
    hsource_smooth⟩

/--
%%handwave
name:
  Existence of cutoff logarithmic models
statement:
  For a conformal background metric, every point on a connected Riemann
  surface admits a compactly supported logarithmic cutoff pole model.
proof:
  Choose a coordinate disk around the point and a smooth bump function that is
  one on a smaller disk and zero outside the coordinate disk.  Multiplying the
  local function \(-\log |z-z(p)|\) by this bump gives the model.  Since the
  metric is conformal in the holomorphic coordinate, the Laplace-Beltrami
  operator is a smooth positive multiple of the Euclidean Laplacian there.
  The logarithm is therefore harmonic away from \(p\), so the source is smooth
  and supported where the cutoff varies.
-/
theorem exists_logarithmicCutoffPoleModel
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [RiemannSurface X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (hconformal : BackgroundSurfaceMetricConformalToComplexStructure g)
    (p : X) :
    Nonempty (LogarithmicCutoffPoleModel g p) := by
  rcases exists_logarithmicCutoffPoleModel_canonical_data X g.metric hconformal p with
    ⟨toFun, cutoff, coordinate, innerRadius, source, hinner_pos,
      hcutoff_smooth, hmodel_smooth, hmodel_compact, hcutoff_eq_one,
      hmodel_eq_negative_log, hmodel_eq_cutoff, hsource_eq_laplace,
      hsource_compact, hsource_away, hsource_smooth⟩
  refine ⟨
    { toFun := toFun
      cutoff := cutoff
      coordinate := coordinate
      innerRadius := innerRadius
      innerRadius_pos := hinner_pos
      cutoff_smooth_away_pole := hcutoff_smooth
      smooth_away_pole := hmodel_smooth
      compact_support := hmodel_compact
      cutoff_eq_one_near_pole := hcutoff_eq_one
      model_eq_negative_log_near_pole := hmodel_eq_negative_log
      model_eq_cutoff_negative_log := hmodel_eq_cutoff
      source := source
      source_eq_laplace := ?_
      source_compact_support := hsource_compact
      source_support_away_pole := hsource_away
      source_smooth := hsource_smooth }⟩
  intro x hx
  have hoperator :
      g.laplaceBeltrami toFun x =
        surfaceDivergenceFormLaplaceBeltrami g.metric toFun x := by
    exact congrFun (congrFun
      (BackgroundSurfaceMetricOnSurface.laplaceBeltrami_eq_divergence g)
      toFun) x
  exact hoperator.trans (hsource_eq_laplace x hx)

end Uniformization

end JJMath
