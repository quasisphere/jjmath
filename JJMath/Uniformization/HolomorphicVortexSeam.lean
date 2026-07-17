import JJMath.Uniformization.GreenFunctionCore
import JJMath.Uniformization.PlanarVortexPair

/-!
# Smooth cancellation across a holomorphic coordinate seam

Two consecutive vortex pairs may be written in different surface
coordinates.  At their common endpoint, the apparent zero and pole cancel.
The only residual factor is the unit phase of the divided difference of the
holomorphic coordinate transition.  Since that divided difference extends
analytically and is nonzero at the endpoint, its unit phase extends smoothly
as well.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

/-- The unit phase of the divided difference of `F` at `z₀`. -/
def holomorphicDividedDifferenceUnitPhase
    (F : ℂ → ℂ) (z₀ z : ℂ) : ℂ :=
  dslope F z₀ z / ‖dslope F z₀ z‖

private theorem contDiffAt_complex_to_real
    {f : ℂ → ℂ} {z : ℂ} (h : ContDiffAt ℂ ∞ f z) :
    ContDiffAt ℝ ∞ f z :=
  @ContDiffAt.restrict_scalars ℝ inferInstance ℂ inferInstance
    inferInstance ℂ inferInstance inferInstance f z ∞ ℂ inferInstance
    inferInstance inferInstance
    (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ) inferInstance
    (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ) h

/-- A holomorphic divided difference with nonzero derivative has a smooth
unit phase on a ball around its base point.  Away from the base point this is
the normalized phase of the ordinary difference quotient. -/
theorem holomorphicDividedDifferenceUnitPhase_local
    {F : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀)
    (hderiv : deriv F z₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ z ∈ Metric.ball z₀ δ, dslope F z₀ z ≠ 0) ∧
      ContDiffOn ℝ ∞ (holomorphicDividedDifferenceUnitPhase F z₀)
        (Metric.ball z₀ δ) ∧
      (∀ z ∈ Metric.ball z₀ δ,
        ‖holomorphicDividedDifferenceUnitPhase F z₀ z‖ = 1) ∧
      ∀ z ∈ Metric.ball z₀ δ, z ≠ z₀ →
        holomorphicDividedDifferenceUnitPhase F z₀ z =
          ((F z - F z₀) / (z - z₀)) /
            ‖(F z - F z₀) / (z - z₀)‖ := by
  let q : ℂ → ℂ := dslope F z₀
  have hq_an : AnalyticAt ℂ q z₀ := by
    rcases hF with ⟨pF, hpF⟩
    exact (HasFPowerSeriesAt.has_fpower_series_dslope_fslope hpF).analyticAt
  have hq_z₀_ne : q z₀ ≠ 0 := by
    simpa [q, dslope_same] using hderiv
  rcases hq_an.exists_ball_analyticOnNhd with
    ⟨r_an, hr_an_pos, hq_an_ball⟩
  have hq_ne_nhds : {z : ℂ | q z ≠ 0} ∈ 𝓝 z₀ :=
    hq_an.differentiableAt.continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds hq_z₀_ne)
  rcases Metric.mem_nhds_iff.mp hq_ne_nhds with
    ⟨r_ne, hr_ne_pos, hq_ne_ball⟩
  let δ : ℝ := min r_an r_ne
  have hδ_pos : 0 < δ := by
    exact lt_min hr_an_pos hr_ne_pos
  have hq_an_on :
      ∀ z ∈ Metric.ball z₀ δ, AnalyticAt ℂ q z := by
    intro z hz
    exact hq_an_ball z (Metric.ball_subset_ball (min_le_left _ _) hz)
  have hq_ne_on :
      ∀ z ∈ Metric.ball z₀ δ, q z ≠ 0 := by
    intro z hz
    exact hq_ne_ball (Metric.ball_subset_ball (min_le_right _ _) hz)
  have hsmooth : ContDiffOn ℝ ∞
      (holomorphicDividedDifferenceUnitPhase F z₀)
      (Metric.ball z₀ δ) := by
    intro z hz
    have hqR : ContDiffAt ℝ ∞ q z :=
      contDiffAt_complex_to_real (hq_an_on z hz).contDiffAt
    have hnorm : ContDiffAt ℝ ∞ (fun w : ℂ ↦ ‖q w‖) z :=
      hqR.norm ℝ (hq_ne_on z hz)
    have hnormC : ContDiffAt ℝ ∞
        (fun w : ℂ ↦ ((‖q w‖ : ℝ) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z hnorm
    exact (hqR.mul (hnormC.inv (by
      exact_mod_cast norm_ne_zero_iff.mpr (hq_ne_on z hz)))).contDiffWithinAt
  have hnorm : ∀ z ∈ Metric.ball z₀ δ,
      ‖holomorphicDividedDifferenceUnitPhase F z₀ z‖ = 1 := by
    intro z hz
    unfold holomorphicDividedDifferenceUnitPhase
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self]
    exact norm_ne_zero_iff.mpr (hq_ne_on z hz)
  refine ⟨δ, hδ_pos, ?_, hsmooth, hnorm, ?_⟩
  · simpa [q] using hq_ne_on
  · intro z hz hz_ne
    have hq_eq : dslope F z₀ z = (F z - F z₀) / (z - z₀) := by
      rw [dslope_of_ne F hz_ne]
      simp [slope, div_eq_inv_mul, smul_eq_mul, mul_comm]
    simp only [holomorphicDividedDifferenceUnitPhase, hq_eq]

/-- For two pointed surface coordinates, the unit phase of the holomorphic
transition's divided difference is smooth and nonvanishing near the marked
coordinate value.  Off the marked point it is the normalized coordinate
difference quotient. -/
theorem pointedCoordinate_transition_unitPhase_local
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {p : X}
    (χ ψ : PointedSurfaceCoordinate X p) :
    let F : ℂ → ℂ := fun z ↦ χ.chart (ψ.chart.symm z)
    let z₀ : ℂ := ψ.chart p
    ∃ δ : ℝ, 0 < δ ∧
      ContDiffOn ℝ ∞ (holomorphicDividedDifferenceUnitPhase F z₀)
        (Metric.ball z₀ δ) ∧
      (∀ z ∈ Metric.ball z₀ δ,
        ‖holomorphicDividedDifferenceUnitPhase F z₀ z‖ = 1) ∧
      ∀ z ∈ Metric.ball z₀ δ, z ≠ z₀ →
        holomorphicDividedDifferenceUnitPhase F z₀ z =
          ((F z - F z₀) / (z - z₀)) /
            ‖(F z - F z₀) / (z - z₀)‖ := by
  dsimp only
  let F : ℂ → ℂ := fun z ↦ χ.chart (ψ.chart.symm z)
  let z₀ : ℂ := ψ.chart p
  have hz₀_target : z₀ ∈ ψ.chart.target := by
    exact ψ.chart.map_source ψ.base_mem_source
  have hz₀_sourceχ : ψ.chart.symm z₀ ∈ χ.chart.source := by
    simpa [z₀, ψ.chart.left_inv ψ.base_mem_source] using χ.base_mem_source
  have hF_an : AnalyticAt ℂ F z₀ := by
    exact chartTransition_analyticAt ψ.chart ψ.chart_mem_atlas
      χ.chart χ.chart_mem_atlas hz₀_target hz₀_sourceχ
  have hderiv : deriv F z₀ ≠ 0 := by
    simpa [F, z₀] using pointedCoordinate_transition_deriv_ne_zero X χ ψ
  rcases holomorphicDividedDifferenceUnitPhase_local hF_an hderiv with
    ⟨δ, hδ, _hne, hsmooth, hnorm, hratio⟩
  exact ⟨δ, hδ, hsmooth, hnorm, hratio⟩

/-! ## The full consecutive-pair seam -/

/-- The analytic factor left after a pole in the `F`-coordinate cancels a
zero in the source coordinate. -/
def holomorphicVortexSeamFactor
    (F : ℂ → ℂ) (z₀ α β z : ℂ) : ℂ :=
  ((F z - α) / (z - β)) / dslope F z₀ z

/-- The unit phase of the analytic seam factor. -/
def holomorphicVortexSeamPhase
    (F : ℂ → ℂ) (z₀ α β z : ℂ) : ℂ :=
  holomorphicVortexSeamFactor F z₀ α β z /
    ‖holomorphicVortexSeamFactor F z₀ α β z‖

private theorem normalized_mul_normalized
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (u / ‖u‖) * (v / ‖v‖) = (u * v) / ‖u * v‖ := by
  rw [norm_mul]
  push_cast
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hv]

/-- The product of two consecutive raw vortex phases extends smoothly over
their common endpoint.  The first pair has its pole at `F z₀`, in the target
coordinate of `F`; the second has its zero at `z₀`, in the source coordinate.
The other endpoints are `α` and `β` respectively. -/
theorem holomorphicVortexSeamPhase_local
    {F : ℂ → ℂ} {z₀ α β : ℂ}
    (hF : AnalyticAt ℂ F z₀) (hderiv : deriv F z₀ ≠ 0)
    (hα : F z₀ ≠ α) (hβ : z₀ ≠ β) :
    ∃ δ : ℝ, 0 < δ ∧
      ContDiffOn ℝ ∞ (holomorphicVortexSeamPhase F z₀ α β)
        (Metric.ball z₀ δ) ∧
      (∀ z ∈ Metric.ball z₀ δ,
        ‖holomorphicVortexSeamPhase F z₀ α β z‖ = 1) ∧
      ∀ z ∈ Metric.ball z₀ δ, z ≠ z₀ →
        (((F z - α) / (F z - F z₀)) /
            ‖(F z - α) / (F z - F z₀)‖) *
          (((z - z₀) / (z - β)) /
            ‖(z - z₀) / (z - β)‖) =
          holomorphicVortexSeamPhase F z₀ α β z := by
  let q : ℂ → ℂ := dslope F z₀
  have hq_an : AnalyticAt ℂ q z₀ := by
    rcases hF with ⟨pF, hpF⟩
    exact (HasFPowerSeriesAt.has_fpower_series_dslope_fslope hpF).analyticAt
  have hq_z₀_ne : q z₀ ≠ 0 := by
    simpa [q, dslope_same] using hderiv
  rcases hF.exists_ball_analyticOnNhd with
    ⟨rF, hrF_pos, hF_an_ball⟩
  rcases hq_an.exists_ball_analyticOnNhd with
    ⟨rq, hrq_pos, hq_an_ball⟩
  have hballF_nhds : Metric.ball z₀ rF ∈ 𝓝 z₀ :=
    Metric.ball_mem_nhds z₀ hrF_pos
  have hballq_nhds : Metric.ball z₀ rq ∈ 𝓝 z₀ :=
    Metric.ball_mem_nhds z₀ hrq_pos
  have hq_ne_nhds : {z : ℂ | q z ≠ 0} ∈ 𝓝 z₀ :=
    hq_an.differentiableAt.continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds hq_z₀_ne)
  have hFα_ne_nhds : {z : ℂ | F z ≠ α} ∈ 𝓝 z₀ :=
    hF.differentiableAt.continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds hα)
  have hβ_ne_nhds : {z : ℂ | z ≠ β} ∈ 𝓝 z₀ :=
    isOpen_ne.mem_nhds hβ
  have hgood_nhds :
      Metric.ball z₀ rF ∩
        (Metric.ball z₀ rq ∩
          ({z : ℂ | q z ≠ 0} ∩
            ({z : ℂ | F z ≠ α} ∩ {z : ℂ | z ≠ β}))) ∈ 𝓝 z₀ :=
    Filter.inter_mem hballF_nhds
      (Filter.inter_mem hballq_nhds
        (Filter.inter_mem hq_ne_nhds
          (Filter.inter_mem hFα_ne_nhds hβ_ne_nhds)))
  rcases Metric.mem_nhds_iff.mp hgood_nhds with
    ⟨δ, hδ_pos, hball_good⟩
  have hF_on : ∀ z ∈ Metric.ball z₀ δ, AnalyticAt ℂ F z := by
    intro z hz
    exact hF_an_ball z (hball_good hz).1
  have hq_on : ∀ z ∈ Metric.ball z₀ δ, AnalyticAt ℂ q z := by
    intro z hz
    exact hq_an_ball z (hball_good hz).2.1
  have hq_ne_on : ∀ z ∈ Metric.ball z₀ δ, q z ≠ 0 := by
    intro z hz
    exact (hball_good hz).2.2.1
  have hFα_ne_on : ∀ z ∈ Metric.ball z₀ δ, F z ≠ α := by
    intro z hz
    exact (hball_good hz).2.2.2.1
  have hβ_ne_on : ∀ z ∈ Metric.ball z₀ δ, z ≠ β := by
    intro z hz
    exact (hball_good hz).2.2.2.2
  have hfactor_ne : ∀ z ∈ Metric.ball z₀ δ,
      holomorphicVortexSeamFactor F z₀ α β z ≠ 0 := by
    intro z hz
    exact div_ne_zero
      (div_ne_zero (sub_ne_zero.mpr (hFα_ne_on z hz))
        (sub_ne_zero.mpr (hβ_ne_on z hz)))
      (hq_ne_on z hz)
  have hfactor_contDiffAt : ∀ z ∈ Metric.ball z₀ δ,
      ContDiffAt ℝ ∞ (holomorphicVortexSeamFactor F z₀ α β) z := by
    intro z hz
    have hFR : ContDiffAt ℝ ∞ F z :=
      contDiffAt_complex_to_real (hF_on z hz).contDiffAt
    have hqR : ContDiffAt ℝ ∞ q z :=
      contDiffAt_complex_to_real (hq_on z hz).contDiffAt
    have hnum : ContDiffAt ℝ ∞ (fun w : ℂ ↦ F w - α) z :=
      hFR.sub contDiffAt_const
    have hden : ContDiffAt ℝ ∞ (fun w : ℂ ↦ w - β) z :=
      contDiffAt_id.sub contDiffAt_const
    exact (hnum.mul (hden.inv (sub_ne_zero.mpr (hβ_ne_on z hz)))).mul
      (hqR.inv (hq_ne_on z hz))
  have hfactor_smooth : ContDiffOn ℝ ∞
      (holomorphicVortexSeamFactor F z₀ α β)
      (Metric.ball z₀ δ) := by
    intro z hz
    exact (hfactor_contDiffAt z hz).contDiffWithinAt
  have hphase_smooth : ContDiffOn ℝ ∞
      (holomorphicVortexSeamPhase F z₀ α β)
      (Metric.ball z₀ δ) := by
    intro z hz
    have hfactor_at' : ContDiffAt ℝ ∞
        (holomorphicVortexSeamFactor F z₀ α β) z :=
      hfactor_contDiffAt z hz
    have hnorm_at : ContDiffAt ℝ ∞
        (fun w : ℂ ↦ ‖holomorphicVortexSeamFactor F z₀ α β w‖) z :=
      hfactor_at'.norm ℝ (hfactor_ne z hz)
    have hnormC_at : ContDiffAt ℝ ∞
        (fun w : ℂ ↦
          ((‖holomorphicVortexSeamFactor F z₀ α β w‖ : ℝ) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z hnorm_at
    exact (hfactor_at'.mul (hnormC_at.inv (by
      exact_mod_cast norm_ne_zero_iff.mpr (hfactor_ne z hz)))).contDiffWithinAt
  have hphase_norm : ∀ z ∈ Metric.ball z₀ δ,
      ‖holomorphicVortexSeamPhase F z₀ α β z‖ = 1 := by
    intro z hz
    unfold holomorphicVortexSeamPhase
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self]
    exact norm_ne_zero_iff.mpr (hfactor_ne z hz)
  refine ⟨δ, hδ_pos, hphase_smooth, hphase_norm, ?_⟩
  intro z hz hz_ne
  have hq_eq : dslope F z₀ z = (F z - F z₀) / (z - z₀) := by
    rw [dslope_of_ne F hz_ne]
    simp [slope, div_eq_inv_mul, smul_eq_mul, mul_comm]
  have hFdiff : F z - F z₀ ≠ 0 := by
    intro h
    have hq_ne : dslope F z₀ z ≠ 0 := by
      simpa [q] using hq_ne_on z hz
    apply hq_ne
    rw [hq_eq, h]
    simp
  have hfirst : (F z - α) / (F z - F z₀) ≠ 0 := by
    exact div_ne_zero (sub_ne_zero.mpr (hFα_ne_on z hz)) hFdiff
  have hsecond : (z - z₀) / (z - β) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hz_ne) (sub_ne_zero.mpr (hβ_ne_on z hz))
  rw [normalized_mul_normalized hfirst hsecond]
  have hproduct :
      ((F z - α) / (F z - F z₀)) * ((z - z₀) / (z - β)) =
        holomorphicVortexSeamFactor F z₀ α β z := by
    unfold holomorphicVortexSeamFactor
    rw [hq_eq]
    field_simp [sub_ne_zero.mpr hz_ne,
      sub_ne_zero.mpr (hβ_ne_on z hz), hFdiff]
  rw [hproduct]
  rfl

end

end JJMath.Uniformization
