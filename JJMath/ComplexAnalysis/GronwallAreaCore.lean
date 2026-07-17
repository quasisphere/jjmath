import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import JJMath.Manifold.OneFormPeriod

/-!
# Geometric and measure-theoretic core of Grönwall's area theorem

This file contains the topological containment and quantitative ellipse
estimates needed for the first-coefficient form of Grönwall's area theorem.
-/

open scoped ENNReal Interval Topology
open Filter MeasureTheory Metric Set Topology

noncomputable section

namespace JJMath.ComplexAnalysis

private theorem isPreconnected_exterior (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected {z : ℂ | R < ‖z‖} := by
  let S : Set (ℝ × ℂ) := Ioi R ×ˢ sphere (0 : ℂ) 1
  let p : ℝ × ℂ → ℂ := fun x ↦ x.1 • x.2
  have hrank : 1 < Module.rank ℝ ℂ := by norm_num
  have hS : IsPreconnected S :=
    isPreconnected_Ioi.prod
      (isPreconnected_sphere hrank (0 : ℂ) 1)
  have hp : Continuous p := by
    change Continuous (fun x : ℝ × ℂ ↦ (x.1 : ℂ) * x.2)
    fun_prop
  have himage : p '' S = {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      have hr0 : 0 < r := hR.trans_lt hr
      simpa [p, mem_sphere_zero_iff_norm.mp hu, norm_smul, abs_of_pos hr0] using hr
    · intro hz
      have hz0 : ‖z‖ ≠ 0 := by
        intro hzero
        have : z = 0 := norm_eq_zero.mp hzero
        subst z
        exact (not_lt_of_ge hR (by simpa using hz)).elim
      refine ⟨(‖z‖, (‖z‖⁻¹ : ℝ) * z), ⟨hz, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hz0]
      · change (‖z‖ : ℂ) * ((‖z‖⁻¹ : ℝ) * z) = z
        push_cast
        have hcast : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hz0
        rw [← mul_assoc, mul_inv_cancel₀ hcast, one_mul]
  rw [← himage]
  exact hS.image p hp.continuousOn

private theorem exists_exterior_image_above
    {G : ℂ → ℂ}
    (hG : Tendsto (fun z ↦ G z - z) (cocompact ℂ) (𝓝 0))
    (L : ℂ →L[ℝ] ℝ) (hL : L ≠ 0) (R u : ℝ) :
    ∃ z : ℂ, R < ‖z‖ ∧ u < L (G z) := by
  have hex : ∃ v : ℂ, L v ≠ 0 := by
    by_contra h
    push Not at h
    exact hL (ContinuousLinearMap.ext fun v ↦ by simpa using h v)
  rcases hex with ⟨v, hv⟩
  let w : ℂ := (L v)⁻¹ • v
  have hLw : L w = 1 := by
    rw [show w = (L v)⁻¹ • v by rfl, map_smul]
    exact inv_mul_cancel₀ hv
  have hw : w ≠ 0 := by
    intro hw
    simp [hw] at hLw
  have hnormw : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hnorm : Tendsto (fun t : ℝ ↦ ‖t • w‖) atTop atTop := by
    have hmul : Tendsto (fun t : ℝ ↦ t * ‖w‖) atTop atTop :=
      tendsto_id.atTop_mul_const hnormw
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [Real.norm_eq_abs, abs_of_nonneg ht]
  have hray : Tendsto (fun t : ℝ ↦ t • w) atTop (cocompact ℂ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop 0
    simpa [dist_zero_right] using hnorm
  have herr : Tendsto (fun t : ℝ ↦ G (t • w) - t • w) atTop (𝓝 0) :=
    hG.comp hray
  have hLerr :
      Tendsto (fun t : ℝ ↦ L (G (t • w) - t • w)) atTop (𝓝 0) :=
    by simpa only [Function.comp_apply, map_zero] using
      L.continuous.continuousAt.tendsto.comp herr
  have hLG : Tendsto (fun t : ℝ ↦ L (G (t • w))) atTop atTop := by
    have hadd := tendsto_id.atTop_add hLerr
    apply hadd.congr'
    filter_upwards with t
    have hLtw : L (t • w) = t := by rw [map_smul, hLw]; simp
    rw [map_sub, hLtw]
    simp
  have hevent : ∀ᶠ t : ℝ in atTop,
      R < ‖t • w‖ ∧ u < L (G (t • w)) :=
    (hnorm.eventually_gt_atTop R).and (hLG.eventually_gt_atTop u)
  rcases hevent.exists with ⟨t, htR, htu⟩
  exact ⟨t • w, htR, htu⟩

private theorem isClosed_image_exterior_of_tendsto_sub_id
    {G : ℂ → ℂ} {R : ℝ}
    (hGcont : ContinuousOn G {z : ℂ | R ≤ ‖z‖})
    (hGinf : Tendsto (fun z ↦ G z - z) (cocompact ℂ) (𝓝 0)) :
    IsClosed (G '' {z : ℂ | R ≤ ‖z‖}) := by
  let D : Set ℂ := {z : ℂ | R ≤ ‖z‖}
  let f : D → ℂ := fun z ↦ G z
  have hDclosed : IsClosed D := isClosed_le continuous_const continuous_norm
  have hfcont : Continuous f :=
    hGcont.comp_continuous continuous_subtype_val fun z ↦ z.property
  have hnormG : Tendsto (fun z : ℂ ↦ ‖G z‖) (cocompact ℂ) atTop := by
    rw [Filter.tendsto_atTop]
    intro A
    have hnormz := (tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop (A + 1)
    have herr : ∀ᶠ z : ℂ in cocompact ℂ, ‖G z - z‖ < 1 := by
      filter_upwards [hGinf (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with z hz
      simpa [Metric.mem_ball, dist_zero_right] using hz
    filter_upwards [hnormz, herr] with z hz he
    have htri : ‖z‖ ≤ ‖G z‖ + ‖G z - z‖ := by
      calc
        ‖z‖ = ‖G z - (G z - z)‖ := by congr 1; abel
        _ ≤ ‖G z‖ + ‖G z - z‖ := norm_sub_le _ _
    linarith
  have hGcocompact : Tendsto G (cocompact ℂ) (cocompact ℂ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop 0
    simpa [dist_zero_right] using hnormG
  have hval : Tendsto (fun z : D ↦ (z : ℂ)) (cocompact D) (cocompact ℂ) :=
    hDclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hfproper : IsProperMap f :=
    isProperMap_iff_tendsto_cocompact.mpr ⟨hfcont, hGcocompact.comp hval⟩
  have hrange : IsClosed (Set.range f) := by
    simpa only [Set.image_univ] using hfproper.isClosedMap _ isClosed_univ
  convert hrange using 1
  ext y
  simp [f, D]

/--
The compact set omitted by an exterior univalent map lies in the closed convex
hull of the image of the boundary circle.  This is the topological input in
the area proof; it uses only openness, properness at the finite boundary, and
the normalization at infinity.
-/
theorem complement_exterior_image_subset_closedConvexHull
    {G : ℂ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hGanalytic : AnalyticOnNhd ℂ G {z : ℂ | R < ‖z‖})
    (hGinj : Set.InjOn G {z : ℂ | R ≤ ‖z‖})
    (hGclosed : IsClosed (G '' {z : ℂ | R ≤ ‖z‖}))
    (hGinf : Tendsto (fun z ↦ G z - z) (cocompact ℂ) (𝓝 0)) :
    (G '' {z : ℂ | R < ‖z‖})ᶜ ⊆
      closedConvexHull ℝ (G '' sphere (0 : ℂ) R) := by
  let U : Set ℂ := {z : ℂ | R < ‖z‖}
  let D : Set ℂ := {z : ℂ | R ≤ ‖z‖}
  let B : Set ℂ := G '' sphere (0 : ℂ) R
  let E : Set ℂ := G '' U
  let C : Set ℂ := closedConvexHull ℝ B
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hEopen : IsOpen E := by
    rcases hGanalytic.is_constant_or_isOpen (isPreconnected_exterior R hR) with hconst | hopen
    · exfalso
      rcases hconst with ⟨c, hconst⟩
      let z₁ : ℂ := (R + 1 : ℝ)
      let z₂ : ℂ := (R + 2 : ℝ)
      have hz₁U : z₁ ∈ U := by
        change R < ‖z₁‖
        rw [show z₁ = (R + 1 : ℝ) by rfl, Complex.norm_real]
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      have hz₂U : z₂ ∈ U := by
        change R < ‖z₂‖
        rw [show z₂ = (R + 2 : ℝ) by rfl, Complex.norm_real]
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      have hz₁D : z₁ ∈ D := by exact le_of_lt (show R < ‖z₁‖ from hz₁U)
      have hz₂D : z₂ ∈ D := by exact le_of_lt (show R < ‖z₂‖ from hz₂U)
      have hz : z₁ = z₂ := hGinj hz₁D hz₂D ((hconst z₁ hz₁U).trans (hconst z₂ hz₂U).symm)
      norm_num [z₁, z₂] at hz
    · exact hopen U Subset.rfl hUopen
  have hDdecomp : D = U ∪ sphere (0 : ℂ) R := by
    ext z
    simp [D, U, le_iff_lt_or_eq, eq_comm]
  have hDE : G '' D = E ∪ B := by
    rw [hDdecomp, Set.image_union]
  intro x hx
  by_contra hxC
  have hCclosed : IsClosed C := isClosed_closedConvexHull
  have hCconvex : Convex ℝ C := convex_closedConvexHull
  rcases geometric_hahn_banach_closed_point hCconvex hCclosed hxC with
    ⟨L, u, hLC, hLx⟩
  have hBC : B ⊆ C := subset_closedConvexHull
  have hLne : L ≠ 0 := by
    intro hzero
    have hGRB : G (R : ℂ) ∈ B := by
      refine ⟨(R : ℂ), ?_, rfl⟩
      simp [abs_of_nonneg hR]
    have := hLC (G (R : ℂ)) (hBC hGRB)
    simp [hzero] at this hLx
    linarith
  rcases exists_exterior_image_above hGinf L hLne R u with ⟨z, hzU, hzL⟩
  let H : Set ℂ := {y : ℂ | u < L y}
  have hHopen : IsOpen H := isOpen_lt continuous_const L.continuous
  have hHpre : IsPreconnected H :=
    (convex_halfSpace_gt L.isLinear u).isPreconnected
  have hHB : Disjoint H B := by
    rw [Set.disjoint_left]
    intro y hyH hyB
    exact (not_lt_of_ge (hLC y (hBC hyB)).le) hyH
  have hEsubD : E ⊆ G '' D := by
    rw [hDE]
    exact subset_union_left
  have hcover : H ⊆ E ∪ (G '' D)ᶜ := by
    intro y hyH
    by_cases hyD : y ∈ G '' D
    · rw [hDE] at hyD
      rcases hyD with hyE | hyB
      · exact Or.inl hyE
      · exact (hHB.le_bot ⟨hyH, hyB⟩).elim
    · exact Or.inr hyD
  have hdisj : Disjoint E (G '' D)ᶜ :=
    disjoint_compl_right.mono_left hEsubD
  have hnonempty : (H ∩ E).Nonempty :=
    ⟨G z, hzL, z, hzU, rfl⟩
  have hHE : H ⊆ E :=
    hHpre.subset_left_of_subset_union hEopen hGclosed.isOpen_compl hdisj
      hcover (by simpa [inter_comm] using hnonempty)
  exact hx (hHE hLx)

/-- The normalized Laurent form used in the first-coefficient area theorem. -/
def exteriorLaurentMap (b : ℂ) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  z + b * z⁻¹ + h z⁻¹

@[simp]
theorem exteriorLaurentMap_sub_id (b : ℂ) (h : ℂ → ℂ) (z : ℂ) :
    exteriorLaurentMap b h z - z = b * z⁻¹ + h z⁻¹ := by
  simp [exteriorLaurentMap]
  ring

private theorem tendsto_inv_cocompact_zero :
    Tendsto (fun z : ℂ ↦ z⁻¹) (cocompact ℂ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [norm_inv] using
    (tendsto_norm_cocompact_atTop (E := ℂ)).inv_tendsto_atTop

private theorem exteriorLaurentMap_tendsto_sub_id
    {b : ℂ} {h : ℂ → ℂ} (hh : ContinuousAt h 0) (h0 : h 0 = 0) :
    Tendsto (fun z ↦ exteriorLaurentMap b h z - z) (cocompact ℂ) (𝓝 0) := by
  have hinv := tendsto_inv_cocompact_zero
  have hb : Tendsto (fun z : ℂ ↦ b * z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have hh' : Tendsto (fun z : ℂ ↦ h z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa [h0] using hh.tendsto.comp hinv
  simpa [exteriorLaurentMap_sub_id] using hb.add hh'

theorem exteriorLaurentMap_analyticOn_exterior
    {b : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (ball 0 1)) {R : ℝ} (hR : 1 ≤ R) :
    AnalyticOnNhd ℂ (exteriorLaurentMap b h) {z : ℂ | R < ‖z‖} := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    have hz' : R < 0 := by simpa using hz
    linarith
  have hinv : AnalyticAt ℂ (fun z : ℂ ↦ z⁻¹) z := analyticAt_inv hz0
  have hinv_mem : z⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_one₀ (norm_pos_iff.mpr hz0)).2 (hR.trans_lt hz)
  exact analyticAt_id.add (analyticAt_const.mul hinv) |>.add
    ((hh z⁻¹ hinv_mem).comp hinv)

private theorem exteriorLaurentMap_continuousOn_closedExterior
    {b : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (ball 0 1)) {R : ℝ} (hR : 1 < R) :
    ContinuousOn (exteriorLaurentMap b h) {z : ℂ | R ≤ ‖z‖} := by
  intro z hz
  have hz' : 1 < ‖z‖ := hR.trans_le hz
  exact (exteriorLaurentMap_analyticOn_exterior (R := 1) hh le_rfl z hz').continuousAt.continuousWithinAt

/-- An analytic function whose value and first derivative vanish has a quadratic
bound on a sufficiently small disk. -/
theorem analytic_quadratic_bound
    {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 0) (h1 : deriv h 0 = 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ z : ℂ, ‖z‖ < ρ → ‖h z‖ ≤ C * ‖z‖ ^ 2 := by
  rcases hh.exists_eq_sum_add_pow_mul 2 with ⟨H, hH, heq⟩
  have hform : ∀ z : ℂ, h z = z ^ 2 * H z := by
    intro z
    rw [heq]
    have hi0 : iteratedDeriv 0 h 0 = 0 := by simp [iteratedDeriv_zero, h0]
    have hi1 : iteratedDeriv 1 h 0 = 0 := by simp [iteratedDeriv_one, h1]
    simp [Finset.sum_range_succ, hi0, hi1, smul_eq_mul]
  have hcont : ContinuousAt H 0 := hH.continuousAt
  have hevent : ∀ᶠ z : ℂ in 𝓝 0, ‖H z‖ < ‖H 0‖ + 1 := by
    have : Tendsto (fun z : ℂ ↦ ‖H z‖) (𝓝 0) (𝓝 ‖H 0‖) := hcont.norm
    exact (this.eventually (Iio_mem_nhds (lt_add_one ‖H 0‖)))
  rcases Metric.eventually_nhds_iff_ball.mp hevent with ⟨ρ, hρ, hbound⟩
  refine ⟨ρ, ‖H 0‖ + 1, hρ, by positivity, ?_⟩
  intro z hz
  rw [hform, norm_mul, norm_pow]
  have hb := mul_le_mul_of_nonneg_left
    (hbound z (by simpa [mem_ball] using hz)).le (sq_nonneg ‖z‖)
  simpa [mul_comm] using hb

/-- The real-linear ellipse map `z ↦ z + c * conj z`. -/
def ellipseLinearMap (c : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ + c • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp]
theorem ellipseLinearMap_apply (c z : ℂ) :
    ellipseLinearMap c z = z + c * starRingEnd ℂ z := by
  change z + c * Complex.conjCLE z = z + c * starRingEnd ℂ z
  rw [Complex.conjCLE_apply]

theorem ellipseLinearMap_det (c : ℂ) :
    LinearMap.det (ellipseLinearMap c : ℂ →ₗ[ℝ] ℂ) = 1 - ‖c‖ ^ 2 := by
  calc
    LinearMap.det (ellipseLinearMap c).toLinearMap =
        (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (ellipseLinearMap c).toLinearMap).det :=
      (LinearMap.det_toMatrix Complex.basisOneI (ellipseLinearMap c).toLinearMap).symm
    _ = 1 - ‖c‖ ^ 2 := by
      rw [Matrix.det_fin_two]
      have h_one : (ellipseLinearMap c : ℂ →ₗ[ℝ] ℂ) (1 : ℂ) = 1 + c := by
        simp [ellipseLinearMap_apply]
      have h_I : (ellipseLinearMap c : ℂ →ₗ[ℝ] ℂ) Complex.I =
          Complex.I - c * Complex.I := by
        simp [ellipseLinearMap_apply, sub_eq_add_neg]
      simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Complex.coe_basisOneI_repr]
      erw [h_one, h_I]
      simp only [
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero,
        mul_one, zero_sub]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

private theorem ellipseLinearMap_norm_lower (c z : ℂ) :
    (1 - ‖c‖) * ‖z‖ ≤ ‖ellipseLinearMap c z‖ := by
  rw [ellipseLinearMap_apply]
  calc
    (1 - ‖c‖) * ‖z‖ = ‖z‖ - ‖c * starRingEnd ℂ z‖ := by
      rw [norm_mul, Complex.norm_conj]
      ring
    _ ≤ ‖z + c * starRingEnd ℂ z‖ := by
      simpa [sub_eq_add_neg] using
        norm_sub_norm_le z (-(c * starRingEnd ℂ z))

theorem exterior_omitted_measure_le_ellipse
    {b : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (ball 0 1)) (h0 : h 0 = 0)
    {ρ C R : ℝ} (_hρ : 0 < ρ) (_hC : 0 ≤ C)
    (hquad : ∀ z : ℂ, ‖z‖ < ρ → ‖h z‖ ≤ C * ‖z‖ ^ 2)
    (hR : 1 < R) (hbR : ‖b‖ < R ^ 2) (hinvR : R⁻¹ < ρ)
    (hinj : Set.InjOn (exteriorLaurentMap b h) {z : ℂ | R ≤ ‖z‖}) :
    volume ((exteriorLaurentMap b h '' {z : ℂ | R < ‖z‖})ᶜ) ≤
      ENNReal.ofReal (1 - (‖b‖ / R ^ 2) ^ 2) *
        volume (closedBall (0 : ℂ)
          (R + (C / R ^ 2) / (1 - ‖b‖ / R ^ 2))) := by
  let G := exteriorLaurentMap b h
  let c : ℂ := b / (R : ℂ) ^ 2
  let q : ℝ := ‖b‖ / R ^ 2
  let η : ℝ := C / R ^ 2
  let s : ℝ := R + η / (1 - q)
  let L : ℂ →L[ℝ] ℂ := ellipseLinearMap c
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR0
  have hq : q < 1 := by
    dsimp [q]
    exact (div_lt_one hR2).2 hbR
  have hq0 : 0 ≤ q := by positivity
  have hc : ‖c‖ = q := by
    simp [c, q, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR0]
  have hdet : LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
    rw [show LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) = 1 - ‖c‖ ^ 2 by
      simpa [L] using ellipseLinearMap_det c, hc]
    nlinarith
  have hGinf : Tendsto (fun z ↦ G z - z) (cocompact ℂ) (𝓝 0) := by
    exact exteriorLaurentMap_tendsto_sub_id (hh 0 (mem_ball_self zero_lt_one)).continuousAt h0
  have hGanalytic : AnalyticOnNhd ℂ G {z : ℂ | R < ‖z‖} :=
    exteriorLaurentMap_analyticOn_exterior hh hR.le
  have hGcont : ContinuousOn G {z : ℂ | R ≤ ‖z‖} :=
    exteriorLaurentMap_continuousOn_closedExterior hh hR
  have hGclosed : IsClosed (G '' {z : ℂ | R ≤ ‖z‖}) :=
    isClosed_image_exterior_of_tendsto_sub_id hGcont hGinf
  have htop :
      (G '' {z : ℂ | R < ‖z‖})ᶜ ⊆
        closedConvexHull ℝ (G '' sphere (0 : ℂ) R) :=
    complement_exterior_image_subset_closedConvexHull hR0.le hGanalytic hinj hGclosed hGinf
  have hboundary : G '' sphere (0 : ℂ) R ⊆ L '' closedBall (0 : ℂ) s := by
    rintro y ⟨z, hz, rfl⟩
    have hznorm : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
    have hz0 : z ≠ 0 := by
      intro hz0
      subst z
      simp at hznorm
      linarith
    have hinvnorm : ‖z⁻¹‖ = R⁻¹ := by rw [norm_inv, hznorm]
    have htail : ‖h z⁻¹‖ ≤ η := by
      calc
        ‖h z⁻¹‖ ≤ C * ‖z⁻¹‖ ^ 2 := hquad z⁻¹ (by simpa [hinvnorm] using hinvR)
        _ = η := by rw [hinvnorm]; simp [η, inv_pow, div_eq_mul_inv]
    have hcinv : c * starRingEnd ℂ z = b * z⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hznorm]
      dsimp [c]
      push_cast
      field_simp [hR0.ne']
    let e : ℂ ≃ₗ[ℝ] ℂ := (L : ℂ →ₗ[ℝ] ℂ).equivOfDetNeZero hdet
    let v : ℂ := e.symm (h z⁻¹)
    have hLv : L v = h z⁻¹ := by
      change e v = h z⁻¹
      simp [v]
    have hvbound : ‖v‖ ≤ η / (1 - q) := by
      have hlower := ellipseLinearMap_norm_lower c v
      rw [show L v = ellipseLinearMap c v by rfl, hLv, hc] at hlower
      apply (le_div_iff₀ (sub_pos.mpr hq)).2
      simpa [mul_comm] using hlower.trans htail
    refine ⟨z + v, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      calc
        ‖z + v‖ ≤ ‖z‖ + ‖v‖ := norm_add_le _ _
        _ ≤ R + η / (1 - q) := by rw [hznorm]; gcongr
        _ = s := rfl
    · change L (z + v) = G z
      rw [map_add, hLv]
      simp only [L, ellipseLinearMap_apply, G, exteriorLaurentMap]
      rw [hcinv]
  have htargetCompact : IsCompact (L '' closedBall (0 : ℂ) s) :=
    (isCompact_closedBall (0 : ℂ) s).image L.continuous
  have htargetConvex : Convex ℝ (L '' closedBall (0 : ℂ) s) :=
    (convex_closedBall (0 : ℂ) s).linear_image (L : ℂ →ₗ[ℝ] ℂ)
  have hhull : closedConvexHull ℝ (G '' sphere (0 : ℂ) R) ⊆
      L '' closedBall (0 : ℂ) s :=
    closedConvexHull_min hboundary htargetConvex htargetCompact.isClosed
  calc
    volume ((G '' {z : ℂ | R < ‖z‖})ᶜ)
        ≤ volume (L '' closedBall (0 : ℂ) s) := measure_mono (htop.trans hhull)
    _ = ENNReal.ofReal |LinearMap.det (L : ℂ →ₗ[ℝ] ℂ)| *
          volume (closedBall (0 : ℂ) s) :=
      MeasureTheory.Measure.addHaar_image_continuousLinearMap volume L _
    _ = ENNReal.ofReal (1 - q ^ 2) * volume (closedBall (0 : ℂ) s) := by
      rw [show LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) = 1 - q ^ 2 by
        simpa [L, hc] using ellipseLinearMap_det c]
      rw [abs_of_pos (by nlinarith)]
    _ = _ := by rfl

/-- Multiplication by a complex number, regarded as a real continuous linear map. -/
def complexMulReal (a : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ

@[simp]
theorem complexMulReal_apply (a z : ℂ) : complexMulReal a z = z * a := by
  simp [complexMulReal]

theorem complexMulReal_det (a : ℂ) :
    LinearMap.det (complexMulReal a : ℂ →ₗ[ℝ] ℂ) = ‖a‖ ^ 2 := by
  calc
    LinearMap.det (complexMulReal a).toLinearMap =
        (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (complexMulReal a).toLinearMap).det :=
      (LinearMap.det_toMatrix Complex.basisOneI (complexMulReal a).toLinearMap).symm
    _ = ‖a‖ ^ 2 := by
      rw [Matrix.det_fin_two]
      have h_one : (complexMulReal a : ℂ →ₗ[ℝ] ℂ) (1 : ℂ) = a := by simp
      have h_I : (complexMulReal a : ℂ →ₗ[ℝ] ℂ) Complex.I = Complex.I * a := by simp
      simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Complex.coe_basisOneI_repr]
      erw [h_one, h_I]
      simp only [
        Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, one_mul, zero_mul, zero_sub, zero_add]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

theorem exteriorLaurentMap_deriv
    {b : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (ball 0 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    deriv (exteriorLaurentMap b h) z =
      1 - b * z⁻¹ ^ 2 - deriv h z⁻¹ * z⁻¹ ^ 2 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at hz
  have hinvDeriv : HasDerivAt (fun z : ℂ ↦ z⁻¹) (-z⁻¹ ^ 2) z := by
    simpa using hasDerivAt_inv hz0
  have hinv_mem : z⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_one₀ (norm_pos_iff.mpr hz0)).2 hz
  have hh' : HasDerivAt h (deriv h z⁻¹) z⁻¹ :=
    (hh z⁻¹ hinv_mem).differentiableAt.hasDerivAt
  have htotal : HasDerivAt (fun w : ℂ ↦ w + b * w⁻¹ + h w⁻¹)
      (1 + b * (-z⁻¹ ^ 2) + deriv h z⁻¹ * (-z⁻¹ ^ 2)) z := by
    convert (hasDerivAt_id z).add ((hasDerivAt_const z b).mul hinvDeriv) |>.add
      (hh'.comp z hinvDeriv) using 1 <;> simp
  change deriv (fun w : ℂ ↦ w + b * w⁻¹ + h w⁻¹) z = _
  rw [htotal.deriv]
  ring

end JJMath.ComplexAnalysis
