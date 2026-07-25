import JJMath.Quasiconformal.CauchyTransform
import JJMath.Quasiconformal.ChangeOfVariables
import JJMath.Quasiconformal.Examples
import JJMath.Quasiconformal.LocalSobolev

/-!
# Isolated-point removability for planar Sobolev maps

This file develops the shrinking smooth cutoffs used to extend a weak
derivative identity across a single point.  The eventual application is the
reciprocal chart at infinity of a plane quasiconformal homeomorphism.
-/

namespace JJMath

open Set MeasureTheory Filter Metric
open scoped ENNReal Topology ContDiff

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Test function cut off near the origin
statement:
  Let $\varphi\in C_c^\infty(\mathbb C)$ and let $R>0$. The punctured
  test function
  $$
    \varphi_R(z)=(1-\beta_R(z))\varphi(z)
  $$
  is smooth and compactly supported in $\mathbb C\setminus\{0\}$, where
  $\beta_R$ equals one on $\overline B(0,R)$ and vanishes outside
  $\overline B(0,2R)$.
-/
def puncturedTestCutoff
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
      (Set.univ : Set ℂ))
    (R : ℝ) (hR : 0 < R) :
    JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
      ({0}ᶜ : Set ℂ) where
  toFun z := (1 - cauchyDiskCutoff R hR z) * φ z
  smooth :=
    (contDiff_const.sub (cauchyDiskCutoff R hR).contDiff).mul φ.smooth
  support_subset := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hz0
    subst z
    have hzero :
        (fun z : ℂ ↦
          (1 - cauchyDiskCutoff R hR z) * φ z) =ᶠ[𝓝 0]
            fun _ : ℂ ↦ 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
      rw [cauchyDiskCutoff_eq_one_of_norm_le hR]
      · simp
      · exact (by
          simpa [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < R).le
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hz
  compact_support :=
    φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_mul_subset_right
        (f := fun z : ℂ ↦ 1 - cauchyDiskCutoff R hR z)
        (g := (φ : ℂ → ℝ)))

/--
%%handwave
name:
  Value of the punctured test cutoff
statement:
  For every $z\in\mathbb C$,
  $$
    \varphi_R(z)=(1-\beta_R(z))\varphi(z).
  $$
proof:
  This is the defining formula for the cutoff test.
-/
@[simp]
theorem puncturedTestCutoff_apply
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
      (Set.univ : Set ℂ))
    (R : ℝ) (hR : 0 < R) (z : ℂ) :
    puncturedTestCutoff φ R hR z =
      (1 - cauchyDiskCutoff R hR z) * φ z :=
  rfl

/--
%%handwave
name:
  Product-rule differential of the punctured test cutoff
statement:
  For $R>0$,
  $$
    D\varphi_R(z)
      =(1-\beta_R(z))D\varphi(z)-\varphi(z)D\beta_R(z).
  $$
proof:
  Differentiate $(1-\beta_R)\varphi$ by the product rule.
-/
theorem fderiv_puncturedTestCutoff
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
      (Set.univ : Set ℂ))
    (R : ℝ) (hR : 0 < R) (z : ℂ) :
    fderiv ℝ (puncturedTestCutoff φ R hR : ℂ → ℝ) z =
      (1 - cauchyDiskCutoff R hR z) • fderiv ℝ (φ : ℂ → ℝ) z -
        φ z • fderiv ℝ (cauchyDiskCutoff R hR : ℂ → ℝ) z := by
  change fderiv ℝ
      (fun w : ℂ ↦ (1 - cauchyDiskCutoff R hR w) * φ w) z = _
  have hβsmooth : ContDiff ℝ ∞
      (cauchyDiskCutoff R hR : ℂ → ℝ) :=
    (cauchyDiskCutoff R hR).contDiff
  have hβ : DifferentiableAt ℝ
      (cauchyDiskCutoff R hR : ℂ → ℝ) z :=
    hβsmooth.differentiable (by simp) z
  have hφ : DifferentiableAt ℝ (φ : ℂ → ℝ) z :=
    φ.smooth.differentiable (by simp) z
  have hone : DifferentiableAt ℝ (fun _ : ℂ ↦ (1 : ℝ)) z :=
    differentiableAt_const 1
  calc
    fderiv ℝ (fun w : ℂ ↦
        (1 - cauchyDiskCutoff R hR w) * φ w) z =
        (1 - cauchyDiskCutoff R hR z) • fderiv ℝ (φ : ℂ → ℝ) z +
          φ z • fderiv ℝ
            (fun w : ℂ ↦ 1 - cauchyDiskCutoff R hR w) z := by
      simpa only [Pi.sub_apply] using fderiv_fun_mul (hone.sub hβ) hφ
    _ = (1 - cauchyDiskCutoff R hR z) • fderiv ℝ (φ : ℂ → ℝ) z -
          φ z • fderiv ℝ (cauchyDiskCutoff R hR : ℂ → ℝ) z := by
      have hsub : fderiv ℝ
          (fun w : ℂ ↦ 1 - cauchyDiskCutoff R hR w) z =
            fderiv ℝ (fun _ : ℂ ↦ (1 : ℝ)) z -
              fderiv ℝ (cauchyDiskCutoff R hR : ℂ → ℝ) z := by
        simpa only [Pi.sub_apply] using fderiv_sub hone hβ
      rw [hsub]
      have hconst : fderiv ℝ (fun _ : ℂ ↦ (1 : ℝ)) z = 0 :=
        congrFun (fderiv_const (𝕜 := ℝ) (E := ℂ) (1 : ℝ)) z
      rw [hconst]
      module

/--
%%handwave
name:
  Differential of the disk cutoff inside its inner disk
statement:
  If $R>0$ and $|z|<R$, then $D\beta_R(z)=0$.
proof:
  The cutoff is identically one on a neighborhood of $z$.
-/
theorem fderiv_cauchyDiskCutoff_eq_zero_of_norm_lt
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    fderiv ℝ (cauchyDiskCutoff R hR : ℂ → ℝ) z = 0 := by
  have hopen : IsOpen {w : ℂ | ‖w‖ < R} :=
    isOpen_lt continuous_norm continuous_const
  have heq :
      (cauchyDiskCutoff R hR : ℂ → ℝ) =ᶠ[𝓝 z]
        fun _ : ℂ ↦ 1 := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact cauchyDiskCutoff_eq_one_of_norm_le hR hw.le
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]
  simp

/--
%%handwave
name:
  Differential of the disk cutoff outside its support
statement:
  If $R>0$ and $2R<|z|$, then $D\beta_R(z)=0$.
proof:
  The cutoff is identically zero on a neighborhood of $z$.
-/
theorem fderiv_cauchyDiskCutoff_eq_zero_of_two_mul_lt_norm
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : 2 * R < ‖z‖) :
    fderiv ℝ (cauchyDiskCutoff R hR : ℂ → ℝ) z = 0 := by
  have hopen : IsOpen {w : ℂ | 2 * R < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  have heq :
      (cauchyDiskCutoff R hR : ℂ → ℝ) =ᶠ[𝓝 z]
        fun _ : ℂ ↦ 0 := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact cauchyDiskCutoff_eq_zero_of_two_mul_le_norm hR hw.le
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]
  simp

/--
%%handwave
name:
  Canonical shrinking point-removal radius
statement:
  The radius used for the $n$th point-removal cutoff is
  $$
    R_n=(n+1)^{-1}.
  $$
-/
def pointRemovabilityRadius (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹

/--
%%handwave
name:
  Positivity of the point-removal radii
statement:
  For every $n$, one has $R_n>0$.
proof:
  The real number $n+1$ is positive, so its inverse is positive.
-/
theorem pointRemovabilityRadius_pos (n : ℕ) :
    0 < pointRemovabilityRadius n := by
  dsimp [pointRemovabilityRadius]
  positivity

/--
%%handwave
name:
  Point-removal radii tend to zero
statement:
  The sequence $R_n=(n+1)^{-1}$ converges to $0$.
proof:
  The natural numbers tend to infinity, their reciprocals tend to zero, and
  shifting the index by one does not change the limit.
-/
theorem tendsto_pointRemovabilityRadius_zero :
    Tendsto pointRemovabilityRadius atTop (𝓝 0) := by
  exact tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Continuous finite-energy Sobolev maps are removable across one point
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous. Suppose $Df$ is its local
  $W^{1,2}$ weak differential on $\mathbb C\setminus\{0\}$ and that
  $Df\in L^2(K)$ for every compact $K\subseteq\mathbb C$. Then
  $f\in W^{1,2}_{\mathrm{loc}}(\mathbb C)$ with weak differential $Df$
  across the origin as well.
proof:
  Multiply every test function by $1-\beta_{R_n}$, where
  $R_n=(n+1)^{-1}$. The main product-rule terms converge by dominated
  convergence. The cutoff-derivative error is supported on
  $R_n\le|z|\le2R_n$ and is dominated by a compactly supported multiple of
  $|z|^{-1}$, which is locally integrable in two dimensions. Passing to the
  limit in the punctured weak derivative identity removes the point.
-/
theorem isLocalW12On_univ_of_compl_singleton_of_continuous
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hf : Continuous f)
    (hpunct : IsLocalW12On ({0}ᶜ : Set ℂ) f df)
    (hdfLp : ∀ K : Set ℂ, IsCompact K →
      MemLp df 2 (volume.restrict K)) :
    IsLocalW12On Set.univ f df := by
  have hdfLocal : LocallyIntegrable df (volume : Measure ℂ) := by
    rw [locallyIntegrable_iff]
    intro K hK
    let μK : Measure ℂ := volume.restrict K
    haveI : IsFiniteMeasure μK :=
      isFiniteMeasure_restrict.2 hK.measure_ne_top
    simpa [IntegrableOn, μK] using
      (hdfLp K hK).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨isOpen_univ, ?_, ?_⟩
  · intro φ v
    let dφ : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
    have hφcont : Continuous (φ : ℂ → ℝ) := φ.smooth.continuous
    have hdφcont : Continuous dφ := by
      simpa [dφ] using
        (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφcompact : HasCompactSupport dφ :=
      φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
        (by
          simpa [dφ] using
            tsupport_fderiv_apply_subset (𝕜 := ℝ)
              (f := (φ : ℂ → ℝ)) v)
    have hleftInt : Integrable (fun z ↦ dφ z • f z) volume :=
      (hdφcont.smul hf).integrable_of_hasCompactSupport
        (hdφcompact.smul_right)
    have hdfvLocal : LocallyIntegrable (fun z ↦ df z v)
        (volume : Measure ℂ) := by
      have hcomp :=
        ((ContinuousLinearMap.apply ℝ ℂ) v).locallyIntegrableOn_comp
          (s := Set.univ) (locallyIntegrableOn_univ.mpr hdfLocal)
      simpa [Function.comp_def] using locallyIntegrableOn_univ.mp hcomp
    have hrightInt : Integrable (fun z ↦ φ z • df z v) volume :=
      hdfvLocal.integrable_smul_left_of_hasCompactSupport
        hφcont φ.compact_support
    let β : ℕ → ℂ → ℝ := fun n ↦
      cauchyDiskCutoff (pointRemovabilityRadius n)
        (pointRemovabilityRadius_pos n)
    let ψ : ℕ →
        JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
          ({0}ᶜ : Set ℂ) :=
      fun n ↦ puncturedTestCutoff φ (pointRemovabilityRadius n)
        (pointRemovabilityRadius_pos n)
    let mainLeft : ℕ → ℂ → ℂ := fun n z ↦
      (1 - β n z) • (dφ z • f z)
    let errorLeft : ℕ → ℂ → ℂ := fun n z ↦
      (φ z * fderiv ℝ (β n) z v) • f z
    let right : ℕ → ℂ → ℂ := fun n z ↦
      (1 - β n z) • (φ z • df z v)
    have hmainInt (n : ℕ) : Integrable (mainLeft n) volume := by
      apply ((continuous_const.sub
        (cauchyDiskCutoff (pointRemovabilityRadius n)
          (pointRemovabilityRadius_pos n)).continuous).smul
            (hdφcont.smul hf)).integrable_of_hasCompactSupport
      exact (hdφcompact.smul_right (f' := f)).of_isClosed_subset
        (isClosed_tsupport _)
        (tsupport_smul_subset_right
          (fun z ↦ 1 - β n z) (fun z ↦ dφ z • f z))
    have herrorInt (n : ℕ) : Integrable (errorLeft n) volume := by
      have hβsmooth : ContDiff ℝ ∞ (β n) := by
        simpa [β] using
          (cauchyDiskCutoff (pointRemovabilityRadius n)
            (pointRemovabilityRadius_pos n)).contDiff
      have hβderiv : Continuous (fun z ↦ fderiv ℝ (β n) z v) := by
        exact (hβsmooth.continuous_fderiv (by simp)).clm_apply
          continuous_const
      apply ((hφcont.mul hβderiv).smul hf).integrable_of_hasCompactSupport
      exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_smul_subset_left
          (fun z ↦ φ z * fderiv ℝ (β n) z v) f |>.trans
            (tsupport_mul_subset_left
              (f := (φ : ℂ → ℝ))
              (g := fun z ↦ fderiv ℝ (β n) z v)))
    have hrightSeqInt (n : ℕ) : Integrable (right n) volume := by
      let q : ℂ → ℝ := fun z ↦ (1 - β n z) * φ z
      have hqcont : Continuous q := by
        exact (continuous_const.sub
          (cauchyDiskCutoff (pointRemovabilityRadius n)
            (pointRemovabilityRadius_pos n)).continuous).mul hφcont
      have hqcompact : HasCompactSupport q :=
        φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
          (tsupport_mul_subset_right
            (f := fun z ↦ 1 - β n z) (g := (φ : ℂ → ℝ)))
      simpa [right, q, smul_smul, mul_assoc] using
        hdfvLocal.integrable_smul_left_of_hasCompactSupport hqcont hqcompact
    have hpunctIdentity (n : ℕ) :
        ∫ z, mainLeft n z ∂volume - ∫ z, errorLeft n z ∂volume =
          -∫ z, right n z ∂volume := by
      rcases hpunct.2.1 (ψ n) v with ⟨_hleft, _hright, heq⟩
      have heq' :
          ∫ z, fderiv ℝ (ψ n : ℂ → ℝ) z v • f z ∂volume =
            -∫ z, ψ n z • df z v ∂volume := by
        simpa [restrict_compl_singleton] using heq
      calc
        ∫ z, mainLeft n z ∂volume - ∫ z, errorLeft n z ∂volume =
            ∫ z, mainLeft n z - errorLeft n z ∂volume := by
              rw [integral_sub (hmainInt n) (herrorInt n)]
        _ = ∫ z, fderiv ℝ (ψ n : ℂ → ℝ) z v • f z ∂volume := by
          apply integral_congr_ae
          filter_upwards with z
          rw [fderiv_puncturedTestCutoff]
          simp only [β, dφ, mainLeft, errorLeft]
          simp only [ContinuousLinearMap.sub_apply,
            ContinuousLinearMap.smul_apply, smul_eq_mul]
          module
        _ = -∫ z, ψ n z • df z v ∂volume := heq'
        _ = -∫ z, right n z ∂volume := by
          congr 1
          apply integral_congr_ae
          filter_upwards with z
          simp [ψ, β, right, mul_assoc]
    have haway (z : ℂ) (hz : z ≠ 0) :
        ∀ᶠ n : ℕ in atTop,
          2 * pointRemovabilityRadius n < ‖z‖ := by
      have htwo :
          Tendsto (fun n ↦ 2 * pointRemovabilityRadius n)
            atTop (𝓝 0) := by
        simpa using tendsto_pointRemovabilityRadius_zero.const_mul 2
      exact htwo.eventually (Iio_mem_nhds (norm_pos_iff.mpr hz))
    have hmainTend :
        Tendsto (fun n ↦ ∫ z, mainLeft n z ∂volume) atTop
          (𝓝 (∫ z, dφ z • f z ∂volume)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun z ↦ ‖dφ z • f z‖)
      · exact fun n ↦ (hmainInt n).aestronglyMeasurable
      · exact hleftInt.norm
      · intro n
        filter_upwards with z
        have hβ0 := (cauchyDiskCutoff
          (pointRemovabilityRadius n)
          (pointRemovabilityRadius_pos n)).nonneg (x := z)
        have hβ1 := (cauchyDiskCutoff
          (pointRemovabilityRadius n)
          (pointRemovabilityRadius_pos n)).le_one (x := z)
        simp only [mainLeft, β, norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (sub_nonneg.mpr hβ1)]
        exact mul_le_of_le_one_left (by positivity) (by linarith)
      · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))]
          with z hz
        have hz0 : z ≠ 0 := by simpa using hz
        have heq : (fun n ↦ mainLeft n z) =ᶠ[atTop]
            fun _n : ℕ ↦ dφ z • f z := by
          filter_upwards [haway z hz0] with n hn
          dsimp only [mainLeft]
          rw [show β n z = 0 by
            exact cauchyDiskCutoff_eq_zero_of_two_mul_le_norm
              (pointRemovabilityRadius_pos n) hn.le]
          simp
        exact (tendsto_congr' heq).mpr tendsto_const_nhds
    have hrightTend :
        Tendsto (fun n ↦ ∫ z, right n z ∂volume) atTop
          (𝓝 (∫ z, φ z • df z v ∂volume)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun z ↦ ‖φ z • df z v‖)
      · exact fun n ↦ (hrightSeqInt n).aestronglyMeasurable
      · exact hrightInt.norm
      · intro n
        filter_upwards with z
        have hβ0 := (cauchyDiskCutoff
          (pointRemovabilityRadius n)
          (pointRemovabilityRadius_pos n)).nonneg (x := z)
        have hβ1 := (cauchyDiskCutoff
          (pointRemovabilityRadius n)
          (pointRemovabilityRadius_pos n)).le_one (x := z)
        simp only [right, β, norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (sub_nonneg.mpr hβ1)]
        exact mul_le_of_le_one_left (by positivity) (by linarith)
      · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))]
          with z hz
        have hz0 : z ≠ 0 := by simpa using hz
        have heq : (fun n ↦ right n z) =ᶠ[atTop]
            fun _n : ℕ ↦ φ z • df z v := by
          filter_upwards [haway z hz0] with n hn
          dsimp only [right]
          rw [show β n z = 0 by
            exact cauchyDiskCutoff_eq_zero_of_two_mul_le_norm
              (pointRemovabilityRadius_pos n) hn.le]
          simp
        exact (tendsto_congr' heq).mpr tendsto_const_nhds
    obtain ⟨A, hA⟩ := exists_norm_fderiv_cauchyDiskCutoff_le_div
    let errorBound : ℂ → ℝ := fun z ↦
      2 * (A : ℝ) * ‖v‖ * (‖φ z‖ * ‖f z‖ * ‖z⁻¹‖)
    have herrorBoundInt : Integrable errorBound volume := by
      let q : ℂ → ℝ := fun z ↦ ‖φ z‖ * ‖f z‖
      have hqcont : Continuous q := hφcont.norm.mul hf.norm
      have hφnormcompact : HasCompactSupport (fun z : ℂ ↦ ‖φ z‖) :=
        HasCompactSupport.norm φ.compact_support
      have hqcompact : HasCompactSupport q := hφnormcompact.mul_right
      have hbase :
          Integrable (fun z ↦ q z * ‖z⁻¹‖) volume := by
        have hinvnorm : LocallyIntegrable (fun z : ℂ ↦ ‖z⁻¹‖) volume :=
          locallyIntegrableOn_univ.mp
            ((locallyIntegrableOn_univ.mpr
              locallyIntegrable_inv_complex).norm)
        simpa [smul_eq_mul] using
          hinvnorm.integrable_smul_left_of_hasCompactSupport hqcont hqcompact
      simpa [errorBound, q, mul_assoc] using
        hbase.const_mul (2 * (A : ℝ) * ‖v‖)
    have herrorBound (n : ℕ) :
        ∀ᵐ z ∂volume, ‖errorLeft n z‖ ≤ errorBound z := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))]
        with z hz
      have hz0 : z ≠ 0 := by simpa using hz
      have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      let R := pointRemovabilityRadius n
      have hR : 0 < R := pointRemovabilityRadius_pos n
      by_cases hin : ‖z‖ < R
      · simp only [errorLeft]
        rw [show fderiv ℝ (β n) z = 0 by
          simpa [β, R] using
            fderiv_cauchyDiskCutoff_eq_zero_of_norm_lt hR hin]
        simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_smul, norm_zero]
        change 0 ≤ errorBound z
        dsimp [errorBound]
        positivity
      by_cases hout : 2 * R < ‖z‖
      · simp only [errorLeft]
        rw [show fderiv ℝ (β n) z = 0 by
          simpa [β, R] using
            fderiv_cauchyDiskCutoff_eq_zero_of_two_mul_lt_norm hR hout]
        simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_smul, norm_zero]
        change 0 ≤ errorBound z
        dsimp [errorBound]
        positivity
      have hRle : R ≤ ‖z‖ := le_of_not_gt hin
      have hnormle : ‖z‖ ≤ 2 * R := le_of_not_gt hout
      have hinvle : 1 / R ≤ 2 / ‖z‖ := by
        rw [div_le_div_iff₀ hR hznorm]
        nlinarith
      have hderiv :
          ‖fderiv ℝ (β n) z‖ ≤ (A : ℝ) * (2 / ‖z‖) := by
        calc
          ‖fderiv ℝ (β n) z‖ ≤ (A : ℝ) / R := by
            simpa [β, R] using hA R hR z
          _ = (A : ℝ) * (1 / R) := by ring
          _ ≤ (A : ℝ) * (2 / ‖z‖) :=
            mul_le_mul_of_nonneg_left hinvle A.coe_nonneg
      calc
        ‖errorLeft n z‖ =
            ‖φ z‖ * ‖fderiv ℝ (β n) z v‖ * ‖f z‖ := by
          simp [errorLeft]
        _ ≤ ‖φ z‖ * (‖fderiv ℝ (β n) z‖ * ‖v‖) * ‖f z‖ := by
          gcongr
          exact (fderiv ℝ (β n) z).le_opNorm v
        _ ≤ ‖φ z‖ * (((A : ℝ) * (2 / ‖z‖)) * ‖v‖) * ‖f z‖ := by
          gcongr
        _ = errorBound z := by
          dsimp [errorBound]
          rw [norm_inv]
          field_simp
    have herrorTend :
        Tendsto (fun n ↦ ∫ z, errorLeft n z ∂volume) atTop (𝓝 0) := by
      simpa using
        (tendsto_integral_of_dominated_convergence
          (F := errorLeft) (f := fun _ ↦ (0 : ℂ))
          errorBound
          (fun n ↦ (herrorInt n).aestronglyMeasurable)
          herrorBoundInt herrorBound
          (by
            filter_upwards
              [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))]
              with z hz
            have hz0 : z ≠ 0 := by simpa using hz
            have heq : (fun n ↦ errorLeft n z) =ᶠ[atTop]
                fun _n : ℕ ↦ (0 : ℂ) := by
              filter_upwards [haway z hz0] with n hn
              simp only [errorLeft]
              rw [show fderiv ℝ (β n) z = 0 by
                simpa [β] using
                  fderiv_cauchyDiskCutoff_eq_zero_of_two_mul_lt_norm
                    (pointRemovabilityRadius_pos n) hn]
              simp
            exact (tendsto_congr' heq).mpr tendsto_const_nhds))
    have hleftLimit :
        Tendsto
          (fun n ↦
            ∫ z, mainLeft n z ∂volume - ∫ z, errorLeft n z ∂volume)
          atTop (𝓝 (∫ z, dφ z • f z ∂volume)) := by
      simpa using hmainTend.sub herrorTend
    have hrightLimit :
        Tendsto (fun n ↦ -∫ z, right n z ∂volume) atTop
          (𝓝 (-∫ z, φ z • df z v ∂volume)) :=
      hrightTend.neg
    have hseq :
        (fun n ↦
          ∫ z, mainLeft n z ∂volume - ∫ z, errorLeft n z ∂volume) =
        fun n ↦ -∫ z, right n z ∂volume :=
      funext hpunctIdentity
    rw [hseq] at hleftLimit
    simpa only [Measure.restrict_univ, dφ] using
      ⟨hleftInt, hrightInt,
        tendsto_nhds_unique hleftLimit hrightLimit⟩
  · intro K hK _hKuniv
    exact ⟨memLp_restrict_of_isCompact_of_continuousOn
        hK hf.continuousOn,
      hdfLp K hK⟩

/--
%%handwave
name:
  Finite quasiconformal energy across an omitted point
statement:
  Let $P:\mathbb C^\times\to\mathbb C^\times$ be $K$-quasiconformal with
  weak differential $DP$. Suppose its ambient representative agrees with a
  continuous map $H:\mathbb C\to\mathbb C$. Then
  $$
    DP\in L^2(K_0)
  $$
  for every compact set $K_0\subset\mathbb C$.
proof:
  Enclose $K_0$ in a closed disk and apply the quasiconformal differential
  energy estimate to that disk with the origin removed. Its image is
  contained in the continuous image under $H$ of the full disk, which is
  compact and hence has finite area. The omitted singleton is null.
-/
theorem IsKQuasiconformalBetween.weakDifferential_memLp_two_on_compact_of_punctured
    {K : ℝ} {P : ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ)}
    (hP : IsKQuasiconformalBetween K P)
    {H : ℂ → ℂ} (hH : Continuous H)
    (hagree : ∀ z : ℂ, ambientMap P z = H z)
    {dP : ℂ → ℂ →L[ℝ] ℂ}
    (hdP : IsLocalW12On ({0}ᶜ : Set ℂ) (ambientMap P) dP)
    (K₀ : Set ℂ) (hK₀ : IsCompact K₀) :
    MemLp dP 2 (volume.restrict K₀) := by
  obtain ⟨R, hR, hK₀R⟩ :=
    hK₀.isBounded.subset_closedBall_lt (0 : ℝ) (0 : ℂ)
  let C : Set ℂ := Metric.closedBall (0 : ℂ) R
  let E : Set ℂ := C \ {0}
  have hC : IsCompact C := isCompact_closedBall _ _
  have hEmeas : MeasurableSet E :=
    hC.measurableSet.diff (measurableSet_singleton (0 : ℂ))
  have hEP : E ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    simpa [E] using hz.2
  have himage : ambientMap P '' E ⊆ H '' C := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, hz.1, (hagree z).symm⟩
  have himageTop : volume (ambientMap P '' E) < (∞ : ℝ≥0∞) := by
    exact (measure_mono himage).trans_lt (hC.image hH).measure_lt_top
  have henergy :=
    hP.lintegral_norm_weakDifferential_sq_le_volume_image
      hdP hEmeas hEP
  have henergyTop :
      (∫⁻ z in E, ENNReal.ofReal (‖dP z‖ ^ 2) ∂volume) < (∞ : ℝ≥0∞) :=
    henergy.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top himageTop)
  have hdPmeasE : AEStronglyMeasurable dP (volume.restrict E) := by
    exact hdP.differential_locallyIntegrableOn.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hEP le_rfl)
  have hdPmemE : MemLp dP 2 (volume.restrict E) := by
    rw [memLp_two_iff_integrable_sq_norm hdPmeasE]
    refine ⟨hdPmeasE.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact henergyTop
    · filter_upwards with z
      positivity
  have hdPmemC : MemLp dP 2 (volume.restrict C) := by
    have hrestrict : volume.restrict E = volume.restrict C := by
      apply Measure.restrict_congr_set
      filter_upwards
        [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with z hz
      apply propext
      constructor
      · intro hEz
        exact hEz.1
      · intro hCz
        exact ⟨hCz, by simpa using hz⟩
    rw [← hrestrict]
    exact hdPmemE
  exact hdPmemC.mono_measure
    (Measure.restrict_mono hK₀R le_rfl)

/--
%%handwave
name:
  Analytic quasiconformal removability of an omitted point
statement:
  Let $P:\mathbb C^\times\to\mathbb C^\times$ be $K$-quasiconformal and
  suppose its ambient representative extends to a continuous map
  $H:\mathbb C\to\mathbb C$. Then there is a weak differential $DH$ on the
  whole plane such that $H\in W^{1,2}_{\mathrm{loc}}(\mathbb C)$ and
  $$
    |DH|^2\le K\operatorname{Jac}DH
  $$
  almost everywhere.
proof:
  Take the weak differential furnished by quasiconformality on the punctured
  plane. The area estimate gives its finite $L^2$-energy on every compact
  set, so continuous finite-energy point removability extends the weak
  derivative identity across the origin. The distortion inequality extends
  because the omitted singleton has measure zero.
-/
theorem IsKQuasiconformalBetween.exists_isLocalW12On_univ_of_punctured_continuous
    {K : ℝ} {P : ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ)}
    (hP : IsKQuasiconformalBetween K P)
    {H : ℂ → ℂ} (hH : Continuous H)
    (hagree : ∀ z : ℂ, ambientMap P z = H z) :
    ∃ dH : ℂ → ℂ →L[ℝ] ℂ,
      IsLocalW12On Set.univ H dH ∧
        ∀ᵐ z ∂(volume : Measure ℂ),
          ‖dH z‖ ^ 2 ≤ K * weakJacobian (dH z) := by
  obtain ⟨dH, hdH, hdist⟩ := hP.2.2.2
  have hdHpunct : IsLocalW12On ({0}ᶜ : Set ℂ) H dH := by
    apply hdH.congr_ae
    filter_upwards with z
    exact (hagree z).symm
  have hdHLp : ∀ C : Set ℂ, IsCompact C →
      MemLp dH 2 (volume.restrict C) := by
    intro C hC
    exact hP.weakDifferential_memLp_two_on_compact_of_punctured
      hH hagree hdH C hC
  refine ⟨dH,
    isLocalW12On_univ_of_compl_singleton_of_continuous hH hdHpunct hdHLp,
    ?_⟩
  simpa [restrict_compl_singleton] using hdist

/--
%%handwave
name:
  Filling a puncture with a nonzero complex tangent preserves orientation
statement:
  Let $H:\mathbb C\to\mathbb C$ be a homeomorphism fixing $0$. Suppose its
  restriction to $\mathbb C^\times$ preserves orientation and, for some
  $a\ne0$,
  $$
    \frac{H(z)}z\longrightarrow a
    \qquad (z\to0,\ z\ne0).
  $$
  Then $H$ preserves planar orientation on the whole plane.
proof:
  Away from the origin, use the orientation witnesses of the punctured
  restriction. Near the origin, the image of a sufficiently small circle is
  closer pointwise to the complex-linear circle $z\mapsto az$ than that
  linear circle is to the origin. Their straight-line interpolation avoids
  the origin, so their normalized boundary loops are homotopic. The
  complex-linear circle has the positive class.
-/
theorem preservesPlanarOrientation_wholePlaneSubtype_of_punctured_of_tendsto_div
    (H : ℂ ≃ₜ ℂ) (hH0 : H 0 = 0)
    (P : ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ))
    (hP : PreservesPlanarOrientation P)
    (hagree : ∀ z : ℂ, ambientMap P z = H z)
    {a : ℂ} (ha : a ≠ 0)
    (htangent : Tendsto (fun z : ℂ ↦ H z / z)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (𝓝 a)) :
    PreservesPlanarOrientation (wholePlaneSubtypeHomeomorph H) := by
  intro z
  by_cases hz : (z : ℂ) = 0
  · have hzsub : z = (⟨0, Set.mem_univ 0⟩ : (Set.univ : Set ℂ)) :=
      Subtype.ext hz
    subst z
    have hnear : {w : ℂ | ‖H w / w - a‖ < ‖a‖} ∈
        nhdsWithin 0 ({0}ᶜ : Set ℂ) := by
      simpa [dist_eq_norm] using htangent.eventually
        (Metric.ball_mem_nhds a (norm_pos_iff.mpr ha))
    obtain ⟨W, hW, hWsub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnear
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
    let r : ℝ := ε / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrε : r < ε := by dsimp [r]; linarith
    let z0 : (Set.univ : Set ℂ) := ⟨0, Set.mem_univ 0⟩
    have hball : Metric.closedBall (z0 : ℂ) r ⊆ (Set.univ : Set ℂ) :=
      fun _ _ ↦ Set.mem_univ _
    let hcircle := circlePoint_mem_of_closedBall_subset z0 hr hball
    let B := complexAffineHomeomorph a 0 ha
    have hclose (t : unitInterval) :
        ‖(a * circlePoint 0 r t) - H (circlePoint 0 r t)‖ <
          ‖a * circlePoint 0 r t - 0‖ := by
      let w : ℂ := circlePoint 0 r t
      have hw0 : w ≠ 0 := circlePoint_ne_center 0 hr t
      have hwball : w ∈ Metric.ball (0 : ℂ) ε := by
        rw [Metric.mem_ball, dist_circlePoint_center 0 hr t]
        exact hrε
      have hwnear : ‖H w / w - a‖ < ‖a‖ :=
        hWsub ⟨hεW hwball, by simpa using hw0⟩
      have hfactor : a * w - H w = (a - H w / w) * w := by
        field_simp [hw0]
      rw [show circlePoint 0 r t = w by rfl, hfactor, norm_mul,
        norm_sub_rev]
      have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      simpa [norm_mul] using (mul_lt_mul_of_pos_right hwnear hwnorm)
    have hhom :
        (normalizedBoundaryLoop (wholePlaneSubtypeHomeomorph H) z0 r hr
          hcircle).Homotopic
          (normalizedBoundaryLoop B ⟨0, Set.mem_univ 0⟩ r hr
            (fun _ ↦ Set.mem_univ _)) := by
      have hraw := normalizedLoopAround_homotopic_of_norm_sub_lt
        (imageCircleLoop (fun w : ℂ ↦ a * w) (by fun_prop) 0 r)
        (imageCircleLoop H H.continuous 0 r) 0
        (fun t hzero ↦ by
          have hw0 := circlePoint_ne_center 0 hr t
          exact hw0 (mul_eq_zero.mp hzero |>.resolve_left ha))
        (fun t hzero ↦ by
          have h := H.injective (hzero.trans hH0.symm)
          exact circlePoint_ne_center 0 hr t h)
        (imageCircleLoop_one_eq_zero (fun w : ℂ ↦ a * w) (by fun_prop) 0 r)
        (imageCircleLoop_one_eq_zero H H.continuous 0 r)
        (fun t ↦ by
          simpa [imageCircleLoop, complexCircleLoop, norm_sub_rev] using hclose t)
      convert hraw.symm using 1 <;>
        apply Path.ext <;> funext t <;> apply Subtype.ext <;>
        simp [normalizedBoundaryLoop, normalizedLoopAround, imageCircleLoop,
          complexCircleLoop, wholePlaneSubtypeHomeomorph_apply, B, z0, hH0]
    refine ⟨r, hr, hball, hhom.trans ?_⟩
    have hB := normalizedBoundaryLoop_complexAffine a 0 ha
      (⟨0, Set.mem_univ 0⟩ : (Set.univ : Set ℂ)) r hr
      (fun _ ↦ Set.mem_univ _)
    rw [hB]
  · let zp : ({0}ᶜ : Set ℂ) := ⟨z, by simpa using hz⟩
    obtain ⟨r, hr, hballP, hloopP⟩ := hP zp
    have hball : Metric.closedBall (z : ℂ) r ⊆ (Set.univ : Set ℂ) :=
      fun _ _ ↦ Set.mem_univ _
    refine ⟨r, hr, hball, ?_⟩
    convert hloopP using 1
    apply Path.ext
    funext t
    apply Subtype.ext
    have hval (w : ({0}ᶜ : Set ℂ)) : (P w : ℂ) = H w := by
      rw [← hagree w]
      exact (ambientMap_apply P w).symm
    simp [normalizedBoundaryLoop, wholePlaneSubtypeHomeomorph_apply, hval, zp]

end

end Quasiconformal

end JJMath
