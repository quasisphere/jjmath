import JJMath.Quasiconformal.BeurlingSeparated

/-!
# The physical Beurling formula for rough compactly supported data

This file extends the off-support physical-kernel representation from smooth
test functions to compactly supported `L²` functions.  Support-controlled
smooth approximation leaves a fixed gap between the data and the exterior
evaluation region.  The Fourier-side and physical-side approximants converge
in measure there, so uniqueness of the limit identifies the two formulas.
-/

namespace JJMath

open Set MeasureTheory Metric Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Convergence in measure for a smaller measure
statement:
  If $\nu\leq\mu$ and $f_i\to f$ in measure with respect to $\mu$, then
  $f_i\to f$ in measure with respect to $\nu$.
proof:
  Every exceptional set has $\nu$-measure at most its $\mu$-measure, so the
  defining measures are squeezed to zero.
-/
theorem tendstoInMeasure_mono_measure
    {α E ι : Type*} [MeasurableSpace α] [EDist E]
    {μ ν : Measure α} {f : ι → α → E} {g : α → E} {l : Filter ι}
    (hνμ : ν ≤ μ) (h : TendstoInMeasure μ f l g) :
    TendstoInMeasure ν f l g := by
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h ε hε) (fun _ ↦ bot_le) (fun i ↦ hνμ _)

/--
%%handwave
name:
  Off-support physical formula for compactly supported $L^2$ data
statement:
  Let $r>0$ and let $h\in L^2(\mathbb C)$ vanish outside
  $\overline B(c,r)$. Then, for almost every $x$ with $|x-c|>2r$,
  $$
    \mathcal S h(x)=\mathcal K h(x)
      =\int_{\mathbb C}-\frac{h(w)}{\pi(x-w)^2}\,dw.
  $$
proof:
  Approximate $h$ in $L^2$ by smooth functions supported in
  $\overline B(c,3r/2)$. The $L^2$ isometry of $\mathcal S$ gives
  convergence in measure of their Fourier-side transforms. The
  separated-disk estimate gives convergence in measure of their physical
  kernel integrals on $\{|x-c|>2r\}$. The smooth off-support formula makes
  the two approximating sequences equal almost everywhere, so uniqueness
  of limits in measure identifies their limits.
-/
theorem beurlingTransformL2_eq_kernelIntegral_ae_exterior_of_memLp_two_of_support_closedBall
    {h : ℂ → ℂ} (hh : MemLp h 2 volume)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ r) :
    (beurlingTransformL2 (hh.toLp h) : ℂ → ℂ) =ᵐ[
      volume.restrict {x : ℂ | 2 * r < ‖x - c‖}]
      beurlingKernelIntegral h := by
  let δ : ℕ → ℝ := fun n ↦ (1 : ℝ) / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp only [δ]
    positivity
  have happ (n : ℕ) :
      ∃ φ : PlaneTestFunction,
        tsupport (φ : ℂ → ℂ) ⊆ Metric.closedBall c (3 * r / 2) ∧
        eLpNorm (h - (φ : ℂ → ℂ)) 2 volume ≤ ENNReal.ofReal (δ n) :=
    exists_planeTestFunction_eLpNorm_sub_le_tsupport_subset_intermediateDisk
      hh hr hhsupp (hδpos n)
  choose φ hφsupp hφerror using happ
  have hφmem (n : ℕ) : MemLp (φ n : ℂ → ℂ) 2 volume :=
    (φ n).continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport
  have hδreal : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδenn : Tendsto (fun n ↦ ENNReal.ofReal (δ n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hδreal
  have happrox : Tendsto
      (fun n ↦ eLpNorm (h - (φ n : ℂ → ℂ)) 2 volume)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδenn
      (fun _ ↦ bot_le) hφerror
  have hdiffnorm : Tendsto
      (fun n ↦ eLpNorm ((φ n : ℂ → ℂ) - h) 2 volume)
      atTop (𝓝 0) := by
    convert happrox using 1
    funext n
    rw [show (φ n : ℂ → ℂ) - h = -(h - (φ n : ℂ → ℂ)) by abel,
      eLpNorm_neg]
  have hinput : Tendsto (fun n ↦ testFunctionPlaneL2 (φ n)) atTop
      (𝓝 (hh.toLp h)) := by
    have hraw :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n ↦ (φ n : ℂ → ℂ)) hφmem h hh).2 hdiffnorm
    simpa only [testFunctionPlaneL2] using hraw
  have hfourier_global : TendstoInMeasure volume
      (fun n ↦ (beurlingTransformL2 (testFunctionPlaneL2 (φ n)) : ℂ → ℂ))
      atTop (beurlingTransformL2 (hh.toLp h) : ℂ → ℂ) := by
    apply tendstoInMeasure_of_tendsto_Lp
    exact beurlingTransformL2.continuous.continuousAt.tendsto.comp hinput
  let E : Set ℂ := {x : ℂ | 2 * r < ‖x - c‖}
  let μE : Measure ℂ := volume.restrict E
  have hfourier : TendstoInMeasure μE
      (fun n ↦ (beurlingTransformL2 (testFunctionPlaneL2 (φ n)) : ℂ → ℂ))
      atTop (beurlingTransformL2 (hh.toLp h) : ℂ → ℂ) := by
    apply tendstoInMeasure_mono_measure Measure.restrict_le_self
    exact hfourier_global
  have hdiffmem (n : ℕ) : MemLp ((φ n : ℂ → ℂ) - h) 2 volume :=
    (hφmem n).sub hh
  have hdiffsupp (n : ℕ) (w : ℂ)
      (hw : (φ n : ℂ → ℂ) w - h w ≠ 0) :
      ‖w - c‖ ≤ 3 * r / 2 := by
    by_cases hφw : (φ n : ℂ → ℂ) w = 0
    · have hhw : h w ≠ 0 := by
        intro hhw
        exact hw (by simp [hφw, hhw])
      exact (hhsupp w hhw).trans (by linarith)
    · simpa only [Metric.mem_closedBall, dist_eq_norm] using
        hφsupp n (subset_tsupport (φ n : ℂ → ℂ) hφw)
  have hKmem (n : ℕ) : MemLp
      (beurlingKernelIntegral ((φ n : ℂ → ℂ) - h)) 2 μE := by
    dsimp only [μE, E]
    exact memLp_two_beurlingKernelIntegral_restrict_exterior_of_support_intermediateDisk
      (hdiffmem n) hr (hdiffsupp n)
  let A : ℝ := (16 * (Real.pi)⁻¹) ^ (2 : ℕ) *
    (volume (Metric.closedBall c (3 * r / 2))).toReal *
    (2 * Real.pi / (2 * r) ^ 2)
  have hsq (n : ℕ) :
      (eLpNorm (beurlingKernelIntegral ((φ n : ℂ → ℂ) - h)) 2 μE).toReal ^
          (2 : ℕ) ≤
        A * (eLpNorm ((φ n : ℂ → ℂ) - h) 2 volume).toReal ^ (2 : ℕ) := by
    dsimp only [μE, E, A]
    exact eLpNorm_two_toReal_sq_beurlingKernelIntegral_restrict_exterior_le
      (hdiffmem n) hr (hdiffsupp n)
  have hdiffreal : Tendsto
      (fun n ↦ (eLpNorm ((φ n : ℂ → ℂ) - h) 2 volume).toReal)
      atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdiffnorm
  have hroot : Tendsto
      (fun n ↦ Real.sqrt
        (A * (eLpNorm ((φ n : ℂ → ℂ) - h) 2 volume).toReal ^ (2 : ℕ)))
      atTop (𝓝 0) := by
    have hinside : Tendsto
        (fun n ↦ A * (eLpNorm ((φ n : ℂ → ℂ) - h) 2 volume).toReal ^
          (2 : ℕ))
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (hdiffreal.pow 2)
    simpa only [Function.comp_apply, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hinside
  have hKreal : Tendsto
      (fun n ↦ (eLpNorm
        (beurlingKernelIntegral ((φ n : ℂ → ℂ) - h)) 2 μE).toReal)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards with n
      exact ENNReal.toReal_nonneg
    · filter_upwards with n
      exact Real.le_sqrt_of_sq_le (hsq n)
    · exact hroot
  have hKnorm : Tendsto
      (fun n ↦ eLpNorm
        (beurlingKernelIntegral ((φ n : ℂ → ℂ) - h)) 2 μE)
      atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal_zero_iff
      (fun n ↦ (hKmem n).2.ne)).1 hKreal
  have hφintegrable (n : ℕ) : Integrable (φ n : ℂ → ℂ) volume :=
    (φ n).continuous.integrable_of_hasCompactSupport (φ n).hasCompactSupport
  have hhintegrable : Integrable h volume :=
    integrable_of_memLp_two_of_support_closedBall hh hhsupp
  have hφsupport (n : ℕ) (w : ℂ) (hw : (φ n : ℂ → ℂ) w ≠ 0) :
      ‖w - c‖ ≤ 3 * r / 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using
      hφsupp n (subset_tsupport (φ n : ℂ → ℂ) hw)
  have hhsupportIntermediate (w : ℂ) (hw : h w ≠ 0) :
      ‖w - c‖ ≤ 3 * r / 2 :=
    (hhsupp w hw).trans (by linarith)
  have hEmeas : MeasurableSet E := by
    exact (isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).measurableSet
  have hkernelSub (n : ℕ) :
      (fun x ↦ beurlingKernelIntegral ((φ n : ℂ → ℂ) - h) x) =ᵐ[μE]
        (fun x ↦ beurlingKernelIntegral (φ n : ℂ → ℂ) x -
          beurlingKernelIntegral h x) := by
    filter_upwards [ae_restrict_mem hEmeas] with x hx
    exact beurlingKernelIntegral_sub_of_support_intermediateDisk_of_mem_exterior
      (hφintegrable n) hhintegrable hr (hφsupport n)
        hhsupportIntermediate hx
  have hphysical : TendstoInMeasure μE
      (fun n ↦ beurlingKernelIntegral (φ n : ℂ → ℂ)) atTop
      (beurlingKernelIntegral h) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
    · norm_num
    · exact fun n ↦
        (aestronglyMeasurable_beurlingKernelIntegral
          (hφmem n).aestronglyMeasurable).mono_measure
            Measure.restrict_le_self
    · exact (aestronglyMeasurable_beurlingKernelIntegral
        hh.aestronglyMeasurable).mono_measure Measure.restrict_le_self
    · apply hKnorm.congr'
      filter_upwards with n
      apply eLpNorm_congr_ae
      filter_upwards [hkernelSub n] with x hx
      simpa only [Pi.sub_apply] using hx
  have hsmooth (n : ℕ) :
      (beurlingTransformL2 (testFunctionPlaneL2 (φ n)) : ℂ → ℂ) =ᵐ[μE]
        beurlingKernelIntegral (φ n : ℂ → ℂ) := by
    filter_upwards [
      ae_restrict_of_ae
        (beurlingTransformL2_eq_kernelIntegral_ae_off_tsupport (φ n)),
      ae_restrict_mem hEmeas] with x hxformula hxE
    apply hxformula
    intro hxsupp
    change 2 * r < ‖x - c‖ at hxE
    have hxball : ‖x - c‖ ≤ 3 * r / 2 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hφsupp n hxsupp
    exact (not_lt_of_ge hxball) (lt_of_lt_of_le (by linarith) hxE.le)
  have hphysicalSmooth : TendstoInMeasure μE
      (fun n ↦ (beurlingTransformL2 (testFunctionPlaneL2 (φ n)) : ℂ → ℂ))
      atTop (beurlingKernelIntegral h) :=
    hphysical.congr_left (fun n ↦ (hsmooth n).symm)
  simpa only [μE, E] using
    tendstoInMeasure_ae_unique hfourier hphysicalSmooth

end

end Quasiconformal

end JJMath
