import JJMath.Quasiconformal.CauchyTransform
import JJMath.Quasiconformal.BeurlingKernel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Off-support representation of the Beurling transform

This file connects the Fourier-multiplier Beurling transform to its physical
Calderón--Zygmund kernel. Away from the support of a test function, the Cauchy
integral may be differentiated under the integral sign. Its complex
derivative is convolution with `-1 / (π z²)`. Combining this pointwise fact
with the established almost-everywhere Cauchy--Beurling identity gives the
off-support representation required by the singular-integral argument.
-/

namespace JJMath

open Set MeasureTheory Metric Filter
open scoped Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Complex derivative of the Cauchy transform away from the support
statement:
  Let $g\in C_c^\infty(\mathbb C)$ and let
  $x\notin\operatorname{supp}g$. Then the normalized Cauchy transform is
  complex Fréchet differentiable at $x$, with derivative
  $$
    h\longmapsto h\int_{\mathbb C}
      -\frac{g(w)}{\pi(x-w)^2}\,dw.
  $$
proof:
  Choose a ball about $x$ disjoint from the closed support of $g$. On half
  that ball, every nonzero part of the integrand remains a fixed positive
  distance from its pole. Its derivative is therefore bounded by a constant
  times $|g(w)|$, which is integrable because $g$ is continuous and compactly
  supported. Differentiate under the integral sign and identify the resulting
  complex-linear map.
-/
theorem hasFDerivAt_cauchyTransform_of_not_mem_tsupport
    (g : PlaneTestFunction) (x : ℂ) (hx : x ∉ tsupport g) :
    HasFDerivAt (cauchyTransform g)
      (ContinuousLinearMap.toSpanSingleton ℂ
        (∫ w : ℂ, planarBeurlingKernel (x - w) * g w ∂volume)) x := by
  have hopen : IsOpen (tsupport (g : ℂ → ℂ))ᶜ :=
    (isClosed_tsupport (g : ℂ → ℂ)).isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  let F : ℂ → ℂ → ℂ := fun z w ↦
    (Real.pi : ℂ)⁻¹ * (z - w)⁻¹ * g w
  let coeff : ℂ → ℂ → ℂ := fun z w ↦
    planarBeurlingKernel (z - w) * g w
  let F' : ℂ → ℂ → ℂ →L[ℂ] ℂ := fun z w ↦
    (ContinuousLinearMap.lsmul ℂ ℂ) (coeff z w)
  let B : ℂ → ℝ := fun w ↦
    ((Real.pi)⁻¹ * (2 / δ) ^ 2) * ‖g w‖
  have hs : Metric.ball x (δ / 2) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (half_pos hδ)
  have hmeas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (F z) (volume : Measure ℂ) := by
    filter_upwards
    intro z
    apply Measurable.aestronglyMeasurable
    unfold F
    fun_prop
  have hint : Integrable (F x) (volume : Measure ℂ) := by
    simpa [F, planarCauchyKernel, mul_assoc] using
      (integrable_planarCauchyKernel_mul_testFunction g x).const_mul
        (Real.pi : ℂ)⁻¹
  have hderivmeas : AEStronglyMeasurable (F' x)
      (volume : Measure ℂ) := by
    apply Measurable.aestronglyMeasurable
    unfold F' coeff planarBeurlingKernel
    fun_prop
  have hbound : ∀ᵐ w : ℂ ∂volume,
      ∀ z ∈ Metric.ball x (δ / 2), ‖F' z w‖ ≤ B w := by
    filter_upwards
    intro w z hz
    by_cases hgw : g w = 0
    · simp [F', coeff, B, hgw]
    have hwt : w ∈ tsupport (g : ℂ → ℂ) :=
      subset_tsupport (g : ℂ → ℂ) hgw
    have hwball : w ∉ Metric.ball x δ := fun hw ↦ (hball hw) hwt
    have hxw : δ ≤ ‖x - w‖ := by
      have hdist : δ ≤ dist w x := by
        exact not_lt.mp (by simpa [Metric.mem_ball] using hwball)
      simpa [dist_eq_norm, norm_sub_rev] using hdist
    have hzx : ‖z - x‖ < δ / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have htri : ‖x - w‖ ≤ ‖z - x‖ + ‖z - w‖ := by
      calc
        ‖x - w‖ = ‖(x - z) + (z - w)‖ := by ring_nf
        _ ≤ ‖x - z‖ + ‖z - w‖ := norm_add_le _ _
        _ = ‖z - x‖ + ‖z - w‖ := by rw [norm_sub_rev]
    have hzw : δ / 2 ≤ ‖z - w‖ := by linarith
    have hzwpos : 0 < ‖z - w‖ := (half_pos hδ).trans_le hzw
    have hinv : ‖z - w‖⁻¹ ≤ 2 / δ := by
      have h := (inv_le_inv₀ hzwpos (half_pos hδ)).2 hzw
      convert h using 1
      all_goals field_simp
    unfold F' coeff B
    calc
      ‖(ContinuousLinearMap.lsmul ℂ ℂ)
          (planarBeurlingKernel (z - w) * g w)‖ ≤
          ‖planarBeurlingKernel (z - w) * g w‖ :=
        ContinuousLinearMap.opNorm_lsmul_apply_le _
      _ = (Real.pi)⁻¹ * ‖z - w‖⁻¹ ^ 2 * ‖g w‖ := by
        rw [norm_mul, norm_planarBeurlingKernel]
      _ ≤ (Real.pi)⁻¹ * (2 / δ) ^ 2 * ‖g w‖ := by gcongr
      _ = ((Real.pi)⁻¹ * (2 / δ) ^ 2) * ‖g w‖ := by ring
  have hBint : Integrable B (volume : Measure ℂ) := by
    unfold B
    exact (g.continuous.integrable_of_hasCompactSupport
      g.hasCompactSupport).norm.const_mul _
  have hdiff : ∀ᵐ w : ℂ ∂volume,
      ∀ z ∈ Metric.ball x (δ / 2),
        HasFDerivAt (fun z ↦ F z w) (F' z w) z := by
    filter_upwards
    intro w z hz
    have hmap : F' z w =
        ContinuousLinearMap.toSpanSingleton ℂ (coeff z w) := by
      ext
      simp [F', ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
    rw [hmap]
    show HasDerivAt (fun z ↦ F z w) (coeff z w) z
    by_cases hgw : g w = 0
    · simpa [F, coeff, hgw] using hasDerivAt_const z (0 : ℂ)
    have hwt : w ∈ tsupport (g : ℂ → ℂ) :=
      subset_tsupport (g : ℂ → ℂ) hgw
    have hwball : w ∉ Metric.ball x δ := fun hw ↦ (hball hw) hwt
    have hxw : δ ≤ ‖x - w‖ := by
      have hdist : δ ≤ dist w x := by
        exact not_lt.mp (by simpa [Metric.mem_ball] using hwball)
      simpa [dist_eq_norm, norm_sub_rev] using hdist
    have hzx : ‖z - x‖ < δ / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have htri : ‖x - w‖ ≤ ‖z - x‖ + ‖z - w‖ := by
      calc
        ‖x - w‖ = ‖(x - z) + (z - w)‖ := by ring_nf
        _ ≤ ‖x - z‖ + ‖z - w‖ := norm_add_le _ _
        _ = ‖z - x‖ + ‖z - w‖ := by rw [norm_sub_rev]
    have hzw : δ / 2 ≤ ‖z - w‖ := by linarith
    have hne : z - w ≠ 0 :=
      norm_ne_zero_iff.mp ((half_pos hδ).trans_le hzw).ne'
    have hinv : HasDerivAt (fun u : ℂ ↦ (u - w)⁻¹)
        (-(z - w)⁻¹ ^ 2) z := by
      convert ((hasDerivAt_id z).sub_const w).inv hne using 1
      field_simp [hne]
      simp [id]
    have hmul :=
      ((hasDerivAt_const z (Real.pi : ℂ)⁻¹).mul hinv).mul_const (g w)
    simpa [F, coeff, planarCauchyKernel, planarBeurlingKernel, mul_assoc] using hmul
  have hparam := hasFDerivAt_integral_of_dominated_of_fderiv_le
    hs hmeas hint hderivmeas hbound hBint hdiff
  have hF'int : Integrable (F' x) (volume : Measure ℂ) := by
    refine Integrable.mono' hBint hderivmeas ?_
    filter_upwards [hbound] with w hw
    exact hw x (Metric.mem_ball_self (half_pos hδ))
  have hmapint : (∫ w : ℂ, F' x w ∂volume) =
      ContinuousLinearMap.toSpanSingleton ℂ
        (∫ w : ℂ, coeff x w ∂volume) := by
    ext
    rw [ContinuousLinearMap.integral_apply hF'int]
    simp [F', ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hfun : (fun z ↦ ∫ w : ℂ, F z w ∂volume) =
      cauchyTransform g := by
    funext z
    unfold F cauchyTransform planarCauchyKernel
    simpa [mul_assoc] using integral_const_mul (Real.pi : ℂ)⁻¹
      (fun w : ℂ ↦ (z - w)⁻¹ * g w)
  rw [hfun, hmapint] at hparam
  exact hparam

/--
%%handwave
name:
  Physical-kernel formula for the holomorphic derivative of the Cauchy transform
statement:
  If $g\in C_c^\infty(\mathbb C)$ and
  $x\notin\operatorname{supp}g$, then
  $$
    \partial_z\mathcal Cg(x)
      =\int_{\mathbb C}-\frac{g(w)}{\pi(x-w)^2}\,dw.
  $$
proof:
  Restrict the complex Fréchet derivative to real scalars. Its
  antiholomorphic component vanishes and its holomorphic Wirtinger component
  is the displayed complex derivative.
-/
theorem frechetDZValue_cauchyTransform_eq_kernelIntegral_of_not_mem_tsupport
    (g : PlaneTestFunction) (x : ℂ) (hx : x ∉ tsupport g) :
    frechetDZValue (cauchyTransform g) x =
      ∫ w : ℂ, planarBeurlingKernel (x - w) * g w ∂volume := by
  have h :=
    (hasFDerivAt_cauchyTransform_of_not_mem_tsupport g x hx).restrictScalars ℝ
  rw [frechetDZValue, h.fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [show Complex.I * (Complex.I *
      (∫ w : ℂ, planarBeurlingKernel (x - w) * g w ∂volume)) =
        -(∫ w : ℂ, planarBeurlingKernel (x - w) * g w ∂volume) by
      rw [← mul_assoc, Complex.I_mul_I]
      simp]
  ring

/--
%%handwave
name:
  Off-support physical-kernel representation of the $L^2$ Beurling transform
statement:
  For $g\in C_c^\infty(\mathbb C)$, almost every
  $x\notin\operatorname{supp}g$ satisfies
  $$
    \mathcal Sg(x)
      =\int_{\mathbb C}-\frac{g(w)}{\pi(x-w)^2}\,dw,
  $$
  where $\mathcal S$ is the Fourier-multiplier Beurling transform on $L^2$.
proof:
  The holomorphic derivative of the Cauchy transform equals the $L^2$
  Beurling transform almost everywhere. Away from the support, substitute
  the proved pointwise physical-kernel formula for that derivative.
-/
theorem beurlingTransformL2_eq_kernelIntegral_ae_off_tsupport
    (g : PlaneTestFunction) :
    ∀ᵐ x : ℂ ∂volume, x ∉ tsupport g →
      (beurlingTransformL2 (testFunctionPlaneL2 g) : ℂ → ℂ) x =
        ∫ w : ℂ, planarBeurlingKernel (x - w) * g w ∂volume := by
  filter_upwards [frechetDZValue_cauchyTransform_ae g] with x hx
  intro hxsupp
  rw [← hx,
    frechetDZValue_cauchyTransform_eq_kernelIntegral_of_not_mem_tsupport
      g x hxsupp]

end

end Quasiconformal

end JJMath
