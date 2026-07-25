import JJMath.Quasiconformal.BeurlingTransform
import JJMath.Quasiconformal.CauchyKernel
import JJMath.Quasiconformal.LocalSobolev
import JJMath.Quasiconformal.ApproxDifferentiability
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The planar Cauchy transform

This file starts the Cauchy--Beurling interface on smooth compactly supported
functions.  The Cauchy kernel is locally integrable, so its convolution with
a test function is an honest Bochner integral at every point.  Test functions
are also placed canonically in planar `L²`, where the Beurling transform from
`BeurlingTransform.lean` is available.

The distributional fundamental-solution identity for the Cauchy kernel is
proved in `CauchyKernel.lean`. The remaining analytic heart is stated directly:
the Cauchy transform has
weak Wirtinger derivatives `∂_z Cg = Sg` and `∂_{\bar z} Cg = g`.  Its proof
now reduces to passing that identity through convolution and identifying the
other component by Fourier transformation.
-/

namespace JJMath

open Set MeasureTheory
open scoped Distributions ENNReal SchwartzMap

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Centered planar Cauchy kernel
statement:
  For $z,w\in\mathbb C$, the Cauchy kernel centered at $z$ is
  $$
    K_z(w)=\frac{1}{z-w}.
  $$
-/
def planarCauchyKernel (z w : ℂ) : ℂ :=
  (z - w)⁻¹

/--
%%handwave
name:
  Translation of a planar test function
statement:
  For $w\in\mathbb C$ and $\varphi\in C_c^\infty(\mathbb C)$, its translate
  is the test function $z\mapsto\varphi(z+w)$.
-/
def translatePlaneTestFunction
    (w : ℂ) (φ : PlaneTestFunction) : PlaneTestFunction where
  toFun z := φ (z + w)
  contDiff' := φ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph
    (Homeomorph.addRight w)
  tsupport_subset' := by simp

/--
%%handwave
name:
  Evaluation of a translated planar test function
statement:
  If $\varphi\in C_c^\infty(\mathbb C)$ and $w,z\in\mathbb C$, then the
  translate by $w$ has value $\varphi(z+w)$ at $z$.
proof:
  This is the defining formula for translation.
-/
@[simp]
theorem translatePlaneTestFunction_apply
    (w : ℂ) (φ : PlaneTestFunction) (z : ℂ) :
    translatePlaneTestFunction w φ z = φ (z + w) := rfl

/--
%%handwave
name:
  Wirtinger differentiation commutes with translation
statement:
  If $\varphi\in C_c^\infty(\mathbb C)$ and $w,z\in\mathbb C$, then
  $$
    \partial_{\bar z}\bigl(\varphi(\mathord\cdot+w)\bigr)(z)
      =\partial_{\bar z}\varphi(z+w).
  $$
proof:
  The translation has real Fréchet derivative equal to the identity, so the
  chain rule leaves both directional derivatives unchanged.
-/
theorem frechetDBarValue_translatePlaneTestFunction
    (w : ℂ) (φ : PlaneTestFunction) (z : ℂ) :
    frechetDBarValue (translatePlaneTestFunction w φ) z =
      frechetDBarValue φ (z + w) := by
  have hφ : DifferentiableAt ℝ (φ : ℂ → ℂ) (z + w) :=
    (φ.contDiff.differentiable (by simp)) _
  have hadd : HasFDerivAt (fun x : ℂ ↦ x + w) (1 : ℂ →L[ℝ] ℂ) z := by
    simpa using (hasFDerivAt_id z).add_const w
  have hcomp := hφ.hasFDerivAt.comp z hadd
  have hfderiv : fderiv ℝ (fun x : ℂ ↦ φ (x + w)) z =
      fderiv ℝ (φ : ℂ → ℂ) (z + w) := by
    simpa [Function.comp_def] using hcomp.fderiv
  simp only [frechetDBarValue]
  rw [show fderiv ℝ (translatePlaneTestFunction w φ : ℂ → ℂ) z =
      fderiv ℝ (fun x : ℂ ↦ φ (x + w)) z by rfl,
    hfderiv]

/--
%%handwave
name:
  Fundamental-solution identity centered at an arbitrary point
statement:
  For every $w\in\mathbb C$ and $\varphi\in C_c^\infty(\mathbb C)$,
  $$
    -\frac1\pi\int_{\mathbb C}
      (z-w)^{-1}\partial_{\bar z}\varphi(z)\,dz=\varphi(w).
  $$
proof:
  Apply [the fundamental-solution identity at the origin](lean:JJMath.Quasiconformal.neg_piInv_mul_integral_inv_mul_frechetDBarValue_eq_eval_zero) to $z\mapsto\varphi(z+w)$ and use translation invariance of planar Lebesgue measure.
-/
theorem neg_piInv_mul_integral_sub_inv_mul_frechetDBarValue_eq_eval
    (w : ℂ) (φ : PlaneTestFunction) :
    -(Real.pi : ℂ)⁻¹ *
        (∫ z : ℂ, (z - w)⁻¹ * frechetDBarValue φ z ∂volume) =
      φ w := by
  have hfund :=
    neg_piInv_mul_integral_inv_mul_frechetDBarValue_eq_eval_zero
      (translatePlaneTestFunction w φ)
  have hshift := integral_add_right_eq_self
    (fun z : ℂ ↦ (z - w)⁻¹ * frechetDBarValue φ z) w
    (μ := (volume : Measure ℂ))
  simp only [add_sub_cancel_right] at hshift
  rw [← hshift]
  simpa only [translatePlaneTestFunction_apply,
    frechetDBarValue_translatePlaneTestFunction, zero_add] using hfund

/--
%%handwave
name:
  Local integrability of every centered Cauchy kernel
statement:
  For every $z\in\mathbb C$, the function
  $w\mapsto (z-w)^{-1}$ is locally integrable on $\mathbb C$.
proof:
  Translate and reflect the [locally integrable reciprocal kernel](lean:JJMath.Quasiconformal.locallyIntegrable_inv_complex). The affine isometry $w\mapsto z-w$ preserves planar Lebesgue measure.
-/
theorem locallyIntegrable_planarCauchyKernel (z : ℂ) :
    LocallyIntegrable (planarCauchyKernel z) (volume : Measure ℂ) := by
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.neg ℂ).trans (Homeomorph.addRight z)
  have he_map : Measure.map e (volume : Measure ℂ) = volume := by
    change Measure.map ((Homeomorph.addRight z) ∘ (Homeomorph.neg ℂ))
      (volume : Measure ℂ) = volume
    rw [← Measure.map_map (Homeomorph.addRight z).continuous.measurable
      (Homeomorph.neg ℂ).continuous.measurable]
    change Measure.map (fun w : ℂ ↦ w + z)
      (Measure.map (fun w : ℂ ↦ -w) volume) = volume
    rw [Measure.map_neg_eq_self]
    exact map_add_right_eq_self volume z
  have hcomp : LocallyIntegrable ((fun w : ℂ ↦ w⁻¹) ∘ e)
      (volume : Measure ℂ) := by
    rw [← locallyIntegrable_map_homeomorph e, he_map]
    exact locallyIntegrable_inv_complex
  simpa [planarCauchyKernel, e, Function.comp_def, sub_eq_add_neg,
    add_comm] using hcomp

/--
%%handwave
name:
  Integrability of the Cauchy kernel against a test function
statement:
  If $g\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$, then
  $$
    w\longmapsto \frac{g(w)}{z-w}
  $$
  is integrable over $\mathbb C$.
proof:
  The centered Cauchy kernel is locally integrable, while $g$ is bounded and
  compactly supported. Their product is therefore integrable.
-/
theorem integrable_planarCauchyKernel_mul_testFunction
    (g : PlaneTestFunction) (z : ℂ) :
    Integrable (fun w : ℂ ↦ planarCauchyKernel z w * g w)
      (volume : Measure ℂ) := by
  have hkernel : LocallyIntegrableOn (planarCauchyKernel z)
      (Set.univ : Set ℂ) (volume : Measure ℂ) :=
    locallyIntegrableOn_univ.mpr
      (locallyIntegrable_planarCauchyKernel z)
  have hproduct :=
    g.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ) hkernel
  simpa [mul_comm] using hproduct

/--
%%handwave
name:
  Cauchy transform of a planar test function
statement:
  For $g\in C_c^\infty(\mathbb C)$, its normalized Cauchy transform is
  $$
    \mathcal Cg(z)=\frac1\pi\int_{\mathbb C}\frac{g(w)}{z-w}\,dw.
  $$
-/
def cauchyTransform (g : PlaneTestFunction) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ *
    ∫ w : ℂ, planarCauchyKernel z w * g w ∂volume

/--
%%handwave
name:
  Reciprocal convolution
statement:
  For $g\in C_c^\infty(\mathbb C)$, the reciprocal convolution is
  $$
    (z\mapsto z^{-1})*g.
  $$
-/
def reciprocalConvolution (g : PlaneTestFunction) : ℂ → ℂ :=
  convolution (fun z : ℂ ↦ z⁻¹) (g : ℂ → ℂ)
    (ContinuousLinearMap.mul ℝ ℂ) volume

/--
%%handwave
name:
  A test function is supported in a centered disk
statement:
  For every $g\in C_c^\infty(\mathbb C)$ there is $R\geq0$ such that
  $g(z)=0$ whenever $|z|>R$.
proof:
  The closed support of $g$ is compact and hence bounded; enlarge a centered
  closed ball containing it so that its radius is nonnegative.
-/
theorem exists_nonneg_support_radius_planeTestFunction
    (g : PlaneTestFunction) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ, g z ≠ 0 → ‖z‖ ≤ R := by
  obtain ⟨R, hR⟩ :=
    g.hasCompactSupport.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨|R|, abs_nonneg R, ?_⟩
  intro z hz
  have hzsupport : z ∈ tsupport (g : ℂ → ℂ) :=
    subset_tsupport (g : ℂ → ℂ) hz
  have hzR : ‖z‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hzsupport
  exact hzR.trans (le_abs_self R)

/--
%%handwave
name:
  Far-field decay of the Cauchy transform
statement:
  Suppose $g\in C_c^\infty(\mathbb C)$ vanishes outside
  $\overline B(0,R)$. If $2R\leq|z|$ and $z\ne0$, then
  $$
    |\mathcal Cg(z)|\leq
      \frac{2}{\pi|z|}\int_{\mathbb C}|g(w)|\,dw.
  $$
proof:
  On the support of $g$, the reverse triangle inequality gives
  $|z-w|\geq |z|-R\geq |z|/2$. Bound the Cauchy kernel by
  $2/|z|$ and apply the norm bound for the Bochner integral.
-/
theorem norm_cauchyTransform_le_of_support_subset_closedBall
    (g : PlaneTestFunction) {R : ℝ}
    (hsupp : ∀ w : ℂ, g w ≠ 0 → ‖w‖ ≤ R)
    {z : ℂ} (hzR : 2 * R ≤ ‖z‖) (hz : 0 < ‖z‖) :
    ‖cauchyTransform g z‖ ≤
      (Real.pi)⁻¹ * (2 / ‖z‖) * ∫ w : ℂ, ‖g w‖ ∂volume := by
  have hmajor_int : Integrable
      (fun w : ℂ ↦ (2 / ‖z‖) * ‖g w‖)
      (volume : Measure ℂ) :=
    (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).norm.const_mul _
  have hpoint : ∀ w : ℂ,
      ‖planarCauchyKernel z w * g w‖ ≤
        (2 / ‖z‖) * ‖g w‖ := by
    intro w
    by_cases hgw : g w = 0
    · simp [hgw]
    have hwR : ‖w‖ ≤ R := hsupp w hgw
    have hhalf : ‖z‖ / 2 ≤ ‖z - w‖ := by
      calc
        ‖z‖ / 2 ≤ ‖z‖ - R := by linarith
        _ ≤ ‖z - w‖ := by
          linarith [norm_sub_norm_le z w]
    have hzw : 0 < ‖z - w‖ := lt_of_lt_of_le (half_pos hz) hhalf
    have hinv : ‖(z - w)⁻¹‖ ≤ 2 / ‖z‖ := by
      rw [norm_inv]
      have hle := one_div_le_one_div_of_le (half_pos hz) hhalf
      simpa [one_div] using hle
    rw [planarCauchyKernel, norm_mul]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  rw [cauchyTransform, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  calc
    (Real.pi)⁻¹ *
        ‖∫ w : ℂ, planarCauchyKernel z w * g w ∂volume‖ ≤
      (Real.pi)⁻¹ *
        ∫ w : ℂ, (2 / ‖z‖) * ‖g w‖ ∂volume := by
          exact mul_le_mul_of_nonneg_left
            (norm_integral_le_of_norm_le hmajor_int
              (Filter.Eventually.of_forall hpoint))
            (inv_nonneg.mpr Real.pi_pos.le)
    _ = (Real.pi)⁻¹ * (2 / ‖z‖) *
        ∫ w : ℂ, ‖g w‖ ∂volume := by
          rw [integral_const_mul]
          ring

/--
%%handwave
name:
  The Cauchy transform as reciprocal convolution
statement:
  For every $g\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$,
  $$
    \mathcal Cg(z)=\frac1\pi
      \bigl((\mathord\cdot)^{-1}*g\bigr)(z).
  $$
proof:
  In the convolution integral substitute $w=z-t$. Reflection and
  translation preserve planar Lebesgue measure, and the resulting integrand
  is $(z-w)^{-1}g(w)$.
-/
theorem cauchyTransform_eq_piInv_mul_reciprocalConvolution
    (g : PlaneTestFunction) (z : ℂ) :
    cauchyTransform g z =
      (Real.pi : ℂ)⁻¹ * reciprocalConvolution g z := by
  rw [cauchyTransform]
  congr 1
  unfold reciprocalConvolution convolution planarCauchyKernel
  have h := integral_sub_left_eq_self
    (fun w : ℂ ↦ (z - w)⁻¹ * g w) (volume : Measure ℂ) z
  simpa using h.symm

/--
%%handwave
name:
  Smoothness of reciprocal convolution
statement:
  If $g\in C_c^\infty(\mathbb C)$, then
  $(\mathord\cdot)^{-1}*g$ is a smooth function on $\mathbb C$.
proof:
  The reciprocal kernel is locally integrable, while $g$ is smooth and
  compactly supported.  Differentiation of convolution may therefore be
  iterated to every order, with all derivatives falling on $g$.
-/
theorem contDiff_reciprocalConvolution (g : PlaneTestFunction) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (reciprocalConvolution g) := by
  simpa [reciprocalConvolution] using
    g.hasCompactSupport.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex g.contDiff

/--
%%handwave
name:
  Continuous differentiability of reciprocal convolution
statement:
  If $g\in C_c^\infty(\mathbb C)$, then
  $(\mathord\cdot)^{-1}*g$ is continuously real differentiable on
  $\mathbb C$.
proof:
  The reciprocal kernel is locally integrable, while $g$ is continuously
  differentiable and compactly supported. Apply differentiation under the
  convolution integral.
-/
theorem contDiff_one_reciprocalConvolution (g : PlaneTestFunction) :
    ContDiff ℝ 1 (reciprocalConvolution g) := by
  exact (contDiff_reciprocalConvolution g).of_le (by simp)

/--
%%handwave
name:
  Smoothness of the Cauchy transform
statement:
  For every $g\in C_c^\infty(\mathbb C)$, the function $\mathcal Cg$ is
  smooth on $\mathbb C$.
proof:
  The Cauchy transform is the smooth reciprocal convolution multiplied by
  the constant $1/\pi$.
-/
theorem contDiff_cauchyTransform (g : PlaneTestFunction) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cauchyTransform g) := by
  have heq : cauchyTransform g = fun z ↦
      (Real.pi : ℂ)⁻¹ * reciprocalConvolution g z := by
    funext z
    exact cauchyTransform_eq_piInv_mul_reciprocalConvolution g z
  rw [heq]
  exact contDiff_const.mul (contDiff_reciprocalConvolution g)

/--
%%handwave
name:
  Continuous differentiability of the Cauchy transform
statement:
  For every $g\in C_c^\infty(\mathbb C)$, the function $\mathcal Cg$ is
  continuously real differentiable on $\mathbb C$.
proof:
  The Cauchy transform is $1/\pi$ times the continuously differentiable
  reciprocal convolution.
-/
theorem contDiff_one_cauchyTransform (g : PlaneTestFunction) :
    ContDiff ℝ 1 (cauchyTransform g) := by
  exact (contDiff_cauchyTransform g).of_le (by simp)

/--
%%handwave
name:
  The Cauchy transform inverts the Wirtinger derivative on test functions
statement:
  For every $g\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$,
  $$
    \mathcal C(\partial_{\bar z}g)(z)=g(z).
  $$
proof:
  Replace $(z-w)^{-1}$ by $-(w-z)^{-1}$ in the defining integral and apply
  [the fundamental-solution identity centered at $z$](lean:JJMath.Quasiconformal.neg_piInv_mul_integral_sub_inv_mul_frechetDBarValue_eq_eval).
-/
theorem cauchyTransform_planeTestFunctionDBar_eq
    (g : PlaneTestFunction) (z : ℂ) :
    cauchyTransform (planeTestFunctionDBar g) z = g z := by
  rw [cauchyTransform]
  change (Real.pi : ℂ)⁻¹ *
      (∫ w : ℂ, (z - w)⁻¹ * frechetDBarValue g w ∂volume) = g z
  rw [show (fun w : ℂ ↦ (z - w)⁻¹ * frechetDBarValue g w) =
      fun w ↦ -((w - z)⁻¹ * frechetDBarValue g w) by
    funext w
    rw [show z - w = -(w - z) by abel, inv_neg]
    ring]
  rw [integral_neg]
  calc
    (Real.pi : ℂ)⁻¹ *
        -(∫ w : ℂ, (w - z)⁻¹ * frechetDBarValue g w ∂volume) =
      -(Real.pi : ℂ)⁻¹ *
        (∫ w : ℂ, (w - z)⁻¹ * frechetDBarValue g w ∂volume) := by ring
    _ = g z :=
      neg_piInv_mul_integral_sub_inv_mul_frechetDBarValue_eq_eval z g

/--
%%handwave
name:
  Wirtinger differentiation passes through reciprocal convolution
statement:
  For every $g\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$,
  $$
    \partial_{\bar z}\bigl((\mathord\cdot)^{-1}*g\bigr)(z)
      =\bigl((\mathord\cdot)^{-1}*\partial_{\bar z}g\bigr)(z).
  $$
proof:
  Differentiate under the convolution integral in the two real coordinate
  directions. Move the resulting finite linear combination through the
  integral and recombine it as $\partial_{\bar z}g$.
-/
theorem frechetDBarValue_reciprocalConvolution
    (g : PlaneTestFunction) (z : ℂ) :
    frechetDBarValue (reciprocalConvolution g) z =
      reciprocalConvolution (planeTestFunctionDBar g) z := by
  have hg1 : ContDiff ℝ 1 (g : ℂ → ℂ) :=
    g.contDiff.of_le (by norm_num)
  have hderiv := g.hasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex hg1 z
  rw [frechetDBarValue, show fderiv ℝ (reciprocalConvolution g) z =
      convolution (fun w : ℂ ↦ w⁻¹) (fderiv ℝ (g : ℂ → ℂ))
        ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) volume z by
    exact hderiv.fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_inv_complex (g.hasCompactSupport.fderiv ℝ)
      (g.contDiff.continuous_fderiv (by simp)) z 1,
    convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_inv_complex (g.hasCompactSupport.fderiv ℝ)
      (g.contDiff.continuous_fderiv (by simp)) z Complex.I]
  unfold reciprocalConvolution convolution
  simp only [ContinuousLinearMap.mul_apply', planeTestFunctionDBar_apply]
  change (1 / 2 : ℂ) *
      ((∫ t : ℂ, t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) 1 ∂volume) +
        Complex.I *
          ∫ t : ℂ,
            t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) Complex.I ∂volume) =
    ∫ t : ℂ, t⁻¹ * frechetDBarValue g (z - t) ∂volume
  let d1 : PlaneTestFunction := TestFunction.lineDerivCLM ℂ (1 : ℂ) g
  let dI : PlaneTestFunction := TestFunction.lineDerivCLM ℂ Complex.I g
  have hd1 (x : ℂ) : d1 x = fderiv ℝ (g : ℂ → ℂ) x 1 := by
    rw [show d1 x = lineDeriv ℝ (g : ℂ → ℂ) x 1 by
      simp [d1, TestFunction.lineDerivCLM_apply]]
    exact ((g.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv
  have hdI (x : ℂ) :
      dI x = fderiv ℝ (g : ℂ → ℂ) x Complex.I := by
    rw [show dI x = lineDeriv ℝ (g : ℂ → ℂ) x Complex.I by
      simp [dI, TestFunction.lineDerivCLM_apply]]
    exact ((g.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv
  have h1 : Integrable
      (fun t : ℂ ↦ t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) 1)
      (volume : Measure ℂ) := by
    have hconv := d1.hasCompactSupport.convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex
      d1.continuous z
    simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', hd1] using
      hconv
  have hI : Integrable
      (fun t : ℂ ↦
        t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) Complex.I)
      (volume : Measure ℂ) := by
    have hconv := dI.hasCompactSupport.convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex
      dI.continuous z
    simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', hdI] using
      hconv
  rw [show (fun t : ℂ ↦ t⁻¹ * frechetDBarValue g (z - t)) =
      fun t ↦ (1 / 2 : ℂ) *
        ((t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) 1) +
          Complex.I *
            (t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) Complex.I)) by
    funext t
    simp only [frechetDBarValue]
    ring]
  rw [integral_const_mul, integral_add h1 (hI.const_mul _),
    integral_const_mul]

/--
%%handwave
name:
  Holomorphic Wirtinger differentiation passes through reciprocal convolution
statement:
  For every $g\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$,
  $$
    \partial_z\bigl((\mathord\cdot)^{-1}*g\bigr)(z)
      =\bigl((\mathord\cdot)^{-1}*\partial_zg\bigr)(z).
  $$
proof:
  Differentiate under the convolution integral in the two real coordinate
  directions. Move their difference through the integral and recombine it as
  $\partial_zg$.
-/
theorem frechetDZValue_reciprocalConvolution
    (g : PlaneTestFunction) (z : ℂ) :
    frechetDZValue (reciprocalConvolution g) z =
      reciprocalConvolution (planeTestFunctionZ g) z := by
  have hg1 : ContDiff ℝ 1 (g : ℂ → ℂ) :=
    g.contDiff.of_le (by norm_num)
  have hderiv := g.hasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex hg1 z
  rw [frechetDZValue, show fderiv ℝ (reciprocalConvolution g) z =
      convolution (fun w : ℂ ↦ w⁻¹) (fderiv ℝ (g : ℂ → ℂ))
        ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) volume z by
    exact hderiv.fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_inv_complex (g.hasCompactSupport.fderiv ℝ)
      (g.contDiff.continuous_fderiv (by simp)) z 1,
    convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_inv_complex (g.hasCompactSupport.fderiv ℝ)
      (g.contDiff.continuous_fderiv (by simp)) z Complex.I]
  unfold reciprocalConvolution convolution
  simp only [ContinuousLinearMap.mul_apply', planeTestFunctionZ_apply]
  change (1 / 2 : ℂ) *
      ((∫ t : ℂ, t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) 1 ∂volume) -
        Complex.I *
          ∫ t : ℂ,
            t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) Complex.I ∂volume) =
    ∫ t : ℂ, t⁻¹ * frechetDZValue g (z - t) ∂volume
  let d1 : PlaneTestFunction := TestFunction.lineDerivCLM ℂ (1 : ℂ) g
  let dI : PlaneTestFunction := TestFunction.lineDerivCLM ℂ Complex.I g
  have hd1 (x : ℂ) : d1 x = fderiv ℝ (g : ℂ → ℂ) x 1 := by
    rw [show d1 x = lineDeriv ℝ (g : ℂ → ℂ) x 1 by
      simp [d1, TestFunction.lineDerivCLM_apply]]
    exact ((g.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv
  have hdI (x : ℂ) :
      dI x = fderiv ℝ (g : ℂ → ℂ) x Complex.I := by
    rw [show dI x = lineDeriv ℝ (g : ℂ → ℂ) x Complex.I by
      simp [dI, TestFunction.lineDerivCLM_apply]]
    exact ((g.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv
  have h1 : Integrable
      (fun t : ℂ ↦ t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) 1)
      (volume : Measure ℂ) := by
    have hconv := d1.hasCompactSupport.convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex
      d1.continuous z
    simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', hd1] using
      hconv
  have hI : Integrable
      (fun t : ℂ ↦
        t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) Complex.I)
      (volume : Measure ℂ) := by
    have hconv := dI.hasCompactSupport.convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex
      dI.continuous z
    simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', hdI] using
      hconv
  rw [show (fun t : ℂ ↦ t⁻¹ * frechetDZValue g (z - t)) =
      fun t ↦ (1 / 2 : ℂ) *
        ((t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) 1) -
          Complex.I *
            (t⁻¹ * fderiv ℝ (g : ℂ → ℂ) (z - t) Complex.I)) by
    funext t
    simp only [frechetDZValue]
    ring]
  rw [integral_const_mul, integral_sub h1 (hI.const_mul _),
    integral_const_mul]

/--
%%handwave
name:
  Holomorphic Wirtinger derivative of the Cauchy transform as a convolution
statement:
  For every $g\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$,
  $$
    \partial_z\mathcal Cg(z)=\mathcal C(\partial_zg)(z).
  $$
proof:
  Write the Cauchy transform as $1/\pi$ times reciprocal convolution and
  apply [holomorphic Wirtinger differentiation through that convolution](lean:JJMath.Quasiconformal.frechetDZValue_reciprocalConvolution).
-/
theorem frechetDZValue_cauchyTransform_eq
    (g : PlaneTestFunction) (z : ℂ) :
    frechetDZValue (cauchyTransform g) z =
      cauchyTransform (planeTestFunctionZ g) z := by
  have hrecDiff : DifferentiableAt ℝ (reciprocalConvolution g) z :=
    (contDiff_one_reciprocalConvolution g).differentiable (by norm_num) z
  have heq : cauchyTransform g = fun w ↦
      (Real.pi : ℂ)⁻¹ * reciprocalConvolution g w := by
    funext w
    exact cauchyTransform_eq_piInv_mul_reciprocalConvolution g w
  rw [heq,
    frechetDZValue_const_mul_of_differentiableAt hrecDiff,
    frechetDZValue_reciprocalConvolution]
  rw [← cauchyTransform_eq_piInv_mul_reciprocalConvolution]

/--
%%handwave
name:
  Compactly supported Cauchy localization
statement:
  Given a smooth compactly supported bump $\beta$ and a planar test function
  $g$, the localized Cauchy transform is the test function
  $z\mapsto\beta(z)\mathcal Cg(z)$.
-/
def cutoffCauchyTransform
    (β : ContDiffBump (0 : ℂ)) (g : PlaneTestFunction) :
    PlaneTestFunction where
  toFun z := β z • cauchyTransform g z
  contDiff' := β.contDiff.smul (contDiff_cauchyTransform g)
  hasCompactSupport' := β.hasCompactSupport.smul_right
  tsupport_subset' := Set.subset_univ _

/--
%%handwave
name:
  Standard Cauchy disk cutoff
statement:
  For $R>0$, the standard disk cutoff $\beta_R$ is smooth, equals one on
  $\overline B(0,R)$, and is supported in $\overline B(0,2R)$.
-/
def cauchyDiskCutoff (R : ℝ) (hR : 0 < R) :
    ContDiffBump (0 : ℂ) where
  rIn := R
  rOut := 2 * R
  rIn_pos := hR
  rIn_lt_rOut := by linarith

/--
%%handwave
name:
  The standard Cauchy cutoff is one on its inner disk
statement:
  If $R>0$ and $|z|\leq R$, then the smooth disk cutoff
  $\beta_R$ satisfies $\beta_R(z)=1$.
proof:
  The inner radius of $\beta_R$ is $R$, so this is the defining inner-disk
  property of a smooth bump.
-/
@[simp]
theorem cauchyDiskCutoff_eq_one_of_norm_le
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    cauchyDiskCutoff R hR z = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, dist_zero_right, cauchyDiskCutoff] using hz

/--
%%handwave
name:
  The standard Cauchy cutoff vanishes outside its outer disk
statement:
  If $R>0$ and $2R\leq|z|$, then the smooth disk cutoff
  $\beta_R$ satisfies $\beta_R(z)=0$.
proof:
  The outer radius of $\beta_R$ is $2R$, so this is the defining
  support property of a smooth bump.
-/
@[simp]
theorem cauchyDiskCutoff_eq_zero_of_two_mul_le_norm
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : 2 * R ≤ ‖z‖) :
    cauchyDiskCutoff R hR z = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simpa [dist_zero_right, cauchyDiskCutoff] using hz

/--
%%handwave
name:
  Scaling formula for the standard Cauchy cutoff
statement:
  If $R>0$, then
  $$
    \beta_R(z)=\beta_1(R^{-1}z).
  $$
proof:
  Both cutoffs use the same fixed bump profile with outer-to-inner radius
  ratio two; only the radial scale changes.
-/
theorem cauchyDiskCutoff_eq_unit_comp_inv_smul
    {R : ℝ} (hR : 0 < R) (z : ℂ) :
    cauchyDiskCutoff R hR z =
      cauchyDiskCutoff 1 zero_lt_one (R⁻¹ • z) := by
  change (someContDiffBumpBase ℂ).toFun ((2 * R) / R)
      (R⁻¹ • (z - 0)) =
    (someContDiffBumpBase ℂ).toFun ((2 * 1) / 1)
      (1⁻¹ • (R⁻¹ • z - 0))
  rw [show (2 * R) / R = 2 by field_simp]
  simp

/--
%%handwave
name:
  Uniform derivative scaling for the standard Cauchy cutoffs
statement:
  There is a constant $A\geq0$ such that for every $R>0$ and
  $z\in\mathbb C$,
  $$
    \lVert D\beta_R(z)\rVert\leq \frac{A}{R}.
  $$
proof:
  The unit-scale cutoff is smooth and compactly supported, hence globally
  Lipschitz with some constant $A$. Compose it with the dilation
  $z\mapsto R^{-1}z$ and use the converse mean-value bound for its Fréchet
  derivative.
-/
theorem exists_norm_fderiv_cauchyDiskCutoff_le_div :
    ∃ A : NNReal, ∀ (R : ℝ) (hR : 0 < R) (z : ℂ),
      ‖fderiv ℝ (cauchyDiskCutoff R hR : ℂ → ℝ) z‖ ≤
        (A : ℝ) / R := by
  let β : ContDiffBump (0 : ℂ) := cauchyDiskCutoff 1 zero_lt_one
  have hβone : ContDiff ℝ 1 β := β.contDiff
  obtain ⟨A, hA⟩ :=
    hβone.lipschitzWith_of_hasCompactSupport β.hasCompactSupport
      (by norm_num)
  refine ⟨A, ?_⟩
  intro R hR z
  have heq : (cauchyDiskCutoff R hR : ℂ → ℝ) =
      fun w ↦ β (R⁻¹ • w) := by
    funext w
    exact cauchyDiskCutoff_eq_unit_comp_inv_smul hR w
  rw [heq]
  have hscale : LipschitzWith ‖R⁻¹‖₊ (fun w : ℂ ↦ R⁻¹ • w) :=
    lipschitzWith_smul R⁻¹
  have hcomp := hA.comp hscale
  have hbound := norm_fderiv_le_of_lipschitz ℝ hcomp (x₀ := z)
  simpa [β, NNReal.smul_def, norm_inv, Real.norm_eq_abs,
    abs_of_pos hR, div_eq_mul_inv] using hbound

/--
%%handwave
name:
  Wirtinger derivative scaling for the standard Cauchy cutoffs
statement:
  There is a constant $A\geq0$ such that for every $R>0$ and
  $z\in\mathbb C$,
  $$
    |\partial_z\beta_R(z)|\leq \frac{A}{R},
    \qquad
    |\partial_{\bar z}\beta_R(z)|\leq \frac{A}{R}.
  $$
proof:
  Regard the real cutoff as complex-valued. Its unit-scale representative is
  smooth and compactly supported, hence globally Lipschitz. Dilation gives
  the $A/R$ bound for its full Fréchet derivative, and each Wirtinger
  component has norm at most the full operator norm.
-/
theorem exists_norm_frechetDZValue_and_frechetDBarValue_cauchyDiskCutoff_le_div :
    ∃ A : NNReal, ∀ (R : ℝ) (hR : 0 < R) (z : ℂ),
      ‖frechetDZValue
          (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z‖ ≤
          (A : ℝ) / R ∧
        ‖frechetDBarValue
          (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z‖ ≤
          (A : ℝ) / R := by
  let β : ContDiffBump (0 : ℂ) := cauchyDiskCutoff 1 zero_lt_one
  let βc : ℂ → ℂ := fun w ↦ (β w : ℂ)
  have hβc_compact : HasCompactSupport βc := by
    have hsupp :
        Function.support βc = Function.support (β : ℂ → ℝ) := by
      ext w
      simp [βc, Function.mem_support]
    rw [HasCompactSupport, tsupport, hsupp]
    exact β.hasCompactSupport
  have hβc_one : ContDiff ℝ 1 βc :=
    (show ContDiff ℝ 1 (fun w : ℂ ↦ (β w : ℂ)) from
      Complex.ofRealCLM.contDiff.comp β.contDiff)
  obtain ⟨A, hA⟩ :=
    hβc_one.lipschitzWith_of_hasCompactSupport hβc_compact
      (by norm_num)
  refine ⟨A, ?_⟩
  intro R hR z
  let fR : ℂ → ℂ :=
    fun w ↦ (cauchyDiskCutoff R hR w : ℂ)
  have heq : fR = fun w ↦ βc (R⁻¹ • w) := by
    funext w
    exact congrArg (fun t : ℝ ↦ (t : ℂ))
      (cauchyDiskCutoff_eq_unit_comp_inv_smul hR w)
  have hscale : LipschitzWith ‖R⁻¹‖₊ (fun w : ℂ ↦ R⁻¹ • w) :=
    lipschitzWith_smul R⁻¹
  have hcomp := hA.comp hscale
  have hfull : ‖fderiv ℝ fR z‖ ≤ (A : ℝ) / R := by
    rw [heq]
    have hbound := norm_fderiv_le_of_lipschitz ℝ hcomp (x₀ := z)
    simpa [βc, β, NNReal.smul_def, norm_inv, Real.norm_eq_abs,
      abs_of_pos hR, div_eq_mul_inv] using hbound
  constructor
  · calc
      ‖frechetDZValue fR z‖ ≤ ‖fderiv ℝ fR z‖ := by
        change ‖weakDZ (fderiv ℝ fR z)‖ ≤ ‖fderiv ℝ fR z‖
        rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
        exact le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ (A : ℝ) / R := hfull
  · calc
      ‖frechetDBarValue fR z‖ ≤ ‖fderiv ℝ fR z‖ := by
        change ‖weakDBar (fderiv ℝ fR z)‖ ≤ ‖fderiv ℝ fR z‖
        rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
        exact le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ (A : ℝ) / R := hfull

/--
%%handwave
name:
  Vanishing cutoff derivative in the inner disk
statement:
  If $R>0$ and $|z|<R$, then the standard cutoff satisfies
  $$
    \partial_{\bar z}\beta_R(z)=0.
  $$
proof:
  The cutoff is identically one in a neighborhood of every point of the
  open inner disk, so its Fréchet derivative, and hence its
  antiholomorphic Wirtinger derivative, vanishes there.
-/
theorem frechetDBarValue_cauchyDiskCutoff_eq_zero_of_norm_lt
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    frechetDBarValue
        (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z = 0 := by
  have hzball : z ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have heqR : (cauchyDiskCutoff R hR : ℂ → ℝ) =ᶠ[nhds z]
      fun _ : ℂ ↦ (1 : ℝ) :=
    (cauchyDiskCutoff R hR).eventuallyEq_one_of_mem_ball hzball
  have heqC :
      (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) =ᶠ[nhds z]
        fun _ : ℂ ↦ (1 : ℂ) :=
    heqR.fun_comp (fun t : ℝ ↦ (t : ℂ))
  rw [frechetDBarValue,
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heqC]
  simp

/--
%%handwave
name:
  Vanishing holomorphic cutoff derivative in the inner disk
statement:
  If $R>0$ and $|z|<R$, then the standard cutoff satisfies
  $$
    \partial_z\beta_R(z)=0.
  $$
proof:
  The cutoff is identically one in a neighborhood of every point of the
  open inner disk, so its Fréchet derivative, and hence its holomorphic
  Wirtinger derivative, vanishes there.
-/
theorem frechetDZValue_cauchyDiskCutoff_eq_zero_of_norm_lt
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    frechetDZValue
        (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z = 0 := by
  have hzball : z ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have heqR : (cauchyDiskCutoff R hR : ℂ → ℝ) =ᶠ[nhds z]
      fun _ : ℂ ↦ (1 : ℝ) :=
    (cauchyDiskCutoff R hR).eventuallyEq_one_of_mem_ball hzball
  have heqC :
      (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) =ᶠ[nhds z]
        fun _ : ℂ ↦ (1 : ℂ) :=
    heqR.fun_comp (fun t : ℝ ↦ (t : ℂ))
  rw [frechetDZValue,
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heqC]
  simp

/--
%%handwave
name:
  Vanishing cutoff derivative outside the outer disk
statement:
  If $R>0$ and $2R<|z|$, then the standard cutoff satisfies
  $$
    \partial_{\bar z}\beta_R(z)=0.
  $$
proof:
  The cutoff is identically zero in a neighborhood of every point strictly
  outside its outer disk, so its Fréchet derivative, and hence its
  antiholomorphic Wirtinger derivative, vanishes there.
-/
theorem frechetDBarValue_cauchyDiskCutoff_eq_zero_of_two_mul_lt_norm
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : 2 * R < ‖z‖) :
    frechetDBarValue
        (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z = 0 := by
  have hnear : {w : ℂ | 2 * R < ‖w‖} ∈ nhds z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  have heqC :
      (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) =ᶠ[nhds z]
        fun _ : ℂ ↦ (0 : ℂ) := by
    filter_upwards [hnear] with w hw
    rw [cauchyDiskCutoff_eq_zero_of_two_mul_le_norm hR hw.le]
    simp
  rw [frechetDBarValue,
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heqC]
  simp

/--
%%handwave
name:
  Holomorphic derivative of a cutoff Cauchy transform
statement:
  If $\beta$ is a smooth compactly supported real cutoff and
  $g\in C_c^\infty(\mathbb C)$, then
  $$
    \partial_z(\beta\mathcal Cg)
      =(\partial_z\beta)\mathcal Cg+\beta\mathcal C(\partial_zg).
  $$
proof:
  Apply the Wirtinger product rule and the pointwise convolution formula for
  $\partial_z\mathcal Cg$.
-/
theorem frechetDZValue_cutoffCauchyTransform
    (β : ContDiffBump (0 : ℂ)) (g : PlaneTestFunction) (z : ℂ) :
    frechetDZValue (cutoffCauchyTransform β g) z =
      frechetDZValue (fun w : ℂ ↦ (β w : ℂ)) z * cauchyTransform g z +
        (β z : ℂ) * cauchyTransform (planeTestFunctionZ g) z := by
  have hβ : DifferentiableAt ℝ (fun w : ℂ ↦ (β w : ℂ)) z :=
    (show ContDiff ℝ 1 (fun w : ℂ ↦ (β w : ℂ)) from
      Complex.ofRealCLM.contDiff.comp β.contDiff).differentiable
        (by norm_num) z
  have hC : DifferentiableAt ℝ (cauchyTransform g) z :=
    (contDiff_one_cauchyTransform g).differentiable (by norm_num) z
  rw [show (cutoffCauchyTransform β g : ℂ → ℂ) =
      fun w ↦ (β w : ℂ) * cauchyTransform g w by
    funext w
    exact Complex.real_smul]
  rw [frechetDZValue_mul_of_differentiableAt hβ hC,
    frechetDZValue_cauchyTransform_eq]

/--
%%handwave
name:
  The antiholomorphic Wirtinger derivative of the Cauchy transform
statement:
  For every $g\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$,
  $$
    \partial_{\bar z}\mathcal Cg(z)=g(z).
  $$
proof:
  Pass $\partial_{\bar z}$ through reciprocal convolution, then apply
  [the fact that the Cauchy transform inverts $\partial_{\bar z}$ on test functions](lean:JJMath.Quasiconformal.cauchyTransform_planeTestFunctionDBar_eq).
-/
theorem frechetDBarValue_cauchyTransform
    (g : PlaneTestFunction) (z : ℂ) :
    frechetDBarValue (cauchyTransform g) z = g z := by
  have hrecDiff : DifferentiableAt ℝ (reciprocalConvolution g) z :=
    (contDiff_one_reciprocalConvolution g).differentiable (by norm_num) z
  have heq : cauchyTransform g = fun w ↦
      (Real.pi : ℂ)⁻¹ * reciprocalConvolution g w := by
    funext w
    exact cauchyTransform_eq_piInv_mul_reciprocalConvolution g w
  rw [heq,
    frechetDBarValue_const_mul_of_differentiableAt hrecDiff,
    frechetDBarValue_reciprocalConvolution]
  rw [← cauchyTransform_eq_piInv_mul_reciprocalConvolution]
  exact cauchyTransform_planeTestFunctionDBar_eq g z

/--
%%handwave
name:
  Antiholomorphic derivative of a cutoff Cauchy transform
statement:
  If $\beta$ is a smooth compactly supported real cutoff and
  $g\in C_c^\infty(\mathbb C)$, then
  $$
    \partial_{\bar z}(\beta\mathcal Cg)
      =(\partial_{\bar z}\beta)\mathcal Cg+\beta g.
  $$
proof:
  Apply the Wirtinger product rule and the pointwise identity
  $\partial_{\bar z}\mathcal Cg=g$.
-/
theorem frechetDBarValue_cutoffCauchyTransform
    (β : ContDiffBump (0 : ℂ)) (g : PlaneTestFunction) (z : ℂ) :
    frechetDBarValue (cutoffCauchyTransform β g) z =
      frechetDBarValue (fun w : ℂ ↦ (β w : ℂ)) z * cauchyTransform g z +
        (β z : ℂ) * g z := by
  have hβ : DifferentiableAt ℝ (fun w : ℂ ↦ (β w : ℂ)) z :=
    (show ContDiff ℝ 1 (fun w : ℂ ↦ (β w : ℂ)) from
      Complex.ofRealCLM.contDiff.comp β.contDiff).differentiable
        (by norm_num) z
  have hC : DifferentiableAt ℝ (cauchyTransform g) z :=
    (contDiff_one_cauchyTransform g).differentiable (by norm_num) z
  rw [show (cutoffCauchyTransform β g : ℂ → ℂ) =
      fun w ↦ (β w : ℂ) * cauchyTransform g w by
    funext w
    exact Complex.real_smul]
  rw [frechetDBarValue_mul_of_differentiableAt hβ hC,
    frechetDBarValue_cauchyTransform]

/--
%%handwave
name:
  Antiholomorphic cutoff error
statement:
  For $R>0$ and $g\in C_c^\infty(\mathbb C)$, the disk-cutoff error is
  $$
    \partial_{\bar z}(\beta_R\mathcal Cg)-g,
  $$
  regarded as a smooth compactly supported function.
-/
def cauchyDiskCutoffDBarError
    (R : ℝ) (hR : 0 < R) (g : PlaneTestFunction) :
    PlaneTestFunction :=
  planeTestFunctionDBar
      (cutoffCauchyTransform (cauchyDiskCutoff R hR) g) - g

/--
%%handwave
name:
  Pointwise formula for the cutoff Cauchy error
statement:
  Suppose $g$ vanishes outside $\overline B(0,r)$ and $r\leq R$. Then
  for every $z\in\mathbb C$,
  $$
    \partial_{\bar z}(\beta_R\mathcal Cg)(z)-g(z)
      =\partial_{\bar z}\beta_R(z)\,\mathcal Cg(z).
  $$
proof:
  Expand the cutoff product rule. On the support of $g$ one has
  $\beta_R=1$, while away from that support the term containing $g$
  vanishes.
-/
theorem cauchyDiskCutoffDBarError_apply
    {r R : ℝ} (hR : 0 < R) (g : PlaneTestFunction)
    (hsupp : ∀ z : ℂ, g z ≠ 0 → ‖z‖ ≤ r) (hrR : r ≤ R)
    (z : ℂ) :
    cauchyDiskCutoffDBarError R hR g z =
      frechetDBarValue
          (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z *
        cauchyTransform g z := by
  have hβg : (cauchyDiskCutoff R hR z : ℂ) * g z = g z := by
    by_cases hgz : g z = 0
    · simp [hgz]
    · rw [cauchyDiskCutoff_eq_one_of_norm_le hR
          ((hsupp z hgz).trans hrR)]
      simp
  change
    frechetDBarValue
        (cutoffCauchyTransform (cauchyDiskCutoff R hR) g) z - g z =
      frechetDBarValue
          (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z *
        cauchyTransform g z
  rw [frechetDBarValue_cutoffCauchyTransform, hβg]
  ring

/--
%%handwave
name:
  Pointwise bound for the cutoff Cauchy error
statement:
  Suppose $g$ vanishes outside $\overline B(0,r)$, $2r\leq R$, and
  $|\partial_{\bar z}\beta_R|\leq A/R$. Then for every $z\in\mathbb C$,
  $$
    \left|\partial_{\bar z}(\beta_R\mathcal Cg)(z)-g(z)\right|
      \leq \frac A R\frac{2}{\pi R}
        \int_{\mathbb C}|g(w)|\,dw.
  $$
proof:
  The error vanishes in the open inner disk. Outside that disk, the
  far-field estimate gives
  $|\mathcal Cg(z)|\leq2(\pi R)^{-1}\int|g|$; multiply it by the assumed
  $A/R$ derivative bound and use the exact cutoff-error formula.
-/
theorem norm_cauchyDiskCutoffDBarError_le
    {r R : ℝ} (hR : 0 < R) (g : PlaneTestFunction)
    (hsupp : ∀ z : ℂ, g z ≠ 0 → ‖z‖ ≤ r) (h2rR : 2 * r ≤ R)
    (A : NNReal)
    (hA : ∀ z : ℂ,
      ‖frechetDBarValue
          (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z‖ ≤
        (A : ℝ) / R)
    (z : ℂ) :
    ‖cauchyDiskCutoffDBarError R hR g z‖ ≤
      ((A : ℝ) / R) *
        ((Real.pi)⁻¹ * (2 / R) * ∫ w : ℂ, ‖g w‖ ∂volume) := by
  have hInt : 0 ≤ ∫ w : ℂ, ‖g w‖ ∂volume :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hright : 0 ≤
      ((A : ℝ) / R) *
        ((Real.pi)⁻¹ * (2 / R) * ∫ w : ℂ, ‖g w‖ ∂volume) := by
    positivity
  by_cases hzR : ‖z‖ < R
  · rw [cauchyDiskCutoffDBarError_apply hR g hsupp
      (by linarith : r ≤ R),
      frechetDBarValue_cauchyDiskCutoff_eq_zero_of_norm_lt hR hzR]
    simpa using hright
  · have hRz : R ≤ ‖z‖ := le_of_not_gt hzR
    have hzpos : 0 < ‖z‖ := hR.trans_le hRz
    have hC := norm_cauchyTransform_le_of_support_subset_closedBall
      g hsupp (h2rR.trans hRz) hzpos
    rw [cauchyDiskCutoffDBarError_apply hR g hsupp
      (by linarith : r ≤ R), norm_mul]
    apply mul_le_mul (hA z) (hC.trans ?_)
      (norm_nonneg _) (by positivity)
    gcongr

/--
%%handwave
name:
  Disk support of the cutoff Cauchy error
statement:
  Suppose $g$ vanishes outside $\overline B(0,r)$ and $2r\leq R$. If
  $3R\leq|z|$, then
  $$
    \partial_{\bar z}(\beta_R\mathcal Cg)(z)-g(z)=0.
  $$
proof:
  Since $R>0$, the inequality $3R\leq|z|$ places $z$ strictly outside the
  outer cutoff disk of radius $2R$. The cutoff derivative therefore
  vanishes there, and so does the exact product-rule error.
-/
theorem cauchyDiskCutoffDBarError_eq_zero_of_three_mul_le_norm
    {r R : ℝ} (hR : 0 < R) (g : PlaneTestFunction)
    (hsupp : ∀ z : ℂ, g z ≠ 0 → ‖z‖ ≤ r) (h2rR : 2 * r ≤ R)
    {z : ℂ} (hz : 3 * R ≤ ‖z‖) :
    cauchyDiskCutoffDBarError R hR g z = 0 := by
  rw [cauchyDiskCutoffDBarError_apply hR g hsupp
    (by linarith : r ≤ R),
    frechetDBarValue_cauchyDiskCutoff_eq_zero_of_two_mul_lt_norm hR
      (by linarith)]
  simp

/--
%%handwave
name:
  Schwartz embedding of planar test functions
statement:
  Every $g\in C_c^\infty(\mathbb C)$ determines a Schwartz function with
  the same pointwise values.
-/
def planeTestFunctionSchwartz
    (g : PlaneTestFunction) : 𝓢(ℂ, ℂ) :=
  g.hasCompactSupport.toSchwartzMap g.contDiff

/--
%%handwave
name:
  Pointwise value of the Schwartz embedding of a test function
statement:
  A compactly supported smooth function and its canonical Schwartz embedding
  have the same value at every point of $\mathbb C$.
proof:
  The Schwartz embedding retains the original function as its underlying
  pointwise map.
-/
@[simp]
theorem planeTestFunctionSchwartz_apply
    (g : PlaneTestFunction) (z : ℂ) :
    planeTestFunctionSchwartz g z = g z := rfl

/--
%%handwave
name:
  Schwartz embedding commutes with the antiholomorphic Wirtinger derivative
statement:
  For every $g\in C_c^\infty(\mathbb C)$, embedding
  $\partial_{\bar z}g$ into Schwartz space gives the same Schwartz function
  as applying $\partial_{\bar z}$ after embedding $g$.
proof:
  Both sides are the same linear combination of the real directional
  derivatives in directions $1$ and $i$.
-/
theorem schwartzWirtingerDBar_planeTestFunctionSchwartz
    (g : PlaneTestFunction) :
    schwartzWirtingerDBar (planeTestFunctionSchwartz g) =
      planeTestFunctionSchwartz (planeTestFunctionDBar g) := by
  ext z
  simp only [schwartzWirtingerDBar, SchwartzMap.smul_apply,
    SchwartzMap.add_apply, planeTestFunctionSchwartz_apply,
    planeTestFunctionDBar_apply]
  rw [frechetDBarValue]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have heq : (planeTestFunctionSchwartz g : ℂ → ℂ) =
      (g : ℂ → ℂ) := by
    funext w
    rfl
  rw [heq]
  simp only [smul_eq_mul]
  ring

/--
%%handwave
name:
  Schwartz embedding commutes with the holomorphic Wirtinger derivative
statement:
  For every $g\in C_c^\infty(\mathbb C)$, embedding $\partial_zg$ into
  Schwartz space gives the same Schwartz function as applying $\partial_z$
  after embedding $g$.
proof:
  Both sides are the same linear combination of the real directional
  derivatives in directions $1$ and $i$.
-/
theorem schwartzWirtingerZ_planeTestFunctionSchwartz
    (g : PlaneTestFunction) :
    schwartzWirtingerZ (planeTestFunctionSchwartz g) =
      planeTestFunctionSchwartz (planeTestFunctionZ g) := by
  ext z
  simp only [schwartzWirtingerZ, SchwartzMap.smul_apply,
    SchwartzMap.sub_apply, planeTestFunctionSchwartz_apply,
    planeTestFunctionZ_apply]
  rw [frechetDZValue]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have heq : (planeTestFunctionSchwartz g : ℂ → ℂ) =
      (g : ℂ → ℂ) := by
    funext w
    rfl
  rw [heq]
  simp only [smul_eq_mul]
  ring

/--
%%handwave
name:
  $L^2$ class of a planar test function
statement:
  Every $g\in C_c^\infty(\mathbb C)$ determines its canonical equivalence
  class $[g]\in L^2(\mathbb C)$.
-/
def testFunctionPlaneL2 (g : PlaneTestFunction) : PlaneL2 :=
  let hg : MemLp (g : ℂ → ℂ) 2 (volume : Measure ℂ) :=
    g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  hg.toLp g

/--
%%handwave
name:
  The canonical $L^2$ representative of a test function
statement:
  For $g\in C_c^\infty(\mathbb C)$, its canonical class in
  $L^2(\mathbb C)$ is represented almost everywhere by $g$ itself.
proof:
  This is the defining representative property of the passage from a
  square-integrable function to its $L^2$ equivalence class.
-/
theorem testFunctionPlaneL2_coeFn (g : PlaneTestFunction) :
    (testFunctionPlaneL2 g : ℂ → ℂ) =ᵐ[(volume : Measure ℂ)] g := by
  unfold testFunctionPlaneL2
  exact (g.continuous.memLp_of_hasCompactSupport
    (p := (2 : ℝ≥0∞)) (μ := (volume : Measure ℂ))
    g.hasCompactSupport).coeFn_toLp

/--
%%handwave
name:
  Global $L^2$ bound for the cutoff Cauchy error
statement:
  Suppose $g$ vanishes outside $\overline B(0,r)$, $2r\leq R$, and
  $|\partial_{\bar z}\beta_R|\leq A/R$. Then
  $$
    \left\|\partial_{\bar z}(\beta_R\mathcal Cg)-g\right\|_2
      \leq
      \left(\frac A R\frac{2}{\pi R}\int_{\mathbb C}|g|\right)
      3R\sqrt\pi.
  $$
proof:
  The pointwise error is bounded by the first parenthesized factor and
  vanishes outside $B(0,3R)$. Its $L^2$ norm is therefore at most that
  factor times $|B(0,3R)|^{1/2}=3R\sqrt\pi$.
-/
theorem norm_testFunctionPlaneL2_cauchyDiskCutoffDBarError_le
    {r R : ℝ} (hR : 0 < R) (g : PlaneTestFunction)
    (hsupp : ∀ z : ℂ, g z ≠ 0 → ‖z‖ ≤ r) (h2rR : 2 * r ≤ R)
    (A : NNReal)
    (hA : ∀ z : ℂ,
      ‖frechetDBarValue
          (fun w : ℂ ↦ (cauchyDiskCutoff R hR w : ℂ)) z‖ ≤
        (A : ℝ) / R) :
    ‖testFunctionPlaneL2 (cauchyDiskCutoffDBarError R hR g)‖ ≤
      (((A : ℝ) / R) *
        ((Real.pi)⁻¹ * (2 / R) * ∫ w : ℂ, ‖g w‖ ∂volume)) *
          ((3 * R) * Real.sqrt Real.pi) := by
  let e : PlaneTestFunction := cauchyDiskCutoffDBarError R hR g
  let M : ℝ := ((A : ℝ) / R) *
    ((Real.pi)⁻¹ * (2 / R) * ∫ w : ℂ, ‖g w‖ ∂volume)
  let B : Set ℂ := Metric.ball 0 (3 * R)
  have hM : 0 ≤ M := by
    dsimp [M]
    have hInt : 0 ≤ ∫ w : ℂ, ‖g w‖ ∂volume :=
      integral_nonneg fun _ ↦ norm_nonneg _
    positivity
  have hpoint : ∀ z : ℂ, ‖e z‖ ≤ M := by
    intro z
    exact norm_cauchyDiskCutoffDBarError_le hR g hsupp h2rR A hA z
  have heq : B.indicator (e : ℂ → ℂ) = (e : ℂ → ℂ) := by
    funext z
    by_cases hzB : z ∈ B
    · rw [Set.indicator_of_mem hzB]
    · rw [Set.indicator_of_notMem hzB]
      symm
      apply cauchyDiskCutoffDBarError_eq_zero_of_three_mul_le_norm
        hR g hsupp h2rR
      simpa [B, Metric.mem_ball, dist_zero_right, not_lt] using hzB
  have hBpos : 0 < 3 * R := by positivity
  have hmono :
      eLpNorm (e : ℂ → ℂ) 2 (volume.restrict B) ≤
        eLpNorm (fun _ : ℂ ↦ M) 2 (volume.restrict B) := by
    apply eLpNorm_mono_ae_real
    filter_upwards [] with z
    exact hpoint z
  have hconst_top :
      eLpNorm (fun _ : ℂ ↦ M) 2 (volume.restrict B) ≠
        (⊤ : ENNReal) := by
    haveI : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.2
        (ne_of_lt (lt_of_le_of_lt
          (measure_mono Metric.ball_subset_closedBall)
          (isCompact_closedBall (0 : ℂ) (3 * R)).measure_lt_top))
    exact (memLp_const M).eLpNorm_ne_top
  have hreal := (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top hconst_top hmono) hconst_top).2 hmono
  have hnorm :
      ‖testFunctionPlaneL2 e‖ =
        (eLpNorm (e : ℂ → ℂ) 2 volume).toReal := by
    unfold testFunctionPlaneL2
    rw [Lp.norm_toLp]
  rw [hnorm, ← heq,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
  rw [eLpNorm_const_two_ball_toReal M (0 : ℂ) hBpos] at hreal
  rw [Real.norm_of_nonneg hM] at hreal
  change
    (eLpNorm (cauchyDiskCutoffDBarError R hR g : ℂ → ℂ) 2
      (volume.restrict (Metric.ball 0 (3 * R)))).toReal ≤
        M * ((3 * R) * Real.sqrt Real.pi)
  simpa [e, B] using hreal

/--
%%handwave
name:
  Inverse-radius decay of the cutoff Cauchy error
statement:
  Suppose $g$ vanishes outside $\overline B(0,r)$. There is a constant
  $B\geq0$, depending only on $g$ and the fixed cutoff profile, such that
  whenever $R>0$ and $2r\leq R$,
  $$
    \left\|\partial_{\bar z}(\beta_R\mathcal Cg)-g\right\|_2
      \leq \frac B R.
  $$
proof:
  Use the uniform $A/R$ derivative estimate for the scaled cutoffs in the
  preceding global $L^2$ bound. The pointwise error is $O(R^{-2})$ on a disk
  of area $O(R^2)$, giving the asserted $O(R^{-1})$ norm.
-/
theorem exists_norm_testFunctionPlaneL2_cauchyDiskCutoffDBarError_le_div
    (g : PlaneTestFunction) (r : ℝ)
    (hsupp : ∀ z : ℂ, g z ≠ 0 → ‖z‖ ≤ r) :
    ∃ B : NNReal, ∀ (R : ℝ) (hR : 0 < R), 2 * r ≤ R →
      ‖testFunctionPlaneL2 (cauchyDiskCutoffDBarError R hR g)‖ ≤
        (B : ℝ) / R := by
  obtain ⟨A, hA⟩ :=
    exists_norm_frechetDZValue_and_frechetDBarValue_cauchyDiskCutoff_le_div
  have hInt : 0 ≤ ∫ w : ℂ, ‖g w‖ ∂volume :=
    integral_nonneg fun _ ↦ norm_nonneg _
  let B : NNReal := ⟨6 * (A : ℝ) * (Real.pi)⁻¹ *
    (∫ w : ℂ, ‖g w‖ ∂volume) * Real.sqrt Real.pi, by positivity⟩
  refine ⟨B, ?_⟩
  intro R hR h2rR
  refine (norm_testFunctionPlaneL2_cauchyDiskCutoffDBarError_le
    hR g hsupp h2rR A (fun z ↦ (hA R hR z).2)).trans_eq ?_
  change
    (((A : ℝ) / R) *
      ((Real.pi)⁻¹ * (2 / R) * ∫ w : ℂ, ‖g w‖ ∂volume)) *
        ((3 * R) * Real.sqrt Real.pi) =
      (6 * (A : ℝ) * (Real.pi)⁻¹ *
        (∫ w : ℂ, ‖g w‖ ∂volume) * Real.sqrt Real.pi) / R
  field_simp [hR.ne', Real.pi_ne_zero]
  ring

/--
%%handwave
name:
  Agreement of the test-function and Schwartz $L^2$ embeddings
statement:
  For every $g\in C_c^\infty(\mathbb C)$, its direct class in
  $L^2(\mathbb C)$ equals the $L^2$ class obtained after regarding $g$ as a
  Schwartz function.
proof:
  Both $L^2$ classes are represented almost everywhere by the same pointwise
  function $g$.
-/
theorem testFunctionPlaneL2_eq_planeTestFunctionSchwartz_toLp
    (g : PlaneTestFunction) :
    testFunctionPlaneL2 g = (planeTestFunctionSchwartz g).toLp 2 := by
  apply Lp.ext
  filter_upwards
      [testFunctionPlaneL2_coeFn g,
        (planeTestFunctionSchwartz g).coeFn_toLp 2]
      with z hg hschwartz
  rw [hg, hschwartz]
  rfl

/--
%%handwave
name:
  Beurling transform converts the two test-function Wirtinger derivatives
statement:
  For every $g\in C_c^\infty(\mathbb C)$,
  $$
    \mathcal S(\partial_{\bar z}g)=\partial_zg
  $$
  as elements of $L^2(\mathbb C)$.
proof:
  Embed $g$ into Schwartz space, where [the Beurling multiplier converts $\partial_{\bar z}$ into $\partial_z$](lean:JJMath.Quasiconformal.beurlingTransformL2_schwartzWirtingerDBar), and use compatibility of both Wirtinger derivatives with the embedding.
-/
theorem beurlingTransformL2_testFunctionDBar
    (g : PlaneTestFunction) :
    beurlingTransformL2 (testFunctionPlaneL2 (planeTestFunctionDBar g)) =
      testFunctionPlaneL2 (planeTestFunctionZ g) := by
  rw [testFunctionPlaneL2_eq_planeTestFunctionSchwartz_toLp,
    ← schwartzWirtingerDBar_planeTestFunctionSchwartz,
    beurlingTransformL2_schwartzWirtingerDBar,
    schwartzWirtingerZ_planeTestFunctionSchwartz,
    ← testFunctionPlaneL2_eq_planeTestFunctionSchwartz_toLp]

/--
%%handwave
name:
  Candidate weak differential of the Cauchy transform
statement:
  For $g\in C_c^\infty(\mathbb C)$, the candidate weak differential of
  $\mathcal Cg$ is the real-linear map whose Wirtinger components are
  $\partial_z\mathcal Cg=\mathcal Sg$ and
  $\partial_{\bar z}\mathcal Cg=g$.
-/
def cauchyTransformWeakDifferential
    (g : PlaneTestFunction) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  realLinearMapOfWirtinger
    ((beurlingTransformL2 (testFunctionPlaneL2 g)) z) (g z)

/--
%%handwave
name:
  The $z$-component of the candidate Cauchy differential
statement:
  For $g\in C_c^\infty(\mathbb C)$ and every $z\in\mathbb C$, the
  $\partial_z$ component of the candidate weak differential of
  $\mathcal Cg$ equals the $L^2$ Beurling transform $\mathcal Sg$ at $z$.
proof:
  The real-linear map with Wirtinger components $(a,b)$ has
  $\partial_z$ component $a$.
-/
@[simp]
theorem weakDZField_cauchyTransformWeakDifferential
    (g : PlaneTestFunction) (z : ℂ) :
    weakDZField (cauchyTransformWeakDifferential g) z =
      (beurlingTransformL2 (testFunctionPlaneL2 g)) z := by
  simp [weakDZField, cauchyTransformWeakDifferential]

/--
%%handwave
name:
  The $\overline z$-component of the candidate Cauchy differential
statement:
  For $g\in C_c^\infty(\mathbb C)$ and every $z\in\mathbb C$, the
  $\partial_{\bar z}$ component of the candidate weak differential of
  $\mathcal Cg$ equals $g(z)$.
proof:
  The real-linear map with Wirtinger components $(a,b)$ has
  $\partial_{\bar z}$ component $b$.
-/
@[simp]
theorem weakDBarField_cauchyTransformWeakDifferential
    (g : PlaneTestFunction) (z : ℂ) :
    weakDBarField (cauchyTransformWeakDifferential g) z = g z := by
  simp [weakDBarField, cauchyTransformWeakDifferential]

/--
%%handwave
name:
  The holomorphic Wirtinger derivative of the Cauchy transform
statement:
  For every $g\in C_c^\infty(\mathbb C)$,
  $$
    \partial_z\mathcal Cg=\mathcal Sg
  $$
  almost everywhere on $\mathbb C$, where $\mathcal S$ is the $L^2$
  Beurling transform.
proof:
  Multiply $\mathcal Cg$ by the standard cutoff $\beta_R$. The
  test-function identity
  $\mathcal S(\partial_{\bar z}u)=\partial_zu$ shows that, on every fixed
  disk contained in the inner cutoff disk, the difference
  $\partial_z\mathcal Cg-\mathcal Sg$ is the Beurling transform of the cutoff
  error. The latter has global $L^2$ norm at most $B/R$, and the Beurling
  transform is an isometry. Letting $R$ be arbitrarily large forces the local
  $L^2$ norm of the difference to vanish. Exhaust the plane by closed disks.
-/
theorem frechetDZValue_cauchyTransform_ae (g : PlaneTestFunction) :
    (fun z : ℂ ↦ frechetDZValue (cauchyTransform g) z)
      =ᵐ[(volume : Measure ℂ)]
        (beurlingTransformL2 (testFunctionPlaneL2 g) : ℂ → ℂ) := by
  obtain ⟨r, hr_nonneg, hsupp⟩ :=
    exists_nonneg_support_radius_planeTestFunction g
  obtain ⟨B, hB⟩ :=
    exists_norm_testFunctionPlaneL2_cauchyDiskCutoffDBarError_le_div
      g r hsupp
  let Sg : PlaneL2 := beurlingTransformL2 (testFunctionPlaneL2 g)
  let f0 : ℂ → ℂ := cauchyTransform (planeTestFunctionZ g)
  have hf0_cont : Continuous f0 :=
    (contDiff_cauchyTransform (planeTestFunctionZ g)).continuous
  have hpiece : ∀ n : ℕ,
      f0 =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) n)]
        (Sg : ℂ → ℂ) := by
    intro n
    let C : Set ℂ := Metric.closedBall 0 n
    let d : ℂ → ℂ := fun z ↦ f0 z - Sg z
    have hf0_mem : MemLp f0 2 (volume.restrict C) :=
      memLp_restrict_of_isCompact_of_continuousOn
        (isCompact_closedBall (0 : ℂ) n) hf0_cont.continuousOn
    have hSg_mem : MemLp (Sg : ℂ → ℂ) 2 (volume.restrict C) :=
      (Lp.memLp Sg).restrict C
    have hdmem : MemLp d 2 (volume.restrict C) := hf0_mem.sub hSg_mem
    let dLp : Lp ℂ 2 (volume.restrict C) := hdmem.toLp d
    have hlocal_bound : ∀ (R : ℝ) (hR : 0 < R),
        2 * r ≤ R → (n : ℝ) < R → ‖dLp‖ ≤ (B : ℝ) / R := by
      intro R hR h2rR hnR
      let β : ContDiffBump (0 : ℂ) := cauchyDiskCutoff R hR
      let u : PlaneTestFunction := cutoffCauchyTransform β g
      let e : PlaneTestFunction := cauchyDiskCutoffDBarError R hR g
      have hDBar : planeTestFunctionDBar u = e + g := by
        ext z
        change frechetDBarValue (u : ℂ → ℂ) z =
          (frechetDBarValue (u : ℂ → ℂ) z - g z) + g z
        ring
      have htestDBar :
          testFunctionPlaneL2 (planeTestFunctionDBar u) =
            testFunctionPlaneL2 e + testFunctionPlaneL2 g := by
        apply Lp.ext
        filter_upwards
            [testFunctionPlaneL2_coeFn (planeTestFunctionDBar u),
              testFunctionPlaneL2_coeFn e,
              testFunctionPlaneL2_coeFn g,
              Lp.coeFn_add (testFunctionPlaneL2 e) (testFunctionPlaneL2 g)]
            with z hzD hze hzg hzadd
        rw [hzD, hzadd]
        change planeTestFunctionDBar u z =
          (testFunctionPlaneL2 e : ℂ → ℂ) z +
            (testFunctionPlaneL2 g : ℂ → ℂ) z
        rw [hze, hzg]
        exact DFunLike.congr_fun hDBar z
      have hDZLp :
          testFunctionPlaneL2 (planeTestFunctionZ u) =
            beurlingTransformL2 (testFunctionPlaneL2 e) + Sg := by
        calc
          testFunctionPlaneL2 (planeTestFunctionZ u) =
              beurlingTransformL2
                (testFunctionPlaneL2 (planeTestFunctionDBar u)) :=
            (beurlingTransformL2_testFunctionDBar u).symm
          _ = beurlingTransformL2
                (testFunctionPlaneL2 e + testFunctionPlaneL2 g) := by
            rw [htestDBar]
          _ = beurlingTransformL2 (testFunctionPlaneL2 e) + Sg := by
            rw [map_add]
      have hdiffLp :
          testFunctionPlaneL2 (planeTestFunctionZ u) - Sg =
            beurlingTransformL2 (testFunctionPlaneL2 e) := by
        rw [hDZLp]
        abel
      have haeGlobal :
          (fun z : ℂ ↦ planeTestFunctionZ u z - Sg z) =ᵐ[volume]
            (beurlingTransformL2 (testFunctionPlaneL2 e) : ℂ → ℂ) := by
        calc
          (fun z : ℂ ↦ planeTestFunctionZ u z - Sg z) =ᵐ[volume]
              (testFunctionPlaneL2 (planeTestFunctionZ u) - Sg :
                PlaneL2) := by
            filter_upwards
                [testFunctionPlaneL2_coeFn (planeTestFunctionZ u),
                  Lp.coeFn_sub (testFunctionPlaneL2 (planeTestFunctionZ u)) Sg]
                with z hzu hzsub
            rw [hzsub]
            change planeTestFunctionZ u z - Sg z =
              (testFunctionPlaneL2 (planeTestFunctionZ u) : ℂ → ℂ) z - Sg z
            rw [hzu]
          _ =ᵐ[volume]
              (beurlingTransformL2 (testFunctionPlaneL2 e) : PlaneL2) := by
            rw [hdiffLp]
      have huDZ (z : ℂ) (hzC : z ∈ C) :
          planeTestFunctionZ u z = f0 z := by
        have hzn : ‖z‖ ≤ (n : ℝ) := by
          simpa [C, Metric.mem_closedBall, dist_zero_right] using hzC
        have hzR : ‖z‖ < R := hzn.trans_lt hnR
        change frechetDZValue (u : ℂ → ℂ) z = f0 z
        rw [show u = cutoffCauchyTransform (cauchyDiskCutoff R hR) g by rfl,
          frechetDZValue_cutoffCauchyTransform,
          frechetDZValue_cauchyDiskCutoff_eq_zero_of_norm_lt hR hzR,
          cauchyDiskCutoff_eq_one_of_norm_le hR hzR.le]
        simp [f0]
      have haeLocal : d =ᵐ[volume.restrict C]
          (beurlingTransformL2 (testFunctionPlaneL2 e) : ℂ → ℂ) := by
        filter_upwards [ae_restrict_mem measurableSet_closedBall,
          ae_restrict_of_ae haeGlobal] with z hzC hz
        simpa [d, huDZ z hzC] using hz
      have hdLpEq : dLp =
          ((Lp.memLp (beurlingTransformL2 (testFunctionPlaneL2 e))).restrict C).toLp
            (beurlingTransformL2 (testFunctionPlaneL2 e) : ℂ → ℂ) := by
        apply Lp.ext
        filter_upwards [hdmem.coeFn_toLp,
          ((Lp.memLp (beurlingTransformL2
            (testFunctionPlaneL2 e))).restrict C).coeFn_toLp,
          haeLocal] with z hzd hze hz
        rw [hzd, hze, hz]
      rw [hdLpEq]
      calc
        ‖((Lp.memLp (beurlingTransformL2 (testFunctionPlaneL2 e))).restrict C).toLp
            (beurlingTransformL2 (testFunctionPlaneL2 e) : ℂ → ℂ)‖
            ≤ ‖beurlingTransformL2 (testFunctionPlaneL2 e)‖ :=
          norm_Lp_toLp_restrict_le C _
        _ = ‖testFunctionPlaneL2 e‖ :=
          norm_beurlingTransformL2_apply _
        _ ≤ (B : ℝ) / R := hB R hR h2rR
    have hnormzero : ‖dLp‖ = 0 := by
      apply le_antisymm
      · by_contra hnot
        have hdpos : 0 < ‖dLp‖ := lt_of_not_ge hnot
        have hquot_nonneg : 0 ≤ (B : ℝ) / ‖dLp‖ := by positivity
        let R : ℝ := 2 * r + (n : ℝ) + (B : ℝ) / ‖dLp‖ + 1
        have hR0 : 0 < R := by
          dsimp [R]
          positivity
        have h2rR : 2 * r ≤ R := by
          dsimp [R]
          have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have hnR : (n : ℝ) < R := by
          dsimp [R]
          linarith
        have hquotR : (B : ℝ) / ‖dLp‖ < R := by
          dsimp [R]
          linarith
        have hBR : (B : ℝ) / R < ‖dLp‖ := by
          apply (div_lt_iff₀ hR0).2
          have := (div_lt_iff₀ hdpos).1 hquotR
          simpa [mul_comm] using this
        exact (not_lt_of_ge (hlocal_bound R hR0 h2rR hnR)) hBR
      · exact norm_nonneg _
    have hdLpZero : dLp = 0 := norm_eq_zero.mp hnormzero
    have hdzero : d =ᵐ[volume.restrict C] fun _ : ℂ ↦ 0 := by
      have hcoe := hdmem.coeFn_toLp
      have hdLpZero' : hdmem.toLp d = 0 := by
        simpa [dLp] using hdLpZero
      rw [hdLpZero'] at hcoe
      filter_upwards [hcoe.symm,
        Lp.coeFn_zero ℂ 2 (volume.restrict C)] with z hz hz0
      exact hz.trans hz0
    filter_upwards [hdzero] with z hz
    change f0 z - Sg z = 0 at hz
    exact sub_eq_zero.mp hz
  have hglobal : f0 =ᵐ[volume.restrict
      (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)] (Sg : ℂ → ℂ) :=
    (ae_eq_restrict_iUnion_iff
      (fun n : ℕ ↦ Metric.closedBall (0 : ℂ) n) f0 (Sg : ℂ → ℂ)).2 hpiece
  have hglobal' : f0 =ᵐ[volume] (Sg : ℂ → ℂ) := by
    simpa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using hglobal
  filter_upwards [hglobal'] with z hz
  rw [frechetDZValue_cauchyTransform_eq]
  simpa [f0, Sg] using hz

/--
%%handwave
name:
  Distributional Cauchy--Beurling identities on test functions
statement:
  For every $g\in C_c^\infty(\mathbb C)$, the Cauchy transform
  $\mathcal Cg$ belongs to $W^{1,2}_{\mathrm{loc}}(\mathbb C)$ and has weak
  Wirtinger derivatives
  $$
    \partial_{\bar z}\mathcal Cg=g,
    \qquad
    \partial_z\mathcal Cg=\mathcal Sg
  $$
  almost everywhere.
proof:
  The Cauchy transform is continuously differentiable and its
  $\partial_{\bar z}$ derivative is $g$ pointwise. Its
  [$\partial_z$ derivative equals the $L^2$ Beurling transform almost everywhere](lean:JJMath.Quasiconformal.frechetDZValue_cauchyTransform_ae). These two components identify the classical differential with the displayed candidate almost everywhere. Classical integration by parts gives the weak derivative identity, while the global $L^2$ bounds on $g$ and $\mathcal Sg$ give compact-local square-integrability.
-/
theorem cauchyTransform_isLocalW12On (g : PlaneTestFunction) :
    IsLocalW12On Set.univ (cauchyTransform g)
      (cauchyTransformWeakDifferential g) := by
  have hderiv_ae : cauchyTransformWeakDifferential g =ᵐ[volume]
      fun z ↦ fderiv ℝ (cauchyTransform g) z := by
    filter_upwards [frechetDZValue_cauchyTransform_ae g] with z hz
    apply ext_weakDZ_weakDBar
    · change weakDZField (cauchyTransformWeakDifferential g) z =
        frechetDZValue (cauchyTransform g) z
      rw [weakDZField_cauchyTransformWeakDifferential]
      exact hz.symm
    · change weakDBarField (cauchyTransformWeakDifferential g) z =
        frechetDBarValue (cauchyTransform g) z
      rw [weakDBarField_cauchyTransformWeakDifferential]
      exact (frechetDBarValue_cauchyTransform g z).symm
  have hweak0 := weakDerivativeOn_of_contDiff
    (Ω := Set.univ) (contDiff_one_cauchyTransform g)
  have hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Set.univ (cauchyTransform g) (cauchyTransformWeakDifferential g) := by
    intro φ v
    rcases hweak0 φ v with ⟨hleft, hright, heq⟩
    have hright_ae :
        (fun z ↦ φ z • fderiv ℝ (cauchyTransform g) z v)
          =ᵐ[volume.restrict Set.univ]
            fun z ↦ φ z • cauchyTransformWeakDifferential g z v := by
      have hderiv_ae' : cauchyTransformWeakDifferential g
          =ᵐ[volume.restrict Set.univ]
            fun z ↦ fderiv ℝ (cauchyTransform g) z := by
        simpa only [Measure.restrict_univ] using hderiv_ae
      filter_upwards [hderiv_ae'] with z hz
      rw [hz]
    refine ⟨hleft, hright.congr hright_ae, ?_⟩
    simpa only [Measure.restrict_univ] using
      heq.trans (congrArg Neg.neg (integral_congr_ae hright_ae))
  refine ⟨isOpen_univ, hweak, ?_⟩
  intro K hK _hKuniv
  refine ⟨memLp_restrict_of_isCompact_of_continuousOn hK
      (contDiff_one_cauchyTransform g).continuous.continuousOn, ?_⟩
  let Lz : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    { toFun := fun a ↦ a • ContinuousLinearMap.id ℝ ℂ
      map_add' := by
        intro a b
        ext v
        simp
        ring
      map_smul' := by
        intros r a
        ext v
        simp [Complex.real_smul]
        ring
      cont := by fun_prop }
  let Lbar : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    { toFun := fun a ↦ a • Complex.conjCLE
      map_add' := by
        intro a b
        ext v
        simp
        ring
      map_smul' := by
        intros r a
        ext v
        simp [Complex.real_smul]
        ring
      cont := by fun_prop }
  have hS : MemLp
      (beurlingTransformL2 (testFunctionPlaneL2 g) : ℂ → ℂ)
      2 (volume : Measure ℂ) := Lp.memLp _
  have hg : MemLp (g : ℂ → ℂ) 2 (volume : Measure ℂ) :=
    g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hsum : MemLp
      (fun z ↦ Lz ((beurlingTransformL2 (testFunctionPlaneL2 g)) z) +
        Lbar (g z)) 2 (volume : Measure ℂ) :=
    (Lz.comp_memLp' hS).add (Lbar.comp_memLp' hg)
  have hcand : MemLp (cauchyTransformWeakDifferential g) 2
      (volume : Measure ℂ) := by
    simpa [cauchyTransformWeakDifferential, realLinearMapOfWirtinger,
      Lz, Lbar, Function.comp_def] using hsum
  exact hcand.restrict K

end

end Quasiconformal

end JJMath
