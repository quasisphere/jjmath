import JJMath.Hyperbolic.Schwarzian.Wirtinger
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The distributional Cauchy kernel

This file develops the regularization used to prove that the normalized
kernel $1/(\pi z)$ is a fundamental solution of $\partial_{\bar z}$. The first layer
is pointwise: a smooth regularized reciprocal has an explicit nonnegative
$\partial_{\bar z}$ derivative. The second layer identifies this derivative, after
normalization and rescaling, as an approximate identity on the plane.
-/

namespace JJMath

open Set Filter MeasureTheory
open MeasureTheory.Measure
open Module Bornology
open scoped Distributions

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Planar test functions
statement:
  A planar test function is a smooth compactly supported map
  $\varphi:\mathbb C\to\mathbb C$.
-/
abbrev PlaneTestFunction :=
  𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)

/--
%%handwave
name:
  Local integrability of the reciprocal kernel
statement:
  The function $z\mapsto z^{-1}$ is locally integrable on $\mathbb C$ with
  respect to planar Lebesgue measure.
proof:
  Its norm is $|z|^{-1}$. In real dimension two this radial singularity has
  exponent $1<2$, hence is locally integrable.
-/
theorem locallyIntegrable_inv_complex :
    LocallyIntegrable (fun z : ℂ ↦ z⁻¹) (volume : Measure ℂ) := by
  exact locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ)
    (μ := (volume : Measure ℂ)) (C := 1) (α := 1)
    (by simp) (by simp)
    (by
      filter_upwards with z
      rw [Real.rpow_neg_one]
      simp [norm_inv])
    measurable_inv.aestronglyMeasurable

/--
%%handwave
name:
  Test-function $\bar z$-Wirtinger derivative
statement:
  For $\varphi\in C_c^\infty(\mathbb C)$, define
  $$
    \partial_{\bar z}\varphi
      =\frac12(\partial_1\varphi+i\partial_i\varphi),
  $$
  again as a smooth compactly supported function.
-/
def planeTestFunctionDBar (φ : PlaneTestFunction) : PlaneTestFunction :=
  (1 / 2 : ℂ) •
    (TestFunction.lineDerivCLM ℂ (1 : ℂ) φ +
      Complex.I • TestFunction.lineDerivCLM ℂ Complex.I φ)

/--
%%handwave
name:
  Test-function $z$-Wirtinger derivative
statement:
  For $\varphi\in C_c^\infty(\mathbb C)$, define
  $$
    \partial_z\varphi
      =\frac12(\partial_1\varphi-i\partial_i\varphi),
  $$
  again as a smooth compactly supported function.
-/
def planeTestFunctionZ (φ : PlaneTestFunction) : PlaneTestFunction :=
  (1 / 2 : ℂ) •
    (TestFunction.lineDerivCLM ℂ (1 : ℂ) φ -
      Complex.I • TestFunction.lineDerivCLM ℂ Complex.I φ)

/--
%%handwave
name:
  Pointwise formula for the test-function Wirtinger derivative
statement:
  For every $\varphi\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$, the
  bundled test function $\partial_{\bar z}\varphi$ has value
  $$
    \frac12\bigl(D\varphi(z)(1)+iD\varphi(z)(i)\bigr).
  $$
proof:
  Evaluate the two bundled directional derivatives and use the definition of
  $\partial_{\bar z}$.
-/
@[simp]
theorem planeTestFunctionDBar_apply (φ : PlaneTestFunction) (z : ℂ) :
    planeTestFunctionDBar φ z = frechetDBarValue φ z := by
  have hdiff : DifferentiableAt ℝ (φ : ℂ → ℂ) z :=
    (φ.contDiff.differentiable (by simp)) z
  rw [frechetDBarValue]
  change (1 / 2 : ℂ) *
      (((TestFunction.lineDerivCLM ℂ (1 : ℂ) φ) z) +
        Complex.I * (TestFunction.lineDerivCLM ℂ Complex.I φ) z) =
    (1 / 2 : ℂ) *
      (fderiv ℝ (φ : ℂ → ℂ) z 1 +
        Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I)
  rw [show (TestFunction.lineDerivCLM ℂ (1 : ℂ) φ) z =
      fderiv ℝ (φ : ℂ → ℂ) z 1 by
    rw [TestFunction.lineDerivCLM_apply]
    exact hdiff.lineDeriv_eq_fderiv,
    show (TestFunction.lineDerivCLM ℂ Complex.I φ) z =
      fderiv ℝ (φ : ℂ → ℂ) z Complex.I by
    rw [TestFunction.lineDerivCLM_apply]
    exact hdiff.lineDeriv_eq_fderiv]

/--
%%handwave
name:
  Pointwise formula for the test-function holomorphic Wirtinger derivative
statement:
  For every $\varphi\in C_c^\infty(\mathbb C)$ and $z\in\mathbb C$, the
  bundled test function $\partial_z\varphi$ has value
  $$
    \frac12\bigl(D\varphi(z)(1)-iD\varphi(z)(i)\bigr).
  $$
proof:
  Evaluate the two bundled directional derivatives and use the definition of
  $\partial_z$.
-/
@[simp]
theorem planeTestFunctionZ_apply (φ : PlaneTestFunction) (z : ℂ) :
    planeTestFunctionZ φ z = frechetDZValue φ z := by
  have hdiff : DifferentiableAt ℝ (φ : ℂ → ℂ) z :=
    (φ.contDiff.differentiable (by simp)) z
  rw [frechetDZValue]
  change (1 / 2 : ℂ) *
      (((TestFunction.lineDerivCLM ℂ (1 : ℂ) φ) z) -
        Complex.I * (TestFunction.lineDerivCLM ℂ Complex.I φ) z) =
    (1 / 2 : ℂ) *
      (fderiv ℝ (φ : ℂ → ℂ) z 1 -
        Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I)
  rw [show (TestFunction.lineDerivCLM ℂ (1 : ℂ) φ) z =
      fderiv ℝ (φ : ℂ → ℂ) z 1 by
    rw [TestFunction.lineDerivCLM_apply]
    exact hdiff.lineDeriv_eq_fderiv,
    show (TestFunction.lineDerivCLM ℂ Complex.I φ) z =
      fderiv ℝ (φ : ℂ → ℂ) z Complex.I by
    rw [TestFunction.lineDerivCLM_apply]
    exact hdiff.lineDeriv_eq_fderiv]

/--
%%handwave
name:
  Integrability of the reciprocal kernel against a test-function derivative
statement:
  If $\varphi\in C_c^\infty(\mathbb C)$, then
  $$
    z\longmapsto z^{-1}\partial_{\bar z}\varphi(z)
  $$
  is integrable over $\mathbb C$.
proof:
  The reciprocal kernel is locally integrable, while
  $\partial_{\bar z}\varphi$ is a smooth compactly supported test function.
-/
theorem integrable_inv_mul_frechetDBarValue (φ : PlaneTestFunction) :
    Integrable (fun z : ℂ ↦ z⁻¹ * frechetDBarValue φ z)
      (volume : Measure ℂ) := by
  have h := (planeTestFunctionDBar φ).integrable_bilin
    (ContinuousLinearMap.mul ℂ ℂ)
    (locallyIntegrableOn_univ.mpr locallyIntegrable_inv_complex)
  simpa [mul_comm] using h

/--
%%handwave
name:
  Regularized Cauchy kernel
statement:
  For $\varepsilon\in\mathbb R$, the regularized reciprocal kernel is
  $$
    K_\varepsilon(z)=\frac{\overline z}{z\overline z+\varepsilon^2}.
  $$
-/
def regularizedCauchyKernel (ε : ℝ) (z : ℂ) : ℂ :=
  starRingEnd ℂ z /
    (z * starRingEnd ℂ z + (ε ^ 2 : ℂ))

/--
%%handwave
name:
  The regularized Cauchy denominator is nonzero
statement:
  If $\varepsilon>0$, then for every $z\in\mathbb C$,
  $$
    z\bar z+\varepsilon^2\ne0.
  $$
proof:
  The denominator is the positive real number $|z|^2+\varepsilon^2$.
-/
theorem regularizedCauchyKernel_denominator_ne_zero
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    z * starRingEnd ℂ z + (ε ^ 2 : ℂ) ≠ 0 := by
  rw [Complex.mul_conj]
  norm_cast
  exact ne_of_gt <|
    add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) (sq_pos_of_pos hε)

/--
%%handwave
name:
  Smoothness of the regularized Cauchy kernel
statement:
  For every $\varepsilon>0$, the function
  $$
    z\longmapsto\frac{\bar z}{z\bar z+\varepsilon^2}
  $$
  is smooth as a map from $\mathbb R^2$ to $\mathbb R^2$.
proof:
  Conjugation and multiplication are smooth over $\mathbb R$, and the
  denominator is nowhere zero.
-/
theorem contDiff_regularizedCauchyKernel
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ⊤ (regularizedCauchyKernel ε) := by
  have hc : ContDiff ℝ ⊤ (fun z : ℂ ↦ starRingEnd ℂ z) :=
    Complex.conjCLE.contDiff
  have hq : ContDiff ℝ ⊤
      (fun z : ℂ ↦ z * starRingEnd ℂ z + (ε ^ 2 : ℂ)) := by
    fun_prop
  simpa [regularizedCauchyKernel, div_eq_mul_inv] using
    hc.mul (hq.inv (regularizedCauchyKernel_denominator_ne_zero hε))

/--
%%handwave
name:
  Wirtinger derivative of the regularized Cauchy kernel
statement:
  If $\varepsilon>0$, then for every $z\in\mathbb C$,
  $$
    \partial_{\bar z}
      \left(\frac{\bar z}{z\bar z+\varepsilon^2}\right)
      =\frac{\varepsilon^2}{(z\bar z+\varepsilon^2)^2}.
  $$
proof:
  Apply the Wirtinger quotient rule, using
  $\partial_{\bar z}z=0$ and $\partial_{\bar z}\bar z=1$, and simplify the
  numerator.
-/
theorem frechetDBarValue_regularizedCauchyKernel
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    frechetDBarValue (regularizedCauchyKernel ε) z =
      (ε ^ 2 : ℂ) /
        (z * starRingEnd ℂ z + (ε ^ 2 : ℂ)) ^ 2 := by
  let c : ℂ → ℂ := fun w ↦ starRingEnd ℂ w
  let q : ℂ → ℂ := fun w ↦ w * starRingEnd ℂ w + (ε ^ 2 : ℂ)
  have hc : DifferentiableAt ℝ c z := by
    simpa [c] using Complex.conjCLE.differentiable.differentiableAt
  have hq : DifferentiableAt ℝ q z := by
    exact (differentiableAt_id.mul hc).add (differentiableAt_const _)
  have hqne : q z ≠ 0 := by
    simpa [q] using regularizedCauchyKernel_denominator_ne_zero hε z
  rw [show regularizedCauchyKernel ε = fun w ↦ c w / q w by rfl]
  rw [frechetDBarValue_div_of_differentiableAt hc hq hqne]
  have hcbar : frechetDBarValue c z = 1 := by
    dsimp [c]
    rw [frechetDBarValue]
    have hfd : fderiv ℝ (fun w : ℂ ↦ starRingEnd ℂ w) z =
        Complex.conjCLE := Complex.conjCLE.fderiv
    rw [hfd]
    norm_num [Complex.conjCLE_apply, div_eq_mul_inv]
  have hidbar : frechetDBarValue (fun w : ℂ ↦ w) z = 0 := by
    simp [frechetDBarValue]
  have hqbar : frechetDBarValue q z = z := by
    have hconjbar :
        frechetDBarValue (fun w : ℂ ↦ starRingEnd ℂ w) z = 1 := by
      simpa [c] using hcbar
    have hconstbar :
        frechetDBarValue (fun _ : ℂ ↦ (ε ^ 2 : ℂ)) z = 0 := by
      simp [frechetDBarValue]
    dsimp [q]
    rw [show (fun w : ℂ ↦ w * starRingEnd ℂ w + (ε ^ 2 : ℂ)) =
        fun w ↦ (fun x : ℂ ↦ x * starRingEnd ℂ x) w +
          (fun _ : ℂ ↦ (ε ^ 2 : ℂ)) w by rfl]
    rw [frechetDBarValue_add_of_differentiableAt]
    · rw [frechetDBarValue_mul_of_differentiableAt]
      · rw [hidbar, hconjbar, hconstbar]
        simp
      · exact differentiableAt_id
      · exact hc
    · exact differentiableAt_id.mul hc
    · exact differentiableAt_const _
  rw [hcbar, hqbar]
  dsimp [c, q]
  field_simp [hqne]
  ring

/--
%%handwave
name:
  Regularized reciprocal is dominated by the reciprocal kernel
statement:
  If $\varepsilon>0$, then for every $z\in\mathbb C$,
  $$
    \left|\frac{\bar z}{|z|^2+\varepsilon^2}\right|
      \leq \frac1{|z|},
  $$
  where the right-hand side is interpreted as zero at $z=0$.
proof:
  The claim is immediate at $z=0$. Away from zero, clear the positive
  denominators and use $|z|^2\leq |z|^2+\varepsilon^2$.
-/
theorem norm_regularizedCauchyKernel_le_norm_inv
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ‖regularizedCauchyKernel ε z‖ ≤ ‖z⁻¹‖ := by
  by_cases hz : z = 0
  · simp [hz, regularizedCauchyKernel]
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hden : 0 < ‖z‖ ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  rw [regularizedCauchyKernel, norm_div, norm_inv, Complex.norm_conj]
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, Real.norm_eq_abs, abs_of_pos hden]
  rw [inv_eq_one_div]
  exact (div_le_div_iff₀ hden hnz).2 (by nlinarith [sq_nonneg ε])

/--
%%handwave
name:
  Regularized reciprocals converge to the reciprocal kernel
statement:
  For every $z\in\mathbb C$,
  $$
    \frac{\bar z}{|z|^2+c^{-2}}\longrightarrow z^{-1}
    \qquad\text{as }c\to+\infty.
  $$
  Both sides use the value zero at $z=0$.
proof:
  Since $c^{-1}\to0$, the denominator tends to $z\bar z$. At nonzero
  $z$ this limit is nonzero, so continuity of division applies and
  $\bar z/(z\bar z)=z^{-1}$. The case $z=0$ is immediate.
-/
theorem tendsto_regularizedCauchyKernel_inv_atTop (z : ℂ) :
    Tendsto (fun c : ℝ ↦ regularizedCauchyKernel c⁻¹ z)
      atTop (nhds z⁻¹) := by
  by_cases hz : z = 0
  · simp [hz, regularizedCauchyKernel]
  have heps : Tendsto (fun c : ℝ ↦ c⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hepsc : Tendsto (fun c : ℝ ↦ ((c⁻¹ : ℝ) : ℂ))
      atTop (nhds 0) := by
    simpa only [Complex.ofReal_zero] using heps.ofReal
  have heps2c : Tendsto (fun c : ℝ ↦ ((c⁻¹ : ℝ) : ℂ) ^ 2)
      atTop (nhds 0) := by
    simpa using hepsc.pow 2
  have hden : Tendsto
      (fun c : ℝ ↦ z * starRingEnd ℂ z +
        ((c⁻¹ : ℝ) : ℂ) ^ 2)
      atTop (nhds (z * starRingEnd ℂ z)) := by
    simpa only [add_zero] using tendsto_const_nhds.add heps2c
  have hdenne : z * starRingEnd ℂ z ≠ 0 := by simp [hz]
  have hnum : Tendsto (fun _ : ℝ ↦ starRingEnd ℂ z) atTop
      (nhds (starRingEnd ℂ z)) := tendsto_const_nhds
  have hquot : Tendsto
      (fun c : ℝ ↦ starRingEnd ℂ z /
        (z * starRingEnd ℂ z + ((c⁻¹ : ℝ) : ℂ) ^ 2))
      atTop
      (nhds (starRingEnd ℂ z / (z * starRingEnd ℂ z))) :=
    hnum.div hden hdenne
  rw [show z⁻¹ = starRingEnd ℂ z / (z * starRingEnd ℂ z) by
    field_simp [hz]]
  simpa only [regularizedCauchyKernel] using hquot

/--
%%handwave
name:
  Regularized Cauchy integrals converge to the singular integral
statement:
  For every $\varphi\in C_c^\infty(\mathbb C)$,
  $$
    \int_{\mathbb C}
      \frac{\bar z}{|z|^2+c^{-2}}\,
      \partial_{\bar z}\varphi(z)\,dz
      \longrightarrow
    \int_{\mathbb C}z^{-1}\partial_{\bar z}\varphi(z)\,dz
  $$
  as $c\to+\infty$.
proof:
  The regularized kernels converge pointwise to $z^{-1}$ and, for positive
  $c$, their norms are bounded by $|z^{-1}|$. The resulting dominating
  function $|z^{-1}\partial_{\bar z}\varphi(z)|$ is integrable, so dominated
  convergence applies.
-/
theorem tendsto_integral_regularizedCauchyKernel_inv_mul_frechetDBarValue
    (φ : PlaneTestFunction) :
    Tendsto
      (fun c : ℝ ↦ ∫ z : ℂ,
        regularizedCauchyKernel c⁻¹ z * frechetDBarValue φ z ∂volume)
      atTop
      (nhds (∫ z : ℂ, z⁻¹ * frechetDBarValue φ z ∂volume)) := by
  apply tendsto_integral_filter_of_dominated_convergence
      (fun z : ℂ ↦ ‖z⁻¹ * frechetDBarValue φ z‖)
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact ((contDiff_regularizedCauchyKernel (inv_pos.mpr hc)).continuous.mul
      (planeTestFunctionDBar φ).continuous).aestronglyMeasurable
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    filter_upwards with z
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_regularizedCauchyKernel_le_norm_inv (inv_pos.mpr hc) z)
      (norm_nonneg _)
  · exact (integrable_inv_mul_frechetDBarValue φ).norm
  · filter_upwards with z
    exact (tendsto_regularizedCauchyKernel_inv_atTop z).mul_const _

/--
%%handwave
name:
  Integration by parts for the regularized Cauchy kernel
statement:
  If $\varepsilon>0$ and $\varphi\in C_c^\infty(\mathbb C)$, then
  $$
    \int_{\mathbb C}K_\varepsilon(z)\,
      \partial_{\bar z}\varphi(z)\,dz
      =-
      \int_{\mathbb C}\partial_{\bar z}K_\varepsilon(z)\,
        \varphi(z)\,dz,
    \qquad
    K_\varepsilon(z)=\frac{\bar z}{|z|^2+\varepsilon^2}.
  $$
proof:
  Apply real integration by parts in the coordinate directions $1$ and $i$.
  All products are integrable because the test function and its derivatives
  have compact support, while the regularized kernel and its derivative are
  smooth. Combine the two identities according to
  $\partial_{\bar z}=(\partial_x+i\partial_y)/2$.
-/
theorem integral_regularizedCauchyKernel_mul_frechetDBarValue
    {ε : ℝ} (hε : 0 < ε) (φ : PlaneTestFunction) :
    ∫ z : ℂ, regularizedCauchyKernel ε z * frechetDBarValue φ z ∂volume =
      -∫ z : ℂ,
        frechetDBarValue (regularizedCauchyKernel ε) z * φ z ∂volume := by
  let K : ℂ → ℂ := regularizedCauchyKernel ε
  have hK : ContDiff ℝ ⊤ K := contDiff_regularizedCauchyKernel hε
  have hKdiff : ∀ z, DifferentiableAt ℝ K z := fun z ↦
    (hK.differentiable (by simp)) z
  have hφdiff : ∀ z, DifferentiableAt ℝ (φ : ℂ → ℂ) z := fun z ↦
    (φ.contDiff.differentiable (by simp)) z
  have hKlocal : LocallyIntegrable K (volume : Measure ℂ) :=
    hK.continuous.locallyIntegrable
  have hDKlocal (v : ℂ) :
      LocallyIntegrable (fun z ↦ fderiv ℝ K z v)
        (volume : Measure ℂ) := by
    have hpair : Continuous
        (fun p : ℂ × ℂ ↦ (fderiv ℝ K p.1 : ℂ →L[ℝ] ℂ) p.2) :=
      hK.continuous_fderiv_apply (by simp)
    exact (hpair.comp (continuous_id.prodMk continuous_const)).locallyIntegrable
  have hip (v : ℂ) :
      ∫ z : ℂ, K z * fderiv ℝ (φ : ℂ → ℂ) z v ∂volume =
        -∫ z : ℂ, fderiv ℝ K z v * φ z ∂volume := by
    let dφ : PlaneTestFunction := TestFunction.lineDerivCLM ℂ v φ
    have hdφ_apply (z : ℂ) : dφ z = fderiv ℝ (φ : ℂ → ℂ) z v := by
      rw [show dφ z = lineDeriv ℝ (φ : ℂ → ℂ) z v by
        simp [dφ, TestFunction.lineDerivCLM_apply]]
      exact (hφdiff z).lineDeriv_eq_fderiv
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · simpa [mul_comm] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
          (locallyIntegrableOn_univ.mpr (hDKlocal v))
    · simpa [hdφ_apply, mul_comm] using
        dφ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
          (locallyIntegrableOn_univ.mpr hKlocal)
    · simpa [mul_comm] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
          (locallyIntegrableOn_univ.mpr hKlocal)
    · exact fun z _hz ↦ hKdiff z
    · exact fun z _hz ↦ hφdiff z
  have h1 := hip (1 : ℂ)
  have hI := hip Complex.I
  have hleft (v : ℂ) :
      Integrable (fun z : ℂ ↦ K z * fderiv ℝ (φ : ℂ → ℂ) z v)
        (volume : Measure ℂ) := by
    let dφ : PlaneTestFunction := TestFunction.lineDerivCLM ℂ v φ
    have hdφ_apply (z : ℂ) : dφ z = fderiv ℝ (φ : ℂ → ℂ) z v := by
      rw [show dφ z = lineDeriv ℝ (φ : ℂ → ℂ) z v by
        simp [dφ, TestFunction.lineDerivCLM_apply]]
      exact (hφdiff z).lineDeriv_eq_fderiv
    simpa [hdφ_apply, mul_comm] using
      dφ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
        (locallyIntegrableOn_univ.mpr hKlocal)
  have hright (v : ℂ) :
      Integrable (fun z : ℂ ↦ fderiv ℝ K z v * φ z)
        (volume : Measure ℂ) := by
    simpa [mul_comm] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
        (locallyIntegrableOn_univ.mpr (hDKlocal v))
  have hL :
      (∫ z : ℂ, K z * frechetDBarValue φ z ∂volume) =
        (1 / 2 : ℂ) * (∫ z : ℂ,
          K z * fderiv ℝ (φ : ℂ → ℂ) z 1 ∂volume) +
          ((1 / 2 : ℂ) * Complex.I) *
            ∫ z : ℂ,
              K z * fderiv ℝ (φ : ℂ → ℂ) z Complex.I ∂volume := by
    have heq : (fun z : ℂ ↦ K z * frechetDBarValue φ z) =
        fun z ↦ (1 / 2 : ℂ) * (K z * fderiv ℝ (φ : ℂ → ℂ) z 1) +
          ((1 / 2 : ℂ) * Complex.I) *
            (K z * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) := by
      funext z
      simp only [frechetDBarValue]
      ring
    rw [heq, integral_add ((hleft 1).const_mul _)
      ((hleft Complex.I).const_mul _), integral_const_mul, integral_const_mul]
  have hR :
      (∫ z : ℂ, frechetDBarValue K z * φ z ∂volume) =
        (1 / 2 : ℂ) * (∫ z : ℂ, fderiv ℝ K z 1 * φ z ∂volume) +
          ((1 / 2 : ℂ) * Complex.I) *
            ∫ z : ℂ, fderiv ℝ K z Complex.I * φ z ∂volume := by
    have heq : (fun z : ℂ ↦ frechetDBarValue K z * φ z) =
        fun z ↦ (1 / 2 : ℂ) * (fderiv ℝ K z 1 * φ z) +
          ((1 / 2 : ℂ) * Complex.I) *
            (fderiv ℝ K z Complex.I * φ z) := by
      funext z
      simp only [frechetDBarValue]
      ring
    rw [heq, integral_add ((hright 1).const_mul _)
      ((hright Complex.I).const_mul _), integral_const_mul, integral_const_mul]
  change (∫ z : ℂ, K z * frechetDBarValue φ z ∂volume) =
    -∫ z : ℂ, frechetDBarValue K z * φ z ∂volume
  rw [hL, hR, h1, hI]
  ring

/--
%%handwave
name:
  Cauchy approximate-identity profile
statement:
  The normalized radial profile associated with the regularized Cauchy
  kernel is
  $$
    \rho(z)=\frac{1}{\pi(1+|z|^2)^2}.
  $$
-/
def cauchyApproximateIdentityProfile (z : ℂ) : ℝ :=
  (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)⁻¹

/--
%%handwave
name:
  Positivity of the Cauchy approximate-identity profile
statement:
  For every $z\in\mathbb C$,
  $$
    0\leq \frac{1}{\pi(1+|z|^2)^2}.
  $$
proof:
  Both $\pi$ and $1+|z|^2$ are positive.
-/
theorem cauchyApproximateIdentityProfile_nonneg (z : ℂ) :
    0 ≤ cauchyApproximateIdentityProfile z := by
  unfold cauchyApproximateIdentityProfile
  positivity

/--
%%handwave
name:
  Radial mass of the Cauchy approximate identity
statement:
  The radial factor in the polar-coordinate integral of the normalized
  Cauchy profile satisfies
  $$
    \int_0^\infty
      \frac{r}{\pi(1+r^2)^2}\,dr=\frac{1}{2\pi}.
  $$
proof:
  Use the antiderivative
  $-1/(2\pi(1+r^2))$, whose value tends to zero at infinity.
-/
theorem integral_Ioi_cauchyApproximateIdentityProfile_radial :
    ∫ r in Set.Ioi (0 : ℝ),
        r / (Real.pi * (1 + r ^ 2) ^ 2) =
      1 / (2 * Real.pi) := by
  let G : ℝ → ℝ := fun r ↦ -1 / (2 * Real.pi * (1 + r ^ 2))
  let G' : ℝ → ℝ := fun r ↦ r / (Real.pi * (1 + r ^ 2) ^ 2)
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ), HasDerivAt G (G' r) r := by
    intro r _hr
    have hbase : HasDerivAt (fun x : ℝ ↦ 1 + x ^ 2) (2 * r) r := by
      convert (hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hinv : HasDerivAt (fun x : ℝ ↦ (1 + x ^ 2)⁻¹)
        (-(2 * r) / (1 + r ^ 2) ^ 2) r := by
      simpa only [neg_div] using hbase.inv (by positivity)
    have hmul := hinv.const_mul (-1 / (2 * Real.pi))
    convert hmul using 1
    · dsimp [G]
      field_simp [Real.pi_ne_zero]
    · dsimp [G']
      field_simp [Real.pi_ne_zero]
  have hnonneg : ∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ G' r := by
    intro r hr
    dsimp [G']
    exact div_nonneg hr.le (mul_nonneg Real.pi_pos.le (sq_nonneg _))
  have hden : Tendsto (fun r : ℝ ↦ 2 * Real.pi * (1 + r ^ 2))
      atTop atTop := by
    have hsquare : Tendsto (fun r : ℝ ↦ r ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    have hone : Tendsto (fun r : ℝ ↦ 1 + r ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 hsquare
    exact (tendsto_const_mul_atTop_of_pos (by positivity)).2 hone
  have hG : Tendsto G atTop (nhds 0) := by
    simpa [G] using (tendsto_const_nhds.div_atTop hden)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    hderiv hnonneg hG
  rw [show 1 / (2 * Real.pi) = -(-1 / (2 * Real.pi)) by ring]
  simpa [G, G'] using h

/--
%%handwave
name:
  Unit mass of the Cauchy approximate-identity profile
statement:
  The radial profile
  $$
    \rho(z)=\frac{1}{\pi(1+|z|^2)^2}
  $$
  has total planar mass one:
  $$
    \int_{\mathbb C}\rho(z)\,dz=1.
  $$
proof:
  Pass to polar coordinates. The angular integral is $2\pi$, and the radial
  integral is [equal to $1/(2\pi)$](lean:JJMath.Quasiconformal.integral_Ioi_cauchyApproximateIdentityProfile_radial).
-/
theorem integral_cauchyApproximateIdentityProfile :
    ∫ z : ℂ, cauchyApproximateIdentityProfile z = 1 := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  simp_rw [cauchyApproximateIdentityProfile,
    Complex.norm_polarCoord_symm, smul_eq_mul]
  calc
    ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * (Real.pi * (1 + |p.1| ^ 2) ^ 2)⁻¹ =
      (∫ r in Set.Ioi (0 : ℝ),
          r / (Real.pi * (1 + r ^ 2) ^ 2)) *
        ∫ _θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← MeasureTheory.setIntegral_prod_mul, volume_eq_prod]
      apply setIntegral_congr_fun
        (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      change p.1 * (Real.pi * (1 + |p.1| ^ 2) ^ 2)⁻¹ =
        p.1 / (Real.pi * (1 + p.1 ^ 2) ^ 2) * 1
      rw [abs_of_pos hp0]
      simp [div_eq_mul_inv]
    _ = 1 := by
      rw [integral_Ioi_cauchyApproximateIdentityProfile_radial]
      have hangle :
          (∫ _θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
            2 * Real.pi := by
        rw [integral_const, measureReal_restrict_apply MeasurableSet.univ,
          Set.univ_inter,
          Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
        simp [sub_neg_eq_add, two_mul]
      rw [hangle]
      field_simp [Real.pi_ne_zero]

/--
%%handwave
name:
  Quadratic decay of the Cauchy approximate-identity profile
statement:
  As $|z|\to\infty$ in the plane,
  $$
    |z|^2\rho(z)
      =\frac{|z|^2}{\pi(1+|z|^2)^2}longrightarrow0.
  $$
proof:
  For $r>1$ the displayed quantity is nonnegative and bounded above by
  $1/(\pi r^2)$, which tends to zero. Compose this one-dimensional estimate
  with $z\mapsto|z|$.
-/
theorem tendsto_norm_pow_finrank_mul_cauchyApproximateIdentityProfile :
    Tendsto
      (fun z : ℂ ↦ ‖z‖ ^ finrank ℝ ℂ *
        cauchyApproximateIdentityProfile z)
      (cobounded ℂ) (nhds 0) := by
  have hreal : Tendsto
      (fun r : ℝ ↦ r ^ 2 * (Real.pi * (1 + r ^ 2) ^ 2)⁻¹)
      atTop (nhds 0) := by
    have hsquare : Tendsto (fun r : ℝ ↦ r ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    have hden : Tendsto (fun r : ℝ ↦ Real.pi * r ^ 2) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos Real.pi_pos).2 hsquare
    have hupper : Tendsto (fun r : ℝ ↦ 1 / (Real.pi * r ^ 2))
        atTop (nhds 0) := by
      exact Tendsto.div_atTop (a := (1 : ℝ)) tendsto_const_nhds hden
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper ?_ ?_
    · exact Filter.Eventually.of_forall fun r ↦ by positivity
    · filter_upwards [Ioi_mem_atTop (1 : ℝ)] with r hr
      have hr0 : 0 < r := zero_lt_one.trans hr
      rw [div_eq_mul_inv]
      apply (le_div_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos hr0))).2
      field_simp [Real.pi_ne_zero, hr0.ne']
      nlinarith [sq_nonneg (r ^ 2)]
  have h := hreal.comp (tendsto_norm_cobounded_atTop (E := ℂ))
  simpa [cauchyApproximateIdentityProfile] using h

/--
%%handwave
name:
  Cauchy profiles form an approximate identity
statement:
  Let $g:\mathbb C\to E$ be integrable and continuous at $0$. Then, as
  $c\to+\infty$,
  $$
    \int_{\mathbb C}c^2\rho(cz)g(z)\,dz\longrightarrow g(0),
    \qquad
    \rho(z)=\frac{1}{\pi(1+|z|^2)^2}.
  $$
proof:
  The profile is nonnegative, has total mass one, and satisfies
  $|z|^2\rho(z)\to0$ at infinity. Apply the finite-dimensional
  approximate-identity theorem.
-/
theorem tendsto_integral_cauchyApproximateIdentityProfile_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℂ → E} (hg : Integrable g (volume : Measure ℂ))
    (h'g : ContinuousAt g 0) :
    Tendsto
      (fun c : ℝ ↦ ∫ z : ℂ,
        (c ^ 2 * cauchyApproximateIdentityProfile (c • z)) • g z ∂volume)
      atTop (nhds (g 0)) := by
  simpa using
    (tendsto_integral_comp_smul_smul_of_integrable
      cauchyApproximateIdentityProfile_nonneg
      integral_cauchyApproximateIdentityProfile
      tendsto_norm_pow_finrank_mul_cauchyApproximateIdentityProfile
      hg h'g)

/--
%%handwave
name:
  Regularized Cauchy derivative as a rescaled profile
statement:
  If $c>0$, then for every $z\in\mathbb C$,
  $$
    \frac1\pi\partial_{\bar z}
      \left(\frac{\bar z}{|z|^2+c^{-2}}\right)
      =c^2\rho(cz),
    \qquad
    \rho(w)=\frac{1}{\pi(1+|w|^2)^2}.
  $$
proof:
  Substitute $\varepsilon=c^{-1}$ in the explicit Wirtinger derivative,
  use $|cz|=c|z|$, and clear the positive denominators.
-/
theorem piInv_mul_frechetDBarValue_regularizedCauchyKernel_inv
    {c : ℝ} (hc : 0 < c) (z : ℂ) :
    (Real.pi : ℂ)⁻¹ *
        frechetDBarValue (regularizedCauchyKernel c⁻¹) z =
      ((c ^ 2 * cauchyApproximateIdentityProfile (c • z) : ℝ) : ℂ) := by
  rw [frechetDBarValue_regularizedCauchyKernel (inv_pos.mpr hc)]
  rw [Complex.mul_conj]
  simp only [cauchyApproximateIdentityProfile, norm_smul,
    Real.norm_eq_abs, abs_of_pos hc, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_one]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]
  field_simp [Real.pi_ne_zero, hc.ne']
  ring

/--
%%handwave
name:
  Regularized Cauchy derivatives converge to evaluation at zero
statement:
  If $g:\mathbb C\to\mathbb C$ is integrable and continuous at $0$, then
  $$
    \lim_{c\to+\infty}
      \frac1\pi\int_{\mathbb C}
        \partial_{\bar z}
          \left(\frac{\bar z}{|z|^2+c^{-2}}\right)g(z)\,dz
      =g(0).
  $$
proof:
  For positive $c$, the normalized derivative is the rescaled profile
  $c^2\rho(cz)$. Apply the approximate-identity convergence theorem.
-/
theorem tendsto_integral_piInv_mul_frechetDBarValue_regularizedCauchyKernel_inv_mul
    (g : ℂ → ℂ) (hg : Integrable g (volume : Measure ℂ))
    (h'g : ContinuousAt g 0) :
    Tendsto
      (fun c : ℝ ↦ ∫ z : ℂ,
        ((Real.pi : ℂ)⁻¹ *
          frechetDBarValue (regularizedCauchyKernel c⁻¹) z) * g z ∂volume)
      atTop (nhds (g 0)) := by
  have hpeak :=
    tendsto_integral_cauchyApproximateIdentityProfile_smul hg h'g
  refine hpeak.congr' ?_
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  apply integral_congr_ae
  filter_upwards with z
  rw [piInv_mul_frechetDBarValue_regularizedCauchyKernel_inv hc z]
  simp

/--
%%handwave
name:
  The reciprocal kernel is a fundamental solution of the Wirtinger operator
statement:
  For every $\varphi\in C_c^\infty(\mathbb C)$,
  $$
    -\frac1\pi\int_{\mathbb C}
      z^{-1}\partial_{\bar z}\varphi(z)\,dz=\varphi(0).
  $$
  Equivalently, $\partial_{\bar z}(1/(\pi z))=\delta_0$ in the sense of
  distributions.
proof:
  Apply integration by parts to the smooth regularized reciprocal. After
  multiplication by $-1/\pi$, its differentiated side is the normalized
  approximate identity and therefore converges to $\varphi(0)$. Dominated
  convergence sends the undifferentiated side to the displayed singular
  integral. Uniqueness of limits gives the identity.
-/
theorem neg_piInv_mul_integral_inv_mul_frechetDBarValue_eq_eval_zero
    (φ : PlaneTestFunction) :
    -(Real.pi : ℂ)⁻¹ *
        (∫ z : ℂ, z⁻¹ * frechetDBarValue φ z ∂volume) =
      φ 0 := by
  have hsing :=
    tendsto_integral_regularizedCauchyKernel_inv_mul_frechetDBarValue φ
  have hscaled : Tendsto
      (fun c : ℝ ↦ -(Real.pi : ℂ)⁻¹ *
        (∫ z : ℂ,
          regularizedCauchyKernel c⁻¹ z * frechetDBarValue φ z ∂volume))
      atTop
      (nhds (-(Real.pi : ℂ)⁻¹ *
        (∫ z : ℂ, z⁻¹ * frechetDBarValue φ z ∂volume))) :=
    tendsto_const_nhds.mul hsing
  have hφint : Integrable (φ : ℂ → ℂ) (volume : Measure ℂ) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have happrox :=
    tendsto_integral_piInv_mul_frechetDBarValue_regularizedCauchyKernel_inv_mul
      (φ : ℂ → ℂ) hφint φ.continuous.continuousAt
  have heq : ∀ᶠ c : ℝ in atTop,
      -(Real.pi : ℂ)⁻¹ *
          (∫ z : ℂ,
            regularizedCauchyKernel c⁻¹ z * frechetDBarValue φ z ∂volume) =
        ∫ z : ℂ,
          ((Real.pi : ℂ)⁻¹ *
            frechetDBarValue (regularizedCauchyKernel c⁻¹) z) * φ z
            ∂volume := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    rw [integral_regularizedCauchyKernel_mul_frechetDBarValue
      (inv_pos.mpr hc) φ]
    rw [show (fun z : ℂ ↦
        ((Real.pi : ℂ)⁻¹ *
          frechetDBarValue (regularizedCauchyKernel c⁻¹) z) * φ z) =
        fun z ↦ (Real.pi : ℂ)⁻¹ *
          (frechetDBarValue (regularizedCauchyKernel c⁻¹) z * φ z) by
      funext z
      ring]
    rw [integral_const_mul]
    ring
  exact tendsto_nhds_unique (hscaled.congr' heq) happrox

end

end Quasiconformal

end JJMath
