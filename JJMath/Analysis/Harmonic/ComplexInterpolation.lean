import Mathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Complex interpolation on integrable simple functions

This file develops the analytic deformation of scalar simple functions used
in the Riesz--Thorin theorem. Keeping the construction on finite-range,
finite-measure-support functions makes the eventual three-lines pairing a
finite sum of entire functions.
-/

namespace JJMath

open Set MeasureTheory
open scoped ENNReal

namespace HarmonicAnalysis

noncomputable section

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module
  Lp.simpleFunc.normedSpace Lp.simpleFunc.isBoundedSMul

/--
%%handwave
name:
  Complex interpolation exponent
statement:
  For real exponents $r,p_0,p_1$ and $z\in\mathbb C$, define
  $$
    a(z)=\frac r{p_0}(1-z)+\frac r{p_1}z.
  $$
-/
def complexInterpolationExponent (r p₀ p₁ : ℝ) (z : ℂ) : ℂ :=
  ((r / p₀ : ℝ) : ℂ) * (1 - z) + ((r / p₁ : ℝ) : ℂ) * z

/--
%%handwave
name:
  Holomorphy of the complex interpolation exponent
statement:
  The affine function
  $a(z)=\frac r{p_0}(1-z)+\frac r{p_1}z$ is entire.
proof:
  It is a complex-affine combination of the identity function and constants.
-/
theorem differentiable_complexInterpolationExponent (r p₀ p₁ : ℝ) :
    Differentiable ℂ (complexInterpolationExponent r p₀ p₁) := by
  unfold complexInterpolationExponent
  fun_prop

/--
%%handwave
name:
  Real part of the complex interpolation exponent
statement:
  For every $z\in\mathbb C$,
  $$
    \operatorname{Re}a(z)
      =\frac r{p_0}(1-\operatorname{Re}z)
        +\frac r{p_1}\operatorname{Re}z.
  $$
proof:
  Take real parts in the defining complex-affine formula.
-/
theorem complexInterpolationExponent_re (r p₀ p₁ : ℝ) (z : ℂ) :
    (complexInterpolationExponent r p₀ p₁ z).re =
      (r / p₀) * (1 - z.re) + (r / p₁) * z.re := by
  simp [complexInterpolationExponent]

/--
%%handwave
name:
  Complex interpolation of one scalar value
statement:
  For $w\in\mathbb C$, define
  $$
    w_z=
    \begin{cases}
      0,&w=0,\\
      \dfrac{w}{|w|}|w|^{a(z)},&w\ne0,
    \end{cases}
  $$
  where $a(z)=\frac r{p_0}(1-z)+\frac r{p_1}z$.
-/
def complexInterpolationValue
    (r p₀ p₁ : ℝ) (z w : ℂ) : ℂ :=
  if w = 0 then 0
  else (w / (‖w‖ : ℂ)) * (‖w‖ : ℂ) ^ complexInterpolationExponent r p₀ p₁ z

/--
%%handwave
name:
  Complex interpolation preserves zero
statement:
  For every $z\in\mathbb C$,
  $$0_z=0.$$
proof:
  This is the zero branch in the definition.
-/
@[simp]
theorem complexInterpolationValue_zero (r p₀ p₁ : ℝ) (z : ℂ) :
    complexInterpolationValue r p₀ p₁ z 0 = 0 := by
  simp [complexInterpolationValue]

/--
%%handwave
name:
  Holomorphy of an interpolated scalar value
statement:
  For fixed $w\in\mathbb C$, the function $z\mapsto w_z$ is entire.
proof:
  At $w=0$ the function is constant. Otherwise $|w|>0$, so complex power
  with fixed nonzero base is entire in its exponent; compose it with the
  affine exponent $a(z)$ and multiply by the constant phase $w/|w|$.
-/
theorem differentiable_complexInterpolationValue
    (r p₀ p₁ : ℝ) (w : ℂ) :
    Differentiable ℂ (fun z ↦ complexInterpolationValue r p₀ p₁ z w) := by
  by_cases hw : w = 0
  · subst w
    simp only [complexInterpolationValue_zero]
    fun_prop
  · simp only [complexInterpolationValue, hw, if_false]
    have hphase : Differentiable ℂ
        (fun _ : ℂ ↦ w / (‖w‖ : ℂ)) :=
      differentiable_const (w / (‖w‖ : ℂ))
    have hpow : Differentiable ℂ
        (fun z ↦ (‖w‖ : ℂ) ^ complexInterpolationExponent r p₀ p₁ z) := by
      apply Differentiable.const_cpow
        (differentiable_complexInterpolationExponent r p₀ p₁)
      left
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
    exact hphase.mul hpow

/--
%%handwave
name:
  Norm of a nonzero interpolated scalar value
statement:
  If $w\ne0$, then for every $z\in\mathbb C$,
  $$
    |w_z|=|w|^{\frac r{p_0}(1-\operatorname{Re}z)
      +\frac r{p_1}\operatorname{Re}z}.
  $$
proof:
  The phase $w/|w|$ has norm one. Since the power has positive real base,
  the norm of its complex power is the real base raised to the real part of
  the exponent.
-/
theorem norm_complexInterpolationValue_of_ne_zero
    (r p₀ p₁ : ℝ) (z : ℂ) {w : ℂ} (hw : w ≠ 0) :
    ‖complexInterpolationValue r p₀ p₁ z w‖ =
      ‖w‖ ^ ((r / p₀) * (1 - z.re) + (r / p₁) * z.re) := by
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [complexInterpolationValue, if_neg hw, norm_mul, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w),
    div_self hwnorm.ne', one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hwnorm,
    complexInterpolationExponent_re]

/--
%%handwave
name:
  Positivity of the interpolation exponent on the closed strip
statement:
  If $r,p_0,p_1>0$ and $0\leq\operatorname{Re}z\leq1$, then
  $$
    \frac r{p_0}(1-\operatorname{Re}z)
      +\frac r{p_1}\operatorname{Re}z>0.
  $$
proof:
  This is a convex combination of the two positive numbers $r/p_0$ and
  $r/p_1$.
-/
theorem complexInterpolationExponent_re_pos
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    0 < (r / p₀) * (1 - z.re) + (r / p₁) * z.re := by
  rw [Complex.HadamardThreeLines.verticalClosedStrip] at hz
  rcases hz with ⟨hz0, hz1⟩
  have hleft : 0 ≤ (r / p₀) * (1 - z.re) :=
    mul_nonneg (div_nonneg hr.le hp₀.le) (sub_nonneg.mpr hz1)
  have hright : 0 ≤ (r / p₁) * z.re :=
    mul_nonneg (div_nonneg hr.le hp₁.le) hz0
  rcases hz0.eq_or_lt with hz0eq | hz0lt
  · rw [← hz0eq, mul_zero, add_zero]
    exact mul_pos (div_pos hr hp₀) (by linarith)
  · exact add_pos_of_nonneg_of_pos hleft (mul_pos (div_pos hr hp₁) hz0lt)

/--
%%handwave
name:
  Norm of an interpolated scalar value on the closed strip
statement:
  If $r,p_0,p_1>0$ and $0\leq\operatorname{Re}z\leq1$, then every
  $w\in\mathbb C$ satisfies
  $$
    |w_z|=|w|^{\frac r{p_0}(1-\operatorname{Re}z)
      +\frac r{p_1}\operatorname{Re}z}.
  $$
proof:
  For $w\ne0$ this is the nonzero norm formula. At $w=0$, positivity of the
  real exponent makes both sides zero.
-/
theorem norm_complexInterpolationValue
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1)
    (w : ℂ) :
    ‖complexInterpolationValue r p₀ p₁ z w‖ =
      ‖w‖ ^ ((r / p₀) * (1 - z.re) + (r / p₁) * z.re) := by
  by_cases hw : w = 0
  · subst w
    rw [complexInterpolationValue_zero, norm_zero,
      Real.zero_rpow (complexInterpolationExponent_re_pos hr hp₀ hp₁ hz).ne']
  · exact norm_complexInterpolationValue_of_ne_zero r p₀ p₁ z hw

/--
%%handwave
name:
  Uniform strip boundedness of one interpolated scalar
statement:
  If $r,p_0,p_1>0$, then for every $w\in\mathbb C$ the set
  $$
    \{|w_z|:0\leq\operatorname{Re}z\leq1\}
  $$
  is bounded above.
proof:
  The norm depends only on $x=\operatorname{Re}z$ and equals the continuous
  function
  $|w|^{(r/p_0)(1-x)+(r/p_1)x}$ on the compact interval $[0,1]$.
-/
theorem bddAbove_norm_complexInterpolationValue
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (w : ℂ) :
    BddAbove
      ((norm ∘ fun z ↦ complexInterpolationValue r p₀ p₁ z w) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  by_cases hw : w = 0
  · subst w
    rw [bddAbove_def]
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    simp only [Function.comp_apply, complexInterpolationValue_zero, norm_zero,
      le_refl]
  · let φ : ℝ → ℝ := fun x ↦
      ‖w‖ ^ ((r / p₀) * (1 - x) + (r / p₁) * x)
    have hφ : Continuous φ := by
      apply (Real.continuous_const_rpow
        (norm_ne_zero_iff.mpr hw)).comp
      fun_prop
    apply (isCompact_Icc.image hφ).bddAbove.mono
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨z.re, ?_, ?_⟩
    · simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
    · simp only [Function.comp_apply, φ]
      exact (norm_complexInterpolationValue hr hp₀ hp₁ hz w).symm

/--
%%handwave
name:
  Recovery at the interpolated exponent
statement:
  Suppose $0\leq\theta\leq1$ and
  $$
    \frac1r=\frac{1-\theta}{p_0}+\frac\theta{p_1}.
  $$
  Then every $w\in\mathbb C$ satisfies $w_\theta=w$.
proof:
  The reciprocal-exponent identity makes $a(\theta)=1$. Thus the complex
  power contributes $|w|$, cancelling the denominator in the phase; the
  zero case is immediate.
-/
theorem complexInterpolationValue_of_reciprocal_interpolation
    {r p₀ p₁ θ : ℝ} (hr : 0 < r)
    (hθ : r⁻¹ = (1 - θ) / p₀ + θ / p₁) (w : ℂ) :
    complexInterpolationValue r p₀ p₁ (θ : ℂ) w = w := by
  have hexponent : complexInterpolationExponent r p₀ p₁ (θ : ℂ) = 1 := by
    apply Complex.ext
    · rw [complexInterpolationExponent_re]
      simp only [Complex.ofReal_re]
      change (r / p₀) * (1 - θ) + (r / p₁) * θ = (1 : ℝ)
      calc
        (r / p₀) * (1 - θ) + (r / p₁) * θ =
            r * ((1 - θ) / p₀ + θ / p₁) := by ring
        _ = r * r⁻¹ := by rw [hθ]
        _ = 1 := mul_inv_cancel₀ hr.ne'
    · simp [complexInterpolationExponent]
  by_cases hw : w = 0
  · subst w
    exact complexInterpolationValue_zero r p₀ p₁ (θ : ℂ)
  · rw [complexInterpolationValue, if_neg hw, hexponent, Complex.cpow_one]
    exact div_mul_cancel₀ w (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))

/--
%%handwave
name:
  Complex interpolation of a simple function
statement:
  For a simple function $f:X\to\mathbb C$, define the simple function
  $f_z$ by applying the scalar interpolation $w\mapsto w_z$ to every value
  of $f$.
-/
def complexInterpolationSimpleFunc
    {α : Type*} [MeasurableSpace α]
    (r p₀ p₁ : ℝ) (z : ℂ) (f : SimpleFunc α ℂ) : SimpleFunc α ℂ :=
  f.map (complexInterpolationValue r p₀ p₁ z)

/--
%%handwave
name:
  Interpolation preserves integrable simple functions
statement:
  If a simple function $f:X\to\mathbb C$ is integrable, then each
  interpolated simple function $f_z$ is integrable.
proof:
  The interpolation sends zero to zero, so the support of $f_z$ is contained
  in the finite-measure support of $f$.
-/
theorem integrable_complexInterpolationSimpleFunc
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (r p₀ p₁ : ℝ) (z : ℂ) {f : SimpleFunc α ℂ} (hf : Integrable f μ) :
    Integrable (complexInterpolationSimpleFunc r p₀ p₁ z f) μ := by
  rw [SimpleFunc.integrable_iff_finMeasSupp] at hf ⊢
  exact hf.map (complexInterpolationValue_zero r p₀ p₁ z)

/--
%%handwave
name:
  Simple-function interpolation recovers the original function
statement:
  Suppose
  $$
    \frac1r=\frac{1-\theta}{p_0}+\frac\theta{p_1}.
  $$
  Then every simple function $f:X\to\mathbb C$ satisfies $f_\theta=f$.
proof:
  Apply the scalar recovery identity to every value of the simple function.
-/
theorem complexInterpolationSimpleFunc_of_reciprocal_interpolation
    {α : Type*} [MeasurableSpace α]
    {r p₀ p₁ θ : ℝ} (hr : 0 < r)
    (hθ : r⁻¹ = (1 - θ) / p₀ + θ / p₁) (f : SimpleFunc α ℂ) :
    complexInterpolationSimpleFunc r p₀ p₁ (θ : ℂ) f = f := by
  ext x
  simp only [complexInterpolationSimpleFunc, SimpleFunc.coe_map,
    Function.comp_apply]
  exact complexInterpolationValue_of_reciprocal_interpolation hr hθ (f x)

/--
%%handwave
name:
  Left-boundary norm of an interpolated simple function
statement:
  Let $r,p_0,p_1>0$, let $f:X\to\mathbb C$ be a simple function, and let
  $\operatorname{Re}z=0$. Then
  $$
    \|f_z\|_{p_0}
      =\left(\int_X|f|^r\,d\mu\right)^{1/p_0}.
  $$
proof:
  On the left boundary, $|f_z|=|f|^{r/p_0}$. Raising to the $p_0$ power
  gives $|f|^r$ pointwise, and the standard integral formula for the finite
  $L^{p_0}$ seminorm gives the result.
-/
theorem lpNorm_complexInterpolationSimpleFunc_of_re_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (f : SimpleFunc α ℂ) {z : ℂ} (hz : z.re = 0) :
    lpNorm (complexInterpolationSimpleFunc r p₀ p₁ z f : α → ℂ)
        (ENNReal.ofReal p₀) μ =
      (∫ x, ‖f x‖ ^ r ∂μ) ^ p₀⁻¹ := by
  have hzstrip : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, hz]
  rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp₀)
      ENNReal.ofReal_ne_top
      (complexInterpolationSimpleFunc r p₀ p₁ z f).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp₀.le]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change ‖(complexInterpolationSimpleFunc r p₀ p₁ z f : α → ℂ) x‖ ^ p₀ =
    ‖f x‖ ^ r
  rw [show (complexInterpolationSimpleFunc r p₀ p₁ z f : α → ℂ) x =
      complexInterpolationValue r p₀ p₁ z (f x) from rfl,
    norm_complexInterpolationValue hr hp₀ hp₁ hzstrip, hz]
  simp only [sub_zero, mul_one, mul_zero, add_zero]
  rw [← Real.rpow_mul (norm_nonneg (f x))]
  congr 1
  exact div_mul_cancel₀ r hp₀.ne'

/--
%%handwave
name:
  Right-boundary norm of an interpolated simple function
statement:
  Let $r,p_0,p_1>0$, let $f:X\to\mathbb C$ be a simple function, and let
  $\operatorname{Re}z=1$. Then
  $$
    \|f_z\|_{p_1}
      =\left(\int_X|f|^r\,d\mu\right)^{1/p_1}.
  $$
proof:
  On the right boundary, $|f_z|=|f|^{r/p_1}$. Raising to the $p_1$ power
  gives $|f|^r$ pointwise, and the integral formula for the finite
  $L^{p_1}$ seminorm gives the result.
-/
theorem lpNorm_complexInterpolationSimpleFunc_of_re_eq_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (f : SimpleFunc α ℂ) {z : ℂ} (hz : z.re = 1) :
    lpNorm (complexInterpolationSimpleFunc r p₀ p₁ z f : α → ℂ)
        (ENNReal.ofReal p₁) μ =
      (∫ x, ‖f x‖ ^ r ∂μ) ^ p₁⁻¹ := by
  have hzstrip : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, hz]
  rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp₁)
      ENNReal.ofReal_ne_top
      (complexInterpolationSimpleFunc r p₀ p₁ z f).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp₁.le]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change ‖(complexInterpolationSimpleFunc r p₀ p₁ z f : α → ℂ) x‖ ^ p₁ =
    ‖f x‖ ^ r
  rw [show (complexInterpolationSimpleFunc r p₀ p₁ z f : α → ℂ) x =
      complexInterpolationValue r p₀ p₁ z (f x) from rfl,
    norm_complexInterpolationValue hr hp₀ hp₁ hzstrip, hz]
  simp only [sub_self, mul_zero, mul_one, zero_add]
  rw [← Real.rpow_mul (norm_nonneg (f x))]
  congr 1
  exact div_mul_cancel₀ r hp₁.ne'

/--
%%handwave
name:
  Unit $L^r$ norm determines the $r$th moment
statement:
  If $r>0$, $f:X\to\mathbb C$ is strongly measurable, and
  $\|f\|_r=1$, then
  $$
    \int_X|f|^r\,d\mu=1.
  $$
proof:
  The integral formula for the finite $L^r$ seminorm gives
  $(\int|f|^r)^{1/r}=1$. Both bases are nonnegative and the exponent
  $1/r$ is nonzero, so injectivity of positive real powers yields the claim.
-/
theorem integral_norm_rpow_eq_one_of_lpNorm_eq_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r : ℝ} (hr : 0 < r) {f : α → ℂ} (hf : StronglyMeasurable f)
    (hnorm : lpNorm f (ENNReal.ofReal r) μ = 1) :
    (∫ x, ‖f x‖ ^ r ∂μ) = 1 := by
  have hnorm' := hnorm
  rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hr)
      ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hr.le] at hnorm'
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ r ∂μ :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (f x)) r
  apply (Real.rpow_left_inj hnonneg zero_le_one (inv_ne_zero hr.ne')).mp
  simpa only [Real.one_rpow] using hnorm'

/--
%%handwave
name:
  Unit norm on the left interpolation boundary
statement:
  Let $r,p_0,p_1>0$. If a simple function $f$ satisfies $\|f\|_r=1$,
  then every interpolant on the line $\operatorname{Re}z=0$ satisfies
  $$\|f_z\|_{p_0}=1.$$
proof:
  The left-boundary formula is
  $(\int|f|^r)^{1/p_0}$, and the unit $L^r$ norm makes the integral equal
  to one.
-/
theorem lpNorm_complexInterpolationSimpleFunc_eq_one_of_re_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (f : SimpleFunc α ℂ)
    (hnorm : lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ = 1)
    {z : ℂ} (hz : z.re = 0) :
    lpNorm (complexInterpolationSimpleFunc r p₀ p₁ z f : α → ℂ)
        (ENNReal.ofReal p₀) μ = 1 := by
  rw [lpNorm_complexInterpolationSimpleFunc_of_re_eq_zero
      hr hp₀ hp₁ f hz,
    integral_norm_rpow_eq_one_of_lpNorm_eq_one hr f.stronglyMeasurable hnorm,
    Real.one_rpow]

/--
%%handwave
name:
  Unit norm on the right interpolation boundary
statement:
  Let $r,p_0,p_1>0$. If a simple function $f$ satisfies $\|f\|_r=1$,
  then every interpolant on the line $\operatorname{Re}z=1$ satisfies
  $$\|f_z\|_{p_1}=1.$$
proof:
  The right-boundary formula is
  $(\int|f|^r)^{1/p_1}$, and the unit $L^r$ norm makes the integral equal
  to one.
-/
theorem lpNorm_complexInterpolationSimpleFunc_eq_one_of_re_eq_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (f : SimpleFunc α ℂ)
    (hnorm : lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ = 1)
    {z : ℂ} (hz : z.re = 1) :
    lpNorm (complexInterpolationSimpleFunc r p₀ p₁ z f : α → ℂ)
        (ENNReal.ofReal p₁) μ = 1 := by
  rw [lpNorm_complexInterpolationSimpleFunc_of_re_eq_one
      hr hp₀ hp₁ f hz,
    integral_norm_rpow_eq_one_of_lpNorm_eq_one hr f.stronglyMeasurable hnorm,
    Real.one_rpow]

/--
%%handwave
name:
  Analytic deformation on the integrable simple-function core
statement:
  If $f$ is an integrable complex simple function, then applying the scalar
  deformation value by value defines another integrable simple function
  $f_z$ for every $z\in\mathbb C$.
-/
def complexInterpolationL1SimpleFunc
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (r p₀ p₁ : ℝ) (z : ℂ) (f : α →₁ₛ[μ] ℂ) : α →₁ₛ[μ] ℂ :=
  let fz : SimpleFunc α ℂ :=
    complexInterpolationSimpleFunc r p₀ p₁ z
      (Lp.simpleFunc.toSimpleFunc f)
  let hfz : Integrable fz μ :=
    integrable_complexInterpolationSimpleFunc r p₀ p₁ z
      (L1.SimpleFunc.integrable f)
  fz.toLp (memLp_one_iff_integrable.mpr hfz)

/--
%%handwave
name:
  Representative of the analytic simple-function deformation
statement:
  The function representative of the integrable simple-function class
  $f_z$ agrees almost everywhere with the pointwise deformation of the
  chosen simple representative of $f$.
proof:
  The pointwise deformation is the representative used to construct the
  integrable simple-function class.
-/
theorem complexInterpolationL1SimpleFunc_coeFn
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (r p₀ p₁ : ℝ) (z : ℂ) (f : α →₁ₛ[μ] ℂ) :
    (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f : α → ℂ) =ᵐ[μ]
      (complexInterpolationSimpleFunc r p₀ p₁ z
        (Lp.simpleFunc.toSimpleFunc f) : α → ℂ) := by
  dsimp only [complexInterpolationL1SimpleFunc]
  exact MemLp.coeFn_toLp _

/--
%%handwave
name:
  Integrable simple functions belong to every finite positive $L^p$
statement:
  If $f$ is an integrable simple function and $0<p<\infty$, then
  $f\in L^p$.
proof:
  An integrable simple function is bounded and has finite-measure support.
  The finite-support criterion for simple functions gives the assertion for
  every finite positive exponent.
-/
theorem memLp_integrableSimpleFunc
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : ℝ} (hp : 0 < p) (f : α →₁ₛ[μ] ℂ) :
    MemLp (f : α → ℂ) (ENNReal.ofReal p) μ := by
  have hsimple :
      MemLp (Lp.simpleFunc.toSimpleFunc f : α → ℂ)
        (ENNReal.ofReal p) μ := by
    rw [SimpleFunc.memLp_iff_integrable
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
    exact L1.SimpleFunc.integrable f
  exact (memLp_congr_ae
    (Lp.simpleFunc.toSimpleFunc_eq_toFun f)).mp hsimple

/--
%%handwave
name:
  Homogeneity of $L^p$ seminorm on integrable simple functions
statement:
  For every integrable simple function $f$, scalar $c\in\mathbb C$, and
  exponent $p$,
  $$
    \|cf\|_p=|c|\,\|f\|_p.
  $$
proof:
  The representative of the scalar multiple agrees almost everywhere with
  the pointwise scalar multiple, whose $L^p$ seminorm is homogeneous.
-/
theorem lpNorm_smul_integrableSimpleFunc
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ENNReal) (c : ℂ) (f : α →₁ₛ[μ] ℂ) :
    lpNorm ((c • f : α →₁ₛ[μ] ℂ) : α → ℂ) p μ =
      ‖c‖ * lpNorm (f : α → ℂ) p μ := by
  have hcoe :
      ((c • f : α →₁ₛ[μ] ℂ) : α → ℂ) =ᵐ[μ]
        c • (f : α → ℂ) := by
    exact Lp.coeFn_smul c (f : α →₁[μ] ℂ)
  calc
    lpNorm ((c • f : α →₁ₛ[μ] ℂ) : α → ℂ) p μ =
        (eLpNorm ((c • f : α →₁ₛ[μ] ℂ) : α → ℂ) p μ).toReal :=
      (toReal_eLpNorm
        (Lp.memLp (c • (f : α →₁[μ] ℂ))).aestronglyMeasurable).symm
    _ = (eLpNorm (c • (f : α → ℂ)) p μ).toReal :=
      congrArg ENNReal.toReal (eLpNorm_congr_ae hcoe)
    _ = lpNorm (c • (f : α → ℂ)) p μ :=
      toReal_eLpNorm
        ((Lp.memLp (f : α →₁[μ] ℂ)).aestronglyMeasurable.const_smul c)
    _ = ‖c‖ * lpNorm (f : α → ℂ) p μ :=
      lpNorm_const_smul c (f : α → ℂ) μ

/--
%%handwave
name:
  Unit norm on the left boundary for an integrable simple function
statement:
  Let $r,p_0,p_1>0$. If an integrable simple function $f$ satisfies
  $\|f\|_r=1$, then for every $z$ with $\operatorname{Re}z=0$,
  $$
    \|f_z\|_{p_0}=1.
  $$
proof:
  The chosen simple representative of $f$ has the same $L^r$ seminorm.
  Apply the pointwise simple-function boundary formula and transfer the
  result back through the almost-everywhere representative of $f_z$.
-/
theorem lpNorm_complexInterpolationL1SimpleFunc_eq_one_of_re_eq_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (f : α →₁ₛ[μ] ℂ)
    (hnorm : lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ = 1)
    {z : ℂ} (hz : z.re = 0) :
    lpNorm
        (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f : α → ℂ)
        (ENNReal.ofReal p₀) μ = 1 := by
  have hf_norm :
      lpNorm (Lp.simpleFunc.toSimpleFunc f : α → ℂ)
        (ENNReal.ofReal r) μ = 1 := by
    calc
      lpNorm (Lp.simpleFunc.toSimpleFunc f : α → ℂ)
          (ENNReal.ofReal r) μ =
          lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ := by
        rw [← toReal_eLpNorm
            (Lp.simpleFunc.toSimpleFunc f).aestronglyMeasurable,
          ← toReal_eLpNorm
            (Lp.memLp (f : α →₁[μ] ℂ)).aestronglyMeasurable,
          eLpNorm_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun f)]
      _ = 1 := hnorm
  calc
    lpNorm
        (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f : α → ℂ)
        (ENNReal.ofReal p₀) μ =
        lpNorm
          (complexInterpolationSimpleFunc r p₀ p₁ z
            (Lp.simpleFunc.toSimpleFunc f) : α → ℂ)
          (ENNReal.ofReal p₀) μ := by
      rw [← toReal_eLpNorm
          (Lp.memLp
            (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f :
              α →₁[μ] ℂ)).aestronglyMeasurable,
        ← toReal_eLpNorm
          (complexInterpolationSimpleFunc r p₀ p₁ z
            (Lp.simpleFunc.toSimpleFunc f)).aestronglyMeasurable,
        eLpNorm_congr_ae
          (complexInterpolationL1SimpleFunc_coeFn μ r p₀ p₁ z f)]
    _ = 1 :=
      lpNorm_complexInterpolationSimpleFunc_eq_one_of_re_eq_zero
        hr hp₀ hp₁ (Lp.simpleFunc.toSimpleFunc f) hf_norm hz

/--
%%handwave
name:
  Unit norm on the right boundary for an integrable simple function
statement:
  Let $r,p_0,p_1>0$. If an integrable simple function $f$ satisfies
  $\|f\|_r=1$, then for every $z$ with $\operatorname{Re}z=1$,
  $$
    \|f_z\|_{p_1}=1.
  $$
proof:
  The chosen simple representative of $f$ has the same $L^r$ seminorm.
  Apply the pointwise simple-function boundary formula and transfer the
  result back through the almost-everywhere representative of $f_z$.
-/
theorem lpNorm_complexInterpolationL1SimpleFunc_eq_one_of_re_eq_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {r p₀ p₁ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (f : α →₁ₛ[μ] ℂ)
    (hnorm : lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ = 1)
    {z : ℂ} (hz : z.re = 1) :
    lpNorm
        (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f : α → ℂ)
        (ENNReal.ofReal p₁) μ = 1 := by
  have hf_norm :
      lpNorm (Lp.simpleFunc.toSimpleFunc f : α → ℂ)
        (ENNReal.ofReal r) μ = 1 := by
    calc
      lpNorm (Lp.simpleFunc.toSimpleFunc f : α → ℂ)
          (ENNReal.ofReal r) μ =
          lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ := by
        rw [← toReal_eLpNorm
            (Lp.simpleFunc.toSimpleFunc f).aestronglyMeasurable,
          ← toReal_eLpNorm
            (Lp.memLp (f : α →₁[μ] ℂ)).aestronglyMeasurable,
          eLpNorm_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun f)]
      _ = 1 := hnorm
  calc
    lpNorm
        (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f : α → ℂ)
        (ENNReal.ofReal p₁) μ =
        lpNorm
          (complexInterpolationSimpleFunc r p₀ p₁ z
            (Lp.simpleFunc.toSimpleFunc f) : α → ℂ)
          (ENNReal.ofReal p₁) μ := by
      rw [← toReal_eLpNorm
          (Lp.memLp
            (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f :
              α →₁[μ] ℂ)).aestronglyMeasurable,
        ← toReal_eLpNorm
          (complexInterpolationSimpleFunc r p₀ p₁ z
            (Lp.simpleFunc.toSimpleFunc f)).aestronglyMeasurable,
        eLpNorm_congr_ae
          (complexInterpolationL1SimpleFunc_coeFn μ r p₀ p₁ z f)]
    _ = 1 :=
      lpNorm_complexInterpolationSimpleFunc_eq_one_of_re_eq_one
        hr hp₀ hp₁ (Lp.simpleFunc.toSimpleFunc f) hf_norm hz

/--
%%handwave
name:
  Recovery of an integrable simple function at the interpolation point
statement:
  Suppose
  $$
    \frac1r=\frac{1-\theta}{p_0}+\frac\theta{p_1}.
  $$
  Then the analytic deformation of every integrable simple function satisfies
  $f_\theta=f$.
proof:
  The pointwise deformation at $\theta$ is the identity. The chosen simple
  representative of an integrable simple-function class agrees almost
  everywhere with that class.
-/
theorem complexInterpolationL1SimpleFunc_of_reciprocal_interpolation
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {r p₀ p₁ θ : ℝ} (hr : 0 < r)
    (hθ : r⁻¹ = (1 - θ) / p₀ + θ / p₁)
    (f : α →₁ₛ[μ] ℂ) :
    complexInterpolationL1SimpleFunc μ r p₀ p₁ (θ : ℂ) f = f := by
  apply Lp.simpleFunc.eq'
  apply AEEqFun.ext
  have hpoint :
      (complexInterpolationSimpleFunc r p₀ p₁ (θ : ℂ)
          (Lp.simpleFunc.toSimpleFunc f) : α → ℂ) =
        (Lp.simpleFunc.toSimpleFunc f : α → ℂ) :=
    congrArg DFunLike.coe <|
      complexInterpolationSimpleFunc_of_reciprocal_interpolation
        hr hθ (Lp.simpleFunc.toSimpleFunc f)
  have haeq :
      (complexInterpolationSimpleFunc r p₀ p₁ (θ : ℂ)
          (Lp.simpleFunc.toSimpleFunc f) : α → ℂ) =ᵐ[μ]
        (Lp.simpleFunc.toSimpleFunc f : α → ℂ) :=
    Filter.Eventually.of_forall fun x ↦ congrFun hpoint x
  exact (complexInterpolationL1SimpleFunc_coeFn μ r p₀ p₁ (θ : ℂ) f).trans
    (haeq.trans (Lp.simpleFunc.toSimpleFunc_eq_toFun f))

/--
%%handwave
name:
  Simple indicator of a value fiber
statement:
  If $f:X\to\mathbb C$ is a simple function and $c\in\mathbb C$, define
  $\mathbf1_{\{f=c\}}$ as the simple function equal to one on the fiber
  $\{x:f(x)=c\}$ and zero elsewhere.
-/
def simpleFuncFiberIndicator
    {α : Type*} [MeasurableSpace α] (f : SimpleFunc α ℂ) (c : ℂ) :
    SimpleFunc α ℂ :=
  (SimpleFunc.const α 1).piecewise (f ⁻¹' {c}) (f.measurableSet_fiber c)
    (SimpleFunc.const α 0)

/--
%%handwave
name:
  Value of a simple fiber indicator
statement:
  For every $x\in X$,
  $$
    \mathbf1_{\{f=c\}}(x)=
      \begin{cases}1,&f(x)=c,\\0,&f(x)\ne c.\end{cases}
  $$
proof:
  This is the pointwise formula for the defining piecewise simple function.
-/
theorem simpleFuncFiberIndicator_apply
    {α : Type*} [MeasurableSpace α] (f : SimpleFunc α ℂ) (c : ℂ) (x : α) :
    simpleFuncFiberIndicator f c x = if f x = c then 1 else 0 := by
  by_cases hx : f x = c
  · simp [simpleFuncFiberIndicator, hx]
  · simp [simpleFuncFiberIndicator, hx]

/--
%%handwave
name:
  Integrable simple indicator of a value fiber
statement:
  If $f:X\to\mathbb C$ is an integrable simple function and $c\in\mathbb C$,
  define $e_{f,c}$ to be the integrable simple function equal to one on
  $\{x:f(x)=c\}$ and zero elsewhere when $c\ne0$, and define
  $e_{f,0}=0$.
-/
def integrableSimpleFuncFiberIndicator
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α →₁ₛ[μ] ℂ) (c : ℂ) : α →₁ₛ[μ] ℂ :=
  if hc : c = 0 then 0
  else
    Lp.simpleFunc.indicatorConst (1 : ENNReal)
      ((Lp.simpleFunc.toSimpleFunc f).measurableSet_fiber c)
      ((SimpleFunc.integrable_iff.mp (L1.SimpleFunc.integrable f) c hc).ne)
      1

/--
%%handwave
name:
  Representative of a nonzero value-fiber indicator
statement:
  If $c\ne0$, then $e_{f,c}$ agrees almost everywhere with the simple
  function that is one on $\{x:f(x)=c\}$ and zero elsewhere.
proof:
  Integrability of $f$ gives finite measure to every nonzero value fiber, so
  the standard finite-measure indicator class applies and has the asserted
  representative.
-/
theorem integrableSimpleFuncFiberIndicator_coeFn
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α →₁ₛ[μ] ℂ) {c : ℂ} (hc : c ≠ 0) :
    (integrableSimpleFuncFiberIndicator μ f c : α → ℂ) =ᵐ[μ]
      (simpleFuncFiberIndicator (Lp.simpleFunc.toSimpleFunc f) c : α → ℂ) := by
  rw [integrableSimpleFuncFiberIndicator, dif_neg hc]
  exact (Lp.simpleFunc.toSimpleFunc_eq_toFun _).symm.trans
    ((Lp.simpleFunc.toSimpleFunc_indicatorConst
      (p := (1 : ENNReal))
      ((Lp.simpleFunc.toSimpleFunc f).measurableSet_fiber c)
      ((SimpleFunc.integrable_iff.mp (L1.SimpleFunc.integrable f) c hc).ne)
      1).trans (Filter.Eventually.of_forall fun x ↦ by
        simp [simpleFuncFiberIndicator]))

/--
%%handwave
name:
  Finite-sum form of the analytic simple-function deformation
statement:
  For an integrable simple function $f$, define
  $$
    \widetilde f_z=
      \sum_{c\in\operatorname{range}(f)\setminus\{0\}}c_z e_{f,c},
  $$
  where $c_z$ is the scalar analytic deformation and $e_{f,c}$ is the
  indicator of the value fiber $\{f=c\}$.
-/
def complexInterpolationL1SimpleFuncSum
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (r p₀ p₁ : ℝ) (z : ℂ) (f : α →₁ₛ[μ] ℂ) : α →₁ₛ[μ] ℂ :=
  ∑ c ∈ (Lp.simpleFunc.toSimpleFunc f).range.filter (· ≠ 0),
    complexInterpolationValue r p₀ p₁ z c •
      integrableSimpleFuncFiberIndicator μ f c

/--
%%handwave
name:
  Finite-sum deformation represents the pointwise deformation
statement:
  For every integrable simple function $f$ and $z\in\mathbb C$, the
  finite sum
  $$
    \sum_{c\in\operatorname{range}(f)\setminus\{0\}}c_z e_{f,c}
  $$
  agrees almost everywhere with the valuewise deformation $f_z$.
proof:
  The fiber indicators have pairwise disjoint supports. At a point $x$ with
  $f(x)\ne0$, exactly the summand indexed by $c=f(x)$ survives and equals
  $f(x)_z$; when $f(x)=0$, all summands and the deformation vanish.
-/
theorem complexInterpolationL1SimpleFuncSum_coeFn
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (r p₀ p₁ : ℝ) (z : ℂ) (f : α →₁ₛ[μ] ℂ) :
    (complexInterpolationL1SimpleFuncSum μ r p₀ p₁ z f : α → ℂ) =ᵐ[μ]
      (complexInterpolationSimpleFunc r p₀ p₁ z
        (Lp.simpleFunc.toSimpleFunc f) : α → ℂ) := by
  classical
  let f₀ : SimpleFunc α ℂ := Lp.simpleFunc.toSimpleFunc f
  let s : Finset ℂ := f₀.range.filter (· ≠ 0)
  let a : ℂ → ℂ := complexInterpolationValue r p₀ p₁ z
  let e : ℂ → α →₁ₛ[μ] ℂ := integrableSimpleFuncFiberIndicator μ f
  let e₀ : ℂ → SimpleFunc α ℂ := simpleFuncFiberIndicator f₀
  have hs_ne : ∀ c ∈ s, c ≠ 0 := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have hsum_general : ∀ (t : Finset ℂ),
      (∀ c ∈ t, c ≠ 0) →
      ((∑ c ∈ t, a c • e c : α →₁ₛ[μ] ℂ) : α → ℂ) =ᵐ[μ]
        fun x ↦ ∑ c ∈ t, a c * e₀ c x := by
    intro t ht
    induction t using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (Lp.coeFn_zero ℂ (1 : ENNReal) μ)
    | @insert c t hc ih =>
        have hc0 : c ≠ 0 := ht c (Finset.mem_insert_self c t)
        have ht0 : ∀ d ∈ t, d ≠ 0 := by
          intro d hd
          exact ht d (Finset.mem_insert_of_mem hd)
        have hbasis : (e c : α → ℂ) =ᵐ[μ] (e₀ c : α → ℂ) := by
          exact integrableSimpleFuncFiberIndicator_coeFn μ f hc0
        have hcoe_smul :
            ((a c • e c : α →₁ₛ[μ] ℂ) : α → ℂ) =ᵐ[μ]
              a c • (e c : α → ℂ) := by
          exact Lp.coeFn_smul (a c) (e c : α →₁[μ] ℂ)
        have hsmul :
            ((a c • e c : α →₁ₛ[μ] ℂ) : α → ℂ) =ᵐ[μ]
              fun x ↦ a c * e₀ c x := by
          filter_upwards [hcoe_smul, hbasis] with x hxsmul hxbasis
          rw [hxsmul, Pi.smul_apply, hxbasis, smul_eq_mul]
        have hadd :
            ((a c • e c + ∑ d ∈ t, a d • e d : α →₁ₛ[μ] ℂ) : α → ℂ)
              =ᵐ[μ]
            ((a c • e c : α →₁ₛ[μ] ℂ) : α → ℂ) +
              ((∑ d ∈ t, a d • e d : α →₁ₛ[μ] ℂ) : α → ℂ) := by
          exact Lp.coeFn_add
            (a c • e c : α →₁[μ] ℂ)
            ((∑ d ∈ t, a d • e d : α →₁ₛ[μ] ℂ) : α →₁[μ] ℂ)
        filter_upwards [hadd, hsmul, ih ht0] with x hxadd hxc hxt
        simp only [Finset.sum_insert hc]
        rw [hxadd, Pi.add_apply, hxc, hxt]
  have hsum := hsum_general s hs_ne
  apply hsum.trans
  apply Filter.Eventually.of_forall
  intro x
  change (∑ c ∈ s, a c * e₀ c x) =
    complexInterpolationValue r p₀ p₁ z (f₀ x)
  by_cases hx0 : f₀ x = 0
  · rw [hx0, complexInterpolationValue_zero]
    apply Finset.sum_eq_zero
    intro c hc
    rw [simpleFuncFiberIndicator_apply]
    have hc0 : c ≠ 0 := hs_ne c hc
    have h0c : ¬(0 : ℂ) = c := Ne.symm hc0
    simp [hx0, h0c]
  · have hxmem : f₀ x ∈ s := by
      exact Finset.mem_filter.mpr ⟨f₀.mem_range_self x, hx0⟩
    rw [Finset.sum_eq_single (f₀ x)]
    · rw [simpleFuncFiberIndicator_apply]
      simp [a]
    · intro c hc hcx
      rw [simpleFuncFiberIndicator_apply]
      simp [Ne.symm hcx]
    · exact fun hnot ↦ (hnot hxmem).elim

/--
%%handwave
name:
  Equality of the two analytic simple-function deformations
statement:
  The valuewise deformation $f_z$ equals its finite value-fiber expansion
  $$
    f_z=\sum_{c\in\operatorname{range}(f)\setminus\{0\}}c_z e_{f,c}
  $$
  as an integrable simple-function class.
proof:
  Both classes have almost-everywhere representatives equal to the same
  valuewise deformation.
-/
theorem complexInterpolationL1SimpleFunc_eq_sum
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (r p₀ p₁ : ℝ) (z : ℂ) (f : α →₁ₛ[μ] ℂ) :
    complexInterpolationL1SimpleFunc μ r p₀ p₁ z f =
      complexInterpolationL1SimpleFuncSum μ r p₀ p₁ z f := by
  apply Lp.simpleFunc.eq'
  apply AEEqFun.ext
  exact (complexInterpolationL1SimpleFunc_coeFn μ r p₀ p₁ z f).trans
    (complexInterpolationL1SimpleFuncSum_coeFn μ r p₀ p₁ z f).symm

/--
%%handwave
name:
  Interpolated bilinear pairing on the simple core
statement:
  Given a complex-bilinear pairing
  $B:L^1_{\mathrm{simple}}(X)\times
  L^1_{\mathrm{simple}}(Y)\to\mathbb C$ and analytic deformations $f_z$
  and $g_z$, define
  $$
    F(z)=B(f_z,g_z).
  $$
-/
def complexInterpolationBilinearPairing
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (B : (α →₁ₛ[μ] ℂ) →ₗ[ℂ] ((β →₁ₛ[ν] ℂ) →ₗ[ℂ] ℂ))
    (r p₀ p₁ s q₀ q₁ : ℝ)
    (f : α →₁ₛ[μ] ℂ) (g : β →₁ₛ[ν] ℂ) (z : ℂ) : ℂ :=
  B (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f)
    (complexInterpolationL1SimpleFunc ν s q₀ q₁ z g)

/--
%%handwave
name:
  Finite expansion of the interpolated bilinear pairing
statement:
  If $e_{f,c}$ and $e_{g,d}$ are the indicators of the nonzero value
  fibers of $f$ and $g$, then
  $$
    B(f_z,g_z)=
      \sum_{d\in\operatorname{range}(g)\setminus\{0\}}
      \sum_{c\in\operatorname{range}(f)\setminus\{0\}}
      d_zc_zB(e_{f,c},e_{g,d}).
  $$
proof:
  Substitute the finite value-fiber expansions of both deformations and
  distribute the two linear arguments of $B$ over the sums.
-/
theorem complexInterpolationBilinearPairing_eq_sum
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (B : (α →₁ₛ[μ] ℂ) →ₗ[ℂ] ((β →₁ₛ[ν] ℂ) →ₗ[ℂ] ℂ))
    (r p₀ p₁ s q₀ q₁ : ℝ)
    (f : α →₁ₛ[μ] ℂ) (g : β →₁ₛ[ν] ℂ) (z : ℂ) :
    complexInterpolationBilinearPairing μ ν B r p₀ p₁ s q₀ q₁ f g z =
      ∑ d ∈ (Lp.simpleFunc.toSimpleFunc g).range.filter (· ≠ 0),
        ∑ c ∈ (Lp.simpleFunc.toSimpleFunc f).range.filter (· ≠ 0),
          complexInterpolationValue s q₀ q₁ z d *
            complexInterpolationValue r p₀ p₁ z c *
              B (integrableSimpleFuncFiberIndicator μ f c)
                (integrableSimpleFuncFiberIndicator ν g d) := by
  classical
  unfold complexInterpolationBilinearPairing
  rw [complexInterpolationL1SimpleFunc_eq_sum,
    complexInterpolationL1SimpleFunc_eq_sum]
  simp only [complexInterpolationL1SimpleFuncSum, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/--
%%handwave
name:
  Holomorphy of a bilinear pairing on the simple core
statement:
  Let $B:L^1_{\mathrm{simple}}(X)\times
  L^1_{\mathrm{simple}}(Y)\to\mathbb C$ be complex-bilinear. If $f_z$ and
  $g_z$ are analytic simple-function deformations, possibly formed with
  different endpoint exponents, then
  $$
    z\longmapsto B(f_z,g_z)
  $$
  is entire.
proof:
  Expand both deformations over their finitely many nonzero value fibers.
  Bilinearity gives a finite double sum whose scalar coefficients are
  products of entire scalar deformations.
-/
theorem differentiable_bilinearMap_complexInterpolationL1SimpleFunc
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (B : (α →₁ₛ[μ] ℂ) →ₗ[ℂ] ((β →₁ₛ[ν] ℂ) →ₗ[ℂ] ℂ))
    (r p₀ p₁ s q₀ q₁ : ℝ)
    (f : α →₁ₛ[μ] ℂ) (g : β →₁ₛ[ν] ℂ) :
    Differentiable ℂ
      (complexInterpolationBilinearPairing μ ν B r p₀ p₁ s q₀ q₁ f g) := by
  classical
  let sf : Finset ℂ :=
    (Lp.simpleFunc.toSimpleFunc f).range.filter (· ≠ 0)
  let sg : Finset ℂ :=
    (Lp.simpleFunc.toSimpleFunc g).range.filter (· ≠ 0)
  have hfun :
      complexInterpolationBilinearPairing μ ν B r p₀ p₁ s q₀ q₁ f g =
        fun z ↦ ∑ d ∈ sg, ∑ c ∈ sf,
          complexInterpolationValue s q₀ q₁ z d *
            complexInterpolationValue r p₀ p₁ z c *
              B (integrableSimpleFuncFiberIndicator μ f c)
                (integrableSimpleFuncFiberIndicator ν g d) := by
    funext z
    exact complexInterpolationBilinearPairing_eq_sum
      μ ν B r p₀ p₁ s q₀ q₁ f g z
  rw [hfun]
  apply Differentiable.fun_sum
  intro d hd
  apply Differentiable.fun_sum
  intro c hc
  apply Differentiable.mul
  · apply Differentiable.mul
    · exact differentiable_complexInterpolationValue s q₀ q₁ d
    · exact differentiable_complexInterpolationValue r p₀ p₁ c
  · exact differentiable_const _

/--
%%handwave
name:
  Uniform strip boundedness of an interpolated bilinear pairing
statement:
  Let $B$ be a complex-bilinear pairing of two integrable simple-function
  spaces. If all six deformation exponents are positive, then
  $$
    \{|B(f_z,g_z)|:0\leq\operatorname{Re}z\leq1\}
  $$
  is bounded above.
proof:
  The pairing is a finite double sum over the nonzero value fibers of $f$
  and $g$. Each scalar deformation is uniformly bounded on the strip, so
  the triangle inequality bounds the whole pairing by a finite sum of
  constants.
-/
theorem bddAbove_norm_complexInterpolationBilinearPairing
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (B : (α →₁ₛ[μ] ℂ) →ₗ[ℂ] ((β →₁ₛ[ν] ℂ) →ₗ[ℂ] ℂ))
    {r p₀ p₁ s q₀ q₁ : ℝ}
    (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hs : 0 < s) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (f : α →₁ₛ[μ] ℂ) (g : β →₁ₛ[ν] ℂ) :
    BddAbove
      ((norm ∘
          complexInterpolationBilinearPairing
            μ ν B r p₀ p₁ s q₀ q₁ f g) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  classical
  let strip : Set ℂ :=
    Complex.HadamardThreeLines.verticalClosedStrip 0 1
  have hfbound : ∀ c : ℂ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ strip,
        ‖complexInterpolationValue r p₀ p₁ z c‖ ≤ M := by
    intro c
    rcases bddAbove_def.mp
        (bddAbove_norm_complexInterpolationValue hr hp₀ hp₁ c) with
      ⟨M, hM⟩
    refine ⟨max M 0, le_max_right M 0, ?_⟩
    intro z hz
    exact (hM _ ⟨z, hz, rfl⟩).trans (le_max_left M 0)
  have hgbound : ∀ d : ℂ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ strip,
        ‖complexInterpolationValue s q₀ q₁ z d‖ ≤ M := by
    intro d
    rcases bddAbove_def.mp
        (bddAbove_norm_complexInterpolationValue hs hq₀ hq₁ d) with
      ⟨M, hM⟩
    refine ⟨max M 0, le_max_right M 0, ?_⟩
    intro z hz
    exact (hM _ ⟨z, hz, rfl⟩).trans (le_max_left M 0)
  choose Mf hMf0 hMf using hfbound
  choose Mg hMg0 hMg using hgbound
  rw [bddAbove_def]
  refine ⟨
    ∑ d ∈ (Lp.simpleFunc.toSimpleFunc g).range.filter (· ≠ 0),
      ∑ c ∈ (Lp.simpleFunc.toSimpleFunc f).range.filter (· ≠ 0),
        Mg d * Mf c *
          ‖B (integrableSimpleFuncFiberIndicator μ f c)
            (integrableSimpleFuncFiberIndicator ν g d)‖, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  simp only [Function.comp_apply]
  rw [complexInterpolationBilinearPairing_eq_sum]
  calc
    ‖∑ d ∈ (Lp.simpleFunc.toSimpleFunc g).range.filter (· ≠ 0),
        ∑ c ∈ (Lp.simpleFunc.toSimpleFunc f).range.filter (· ≠ 0),
          complexInterpolationValue s q₀ q₁ z d *
            complexInterpolationValue r p₀ p₁ z c *
              B (integrableSimpleFuncFiberIndicator μ f c)
                (integrableSimpleFuncFiberIndicator ν g d)‖
        ≤ ∑ d ∈ (Lp.simpleFunc.toSimpleFunc g).range.filter (· ≠ 0),
            ‖∑ c ∈ (Lp.simpleFunc.toSimpleFunc f).range.filter (· ≠ 0),
              complexInterpolationValue s q₀ q₁ z d *
                complexInterpolationValue r p₀ p₁ z c *
                  B (integrableSimpleFuncFiberIndicator μ f c)
                    (integrableSimpleFuncFiberIndicator ν g d)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ d ∈ (Lp.simpleFunc.toSimpleFunc g).range.filter (· ≠ 0),
          ∑ c ∈ (Lp.simpleFunc.toSimpleFunc f).range.filter (· ≠ 0),
            ‖complexInterpolationValue s q₀ q₁ z d *
              complexInterpolationValue r p₀ p₁ z c *
                B (integrableSimpleFuncFiberIndicator μ f c)
                  (integrableSimpleFuncFiberIndicator ν g d)‖ := by
          apply Finset.sum_le_sum
          intro d hd
          exact norm_sum_le _ _
    _ ≤ ∑ d ∈ (Lp.simpleFunc.toSimpleFunc g).range.filter (· ≠ 0),
          ∑ c ∈ (Lp.simpleFunc.toSimpleFunc f).range.filter (· ≠ 0),
            Mg d * Mf c *
              ‖B (integrableSimpleFuncFiberIndicator μ f c)
                (integrableSimpleFuncFiberIndicator ν g d)‖ := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro c hc
          rw [norm_mul, norm_mul]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul (hMg d z hz) (hMf c z hz)
            (norm_nonneg _) (hMg0 d)

/--
%%handwave
name:
  Three-lines estimate for an interpolated bilinear pairing
statement:
  Let $F(z)=B(f_z,g_z)$ be an interpolated bilinear pairing with positive
  deformation exponents. Suppose
  $$
    |F(it)|\leq A
    \quad\text{and}\quad
    |F(1+it)|\leq C
  $$
  for every $t\in\mathbb R$. Then for $0\leq\theta\leq1$,
  $$
    |F(\theta)|\leq A^{1-\theta}C^\theta.
  $$
proof:
  The pairing is entire and bounded on the closed strip by the finite-fiber
  expansion. Hadamard's three-lines theorem therefore applies with the two
  stated boundary bounds.
-/
theorem norm_complexInterpolationBilinearPairing_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (B : (α →₁ₛ[μ] ℂ) →ₗ[ℂ] ((β →₁ₛ[ν] ℂ) →ₗ[ℂ] ℂ))
    {r p₀ p₁ s q₀ q₁ θ A C : ℝ}
    (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hs : 0 < s) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (f : α →₁ₛ[μ] ℂ) (g : β →₁ₛ[ν] ℂ)
    (hleft : ∀ z : ℂ, z.re = 0 →
      ‖complexInterpolationBilinearPairing
        μ ν B r p₀ p₁ s q₀ q₁ f g z‖ ≤ A)
    (hright : ∀ z : ℂ, z.re = 1 →
      ‖complexInterpolationBilinearPairing
        μ ν B r p₀ p₁ s q₀ q₁ f g z‖ ≤ C) :
    ‖complexInterpolationBilinearPairing
      μ ν B r p₀ p₁ s q₀ q₁ f g (θ : ℂ)‖ ≤
        A ^ (1 - θ) * C ^ θ := by
  have hz :
      (θ : ℂ) ∈
        Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hθ
  have hd : DiffContOnCl ℂ
      (complexInterpolationBilinearPairing
        μ ν B r p₀ p₁ s q₀ q₁ f g)
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
    (differentiable_bilinearMap_complexInterpolationL1SimpleFunc
      μ ν B r p₀ p₁ s q₀ q₁ f g).diffContOnCl
  have hB := bddAbove_norm_complexInterpolationBilinearPairing
    μ ν B hr hp₀ hp₁ hs hq₀ hq₁ f g
  have hthree :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      (complexInterpolationBilinearPairing
        μ ν B r p₀ p₁ s q₀ q₁ f g)
      hz hd hB
      (fun z hz0 ↦ hleft z (by simpa using hz0))
      (fun z hz1 ↦ hright z (by simpa using hz1))
  simpa using hthree

/--
%%handwave
name:
  Bilinear Riesz--Thorin estimate for unit simple functions
statement:
  Let $B$ be a complex-bilinear pairing satisfying
  $$
    |B(u,v)|\leq A\|u\|_{p_0}\|v\|_{q_0},
    \qquad
    |B(u,v)|\leq C\|u\|_{p_1}\|v\|_{q_1}.
  $$
  Suppose $0\leq\theta\leq1$ and
  $$
    \frac1r=\frac{1-\theta}{p_0}+\frac\theta{p_1},
    \qquad
    \frac1s=\frac{1-\theta}{q_0}+\frac\theta{q_1}.
  $$
  If the integrable simple functions $f,g$ satisfy
  $\|f\|_r=\|g\|_s=1$, then
  $$
    |B(f,g)|\leq A^{1-\theta}C^\theta.
  $$
proof:
  Deform both unit functions analytically. Their norms equal one on each
  corresponding boundary line, so the endpoint estimates bound the
  bilinear pairing by $A$ and $C$. Apply the three-lines estimate and use
  the two reciprocal-exponent identities to recover $f$ and $g$ at
  $z=\theta$.
tags:
  milestone
-/
theorem norm_bilinearMap_le_of_lpNorm_eq_one
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (B : (α →₁ₛ[μ] ℂ) →ₗ[ℂ] ((β →₁ₛ[ν] ℂ) →ₗ[ℂ] ℂ))
    {r p₀ p₁ s q₀ q₁ θ A C : ℝ}
    (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hs : 0 < s) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / p₀ + θ / p₁)
    (hs_interp : s⁻¹ = (1 - θ) / q₀ + θ / q₁)
    (hleft : ∀ u v,
      ‖B u v‖ ≤
        A * lpNorm (u : α → ℂ) (ENNReal.ofReal p₀) μ *
          lpNorm (v : β → ℂ) (ENNReal.ofReal q₀) ν)
    (hright : ∀ u v,
      ‖B u v‖ ≤
        C * lpNorm (u : α → ℂ) (ENNReal.ofReal p₁) μ *
          lpNorm (v : β → ℂ) (ENNReal.ofReal q₁) ν)
    (f : α →₁ₛ[μ] ℂ) (g : β →₁ₛ[ν] ℂ)
    (hf : lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ = 1)
    (hg : lpNorm (g : β → ℂ) (ENNReal.ofReal s) ν = 1) :
    ‖B f g‖ ≤ A ^ (1 - θ) * C ^ θ := by
  have hthree := norm_complexInterpolationBilinearPairing_le
    μ ν B hr hp₀ hp₁ hs hq₀ hq₁ hθ f g
    (fun z hz ↦ by
      calc
        ‖complexInterpolationBilinearPairing
            μ ν B r p₀ p₁ s q₀ q₁ f g z‖ =
            ‖B (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f)
              (complexInterpolationL1SimpleFunc ν s q₀ q₁ z g)‖ := rfl
        _ ≤ A *
              lpNorm
                (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f :
                  α → ℂ)
                (ENNReal.ofReal p₀) μ *
              lpNorm
                (complexInterpolationL1SimpleFunc ν s q₀ q₁ z g :
                  β → ℂ)
                (ENNReal.ofReal q₀) ν :=
          hleft _ _
        _ = A := by
          rw [
            lpNorm_complexInterpolationL1SimpleFunc_eq_one_of_re_eq_zero
              μ hr hp₀ hp₁ f hf hz,
            lpNorm_complexInterpolationL1SimpleFunc_eq_one_of_re_eq_zero
              ν hs hq₀ hq₁ g hg hz]
          ring)
    (fun z hz ↦ by
      calc
        ‖complexInterpolationBilinearPairing
            μ ν B r p₀ p₁ s q₀ q₁ f g z‖ =
            ‖B (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f)
              (complexInterpolationL1SimpleFunc ν s q₀ q₁ z g)‖ := rfl
        _ ≤ C *
              lpNorm
                (complexInterpolationL1SimpleFunc μ r p₀ p₁ z f :
                  α → ℂ)
                (ENNReal.ofReal p₁) μ *
              lpNorm
                (complexInterpolationL1SimpleFunc ν s q₀ q₁ z g :
                  β → ℂ)
                (ENNReal.ofReal q₁) ν :=
          hright _ _
        _ = C := by
          rw [
            lpNorm_complexInterpolationL1SimpleFunc_eq_one_of_re_eq_one
              μ hr hp₀ hp₁ f hf hz,
            lpNorm_complexInterpolationL1SimpleFunc_eq_one_of_re_eq_one
              ν hs hq₀ hq₁ g hg hz]
          ring)
  rw [complexInterpolationBilinearPairing,
    complexInterpolationL1SimpleFunc_of_reciprocal_interpolation
      μ hr hr_interp f,
    complexInterpolationL1SimpleFunc_of_reciprocal_interpolation
      ν hs hs_interp g] at hthree
  exact hthree

/--
%%handwave
name:
  Bilinear Riesz--Thorin estimate on the integrable simple core
statement:
  Under the endpoint estimates and reciprocal-exponent identities of the
  unit-norm bilinear interpolation theorem, every pair of integrable simple
  functions satisfies
  $$
    |B(f,g)|\leq
      A^{1-\theta}C^\theta\|f\|_r\|g\|_s.
  $$
proof:
  If either seminorm vanishes, the corresponding simple-function class is
  zero. Otherwise divide each function by its positive seminorm, apply the
  unit-norm estimate, and rescale using bilinearity and homogeneity of the
  seminorm.
-/
theorem norm_bilinearMap_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (B : (α →₁ₛ[μ] ℂ) →ₗ[ℂ] ((β →₁ₛ[ν] ℂ) →ₗ[ℂ] ℂ))
    {r p₀ p₁ s q₀ q₁ θ A C : ℝ}
    (hr : 0 < r) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hs : 0 < s) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hr_interp : r⁻¹ = (1 - θ) / p₀ + θ / p₁)
    (hs_interp : s⁻¹ = (1 - θ) / q₀ + θ / q₁)
    (hleft : ∀ u v,
      ‖B u v‖ ≤
        A * lpNorm (u : α → ℂ) (ENNReal.ofReal p₀) μ *
          lpNorm (v : β → ℂ) (ENNReal.ofReal q₀) ν)
    (hright : ∀ u v,
      ‖B u v‖ ≤
        C * lpNorm (u : α → ℂ) (ENNReal.ofReal p₁) μ *
          lpNorm (v : β → ℂ) (ENNReal.ofReal q₁) ν)
    (f : α →₁ₛ[μ] ℂ) (g : β →₁ₛ[ν] ℂ) :
    ‖B f g‖ ≤
      (A ^ (1 - θ) * C ^ θ) *
        lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ *
          lpNorm (g : β → ℂ) (ENNReal.ofReal s) ν := by
  let nf : ℝ := lpNorm (f : α → ℂ) (ENNReal.ofReal r) μ
  let ng : ℝ := lpNorm (g : β → ℂ) (ENNReal.ofReal s) ν
  by_cases hnf : nf = 0
  · have hf_ae : (f : α → ℂ) =ᵐ[μ] 0 :=
      (lpNorm_eq_zero (memLp_integrableSimpleFunc μ hr f)
        (ENNReal.ofReal_ne_zero_iff.mpr hr)).mp hnf
    have hf0 : f = 0 := by
      apply Lp.simpleFunc.eq'
      apply AEEqFun.ext
      exact hf_ae.trans (Lp.coeFn_zero ℂ (1 : ENNReal) μ).symm
    rw [hf0, map_zero, LinearMap.zero_apply, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hC _))
        lpNorm_nonneg)
      lpNorm_nonneg
  by_cases hng : ng = 0
  · have hg_ae : (g : β → ℂ) =ᵐ[ν] 0 :=
      (lpNorm_eq_zero (memLp_integrableSimpleFunc ν hs g)
        (ENNReal.ofReal_ne_zero_iff.mpr hs)).mp hng
    have hg0 : g = 0 := by
      apply Lp.simpleFunc.eq'
      apply AEEqFun.ext
      exact hg_ae.trans (Lp.coeFn_zero ℂ (1 : ENNReal) ν).symm
    rw [hg0, LinearMap.map_zero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hC _))
        lpNorm_nonneg)
      lpNorm_nonneg
  let f' : α →₁ₛ[μ] ℂ := ((nf⁻¹ : ℝ) : ℂ) • f
  let g' : β →₁ₛ[ν] ℂ := ((ng⁻¹ : ℝ) : ℂ) • g
  have hnf0 : 0 ≤ nf := by
    exact lpNorm_nonneg
  have hng0 : 0 ≤ ng := by
    exact lpNorm_nonneg
  have hf' : lpNorm (f' : α → ℂ) (ENNReal.ofReal r) μ = 1 := by
    dsimp only [f']
    rw [lpNorm_smul_integrableSimpleFunc]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg hnf0]
    exact inv_mul_cancel₀ hnf
  have hg' : lpNorm (g' : β → ℂ) (ENNReal.ofReal s) ν = 1 := by
    dsimp only [g']
    rw [lpNorm_smul_integrableSimpleFunc]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg hng0]
    exact inv_mul_cancel₀ hng
  have hunit := norm_bilinearMap_le_of_lpNorm_eq_one
    μ ν B hr hp₀ hp₁ hs hq₀ hq₁ hθ hr_interp hs_interp
    hleft hright f' g' hf' hg'
  have hscaled :
      ng⁻¹ * (nf⁻¹ * ‖B f g‖) ≤ A ^ (1 - θ) * C ^ θ := by
    simpa only [f', g', map_smul, LinearMap.smul_apply, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg hnf0,
      abs_of_nonneg hng0, mul_assoc] using hunit
  change ‖B f g‖ ≤ (A ^ (1 - θ) * C ^ θ) * nf * ng
  calc
    ‖B f g‖ = (nf * ng) * (ng⁻¹ * (nf⁻¹ * ‖B f g‖)) := by
      field_simp
    _ ≤ (nf * ng) * (A ^ (1 - θ) * C ^ θ) :=
      mul_le_mul_of_nonneg_left hscaled (mul_nonneg hnf0 hng0)
    _ = (A ^ (1 - θ) * C ^ θ) * nf * ng := by ring

end

end HarmonicAnalysis

end JJMath
