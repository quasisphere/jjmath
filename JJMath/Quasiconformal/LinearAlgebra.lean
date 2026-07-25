import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Real-linear distortion in the complex plane

This file develops the pointwise linear algebra used by quasiconformal maps.
Every real-linear endomorphism of the complex plane has a unique decomposition

`L z = a * z + b * conj z`.

The two coefficients are its Wirtinger components.  The operator norm and
real determinant are respectively `‖a‖ + ‖b‖` and `‖a‖² - ‖b‖²`.
-/

namespace JJMath

open scoped ComplexConjugate

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Complex-linear Wirtinger coefficient
statement:
  For a real-linear map $L:\mathbb C\to\mathbb C$, define
  $$
    a(L)=\frac12\bigl(L(1)-iL(i)\bigr).
  $$
  When $L=Df$, this is the coefficient representing $\partial_zf$.
-/
def weakDZ (L : ℂ →L[ℝ] ℂ) : ℂ :=
  (1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I)

/--
%%handwave
name:
  Conjugate-linear Wirtinger coefficient
statement:
  For a real-linear map $L:\mathbb C\to\mathbb C$, define
  $$
    b(L)=\frac12\bigl(L(1)+iL(i)\bigr).
  $$
  When $L=Df$, this is the coefficient representing
  $\partial_{\bar z}f$.
-/
def weakDBar (L : ℂ →L[ℝ] ℂ) : ℂ :=
  (1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)

/--
%%handwave
name:
  Real Jacobian of a planar real-linear map
statement:
  For a real-linear map $L:\mathbb C\to\mathbb C$, define its Jacobian by
  $$
    J(L)=\det_{\mathbb R}L.
  $$
-/
def weakJacobian (L : ℂ →L[ℝ] ℂ) : ℝ :=
  LinearMap.det (L : ℂ →ₗ[ℝ] ℂ)

/--
%%handwave
name:
  Jacobian of a composition
statement:
  For real-linear maps $L,M:\mathbb C\to\mathbb C$,
  $$J(L\circ M)=J(L)J(M).$$
proof:
  Apply multiplicativity of the determinant.
-/
theorem weakJacobian_comp (L M : ℂ →L[ℝ] ℂ) :
    weakJacobian (L.comp M) = weakJacobian L * weakJacobian M := by
  exact LinearMap.det_comp (L : ℂ →ₗ[ℝ] ℂ) (M : ℂ →ₗ[ℝ] ℂ)

/--
%%handwave
name:
  Jacobian of the identity
statement:
  The identity map of the complex plane has real Jacobian $1$.
proof:
  The determinant of the identity is $1$.
-/
@[simp]
theorem weakJacobian_id :
    weakJacobian (ContinuousLinearMap.id ℝ ℂ) = 1 := by
  simp [weakJacobian]

/--
%%handwave
name:
  Real-linear map reconstructed from Wirtinger coefficients
statement:
  For $a,b\in\mathbb C$, define the real-linear map
  $$
    L_{a,b}(z)=az+b\overline z.
  $$
-/
def realLinearMapOfWirtinger (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  a • ContinuousLinearMap.id ℝ ℂ + b • Complex.conjCLE

/--
%%handwave
name:
  Real-affine map in Wirtinger form
statement:
  For $a,b,c\in\mathbb C$, define
  $$
    F_{a,b,c}(z)=az+b\overline z+c.
  $$
-/
def affineMap (a b c z : ℂ) : ℂ :=
  realLinearMapOfWirtinger a b z + c

/--
%%handwave
name:
  Continuity of the complex-linear Wirtinger component
statement:
  The assignment sending a real-linear endomorphism of $\mathbb C$ to its
  $z$ Wirtinger component is continuous in the operator norm.
proof:
  It is a fixed linear combination of evaluation at $1$ and at $i$.
-/
@[fun_prop]
theorem continuous_weakDZ :
    Continuous (weakDZ : (ℂ →L[ℝ] ℂ) → ℂ) := by
  unfold weakDZ
  fun_prop

/--
%%handwave
name:
  Continuity of the conjugate-linear Wirtinger component
statement:
  The assignment sending a real-linear endomorphism of $\mathbb C$ to its
  $\bar z$ Wirtinger component is continuous in the operator norm.
proof:
  It is a fixed linear combination of evaluation at $1$ and at $i$.
-/
@[fun_prop]
theorem continuous_weakDBar :
    Continuous (weakDBar : (ℂ →L[ℝ] ℂ) → ℂ) := by
  unfold weakDBar
  fun_prop

/--
%%handwave
name:
  Cauchy--Riemann equations from a vanishing conjugate Wirtinger component
statement:
  Let $L:\mathbb C\to\mathbb C$ be real-linear. If $L_{\bar z}=0$, then
  $$
    \operatorname{Re}L(1)=\operatorname{Im}L(i),
    \qquad
    \operatorname{Re}L(i)=-\operatorname{Im}L(1).
  $$
proof:
  Take real and imaginary parts in
  $2L_{\bar z}=L(1)+iL(i)=0$.
-/
theorem cauchyRiemann_of_weakDBar_eq_zero
    (L : ℂ →L[ℝ] ℂ) (h : weakDBar L = 0) :
    (L 1).re = (L Complex.I).im ∧
      (L Complex.I).re = -(L 1).im := by
  constructor
  · have hre := congrArg Complex.re h
    simp [weakDBar, Complex.mul_re, Complex.mul_im] at hre
    linarith
  · have him := congrArg Complex.im h
    simp [weakDBar, Complex.mul_re, Complex.mul_im] at him
    linarith

/--
%%handwave
name:
  Complex linearity from a vanishing conjugate Wirtinger component
statement:
  Let $L:\mathbb C\to\mathbb C$ be real-linear. If $L_{\bar z}=0$, then
  $$L(i)=iL(1).$$
proof:
  The equation $L_{\bar z}=0$ says $L(1)+iL(i)=0$. Multiplication by $-i$
  gives the asserted identity.
-/
theorem map_I_eq_I_smul_map_one_of_weakDBar_eq_zero
    (L : ℂ →L[ℝ] ℂ) (h : weakDBar L = 0) :
    L Complex.I = Complex.I • L (1 : ℂ) := by
  have hsum : L (1 : ℂ) + Complex.I * L Complex.I = 0 := by
    have hz := h
    simp only [weakDBar] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hIb : Complex.I * L Complex.I = -L (1 : ℂ) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hsum
  calc
    L Complex.I =
        (-Complex.I) * (Complex.I * L Complex.I) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I]
          ring
    _ = (-Complex.I) * (-L (1 : ℂ)) := by rw [hIb]
    _ = Complex.I • L (1 : ℂ) := by simp [smul_eq_mul]

/--
%%handwave
name:
  Continuous dependence on Wirtinger components
statement:
  The real-linear map $z\mapsto az+b\overline z$ depends continuously in
  operator norm on the pair $(a,b)\in\mathbb C^2$.
proof:
  Scalar multiplication and addition of continuous real-linear maps are
  continuous.
-/
@[fun_prop]
theorem continuous_uncurry_realLinearMapOfWirtinger :
    Continuous (Function.uncurry realLinearMapOfWirtinger) := by
  unfold realLinearMapOfWirtinger Function.uncurry
  fun_prop

/--
%%handwave
name:
  Differential of a real-affine complex map
statement:
  The real-affine map $z\mapsto az+b\overline z+c$ is differentiable at every
  point with real differential $\xi\mapsto a\xi+b\overline\xi$.
proof:
  A continuous real-linear map is its own derivative, and adding a constant
  does not change the derivative.
-/
theorem hasFDerivAt_affineMap (a b c z : ℂ) :
    HasFDerivAt (affineMap a b c) (realLinearMapOfWirtinger a b) z := by
  change HasFDerivAt
    (fun x : ℂ ↦ realLinearMapOfWirtinger a b x + c)
    (realLinearMapOfWirtinger a b) z
  exact ((realLinearMapOfWirtinger a b).hasFDerivAt (x := z)).add_const c

/--
%%handwave
name:
  Real-linear map from prescribed Wirtinger components
statement:
  The real-linear map determined by $a,b\in\mathbb C$ takes $\xi$ to
  $a\xi+b\overline\xi$.
proof:
  Expand the identity and conjugation continuous linear maps.
-/
@[simp]
theorem realLinearMapOfWirtinger_apply (a b ξ : ℂ) :
    realLinearMapOfWirtinger a b ξ = a * ξ + b * starRingEnd ℂ ξ := by
  simp [realLinearMapOfWirtinger]

/--
%%handwave
name:
  Prescribed complex-linear Wirtinger component
statement:
  The $z$ component of the map $\xi\mapsto a\xi+b\overline\xi$ is $a$.
proof:
  Evaluate the map at $1$ and $i$ in the definition of its $z$ component.
-/
@[simp]
theorem weakDZ_realLinearMapOfWirtinger (a b : ℂ) :
    weakDZ (realLinearMapOfWirtinger a b) = a := by
  have hI (x : ℂ) : Complex.I * (x * Complex.I) = -x := by
    calc
      Complex.I * (x * Complex.I) = x * (Complex.I * Complex.I) := by ring
      _ = -x := by rw [Complex.I_mul_I]; ring
  simp [weakDZ, realLinearMapOfWirtinger]
  simp only [mul_add, mul_neg, hI]
  ring

/--
%%handwave
name:
  Prescribed conjugate-linear Wirtinger component
statement:
  The $\bar z$ component of the map $\xi\mapsto a\xi+b\overline\xi$ is $b$.
proof:
  Evaluate the map at $1$ and $i$ in the definition of its $\bar z$ component.
-/
@[simp]
theorem weakDBar_realLinearMapOfWirtinger (a b : ℂ) :
    weakDBar (realLinearMapOfWirtinger a b) = b := by
  have hI (x : ℂ) : Complex.I * (x * Complex.I) = -x := by
    calc
      Complex.I * (x * Complex.I) = x * (Complex.I * Complex.I) := by ring
      _ = -x := by rw [Complex.I_mul_I]; ring
  simp [weakDBar, realLinearMapOfWirtinger]
  simp only [mul_add, mul_neg, hI]
  ring

/--
%%handwave
name:
  Real-linear Wirtinger decomposition
statement:
  Every real-linear map $L:\mathbb C\to\mathbb C$ satisfies
  $$L(\xi)=L_z\xi+L_{\bar z}\overline\xi$$
  for every $\xi\in\mathbb C$.
proof:
  Write $\xi=\operatorname{Re}(\xi)+\operatorname{Im}(\xi)i$, use real
  linearity, and substitute the definitions of $L_z$ and $L_{\bar z}$.
-/
theorem apply_eq_weakDZ_mul_add_weakDBar_mul_conj
    (L : ℂ →L[ℝ] ℂ) (ξ : ℂ) :
    L ξ = weakDZ L * ξ + weakDBar L * starRingEnd ℂ ξ := by
  have hξ : ξ = ξ.re • (1 : ℂ) + ξ.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hξ, map_add, map_smul, map_smul]
  simp [weakDZ, weakDBar, Complex.real_smul]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  <;> ring

/--
%%handwave
name:
  Wirtinger components determine a real-linear map
statement:
  Two real-linear endomorphisms of $\mathbb C$ with the same $z$ and
  $\bar z$ components are equal.
proof:
  Apply the real-linear Wirtinger decomposition to both maps at every complex
  number.
-/
theorem ext_weakDZ_weakDBar {L M : ℂ →L[ℝ] ℂ}
    (hz : weakDZ L = weakDZ M) (hbar : weakDBar L = weakDBar M) :
    L = M := by
  ext ξ
  rw [apply_eq_weakDZ_mul_add_weakDBar_mul_conj,
    apply_eq_weakDZ_mul_add_weakDBar_mul_conj, hz, hbar]

/--
%%handwave
name:
  Jacobian in Wirtinger coordinates
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ is real linear, then
  $$\det_{\mathbb R}L=|L_z|^2-|L_{\bar z}|^2.$$
proof:
  Write the matrix of $L$ on the real basis $(1,i)$ and expand its
  two-by-two determinant.
-/
theorem weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq
    (L : ℂ →L[ℝ] ℂ) :
    weakJacobian L = ‖weakDZ L‖ ^ 2 - ‖weakDBar L‖ ^ 2 := by
  rw [weakJacobian]
  calc
    LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) =
        (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (L : ℂ →ₗ[ℝ] ℂ)).det :=
      (LinearMap.det_toMatrix Complex.basisOneI (L : ℂ →ₗ[ℝ] ℂ)).symm
    _ = ‖weakDZ L‖ ^ 2 - ‖weakDBar L‖ ^ 2 := by
      rw [Matrix.det_fin_two]
      simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Complex.coe_basisOneI_repr]
      rw [Complex.sq_norm, Complex.sq_norm]
      simp [weakDZ, weakDBar, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im]
      ring

/--
%%handwave
name:
  Continuity of the planar Jacobian
statement:
  The assignment $L\mapsto J(L)$ on real-linear endomorphisms of
  $\mathbb C$ is continuous in the operator norm.
proof:
  Express the Jacobian as $|a|^2-|b|^2$ in terms of the two continuously
  varying Wirtinger coefficients $a,b$.
-/
@[fun_prop]
theorem continuous_weakJacobian : Continuous weakJacobian := by
  rw [show weakJacobian = fun L : ℂ →L[ℝ] ℂ ↦
      ‖weakDZ L‖ ^ 2 - ‖weakDBar L‖ ^ 2 by
    funext L
    exact weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq L]
  fun_prop

/--
%%handwave
name:
  Upper operator-norm bound from Wirtinger components
statement:
  For every real-linear $L:\mathbb C\to\mathbb C$,
  $$\|L\|_{\mathrm{op}}\le |L_z|+|L_{\bar z}|.$$
proof:
  Use the Wirtinger decomposition, the triangle inequality, and
  $|\overline z|=|z|$.
-/
theorem norm_le_norm_weakDZ_add_norm_weakDBar (L : ℂ →L[ℝ] ℂ) :
    ‖L‖ ≤ ‖weakDZ L‖ + ‖weakDBar L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro ξ
  rw [apply_eq_weakDZ_mul_add_weakDBar_mul_conj]
  calc
    ‖weakDZ L * ξ + weakDBar L * starRingEnd ℂ ξ‖
        ≤ ‖weakDZ L * ξ‖ + ‖weakDBar L * starRingEnd ℂ ξ‖ := norm_add_le _ _
    _ = (‖weakDZ L‖ + ‖weakDBar L‖) * ‖ξ‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      ring

/--
%%handwave
name:
  Lower metric bound from Wirtinger components
statement:
  For every real-linear map $L:\mathbb C\to\mathbb C$ and every
  $\xi\in\mathbb C$,
  $$
    \bigl(|\partial_zL|-|\partial_{\bar z}L|\bigr)|\xi|
      \leq |L(\xi)|.
  $$
proof:
  Use the Wirtinger decomposition and the reverse triangle inequality.
-/
theorem norm_weakDZ_sub_norm_weakDBar_mul_le
    (L : ℂ →L[ℝ] ℂ) (ξ : ℂ) :
    (‖weakDZ L‖ - ‖weakDBar L‖) * ‖ξ‖ ≤ ‖L ξ‖ := by
  rw [apply_eq_weakDZ_mul_add_weakDBar_mul_conj]
  calc
    (‖weakDZ L‖ - ‖weakDBar L‖) * ‖ξ‖ =
        ‖weakDZ L * ξ‖ - ‖weakDBar L * starRingEnd ℂ ξ‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      ring
    _ ≤ ‖weakDZ L * ξ + weakDBar L * starRingEnd ℂ ξ‖ :=
      norm_sub_le_norm_add _ _

/--
%%handwave
name:
  Conjugate-linear lower metric bound
statement:
  For every real-linear map $L:\mathbb C\to\mathbb C$ and every
  $\xi\in\mathbb C$,
  $$
    \bigl(|\partial_{\bar z}L|-|\partial_zL|\bigr)|\xi|
      \leq |L(\xi)|.
  $$
proof:
  Apply the reverse triangle inequality to the conjugate-linear and
  complex-linear terms in the Wirtinger decomposition.
-/
theorem norm_weakDBar_sub_norm_weakDZ_mul_le
    (L : ℂ →L[ℝ] ℂ) (ξ : ℂ) :
    (‖weakDBar L‖ - ‖weakDZ L‖) * ‖ξ‖ ≤ ‖L ξ‖ := by
  rw [apply_eq_weakDZ_mul_add_weakDBar_mul_conj]
  calc
    (‖weakDBar L‖ - ‖weakDZ L‖) * ‖ξ‖ =
        ‖weakDBar L * starRingEnd ℂ ξ‖ - ‖weakDZ L * ξ‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      ring
    _ ≤ ‖weakDBar L * starRingEnd ℂ ξ + weakDZ L * ξ‖ :=
      norm_sub_le_norm_add _ _
    _ = ‖weakDZ L * ξ + weakDBar L * starRingEnd ℂ ξ‖ := by
      rw [add_comm]

/--
%%handwave
name:
  Positive Jacobian separates the Wirtinger components
statement:
  If a real-linear map $L:\mathbb C\to\mathbb C$ has positive Jacobian,
  then
  $$
    |\partial_{\bar z}L|<|\partial_zL|.
  $$
proof:
  Since $J(L)=|\partial_zL|^2-|\partial_{\bar z}L|^2$, positivity of the
  Jacobian and nonnegativity of both norms give the strict inequality.
-/
theorem norm_weakDBar_lt_norm_weakDZ_of_weakJacobian_pos
    {L : ℂ →L[ℝ] ℂ} (hJ : 0 < weakJacobian L) :
    ‖weakDBar L‖ < ‖weakDZ L‖ := by
  rw [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] at hJ
  nlinarith [norm_nonneg (weakDZ L), norm_nonneg (weakDBar L)]

/--
%%handwave
name:
  Negative Jacobian reverses the Wirtinger dominance
statement:
  If a real-linear map $L:\mathbb C\to\mathbb C$ has negative Jacobian,
  then
  $$
    |\partial_zL|<|\partial_{\bar z}L|.
  $$
proof:
  Since $J(L)=|\partial_zL|^2-|\partial_{\bar z}L|^2$, negativity of the
  Jacobian and nonnegativity of both norms give the strict inequality.
-/
theorem norm_weakDZ_lt_norm_weakDBar_of_weakJacobian_neg
    {L : ℂ →L[ℝ] ℂ} (hJ : weakJacobian L < 0) :
    ‖weakDZ L‖ < ‖weakDBar L‖ := by
  rw [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] at hJ
  nlinarith [norm_nonneg (weakDZ L), norm_nonneg (weakDBar L)]

/--
%%handwave
name:
  Maximizing direction for a real-linear complex map
statement:
  For $a,b\in\mathbb C$, there is a nonzero $\xi\in\mathbb C$ such that
  $$|a\xi+b\overline\xi|=(|a|+|b|)|\xi|.$$
proof:
  The result is immediate if either coefficient vanishes. Otherwise choose
  $\xi$ with $\xi^2=b/a$; the two summands then point in the same direction.
-/
theorem exists_maximizing_direction (a b : ℂ) :
    ∃ ξ : ℂ, ξ ≠ 0 ∧
      ‖a * ξ + b * starRingEnd ℂ ξ‖ = (‖a‖ + ‖b‖) * ‖ξ‖ := by
  by_cases ha : a = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    simp [ha]
  by_cases hb : b = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    simp [hb]
  obtain ⟨ξ, hξpow⟩ :=
    IsAlgClosed.exists_pow_nat_eq (b / a) (show 0 < 2 by norm_num)
  have hdiv : b / a ≠ 0 := div_ne_zero hb ha
  have hξ : ξ ≠ 0 := by
    intro h
    apply hdiv
    simpa [h] using hξpow.symm
  have hbξ : b = a * ξ ^ 2 := by
    calc
      b = a * (b / a) := by field_simp
      _ = a * ξ ^ 2 := by rw [hξpow]
  have hnormb : ‖b‖ = ‖a‖ * ‖ξ‖ ^ 2 := by
    rw [hbξ, norm_mul, norm_pow]
  refine ⟨ξ, hξ, ?_⟩
  calc
    ‖a * ξ + b * starRingEnd ℂ ξ‖ =
        ‖a * ξ + a * ξ ^ 2 * starRingEnd ℂ ξ‖ := by rw [hbξ]
    _ = ‖(a * ξ) * (1 + ξ * starRingEnd ℂ ξ)‖ := by
      congr 1
      ring
    _ = ‖a * ξ‖ * ‖1 + ξ * starRingEnd ℂ ξ‖ := norm_mul _ _
    _ = (‖a‖ * ‖ξ‖) * (1 + ‖ξ‖ ^ 2) := by
      rw [norm_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      congr 1
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2)]
    _ = (‖a‖ + ‖b‖) * ‖ξ‖ := by
      rw [hnormb]
      ring

/--
%%handwave
name:
  Operator norm in Wirtinger coordinates
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ is real linear, then
  $$\|L\|_{\mathrm{op}}=|L_z|+|L_{\bar z}|.$$
proof:
  The triangle inequality gives the upper bound. For the reverse bound,
  evaluate $L$ on a nonzero direction where its complex-linear and
  conjugate-linear components point in the same direction.
-/
theorem norm_eq_norm_weakDZ_add_norm_weakDBar (L : ℂ →L[ℝ] ℂ) :
    ‖L‖ = ‖weakDZ L‖ + ‖weakDBar L‖ := by
  apply le_antisymm (norm_le_norm_weakDZ_add_norm_weakDBar L)
  obtain ⟨ξ, hξ, hmax⟩ :=
    exists_maximizing_direction (weakDZ L) (weakDBar L)
  have hop := L.le_opNorm ξ
  rw [apply_eq_weakDZ_mul_add_weakDBar_mul_conj, hmax] at hop
  exact le_of_mul_le_mul_right hop (norm_pos_iff.mpr hξ)

/--
%%handwave
name:
  Quadratic difference bound for the planar Jacobian
statement:
  For real-linear maps $L,M:\mathbb C\to\mathbb C$,
  $$
    |J(L)-J(M)|
      \leq 2\bigl(\|L\|_{\mathrm{op}}+\|M\|_{\mathrm{op}}\bigr)
        \|L-M\|_{\mathrm{op}}.
  $$
proof:
  Write $J(L)=|L_z|^2-|L_{\bar z}|^2$. For either Wirtinger component use
  $\bigl||a|^2-|b|^2\bigr|\leq(|a|+|b|)|a-b|$. Each component norm is at most the
  operator norm of the real-linear map, including for $L-M$, and summing the
  two estimates gives the stated bound.
-/
theorem abs_weakJacobian_sub_le (L M : ℂ →L[ℝ] ℂ) :
    |weakJacobian L - weakJacobian M| ≤
      2 * (‖L‖ + ‖M‖) * ‖L - M‖ := by
  have hsquare (a b : ℂ) :
      |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
    rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 =
      (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring]
    rw [abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b)
        (add_nonneg (norm_nonneg a) (norm_nonneg b))
  have hz_sub : weakDZ L - weakDZ M = weakDZ (L - M) := by
    simp [weakDZ]
    ring
  have hb_sub : weakDBar L - weakDBar M = weakDBar (L - M) := by
    simp [weakDBar]
    ring
  have hz_le (N : ℂ →L[ℝ] ℂ) : ‖weakDZ N‖ ≤ ‖N‖ := by
    rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hb_le (N : ℂ →L[ℝ] ℂ) : ‖weakDBar N‖ ≤ ‖N‖ := by
    rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
    exact le_add_of_nonneg_left (norm_nonneg _)
  rw [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq,
    weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq]
  have hrearrange :
      (‖weakDZ L‖ ^ 2 - ‖weakDBar L‖ ^ 2) -
          (‖weakDZ M‖ ^ 2 - ‖weakDBar M‖ ^ 2) =
        (‖weakDZ L‖ ^ 2 - ‖weakDZ M‖ ^ 2) -
          (‖weakDBar L‖ ^ 2 - ‖weakDBar M‖ ^ 2) := by ring
  rw [hrearrange]
  calc
    |(‖weakDZ L‖ ^ 2 - ‖weakDZ M‖ ^ 2) -
        (‖weakDBar L‖ ^ 2 - ‖weakDBar M‖ ^ 2)| ≤
        |‖weakDZ L‖ ^ 2 - ‖weakDZ M‖ ^ 2| +
          |‖weakDBar L‖ ^ 2 - ‖weakDBar M‖ ^ 2| := abs_sub _ _
    _ ≤ (‖weakDZ L‖ + ‖weakDZ M‖) * ‖weakDZ L - weakDZ M‖ +
          (‖weakDBar L‖ + ‖weakDBar M‖) *
            ‖weakDBar L - weakDBar M‖ :=
      add_le_add (hsquare _ _) (hsquare _ _)
    _ ≤ (‖L‖ + ‖M‖) * ‖L - M‖ +
          (‖L‖ + ‖M‖) * ‖L - M‖ := by
      apply add_le_add
      · apply mul_le_mul
        · exact add_le_add (hz_le L) (hz_le M)
        · rw [hz_sub]
          exact hz_le (L - M)
        · exact norm_nonneg _
        · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
      · apply mul_le_mul
        · exact add_le_add (hb_le L) (hb_le M)
        · rw [hb_sub]
          exact hb_le (L - M)
        · exact norm_nonneg _
        · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = 2 * (‖L‖ + ‖M‖) * ‖L - M‖ := by ring

/--
%%handwave
name:
  Algebraic form of the distortion conversion
statement:
  If $A,B\geq 0$ and $0\leq k<1$, then
  $$B\leq kA$$
  if and only if
  $$(A+B)^2\leq\frac{1+k}{1-k}(A^2-B^2).$$
proof:
  After multiplying by $1-k>0$, the difference of the right- and left-hand
  sides factors as $2(A+B)(kA-B)$.
-/
theorem distortion_algebra {A B k : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    B ≤ k * A ↔
      (A + B) ^ 2 ≤ ((1 + k) / (1 - k)) * (A ^ 2 - B ^ 2) := by
  have hden : 0 < 1 - k := sub_pos.mpr hk1
  constructor
  · intro h
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    have hprod : 0 ≤ (A + B) * (k * A - B) :=
      mul_nonneg (add_nonneg hA hB) (sub_nonneg.mpr h)
    nlinarith
  · intro h
    rw [div_mul_eq_mul_div, le_div_iff₀ hden] at h
    have hprod : 0 ≤ (A + B) * (k * A - B) := by nlinarith
    by_cases hab : A + B = 0
    · nlinarith
    · have habpos : 0 < A + B :=
        lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hab)
      rw [mul_comm] at hprod
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hprod habpos)

/--
%%handwave
name:
  Pointwise Beltrami bound is equivalent to metric distortion
statement:
  Let $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $0\leq k<1$. Then
  $$|L_{\bar z}|\leq k|L_z|$$
  if and only if
  $$\|L\|_{\mathrm{op}}^2\leq\frac{1+k}{1-k}\det_{\mathbb R}L.$$
proof:
  Substitute $\|L\|_{\mathrm{op}}=|L_z|+|L_{\bar z}|$ and
  $\det_{\mathbb R}L=|L_z|^2-|L_{\bar z}|^2$, then use the algebraic
  distortion conversion.
-/
theorem norm_weakDBar_le_iff_norm_sq_le_distortion
    (L : ℂ →L[ℝ] ℂ) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ‖weakDBar L‖ ≤ k * ‖weakDZ L‖ ↔
      ‖L‖ ^ 2 ≤ ((1 + k) / (1 - k)) * weakJacobian L := by
  rw [norm_eq_norm_weakDZ_add_norm_weakDBar,
    weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq]
  exact distortion_algebra (norm_nonneg _) (norm_nonneg _) hk0 hk1

/--
%%handwave
name:
  Metric distortion in terms of the Beltrami ratio
statement:
  Let $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $K\geq 1$. Then
  $$|L_{\bar z}|\leq\frac{K-1}{K+1}|L_z|$$
  if and only if
  $$\|L\|_{\mathrm{op}}^2\leq K\det_{\mathbb R}L.$$
proof:
  Apply the pointwise distortion equivalence with
  $k=(K-1)/(K+1)$ and simplify $(1+k)/(1-k)=K$.
-/
theorem norm_weakDBar_le_ratio_iff_norm_sq_le_mul_weakJacobian
    (L : ℂ →L[ℝ] ℂ) {K : ℝ} (hK : 1 ≤ K) :
    ‖weakDBar L‖ ≤ ((K - 1) / (K + 1)) * ‖weakDZ L‖ ↔
      ‖L‖ ^ 2 ≤ K * weakJacobian L := by
  have hKp : 0 < K + 1 := by linarith
  have hk0 : 0 ≤ (K - 1) / (K + 1) :=
    div_nonneg (sub_nonneg.mpr hK) hKp.le
  have hk1 : (K - 1) / (K + 1) < 1 :=
    (div_lt_one hKp).mpr (by linarith)
  have h := norm_weakDBar_le_iff_norm_sq_le_distortion L hk0 hk1
  have hfactor :
      (1 + (K - 1) / (K + 1)) / (1 - (K - 1) / (K + 1)) = K := by
    field_simp [ne_of_gt hKp]
    ring
  rw [hfactor] at h
  exact h

/--
%%handwave
name:
  Bounded distortion forces a nonnegative Jacobian
statement:
  Let $L:\mathbb C\to_{\mathbb R}\mathbb C$ and let $K>0$. If
  $$
    \|L\|_{\mathrm{op}}^2\le K\det_{\mathbb R}L,
  $$
  then $\det_{\mathbb R}L\ge0$.
proof:
  A negative Jacobian would make the right-hand side negative, while the
  squared operator norm on the left is nonnegative.
-/
theorem weakJacobian_nonneg_of_distortion
    (L : ℂ →L[ℝ] ℂ) {K : ℝ} (hK : 0 < K)
    (hdist : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    0 ≤ weakJacobian L := by
  by_contra hJ
  have hJneg : weakJacobian L < 0 := lt_of_not_ge hJ
  have hright : K * weakJacobian L < 0 :=
    mul_neg_of_pos_of_neg hK hJneg
  nlinarith [sq_nonneg ‖L‖]

/--
%%handwave
name:
  Zero-Jacobian branch of bounded distortion
statement:
  If a real-linear planar map $L$ satisfies
  $\|L\|_{\mathrm{op}}^2\le K\det_{\mathbb R}L$ and
  $\det_{\mathbb R}L=0$, then $L=0$.
proof:
  Substitution makes the nonnegative quantity
  $\|L\|_{\mathrm{op}}^2$ at most zero, so the operator norm vanishes.
-/
theorem eq_zero_of_weakJacobian_eq_zero_of_distortion
    (L : ℂ →L[ℝ] ℂ) {K : ℝ}
    (hdist : ‖L‖ ^ 2 ≤ K * weakJacobian L)
    (hJ : weakJacobian L = 0) :
    L = 0 := by
  rw [hJ, mul_zero] at hdist
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg L]

/--
%%handwave
name:
  Jacobian of an affine Wirtinger differential
statement:
  The real-linear map $\xi\mapsto a\xi+b\overline\xi$ has Jacobian
  $$|a|^2-|b|^2.$$
proof:
  Substitute its prescribed Wirtinger components into the Jacobian formula.
-/
@[simp]
theorem weakJacobian_realLinearMapOfWirtinger (a b : ℂ) :
    weakJacobian (realLinearMapOfWirtinger a b) = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq]
  simp

/--
%%handwave
name:
  Operator norm of an affine Wirtinger differential
statement:
  The real-linear map $\xi\mapsto a\xi+b\overline\xi$ has operator norm
  $$|a|+|b|.$$
proof:
  Substitute its prescribed Wirtinger components into the operator-norm
  formula.
-/
@[simp]
theorem norm_realLinearMapOfWirtinger (a b : ℂ) :
    ‖realLinearMapOfWirtinger a b‖ = ‖a‖ + ‖b‖ := by
  rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
  simp

/--
%%handwave
name:
  Composition in Wirtinger coordinates
statement:
  If $L(z)=az+b\overline z$ and $M(z)=cz+d\overline z$, then
  $$(L\circ M)(z)=(ac+b\overline d)z+(ad+b\overline c)\overline z.$$
proof:
  Substitute the formula for $M$, conjugate it, and collect the coefficients
  of $z$ and $\overline z$.
-/
theorem realLinearMapOfWirtinger_comp (a b c d : ℂ) :
    (realLinearMapOfWirtinger a b).comp (realLinearMapOfWirtinger c d) =
      realLinearMapOfWirtinger
        (a * c + b * starRingEnd ℂ d)
        (a * d + b * starRingEnd ℂ c) := by
  ext z
  simp [ContinuousLinearMap.comp_apply]
  ring

/--
%%handwave
name:
  Complex-linear precomposition of the complex Wirtinger component
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $M_a(z)=az$, then
  $$(L\circ M_a)_z=L_z a.$$
proof:
  Use the composition formula with the conjugate-linear component of $M_a$
  equal to zero.
-/
theorem weakDZ_comp_complexLinear (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    weakDZ (L.comp (realLinearMapOfWirtinger a 0)) = weakDZ L * a := by
  have hL : L = realLinearMapOfWirtinger (weakDZ L) (weakDBar L) :=
    ext_weakDZ_weakDBar (by simp) (by simp)
  rw [hL, realLinearMapOfWirtinger_comp]
  simp

/--
%%handwave
name:
  Complex-linear precomposition of the conjugate Wirtinger component
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $M_a(z)=az$, then
  $$(L\circ M_a)_{\bar z}=L_{\bar z}\overline a.$$
proof:
  Use the composition formula with the conjugate-linear component of $M_a$
  equal to zero.
-/
theorem weakDBar_comp_complexLinear (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    weakDBar (L.comp (realLinearMapOfWirtinger a 0)) =
      weakDBar L * starRingEnd ℂ a := by
  have hL : L = realLinearMapOfWirtinger (weakDZ L) (weakDBar L) :=
    ext_weakDZ_weakDBar (by simp) (by simp)
  rw [hL, realLinearMapOfWirtinger_comp]
  simp

/--
%%handwave
name:
  Complex-linear postcomposition of the complex Wirtinger component
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $M_a(z)=az$, then
  $$(M_a\circ L)_z=aL_z.$$
proof:
  Use the composition formula with the conjugate-linear component of $M_a$
  equal to zero.
-/
theorem weakDZ_complexLinear_comp (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    weakDZ ((realLinearMapOfWirtinger a 0).comp L) = a * weakDZ L := by
  have hL : L = realLinearMapOfWirtinger (weakDZ L) (weakDBar L) :=
    ext_weakDZ_weakDBar (by simp) (by simp)
  rw [hL, realLinearMapOfWirtinger_comp]
  simp

/--
%%handwave
name:
  Complex-linear postcomposition of the conjugate Wirtinger component
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $M_a(z)=az$, then
  $$(M_a\circ L)_{\bar z}=aL_{\bar z}.$$
proof:
  Use the composition formula with the conjugate-linear component of $M_a$
  equal to zero.
-/
theorem weakDBar_complexLinear_comp (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    weakDBar ((realLinearMapOfWirtinger a 0).comp L) = a * weakDBar L := by
  have hL : L = realLinearMapOfWirtinger (weakDZ L) (weakDBar L) :=
    ext_weakDZ_weakDBar (by simp) (by simp)
  rw [hL, realLinearMapOfWirtinger_comp]
  simp

/--
%%handwave
name:
  Right inverse of an orientation-preserving real-linear planar map
statement:
  Put $\Delta=a\overline a-b\overline b$. If $\Delta\ne0$, the map
  $$z\mapsto \frac{\overline a}{\Delta}z-
    \frac{b}{\Delta}\overline z$$
  is a right inverse of $z\mapsto az+b\overline z$.
proof:
  Substitute the two pairs of Wirtinger coefficients in the composition
  formula. The complex-linear coefficient becomes one and the
  conjugate-linear coefficient becomes zero.
-/
theorem realLinearMapOfWirtinger_comp_inverse (a b : ℂ)
    (hΔ : a * starRingEnd ℂ a - b * starRingEnd ℂ b ≠ 0) :
    (realLinearMapOfWirtinger a b).comp
      (realLinearMapOfWirtinger
        (starRingEnd ℂ a / (a * starRingEnd ℂ a - b * starRingEnd ℂ b))
        (-b / (a * starRingEnd ℂ a - b * starRingEnd ℂ b))) =
      ContinuousLinearMap.id ℝ ℂ := by
  rw [realLinearMapOfWirtinger_comp]
  ext z
  simp [ContinuousLinearMap.id_apply]
  have hΔ' : starRingEnd ℂ a * a - b * starRingEnd ℂ b ≠ 0 := by
    simpa [mul_comm] using hΔ
  field_simp [hΔ']
  ring

/--
%%handwave
name:
  Left inverse of an orientation-preserving real-linear planar map
statement:
  Put $\Delta=a\overline a-b\overline b$. If $\Delta\ne0$, the map
  $$z\mapsto \frac{\overline a}{\Delta}z-
    \frac{b}{\Delta}\overline z$$
  is a left inverse of $z\mapsto az+b\overline z$.
proof:
  Substitute the two pairs of Wirtinger coefficients in the composition
  formula. The complex-linear coefficient becomes one and the
  conjugate-linear coefficient becomes zero.
-/
theorem inverse_comp_realLinearMapOfWirtinger (a b : ℂ)
    (hΔ : a * starRingEnd ℂ a - b * starRingEnd ℂ b ≠ 0) :
    (realLinearMapOfWirtinger
        (starRingEnd ℂ a / (a * starRingEnd ℂ a - b * starRingEnd ℂ b))
        (-b / (a * starRingEnd ℂ a - b * starRingEnd ℂ b))).comp
      (realLinearMapOfWirtinger a b) = ContinuousLinearMap.id ℝ ℂ := by
  rw [realLinearMapOfWirtinger_comp]
  ext z
  simp [ContinuousLinearMap.id_apply]
  have hΔ' : starRingEnd ℂ a * a - b * starRingEnd ℂ b ≠ 0 := by
    simpa [mul_comm] using hΔ
  field_simp [hΔ']
  ring

/--
%%handwave
name:
  Orientation-preserving real-linear Wirtinger equivalence
statement:
  If $|a|^2-|b|^2>0$, define the continuous real-linear equivalence
  $$
    z\longmapsto az+b\overline z
  $$
  with inverse
  $$
    w\longmapsto
      \frac{\overline a}{|a|^2-|b|^2}w
      -\frac{b}{|a|^2-|b|^2}\overline w.
  $$
-/
def realLinearEquivOfWirtinger (a b : ℂ)
    (hJ : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2) : ℂ ≃L[ℝ] ℂ := by
  let Δ : ℂ := a * starRingEnd ℂ a - b * starRingEnd ℂ b
  have hΔ : Δ ≠ 0 := by
    dsimp [Δ]
    rw [Complex.mul_conj, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    linarith
  let f := realLinearMapOfWirtinger a b
  let g := realLinearMapOfWirtinger (starRingEnd ℂ a / Δ) (-b / Δ)
  exact ContinuousLinearEquiv.equivOfInverse f g
    (fun z ↦ by
      have h := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L z)
        (inverse_comp_realLinearMapOfWirtinger a b hΔ)
      simpa [f, g, Δ, ContinuousLinearMap.comp_apply] using h)
    (fun z ↦ by
      have h := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L z)
        (realLinearMapOfWirtinger_comp_inverse a b hΔ)
      simpa [f, g, Δ, ContinuousLinearMap.comp_apply] using h)

/--
%%handwave
name:
  Inverse of the real-linear Wirtinger equivalence
statement:
  If $|a|^2-|b|^2>0$ and $\Delta=a\overline a-b\overline b$, the inverse of
  $z\mapsto az+b\overline z$ is
  $$z\mapsto \frac{\overline a}{\Delta}z-
    \frac{b}{\Delta}\overline z.$$
proof:
  This is the explicit inverse used to construct the continuous real-linear
  equivalence.
-/
@[simp]
theorem realLinearEquivOfWirtinger_symm_apply (a b : ℂ)
    (hJ : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2) (z : ℂ) :
    (realLinearEquivOfWirtinger a b hJ).symm z =
      (starRingEnd ℂ a /
        (a * starRingEnd ℂ a - b * starRingEnd ℂ b)) * z +
      (-b / (a * starRingEnd ℂ a - b * starRingEnd ℂ b)) *
        starRingEnd ℂ z := by
  rfl

/--
%%handwave
name:
  Continuous real-linear map underlying the inverse Wirtinger equivalence
statement:
  If $|a|^2-|b|^2>0$ and $\Delta=a\overline a-b\overline b$, the continuous
  real-linear map underlying the inverse of $z\mapsto az+b\overline z$ is
  $$z\mapsto \frac{\overline a}{\Delta}z-
    \frac{b}{\Delta}\overline z.$$
proof:
  Apply the explicit inverse formula pointwise and use extensionality of
  continuous real-linear maps.
-/
theorem realLinearEquivOfWirtinger_symm_toContinuousLinearMap (a b : ℂ)
    (hJ : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2) :
    (realLinearEquivOfWirtinger a b hJ).symm.toContinuousLinearMap =
      realLinearMapOfWirtinger
        (starRingEnd ℂ a / (a * starRingEnd ℂ a - b * starRingEnd ℂ b))
        (-b / (a * starRingEnd ℂ a - b * starRingEnd ℂ b)) := by
  ext z
  exact realLinearEquivOfWirtinger_symm_apply a b hJ z

/--
%%handwave
name:
  Adjugate of a planar real-linear map
statement:
  If $L(z)=az+b\overline z$, define its real-linear adjugate by
  $$
    \operatorname{adj}(L)(z)=\overline a\,z-b\overline z.
  $$
-/
def realLinearAdjugate (L : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ :=
  realLinearMapOfWirtinger (starRingEnd ℂ (weakDZ L)) (-weakDBar L)

/--
%%handwave
name:
  Continuity of the planar adjugate
statement:
  The assignment $L\mapsto\operatorname{adj}(L)$ on real-linear
  endomorphisms of $\mathbb C$ is continuous in the operator norm.
proof:
  If $L(\xi)=a\xi+b\overline\xi$, then
  $\operatorname{adj}(L)(\xi)=\overline a\xi-b\overline\xi$; conjugation,
  negation, and reconstruction from the two coefficients are continuous.
-/
@[fun_prop]
theorem continuous_realLinearAdjugate :
    Continuous realLinearAdjugate := by
  unfold realLinearAdjugate
  fun_prop

/--
%%handwave
name:
  Operator norm of the planar adjugate
statement:
  Every real-linear endomorphism $L:\mathbb C\to\mathbb C$ satisfies
  $$\|\operatorname{adj}(L)\|_{\mathrm{op}}=\|L\|_{\mathrm{op}}.$$
proof:
  If $L(\xi)=a\xi+b\overline\xi$, the operator norms of $L$ and its
  adjugate are respectively $|a|+|b|$ and $|\overline a|+|-b|$.
-/
theorem norm_realLinearAdjugate (L : ℂ →L[ℝ] ℂ) :
    ‖realLinearAdjugate L‖ = ‖L‖ := by
  rw [realLinearAdjugate, norm_realLinearMapOfWirtinger,
    norm_eq_norm_weakDZ_add_norm_weakDBar, Complex.norm_conj, norm_neg]

/--
%%handwave
name:
  The adjugate composed with the original map
statement:
  For every real-linear endomorphism $L:\mathbb C\to\mathbb C$,
  $$\operatorname{adj}(L)\circ L=J(L)\operatorname{id}_{\mathbb C}.$$
proof:
  Write $L(\xi)=a\xi+b\overline\xi$ and multiply it by the map with
  coefficients $\overline a$ and $-b$. The conjugate-linear coefficient
  cancels, while the complex-linear coefficient is $|a|^2-|b|^2=J(L)$.
-/
theorem realLinearAdjugate_comp (L : ℂ →L[ℝ] ℂ) :
    (realLinearAdjugate L).comp L =
      weakJacobian L • ContinuousLinearMap.id ℝ ℂ := by
  have hL : L = realLinearMapOfWirtinger (weakDZ L) (weakDBar L) :=
    (ext_weakDZ_weakDBar (by simp) (by simp)).symm
  rw [hL, realLinearAdjugate, weakDZ_realLinearMapOfWirtinger,
    weakDBar_realLinearMapOfWirtinger, realLinearMapOfWirtinger_comp]
  have hsmul :
      weakJacobian (realLinearMapOfWirtinger (weakDZ L) (weakDBar L)) •
          ContinuousLinearMap.id ℝ ℂ =
        realLinearMapOfWirtinger
          (weakJacobian
            (realLinearMapOfWirtinger (weakDZ L) (weakDBar L))) 0 := by
    ext z
    simp
  rw [hsmul]
  apply ext_weakDZ_weakDBar
  · simp [weakJacobian_realLinearMapOfWirtinger]
    rw [mul_comm (starRingEnd ℂ (weakDZ L)) (weakDZ L),
      Complex.mul_conj, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    ring
  · simp
    ring

/--
%%handwave
name:
  The original map composed with its adjugate
statement:
  For every real-linear endomorphism $L:\mathbb C\to\mathbb C$,
  $$L\circ\operatorname{adj}(L)=J(L)\operatorname{id}_{\mathbb C}.$$
proof:
  Multiply the Wirtinger coefficients $a,b$ of $L$ by the coefficients
  $\overline a,-b$ of its adjugate. The conjugate-linear term cancels and
  the remaining coefficient is $|a|^2-|b|^2=J(L)$.
-/
theorem comp_realLinearAdjugate (L : ℂ →L[ℝ] ℂ) :
    L.comp (realLinearAdjugate L) =
      weakJacobian L • ContinuousLinearMap.id ℝ ℂ := by
  have hL : L = realLinearMapOfWirtinger (weakDZ L) (weakDBar L) :=
    (ext_weakDZ_weakDBar (by simp) (by simp)).symm
  rw [hL, realLinearAdjugate, weakDZ_realLinearMapOfWirtinger,
    weakDBar_realLinearMapOfWirtinger, realLinearMapOfWirtinger_comp]
  have hsmul :
      weakJacobian (realLinearMapOfWirtinger (weakDZ L) (weakDBar L)) •
          ContinuousLinearMap.id ℝ ℂ =
        realLinearMapOfWirtinger
          (weakJacobian
            (realLinearMapOfWirtinger (weakDZ L) (weakDBar L))) 0 := by
    ext z
    simp
  rw [hsmul]
  apply ext_weakDZ_weakDBar
  · simp [weakJacobian_realLinearMapOfWirtinger]
    rw [Complex.mul_conj, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    ring
  · simp
    ring

/--
%%handwave
name:
  Real coordinate of the planar adjugate
statement:
  For real-linear $L:\mathbb C\to\mathbb C$ and $v\in\mathbb C$,
  $$
    \operatorname{Re}(\operatorname{adj}(L)v)
      =\operatorname{Im}(L(i))\operatorname{Re}v
        -\operatorname{Re}(L(i))\operatorname{Im}v.
  $$
proof:
  Expand $L$ through its two Wirtinger coefficients and take real parts in
  the explicit adjugate formula.
-/
theorem real_part_realLinearAdjugate_apply (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    (realLinearAdjugate L v).re =
      (L Complex.I).im * v.re - (L Complex.I).re * v.im := by
  simp [realLinearAdjugate, realLinearMapOfWirtinger_apply,
    weakDZ, weakDBar, Complex.mul_re, Complex.mul_im]
  ring

/--
%%handwave
name:
  Imaginary coordinate of the planar adjugate
statement:
  For real-linear $L:\mathbb C\to\mathbb C$ and $v\in\mathbb C$,
  $$
    \operatorname{Im}(\operatorname{adj}(L)v)
      =-\operatorname{Im}(L(1))\operatorname{Re}v
        +\operatorname{Re}(L(1))\operatorname{Im}v.
  $$
proof:
  Expand the explicit adjugate formula through the two Wirtinger coefficients
  and take imaginary parts.
-/
theorem imag_part_realLinearAdjugate_apply (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    (realLinearAdjugate L v).im =
      -(L 1).im * v.re + (L 1).re * v.im := by
  simp [realLinearAdjugate, realLinearMapOfWirtinger_apply,
    weakDZ, weakDBar, Complex.mul_re, Complex.mul_im]
  ring

/--
%%handwave
name:
  Jacobian in Cartesian coordinates
statement:
  For a real-linear map $L:\mathbb C\to\mathbb C$,
  $$
    J(L)=\operatorname{Re}(L(1))\operatorname{Im}(L(i))
      -\operatorname{Re}(L(i))\operatorname{Im}(L(1)).
  $$
proof:
  Write the matrix of $L$ in the oriented real basis $(1,i)$ and expand its
  two-by-two determinant.
-/
theorem weakJacobian_eq_cartesian_coordinates (L : ℂ →L[ℝ] ℂ) :
    weakJacobian L =
      (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
  rw [weakJacobian]
  rw [← LinearMap.det_toMatrix Complex.basisOneI (L : ℂ →ₗ[ℝ] ℂ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr]

/--
%%handwave
name:
  Total Wirtinger pseudoinverse
statement:
  If $L(z)=az+b\overline z$ and
  $\Delta=|a|^2-|b|^2$, define the total real-linear inverse candidate
  $$
    L^\dagger(w)
      =\frac{\overline a}{\Delta}w
       -\frac b{\Delta}\overline w,
  $$
  using totalized division when $\Delta=0$. It agrees with $L^{-1}$ whenever
  $J(L)>0$.
-/
def realLinearPseudoInverse (L : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ :=
  let a := weakDZ L
  let b := weakDBar L
  let Δ := a * starRingEnd ℂ a - b * starRingEnd ℂ b
  realLinearMapOfWirtinger (starRingEnd ℂ a / Δ) (-b / Δ)

/--
%%handwave
name:
  Measurability of the Wirtinger pseudoinverse
statement:
  The total assignment $L\mapsto L^{\dagger}$ from real-linear endomorphisms
  of $\mathbb C$ to their Wirtinger pseudoinverses is measurable.
proof:
  Its two coefficients are obtained from the continuous Wirtinger components
  by conjugation, multiplication, subtraction, and totalized division, all of
  which are measurable operations.
-/
theorem measurable_realLinearPseudoInverse :
    Measurable realLinearPseudoInverse := by
  unfold realLinearPseudoInverse
  fun_prop

/--
%%handwave
name:
  The Wirtinger pseudoinverse is the inverse at positive Jacobian
statement:
  If a real-linear $L:\mathbb C\to\mathbb C$ has $J(L)>0$, its Wirtinger
  pseudoinverse is the continuous real-linear map underlying $L^{-1}$.
proof:
  Both maps have Wirtinger coefficients
  $\overline{L_z}/\Delta$ and $-L_{\bar z}/\Delta$, where
  $\Delta=|L_z|^2-|L_{\bar z}|^2$.
-/
theorem realLinearPseudoInverse_eq_symm_toContinuousLinearMap
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 < weakJacobian L) :
    realLinearPseudoInverse L =
      (realLinearEquivOfWirtinger (weakDZ L) (weakDBar L)
        (by simpa [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] using hJ)).symm.toContinuousLinearMap := by
  rw [realLinearEquivOfWirtinger_symm_toContinuousLinearMap]
  rfl

/--
%%handwave
name:
  The Wirtinger pseudoinverse is a left inverse at positive Jacobian
statement:
  If $J(L)>0$, then the Wirtinger pseudoinverse of $L$ satisfies
  $$L^{\dagger}\circ L=\operatorname{id}_{\mathbb C}.$$
proof:
  The Wirtinger determinant is nonzero, so substitute the explicit inverse
  coefficients and multiply the two real-linear maps.
-/
theorem realLinearPseudoInverse_comp_of_pos_weakJacobian
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 < weakJacobian L) :
    (realLinearPseudoInverse L).comp L = ContinuousLinearMap.id ℝ ℂ := by
  have hΔ : weakDZ L * starRingEnd ℂ (weakDZ L) -
      weakDBar L * starRingEnd ℂ (weakDBar L) ≠ 0 := by
    rw [Complex.mul_conj, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    simpa [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] using hJ.ne'
  let M : ℂ →L[ℝ] ℂ := realLinearPseudoInverse L
  have hL : L = realLinearMapOfWirtinger (weakDZ L) (weakDBar L) :=
    (ext_weakDZ_weakDBar (by simp) (by simp)).symm
  change M.comp L = _
  calc
    M.comp L = M.comp (realLinearMapOfWirtinger (weakDZ L) (weakDBar L)) :=
      congrArg M.comp hL
    _ = ContinuousLinearMap.id ℝ ℂ := by
      exact inverse_comp_realLinearMapOfWirtinger _ _ hΔ

/--
%%handwave
name:
  A positive-Jacobian map composed with its Wirtinger pseudoinverse
statement:
  If a real-linear $L:\mathbb C\to\mathbb C$ has $J(L)>0$, then
  $$L\circ L^{\dagger}=\operatorname{id}_{\mathbb C}.$$
proof:
  Identify $L$ with the continuous real-linear equivalence determined by its
  two Wirtinger coefficients and identify $L^{\dagger}$ with the continuous
  linear map underlying the inverse equivalence.
-/
theorem comp_realLinearPseudoInverse_of_pos_weakJacobian
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 < weakJacobian L) :
    L.comp (realLinearPseudoInverse L) = ContinuousLinearMap.id ℝ ℂ := by
  let E := realLinearEquivOfWirtinger (weakDZ L) (weakDBar L)
    (by
      simpa [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] using hJ)
  have hpseudo :
      realLinearPseudoInverse L = E.symm.toContinuousLinearMap :=
    realLinearPseudoInverse_eq_symm_toContinuousLinearMap L hJ
  have hL : L = E.toContinuousLinearMap := by
    change L = realLinearMapOfWirtinger (weakDZ L) (weakDBar L)
    exact (ext_weakDZ_weakDBar (by simp) (by simp)).symm
  rw [hpseudo, hL]
  ext z
  simp

/--
%%handwave
name:
  Adjugate as Jacobian times the inverse
statement:
  If $J(L)>0$, then
  $$\operatorname{adj}(L)=J(L)L^{\dagger}.$$
proof:
  Insert $L\circ L^{\dagger}=\operatorname{id}$ on the right of the
  adjugate and use
  $\operatorname{adj}(L)\circ L=J(L)\operatorname{id}$.
-/
theorem realLinearAdjugate_eq_weakJacobian_smul_realLinearPseudoInverse
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 < weakJacobian L) :
    realLinearAdjugate L =
      weakJacobian L • realLinearPseudoInverse L := by
  let M := realLinearPseudoInverse L
  calc
    realLinearAdjugate L =
        (realLinearAdjugate L).comp (ContinuousLinearMap.id ℝ ℂ) := by
          simp
    _ = (realLinearAdjugate L).comp (L.comp M) := by
          rw [comp_realLinearPseudoInverse_of_pos_weakJacobian L hJ]
    _ = ((realLinearAdjugate L).comp L).comp M := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = (weakJacobian L • ContinuousLinearMap.id ℝ ℂ).comp M := by
          rw [realLinearAdjugate_comp]
    _ = weakJacobian L • realLinearPseudoInverse L := by
          ext z
          simp [M]

/--
%%handwave
name:
  Beltrami cancellation under inverse composition
statement:
  Let $A,B:\mathbb C\to\mathbb C$ be real-linear, with $J(B)>0$. If
  $A_{\bar z}=\mu A_z$ and $B_{\bar z}=\mu B_z$, then
  $$
    \bigl(A\circ B^{-1}\bigr)_{\bar z}=0.
  $$
proof:
  First compose $A$ with the adjugate of $B$. Its conjugate-linear component
  is $-A_zB_{\bar z}+A_{\bar z}B_z=0$. Since
  $\operatorname{adj}(B)=J(B)B^{-1}$ and $J(B)\ne0$, the same component of
  $A\circ B^{-1}$ vanishes.
-/
theorem weakDBar_comp_realLinearPseudoInverse_eq_zero_of_same_beltrami
    (A B : ℂ →L[ℝ] ℂ) (μ : ℂ)
    (hJB : 0 < weakJacobian B)
    (hA : weakDBar A = μ * weakDZ A)
    (hB : weakDBar B = μ * weakDZ B) :
    weakDBar (A.comp (realLinearPseudoInverse B)) = 0 := by
  have hA' :
      A = realLinearMapOfWirtinger (weakDZ A) (weakDBar A) :=
    (ext_weakDZ_weakDBar (by simp) (by simp)).symm
  have hadj : weakDBar (A.comp (realLinearAdjugate B)) = 0 := by
    rw [hA', realLinearAdjugate, realLinearMapOfWirtinger_comp]
    simp only [weakDBar_realLinearMapOfWirtinger, map_neg]
    rw [hA, hB]
    simp
    ring
  have hrel :
      realLinearAdjugate B =
        weakJacobian B • realLinearPseudoInverse B :=
    realLinearAdjugate_eq_weakJacobian_smul_realLinearPseudoInverse B hJB
  have hcomp :
      A.comp (realLinearAdjugate B) =
        weakJacobian B • A.comp (realLinearPseudoInverse B) := by
    rw [hrel]
    ext z
    simp
  have hweakDBar_smul (r : ℝ) (L : ℂ →L[ℝ] ℂ) :
      weakDBar (r • L) = r • weakDBar L := by
    simp [weakDBar]
    ring
  have hscaled := congrArg weakDBar hcomp
  rw [hadj, hweakDBar_smul] at hscaled
  exact (smul_eq_zero.mp hscaled.symm).resolve_left hJB.ne'

/--
%%handwave
name:
  Adjugate-pseudoinverse identity under finite distortion
statement:
  Let $J(L)\geq0$ and suppose
  $\|L\|_{\mathrm{op}}^2\leq KJ(L)$. Then
  $$\operatorname{adj}(L)=J(L)L^{\dagger}.$$
proof:
  If $J(L)>0$, apply the positive-Jacobian adjugate identity. If $J(L)=0$,
  the distortion inequality and nonnegativity of the squared norm force
  $L=0$, so both sides vanish. This excludes the rank-one zero-Jacobian
  case, for which the identity would otherwise be false.
-/
theorem realLinearAdjugate_eq_weakJacobian_smul_realLinearPseudoInverse_of_nonneg
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 ≤ weakJacobian L) (K : ℝ)
    (hdist : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    realLinearAdjugate L =
      weakJacobian L • realLinearPseudoInverse L := by
  by_cases hzero : weakJacobian L = 0
  · have hnormsq : ‖L‖ ^ 2 = 0 := by
      apply le_antisymm
      · simpa [hzero] using hdist
      · positivity
    have hLzero : L = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg L]
    subst L
    ext z
    simp [realLinearAdjugate, weakJacobian, weakDZ, weakDBar]
  · exact
      realLinearAdjugate_eq_weakJacobian_smul_realLinearPseudoInverse L
        (lt_of_le_of_ne hJ (Ne.symm hzero))

/--
%%handwave
name:
  Reciprocal Jacobian of the Wirtinger pseudoinverse
statement:
  If $J(L)>0$, then
  $$J(L^{\dagger})J(L)=1.$$
proof:
  Take determinants in $L^{\dagger}\circ L=\operatorname{id}_{\mathbb C}$
  and use multiplicativity of the determinant.
-/
theorem weakJacobian_realLinearPseudoInverse_mul
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 < weakJacobian L) :
    weakJacobian (realLinearPseudoInverse L) * weakJacobian L = 1 := by
  have hdet := congrArg weakJacobian
    (realLinearPseudoInverse_comp_of_pos_weakJacobian L hJ)
  simpa [weakJacobian_comp] using hdet

/--
%%handwave
name:
  The Wirtinger pseudoinverse at zero Jacobian
statement:
  If $J(L)=0$, then the totalized Wirtinger pseudoinverse of $L$ is the zero
  real-linear map.
proof:
  Its denominator is
  $|L_z|^2-|L_{\bar z}|^2=J(L)$, so both coefficients are zero under the
  division-by-zero convention.
-/
theorem realLinearPseudoInverse_eq_zero_of_weakJacobian_eq_zero
    (L : ℂ →L[ℝ] ℂ) (hJ : weakJacobian L = 0) :
    realLinearPseudoInverse L = 0 := by
  have hΔ : weakDZ L * starRingEnd ℂ (weakDZ L) -
      weakDBar L * starRingEnd ℂ (weakDBar L) = 0 := by
    rw [Complex.mul_conj, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    simpa [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] using hJ
  simp only [realLinearPseudoInverse, hΔ, div_zero]
  ext z
  simp

/--
%%handwave
name:
  Norm of the positive Wirtinger determinant
statement:
  If $|a|^2-|b|^2>0$, then
  $$|a\overline a-b\overline b|=|a|^2-|b|^2.$$
proof:
  Both products with the complex conjugate are real norm squares, and the
  resulting real difference is positive.
-/
theorem norm_wirtingerDeterminant (a b : ℂ)
    (hJ : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2) :
    ‖a * starRingEnd ℂ a - b * starRingEnd ℂ b‖ =
      ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Real.norm_of_nonneg hJ.le]

/--
%%handwave
name:
  Metric distortion of the inverse Wirtinger equivalence
statement:
  Let $L(z)=az+b\overline z$ have positive Jacobian. If
  $\|L\|_{\mathrm{op}}^2\leq KJ(L)$, then its inverse satisfies
  $$\|L^{-1}\|_{\mathrm{op}}^2\leq KJ(L^{-1}).$$
proof:
  The inverse has Wirtinger coefficients $\overline a/\Delta$ and
  $-b/\Delta$, where $|\Delta|=|a|^2-|b|^2$. Substitute these coefficients
  into the exact norm and Jacobian formulas and clear the positive
  denominator.
-/
theorem distortion_realLinearEquivOfWirtinger_symm
    (a b : ℂ) (hJ : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2) (K : ℝ)
    (h : ‖realLinearMapOfWirtinger a b‖ ^ 2 ≤
      K * weakJacobian (realLinearMapOfWirtinger a b)) :
    ‖(realLinearEquivOfWirtinger a b hJ).symm.toContinuousLinearMap‖ ^ 2 ≤
      K * weakJacobian
        (realLinearEquivOfWirtinger a b hJ).symm.toContinuousLinearMap := by
  rw [realLinearEquivOfWirtinger_symm_toContinuousLinearMap,
    norm_realLinearMapOfWirtinger, weakJacobian_realLinearMapOfWirtinger] at ⊢
  rw [norm_realLinearMapOfWirtinger, weakJacobian_realLinearMapOfWirtinger] at h
  rw [Complex.norm_div, Complex.norm_div, Complex.norm_conj, norm_neg,
    norm_wirtingerDeterminant a b hJ]
  have hJne : ‖a‖ ^ 2 - ‖b‖ ^ 2 ≠ 0 := ne_of_gt hJ
  field_simp [hJne]
  nlinarith

/--
%%handwave
name:
  Metric distortion is preserved by inversion of a positive-Jacobian linear map
statement:
  Let $L:\mathbb C\to_{\mathbb R}\mathbb C$ have $J(L)>0$. If
  $\|L\|_{\mathrm{op}}^2\leq KJ(L)$, then the inverse of $L$ satisfies the
  same inequality with the same constant $K$.
proof:
  Decompose $L$ using its two Wirtinger derivatives and apply
  [the inverse Wirtinger equivalence has the same metric distortion](lean:JJMath.Quasiconformal.distortion_realLinearEquivOfWirtinger_symm).
-/
theorem distortion_inverse_of_pos_weakJacobian
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 < weakJacobian L) (K : ℝ)
    (h : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    ‖(realLinearEquivOfWirtinger (weakDZ L) (weakDBar L)
        (by simpa [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] using hJ)).symm.toContinuousLinearMap‖ ^ 2 ≤
      K * weakJacobian
        (realLinearEquivOfWirtinger (weakDZ L) (weakDBar L)
          (by simpa [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] using hJ)).symm.toContinuousLinearMap := by
  have hL : realLinearMapOfWirtinger (weakDZ L) (weakDBar L) = L :=
    ext_weakDZ_weakDBar (by simp) (by simp)
  have hcomponents : 0 < ‖weakDZ L‖ ^ 2 - ‖weakDBar L‖ ^ 2 := by
    simpa [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] using hJ
  apply distortion_realLinearEquivOfWirtinger_symm
    (weakDZ L) (weakDBar L) hcomponents K
  simpa [hL] using h

/--
%%handwave
name:
  Distortion bound for the Wirtinger pseudoinverse
statement:
  Let $J(L)\ge0$. If $\|L\|_{\mathrm{op}}^2\le KJ(L)$, then
  $$\|L^{\dagger}\|_{\mathrm{op}}^2\le KJ(L^{\dagger}).$$
proof:
  At positive Jacobian the pseudoinverse is the genuine inverse and inversion
  preserves the distortion bound. At zero Jacobian the pseudoinverse is the
  zero map.
-/
theorem distortion_realLinearPseudoInverse_of_nonneg_weakJacobian
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 ≤ weakJacobian L) (K : ℝ)
    (hdist : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    ‖realLinearPseudoInverse L‖ ^ 2 ≤
      K * weakJacobian (realLinearPseudoInverse L) := by
  by_cases hzero : weakJacobian L = 0
  · rw [realLinearPseudoInverse_eq_zero_of_weakJacobian_eq_zero L hzero]
    simp [weakJacobian]
  · have hpos : 0 < weakJacobian L := lt_of_le_of_ne hJ (Ne.symm hzero)
    have heq := realLinearPseudoInverse_eq_symm_toContinuousLinearMap L hpos
    have hinv := distortion_inverse_of_pos_weakJacobian L hpos K hdist
    rwa [← heq] at hinv

/--
%%handwave
name:
  Weighted norm bound for the Wirtinger pseudoinverse
statement:
  Let $J(L)>0$. If $\|L\|_{\mathrm{op}}^2\le KJ(L)$, then
  $$\|L^{\dagger}\|_{\mathrm{op}}^2J(L)\le K.$$
proof:
  The inverse distortion inequality gives
  $\|L^{\dagger}\|_{\mathrm{op}}^2\le KJ(L^{\dagger})$; multiply by
  $J(L)>0$ and use $J(L^{\dagger})J(L)=1$.
-/
theorem norm_sq_realLinearPseudoInverse_mul_weakJacobian_le
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 < weakJacobian L) (K : ℝ)
    (hdist : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    ‖realLinearPseudoInverse L‖ ^ 2 * weakJacobian L ≤ K := by
  have heq : realLinearPseudoInverse L =
      (realLinearEquivOfWirtinger (weakDZ L) (weakDBar L)
        (by simpa [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq] using hJ)).symm.toContinuousLinearMap :=
    realLinearPseudoInverse_eq_symm_toContinuousLinearMap L hJ
  have hinv := distortion_inverse_of_pos_weakJacobian L hJ K hdist
  rw [← heq] at hinv
  calc
    ‖realLinearPseudoInverse L‖ ^ 2 * weakJacobian L ≤
        (K * weakJacobian (realLinearPseudoInverse L)) * weakJacobian L :=
      mul_le_mul_of_nonneg_right hinv hJ.le
    _ = K := by
      rw [mul_assoc, weakJacobian_realLinearPseudoInverse_mul L hJ, mul_one]

/--
%%handwave
name:
  Weighted pseudoinverse bound at nonnegative Jacobian
statement:
  Let $K\ge0$ and $J(L)\ge0$. If
  $\|L\|_{\mathrm{op}}^2\le KJ(L)$, then
  $$\|L^{\dagger}\|_{\mathrm{op}}^2J(L)\le K.$$
proof:
  For positive Jacobian this is the inverse distortion estimate. At zero
  Jacobian the pseudoinverse is the zero map.
-/
theorem norm_sq_realLinearPseudoInverse_mul_weakJacobian_le_of_nonneg
    (L : ℂ →L[ℝ] ℂ) (hJ : 0 ≤ weakJacobian L) (K : ℝ) (hK : 0 ≤ K)
    (hdist : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    ‖realLinearPseudoInverse L‖ ^ 2 * weakJacobian L ≤ K := by
  by_cases hzero : weakJacobian L = 0
  · rw [realLinearPseudoInverse_eq_zero_of_weakJacobian_eq_zero L hzero,
      hzero]
    simpa using hK
  · exact norm_sq_realLinearPseudoInverse_mul_weakJacobian_le L
      (lt_of_le_of_ne hJ (Ne.symm hzero)) K hdist

/--
%%handwave
name:
  Operator norm under complex-linear precomposition
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $M_a(z)=az$, then
  $$\|L\circ M_a\|_{\mathrm{op}}=|a|\,\|L\|_{\mathrm{op}}.$$
proof:
  Substitute the transformed Wirtinger components into the operator-norm
  formula and use $|\overline a|=|a|$.
-/
theorem norm_comp_complexLinear (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    ‖L.comp (realLinearMapOfWirtinger a 0)‖ = ‖a‖ * ‖L‖ := by
  rw [norm_eq_norm_weakDZ_add_norm_weakDBar,
    weakDZ_comp_complexLinear, weakDBar_comp_complexLinear,
    norm_mul, norm_mul, Complex.norm_conj,
    norm_eq_norm_weakDZ_add_norm_weakDBar]
  ring

/--
%%handwave
name:
  Operator norm under complex-linear postcomposition
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $M_a(z)=az$, then
  $$\|M_a\circ L\|_{\mathrm{op}}=|a|\,\|L\|_{\mathrm{op}}.$$
proof:
  Substitute the transformed Wirtinger components into the operator-norm
  formula.
-/
theorem norm_complexLinear_comp (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    ‖(realLinearMapOfWirtinger a 0).comp L‖ = ‖a‖ * ‖L‖ := by
  rw [norm_eq_norm_weakDZ_add_norm_weakDBar,
    weakDZ_complexLinear_comp, weakDBar_complexLinear_comp,
    norm_mul, norm_mul,
    norm_eq_norm_weakDZ_add_norm_weakDBar]
  ring

/--
%%handwave
name:
  Jacobian under complex-linear precomposition
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $M_a(z)=az$, then
  $$J(L\circ M_a)=|a|^2J(L).$$
proof:
  Substitute the transformed Wirtinger components into the Jacobian formula
  and use $|\overline a|=|a|$.
-/
theorem weakJacobian_comp_complexLinear (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    weakJacobian (L.comp (realLinearMapOfWirtinger a 0)) =
      ‖a‖ ^ 2 * weakJacobian L := by
  rw [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq,
    weakDZ_comp_complexLinear, weakDBar_comp_complexLinear,
    norm_mul, norm_mul, Complex.norm_conj,
    weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq]
  ring

/--
%%handwave
name:
  Jacobian under complex-linear postcomposition
statement:
  If $L:\mathbb C\to_{\mathbb R}\mathbb C$ and $M_a(z)=az$, then
  $$J(M_a\circ L)=|a|^2J(L).$$
proof:
  Substitute the transformed Wirtinger components into the Jacobian formula.
-/
theorem weakJacobian_complexLinear_comp (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    weakJacobian ((realLinearMapOfWirtinger a 0).comp L) =
      ‖a‖ ^ 2 * weakJacobian L := by
  rw [weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq,
    weakDZ_complexLinear_comp, weakDBar_complexLinear_comp,
    norm_mul, norm_mul,
    weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq]
  ring

/--
%%handwave
name:
  Metric distortion is invariant under complex-linear precomposition
statement:
  If a real-linear map $L:\mathbb C\to_{\mathbb R}\mathbb C$ satisfies
  $\|L\|_{\mathrm{op}}^2\leq KJ(L)$, then for every $a\in\mathbb C$,
  $$
  \|L\circ M_a\|_{\mathrm{op}}^2\leq KJ(L\circ M_a),
  \qquad M_a(z)=az.
  $$
proof:
  Complex-linear precomposition multiplies both the squared operator norm and
  the real Jacobian by $|a|^2$.
-/
theorem distortion_comp_complexLinear
    (L : ℂ →L[ℝ] ℂ) (a : ℂ) (K : ℝ)
    (h : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    ‖L.comp (realLinearMapOfWirtinger a 0)‖ ^ 2 ≤
      K * weakJacobian (L.comp (realLinearMapOfWirtinger a 0)) := by
  rw [norm_comp_complexLinear, weakJacobian_comp_complexLinear]
  calc
    (‖a‖ * ‖L‖) ^ 2 = ‖a‖ ^ 2 * ‖L‖ ^ 2 := by ring
    _ ≤ ‖a‖ ^ 2 * (K * weakJacobian L) := by
      exact mul_le_mul_of_nonneg_left h (sq_nonneg ‖a‖)
    _ = K * (‖a‖ ^ 2 * weakJacobian L) := by ring

/--
%%handwave
name:
  Metric distortion is invariant under complex-linear postcomposition
statement:
  If a real-linear map $L:\mathbb C\to_{\mathbb R}\mathbb C$ satisfies
  $\|L\|_{\mathrm{op}}^2\leq KJ(L)$, then for every $a\in\mathbb C$,
  $$
  \|M_a\circ L\|_{\mathrm{op}}^2\leq KJ(M_a\circ L),
  \qquad M_a(z)=az.
  $$
proof:
  Complex-linear postcomposition multiplies both the squared operator norm and
  the real Jacobian by $|a|^2$.
-/
theorem distortion_complexLinear_comp
    (L : ℂ →L[ℝ] ℂ) (a : ℂ) (K : ℝ)
    (h : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    ‖(realLinearMapOfWirtinger a 0).comp L‖ ^ 2 ≤
      K * weakJacobian ((realLinearMapOfWirtinger a 0).comp L) := by
  rw [norm_complexLinear_comp, weakJacobian_complexLinear_comp]
  calc
    (‖a‖ * ‖L‖) ^ 2 = ‖a‖ ^ 2 * ‖L‖ ^ 2 := by ring
    _ ≤ ‖a‖ ^ 2 * (K * weakJacobian L) := by
      exact mul_le_mul_of_nonneg_left h (sq_nonneg ‖a‖)
    _ = K * (‖a‖ ^ 2 * weakJacobian L) := by ring

end

end Quasiconformal

end JJMath
