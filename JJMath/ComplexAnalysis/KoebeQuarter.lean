import JJMath.ComplexAnalysis.GronwallAreaCore
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Grönwall's area theorem and the Koebe quarter theorem

This file proves the first-coefficient form of Grönwall's area theorem and
deduces the Koebe quarter theorem.  The two distinguished Fourier modes in
the area calculation are isolated by Bessel's inequality.  A planar
chain-level specialization records the corresponding Stokes identity; the
positive area estimate itself uses the Jacobian change-of-variables theorem.
-/

open scoped ENNReal Interval Topology Manifold ContDiff
open Filter MeasureTheory Metric Set Topology
open JJMath.Manifold

noncomputable section

namespace JJMath.ComplexAnalysis

set_option backward.isDefEq.respectTransparency false

/--
%%handwave
name:
  Planar Stokes identity for a two-chain
statement:
  Let $\omega$ be a continuously differentiable real $1$-form on
  $\mathbb C$, and let $c$ be a smooth singular $2$-chain. Then
  \[
    \int_{\partial c}\omega=\int_c d\omega.
  \]
proof:
  [Stokes' theorem identifies integration of a differential form over the boundary of a chain with integration of its exterior derivative over the chain](lean:JJMath.Manifold.integrateChain_boundary_eq_integrateChain_exteriorDerivative). Specialize it to real differential forms of degree $1$ on the complex plane.
-/
theorem planar_annulus_stokes_identity
    (omega : C1DifferentialForm (I := 𝓘(ℝ, ℂ)) (M := ℂ) (F := ℝ) 1)
    (c : SingularChain (I := 𝓘(ℝ, ℂ)) (M := ℂ) 2 (⊤ : WithTop ℕ∞)) :
    integrateChain (I := 𝓘(ℝ, ℂ)) (F := ℝ)
        (pullbackSimplexIntegrationTheory (I := 𝓘(ℝ, ℂ)) (M := ℂ) (F := ℝ))
        (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) by simp)
        (DifferentialForm.toContinuous (I := 𝓘(ℝ, ℂ)) (M := ℂ) (F := ℝ) (n := 1) omega)
        (boundary (I := 𝓘(ℝ, ℂ)) c) =
      integrateChain (I := 𝓘(ℝ, ℂ)) (F := ℝ)
        (pullbackSimplexIntegrationTheory (I := 𝓘(ℝ, ℂ)) (M := ℂ) (F := ℝ))
        (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) by simp)
        (exteriorDerivative (I := 𝓘(ℝ, ℂ)) (r := (0 : WithTop ℕ∞)) omega) c := by
  simpa using integrateChain_boundary_eq_integrateChain_exteriorDerivative
    (I := 𝓘(ℝ, ℂ)) (M := ℂ) (F := ℝ) (k := 1) (r := (⊤ : WithTop ℕ∞))
    (show (2 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) by simp) omega c

/--
%%handwave
name: Two-mode Fourier energy bound
statement:
  If $F:[0,2\pi]\to\mathbb C$ is continuous and $\widehat F(n)=(2\pi)^{-1}\int_0^{2\pi}e^{-int}F(t)\,dt$, then $|\widehat F(0)|^2+|\widehat F(2)|^2\le(2\pi)^{-1}\int_0^{2\pi}|F(t)|^2\,dt$.
proof:
  Continuity makes $F$ square-integrable. Apply Parseval's identity and retain only the nonnegative summands with indices $0$ and $2$.
-/
private theorem two_fourier_coeff_sq_le_average
    {F : ℝ → ℂ} (hF : Continuous F) :
    ‖fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) F 0‖ ^ 2 +
        ‖fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) F 2‖ ^ 2 ≤
      (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, ‖F t‖ ^ 2 := by
  let hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hL2 : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    rcases isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn with ⟨C, hC⟩
    refine MemLp.of_bound hF.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x ⟨hx.1.le, hx.2⟩
  have hs := hasSum_sq_fourierCoeffOn hp hL2
  have hsum := Summable.sum_le_tsum ({0, 2} : Finset ℤ)
    (fun _ _ ↦ sq_nonneg _) hs.summable
  rw [hs.tsum_eq] at hsum
  simpa [hp, Finset.sum_insert, show (0 : ℤ) ≠ 2 by norm_num, smul_eq_mul] using hsum

private def reciprocalCircle (s t : ℝ) : ℂ :=
  (s : ℂ)⁻¹ * Complex.exp ((t : ℂ) * Complex.I)

private def exteriorCircleDerivative (b : ℂ) (h : ℂ → ℂ) (s t : ℝ) : ℂ :=
  1 - b * reciprocalCircle s t ^ 2 -
    deriv h (reciprocalCircle s t) * reciprocalCircle s t ^ 2

/--
%%handwave
name: Norm of the reciprocal-circle parametrization
statement:
  For $s>0$ and $t\in\mathbb R$, the point $s^{-1}e^{it}$ has modulus $s^{-1}$.
proof:
  Use $|e^{it}|=1$ and positivity of $s$.
-/
private theorem norm_reciprocalCircle {s t : ℝ} (hs : 0 < s) :
    ‖reciprocalCircle s t‖ = s⁻¹ := by
  simp [reciprocalCircle, Complex.norm_exp, Complex.mul_re, hs.le]

/--
%%handwave
name: Continuity of the exterior derivative along a circle
statement:
  Let $h$ be holomorphic on the unit disk and $s>1$. For $w(t)=s^{-1}e^{it}$, the function $t\mapsto1-bw(t)^2-h'(w(t))w(t)^2$ is continuous on $\mathbb R$.
proof:
  The circle parametrization is continuous and lies in the unit disk. The derivative $h'$ is continuous there, and sums and products preserve continuity.
-/
private theorem continuous_exteriorCircleDerivative
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    {s : ℝ} (hs : 1 < s) :
    Continuous (exteriorCircleDerivative b h s) := by
  have hw : Continuous (reciprocalCircle s) := by
    unfold reciprocalCircle
    fun_prop
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hwmem : ∀ t, reciprocalCircle s t ∈ ball (0 : ℂ) 1 := by
    intro t
    rw [mem_ball_zero_iff, norm_reciprocalCircle hs0]
    exact inv_lt_one₀ hs0 |>.2 hs
  have hd : Continuous (fun t ↦ deriv h (reciprocalCircle s t)) := by
    simpa [Function.comp_def] using hh.deriv.continuousOn.comp_continuous hw hwmem
  unfold exteriorCircleDerivative
  fun_prop

/--
%%handwave
name: Constant Fourier mode of the exterior derivative
statement:
  Let $h$ be holomorphic on the unit disk and $s>1$. The zeroth Fourier coefficient of $1-bw(t)^2-h'(w(t))w(t)^2$, where $w(t)=s^{-1}e^{it}$, is $1$.
proof:
  This integrand is the restriction to $|w|=s^{-1}$ of the holomorphic function $1-bw^2-h'(w)w^2$. Its circle average is its value at $0$, namely $1$.
-/
private theorem exteriorCircleDerivative_fourierCoeff_zero
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    {s : ℝ} (hs : 1 < s) :
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi)
      (exteriorCircleDerivative b h s) 0 = 1 := by
  let φ : ℂ → ℂ := fun w ↦ 1 - b * w ^ 2 - deriv h w * w ^ 2
  have hφ : AnalyticOnNhd ℂ φ (ball 0 1) := by
    exact analyticOnNhd_const.sub (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2)) |>.sub
      (hh.deriv.mul (analyticOnNhd_id.pow 2))
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hinv0 : 0 < s⁻¹ := inv_pos.mpr hs0
  have hclosed : closure (ball (0 : ℂ) s⁻¹) ⊆ ball 0 1 := by
    rw [show closure (ball (0 : ℂ) s⁻¹) = closedBall 0 s⁻¹ by
      exact closure_ball (0 : ℂ) hinv0.ne']
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    exact hz.trans_lt ((inv_lt_one₀ hs0).2 hs)
  have havg : Real.circleAverage φ 0 s⁻¹ = φ 0 := by
    have hdiff : DiffContOnCl ℂ φ (ball 0 |s⁻¹|) := by
      simpa [abs_of_pos hinv0] using
        (hφ.differentiableOn.mono hclosed).diffContOnCl
    exact hdiff.circleAverage
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_coe_apply, Int.cast_zero, mul_zero, zero_mul, zero_div,
    Complex.exp_zero, one_smul]
  rw [Real.circleAverage_def] at havg
  have hparam : ∀ t : ℝ, circleMap 0 s⁻¹ t = reciprocalCircle s t := by
    intro t
    simp [circleMap_zero, reciprocalCircle]
  simp only [hparam] at havg
  simpa [φ, exteriorCircleDerivative, reciprocalCircle, smul_eq_mul] using havg

/--
%%handwave
name: Vanishing integral of the second negative Fourier mode
statement:
  One has $\int_0^{2\pi}e^{-2it}\,dt=0$.
proof:
  Integrate the derivative relation $(e^{-2it})'=-2i e^{-2it}$ and use the equality of the endpoint values.
-/
private theorem integral_exp_neg_two_mul_I :
    ∫ t in (0 : ℝ)..2 * Real.pi,
      Complex.exp ((-2 : ℂ) * (t : ℂ) * Complex.I) = 0 := by
  let e : ℝ → ℂ := fun t ↦ Complex.exp ((-2 : ℂ) * (t : ℂ) * Complex.I)
  have he : ∀ t : ℝ, HasDerivAt e (((-2 : ℂ) * Complex.I) * e t) t := by
    intro t
    have hinner : HasDerivAt (fun z : ℂ ↦ (-2 : ℂ) * z * Complex.I)
        ((-2 : ℂ) * Complex.I) (t : ℂ) := by
      convert ((hasDerivAt_const (t : ℂ) (-2 : ℂ)).mul (hasDerivAt_id (t : ℂ))).mul_const
        Complex.I using 1 <;> ring
    convert ((Complex.hasDerivAt_exp _).comp (t : ℂ) hinner).comp_ofReal using 1;
      simp [e] <;> ring
  have hint : IntervalIntegrable (fun t : ℝ ↦ ((-2 : ℂ) * Complex.I) * e t)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold e
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ he t) hint
  have hpull :
      (∫ t in (0 : ℝ)..2 * Real.pi, ((-2 : ℂ) * Complex.I) * e t) =
        ((-2 : ℂ) * Complex.I) * ∫ t in (0 : ℝ)..2 * Real.pi, e t :=
    intervalIntegral.integral_const_mul _ _
  rw [hpull] at hFTC
  have hend : e (2 * Real.pi) = e 0 := by
    simp [e, Complex.exp_eq_one_iff]
    exact ⟨-2, by push_cast; ring⟩
  rw [hend, sub_self, mul_eq_zero] at hFTC
  rcases hFTC with hzero | hzero
  · norm_num [Complex.I_ne_zero] at hzero
  · exact hzero

/--
%%handwave
name: Second Fourier mode of the exterior derivative
statement:
  Let $h$ be holomorphic on the unit disk with $h'(0)=0$, and let $s>1$. The second Fourier coefficient of $1-bw(t)^2-h'(w(t))w(t)^2$, where $w(t)=s^{-1}e^{it}$, is $-b/s^2$.
proof:
  Multiplication by $e^{-2it}$ turns the $bw(t)^2$ term into the constant $b/s^2$. The pure exponential integrates to zero, while the mean-value theorem applied to $h'$ makes its remaining circle average equal to $h'(0)=0$.
-/
private theorem exteriorCircleDerivative_fourierCoeff_two
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (h1 : deriv h 0 = 0) {s : ℝ} (hs : 1 < s) :
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi)
      (exteriorCircleDerivative b h s) 2 = -b / (s : ℂ) ^ 2 := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hinv0 : 0 < s⁻¹ := inv_pos.mpr hs0
  have hclosed : closure (ball (0 : ℂ) s⁻¹) ⊆ ball 0 1 := by
    rw [show closure (ball (0 : ℂ) s⁻¹) = closedBall 0 s⁻¹ by
      exact closure_ball (0 : ℂ) hinv0.ne']
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    exact hz.trans_lt ((inv_lt_one₀ hs0).2 hs)
  have havg : Real.circleAverage (deriv h) 0 s⁻¹ = 0 := by
    have hdiff : DiffContOnCl ℂ (deriv h) (ball 0 |s⁻¹|) := by
      simpa [abs_of_pos hinv0] using
        (hh.deriv.differentiableOn.mono hclosed).diffContOnCl
    simpa [h1] using hdiff.circleAverage
  have hparam : ∀ t : ℝ, circleMap 0 s⁻¹ t = reciprocalCircle s t := by
    intro t
    simp [circleMap_zero, reciprocalCircle]
  rw [Real.circleAverage_def] at havg
  simp only [hparam] at havg
  have hderivIntegral :
      ∫ t in (0 : ℝ)..2 * Real.pi, deriv h (reciprocalCircle s t) = 0 := by
    rw [smul_eq_zero] at havg
    rcases havg with hzero | hzero
    · norm_num [Real.pi_ne_zero] at hzero
    · exact hzero
  rw [fourierCoeffOn_eq_integral]
  have hexp : ∀ t : ℝ,
      fourier (-2) (t : AddCircle (2 * Real.pi - 0)) =
        Complex.exp ((-2 : ℂ) * (t : ℂ) * Complex.I) := by
    intro t
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  simp_rw [hexp]
  have halgebra : ∀ t : ℝ,
      Complex.exp ((-2 : ℂ) * (t : ℂ) * Complex.I) *
          exteriorCircleDerivative b h s t =
        Complex.exp ((-2 : ℂ) * (t : ℂ) * Complex.I) -
          b / (s : ℂ) ^ 2 -
          (deriv h (reciprocalCircle s t)) / (s : ℂ) ^ 2 := by
    intro t
    unfold exteriorCircleDerivative reciprocalCircle
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hexpcancel : Complex.exp ((-2 : ℂ) * (t : ℂ) * Complex.I) *
        Complex.exp ((t : ℂ) * Complex.I) ^ 2 = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      convert Complex.exp_zero using 1
      ring
    have hexpcancel' : Complex.exp (-(2 * (t : ℂ) * Complex.I)) *
        Complex.exp ((t : ℂ) * Complex.I) ^ 2 = 1 := by
      convert hexpcancel using 1 <;> ring
    field_simp [hsC]
    calc
      Complex.exp (-(2 * (t : ℂ) * Complex.I)) *
          ((s : ℂ) ^ 2 - b * Complex.exp ((t : ℂ) * Complex.I) ^ 2 -
            Complex.exp ((t : ℂ) * Complex.I) ^ 2 *
              deriv h (Complex.exp ((t : ℂ) * Complex.I) / (s : ℂ))) =
        Complex.exp (-(2 * (t : ℂ) * Complex.I)) * (s : ℂ) ^ 2 -
          b * (Complex.exp (-(2 * (t : ℂ) * Complex.I)) *
            Complex.exp ((t : ℂ) * Complex.I) ^ 2) -
          deriv h (Complex.exp ((t : ℂ) * Complex.I) / (s : ℂ)) *
            (Complex.exp (-(2 * (t : ℂ) * Complex.I)) *
              Complex.exp ((t : ℂ) * Complex.I) ^ 2) := by ring
      _ = _ := by rw [hexpcancel']; ring
  simp only [smul_eq_mul]
  simp_rw [halgebra]
  have hExpInt : IntervalIntegrable
      (fun t : ℝ ↦ Complex.exp ((-2 : ℂ) * (t : ℂ) * Complex.I))
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hConstInt : IntervalIntegrable (fun _ : ℝ ↦ b / (s : ℂ) ^ 2)
      volume 0 (2 * Real.pi) := intervalIntegrable_const
  have hDerivCont : Continuous (fun t ↦ deriv h (reciprocalCircle s t)) := by
    have hw : Continuous (reciprocalCircle s) := by
      unfold reciprocalCircle
      fun_prop
    have hwmem : ∀ t, reciprocalCircle s t ∈ ball (0 : ℂ) 1 := by
      intro t
      rw [mem_ball_zero_iff, norm_reciprocalCircle hs0]
      exact (inv_lt_one₀ hs0).2 hs
    simpa [Function.comp_def] using hh.deriv.continuousOn.comp_continuous hw hwmem
  have hDivInt : IntervalIntegrable
      (fun t : ℝ ↦ deriv h (reciprocalCircle s t) / (s : ℂ) ^ 2)
      volume 0 (2 * Real.pi) := by
    exact (hDerivCont.div_const ((s : ℂ) ^ 2)).intervalIntegrable 0 (2 * Real.pi)
  rw [intervalIntegral.integral_sub (hExpInt.sub hConstInt) hDivInt,
    intervalIntegral.integral_sub hExpInt hConstInt,
    integral_exp_neg_two_mul_I, intervalIntegral.integral_const]
  have hdivIntegral :
      (∫ t in (0 : ℝ)..2 * Real.pi,
        deriv h (reciprocalCircle s t) / (s : ℂ) ^ 2) = 0 := by
    have hpull :
        (∫ t in (0 : ℝ)..2 * Real.pi,
          deriv h (reciprocalCircle s t) * ((s : ℂ) ^ 2)⁻¹) =
          (∫ t in (0 : ℝ)..2 * Real.pi,
            deriv h (reciprocalCircle s t)) * ((s : ℂ) ^ 2)⁻¹ :=
      intervalIntegral.integral_mul_const _ _
    simp only [div_eq_mul_inv, hpull, hderivIntegral, zero_mul]
  rw [hdivIntegral]
  simp only [sub_zero, zero_sub]
  rw [smul_neg, smul_smul]
  have hscalar : (1 / (2 * Real.pi)) * (2 * Real.pi) = 1 := by
    field_simp [Real.pi_ne_zero]
  rw [hscalar, one_smul]
  rw [neg_div]

/-- The two Laurent modes give the sharp circle-energy lower bound.

%%handwave
name: Circle-energy lower bound for an exterior Laurent map
statement:
  Let $h$ be holomorphic on the unit disk with $h'(0)=0$, let $b\in\mathbb C$, and let $s>1$. If $D_s(t)=1-bw(t)^2-h'(w(t))w(t)^2$ for $w(t)=s^{-1}e^{it}$, then $1+|b|^2/s^4\le(2\pi)^{-1}\int_0^{2\pi}|D_s(t)|^2\,dt$.
proof:
  Apply the two-mode Fourier energy bound. The zeroth coefficient is $1$ and the second coefficient is $-b/s^2$, giving the stated left-hand side.
-/
theorem exteriorCircleDerivative_energy_lower
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (h1 : deriv h 0 = 0) {s : ℝ} (hs : 1 < s) :
    1 + ‖b‖ ^ 2 / s ^ 4 ≤
      (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
        ‖exteriorCircleDerivative b h s t‖ ^ 2 := by
  have hB := two_fourier_coeff_sq_le_average
    (continuous_exteriorCircleDerivative (b := b) hh hs)
  rw [exteriorCircleDerivative_fourierCoeff_zero hh hs,
    exteriorCircleDerivative_fourierCoeff_two hh h1 hs] at hB
  have hs0 : 0 < s := zero_lt_one.trans hs
  convert hB using 1
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  field_simp [hs0.ne']

/--
%%handwave
name: Polar-coordinate inverse formula
statement:
  For $r,t\in\mathbb R$, the inverse polar-coordinate map sends $(r,t)$ to $re^{it}$, the standard parametrization of the circle of radius $r$ about $0$.
proof:
  Expand the two parametrizations and use $e^{it}=\cos t+i\sin t$.
-/
private theorem polarCoord_symm_eq_circleMap (r t : ℝ) :
    Complex.polarCoord.symm (r, t) = circleMap (0 : ℂ) r t := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

/--
%%handwave
name: Polar-coordinate integral over an open annulus
statement:
  Let $0<r<R$ and let $F:\mathbb C\to\mathbb R$ be continuous on $r\le|z|\le R$. Then $\int_{r<|z|<R}F(z)\,dz=\int_{(r,R)\times(-\pi,\pi)}\rho F(\rho e^{it})\,d\rho\,dt$.
proof:
  Apply the planar polar-coordinate change of variables to the indicator of the annulus. On the polar chart, that indicator is exactly the indicator of $(r,R)\times(-\pi,\pi)$, and the Jacobian is $\rho$.
-/
private theorem setIntegral_openAnnulus_eq_polar
    {F : ℂ → ℝ} {r R : ℝ} (hr : 0 < r) (_hrR : r < R)
    (_hF : ContinuousOn F {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}) :
    (∫ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}, F z) =
      ∫ p in Ioo r R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * F (Complex.polarCoord.symm p) := by
  let A : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}
  let B : Set (ℝ × ℝ) := Ioo r R ×ˢ Set.univ
  let H : ℝ × ℝ → ℝ := fun p ↦ p.1 * F (Complex.polarCoord.symm p)
  have hAmeas : MeasurableSet A := by
    exact (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hBmeas : MeasurableSet B := measurableSet_Ioo.prod MeasurableSet.univ
  have hpolar := Complex.integral_comp_polarCoord_symm (A.indicator F)
  calc
    (∫ z in A, F z) = ∫ z : ℂ, A.indicator F z :=
      (integral_indicator hAmeas).symm
    _ = ∫ p in Complex.polarCoord.target,
        p.1 * A.indicator F (Complex.polarCoord.symm p) := by
      simpa [smul_eq_mul] using hpolar.symm
    _ = ∫ p in Complex.polarCoord.target, B.indicator H p := by
      refine setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet ?_
      intro p hp
      have hp' : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := by
        simpa [Complex.polarCoord_target] using hp
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp'.1]
      by_cases hpB : p ∈ B
      · have hpA : Complex.polarCoord.symm p ∈ A := by
          change r < ‖Complex.polarCoord.symm p‖ ∧
            ‖Complex.polarCoord.symm p‖ < R
          rw [hnorm]
          exact hpB.1
        change p.1 * A.indicator F (Complex.polarCoord.symm p) = B.indicator H p
        rw [Set.indicator_of_mem hpA, Set.indicator_of_mem hpB]
      · have hpA : Complex.polarCoord.symm p ∉ A := by
          intro hpA
          apply hpB
          refine ⟨?_, trivial⟩
          change r < ‖Complex.polarCoord.symm p‖ ∧
            ‖Complex.polarCoord.symm p‖ < R at hpA
          rwa [hnorm] at hpA
        change p.1 * A.indicator F (Complex.polarCoord.symm p) = B.indicator H p
        rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem hpB]
        simp
    _ = ∫ p in Complex.polarCoord.target ∩ B, H p := by
      rw [setIntegral_indicator hBmeas]
    _ = ∫ p in Ioo r R ×ˢ Ioo (-Real.pi) Real.pi, H p := by
      have hset : Complex.polarCoord.target ∩ B =
          Ioo r R ×ˢ Ioo (-Real.pi) Real.pi := by
        ext p
        simp only [Complex.polarCoord_target, B, mem_inter_iff, mem_prod, mem_Ioi,
          mem_Ioo, mem_univ, and_true]
        constructor
        · rintro ⟨⟨hp0, hpa⟩, hpr⟩
          exact ⟨hpr, hpa⟩
        · rintro ⟨hpr, hpa⟩
          exact ⟨⟨hr.trans hpr.1, hpa⟩, hpr⟩
      rw [hset]
    _ = _ := rfl

/--
%%handwave
name: Iterated polar integral over an annulus
statement:
  Under the same hypotheses, $\int_{r<|z|<R}F(z)\,dz=\int_r^R\int_{-\pi}^{\pi}\rho F(\rho e^{it})\,dt\,d\rho$.
proof:
  The polar integrand is continuous on the compact closed rectangle and hence integrable. Fubini's theorem converts the product integral to the displayed iterated integral; changing open rectangles to interval integrals does not affect the value.
-/
private theorem setIntegral_openAnnulus_eq_iterated
    {F : ℂ → ℝ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hF : ContinuousOn F {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}) :
    (∫ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}, F z) =
      ∫ ρ in r..R, ∫ t in (-Real.pi)..Real.pi,
        ρ * F (circleMap (0 : ℂ) ρ t) := by
  rw [setIntegral_openAnnulus_eq_polar hr hrR hF]
  let rect : Set (ℝ × ℝ) := Icc r R ×ˢ Icc (-Real.pi) Real.pi
  let K : ℝ × ℝ → ℝ := fun p ↦ p.1 * F (Complex.polarCoord.symm p)
  have hsymm : Continuous (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
    simpa [Complex.polarCoord] using
      (Complex.equivRealProdCLM.symm.continuous.comp continuous_polarCoord_symm)
  have hmaps : MapsTo (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p)
      rect {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    intro p hp
    have hp0 : 0 ≤ p.1 := hr.le.trans hp.1.1
    simpa [rect, Complex.norm_polarCoord_symm, abs_of_nonneg hp0] using hp.1
  have hKcont : ContinuousOn K rect := by
    exact continuous_fst.continuousOn.mul (hF.comp hsymm.continuousOn hmaps)
  have hKintRect : IntegrableOn K rect :=
    hKcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hsub : Ioo r R ×ˢ Ioo (-Real.pi) Real.pi ⊆ rect :=
    Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hKint : IntegrableOn K (Ioo r R ×ˢ Ioo (-Real.pi) Real.pi) :=
    hKintRect.mono_set hsub
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [setIntegral_prod K hKint]
  have hrle : r ≤ R := hrR.le
  have hpile : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simp_rw [intervalIntegral.integral_of_le hrle,
    intervalIntegral.integral_of_le hpile, integral_Ioc_eq_integral_Ioo]
  simp [K, circleMap, Complex.exp_mul_I, Complex.polarCoord_symm_apply]

/--
%%handwave
name: Periodicity of the reciprocal-circle parametrization
statement:
  For every $s\in\mathbb R$, the function $t\mapsto s^{-1}e^{it}$ has period $2\pi$.
proof:
  Use $e^{i(t+2\pi)}=e^{it}e^{2\pi i}=e^{it}$.
-/
private theorem periodic_reciprocalCircle (s : ℝ) :
    Function.Periodic (reciprocalCircle s) (2 * Real.pi) := by
  intro t
  unfold reciprocalCircle
  congr 1
  rw [show (((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (t : ℂ) * Complex.I + (2 * Real.pi : ℝ) * Complex.I by push_cast; ring,
    Complex.exp_add]
  have : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    simp [Complex.exp_mul_I]
  rw [this, mul_one]

/--
%%handwave
name: Periodicity of the exterior derivative along a circle
statement:
  For $b\in\mathbb C$, $h:\mathbb C\to\mathbb C$, and $s\in\mathbb R$, the function $t\mapsto1-bw(t)^2-h'(w(t))w(t)^2$, with $w(t)=s^{-1}e^{it}$, has period $2\pi$.
proof:
  Every occurrence of $t$ factors through the $2\pi$-periodic function $w$.
-/
private theorem periodic_exteriorCircleDerivative (b : ℂ) (h : ℂ → ℂ) (s : ℝ) :
    Function.Periodic (exteriorCircleDerivative b h s) (2 * Real.pi) := by
  intro t
  unfold exteriorCircleDerivative
  rw [periodic_reciprocalCircle s t]

/--
%%handwave
name: Exterior derivative on a geometric circle
statement:
  Let $G(z)=z+bz^{-1}+h(z^{-1})$, with $h$ holomorphic on the unit disk. If $s>1$, then $G'(se^{it})=1-bw(-t)^2-h'(w(-t))w(-t)^2$, where $w(t)=s^{-1}e^{it}$.
proof:
  Insert $z=se^{it}$ into the derivative formula for $G$ and use $(se^{it})^{-1}=s^{-1}e^{-it}$.
-/
private theorem actualCircleDerivative_eq
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    {s t : ℝ} (hs : 1 < s) :
    deriv (exteriorLaurentMap b h) (circleMap (0 : ℂ) s t) =
      exteriorCircleDerivative b h s (-t) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hnorm : ‖circleMap (0 : ℂ) s t‖ = s := by
    simp [circleMap_zero, Complex.norm_exp, Complex.mul_re, hs0.le]
  rw [exteriorLaurentMap_deriv hh (by simpa [hnorm] using hs)]
  have hinv : (circleMap (0 : ℂ) s t)⁻¹ = reciprocalCircle s (-t) := by
    rw [circleMap_zero]
    unfold reciprocalCircle
    rw [mul_inv_rev, ← Complex.exp_neg, mul_comm]
    congr 1
    push_cast
    ring
  rw [hinv]
  rfl

/--
%%handwave
name: Geometric circle-energy lower bound
statement:
  Let $G(z)=z+bz^{-1}+h(z^{-1})$, where $h$ is holomorphic on the unit disk and $h'(0)=0$. For every $s>1$, $2\pi(1+|b|^2/s^4)\le\int_{-\pi}^{\pi}|G'(se^{it})|^2\,dt$.
proof:
  Rewrite $G'(se^{it})$ using the reciprocal-circle formula, reverse $t$, and translate one period from $[-\pi,\pi]$ to $[0,2\pi]$. The preceding normalized circle-energy estimate then gives the bound after multiplying by $2\pi$.
-/
private theorem actualCircleDerivative_energy_lower
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (h1 : deriv h 0 = 0) {s : ℝ} (hs : 1 < s) :
    2 * Real.pi * (1 + ‖b‖ ^ 2 / s ^ 4) ≤
      ∫ t in (-Real.pi)..Real.pi,
        ‖deriv (exteriorLaurentMap b h) (circleMap (0 : ℂ) s t)‖ ^ 2 := by
  let E : ℝ → ℝ := fun t ↦ ‖exteriorCircleDerivative b h s t‖ ^ 2
  have hperiod : Function.Periodic E (2 * Real.pi) := by
    intro t
    simp only [E]
    rw [periodic_exteriorCircleDerivative b h s t]
  have hrev : (∫ t in (-Real.pi)..Real.pi, E (-t)) =
      ∫ t in (-Real.pi)..Real.pi, E t := by
    simpa using intervalIntegral.integral_comp_neg E
  have hshift : (∫ t in (-Real.pi)..Real.pi, E t) =
      ∫ t in (0 : ℝ)..2 * Real.pi, E t := by
    have hleft : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have hright : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
    simpa [hleft, hright] using hperiod.intervalIntegral_add_eq (-Real.pi) 0
  have henergy := exteriorCircleDerivative_energy_lower (b := b) hh h1 hs
  have hpi : 0 < 2 * Real.pi := by positivity
  have hscaled := mul_le_mul_of_nonneg_left henergy hpi.le
  have hscaled' : 2 * Real.pi * (1 + ‖b‖ ^ 2 / s ^ 4) ≤
      ∫ t in (0 : ℝ)..2 * Real.pi, E t := by
    calc
      2 * Real.pi * (1 + ‖b‖ ^ 2 / s ^ 4) ≤
          2 * Real.pi * ((2 * Real.pi)⁻¹ *
            ∫ t in (0 : ℝ)..2 * Real.pi, E t) := hscaled
      _ = _ := by field_simp [Real.pi_ne_zero]
  calc
    2 * Real.pi * (1 + ‖b‖ ^ 2 / s ^ 4)
        ≤ ∫ t in (0 : ℝ)..2 * Real.pi, E t := hscaled'
    _ = ∫ t in (-Real.pi)..Real.pi, E t := hshift.symm
    _ = ∫ t in (-Real.pi)..Real.pi, E (-t) := hrev.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change ‖exteriorCircleDerivative b h s (-t)‖ ^ 2 =
        ‖deriv (exteriorLaurentMap b h) (circleMap (0 : ℂ) s t)‖ ^ 2
      rw [actualCircleDerivative_eq hh hs]

/--
%%handwave
name: Area formula for an exterior Laurent map on an annulus
statement:
  Let $1<r<R$ and let $G(z)=z+bz^{-1}+h(z^{-1})$, where $h$ is holomorphic on the unit disk. If $G$ is injective on $|z|>1$, then $\operatorname{area}(G(\{r<|z|<R\}))=\int_{r<|z|<R}|G'(z)|^2\,dz$.
proof:
  Apply the change-of-variables formula to the injective restriction of $G$ to the annulus. Its real derivative is multiplication by $G'(z)$, whose real Jacobian determinant is $|G'(z)|^2$.
-/
private theorem exterior_annulus_area_eq_energy
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    {r R : ℝ} (hr : 1 < r) (_hrR : r < R)
    (hinj : Set.InjOn (exteriorLaurentMap b h) {z : ℂ | 1 < ‖z‖}) :
    (volume (exteriorLaurentMap b h '' {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R})).toReal =
      ∫ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R},
        ‖deriv (exteriorLaurentMap b h) z‖ ^ 2 := by
  let A : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}
  let G := exteriorLaurentMap b h
  have hAmeas : MeasurableSet A :=
    (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hderiv : ∀ z ∈ A,
      HasFDerivWithinAt G (complexMulReal (deriv G z)) A z := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hr.trans hz.1
    have hd : HasDerivAt G (deriv G z) z :=
      (exteriorLaurentMap_analyticOn_exterior hh (R := 1) le_rfl z hz1).differentiableAt.hasDerivAt
    simpa [complexMulReal] using hd.hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt
  have hinjA : Set.InjOn G A := by
    exact hinj.mono (fun z hz ↦ hr.trans hz.1)
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    volume hAmeas hderiv hinjA (fun _ : ℂ ↦ (1 : ℝ))
  change (∫ _z in G '' A, (1 : ℝ)) = _ at hchange
  simpa [MeasureTheory.Measure.real_def, complexMulReal_det, abs_of_nonneg,
    sq_nonneg, A, G] using hchange

set_option backward.isDefEq.respectTransparency true

/--
%%handwave
name: Integrated lower energy bound on an annulus
statement:
  Under the holomorphic hypotheses above, if $h'(0)=0$ and $1<r<R$, then $\pi(R^2-r^2)+\pi|b|^2(r^{-2}-R^{-2})\le\int_{r<|z|<R}|G'(z)|^2\,dz$.
proof:
  Express the annular integral in polar coordinates and apply the geometric circle-energy bound at each radius $\rho$. Integrating $2\pi\rho(1+|b|^2/\rho^4)$ from $r$ to $R$ gives the stated expression.
-/
private theorem exterior_annulus_energy_lower
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (h1 : deriv h 0 = 0) {r R : ℝ} (hr : 1 < r) (hrR : r < R) :
    Real.pi * (R ^ 2 - r ^ 2) +
        Real.pi * ‖b‖ ^ 2 * (r⁻¹ ^ 2 - R⁻¹ ^ 2) ≤
      ∫ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R},
        ‖deriv (exteriorLaurentMap b h) z‖ ^ 2 := by
  let F : ℂ → ℝ := fun z ↦ ‖deriv (exteriorLaurentMap b h) z‖ ^ 2
  let J : ℝ → ℝ := fun ρ ↦ ∫ t in (-Real.pi)..Real.pi,
    ρ * F (circleMap (0 : ℂ) ρ t)
  let L : ℝ → ℝ := fun ρ ↦ 2 * Real.pi * ρ * (1 + ‖b‖ ^ 2 / ρ ^ 4)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hR1 : 1 < R := hr.trans hrR
  have hFcont : ContinuousOn F {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    have hsub : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} ⊆ {z : ℂ | 1 < ‖z‖} :=
      fun z hz ↦ hr.trans_le hz.1
    exact (exteriorLaurentMap_analyticOn_exterior hh (R := 1) le_rfl).deriv.continuousOn.norm.pow 2 |>.mono hsub
  rw [setIntegral_openAnnulus_eq_iterated hr0 hrR hFcont]
  change _ ≤ ∫ ρ in r..R, J ρ
  have hLcont : ContinuousOn L (Icc r R) := by
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := ne_of_gt (hr0.trans_le hρ.1)
    unfold L
    exact ((continuousAt_const.mul continuousAt_id).mul
      (continuousAt_const.add
        (continuousAt_const.div (continuousAt_id.pow 4) (pow_ne_zero 4 hρ0)))).continuousWithinAt
  have hLint : IntervalIntegrable L volume r R := by
    rw [intervalIntegrable_iff]
    rw [uIoc_of_le hrR.le]
    exact (hLcont.integrableOn_compact (isCompact_Icc) (μ := volume)).mono_set
      Ioc_subset_Icc_self
  have hJint : IntervalIntegrable J volume r R := by
    let rect : Set (ℝ × ℝ) := Icc r R ×ˢ Icc (-Real.pi) Real.pi
    let K : ℝ × ℝ → ℝ := fun p ↦ p.1 * F (circleMap (0 : ℂ) p.1 p.2)
    have hcircle : Continuous (fun p : ℝ × ℝ ↦ circleMap (0 : ℂ) p.1 p.2) := by
      unfold circleMap
      fun_prop
    have hmaps : MapsTo (fun p : ℝ × ℝ ↦ circleMap (0 : ℂ) p.1 p.2)
        rect {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
      intro p hp
      have hp0 : 0 ≤ p.1 := hr0.le.trans hp.1.1
      have hnorm : ‖circleMap (0 : ℂ) p.1 p.2‖ = p.1 := by
        simp [circleMap_zero, Complex.norm_exp, Complex.mul_re, hp0]
      change r ≤ ‖circleMap (0 : ℂ) p.1 p.2‖ ∧
        ‖circleMap (0 : ℂ) p.1 p.2‖ ≤ R
      rw [hnorm]
      exact hp.1
    have hKcont : ContinuousOn K rect :=
      continuous_fst.continuousOn.mul (hFcont.comp hcircle.continuousOn hmaps)
    have hKint : IntegrableOn K rect :=
      hKcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hprod : Integrable K
        ((volume.restrict (Icc r R)).prod
          (volume.restrict (Icc (-Real.pi) Real.pi))) := by
      rw [Measure.prod_restrict]
      exact hKint
    have houter := hprod.integral_prod_left
    have hJeq : ∀ ρ : ℝ, J ρ =
        ∫ t in Icc (-Real.pi) Real.pi, K (ρ, t) := by
      intro ρ
      unfold J K
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        ← integral_Icc_eq_integral_Ioc]
    rw [intervalIntegrable_iff]
    rw [uIoc_of_le hrR.le]
    have houter' : Integrable
        (fun ρ ↦ ∫ t in Icc (-Real.pi) Real.pi, K (ρ, t))
        (volume.restrict (Ioc r R)) :=
      houter.mono_measure (Measure.restrict_mono
        (μ := (volume : Measure ℝ)) (ν := volume) Ioc_subset_Icc_self le_rfl)
    exact houter'.congr (ae_of_all _ fun ρ ↦ (hJeq ρ).symm)
  have hpoint : ∀ ρ ∈ Icc r R, L ρ ≤ J ρ := by
    intro ρ hρ
    have hρ1 : 1 < ρ := hr.trans_le hρ.1
    have heng := actualCircleDerivative_energy_lower (b := b) hh h1 hρ1
    dsimp [L, J, F]
    have hρ0 : 0 ≤ ρ := (zero_lt_one.trans hρ1).le
    calc
      2 * Real.pi * ρ * (1 + ‖b‖ ^ 2 / ρ ^ 4) =
          ρ * (2 * Real.pi * (1 + ‖b‖ ^ 2 / ρ ^ 4)) := by ring
      _ ≤ ρ * (∫ t in (-Real.pi)..Real.pi,
          ‖deriv (exteriorLaurentMap b h) (circleMap 0 ρ t)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left heng hρ0
      _ = _ := by rw [← intervalIntegral.integral_const_mul]
  have hmono := intervalIntegral.integral_mono_on hrR.le hLint hJint hpoint
  have hcalc : (∫ ρ in r..R, L ρ) =
      Real.pi * (R ^ 2 - r ^ 2) +
        Real.pi * ‖b‖ ^ 2 * (r⁻¹ ^ 2 - R⁻¹ ^ 2) := by
    let P : ℝ → ℝ := fun ρ ↦ Real.pi * ρ ^ 2 - Real.pi * ‖b‖ ^ 2 * ρ⁻¹ ^ 2
    have hderiv : ∀ ρ ∈ uIcc r R, HasDerivAt P (L ρ) ρ := by
      intro ρ hρ
      have hρI : ρ ∈ Icc r R := by simpa [uIcc_of_le hrR.le] using hρ
      have hρ0 : ρ ≠ 0 := by
        exact ne_of_gt (hr0.trans_le hρI.1)
      have hcancel : ρ * ‖b‖ ^ 2 * ρ⁻¹ = ‖b‖ ^ 2 := by
        calc
          ρ * ‖b‖ ^ 2 * ρ⁻¹ = ‖b‖ ^ 2 * (ρ * ρ⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hρ0, mul_one]
      unfold P L
      convert (((hasDerivAt_id ρ).pow 2).const_mul Real.pi).sub
        (((hasDerivAt_inv hρ0).pow 2).const_mul (Real.pi * ‖b‖ ^ 2)) using 1;
        norm_num [id_eq] <;> rw [inv_eq_one_div];
        field_simp [hρ0]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hLint
    rw [hFTC]
    dsimp [P]
    ring
  rw [hcalc] at hmono
  exact hmono

/--
%%handwave
name: Upper energy bound from the omitted exterior area
statement:
  Let $G(z)=z+bz^{-1}+h(z^{-1})$ be injective on $|z|>1$, with $h(0)=0$ and $|h(w)|\le C|w|^2$ for $|w|<\rho$. If $1<r<R$, $|b|<R^2$, and $R^{-1}<\rho$, then $\int_{r<|z|<R}|G'(z)|^2\,dz\le\pi(1-|b|^2/R^4)\bigl(R+(C/R^2)/(1-|b|/R^2)\bigr)^2$.
proof:
  Injectivity makes the image of the annulus disjoint from the image of $|z|>R$, so it lies in the omitted exterior set. Bound that set by the ellipse estimate, convert its disk measure to $\pi s^2$, and use the annular area formula to identify image area with derivative energy.
-/
private theorem exterior_annulus_energy_upper
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (h0 : h 0 = 0) {ρ C r R : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hquad : ∀ z : ℂ, ‖z‖ < ρ → ‖h z‖ ≤ C * ‖z‖ ^ 2)
    (hr : 1 < r) (hrR : r < R) (hbR : ‖b‖ < R ^ 2) (hinvR : R⁻¹ < ρ)
    (hinj : Set.InjOn (exteriorLaurentMap b h) {z : ℂ | 1 < ‖z‖}) :
    ∫ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R},
        ‖deriv (exteriorLaurentMap b h) z‖ ^ 2 ≤
      Real.pi * (1 - (‖b‖ / R ^ 2) ^ 2) *
        (R + (C / R ^ 2) / (1 - ‖b‖ / R ^ 2)) ^ 2 := by
  let G := exteriorLaurentMap b h
  let A : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}
  let K : Set ℂ := (G '' {z : ℂ | R < ‖z‖})ᶜ
  let q : ℝ := ‖b‖ / R ^ 2
  let s : ℝ := R + (C / R ^ 2) / (1 - q)
  have hR : 1 < R := hr.trans hrR
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR0
  have hq : q < 1 := by
    dsimp [q]
    exact (div_lt_one hR2).2 hbR
  have hq0 : 0 ≤ q := by positivity
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact add_nonneg hR0.le
      (div_nonneg (div_nonneg hC hR2.le) (sub_nonneg.mpr hq.le))
  have hinjR : Set.InjOn G {z : ℂ | R ≤ ‖z‖} := by
    exact hinj.mono (fun z hz ↦ hR.trans_le hz)
  have hupper := exterior_omitted_measure_le_ellipse hh h0 hρ hC hquad hR hbR hinvR hinjR
  have hAK : G '' A ⊆ K := by
    rintro y ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have hzw := hinj (hr.trans hz.1) (hR.trans hw) heq.symm
    subst w
    exact (not_lt_of_ge hz.2.le) hw
  have hmeasure : volume (G '' A) ≤
      ENNReal.ofReal (1 - q ^ 2) * volume (closedBall (0 : ℂ) s) := by
    exact (measure_mono hAK).trans (by simpa [G, K, q, s] using hupper)
  have hright_ne_top :
      ENNReal.ofReal (1 - q ^ 2) * volume (closedBall (0 : ℂ) s) ≠ ⊤ := by
    rw [Complex.volume_closedBall]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.coe_lt_top)).ne
  have hleft_ne_top : volume (G '' A) ≠ ⊤ :=
    (lt_of_le_of_lt hmeasure (lt_top_iff_ne_top.mpr hright_ne_top)).ne
  have hreal := (ENNReal.toReal_le_toReal hleft_ne_top hright_ne_top).2 hmeasure
  have harea : (volume (G '' A)).toReal =
      ∫ z in A, ‖deriv G z‖ ^ 2 := by
    simpa [G, A] using exterior_annulus_area_eq_energy hh hr hrR hinj
  rw [harea] at hreal
  rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal,
    ENNReal.coe_toReal] at hreal
  · simpa [q, s, mul_assoc, mul_left_comm, mul_comm] using hreal
  · exact hs0
  · nlinarith [sq_nonneg q]

/--
%%handwave
name:
  Grönwall's area theorem
statement:
  Let
  $G(z)=z+b/z+h(1/z)$ be holomorphic and injective on $|z|>1$, where $h$ is
  holomorphic on $|w|<1$ and satisfies $h(0)=h'(0)=0$. Then $|b|\le1$.
proof:
  On every circle $|z|=s>1$, the constant and second Fourier modes of the
  tangential derivative give an energy lower bound containing
  $1+|b|^2/s^4$. Integrating over an annulus and comparing with the area
  enclosed by the outer image curve yields $|b|^2\le r^4$ for every $r>1$.
  Letting $r\downarrow1$ gives $|b|\le1$.
tags:
  milestone
-/
theorem gronwall_area_first_coefficient
    {b : ℂ} {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (h0 : h 0 = 0) (h1 : deriv h 0 = 0)
    (hinj : Set.InjOn (exteriorLaurentMap b h) {z : ℂ | 1 < ‖z‖}) :
    ‖b‖ ≤ 1 := by
  rcases analytic_quadratic_bound (hh 0 (mem_ball_self zero_lt_one)) h0 h1 with
    ⟨ρ, C, hρ, hC, hquad⟩
  have hfixed : ∀ r : ℝ, 1 < r → ‖b‖ ^ 2 ≤ r ^ 4 := by
    intro r hr
    let lower : ℝ → ℝ := fun R ↦
      Real.pi * (R ^ 2 - r ^ 2) +
        Real.pi * ‖b‖ ^ 2 * (r⁻¹ ^ 2 - R⁻¹ ^ 2) - Real.pi * R ^ 2
    let upper : ℝ → ℝ := fun R ↦
      Real.pi * (1 - (‖b‖ / R ^ 2) ^ 2) *
        (R + (C / R ^ 2) / (1 - ‖b‖ / R ^ 2)) ^ 2 - Real.pi * R ^ 2
    have hinv : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hlarge : ∀ᶠ R : ℝ in atTop, 1 < R ∧ ‖b‖ < R ^ 2 := by
      filter_upwards [eventually_gt_atTop (max 1 ‖b‖)] with R hR
      have hR1 : 1 < R := lt_of_le_of_lt (le_max_left 1 ‖b‖) hR
      have hbR : ‖b‖ < R := lt_of_le_of_lt (le_max_right 1 ‖b‖) hR
      exact ⟨hR1, hbR.trans (by nlinarith)⟩
    have hrR : ∀ᶠ R : ℝ in atTop, r < R := eventually_gt_atTop r
    have hinvρ : ∀ᶠ R : ℝ in atTop, R⁻¹ < ρ :=
      hinv.eventually (Iio_mem_nhds hρ)
    have hcompare : ∀ᶠ R : ℝ in atTop, lower R ≤ upper R := by
      filter_upwards [hlarge, hrR, hinvρ] with R hR hrR hinvR
      have hlo := exterior_annulus_energy_lower (b := b) hh h1 hr hrR
      have hup := exterior_annulus_energy_upper hh h0 hρ hC hquad hr hrR hR.2 hinvR hinj
      exact sub_le_sub_right (hlo.trans hup) (Real.pi * R ^ 2)
    have hlower : Tendsto lower atTop
        (𝓝 (Real.pi * (‖b‖ ^ 2 * r⁻¹ ^ 2 - r ^ 2))) := by
      have hvanish : Tendsto (fun R : ℝ ↦ Real.pi * ‖b‖ ^ 2 * R⁻¹ ^ 2)
          atTop (𝓝 0) := by
        convert (tendsto_const_nhds.mul (hinv.pow 2)) using 1 <;> norm_num
      have hconst : Tendsto
          (fun _ : ℝ ↦ Real.pi * (‖b‖ ^ 2 * r⁻¹ ^ 2 - r ^ 2)) atTop
          (𝓝 (Real.pi * (‖b‖ ^ 2 * r⁻¹ ^ 2 - r ^ 2))) := tendsto_const_nhds
      have ht := hconst.sub hvanish
      convert ht using 1 <;> simp [lower] <;> ring
    have hq : Tendsto (fun R : ℝ ↦ ‖b‖ * R⁻¹ ^ 2) atTop (𝓝 0) := by
      convert (tendsto_const_nhds.mul (hinv.pow 2)) using 1 <;> norm_num
    have hone_sub_q : Tendsto (fun R : ℝ ↦ 1 - ‖b‖ * R⁻¹ ^ 2)
        atTop (𝓝 1) := by
      convert tendsto_const_nhds.sub hq using 1 <;> norm_num
    have hone_sub_qsq : Tendsto
        (fun R : ℝ ↦ 1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) atTop (𝓝 1) := by
      convert tendsto_const_nhds.sub (hq.pow 2) using 1 <;> norm_num
    have hratio₁ : Tendsto
        (fun R : ℝ ↦ (1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) /
          (1 - ‖b‖ * R⁻¹ ^ 2))
        atTop (𝓝 1) := by
      convert hone_sub_qsq.div hone_sub_q one_ne_zero using 1 <;> norm_num
    have hratio₂ : Tendsto
        (fun R : ℝ ↦ (1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) /
          (1 - ‖b‖ * R⁻¹ ^ 2) ^ 2)
        atTop (𝓝 1) := by
      convert hone_sub_qsq.div (hone_sub_q.pow 2) (by norm_num) using 1 <;> norm_num
    have hnormalized : Tendsto
        (fun R : ℝ ↦
          -‖b‖ ^ 2 * R⁻¹ ^ 2 +
            2 * C * R⁻¹ * ((1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) /
              (1 - ‖b‖ * R⁻¹ ^ 2)) +
            C ^ 2 * R⁻¹ ^ 4 *
              ((1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) /
                (1 - ‖b‖ * R⁻¹ ^ 2) ^ 2))
        atTop (𝓝 0) := by
      have hterm₁ : Tendsto (fun R : ℝ ↦ -‖b‖ ^ 2 * R⁻¹ ^ 2)
          atTop (𝓝 0) := by
        convert tendsto_const_nhds.mul (hinv.pow 2) using 1 <;> norm_num
      have hterm₂ : Tendsto
          (fun R : ℝ ↦ 2 * C * R⁻¹ * ((1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) /
            (1 - ‖b‖ * R⁻¹ ^ 2)))
          atTop (𝓝 0) := by
        convert (tendsto_const_nhds.mul hinv).mul hratio₁ using 1 <;> norm_num
      have hterm₃ : Tendsto
          (fun R : ℝ ↦ C ^ 2 * R⁻¹ ^ 4 *
            ((1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) /
              (1 - ‖b‖ * R⁻¹ ^ 2) ^ 2))
          atTop (𝓝 0) := by
        convert (tendsto_const_nhds.mul (hinv.pow 4)).mul hratio₂ using 1 <;> norm_num
      convert (hterm₁.add hterm₂).add hterm₃ using 1 <;> norm_num
    have hupper : Tendsto upper atTop (𝓝 0) := by
      have hpi : Tendsto (fun _ : ℝ ↦ Real.pi) atTop (𝓝 Real.pi) :=
        tendsto_const_nhds
      have ht := hpi.mul hnormalized
      have ht0 : Tendsto
          (fun R : ℝ ↦ Real.pi *
            (-‖b‖ ^ 2 * R⁻¹ ^ 2 +
              2 * C * R⁻¹ * ((1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) /
                (1 - ‖b‖ * R⁻¹ ^ 2)) +
              C ^ 2 * R⁻¹ ^ 4 *
                ((1 - (‖b‖ * R⁻¹ ^ 2) ^ 2) /
                  (1 - ‖b‖ * R⁻¹ ^ 2) ^ 2)))
          atTop (𝓝 0) := by simpa using ht
      apply ht0.congr'
      filter_upwards [hlarge] with R hR
      have hR0 : R ≠ 0 := ne_of_gt (zero_lt_one.trans hR.1)
      have hqne : 1 - ‖b‖ * R⁻¹ ^ 2 ≠ 0 := by
        have hq_lt : ‖b‖ * R⁻¹ ^ 2 < 1 := by
          rw [inv_pow]
          exact (div_lt_one (sq_pos_of_pos (zero_lt_one.trans hR.1))).2 hR.2
        linarith
      have hden : R ^ 2 - ‖b‖ ≠ 0 := ne_of_gt (sub_pos.mpr hR.2)
      dsimp [upper]
      field_simp [hR0, hqne, hden]
      <;> ring
    have hlimit := le_of_tendsto_of_tendsto hlower hupper hcompare
    have hbase : ‖b‖ ^ 2 * r⁻¹ ^ 2 ≤ r ^ 2 := by
      have hmul : Real.pi * (‖b‖ ^ 2 * r⁻¹ ^ 2 - r ^ 2) ≤ 0 := by
        simpa using hlimit
      have := nonpos_of_mul_nonpos_right hmul Real.pi_pos
      linarith
    have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans hr)
    have hmul := mul_le_mul_of_nonneg_right hbase (sq_nonneg r)
    calc
      ‖b‖ ^ 2 = (‖b‖ ^ 2 * r⁻¹ ^ 2) * r ^ 2 := by
        field_simp [hr0]
      _ ≤ r ^ 2 * r ^ 2 := hmul
      _ = r ^ 4 := by ring
  apply le_of_forall_pos_le_add
  intro ε hε
  let r := Real.sqrt (1 + ε)
  have harg : 0 ≤ 1 + ε := by positivity
  have hr : 1 < r := by
    change 1 < Real.sqrt (1 + ε)
    rw [Real.lt_sqrt (by positivity)]
    nlinarith
  have hrsq : r ^ 2 = 1 + ε := by
    simpa [r] using Real.sq_sqrt harg
  have hbpow := hfixed r hr
  have hbnorm : ‖b‖ ≤ r ^ 2 := by
    rw [← sq_le_sq₀ (norm_nonneg b) (sq_nonneg r)]
    convert hbpow using 1 <;> ring
  simpa [hrsq] using hbnorm

/-- The analytic extension to the origin of `f(z) / z`. -/
def diskNormalizedQuotient (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then deriv f 0 else f z / z

/--
%%handwave
name: Normalized quotient at the origin
statement:
  For every function $f:\mathbb C\to\mathbb C$, its normalized quotient is defined at $0$ by $q(0)=f'(0)$.
proof:
  This is the zero branch of the definition.
-/
@[simp]
theorem diskNormalizedQuotient_zero (f : ℂ → ℂ) :
    diskNormalizedQuotient f 0 = deriv f 0 := by
  simp [diskNormalizedQuotient]

/--
%%handwave
name: Factorization through the normalized quotient
statement:
  If $f(0)=0$ and $q(0)=f'(0)$ while $q(z)=f(z)/z$ for $z\ne0$, then $zq(z)=f(z)$ for every $z\in\mathbb C$.
proof:
  At $z=0$ both sides vanish. For $z\ne0$, cancel $z$ in the defining quotient.
-/
theorem diskNormalizedQuotient_mul
    {f : ℂ → ℂ} (h0 : f 0 = 0) (z : ℂ) :
    z * diskNormalizedQuotient f z = f z := by
  by_cases hz : z = 0
  · simp [hz, h0]
  · rw [diskNormalizedQuotient, if_neg hz]
    field_simp

/--
%%handwave
name: Holomorphic extension of the normalized quotient
statement:
  If $f$ is holomorphic on the unit disk and $f(0)=0$, then the function $q(z)=f(z)/z$ for $z\ne0$, extended by $q(0)=f'(0)$, is holomorphic on the unit disk.
proof:
  Away from $0$, divide by the nonvanishing coordinate function. Near $0$, factor the power series as $f(z)=zH(z)$; differentiating at $0$ gives $H(0)=f'(0)$, so $H$ agrees with the prescribed extension.
-/
theorem diskNormalizedQuotient_analyticOnNhd
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1)) (h0 : f 0 = 0) :
    AnalyticOnNhd ℂ (diskNormalizedQuotient f) (ball 0 1) := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    rcases (hf 0 (mem_ball_self zero_lt_one)).exists_eq_sum_add_pow_mul 1 with
      ⟨H, hH, heq⟩
    have hform : ∀ w : ℂ, f w = w * H w := by
      intro w
      rw [heq]
      simp [h0, smul_eq_mul]
    have hH0 : H 0 = deriv f 0 := by
      have hprod : HasDerivAt (fun w : ℂ ↦ w * H w) (H 0) 0 := by
        convert (hasDerivAt_id (0 : ℂ)).mul hH.differentiableAt.hasDerivAt using 1 <;> simp
      have hfder := (hf 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
      have hprod' : HasDerivAt (fun w : ℂ ↦ w * H w) (deriv f 0) 0 :=
        hfder.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w ↦ (hform w).symm))
      exact hprod.unique hprod'
    apply hH.congr
    filter_upwards [] with w
    by_cases hw : w = 0
    · simp [diskNormalizedQuotient, hw, hH0]
    · rw [diskNormalizedQuotient, if_neg hw, hform w]
      field_simp
  · have hquot : AnalyticAt ℂ (fun w : ℂ ↦ f w / w) z :=
      (hf z hz).div analyticAt_id hz0
    apply hquot.congr
    filter_upwards [eventually_ne_nhds hz0] with w hw
    simp [diskNormalizedQuotient, hw]

/-- Differentiating `f(z) = z q(z)` twice at the origin, where `q` is the
normalized analytic quotient, identifies the second derivative of `f` with
twice the first derivative of `q`.

%%handwave
name: Second derivative from the normalized quotient
statement:
  If $f$ is holomorphic on the unit disk, $f(0)=0$, and $q$ is the holomorphic extension of $f(z)/z$, then $f''(0)=2q'(0)$.
proof:
  Differentiate $f(z)=zq(z)$ once to obtain $f'(z)=q(z)+zq'(z)$ near $0$, then differentiate again at $0$.
-/
theorem deriv_deriv_eq_two_mul_deriv_diskNormalizedQuotient
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1)) (h0 : f 0 = 0) :
    deriv (deriv f) 0 = 2 * deriv (diskNormalizedQuotient f) 0 := by
  let q : ℂ → ℂ := diskNormalizedQuotient f
  have hq : AnalyticOnNhd ℂ q (ball 0 1) :=
    diskNormalizedQuotient_analyticOnNhd hf h0
  have hderivEq :
      (deriv f) =ᶠ[𝓝 (0 : ℂ)] fun z ↦ q z + z * deriv q z := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    have hqz : HasDerivAt q (deriv q z) z :=
      (hq z hz).differentiableAt.hasDerivAt
    have hprod : HasDerivAt (fun w : ℂ ↦ w * q w)
        (q z + z * deriv q z) z := by
      convert (hasDerivAt_id z).mul hqz using 1 <;> simp
    have heq : (fun w : ℂ ↦ w * q w) = f := by
      funext w
      exact diskNormalizedQuotient_mul h0 w
    rw [← heq]
    exact hprod.deriv
  rw [hderivEq.deriv_eq]
  have hq0 : HasDerivAt q (deriv q 0) 0 :=
    (hq 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hdq0 : HasDerivAt (deriv q) (deriv (deriv q) 0) 0 :=
    (hq.deriv 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hright : HasDerivAt (fun z : ℂ ↦ q z + z * deriv q z)
      (2 * deriv q 0) 0 := by
    convert hq0.add ((hasDerivAt_id 0).mul hdq0) using 1;
      simp [two_mul]
  exact hright.deriv

/--
%%handwave
name: Nonvanishing of the normalized quotient
statement:
  If $f$ is injective on the unit disk, $f(0)=0$, and $f'(0)=1$, then the holomorphic extension $q$ of $f(z)/z$ has no zero in the unit disk.
proof:
  At $0$, $q(0)=1$. If $z\ne0$ and $q(z)=0$, then $f(z)=0=f(0)$, contradicting injectivity.
-/
private theorem diskNormalizedQuotient_ne_zero
    {f : ℂ → ℂ} (hinj : Set.InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∀ z ∈ ball (0 : ℂ) 1, diskNormalizedQuotient f z ≠ 0 := by
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0, h1]
  · rw [diskNormalizedQuotient, if_neg hz0]
    exact div_ne_zero (fun hfz ↦ hz0 (hinj hz (mem_ball_self zero_lt_one)
      (by simpa [h0] using hfz))) hz0

/--
%%handwave
name: Normalized holomorphic square root on the disk
statement:
  If $q$ is holomorphic and nonvanishing on the unit disk with $q(0)=1$, then there is a holomorphic $u$ on the disk such that $u(0)=1$ and $u(z)^2=q(z)$.
proof:
  Integrate the holomorphic logarithmic derivative $q'/q$ to a primitive $L$ with $L(0)=0$. The derivative of $e^L/q$ vanishes, so this quotient is constantly $1$. Then $u=e^{L/2}$ has the required normalization and square.
-/
private theorem analytic_square_root_on_ball
    {q : ℂ → ℂ} (hq : AnalyticOnNhd ℂ q (ball 0 1))
    (hq0 : q 0 = 1) (hne : ∀ z ∈ ball (0 : ℂ) 1, q z ≠ 0) :
    ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u (ball 0 1) ∧ u 0 = 1 ∧
      ∀ z ∈ ball (0 : ℂ) 1, u z ^ 2 = q z := by
  let φ : ℂ → ℂ := fun z ↦ deriv q z / q z
  have hφ : AnalyticOnNhd ℂ φ (ball 0 1) := by
    exact hq.deriv.div hq hne
  rcases hφ.differentiableOn.isExactOn_ball.with_val_at (0 : ℂ) 0 with
    ⟨L, hL0, hL⟩
  have hLdiff : DifferentiableOn ℂ L (ball 0 1) :=
    fun z hz ↦ (hL z hz).differentiableAt.differentiableWithinAt
  have hLanalytic : AnalyticOnNhd ℂ L (ball 0 1) :=
    hLdiff.analyticOnNhd isOpen_ball
  let F : ℂ → ℂ := fun z ↦ Complex.exp (L z) / q z
  have hFderiv : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt F 0 z := by
    intro z hz
    have hqz := (hq z hz).differentiableAt.hasDerivAt
    have h := (hL z hz).cexp.div hqz (hne z hz)
    have hzero :
        (Complex.exp (L z) * φ z * q z - Complex.exp (L z) * deriv q z) /
            q z ^ 2 = 0 := by
      dsimp [φ]
      field_simp [hne z hz]
      ring
    rw [hzero] at h
    exact h
  have hFdiff : DifferentiableOn ℂ F (ball 0 1) :=
    fun z hz ↦ (hFderiv z hz).differentiableAt.differentiableWithinAt
  have hFconst : ∀ z ∈ ball (0 : ℂ) 1, F z = F 0 := by
    intro z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      hFdiff (fun w hw ↦ (hFderiv w hw).deriv) hz (mem_ball_self zero_lt_one)
  have hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (L z) = q z := by
    intro z hz
    have hc := hFconst z hz
    have hF0 : F 0 = 1 := by simp [F, hL0, hq0]
    rw [hF0] at hc
    dsimp [F] at hc
    exact (div_eq_one_iff_eq (hne z hz)).mp hc
  let u : ℂ → ℂ := fun z ↦ Complex.exp (L z / 2)
  have hhalf : AnalyticOnNhd ℂ (fun z ↦ L z / 2) (ball 0 1) :=
    hLanalytic.div analyticOnNhd_const (fun _ _ ↦ by norm_num)
  have hu : AnalyticOnNhd ℂ u (ball 0 1) := by
    simpa [u, Function.comp_def] using
      analyticOnNhd_cexp.comp hhalf (fun _ _ ↦ mem_univ _)
  refine ⟨u, hu, ?_, ?_⟩
  · simp [u, hL0]
  · intro z hz
    change Complex.exp (L z / 2) ^ 2 = q z
    rw [pow_two, ← Complex.exp_add, show L z / 2 + L z / 2 = L z by ring]
    exact hexp z hz

private def oddExteriorRemainder (v : ℂ → ℂ) (b w : ℂ) : ℂ :=
  if w = 0 then 0 else (v (w ^ 2) - 1 - b * w ^ 2) / w

/--
%%handwave
name: Cubic odd remainder after quadratic substitution
statement:
  Let $v$ be holomorphic on the unit disk with $v(0)=1$ and $v'(0)=b$. The function $r(w)=(v(w^2)-1-bw^2)/w$ for $w\ne0$, extended by $r(0)=0$, is holomorphic on the unit disk and satisfies $r(0)=r'(0)=0$.
proof:
  Taylor expansion gives $v(t)=1+bt+t^2H(t)$ near $0$, hence $r(w)=w^3H(w^2)$. This formula proves holomorphicity and the two vanishing conditions at $0$; away from $0$ the original quotient is holomorphic.
-/
private theorem oddExteriorRemainder_properties
    {v : ℂ → ℂ} (hv : AnalyticOnNhd ℂ v (ball 0 1))
    (hv0 : v 0 = 1) {b : ℂ} (hb : deriv v 0 = b) :
    AnalyticOnNhd ℂ (oddExteriorRemainder v b) (ball 0 1) ∧
      oddExteriorRemainder v b 0 = 0 ∧ deriv (oddExteriorRemainder v b) 0 = 0 := by
  rcases (hv 0 (mem_ball_self zero_lt_one)).exists_eq_sum_add_pow_mul 2 with
    ⟨H, hH, heq⟩
  have hform : ∀ t : ℂ, v t = 1 + b * t + t ^ 2 * H t := by
    intro t
    rw [heq]
    simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, hv0, hb,
      smul_eq_mul]
    ring
  have hmodel : ∀ w : ℂ,
      oddExteriorRemainder v b w = w ^ 3 * H (w ^ 2) := by
    intro w
    by_cases hw : w = 0
    · simp [oddExteriorRemainder, hw]
    · rw [oddExteriorRemainder, if_neg hw, hform]
      field_simp [hw]
      ring
  have hanalytic : AnalyticOnNhd ℂ (oddExteriorRemainder v b) (ball 0 1) := by
    intro w hw
    by_cases hw0 : w = 0
    · subst w
      have hsquare : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) 0 := by
        simpa [id_eq] using (analyticAt_id (𝕜 := ℂ) (E := ℂ)).pow 2
      have hH' : AnalyticAt ℂ H ((0 : ℂ) ^ 2) := by simpa using hH
      have hcomp : AnalyticAt ℂ (fun z : ℂ ↦ H (z ^ 2)) 0 := by
        simpa [Function.comp_def] using hH'.comp (f := fun z : ℂ ↦ z ^ 2) hsquare
      have hm : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 3 * H (z ^ 2)) 0 :=
        (analyticAt_id.pow 3).mul hcomp
      exact hm.congr (Filter.Eventually.of_forall (fun z ↦ (hmodel z).symm))
    · have hw2 : w ^ 2 ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_pow]
        have hn := norm_nonneg w
        rw [mem_ball_zero_iff] at hw
        nlinarith [sq_nonneg ‖w‖]
      have hvcomp : AnalyticAt ℂ (fun z : ℂ ↦ v (z ^ 2)) w := by
        have hsquare : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) w := by
          simpa [id_eq] using (analyticAt_id (𝕜 := ℂ) (E := ℂ)).pow 2
        simpa [Function.comp_def] using
          (hv (w ^ 2) hw2).comp (f := fun z : ℂ ↦ z ^ 2) hsquare
      have hquot : AnalyticAt ℂ
          (fun z : ℂ ↦ (v (z ^ 2) - 1 - b * z ^ 2) / z) w :=
        (hvcomp.sub analyticAt_const |>.sub (analyticAt_const.mul (analyticAt_id.pow 2))).div
          analyticAt_id hw0
      apply hquot.congr
      filter_upwards [eventually_ne_nhds hw0] with z hz
      simp [oddExteriorRemainder, hz]
  have hzero : oddExteriorRemainder v b 0 = 0 := by
    simp [oddExteriorRemainder]
  have hmodelDeriv : HasDerivAt (fun w : ℂ ↦ w ^ 3 * H (w ^ 2)) 0 0 := by
    have hsquare : HasDerivAt (fun w : ℂ ↦ w ^ 2) 0 0 := by
      convert (hasDerivAt_id (0 : ℂ)).pow 2 using 1 <;> simp
    have hH' : HasDerivAt H (deriv H 0) ((0 : ℂ) ^ 2) := by
      simpa using hH.differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun w : ℂ ↦ H (w ^ 2)) 0 0 := by
      simpa [Function.comp_def] using hH'.comp
        (h := fun w : ℂ ↦ w ^ 2) (h₂ := H) 0 hsquare
    convert ((hasDerivAt_id (0 : ℂ)).pow 3).mul hcomp using 1 <;> simp
  have hremainderDeriv : HasDerivAt (oddExteriorRemainder v b) 0 0 :=
    hmodelDeriv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall hmodel)
  exact ⟨hanalytic, hzero, hremainderDeriv.deriv⟩

/--
%%handwave
name:
  Bieberbach's second-coefficient estimate
statement:
  Let \(f\) be holomorphic and injective on \(\mathbb D\), with
  \(f(0)=0\) and \(f'(0)=1\). If
  \(f(z)=z+a_2z^2+\cdots\), equivalently
  \(a_2=(f(z)/z)'|_{z=0}\), then \(|a_2|\le2\).
proof:
  Put \(q(z)=f(z)/z\), extended by \(q(0)=1\), and choose the holomorphic
  square root \(u\) with \(u^2=q\) and \(u(0)=1\). Then
  \[
    g(z)=z\,u(z^2)
  \]
  is odd and injective and satisfies \(g(z)^2=f(z^2)\). For \(|\zeta|>1\),
  \[
    G(\zeta)=\frac{1}{g(1/\zeta)}
    =\zeta-\frac{a_2}{2\zeta}+O(\zeta^{-3})
  \]
  is univalent. [Grönwall's area theorem bounds the modulus of the coefficient \(-a_2/2\) by \(1\)](lean:JJMath.ComplexAnalysis.gronwall_area_first_coefficient), so \(|a_2|\le2\).
-/
theorem bieberbach_second_coefficient
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : Set.InjOn f (ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ‖deriv (diskNormalizedQuotient f) 0‖ ≤ 2 := by
  let q := diskNormalizedQuotient f
  have hq : AnalyticOnNhd ℂ q (ball 0 1) :=
    diskNormalizedQuotient_analyticOnNhd hf h0
  have hq0 : q 0 = 1 := by simp [q, h1]
  have hqne : ∀ z ∈ ball (0 : ℂ) 1, q z ≠ 0 :=
    diskNormalizedQuotient_ne_zero hinj h0 h1
  rcases analytic_square_root_on_ball hq hq0 hqne with ⟨u, hu, hu0, huSq⟩
  have hune : ∀ z ∈ ball (0 : ℂ) 1, u z ≠ 0 := by
    intro z hz huz
    exact hqne z hz (by simpa [huz] using (huSq z hz).symm)
  let v : ℂ → ℂ := fun z ↦ (u z)⁻¹
  have hv : AnalyticOnNhd ℂ v (ball 0 1) := by
    simpa [v] using hu.inv hune
  have hv0 : v 0 = 1 := by simp [v, hu0]
  let b : ℂ := deriv v 0
  let h : ℂ → ℂ := oddExteriorRemainder v b
  rcases oddExteriorRemainder_properties hv hv0 (b := b) rfl with ⟨hh, hh0, hh1⟩
  have hsquare_mem : MapsTo (fun z : ℂ ↦ z ^ 2) (ball 0 1) (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff, norm_pow]
    rw [mem_ball_zero_iff] at hz
    nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
  let g : ℂ → ℂ := fun z ↦ z * u (z ^ 2)
  have hg : AnalyticOnNhd ℂ g (ball 0 1) := by
    have hsquare : AnalyticOnNhd ℂ (fun z : ℂ ↦ z ^ 2) (ball 0 1) := by
      simpa [id_eq] using (analyticOnNhd_id (𝕜 := ℂ) (E := ℂ)).pow 2
    have hucomp : AnalyticOnNhd ℂ (fun z : ℂ ↦ u (z ^ 2)) (ball 0 1) := by
      simpa [Function.comp_def] using hu.comp hsquare hsquare_mem
    exact analyticOnNhd_id.mul hucomp
  have hgSq : ∀ z ∈ ball (0 : ℂ) 1, g z ^ 2 = f (z ^ 2) := by
    intro z hz
    calc
      g z ^ 2 = z ^ 2 * u (z ^ 2) ^ 2 := by simp [g]; ring
      _ = z ^ 2 * q (z ^ 2) := by rw [huSq (z ^ 2) (hsquare_mem hz)]
      _ = f (z ^ 2) := by
        simpa [q] using diskNormalizedQuotient_mul h0 (z ^ 2)
  have hgodd : ∀ z : ℂ, g (-z) = -g z := by
    intro z
    simp [g]
  have hginj : Set.InjOn g (ball 0 1) := by
    intro z hz w hw hzw
    have hfsq : f (z ^ 2) = f (w ^ 2) := by
      rw [← hgSq z hz, ← hgSq w hw, hzw]
    have hzsq : z ^ 2 = w ^ 2 := hinj (hsquare_mem hz) (hsquare_mem hw) hfsq
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hzsq) with hEq | hEq
    · exact hEq
    · have hneg : -g w = g w := by
        calc
          -g w = g (-w) := (hgodd w).symm
          _ = g z := by rw [hEq]
          _ = g w := hzw
      have hgw : g w = 0 := by
        linear_combination (-1 / 2 : ℂ) * hneg
      have huw : u (w ^ 2) ≠ 0 := hune (w ^ 2) (hsquare_mem hw)
      have hw0 : w = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right huw
        simpa [g] using hgw
      simpa [hw0] using hEq
  have huDer : HasDerivAt u (deriv u 0) 0 :=
    (hu 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hqDer : HasDerivAt q (deriv q 0) 0 :=
    (hq 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hprodEq : (fun z : ℂ ↦ u z * u z) =ᶠ[𝓝 0] q := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    simpa [pow_two] using huSq z hz
  have hqAsProduct : HasDerivAt (fun z : ℂ ↦ u z * u z) (deriv q 0) 0 :=
    hqDer.congr_of_eventuallyEq hprodEq
  have hdu := (huDer.mul huDer).unique hqAsProduct
  have hinvDer : HasDerivAt v (-deriv u 0) 0 := by
    simpa [v, hu0] using huDer.inv (by simp [hu0])
  have hvDer : HasDerivAt v (deriv v 0) 0 :=
    (hv 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hbdu : b = -deriv u 0 := by
    simpa [b] using hvDer.unique hinvDer
  have hqrel : deriv q 0 = -2 * b := by
    have hdu' : deriv u 0 + deriv u 0 = deriv q 0 := by
      simpa [hu0] using hdu
    have hub : deriv u 0 = -b := by
      linear_combination hbdu
    rw [← hdu', hub]
    ring
  have hidentity : ∀ z : ℂ, 1 < ‖z‖ →
      exteriorLaurentMap b h z = (g z⁻¹)⁻¹ := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hz)
    have hzin : z⁻¹ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_inv]
      exact (inv_lt_one₀ (norm_pos_iff.mpr hz0)).2 hz
    have huz : u (z⁻¹ ^ 2) ≠ 0 := hune (z⁻¹ ^ 2) (hsquare_mem hzin)
    change exteriorLaurentMap b (oddExteriorRemainder v b) z = (g z⁻¹)⁻¹
    simp only [exteriorLaurentMap, oddExteriorRemainder, if_neg (inv_ne_zero hz0)]
    dsimp [g, v]
    field_simp [hz0, huz]
    <;> ring
  have hGinj : Set.InjOn (exteriorLaurentMap b h) {z : ℂ | 1 < ‖z‖} := by
    intro z hz w hw hEq
    have hz0 : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hz)
    have hw0 : w ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hw)
    have hzin : z⁻¹ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_inv]
      exact (inv_lt_one₀ (norm_pos_iff.mpr hz0)).2 hz
    have hwin : w⁻¹ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_inv]
      exact (inv_lt_one₀ (norm_pos_iff.mpr hw0)).2 hw
    rw [hidentity z hz, hidentity w hw] at hEq
    exact inv_inj.mp (hginj hzin hwin (inv_inj.mp hEq))
  have hb := gronwall_area_first_coefficient hh hh0 hh1 hGinj
  change ‖deriv q 0‖ ≤ 2
  calc
    ‖deriv q 0‖ = 2 * ‖b‖ := by rw [hqrel]; norm_num
    _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 2 := by norm_num

/--
%%handwave
name:
  Koebe's one-quarter theorem, normalized form
statement:
  If $f$ is holomorphic and injective on $\mathbb D$, with $f(0)=0$ and
  $f'(0)=1$, then
  \[
    \{w\in\mathbb C:|w|<1/4\}\subseteq f(\mathbb D).
  \]
proof:
  If $a\ne0$ were omitted, then
  $F(z)=a f(z)/(a-f(z))$ would again be normalized and univalent. The second
  coefficients of $f$ and $F$ differ by $1/a$. [Both second coefficients have modulus at most $2$](lean:JJMath.ComplexAnalysis.bieberbach_second_coefficient), hence $|1/a|\le4$ and $|a|\ge1/4$.
-/
theorem koebe_quarter_normalized
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : Set.InjOn f (ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ball (0 : ℂ) (1 / 4 : ℝ) ⊆ f '' ball 0 1 := by
  intro a ha
  by_contra haImage
  have haOmitted : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ a := by
    intro z hz hza
    exact haImage ⟨z, hz, hza⟩
  have ha0 : a ≠ 0 := by
    intro haZero
    apply haImage
    refine ⟨0, mem_ball_self zero_lt_one, ?_⟩
    simpa [haZero] using h0
  let F : ℂ → ℂ := fun z ↦ a * f z / (a - f z)
  have hden : ∀ z ∈ ball (0 : ℂ) 1, a - f z ≠ 0 := by
    intro z hz hzero
    exact haOmitted z hz (sub_eq_zero.mp hzero).symm
  have hF : AnalyticOnNhd ℂ F (ball 0 1) := by
    exact (analyticOnNhd_const.mul hf).div (analyticOnNhd_const.sub hf) hden
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hfDer : HasDerivAt f 1 0 := by
    simpa [h1] using (hf 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hFDer : HasDerivAt F 1 0 := by
    have hquot := (hfDer.const_mul a).div (hfDer.const_sub a) (by simp [h0, ha0])
    convert hquot using 1 <;> simp [h0] <;> field_simp [ha0]
  have hF1 : deriv F 0 = 1 := hFDer.deriv
  have hFinj : Set.InjOn F (ball 0 1) := by
    intro z hz w hw hEq
    have hdz := hden z hz
    have hdw := hden w hw
    dsimp [F] at hEq
    have hfw : f z = f w := by
      field_simp [ha0, hdz, hdw] at hEq
      have hmul : a * (f z - f w) = 0 := by
        linear_combination hEq
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha0)
    exact hinj hz hw hfw
  let q := diskNormalizedQuotient f
  let Q := diskNormalizedQuotient F
  have hq : AnalyticOnNhd ℂ q (ball 0 1) :=
    diskNormalizedQuotient_analyticOnNhd hf h0
  have hq0 : q 0 = 1 := by simp [q, h1]
  have hQformula : ∀ z ∈ ball (0 : ℂ) 1, Q z = a * q z / (a - f z) := by
    intro z hzball
    by_cases hz : z = 0
    · subst z
      simp [Q, q, hF1, h1, h0, ha0]
    · have hdz : a - f z ≠ 0 := hden z hzball
      simp only [Q, q, diskNormalizedQuotient, if_neg hz]
      dsimp [F]
      field_simp [hz, hdz]
  have hqDer : HasDerivAt q (deriv q 0) 0 :=
    (hq 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hQcoef : deriv Q 0 = deriv q 0 + a⁻¹ := by
    have hformulaDer := (hqDer.const_mul a).div (hfDer.const_sub a) (by simp [h0, ha0])
    have hQDer : HasDerivAt Q
        ((a * deriv q 0 * (a - f 0) - a * q 0 * (-1)) / (a - f 0) ^ 2) 0 :=
      hformulaDer.congr_of_eventuallyEq (by
        filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
        exact hQformula z hz)
    rw [hQDer.deriv]
    simp [hq0, h0]
    field_simp [ha0]
  have hcoefF := bieberbach_second_coefficient hF hFinj hF0 hF1
  have hcoeff := bieberbach_second_coefficient hf hinj h0 h1
  have hInvLe : ‖a⁻¹‖ ≤ 4 := by
    calc
      ‖a⁻¹‖ = ‖deriv Q 0 - deriv q 0‖ := by rw [hQcoef]; congr 1; ring
      _ ≤ ‖deriv Q 0‖ + ‖deriv q 0‖ := norm_sub_le _ _
      _ ≤ 2 + 2 := add_le_add hcoefF hcoeff
      _ = 4 := by norm_num
  rw [norm_inv] at hInvLe
  have haNormPos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hquarter : (4 : ℝ)⁻¹ ≤ ‖a‖ :=
    (inv_le_comm₀ haNormPos (by norm_num)).mp hInvLe
  rw [mem_ball_zero_iff] at ha
  norm_num at hquarter
  linarith

/--
%%handwave
name:
  Koebe's one-quarter theorem
statement:
  If $f$ is holomorphic and injective on $\mathbb D$ and $f'(0)\ne0$, then
  \[
    \{w\in\mathbb C:|w-f(0)|<|f'(0)|/4\}\subseteq f(\mathbb D).
  \]
proof:
  [Every normalized univalent disk map contains the open disk of radius $1/4$ in its image](lean:JJMath.ComplexAnalysis.koebe_quarter_normalized). Apply this result to $F(z)=(f(z)-f(0))/f'(0)$ and undo the affine normalization.
-/
theorem koebe_quarter
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : Set.InjOn f (ball 0 1)) (hderiv : deriv f 0 ≠ 0) :
    ball (f 0) (‖deriv f 0‖ / 4) ⊆ f '' ball 0 1 := by
  let d := deriv f 0
  let F : ℂ → ℂ := fun z ↦ (f z - f 0) / d
  have hF : AnalyticOnNhd ℂ F (ball 0 1) := by
    exact (hf.sub analyticOnNhd_const).div analyticOnNhd_const
      (fun _ _ ↦ by simpa [d] using hderiv)
  have hF0 : F 0 = 0 := by simp [F]
  have hfDer : HasDerivAt f d 0 := by
    simpa [d] using (hf 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hFDer : HasDerivAt F 1 0 := by
    have h := (hfDer.sub_const (f 0)).div_const d
    convert h using 1 <;> simp [d, hderiv]
  have hF1 : deriv F 0 = 1 := hFDer.deriv
  have hFinj : Set.InjOn F (ball 0 1) := by
    intro z hz w hw hEq
    dsimp [F] at hEq
    field_simp [d, hderiv] at hEq
    exact hinj hz hw (sub_left_inj.mp hEq)
  have hquarter := koebe_quarter_normalized hF hFinj hF0 hF1
  intro w hw
  let a : ℂ := (w - f 0) / d
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr (by simpa [d] using hderiv)
  have ha : a ∈ ball (0 : ℂ) (1 / 4 : ℝ) := by
    rw [mem_ball_zero_iff]
    dsimp [a]
    rw [norm_div]
    rw [mem_ball, dist_eq_norm] at hw
    rw [div_lt_iff₀ hdpos]
    convert hw using 1 <;> simp [d] <;> ring
  rcases hquarter ha with ⟨z, hz, hza⟩
  refine ⟨z, hz, ?_⟩
  dsimp [F, a] at hza
  field_simp [d, hderiv] at hza
  linear_combination hza

end JJMath.ComplexAnalysis
