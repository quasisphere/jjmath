import JJMath.Hyperbolic.ConformalMetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# The hyperbolic metric on the upper half-plane

This file packages the squared Poincare density on `ℍ`.  Mathlib already
supplies the upper half-plane, its complex manifold structure, and a hyperbolic
distance.  We record the conformal metric language used by the project.
-/

namespace JJMath

open UpperHalfPlane
open Filter
open scoped MatrixGroups Topology

noncomputable section

/-- The squared Poincare density on the upper half-plane: `1 / (Im z)^2`. -/
def poincareDensitySq (z : ℍ) : ℝ :=
  (((z : ℂ).im) ^ 2)⁻¹

/--
The ambient coordinate representative of the Poincare squared density.

This is only used on the upper-half-plane chart target `{z : ℂ | 0 < z.im}`.
-/
def poincareDensitySqInChart (z : ℂ) : ℝ :=
  (z.im ^ 2)⁻¹

@[simp]
theorem poincareDensitySqInChart_coe (z : ℍ) :
    poincareDensitySqInChart (z : ℂ) = poincareDensitySq z :=
  rfl

theorem poincareDensitySq_pos (z : ℍ) : 0 < poincareDensitySq z := by
  exact inv_pos.mpr (sq_pos_of_pos z.im_pos)

/-- The off-real-line locus in the finite affine coordinate. -/
def offRealLineInComplexPlane : Set ℂ :=
  {z | z.im ≠ 0}

/-- The squared hyperbolic density is positive off the real line. -/
theorem poincareDensitySqInChart_pos_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    0 < poincareDensitySqInChart z :=
  inv_pos.mpr (sq_pos_of_ne_zero hz)

/-- Real projective transformations preserve the finite off-real locus. -/
theorem pgl2r_smulAux'_im_ne_zero
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (UpperHalfPlane.smulAux' A z).im ≠ 0 := by
  rw [UpperHalfPlane.smulAux'_im]
  have hdet : |A.det.val| ≠ 0 := abs_ne_zero.mpr A.det_ne_zero
  have hden :
      Complex.normSq (UpperHalfPlane.denom A z) ≠ 0 :=
    UpperHalfPlane.normSq_denom_ne_zero A hz
  exact div_ne_zero (mul_ne_zero hdet hz) hden

/-- Real projective transformations map the finite off-real locus to itself. -/
theorem pgl2r_smulAux'_mem_offRealLine
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z ∈ offRealLineInComplexPlane) :
    UpperHalfPlane.smulAux' A z ∈ offRealLineInComplexPlane :=
  pgl2r_smulAux'_im_ne_zero A hz

/-- The holomorphic real projective formula preserves the finite off-real locus. -/
theorem pgl2r_holomorphic_smul_im_ne_zero
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (UpperHalfPlane.num A z / UpperHalfPlane.denom A z).im ≠ 0 := by
  rw [UpperHalfPlane.moebius_im]
  have hden :
      Complex.normSq (UpperHalfPlane.denom A z) ≠ 0 :=
    UpperHalfPlane.normSq_denom_ne_zero A hz
  exact div_ne_zero (mul_ne_zero A.det_ne_zero hz) hden

/-- The holomorphic real projective formula maps the finite off-real locus to itself. -/
theorem pgl2r_holomorphic_smul_mem_offRealLine
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z ∈ offRealLineInComplexPlane) :
    UpperHalfPlane.num A z / UpperHalfPlane.denom A z ∈ offRealLineInComplexPlane :=
  pgl2r_holomorphic_smul_im_ne_zero A hz

/-- Derivative of the holomorphic real projective formula off the real line. -/
theorem pgl2r_holomorphic_smul_hasDerivAt
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ UpperHalfPlane.num A w / UpperHalfPlane.denom A w)
      ((A.det.val : ℂ) / UpperHalfPlane.denom A z ^ 2) z := by
  convert
    (((hasDerivAt_id z).const_mul (A 0 0 : ℂ)).add_const (A 0 1 : ℂ)).div
      (((hasDerivAt_id z).const_mul (A 1 0 : ℂ)).add_const (A 1 1 : ℂ))
      (UpperHalfPlane.denom_ne_zero_of_im A hz)
    using 1
  · simp [UpperHalfPlane.denom, Matrix.det_fin_two]
    ring

/-- Derivative of the holomorphic real projective formula off the real line. -/
theorem pgl2r_holomorphic_smul_deriv
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    deriv (fun w : ℂ ↦ UpperHalfPlane.num A w / UpperHalfPlane.denom A w) z =
      (A.det.val : ℂ) / UpperHalfPlane.denom A z ^ 2 :=
  (pgl2r_holomorphic_smul_hasDerivAt A hz).deriv

/-- Norm-squared derivative scale of the holomorphic real projective formula. -/
theorem pgl2r_holomorphic_smul_deriv_normSq
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Complex.normSq
        (deriv (fun w : ℂ ↦ UpperHalfPlane.num A w / UpperHalfPlane.denom A w) z) =
      (|A.det.val| / Complex.normSq (UpperHalfPlane.denom A z)) ^ 2 := by
  rw [pgl2r_holomorphic_smul_deriv A hz]
  simp [Complex.normSq_ofReal, sq_abs, div_pow]
  ring

/--
%%handwave
name:
  Real projective transformations preserve the off-real-line density
statement:
  A real projective Möbius transformation preserves the squared hyperbolic
  density $\operatorname{Im}(z)^{-2}$ on the complement of the real projective
  line.
proof:
  If $A \in \mathrm{PGL}_2(\mathbb R)$ is represented by a real matrix
  and its conformal scale at $z$ is $|\det A|/|cz+d|^2$, then the transformed
  density times the square of this scale is the original density. The same
  formula applies on the upper and lower half-planes because the density uses
  $\operatorname{Im}(z)^2$.
-/
theorem pgl2r_preserves_offRealLineDensity
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (((UpperHalfPlane.smulAux' A z).im ^ 2)⁻¹) *
        ((|A.det.val| / Complex.normSq (UpperHalfPlane.denom A z)) ^ 2) =
      (z.im ^ 2)⁻¹ := by
  have him :
      (UpperHalfPlane.smulAux' A z).im =
        |A.det.val| * z.im / Complex.normSq (UpperHalfPlane.denom A z) :=
    UpperHalfPlane.smulAux'_im A z
  have hdet : |A.det.val| ≠ 0 := abs_ne_zero.mpr A.det_ne_zero
  have hden :
      Complex.normSq (UpperHalfPlane.denom A z) ≠ 0 :=
    UpperHalfPlane.normSq_denom_ne_zero A hz
  rw [him]
  field_simp [hdet, hden, hz]

/--
The holomorphic real projective formula preserves the off-real-line
hyperbolic density with the derivative scale.
-/
theorem pgl2r_preserves_offRealLineDensity_holomorphic
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    poincareDensitySqInChart (UpperHalfPlane.num A z / UpperHalfPlane.denom A z) *
        Complex.normSq
          (deriv (fun w : ℂ ↦ UpperHalfPlane.num A w / UpperHalfPlane.denom A w) z) =
      poincareDensitySqInChart z := by
  rw [poincareDensitySqInChart, pgl2r_holomorphic_smul_deriv_normSq A hz]
  have him :
      (UpperHalfPlane.num A z / UpperHalfPlane.denom A z).im =
        A.det.val * z.im / Complex.normSq (UpperHalfPlane.denom A z) :=
    UpperHalfPlane.moebius_im A z
  have hdet : |A.det.val| ≠ 0 := abs_ne_zero.mpr A.det_ne_zero
  have hden :
      Complex.normSq (UpperHalfPlane.denom A z) ≠ 0 :=
    UpperHalfPlane.normSq_denom_ne_zero A hz
  rw [him]
  field_simp [hdet, hden, hz]
  rw [sq_abs]
  rw [poincareDensitySqInChart]
  field_simp [pow_ne_zero 2 hz]
  field_simp [A.det_ne_zero]

/-- The off-real-line density computation specialized to the upper half-plane. -/
theorem pgl2r_preserves_poincareDensitySq
    (A : GL (Fin 2) ℝ) (z : ℍ) :
    poincareDensitySq (A • z) *
        ((|A.det.val| / Complex.normSq (UpperHalfPlane.denom A (z : ℂ))) ^ 2) =
      poincareDensitySq z := by
  simpa [poincareDensitySq, UpperHalfPlane.smulAux]
    using pgl2r_preserves_offRealLineDensity A (z := (z : ℂ)) z.im_ne_zero

theorem poincareDensitySqInChart_pos
    (e : OpenPartialHomeomorph ℍ ℂ) (he : e ∈ atlas ℂ ℍ) (z : ℂ)
    (hz : z ∈ e.target) : 0 < poincareDensitySqInChart z := by
  have heq : e = chartAt ℂ (⟨I, by norm_num⟩ : ℍ) := by
    simpa using he
  subst e
  have hz_im : 0 < z.im := by
    simpa using hz
  exact inv_pos.mpr (sq_pos_of_pos hz_im)

theorem poincareDensitySqInChart_contDiffOn :
    ∀ (e : OpenPartialHomeomorph ℍ ℂ),
      e ∈ atlas ℂ ℍ → ContDiffOn ℝ ⊤ poincareDensitySqInChart e.target := by
  intro e he
  have heq : e = chartAt ℂ (⟨I, by norm_num⟩ : ℍ) := by
    simpa using he
  subst e
  have him' : ContDiff ℝ ⊤ (Complex.imCLM : ℂ → ℝ) :=
    (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff (𝕜 := ℝ) (n := ⊤)
  have him : ContDiff ℝ ⊤ (fun z : ℂ ↦ (z.im : ℝ)) := by
    convert him' using 1
  have hsquare :
      ContDiffOn ℝ ⊤ (fun z : ℂ ↦ ((z.im : ℝ) ^ 2))
        ((chartAt ℂ (⟨I, by norm_num⟩ : ℍ)).target) := by
    simpa using (him.pow 2).contDiffOn
  refine hsquare.inv ?_
  intro z hz
  have hz_im : 0 < z.im := by
    simpa using hz
  exact pow_ne_zero 2 (ne_of_gt hz_im)

/-- The finite `C^3` regularity of the Poincare squared density. -/
theorem poincareDensitySqInChart_contDiffOn_three :
    ∀ (e : OpenPartialHomeomorph ℍ ℂ),
      e ∈ atlas ℂ ℍ → ContDiffOn ℝ 3 poincareDensitySqInChart e.target :=
  fun e he ↦ (poincareDensitySqInChart_contDiffOn e he).of_le le_top

/-- The off-real-line squared density is smooth on the complement of the real line. -/
theorem poincareDensitySqInChart_contDiffOn_offRealLine :
    ContDiffOn ℝ ⊤ poincareDensitySqInChart offRealLineInComplexPlane := by
  have him' : ContDiff ℝ ⊤ (Complex.imCLM : ℂ → ℝ) :=
    (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff (𝕜 := ℝ) (n := ⊤)
  have him : ContDiff ℝ ⊤ (fun z : ℂ ↦ (z.im : ℝ)) := by
    convert him' using 1
  have hsquare : ContDiffOn ℝ ⊤ (fun z : ℂ ↦ ((z.im : ℝ) ^ 2))
      offRealLineInComplexPlane := by
    simpa using (him.pow 2).contDiffOn
  refine hsquare.inv ?_
  intro z hz
  exact pow_ne_zero 2 hz

theorem poincareDensitySqInChart_transition :
    ∀ (e : OpenPartialHomeomorph ℍ ℂ), e ∈ atlas ℂ ℍ →
      ∀ (e' : OpenPartialHomeomorph ℍ ℂ), e' ∈ atlas ℂ ℍ → ∀ z,
        z ∈ e.target →
        e.symm z ∈ e'.source →
        poincareDensitySqInChart z =
          poincareDensitySqInChart (e' (e.symm z)) *
            Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z) := by
  intro e he e' he' z hz _hz'
  have heq : e = chartAt ℂ (⟨I, by norm_num⟩ : ℍ) := by
    simpa using he
  have heq' : e' = chartAt ℂ (⟨I, by norm_num⟩ : ℍ) := by
    simpa using he'
  subst e
  subst e'
  let c : OpenPartialHomeomorph ℍ ℂ := chartAt ℂ (⟨I, by norm_num⟩ : ℍ)
  change poincareDensitySqInChart z =
    poincareDensitySqInChart (c (c.symm z)) *
      Complex.normSq (deriv (fun w : ℂ ↦ c (c.symm w)) z)
  have hval : c (c.symm z) = z := c.right_inv hz
  have hev : (fun w : ℂ ↦ c (c.symm w)) =ᶠ[𝓝 z] fun w : ℂ ↦ w :=
    c.eventually_right_inverse hz
  have hderiv : deriv (fun w : ℂ ↦ c (c.symm w)) z = 1 := by
    simpa using (hev.deriv_eq (𝕜 := ℂ))
  rw [hval, hderiv]
  simp [poincareDensitySqInChart]

private theorem neg_log_im_hasFDerivAt (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ - Real.log w.im)
      (- (z.im)⁻¹ • (Complex.imCLM : ℂ →L[ℝ] ℝ)) z := by
  have him : HasFDerivAt (fun w : ℂ ↦ w.im) (Complex.imCLM : ℂ →L[ℝ] ℝ) z := by
    simpa [Complex.imCLM_apply] using
      (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt (x := z)
  convert (him.log hz).neg using 1
  · ext w
    simp

private theorem neg_inv_im_smul_hasFDerivAt (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt
      (fun w : ℂ ↦ (- (w.im)⁻¹) • (Complex.imCLM : ℂ →L[ℝ] ℝ))
      ((- ((ContinuousLinearMap.toSpanSingleton ℝ (-(z.im ^ 2)⁻¹)).comp
        (Complex.imCLM : ℂ →L[ℝ] ℝ))).smulRight
          (Complex.imCLM : ℂ →L[ℝ] ℝ)) z := by
  have him : HasFDerivAt (fun w : ℂ ↦ w.im) (Complex.imCLM : ℂ →L[ℝ] ℝ) z := by
    simpa [Complex.imCLM_apply] using
      (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt (x := z)
  have hinv : HasFDerivAt (fun w : ℂ ↦ (w.im)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(z.im ^ 2)⁻¹)).comp
        (Complex.imCLM : ℂ →L[ℝ] ℝ)) z :=
    (hasFDerivAt_inv (𝕜 := ℝ) hz).comp z him
  have hs : HasFDerivAt (fun w : ℂ ↦ - (w.im)⁻¹)
      (- ((ContinuousLinearMap.toSpanSingleton ℝ (-(z.im ^ 2)⁻¹)).comp
        (Complex.imCLM : ℂ →L[ℝ] ℝ))) z := by
    simpa using hinv.neg
  exact hs.smul_const (Complex.imCLM : ℂ →L[ℝ] ℝ)

/--
%%handwave
name:
  Laplacian of logarithmic height
statement:
  Write $z=x+iy$ with $y\ne0$. On either half-plane, the function
  $u(z)=-\log|y|$ satisfies
  $\Delta u(z)=1/y^2$.
proof:
  The function is independent of $x$, while
  $\partial u/\partial y=-1/y$ and
  $\partial^2u/\partial y^2=1/y^2$. Thus its Euclidean Laplacian is
  $0+1/y^2$.
-/
theorem laplacian_neg_log_im (z : ℂ) (hz : z.im ≠ 0) :
    Laplacian.laplacian (fun w : ℂ ↦ - Real.log w.im) z = (z.im ^ 2)⁻¹ := by
  let A : ℂ → ℂ →L[ℝ] ℝ :=
    fun w ↦ (- (w.im)⁻¹) • (Complex.imCLM : ℂ →L[ℝ] ℝ)
  have hne_ev : ∀ᶠ w in 𝓝 z, w.im ≠ 0 :=
    (Complex.continuous_im.continuousAt (x := z)).preimage_mem_nhds (isOpen_ne.mem_nhds hz)
  have hfderiv_ev :
      fderiv ℝ (fun w : ℂ ↦ - Real.log w.im) =ᶠ[𝓝 z] A := by
    filter_upwards [hne_ev] with w hw
    exact (neg_log_im_hasFDerivAt w hw).fderiv
  have hAderiv : fderiv ℝ A z =
      (- ((ContinuousLinearMap.toSpanSingleton ℝ (-(z.im ^ 2)⁻¹)).comp
        (Complex.imCLM : ℂ →L[ℝ] ℝ))).smulRight
          (Complex.imCLM : ℂ →L[ℝ] ℝ) :=
    (neg_inv_im_smul_hasFDerivAt z hz).fderiv
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [Filter.EventuallyEq.fderiv_eq hfderiv_ev, hAderiv]
  simp [Complex.imCLM_apply]

/-- The logarithm of the imaginary coordinate has Laplacian `-1 / y^2`. -/
theorem laplacian_log_im (z : ℂ) (hz : z.im ≠ 0) :
    Laplacian.laplacian (fun w : ℂ ↦ Real.log w.im) z = - (z.im ^ 2)⁻¹ := by
  have hneg := laplacian_neg_log_im z hz
  rw [show (fun w : ℂ ↦ - Real.log w.im) =
      -(fun w : ℂ ↦ Real.log w.im) by
        rfl] at hneg
  rw [InnerProductSpace.laplacian_neg] at hneg
  have hneg' :
      - Laplacian.laplacian (fun w : ℂ ↦ Real.log w.im) z =
        (z.im ^ 2)⁻¹ := by
    simpa using hneg
  linarith

private theorem logDensity_poincareDensitySqInChart_eq_neg_log_im (z : ℂ) :
    logDensityFromDensitySq poincareDensitySqInChart z = - Real.log z.im := by
  simp [logDensityFromDensitySq, poincareDensitySqInChart]
  ring

/--
%%handwave
name:
  Curvature of the Poincaré metric
statement:
  On the upper half-plane $\mathbb H$, the conformal metric
  $g_{\mathbb H}=|dz|^2/(\operatorname{Im}z)^2$ has Gaussian curvature
  identically equal to $-1$.
proof:
  [For $u(z)=-\log(\operatorname{Im}z)$ one has $\Delta u=(\operatorname{Im}z)^{-2}$](lean:JJMath.laplacian_neg_log_im). Since $e^{2u}=(\operatorname{Im}z)^{-2}$, substitution in $K=-e^{-2u}\Delta u$ gives $K=-1$.
-/
theorem poincareDensitySqInChart_gaussianCurvature_eq_minus_one :
    ∀ (e : OpenPartialHomeomorph ℍ ℂ), e ∈ atlas ℂ ℍ → ∀ z,
      z ∈ e.target →
        gaussianCurvatureOfDensitySq poincareDensitySqInChart z = -1 := by
  intro e he z hz
  have heq : e = chartAt ℂ (⟨I, by norm_num⟩ : ℍ) := by
    simpa using he
  subst e
  have hz_im : 0 < z.im := by
    simpa using hz
  have hlog_ev :
      logDensityFromDensitySq poincareDensitySqInChart =ᶠ[𝓝 z]
        fun w : ℂ ↦ - Real.log w.im := by
    filter_upwards with w
    exact logDensity_poincareDensitySqInChart_eq_neg_log_im w
  have hlap : Laplacian.laplacian (logDensityFromDensitySq poincareDensitySqInChart) z =
      (z.im ^ 2)⁻¹ := by
    rw [(InnerProductSpace.laplacian_congr_nhds hlog_ev).eq_of_nhds]
    exact laplacian_neg_log_im z (ne_of_gt hz_im)
  have hlogz :
      logDensityFromDensitySq poincareDensitySqInChart z = - Real.log z.im :=
    logDensity_poincareDensitySqInChart_eq_neg_log_im z
  simp [gaussianCurvatureOfDensitySq, hlogz, hlap]
  have hexp : Real.exp (2 * Real.log z.im) = z.im ^ 2 := by
    rw [show 2 * Real.log z.im = Real.log (z.im ^ 2) by
      rw [Real.log_pow]
      norm_num]
    exact Real.exp_log (sq_pos_of_pos hz_im)
  rw [hexp]
  field_simp [pow_ne_zero 2 (ne_of_gt hz_im)]

/--
Computed Gaussian curvature of the off-real-line density on either half-plane.

The density is the same formula as the Poincare density, but this form only
requires that the point is not on the real line.
-/
theorem offRealLineDensitySq_gaussianCurvature_eq_minus_one
    {z : ℂ} (hz : z.im ≠ 0) :
    gaussianCurvatureOfDensitySq poincareDensitySqInChart z = -1 := by
  have hlog_ev :
      logDensityFromDensitySq poincareDensitySqInChart =ᶠ[𝓝 z]
        fun w : ℂ ↦ - Real.log w.im := by
    filter_upwards with w
    exact logDensity_poincareDensitySqInChart_eq_neg_log_im w
  have hlap : Laplacian.laplacian (logDensityFromDensitySq poincareDensitySqInChart) z =
      (z.im ^ 2)⁻¹ := by
    rw [(InnerProductSpace.laplacian_congr_nhds hlog_ev).eq_of_nhds]
    exact laplacian_neg_log_im z hz
  have hlogz :
      logDensityFromDensitySq poincareDensitySqInChart z = - Real.log z.im :=
    logDensity_poincareDensitySqInChart_eq_neg_log_im z
  simp [gaussianCurvatureOfDensitySq, hlogz, hlap]
  have hexp : Real.exp (2 * Real.log z.im) = z.im ^ 2 := by
    rw [show 2 * Real.log z.im = Real.log (z.im ^ 2) by
      rw [Real.log_pow]
      norm_num]
    exact Real.exp_log (sq_pos_of_ne_zero hz)
  rw [hexp]
  field_simp [pow_ne_zero 2 hz]

/--
Continuity of the Poincare squared density on the upper half-plane.
-/
theorem poincareDensitySq_continuous : Continuous poincareDensitySq := by
  have him : Continuous fun z : ℍ ↦ (z : ℂ).im :=
    UpperHalfPlane.continuous_im
  simpa [poincareDensitySq] using
    (him.pow 2).inv₀ (fun z ↦ pow_ne_zero 2 (ne_of_gt z.im_pos))

/--
The conformal Poincare metric on `ℍ`, represented by squared density
`1 / (Im z)^2`.
-/
def upperHalfPlaneConformalMetric : ConformalMetric ℍ where
  chartedDensity := {
    densitySqInChart := fun _ _ ↦ poincareDensitySqInChart
    densitySq_pos := poincareDensitySqInChart_pos
    densitySq_transition := poincareDensitySqInChart_transition }

/-- The upper half-plane as a hyperbolic Riemann surface. -/
def upperHalfPlaneHyperbolicMetric : HyperbolicMetric ℍ where
  toConformalMetric := upperHalfPlaneConformalMetric
  smooth := poincareDensitySqInChart_contDiffOn
  curvature_minus_one := by
    intro e he z hz
    exact poincareDensitySqInChart_gaussianCurvature_eq_minus_one e he z hz

end

end JJMath
