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

/--
%%handwave
name:
  The chart and intrinsic Poincaré densities agree
statement:
  For every $z\in\mathbb H$, evaluating the ambient density
  $\operatorname{Im}(w)^{-2}$ at $w=z$ gives the intrinsic squared
  Poincaré density: $\rho_{\mathbb H}^2(z)=\operatorname{Im}(z)^{-2}$.
proof:
  This is immediate from the definitions of the two density functions.
-/
@[simp]
theorem poincareDensitySqInChart_coe (z : ℍ) :
    poincareDensitySqInChart (z : ℂ) = poincareDensitySq z :=
  rfl

/--
%%handwave
name:
  Positivity of the Poincaré density
statement:
  The squared Poincaré density satisfies $\rho_{\mathbb H}^2(z)>0$ for every
  $z\in\mathbb H$.
proof:
  The imaginary part of a point of $\mathbb H$ is positive, so its square and
  the reciprocal of that square are positive.
-/
theorem poincareDensitySq_pos (z : ℍ) : 0 < poincareDensitySq z := by
  exact inv_pos.mpr (sq_pos_of_pos z.im_pos)

/-- The off-real-line locus in the finite affine coordinate. -/
def offRealLineInComplexPlane : Set ℂ :=
  {z | z.im ≠ 0}

/-- The squared hyperbolic density is positive off the real line.

%%handwave
name:
  Positivity of the off-real-line density
statement:
  If $z\in\mathbb C$ has $\operatorname{Im}z\ne0$, then
  $(\operatorname{Im}z)^{-2}>0$.
proof:
  A nonzero real number has positive square, and the reciprocal of a positive
  number is positive.
-/
theorem poincareDensitySqInChart_pos_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    0 < poincareDensitySqInChart z :=
  inv_pos.mpr (sq_pos_of_ne_zero hz)

/-- Real projective transformations preserve the finite off-real locus.

%%handwave
name:
  A real Möbius transformation has nonreal image off the real line
statement:
  Let $A\in\mathrm{GL}_2(\mathbb R)$ and let $z\in\mathbb C$ satisfy
  $\operatorname{Im}z\ne0$. Then the real projective action of $A$ at $z$
  also has nonzero imaginary part.
proof:
  The imaginary-part formula is
  $\operatorname{Im}(A\cdot z)=|\det A|\operatorname{Im}z/|cz+d|^2$.
  Its determinant, numerator height, and denominator are all nonzero.
-/
theorem pgl2r_smulAux'_im_ne_zero
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (UpperHalfPlane.smulAux' A z).im ≠ 0 := by
  rw [UpperHalfPlane.smulAux'_im]
  have hdet : |A.det.val| ≠ 0 := abs_ne_zero.mpr A.det_ne_zero
  have hden :
      Complex.normSq (UpperHalfPlane.denom A z) ≠ 0 :=
    UpperHalfPlane.normSq_denom_ne_zero A hz
  exact div_ne_zero (mul_ne_zero hdet hz) hden

/-- Real projective transformations map the finite off-real locus to itself.

%%handwave
name:
  Invariance of the finite off-real locus
statement:
  Every $A\in\mathrm{GL}_2(\mathbb R)$ maps
  $\mathbb C\setminus\mathbb R$ into $\mathbb C\setminus\mathbb R$ under its
  real projective action.
proof:
  Apply [the image has nonzero imaginary part whenever the original point does](lean:JJMath.pgl2r_smulAux'_im_ne_zero).
-/
theorem pgl2r_smulAux'_mem_offRealLine
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z ∈ offRealLineInComplexPlane) :
    UpperHalfPlane.smulAux' A z ∈ offRealLineInComplexPlane :=
  pgl2r_smulAux'_im_ne_zero A hz

/-- The holomorphic real projective formula preserves the finite off-real locus.

%%handwave
name:
  The holomorphic real Möbius formula remains nonreal
statement:
  If $A=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$ and
  $\operatorname{Im}z\ne0$, then
  $\operatorname{Im}((az+b)/(cz+d))\ne0$.
proof:
  Use
  $\operatorname{Im}((az+b)/(cz+d))=(\det A)\operatorname{Im}z/|cz+d|^2$;
  all three factors relevant to nonvanishing are nonzero.
-/
theorem pgl2r_holomorphic_smul_im_ne_zero
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (UpperHalfPlane.num A z / UpperHalfPlane.denom A z).im ≠ 0 := by
  rw [UpperHalfPlane.moebius_im]
  have hden :
      Complex.normSq (UpperHalfPlane.denom A z) ≠ 0 :=
    UpperHalfPlane.normSq_denom_ne_zero A hz
  exact div_ne_zero (mul_ne_zero A.det_ne_zero hz) hden

/-- The holomorphic real projective formula maps the finite off-real locus to itself.

%%handwave
name:
  The holomorphic real Möbius formula preserves the off-real locus
statement:
  For $A\in\mathrm{GL}_2(\mathbb R)$, the map
  $z\mapsto(az+b)/(cz+d)$ sends $\mathbb C\setminus\mathbb R$ into itself.
proof:
  Apply [the transformed point has nonzero imaginary part](lean:JJMath.pgl2r_holomorphic_smul_im_ne_zero).
-/
theorem pgl2r_holomorphic_smul_mem_offRealLine
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z ∈ offRealLineInComplexPlane) :
    UpperHalfPlane.num A z / UpperHalfPlane.denom A z ∈ offRealLineInComplexPlane :=
  pgl2r_holomorphic_smul_im_ne_zero A hz

/-- Derivative of the holomorphic real projective formula off the real line.

%%handwave
name:
  Derivative of a real Möbius transformation
statement:
  Let $A=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$.
  At every $z$ with $\operatorname{Im}z\ne0$, the map
  $f(w)=(aw+b)/(cw+d)$ has complex derivative
  $f'(z)=\det(A)/(cz+d)^2$.
proof:
  Since $cz+d\ne0$, the quotient rule gives
  $f'(z)=(a(cz+d)-c(az+b))/(cz+d)^2$; the numerator is $ad-bc=\det A$.
-/
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

/-- Derivative of the holomorphic real projective formula off the real line.

%%handwave
name:
  Value of the derivative of a real Möbius transformation
statement:
  For $A=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$ and
  $\operatorname{Im}z\ne0$,
  $\frac{d}{dz}\frac{az+b}{cz+d}=\det(A)/(cz+d)^2$.
proof:
  This is the derivative value supplied by [the corresponding differentiability formula](lean:JJMath.pgl2r_holomorphic_smul_hasDerivAt).
-/
theorem pgl2r_holomorphic_smul_deriv
    (A : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    deriv (fun w : ℂ ↦ UpperHalfPlane.num A w / UpperHalfPlane.denom A w) z =
      (A.det.val : ℂ) / UpperHalfPlane.denom A z ^ 2 :=
  (pgl2r_holomorphic_smul_hasDerivAt A hz).deriv

/-- Norm-squared derivative scale of the holomorphic real projective formula.

%%handwave
name:
  Conformal scale of a real Möbius transformation
statement:
  For $A=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$ and
  $\operatorname{Im}z\ne0$, the squared norm of the complex derivative of
  $f(z)=(az+b)/(cz+d)$ is
  $|f'(z)|^2=(|\det A|/|cz+d|^2)^2$.
proof:
  Substitute [the formula $f'(z)=\det(A)/(cz+d)^2$](lean:JJMath.pgl2r_holomorphic_smul_deriv) and take complex norm-squares.
-/
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

%%handwave
name:
  Möbius invariance of the off-real-line hyperbolic density
statement:
  Let $A=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$,
  $f(z)=(az+b)/(cz+d)$, and $\operatorname{Im}z\ne0$. Then
  $\operatorname{Im}(f(z))^{-2}|f'(z)|^2=\operatorname{Im}(z)^{-2}$.
proof:
  Substitute
  $\operatorname{Im}(f(z))=(\det A)\operatorname{Im}z/|cz+d|^2$ and
  [$|f'(z)|^2=(|\det A|/|cz+d|^2)^2$](lean:JJMath.pgl2r_holomorphic_smul_deriv_normSq); the determinant and denominator factors cancel.
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

/-- The off-real-line density computation specialized to the upper half-plane.

%%handwave
name:
  Real projective invariance of the Poincaré density
statement:
  For $A\in\mathrm{GL}_2(\mathbb R)$ and $z\in\mathbb H$,
  $\rho_{\mathbb H}^2(A\cdot z)(|\det A|/|cz+d|^2)^2=
  \rho_{\mathbb H}^2(z)$.
proof:
  Regard $z$ as a complex number with nonzero imaginary part and apply
  [the off-real-line density transformation formula](lean:JJMath.pgl2r_preserves_offRealLineDensity).
-/
theorem pgl2r_preserves_poincareDensitySq
    (A : GL (Fin 2) ℝ) (z : ℍ) :
    poincareDensitySq (A • z) *
        ((|A.det.val| / Complex.normSq (UpperHalfPlane.denom A (z : ℂ))) ^ 2) =
      poincareDensitySq z := by
  simpa [poincareDensitySq, UpperHalfPlane.smulAux]
    using pgl2r_preserves_offRealLineDensity A (z := (z : ℂ)) z.im_ne_zero

/--
%%handwave
name:
  Positivity of the Poincaré density in every atlas chart
statement:
  If $e$ is a complex-manifold chart of $\mathbb H$ and $z$ lies in its
  coordinate target, then $\operatorname{Im}(z)^{-2}>0$.
proof:
  The upper half-plane has its standard global chart, whose target consists
  of points with positive imaginary part; the reciprocal square is positive.
-/
theorem poincareDensitySqInChart_pos
    (e : OpenPartialHomeomorph ℍ ℂ) (he : e ∈ atlas ℂ ℍ) (z : ℂ)
    (hz : z ∈ e.target) : 0 < poincareDensitySqInChart z := by
  have heq : e = chartAt ℂ (⟨I, by norm_num⟩ : ℍ) := by
    simpa using he
  subst e
  have hz_im : 0 < z.im := by
    simpa using hz
  exact inv_pos.mpr (sq_pos_of_pos hz_im)

/--
%%handwave
name:
  Smoothness of the Poincaré density in upper-half-plane coordinates
statement:
  In every complex-manifold chart $e$ of $\mathbb H$, the function
  $z\mapsto\operatorname{Im}(z)^{-2}$ is smooth on the coordinate target of
  $e$.
proof:
  Every atlas chart is the standard chart. The imaginary-part map is linear
  and smooth, squaring preserves smoothness, and inversion is smooth because
  the imaginary part is positive on the chart target.
-/
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

/-- The finite `C^3` regularity of the Poincare squared density.

%%handwave
name:
  Three-times differentiability of the Poincaré density
statement:
  In every complex-manifold chart $e$ of $\mathbb H$, the squared Poincaré
  density $z\mapsto\operatorname{Im}(z)^{-2}$ is of class $C^3$ on the
  coordinate target of $e$.
proof:
  [The density is smooth on every chart target](lean:JJMath.poincareDensitySqInChart_contDiffOn), hence in particular it is $C^3$ there.
-/
theorem poincareDensitySqInChart_contDiffOn_three :
    ∀ (e : OpenPartialHomeomorph ℍ ℂ),
      e ∈ atlas ℂ ℍ → ContDiffOn ℝ 3 poincareDensitySqInChart e.target :=
  fun e he ↦ (poincareDensitySqInChart_contDiffOn e he).of_le le_top

/-- The off-real-line squared density is smooth on the complement of the real line.

%%handwave
name:
  Smoothness of the reciprocal-square height off the real line
statement:
  The function $z\mapsto\operatorname{Im}(z)^{-2}$ is smooth on
  $\mathbb C\setminus\mathbb R$.
proof:
  The imaginary-part map is linear and smooth. Its square is smooth and
  nonzero away from the real line, so its reciprocal is smooth there.
-/
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

/--
%%handwave
name:
  Coordinate transformation law for the Poincaré density
statement:
  If $e,e'$ are complex-manifold charts of $\mathbb H$, $z$ lies in the
  target of $e$, and the corresponding point lies in the source of $e'$, then
  $$\operatorname{Im}(z)^{-2}=\operatorname{Im}(e'(e^{-1}z))^{-2}
  \left|\frac{d}{dz}(e'\circ e^{-1})(z)\right|^2.$$
proof:
  Both atlas charts are the standard global coordinate, so their transition
  is locally the identity. Its value is $z$ and its derivative is $1$.
-/
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

/--
%%handwave
name:
  Differential of negative logarithmic height
statement:
  For $z\in\mathbb C$ with $y=\operatorname{Im}z\ne0$, the real differential
  of $w\mapsto-\log(\operatorname{Im}w)$ at $z$ is
  $h\mapsto-y^{-1}\operatorname{Im}h$.
proof:
  Compose the differential $h\mapsto\operatorname{Im}h$ with the derivative
  of $t\mapsto-\log t$, namely multiplication by $-1/y$.
-/
private theorem neg_log_im_hasFDerivAt (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ - Real.log w.im)
      (- (z.im)⁻¹ • (Complex.imCLM : ℂ →L[ℝ] ℝ)) z := by
  have him : HasFDerivAt (fun w : ℂ ↦ w.im) (Complex.imCLM : ℂ →L[ℝ] ℝ) z := by
    simpa [Complex.imCLM_apply] using
      (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt (x := z)
  convert (him.log hz).neg using 1
  · ext w
    simp

/--
%%handwave
name:
  Differential of the first derivative of negative logarithmic height
statement:
  Let $L(h)=\operatorname{Im}h$. For $z\in\mathbb C$ with
  $y=\operatorname{Im}z\ne0$, the operator-valued map
  $w\mapsto-(\operatorname{Im}w)^{-1}L$ has differential at $z$ equal to the
  rank-one bilinear operator $(h,k)\mapsto y^{-2}L(h)L(k)$.
proof:
  Differentiate $t\mapsto-t^{-1}$ at $t=y$, compose with the linear map
  $w\mapsto\operatorname{Im}w$, and multiply the resulting scalar derivative
  by the fixed functional $L$.
-/
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

/-- The logarithm of the imaginary coordinate has Laplacian `-1 / y^2`.

%%handwave
name:
  Laplacian of logarithmic height
statement:
  For $z\in\mathbb C$ with $y=\operatorname{Im}z\ne0$,
  $\Delta\log(\operatorname{Im}w)|_{w=z}=-y^{-2}$.
proof:
  [The Laplacian of $-\log(\operatorname{Im}w)$ is $y^{-2}$](lean:JJMath.laplacian_neg_log_im), and the Laplacian changes sign when the function is negated.
-/
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

/--
%%handwave
name:
  Logarithmic Poincaré density
statement:
  For every $z\in\mathbb C$, the logarithmic density associated with
  $\operatorname{Im}(z)^{-2}$ is $-\log(\operatorname{Im}z)$; equivalently,
  $\tfrac12\log((\operatorname{Im}z)^2)^{-1}=-\log(\operatorname{Im}z)$.
proof:
  Apply the logarithm identities for reciprocals and squares. The real
  logarithm depends only on absolute value, so the formula also holds when
  the imaginary part is negative; at zero both sides use the same extended
  convention.
-/
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

%%handwave
name:
  Curvature of reciprocal-square height on both half-planes
statement:
  At every $z\in\mathbb C$ with $\operatorname{Im}z\ne0$, the conformal
  density $\operatorname{Im}(z)^{-2}$ has Gaussian curvature $-1$.
proof:
  Its logarithmic density is $u(z)=-\log(\operatorname{Im}z)$ and
  [$\Delta u(z)=\operatorname{Im}(z)^{-2}$](lean:JJMath.laplacian_neg_log_im). Since $e^{2u}=\operatorname{Im}(z)^{-2}$, the formula $K=-e^{-2u}\Delta u$ gives $K=-1$.
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

%%handwave
name:
  Continuity of the Poincaré density
statement:
  The function $z\mapsto\operatorname{Im}(z)^{-2}$ is continuous on
  $\mathbb H$.
proof:
  The imaginary-part function is continuous and never vanishes on
  $\mathbb H$; squaring and then taking the reciprocal therefore preserves
  continuity.
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
