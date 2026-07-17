import JJMath.Hyperbolic.Converse.Setup

/-!
# Schwarzian boundary for hyperbolic local isometries

This file isolates the analytic calculation behind the local-isometry
classification boundary.

For a holomorphic map `f`, write `P = f'' / f'` for its scalar pre-Schwarzian.
The Schwarzian identity gives

`P' = S(f) + (1 / 2) P^2`.

Thus the hyperbolic metric calculation only has to prove the Riccati equation
`∂z P = (1 / 2) P^2`; after converting the ordinary derivative to the
Wirtinger `∂z` value, the Schwarzian vanishes.
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Frechet-Wirtinger `∂z` only depends on the germ of a function. -/
theorem frechetDZValue_congr_of_eventuallyEq
    {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[nhds z] g) :
    frechetDZValue f z = frechetDZValue g z := by
  rw [frechetDZValue, frechetDZValue]
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h]

/-- Frechet-Wirtinger `∂z` of `(a - b) / c` for a constant `c`. -/
theorem frechetDZValue_sub_div_const_of_differentiableAt
    {a b : ℂ → ℂ} {z c : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) :
    frechetDZValue (fun w : ℂ ↦ (a w - b w) / c) z =
      (frechetDZValue a z - frechetDZValue b z) / c := by
  have hsub : DifferentiableAt ℝ (fun w : ℂ ↦ a w - b w) z := ha.sub hb
  rw [show (fun w : ℂ ↦ (a w - b w) / c) =
      (fun w : ℂ ↦ c⁻¹ * (a w - b w)) by
        ext w
        rw [div_eq_inv_mul]]
  rw [frechetDZValue_const_mul_of_differentiableAt hsub]
  rw [frechetDZValue_sub_of_differentiableAt ha hb]
  ring

/--
If the scalar pre-Schwarzian satisfies the Riccati equation
`∂z P = (1 / 2) P^2` at a point, then the Schwarzian vanishes there.

This is the formal core of the proposed argument: the hyperbolic metric
identity should supply the Riccati equation by a Wirtinger calculation, while
the standard pre-Schwarzian derivative formula supplies
`∂z P = S(f) + (1 / 2) P^2`.
-/
theorem actualSchwarzian_eq_zero_of_scalarPreSchwarzian_riccati
    {f : ℂ → ℂ} {z : ℂ}
    (hf_ne : deriv f z ≠ 0)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z) z)
    (hRiccati :
      frechetDZValue (fun t : ℂ ↦ scalarPreSchwarzian f t) z =
        (1 / 2 : ℂ) * (scalarPreSchwarzian f z) ^ 2) :
    actualSchwarzian f z = 0 := by
  have hP := scalarPreSchwarzian_hasDerivAt hf_ne hf₁ hf₂
  have hDZ :
      frechetDZValue (fun t : ℂ ↦ scalarPreSchwarzian f t) z =
        actualSchwarzian f z +
          (1 / 2 : ℂ) * (scalarPreSchwarzian f z) ^ 2 :=
    frechetDZValue_of_hasDerivAt hP
  have hcancel :
      actualSchwarzian f z +
          (1 / 2 : ℂ) * (scalarPreSchwarzian f z) ^ 2 =
        0 + (1 / 2 : ℂ) * (scalarPreSchwarzian f z) ^ 2 := by
    simpa using hDZ.symm.trans hRiccati
  exact add_right_cancel hcancel

/--
The algebraic Riccati calculation behind the hyperbolic metric equation.

In the intended application

* `P = f'' / f'`,
* `a = f' / Im f`,
* `b = 1 / Im z`.

The first-order metric identity gives `P = (a - b) / I`.  Differentiating
`a` and `b` by `∂z` gives the two displayed derivative identities.  These
purely algebraic data force `∂z P = (1 / 2) P^2`.
-/
theorem frechetDZValue_riccati_of_hyperbolic_preSchwarzian_data
    {P a b : ℂ → ℂ} {z : ℂ}
    (hPz : P z = (a z - b z) / Complex.I)
    (hPdz :
      frechetDZValue P z =
        (frechetDZValue a z - frechetDZValue b z) / Complex.I)
    (ha :
      frechetDZValue a z =
        P z * a z - a z ^ 2 / ((2 : ℂ) * Complex.I))
    (hb :
      frechetDZValue b z =
        - b z ^ 2 / ((2 : ℂ) * Complex.I)) :
    frechetDZValue P z = (1 / 2 : ℂ) * P z ^ 2 := by
  rw [hPdz, ha, hb, hPz]
  field_simp [Complex.I_ne_zero]
  ring_nf

/--
The fixed Poincare height term satisfies the Riccati derivative identity
needed in the hyperbolic calculation:

`∂z (1 / Im z) = -(1 / Im z)^2 / (2 I)`.
-/
theorem frechetDZValue_inv_complex_ofReal_im
    {z : ℂ} (hz : (((z.im : ℝ) : ℂ)) ≠ 0) :
    frechetDZValue
        (fun w : ℂ ↦ (((w.im : ℝ) : ℂ))⁻¹) z =
      - ((((z.im : ℝ) : ℂ))⁻¹) ^ 2 / ((2 : ℂ) * Complex.I) := by
  let y : ℂ → ℂ := fun w : ℂ ↦ (((w.im : ℝ) : ℂ))
  have hy_diff : DifferentiableAt ℝ y z :=
    differentiableAt_complex_ofReal_im_of_hasDerivAt
      (F := fun w : ℂ ↦ w) (z₀ := z) (F' := 1) (hasDerivAt_id z)
  have hy_dz :
      frechetDZValue y z = -Complex.I * (1 : ℂ) / 2 :=
    frechetDZValue_complex_ofReal_im_of_hasDerivAt_general
      (F := fun w : ℂ ↦ w) (z₀ := z) (F' := 1) (hasDerivAt_id z)
  calc
    frechetDZValue
        (fun w : ℂ ↦ (((w.im : ℝ) : ℂ))⁻¹) z
        = frechetDZValue (fun w : ℂ ↦ (y w)⁻¹) z := rfl
    _ = - frechetDZValue y z / (y z) ^ 2 :=
        frechetDZValue_inv_of_differentiableAt hy_diff hz
    _ = - ((((z.im : ℝ) : ℂ))⁻¹) ^ 2 / ((2 : ℂ) * Complex.I) := by
        rw [hy_dz]
        dsimp [y]
        field_simp [hz, Complex.I_ne_zero]
        rw [pow_two, Complex.I_mul_I]

/--
The moving height term in the hyperbolic calculation.

For a holomorphic branch `f`, the function `a = f' / Im f` satisfies

`∂z a = (f'' / f') a - a^2 / (2 I)`.

Here `f'' / f'` is written as `scalarPreSchwarzian f`.
-/
theorem frechetDZValue_deriv_div_complex_ofReal_im
    {f : ℂ → ℂ} {z : ℂ}
    (hf :
      HasDerivAt f (deriv f z) z)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf_ne : deriv f z ≠ 0)
    (him_ne : ((((f z).im : ℝ) : ℂ)) ≠ 0) :
    frechetDZValue
        (fun w : ℂ ↦ deriv f w / ((((f w).im : ℝ) : ℂ))) z =
      scalarPreSchwarzian f z *
          (deriv f z / ((((f z).im : ℝ) : ℂ))) -
        (deriv f z / ((((f z).im : ℝ) : ℂ))) ^ 2 /
          ((2 : ℂ) * Complex.I) := by
  let F : ℂ → ℂ := fun w : ℂ ↦ deriv f w
  let Y : ℂ → ℂ := fun w : ℂ ↦ ((((f w).im : ℝ) : ℂ))
  have hF_diff : DifferentiableAt ℝ F z :=
    hf₁.complexToReal_fderiv.differentiableAt
  have hY_diff : DifferentiableAt ℝ Y z :=
    differentiableAt_complex_ofReal_im_of_hasDerivAt hf
  have hF_dz :
      frechetDZValue F z = deriv (fun t : ℂ ↦ deriv f t) z :=
    frechetDZValue_of_hasDerivAt hf₁
  have hY_dz :
      frechetDZValue Y z = -Complex.I * deriv f z / 2 :=
    frechetDZValue_complex_ofReal_im_of_hasDerivAt_general hf
  calc
    frechetDZValue
        (fun w : ℂ ↦ deriv f w / ((((f w).im : ℝ) : ℂ))) z
        = frechetDZValue (fun w : ℂ ↦ F w / Y w) z := rfl
    _ = (frechetDZValue F z * Y z - F z * frechetDZValue Y z) /
          (Y z) ^ 2 :=
        frechetDZValue_div_of_differentiableAt hF_diff hY_diff him_ne
    _ =
      scalarPreSchwarzian f z *
          (deriv f z / ((((f z).im : ℝ) : ℂ))) -
        (deriv f z / ((((f z).im : ℝ) : ℂ))) ^ 2 /
          ((2 : ℂ) * Complex.I) := by
        rw [hF_dz, hY_dz]
        dsimp [F, Y]
        rw [scalarPreSchwarzian]
        field_simp [hf_ne, him_ne, Complex.I_ne_zero]
        ring_nf
        rw [pow_two, Complex.I_mul_I]
        ring_nf

/--
Derivative of the Poincare squared-density expression
`|f'|^2 / (Im f)^2`.
-/
theorem frechetDZValue_hyperbolic_pullback_densitySq
    {f : ℂ → ℂ} {z : ℂ}
    (hf :
      HasDerivAt f (deriv f z) z)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf_ne : deriv f z ≠ 0)
    (him_ne : ((((f z).im : ℝ) : ℂ)) ≠ 0) :
    frechetDZValue
        (fun w : ℂ ↦
          ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ)) z =
      ((Complex.normSq (deriv f z) / (f z).im ^ 2 : ℝ) : ℂ) *
        (scalarPreSchwarzian f z +
          Complex.I * deriv f z / ((((f z).im : ℝ) : ℂ))) := by
  let F : ℂ → ℂ := f
  let F₁ : ℂ → ℂ := fun w : ℂ ↦ deriv f w
  let F₂ : ℂ → ℂ := fun w : ℂ ↦ deriv (fun t : ℂ ↦ deriv f t) w
  let A : ℂ → ℝ := fun w : ℂ ↦ Complex.normSq (F₁ w)
  let B : ℂ → ℝ := fun w : ℂ ↦ (F w).im ^ 2
  let ρ : ℂ → ℝ := fun w : ℂ ↦ A w / B w
  have hF₁_diff : DifferentiableAt ℝ F₁ z :=
    hf₁.complexToReal_fderiv.differentiableAt
  have hA : DifferentiableAt ℝ A z := by
    simpa [A, F₁, Complex.normSq_apply] using
      ((Complex.reCLM.differentiableAt.comp z hF₁_diff).mul
          (Complex.reCLM.differentiableAt.comp z hF₁_diff)).add
        ((Complex.imCLM.differentiableAt.comp z hF₁_diff).mul
          (Complex.imCLM.differentiableAt.comp z hF₁_diff))
  have hF_diff : DifferentiableAt ℝ F z :=
    hf.complexToReal_fderiv.differentiableAt
  have hB : DifferentiableAt ℝ B z := by
    simpa [B, F, Function.comp_apply, Complex.imCLM_apply, pow_two] using
      ((Complex.imCLM.differentiableAt.comp z hF_diff).mul
        (Complex.imCLM.differentiableAt.comp z hF_diff))
  have hB_ne : B z ≠ 0 := by
    have himR_ne : (f z).im ≠ 0 := by
      exact_mod_cast him_ne
    exact pow_ne_zero 2 himR_ne
  have hA_dz :
      frechetDZValue (fun w : ℂ ↦ (A w : ℂ)) z =
        star (F₁ z) * F₂ z := by
    simpa [A, F₁, F₂] using
      frechetDZValue_complex_ofReal_normSq_of_hasDerivAt hf₁
  have hB_dz :
      frechetDZValue (fun w : ℂ ↦ (B w : ℂ)) z =
        -Complex.I * ((F z).im : ℂ) * deriv f z := by
    simpa [B, F] using
      frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt_general hf
  calc
    frechetDZValue
        (fun w : ℂ ↦
          ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ)) z
        = frechetDZValue (fun w : ℂ ↦ (ρ w : ℂ)) z := rfl
    _ = ((frechetDZValue (fun w : ℂ ↦ (A w : ℂ)) z) * (B z : ℂ) -
          (A z : ℂ) * frechetDZValue (fun w : ℂ ↦ (B w : ℂ)) z) /
          (B z : ℂ) ^ 2 := by
        rw [show (fun w : ℂ ↦ (ρ w : ℂ)) =
            (fun w : ℂ ↦ ((A w / B w : ℝ) : ℂ)) by rfl]
        exact frechetDZValue_complex_ofReal_div_of_differentiableAt
          (A := A) (B := B) (z₀ := z) hA hB hB_ne
    _ = ((Complex.normSq (deriv f z) / (f z).im ^ 2 : ℝ) : ℂ) *
        (scalarPreSchwarzian f z +
          Complex.I * deriv f z / ((((f z).im : ℝ) : ℂ))) := by
        rw [hA_dz, hB_dz]
        dsimp [A, B, ρ, F, F₁, F₂]
        rw [scalarPreSchwarzian]
        simpa only [Complex.ofReal_pow, starRingEnd_apply] using
          LocalHyperbolicTwoJetUpperHalfPlaneNormalization.pullbackDensitySqDerivativeFormula_algebra
            (deriv f z)
            (deriv (fun t : ℂ ↦ deriv f t) z)
            hf_ne
            (by simpa using him_ne)

/--
Derivative of the model squared Poincare density `1 / (Im z)^2`.
-/
theorem frechetDZValue_inv_complex_ofReal_im_sq
    {z : ℂ} (hz : (((z.im : ℝ) : ℂ)) ≠ 0) :
    frechetDZValue
        (fun w : ℂ ↦ ((((w.im ^ 2 : ℝ) : ℂ))⁻¹)) z =
      Complex.I / ((((z.im : ℝ) : ℂ)) ^ 3) := by
  let Y₂ : ℂ → ℂ := fun w : ℂ ↦ (((w.im ^ 2 : ℝ) : ℂ))
  have hY₂_diff : DifferentiableAt ℝ Y₂ z := by
    have hImC :
        DifferentiableAt ℝ (fun w : ℂ ↦ (((w.im : ℝ) : ℂ))) z :=
      differentiableAt_complex_ofReal_im_of_hasDerivAt
        (F := fun w : ℂ ↦ w) (z₀ := z) (F' := 1) (hasDerivAt_id z)
    have hSqC :
        DifferentiableAt ℝ (fun w : ℂ ↦ (((w.im : ℝ) : ℂ)) ^ 2) z := by
      simpa [pow_two] using hImC.mul hImC
    simpa [Y₂, Complex.ofReal_pow] using hSqC
  have hY₂_dz :
      frechetDZValue Y₂ z =
        -Complex.I * (((z.im : ℝ) : ℂ)) * (1 : ℂ) := by
    simpa [Y₂] using
      frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt_general
        (F := fun w : ℂ ↦ w) (z₀ := z) (F' := 1) (hasDerivAt_id z)
  have hY₂_ne : Y₂ z ≠ 0 := by
    dsimp [Y₂]
    have hzR : z.im ≠ 0 := by
      exact_mod_cast hz
    exact_mod_cast (pow_ne_zero 2 hzR)
  calc
    frechetDZValue
        (fun w : ℂ ↦ ((((w.im ^ 2 : ℝ) : ℂ))⁻¹)) z
        = frechetDZValue (fun w : ℂ ↦ (Y₂ w)⁻¹) z := rfl
    _ = - frechetDZValue Y₂ z / (Y₂ z) ^ 2 :=
        frechetDZValue_inv_of_differentiableAt hY₂_diff hY₂_ne
    _ = Complex.I / ((((z.im : ℝ) : ℂ)) ^ 3) := by
        rw [hY₂_dz]
        dsimp [Y₂]
        rw [Complex.ofReal_pow]
        field_simp [hz]

/--
Pointwise extraction of the pre-Schwarzian relation from the differentiated
squared hyperbolic metric identity.
-/
theorem scalarPreSchwarzian_eq_of_hyperbolic_densitySq_derivative
    {f : ℂ → ℂ} {z : ℂ}
    (hf :
      HasDerivAt f (deriv f z) z)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf_ne : deriv f z ≠ 0)
    (him_ne : ((((f z).im : ℝ) : ℂ)) ≠ 0)
    (hz_im_ne : (((z.im : ℝ) : ℂ)) ≠ 0)
    (hMetricValue :
      ((Complex.normSq (deriv f z) / (f z).im ^ 2 : ℝ) : ℂ) =
        ((((z.im ^ 2 : ℝ) : ℂ))⁻¹))
    (hMetricDerivative :
      frechetDZValue
          (fun w : ℂ ↦
            ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ)) z =
        frechetDZValue
          (fun w : ℂ ↦ ((((w.im ^ 2 : ℝ) : ℂ))⁻¹)) z) :
    scalarPreSchwarzian f z =
      (deriv f z / ((((f z).im : ℝ) : ℂ)) -
          ((((z.im : ℝ) : ℂ))⁻¹)) / Complex.I := by
  have hLeft :=
    frechetDZValue_hyperbolic_pullback_densitySq hf hf₁ hf_ne him_ne
  have hRight := frechetDZValue_inv_complex_ofReal_im_sq hz_im_ne
  have hEq :
      ((((z.im ^ 2 : ℝ) : ℂ))⁻¹) *
          (scalarPreSchwarzian f z +
            Complex.I * deriv f z / ((((f z).im : ℝ) : ℂ))) =
        Complex.I / ((((z.im : ℝ) : ℂ)) ^ 3) := by
    calc
      ((((z.im ^ 2 : ℝ) : ℂ))⁻¹) *
          (scalarPreSchwarzian f z +
            Complex.I * deriv f z / ((((f z).im : ℝ) : ℂ)))
          =
        frechetDZValue
          (fun w : ℂ ↦
            ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ)) z := by
          rw [hLeft, hMetricValue]
      _ =
        frechetDZValue
          (fun w : ℂ ↦ ((((w.im ^ 2 : ℝ) : ℂ))⁻¹)) z :=
          hMetricDerivative
      _ = Complex.I / ((((z.im : ℝ) : ℂ)) ^ 3) := hRight
  have hRel :
      scalarPreSchwarzian f z +
          Complex.I * deriv f z / ((((f z).im : ℝ) : ℂ)) =
        Complex.I / ((((z.im : ℝ) : ℂ))) := by
    have hsq :
        ((((z.im ^ 2 : ℝ) : ℂ))⁻¹) =
          ((((z.im : ℝ) : ℂ)) ^ 2)⁻¹ := by
      rw [Complex.ofReal_pow]
    rw [hsq] at hEq
    field_simp [hz_im_ne] at hEq ⊢
    simpa using hEq
  rw [eq_div_iff Complex.I_ne_zero]
  field_simp [him_ne, hz_im_ne, Complex.I_ne_zero] at hRel ⊢
  have hRel' :
      scalarPreSchwarzian f z * ((((f z).im : ℝ) : ℂ)) *
          (((z.im : ℝ) : ℂ)) =
        Complex.I * ((((f z).im : ℝ) : ℂ)) -
          Complex.I * deriv f z * (((z.im : ℝ) : ℂ)) := by
    calc
      scalarPreSchwarzian f z * ((((f z).im : ℝ) : ℂ)) *
          (((z.im : ℝ) : ℂ))
          =
        (scalarPreSchwarzian f z * ((((f z).im : ℝ) : ℂ)) +
            Complex.I * deriv f z) * (((z.im : ℝ) : ℂ)) -
          Complex.I * deriv f z * (((z.im : ℝ) : ℂ)) := by ring
      _ = Complex.I * ((((f z).im : ℝ) : ℂ)) -
          Complex.I * deriv f z * (((z.im : ℝ) : ℂ)) := by rw [hRel]
  calc
    scalarPreSchwarzian f z * Complex.I *
          ((((f z).im : ℝ) : ℂ)) * (((z.im : ℝ) : ℂ))
        = Complex.I *
          (scalarPreSchwarzian f z * ((((f z).im : ℝ) : ℂ)) *
            (((z.im : ℝ) : ℂ))) := by ring
    _ = Complex.I *
        (Complex.I * ((((f z).im : ℝ) : ℂ)) -
          Complex.I * deriv f z * (((z.im : ℝ) : ℂ))) := by rw [hRel']
    _ = deriv f z * (((z.im : ℝ) : ℂ)) -
        ((((f z).im : ℝ) : ℂ)) := by
          ring_nf
          simp [pow_two, Complex.I_mul_I]

/--
Open-neighborhood version of the metric-to-pre-Schwarzian calculation.

The squared hyperbolic metric identity is assumed on an open set, so at every
nearby point it is available as a germ and may be differentiated there.
-/
theorem eventually_hyperbolic_preSchwarzian_of_hyperbolic_densitySq_on
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hUopen : IsOpen U) (hzU : z ∈ U)
    (hf :
      ∀ w, w ∈ U →
        HasDerivAt f (deriv f w) w)
    (hf₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w)
    (hf_ne : ∀ w, w ∈ U → deriv f w ≠ 0)
    (him_ne : ∀ w, w ∈ U → ((((f w).im : ℝ) : ℂ)) ≠ 0)
    (hz_im_ne : ∀ w, w ∈ U → (((w.im : ℝ) : ℂ)) ≠ 0)
    (hMetric :
      ∀ w, w ∈ U →
        ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ) =
          ((((w.im ^ 2 : ℝ) : ℂ))⁻¹)) :
    (fun w : ℂ ↦ scalarPreSchwarzian f w) =ᶠ[nhds z]
      (fun w : ℂ ↦
        (deriv f w / ((((f w).im : ℝ) : ℂ)) -
            ((((w.im : ℝ) : ℂ))⁻¹)) / Complex.I) := by
  filter_upwards [hUopen.mem_nhds hzU] with w hw
  have hMetricGerm :
      (fun t : ℂ ↦
          ((Complex.normSq (deriv f t) / (f t).im ^ 2 : ℝ) : ℂ)) =ᶠ[nhds w]
        (fun t : ℂ ↦ ((((t.im ^ 2 : ℝ) : ℂ))⁻¹)) := by
    filter_upwards [hUopen.mem_nhds hw] with t ht
    exact hMetric t ht
  exact scalarPreSchwarzian_eq_of_hyperbolic_densitySq_derivative
    (hf w hw) (hf₁ w hw) (hf_ne w hw) (him_ne w hw) (hz_im_ne w hw)
    (hMetric w hw)
    (frechetDZValue_congr_of_eventuallyEq hMetricGerm)

/--
Once the differentiated hyperbolic metric identity has supplied the local
pre-Schwarzian relation

`P = (f' / Im f - 1 / Im z) / I`,

the scalar pre-Schwarzian satisfies the Riccati equation
`∂z P = (1 / 2) P^2`.
-/
theorem frechetDZValue_scalarPreSchwarzian_riccati_of_eventually_hyperbolic_preSchwarzian
    {f : ℂ → ℂ} {z : ℂ}
    (hf :
      HasDerivAt f (deriv f z) z)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf_ne : deriv f z ≠ 0)
    (him_ne : ((((f z).im : ℝ) : ℂ)) ≠ 0)
    (hz_im_ne : (((z.im : ℝ) : ℂ)) ≠ 0)
    (hPre :
      (fun w : ℂ ↦ scalarPreSchwarzian f w) =ᶠ[nhds z]
        (fun w : ℂ ↦
          (deriv f w / ((((f w).im : ℝ) : ℂ)) -
              ((((w.im : ℝ) : ℂ))⁻¹)) / Complex.I)) :
    frechetDZValue (fun w : ℂ ↦ scalarPreSchwarzian f w) z =
      (1 / 2 : ℂ) * (scalarPreSchwarzian f z) ^ 2 := by
  let P : ℂ → ℂ := fun w : ℂ ↦ scalarPreSchwarzian f w
  let a : ℂ → ℂ := fun w : ℂ ↦ deriv f w / ((((f w).im : ℝ) : ℂ))
  let b : ℂ → ℂ := fun w : ℂ ↦ ((((w.im : ℝ) : ℂ))⁻¹)
  have hPz : P z = (a z - b z) / Complex.I := by
    simpa [P, a, b] using hPre.eq_of_nhds
  have hF_diff : DifferentiableAt ℝ (fun w : ℂ ↦ deriv f w) z :=
    hf₁.complexToReal_fderiv.differentiableAt
  have hY_diff :
      DifferentiableAt ℝ (fun w : ℂ ↦ ((((f w).im : ℝ) : ℂ))) z :=
    differentiableAt_complex_ofReal_im_of_hasDerivAt hf
  have ha_diff : DifferentiableAt ℝ a z := by
    have hY_inv :
        DifferentiableAt ℝ
          (fun w : ℂ ↦ ((((f w).im : ℝ) : ℂ))⁻¹) z :=
      hY_diff.inv him_ne
    simpa [a, div_eq_mul_inv] using hF_diff.mul hY_inv
  have hy_diff :
      DifferentiableAt ℝ (fun w : ℂ ↦ (((w.im : ℝ) : ℂ))) z :=
    differentiableAt_complex_ofReal_im_of_hasDerivAt
      (F := fun w : ℂ ↦ w) (z₀ := z) (F' := 1) (hasDerivAt_id z)
  have hb_diff : DifferentiableAt ℝ b z := by
    simpa [b] using hy_diff.inv hz_im_ne
  have hPdz_congr :
      frechetDZValue P z =
        frechetDZValue (fun w : ℂ ↦ (a w - b w) / Complex.I) z := by
    exact frechetDZValue_congr_of_eventuallyEq (by simpa [P, a, b] using hPre)
  have hPdz :
      frechetDZValue P z =
        (frechetDZValue a z - frechetDZValue b z) / Complex.I := by
    calc
      frechetDZValue P z =
          frechetDZValue (fun w : ℂ ↦ (a w - b w) / Complex.I) z :=
        hPdz_congr
      _ = (frechetDZValue a z - frechetDZValue b z) / Complex.I :=
        frechetDZValue_sub_div_const_of_differentiableAt ha_diff hb_diff
  have ha :
      frechetDZValue a z =
        P z * a z - a z ^ 2 / ((2 : ℂ) * Complex.I) := by
    simpa [P, a] using
      frechetDZValue_deriv_div_complex_ofReal_im hf hf₁ hf_ne him_ne
  have hb :
      frechetDZValue b z =
        - b z ^ 2 / ((2 : ℂ) * Complex.I) := by
    simpa [b] using frechetDZValue_inv_complex_ofReal_im hz_im_ne
  simpa [P] using
    frechetDZValue_riccati_of_hyperbolic_preSchwarzian_data
      (P := P) (a := a) (b := b) hPz hPdz ha hb

/--
The Schwarzian-zero conclusion from the differentiated hyperbolic metric
identity.
-/
theorem actualSchwarzian_eq_zero_of_eventually_hyperbolic_preSchwarzian
    {f : ℂ → ℂ} {z : ℂ}
    (hf :
      HasDerivAt f (deriv f z) z)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z) z)
    (hf_ne : deriv f z ≠ 0)
    (him_ne : ((((f z).im : ℝ) : ℂ)) ≠ 0)
    (hz_im_ne : (((z.im : ℝ) : ℂ)) ≠ 0)
    (hPre :
      (fun w : ℂ ↦ scalarPreSchwarzian f w) =ᶠ[nhds z]
        (fun w : ℂ ↦
          (deriv f w / ((((f w).im : ℝ) : ℂ)) -
              ((((w.im : ℝ) : ℂ))⁻¹)) / Complex.I)) :
    actualSchwarzian f z = 0 :=
  actualSchwarzian_eq_zero_of_scalarPreSchwarzian_riccati
    hf_ne hf₁ hf₂
    (frechetDZValue_scalarPreSchwarzian_riccati_of_eventually_hyperbolic_preSchwarzian
      hf hf₁ hf_ne him_ne hz_im_ne hPre)

/--
Zero-Schwarzian consequence of the squared hyperbolic metric identity on an
open neighborhood.
-/
theorem actualSchwarzian_eq_zero_of_hyperbolic_densitySq_on
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hUopen : IsOpen U) (hzU : z ∈ U)
    (hf :
      ∀ w, w ∈ U →
        HasDerivAt f (deriv f w) w)
    (hf₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w)
    (hf₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z) z)
    (hf_ne : ∀ w, w ∈ U → deriv f w ≠ 0)
    (him_ne : ∀ w, w ∈ U → ((((f w).im : ℝ) : ℂ)) ≠ 0)
    (hz_im_ne : ∀ w, w ∈ U → (((w.im : ℝ) : ℂ)) ≠ 0)
    (hMetric :
      ∀ w, w ∈ U →
        ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ) =
          ((((w.im ^ 2 : ℝ) : ℂ))⁻¹)) :
    actualSchwarzian f z = 0 :=
  actualSchwarzian_eq_zero_of_eventually_hyperbolic_preSchwarzian
    (hf z hzU) (hf₁ z hzU) hf₂ (hf_ne z hzU) (him_ne z hzU)
    (hz_im_ne z hzU)
    (eventually_hyperbolic_preSchwarzian_of_hyperbolic_densitySq_on
      hUopen hzU hf hf₁ hf_ne him_ne hz_im_ne hMetric)

/--
Setwise zero-Schwarzian consequence of the squared hyperbolic metric identity.
-/
theorem actualSchwarzian_eq_zero_on_of_hyperbolic_densitySq_on
    {f : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hf :
      ∀ w, w ∈ U →
        HasDerivAt f (deriv f w) w)
    (hf₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w)
    (hf₂ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
          (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w)
    (hf_ne : ∀ w, w ∈ U → deriv f w ≠ 0)
    (him_ne : ∀ w, w ∈ U → ((((f w).im : ℝ) : ℂ)) ≠ 0)
    (hz_im_ne : ∀ w, w ∈ U → (((w.im : ℝ) : ℂ)) ≠ 0)
    (hMetric :
      ∀ w, w ∈ U →
        ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ) =
          ((((w.im ^ 2 : ℝ) : ℂ))⁻¹)) :
    ∀ z, z ∈ U → actualSchwarzian f z = 0 := by
  intro z hzU
  exact actualSchwarzian_eq_zero_of_hyperbolic_densitySq_on
    hUopen hzU hf hf₁ (hf₂ z hzU) hf_ne him_ne hz_im_ne hMetric

/--
One-jet rigidity for local Poincare isometries in the standard upper-half-plane
coordinate.

This is the useful “zero Schwarzian implies Mobius” form for the continuation
argument.  A holomorphic map `f : U → ℍ` pulling back the Poincare squared
density to the standard Poincare squared density has zero Schwarzian.  If its
value and first derivative agree at `z` with a fixed real Mobius
representative, then the differentiated metric identity also identifies the
second derivative at `z`; scalar Schwarzian uniqueness then gives local
equality.
-/
theorem poincareLocalIsometry_eq_realMobius_near_of_oneJet
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (A : RealMobiusRepresentative)
    (hUopen : IsOpen U) (hzU : z ∈ U)
    (hf :
      ∀ w, w ∈ U →
        HasDerivAt f (deriv f w) w)
    (hf₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w)
    (hf₂ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
          (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w)
    (hf_ne : ∀ w, w ∈ U → deriv f w ≠ 0)
    (him_pos : ∀ w, w ∈ U → 0 < (f w).im)
    (hz_im_pos : ∀ w, w ∈ U → 0 < w.im)
    (hMetric :
      ∀ w, w ∈ U →
        ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ) =
          ((((w.im ^ 2 : ℝ) : ℂ))⁻¹))
    (hvalue :
      f z =
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
    (hderiv :
      deriv f z =
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
          z) :
    ∃ V : Set ℂ,
      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
        ∀ w, w ∈ V →
          f w =
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ) := by
  let M : ℂ → ℂ :=
    fun w : ℂ ↦
      (realMobiusRepresentativeAction A
        ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  have him_ne : ∀ w, w ∈ U → ((((f w).im : ℝ) : ℂ)) ≠ 0 := by
    intro w hw
    exact_mod_cast (ne_of_gt (him_pos w hw))
  have hz_im_ne : ∀ w, w ∈ U → (((w.im : ℝ) : ℂ)) ≠ 0 := by
    intro w hw
    exact_mod_cast (ne_of_gt (hz_im_pos w hw))
  have hM :
      ∀ w, w ∈ U → HasDerivAt M (deriv M w) w := by
    intro w hw
    let p : ℍ := ⟨w, hz_im_pos w hw⟩
    have h :=
      realMobiusRepresentativeAction_hasDerivAt A p
    exact h.congr_deriv (by
      simpa [M, p, UpperHalfPlane.ofComplex_apply_of_im_pos (hz_im_pos w hw)]
        using h.deriv.symm)
  have hM₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv M t)
          (deriv (fun t : ℂ ↦ deriv M t) w) w := by
    intro w hw
    let p : ℍ := ⟨w, hz_im_pos w hw⟩
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A p
    exact h.congr_deriv (by
      simpa [M, p, UpperHalfPlane.ofComplex_apply_of_im_pos (hz_im_pos w hw)]
        using h.deriv.symm)
  have hM₂ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv M s) t)
          (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv M s) t) w) w := by
    intro w hw
    let p : ℍ := ⟨w, hz_im_pos w hw⟩
    have h :=
      realMobiusRepresentativeAction_second_deriv_hasDerivAt A p
    exact h.congr_deriv (by
      simpa [M, p, UpperHalfPlane.ofComplex_apply_of_im_pos (hz_im_pos w hw)]
        using h.deriv.symm)
  have hM_ne : ∀ w, w ∈ U → deriv M w ≠ 0 := by
    intro w hw
    let p : ℍ := ⟨w, hz_im_pos w hw⟩
    have h :=
      realMobiusRepresentativeAction_deriv_ne_zero A p
    simpa [M, p, UpperHalfPlane.ofComplex_apply_of_im_pos (hz_im_pos w hw)]
      using h
  have hM_im_ne : ∀ w, w ∈ U → ((((M w).im : ℝ) : ℂ)) ≠ 0 := by
    intro w hw
    let p : ℍ := ⟨w, hz_im_pos w hw⟩
    have hpos :
        0 <
          (realMobiusRepresentativeAction A p : ℂ).im :=
      (realMobiusRepresentativeAction A p).im_pos
    exact_mod_cast (ne_of_gt (by
      simpa [M, p, UpperHalfPlane.ofComplex_apply_of_im_pos (hz_im_pos w hw)]
        using hpos))
  have hMMetric :
      ∀ w, w ∈ U →
        ((Complex.normSq (deriv M w) / (M w).im ^ 2 : ℝ) : ℂ) =
          ((((w.im ^ 2 : ℝ) : ℂ))⁻¹) := by
    intro w hw
    let p : ℍ := ⟨w, hz_im_pos w hw⟩
    have hIso := realMobiusRepresentativeAction_deriv_hyperbolicNormSq A p
    have hw_im_ne : w.im ≠ 0 := ne_of_gt (hz_im_pos w hw)
    have hDeriv :
        deriv M w =
          deriv
            (fun z : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
            p := by
      simp [M, p]
    have hIso' :
        Complex.normSq (deriv M w) /
            ((M w).im ^ 2) =
          1 / (w.im ^ 2) := by
      simpa [M, p, hDeriv,
        UpperHalfPlane.ofComplex_apply_of_im_pos (hz_im_pos w hw)]
        using hIso
    norm_num [hIso', Complex.ofReal_inv, Complex.ofReal_pow, hw_im_ne]
  have hPre_f :
      (fun w : ℂ ↦ scalarPreSchwarzian f w) =ᶠ[nhds z]
        (fun w : ℂ ↦
          (deriv f w / ((((f w).im : ℝ) : ℂ)) -
              ((((w.im : ℝ) : ℂ))⁻¹)) / Complex.I) :=
    eventually_hyperbolic_preSchwarzian_of_hyperbolic_densitySq_on
      hUopen hzU hf hf₁ hf_ne him_ne hz_im_ne hMetric
  have hPre_M :
      (fun w : ℂ ↦ scalarPreSchwarzian M w) =ᶠ[nhds z]
        (fun w : ℂ ↦
          (deriv M w / ((((M w).im : ℝ) : ℂ)) -
              ((((w.im : ℝ) : ℂ))⁻¹)) / Complex.I) :=
    eventually_hyperbolic_preSchwarzian_of_hyperbolic_densitySq_on
      hUopen hzU hM hM₁ hM_ne hM_im_ne hz_im_ne hMMetric
  have hPre_eq :
      scalarPreSchwarzian f z = scalarPreSchwarzian M z := by
    have hfz := hPre_f.eq_of_nhds
    have hMz := hPre_M.eq_of_nhds
    calc
      scalarPreSchwarzian f z =
          (deriv f z / ((((f z).im : ℝ) : ℂ)) -
              ((((z.im : ℝ) : ℂ))⁻¹)) / Complex.I := hfz
      _ =
          (deriv M z / ((((M z).im : ℝ) : ℂ)) -
              ((((z.im : ℝ) : ℂ))⁻¹)) / Complex.I := by
            rw [hderiv, hvalue]
      _ = scalarPreSchwarzian M z := hMz.symm
  have hsecond :
      deriv (fun w : ℂ ↦ deriv f w) z =
        deriv (fun w : ℂ ↦ deriv M w) z := by
    have hden : deriv M z ≠ 0 := hM_ne z hzU
    have hpre := hPre_eq
    unfold scalarPreSchwarzian at hpre
    rw [hderiv] at hpre
    have hmul :=
      (div_eq_div_iff hden hden).mp hpre
    exact mul_right_cancel₀ hden hmul
  have hSchwarzian :
      ∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian M w := by
    intro w hw
    have hf_zero :
        actualSchwarzian f w = 0 :=
      actualSchwarzian_eq_zero_of_hyperbolic_densitySq_on
        hUopen hw hf hf₁ (hf₂ w hw) hf_ne him_ne hz_im_ne hMetric
    have hM_zero :
        actualSchwarzian M w = 0 := by
      let p : ℍ := ⟨w, hz_im_pos w hw⟩
      simpa [M, p, UpperHalfPlane.ofComplex_apply_of_im_pos (hz_im_pos w hw)]
        using realMobiusActualSchwarzianZeroTheorem A p
    rw [hf_zero, hM_zero]
  have hScalar :
      ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem :=
    scalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem_of_preSchwarzian
      scalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem_proved
      scalarPreSchwarzianValueDerivativeLocalUniquenessTheorem_of_derivativeQuotient
  exact hScalar f M U z hUopen hzU hf_ne hM_ne hf₁ hf₂ hM₁ hM₂
    hSchwarzian hvalue hderiv hsecond

/--
Open-set holomorphic version of
`poincareLocalIsometry_eq_realMobius_near_of_oneJet`.

For complex functions, holomorphicity on an open set gives the iterated
derivative hypotheses needed by the Schwarzian calculation, so the coordinate
classification can be used from the usual `DifferentiableOn` API.
-/
theorem poincareLocalIsometry_eq_realMobius_near_of_oneJet_differentiableOn
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (A : RealMobiusRepresentative)
    (hUopen : IsOpen U) (hzU : z ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (hf_ne : ∀ w, w ∈ U → deriv f w ≠ 0)
    (him_pos : ∀ w, w ∈ U → 0 < (f w).im)
    (hz_im_pos : ∀ w, w ∈ U → 0 < w.im)
    (hMetric : ∀ w, w ∈ U →
        ((Complex.normSq (deriv f w) / (f w).im ^ 2 : ℝ) : ℂ) =
          ((((w.im ^ 2 : ℝ) : ℂ))⁻¹))
    (hvalue : f z =
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
    (hderiv : deriv f z =
        deriv (fun w : ℂ =>
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)) z) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∀ w, w ∈ V →
        f w =
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ) := by
  have hf₀ :
      ∀ w, w ∈ U → HasDerivAt f (deriv f w) w := by
    intro w hw
    exact ((hf w hw).differentiableAt (hUopen.mem_nhds hw)).hasDerivAt
  have hf_deriv_on : DifferentiableOn ℂ (deriv f) U :=
    hf.deriv hUopen
  have hf₁ :
      ∀ w, w ∈ U →
        HasDerivAt (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w := by
    intro w hw
    exact
      ((hf_deriv_on w hw).differentiableAt
        (hUopen.mem_nhds hw)).hasDerivAt
  have hf_deriv_deriv_on :
      DifferentiableOn ℂ (deriv (fun t : ℂ ↦ deriv f t)) U :=
    hf_deriv_on.deriv hUopen
  have hf₂ :
      ∀ w, w ∈ U →
        HasDerivAt (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
          (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w := by
    intro w hw
    exact
      ((hf_deriv_deriv_on w hw).differentiableAt
        (hUopen.mem_nhds hw)).hasDerivAt
  exact
    poincareLocalIsometry_eq_realMobius_near_of_oneJet
      A hUopen hzU hf₀ hf₁ hf₂ hf_ne him_pos hz_im_pos
      hMetric hvalue hderiv

end HyperbolicMetric

end

end JJMath
