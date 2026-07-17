import JJMath.Hyperbolic.LocalFormula
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Schwarzians from constant-curvature conformal factors

This file isolates the next local analytic step after the Liouville equation.

For a conformal metric `exp (2u) |dz|^2` of constant curvature `K`, the local
curvature formula says

`Δ u = -K * exp (2u)`.

In a complex coordinate, the classical Schwarzian/projective-connection
coefficient attached to the metric is

`Q = 2 * (u_zz - u_z ^ 2)`.

The Liouville equation implies `∂_{\bar z} (u_zz - u_z ^ 2) = 0`, so the
actual Schwarzian coefficient `Q` is holomorphic.  The file proves the
curvature-to-constant-curvature-equation algebra, records the local Wirtinger
calculation producing this cancellation, and names the holomorphic-Schwarzian
data needed by the developing-map construction.
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace LocalConformalFactor

/-- The local conformal curvature formula has constant value `K`. -/
def HasGaussianCurvature (u : LocalConformalFactor) (K : ℝ) : Prop :=
  ∀ z, z ∈ u.coordinateDomain → u.gaussianCurvature z = K

/--
The constant-curvature Liouville equation for `exp (2u) |dz|^2`:

`Δ u = -K * exp (2u)`.

For `K = -1` this is the hyperbolic Liouville equation already used elsewhere.
-/
def SolvesConstantCurvatureEquation (u : LocalConformalFactor) (K : ℝ) : Prop :=
  ∀ z, z ∈ u.coordinateDomain →
    Laplacian.laplacian u.logDensity z = -K * Real.exp (2 * u.logDensity z)

/-- The old curvature `-1` predicate is the `K = -1` case of constant curvature. -/
theorem hasGaussianCurvatureMinusOne_iff_hasGaussianCurvature_neg_one
    (u : LocalConformalFactor) :
    u.HasGaussianCurvatureMinusOne ↔ u.HasGaussianCurvature (-1) :=
  Iff.rfl

/-- The old hyperbolic Liouville equation is the `K = -1` case. -/
theorem solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one
    (u : LocalConformalFactor) :
    u.SolvesLiouvilleEquation ↔ u.SolvesConstantCurvatureEquation (-1) := by
  constructor
  · intro h z hz
    simpa [SolvesConstantCurvatureEquation] using h z hz
  · intro h z hz
    simpa [SolvesConstantCurvatureEquation] using h z hz

/--
The local curvature formula `K = -exp (-2u) Δu` implies the
constant-curvature Liouville equation.
-/
theorem solvesConstantCurvatureEquation_of_hasGaussianCurvature
    (u : LocalConformalFactor) (K : ℝ) (hK : u.HasGaussianCurvature K) :
    u.SolvesConstantCurvatureEquation K := by
  intro z hz
  have hKz :
      - Real.exp (-(2 * u.logDensity z)) *
          Laplacian.laplacian u.logDensity z = K := by
    simpa [HasGaussianCurvature, gaussianCurvature] using hK z hz
  have hne : Real.exp (-(2 * u.logDensity z)) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  have hmul :
      Real.exp (-(2 * u.logDensity z)) *
          Laplacian.laplacian u.logDensity z = -K := by
    linarith
  calc
    Laplacian.laplacian u.logDensity z
        = (Real.exp (-(2 * u.logDensity z)))⁻¹ *
            (Real.exp (-(2 * u.logDensity z)) *
              Laplacian.laplacian u.logDensity z) := by
            field_simp [hne]
    _ = (Real.exp (-(2 * u.logDensity z)))⁻¹ * (-K) := by
            rw [hmul]
    _ = -K * Real.exp (2 * u.logDensity z) := by
            rw [← Real.exp_neg]
            ring_nf

/--
Conversely, the constant-curvature Liouville equation implies the local
curvature formula with constant value `K`.
-/
theorem hasGaussianCurvature_of_solvesConstantCurvatureEquation
    (u : LocalConformalFactor) (K : ℝ)
    (hL : u.SolvesConstantCurvatureEquation K) :
    u.HasGaussianCurvature K := by
  intro z hz
  have hpos : 0 < Real.exp (2 * u.logDensity z) := Real.exp_pos _
  calc
    u.gaussianCurvature z
        = - Real.exp (-(2 * u.logDensity z)) *
            (-K * Real.exp (2 * u.logDensity z)) := by
            rw [gaussianCurvature, hL z hz]
    _ = K := by
            rw [Real.exp_neg]
            field_simp [ne_of_gt hpos]

/--
%%handwave
name:
  Curvature and the Liouville equation
statement:
  Let $u : U \to \mathbb R$ be the logarithmic conformal factor of the metric
  $e^{2u}|dz|^2$ on a complex coordinate domain $U$. Its Gaussian curvature
  is identically $K$ if and only if
  $\Delta u = -K e^{2u}$ throughout $U$. In particular, curvature $-1$ is
  equivalent to the hyperbolic Liouville equation $\Delta u=e^{2u}$.
proof:
  Substitute the curvature formula $K_u=-e^{-2u}\Delta u$ and multiply by
  the everywhere positive function $e^{2u}$; the converse follows by the same
  algebra in reverse.
-/
theorem hasGaussianCurvature_iff_solvesConstantCurvatureEquation
    (u : LocalConformalFactor) (K : ℝ) :
    u.HasGaussianCurvature K ↔ u.SolvesConstantCurvatureEquation K :=
  ⟨u.solvesConstantCurvatureEquation_of_hasGaussianCurvature K,
    u.hasGaussianCurvature_of_solvesConstantCurvatureEquation K⟩

end LocalConformalFactor

/--
The pointwise Cauchy-Riemann, or `∂_{\bar z} = 0`, condition for a
complex-valued function, expressed through the real Frechet derivative.

Mathlib's complex-differentiability criterion uses exactly this condition:
the real derivative must commute with multiplication by `I`.
-/
def HasDBarZeroAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  DifferentiableAt ℝ f z ∧
    fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z (1 : ℂ)

/-- The `∂_{\bar z} = 0` condition at every point of a set. -/
def HasDBarZeroOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ z, z ∈ U → HasDBarZeroAt f z

/--
The Frechet-derivative value of the Wirtinger operator `∂_{\bar z}`.

For a real-differentiable complex-valued function this is
`(1 / 2) * (df(1) + I * df(I))`.  Vanishing of this value is exactly the
Cauchy-Riemann condition used by mathlib's complex differentiability criterion.
-/
def frechetDBarValue (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (fderiv ℝ f z (1 : ℂ) + Complex.I * fderiv ℝ f z Complex.I)

/--
The Frechet-derivative value of the Wirtinger operator `∂_z`.

For a real-differentiable complex-valued function this is
`(1 / 2) * (df(1) - I * df(I))`.  Together with `frechetDBarValue` it gives the
canonical Frechet-level Wirtinger decomposition of the real derivative.
-/
def frechetDZValue (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (fderiv ℝ f z (1 : ℂ) - Complex.I * fderiv ℝ f z Complex.I)

/--
The Frechet-Wirtinger decomposition reconstructs the full real Frechet
derivative.

For a real-differentiable complex-valued function,
`df(ξ) = Re(ξ) * (∂z f + ∂bar f) + Im(ξ) * I * (∂z f - ∂bar f)`.
-/
theorem fderiv_apply_eq_re_smul_frechetDZValue_add_dbar
    {f : ℂ → ℂ} {z ξ : ℂ} :
    fderiv ℝ f z ξ =
      (ξ.re : ℂ) * (frechetDZValue f z + frechetDBarValue f z) +
        (ξ.im : ℂ) * Complex.I * (frechetDZValue f z - frechetDBarValue f z) := by
  let L : ℂ →L[ℝ] ℂ := fderiv ℝ f z
  have hξ : ξ = (ξ.re : ℝ) • (1 : ℂ) + (ξ.im : ℝ) • Complex.I := by
    simp [Complex.re_add_im]
  calc
    fderiv ℝ f z ξ = L ξ := rfl
    _ = L ((ξ.re : ℝ) • (1 : ℂ) + (ξ.im : ℝ) • Complex.I) := by
      exact congrArg L hξ
    _ = (ξ.re : ℝ) • L (1 : ℂ) + (ξ.im : ℝ) • L Complex.I := by
      rw [map_add, map_smul, map_smul]
    _ = (ξ.re : ℂ) * (frechetDZValue f z + frechetDBarValue f z) +
        (ξ.im : ℂ) * Complex.I * (frechetDZValue f z - frechetDBarValue f z) := by
      simp [frechetDZValue, frechetDBarValue, L]
      ring_nf
      rw [Complex.I_sq]
      ring

/-- Frechet-Wirtinger `∂z` of a sum. -/
theorem frechetDZValue_add_of_differentiableAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    frechetDZValue (fun w : ℂ ↦ f w + g w) z =
      frechetDZValue f z + frechetDZValue g z := by
  rw [frechetDZValue, frechetDZValue, frechetDZValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ f w + g w) z =
      fderiv ℝ f z + fderiv ℝ g z by
        simpa only [Pi.add_apply] using fderiv_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Frechet-Wirtinger `∂z` of a difference. -/
theorem frechetDZValue_sub_of_differentiableAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    frechetDZValue (fun w : ℂ ↦ f w - g w) z =
      frechetDZValue f z - frechetDZValue g z := by
  rw [frechetDZValue, frechetDZValue, frechetDZValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ f w - g w) z =
      fderiv ℝ f z - fderiv ℝ g z by
        simpa only [Pi.sub_apply] using fderiv_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- Frechet-Wirtinger `∂bar` of a difference. -/
theorem frechetDBarValue_sub_of_differentiableAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    frechetDBarValue (fun w : ℂ ↦ f w - g w) z =
      frechetDBarValue f z - frechetDBarValue g z := by
  rw [frechetDBarValue, frechetDBarValue, frechetDBarValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ f w - g w) z =
      fderiv ℝ f z - fderiv ℝ g z by
        simpa only [Pi.sub_apply] using fderiv_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- Frechet-Wirtinger `∂bar` of a sum. -/
theorem frechetDBarValue_add_of_differentiableAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    frechetDBarValue (fun w : ℂ ↦ f w + g w) z =
      frechetDBarValue f z + frechetDBarValue g z := by
  rw [frechetDBarValue, frechetDBarValue, frechetDBarValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ f w + g w) z =
      fderiv ℝ f z + fderiv ℝ g z by
        simpa only [Pi.add_apply] using fderiv_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/--
For a real-valued function, the two complexified Frechet-Wirtinger derivatives
are conjugate.
-/
theorem frechetDBarValue_complex_ofReal_eq_star_frechetDZValue
    {φ : ℂ → ℝ} {z : ℂ} (hφ : DifferentiableAt ℝ φ z) :
    frechetDBarValue (fun w : ℂ ↦ (φ w : ℂ)) z =
      star (frechetDZValue (fun w : ℂ ↦ (φ w : ℂ)) z) := by
  let L : ℂ →L[ℝ] ℝ := fderiv ℝ φ z
  have hfd :
      fderiv ℝ (fun w : ℂ ↦ (φ w : ℂ)) z =
        Complex.ofRealCLM.comp L := by
    simpa [L] using
      (Complex.ofRealCLM.hasFDerivAt.comp z hφ.hasFDerivAt).fderiv
  simp [frechetDBarValue, frechetDZValue, L, hfd]

/--
For a real-valued function, vanishing of the complexified Frechet-Wirtinger
`∂z` value forces the full real Frechet derivative to vanish.
-/
theorem fderiv_real_eq_zero_of_frechetDZValue_complex_ofReal_eq_zero
    {φ : ℂ → ℝ} {z : ℂ}
    (hφ : DifferentiableAt ℝ φ z)
    (hZ : frechetDZValue (fun w : ℂ ↦ (φ w : ℂ)) z = 0) :
    fderiv ℝ φ z = 0 := by
  let L : ℂ →L[ℝ] ℝ := fderiv ℝ φ z
  have hfd :
      fderiv ℝ (fun w : ℂ ↦ (φ w : ℂ)) z =
        Complex.ofRealCLM.comp L := by
    simpa [L] using
      (Complex.ofRealCLM.hasFDerivAt.comp z hφ.hasFDerivAt).fderiv
  have hmain :
      (1 / 2 : ℂ) * ((L (1 : ℂ) : ℂ) - Complex.I * (L Complex.I : ℂ)) = 0 := by
    simpa [frechetDZValue, L, hfd] using hZ
  have hinner :
      ((L (1 : ℂ) : ℂ) - Complex.I * (L Complex.I : ℂ)) = 0 := by
    exact (mul_eq_zero.mp hmain).resolve_left (by norm_num)
  have hL1 : L (1 : ℂ) = 0 := by
    have hre := congrArg Complex.re hinner
    simpa using hre
  have hLI : L Complex.I = 0 := by
    have him := congrArg Complex.im hinner
    simpa using him
  apply ContinuousLinearMap.ext
  intro w
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    simp [Complex.re_add_im]
  calc
    L w = L ((w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I) := by
      exact congrArg L hw
    _ = (w.re : ℝ) • L (1 : ℂ) + (w.im : ℝ) • L Complex.I := by
      rw [map_add, map_smul, map_smul]
    _ = 0 := by
      simp [hL1, hLI]
    _ = (0 : ℂ →L[ℝ] ℝ) w := rfl

/--
On a preconnected open set, equality of the Frechet-Wirtinger `∂z` values of
two real-valued functions, after complexification, and equality at one point
force equality everywhere.
-/
theorem eqOn_of_frechetDZValue_complex_ofReal_eq
    {U : Set ℂ} {f g : ℂ → ℝ} {z₀ : ℂ}
    (hUopen : IsOpen U) (hUpre : IsPreconnected U)
    (hf : DifferentiableOn ℝ f U) (hg : DifferentiableOn ℝ g U)
    (hZ : ∀ z, z ∈ U →
      frechetDZValue (fun w : ℂ ↦ (f w : ℂ)) z =
        frechetDZValue (fun w : ℂ ↦ (g w : ℂ)) z)
    (hz₀ : z₀ ∈ U) (hbase : f z₀ = g z₀) :
    U.EqOn f g := by
  refine hUopen.eqOn_of_fderiv_eq hUpre hf hg ?_ hz₀ hbase
  intro z hz
  have hfz : DifferentiableAt ℝ f z := hf.differentiableAt (hUopen.mem_nhds hz)
  have hgz : DifferentiableAt ℝ g z := hg.differentiableAt (hUopen.mem_nhds hz)
  have hdiff : DifferentiableAt ℝ (fun w : ℂ ↦ f w - g w) z := hfz.sub hgz
  have hfzc : DifferentiableAt ℝ (fun w : ℂ ↦ (f w : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hfz
  have hgzc : DifferentiableAt ℝ (fun w : ℂ ↦ (g w : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hgz
  have hZsub :
      frechetDZValue (fun w : ℂ ↦ ((f w - g w : ℝ) : ℂ)) z = 0 := by
    calc
      frechetDZValue (fun w : ℂ ↦ ((f w - g w : ℝ) : ℂ)) z
          = frechetDZValue (fun w : ℂ ↦ (f w : ℂ) - (g w : ℂ)) z := by
              congr 1
              ext w
              simp
      _ = frechetDZValue (fun w : ℂ ↦ (f w : ℂ)) z -
            frechetDZValue (fun w : ℂ ↦ (g w : ℂ)) z :=
              frechetDZValue_sub_of_differentiableAt hfzc hgzc
      _ = 0 := by
            rw [hZ z hz, sub_self]
  have hFsub : fderiv ℝ (fun w : ℂ ↦ f w - g w) z = 0 :=
    fderiv_real_eq_zero_of_frechetDZValue_complex_ofReal_eq_zero hdiff hZsub
  have hFsub' : fderiv ℝ f z - fderiv ℝ g z = 0 := by
    simpa [fderiv_fun_sub hfz hgz] using hFsub
  exact sub_eq_zero.mp hFsub'

/-- Frechet-Wirtinger `∂z` of a constant multiple. -/
theorem frechetDZValue_const_mul_of_differentiableAt
    {f : ℂ → ℂ} {z c : ℂ} (hf : DifferentiableAt ℝ f z) :
    frechetDZValue (fun w : ℂ ↦ c * f w) z =
      c * frechetDZValue f z := by
  rw [frechetDZValue, frechetDZValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ c * f w) z =
      c • fderiv ℝ f z by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          (hf.hasFDerivAt.const_smul c).fderiv]
  simp only [ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring_nf

/-- Frechet-Wirtinger `∂z` of a product. -/
theorem frechetDZValue_mul_of_differentiableAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    frechetDZValue (fun w : ℂ ↦ f w * g w) z =
      frechetDZValue f z * g z + f z * frechetDZValue g z := by
  rw [frechetDZValue, frechetDZValue, frechetDZValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ f w * g w) z =
      f z • fderiv ℝ g z + g z • fderiv ℝ f z by
        simpa only [Pi.mul_apply] using fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring_nf

/-- Frechet-Wirtinger `∂z` of an inverse. -/
theorem frechetDZValue_inv_of_differentiableAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hfnz : f z ≠ 0) :
    frechetDZValue (fun w : ℂ ↦ (f w)⁻¹) z =
      - frechetDZValue f z / (f z) ^ 2 := by
  rw [frechetDZValue, frechetDZValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ (f w)⁻¹) z =
      (fderiv ℝ (fun x : ℂ ↦ x⁻¹) (f z)).comp (fderiv ℝ f z) by
        exact fderiv_comp z (differentiableAt_inv hfnz) hf]
  rw [show fderiv ℝ (fun x : ℂ ↦ x⁻¹) (f z) =
      fderiv ℝ Inv.inv (f z) by rfl]
  rw [show (fderiv ℝ Inv.inv (f z)).comp (fderiv ℝ f z) =
      (-ContinuousLinearMap.mulLeftRight ℝ ℂ (f z)⁻¹ (f z)⁻¹).comp (fderiv ℝ f z) by
        exact congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L.comp (fderiv ℝ f z))
          (fderiv_inv' (𝕜 := ℝ) hfnz)]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  field_simp [hfnz]
  ring_nf

/-- Frechet-Wirtinger quotient rule for complex-valued functions. -/
theorem frechetDZValue_div_of_differentiableAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hgnz : g z ≠ 0) :
    frechetDZValue (fun w : ℂ ↦ f w / g w) z =
      (frechetDZValue f z * g z - f z * frechetDZValue g z) / (g z) ^ 2 := by
  rw [show (fun w : ℂ ↦ f w / g w) =
      (fun w : ℂ ↦ f w * (g w)⁻¹) by
        ext w
        rw [div_eq_mul_inv]]
  rw [show frechetDZValue (fun w : ℂ ↦ f w * (g w)⁻¹) z =
      frechetDZValue f z * (g z)⁻¹ +
        f z * frechetDZValue (fun w : ℂ ↦ (g w)⁻¹) z by
        exact frechetDZValue_mul_of_differentiableAt hf (hg.inv hgnz)]
  rw [frechetDZValue_inv_of_differentiableAt hg hgnz]
  field_simp [hgnz]
  ring

/-- Frechet-Wirtinger `∂bar` of a constant multiple. -/
theorem frechetDBarValue_const_mul_of_differentiableAt
    {f : ℂ → ℂ} {z c : ℂ} (hf : DifferentiableAt ℝ f z) :
    frechetDBarValue (fun w : ℂ ↦ c * f w) z =
      c * frechetDBarValue f z := by
  rw [frechetDBarValue, frechetDBarValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ c * f w) z =
      c • fderiv ℝ f z by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          (hf.hasFDerivAt.const_smul c).fderiv]
  simp only [ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring_nf

/-- Frechet-Wirtinger `∂bar` of a product. -/
theorem frechetDBarValue_mul_of_differentiableAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    frechetDBarValue (fun w : ℂ ↦ f w * g w) z =
      frechetDBarValue f z * g z + f z * frechetDBarValue g z := by
  rw [frechetDBarValue, frechetDBarValue, frechetDBarValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ f w * g w) z =
      f z • fderiv ℝ g z + g z • fderiv ℝ f z by
        simpa only [Pi.mul_apply] using fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring_nf

/-- Frechet-Wirtinger `∂bar` of an inverse. -/
theorem frechetDBarValue_inv_of_differentiableAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hfnz : f z ≠ 0) :
    frechetDBarValue (fun w : ℂ ↦ (f w)⁻¹) z =
      - frechetDBarValue f z / (f z) ^ 2 := by
  rw [frechetDBarValue, frechetDBarValue]
  rw [show fderiv ℝ (fun w : ℂ ↦ (f w)⁻¹) z =
      (fderiv ℝ (fun x : ℂ ↦ x⁻¹) (f z)).comp (fderiv ℝ f z) by
        exact fderiv_comp z (differentiableAt_inv hfnz) hf]
  rw [show fderiv ℝ (fun x : ℂ ↦ x⁻¹) (f z) =
      fderiv ℝ Inv.inv (f z) by rfl]
  rw [show (fderiv ℝ Inv.inv (f z)).comp (fderiv ℝ f z) =
      (-ContinuousLinearMap.mulLeftRight ℝ ℂ (f z)⁻¹ (f z)⁻¹).comp (fderiv ℝ f z) by
        exact congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L.comp (fderiv ℝ f z))
          (fderiv_inv' (𝕜 := ℝ) hfnz)]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  field_simp [hfnz]
  ring_nf

/-- Frechet-Wirtinger quotient rule for `∂bar` of complex-valued functions. -/
theorem frechetDBarValue_div_of_differentiableAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hgnz : g z ≠ 0) :
    frechetDBarValue (fun w : ℂ ↦ f w / g w) z =
      (frechetDBarValue f z * g z - f z * frechetDBarValue g z) / (g z) ^ 2 := by
  rw [show (fun w : ℂ ↦ f w / g w) =
      (fun w : ℂ ↦ f w * (g w)⁻¹) by
        ext w
        rw [div_eq_mul_inv]]
  rw [show frechetDBarValue (fun w : ℂ ↦ f w * (g w)⁻¹) z =
      frechetDBarValue f z * (g z)⁻¹ +
        f z * frechetDBarValue (fun w : ℂ ↦ (g w)⁻¹) z by
        exact frechetDBarValue_mul_of_differentiableAt hf (hg.inv hgnz)]
  rw [frechetDBarValue_inv_of_differentiableAt hg hgnz]
  field_simp [hgnz]
  ring

/--
For a holomorphic one-variable function, the Frechet-Wirtinger `∂z` value is
its ordinary complex derivative.
-/
theorem frechetDZValue_of_hasDerivAt
    {f : ℂ → ℂ} {z f' : ℂ} (hf : HasDerivAt f f' z) :
    frechetDZValue f z = f' := by
  rw [frechetDZValue, hf.complexToReal_fderiv.fderiv]
  simp [ContinuousLinearMap.one_apply]
  rw [show Complex.I * (f' * Complex.I) = (Complex.I * Complex.I) * f' by ring]
  rw [Complex.I_mul_I]
  ring

/-- For a holomorphic one-variable function, the Frechet-Wirtinger `∂bar` value vanishes. -/
theorem frechetDBarValue_of_hasDerivAt
    {f : ℂ → ℂ} {z f' : ℂ} (hf : HasDerivAt f f' z) :
    frechetDBarValue f z = 0 := by
  rw [frechetDBarValue, hf.complexToReal_fderiv.fderiv]
  simp [ContinuousLinearMap.one_apply]
  rw [show Complex.I * (f' * Complex.I) = (Complex.I * Complex.I) * f' by ring]
  rw [Complex.I_mul_I]
  ring

/--
Frechet-Wirtinger chain rule for the logarithm of a positive real-valued
function, written after complexifying the real values.

This is the local calculus bridge used for squared conformal densities:
if `v = (1 / 2) log ρ`, then
`∂z v = (1 / (2ρ)) ∂z ρ`.
-/
theorem frechetDZValue_complex_ofReal_half_log_of_differentiableAt
    {ρ : ℂ → ℝ} {z₀ : ℂ} (hρ : DifferentiableAt ℝ ρ z₀)
    (hpos : 0 < ρ z₀) :
    frechetDZValue
        (fun z : ℂ ↦ (((1 / 2 : ℝ) * Real.log (ρ z) : ℝ) : ℂ)) z₀ =
      (1 / (2 * (ρ z₀ : ℂ))) *
        frechetDZValue (fun z : ℂ ↦ (ρ z : ℂ)) z₀ := by
  let L : ℂ →L[ℝ] ℝ := fderiv ℝ ρ z₀
  have hρF : HasFDerivAt ρ L z₀ := by
    simpa [L] using hρ.hasFDerivAt
  have hρcF :
      HasFDerivAt (fun z : ℂ ↦ (ρ z : ℂ)) (Complex.ofRealCLM.comp L) z₀ := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z₀ hρF)
  have hlog : HasDerivAt Real.log (ρ z₀)⁻¹ (ρ z₀) :=
    Real.hasDerivAt_log hpos.ne'
  have hhalfLog :
      HasDerivAt (fun x : ℝ ↦ (1 / 2 : ℝ) * Real.log x)
        ((1 / 2 : ℝ) * (ρ z₀)⁻¹) (ρ z₀) := by
    simpa using HasDerivAt.const_mul (1 / 2 : ℝ) hlog
  have hvFReal :
      HasFDerivAt (fun z : ℂ ↦ (1 / 2 : ℝ) * Real.log (ρ z))
        (((1 / 2 : ℝ) * (ρ z₀)⁻¹) • L) z₀ := by
    simpa only [Function.comp_apply] using
      (HasDerivAt.comp_hasFDerivAt z₀ hhalfLog hρF)
  have hvF :
      HasFDerivAt
        (fun z : ℂ ↦ (((1 / 2 : ℝ) * Real.log (ρ z) : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (((1 / 2 : ℝ) * (ρ z₀)⁻¹) • L)) z₀ := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z₀ hvFReal)
  repeat rw [frechetDZValue]
  rw [hvF.fderiv, hρcF.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.ofRealCLM_apply]
  norm_num
  ring

/--
Frechet-Wirtinger quotient rule for complexified real-valued functions.

This is the squared-density analogue of the logarithm bridge above: once the
numerator and denominator derivatives of a real quotient are known, the
`∂z`-derivative of the quotient follows from mathlib's Frechet calculus.
-/
theorem frechetDZValue_complex_ofReal_div_of_differentiableAt
    {A B : ℂ → ℝ} {z₀ : ℂ}
    (hA : DifferentiableAt ℝ A z₀) (hB : DifferentiableAt ℝ B z₀)
    (hB_ne : B z₀ ≠ 0) :
    frechetDZValue (fun z : ℂ ↦ ((A z / B z : ℝ) : ℂ)) z₀ =
      ((frechetDZValue (fun z : ℂ ↦ (A z : ℂ)) z₀) * (B z₀ : ℂ) -
        (A z₀ : ℂ) * frechetDZValue (fun z : ℂ ↦ (B z : ℂ)) z₀) /
        (B z₀ : ℂ) ^ 2 := by
  let LA : ℂ →L[ℝ] ℝ := fderiv ℝ A z₀
  let LB : ℂ →L[ℝ] ℝ := fderiv ℝ B z₀
  have hAF : HasFDerivAt A LA z₀ := by
    simpa [LA] using hA.hasFDerivAt
  have hBF : HasFDerivAt B LB z₀ := by
    simpa [LB] using hB.hasFDerivAt
  have hAcF :
      HasFDerivAt (fun z : ℂ ↦ (A z : ℂ)) (Complex.ofRealCLM.comp LA) z₀ := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z₀ hAF)
  have hBcF :
      HasFDerivAt (fun z : ℂ ↦ (B z : ℂ)) (Complex.ofRealCLM.comp LB) z₀ := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z₀ hBF)
  have hInvBase : HasFDerivAt (fun x : ℝ ↦ x⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(B z₀ ^ 2)⁻¹)) (B z₀) := by
    simpa using (hasDerivAt_inv hB_ne).hasFDerivAt
  have hInvB : HasFDerivAt (fun z : ℂ ↦ (B z)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(B z₀ ^ 2)⁻¹)).comp LB) z₀ := by
    simpa only [Function.comp_apply] using hInvBase.comp z₀ hBF
  have hQuotReal : HasFDerivAt (fun z : ℂ ↦ A z * (B z)⁻¹)
      (A z₀ • ((ContinuousLinearMap.toSpanSingleton ℝ (-(B z₀ ^ 2)⁻¹)).comp LB) +
        (B z₀)⁻¹ • LA) z₀ := by
    simpa only [Pi.mul_apply] using hAF.mul hInvB
  have hQuotReal' : HasFDerivAt (fun z : ℂ ↦ A z / B z)
      (A z₀ • ((ContinuousLinearMap.toSpanSingleton ℝ (-(B z₀ ^ 2)⁻¹)).comp LB) +
        (B z₀)⁻¹ • LA) z₀ := by
    simpa [div_eq_mul_inv] using hQuotReal
  have hQuotC :
      HasFDerivAt (fun z : ℂ ↦ ((A z / B z : ℝ) : ℂ))
        (Complex.ofRealCLM.comp
          (A z₀ • ((ContinuousLinearMap.toSpanSingleton ℝ (-(B z₀ ^ 2)⁻¹)).comp LB) +
            (B z₀)⁻¹ • LA)) z₀ := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z₀ hQuotReal')
  repeat rw [frechetDZValue]
  rw [hQuotC.fderiv, hAcF.fderiv, hBcF.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Complex.ofRealCLM_apply]
  norm_num
  field_simp [show (B z₀ : ℂ) ≠ 0 by exact_mod_cast hB_ne]
  ring

/-- Differentiability of the complexified imaginary part of a holomorphic branch. -/
theorem differentiableAt_complex_ofReal_im_of_hasDerivAt
    {F : ℂ → ℂ} {z₀ F' : ℂ} (hF : HasDerivAt F F' z₀) :
    DifferentiableAt ℝ (fun z : ℂ ↦ (((F z).im : ℝ) : ℂ)) z₀ := by
  let L : ℂ →L[ℝ] ℂ := F' • (1 : ℂ →L[ℝ] ℂ)
  let M : ℂ →L[ℝ] ℝ := Complex.imCLM.comp L
  have hFR : HasFDerivAt F L z₀ := by
    simpa [L] using hF.complexToReal_fderiv
  have hImF : HasFDerivAt (fun z : ℂ ↦ (F z).im) M z₀ := by
    simpa [M, Function.comp_apply, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp z₀ hFR)
  exact (Complex.ofRealCLM.hasFDerivAt.comp z₀ hImF).differentiableAt

/--
Frechet-Wirtinger derivative of the imaginary part of a holomorphic branch:
`∂z Im(F) = -i F' / 2`.
-/
theorem frechetDZValue_complex_ofReal_im_of_hasDerivAt_general
    {F : ℂ → ℂ} {z₀ F' : ℂ}
    (hF : HasDerivAt F F' z₀) :
    frechetDZValue (fun z : ℂ ↦ (((F z).im : ℝ) : ℂ)) z₀ =
      -Complex.I * F' / 2 := by
  let L : ℂ →L[ℝ] ℂ := F' • (1 : ℂ →L[ℝ] ℂ)
  let M : ℂ →L[ℝ] ℝ := Complex.imCLM.comp L
  have hFR : HasFDerivAt F L z₀ := by
    simpa [L] using hF.complexToReal_fderiv
  have hImF : HasFDerivAt (fun z : ℂ ↦ (F z).im) M z₀ := by
    simpa [M, Function.comp_apply, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp z₀ hFR)
  have hImC : HasFDerivAt (fun z : ℂ ↦ (((F z).im : ℝ) : ℂ))
      (Complex.ofRealCLM.comp M) z₀ := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z₀ hImF)
  rw [frechetDZValue]
  rw [hImC.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  simp [M, L, ContinuousLinearMap.one_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/--
Frechet-Wirtinger `∂bar` derivative of the imaginary part of a holomorphic
branch: `∂bar Im(F) = i \overline{F'} / 2`.
-/
theorem frechetDBarValue_complex_ofReal_im_of_hasDerivAt_general
    {F : ℂ → ℂ} {z₀ F' : ℂ}
    (hF : HasDerivAt F F' z₀) :
    frechetDBarValue (fun z : ℂ ↦ (((F z).im : ℝ) : ℂ)) z₀ =
      Complex.I * star F' / 2 := by
  have hdiff : DifferentiableAt ℝ (fun z : ℂ ↦ (F z).im) z₀ := by
    let L : ℂ →L[ℝ] ℂ := F' • (1 : ℂ →L[ℝ] ℂ)
    let M : ℂ →L[ℝ] ℝ := Complex.imCLM.comp L
    have hFR : HasFDerivAt F L z₀ := by
      simpa [L] using hF.complexToReal_fderiv
    have hImF : HasFDerivAt (fun z : ℂ ↦ (F z).im) M z₀ := by
      simpa [M, Function.comp_apply, Complex.imCLM_apply] using
        (Complex.imCLM.hasFDerivAt.comp z₀ hFR)
    exact hImF.differentiableAt
  rw [frechetDBarValue_complex_ofReal_eq_star_frechetDZValue hdiff]
  rw [frechetDZValue_complex_ofReal_im_of_hasDerivAt_general hF]
  simp

/--
Frechet-Wirtinger derivative of `(Im F)^2` for a holomorphic branch.

For a complex differentiable function `F`, the complexified real function
`z ↦ (Im F z)^2` satisfies
`∂z (Im F)^2 = -i (Im F) F'`.
-/
theorem frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt_general
    {F : ℂ → ℂ} {z₀ F' : ℂ}
    (hF : HasDerivAt F F' z₀) :
    frechetDZValue (fun z : ℂ ↦ (((F z).im ^ 2 : ℝ) : ℂ)) z₀ =
      -Complex.I * ((F z₀).im : ℂ) * F' := by
  let L : ℂ →L[ℝ] ℂ := F' • (1 : ℂ →L[ℝ] ℂ)
  let M : ℂ →L[ℝ] ℝ := Complex.imCLM.comp L
  have hFR : HasFDerivAt F L z₀ := by
    simpa [L] using hF.complexToReal_fderiv
  have hImF : HasFDerivAt (fun z : ℂ ↦ (F z).im) M z₀ := by
    simpa [M, Function.comp_apply, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp z₀ hFR)
  have hSqReal : HasFDerivAt (fun z : ℂ ↦ (F z).im * (F z).im)
      ((F z₀).im • M + (F z₀).im • M) z₀ := by
    simpa only [Pi.mul_apply] using hImF.mul hImF
  have hSqReal' : HasFDerivAt (fun z : ℂ ↦ (F z).im ^ 2)
      ((F z₀).im • M + (F z₀).im • M) z₀ := by
    simpa [pow_two] using hSqReal
  have hSqC : HasFDerivAt (fun z : ℂ ↦ (((F z).im ^ 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (((F z₀).im • M + (F z₀).im • M))) z₀ := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z₀ hSqReal')
  rw [frechetDZValue]
  rw [hSqC.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply]
  simp [M, L, ContinuousLinearMap.one_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/--
Frechet-Wirtinger derivative of `(Im F)^2` for a holomorphic branch.

At a point where `Im F = 1`, the identity is
`∂z (Im F)^2 = -i F'`.
-/
theorem frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt
    {F : ℂ → ℂ} {z₀ F' : ℂ}
    (hF : HasDerivAt F F' z₀) (hIm : (F z₀).im = 1) :
    frechetDZValue (fun z : ℂ ↦ (((F z).im ^ 2 : ℝ) : ℂ)) z₀ =
      -Complex.I * F' := by
  rw [frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt_general hF]
  rw [hIm]
  norm_num

/--
Frechet-Wirtinger derivative of `|G|²` for a holomorphic function.

For a complex differentiable function `G`, the complexified real function
`z ↦ |G(z)|²` satisfies
`∂z |G|² = conjugate(G) * G'`.
-/
theorem frechetDZValue_complex_ofReal_normSq_of_hasDerivAt
    {G : ℂ → ℂ} {z₀ G' : ℂ}
    (hG : HasDerivAt G G' z₀) :
    frechetDZValue (fun z : ℂ ↦ (Complex.normSq (G z) : ℂ)) z₀ =
      star (G z₀) * G' := by
  let L : ℂ →L[ℝ] ℂ := G' • (1 : ℂ →L[ℝ] ℂ)
  let LR : ℂ →L[ℝ] ℝ := Complex.reCLM.comp L
  let LI : ℂ →L[ℝ] ℝ := Complex.imCLM.comp L
  have hGR : HasFDerivAt G L z₀ := by
    simpa [L] using hG.complexToReal_fderiv
  have hReG : HasFDerivAt (fun z : ℂ ↦ (G z).re) LR z₀ := by
    simpa [LR, Function.comp_apply, Complex.reCLM_apply] using
      (Complex.reCLM.hasFDerivAt.comp z₀ hGR)
  have hImG : HasFDerivAt (fun z : ℂ ↦ (G z).im) LI z₀ := by
    simpa [LI, Function.comp_apply, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp z₀ hGR)
  have hReSq : HasFDerivAt (fun z : ℂ ↦ (G z).re * (G z).re)
      ((G z₀).re • LR + (G z₀).re • LR) z₀ := by
    simpa only [Pi.mul_apply] using hReG.mul hReG
  have hImSq : HasFDerivAt (fun z : ℂ ↦ (G z).im * (G z).im)
      ((G z₀).im • LI + (G z₀).im • LI) z₀ := by
    simpa only [Pi.mul_apply] using hImG.mul hImG
  have hNormReal : HasFDerivAt (fun z : ℂ ↦ Complex.normSq (G z))
      (((G z₀).re • LR + (G z₀).re • LR) +
        ((G z₀).im • LI + (G z₀).im • LI)) z₀ := by
    simpa [Complex.normSq_apply] using hReSq.add hImSq
  have hNormC : HasFDerivAt (fun z : ℂ ↦ (Complex.normSq (G z) : ℂ))
      (Complex.ofRealCLM.comp
        (((G z₀).re • LR + (G z₀).re • LR) +
          ((G z₀).im • LI + (G z₀).im • LI))) z₀ := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z₀ hNormReal)
  rw [frechetDZValue]
  rw [hNormC.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply]
  simp [LR, LI, L, ContinuousLinearMap.one_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/--
The symbolic function `dbar` is the Frechet/Wirtinger `∂_{\bar z}` value of
`f` on `U`.
-/
structure HasFrechetDBarOn (f dbar : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The underlying function is real differentiable at points of the domain. -/
  differentiable_at : ∀ z, z ∈ U → DifferentiableAt ℝ f z
  /-- The symbolic `dbar` agrees with the Frechet formula for `∂_{\bar z}`. -/
  dbar_eq_frechet : ∀ z, z ∈ U → dbar z = frechetDBarValue f z

/--
At a point, `∂_{\bar z} f = 0` in the real Frechet derivative sense is
equivalent to complex differentiability.
-/
theorem differentiableAt_complex_iff_hasDBarZeroAt (f : ℂ → ℂ) (z : ℂ) :
    DifferentiableAt ℂ f z ↔ HasDBarZeroAt f z := by
  simpa [HasDBarZeroAt] using
    (differentiableAt_complex_iff_differentiableAt_real
      (f := f) (x := z))

/--
If the Frechet/Wirtinger `∂_{\bar z}` value vanishes at a real-differentiability
point, then the Cauchy-Riemann condition holds there.
-/
theorem hasDBarZeroAt_of_frechetDBarValue_eq_zero
    {f : ℂ → ℂ} {z : ℂ}
    (hdiff : DifferentiableAt ℝ f z)
    (hzero : frechetDBarValue f z = 0) :
    HasDBarZeroAt f z := by
  refine ⟨hdiff, ?_⟩
  let a : ℂ := fderiv ℝ f z (1 : ℂ)
  let b : ℂ := fderiv ℝ f z Complex.I
  have hsum : a + Complex.I * b = 0 := by
    have h := hzero
    rw [frechetDBarValue] at h
    change (1 / 2 : ℂ) * (a + Complex.I * b) = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hIb : Complex.I * b = -a := by
    rw [← add_eq_zero_iff_eq_neg]
    simpa [add_comm] using hsum
  have hb : b = Complex.I * a := by
    calc
      b = (-Complex.I) * (Complex.I * b) := by
            rw [← mul_assoc, neg_mul, Complex.I_mul_I]
            ring
      _ = (-Complex.I) * (-a) := by rw [hIb]
      _ = Complex.I * a := by ring
  simpa [a, b, smul_eq_mul] using hb

/-- The Cauchy-Riemann condition makes the Frechet/Wirtinger `∂_{\bar z}` value vanish. -/
theorem frechetDBarValue_eq_zero_of_hasDBarZeroAt
    {f : ℂ → ℂ} {z : ℂ} (h : HasDBarZeroAt f z) :
    frechetDBarValue f z = 0 := by
  rw [frechetDBarValue, h.2]
  simp [smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/--
At a real-differentiability point, vanishing of the Frechet/Wirtinger
`∂_{\bar z}` value is equivalent to the Cauchy-Riemann condition.
-/
theorem frechetDBarValue_eq_zero_iff_hasDBarZeroAt
    {f : ℂ → ℂ} {z : ℂ} (hdiff : DifferentiableAt ℝ f z) :
    frechetDBarValue f z = 0 ↔ HasDBarZeroAt f z :=
  ⟨hasDBarZeroAt_of_frechetDBarValue_eq_zero hdiff,
    frechetDBarValue_eq_zero_of_hasDBarZeroAt⟩

/--
Named bridge between the concrete Frechet `∂_z` value and mathlib's
one-variable complex derivative.

This is intentionally kept as a theorem target for now.  The Cauchy-Riemann
criterion above proves complex differentiability from `∂_{\bar z}=0`; this
target additionally identifies the derivative value with the Frechet
Wirtinger formula.
-/
def FrechetDZValueIsComplexDerivativeTheorem : Prop :=
  ∀ {f : ℂ → ℂ} {z : ℂ}, HasDBarZeroAt f z →
    HasDerivAt f (frechetDZValue f z) z

/--
The Frechet/Wirtinger `∂_z` value is the ordinary one-variable complex
derivative whenever the Frechet/Wirtinger `∂_{\bar z}` value vanishes.

This closes the local bridge from the Cauchy-Riemann criterion supplied by
mathlib to the explicit derivative value used in the Schwarzian ODE layer.
-/
theorem frechetDZValueIsComplexDerivativeTheorem :
    FrechetDZValueIsComplexDerivativeTheorem := by
  intro f z h
  have hI :
      fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z (1 : ℂ) := by
    simpa [smul_eq_mul] using h.2
  have hdz : frechetDZValue f z = fderiv ℝ f z (1 : ℂ) := by
    rw [frechetDZValue, hI]
    calc
      (1 / 2 : ℂ) *
          (fderiv ℝ f z 1 -
            Complex.I * (Complex.I * fderiv ℝ f z (1 : ℂ)))
          =
          (1 / 2 : ℂ) *
            (fderiv ℝ f z 1 -
              (Complex.I * Complex.I) * fderiv ℝ f z (1 : ℂ)) := by
            ring
      _ = fderiv ℝ f z (1 : ℂ) := by
            rw [Complex.I_mul_I]
            ring
  rw [hdz]
  exact complexOfReal_hasDerivAt h.1 h.2

/--
Pointwise form of `FrechetDZValueIsComplexDerivativeTheorem`, useful when
threading canonical Wirtinger data into one-variable ODE statements.
-/
theorem hasDerivAt_frechetDZValue_of_hasDBarZeroAt
    {f : ℂ → ℂ} {z : ℂ} (h : HasDBarZeroAt f z) :
    HasDerivAt f (frechetDZValue f z) z :=
  frechetDZValueIsComplexDerivativeTheorem h

/-- Set-level form of `FrechetDZValueIsComplexDerivativeTheorem`. -/
theorem hasDerivAt_frechetDZValue_of_hasDBarZeroOn
    {f : ℂ → ℂ} {U : Set ℂ} (h : HasDBarZeroOn f U) :
    ∀ z, z ∈ U → HasDerivAt f (frechetDZValue f z) z := by
  intro z hz
  exact hasDerivAt_frechetDZValue_of_hasDBarZeroAt (h z hz)

namespace HasFrechetDBarOn

/--
If a symbolic `dbar` has been identified with the Frechet/Wirtinger
`∂_{\bar z}` operator and vanishes, then the function satisfies the
Cauchy-Riemann condition on the domain.
-/
theorem hasDBarZeroOn_of_dbar_eq_zero
    {f dbar : ℂ → ℂ} {U : Set ℂ}
    (D : HasFrechetDBarOn f dbar U)
    (hzero : ∀ z, z ∈ U → dbar z = 0) :
    HasDBarZeroOn f U := by
  intro z hz
  exact hasDBarZeroAt_of_frechetDBarValue_eq_zero (D.differentiable_at z hz) <| by
    rw [← D.dbar_eq_frechet z hz]
    exact hzero z hz

end HasFrechetDBarOn

/-- A function with `∂_{\bar z} = 0` at every point of a set is complex differentiable there. -/
theorem differentiableOn_complex_of_hasDBarZeroOn
    {f : ℂ → ℂ} {U : Set ℂ} (h : HasDBarZeroOn f U) :
    DifferentiableOn ℂ f U := by
  intro z hz
  exact ((differentiableAt_complex_iff_hasDBarZeroAt f z).2 (h z hz)).differentiableWithinAt

/-- On an open set, `∂_{\bar z} = 0` implies holomorphicity/analyticity. -/
theorem analyticOnNhd_of_hasDBarZeroOn
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h : HasDBarZeroOn f U) :
    AnalyticOnNhd ℂ f U :=
  (differentiableOn_complex_of_hasDBarZeroOn h).analyticOnNhd hU

/-- The same criterion phrased with `AnalyticOn`. -/
theorem analyticOn_of_hasDBarZeroOn
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h : HasDBarZeroOn f U) :
    AnalyticOn ℂ f U :=
  (differentiableOn_complex_of_hasDBarZeroOn h).analyticOn hU

/-- The Cauchy-Riemann/`∂_{\bar z} = 0` condition is closed under scalar multiplication. -/
theorem hasDBarZeroAt_const_smul
    {f : ℂ → ℂ} {z : ℂ} (c : ℂ) (h : HasDBarZeroAt f z) :
    HasDBarZeroAt (c • f) z := by
  exact (differentiableAt_complex_iff_hasDBarZeroAt (c • f) z).1
    (((differentiableAt_complex_iff_hasDBarZeroAt f z).2 h).const_smul c)

/-- The Cauchy-Riemann/`∂_{\bar z} = 0` condition on a set is closed under scalar multiplication. -/
theorem hasDBarZeroOn_const_smul
    {f : ℂ → ℂ} {U : Set ℂ} (c : ℂ) (h : HasDBarZeroOn f U) :
    HasDBarZeroOn (c • f) U := by
  intro z hz
  exact hasDBarZeroAt_const_smul c (h z hz)

/-- Multiplying a function by `2` preserves the `∂_{\bar z} = 0` condition. -/
theorem hasDBarZeroOn_two_mul
    {f : ℂ → ℂ} {U : Set ℂ} (h : HasDBarZeroOn f U) :
    HasDBarZeroOn (fun z ↦ 2 * f z) U := by
  simpa [Pi.smul_apply, smul_eq_mul] using hasDBarZeroOn_const_smul (2 : ℂ) h

namespace LocalConformalFactor

/-- The real log-density, regarded as a complex-valued function. -/
def complexLogDensity (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ (u.logDensity z : ℂ)

/-- The canonical Frechet-level Wirtinger derivative `u_z`. -/
def wirtingerZ (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ frechetDZValue u.complexLogDensity z

/-- The canonical Frechet-level Wirtinger derivative `u_{\bar z}`. -/
def wirtingerDBar (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ frechetDBarValue u.complexLogDensity z

/-- The canonical Frechet-level second Wirtinger derivative `u_{zz}`. -/
def wirtingerZZ (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ frechetDZValue u.wirtingerZ z

/-- The canonical Frechet-level mixed Wirtinger derivative `u_{z\bar z}`. -/
def wirtingerZBar (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ frechetDBarValue u.wirtingerZ z

/-- The canonical `z` derivative of the mixed Wirtinger derivative `u_{z\bar z}`. -/
def dZWirtingerZBar (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ frechetDZValue u.wirtingerZBar z

/-- The canonical `\bar z` derivative of `u_{zz}`. -/
def dbarWirtingerZZ (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ frechetDBarValue u.wirtingerZZ z

/-- The complexified conformal factor `exp (2u)`. -/
def expTwoUComplex (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ Complex.exp (2 * u.complexLogDensity z)

/-- The canonical `z` derivative of the complexified conformal factor. -/
def dZExpTwoUComplex (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ frechetDZValue u.expTwoUComplex z

/-- The unscaled metric Schwarzian coefficient `u_zz - u_z ^ 2`. -/
def halfSchwarzianCoefficient (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ u.wirtingerZZ z - u.wirtingerZ z ^ 2

/-- The canonical `∂_{\bar z}` derivative of the unscaled metric Schwarzian coefficient. -/
def dbarHalfSchwarzianCoefficient (u : LocalConformalFactor) : ℂ → ℂ :=
  fun z ↦ frechetDBarValue u.halfSchwarzianCoefficient z

@[simp]
theorem halfSchwarzianCoefficient_apply (u : LocalConformalFactor) (z : ℂ) :
    u.halfSchwarzianCoefficient z = u.wirtingerZZ z - u.wirtingerZ z ^ 2 :=
  rfl

@[simp]
theorem expTwoUComplex_apply (u : LocalConformalFactor) (z : ℂ) :
    u.expTwoUComplex z = (Real.exp (2 * u.logDensity z) : ℂ) :=
  by simp [expTwoUComplex, complexLogDensity, Complex.ofReal_exp]

/-- The complexified log-density inherits the `C^3` regularity of `u.logDensity`. -/
theorem complexLogDensity_contDiffOn (u : LocalConformalFactor) :
    ContDiffOn ℝ 3 u.complexLogDensity u.coordinateDomain := by
  simpa [complexLogDensity] using
    (Complex.ofRealCLM.contDiff.comp_contDiffOn u.logDensity_contDiffOn)

/-- The complexified log-density is `C^3` at points of the coordinate domain. -/
theorem complexLogDensity_contDiffAt (u : LocalConformalFactor) {z : ℂ}
    (hz : z ∈ u.coordinateDomain) :
    ContDiffAt ℝ 3 u.complexLogDensity z :=
  u.complexLogDensity_contDiffOn.contDiffAt (u.isOpen_coordinateDomain.mem_nhds hz)

/-- The concrete field `u_z` is `C^2` at points of the coordinate domain. -/
theorem wirtingerZ_contDiffAt (u : LocalConformalFactor) {z : ℂ}
    (hz : z ∈ u.coordinateDomain) :
    ContDiffAt ℝ 2 u.wirtingerZ z := by
  have hF : ContDiffAt ℝ 2 (fderiv ℝ u.complexLogDensity) z :=
    (u.complexLogDensity_contDiffAt hz).fderiv_right (m := 2) (by norm_num)
  have h1 : ContDiffAt ℝ 2 (fun w : ℂ ↦ fderiv ℝ u.complexLogDensity w (1 : ℂ)) z :=
    hF.clm_apply contDiffAt_const
  have hI : ContDiffAt ℝ 2 (fun w : ℂ ↦ fderiv ℝ u.complexLogDensity w Complex.I) z :=
    hF.clm_apply contDiffAt_const
  convert
    ContDiffAt.const_smul (1 / 2 : ℂ)
      (h1.sub (ContDiffAt.const_smul Complex.I hI)) using 1

/-- The concrete field `u_z` is real differentiable on the coordinate domain. -/
theorem wirtingerZ_differentiableAt (u : LocalConformalFactor) {z : ℂ}
    (hz : z ∈ u.coordinateDomain) :
    DifferentiableAt ℝ u.wirtingerZ z :=
  (u.wirtingerZ_contDiffAt hz).differentiableAt (by norm_num)

/-- The concrete field `u_z` is continuous on the coordinate domain. -/
theorem wirtingerZ_continuousOn (u : LocalConformalFactor) :
    ContinuousOn u.wirtingerZ u.coordinateDomain :=
  continuousOn_of_forall_continuousAt fun _ hz ↦
    (u.wirtingerZ_contDiffAt hz).continuousAt

/-- The concrete field `u_zz` is `C^1` at points of the coordinate domain. -/
theorem wirtingerZZ_contDiffAt (u : LocalConformalFactor) {z : ℂ}
    (hz : z ∈ u.coordinateDomain) :
    ContDiffAt ℝ 1 u.wirtingerZZ z := by
  have hF : ContDiffAt ℝ 1 (fderiv ℝ u.wirtingerZ) z :=
    (u.wirtingerZ_contDiffAt hz).fderiv_right (m := 1) (by norm_num)
  have h1 : ContDiffAt ℝ 1 (fun w : ℂ ↦ fderiv ℝ u.wirtingerZ w (1 : ℂ)) z :=
    hF.clm_apply contDiffAt_const
  have hI : ContDiffAt ℝ 1 (fun w : ℂ ↦ fderiv ℝ u.wirtingerZ w Complex.I) z :=
    hF.clm_apply contDiffAt_const
  convert
    ContDiffAt.const_smul (1 / 2 : ℂ)
      (h1.sub (ContDiffAt.const_smul Complex.I hI)) using 1

/-- The concrete field `u_zz` is real differentiable on the coordinate domain. -/
theorem wirtingerZZ_differentiableAt (u : LocalConformalFactor) {z : ℂ}
    (hz : z ∈ u.coordinateDomain) :
    DifferentiableAt ℝ u.wirtingerZZ z :=
  (u.wirtingerZZ_contDiffAt hz).differentiableAt (by norm_num)

/--
The concrete half-Schwarzian coefficient is differentiable once its two
component Wirtinger fields are differentiable.
-/
theorem halfSchwarzianCoefficient_differentiableAt
    (u : LocalConformalFactor) {z : ℂ}
    (hZZ : DifferentiableAt ℝ u.wirtingerZZ z)
    (hZ : DifferentiableAt ℝ u.wirtingerZ z) :
    DifferentiableAt ℝ u.halfSchwarzianCoefficient z := by
  change DifferentiableAt ℝ (fun w : ℂ ↦ u.wirtingerZZ w - u.wirtingerZ w ^ 2) z
  simpa [pow_two] using hZZ.sub (hZ.mul hZ)

/--
The product-rule part of the concrete Wirtinger package is a mathlib
calculus consequence of differentiability of `u_zz` and `u_z`.
-/
theorem dbarHalfSchwarzianCoefficient_eq_of_differentiableAt
    (u : LocalConformalFactor) {z : ℂ}
    (hZZ : DifferentiableAt ℝ u.wirtingerZZ z)
    (hZ : DifferentiableAt ℝ u.wirtingerZ z) :
    u.dbarHalfSchwarzianCoefficient z =
      u.dbarWirtingerZZ z - 2 * u.wirtingerZ z * u.wirtingerZBar z := by
  have hsq : DifferentiableAt ℝ (fun w : ℂ ↦ u.wirtingerZ w * u.wirtingerZ w) z :=
    hZ.mul hZ
  have hfd :
      fderiv ℝ u.halfSchwarzianCoefficient z =
        fderiv ℝ u.wirtingerZZ z -
          (u.wirtingerZ z • fderiv ℝ u.wirtingerZ z +
            u.wirtingerZ z • fderiv ℝ u.wirtingerZ z) := by
    change
      fderiv ℝ (fun w : ℂ ↦ u.wirtingerZZ w - u.wirtingerZ w ^ 2) z =
        fderiv ℝ u.wirtingerZZ z -
          (u.wirtingerZ z • fderiv ℝ u.wirtingerZ z +
            u.wirtingerZ z • fderiv ℝ u.wirtingerZ z)
    simp_rw [pow_two]
    rw [fderiv_fun_sub hZZ hsq]
    have hmul :
        fderiv ℝ (fun w : ℂ ↦ u.wirtingerZ w * u.wirtingerZ w) z =
          u.wirtingerZ z • fderiv ℝ u.wirtingerZ z +
            u.wirtingerZ z • fderiv ℝ u.wirtingerZ z := by
      simpa only using (fderiv_fun_mul hZ hZ)
    rw [hmul]
  rw [dbarHalfSchwarzianCoefficient, dbarWirtingerZZ, wirtingerZBar,
    frechetDBarValue]
  rw [hfd]
  simp [frechetDBarValue, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add]
  ring_nf

/--
Concrete Frechet/Wirtinger derivative identities needed for the local
Schwarzian calculation.

Unlike the older symbolic product-rule structures, all functions here are the
canonical Frechet-level Wirtinger expressions attached to `u.logDensity`.
  The fields record exactly the analytic identities still not derivable from the
stored finite-regularity predicate on `LocalConformalFactor`.
-/
structure WirtingerDerivativePackage (u : LocalConformalFactor) (K : ℝ) where
  /-- The identity `u_{z\bar z} = (1 / 4) Δu`. -/
  wirtingerZBar_eq_laplacian :
    ∀ z, z ∈ u.coordinateDomain →
      u.wirtingerZBar z = (1 / 4 : ℂ) * (Laplacian.laplacian u.logDensity z : ℂ)
  /-- Mixed derivative compatibility: `∂_{\bar z} u_zz = ∂_z u_{z\bar z}`. -/
  mixed_derivatives_eq :
    ∀ z, z ∈ u.coordinateDomain → u.dbarWirtingerZZ z = u.dZWirtingerZBar z
  /-- Differentiating `u_{z\bar z} = -(K / 4) exp (2u)` in the `z` direction. -/
  dZ_wirtingerZBar_eq :
    ∀ z, z ∈ u.coordinateDomain →
      u.dZWirtingerZBar z = -((K : ℂ) / 4) * u.dZExpTwoUComplex z
  /-- Chain rule for the `z` derivative of `exp (2u)`. -/
  dZ_expTwoU_eq :
    ∀ z, z ∈ u.coordinateDomain →
      u.dZExpTwoUComplex z = 2 * u.wirtingerZ z * u.expTwoUComplex z
  /-
  The differentiability of `u_zz - u_z ^ 2` and its `∂_{\bar z}` product rule
  are derived below from the `C^3` regularity carried by `LocalConformalFactor`.
  -/

namespace WirtingerDerivativePackage

/-- The concrete half-Schwarzian coefficient is real differentiable on the domain. -/
theorem halfSchwarzian_differentiable_at
    {u : LocalConformalFactor} {K : ℝ}
    (_W : u.WirtingerDerivativePackage K) :
  ∀ z, z ∈ u.coordinateDomain → DifferentiableAt ℝ u.halfSchwarzianCoefficient z := by
  intro z hz
  exact u.halfSchwarzianCoefficient_differentiableAt
    (u.wirtingerZZ_differentiableAt hz)
    (u.wirtingerZ_differentiableAt hz)

/-- Product rule for `∂_{\bar z}(u_zz - u_z ^ 2)`, derived by mathlib calculus. -/
theorem dbar_halfSchwarzian_eq
    {u : LocalConformalFactor} {K : ℝ}
    (_W : u.WirtingerDerivativePackage K) :
    ∀ z, z ∈ u.coordinateDomain →
      u.dbarHalfSchwarzianCoefficient z =
        u.dbarWirtingerZZ z - 2 * u.wirtingerZ z * u.wirtingerZBar z := by
  intro z hz
  exact u.dbarHalfSchwarzianCoefficient_eq_of_differentiableAt
    (u.wirtingerZZ_differentiableAt hz)
    (u.wirtingerZ_differentiableAt hz)

/--
The concrete `∂_{\bar z}` field of the half-Schwarzian coefficient is exactly
the Frechet/Wirtinger `∂_{\bar z}` value.
-/
theorem hasFrechetDBarOn_halfSchwarzian
    {u : LocalConformalFactor} {K : ℝ}
    (W : u.WirtingerDerivativePackage K) :
    HasFrechetDBarOn u.halfSchwarzianCoefficient u.dbarHalfSchwarzianCoefficient
      u.coordinateDomain where
  differentiable_at := W.halfSchwarzian_differentiable_at
  dbar_eq_frechet := by
    intro z _hz
    rfl

end WirtingerDerivativePackage

/-!
The remaining second-order Wirtinger identities are recorded here.  The most
basic identities are proved directly from mathlib's Frechet calculus; the
remaining higher-order compatibility statements are the intended next
replacement targets for project-local proofs from the `C^3` regularity field.
-/

/--
The complexified log-density has the complexification of the real-valued
Laplacian.
-/
theorem complexLogDensity_laplacian_eq
    (u : LocalConformalFactor) {z : ℂ} (hz : z ∈ u.coordinateDomain) :
    Laplacian.laplacian u.complexLogDensity z =
      (Laplacian.laplacian u.logDensity z : ℂ) := by
  have hlog2 : ContDiffAt ℝ 2 u.logDensity z :=
    (u.logDensity_contDiffOn.contDiffAt
      (u.isOpen_coordinateDomain.mem_nhds hz)).of_le (by norm_num)
  simpa [complexLogDensity] using
    hlog2.laplacian_CLM_comp_left (l := Complex.ofRealCLM)

/-- The identity `u_{z\bar z} = (1 / 4) Δu` for the concrete Frechet fields. -/
theorem wirtingerZBar_eq_laplacian
    (u : LocalConformalFactor) :
    ∀ z, z ∈ u.coordinateDomain →
      u.wirtingerZBar z = (1 / 4 : ℂ) * (Laplacian.laplacian u.logDensity z : ℂ) := by
  intro z hz
  have hf2 : ContDiffAt ℝ 2 u.complexLogDensity z :=
    (u.complexLogDensity_contDiffAt hz).of_le (by norm_num)
  have hF : DifferentiableAt ℝ (fderiv ℝ u.complexLogDensity) z :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ
      (fun w : ℂ ↦ fderiv ℝ u.complexLogDensity w (1 : ℂ)) z :=
    hF.clm_apply (differentiableAt_const (1 : ℂ))
  have hI : DifferentiableAt ℝ
      (fun w : ℂ ↦ fderiv ℝ u.complexLogDensity w Complex.I) z :=
    hF.clm_apply (differentiableAt_const Complex.I)
  have hInner : DifferentiableAt ℝ
      (fun w : ℂ ↦
        fderiv ℝ u.complexLogDensity w (1 : ℂ) -
          Complex.I * fderiv ℝ u.complexLogDensity w Complex.I) z :=
    h1.sub (hI.const_mul Complex.I)
  have hsymm : IsSymmSndFDerivAt ℝ u.complexLogDensity z :=
    hf2.isSymmSndFDerivAt (by simp)
  have hlapC : Laplacian.laplacian u.complexLogDensity z =
      (Laplacian.laplacian u.logDensity z : ℂ) :=
    u.complexLogDensity_laplacian_eq hz
  change frechetDBarValue (fun z ↦ frechetDZValue u.complexLogDensity z) z =
    (1 / 4 : ℂ) * (Laplacian.laplacian u.logDensity z : ℂ)
  simp only [frechetDBarValue, frechetDZValue]
  have hfd_outer :
      fderiv ℝ (fun w : ℂ ↦
        (1 / 2 : ℂ) *
          (fderiv ℝ u.complexLogDensity w (1 : ℂ) -
            Complex.I * fderiv ℝ u.complexLogDensity w Complex.I)) z =
        (1 / 2 : ℂ) • fderiv ℝ (fun w : ℂ ↦
          fderiv ℝ u.complexLogDensity w (1 : ℂ) -
            Complex.I * fderiv ℝ u.complexLogDensity w Complex.I) z := by
    simpa using fderiv_const_mul (𝕜 := ℝ) (a := fun w : ℂ ↦
      fderiv ℝ u.complexLogDensity w (1 : ℂ) -
        Complex.I * fderiv ℝ u.complexLogDensity w Complex.I)
      (x := z) hInner (1 / 2 : ℂ)
  rw [hfd_outer]
  rw [fderiv_fun_sub h1 (hI.const_mul Complex.I)]
  have hfd_I_mul :
      fderiv ℝ
          (fun y : ℂ => Complex.I * (fderiv ℝ u.complexLogDensity y) Complex.I) z =
        Complex.I • fderiv ℝ
          (fun y : ℂ => (fderiv ℝ u.complexLogDensity y) Complex.I) z := by
    simpa using fderiv_const_mul (𝕜 := ℝ)
      (a := fun y : ℂ ↦ fderiv ℝ u.complexLogDensity y Complex.I)
      (x := z) hI Complex.I
  rw [hfd_I_mul]
  rw [fderiv_clm_apply hF (differentiableAt_const (1 : ℂ))]
  rw [fderiv_clm_apply hF (differentiableAt_const Complex.I)]
  simp [ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [← hlapC]
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hsymm.eq Complex.I (1 : ℂ)]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/--
For a `C^2` complex-valued function, the concrete Frechet-Wirtinger operators
`∂z` and `∂bar` commute at a point.
-/
theorem frechetDBar_frechetDZ_eq_frechetDZ_frechetDBar
    {g : ℂ → ℂ} {z : ℂ} (hg : ContDiffAt ℝ 2 g z) :
    frechetDBarValue (fun w ↦ frechetDZValue g w) z =
      frechetDZValue (fun w ↦ frechetDBarValue g w) z := by
  have hF : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fun w : ℂ ↦ fderiv ℝ g w (1 : ℂ)) z :=
    hF.clm_apply (differentiableAt_const (1 : ℂ))
  have hI : DifferentiableAt ℝ (fun w : ℂ ↦ fderiv ℝ g w Complex.I) z :=
    hF.clm_apply (differentiableAt_const Complex.I)
  have hDZInner : DifferentiableAt ℝ
      (fun w : ℂ ↦ fderiv ℝ g w (1 : ℂ) -
        Complex.I * fderiv ℝ g w Complex.I) z :=
    h1.sub (hI.const_mul Complex.I)
  have hDBarInner : DifferentiableAt ℝ
      (fun w : ℂ ↦ fderiv ℝ g w (1 : ℂ) +
        Complex.I * fderiv ℝ g w Complex.I) z :=
    h1.add (hI.const_mul Complex.I)
  have hsymm : IsSymmSndFDerivAt ℝ g z :=
    hg.isSymmSndFDerivAt (by simp)
  change
    frechetDBarValue (fun w ↦ frechetDZValue g w) z =
      frechetDZValue (fun w ↦ frechetDBarValue g w) z
  simp only [frechetDBarValue, frechetDZValue]
  have hfd_DZ :
      fderiv ℝ (fun w : ℂ ↦
        (1 / 2 : ℂ) *
          (fderiv ℝ g w (1 : ℂ) - Complex.I * fderiv ℝ g w Complex.I)) z =
        (1 / 2 : ℂ) • fderiv ℝ (fun w : ℂ ↦
          fderiv ℝ g w (1 : ℂ) - Complex.I * fderiv ℝ g w Complex.I) z := by
    simpa using fderiv_const_mul (𝕜 := ℝ) (a := fun w : ℂ ↦
      fderiv ℝ g w (1 : ℂ) - Complex.I * fderiv ℝ g w Complex.I)
      (x := z) hDZInner (1 / 2 : ℂ)
  have hfd_DBar :
      fderiv ℝ (fun w : ℂ ↦
        (1 / 2 : ℂ) *
          (fderiv ℝ g w (1 : ℂ) + Complex.I * fderiv ℝ g w Complex.I)) z =
        (1 / 2 : ℂ) • fderiv ℝ (fun w : ℂ ↦
          fderiv ℝ g w (1 : ℂ) + Complex.I * fderiv ℝ g w Complex.I) z := by
    simpa using fderiv_const_mul (𝕜 := ℝ) (a := fun w : ℂ ↦
      fderiv ℝ g w (1 : ℂ) + Complex.I * fderiv ℝ g w Complex.I)
      (x := z) hDBarInner (1 / 2 : ℂ)
  have hfd_I_mul :
      fderiv ℝ (fun y : ℂ => Complex.I * (fderiv ℝ g y) Complex.I) z =
        Complex.I • fderiv ℝ (fun y : ℂ => (fderiv ℝ g y) Complex.I) z := by
    simpa using fderiv_const_mul (𝕜 := ℝ)
      (a := fun y : ℂ ↦ fderiv ℝ g y Complex.I)
      (x := z) hI Complex.I
  rw [hfd_DZ, hfd_DBar]
  rw [fderiv_fun_sub h1 (hI.const_mul Complex.I)]
  rw [fderiv_fun_add h1 (hI.const_mul Complex.I)]
  rw [hfd_I_mul]
  rw [fderiv_clm_apply hF (differentiableAt_const (1 : ℂ))]
  rw [fderiv_clm_apply hF (differentiableAt_const Complex.I)]
  simp [ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hsymm.eq Complex.I (1 : ℂ)]
  ring_nf

/-- Mixed derivative compatibility: `∂_{\bar z} u_zz = ∂_z u_{z\bar z}`. -/
theorem mixed_derivatives_eq
    (u : LocalConformalFactor) :
    ∀ z, z ∈ u.coordinateDomain → u.dbarWirtingerZZ z = u.dZWirtingerZBar z := by
  intro z hz
  exact frechetDBar_frechetDZ_eq_frechetDZ_frechetDBar
    (u.wirtingerZ_contDiffAt hz)

/-- Chain rule for the `z` derivative of `exp (2u)`. -/
theorem dZ_expTwoU_eq
    (u : LocalConformalFactor) :
    ∀ z, z ∈ u.coordinateDomain →
      u.dZExpTwoUComplex z = 2 * u.wirtingerZ z * u.expTwoUComplex z := by
  intro z hz
  have hlog : DifferentiableAt ℝ u.complexLogDensity z :=
    (u.complexLogDensity_contDiffAt hz).differentiableAt (by norm_num)
  have htwo : DifferentiableAt ℝ (fun w : ℂ ↦ 2 * u.complexLogDensity w) z :=
    hlog.const_mul (2 : ℂ)
  have hfd_exp :
      fderiv ℝ u.expTwoUComplex z =
        u.expTwoUComplex z • fderiv ℝ (fun w : ℂ ↦ 2 * u.complexLogDensity w) z := by
    have h :=
      ((Complex.hasStrictFDerivAt_exp_real
          (2 * u.complexLogDensity z)).hasFDerivAt.comp z htwo.hasFDerivAt).fderiv
    simpa [expTwoUComplex, ContinuousLinearMap.comp_assoc] using h
  have hfd_two :
      fderiv ℝ (fun w : ℂ ↦ 2 * u.complexLogDensity w) z =
        (2 : ℂ) • fderiv ℝ u.complexLogDensity z := by
    simpa using fderiv_const_mul (𝕜 := ℝ) (a := u.complexLogDensity)
      (x := z) hlog (2 : ℂ)
  rw [dZExpTwoUComplex, frechetDZValue, hfd_exp, hfd_two, wirtingerZ, frechetDZValue]
  simp [smul_eq_mul]
  ring

/--
Differentiating the constant-curvature identity
`u_{z\bar z} = -(K / 4) exp (2u)` in the `z` direction.

The pointwise identity is obtained from `u_{z\bar z} = (1 / 4) Δu` and the
constant-curvature equation, then differentiated by neighborhood congruence.
-/
theorem dZ_wirtingerZBar_eq_of_solvesConstantCurvatureEquation
    (u : LocalConformalFactor) (K : ℝ)
    (hK : u.SolvesConstantCurvatureEquation K) :
    ∀ z, z ∈ u.coordinateDomain →
      u.dZWirtingerZBar z = -((K : ℂ) / 4) * u.dZExpTwoUComplex z := by
  intro z hz
  let c : ℂ := -((K : ℂ) / 4)
  have hlocal :
      u.wirtingerZBar =ᶠ[nhds z] fun w : ℂ ↦ c * u.expTwoUComplex w :=
    Filter.Eventually.mono (u.isOpen_coordinateDomain.mem_nhds hz) fun w hw => by
      rw [u.wirtingerZBar_eq_laplacian w hw, hK w hw]
      simp [expTwoUComplex_apply, c]
      ring
  have hfd :
      fderiv ℝ u.wirtingerZBar z =
        fderiv ℝ (fun w : ℂ ↦ c * u.expTwoUComplex w) z :=
    hlocal.fderiv_eq
  have hlog : DifferentiableAt ℝ u.complexLogDensity z :=
    (u.complexLogDensity_contDiffAt hz).differentiableAt (by norm_num)
  have htwo : DifferentiableAt ℝ (fun w : ℂ ↦ 2 * u.complexLogDensity w) z :=
    hlog.const_mul (2 : ℂ)
  have hexp : DifferentiableAt ℝ u.expTwoUComplex z := by
    have hderiv :=
      (Complex.hasStrictFDerivAt_exp_real
        (2 * u.complexLogDensity z)).hasFDerivAt.comp z htwo.hasFDerivAt
    simpa [expTwoUComplex] using hderiv.differentiableAt
  have hfd_const :
      fderiv ℝ (fun w : ℂ ↦ c * u.expTwoUComplex w) z =
        c • fderiv ℝ u.expTwoUComplex z := by
    simpa using fderiv_const_mul (𝕜 := ℝ) (a := u.expTwoUComplex)
      (x := z) hexp c
  rw [dZWirtingerZBar, dZExpTwoUComplex, frechetDZValue, hfd, hfd_const]
  rw [frechetDZValue]
  simp [c, smul_eq_mul]
  ring_nf

/--
The concrete Wirtinger derivative package is now constructible from the named
analytic axioms above.
-/
def wirtingerDerivativePackage
    (u : LocalConformalFactor) (K : ℝ)
    (hK : u.SolvesConstantCurvatureEquation K) :
    u.WirtingerDerivativePackage K where
  wirtingerZBar_eq_laplacian := u.wirtingerZBar_eq_laplacian
  mixed_derivatives_eq := u.mixed_derivatives_eq
  dZ_wirtingerZBar_eq := u.dZ_wirtingerZBar_eq_of_solvesConstantCurvatureEquation K hK
  dZ_expTwoU_eq := u.dZ_expTwoU_eq

end LocalConformalFactor

/--
The local Wirtinger data needed for the Schwarzian calculation.

The intended meanings are:

* `uZ = u_z`;
* `uZZ = u_zz`;
* `expTwoU = exp (2u)`, complexified;
* `dbarUZZ = ∂_{\bar z}(u_zz)`;
* `dbarSchwarzian = ∂_{\bar z}(u_zz - u_z ^ 2)`.

The two identities come from differentiating
`u_{z\bar z} = -(K / 4) exp (2u)` and applying the product rule to
`u_z ^ 2`.
-/
structure SchwarzianWirtingerCalculationData (u : LocalConformalFactor) (K : ℝ) where
  /-- The first Wirtinger derivative `u_z`. -/
  uZ : ℂ → ℂ
  /-- The second Wirtinger derivative `u_zz`. -/
  uZZ : ℂ → ℂ
  /-- The complexified exponential factor `exp (2u)`. -/
  expTwoU : ℂ → ℂ
  /-- The Schwarzian/projective-connection coefficient `u_zz - u_z ^ 2`. -/
  schwarzianCoefficient : ℂ → ℂ
  /-- The `∂_{\bar z}` derivative of `u_zz`. -/
  dbarUZZ : ℂ → ℂ
  /-- The `∂_{\bar z}` derivative of the Schwarzian coefficient. -/
  dbarSchwarzian : ℂ → ℂ
  /-- The coefficient is `u_zz - u_z ^ 2`. -/
  schwarzianCoefficient_eq : ∀ z,
    schwarzianCoefficient z = uZZ z - uZ z ^ 2
  /-- Differentiating the constant-curvature equation gives this identity. -/
  dbarUZZ_eq : ∀ z,
    z ∈ u.coordinateDomain → dbarUZZ z = -((K : ℂ) / 2) * uZ z * expTwoU z
  /-- Product rule for `∂_{\bar z}(u_zz - u_z ^ 2)`. -/
  dbarSchwarzian_eq : ∀ z,
    z ∈ u.coordinateDomain →
    dbarSchwarzian z =
      dbarUZZ z - 2 * uZ z * (-((K : ℂ) / 4) * expTwoU z)

namespace SchwarzianWirtingerCalculationData

/--
The local Schwarzian calculation:

if `u_{z\bar z} = -(K / 4) exp (2u)`, then
`∂_{\bar z}(u_{zz} - u_z ^ 2) = 0`.

The analytic boundary is now the construction of the Wirtinger data and the
proofs of the two derivative identities from the current smooth local
conformal factor.
-/
theorem dbarSchwarzian_eq_zero
    {u : LocalConformalFactor} {K : ℝ}
    (C : SchwarzianWirtingerCalculationData u K) :
    ∀ z, z ∈ u.coordinateDomain → C.dbarSchwarzian z = 0 := by
  intro z hz
  rw [C.dbarSchwarzian_eq z hz, C.dbarUZZ_eq z hz]
  ring

end SchwarzianWirtingerCalculationData

/--
Primitive Wirtinger identities for a constant-curvature conformal factor.

This structure separates the easy algebra from the still-unimplemented analytic
instantiation of the symbolic Wirtinger derivatives.  The field
`uZBar_eq_laplacian` records the standard identity
`u_{z\bar z} = (1 / 4) Δu`; together with the constant-curvature equation it
gives `u_{z\bar z} = -(K / 4) exp (2u)`.  The remaining derivative fields record
the chain rule, mixed-derivative compatibility, and the derivative of that
identity in the `z` direction.
-/
structure ConstantCurvatureWirtingerIdentityData
    (u : LocalConformalFactor) (K : ℝ) where
  /-- The first Wirtinger derivative `u_z`. -/
  uZ : ℂ → ℂ
  /-- The mixed Wirtinger derivative `u_{z\bar z}`. -/
  uZBar : ℂ → ℂ
  /-- The `z` derivative of `u_{z\bar z}`. -/
  dZ_uZBar : ℂ → ℂ
  /-- The complexified exponential factor `exp (2u)`. -/
  expTwoU : ℂ → ℂ
  /-- The `z` derivative of `exp (2u)`. -/
  dZExpTwoU : ℂ → ℂ
  /-- The `∂_{\bar z}` derivative of `u_zz`. -/
  dbarUZZ : ℂ → ℂ
  /-- The identity `u_{z\bar z} = (1 / 4) Δu`. -/
  uZBar_eq_laplacian : ∀ z,
    z ∈ u.coordinateDomain →
      uZBar z = (1 / 4 : ℂ) * (Laplacian.laplacian u.logDensity z : ℂ)
  /-- The complexified exponential agrees with the real conformal density. -/
  expTwoU_eq : ∀ z,
    z ∈ u.coordinateDomain → expTwoU z = (Real.exp (2 * u.logDensity z) : ℂ)
  /-- Mixed derivative compatibility: `∂_{\bar z} u_zz = ∂_z u_{z\bar z}`. -/
  mixed_derivatives_eq : ∀ z,
    z ∈ u.coordinateDomain → dbarUZZ z = dZ_uZBar z
  /-- Differentiating `u_{z\bar z} = -(K / 4) exp (2u)` in the `z` direction. -/
  dZ_uZBar_eq : ∀ z,
    z ∈ u.coordinateDomain → dZ_uZBar z = -((K : ℂ) / 4) * dZExpTwoU z
  /-- Chain rule for the `z` derivative of `exp (2u)`. -/
  dZExpTwoU_eq : ∀ z,
    z ∈ u.coordinateDomain → dZExpTwoU z = 2 * uZ z * expTwoU z

namespace ConstantCurvatureWirtingerIdentityData

/--
The constant-curvature equation implies the Wirtinger form
`u_{z\bar z} = -(K / 4) exp (2u)`.
-/
theorem uZBar_eq_of_solvesConstantCurvatureEquation
    {u : LocalConformalFactor} {K : ℝ}
    (D : ConstantCurvatureWirtingerIdentityData u K)
    (hK : u.SolvesConstantCurvatureEquation K) :
    ∀ z, z ∈ u.coordinateDomain →
      D.uZBar z = -((K : ℂ) / 4) * D.expTwoU z := by
  intro z hz
  calc
    D.uZBar z
        = (1 / 4 : ℂ) * (Laplacian.laplacian u.logDensity z : ℂ) := by
            exact D.uZBar_eq_laplacian z hz
    _ = (1 / 4 : ℂ) * ((-K * Real.exp (2 * u.logDensity z) : ℝ) : ℂ) := by
            rw [hK z hz]
    _ = -((K : ℂ) / 4) * D.expTwoU z := by
            rw [D.expTwoU_eq z hz]
            norm_num
            ring

/--
After differentiating the Wirtinger constant-curvature identity, the chain rule
gives `∂_{\bar z} u_zz = -(K / 2) u_z exp (2u)`.
-/
theorem dbarUZZ_eq_of_differentiated_constantCurvatureEquation
    {u : LocalConformalFactor} {K : ℝ}
    (D : ConstantCurvatureWirtingerIdentityData u K) :
    ∀ z, z ∈ u.coordinateDomain →
      D.dbarUZZ z = -((K : ℂ) / 2) * D.uZ z * D.expTwoU z := by
  intro z hz
  rw [D.mixed_derivatives_eq z hz, D.dZ_uZBar_eq z hz, D.dZExpTwoU_eq z hz]
  ring

end ConstantCurvatureWirtingerIdentityData

/--
Product-rule data for the local Schwarzian coefficient
`q = u_zz - u_z ^ 2`.

The parent structure supplies the constant-curvature Wirtinger identities.  The
new fields identify the coefficient and record the product rule
`∂_{\bar z} q = ∂_{\bar z} u_zz - 2 u_z u_{z\bar z}`.
-/
structure SchwarzianProductRuleData (u : LocalConformalFactor) (K : ℝ)
    extends ConstantCurvatureWirtingerIdentityData u K where
  /-- The second Wirtinger derivative `u_zz`. -/
  uZZ : ℂ → ℂ
  /-- The Schwarzian/projective-connection coefficient `u_zz - u_z ^ 2`. -/
  schwarzianCoefficient : ℂ → ℂ
  /-- The `∂_{\bar z}` derivative of the Schwarzian coefficient. -/
  dbarSchwarzian : ℂ → ℂ
  /-- The coefficient is `u_zz - u_z ^ 2`. -/
  schwarzianCoefficient_eq : ∀ z,
    z ∈ u.coordinateDomain → schwarzianCoefficient z = uZZ z - uZ z ^ 2
  /-- Product rule for `∂_{\bar z}(u_zz - u_z ^ 2)`. -/
  dbarSchwarzian_product_eq : ∀ z,
    z ∈ u.coordinateDomain →
      dbarSchwarzian z = dbarUZZ z - 2 * uZ z * uZBar z

namespace SchwarzianProductRuleData

/--
Using the constant-curvature equation, the product rule becomes the exact
Schwarzian identity used in the final cancellation.
-/
theorem dbarSchwarzian_eq_of_solvesConstantCurvatureEquation
    {u : LocalConformalFactor} {K : ℝ}
    (P : SchwarzianProductRuleData u K)
    (hK : u.SolvesConstantCurvatureEquation K) :
    ∀ z, z ∈ u.coordinateDomain →
      P.dbarSchwarzian z =
        P.dbarUZZ z - 2 * P.uZ z * (-((K : ℂ) / 4) * P.expTwoU z) := by
  intro z hz
  rw [P.dbarSchwarzian_product_eq z hz,
    P.toConstantCurvatureWirtingerIdentityData.uZBar_eq_of_solvesConstantCurvatureEquation hK z hz]

/--
The local Schwarzian cancellation derived from the constant-curvature
Wirtinger identity, its differentiated form, the chain rule, mixed derivatives,
and the product rule.
-/
theorem dbarSchwarzian_eq_zero_of_solvesConstantCurvatureEquation
    {u : LocalConformalFactor} {K : ℝ}
    (P : SchwarzianProductRuleData u K)
    (hK : u.SolvesConstantCurvatureEquation K) :
    ∀ z, z ∈ u.coordinateDomain → P.dbarSchwarzian z = 0 := by
  intro z hz
  rw [P.dbarSchwarzian_eq_of_solvesConstantCurvatureEquation hK z hz,
    P.toConstantCurvatureWirtingerIdentityData.dbarUZZ_eq_of_differentiated_constantCurvatureEquation
      z hz]
  ring

end SchwarzianProductRuleData

/--
Local holomorphic Schwarzian/projective-connection data attached to a conformal
factor.

In a chosen complex coordinate the intended coefficient is
`2 * (u_zz - u_z ^ 2)`.  Across coordinate changes this coefficient obeys the
Schwarzian projective-connection transformation law, so this structure is local
coordinate data rather than a global quadratic differential by itself.
-/
structure LocalSchwarzianData (u : LocalConformalFactor) where
  /-- The local Schwarzian/projective-connection coefficient. -/
  coefficient : ℂ → ℂ
  /-- Holomorphicity of `coefficient` on `u.coordinateDomain`. -/
  holomorphic_on_domain : AnalyticOnNhd ℂ coefficient u.coordinateDomain
  /-- The coefficient is the canonical metric Schwarzian `2 * (u_zz - u_z ^ 2)`. -/
  coefficient_eq_metricSchwarzian :
    ∀ z, z ∈ u.coordinateDomain →
      coefficient z =
        2 * u.halfSchwarzianCoefficient z
  /-- The Cauchy-Riemann/`∂_{\bar z} = 0` condition for `coefficient`. -/
  has_dbar_zero_on : HasDBarZeroOn coefficient u.coordinateDomain

namespace LocalSchwarzianData

/-- The underlying coordinate domain of a local Schwarzian coefficient. -/
def coordinateDomain {u : LocalConformalFactor} (_S : LocalSchwarzianData u) : Set ℂ :=
  u.coordinateDomain

/--
The actual Schwarzian coefficient of a hyperbolic developing map is twice the
unscaled Liouville expression `u_zz - u_z ^ 2`.
-/
def metricSchwarzianCoefficient (halfCoefficient : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ 2 * halfCoefficient z

@[simp]
theorem metricSchwarzianCoefficient_apply (halfCoefficient : ℂ → ℂ) (z : ℂ) :
    metricSchwarzianCoefficient halfCoefficient z = 2 * halfCoefficient z :=
  rfl

/-- If the unscaled Liouville expression has `∂_{\bar z} = 0`, so does the actual Schwarzian coefficient. -/
theorem hasDBarZeroOn_metricSchwarzianCoefficient
    {u : LocalConformalFactor} {halfCoefficient : ℂ → ℂ}
    (h : HasDBarZeroOn halfCoefficient u.coordinateDomain) :
    HasDBarZeroOn (metricSchwarzianCoefficient halfCoefficient) u.coordinateDomain := by
  simpa [metricSchwarzianCoefficient] using hasDBarZeroOn_two_mul h

/--
Construct local Schwarzian data for the actual metric Schwarzian coefficient
`2q` from the unscaled Liouville expression `q`.
-/
def of_halfCoefficient_hasDBarZeroOn {u : LocalConformalFactor} (q : ℂ → ℂ)
    (hformula :
      ∀ z, z ∈ u.coordinateDomain → q z = u.halfSchwarzianCoefficient z)
    (hdbar : HasDBarZeroOn q u.coordinateDomain) :
    LocalSchwarzianData u where
  coefficient := metricSchwarzianCoefficient q
  holomorphic_on_domain :=
    analyticOnNhd_of_hasDBarZeroOn u.isOpen_coordinateDomain
      (hasDBarZeroOn_metricSchwarzianCoefficient hdbar)
  coefficient_eq_metricSchwarzian := by
    intro z hz
    simp [metricSchwarzianCoefficient, hformula z hz]
  has_dbar_zero_on := hasDBarZeroOn_metricSchwarzianCoefficient hdbar

/--
Construct local Schwarzian data once the coefficient has been identified and
its `∂_{\bar z}` derivative has been shown to vanish in the Cauchy-Riemann
sense.
-/
def of_hasDBarZeroOn {u : LocalConformalFactor} (q : ℂ → ℂ)
    (hformula :
      ∀ z, z ∈ u.coordinateDomain →
        q z = metricSchwarzianCoefficient u.halfSchwarzianCoefficient z)
    (hdbar : HasDBarZeroOn q u.coordinateDomain) :
    LocalSchwarzianData u where
  coefficient := q
  holomorphic_on_domain :=
    analyticOnNhd_of_hasDBarZeroOn u.isOpen_coordinateDomain hdbar
  coefficient_eq_metricSchwarzian := hformula
  has_dbar_zero_on := hdbar

end LocalSchwarzianData

/--
The stored local Schwarzian coefficient is the metric Schwarzian coefficient
of the conformal factor `u`.

This keeps the original-side coefficient identification as a reusable equality
rather than an opaque assumption.  It is the input needed to compare the
canonical Poincare pullback metric Schwarzian with the original Liouville
metric Schwarzian.
-/
structure LocalOriginalMetricSchwarzianIdentification
    {u : LocalConformalFactor} (S : LocalSchwarzianData u) where
  coefficient_eq_metric :
    ∀ z, z ∈ u.coordinateDomain →
      S.coefficient z =
        LocalSchwarzianData.metricSchwarzianCoefficient
          u.halfSchwarzianCoefficient z

/--
Local Schwarzian data whose coefficient is known to be the canonical metric
Schwarzian coefficient of `u`.
-/
structure LocalMetricSchwarzianData (u : LocalConformalFactor) where
  /-- The underlying holomorphic Schwarzian/projective-connection data. -/
  toLocalSchwarzianData : LocalSchwarzianData u
  /-- The coefficient is the metric Schwarzian coefficient of `u`. -/
  originalMetricIdentification :
    LocalOriginalMetricSchwarzianIdentification toLocalSchwarzianData

/--
Unscaled local Liouville Schwarzian data.

The local Wirtinger computation naturally produces the holomorphicity of
`q = u_zz - u_z ^ 2`.  The actual developing-map Schwarzian coefficient is
`2q`, so this structure is an intermediate analytic output.
-/
structure LocalHalfSchwarzianData (u : LocalConformalFactor) where
  /-- The unscaled Liouville expression, intended to be `u_zz - u_z ^ 2`. -/
  halfCoefficient : ℂ → ℂ
  /-- The half coefficient is the canonical Liouville expression `u_zz - u_z ^ 2`. -/
  halfCoefficient_eq_wirtinger_formula :
    ∀ z, z ∈ u.coordinateDomain → halfCoefficient z = u.halfSchwarzianCoefficient z
  /-- The unscaled coefficient satisfies the Cauchy-Riemann condition. -/
  has_dbar_zero_on : HasDBarZeroOn halfCoefficient u.coordinateDomain

namespace LocalHalfSchwarzianData

/-- Scale the unscaled Liouville coefficient to the actual Schwarzian data. -/
def toLocalSchwarzianData {u : LocalConformalFactor} (H : LocalHalfSchwarzianData u) :
    LocalSchwarzianData u :=
  LocalSchwarzianData.of_halfCoefficient_hasDBarZeroOn H.halfCoefficient
    H.halfCoefficient_eq_wirtinger_formula H.has_dbar_zero_on

@[simp]
theorem toLocalSchwarzianData_coefficient
    {u : LocalConformalFactor} (H : LocalHalfSchwarzianData u) :
    H.toLocalSchwarzianData.coefficient =
      LocalSchwarzianData.metricSchwarzianCoefficient H.halfCoefficient :=
  rfl

end LocalHalfSchwarzianData

namespace SchwarzianWirtingerCalculationData

/--
If the symbolic `∂_{\bar z}` field for `u_zz - u_z ^ 2` has been identified
with the real Cauchy-Riemann condition, the direct Wirtinger calculation
produces unscaled local Schwarzian data.
-/
def toLocalHalfSchwarzianData
    {u : LocalConformalFactor} {K : ℝ}
    (C : SchwarzianWirtingerCalculationData u K)
    (hformula :
      ∀ z, z ∈ u.coordinateDomain →
        C.schwarzianCoefficient z = u.halfSchwarzianCoefficient z)
    (hCR : HasDBarZeroOn C.schwarzianCoefficient u.coordinateDomain) :
    LocalHalfSchwarzianData u where
  halfCoefficient := C.schwarzianCoefficient
  halfCoefficient_eq_wirtinger_formula := hformula
  has_dbar_zero_on := hCR

end SchwarzianWirtingerCalculationData

namespace SchwarzianProductRuleData

/--
If the symbolic `∂_{\bar z}` field for `u_zz - u_z ^ 2` has been identified
with the real Cauchy-Riemann condition, the product-rule calculation produces
unscaled local Schwarzian data.
-/
def toLocalHalfSchwarzianData
    {u : LocalConformalFactor} {K : ℝ}
    (P : SchwarzianProductRuleData u K)
    (hformula :
      ∀ z, z ∈ u.coordinateDomain →
        P.schwarzianCoefficient z = u.halfSchwarzianCoefficient z)
    (hCR : HasDBarZeroOn P.schwarzianCoefficient u.coordinateDomain) :
    LocalHalfSchwarzianData u where
  halfCoefficient := P.schwarzianCoefficient
  halfCoefficient_eq_wirtinger_formula := hformula
  has_dbar_zero_on := hCR

end SchwarzianProductRuleData

namespace LocalConformalFactor.WirtingerDerivativePackage

/--
Concrete Frechet/Wirtinger data instantiate the older symbolic
constant-curvature identity package.
-/
def toConstantCurvatureWirtingerIdentityData
    {u : LocalConformalFactor} {K : ℝ}
    (W : u.WirtingerDerivativePackage K) :
    ConstantCurvatureWirtingerIdentityData u K where
  uZ := u.wirtingerZ
  uZBar := u.wirtingerZBar
  dZ_uZBar := u.dZWirtingerZBar
  expTwoU := u.expTwoUComplex
  dZExpTwoU := u.dZExpTwoUComplex
  dbarUZZ := u.dbarWirtingerZZ
  uZBar_eq_laplacian := W.wirtingerZBar_eq_laplacian
  expTwoU_eq := by
    intro z _hz
    exact u.expTwoUComplex_apply z
  mixed_derivatives_eq := W.mixed_derivatives_eq
  dZ_uZBar_eq := W.dZ_wirtingerZBar_eq
  dZExpTwoU_eq := W.dZ_expTwoU_eq

/--
Concrete Frechet/Wirtinger data instantiate the symbolic product-rule package
used by the Schwarzian cancellation theorem.
-/
def toSchwarzianProductRuleData
    {u : LocalConformalFactor} {K : ℝ}
    (W : u.WirtingerDerivativePackage K) :
    SchwarzianProductRuleData u K where
  toConstantCurvatureWirtingerIdentityData :=
    W.toConstantCurvatureWirtingerIdentityData
  uZZ := u.wirtingerZZ
  schwarzianCoefficient := u.halfSchwarzianCoefficient
  dbarSchwarzian := u.dbarHalfSchwarzianCoefficient
  schwarzianCoefficient_eq := by
    intro z _hz
    rfl
  dbarSchwarzian_product_eq := W.dbar_halfSchwarzian_eq

/--
The half-Schwarzian data produced by a concrete Frechet/Wirtinger package.
-/
def toLocalHalfSchwarzianData
    {u : LocalConformalFactor} {K : ℝ}
    (W : u.WirtingerDerivativePackage K)
    (hK : u.SolvesConstantCurvatureEquation K) :
    LocalHalfSchwarzianData u :=
  let P := W.toSchwarzianProductRuleData
  P.toLocalHalfSchwarzianData
    (by
      intro z _hz
      rfl)
    ((W.hasFrechetDBarOn_halfSchwarzian).hasDBarZeroOn_of_dbar_eq_zero
      (P.dbarSchwarzian_eq_zero_of_solvesConstantCurvatureEquation hK))

/--
The Schwarzian data produced from the concrete Frechet-Wirtinger package has
the canonical metric Schwarzian coefficient of `u`.
-/
theorem toLocalSchwarzianData_originalMetricIdentification
    {u : LocalConformalFactor} {K : ℝ}
    (W : u.WirtingerDerivativePackage K)
    (hK : u.SolvesConstantCurvatureEquation K) :
    LocalOriginalMetricSchwarzianIdentification
      (W.toLocalHalfSchwarzianData hK).toLocalSchwarzianData where
  coefficient_eq_metric := by
    intro z _hz
    rfl

/--
The concrete Frechet-Wirtinger package produces local metric Schwarzian data,
not merely an anonymous holomorphic coefficient.
-/
def toLocalMetricSchwarzianData
    {u : LocalConformalFactor} {K : ℝ}
    (W : u.WirtingerDerivativePackage K)
    (hK : u.SolvesConstantCurvatureEquation K) :
    LocalMetricSchwarzianData u where
  toLocalSchwarzianData := (W.toLocalHalfSchwarzianData hK).toLocalSchwarzianData
  originalMetricIdentification :=
    W.toLocalSchwarzianData_originalMetricIdentification hK

end LocalConformalFactor.WirtingerDerivativePackage

end

end JJMath
