import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The Beurling transform on planar `L²`

This file constructs the Hilbert-space part of the Beurling transform directly
from Plancherel's theorem.  With Mathlib's Fourier convention, the symbols of
`∂_z` and `∂_{\bar z}` are respectively `π i \bar ξ` and `π i ξ`.  The
multiplier which converts the latter into the former is therefore

`m(ξ) = \bar ξ / ξ`.

At frequency zero we set `m(0) = 1`.  This value does not affect the associated
`L²` class and has the useful feature that `|m(ξ)| = 1` literally everywhere.
Pointwise multiplication by this symbol is consequently an `L²` isometry, and
conjugating by the unitary Fourier transform gives the Beurling transform.

No Calderón--Zygmund estimate is used here.  Boundedness on `Lᵖ` for `p > 2`
is a separate, substantially deeper part of the principal-solution branch.
-/

namespace JJMath

open MeasureTheory
open FourierTransform LineDeriv
open scoped ENNReal ComplexConjugate FourierTransform SchwartzMap LineDeriv

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Planar complex $L^2$ space
statement:
  The planar complex $L^2$ space consists of equivalence classes of
  square-integrable functions $f:\mathbb C\to\mathbb C$ with respect to
  Lebesgue measure.
-/
abbrev PlaneL2 := Lp (α := ℂ) ℂ 2 volume

/--
%%handwave
name:
  Schwartz $z$-Wirtinger derivative
statement:
  For a complex-valued Schwartz function $f$ on $\mathbb C$, define
  $$
    \partial_z f=\frac12(\partial_1f-i\partial_if).
  $$
-/
def schwartzWirtingerZ (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (∂_{(1 : ℂ)} f - Complex.I • ∂_{Complex.I} f)

/--
%%handwave
name:
  Schwartz $\bar z$-Wirtinger derivative
statement:
  For a complex-valued Schwartz function $f$ on $\mathbb C$, define
  $$
    \partial_{\bar z}f=\frac12(\partial_1f+i\partial_if).
  $$
-/
def schwartzWirtingerDBar (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (∂_{(1 : ℂ)} f + Complex.I • ∂_{Complex.I} f)

/--
%%handwave
name:
  Fourier symbol of the $z$-Wirtinger derivative
statement:
  For every complex-valued Schwartz function $f$ on $\mathbb C$ and every
  $\xi\in\mathbb C$,
  $$
    \mathcal F(\partial_z f)(\xi)
      =\pi i\,\overline\xi\,\mathcal Ff(\xi).
  $$
proof:
  The Fourier symbol of the directional derivative in direction $v$ is
  $2\pi i\langle\xi,v\rangle_{\mathbb R}$. Substitute $v=1$ and $v=i$ into
  $\partial_z=\tfrac12(\partial_1-i\partial_i)$ and identify the result with
  $\pi i\overline\xi$.
-/
theorem fourier_schwartzWirtingerZ_apply
    (f : 𝓢(ℂ, ℂ)) (ξ : ℂ) :
    (𝓕 (schwartzWirtingerZ f) : 𝓢(ℂ, ℂ)) ξ =
      (Real.pi * Complex.I * starRingEnd ℂ ξ) *
        (𝓕 f : 𝓢(ℂ, ℂ)) ξ := by
  change (FourierTransform.fourierCLM ℂ (𝓢(ℂ, ℂ))
    (schwartzWirtingerZ f)) ξ = _
  rw [schwartzWirtingerZ, map_smul, map_sub, map_smul]
  simp only [FourierTransform.fourierCLM_apply,
    SchwartzMap.fourier_lineDerivOp_eq]
  simp [SchwartzMap.smul_apply, Complex.inner]
  have hre : (fun x : ℂ ↦ x.re).HasTemperateGrowth := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.hasTemperateGrowth
  have him : (fun x : ℂ ↦ x.im).HasTemperateGrowth := by
    simpa [Complex.imCLM_apply] using Complex.imCLM.hasTemperateGrowth
  rw [SchwartzMap.smulLeftCLM_apply_apply hre,
    SchwartzMap.smulLeftCLM_apply_apply him]
  simp
  have hstar : starRingEnd ℂ ξ =
      (ξ.re : ℂ) - (ξ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hstar]
  ring_nf

/--
%%handwave
name:
  Fourier symbol of the $\overline z$-Wirtinger derivative
statement:
  For every complex-valued Schwartz function $f$ on $\mathbb C$ and every
  $\xi\in\mathbb C$,
  $$
    \mathcal F(\partial_{\bar z} f)(\xi)
      =\pi i\,\xi\,\mathcal Ff(\xi).
  $$
proof:
  The Fourier symbol of the directional derivative in direction $v$ is
  $2\pi i\langle\xi,v\rangle_{\mathbb R}$. Substitute $v=1$ and $v=i$ into
  $\partial_{\bar z}=\tfrac12(\partial_1+i\partial_i)$ and identify the
  result with $\pi i\xi$.
-/
theorem fourier_schwartzWirtingerDBar_apply
    (f : 𝓢(ℂ, ℂ)) (ξ : ℂ) :
    (𝓕 (schwartzWirtingerDBar f) : 𝓢(ℂ, ℂ)) ξ =
      (Real.pi * Complex.I * ξ) * (𝓕 f : 𝓢(ℂ, ℂ)) ξ := by
  change (FourierTransform.fourierCLM ℂ (𝓢(ℂ, ℂ))
    (schwartzWirtingerDBar f)) ξ = _
  rw [schwartzWirtingerDBar, map_smul, map_add, map_smul]
  simp only [FourierTransform.fourierCLM_apply,
    SchwartzMap.fourier_lineDerivOp_eq]
  simp [SchwartzMap.smul_apply, Complex.inner]
  have hre : (fun x : ℂ ↦ x.re).HasTemperateGrowth := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.hasTemperateGrowth
  have him : (fun x : ℂ ↦ x.im).HasTemperateGrowth := by
    simpa [Complex.imCLM_apply] using Complex.imCLM.hasTemperateGrowth
  rw [SchwartzMap.smulLeftCLM_apply_apply hre,
    SchwartzMap.smulLeftCLM_apply_apply him]
  simp
  have hcoef :
      Real.pi * Complex.I * (ξ.re : ℂ) +
          Real.pi * Complex.I ^ 2 * (ξ.im : ℂ) =
        Real.pi * Complex.I * ξ := by
    calc
      _ = Real.pi * Complex.I *
          ((ξ.re : ℂ) + (ξ.im : ℂ) * Complex.I) := by ring
      _ = Real.pi * Complex.I * ξ := by rw [Complex.re_add_im]
  calc
    _ = (Real.pi * Complex.I * (ξ.re : ℂ) +
          Real.pi * Complex.I ^ 2 * (ξ.im : ℂ)) *
        (𝓕 f : 𝓢(ℂ, ℂ)) ξ := by ring
    _ = (Real.pi * Complex.I * ξ) *
        (𝓕 f : 𝓢(ℂ, ℂ)) ξ := by rw [hcoef]
    _ = _ := by ring

/--
%%handwave
name:
  Algebraic $L^\infty$ multiplier on planar $L^2$
statement:
  Every $m\in L^\infty(\mathbb C)$ determines the complex-linear map on
  $L^2(\mathbb C)$ given by $f\mapsto mf$.
-/
def l2PointwiseMultiplierLinearMap
    (m : Lp (α := ℂ) ℂ ∞ volume) : PlaneL2 →ₗ[ℂ] PlaneL2 where
  toFun f := m • f
  map_add' f g := MeasureTheory.Lp.add_smul m f g
  map_smul' c f := (MeasureTheory.Lp.smul_comm c m f).symm

/--
%%handwave
name:
  Bounded $L^\infty$ multiplier on planar $L^2$
statement:
  For $m\in L^\infty(\mathbb C)$, pointwise multiplication is the bounded
  complex-linear operator $M_mf=mf$ on $L^2(\mathbb C)$, with operator norm
  at most $\|m\|_\infty$.
-/
def l2PointwiseMultiplier
    (m : Lp (α := ℂ) ℂ ∞ volume) : PlaneL2 →L[ℂ] PlaneL2 :=
  LinearMap.mkContinuous (l2PointwiseMultiplierLinearMap m) ‖m‖ fun f ↦
    MeasureTheory.Lp.norm_smul_le m f

/--
%%handwave
name:
  Beurling Fourier symbol
statement:
  The Fourier symbol of the Beurling transform is
  $$
    m(\xi)=\begin{cases}
      1,&\xi=0,\\
      \overline\xi/\xi,&\xi\ne0.
    \end{cases}
  $$
-/
def beurlingFourierSymbol (ξ : ℂ) : ℂ :=
  if ξ = 0 then 1 else starRingEnd ℂ ξ / ξ

/--
%%handwave
name:
  Measurability of the Beurling multiplier
statement:
  The function $m:\mathbb C\to\mathbb C$ given by $m(0)=1$ and
  $m(\xi)=\overline\xi/\xi$ for $\xi\ne0$ is measurable.
proof:
  The quotient is continuous away from the measurable singleton $\{0\}$,
  and changing its value on that singleton preserves measurability.
-/
theorem measurable_beurlingFourierSymbol :
    Measurable beurlingFourierSymbol := by
  unfold beurlingFourierSymbol
  refine Measurable.ite (by simp)
    measurable_const ?_
  exact Complex.continuous_conj.measurable.div measurable_id

/--
%%handwave
name:
  Unit modulus of the Beurling multiplier
statement:
  For every $\xi\in\mathbb C$, the multiplier with $m(0)=1$ and
  $m(\xi)=\overline\xi/\xi$ away from zero satisfies $|m(\xi)|=1$.
proof:
  This is immediate at zero. Away from zero, conjugation preserves modulus,
  so $|\overline\xi/\xi|=|\xi|/|\xi|=1$.
-/
@[simp]
theorem norm_beurlingFourierSymbol (ξ : ℂ) :
    ‖beurlingFourierSymbol ξ‖ = 1 := by
  by_cases hξ : ξ = 0
  · simp [beurlingFourierSymbol, hξ]
  · simp [beurlingFourierSymbol, hξ]

/--
%%handwave
name:
  Essential boundedness of the Beurling symbol
statement:
  The measurable symbol $m(0)=1$ and
  $m(\xi)=\overline\xi/\xi$ for $\xi\ne0$ belongs to
  $L^\infty(\mathbb C)$ because $|m|=1$ everywhere.
-/
def beurlingFourierSymbolMemLp :
    MemLp beurlingFourierSymbol ∞ (volume : Measure ℂ) :=
  memLp_top_of_bound measurable_beurlingFourierSymbol.aestronglyMeasurable 1 <|
    ae_of_all _ fun ξ ↦ (norm_beurlingFourierSymbol ξ).le

/--
%%handwave
name:
  $L^\infty$ class of the Beurling symbol
statement:
  The Beurling symbol determines its equivalence class
  $[m]\in L^\infty(\mathbb C)$.
-/
def beurlingFourierSymbolLp : Lp (α := ℂ) ℂ ∞ volume :=
  beurlingFourierSymbolMemLp.toLp beurlingFourierSymbol

/--
%%handwave
name:
  The Beurling symbol acts isometrically on frequency-side $L^2$
statement:
  For every $u\in L^2(\mathbb C)$,
  $$
    \|m u\|_{L^2}=\|u\|_{L^2},
    \qquad
    m(0)=1,\quad m(\xi)=\frac{\overline\xi}{\xi}\quad(\xi\ne0).
  $$
proof:
  Choose the measurable representative $m$. Its modulus is identically one,
  hence $|m(\xi)u(\xi)|=|u(\xi)|$ almost everywhere. The two $L^2$ norms are
  therefore equal.
-/
theorem norm_beurlingFourierSymbolLp_smul (f : PlaneL2) :
    ‖beurlingFourierSymbolLp • f‖ = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards
      [MeasureTheory.Lp.coeFn_lpSMul (r := 2) beurlingFourierSymbolLp f,
        beurlingFourierSymbolMemLp.coeFn_toLp]
      with ξ hmul hsymbol
  change beurlingFourierSymbolLp ξ = beurlingFourierSymbol ξ at hsymbol
  rw [hmul, Pi.smul_apply', hsymbol, norm_smul,
    norm_beurlingFourierSymbol, one_mul]

/--
%%handwave
name:
  Beurling multiplier isometry on $L^2$
statement:
  Multiplication by the unit-modulus Beurling symbol defines a complex-linear
  isometry $M_m:L^2(\mathbb C)\to L^2(\mathbb C)$.
-/
def beurlingFourierMultiplierL2 : PlaneL2 →ₗᵢ[ℂ] PlaneL2 where
  toLinearMap := l2PointwiseMultiplierLinearMap beurlingFourierSymbolLp
  norm_map' := norm_beurlingFourierSymbolLp_smul

/--
%%handwave
name:
  Beurling transform as an $L^2$ isometry
statement:
  The Beurling transform on $L^2(\mathbb C)$ is the complex-linear isometry
  $$
    \mathcal S=\mathcal F^{-1}M_m\mathcal F,
    \qquad m(\xi)=\overline\xi/\xi\quad(\xi\ne0).
  $$
-/
def beurlingTransformL2Isometry : PlaneL2 →ₗᵢ[ℂ] PlaneL2 :=
  ((MeasureTheory.Lp.fourierTransformₗᵢ ℂ ℂ).symm.toLinearIsometry :
      PlaneL2 →ₗᵢ[ℂ] PlaneL2).comp
    ((beurlingFourierMultiplierL2 : PlaneL2 →ₗᵢ[ℂ] PlaneL2).comp
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℂ ℂ).toLinearIsometry :
        PlaneL2 →ₗᵢ[ℂ] PlaneL2))

/--
%%handwave
name:
  Bounded $L^2$ Beurling transform
statement:
  The $L^2$ Beurling isometry, regarded as a bounded complex-linear operator,
  is denoted by $\mathcal S:L^2(\mathbb C)\to L^2(\mathbb C)$.
-/
def beurlingTransformL2 : PlaneL2 →L[ℂ] PlaneL2 :=
  beurlingTransformL2Isometry.toContinuousLinearMap

/--
%%handwave
name:
  Fourier formula for the $L^2$ Beurling transform
statement:
  For $u\in L^2(\mathbb C)$, the Beurling transform is
  $$
    \mathcal S u=\mathcal F^{-1}\!\left(m\,\mathcal F u\right),
    \qquad
    m(0)=1,\quad m(\xi)=\frac{\overline\xi}{\xi}\quad(\xi\ne0).
  $$
proof:
  Expand the definition as inverse Fourier transform after multiplication by
  $m$ after Fourier transform.
-/
@[simp]
theorem beurlingTransformL2_apply (f : PlaneL2) :
    beurlingTransformL2 f =
      𝓕⁻ (beurlingFourierSymbolLp • 𝓕 f) := rfl

/--
%%handwave
name:
  Plancherel isometry for the Beurling transform
statement:
  For every $u\in L^2(\mathbb C)$,
  $$\|\mathcal S u\|_{L^2}=\|u\|_{L^2}.$$
proof:
  The Fourier transform and its inverse are isometries by Plancherel, while
  the intervening multiplier has modulus one everywhere.
-/
@[simp]
theorem norm_beurlingTransformL2_apply (f : PlaneL2) :
    ‖beurlingTransformL2 f‖ = ‖f‖ := by
  exact beurlingTransformL2Isometry.norm_map f

/--
%%handwave
name:
  Extended $L^2$ seminorm isometry for the Beurling transform
statement:
  For every $u\in L^2(\mathbb C)$, the extended $L^2$ seminorms of $u$ and
  its Beurling transform agree:
  $$
    \|\mathcal S u\|_{L^2}=\|u\|_{L^2}
    \qquad\text{in }[0,\infty].
  $$
proof:
  Rewrite each extended seminorm as the extended norm of the corresponding
  $L^2$ class and apply the Plancherel isometry.
-/
@[simp]
theorem eLpNorm_two_beurlingTransformL2_apply (f : PlaneL2) :
    eLpNorm (beurlingTransformL2 f : ℂ → ℂ) 2 volume =
      eLpNorm (f : ℂ → ℂ) 2 volume := by
  rw [← Lp.enorm_def, ← Lp.enorm_def]
  simpa only [ofReal_norm] using
    congrArg ENNReal.ofReal (norm_beurlingTransformL2_apply f)

/--
%%handwave
name:
  Operator-norm bound for the $L^2$ Beurling transform
statement:
  The Beurling transform on $L^2(\mathbb C)$ has operator norm at most $1$.
proof:
  It is the bounded linear map underlying a linear isometry.
-/
theorem norm_beurlingTransformL2_le_one :
    ‖beurlingTransformL2‖ ≤ 1 := by
  exact beurlingTransformL2Isometry.norm_toContinuousLinearMap_le

/--
%%handwave
name:
  Beurling transform of an antiholomorphic Wirtinger derivative
statement:
  For every complex-valued Schwartz function $f$ on $\mathbb C$,
  $$
    \mathcal S(\partial_{\bar z}f)=\partial_zf
  $$
  as elements of $L^2(\mathbb C)$.
proof:
  Apply the unitary Fourier transform.  The multiplier
  $m(\xi)=\overline\xi/\xi$ converts
  $\pi i\xi\,\widehat f(\xi)$ into
  $\pi i\overline\xi\,\widehat f(\xi)$ away from zero.  Both sides vanish at
  zero, so the identity holds pointwise in frequency and hence in $L^2$.
-/
theorem beurlingTransformL2_schwartzWirtingerDBar
    (f : 𝓢(ℂ, ℂ)) :
    beurlingTransformL2 ((schwartzWirtingerDBar f).toLp 2) =
      (schwartzWirtingerZ f).toLp 2 := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ ℂ ℂ).injective
  change 𝓕 (𝓕⁻ (beurlingFourierSymbolLp •
      𝓕 ((schwartzWirtingerDBar f).toLp 2))) =
    𝓕 ((schwartzWirtingerZ f).toLp 2)
  rw [fourier_fourierInv_eq,
    SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards
      [MeasureTheory.Lp.coeFn_lpSMul
        (r := 2) beurlingFourierSymbolLp
          ((𝓕 (schwartzWirtingerDBar f)).toLp 2),
        beurlingFourierSymbolMemLp.coeFn_toLp,
        (𝓕 (schwartzWirtingerDBar f)).coeFn_toLp 2,
        (𝓕 (schwartzWirtingerZ f)).coeFn_toLp 2]
      with ξ hmul hsymbol hdbar hz
  change beurlingFourierSymbolLp ξ = beurlingFourierSymbol ξ at hsymbol
  rw [hmul, Pi.smul_apply', hsymbol, hdbar, hz,
    fourier_schwartzWirtingerDBar_apply,
    fourier_schwartzWirtingerZ_apply]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [beurlingFourierSymbol, if_neg hξ]
    simp only [smul_eq_mul]
    field_simp

end

end Quasiconformal

end JJMath
