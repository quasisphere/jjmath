import JJMath.Quasiconformal.BeurlingLp

/-!
# Bilinear symmetry of the Beurling transform

This file develops the Fourier-side symmetry needed to pass the strong
Beurling estimate from exponents below two to their Hölder conjugates above
two.  The relevant pairing is the complex-bilinear pairing
`(f, g) ↦ ∫ z, f z * g z`, rather than the sesquilinear Hilbert pairing.
-/

namespace JJMath

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Complex-bilinear pairing on planar $L^2$
statement:
  For $f,g\in L^2(\mathbb C)$, define the continuous complex-bilinear
  pairing
  $$
    \mathopen\langle f,g\mathclose\rangle_{\mathrm{bil}}
      =\int_{\mathbb C} f(z)g(z)\,dz.
  $$
-/
def planeL2BilinearPairing : PlaneL2 →L[ℂ] PlaneL2 →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2

/--
%%handwave
name:
  Integral formula for the planar bilinear pairing
statement:
  For $f,g\in L^2(\mathbb C)$, the planar complex-bilinear pairing is
  $$
    \mathopen\langle f,g\mathclose\rangle_{\mathrm{bil}}
      =\int_{\mathbb C} f(z)g(z)\,dz.
  $$
proof:
  This is the integral representation of the continuous $L^2$ Hölder
  pairing.
-/
theorem planeL2BilinearPairing_eq_integral (f g : PlaneL2) :
    planeL2BilinearPairing f g = ∫ z, f z * g z := by
  exact (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral f g

/--
%%handwave
name:
  Bilinear pairing of Schwartz $L^2$ classes
statement:
  If $f,g:\mathbb C\to\mathbb C$ are Schwartz functions, then their
  $L^2$ classes satisfy
  $$
    \mathopen\langle [f],[g]\mathclose\rangle_{\mathrm{bil}}
      =\int_{\mathbb C}f(z)g(z)\,dz.
  $$
proof:
  The canonical $L^2$ representatives agree almost everywhere with the
  original Schwartz functions.
-/
theorem planeL2BilinearPairing_schwartz_toLp (f g : 𝓢(ℂ, ℂ)) :
    planeL2BilinearPairing (f.toLp 2) (g.toLp 2) =
      ∫ z, f z * g z := by
  rw [planeL2BilinearPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2, g.coeFn_toLp 2] with z hf hg
  exact congrArg₂ (· * ·) hf hg

/--
%%handwave
name:
  Fourier transform is self-transpose on planar $L^2$
statement:
  For $f,g\in L^2(\mathbb C)$,
  $$
    \mathopen\langle \mathcal Ff,g\mathclose\rangle_{\mathrm{bil}}
      =\mathopen\langle f,\mathcal Fg\mathclose\rangle_{\mathrm{bil}}.
  $$
proof:
  The identity holds for Schwartz functions by Fubini's theorem. Both sides
  depend continuously on the two $L^2$ arguments, so density of Schwartz
  functions proves the general case.
-/
theorem planeL2BilinearPairing_fourier_left (f g : PlaneL2) :
    planeL2BilinearPairing (𝓕 f) g =
      planeL2BilinearPairing f (𝓕 g) := by
  refine DenseRange.induction_on₂
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) ?_ ?_ f g
  · exact isClosed_eq
      (planeL2BilinearPairing.continuous₂.comp₂
        (continuous_fourier.comp continuous_fst) continuous_snd)
      (planeL2BilinearPairing.continuous₂.comp₂
        continuous_fst (continuous_fourier.comp continuous_snd))
  · intro F G
    simp only [SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
      planeL2BilinearPairing_schwartz_toLp,
      planeL2BilinearPairing_schwartz_toLp]
    exact SchwartzMap.integral_fourier_mul_eq F G

/--
%%handwave
name:
  Inverse Fourier transform is self-transpose on planar $L^2$
statement:
  For $f,g\in L^2(\mathbb C)$,
  $$
    \mathopen\langle \mathcal F^{-1}f,g\mathclose\rangle_{\mathrm{bil}}
      =\mathopen\langle f,\mathcal F^{-1}g\mathclose\rangle_{\mathrm{bil}}.
  $$
proof:
  The identity holds for Schwartz functions by Fourier inversion and
  Fubini's theorem. Continuity of the pairing and density of Schwartz
  functions extend it to all of $L^2$.
-/
theorem planeL2BilinearPairing_fourierInv_left (f g : PlaneL2) :
    planeL2BilinearPairing (𝓕⁻ f) g =
      planeL2BilinearPairing f (𝓕⁻ g) := by
  refine DenseRange.induction_on₂
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) ?_ ?_ f g
  · exact isClosed_eq
      (planeL2BilinearPairing.continuous₂.comp₂
        (continuous_fourierInv.comp continuous_fst) continuous_snd)
      (planeL2BilinearPairing.continuous₂.comp₂
        continuous_fst (continuous_fourierInv.comp continuous_snd))
  · intro F G
    simp only [SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourierInv_eq,
      planeL2BilinearPairing_schwartz_toLp,
      planeL2BilinearPairing_schwartz_toLp]
    exact SchwartzMap.integral_fourierInv_mul_eq F G

/--
%%handwave
name:
  Reflection on planar $L^2$
statement:
  Reflection through the origin defines the complex-linear isometry
  $$
    R:L^2(\mathbb C)\longrightarrow L^2(\mathbb C),
    \qquad (Rf)(z)=f(-z).
  $$
-/
def planeL2Reflection : PlaneL2 →ₗᵢ[ℂ] PlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℂ ↦ -z)
    (Measure.measurePreserving_neg volume)

/--
%%handwave
name:
  Pointwise representative of planar reflection
statement:
  For $f\in L^2(\mathbb C)$, the reflected class has representative
  $(Rf)(z)=f(-z)$ almost everywhere.
proof:
  This is the defining representative of composition by the
  measure-preserving map $z\mapsto-z$.
-/
theorem planeL2Reflection_coeFn (f : PlaneL2) :
    (planeL2Reflection f : ℂ → ℂ) =ᵐ[volume] fun z ↦ f (-z) := by
  exact Lp.coeFn_compMeasurePreserving f
    (Measure.measurePreserving_neg volume)

/--
%%handwave
name:
  Reflection is an involution on planar $L^2$
statement:
  For every $f\in L^2(\mathbb C)$, reflection through the origin satisfies
  $R(Rf)=f$.
proof:
  The map $z\mapsto-z$ preserves Lebesgue measure and applying it twice is
  the identity.
-/
@[simp]
theorem planeL2Reflection_involutive (f : PlaneL2) :
    planeL2Reflection (planeL2Reflection f) = f := by
  apply Lp.ext
  have hreflect := planeL2Reflection_coeFn (planeL2Reflection f)
  have hreflect' :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      (planeL2Reflection_coeFn f)
  filter_upwards [hreflect, hreflect'] with z hz hz'
  simpa using hz.trans hz'

/--
%%handwave
name:
  Inverse Fourier transform as reflected Fourier transform on $L^2$
statement:
  For every $f\in L^2(\mathbb C)$,
  $$
    \mathcal F^{-1}f=R(\mathcal Ff),
    \qquad (Rh)(\xi)=h(-\xi).
  $$
proof:
  This is the defining relation on Schwartz functions. Both sides are
  continuous on $L^2$, so density extends it to every square-integrable
  function.
-/
theorem planeL2Reflection_fourier_eq_fourierInv (f : PlaneL2) :
    planeL2Reflection (𝓕 f) = 𝓕⁻ f := by
  refine DenseRange.induction_on
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f ?_ ?_
  · exact isClosed_eq
      (planeL2Reflection.continuous.comp continuous_fourier)
      continuous_fourierInv
  · intro F
    simp only [SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourierInv_eq]
    apply Lp.ext
    have hfourierNeg :=
      (Measure.measurePreserving_neg (volume : Measure ℂ)).quasiMeasurePreserving.ae_eq
        ((𝓕 F : 𝓢(ℂ, ℂ)).coeFn_toLp 2)
    filter_upwards [planeL2Reflection_coeFn
        ((𝓕 F : 𝓢(ℂ, ℂ)).toLp 2),
      hfourierNeg,
      (𝓕⁻ F : 𝓢(ℂ, ℂ)).coeFn_toLp 2] with z hreflect hfourier hfourierInv
    have hfourier' :
        ((𝓕 F : 𝓢(ℂ, ℂ)).toLp 2 : PlaneL2) (-z) =
          (𝓕 F : 𝓢(ℂ, ℂ)) (-z) := by
      simpa only [Function.comp_apply] using hfourier
    rw [hreflect, hfourier', hfourierInv]
    simpa only [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe] using
      (Real.fourierInv_eq_fourier_neg (F : ℂ → ℂ) z).symm

/--
%%handwave
name:
  Evenness of the Beurling symbol
statement:
  The Beurling multiplier
  $m(0)=1$ and $m(\xi)=\overline\xi/\xi$ for $\xi\ne0$ is even:
  $$m(-\xi)=m(\xi)$$
  for every $\xi\in\mathbb C$.
proof:
  Away from zero, the two minus signs in
  $\overline{-\xi}/(-\xi)$ cancel; the assertion at zero is immediate.
-/
@[simp]
theorem beurlingFourierSymbol_neg (ξ : ℂ) :
    beurlingFourierSymbol (-ξ) = beurlingFourierSymbol ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp [beurlingFourierSymbol, hξ]

/--
%%handwave
name:
  Beurling multiplier commutes with reflection
statement:
  If $M_m$ is multiplication on $L^2(\mathbb C)$ by the Beurling symbol
  and $(Rf)(\xi)=f(-\xi)$, then
  $$R(M_mf)=M_m(Rf)$$
  for every $f\in L^2(\mathbb C)$.
proof:
  Both sides have pointwise representative $m(\xi)f(-\xi)$ because the
  Beurling symbol is even.
-/
theorem planeL2Reflection_beurlingFourierSymbolLp_smul (f : PlaneL2) :
    planeL2Reflection (beurlingFourierSymbolLp • f) =
      beurlingFourierSymbolLp • planeL2Reflection f := by
  apply Lp.ext
  let hneg := Measure.measurePreserving_neg (volume : Measure ℂ)
  have hsmulNeg := hneg.quasiMeasurePreserving.ae_eq
    (Lp.coeFn_lpSMul (r := 2) beurlingFourierSymbolLp f)
  have hsymbolNeg := hneg.quasiMeasurePreserving.ae_eq
    beurlingFourierSymbolMemLp.coeFn_toLp
  filter_upwards [planeL2Reflection_coeFn
      (beurlingFourierSymbolLp • f),
    hsmulNeg, hsymbolNeg,
    Lp.coeFn_lpSMul (r := 2) beurlingFourierSymbolLp
      (planeL2Reflection f),
    beurlingFourierSymbolMemLp.coeFn_toLp,
    planeL2Reflection_coeFn f]
      with z hreflectLeft hsmulLeft hsymbolLeft hsmulRight hsymbolRight
        hreflectRight
  have hsmulLeft' :
      (beurlingFourierSymbolLp • f : PlaneL2) (-z) =
        beurlingFourierSymbolLp (-z) • f (-z) := by
    simpa only [Function.comp_apply] using hsmulLeft
  have hsymbolLeft' :
      beurlingFourierSymbolLp (-z) = beurlingFourierSymbol (-z) := by
    simpa only [Function.comp_apply] using hsymbolLeft
  change beurlingFourierSymbolLp z = beurlingFourierSymbol z at hsymbolRight
  rw [hreflectLeft, hsmulLeft', hsymbolLeft', beurlingFourierSymbol_neg,
    hsmulRight, Pi.smul_apply', hsymbolRight, hreflectRight]

/--
%%handwave
name:
  Reflected inverse Fourier transform
statement:
  For every $f\in L^2(\mathbb C)$,
  $$R(\mathcal F^{-1}f)=\mathcal Ff.$$
proof:
  Substitute $\mathcal F^{-1}f=R(\mathcal Ff)$ and use $R^2=1$.
-/
theorem planeL2Reflection_fourierInv_eq_fourier (f : PlaneL2) :
    planeL2Reflection (𝓕⁻ f) = 𝓕 f := by
  rw [← planeL2Reflection_fourier_eq_fourierInv,
    planeL2Reflection_involutive]

/--
%%handwave
name:
  Square of the Fourier transform on planar $L^2$
statement:
  For every $f\in L^2(\mathbb C)$,
  $$\mathcal F(\mathcal Ff)=Rf,$$
  where $(Rf)(z)=f(-z)$.
proof:
  Apply the identity $\mathcal F^{-1}=R\mathcal F$ to $\mathcal Ff$, use
  Fourier inversion, and then apply the involution $R$.
-/
theorem fourier_fourier_eq_planeL2Reflection (f : PlaneL2) :
    𝓕 (𝓕 f) = planeL2Reflection f := by
  have h : planeL2Reflection (𝓕 (𝓕 f)) = f := by
    simpa using planeL2Reflection_fourier_eq_fourierInv (𝓕 f)
  calc
    𝓕 (𝓕 f) = planeL2Reflection (planeL2Reflection (𝓕 (𝓕 f))) :=
      (planeL2Reflection_involutive _).symm
    _ = planeL2Reflection f := congrArg planeL2Reflection h

/--
%%handwave
name:
  Fourier transform as inverse transform after reflection
statement:
  For every $f\in L^2(\mathbb C)$,
  $$\mathcal Ff=\mathcal F^{-1}(Rf).$$
proof:
  Apply the injective Fourier transform. The two images agree by the formula
  $\mathcal F^2=R$ and Fourier inversion.
-/
theorem fourier_eq_fourierInv_planeL2Reflection (f : PlaneL2) :
    𝓕 f = 𝓕⁻ (planeL2Reflection f) := by
  apply (Lp.fourierTransformₗᵢ ℂ ℂ).injective
  change 𝓕 (𝓕 f) = 𝓕 (𝓕⁻ (planeL2Reflection f))
  rw [fourier_fourier_eq_planeL2Reflection, fourier_fourierInv_eq]

/--
%%handwave
name:
  Two Fourier formulas for the Beurling transform agree
statement:
  For every $f\in L^2(\mathbb C)$,
  $$
    \mathcal F\bigl(m\,\mathcal F^{-1}f\bigr)
      =\mathcal F^{-1}\bigl(m\,\mathcal Ff\bigr),
  $$
  where $m(\xi)=\overline\xi/\xi$ away from zero.
proof:
  Replace the outer Fourier transform by inverse Fourier transform after
  reflection, commute the even multiplier with reflection, and use
  $R\mathcal F^{-1}=\mathcal F$.
-/
theorem fourier_beurlingFourierSymbolLp_smul_fourierInv (f : PlaneL2) :
    𝓕 (beurlingFourierSymbolLp • 𝓕⁻ f) =
      𝓕⁻ (beurlingFourierSymbolLp • 𝓕 f) := by
  calc
    𝓕 (beurlingFourierSymbolLp • 𝓕⁻ f) =
        𝓕⁻ (planeL2Reflection
          (beurlingFourierSymbolLp • 𝓕⁻ f)) :=
      fourier_eq_fourierInv_planeL2Reflection _
    _ = 𝓕⁻ (beurlingFourierSymbolLp •
        planeL2Reflection (𝓕⁻ f)) := by
      rw [planeL2Reflection_beurlingFourierSymbolLp_smul]
    _ = 𝓕⁻ (beurlingFourierSymbolLp • 𝓕 f) := by
      rw [planeL2Reflection_fourierInv_eq_fourier]

/--
%%handwave
name:
  Beurling multiplier is symmetric for the bilinear pairing
statement:
  For all $f,g\in L^2(\mathbb C)$, multiplication by the Beurling symbol
  satisfies
  $$
    \mathopen\langle mf,g\mathclose\rangle_{\mathrm{bil}}
      =\mathopen\langle f,mg\mathclose\rangle_{\mathrm{bil}}.
  $$
proof:
  Both sides are the integral of the same pointwise product
  $m(\xi)f(\xi)g(\xi)$.
-/
theorem planeL2BilinearPairing_beurlingFourierSymbolLp_smul_left
    (f g : PlaneL2) :
    planeL2BilinearPairing (beurlingFourierSymbolLp • f) g =
      planeL2BilinearPairing f (beurlingFourierSymbolLp • g) := by
  rw [planeL2BilinearPairing_eq_integral,
    planeL2BilinearPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := 2) beurlingFourierSymbolLp f,
    Lp.coeFn_lpSMul (r := 2) beurlingFourierSymbolLp g]
      with z hf hg
  rw [hf, hg, Pi.smul_apply', Pi.smul_apply']
  change (beurlingFourierSymbolLp z * f z) * g z =
    f z * (beurlingFourierSymbolLp z * g z)
  ring

/--
%%handwave
name:
  Bilinear symmetry of the planar $L^2$ Beurling transform
statement:
  For all $f,g\in L^2(\mathbb C)$,
  $$
    \int_{\mathbb C}(\mathcal Sf)(z)g(z)\,dz
      =\int_{\mathbb C}f(z)(\mathcal Sg)(z)\,dz.
  $$
proof:
  Move the inverse Fourier transform, the multiplier, and then the Fourier
  transform across the bilinear pairing. The resulting transpose is
  $\mathcal F M_m\mathcal F^{-1}$, which equals
  $\mathcal F^{-1}M_m\mathcal F$ because the symbol $m$ is even.
-/
theorem planeL2BilinearPairing_beurlingTransformL2_left (f g : PlaneL2) :
    planeL2BilinearPairing (beurlingTransformL2 f) g =
      planeL2BilinearPairing f (beurlingTransformL2 g) := by
  rw [beurlingTransformL2_apply, beurlingTransformL2_apply]
  calc
    planeL2BilinearPairing
        (𝓕⁻ (beurlingFourierSymbolLp • 𝓕 f)) g =
        planeL2BilinearPairing (beurlingFourierSymbolLp • 𝓕 f)
          (𝓕⁻ g) :=
      planeL2BilinearPairing_fourierInv_left _ _
    _ = planeL2BilinearPairing (𝓕 f)
        (beurlingFourierSymbolLp • 𝓕⁻ g) :=
      planeL2BilinearPairing_beurlingFourierSymbolLp_smul_left _ _
    _ = planeL2BilinearPairing f
        (𝓕 (beurlingFourierSymbolLp • 𝓕⁻ g)) :=
      planeL2BilinearPairing_fourier_left _ _
    _ = planeL2BilinearPairing f
        (𝓕⁻ (beurlingFourierSymbolLp • 𝓕 g)) := by
      rw [fourier_beurlingFourierSymbolLp_smul_fourierInv]

/--
%%handwave
name:
  Bilinear symmetry on integrable square-integrable inputs
statement:
  Let $F,G\in L^1(\mathbb C)$ have square-integrable representatives. Then
  the weak-$L^1$ Beurling transform satisfies
  $$
    \int_{\mathbb C}(\mathcal SF)(z)G(z)\,dz
      =\int_{\mathbb C}F(z)(\mathcal SG)(z)\,dz.
  $$
proof:
  On $L^1\cap L^2$ the weak extension agrees almost everywhere with the
  Fourier-multiplier transform. Replace both transforms by their $L^2$
  versions and apply bilinear symmetry on $L^2$.
-/
theorem integral_beurlingTransformL1_mul_eq_integral_mul_beurlingTransformL1
    (F G : ℂ →₁[volume] ℂ)
    (hF₂ : MemLp (F : ℂ → ℂ) 2 volume)
    (hG₂ : MemLp (G : ℂ → ℂ) 2 volume) :
    (∫ z, (beurlingTransformL1 F : ℂ → ℂ) z * G z) =
      ∫ z, F z * (beurlingTransformL1 G : ℂ → ℂ) z := by
  let F₂ : PlaneL2 := hF₂.toLp (F : ℂ → ℂ)
  let G₂ : PlaneL2 := hG₂.toLp (G : ℂ → ℂ)
  let hF₁ : MemLp (F : ℂ → ℂ) 1 volume :=
    memLp_one_iff_integrable.mpr (L1.integrable_coeFn F)
  let hG₁ : MemLp (G : ℂ → ℂ) 1 volume :=
    memLp_one_iff_integrable.mpr (L1.integrable_coeFn G)
  have hFclass : hF₁.toLp (F : ℂ → ℂ) = F := Lp.toLp_coeFn F hF₁
  have hGclass : hG₁.toLp (G : ℂ → ℂ) = G := Lp.toLp_coeFn G hG₁
  have hFcompat : (beurlingTransformL1 F : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL2 F₂ : ℂ → ℂ) := by
    have h := beurlingTransformL1_ae_eq_beurlingTransformL2
      (F : ℂ → ℂ) (L1.integrable_coeFn F) hF₂
    dsimp only at h
    rw [hFclass] at h
    exact h
  have hGcompat : (beurlingTransformL1 G : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL2 G₂ : ℂ → ℂ) := by
    have h := beurlingTransformL1_ae_eq_beurlingTransformL2
      (G : ℂ → ℂ) (L1.integrable_coeFn G) hG₂
    dsimp only at h
    rw [hGclass] at h
    exact h
  calc
    (∫ z, (beurlingTransformL1 F : ℂ → ℂ) z * G z) =
        ∫ z, (beurlingTransformL2 F₂ : ℂ → ℂ) z * G₂ z := by
      apply integral_congr_ae
      exact hFcompat.mul hG₂.coeFn_toLp.symm
    _ = planeL2BilinearPairing (beurlingTransformL2 F₂) G₂ :=
      (planeL2BilinearPairing_eq_integral _ _).symm
    _ = planeL2BilinearPairing F₂ (beurlingTransformL2 G₂) :=
      planeL2BilinearPairing_beurlingTransformL2_left _ _
    _ = ∫ z, F₂ z * (beurlingTransformL2 G₂ : ℂ → ℂ) z :=
      planeL2BilinearPairing_eq_integral _ _
    _ = ∫ z, F z * (beurlingTransformL1 G : ℂ → ℂ) z := by
      apply integral_congr_ae
      exact hF₂.coeFn_toLp.mul hGcompat.symm

/--
%%handwave
name:
  Finite-support simple functions belong to planar $L^2$
statement:
  Let $0<p<\infty$. If $F$ is a finite-support $L^p$ simple function and
  $F_1$ is the same function regarded as an $L^1$ class, then the
  representative of $F_1$ belongs to $L^2$.
proof:
  A finite-support simple function is integrable. For simple functions,
  integrability is equivalent to membership in every finite positive
  $L^r$ space, in particular $L^2$; the $L^1$ representative agrees almost
  everywhere with the original simple function.
-/
theorem memLp_two_simpleFuncToL1LinearMap
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ENNReal) (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (F : Lp.simpleFunc ℂ p μ) :
    MemLp ((simpleFuncToL1LinearMap μ p hp0 hptop F : α →₁[μ] ℂ) : α → ℂ)
      2 μ := by
  have hF₂ : MemLp (Lp.simpleFunc.toSimpleFunc F : α → ℂ) 2 μ :=
    (SimpleFunc.memLp_iff_integrable (p := (2 : ENNReal)) (by norm_num)
      (by simp)).mpr (integrable_simpleFunc_toSimpleFunc hp0 hptop F)
  exact hF₂.ae_eq
    (integrable_simpleFunc_toSimpleFunc hp0 hptop F).coeFn_toL1.symm

end

end Quasiconformal

end JJMath
