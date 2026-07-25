import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import JJMath.Hyperbolic.RealProjective
import JJMath.Hyperbolic.Schwarzian.Wirtinger

/-!
# Future forward direction to singular hyperbolic metrics

This module keeps the projective-to-singular-hyperbolic target separate from
the hyperbolic-to-projective converse path.
-/

namespace JJMath

open scoped MatrixGroups Topology Manifold

noncomputable section

/--
For maps out of the complex plane, complex `C^∞` regularity at a point gives
complex analyticity at that point.  We use the Cauchy-integral theorem through
the fact that the `C^∞` germ is complex differentiable on a neighborhood.

%%handwave
name:
  Complex smoothness implies analyticity
statement:
  Let \(f : \mathbb C \to \mathbb C\). If \(f\) is complex \(C^\infty\) on a neighborhood of \(z\), then \(f\) is complex analytic at \(z\).
proof:
  Complex smoothness on a neighborhood implies complex differentiability there. The Cauchy integral theorem then makes the germ analytic.
-/
theorem analyticAt_of_contDiffAt_top_complex {f : ℂ → ℂ} {z : ℂ}
    (h : ContDiffAt ℂ ⊤ f z) :
    AnalyticAt ℂ f z := by
  let s : Set ℂ := {w : ℂ | ContDiffAt ℂ ⊤ f w}
  have hs : s ∈ 𝓝 z := h.eventually (by simp)
  have hd : DifferentiableOn ℂ f s := by
    intro w hw
    have hw' : ContDiffAt ℂ ⊤ f w := by
      simpa [s] using hw
    exact (hw'.differentiableAt (by simp)).differentiableWithinAt
  exact hd.analyticAt hs

/--
For a real-valued `C^2` function on the complex plane, the concrete
Frechet-Wirtinger mixed derivative is one quarter of the Laplacian.

%%handwave
name:
  The mixed Wirtinger derivative is one quarter of the Laplacian
statement:
  If \(u : \mathbb C \to \mathbb R\) is \(C^2\) at \(z\), then \(\bar\partial\partial u(z)=\tfrac14\Delta u(z)\), with \(u\) and \(\Delta u\) complexified on the two sides.
proof:
  Expand both Wirtinger operators in terms of the real Fréchet derivative. Symmetry of the second derivative cancels the mixed terms, while the two diagonal terms are exactly the Euclidean Laplacian.
-/
theorem frechetDBar_frechetDZ_complex_ofReal_eq_laplacian
    {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    frechetDBarValue (fun w ↦ frechetDZValue (fun t ↦ (u t : ℂ)) w) z =
      (1 / 4 : ℂ) * (Laplacian.laplacian u z : ℂ) := by
  let U : ℂ → ℂ := fun t ↦ (u t : ℂ)
  have huc2 : ContDiffAt ℝ 2 U z := by
    have hOf : ContDiff ℝ 2 (Complex.ofRealCLM : ℝ → ℂ) :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff (𝕜 := ℝ) (n := 2)
    exact hOf.contDiffAt.comp z hu
  have hF : DifferentiableAt ℝ (fderiv ℝ U) z :=
    (huc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ
      (fun w : ℂ ↦ fderiv ℝ U w (1 : ℂ)) z :=
    hF.clm_apply (differentiableAt_const (1 : ℂ))
  have hI : DifferentiableAt ℝ
      (fun w : ℂ ↦ fderiv ℝ U w Complex.I) z :=
    hF.clm_apply (differentiableAt_const Complex.I)
  have hInner : DifferentiableAt ℝ
      (fun w : ℂ ↦
        fderiv ℝ U w (1 : ℂ) -
          Complex.I * fderiv ℝ U w Complex.I) z :=
    h1.sub (hI.const_mul Complex.I)
  have hsymm : IsSymmSndFDerivAt ℝ U z :=
    huc2.isSymmSndFDerivAt (by simp)
  have hlapC : Laplacian.laplacian U z =
      (Laplacian.laplacian u z : ℂ) := by
    simpa [U] using hu.laplacian_CLM_comp_left (l := Complex.ofRealCLM)
  change frechetDBarValue (fun w ↦ frechetDZValue U w) z =
    (1 / 4 : ℂ) * (Laplacian.laplacian u z : ℂ)
  simp only [frechetDBarValue, frechetDZValue]
  have hfd_outer :
      fderiv ℝ (fun w : ℂ ↦
        (1 / 2 : ℂ) *
          (fderiv ℝ U w (1 : ℂ) -
            Complex.I * fderiv ℝ U w Complex.I)) z =
        (1 / 2 : ℂ) • fderiv ℝ (fun w : ℂ ↦
          fderiv ℝ U w (1 : ℂ) -
            Complex.I * fderiv ℝ U w Complex.I) z := by
    simpa using fderiv_const_mul (𝕜 := ℝ) (a := fun w : ℂ ↦
      fderiv ℝ U w (1 : ℂ) -
        Complex.I * fderiv ℝ U w Complex.I)
      (x := z) hInner (1 / 2 : ℂ)
  rw [hfd_outer]
  rw [fderiv_fun_sub h1 (hI.const_mul Complex.I)]
  have hfd_I_mul :
      fderiv ℝ
          (fun y : ℂ => Complex.I * (fderiv ℝ U y) Complex.I) z =
        Complex.I • fderiv ℝ
          (fun y : ℂ => (fderiv ℝ U y) Complex.I) z := by
    simpa using fderiv_const_mul (𝕜 := ℝ)
      (a := fun y : ℂ ↦ fderiv ℝ U y Complex.I)
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

/-- Frechet-Wirtinger `∂bar` only depends on the germ of a function.

%%handwave
name:
  The antiholomorphic derivative depends only on the germ
statement:
  If two functions \(f,g : \mathbb C \to \mathbb C\) agree on a neighborhood of \(z\), then \(\bar\partial f(z)=\bar\partial g(z)\).
proof:
  Functions with the same germ have the same real Fréchet derivative at the base point, so their antiholomorphic Wirtinger components agree.
-/
theorem frechetDBarValue_congr_of_eventuallyEq
    {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) :
    frechetDBarValue f z = frechetDBarValue g z := by
  rw [frechetDBarValue, frechetDBarValue]
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h]

/--
For a holomorphic branch, the `∂z` derivative of the complexified
height-logarithm is `-i F' / (2 Im F)`.

%%handwave
name:
  Holomorphic derivative of the logarithmic height
statement:
  If \(F\) is holomorphic at \(z\), with \(F'(z)=a\) and \(\operatorname{Im}F(z)\ne0\), then \(\partial\log(\operatorname{Im}F)(z)=-ia/(2\operatorname{Im}F(z))\), after complexifying the real logarithm.
proof:
  Apply the real Fréchet chain rule to the logarithm and use \(\partial\operatorname{Im}F=-iF'/2\) for a holomorphic function.
-/
theorem frechetDZValue_complex_ofReal_log_im_of_hasDerivAt
    {F : ℂ → ℂ} {z F' : ℂ}
    (hF : HasDerivAt F F' z) (him : (F z).im ≠ 0) :
    frechetDZValue (fun w : ℂ ↦ (Real.log (F w).im : ℂ)) z =
      -Complex.I * F' / (2 * (((F z).im : ℝ) : ℂ)) := by
  let yR : ℂ → ℝ := fun w ↦ (F w).im
  let yC : ℂ → ℂ := fun w ↦ (((F w).im : ℝ) : ℂ)
  have hyRdiff : DifferentiableAt ℝ yR z := by
    let L : ℂ →L[ℝ] ℂ := F' • (1 : ℂ →L[ℝ] ℂ)
    have hFR : HasFDerivAt F L z := by
      simpa [L] using hF.complexToReal_fderiv
    exact ((Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp z hFR).differentiableAt
  let L : ℂ →L[ℝ] ℝ := fderiv ℝ yR z
  have hyRF : HasFDerivAt yR L z := by
    simpa [L] using hyRdiff.hasFDerivAt
  have hyCF : HasFDerivAt yC (Complex.ofRealCLM.comp L) z := by
    simpa [yC, yR, L, Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z hyRF)
  have hlog : HasDerivAt Real.log (yR z)⁻¹ (yR z) :=
    Real.hasDerivAt_log (by simpa [yR] using him)
  have hlogF : HasFDerivAt (fun w : ℂ ↦ Real.log (yR w))
      ((yR z)⁻¹ • L) z := by
    simpa only [Function.comp_apply] using hlog.comp_hasFDerivAt z hyRF
  have hlogCF : HasFDerivAt (fun w : ℂ ↦ (Real.log (yR w) : ℂ))
      (Complex.ofRealCLM.comp ((yR z)⁻¹ • L)) z := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp z hlogF)
  have hchain :
      frechetDZValue (fun w : ℂ ↦ (Real.log (yR w) : ℂ)) z =
        (((yR z : ℝ) : ℂ)⁻¹) * frechetDZValue yC z := by
    repeat rw [frechetDZValue]
    rw [hlogCF.fderiv, hyCF.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      Complex.ofRealCLM_apply]
    simp [smul_eq_mul]
    ring_nf
  have hyDZ :
      frechetDZValue yC z = -Complex.I * F' / 2 := by
    simpa [yC] using frechetDZValue_complex_ofReal_im_of_hasDerivAt_general hF
  rw [show (fun w : ℂ ↦ (Real.log (F w).im : ℂ)) =
      (fun w : ℂ ↦ (Real.log (yR w) : ℂ)) by
        rfl]
  rw [hchain, hyDZ]
  simp [yR, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/--
For a holomorphic local branch, the mixed Frechet-Wirtinger derivative of the
complexified height-logarithm is the negative pullback hyperbolic density,
written with the factor of `1 / 4` from the Laplacian convention.

%%handwave
name:
  Mixed derivative of the logarithmic height
statement:
  Suppose \(F\) is holomorphic near \(z\), its derivative there is the holomorphic function \(F_1\), and \(\operatorname{Im}F(z)\ne0\). Then \(\bar\partial\partial\log(\operatorname{Im}F)(z)=-|F_1(z)|^2/(4(\operatorname{Im}F(z))^2)\).
proof:
  Differentiate \(\partial\log(\operatorname{Im}F)=-iF_1/(2\operatorname{Im}F)\). Holomorphicity gives \(\bar\partial F_1=0\), while \(\bar\partial\operatorname{Im}F=i\overline{F_1}/2\); the quotient rule yields the formula.
-/
theorem frechetDBar_frechetDZ_complex_ofReal_log_im_of_hasDerivAt
    {F F₁ : ℂ → ℂ} {z F₁' : ℂ}
    (hF_ev : ∀ᶠ w in 𝓝 z, HasDerivAt F (F₁ w) w)
    (hFz : HasDerivAt F (F₁ z) z)
    (hF₁z : HasDerivAt F₁ F₁' z)
    (him : (F z).im ≠ 0) :
    frechetDBarValue
        (fun w ↦ frechetDZValue (fun t ↦ (Real.log (F t).im : ℂ)) w) z =
      - (Complex.normSq (F₁ z) : ℂ) /
        (4 * ((((F z).im : ℝ) : ℂ) ^ 2)) := by
  let Y : ℂ → ℂ := fun w ↦ (((F w).im : ℝ) : ℂ)
  have him_ev : ∀ᶠ w in 𝓝 z, (F w).im ≠ 0 := by
    have hcont : ContinuousAt (fun w : ℂ ↦ (F w).im) z :=
      Complex.continuous_im.continuousAt.comp hFz.continuousAt
    exact hcont.eventually_ne him
  have hEq :
      (fun w ↦ frechetDZValue (fun t ↦ (Real.log (F t).im : ℂ)) w) =ᶠ[𝓝 z]
        (fun w ↦ -Complex.I * F₁ w / (2 * Y w)) := by
    filter_upwards [hF_ev, him_ev] with w hFw himw
    simpa [Y] using
      frechetDZValue_complex_ofReal_log_im_of_hasDerivAt hFw himw
  have hYDiff : DifferentiableAt ℝ Y z := by
    simpa [Y] using differentiableAt_complex_ofReal_im_of_hasDerivAt hFz
  have hF₁Diff : DifferentiableAt ℝ F₁ z :=
    hF₁z.complexToReal_fderiv.differentiableAt
  have hY_ne : Y z ≠ 0 := by
    simpa [Y] using (show (((F z).im : ℂ) ≠ 0) from by
      exact_mod_cast him)
  have hquotDiff : DifferentiableAt ℝ (fun w : ℂ ↦ F₁ w / Y w) z := by
    rw [show (fun w : ℂ ↦ F₁ w / Y w) =
        (fun w : ℂ ↦ F₁ w * (Y w)⁻¹) by
          ext w
          rw [div_eq_mul_inv]]
    exact hF₁Diff.mul (hYDiff.inv hY_ne)
  have hYbar :
      frechetDBarValue Y z = Complex.I * star (F₁ z) / 2 := by
    simpa [Y] using frechetDBarValue_complex_ofReal_im_of_hasDerivAt_general hFz
  rw [frechetDBarValue_congr_of_eventuallyEq hEq]
  rw [show (fun w : ℂ ↦ -Complex.I * F₁ w / (2 * Y w)) =
      (fun w : ℂ ↦ (-Complex.I / 2) * (F₁ w / Y w)) by
        ext w
        ring_nf]
  rw [frechetDBarValue_const_mul_of_differentiableAt hquotDiff]
  rw [frechetDBarValue_div_of_differentiableAt hF₁Diff hYDiff hY_ne]
  rw [frechetDBarValue_of_hasDerivAt hF₁z, hYbar]
  have hnorm : (Complex.normSq (F₁ z) : ℂ) = star (F₁ z) * F₁ z := by
    simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := F₁ z))
  rw [hnorm]
  simp [Y] at hY_ne ⊢
  field_simp [hY_ne]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- Matrix representatives for real projective Mobius transformations. -/
abbrev RealProjectiveMobiusRepresentative : Type :=
  GL (Fin 2) ℝ

/-- View a real projective Mobius representative as a complex Mobius representative.

%%handwave
name:
  Complexification of a real Möbius representative
statement:
  Entrywise inclusion $\mathbb R\hookrightarrow\mathbb C$ defines a group homomorphism $\mathrm{GL}_2(\mathbb R)\to\mathrm{GL}_2(\mathbb C)$.
-/
def realProjectiveMobiusRepresentativeAsMobiusRepresentative :
    RealProjectiveMobiusRepresentative →* MobiusRepresentative :=
  Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)

/-- The complex projective class of a real projective Mobius representative.

%%handwave
name:
  Complex projective class of a real Möbius representative
statement:
  Complexification followed by passage to projective class defines a group homomorphism $\mathrm{GL}_2(\mathbb R)\to\mathrm{PGL}_2(\mathbb C)$.
-/
def realProjectiveMobiusRepresentativeToMobiusGroup :
    RealProjectiveMobiusRepresentative →* MobiusGroup :=
  (Matrix.ProjGenLinGroup.mk : MobiusRepresentative →* MobiusGroup).comp
    realProjectiveMobiusRepresentativeAsMobiusRepresentative

/-- The subgroup of $\mathrm{PGL}_2(\mathbb C)$ represented by real matrices.

%%handwave
name:
  The real projective Möbius subgroup
statement:
  The subgroup $\mathrm{PGL}_2(\mathbb R)\subseteq\mathrm{PGL}_2(\mathbb C)$ is the image of $\mathrm{GL}_2(\mathbb R)$ under complexification and passage to projective class.
-/
def pgl2rMobiusSubgroup : Subgroup MobiusGroup :=
  MonoidHom.range realProjectiveMobiusRepresentativeToMobiusGroup

/--
A concrete certificate that a based projective structure has holonomy in the
real projective subgroup.
-/
structure ComplexProjectiveStructure.PGL2RHolonomyData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) where
  /-- The complex projective holonomy read from the projective atlas. -/
  projectiveHolonomy : HolonomyRepresentation X x₀
  /-- Concrete atlas data tying the holonomy to the projective structure. -/
  holonomy_constructed_from_projective_charts :
    ProjectiveHolonomyConstructionData X x₀ P projectiveHolonomy
  /-- The holonomy is represented by real projective Mobius transformations. -/
  projectiveHolonomy_real :
    ∀ γ, projectiveHolonomy γ ∈ pgl2rMobiusSubgroup

/--
A complex projective structure has real projective holonomy if the holonomy
constructed from its own projective atlas lies in $\mathrm{PGL}_2(\mathbb R)$.

%%handwave
name:
  Real projective holonomy
statement:
  A based complex projective structure has real projective holonomy when its atlas supplies a holonomy representation whose image is contained in $\mathrm{PGL}_2(\mathbb R)\subseteq\mathrm{PGL}_2(\mathbb C)$.
-/
def HasPGL2RHolonomy {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  Nonempty (P.PGL2RHolonomyData x₀)

namespace ComplexProjectiveStructure.RealHolonomyData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {P : ComplexProjectiveStructure X}

end ComplexProjectiveStructure.RealHolonomyData

/-- The real projective line inside the Riemann sphere.

%%handwave
name:
  Real projective line in the Riemann sphere
statement:
  The subset $\mathbb P^1(\mathbb R)\subseteq\mathbb P^1(\mathbb C)$ is the image of the one-point compactification of $\mathbb R$ under the inclusion $\mathbb R\hookrightarrow\mathbb C$.
-/
def realProjectiveLineInRiemannSphere : Set RiemannSphere :=
  Set.range (OnePoint.map (algebraMap ℝ ℂ) : OnePoint ℝ → RiemannSphere)

/-- A point of the Riemann sphere lies on the real projective line.

%%handwave
name:
  Membership in the real projective line
statement:
  A point $p\in\mathbb P^1(\mathbb C)$ is real projective precisely when $p\in\mathbb P^1(\mathbb R)$ under the standard inclusion.
-/
def RiemannSphere.IsRealProjectivePoint (z : RiemannSphere) : Prop :=
  z ∈ realProjectiveLineInRiemannSphere

/-- The affine finite part of a point of the Riemann sphere, with infinity sent to `0`.

%%handwave
name:
  Finite coordinate on the Riemann sphere
statement:
  The finite-coordinate map $\mathbb P^1(\mathbb C)\to\mathbb C$ sends an affine point $[z:1]$ to $z$ and sends the point at infinity to $0$.
-/
def RiemannSphere.finitePart (z : RiemannSphere) : ℂ :=
  z.elim 0 id

/-- Away from infinity, coercing the finite part recovers the original sphere point.

%%handwave
name:
  Recovery from the finite coordinate
statement:
  If \(p\in\mathbb P^1(\mathbb C)\) is not infinity, then the affine point determined by its finite coordinate is \(p\) itself.
proof:
  Split the sphere into its point at infinity and its affine chart. The hypothesis excludes the first case, and the claim is immediate in the affine case.
-/
theorem RiemannSphere.coe_finitePart_eq_of_ne_infty
    {z : RiemannSphere} (hz : z ≠ OnePoint.infty) :
    ((RiemannSphere.finitePart z : ℂ) : RiemannSphere) = z := by
  induction z using OnePoint.rec with
  | infty => exact (hz rfl).elim
  | coe z => rfl

/-- A point is off the real projective line exactly when it is finite and non-real.

%%handwave
name:
  Characterization of the complement of the real projective line
statement:
  A point \(p\in\mathbb P^1(\mathbb C)\) lies outside \(\mathbb P^1(\mathbb R)\) if and only if \(p=[w:1]\) for some \(w\in\mathbb C\) with \(\operatorname{Im}w\ne0\).
proof:
  Infinity belongs to the real projective line. In the affine chart, a complex number comes from a real number exactly when its imaginary part vanishes.
-/
theorem RiemannSphere.not_isRealProjectivePoint_iff_exists_im_ne_zero
    (z : RiemannSphere) :
    ¬ z.IsRealProjectivePoint ↔
      ∃ w : ℂ, z = (w : RiemannSphere) ∧ w.im ≠ 0 := by
  constructor
  · intro hz
    induction z using OnePoint.rec with
    | infty =>
        exfalso
        exact hz ⟨OnePoint.infty, rfl⟩
    | coe w =>
        refine ⟨w, rfl, ?_⟩
        intro him
        apply hz
        refine ⟨(w.re : OnePoint ℝ), ?_⟩
        change (((w.re : ℝ) : ℂ) : RiemannSphere) = (w : RiemannSphere)
        rw [OnePoint.coe_eq_coe]
        apply Complex.ext <;> simp [him]
  · rintro ⟨w, rfl, hw⟩ hreal
    rcases hreal with ⟨r, hr⟩
    induction r using OnePoint.rec with
    | infty =>
        exact OnePoint.infty_ne_coe w hr
    | coe r =>
        have hcomplex : ((r : ℝ) : ℂ) = w := by
          exact OnePoint.coe_injective hr
        apply hw
        rw [← hcomplex]
        simp

/-- The embedded real line is closed in the complex plane.

%%handwave
name:
  The real axis is closed
statement:
  The image of \(\mathbb R\) in \(\mathbb C\) is a closed subset.
proof:
  The real axis is the zero set of the continuous function \(z\mapsto\operatorname{Im}z\).
-/
theorem complexRealLine_closed : IsClosed (Set.range (algebraMap ℝ ℂ)) := by
  rw [show Set.range (algebraMap ℝ ℂ) = {z : ℂ | z.im = 0} by
    ext z
    constructor
    · rintro ⟨r, rfl⟩
      simp
    · intro hz
      refine ⟨z.re, ?_⟩
      apply Complex.ext
      · simp
      · simpa using hz.symm]
  exact isClosed_eq Complex.continuous_im continuous_const

/-- The real projective line is closed in the Riemann sphere.

%%handwave
name:
  The real projective line is closed in the Riemann sphere
statement:
  The embedded copy \(\mathbb P^1(\mathbb R)\subseteq\mathbb P^1(\mathbb C)\) is closed.
proof:
  It consists of the closed real axis in the affine chart together with the point at infinity. The closed-set criterion for the one-point compactification gives the result.
-/
theorem realProjectiveLineInRiemannSphere_closed :
    IsClosed realProjectiveLineInRiemannSphere := by
  rw [OnePoint.isClosed_iff_of_mem]
  · rw [show ((↑) : ℂ → RiemannSphere) ⁻¹' realProjectiveLineInRiemannSphere =
        Set.range (algebraMap ℝ ℂ) by
      ext z
      constructor
      · rintro ⟨y, hy⟩
        cases y with
        | infty => simp at hy
        | coe r =>
            refine ⟨r, ?_⟩
            simpa using (OnePoint.coe_injective hy)
      · rintro ⟨r, rfl⟩
        exact ⟨(r : OnePoint ℝ), by simp⟩]
    exact complexRealLine_closed
  · exact ⟨OnePoint.infty, by simp⟩

/-- The complement of the real projective line is open in the Riemann sphere.

%%handwave
name:
  The nonreal projective locus is open
statement:
  The complement \(\mathbb P^1(\mathbb C)\setminus\mathbb P^1(\mathbb R)\) is open.
proof:
  It is the complement of the closed real projective line.
-/
theorem offRealProjectiveLineInRiemannSphere_open :
    IsOpen {z : RiemannSphere | ¬ RiemannSphere.IsRealProjectivePoint z} := by
  change IsOpen realProjectiveLineInRiemannSphereᶜ
  exact realProjectiveLineInRiemannSphere_closed.isOpen_compl

/-- Scalar matrices act trivially on the Riemann sphere.

%%handwave
name:
  Scalar matrices act trivially on the projective line
statement:
  For every \(u\in\mathbb C^\times\), the scalar matrix \(uI\) fixes every point of \(\mathbb P^1(\mathbb C)\).
proof:
  Multiplying both homogeneous coordinates by the same nonzero scalar leaves the projective point unchanged; this applies both at infinity and in the affine chart.
-/
theorem scalar_smul_riemannSphere (u : ℂˣ) (z : RiemannSphere) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) ℂ) • z = z := by
  cases z with
  | none =>
      change (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) ℂ) •
          (OnePoint.infty : OnePoint ℂ) = OnePoint.infty
      rw [OnePoint.smul_infty_eq_ite]
      simp [Matrix.GeneralLinearGroup.scalar]
  | some z =>
      change (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) ℂ) •
          (z : OnePoint ℂ) = (z : OnePoint ℂ)
      rw [OnePoint.smul_some_eq_ite]
      simp [Matrix.GeneralLinearGroup.scalar]

/-- Equal projective classes act identically on the Riemann sphere.

%%handwave
name:
  Representatives of one projective class have the same action
statement:
  If \(A,B\in\mathrm{GL}_2(\mathbb C)\) determine the same class in \(\mathrm{PGL}_2(\mathbb C)\), then \(A(p)=B(p)\) for every \(p\in\mathbb P^1(\mathbb C)\).
proof:
  Equality of projective classes means that \(B=A(uI)\) for a nonzero scalar \(u\). Scalar matrices act trivially, so the two actions coincide.
-/
theorem mobiusRepresentative_smul_eq_of_mk_eq
    {A B : MobiusRepresentative}
    (hAB : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (z : RiemannSphere) :
    A • z = B • z := by
  have hscalar : A⁻¹ * B ∈ Subgroup.center (GL (Fin 2) ℂ) := by
    exact QuotientGroup.eq.mp hAB
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hscalar
  rcases hscalar with ⟨u, hu⟩
  have hB : B = A * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    have hmul := congrArg (fun G : GL (Fin 2) ℂ ↦ A * G) hu
    simpa [mul_assoc] using hmul.symm
  rw [hB, mul_smul, scalar_smul_riemannSphere]

/-- Real projective transformations preserve the real projective line.

%%handwave
name:
  Real projective transformations preserve the real projective line
statement:
  Every \(A\in\mathrm{GL}_2(\mathbb R)\), viewed over \(\mathbb C\), maps \(\mathbb P^1(\mathbb R)\) into itself.
proof:
  Write the point using real homogeneous coordinates. Applying the real matrix still gives real homogeneous coordinates, and complexification commutes with the projective action.
-/
theorem realProjectiveMobius_preserves_realProjectiveLine
    (A : RealProjectiveMobiusRepresentative) {z : RiemannSphere}
    (hz : RiemannSphere.IsRealProjectivePoint z) :
    RiemannSphere.IsRealProjectivePoint
      (realProjectiveMobiusRepresentativeAsMobiusRepresentative A • z) := by
  rcases hz with ⟨r, rfl⟩
  refine ⟨A • r, ?_⟩
  exact OnePoint.map_smul (algebraMap ℝ ℂ) A r

/-- Any representative of a real projective class preserves the real projective line.

%%handwave
name:
  Complex representatives of real projective classes preserve the real locus
statement:
  Let \(G\in\mathrm{PGL}_2(\mathbb R)\subseteq\mathrm{PGL}_2(\mathbb C)\). Every complex matrix representing \(G\) maps \(\mathbb P^1(\mathbb R)\) into itself.
proof:
  Compare the chosen complex representative with a real representative of \(G\). They have the same projective action, and the real representative preserves the real projective line.
-/
theorem pgl2r_representative_preserves_realProjectiveLine
    {G : MobiusGroup} (hG : G ∈ pgl2rMobiusSubgroup)
    {A : MobiusRepresentative} (hA : Matrix.ProjGenLinGroup.mk A = G)
    {z : RiemannSphere} (hz : RiemannSphere.IsRealProjectivePoint z) :
    RiemannSphere.IsRealProjectivePoint (A • z) := by
  rcases hG with ⟨R, hR⟩
  have hAR : Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk (realProjectiveMobiusRepresentativeAsMobiusRepresentative R) := by
    rw [hA, ← hR]
    rfl
  rw [mobiusRepresentative_smul_eq_of_mk_eq hAR]
  exact realProjectiveMobius_preserves_realProjectiveLine R hz

namespace ComplexProjectiveStructure.PGL2RHolonomyData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {P : ComplexProjectiveStructure X}

/-- Real-projective-point membership of the developing map is constant on cover fibers.

%%handwave
name:
  The real-projective developing locus is constant on cover fibers
statement:
  If two points of the developing cover project to the same surface point and one developing value lies in ℝP¹, then the other also lies in ℝP¹.
proof:
  A deck transformation carries one lift to the other. Equivariance applies a holonomy element in PGL₂(ℝ), which preserves ℝP¹.
-/
theorem developingMap_isRealProjectivePoint_of_same_fiber
    (H : P.PGL2RHolonomyData x₀)
    {y z : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (hyz : H.holonomy_constructed_from_projective_charts.developingData.cover.projection y =
      H.holonomy_constructed_from_projective_charts.developingData.cover.projection z)
    (hy : RiemannSphere.IsRealProjectivePoint
      (H.holonomy_constructed_from_projective_charts.developingData.developingMap y)) :
    RiemannSphere.IsRealProjectivePoint
      (H.holonomy_constructed_from_projective_charts.developingData.developingMap z) := by
  let cover := H.holonomy_constructed_from_projective_charts.developingData.cover
  rcases cover.deckAction_same_fiber_transitive y z hyz with ⟨γ, hγ⟩
  rcases (H.holonomy_constructed_from_projective_charts.developingData).equivariant_representatives γ with
    ⟨A, hA, hdev⟩
  rw [← hγ, hdev]
  exact pgl2r_representative_preserves_realProjectiveLine
    (H.projectiveHolonomy_real γ) hA hy

/--
If two local developing-chart sections differ by a fixed deck transformation
at one overlap point, then they differ by that same deck transformation near
that point inside the chart-source overlap.

%%handwave
name:
  A deck relation between local lifts persists nearby
statement:
  If two continuous local sections of a covering differ by a fixed deck transformation at one overlap point, then the same deck transformation relates them throughout some overlap neighborhood.
proof:
  Both sections have the same projection. Uniqueness of covering-space lifts makes the equality set locally constant near the point where they agree.
-/
theorem localAgreement_lifts_deckAction_eventuallyEq_on_overlap
    (H : P.PGL2RHolonomyData x₀)
    {y₁ y₂ : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L₁ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₁)
    (L₂ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₂)
    {x : X} (hx₁ : x ∈ L₁.chart.source) (hx₂ : x ∈ L₂.chart.source)
    {γ : FundamentalGroup X x₀}
    (hγ :
      H.holonomy_constructed_from_projective_charts.developingData.cover.deckAction γ
          (L₁.lift ⟨x, hx₁⟩) =
        L₂.lift ⟨x, hx₂⟩) :
    (fun p : {x : X // x ∈ L₁.chart.source ∩ L₂.chart.source} ↦
      H.holonomy_constructed_from_projective_charts.developingData.cover.deckAction γ
        (L₁.lift ⟨(p : X), p.property.1⟩)) =ᶠ[𝓝 (⟨x, hx₁, hx₂⟩ :
          {x : X // x ∈ L₁.chart.source ∩ L₂.chart.source})]
      fun p ↦ L₂.lift ⟨(p : X), p.property.2⟩ := by
  let developingData := H.holonomy_constructed_from_projective_charts.developingData
  let cover := developingData.cover
  let T := {x : X // x ∈ L₁.chart.source ∩ L₂.chart.source}
  let p₀ : T := ⟨x, hx₁, hx₂⟩
  let s₁ : T → cover.total := fun p ↦ L₁.lift ⟨(p : X), p.property.1⟩
  let s₂ : T → cover.total := fun p ↦ L₂.lift ⟨(p : X), p.property.2⟩
  let b : T → X := fun p ↦ (p : X)
  have hi₁ : Continuous (fun p : T ↦ (⟨(p : X), p.property.1⟩ : L₁.chart.source)) :=
    continuous_subtype_val.subtype_mk (fun p ↦ p.property.1)
  have hi₂ : Continuous (fun p : T ↦ (⟨(p : X), p.property.2⟩ : L₂.chart.source)) :=
    continuous_subtype_val.subtype_mk (fun p ↦ p.property.2)
  have hs₁ : ContinuousAt s₁ p₀ := by
    exact (L₁.lift_continuous.comp hi₁).continuousAt
  have hs₂ : ContinuousAt s₂ p₀ := by
    exact (L₂.lift_continuous.comp hi₂).continuousAt
  have hproj₁ : ∀ᶠ p in 𝓝 p₀, cover.projection (s₁ p) = b p := by
    exact Filter.Eventually.of_forall fun p ↦ by
      simpa [cover, developingData, s₁, b] using
        L₁.lift_projects ⟨(p : X), p.property.1⟩
  have hproj₂ : ∀ᶠ p in 𝓝 p₀, cover.projection (s₂ p) = b p := by
    exact Filter.Eventually.of_forall fun p ↦ by
      simpa [cover, developingData, s₂, b] using
        L₂.lift_projects ⟨(p : X), p.property.2⟩
  have h0 : cover.deckAction γ (s₁ p₀) = s₂ p₀ := by
    simpa [cover, developingData, s₁, s₂, p₀] using hγ
  simpa [cover, developingData, T, s₁, s₂, p₀] using
    cover.deckAction_sections_eventuallyEq_of_projection_eq
      s₁ s₂ b γ hs₁ hs₂ hproj₁ hproj₂ h0

/--
The real-projective transition between two local developing-chart agreements
is locally constant on the chart-source overlap.

%%handwave
name:
  The normalized-chart transition is locally constant on an overlap
statement:
  For two local developing-chart agreements at a common point, one R∈PGL₂(ℝ) relates their normalized projective coordinates on a neighborhood inside the chart overlap.
proof:
  Choose the deck transformation relating the two lifted sections, propagate it locally by lift uniqueness, and apply developing-map equivariance pointwise.
-/
theorem localAgreement_normalizedChart_transition_realProjective_eventuallyEq_on_overlap
    (H : P.PGL2RHolonomyData x₀)
    {y₁ y₂ : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L₁ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₁)
    (L₂ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₂)
    {x : X} (hx₁ : x ∈ L₁.chart.source) (hx₂ : x ∈ L₂.chart.source) :
    ∃ R : RealProjectiveMobiusRepresentative,
      L₂.normalization • L₂.chart x =
        realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
          (L₁.normalization • L₁.chart x) ∧
      (fun p : {x : X // x ∈ L₁.chart.source ∩ L₂.chart.source} ↦
        L₂.normalization • L₂.chart (p : X)) =ᶠ[𝓝 (⟨x, hx₁, hx₂⟩ :
          {x : X // x ∈ L₁.chart.source ∩ L₂.chart.source})]
        fun p ↦
          realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
            (L₁.normalization • L₁.chart (p : X)) := by
  let developingData := H.holonomy_constructed_from_projective_charts.developingData
  let cover := developingData.cover
  let y₁x : cover.total := L₁.lift ⟨x, hx₁⟩
  let y₂x : cover.total := L₂.lift ⟨x, hx₂⟩
  have hfiber : cover.projection y₁x = cover.projection y₂x := by
    calc
      cover.projection y₁x = x := by
        simpa [cover, developingData, y₁x] using L₁.lift_projects ⟨x, hx₁⟩
      _ = cover.projection y₂x := by
        simpa [cover, developingData, y₂x] using (L₂.lift_projects ⟨x, hx₂⟩).symm
  rcases cover.deckAction_same_fiber_transitive y₁x y₂x hfiber with ⟨γ, hγ⟩
  rcases developingData.equivariant_representatives γ with
    ⟨A, hA, hdev⟩
  rcases H.projectiveHolonomy_real γ with ⟨R, hR⟩
  have hAR : Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk (realProjectiveMobiusRepresentativeAsMobiusRepresentative R) := by
    rw [hA, ← hR]
    rfl
  have hlifts :=
    H.localAgreement_lifts_deckAction_eventuallyEq_on_overlap
      L₁ L₂ hx₁ hx₂ hγ
  have hlocal :
      (fun p : {x : X // x ∈ L₁.chart.source ∩ L₂.chart.source} ↦
        L₂.normalization • L₂.chart (p : X)) =ᶠ[𝓝 (⟨x, hx₁, hx₂⟩ :
          {x : X // x ∈ L₁.chart.source ∩ L₂.chart.source})]
        fun p ↦
          realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
            (L₁.normalization • L₁.chart (p : X)) := by
    filter_upwards [hlifts] with p hp
    have hdev_eq :
        developingData.developingMap (L₂.lift ⟨(p : X), p.property.2⟩) =
          A • developingData.developingMap (L₁.lift ⟨(p : X), p.property.1⟩) := by
      rw [← hp]
      exact hdev (L₁.lift ⟨(p : X), p.property.1⟩)
    have h₁ := L₁.developing_eq_normalized_chart ⟨(p : X), p.property.1⟩
    have h₂ := L₂.developing_eq_normalized_chart ⟨(p : X), p.property.2⟩
    rw [h₂, h₁] at hdev_eq
    simpa [mobiusRepresentative_smul_eq_of_mk_eq hAR] using hdev_eq
  refine ⟨R, ?_, hlocal⟩
  simpa using hlocal.self_of_nhds

/--
The locally constant real-projective transition between two local developing
agreements, expressed as an ordinary neighborhood statement on the surface.

%%handwave
name:
  The normalized-chart transition holds on a surface neighborhood
statement:
  For two local developing-chart agreements at a common point, one R∈PGL₂(ℝ) relates their normalized projective coordinates for all nearby surface points lying in both chart domains.
proof:
  Transfer the overlap-subspace germ equality to an ordinary neighborhood using openness of the two chart sources.
-/
theorem localAgreement_normalizedChart_transition_realProjective_eventuallyEq_nhds
    (H : P.PGL2RHolonomyData x₀)
    {y₁ y₂ : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L₁ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₁)
    (L₂ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₂)
    {x : X} (hx₁ : x ∈ L₁.chart.source) (hx₂ : x ∈ L₂.chart.source) :
    ∃ R : RealProjectiveMobiusRepresentative,
      L₂.normalization • L₂.chart x =
        realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
          (L₁.normalization • L₁.chart x) ∧
      ∀ᶠ x' in 𝓝 x,
        x' ∈ L₁.chart.source →
          x' ∈ L₂.chart.source →
            L₂.normalization • L₂.chart x' =
              realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
                (L₁.normalization • L₁.chart x') := by
  let S : Set X := L₁.chart.source ∩ L₂.chart.source
  let T := {x : X // x ∈ S}
  let p₀ : T := ⟨x, hx₁, hx₂⟩
  rcases
    H.localAgreement_normalizedChart_transition_realProjective_eventuallyEq_on_overlap
      L₁ L₂ hx₁ hx₂ with
    ⟨R, hpoint, hlocal⟩
  refine ⟨R, hpoint, ?_⟩
  have hS_nhds : ∀ᶠ x' in 𝓝 x, x' ∈ S :=
    (L₁.chart.open_source.inter L₂.chart.open_source).mem_nhds ⟨hx₁, hx₂⟩
  have hmap :
      Filter.map ((↑) : T → X) (𝓝 p₀) = 𝓝 x :=
    map_nhds_subtype_coe_eq_nhds (p := fun x' : X ↦ x' ∈ S)
      ⟨hx₁, hx₂⟩ hS_nhds
  have himage :
      ((↑) : T → X) ''
          {p : T |
            L₂.normalization • L₂.chart (p : X) =
              realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
                (L₁.normalization • L₁.chart (p : X))} ∈ 𝓝 x := by
    rw [← hmap]
    exact Filter.image_mem_map hlocal
  filter_upwards [himage] with x' hx' hx₁' hx₂'
  rcases hx' with ⟨p, hp, hp_eq⟩
  simpa [← hp_eq] using hp

/-- The real-projective locus obtained by descending the developing-map preimage.

%%handwave
name:
  Descended real-projective locus
statement:
  For a projective structure with real holonomy, the real-projective locus is the set of surface points whose chosen developing lift maps into $\mathbb P^1(\mathbb R)$.
-/
def realProjectiveLocus (H : P.PGL2RHolonomyData x₀) : Set X :=
  {x | RiemannSphere.IsRealProjectivePoint
      (H.holonomy_constructed_from_projective_charts.developingData.developingMap
      (Classical.choose
        ((H.holonomy_constructed_from_projective_charts.developingData.cover).projection_surjective x)))}

/-- The regular locus is the complement of the descended real-projective locus.

%%handwave
name:
  Regular locus of a real-holonomy projective structure
statement:
  The regular locus is $X\setminus S$, where $S$ is the descended inverse image of $\mathbb P^1(\mathbb R)$ under the developing map.
-/
def regularSet (H : P.PGL2RHolonomyData x₀) : Set X :=
  H.realProjectiveLocusᶜ

/-- The descended real-projective locus is exactly the developing-map preimage.

%%handwave
name:
  The descended singular locus is the developing preimage of ℝP¹
statement:
  A surface point belongs to the descended real-projective locus exactly when the developing value of any lift lies in ℝP¹.
proof:
  The locus is defined using one chosen lift; fiberwise independence of real-projective membership replaces that lift by the given one.
-/
theorem realProjectiveLocus_eq_developing_preimage
    (H : P.PGL2RHolonomyData x₀)
    (y : H.holonomy_constructed_from_projective_charts.developingData.cover.total) :
    H.holonomy_constructed_from_projective_charts.developingData.cover.projection y
        ∈ H.realProjectiveLocus ↔
      RiemannSphere.IsRealProjectivePoint
        (H.holonomy_constructed_from_projective_charts.developingData.developingMap y) := by
  let cover := H.holonomy_constructed_from_projective_charts.developingData.cover
  let y₀ := Classical.choose (cover.projection_surjective (cover.projection y))
  have hy₀ : cover.projection y₀ = cover.projection y :=
    Classical.choose_spec (cover.projection_surjective (cover.projection y))
  constructor
  · intro h
    change RiemannSphere.IsRealProjectivePoint
      (H.holonomy_constructed_from_projective_charts.developingData.developingMap y₀) at h
    exact H.developingMap_isRealProjectivePoint_of_same_fiber hy₀ h
  · intro h
    change RiemannSphere.IsRealProjectivePoint
      (H.holonomy_constructed_from_projective_charts.developingData.developingMap y₀)
    exact H.developingMap_isRealProjectivePoint_of_same_fiber hy₀.symm h

/--
On a local agreement chart, the regular-locus condition is the off-real
condition for the normalized projective coordinate.

%%handwave
name:
  Regularity in a local normalized projective chart
statement:
  At a point of a local developing-chart agreement, the surface point is regular exactly when the normalized projective chart value avoids ℝP¹.
proof:
  Evaluate the developing map on the local lifted section and use its equality with the normalized chart.
-/
theorem regularSet_iff_normalizedChart_offReal
    (H : P.PGL2RHolonomyData x₀)
    {y : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y)
    {x : X} (hx : x ∈ L.chart.source) :
    x ∈ H.regularSet ↔
      ¬ RiemannSphere.IsRealProjectivePoint (L.normalization • L.chart x) := by
  let xsub : L.chart.source := ⟨x, hx⟩
  have hpre := H.realProjectiveLocus_eq_developing_preimage (L.lift xsub)
  have hproj : H.holonomy_constructed_from_projective_charts.developingData.cover.projection
        (L.lift xsub) = x := by
    simpa [xsub] using L.lift_projects xsub
  rw [hproj] at hpre
  have hdev := L.developing_eq_normalized_chart xsub
  rw [regularSet, Set.mem_compl_iff, hpre, hdev]

/--
At a regular point in a local developing-chart agreement, the normalized
projective coordinate is a finite non-real complex number.

%%handwave
name:
  A regular normalized chart value is finite and nonreal
statement:
  At a regular point of a local developing-chart agreement, the normalized projective value is [z:1] for some z∈ℂ with Im z ≠ 0.
proof:
  The normalized value avoids ℝP¹; use the characterization of off-real projective points as finite nonreal complex points.
-/
theorem normalizedChart_offReal_finiteCoordinate
    (H : P.PGL2RHolonomyData x₀)
    {y : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y)
    {x : X} (hx : x ∈ L.chart.source) (hreg : x ∈ H.regularSet) :
    ∃ z : ℂ,
      L.normalization • L.chart x = (z : RiemannSphere) ∧ z.im ≠ 0 := by
  exact (RiemannSphere.not_isRealProjectivePoint_iff_exists_im_ne_zero
    (L.normalization • L.chart x)).mp
      ((H.regularSet_iff_normalizedChart_offReal L hx).mp hreg)

/--
Every regular point has a local developing-chart agreement whose normalized
projective coordinate is finite and off the real line at that point.

%%handwave
name:
  Regular points admit off-real normalized local charts
statement:
  Every regular surface point has a lift and a locally agreeing projective chart whose normalized value at that point is finite with nonzero imaginary part.
proof:
  Choose a lift and its local developing-chart agreement, then apply the normalized-chart characterization of regularity.
-/
theorem exists_localAgreement_normalizedChart_offReal_finiteCoordinate
    (H : P.PGL2RHolonomyData x₀) {x : X} (hreg : x ∈ H.regularSet) :
    ∃ y : H.holonomy_constructed_from_projective_charts.developingData.cover.total,
      ∃ L : ProjectiveHolonomyLocalChartAgreementData X P
          H.holonomy_constructed_from_projective_charts.developingData y,
        H.holonomy_constructed_from_projective_charts.developingData.cover.projection y = x ∧
          x ∈ L.chart.source ∧
            ∃ z : ℂ,
              L.normalization • L.chart x = (z : RiemannSphere) ∧ z.im ≠ 0 := by
  let cover := H.holonomy_constructed_from_projective_charts.developingData.cover
  rcases cover.projection_surjective x with ⟨y, hy⟩
  rcases
    H.holonomy_constructed_from_projective_charts.developingMap_locally_agrees_with_projective_charts
      y with
    ⟨L⟩
  have hxsource : x ∈ L.chart.source := by
    rw [← hy]
    exact L.projected_mem
  exact ⟨y, L, hy, hxsource, H.normalizedChart_offReal_finiteCoordinate L hxsource hreg⟩



/--
The affine finite-part expression for a normalized projective chart in a chosen
complex coordinate.

%%handwave
name:
  Finite normalized projective coordinate
statement:
  Given a normalized projective chart and a complex coordinate $e$, define $F(w)$ to be the affine finite coordinate of the normalized projective value at $e^{-1}(w)$, with a pole assigned the value $0$.
-/
def normalizedChartFinitePart
    (H : P.PGL2RHolonomyData x₀)
    {y : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y)
    (e : OpenPartialHomeomorph X ℂ) : ℂ → ℂ :=
  fun w ↦ RiemannSphere.finitePart (L.normalization • L.chart (e.symm w))

/--
Near a regular point, the finite-part expression is genuinely a finite affine
representative of the normalized projective coordinate.

%%handwave
name:
  The finite part locally represents a normalized chart
statement:
  Near a regular chart point, the finite-part function of a normalized projective chart genuinely represents that projective value, and its base value has nonzero imaginary part.
proof:
  The normalized value is finite and off real at the base point. Continuity keeps it away from infinity nearby, where taking the finite part is inverse to projective inclusion.
-/
theorem normalizedChartFinitePart_eventually_eq
    (H : P.PGL2RHolonomyData x₀)
    {y : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y)
    (e : OpenPartialHomeomorph X ℂ) {z : ℂ}
    (hz : z ∈ e.target) (hxsource : e.symm z ∈ L.chart.source)
    (hreg : e.symm z ∈ H.regularSet) :
    (∀ᶠ w in 𝓝 z,
        (((H.normalizedChartFinitePart L e w : ℂ) : RiemannSphere) =
          L.normalization • L.chart (e.symm w))) ∧
      (H.normalizedChartFinitePart L e z).im ≠ 0 := by
  have hsymm : ContinuousAt e.symm z :=
    e.symm.continuousAt hz
  have hchart : ContinuousAt L.chart (e.symm z) :=
    L.chart.continuousAt hxsource
  have hnorm : ContinuousAt (fun q : RiemannSphere ↦ L.normalization • q)
      (L.chart (e.symm z)) :=
    (mobiusRepresentative_smul_continuous L.normalization).continuousAt
  have hcont : ContinuousAt
      (fun w : ℂ ↦ L.normalization • L.chart (e.symm w)) z :=
    (hnorm.comp hchart).comp hsymm
  rcases H.normalizedChart_offReal_finiteCoordinate L hxsource hreg with
    ⟨v, hv, hv_im⟩
  have hne_at : L.normalization • L.chart (e.symm z) ≠ OnePoint.infty := by
    rw [hv]
    simp
  have hfinite_nhds :
      ∀ᶠ w in 𝓝 z, L.normalization • L.chart (e.symm w) ≠ OnePoint.infty := by
    exact hcont.preimage_mem_nhds
      (OnePoint.isClosed_infty.isOpen_compl.mem_nhds (by
        simpa using hne_at))
  constructor
  · exact hfinite_nhds.mono fun w hw ↦ by
      exact RiemannSphere.coe_finitePart_eq_of_ne_infty hw
  · simpa [normalizedChartFinitePart, hv] using hv_im

/--
The local coordinate half of the forward pullback-density witness.

This contains no metric equality: it is the projective/developing-map part
that is already forced by the regular-locus construction.
-/
structure RegularLocusLocalPullbackCoordinateData
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) where
  /-- The cover point whose local developing-chart agreement supplies the branch. -/
  coverPoint : H.holonomy_constructed_from_projective_charts.developingData.cover.total
  /-- The local developing-chart agreement supplying the branch. -/
  localAgreement : ProjectiveHolonomyLocalChartAgreementData X P
    H.holonomy_constructed_from_projective_charts.developingData coverPoint
  /-- A finite affine branch of the normalized projective coordinate. -/
  finiteCoordinate : ℂ → ℂ
  /-- The projective chart underlying the branch. -/
  chart : ProjectiveChart X
  /-- The Mobius normalization used before taking the finite affine coordinate. -/
  normalization : MobiusRepresentative
  /-- The projective chart belongs to the stored projective atlas. -/
  chart_mem : chart ∈ P.atlasSet
  /-- The point lies in the selected projective chart. -/
  mem_chart_source : e.symm z ∈ chart.source
  /-- The stored chart is the chart from the local agreement. -/
  chart_eq_localAgreement_chart : chart = localAgreement.chart
  /-- The stored normalization is the normalization from the local agreement. -/
  normalization_eq_localAgreement_normalization :
    normalization = localAgreement.normalization
  /-- Locally, the finite branch represents the normalized projective coordinate. -/
  finiteCoordinate_eventually_eq :
    ∀ᶠ w in 𝓝 z,
      ((finiteCoordinate w : ℂ) : RiemannSphere) = normalization • chart (e.symm w)
  /-- At the selected point, the branch lies off the real line. -/
  finiteCoordinate_offReal : (finiteCoordinate z).im ≠ 0

/-- The local coordinate half of the pullback witness exists at every regular chart point.

%%handwave
name:
  Local pullback-coordinate data exist at every regular chart point
statement:
  Every regular chart point admits a finite off-real normalized developing branch, with its projective chart and normalization, that represents the developing coordinate locally.
proof:
  Use the normalized finite branch construction and package its cover point, local chart agreement, germ equality, and off-real base value.
-/
theorem regularLocusLocalPullbackCoordinateData_nonempty
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    Nonempty (H.RegularLocusLocalPullbackCoordinateData e z) := by
  rcases H.exists_localAgreement_normalizedChart_offReal_finiteCoordinate hreg with
    ⟨y, L, _hy, hxsourceL, _v, _hv, _hv_im⟩
  let F' := H.normalizedChartFinitePart L e
  have hF'_eq :
      ∀ᶠ w in 𝓝 z,
        (((F' w : ℂ) : RiemannSphere) = L.normalization • L.chart (e.symm w)) := by
    exact (H.normalizedChartFinitePart_eventually_eq L e hz hxsourceL hreg).1
  have hF'_offReal : (F' z).im ≠ 0 := by
    exact (H.normalizedChartFinitePart_eventually_eq L e hz hxsourceL hreg).2
  exact
    ⟨{ coverPoint := y
       localAgreement := L
       finiteCoordinate := F'
       chart := L.chart
       normalization := L.normalization
       chart_mem := L.chart_mem
       mem_chart_source := hxsourceL
       chart_eq_localAgreement_chart := rfl
       normalization_eq_localAgreement_normalization := rfl
       finiteCoordinate_eventually_eq := hF'_eq
       finiteCoordinate_offReal := hF'_offReal }⟩

/-- A chosen local pullback-coordinate package at a regular chart point.

%%handwave
name:
  Chosen local pullback coordinate
statement:
  At each regular point in a complex chart, choose a finite normalized developing branch that is locally represented by a projective chart and has nonzero imaginary part at the base point.
-/
def regularLocusLocalPullbackCoordinateData
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    H.RegularLocusLocalPullbackCoordinateData e z :=
  Classical.choice (H.regularLocusLocalPullbackCoordinateData_nonempty e hz hreg)

namespace RegularLocusLocalPullbackCoordinateData

variable {H : P.PGL2RHolonomyData x₀}
    {e : OpenPartialHomeomorph X ℂ} {z : ℂ}

/-- The compatible complex chart selected by the projective structure for this branch.

%%handwave
name:
  Compatible complex-chart data for a branch
statement:
  The projective atlas assigns to the projective chart underlying a finite branch a compatible complex chart together with their projective transition data.
-/
def compatibleComplexChartData
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    ProjectiveCompatibleComplexChartData C.chart :=
  P.chart_complex_compatible_of_mem C.chart_mem

/-- The selected ambient complex chart for the projective chart underlying this branch.

%%handwave
name:
  Compatible complex chart for a finite branch
statement:
  The compatible complex chart of a finite branch is the complex chart selected by the compatibility data of its underlying projective chart.
-/
def compatibleComplexChart
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    OpenPartialHomeomorph X ℂ :=
  C.compatibleComplexChartData.complexChart

/-- The finite coordinate expressing the projective chart in the compatible complex chart.

%%handwave
name:
  Compatible finite projective coordinate
statement:
  The compatible finite coordinate is the holomorphic affine function that expresses the underlying projective chart in its selected complex coordinate.
-/
def compatibleFiniteCoordinate
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℂ :=
  C.compatibleComplexChartData.compatibility.finiteCoordinate

/--
The complex Mobius representative carrying the compatible finite projective
coordinate to this branch's normalized developing coordinate.

%%handwave
name:
  Möbius transition to the normalized developing branch
statement:
  If $N$ is the branch normalization and $B$ is the representative relating the projective chart to its compatible finite coordinate, the transition carrying that coordinate to the normalized developing branch is $NB^{-1}$.
-/
def affineTransitionRepresentative
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    MobiusRepresentative :=
  C.normalization * C.compatibleComplexChartData.compatibility.representative⁻¹

/-- The squared pullback density represented by this finite developing-coordinate branch.

%%handwave
name:
  Squared Poincaré pullback density of a finite branch
statement:
  For a finite developing branch $F$, the squared pullback density is $q(w)=(\operatorname{Im}F(w))^{-2}|F'(w)|^2$.
-/
noncomputable def pullbackDensityFunction
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  fun w ↦ poincareDensitySqInChart (C.finiteCoordinate w) *
    Complex.normSq (deriv C.finiteCoordinate w)

/-- The logarithmic density of the local pullback-density branch.

%%handwave
name:
  Logarithmic Poincaré pullback density
statement:
  For the squared pullback density $q$, the logarithmic density is the function $w\mapsto\tfrac12\log q(w)$.
-/
noncomputable def pullbackLogDensityFunction
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  logDensityFromDensitySq C.pullbackDensityFunction

/-- The derivative part of the explicit local pullback logarithmic density.

%%handwave
name:
  Logarithmic derivative contribution
statement:
  For a finite branch $F$, the derivative contribution to its logarithmic pullback density is $w\mapsto\tfrac12\log |F'(w)|^2$.
-/
noncomputable def pullbackLogDerivativeTerm
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  fun w : ℂ ↦
    Real.log (Complex.normSq (deriv C.finiteCoordinate w)) / 2

/-- The imaginary-coordinate part of the explicit local pullback logarithmic density.

%%handwave
name:
  Logarithmic height contribution
statement:
  For a finite branch $F$, the height contribution to its logarithmic pullback density is $w\mapsto\log(\operatorname{Im}F(w))$.
-/
noncomputable def pullbackLogImaginaryTerm
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  fun w : ℂ ↦ Real.log (C.finiteCoordinate w).im

/-- The explicit local formula for the pullback logarithmic density.

%%handwave
name:
  Explicit logarithmic pullback-density expression
statement:
  For a finite branch $F$, the explicit logarithmic density is $\tfrac12\log |F'|^2-\log(\operatorname{Im}F)$.
-/
noncomputable def pullbackLogDensityExpression
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  C.pullbackLogDerivativeTerm - C.pullbackLogImaginaryTerm

/-- The squared pullback density represented by this finite developing-coordinate branch.

%%handwave
name:
  Formula for a branch pullback density
statement:
  For a finite developing branch F, its squared pullback density is ρ²(w)=(Im F(w))⁻²|F′(w)|².
proof:
  This is the defining formula for the branch pullback density.
-/
noncomputable def pullbackDensity
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℝ :=
  C.pullbackDensityFunction z

/--
%%handwave
name:
  Formula for a branch pullback density
statement:
  For a finite developing branch $F$, its squared pullback density is $\rho^2(w)=|F'(w)|^2/(\operatorname{Im}F(w))^2$.
proof:
  This is the defining formula for the branch pullback density.
-/
@[simp]
theorem pullbackDensityFunction_apply
    (C : H.RegularLocusLocalPullbackCoordinateData e z) (w : ℂ) :
    C.pullbackDensityFunction w =
      poincareDensitySqInChart (C.finiteCoordinate w) *
        Complex.normSq (deriv C.finiteCoordinate w) :=
  rfl

/--
%%handwave
name:
  Pullback density is unchanged by reindexing its base point
statement:
  If $z=z'$, transporting a local pullback-coordinate package from $z$ to $z'$ does not change its pullback-density value.
proof:
  Substitute $z'=z$; the transported package and its density are definitionally identical.
-/
@[simp]
theorem pullbackDensity_cast
    {z' : ℂ} (h : z = z') (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    (cast
        (congrArg (fun t : ℂ ↦ H.RegularLocusLocalPullbackCoordinateData e t) h) C :
        H.RegularLocusLocalPullbackCoordinateData e z').pullbackDensity =
      C.pullbackDensity := by
  cases h
  rfl

/-- The chosen finite branch represents its stored normalized projective coordinate at the point.

%%handwave
name:
  The finite branch represents the normalized projective chart
statement:
  At its base point z, a finite branch F satisfies [F(z):1]=N·φ(e⁻¹(z)), for the stored projective chart φ and normalization N.
proof:
  Evaluate the stored local germ equality at z.
-/
theorem finiteCoordinate_eq_normalizedChart_at
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    ((C.finiteCoordinate z : ℂ) : RiemannSphere) =
      C.normalization • C.chart (e.symm z) :=
  C.finiteCoordinate_eventually_eq.self_of_nhds

/--
The chosen finite branch represents the normalized projective coordinate from
its stored local developing-chart agreement.

%%handwave
name:
  The finite branch agrees with its developing-chart normalization
statement:
  At the base point, the finite branch represents the normalized projective coordinate supplied by the stored local developing-map agreement.
proof:
  Replace the stored chart and normalization by those of the local agreement in the preceding pointwise equality.
-/
theorem finiteCoordinate_eq_localAgreement_normalizedChart_at
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    ((C.finiteCoordinate z : ℂ) : RiemannSphere) =
      C.localAgreement.normalization • C.localAgreement.chart (e.symm z) := by
  simpa [C.chart_eq_localAgreement_chart, C.normalization_eq_localAgreement_normalization]
    using C.finiteCoordinate_eq_normalizedChart_at

/-- The regular point lies in the selected compatible complex chart.

%%handwave
name:
  The base point lies in the compatible complex chart
statement:
  The regular point underlying the selected projective chart lies in the source of its compatible complex chart.
proof:
  Projective–complex compatibility contains the projective chart source in the complex chart source.
-/
theorem mem_compatibleComplexChart_source
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    e.symm z ∈ C.compatibleComplexChart.source :=
  C.compatibleComplexChartData.projective_source_subset_complex_source C.mem_chart_source

/-- The compatible complex coordinate of the point lies in the projective transition source.

%%handwave
name:
  The compatible coordinate lies in the transition domain
statement:
  The compatible complex coordinate of the base point belongs to the domain on which the compatible complex chart and projective chart compose.
proof:
  Use membership in both chart sources and the inverse-chart identities to verify the transition-domain conditions.
-/
theorem compatibleCoordinate_mem_transition_source
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    C.compatibleComplexChart (e.symm z) ∈
      (C.compatibleComplexChart.symm.trans C.chart).source := by
  rw [OpenPartialHomeomorph.trans_source]
  have hxsource : e.symm z ∈ C.compatibleComplexChart.source :=
    C.mem_compatibleComplexChart_source
  constructor
  · simpa [OpenPartialHomeomorph.symm_source] using
      C.compatibleComplexChart.map_source hxsource
  · simpa [C.compatibleComplexChart.left_inv hxsource] using C.mem_chart_source

/-- The compatible finite coordinate represents the projective chart at the selected point.

%%handwave
name:
  The compatible finite coordinate represents the projective chart
statement:
  At the selected point, the compatibility Möbius representative sends the projective chart value to its finite coordinate in the compatible complex chart.
proof:
  Evaluate the projective–complex chart compatibility relation and simplify the chart inverse.
-/
theorem compatibleFiniteCoordinate_eq_projectiveChart_at
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    C.compatibleComplexChartData.compatibility.representative • C.chart (e.symm z) =
      (C.compatibleFiniteCoordinate
        (C.compatibleComplexChart (e.symm z)) : RiemannSphere) := by
  have hsource := C.compatibleCoordinate_mem_transition_source
  have heq :=
    C.compatibleComplexChartData.compatibility.finiteCoordinate_eq
      (C.compatibleComplexChart (e.symm z)) hsource
  have hxsource : e.symm z ∈ C.compatibleComplexChart.source :=
    C.mem_compatibleComplexChart_source
  rw [OpenPartialHomeomorph.trans_apply] at heq
  have hleft :
      C.compatibleComplexChartData.complexChart.symm
          (C.compatibleComplexChart (e.symm z)) =
        e.symm z := by
    simpa [compatibleComplexChart] using C.compatibleComplexChart.left_inv hxsource
  rw [hleft] at heq
  simpa [compatibleFiniteCoordinate] using heq

/-- The compatible finite coordinate is holomorphic at the selected point.

%%handwave
name:
  Holomorphicity of the compatible finite coordinate
statement:
  The finite coordinate expressing a projective chart in a compatible complex chart is complex differentiable at the selected point.
proof:
  Apply the holomorphicity supplied by projective–complex chart compatibility.
-/
theorem compatibleFiniteCoordinate_differentiableAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    DifferentiableAt ℂ C.compatibleFiniteCoordinate
      (C.compatibleComplexChart (e.symm z)) :=
  C.compatibleComplexChartData.compatibility.finiteCoordinate_holomorphic
    (C.compatibleComplexChart (e.symm z)) C.compatibleCoordinate_mem_transition_source

/-- The compatible finite coordinate is locally biholomorphic at the selected point.

%%handwave
name:
  Nondegeneracy of the compatible finite coordinate
statement:
  The compatible finite projective coordinate has nonzero derivative at the selected point.
proof:
  Apply the local-biholomorphism property supplied by projective–complex chart compatibility.
-/
theorem compatibleFiniteCoordinate_deriv_ne_zero
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    deriv C.compatibleFiniteCoordinate
      (C.compatibleComplexChart (e.symm z)) ≠ 0 :=
  C.compatibleComplexChartData.compatibility.finiteCoordinate_deriv_ne_zero
    (C.compatibleComplexChart (e.symm z)) C.compatibleCoordinate_mem_transition_source

/-- The compatible finite projective coordinate is complex-smooth at the selected point.

%%handwave
name:
  Smoothness of the compatible finite coordinate
statement:
  The compatible finite projective coordinate is complex C∞ at the selected point.
proof:
  It is holomorphic on an open neighborhood, hence complex smooth there.
-/
theorem compatibleFiniteCoordinate_contDiffAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    ContDiffAt ℂ ⊤ C.compatibleFiniteCoordinate
      (C.compatibleComplexChart (e.symm z)) := by
  rcases C.compatibleComplexChartData.compatibility.finiteCoordinate_local
      (C.compatibleComplexChart (e.symm z))
      C.compatibleCoordinate_mem_transition_source with
    ⟨U, hUopen, hmem, _hsubset, hlocal⟩
  have hDiffOn : DifferentiableOn ℂ C.compatibleFiniteCoordinate U := by
    intro w hw
    exact (hlocal w hw).1.differentiableWithinAt
  exact (hDiffOn.contDiffOn hUopen).contDiffAt (hUopen.mem_nhds hmem)

/--
At the selected point, the normalized developing coordinate is a finite affine
Mobius transform of the projective chart's compatible finite coordinate.

%%handwave
name:
  Factorization of the normalized projective coordinate
statement:
  The normalized developing coordinate equals the affine transition Möbius map applied to the compatible finite projective coordinate at the selected point.
proof:
  Insert the inverse of the compatibility representative and use associativity of the Möbius action.
-/
theorem normalizedChart_eq_affineTransition_at
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    C.normalization • C.chart (e.symm z) =
      C.affineTransitionRepresentative •
        (C.compatibleFiniteCoordinate
          (C.compatibleComplexChart (e.symm z)) : RiemannSphere) := by
  let B : MobiusRepresentative :=
    C.compatibleComplexChartData.compatibility.representative
  let q : RiemannSphere := C.chart (e.symm z)
  let u : RiemannSphere :=
    (C.compatibleFiniteCoordinate
      (C.compatibleComplexChart (e.symm z)) : RiemannSphere)
  have hB : B • q = u := by
    simpa [B, q, u] using C.compatibleFiniteCoordinate_eq_projectiveChart_at
  have hcancel : B⁻¹ • (B • q) = q := by
    rw [← mul_smul]
    simp
  calc
    C.normalization • C.chart (e.symm z) =
        C.normalization • (B⁻¹ • (B • q)) := by
      rw [hcancel]
    _ = C.normalization • (B⁻¹ • u) := by
      rw [hB]
    _ = (C.normalization * B⁻¹) • u := by
      rw [mul_smul]
    _ =
        C.affineTransitionRepresentative •
          (C.compatibleFiniteCoordinate
            (C.compatibleComplexChart (e.symm z)) : RiemannSphere) := by
      rfl

/-- The affine transition denominator is nonzero at the selected point.

%%handwave
name:
  The affine transition has no pole at the compatible value
statement:
  The denominator of the affine transition formula is nonzero at the selected compatible finite coordinate.
proof:
  Its projective image is the finite value F(z), whereas a zero denominator would give infinity.
-/
theorem affineTransition_denominator_ne_zero_at
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    mobiusFiniteDenom C.affineTransitionRepresentative
        (C.compatibleFiniteCoordinate (C.compatibleComplexChart (e.symm z))) ≠ 0 := by
  refine mobiusFiniteDenom_ne_zero_of_smul_coe_eq_coe
    C.affineTransitionRepresentative
    (z := C.compatibleFiniteCoordinate (C.compatibleComplexChart (e.symm z)))
    (w := C.finiteCoordinate z) ?_
  calc
    C.affineTransitionRepresentative •
        (C.compatibleFiniteCoordinate
          (C.compatibleComplexChart (e.symm z)) : RiemannSphere) =
        C.normalization • C.chart (e.symm z) :=
      C.normalizedChart_eq_affineTransition_at.symm
    _ = (C.finiteCoordinate z : RiemannSphere) :=
      C.finiteCoordinate_eq_normalizedChart_at.symm

end RegularLocusLocalPullbackCoordinateData

/--
The real-projective transition between two selected finite developing branches
holds locally, after changing complex charts.

%%handwave
name:
  Finite developing branches differ locally by a real-projective map
statement:
  For finite branches on overlapping charts, there is R∈PGL₂(ℝ) such that F₂∘τ=R∘F₁ near the overlap point.
proof:
  Compare the local developing-chart agreements at a common lift and substitute their branch germ equalities.
-/
theorem localPullbackCoordinateData_finiteCoordinate_transition_eventuallyEq
    (H : P.PGL2RHolonomyData x₀)
    {e₁ e₂ : OpenPartialHomeomorph X ℂ} {z₁ : ℂ}
    (hz₁ : z₁ ∈ e₁.target) (hz₂ : e₁.symm z₁ ∈ e₂.source)
    (C₁ : H.RegularLocusLocalPullbackCoordinateData e₁ z₁)
    (C₂ : H.RegularLocusLocalPullbackCoordinateData e₂ (e₂ (e₁.symm z₁))) :
    ∃ R : RealProjectiveMobiusRepresentative,
      C₂.finiteCoordinate (e₂ (e₁.symm z₁)) =
          UpperHalfPlane.num R (C₁.finiteCoordinate z₁) /
            UpperHalfPlane.denom R (C₁.finiteCoordinate z₁) ∧
        (fun w : ℂ ↦ C₂.finiteCoordinate (e₂ (e₁.symm w))) =ᶠ[𝓝 z₁]
          (fun w : ℂ ↦
            UpperHalfPlane.num R (C₁.finiteCoordinate w) /
              UpperHalfPlane.denom R (C₁.finiteCoordinate w)) := by
  let z₂ : ℂ := e₂ (e₁.symm z₁)
  have hx₁ : e₁.symm z₁ ∈ C₁.localAgreement.chart.source := by
    simpa [C₁.chart_eq_localAgreement_chart] using C₁.mem_chart_source
  have hx₂_at : e₂.symm z₂ ∈ C₂.localAgreement.chart.source := by
    simpa [z₂, C₂.chart_eq_localAgreement_chart] using C₂.mem_chart_source
  have hx₂ : e₁.symm z₁ ∈ C₂.localAgreement.chart.source := by
    simpa [z₂, e₂.left_inv hz₂] using hx₂_at
  rcases
    H.localAgreement_normalizedChart_transition_realProjective_eventuallyEq_nhds
      C₁.localAgreement C₂.localAgreement hx₁ hx₂ with
    ⟨R, hpoint, hlocal⟩
  refine ⟨R, ?_, ?_⟩
  · have hz₁_eq :
        C₁.localAgreement.normalization •
            C₁.localAgreement.chart (e₁.symm z₁) =
          (C₁.finiteCoordinate z₁ : RiemannSphere) :=
      (C₁.finiteCoordinate_eq_localAgreement_normalizedChart_at).symm
    have hz₂_eq_at :
        C₂.localAgreement.normalization •
            C₂.localAgreement.chart (e₂.symm z₂) =
          (C₂.finiteCoordinate z₂ : RiemannSphere) :=
      (C₂.finiteCoordinate_eq_localAgreement_normalizedChart_at).symm
    have hz₂_eq :
        C₂.localAgreement.normalization •
            C₂.localAgreement.chart (e₁.symm z₁) =
          (C₂.finiteCoordinate z₂ : RiemannSphere) := by
      simpa [z₂, e₂.left_inv hz₂] using hz₂_eq_at
    have hsphere :
        realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
            (C₁.finiteCoordinate z₁ : RiemannSphere) =
          (C₂.finiteCoordinate z₂ : RiemannSphere) := by
      calc
        realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
            (C₁.finiteCoordinate z₁ : RiemannSphere) =
            realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
              (C₁.localAgreement.normalization •
                C₁.localAgreement.chart (e₁.symm z₁)) := by
          rw [← hz₁_eq]
        _ =
            C₂.localAgreement.normalization •
              C₂.localAgreement.chart (e₁.symm z₁) := by
          rw [hpoint]
        _ = (C₂.finiteCoordinate z₂ : RiemannSphere) :=
          hz₂_eq
    have hformula :=
      mobiusFiniteFormula_eq_of_smul_coe_eq_coe
        (realProjectiveMobiusRepresentativeAsMobiusRepresentative R) hsphere
    simpa [z₂, mobiusFiniteFormula, mobiusFiniteNum, mobiusFiniteDenom,
      realProjectiveMobiusRepresentativeAsMobiusRepresentative,
      UpperHalfPlane.num, UpperHalfPlane.denom] using hformula.symm
  · have hsymm : ContinuousAt e₁.symm z₁ :=
      e₁.symm.continuousAt hz₁
    have hτ : ContinuousAt (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁ :=
      (e₂.continuousAt hz₂).comp hsymm
    have hsource₁ : ∀ᶠ w in 𝓝 z₁,
        e₁.symm w ∈ C₁.localAgreement.chart.source :=
      hsymm.preimage_mem_nhds
        (C₁.localAgreement.chart.open_source.mem_nhds hx₁)
    have hsource₂ : ∀ᶠ w in 𝓝 z₁,
        e₁.symm w ∈ C₂.localAgreement.chart.source :=
      hsymm.preimage_mem_nhds
        (C₂.localAgreement.chart.open_source.mem_nhds hx₂)
    have hsource_e₂ : ∀ᶠ w in 𝓝 z₁, e₁.symm w ∈ e₂.source :=
      hsymm.preimage_mem_nhds (e₂.open_source.mem_nhds hz₂)
    have hC₁ :
        ∀ᶠ w in 𝓝 z₁,
          ((C₁.finiteCoordinate w : ℂ) : RiemannSphere) =
            C₁.localAgreement.normalization •
              C₁.localAgreement.chart (e₁.symm w) := by
      filter_upwards [C₁.finiteCoordinate_eventually_eq] with w hw
      simpa [C₁.chart_eq_localAgreement_chart,
        C₁.normalization_eq_localAgreement_normalization] using hw
    have hC₂ :
        ∀ᶠ w in 𝓝 z₁,
          ((C₂.finiteCoordinate (e₂ (e₁.symm w)) : ℂ) : RiemannSphere) =
            C₂.localAgreement.normalization •
              C₂.localAgreement.chart (e₂.symm (e₂ (e₁.symm w))) := by
      exact hτ.eventually (by
        filter_upwards [C₂.finiteCoordinate_eventually_eq] with u hu
        simpa [C₂.chart_eq_localAgreement_chart,
          C₂.normalization_eq_localAgreement_normalization] using hu)
    have hlocal_w :
        ∀ᶠ w in 𝓝 z₁,
          e₁.symm w ∈ C₁.localAgreement.chart.source →
            e₁.symm w ∈ C₂.localAgreement.chart.source →
              C₂.localAgreement.normalization •
                  C₂.localAgreement.chart (e₁.symm w) =
                realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
                  (C₁.localAgreement.normalization •
                    C₁.localAgreement.chart (e₁.symm w)) :=
      hsymm.eventually hlocal
    filter_upwards [hsource₁, hsource₂, hsource_e₂, hC₁, hC₂, hlocal_w] with
      w hw₁ hw₂ hwe₂ hC₁w hC₂w hlocalw
    have hsphere :
        realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
            (C₁.finiteCoordinate w : RiemannSphere) =
          (C₂.finiteCoordinate (e₂ (e₁.symm w)) : RiemannSphere) := by
      calc
        realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
            (C₁.finiteCoordinate w : RiemannSphere) =
            realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
              (C₁.localAgreement.normalization •
                C₁.localAgreement.chart (e₁.symm w)) := by
          rw [hC₁w]
        _ =
            C₂.localAgreement.normalization •
              C₂.localAgreement.chart (e₁.symm w) := by
          rw [hlocalw hw₁ hw₂]
        _ =
            C₂.localAgreement.normalization •
              C₂.localAgreement.chart (e₂.symm (e₂ (e₁.symm w))) := by
          rw [e₂.left_inv hwe₂]
        _ = (C₂.finiteCoordinate (e₂ (e₁.symm w)) : RiemannSphere) :=
          hC₂w.symm
    have hformula :=
      mobiusFiniteFormula_eq_of_smul_coe_eq_coe
        (realProjectiveMobiusRepresentativeAsMobiusRepresentative R) hsphere
    simpa [mobiusFiniteFormula, mobiusFiniteNum, mobiusFiniteDenom,
      realProjectiveMobiusRepresentativeAsMobiusRepresentative,
      UpperHalfPlane.num, UpperHalfPlane.denom] using hformula.symm

/--
The density-cancellation algebra for a real-projective branch change.  Once the
derivative of the second branch, after a coordinate change, is identified with
the derivative of the real projective transition composed with the first branch,
the two pullback-density expressions obey the conformal chart-transition law.

%%handwave
name:
  The derivative chain rule gives the density transition
statement:
  If Poincare density is invariant under R and F₂′τ′=(R∘F₁)′, then the two pullback densities satisfy q₁=q₂|τ′|².
proof:
  Multiply the invariant model-density equality by |F₁′|² and use multiplicativity of squared norms.
-/
theorem localPullbackCoordinateData_pullbackDensity_transition_of_derivative
    (H : P.PGL2RHolonomyData x₀)
    {e₁ e₂ : OpenPartialHomeomorph X ℂ} {z₁ z₂ : ℂ}
    (C₁ : H.RegularLocusLocalPullbackCoordinateData e₁ z₁)
    (C₂ : H.RegularLocusLocalPullbackCoordinateData e₂ z₂)
    (R : RealProjectiveMobiusRepresentative)
    (hDensity :
      poincareDensitySqInChart (C₂.finiteCoordinate z₂) *
          Complex.normSq
            (deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
              (C₁.finiteCoordinate z₁)) =
        poincareDensitySqInChart (C₁.finiteCoordinate z₁))
    (hderiv :
      deriv C₂.finiteCoordinate z₂ *
          deriv (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁ =
        deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
            (C₁.finiteCoordinate z₁) *
          deriv C₁.finiteCoordinate z₁) :
    C₁.pullbackDensity =
      C₂.pullbackDensity *
        Complex.normSq (deriv (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁) := by
  simp only [RegularLocusLocalPullbackCoordinateData.pullbackDensity]
  calc
    poincareDensitySqInChart (C₁.finiteCoordinate z₁) *
        Complex.normSq (deriv C₁.finiteCoordinate z₁) =
        (poincareDensitySqInChart (C₂.finiteCoordinate z₂) *
            Complex.normSq
              (deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
                (C₁.finiteCoordinate z₁))) *
          Complex.normSq (deriv C₁.finiteCoordinate z₁) := by
      rw [hDensity]
    _ =
        poincareDensitySqInChart (C₂.finiteCoordinate z₂) *
          (Complex.normSq
              (deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
                (C₁.finiteCoordinate z₁)) *
            Complex.normSq (deriv C₁.finiteCoordinate z₁)) := by
      ring
    _ =
        poincareDensitySqInChart (C₂.finiteCoordinate z₂) *
          Complex.normSq
            (deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
                (C₁.finiteCoordinate z₁) *
              deriv C₁.finiteCoordinate z₁) := by
      rw [Complex.normSq_mul]
    _ =
        poincareDensitySqInChart (C₂.finiteCoordinate z₂) *
          Complex.normSq
            (deriv C₂.finiteCoordinate z₂ *
              deriv (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁) := by
      rw [← hderiv]
    _ =
        poincareDensitySqInChart (C₂.finiteCoordinate z₂) *
          (Complex.normSq (deriv C₂.finiteCoordinate z₂) *
            Complex.normSq (deriv (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁)) := by
      rw [Complex.normSq_mul]
    _ =
        (poincareDensitySqInChart (C₂.finiteCoordinate z₂) *
          Complex.normSq (deriv C₂.finiteCoordinate z₂)) *
            Complex.normSq (deriv (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁) := by
      ring

/--
An eventual equality of composed finite-coordinate branches gives the derivative
chain rule needed for the density transition.

%%handwave
name:
  Differentiating a branch transition gives its chain rule
statement:
  If F₂∘τ and R∘F₁ agree near z and are differentiable, then F₂′(τ(z))τ′(z)=R′(F₁(z))F₁′(z).
proof:
  Differentiate the germ equality and apply the complex chain rule on both sides.
-/
theorem localPullbackCoordinateData_transition_derivative_of_eventuallyEq
    (H : P.PGL2RHolonomyData x₀)
    {e₁ e₂ : OpenPartialHomeomorph X ℂ} {z₁ : ℂ}
    (C₁ : H.RegularLocusLocalPullbackCoordinateData e₁ z₁)
    (C₂ : H.RegularLocusLocalPullbackCoordinateData e₂ (e₂ (e₁.symm z₁)))
    (R : RealProjectiveMobiusRepresentative)
    (hEq :
      (fun w : ℂ ↦ C₂.finiteCoordinate (e₂ (e₁.symm w))) =ᶠ[𝓝 z₁]
        (fun w : ℂ ↦
          UpperHalfPlane.num R (C₁.finiteCoordinate w) /
            UpperHalfPlane.denom R (C₁.finiteCoordinate w)))
    (hC₁ : DifferentiableAt ℂ C₁.finiteCoordinate z₁)
    (hC₂ : DifferentiableAt ℂ C₂.finiteCoordinate (e₂ (e₁.symm z₁)))
    (hτ : DifferentiableAt ℂ (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁) :
    deriv C₂.finiteCoordinate (e₂ (e₁.symm z₁)) *
        deriv (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁ =
      deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
          (C₁.finiteCoordinate z₁) *
        deriv C₁.finiteCoordinate z₁ := by
  let τ : ℂ → ℂ := fun w ↦ e₂ (e₁.symm w)
  let T : ℂ → ℂ := fun w ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w
  have hT : DifferentiableAt ℂ T (C₁.finiteCoordinate z₁) :=
    (pgl2r_holomorphic_smul_hasDerivAt R C₁.finiteCoordinate_offReal).differentiableAt
  have hleft :
      deriv (fun w : ℂ ↦ C₂.finiteCoordinate (τ w)) z₁ =
        deriv C₂.finiteCoordinate (τ z₁) * deriv τ z₁ := by
    simpa [τ] using deriv_comp z₁ hC₂ hτ
  have hright :
      deriv (fun w : ℂ ↦ T (C₁.finiteCoordinate w)) z₁ =
        deriv T (C₁.finiteCoordinate z₁) * deriv C₁.finiteCoordinate z₁ := by
    simpa [T, Function.comp_def] using deriv_comp z₁ hT hC₁
  calc
    deriv C₂.finiteCoordinate (e₂ (e₁.symm z₁)) *
        deriv (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁ =
        deriv (fun w : ℂ ↦ C₂.finiteCoordinate (τ w)) z₁ := by
      simpa [τ] using hleft.symm
    _ =
        deriv (fun w : ℂ ↦ T (C₁.finiteCoordinate w)) z₁ := by
      simpa [T, τ] using hEq.deriv_eq
    _ =
        deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
            (C₁.finiteCoordinate z₁) *
          deriv C₁.finiteCoordinate z₁ := by
      simpa [T] using hright

/-- Complex coordinate changes between surface charts are differentiable.

%%handwave
name:
  Holomorphicity of a complex chart transition
statement:
  On a complex-chart overlap, the coordinate change e′∘e⁻¹ is complex differentiable.
proof:
  Both chart maps are holomorphic in the complex manifold atlas, and differentiability is preserved by composition.
-/
theorem complexChartTransition_differentiableAt
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    DifferentiableAt ℂ (fun w : ℂ ↦ e' (e.symm w)) z := by
  have hsymm_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm z :=
    mdifferentiableAt_atlas_symm he hz
  have hchart_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e' (e.symm z) :=
    mdifferentiableAt_atlas he' hz'
  exact (hchart_mdiff.comp z hsymm_mdiff).differentiableAt

/-- Complex coordinate changes between surface charts are smooth.

%%handwave
name:
  Smoothness of a complex chart transition
statement:
  On a complex-chart overlap, the coordinate change e′∘e⁻¹ is complex C∞.
proof:
  Charts in the maximal complex atlas are smooth, and their composition is smooth.
-/
theorem complexChartTransition_contDiffAt
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    ContDiffAt ℂ ⊤ (fun w : ℂ ↦ e' (e.symm w)) z := by
  have hsymm_mdiff :
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ⊤ e.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) he) hz
  have hchart_mdiff :
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ⊤ e' (e.symm z) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) he') hz'
  exact (hchart_mdiff.comp z hsymm_mdiff).contDiffAt

/-- Complex coordinate changes between surface charts have nonzero derivative.

%%handwave
name:
  Nondegeneracy of a complex chart transition
statement:
  The derivative of a complex coordinate change e′∘e⁻¹ is nonzero at every overlap point.
proof:
  Compose with the inverse transition to obtain the identity; differentiating gives σ′τ′=1.
-/
theorem complexChartTransition_deriv_ne_zero
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    deriv (fun w : ℂ ↦ e' (e.symm w)) z ≠ 0 := by
  let τ : ℂ → ℂ := fun w ↦ e' (e.symm w)
  let σ : ℂ → ℂ := fun w ↦ e (e'.symm w)
  let z' : ℂ := e' (e.symm z)
  have hz'_target : z' ∈ e'.target := e'.map_source hz'
  have hz'_source_for_e : e'.symm z' ∈ e.source := by
    simpa [z', e'.left_inv hz'] using e.map_target hz
  have hτ_diff : DifferentiableAt ℂ τ z :=
    complexChartTransition_differentiableAt e he e' he' hz hz'
  have hσ_diff : DifferentiableAt ℂ σ z' :=
    complexChartTransition_differentiableAt e' he' e he hz'_target hz'_source_for_e
  have hcomp_eventually :
      (fun w : ℂ ↦ σ (τ w)) =ᶠ[𝓝 z] fun w : ℂ ↦ w := by
    have htarget : ∀ᶠ w in 𝓝 z, w ∈ e.target :=
      e.open_target.mem_nhds hz
    have hsource' : ∀ᶠ w in 𝓝 z, e.symm w ∈ e'.source :=
      (e.symm.continuousAt hz).preimage_mem_nhds (e'.open_source.mem_nhds hz')
    filter_upwards [htarget, hsource'] with w hw_target hw_source'
    dsimp [σ, τ]
    rw [e'.left_inv hw_source']
    exact e.right_inv hw_target
  have hcomp_deriv :
      deriv (fun w : ℂ ↦ σ (τ w)) z = 1 := by
    simpa using hcomp_eventually.deriv_eq
  have hchain :
      deriv (fun w : ℂ ↦ σ (τ w)) z =
        deriv σ (τ z) * deriv τ z := by
    simpa [τ, Function.comp_def] using deriv_comp z hσ_diff hτ_diff
  intro hzero
  have : (1 : ℂ) = 0 := by
    rw [← hcomp_deriv, hchain, hzero, mul_zero]
  exact one_ne_zero this

/--
An eventual equality of composed finite-coordinate branches gives the derivative
chain rule needed for the density transition; the chart-transition derivative
is supplied by the complex atlas.

%%handwave
name:
  The atlas supplies the branch-transition derivative identity
statement:
  If F₂∘τ=R∘F₁ locally for branches on overlapping complex charts, then F₂′(τ(z))τ′(z)=R′(F₁(z))F₁′(z).
proof:
  The complex atlas makes τ differentiable; differentiate the branch germ equality.
-/
theorem localPullbackCoordinateData_transition_derivative_of_eventuallyEq_chartTransition
    (H : P.PGL2RHolonomyData x₀)
    {e₁ e₂ : OpenPartialHomeomorph X ℂ} {z₁ : ℂ}
    (he₁ : e₁ ∈ atlas ℂ X) (he₂ : e₂ ∈ atlas ℂ X)
    (hz₁ : z₁ ∈ e₁.target) (hz₂ : e₁.symm z₁ ∈ e₂.source)
    (C₁ : H.RegularLocusLocalPullbackCoordinateData e₁ z₁)
    (C₂ : H.RegularLocusLocalPullbackCoordinateData e₂ (e₂ (e₁.symm z₁)))
    (R : RealProjectiveMobiusRepresentative)
    (hEq :
      (fun w : ℂ ↦ C₂.finiteCoordinate (e₂ (e₁.symm w))) =ᶠ[𝓝 z₁]
        (fun w : ℂ ↦
          UpperHalfPlane.num R (C₁.finiteCoordinate w) /
            UpperHalfPlane.denom R (C₁.finiteCoordinate w)))
    (hC₁ : DifferentiableAt ℂ C₁.finiteCoordinate z₁)
    (hC₂ : DifferentiableAt ℂ C₂.finiteCoordinate (e₂ (e₁.symm z₁))) :
    deriv C₂.finiteCoordinate (e₂ (e₁.symm z₁)) *
        deriv (fun w : ℂ ↦ e₂ (e₁.symm w)) z₁ =
      deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
          (C₁.finiteCoordinate z₁) *
        deriv C₁.finiteCoordinate z₁ :=
  H.localPullbackCoordinateData_transition_derivative_of_eventuallyEq
    C₁ C₂ R hEq hC₁ hC₂
    (complexChartTransition_differentiableAt e₁ he₁ e₂ he₂ hz₁ hz₂)

namespace RegularLocusLocalPullbackCoordinateData

variable {H : P.PGL2RHolonomyData x₀}
    {e : OpenPartialHomeomorph X ℂ} {z : ℂ}

/--
Locally, a selected finite developing branch is the affine formula for a
complex Mobius transformation applied to the projective chart's compatible
finite coordinate.

%%handwave
name:
  Local affine formula for a finite developing branch
statement:
  Near its regular base point, F equals the affine Möbius transition applied to the compatible finite projective coordinate.
proof:
  Rewrite the local normalized projective-chart agreement using the compatible coordinate and pass to affine coordinates away from the pole.
-/
theorem finiteCoordinate_eventually_eq_mobiusFiniteFormula_compatible
    (C : H.RegularLocusLocalPullbackCoordinateData e z) (hz : z ∈ e.target) :
    C.finiteCoordinate =ᶠ[𝓝 z]
      fun w : ℂ ↦
        mobiusFiniteFormula C.affineTransitionRepresentative
          (C.compatibleFiniteCoordinate (C.compatibleComplexChart (e.symm w))) := by
  have hchart : ∀ᶠ w in 𝓝 z, e.symm w ∈ C.chart.source :=
    (e.symm.continuousAt hz).preimage_mem_nhds
      (C.chart.open_source.mem_nhds C.mem_chart_source)
  filter_upwards [C.finiteCoordinate_eventually_eq, hchart] with w hCw hxw
  have hxec : e.symm w ∈ C.compatibleComplexChart.source :=
    C.compatibleComplexChartData.projective_source_subset_complex_source hxw
  have hsource :
      C.compatibleComplexChart (e.symm w) ∈
        (C.compatibleComplexChart.symm.trans C.chart).source := by
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · simpa [OpenPartialHomeomorph.symm_source] using
        C.compatibleComplexChart.map_source hxec
    · simpa [C.compatibleComplexChart.left_inv hxec] using hxw
  have hB :=
    C.compatibleComplexChartData.compatibility.finiteCoordinate_eq
      (C.compatibleComplexChart (e.symm w)) hsource
  rw [OpenPartialHomeomorph.trans_apply] at hB
  have hleft :
      C.compatibleComplexChartData.complexChart.symm
          (C.compatibleComplexChart (e.symm w)) =
        e.symm w := by
    simpa [compatibleComplexChart] using C.compatibleComplexChart.left_inv hxec
  rw [hleft] at hB
  let B : MobiusRepresentative :=
    C.compatibleComplexChartData.compatibility.representative
  let q : RiemannSphere := C.chart (e.symm w)
  let u : RiemannSphere :=
    (C.compatibleFiniteCoordinate
      (C.compatibleComplexChart (e.symm w)) : RiemannSphere)
  have hB' : B • q = u := by
    simpa [B, q, u, compatibleFiniteCoordinate] using hB
  have hcancel : B⁻¹ • (B • q) = q := by
    rw [← mul_smul]
    simp
  have hA :
      C.affineTransitionRepresentative •
          (C.compatibleFiniteCoordinate
            (C.compatibleComplexChart (e.symm w)) : RiemannSphere) =
        (C.finiteCoordinate w : RiemannSphere) := by
    change (C.normalization * B⁻¹) • u =
      (C.finiteCoordinate w : RiemannSphere)
    calc
      (C.normalization * B⁻¹) • u =
          C.normalization • (B⁻¹ • u) := by
        rw [mul_smul]
      _ = C.normalization • (B⁻¹ • (B • q)) := by
        rw [← hB']
      _ = C.normalization • q := by
        rw [hcancel]
      _ = (C.finiteCoordinate w : RiemannSphere) := by
        simpa [q] using hCw.symm
  exact (mobiusFiniteFormula_eq_of_smul_coe_eq_coe
    C.affineTransitionRepresentative hA).symm

/-- The selected finite developing branch is holomorphic at its base point.

%%handwave
name:
  Holomorphicity of the selected finite branch
statement:
  The selected normalized finite developing branch is complex differentiable at its regular base point.
proof:
  Locally it composes a holomorphic chart transition, compatible finite coordinate, and pole-free Möbius map.
-/
theorem finiteCoordinate_differentiableAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    DifferentiableAt ℂ C.finiteCoordinate z := by
  let τ : ℂ → ℂ := fun w ↦ C.compatibleComplexChart (e.symm w)
  have hτ : DifferentiableAt ℂ τ z :=
    complexChartTransition_differentiableAt e he C.compatibleComplexChart
      C.compatibleComplexChartData.complexChart_mem_atlas hz
      C.mem_compatibleComplexChart_source
  have hF : DifferentiableAt ℂ C.compatibleFiniteCoordinate (τ z) := by
    simpa [τ] using C.compatibleFiniteCoordinate_differentiableAt
  have hT : DifferentiableAt ℂ
      (mobiusFiniteFormula C.affineTransitionRepresentative)
      (C.compatibleFiniteCoordinate (τ z)) := by
    simpa [τ] using
      mobiusFiniteFormula_differentiableAt C.affineTransitionRepresentative
        C.affineTransition_denominator_ne_zero_at
  have hcomp : DifferentiableAt ℂ
      (fun w : ℂ ↦
        mobiusFiniteFormula C.affineTransitionRepresentative
          (C.compatibleFiniteCoordinate (τ w))) z :=
    by
      simpa [Function.comp_def] using hT.comp z (hF.comp z hτ)
  exact hcomp.congr_of_eventuallyEq
    (C.finiteCoordinate_eventually_eq_mobiusFiniteFormula_compatible hz)

/-- The selected finite developing branch is locally biholomorphic at its base point.

%%handwave
name:
  Local univalence of the selected finite branch
statement:
  The selected normalized finite developing branch has nonzero derivative at its regular base point.
proof:
  Differentiate its three-factor local expression; every factor has nonzero derivative.
-/
theorem finiteCoordinate_deriv_ne_zero
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    deriv C.finiteCoordinate z ≠ 0 := by
  let τ : ℂ → ℂ := fun w ↦ C.compatibleComplexChart (e.symm w)
  have hτ : DifferentiableAt ℂ τ z :=
    complexChartTransition_differentiableAt e he C.compatibleComplexChart
      C.compatibleComplexChartData.complexChart_mem_atlas hz
      C.mem_compatibleComplexChart_source
  have hτ_ne : deriv τ z ≠ 0 :=
    complexChartTransition_deriv_ne_zero e he C.compatibleComplexChart
      C.compatibleComplexChartData.complexChart_mem_atlas hz
      C.mem_compatibleComplexChart_source
  have hF : DifferentiableAt ℂ C.compatibleFiniteCoordinate (τ z) := by
    simpa [τ] using C.compatibleFiniteCoordinate_differentiableAt
  have hF_ne :
      deriv C.compatibleFiniteCoordinate (τ z) ≠ 0 := by
    simpa [τ] using C.compatibleFiniteCoordinate_deriv_ne_zero
  have hT : DifferentiableAt ℂ
      (mobiusFiniteFormula C.affineTransitionRepresentative)
      (C.compatibleFiniteCoordinate (τ z)) := by
    simpa [τ] using
      mobiusFiniteFormula_differentiableAt C.affineTransitionRepresentative
        C.affineTransition_denominator_ne_zero_at
  have hT_ne :
      deriv (mobiusFiniteFormula C.affineTransitionRepresentative)
        (C.compatibleFiniteCoordinate (τ z)) ≠ 0 := by
    simpa [τ] using
      mobiusFiniteFormula_deriv_ne_zero C.affineTransitionRepresentative
        C.affineTransition_denominator_ne_zero_at
  have hFcomp : DifferentiableAt ℂ
      (fun w : ℂ ↦ C.compatibleFiniteCoordinate (τ w)) z :=
    hF.comp z hτ
  have hFcomp_deriv :
      deriv (fun w : ℂ ↦ C.compatibleFiniteCoordinate (τ w)) z =
        deriv C.compatibleFiniteCoordinate (τ z) * deriv τ z := by
    simpa [τ, Function.comp_def] using deriv_comp z hF hτ
  have hcomp_deriv :
      deriv
          (fun w : ℂ ↦
            mobiusFiniteFormula C.affineTransitionRepresentative
              (C.compatibleFiniteCoordinate (τ w))) z =
        deriv (mobiusFiniteFormula C.affineTransitionRepresentative)
            (C.compatibleFiniteCoordinate (τ z)) *
          deriv (fun w : ℂ ↦ C.compatibleFiniteCoordinate (τ w)) z := by
    simpa [Function.comp_def] using deriv_comp z hT hFcomp
  have hEq := C.finiteCoordinate_eventually_eq_mobiusFiniteFormula_compatible hz
  rw [hEq.deriv_eq, hcomp_deriv, hFcomp_deriv]
  exact mul_ne_zero hT_ne (mul_ne_zero hF_ne hτ_ne)

/-- The selected finite developing branch is complex-smooth at its base point.

%%handwave
name:
  Complex smoothness of the selected finite branch
statement:
  The selected normalized finite developing branch is complex C∞ at its regular base point.
proof:
  Its local expression is a composition of smooth holomorphic coordinate and Möbius maps.
-/
theorem finiteCoordinate_contDiffAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    ContDiffAt ℂ ⊤ C.finiteCoordinate z := by
  let τ : ℂ → ℂ := fun w ↦ C.compatibleComplexChart (e.symm w)
  have hτ : ContDiffAt ℂ ⊤ τ z :=
    complexChartTransition_contDiffAt e he C.compatibleComplexChart
      C.compatibleComplexChartData.complexChart_mem_atlas hz
      C.mem_compatibleComplexChart_source
  have hF : ContDiffAt ℂ ⊤ C.compatibleFiniteCoordinate (τ z) := by
    simpa [τ] using C.compatibleFiniteCoordinate_contDiffAt
  have hT : ContDiffAt ℂ ⊤
      (mobiusFiniteFormula C.affineTransitionRepresentative)
      (C.compatibleFiniteCoordinate (τ z)) := by
    simpa [τ] using
      mobiusFiniteFormula_contDiffAt C.affineTransitionRepresentative
        C.affineTransition_denominator_ne_zero_at
  have hcomp : ContDiffAt ℂ ⊤
      (fun w : ℂ ↦
        mobiusFiniteFormula C.affineTransitionRepresentative
          (C.compatibleFiniteCoordinate (τ w))) z :=
    by
      simpa [Function.comp_def] using hT.comp z (hF.comp z hτ)
  exact hcomp.congr_of_eventuallyEq
    (C.finiteCoordinate_eventually_eq_mobiusFiniteFormula_compatible hz)

/-- The derivative of the selected finite developing branch is complex-smooth.

%%handwave
name:
  Complex smoothness of the selected branch derivative
statement:
  The derivative F′ of the selected finite developing branch is complex C∞ at its regular base point.
proof:
  A locally holomorphic C∞ branch has a holomorphic, hence smooth, derivative.
-/
theorem finiteCoordinate_deriv_contDiffAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    ContDiffAt ℂ ⊤ (fun w : ℂ ↦ deriv C.finiteCoordinate w) z := by
  have hF : ContDiffAt ℂ ⊤ C.finiteCoordinate z :=
    C.finiteCoordinate_contDiffAt he hz
  simpa using hF.derivWithin (m := ⊤) (by simp)

/--
Restrict a complex-smooth map between complex planes to a real-smooth map.

%%handwave
name:
  Complex smoothness implies real smoothness
statement:
  A complex-valued function that is Cⁿ over ℂ at a point is Cⁿ over ℝ at that point.
proof:
  Restrict each complex Fréchet derivative to the underlying real normed spaces; scalar restriction preserves the required differentiability tower.
-/
theorem contDiffAt_complex_to_real {f : ℂ → ℂ} {z : ℂ}
    (h : ContDiffAt ℂ ⊤ f z) :
    ContDiffAt ℝ ⊤ f z :=
  @ContDiffAt.restrict_scalars ℝ inferInstance ℂ inferInstance
    inferInstance ℂ inferInstance inferInstance f z ⊤ ℂ inferInstance
    inferInstance inferInstance
    (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ) inferInstance
    (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ) h

/--
The selected finite developing branch is real-smooth at its base point.

%%handwave
name:
  Real smoothness of a finite developing coordinate
statement:
  A holomorphic finite normalized developing branch F is C∞ as a map ℂ → ℂ of real manifolds at every regular base point.
proof:
  The branch is complex analytic at the point, hence complex C∞, and restriction of scalars gives real C∞ regularity.
-/
theorem finiteCoordinate_contDiffAt_real
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    ContDiffAt ℝ ⊤ C.finiteCoordinate z :=
  contDiffAt_complex_to_real (C.finiteCoordinate_contDiffAt he hz)

/--
The derivative of the selected finite developing branch is real-smooth.

%%handwave
name:
  Real smoothness of the derivative branch
statement:
  The complex derivative F′ of a finite normalized developing branch is C∞ as a real map near every regular base point.
proof:
  The derivative is complex analytic near the point; convert its complex C∞ regularity to real C∞ regularity.
-/
theorem finiteCoordinate_deriv_contDiffAt_real
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    ContDiffAt ℝ ⊤ (fun w : ℂ ↦ deriv C.finiteCoordinate w) z :=
  contDiffAt_complex_to_real (C.finiteCoordinate_deriv_contDiffAt he hz)

/--
The local pullback-density branch is positive at its base point.

%%handwave
name:
  Positivity of a finite branch pullback density
statement:
  For an off-real locally univalent branch F, the squared pullback density ρ²(z)=|F′(z)|²/(Im F(z))² is strictly positive.
proof:
  The denominator is positive because Im F(z) ≠ 0, and the numerator is positive because F′(z) ≠ 0.
-/
theorem pullbackDensityFunction_pos
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    0 < C.pullbackDensityFunction z := by
  rw [pullbackDensityFunction_apply]
  exact mul_pos
    (poincareDensitySqInChart_pos_of_im_ne_zero C.finiteCoordinate_offReal)
    (Complex.normSq_pos.mpr (C.finiteCoordinate_deriv_ne_zero he hz))

/--
Near the base point, the local pullback log-density is represented by the
usual expression `log |F'| - log |Im F|`.

%%handwave
name:
  Local logarithmic pullback density formula
statement:
  Near a regular base point of an off-real locally univalent branch F, the logarithmic density ½ log ρ² agrees with log|F′| − log|Im F|.
proof:
  Nonvanishing of F′ and Im F persists locally by continuity. Apply the pointwise logarithm identity throughout that neighborhood.
-/
theorem pullbackLogDensityFunction_eventuallyEq_log_deriv_sub_log_im
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    C.pullbackLogDensityFunction =ᶠ[𝓝 z] C.pullbackLogDensityExpression := by
  have hFcont : ContinuousAt C.finiteCoordinate z :=
    (C.finiteCoordinate_contDiffAt_real he hz).continuousAt
  have hImcont :
      ContinuousAt (fun w : ℂ ↦ (C.finiteCoordinate w).im) z :=
    Complex.continuous_im.continuousAt.comp hFcont
  have hIm_ne :
      ∀ᶠ w in 𝓝 z, (C.finiteCoordinate w).im ≠ 0 :=
    hImcont.preimage_mem_nhds
      (isClosed_singleton.isOpen_compl.mem_nhds C.finiteCoordinate_offReal)
  have hDerivCont :
      ContinuousAt (fun w : ℂ ↦ deriv C.finiteCoordinate w) z :=
    (C.finiteCoordinate_deriv_contDiffAt_real he hz).continuousAt
  have hDeriv_ne :
      ∀ᶠ w in 𝓝 z, deriv C.finiteCoordinate w ≠ 0 :=
    hDerivCont.preimage_mem_nhds
      (isClosed_singleton.isOpen_compl.mem_nhds
        (C.finiteCoordinate_deriv_ne_zero he hz))
  filter_upwards [hIm_ne, hDeriv_ne] with w him_ne hderiv_ne
  have hden_ne : (((C.finiteCoordinate w).im ^ 2)⁻¹ : ℝ) ≠ 0 :=
    inv_ne_zero (pow_ne_zero 2 him_ne)
  have hnorm_ne : Complex.normSq (deriv C.finiteCoordinate w) ≠ 0 := by
    exact (Complex.normSq_pos.mpr hderiv_ne).ne'
  rw [pullbackLogDensityFunction, logDensityFromDensitySq,
    pullbackDensityFunction_apply, poincareDensitySqInChart]
  rw [Real.log_mul hden_ne hnorm_ne, Real.log_inv, Real.log_pow]
  unfold pullbackLogDensityExpression pullbackLogDerivativeTerm
    pullbackLogImaginaryTerm
  simp [Pi.sub_apply]
  ring_nf

/--
The derivative term in the explicit log-density formula is real `C^2`.

%%handwave
name:
  Smoothness of the logarithmic derivative term
statement:
  If F is holomorphic and locally univalent near z, then log|F′| is C∞ as a real-valued function at z.
proof:
  The holomorphic derivative F′ is smooth and nonzero near z; complex norm and the real logarithm are smooth away from zero.
-/
theorem pullbackLogDerivativeTerm_contDiffAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    ContDiffAt ℝ 2 C.pullbackLogDerivativeTerm z := by
  have hDeriv :
      ContDiffAt ℝ ⊤ (fun w : ℂ ↦ deriv C.finiteCoordinate w) z :=
    C.finiteCoordinate_deriv_contDiffAt_real he hz
  have hre :
      ContDiffAt ℝ ⊤
        (fun w : ℂ ↦ (deriv C.finiteCoordinate w).re) z := by
    have hRe : ContDiff ℝ ⊤ (Complex.reCLM : ℂ → ℝ) :=
      (Complex.reCLM : ℂ →L[ℝ] ℝ).contDiff (𝕜 := ℝ) (n := ⊤)
    exact hRe.contDiffAt.comp z hDeriv
  have him :
      ContDiffAt ℝ ⊤
        (fun w : ℂ ↦ (deriv C.finiteCoordinate w).im) z := by
    have hIm : ContDiff ℝ ⊤ (Complex.imCLM : ℂ → ℝ) :=
      (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff (𝕜 := ℝ) (n := ⊤)
    exact hIm.contDiffAt.comp z hDeriv
  have hnorm :
      ContDiffAt ℝ ⊤
        (fun w : ℂ ↦ Complex.normSq (deriv C.finiteCoordinate w)) z := by
    simpa [Complex.normSq_apply, pow_two] using (hre.pow 2).add (him.pow 2)
  have hnorm_ne : Complex.normSq (deriv C.finiteCoordinate z) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (C.finiteCoordinate_deriv_ne_zero he hz)).ne'
  exact ((hnorm.log hnorm_ne).div_const 2).of_le (by norm_num)

/--
The derivative term is harmonic: locally it is `log |F'|`, with `F'`
nonvanishing and analytic.

%%handwave
name:
  Harmonicity of the logarithmic derivative term
statement:
  If F is holomorphic and locally univalent near z, then log|F′| is harmonic at z.
proof:
  On a neighborhood where F′ has no zeros, F′ admits a local holomorphic logarithm; log|F′| is its real part and is therefore harmonic.
-/
theorem pullbackLogDerivativeTerm_harmonicAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    InnerProductSpace.HarmonicAt C.pullbackLogDerivativeTerm z := by
  let G : ℂ → ℂ := fun w ↦ deriv C.finiteCoordinate w
  have hG_analytic : AnalyticAt ℂ G z :=
    analyticAt_of_contDiffAt_top_complex
      (C.finiteCoordinate_deriv_contDiffAt he hz)
  have hG_ne : G z ≠ 0 :=
    C.finiteCoordinate_deriv_ne_zero he hz
  have hH : InnerProductSpace.HarmonicAt (fun w : ℂ ↦ Real.log ‖G w‖) z :=
    hG_analytic.harmonicAt_log_norm hG_ne
  have hEq :
      C.pullbackLogDerivativeTerm =ᶠ[𝓝 z]
        fun w : ℂ ↦ Real.log ‖G w‖ := by
    filter_upwards with w
    change Real.log (Complex.normSq (G w)) / 2 = Real.log ‖G w‖
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg (G w))]
  exact (InnerProductSpace.harmonicAt_congr_nhds hEq).2 hH

/--
The derivative term has zero Laplacian at the base point.

%%handwave
name:
  The logarithmic derivative term has zero Laplacian
statement:
  For a holomorphic locally univalent branch F, Δ log|F′|(z)=0 at every regular base point.
proof:
  Harmonicity of log|F′| is precisely the vanishing of its real Laplacian.
-/
theorem pullbackLogDerivativeTerm_laplacian_eq_zero
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    Laplacian.laplacian C.pullbackLogDerivativeTerm z = 0 := by
  have hH := C.pullbackLogDerivativeTerm_harmonicAt he hz
  simpa using hH.2.self_of_nhds

/--
The imaginary-coordinate term in the explicit log-density formula is real `C^2`.

%%handwave
name:
  Smoothness of the logarithmic height term
statement:
  If Im F(z) ≠ 0 for a holomorphic branch F, then log|Im F| is C∞ at z.
proof:
  The imaginary part of F is smooth and remains nonzero near z, while t ↦ log|t| is smooth away from zero.
-/
theorem pullbackLogImaginaryTerm_contDiffAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    ContDiffAt ℝ 2 C.pullbackLogImaginaryTerm z := by
  have hF :
      ContDiffAt ℝ ⊤ C.finiteCoordinate z :=
    C.finiteCoordinate_contDiffAt_real he hz
  have him :
      ContDiffAt ℝ ⊤
        (fun w : ℂ ↦ (C.finiteCoordinate w).im) z := by
    have hIm : ContDiff ℝ ⊤ (Complex.imCLM : ℂ → ℝ) :=
      (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff (𝕜 := ℝ) (n := ⊤)
    exact hIm.contDiffAt.comp z hF
  exact (him.log C.finiteCoordinate_offReal).of_le (by norm_num)

/--
The imaginary-coordinate term contributes exactly the negative of the pulled
back hyperbolic density to the local Laplacian.

%%handwave
name:
  Laplacian of the logarithmic height
statement:
  For a holomorphic locally univalent branch F with Im F(z) ≠ 0, Δ log|Im F|(z)=−|F′(z)|²/(Im F(z))².
proof:
  Compute the first Wirtinger derivative of log|Im F| and differentiate anti-holomorphically; holomorphicity of F gives one quarter of the stated negative density, and Δ=4∂̄∂.
-/
theorem pullbackLogImaginaryTerm_laplacian_eq_neg_pullbackDensityFunction
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    Laplacian.laplacian C.pullbackLogImaginaryTerm z =
      - C.pullbackDensityFunction z := by
  let F : ℂ → ℂ := C.finiteCoordinate
  let F₁ : ℂ → ℂ := fun w ↦ deriv C.finiteCoordinate w
  have hF_smooth : ContDiffAt ℂ ⊤ F z := by
    simpa [F] using C.finiteCoordinate_contDiffAt he hz
  have hF_ev : ∀ᶠ w in 𝓝 z, HasDerivAt F (F₁ w) w := by
    filter_upwards [hF_smooth.eventually (by simp)] with w hw
    exact (hw.differentiableAt (by simp)).hasDerivAt
  have hFz : HasDerivAt F (F₁ z) z := by
    exact (hF_smooth.differentiableAt (by simp)).hasDerivAt
  have hF₁_smooth : ContDiffAt ℂ ⊤ F₁ z := by
    simpa [F₁] using C.finiteCoordinate_deriv_contDiffAt he hz
  have hF₁z : HasDerivAt F₁ (deriv F₁ z) z := by
    exact (hF₁_smooth.differentiableAt (by simp)).hasDerivAt
  have hbridge :=
    frechetDBar_frechetDZ_complex_ofReal_eq_laplacian
      (u := C.pullbackLogImaginaryTerm) (z := z)
      (C.pullbackLogImaginaryTerm_contDiffAt he hz)
  have hmix :
      frechetDBarValue
          (fun w ↦ frechetDZValue (fun t ↦ (C.pullbackLogImaginaryTerm t : ℂ)) w) z =
        - (Complex.normSq (deriv C.finiteCoordinate z) : ℂ) /
          (4 * ((((C.finiteCoordinate z).im : ℝ) : ℂ) ^ 2)) := by
    simpa [pullbackLogImaginaryTerm, F, F₁] using
      frechetDBar_frechetDZ_complex_ofReal_log_im_of_hasDerivAt
        (F := F) (F₁ := F₁) hF_ev hFz hF₁z C.finiteCoordinate_offReal
  have hy_ne : (((C.finiteCoordinate z).im : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast C.finiteCoordinate_offReal
  have hcomplex :
      (Laplacian.laplacian C.pullbackLogImaginaryTerm z : ℂ) =
        - (Complex.normSq (deriv C.finiteCoordinate z) : ℂ) /
          ((((C.finiteCoordinate z).im : ℝ) : ℂ) ^ 2) := by
    calc
      (Laplacian.laplacian C.pullbackLogImaginaryTerm z : ℂ) =
          (4 : ℂ) *
            ((1 / 4 : ℂ) *
              (Laplacian.laplacian C.pullbackLogImaginaryTerm z : ℂ)) := by ring
      _ = (4 : ℂ) *
          (- (Complex.normSq (deriv C.finiteCoordinate z) : ℂ) /
            (4 * ((((C.finiteCoordinate z).im : ℝ) : ℂ) ^ 2))) := by
            rw [← hbridge]
            exact congrArg (fun a : ℂ ↦ (4 : ℂ) * a) hmix
      _ = - (Complex.normSq (deriv C.finiteCoordinate z) : ℂ) /
          ((((C.finiteCoordinate z).im : ℝ) : ℂ) ^ 2) := by
            field_simp [hy_ne]
  apply Complex.ofReal_injective
  rw [hcomplex]
  rw [pullbackDensityFunction_apply, poincareDensitySqInChart]
  rw [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  field_simp [hy_ne]

/--
The Laplacian of the explicit log-density expression splits into the
derivative and imaginary-coordinate contributions.

%%handwave
name:
  Laplacian of the split logarithmic density
statement:
  At a regular point, Δ(log|F′|−log|Im F|)=Δ log|F′|−Δ log|Im F|.
proof:
  Both terms are twice differentiable there, so linearity of the Laplacian applies to their difference.
-/
theorem pullbackLogDensityExpression_laplacian_sub
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    Laplacian.laplacian C.pullbackLogDensityExpression z =
      Laplacian.laplacian C.pullbackLogDerivativeTerm z -
        Laplacian.laplacian C.pullbackLogImaginaryTerm z := by
  have hD : ContDiffAt ℝ 2 C.pullbackLogDerivativeTerm z :=
    C.pullbackLogDerivativeTerm_contDiffAt he hz
  have hI : ContDiffAt ℝ 2 C.pullbackLogImaginaryTerm z :=
    C.pullbackLogImaginaryTerm_contDiffAt he hz
  simpa [pullbackLogDensityExpression] using hD.laplacian_sub hI

/--
The two expected local Laplacian computations imply the explicit Liouville
calculation for the pulled-back hyperbolic density.

%%handwave
name:
  The split Laplacian gives the pullback Liouville identity
statement:
  If Δ log|F′|=0 and Δ log|Im F|=−ρ², then Δ(log|F′|−log|Im F|)=ρ².
proof:
  Apply linearity of the Laplacian to the difference and substitute the two identities.
-/
theorem pullbackDensityFunction_laplacian_logDensityExpression_of_split
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target)
    (hDerivative :
      Laplacian.laplacian C.pullbackLogDerivativeTerm z = 0)
    (hImaginary :
      Laplacian.laplacian C.pullbackLogImaginaryTerm z =
        - C.pullbackDensityFunction z) :
    Laplacian.laplacian C.pullbackLogDensityExpression z =
      C.pullbackDensityFunction z := by
  rw [C.pullbackLogDensityExpression_laplacian_sub he hz,
    hDerivative, hImaginary]
  ring

/--
After the derivative term is known to be harmonic, the imaginary-coordinate
Laplacian alone gives the explicit Liouville calculation.

%%handwave
name:
  The height calculation gives the pullback Liouville identity
statement:
  For a holomorphic locally univalent off-real branch F, the identity Δ log|Im F|=−ρ² implies Δ(log|F′|−log|Im F|)=ρ².
proof:
  The derivative term log|F′| is harmonic, so combine its zero Laplacian with the assumed height-term formula.
-/
theorem pullbackDensityFunction_laplacian_logDensityExpression_of_imaginary
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target)
    (hImaginary :
      Laplacian.laplacian C.pullbackLogImaginaryTerm z =
        - C.pullbackDensityFunction z) :
    Laplacian.laplacian C.pullbackLogDensityExpression z =
      C.pullbackDensityFunction z :=
  C.pullbackDensityFunction_laplacian_logDensityExpression_of_split he hz
    (C.pullbackLogDerivativeTerm_laplacian_eq_zero he hz) hImaginary

/--
%%handwave
name:
  Liouville equation for a local Poincaré pullback
statement:
  Let $F$ be a finite local developing branch with
  $\operatorname{Im}F(z)\ne0$, and set
  \[
    \rho(w)=\frac{|F'(w)|^2}{(\operatorname{Im}F(w))^2},\qquad
    v(w)=\log|F'(w)|-\log|\operatorname{Im}F(w)|.
  \]
  If $\Delta v(z)=\rho(z)$, then
  $\Delta\bigl(\tfrac12\log\rho\bigr)(z)=\rho(z)$.
proof:
  Near $z$, nonvanishing of $F'$ and $\operatorname{Im}F$ gives
  $\tfrac12\log\rho=v$. The Laplacian depends only on the germ, so the assumed
  identity for $v$ is the Liouville equation for $\rho$.
-/
theorem pullbackDensityFunction_liouville_of_laplacian_logDensityExpression
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target)
    (hL :
      Laplacian.laplacian C.pullbackLogDensityExpression z =
        C.pullbackDensityFunction z) :
    Laplacian.laplacian (logDensityFromDensitySq C.pullbackDensityFunction) z =
      C.pullbackDensityFunction z := by
  have hEq :
      C.pullbackLogDensityFunction =ᶠ[𝓝 z] C.pullbackLogDensityExpression :=
    C.pullbackLogDensityFunction_eventuallyEq_log_deriv_sub_log_im he hz
  have hlap :
      Laplacian.laplacian C.pullbackLogDensityFunction z =
        Laplacian.laplacian C.pullbackLogDensityExpression z := by
    rw [(InnerProductSpace.laplacian_congr_nhds hEq).eq_of_nhds]
  change Laplacian.laplacian C.pullbackLogDensityFunction z =
    C.pullbackDensityFunction z
  rw [hlap]
  exact hL

/--
Smoothness of a finite branch and of its complex derivative imply smoothness
of the squared pullback density represented by that branch.

%%handwave
name:
  Smoothness of the Poincare pullback density
statement:
  If F and F′ are smooth near z, with F′(z) ≠ 0 and Im F(z) ≠ 0, then ρ²=|F′|²/(Im F)² is C∞ at z.
proof:
  The squared norm and imaginary part are smooth; the denominator stays nonzero locally, so multiplication and inversion preserve smoothness.
-/
theorem pullbackDensityFunction_contDiffAt_of_finiteCoordinate
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (hF : ContDiffAt ℝ ⊤ C.finiteCoordinate z)
    (hDeriv : ContDiffAt ℝ ⊤ (fun w : ℂ ↦ deriv C.finiteCoordinate w) z) :
    ContDiffAt ℝ ⊤ C.pullbackDensityFunction z := by
  have hoff_open : IsOpen offRealLineInComplexPlane := by
    change IsOpen {w : ℂ | w.im ≠ 0}
    simpa using
      (isOpen_ne_fun Complex.continuous_im (continuous_const : Continuous fun _ : ℂ ↦ (0 : ℝ)))
  have hρ_at :
      ContDiffAt ℝ ⊤ poincareDensitySqInChart (C.finiteCoordinate z) :=
    poincareDensitySqInChart_contDiffOn_offRealLine.contDiffAt
      (hoff_open.mem_nhds C.finiteCoordinate_offReal)
  have hρ :
      ContDiffAt ℝ ⊤
        (fun w : ℂ ↦ poincareDensitySqInChart (C.finiteCoordinate w)) z :=
    hρ_at.comp z hF
  have hre :
      ContDiffAt ℝ ⊤
        (fun w : ℂ ↦ (deriv C.finiteCoordinate w).re) z := by
    have hRe : ContDiff ℝ ⊤ (Complex.reCLM : ℂ → ℝ) :=
      (Complex.reCLM : ℂ →L[ℝ] ℝ).contDiff (𝕜 := ℝ) (n := ⊤)
    exact hRe.contDiffAt.comp z hDeriv
  have him :
      ContDiffAt ℝ ⊤
        (fun w : ℂ ↦ (deriv C.finiteCoordinate w).im) z := by
    have hIm : ContDiff ℝ ⊤ (Complex.imCLM : ℂ → ℝ) :=
      (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff (𝕜 := ℝ) (n := ⊤)
    exact hIm.contDiffAt.comp z hDeriv
  have hnorm :
      ContDiffAt ℝ ⊤
        (fun w : ℂ ↦ Complex.normSq (deriv C.finiteCoordinate w)) z := by
    simpa [Complex.normSq_apply, pow_two] using (hre.pow 2).add (him.pow 2)
  simpa [pullbackDensityFunction_apply] using hρ.mul hnorm

/--
The Liouville equation for the local pullback log-density gives curvature
`-1` for the local pullback density.

%%handwave
name:
  Liouville implies curvature minus one
statement:
  If a positive smooth squared density q satisfies Δ(½ log q)=q at z, then its Gaussian curvature at z equals −1.
proof:
  Use K_q=−q⁻¹Δ(½ log q) and substitute the Liouville equation.
-/
theorem pullbackDensityFunction_curvature_eq_minus_one_of_liouville
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target)
    (hL :
      Laplacian.laplacian (logDensityFromDensitySq C.pullbackDensityFunction) z =
        C.pullbackDensityFunction z) :
    gaussianCurvatureOfDensitySq C.pullbackDensityFunction z = -1 :=
  gaussianCurvatureOfDensitySq_eq_minus_one_of_liouville
    (C.pullbackDensityFunction_pos he hz) hL

/--
The Liouville equation for the local pullback density transfers the curvature
calculation to the off-real model coordinate.

%%handwave
name:
  Liouville transfers pullback curvature to the Poincare model
statement:
  If the finite branch pullback density satisfies Δ log ρ=ρ² at z, then its curvature equals the curvature of the Poincare density at F(z).
proof:
  Liouville gives curvature −1 for the pullback density, while the off-real Poincare model also has curvature −1.
-/
theorem pullbackDensityFunction_curvature_transfer_of_liouville
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target)
    (hL :
      Laplacian.laplacian (logDensityFromDensitySq C.pullbackDensityFunction) z =
        C.pullbackDensityFunction z) :
    gaussianCurvatureOfDensitySq C.pullbackDensityFunction z =
      gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z) := by
  calc
    gaussianCurvatureOfDensitySq C.pullbackDensityFunction z = -1 :=
      C.pullbackDensityFunction_curvature_eq_minus_one_of_liouville he hz hL
    _ = gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z) :=
      (offRealLineDensitySq_gaussianCurvature_eq_minus_one
        (z := C.finiteCoordinate z) C.finiteCoordinate_offReal).symm

end RegularLocusLocalPullbackCoordinateData

/--
Two local pullback-coordinate branches in the same complex chart give the same
pullback density at the same surface point.

%%handwave
name:
  Pullback density is independent of the local branch in one chart
statement:
  Two valid normalized finite developing branches at the same regular chart point give the same value of |F′|²/(Im F)².
proof:
  Their projective coordinates differ locally by a real projective Möbius transformation. The Poincare density is invariant under this transformation, and the chain rule identifies the two derivatives.
-/
theorem localPullbackCoordinateData_pullbackDensity_eq_sameChart
    (H : P.PGL2RHolonomyData x₀)
    {e : OpenPartialHomeomorph X ℂ} {z : ℂ}
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target)
    (C₁ : H.RegularLocusLocalPullbackCoordinateData e z)
    (C₂ : H.RegularLocusLocalPullbackCoordinateData e (e (e.symm z))) :
    C₁.pullbackDensity = C₂.pullbackDensity := by
  have hz_source : e.symm z ∈ e.source := e.map_target hz
  have hz₂_target : e (e.symm z) ∈ e.target := e.map_source hz_source
  rcases
    H.localPullbackCoordinateData_finiteCoordinate_transition_eventuallyEq
      hz hz_source C₁ C₂ with
    ⟨R, hvalue, hEq⟩
  have hdensity :
      poincareDensitySqInChart (C₂.finiteCoordinate (e (e.symm z))) *
          Complex.normSq
            (deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
              (C₁.finiteCoordinate z)) =
        poincareDensitySqInChart (C₁.finiteCoordinate z) := by
    rw [hvalue]
    exact pgl2r_preserves_offRealLineDensity_holomorphic R C₁.finiteCoordinate_offReal
  have hderiv :
      deriv C₂.finiteCoordinate (e (e.symm z)) *
          deriv (fun w : ℂ ↦ e (e.symm w)) z =
        deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
            (C₁.finiteCoordinate z) *
          deriv C₁.finiteCoordinate z := by
    exact
      H.localPullbackCoordinateData_transition_derivative_of_eventuallyEq_chartTransition
        he he hz hz_source C₁ C₂ R hEq
        (C₁.finiteCoordinate_differentiableAt he hz)
        (C₂.finiteCoordinate_differentiableAt he hz₂_target)
  have htransition :=
    H.localPullbackCoordinateData_pullbackDensity_transition_of_derivative
      C₁ C₂ R hdensity hderiv
  have hid_event :
      (fun w : ℂ ↦ e (e.symm w)) =ᶠ[𝓝 z] fun w : ℂ ↦ w := by
    have htarget : ∀ᶠ w in 𝓝 z, w ∈ e.target :=
      e.open_target.mem_nhds hz
    filter_upwards [htarget] with w hw
    exact e.right_inv hw
  have hderiv_id :
      deriv (fun w : ℂ ↦ e (e.symm w)) z = 1 := by
    calc
      deriv (fun w : ℂ ↦ e (e.symm w)) z =
          deriv (fun w : ℂ ↦ w) z := hid_event.deriv_eq
      _ = 1 := by
        simp
  simpa [hderiv_id] using htransition

/-- Two local pullback-coordinate branches over the same point in the same chart
give the same pullback density.

%%handwave
name:
  Pointwise independence of the local pullback branch
statement:
  At a fixed regular chart point, any two valid normalized finite developing branches determine the same pullback squared density.
proof:
  Apply local branch-independence and evaluate the resulting equality at the base point.
-/
theorem localPullbackCoordinateData_pullbackDensity_eq_sameChart_at
    (H : P.PGL2RHolonomyData x₀)
    {e : OpenPartialHomeomorph X ℂ} {z : ℂ}
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target)
    (C₁ C₂ : H.RegularLocusLocalPullbackCoordinateData e z) :
    C₁.pullbackDensity = C₂.pullbackDensity := by
  have hz_id : e (e.symm z) = z := e.right_inv hz
  let C₂' : H.RegularLocusLocalPullbackCoordinateData e (e (e.symm z)) :=
    cast
      (congrArg (fun t : ℂ ↦ H.RegularLocusLocalPullbackCoordinateData e t) hz_id.symm) C₂
  have h := H.localPullbackCoordinateData_pullbackDensity_eq_sameChart he hz C₁ C₂'
  have hcast : C₂'.pullbackDensity = C₂.pullbackDensity := by
    simpa [C₂'] using
      (RegularLocusLocalPullbackCoordinateData.pullbackDensity_cast
        (H := H) (e := e) (h := hz_id.symm) C₂)
  exact h.trans hcast

/-- The canonical selected finite branch is holomorphic at each regular chart point.

%%handwave
name:
  Differentiability of the canonical finite branch
statement:
  The normalized finite developing coordinate selected at a regular chart point is complex differentiable there.
proof:
  It agrees locally with a Möbius transform of a compatible holomorphic projective chart; the denominator is nonzero, so the finite Möbius formula is holomorphic.
-/
theorem regularLocusLocalPullbackCoordinateData_finiteCoordinate_differentiableAt
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    DifferentiableAt ℂ
      (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z :=
  (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate_differentiableAt
    he hz

/-- The canonical selected finite branch is locally biholomorphic at each regular chart point.

%%handwave
name:
  Nondegeneracy of the canonical finite branch
statement:
  The normalized finite developing coordinate selected at a regular chart point has nonzero complex derivative there.
proof:
  Its compatible projective chart has nonzero derivative and the Möbius finite-coordinate derivative is nonzero away from its pole; the chain rule gives a nonzero product.
-/
theorem regularLocusLocalPullbackCoordinateData_finiteCoordinate_deriv_ne_zero
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    deriv (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z ≠ 0 :=
  (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate_deriv_ne_zero
    he hz

/--
The canonical selected finite developing branches on an overlap are locally
related by an actual real-projective fractional-linear transition.

%%handwave
name:
  Canonical finite branches have real-projective transition germs
statement:
  At an overlap point of two complex charts, their canonical finite developing branches are locally related by one real projective Möbius transformation.
proof:
  Lift the common base point to the developing cover, compare the two local chart agreements by the deck action, and use PGL₂(ℝ)-equivariance of the developing map to obtain the real-projective transition germ.
-/
theorem regularLocusLocalPullbackCoordinateData_transition_eventuallyEq
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (_he' : e' ∈ atlas ℂ X) (z : ℂ)
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (hz' : e.symm z ∈ e'.source) :
    ∃ R : RealProjectiveMobiusRepresentative,
      (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
            (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) =
          UpperHalfPlane.num R
              ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) /
            UpperHalfPlane.denom R
              ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) ∧
        (fun w : ℂ ↦
          (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
            (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate
              (e' (e.symm w))) =ᶠ[𝓝 z]
          (fun w : ℂ ↦
            UpperHalfPlane.num R
                ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate w) /
              UpperHalfPlane.denom R
                ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate w)) := by
  let z' : ℂ := e' (e.symm z)
  have hz'_target : z' ∈ e'.target := e'.map_source hz'
  have hreg' : e'.symm z' ∈ H.regularSet := by
    simpa [z', e'.left_inv hz'] using hreg
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  let C' := H.regularLocusLocalPullbackCoordinateData e' hz'_target hreg'
  simpa [C, C', z', hreg'] using
    H.localPullbackCoordinateData_finiteCoordinate_transition_eventuallyEq
      hz hz' C C'

/-- The canonical pullback-density candidate in a complex chart.

%%handwave
name:
  Canonical chartwise pullback density
statement:
  In a complex chart, the canonical squared density equals the Poincaré pullback density of the chosen finite developing branch at regular chart points, and is extended by the value $1$ elsewhere.
-/
noncomputable def canonicalPullbackDensityInChart
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ) : ℝ :=
  by
    classical
    exact
      if h : z ∈ e.target ∧ e.symm z ∈ H.regularSet then
        (H.regularLocusLocalPullbackCoordinateData e h.1 h.2).pullbackDensity
      else
        1

/-- On the regular locus, the canonical density candidate is the chosen branch pullback density.

%%handwave
name:
  The canonical chart density equals a chosen branch pullback
statement:
  At a regular chart point, the canonical squared density equals the pullback value |F′(z)|²/(Im F(z))² of the canonical normalized finite branch selected there.
proof:
  The canonical density is defined as the branch-independent pullback value; instantiate it with the selected branch.
-/
theorem canonicalPullbackDensityInChart_eq_pullbackDensity
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    H.canonicalPullbackDensityInChart e he z =
      (H.regularLocusLocalPullbackCoordinateData e hz hreg).pullbackDensity := by
  classical
  rw [canonicalPullbackDensityInChart]
  rw [dif_pos ⟨hz, hreg⟩]

/--
On the regular locus, the canonical density candidate agrees with the pullback
density of any valid finite developing-coordinate branch in the same chart.

%%handwave
name:
  The canonical density equals any valid local branch pullback
statement:
  At a regular chart point, the canonical squared density equals |F′(z)|²/(Im F(z))² for every valid normalized finite developing branch F at that point.
proof:
  Compare the given branch with the canonical selected branch in the same chart and use branch-independence of the pullback density.
-/
theorem canonicalPullbackDensityInChart_eq_pullbackDensity_of_localPullbackCoordinateData
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    H.canonicalPullbackDensityInChart e he z = C.pullbackDensity := by
  rw [H.canonicalPullbackDensityInChart_eq_pullbackDensity e he hz hreg]
  exact
    H.localPullbackCoordinateData_pullbackDensity_eq_sameChart_at he hz
      (H.regularLocusLocalPullbackCoordinateData e hz hreg) C

/-- The canonical density candidate has the explicit pullback formula on the regular locus.

%%handwave
name:
  Explicit formula for the canonical chart density
statement:
  At a regular chart point with canonical finite branch F, the canonical squared density is q(z)=|F′(z)|²/(Im F(z))².
proof:
  Expand the local pullback-density definition after identifying the canonical density with the selected branch value.
-/
theorem canonicalPullbackDensityInChart_eq_pullback_formula
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
    H.canonicalPullbackDensityInChart e he z =
      ((C.finiteCoordinate z).im ^ 2)⁻¹ *
        Complex.normSq (deriv C.finiteCoordinate z) := by
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  rw [H.canonicalPullbackDensityInChart_eq_pullbackDensity e he hz hreg]
  rfl

/--
The canonical density candidate is positive wherever the selected finite branch
has nonzero derivative.

%%handwave
name:
  Positivity of the canonical chart density
statement:
  If the canonical finite branch F has F′(z) ≠ 0 at a regular point, then the canonical squared density q(z)=|F′(z)|²/(Im F(z))² is positive.
proof:
  The finite branch is off real, so its squared imaginary part is positive; the nonzero derivative gives a positive squared norm.
-/
theorem canonicalPullbackDensityInChart_pos_of_finiteCoordinate_deriv_ne_zero
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (hderiv :
      deriv (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z ≠ 0) :
    0 < H.canonicalPullbackDensityInChart e he z := by
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  rw [H.canonicalPullbackDensityInChart_eq_pullbackDensity e he hz hreg]
  exact mul_pos
    (poincareDensitySqInChart_pos_of_im_ne_zero C.finiteCoordinate_offReal)
    (Complex.normSq_pos.mpr hderiv)

/--
The canonical density candidate satisfies the conformal transition law from
one locally valid real-projective transition between the selected branches.

%%handwave
name:
  Density transition from an existential real-projective branch relation
statement:
  If some real projective Möbius transformation relates two differentiable finite branches locally on a chart overlap, then the canonical chart densities satisfy the conformal transition law there.
proof:
  Choose the transition representative and apply the transition theorem for its local branch equality.
-/
theorem canonicalPullbackDensityInChart_transition_of_branch_eventuallyEq_exists
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (hz' : e.symm z ∈ e'.source)
    (hC :
      DifferentiableAt ℂ
        (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z)
    (hC' :
      DifferentiableAt ℂ
        (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
          (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate
        (e' (e.symm z)))
    (hTrans :
      ∃ R : RealProjectiveMobiusRepresentative,
        (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
              (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) =
            UpperHalfPlane.num R
                ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) /
              UpperHalfPlane.denom R
                ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) ∧
          (fun w : ℂ ↦
            (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
              (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate
                (e' (e.symm w))) =ᶠ[𝓝 z]
            (fun w : ℂ ↦
              UpperHalfPlane.num R
                  ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate w) /
                UpperHalfPlane.denom R
                  ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate w))) :
    H.canonicalPullbackDensityInChart e he z =
      H.canonicalPullbackDensityInChart e' he' (e' (e.symm z)) *
        Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z) := by
  let z' : ℂ := e' (e.symm z)
  have hz'_target : z' ∈ e'.target := e'.map_source hz'
  have hreg' : e'.symm z' ∈ H.regularSet := by
    simpa [z', e'.left_inv hz'] using hreg
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  let C' := H.regularLocusLocalPullbackCoordinateData e' hz'_target hreg'
  rcases hTrans with ⟨R, hvalue, hEq⟩
  have hdensity :
      poincareDensitySqInChart (C'.finiteCoordinate z') *
          Complex.normSq
            (deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
              (C.finiteCoordinate z)) =
        poincareDensitySqInChart (C.finiteCoordinate z) := by
    rw [show C'.finiteCoordinate z' =
        UpperHalfPlane.num R (C.finiteCoordinate z) /
          UpperHalfPlane.denom R (C.finiteCoordinate z) by
      simpa [C, C', z', hreg'] using hvalue]
    exact pgl2r_preserves_offRealLineDensity_holomorphic R C.finiteCoordinate_offReal
  have hderiv :
      deriv C'.finiteCoordinate z' *
          deriv (fun w : ℂ ↦ e' (e.symm w)) z =
        deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
            (C.finiteCoordinate z) *
          deriv C.finiteCoordinate z := by
    exact
      H.localPullbackCoordinateData_transition_derivative_of_eventuallyEq_chartTransition
        he he' hz hz' C C' R
        (by simpa [C, C', z', hreg'] using hEq)
        (by simpa [C] using hC)
        (by simpa [C', z', hreg'] using hC')
  have htransition :=
    H.localPullbackCoordinateData_pullbackDensity_transition_of_derivative
      C C' R hdensity hderiv
  rw [H.canonicalPullbackDensityInChart_eq_pullbackDensity e he hz hreg]
  rw [H.canonicalPullbackDensityInChart_eq_pullbackDensity e' he' hz'_target hreg']
  exact htransition

/--
On a local agreement chart, the regular locus is open provided the fixed
normalization acts continuously on the Riemann sphere.

%%handwave
name:
  Local openness of the regular locus
statement:
  On a developing-map agreement chart, if the fixed projective normalization acts continuously on ℂP¹, then the points whose normalized chart values lie outside ℝP¹ form an open subset; equivalently, the regular locus is locally open there.
proof:
  The complement ℂP¹ ∖ ℝP¹ is open. Take its inverse image under the continuous normalized chart and use the local characterization of regular points.
-/
theorem regularSet_local_open_of_normalization_continuous
    (H : P.PGL2RHolonomyData x₀)
    {y : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y)
    (hA : Continuous fun z : RiemannSphere ↦ L.normalization • z) :
    IsOpen (L.chart.source ∩ H.regularSet) := by
  have hnorm : ContinuousOn
      (fun x : X ↦ L.normalization • L.chart x) L.chart.source := by
    exact hA.continuousOn.comp L.chart.continuousOn (by
      intro x hx
      exact Set.mem_univ _)
  have hopen : IsOpen (L.chart.source ∩
      {x : X | ¬ RiemannSphere.IsRealProjectivePoint (L.normalization • L.chart x)}) :=
    hnorm.isOpen_inter_preimage L.chart.open_source
      offRealProjectiveLineInRiemannSphere_open
  convert hopen using 1
  ext x
  constructor
  · rintro ⟨hx, hreg⟩
    exact ⟨hx, (H.regularSet_iff_normalizedChart_offReal L hx).mp hreg⟩
  · rintro ⟨hx, hoff⟩
    exact ⟨hx, (H.regularSet_iff_normalizedChart_offReal L hx).mpr hoff⟩

/--
Every point of the developing cover admits a local agreement chart whose
normalization acts continuously on the Riemann sphere.

%%handwave
name:
  Continuous local developing normalizations
statement:
  A real-holonomy projective structure has continuous local normalizations when every point of its developing cover admits a locally agreeing projective chart whose fixed normalizing Möbius transformation acts continuously on $\mathbb P^1(\mathbb C)$.
-/
def HasContinuousLocalNormalizations (H : P.PGL2RHolonomyData x₀) : Prop :=
  ∀ y : H.holonomy_constructed_from_projective_charts.developingData.cover.total,
    ∃ L : ProjectiveHolonomyLocalChartAgreementData X P
        H.holonomy_constructed_from_projective_charts.developingData y,
      Continuous fun z : RiemannSphere ↦ L.normalization • z

/--
Continuity of every fixed Mobius action gives continuous local normalizations
for the developing-map chart agreements.

%%handwave
name:
  Continuous Möbius actions give continuous local normalizations
statement:
  If every fixed Möbius transformation acts continuously on ℂP¹, then every point of the developing cover has a local projective-chart agreement whose normalization acts continuously.
proof:
  Choose the local chart agreement supplied by the developing map and apply the assumed continuity to its fixed normalizing Möbius transformation.
-/
theorem hasContinuousLocalNormalizations_of_mobiusAction_continuous
    (H : P.PGL2RHolonomyData x₀)
    (hcont : ∀ A : MobiusRepresentative, Continuous fun z : RiemannSphere ↦ A • z) :
    H.HasContinuousLocalNormalizations := by
  intro y
  rcases
    H.holonomy_constructed_from_projective_charts.developingMap_locally_agrees_with_projective_charts
      y with
    ⟨L⟩
  exact ⟨L, hcont L.normalization⟩

end ComplexProjectiveStructure.PGL2RHolonomyData

namespace ProjectiveHolonomyLocalChartAgreementData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {basepoint : X} {ρ : HolonomyRepresentation X basepoint}
    {P : ComplexProjectiveStructure X}
    {developingData : ProjectiveHolonomyDevelopingData X basepoint ρ}
    {y : developingData.cover.total}

end ProjectiveHolonomyLocalChartAgreementData

/--
Chartwise conformal metric data on a specified locus of a charted surface.

The squared-density representatives are ambient functions on complex chart
targets, but their positivity, transition law, smoothness, and curvature are
only required at points whose inverse chart image lies in the chosen locus.
-/
structure ConformalMetricOn (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) where
  /-- The squared density in a chosen complex chart, as an ambient representative. -/
  densitySqInChart :
    (e : OpenPartialHomeomorph X ℂ) → e ∈ atlas ℂ X → ℂ → ℝ
  /-- The squared density is positive on the chosen locus. -/
  densitySq_pos :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) z,
      z ∈ e.target → e.symm z ∈ U → 0 < densitySqInChart e he z
  /-- Chartwise squared densities transform on the chosen locus. -/
  densitySq_transition :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
      (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) z,
        z ∈ e.target →
        e.symm z ∈ U →
        e.symm z ∈ e'.source →
        densitySqInChart e he z =
          densitySqInChart e' he' (e' (e.symm z)) *
            Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z)

namespace ConformalMetricOn

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {U : Set X}

/-- Gaussian curvature computed from the regular-locus density in a chosen chart.

%%handwave
name:
  Gaussian curvature in a conformal chart
statement:
  The chartwise Gaussian curvature of a conformal metric is the curvature computed from its squared density in that chart.
-/
noncomputable def gaussianCurvatureInChart (g : ConformalMetricOn X U)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) : ℂ → ℝ :=
  gaussianCurvatureOfDensitySq (g.densitySqInChart e he)

/-- Smoothness of the squared density on the coordinate part of the chosen locus.

%%handwave
name:
  Chartwise smoothness of a conformal metric
statement:
  A conformal metric on $U\subseteq X$ is chartwise smooth when every squared-density representative is $C^\infty$ on the chart points representing $U$.
-/
def smooth_in_charts (g : ConformalMetricOn X U) : Prop :=
  ∀ e he, ContDiffOn ℝ ⊤ (g.densitySqInChart e he) (e.target ∩ e.symm ⁻¹' U)

/-- Smoothness predicate for a regular-locus conformal metric.

%%handwave
name:
  Smooth conformal metric on a locus
statement:
  A conformal metric on a locus is smooth exactly when all of its chartwise squared-density representatives are $C^\infty$ there.
-/
def IsSmooth (g : ConformalMetricOn X U) : Prop :=
  g.smooth_in_charts

/-- The Gaussian-curvature predicate on the chosen locus.

%%handwave
name:
  Constant chartwise curvature on a locus
statement:
  A conformal metric has curvature $K$ on $U$ when its Gaussian curvature in every complex chart equals $K$ at every chart point representing a point of $U$.
-/
def curvature_eq (g : ConformalMetricOn X U) (K : ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) z,
    z ∈ e.target → e.symm z ∈ U → g.gaussianCurvatureInChart e he z = K

/-- The metric has Gaussian curvature `-1` on the chosen locus.

%%handwave
name:
  Curvature minus one on a locus
statement:
  A conformal metric has curvature minus one on $U$ when its chartwise Gaussian curvature is identically $-1$ at every point of $U$.
-/
def HasCurvatureMinusOne (g : ConformalMetricOn X U) : Prop :=
  g.curvature_eq (-1)

end ConformalMetricOn

namespace ConformalMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

end ConformalMetric

namespace ComplexProjectiveStructure.PGL2RHolonomyData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {P : ComplexProjectiveStructure X}

/--
Topological data for the canonical regular locus of a real-projective
developing map.
-/
structure RegularLocusTopologicalData (H : P.PGL2RHolonomyData x₀) where
  /-- The regular set is open in the surface. -/
  regularSet_open : IsOpen H.regularSet

/--
Continuous local normalizations supply the topological part of the regular
locus data.

%%handwave
name:
  Topological regular-locus data from continuous normalizations
statement:
  Continuous normalized developing charts determine topological regular-locus data by proving that the complement of the descended real-projective locus is open.
-/
def regularLocusTopologicalData_of_continuousLocalNormalizations
    (H : P.PGL2RHolonomyData x₀)
    (h : H.HasContinuousLocalNormalizations) :
    H.RegularLocusTopologicalData where
  regularSet_open := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    let cover := H.holonomy_constructed_from_projective_charts.developingData.cover
    rcases cover.projection_surjective x with ⟨y, hy⟩
    rcases h y with ⟨L, hA⟩
    have hxsource : x ∈ L.chart.source := by
      rw [← hy]
      exact L.projected_mem
    exact Filter.mem_of_superset
      ((H.regularSet_local_open_of_normalization_continuous L hA).mem_nhds
        ⟨hxsource, hx⟩)
      Set.inter_subset_right

/--
Continuity of fixed Mobius actions on the Riemann sphere gives the topological
regular-locus data.

%%handwave
name:
  Topological regular-locus data from continuous Möbius actions
statement:
  If every fixed complex Möbius transformation acts continuously on $\mathbb P^1(\mathbb C)$, then a real-holonomy projective structure has an open regular locus.
-/
def regularLocusTopologicalData_of_mobiusAction_continuous
    (H : P.PGL2RHolonomyData x₀)
    (hcont : ∀ A : MobiusRepresentative, Continuous fun z : RiemannSphere ↦ A • z) :
    H.RegularLocusTopologicalData :=
  H.regularLocusTopologicalData_of_continuousLocalNormalizations
    (H.hasContinuousLocalNormalizations_of_mobiusAction_continuous hcont)

/-- The topological regular-locus data supplied by continuity of Mobius transformations.

%%handwave
name:
  Canonical topological data of the regular locus
statement:
  The canonical topological data records that the complement of the descended real-projective developing locus is open, using continuity of Möbius actions.
-/
def regularLocusTopologicalData (H : P.PGL2RHolonomyData x₀) :
    H.RegularLocusTopologicalData :=
  H.regularLocusTopologicalData_of_mobiusAction_continuous
    mobiusRepresentative_smul_continuous

/--
The regular locus of the descended real-projective locus is open.

%%handwave
name:
  The complement of the real-projective locus is open
statement:
  For a complex projective structure with PGL₂(ℝ) holonomy, the points whose developing values avoid ℝP¹ form an open subset of the base surface.
proof:
  Lift a regular point to the developing cover, choose a locally agreeing projective chart, and use continuity of its Möbius normalization to obtain an open regular neighborhood.
-/
theorem regularSet_open (H : P.PGL2RHolonomyData x₀) :
    IsOpen H.regularSet :=
  H.regularLocusTopologicalData.regularSet_open

/--
A local pullback-coordinate branch at a regular point remains a valid branch
for all nearby regular chart points after shrinking the coordinate
neighborhood.

%%handwave
name:
  A finite developing branch persists near a regular point
statement:
  A finite normalized developing branch chosen at a regular chart point remains a valid off-real branch for all sufficiently nearby regular chart points, and computes the same pointwise pullback density there.
proof:
  Shrink to where its projective-chart agreement holds. Openness of the chart domain and regular locus keeps the same normalized branch finite and off real; reuse it as the local branch at nearby points.
-/
theorem localPullbackCoordinateData_eventually_sameBranchData
    (H : P.PGL2RHolonomyData x₀)
    {e : OpenPartialHomeomorph X ℂ} {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    ∀ᶠ w in 𝓝 z,
      ∃ (_ : w ∈ e.target) (_ : e.symm w ∈ H.regularSet),
        ∃ Cw : H.RegularLocusLocalPullbackCoordinateData e w,
          Cw.pullbackDensity = C.pullbackDensityFunction w := by
  rcases eventually_nhds_iff.mp C.finiteCoordinate_eventually_eq with
    ⟨Ueq, hUeq, hUeq_open, hzUeq⟩
  have htarget : ∀ᶠ w in 𝓝 z, w ∈ e.target :=
    e.open_target.mem_nhds hz
  have hsource : ∀ᶠ w in 𝓝 z, e.symm w ∈ C.chart.source :=
    (e.symm.continuousAt hz).preimage_mem_nhds
      (C.chart.open_source.mem_nhds C.mem_chart_source)
  have hreg_event : ∀ᶠ w in 𝓝 z, e.symm w ∈ H.regularSet :=
    (e.symm.continuousAt hz).preimage_mem_nhds
      (H.regularSet_open.mem_nhds hreg)
  have hUeq_event : ∀ᶠ w in 𝓝 z, w ∈ Ueq :=
    hUeq_open.mem_nhds hzUeq
  filter_upwards [htarget, hsource, hreg_event, hUeq_event] with
    w hzw hsourcew hregw hwU
  have hEqw :
      ∀ᶠ u in 𝓝 w,
        (((C.finiteCoordinate u : ℂ) : RiemannSphere) =
          C.normalization • C.chart (e.symm u)) :=
    by
      filter_upwards [hUeq_open.mem_nhds hwU] with u hu
      exact hUeq u hu
  have hspherew :
      ((C.finiteCoordinate w : ℂ) : RiemannSphere) =
        C.normalization • C.chart (e.symm w) :=
    hUeq w hwU
  have hsourcew_local : e.symm w ∈ C.localAgreement.chart.source := by
    simpa [C.chart_eq_localAgreement_chart] using hsourcew
  have hoff_normalized :
      ¬ RiemannSphere.IsRealProjectivePoint
        (C.normalization • C.chart (e.symm w)) := by
    have h :=
      (H.regularSet_iff_normalizedChart_offReal C.localAgreement hsourcew_local).mp
        hregw
    simpa [C.chart_eq_localAgreement_chart,
      C.normalization_eq_localAgreement_normalization] using h
  have hoff_coe :
      ¬ RiemannSphere.IsRealProjectivePoint
        ((C.finiteCoordinate w : ℂ) : RiemannSphere) := by
    rw [hspherew]
    exact hoff_normalized
  have hoffw : (C.finiteCoordinate w).im ≠ 0 := by
    rcases
      (RiemannSphere.not_isRealProjectivePoint_iff_exists_im_ne_zero
        ((C.finiteCoordinate w : ℂ) : RiemannSphere)).mp hoff_coe with
      ⟨v, hv, hv_im⟩
    have hv_eq : C.finiteCoordinate w = v := OnePoint.coe_injective hv
    simpa [hv_eq] using hv_im
  let Cw : H.RegularLocusLocalPullbackCoordinateData e w :=
    { coverPoint := C.coverPoint
      localAgreement := C.localAgreement
      finiteCoordinate := C.finiteCoordinate
      chart := C.chart
      normalization := C.normalization
      chart_mem := C.chart_mem
      mem_chart_source := hsourcew
      chart_eq_localAgreement_chart := C.chart_eq_localAgreement_chart
      normalization_eq_localAgreement_normalization :=
        C.normalization_eq_localAgreement_normalization
      finiteCoordinate_eventually_eq := hEqw
      finiteCoordinate_offReal := hoffw }
  exact ⟨hzw, hregw, Cw, rfl⟩

/--
Near a regular chart point, the canonical density is represented by any fixed
valid finite developing-coordinate branch chosen at that point.

%%handwave
name:
  The canonical density is locally a fixed branch pullback
statement:
  Near any regular chart point, the canonical squared density agrees with the pullback density |F′|²/(Im F)² of any valid finite normalized developing branch F chosen there.
proof:
  The fixed branch remains valid nearby. At each nearby point, the definition of the canonical density may therefore use that same branch, giving pointwise equality on a neighborhood.
-/
theorem canonicalPullbackDensityInChart_eventuallyEq_pullbackDensityFunction
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    H.canonicalPullbackDensityInChart e he =ᶠ[𝓝 z] C.pullbackDensityFunction := by
  have hlocal := H.localPullbackCoordinateData_eventually_sameBranchData hz hreg C
  filter_upwards [hlocal] with w hw
  rcases hw with ⟨hzw, hregw, Cw, hCw⟩
  rw [H.canonicalPullbackDensityInChart_eq_pullbackDensity_of_localPullbackCoordinateData
    e he hzw hregw Cw]
  exact hCw

/--
Curvature transfer for the canonical density follows from the curvature
calculation for the fixed local pullback-density function.

%%handwave
name:
  Branch curvature transfers to the canonical density
statement:
  If a finite branch pullback density has the same curvature at z as the Poincare model at F(z), then the canonical chart density has that curvature at z as well.
proof:
  The canonical density and branch density agree on a neighborhood of z, so their Gaussian curvatures agree; then apply the branch curvature hypothesis.
-/
theorem canonicalPullbackDensityInChart_curvature_transfer_of_pullbackDensityFunction
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (hcurv :
      gaussianCurvatureOfDensitySq C.pullbackDensityFunction z =
        gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)) :
    gaussianCurvatureOfDensitySq (H.canonicalPullbackDensityInChart e he) z =
      gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z) := by
  calc
    gaussianCurvatureOfDensitySq (H.canonicalPullbackDensityInChart e he) z =
        gaussianCurvatureOfDensitySq C.pullbackDensityFunction z :=
      gaussianCurvatureOfDensitySq_congr_nhds
        (H.canonicalPullbackDensityInChart_eventuallyEq_pullbackDensityFunction
          e he hz hreg C)
    _ = gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z) :=
      hcurv

/--
Smoothness of the fixed local pullback-density functions implies smoothness of
the canonical density on the regular locus.

%%handwave
name:
  Local branch smoothness gives smoothness of the canonical density
statement:
  If every valid finite branch pullback density is smooth at its base point, then the canonical squared density is smooth throughout the regular part of every complex chart.
proof:
  At each regular chart point, replace the canonical density near that point by a fixed locally equal branch density and transfer smoothness through germ equality.
-/
theorem canonicalPullbackDensityInChart_contDiffOn_of_pullbackDensityFunction
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (hsmooth :
      ∀ (z : ℂ) (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        ContDiffAt ℝ ⊤ C.pullbackDensityFunction z) :
    ContDiffOn ℝ ⊤ (H.canonicalPullbackDensityInChart e he)
      (e.target ∩ e.symm ⁻¹' H.regularSet) := by
  intro z hzreg
  rcases hzreg with ⟨hz, hreg⟩
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  have hC : ContDiffAt ℝ ⊤ C.pullbackDensityFunction z := by
    exact hsmooth z hz hreg
  exact
    (hC.congr_of_eventuallyEq
      (H.canonicalPullbackDensityInChart_eventuallyEq_pullbackDensityFunction
        e he hz hreg C)).contDiffWithinAt

/--
Conformal metric data on the canonical regular locus of a real-projective
developing map.

The real-projective locus has already been descended from the cover; this
package supplies the curvature and pullback-density content on its complement.
-/
structure RegularLocusConformalMetricData (H : P.PGL2RHolonomyData x₀) where
  /-- The conformal metric on the regular locus. -/
  metric : ConformalMetricOn X H.regularSet
  /-- The regular-locus metric is smooth. -/
  metric_smooth_on_regularSet : metric.IsSmooth
  /-- The metric has curvature `-1` on the regular locus. -/
  curvature_minus_one : metric.HasCurvatureMinusOne
  /--
  Away from the real-projective locus, the metric density is locally the
  pullback of the off-real-line hyperbolic density by a finite normalized
  projective coordinate.
  -/
  pullback_density_on_regularSet :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ),
      z ∈ e.target →
      e.symm z ∈ H.regularSet →
        ∃ F : ℂ → ℂ, ∃ chart : ProjectiveChart X, ∃ normalization : MobiusRepresentative,
          chart ∈ P.atlasSet ∧
            e.symm z ∈ chart.source ∧
              (∀ᶠ w in 𝓝 z,
                ((F w : ℂ) : RiemannSphere) = normalization • chart (e.symm w)) ∧
                  (F z).im ≠ 0 ∧
                    metric.densitySqInChart e he z =
                      ((F z).im ^ 2)⁻¹ * Complex.normSq (deriv F z)


/--
Canonical pullback metric data using the normalized finite-coordinate branches
already supplied by the developing map on the regular locus.

Compared with `RegularLocusPullbackMetricData`, this package no longer asks
for the coordinate witness itself: the witness is the canonical local branch
extracted from the developing-chart agreement.
-/
structure RegularLocusCanonicalPullbackMetricData (H : P.PGL2RHolonomyData x₀) where
  /-- The conformal metric on the regular locus. -/
  metric : ConformalMetricOn X H.regularSet
  /-- The regular-locus metric is smooth. -/
  metric_smooth_on_regularSet : metric.IsSmooth
  /-- Curvature transfers to the canonical finite off-real coordinate branch. -/
  curvature_transfers_to_normalizedFiniteCoordinate :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        metric.gaussianCurvatureInChart e he z =
          gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)
  /-- The density is the pullback of the off-real model along the canonical branch. -/
  density_eq_normalizedFiniteCoordinate_pullback :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        metric.densitySqInChart e he z =
          ((C.finiteCoordinate z).im ^ 2)⁻¹ *
            Complex.normSq (deriv C.finiteCoordinate z)

namespace RegularLocusCanonicalPullbackMetricData

variable {H : P.PGL2RHolonomyData x₀}

/--
%%handwave
name:
  Curvature of the canonical metric on the regular locus
statement:
  Let $P$ have holonomy in $\mathrm{PGL}_2(\mathbb R)$, let
  $U=X\setminus\operatorname{dev}^{-1}(\mathbb{RP}^1)$, and let $g$ be the
  canonical pullback metric on $U$. Suppose that, for every complex chart and
  every $z$ representing a point of $U$, the curvature of $g$ at $z$ agrees
  with the curvature of $(\operatorname{Im}w)^{-2}|dw|^2$ at the canonical
  finite developing value $F(z)\in\mathbb C\setminus\mathbb R$. Then $g$ has
  Gaussian curvature $-1$ throughout $U$.
proof:
  At a regular point, transfer the curvature calculation to the finite branch
  value $F(z)\in\mathbb C\setminus\mathbb R$. [The model density $(\operatorname{Im}w)^{-2}$ has curvature $-1$ there](lean:JJMath.offRealLineDensitySq_gaussianCurvature_eq_minus_one), hence so does the pullback metric.
-/
theorem curvature_minus_one (D : H.RegularLocusCanonicalPullbackMetricData) :
    D.metric.HasCurvatureMinusOne := by
  intro e he z hz hreg
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  rw [D.curvature_transfers_to_normalizedFiniteCoordinate e he z hz hreg]
  exact offRealLineDensitySq_gaussianCurvature_eq_minus_one
    (z := C.finiteCoordinate z) C.finiteCoordinate_offReal

/-- Forget canonical pullback provenance after deriving curvature from the model.

%%handwave
name:
  Conformal metric data from canonical pullback data
statement:
  Canonical pullback metric data determine a smooth conformal metric of curvature $-1$ on the regular locus, retaining the local finite-branch pullback formula while forgetting the canonical choice.
-/
def toRegularLocusConformalMetricData
    (D : H.RegularLocusCanonicalPullbackMetricData) :
    H.RegularLocusConformalMetricData where
  metric := D.metric
  metric_smooth_on_regularSet := D.metric_smooth_on_regularSet
  curvature_minus_one := D.curvature_minus_one
  pullback_density_on_regularSet := by
    intro e he z hz hreg
    let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
    exact
      ⟨C.finiteCoordinate, C.chart, C.normalization,
        C.chart_mem, C.mem_chart_source, C.finiteCoordinate_eventually_eq,
        C.finiteCoordinate_offReal,
        D.density_eq_normalizedFiniteCoordinate_pullback e he z hz hreg⟩

end RegularLocusCanonicalPullbackMetricData

/--
Canonical analytic data for the pullback-density candidate.

The branch choices, branch nondegeneracy, and chart-transition law are proved
above from the projective developing map.  This package only asks for
smoothness of the resulting density and the curvature-transfer computation.
-/
structure RegularLocusCanonicalDensityAnalyticData
    (H : P.PGL2RHolonomyData x₀) where
  /-- The canonical density candidate is smooth on the regular locus in complex charts. -/
  smooth_densitySq :
    ∀ e he,
      ContDiffOn ℝ ⊤ (H.canonicalPullbackDensityInChart e he)
        (e.target ∩ e.symm ⁻¹' H.regularSet)
  /-- Curvature transfers from the canonical density candidate to the off-real model branch. -/
  curvature_transfers_to_normalizedFiniteCoordinate :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        gaussianCurvatureOfDensitySq (H.canonicalPullbackDensityInChart e he) z =
          gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)

namespace RegularLocusCanonicalDensityAnalyticData

variable {H : P.PGL2RHolonomyData x₀}

/--
Build canonical-density analytic data from smoothness of the canonical density
and curvature transfer for the fixed local pullback-density functions.

%%handwave
name:
  Canonical-density data from local curvature transfer
statement:
  If the canonical chartwise density is smooth and every fixed finite-branch density has curvature equal to the off-real Poincaré model at the branch value, then the canonical density has the same curvature-transfer property.
-/
noncomputable def ofLocalPullbackDensityCurvature
    (smooth_densitySq :
      ∀ e he,
        ContDiffOn ℝ ⊤ (H.canonicalPullbackDensityInChart e he)
          (e.target ∩ e.symm ⁻¹' H.regularSet))
    (curvature_transfers_to_pullbackDensityFunction :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          gaussianCurvatureOfDensitySq C.pullbackDensityFunction z =
            gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)) :
    H.RegularLocusCanonicalDensityAnalyticData where
  smooth_densitySq := smooth_densitySq
  curvature_transfers_to_normalizedFiniteCoordinate := by
    intro e he z hz hreg
    let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
    exact
      H.canonicalPullbackDensityInChart_curvature_transfer_of_pullbackDensityFunction
        e he hz hreg C
        (curvature_transfers_to_pullbackDensityFunction e he z hz hreg)

/--
Build canonical-density analytic data from pointwise smoothness and curvature
transfer for the fixed local pullback-density functions.

%%handwave
name:
  Canonical-density data from branchwise analytic data
statement:
  Pointwise smoothness and curvature transfer for every finite-branch pullback density imply smoothness and curvature transfer for the canonical chartwise density on the regular locus.
-/
noncomputable def ofLocalPullbackDensityAnalyticData
    (pullbackDensityFunction_contDiffAt :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          ContDiffAt ℝ ⊤ C.pullbackDensityFunction z)
    (curvature_transfers_to_pullbackDensityFunction :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          gaussianCurvatureOfDensitySq C.pullbackDensityFunction z =
            gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)) :
    H.RegularLocusCanonicalDensityAnalyticData :=
  ofLocalPullbackDensityCurvature
    (H := H)
    (fun e he ↦
      H.canonicalPullbackDensityInChart_contDiffOn_of_pullbackDensityFunction
        e he (fun z hz hreg ↦
          pullbackDensityFunction_contDiffAt e he z hz hreg))
    curvature_transfers_to_pullbackDensityFunction

end RegularLocusCanonicalDensityAnalyticData

/--
Analytic facts for the fixed local pullback-density functions.

The local equality theorem above turns these branch-level facts into analytic
data for the canonical density candidate.
-/
structure RegularLocusLocalPullbackDensityAnalyticData
    (H : P.PGL2RHolonomyData x₀) where
  /-- The fixed local pullback-density function is smooth at each regular chart point. -/
  pullbackDensityFunction_contDiffAt :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        ContDiffAt ℝ ⊤ C.pullbackDensityFunction z
  /-- Its curvature computation transfers to the off-real model coordinate. -/
  curvature_transfers_to_pullbackDensityFunction :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        gaussianCurvatureOfDensitySq C.pullbackDensityFunction z =
          gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)

namespace RegularLocusLocalPullbackDensityAnalyticData

variable {H : P.PGL2RHolonomyData x₀}

/--
Build branch-level density analytic data from smoothness of the finite branch,
smoothness of its derivative, and the pullback curvature computation.

%%handwave
name:
  Pullback-density data from finite-coordinate regularity
statement:
  If every finite developing branch $F$ and its derivative $F'$ are smooth and the associated density $|F'|^2/(\operatorname{Im}F)^2$ has the model curvature, then these branch densities form the required local analytic data.
-/
noncomputable def ofFiniteCoordinateAnalyticData
    (finiteCoordinate_contDiffAt :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          ContDiffAt ℝ ⊤ C.finiteCoordinate z)
    (finiteCoordinate_deriv_contDiffAt :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          ContDiffAt ℝ ⊤ (fun w : ℂ ↦ deriv C.finiteCoordinate w) z)
    (curvature_transfers_to_pullbackDensityFunction :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          gaussianCurvatureOfDensitySq C.pullbackDensityFunction z =
            gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)) :
    H.RegularLocusLocalPullbackDensityAnalyticData where
  pullbackDensityFunction_contDiffAt := by
    intro e he z hz hreg
    let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
    exact C.pullbackDensityFunction_contDiffAt_of_finiteCoordinate
      (finiteCoordinate_contDiffAt e he z hz hreg)
      (finiteCoordinate_deriv_contDiffAt e he z hz hreg)
  curvature_transfers_to_pullbackDensityFunction :=
    curvature_transfers_to_pullbackDensityFunction

/--
Build branch-level density analytic data from the local pullback curvature
calculation.  The smoothness of the local finite developing branches follows
from the smooth surface atlas and projective-chart compatibility.

%%handwave
name:
  Pullback-density data from curvature transfer
statement:
  If every finite-branch pullback density has curvature equal to the off-real Poincaré model at the branch value, then the established smoothness of the branch and its derivative supplies all local pullback-density analytic data.
-/
noncomputable def ofCurvatureTransfer
    (curvature_transfers_to_pullbackDensityFunction :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          gaussianCurvatureOfDensitySq C.pullbackDensityFunction z =
            gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)) :
    H.RegularLocusLocalPullbackDensityAnalyticData :=
  ofFiniteCoordinateAnalyticData
    (H := H)
    (fun e he _z hz hreg ↦
      let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
      C.finiteCoordinate_contDiffAt_real he hz)
    (fun e he _z hz hreg ↦
      let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
      C.finiteCoordinate_deriv_contDiffAt_real he hz)
    curvature_transfers_to_pullbackDensityFunction

/--
Build branch-level density analytic data from the Liouville equation for each
local pullback log-density.

%%handwave
name:
  Pullback-density data from Liouville's equation
statement:
  If every finite-branch density $q$ satisfies $\Delta(\tfrac12\log q)=q$ at its base point, then the branch density is smooth and its Gaussian curvature agrees with the curvature $-1$ Poincaré model.
-/
noncomputable def ofLiouvilleEquation
    (pullbackDensityFunction_liouville :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          Laplacian.laplacian (logDensityFromDensitySq C.pullbackDensityFunction) z =
            C.pullbackDensityFunction z) :
    H.RegularLocusLocalPullbackDensityAnalyticData :=
  ofCurvatureTransfer
    (H := H)
    (fun e he z hz hreg ↦
      let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
      C.pullbackDensityFunction_curvature_transfer_of_liouville he hz
        (pullbackDensityFunction_liouville e he z hz hreg))

/-- Branch-level analytic data supplies canonical-density analytic data.

%%handwave
name:
  Canonical analytic density from branch densities
statement:
  Smoothness and curvature transfer for all local finite-branch densities descend to smoothness and curvature transfer for the branch-independent canonical chartwise density.
-/
noncomputable def toRegularLocusCanonicalDensityAnalyticData
    (A : H.RegularLocusLocalPullbackDensityAnalyticData) :
    H.RegularLocusCanonicalDensityAnalyticData :=
  RegularLocusCanonicalDensityAnalyticData.ofLocalPullbackDensityAnalyticData
    (H := H) A.pullbackDensityFunction_contDiffAt
    A.curvature_transfers_to_pullbackDensityFunction

end RegularLocusLocalPullbackDensityAnalyticData

/--
Canonical branch analytic data for the regular-locus pullback density.

The topological descent and real-projective density invariance are proved
above.  This package isolates the local holomorphic branch facts still needed
to turn the canonical density candidate into a conformal metric.
-/
structure RegularLocusCanonicalBranchAnalyticData
    (H : P.PGL2RHolonomyData x₀) where
  /-- The selected finite developing-coordinate branch is locally nondegenerate. -/
  finiteCoordinate_deriv_ne_zero :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        deriv (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z ≠ 0
  /-- The canonical density candidate satisfies the conformal chart-transition law. -/
  densitySq_transition :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
      (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) z,
        z ∈ e.target →
        e.symm z ∈ H.regularSet →
        e.symm z ∈ e'.source →
        H.canonicalPullbackDensityInChart e he z =
          H.canonicalPullbackDensityInChart e' he' (e' (e.symm z)) *
            Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z)
  /-- The canonical density candidate is smooth on the regular locus in complex charts. -/
  smooth_densitySq :
    ∀ e he,
      ContDiffOn ℝ ⊤ (H.canonicalPullbackDensityInChart e he)
        (e.target ∩ e.symm ⁻¹' H.regularSet)
  /-- Curvature transfers from the canonical density candidate to the off-real model branch. -/
  curvature_transfers_to_normalizedFiniteCoordinate :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        gaussianCurvatureOfDensitySq (H.canonicalPullbackDensityInChart e he) z =
          gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)

namespace RegularLocusCanonicalBranchAnalyticData

variable {H : P.PGL2RHolonomyData x₀}

/--
Build the branch-analytic package from an actual local real-projective
transition representative on each chart overlap.  This is the non-tautological
form: the transition data is existential rather than asking every
point-matching real projective map to be the local transition.

%%handwave
name:
  Compatible branch data from real-projective transition germs
statement:
  If canonical finite branches are locally related on every chart overlap by some element of $\mathrm{PGL}_2(\mathbb R)$, and the canonical density is smooth with curvature transferred from the model, then the branches determine compatible analytic pullback data.
-/
noncomputable def ofExistentialEventuallyEqTransitionWithCanonicalDerivatives
    (finiteCoordinate_transition_eventuallyEq :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
        (e' : OpenPartialHomeomorph X ℂ) (_he' : e' ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
        (hz' : e.symm z ∈ e'.source),
          ∃ R : RealProjectiveMobiusRepresentative,
            (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
                  (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) =
                UpperHalfPlane.num R
                    ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) /
                  UpperHalfPlane.denom R
                    ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) ∧
              (fun w : ℂ ↦
                (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
                  (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate
                    (e' (e.symm w))) =ᶠ[𝓝 z]
                (fun w : ℂ ↦
                  UpperHalfPlane.num R
                      ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate w) /
                    UpperHalfPlane.denom R
                      ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate w)))
    (smooth_densitySq :
      ∀ e he,
        ContDiffOn ℝ ⊤ (H.canonicalPullbackDensityInChart e he)
          (e.target ∩ e.symm ⁻¹' H.regularSet))
    (curvature_transfers_to_normalizedFiniteCoordinate :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          gaussianCurvatureOfDensitySq (H.canonicalPullbackDensityInChart e he) z =
            gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)) :
    H.RegularLocusCanonicalBranchAnalyticData where
  finiteCoordinate_deriv_ne_zero := by
    intro e he z hz hreg
    exact H.regularLocusLocalPullbackCoordinateData_finiteCoordinate_deriv_ne_zero
      e he z hz hreg
  densitySq_transition := by
    intro e he e' he' z hz hreg hz'
    exact H.canonicalPullbackDensityInChart_transition_of_branch_eventuallyEq_exists
      e he e' he' hz hreg hz'
      (H.regularLocusLocalPullbackCoordinateData_finiteCoordinate_differentiableAt
        e he z hz hreg)
      (H.regularLocusLocalPullbackCoordinateData_finiteCoordinate_differentiableAt
        e' he' (e' (e.symm z)) (e'.map_source hz')
        (by simpa [e'.left_inv hz'] using hreg))
      (finiteCoordinate_transition_eventuallyEq e he e' he' z hz hreg hz')
  smooth_densitySq := smooth_densitySq
  curvature_transfers_to_normalizedFiniteCoordinate :=
    curvature_transfers_to_normalizedFiniteCoordinate

/--
Build the branch-analytic package using the canonical real-projective branch
transitions proved from the developing map.  The arguments provide smoothness
of the canonical density and the curvature-transfer computation.

%%handwave
name:
  Compatible branch data from canonical transitions
statement:
  Smoothness and model-curvature transfer for the canonical density, together with the real-projective transition germs supplied by the developing map, determine canonical analytic branch data.
-/
noncomputable def ofCanonicalTransitions
    (smooth_densitySq :
      ∀ e he,
        ContDiffOn ℝ ⊤ (H.canonicalPullbackDensityInChart e he)
          (e.target ∩ e.symm ⁻¹' H.regularSet))
    (curvature_transfers_to_normalizedFiniteCoordinate :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          gaussianCurvatureOfDensitySq (H.canonicalPullbackDensityInChart e he) z =
            gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)) :
    H.RegularLocusCanonicalBranchAnalyticData :=
  ofExistentialEventuallyEqTransitionWithCanonicalDerivatives
    (H := H)
    (fun e he e' he' z hz hreg hz' ↦
      H.regularLocusLocalPullbackCoordinateData_transition_eventuallyEq
        e he e' he' z hz hreg hz')
    smooth_densitySq
    curvature_transfers_to_normalizedFiniteCoordinate

/-- The conformal metric represented by the canonical pullback-density candidate.

%%handwave
name:
  Conformal metric from compatible canonical branches
statement:
  Compatible canonical branches define a conformal metric on the regular locus whose squared densities are their canonical Poincaré pullbacks.
-/
noncomputable def toConformalMetricOn
    (A : H.RegularLocusCanonicalBranchAnalyticData) :
    ConformalMetricOn X H.regularSet where
  densitySqInChart := H.canonicalPullbackDensityInChart
  densitySq_pos := by
    intro e he z hz hreg
    exact H.canonicalPullbackDensityInChart_pos_of_finiteCoordinate_deriv_ne_zero
      e he hz hreg (A.finiteCoordinate_deriv_ne_zero e he z hz hreg)
  densitySq_transition := A.densitySq_transition

/-- Analytic branch data supplies the canonical regular-locus pullback metric data.

%%handwave
name:
  Canonical pullback metric data from analytic branches
statement:
  Compatible analytic finite branches determine a smooth regular-locus conformal metric whose density is their Poincaré pullback and whose curvature transfers to the off-real model.
-/
noncomputable def toRegularLocusCanonicalPullbackMetricData
    (A : H.RegularLocusCanonicalBranchAnalyticData) :
    H.RegularLocusCanonicalPullbackMetricData where
  metric := A.toConformalMetricOn
  metric_smooth_on_regularSet := by
    intro e he
    exact A.smooth_densitySq e he
  curvature_transfers_to_normalizedFiniteCoordinate := by
    intro e he z hz hreg
    exact A.curvature_transfers_to_normalizedFiniteCoordinate e he z hz hreg
  density_eq_normalizedFiniteCoordinate_pullback := by
    intro e he z hz hreg
    exact H.canonicalPullbackDensityInChart_eq_pullback_formula e he hz hreg

end RegularLocusCanonicalBranchAnalyticData


/--
Metric data on the canonical regular locus of a real-projective developing map.

This packages the openness of the regular locus together with the conformal
metric, curvature, and pullback-density conditions on that locus.
-/
structure RegularLocusMetricData (H : P.PGL2RHolonomyData x₀) extends
    H.RegularLocusTopologicalData, H.RegularLocusConformalMetricData

end ComplexProjectiveStructure.PGL2RHolonomyData

/--
%%handwave
name:
  Singular hyperbolic metric associated with real projective holonomy
statement:
  Let $P$ be a complex projective structure on $X$ with developing map
  $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb{CP}^1$ and holonomy in
  $\mathrm{PGL}_2(\mathbb R)$. A singular hyperbolic metric associated with
  $P$ consists of the singular locus
  $S=\operatorname{dev}^{-1}(\mathbb{RP}^1)/\pi_1(X,x_0)$ and a smooth
  curvature-$(-1)$ conformal metric on the open set $X\setminus S$, locally
  given by
  \[
    \frac{|F'(z)|^2}{(\operatorname{Im}F(z))^2}|dz|^2
  \]
  for finite normalized projective branches $F$.
-/
structure SingularHyperbolicMetric (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] where
  /-- The projective structure whose real projective holonomy produces the metric. -/
  projectiveStructure : ComplexProjectiveStructure X
  /-- The basepoint used for the real projective holonomy certificate. -/
  basepoint : X
  /-- Real projective holonomy data tied to the same projective atlas. -/
  pgl2rHolonomyData : projectiveStructure.PGL2RHolonomyData basepoint
  /-- The real-projective locus of the developing map. -/
  realProjectiveLocus : Set X
  /-- The regular part on which the metric is smooth. -/
  regularSet : Set X
  /-- The regular set is the complement of the real-projective locus. -/
  regularSet_eq_compl_realProjectiveLocus : regularSet = realProjectiveLocusᶜ
  /-- The regular set is open in the surface. -/
  regularSet_open : IsOpen regularSet
  /-- The singular locus is exactly the projected preimage of the real projective line. -/
  realProjectiveLocus_eq_developing_preimage :
    ∀ y :
      pgl2rHolonomyData.holonomy_constructed_from_projective_charts.developingData.cover.total,
      pgl2rHolonomyData.holonomy_constructed_from_projective_charts.developingData.cover.projection y
          ∈ realProjectiveLocus ↔
        RiemannSphere.IsRealProjectivePoint
          (pgl2rHolonomyData.holonomy_constructed_from_projective_charts.developingData.developingMap y)
  /-- The conformal metric on the regular locus. -/
  metric : ConformalMetricOn X regularSet
  /-- The regular-locus metric is smooth. -/
  metric_smooth_on_regularSet : metric.IsSmooth
  /-- The metric has curvature `-1` on the regular locus. -/
  curvature_minus_one : metric.HasCurvatureMinusOne
  /--
  Away from the real-projective locus, the metric density is locally the
  pullback of the off-real-line hyperbolic density by a finite normalized
  projective coordinate.
  -/
  pullback_density_on_regularSet :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ),
      z ∈ e.target →
      e.symm z ∈ regularSet →
        ∃ F : ℂ → ℂ, ∃ chart : ProjectiveChart X, ∃ normalization : MobiusRepresentative,
          chart ∈ projectiveStructure.atlasSet ∧
            e.symm z ∈ chart.source ∧
              (∀ᶠ w in 𝓝 z,
                ((F w : ℂ) : RiemannSphere) = normalization • chart (e.symm w)) ∧
                  (F z).im ≠ 0 ∧
                    metric.densitySqInChart e he z =
                      ((F z).im ^ 2)⁻¹ * Complex.normSq (deriv F z)

namespace ComplexProjectiveStructure.PGL2RHolonomyData.RegularLocusMetricData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {P : ComplexProjectiveStructure X}
    {H : P.PGL2RHolonomyData x₀}

/-- Combine topological and conformal data into full regular-locus metric data.

%%handwave
name:
  Regular-locus metric data from topology and conformal geometry
statement:
  An open regular locus together with smooth curvature-$-1$ conformal pullback data combine into the full regular-locus metric package.
-/
def ofTopologicalAndConformal
    (T : H.RegularLocusTopologicalData)
    (M : H.RegularLocusConformalMetricData) :
    H.RegularLocusMetricData where
  toRegularLocusTopologicalData := T
  toRegularLocusConformalMetricData := M

/-- The singular hyperbolic metric obtained from metric data on the canonical regular locus.

%%handwave
name:
  Singular hyperbolic metric from regular-locus data
statement:
  Full metric data on the complement of the descended real-projective locus determine a singular hyperbolic metric whose singular set is that locus and whose regular metric is the prescribed Poincaré pullback metric.
-/
def toSingularHyperbolicMetric
    (M : H.RegularLocusMetricData) :
    SingularHyperbolicMetric X where
  projectiveStructure := P
  basepoint := x₀
  pgl2rHolonomyData := H
  realProjectiveLocus := H.realProjectiveLocus
  regularSet := H.regularSet
  regularSet_eq_compl_realProjectiveLocus := rfl
  regularSet_open := M.regularSet_open
  realProjectiveLocus_eq_developing_preimage :=
    H.realProjectiveLocus_eq_developing_preimage
  metric := M.metric
  metric_smooth_on_regularSet := M.metric_smooth_on_regularSet
  curvature_minus_one := M.curvature_minus_one
  pullback_density_on_regularSet := M.pullback_density_on_regularSet

end ComplexProjectiveStructure.PGL2RHolonomyData.RegularLocusMetricData



namespace ComplexProjectiveStructure

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/-- The regular-locus metric construction package for the forward direction.

%%handwave
name:
  Existence of the canonical regular-locus metric construction
statement:
  A based projective structure admits the regular-locus metric construction when every compatible real-holonomy developing datum yields a smooth canonical Poincaré pullback metric with curvature $-1$.
-/
def HasRegularLocusMetricConstruction (x₀ : X) (P : ComplexProjectiveStructure X) :
    Prop :=
  ∀ H : P.PGL2RHolonomyData x₀, Nonempty H.RegularLocusCanonicalPullbackMetricData

/-- The branch-analytic construction package for the forward direction.

%%handwave
name:
  Existence of canonical analytic branch data
statement:
  A based projective structure admits canonical analytic branch data when every compatible real-holonomy developing datum yields nondegenerate finite branches with compatible smooth pullback densities and model curvature.
-/
def HasRegularLocusCanonicalBranchAnalyticConstruction
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀, Nonempty H.RegularLocusCanonicalBranchAnalyticData

/--
Canonical-density analytic construction package: smoothness of the canonical
density and transfer of its curvature calculation to the off-real model
coordinate.

%%handwave
name:
  Existence of canonical-density analytic data
statement:
  A based projective structure admits canonical-density analytic data when, for every compatible real-holonomy developing datum, its canonical chartwise density is smooth and its curvature agrees with the off-real Poincaré model at each normalized finite developing value.
-/
def HasRegularLocusCanonicalDensityAnalyticConstruction
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀, Nonempty H.RegularLocusCanonicalDensityAnalyticData

/--
Branch-level analytic construction package for the forward direction:
smoothness and curvature transfer for the fixed local pullback-density
functions.

%%handwave
name:
  Existence of local pullback-density analytic data
statement:
  A based projective structure admits local pullback-density analytic data when every compatible real-holonomy developing datum has smooth finite-branch Poincaré pullback densities whose curvature agrees with the off-real model.
-/
def HasRegularLocusLocalPullbackDensityAnalyticConstruction
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀,
    Nonempty H.RegularLocusLocalPullbackDensityAnalyticData

/--
Explicit-Laplacian form of the local calculation for the pullback density. This
asks for the Laplacian of the local expression `log |F'| - log |Im F|`.

%%handwave
name:
  Explicit local Laplacian property for pullback densities
statement:
  A based projective structure has the explicit local Laplacian property when every regular finite developing branch $F$ satisfies $\Delta(\log|F'|-\log|\operatorname{Im}F|)=|F'|^2/(\operatorname{Im}F)^2$ at its base point.
-/
def HasRegularLocusLocalPullbackDensityExplicitLaplacian
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀,
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        Laplacian.laplacian C.pullbackLogDensityExpression z =
          C.pullbackDensityFunction z

/--
Height-term form of the local calculation: after the derivative term has been
proved harmonic, the moving height term supplies minus the pulled-back
hyperbolic density.

%%handwave
name:
  Height-term Laplacian property for pullback densities
statement:
  A based projective structure has the height-term Laplacian property when every regular finite developing branch $F$ satisfies $\Delta\log|\operatorname{Im}F|=-|F'|^2/(\operatorname{Im}F)^2$ at its base point.
-/
def HasRegularLocusLocalPullbackDensityImaginaryLaplacian
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀,
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        Laplacian.laplacian C.pullbackLogImaginaryTerm z =
          - C.pullbackDensityFunction z

/--
The moving height term has the required local Laplacian for every real
projective holonomy certificate.

%%handwave
name:
  Laplacian of the moving height term
statement:
  For every finite normalized developing branch F away from the real projective line, Δ log|Im F| = −|F′|²/(Im F)².
proof:
  Differentiate log|Im F| using the Wirtinger formulas for a holomorphic branch; the mixed derivative is minus one quarter of the Poincare pullback density, hence the real Laplacian has the stated value.
-/
theorem hasRegularLocusLocalPullbackDensityImaginaryLaplacian
    (P : ComplexProjectiveStructure X) (x₀ : X) :
    P.HasRegularLocusLocalPullbackDensityImaginaryLaplacian x₀ := by
  intro H e he z hz hreg
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  exact C.pullbackLogImaginaryTerm_laplacian_eq_neg_pullbackDensityFunction he hz

/--
Liouville-equation form of the local calculation for the pullback density.

%%handwave
name:
  Local Liouville property for pullback densities
statement:
  A based projective structure has the local Liouville property when every regular finite-branch squared density $q=|F'|^2/(\operatorname{Im}F)^2$ satisfies $\Delta(\tfrac12\log q)=q$ at its base point.
-/
def HasRegularLocusLocalPullbackDensityLiouvilleEquation
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀,
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        Laplacian.laplacian (logDensityFromDensitySq C.pullbackDensityFunction) z =
          C.pullbackDensityFunction z

/--
The explicit local Laplacian calculation implies the Liouville equation for
the local pullback density.

%%handwave
name:
  The explicit pullback Laplacian implies Liouville
statement:
  If Δ(log|F′| − log|Im F|) = |F′|²/(Im F)² for every regular finite branch F, then the logarithmic pullback density satisfies the Liouville equation Δ log ρ = ρ².
proof:
  Identify log ρ with log|F′| − log|Im F| locally and substitute the assumed explicit Laplacian formula.
-/
theorem hasRegularLocusLocalPullbackDensityLiouvilleEquation_of_localPullbackDensityExplicitLaplacian
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityExplicitLaplacian x₀) :
    P.HasRegularLocusLocalPullbackDensityLiouvilleEquation x₀ := by
  intro H e he z hz hreg
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  exact C.pullbackDensityFunction_liouville_of_laplacian_logDensityExpression he hz
    (h H e he z hz hreg)

/--
The moving-height Laplacian calculation gives the explicit local Liouville
calculation, because the derivative term is already harmonic.

%%handwave
name:
  The height-term Laplacian gives the explicit pullback formula
statement:
  If Δ log|Im F| = −|F′|²/(Im F)² for every regular finite branch, then Δ(log|F′| − log|Im F|) = |F′|²/(Im F)².
proof:
  The logarithm of the nonvanishing holomorphic derivative F′ is harmonic, so only the assumed height-term Laplacian remains.
-/
theorem hasRegularLocusLocalPullbackDensityExplicitLaplacian_of_localPullbackDensityImaginaryLaplacian
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityImaginaryLaplacian x₀) :
    P.HasRegularLocusLocalPullbackDensityExplicitLaplacian x₀ := by
  intro H e he z hz hreg
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  exact C.pullbackDensityFunction_laplacian_logDensityExpression_of_imaginary he hz
    (h H e he z hz hreg)

/--
The Liouville equation for the local pullback density gives the branch-level
analytic construction.

%%handwave
name:
  Local pullback-density analytic data from the Liouville equation Δ log ρ = ρ²
statement:
  If every regular finite developing branch satisfies the Liouville equation Δ log ρ = ρ², then its pullback density is smooth and has curvature −1.
proof:
  Convert the assumed local identity to the Liouville equation for the pullback density, then use K = −(Δ log ρ)/ρ². The necessary branch smoothness is already established.
-/
theorem hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityLiouvilleEquation
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityLiouvilleEquation x₀) :
    P.HasRegularLocusLocalPullbackDensityAnalyticConstruction x₀ := by
  intro H
  exact
    ⟨PGL2RHolonomyData.RegularLocusLocalPullbackDensityAnalyticData.ofLiouvilleEquation
      (H := H) (h H)⟩

/--
The explicit local Laplacian calculation gives the branch-level analytic
construction.

%%handwave
name:
  Local pullback-density analytic data from the explicit identity Δ(log|F′| − log|Im F|) = ρ²
statement:
  If every regular finite developing branch satisfies the explicit identity Δ(log|F′| − log|Im F|) = ρ², then its pullback density is smooth and has curvature −1.
proof:
  Convert the assumed local identity to the Liouville equation for the pullback density, then use K = −(Δ log ρ)/ρ². The necessary branch smoothness is already established.
-/
theorem hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityExplicitLaplacian
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityExplicitLaplacian x₀) :
    P.HasRegularLocusLocalPullbackDensityAnalyticConstruction x₀ :=
  P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityLiouvilleEquation
    (P.hasRegularLocusLocalPullbackDensityLiouvilleEquation_of_localPullbackDensityExplicitLaplacian h)

/--
The moving-height Laplacian calculation gives the branch-level analytic
construction.

%%handwave
name:
  Local pullback-density analytic data from the height identity Δ log|Im F| = −ρ²
statement:
  If every regular finite developing branch satisfies the height identity Δ log|Im F| = −ρ², then its pullback density is smooth and has curvature −1.
proof:
  Convert the assumed local identity to the Liouville equation for the pullback density, then use K = −(Δ log ρ)/ρ². The necessary branch smoothness is already established.
-/
theorem hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityImaginaryLaplacian
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityImaginaryLaplacian x₀) :
    P.HasRegularLocusLocalPullbackDensityAnalyticConstruction x₀ :=
  P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityExplicitLaplacian
    (P.hasRegularLocusLocalPullbackDensityExplicitLaplacian_of_localPullbackDensityImaginaryLaplacian h)

/--
The branch-level local pullback-density analytic construction is internal.

%%handwave
name:
  Analytic construction of the local pullback densities
statement:
  For every complex projective structure with real projective holonomy, each regular finite developing branch has smooth Poincare pullback density |F′|²/(Im F)² and curvature −1.
proof:
  The moving-height Laplacian is computed directly; harmonicity of log|F′| yields Liouville, which supplies the smooth curvature −1 branch data.
-/
theorem hasRegularLocusLocalPullbackDensityAnalyticConstruction
    (P : ComplexProjectiveStructure X) (x₀ : X) :
    P.HasRegularLocusLocalPullbackDensityAnalyticConstruction x₀ :=
  P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityImaginaryLaplacian
    (P.hasRegularLocusLocalPullbackDensityImaginaryLaplacian x₀)

/--
Branch-level pullback-density analytic data implies the canonical-density
analytic construction.

%%handwave
name:
  Local branch densities determine the canonical density
statement:
  If all local finite developing branches have smooth curvature −1 pullback densities, then the chartwise canonical density on the regular locus is smooth and its curvature transfers to each normalized finite coordinate.
proof:
  At every regular chart point, identify the canonical density locally with the chosen branch pullback density and transfer smoothness and curvature through eventual equality.
-/
theorem hasRegularLocusCanonicalDensityAnalyticConstruction_of_localPullbackDensityAnalyticConstruction
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityAnalyticConstruction x₀) :
    P.HasRegularLocusCanonicalDensityAnalyticConstruction x₀ := by
  intro H
  rcases h H with ⟨A⟩
  exact ⟨A.toRegularLocusCanonicalDensityAnalyticData⟩

/--
The canonical-density analytic construction is internal.

%%handwave
name:
  Analytic construction of the canonical regular-locus density
statement:
  For a complex projective structure with real projective holonomy, the canonical chartwise Poincare pullback density is smooth on the regular locus and has curvature −1.
proof:
  Apply the local pullback-density construction and identify every canonical chart density locally with its normalized finite branch density.
-/
theorem hasRegularLocusCanonicalDensityAnalyticConstruction
    (P : ComplexProjectiveStructure X) (x₀ : X) :
    P.HasRegularLocusCanonicalDensityAnalyticConstruction x₀ :=
  P.hasRegularLocusCanonicalDensityAnalyticConstruction_of_localPullbackDensityAnalyticConstruction
    (P.hasRegularLocusLocalPullbackDensityAnalyticConstruction x₀)

/--
Smoothness and curvature transfer for the canonical density now imply the full
branch-analytic package, since the branch transitions are proved internally.

%%handwave
name:
  Canonical density data give compatible branch data
statement:
  Smoothness and curvature transfer for the canonical regular-locus density produce normalized finite branches whose densities agree under real projective coordinate changes.
proof:
  Use the canonical real-projective transition maps between finite branches; invariance of the Poincare density makes the branch pullbacks agree, while the assumed density data supply smoothness and curvature.
-/
theorem hasRegularLocusCanonicalBranchAnalyticConstruction_of_canonicalDensityAnalyticConstruction
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusCanonicalDensityAnalyticConstruction x₀) :
    P.HasRegularLocusCanonicalBranchAnalyticConstruction x₀ := by
  intro H
  rcases h H with ⟨A⟩
  exact
    ⟨PGL2RHolonomyData.RegularLocusCanonicalBranchAnalyticData.ofCanonicalTransitions
      (H := H) A.smooth_densitySq A.curvature_transfers_to_normalizedFiniteCoordinate⟩

/--
The canonical branch-analytic construction is internal.

%%handwave
name:
  Canonical analytic branch construction on the regular locus
statement:
  Every complex projective structure with real projective holonomy admits compatible normalized finite branches on its regular locus, with smooth Poincare pullback densities of curvature −1.
proof:
  Construct the canonical density from local pullbacks, then use the developing-map transition maps to package compatible branch data.
-/
theorem hasRegularLocusCanonicalBranchAnalyticConstruction
    (P : ComplexProjectiveStructure X) (x₀ : X) :
    P.HasRegularLocusCanonicalBranchAnalyticConstruction x₀ :=
  P.hasRegularLocusCanonicalBranchAnalyticConstruction_of_canonicalDensityAnalyticConstruction
    (P.hasRegularLocusCanonicalDensityAnalyticConstruction x₀)

/--
Canonical branch analytic data supplies the regular-locus metric construction
needed by the forward direction.

%%handwave
name:
  Compatible branches construct the regular-locus metric
statement:
  Compatible normalized finite branches with smooth curvature −1 pullback densities determine a conformal metric of curvature −1 on the regular locus.
proof:
  Glue the branch pullback densities using their real projective transition invariance and retain their smoothness and curvature transfer.
-/
theorem hasRegularLocusMetricConstruction_of_canonicalBranchAnalyticConstruction
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusCanonicalBranchAnalyticConstruction x₀) :
    P.HasRegularLocusMetricConstruction x₀ := by
  intro H
  rcases h H with ⟨A⟩
  exact ⟨A.toRegularLocusCanonicalPullbackMetricData⟩

/--
The regular-locus metric construction is internal.

%%handwave
name:
  Construction of the regular-locus hyperbolic metric
statement:
  Every complex projective structure with real projective holonomy carries a smooth conformal metric of curvature −1 on the complement of its real-projective developing locus.
proof:
  Build compatible normalized finite branches and glue their Poincare pullback densities into the canonical regular-locus conformal metric.
-/
theorem hasRegularLocusMetricConstruction
    (P : ComplexProjectiveStructure X) (x₀ : X) :
    P.HasRegularLocusMetricConstruction x₀ :=
  P.hasRegularLocusMetricConstruction_of_canonicalBranchAnalyticConstruction
    (P.hasRegularLocusCanonicalBranchAnalyticConstruction x₀)

end ComplexProjectiveStructure

/--
%%handwave
name:
  Induction of a singular hyperbolic metric
statement:
  A based complex projective structure induces a singular hyperbolic metric when there exists such a metric whose underlying projective structure and base point are the given ones.
-/
def ComplexProjectiveStructure.InducesSingularHyperbolicMetric
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∃ metric : SingularHyperbolicMetric X,
    metric.projectiveStructure = P ∧ metric.basepoint = x₀

/--
A real-projective holonomy certificate produces a singular metric for this projective structure.

%%handwave
name:
  Real projective holonomy induces a singular hyperbolic metric
statement:
  A complex projective structure P with holonomy in PGL₂(ℝ) determines a singular hyperbolic metric whose singular set is the projected inverse image of ℝP¹ and whose regular metric is locally |F′|²/(Im F)²|dz|².
proof:
  Choose the real-projective holonomy data, construct the canonical curvature −1 metric on the open complement of the real-projective locus, and package it with the developing-map description of the singular set.
-/
theorem ComplexProjectiveStructure.inducesSingularHyperbolicMetric
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (hP : HasPGL2RHolonomy x₀ P) :
    P.InducesSingularHyperbolicMetric x₀ := by
  rcases hP with ⟨H⟩
  rcases P.hasRegularLocusMetricConstruction x₀ H with ⟨D⟩
  let M : H.RegularLocusMetricData :=
    ComplexProjectiveStructure.PGL2RHolonomyData.RegularLocusMetricData.ofTopologicalAndConformal
      H.regularLocusTopologicalData D.toRegularLocusConformalMetricData
  exact ⟨M.toSingularHyperbolicMetric, rfl, rfl⟩

/--
%%handwave
name:
  Real projective structures induce singular hyperbolic metrics
statement:
  A complex projective structure whose holonomy lies in
  $\mathrm{PGL}_2(\mathbb R)$ determines a possibly singular hyperbolic
  metric on the complement of its real-projective locus.
proof:
  On the regular locus, the metric is pulled back along the developing map.
  [Real projective holonomy preserves the real projective line and the hyperbolic metric on its complement](lean:JJMath.pgl2r_preserves_offRealLineDensity_holomorphic), so the locally pulled-back metrics glue.
  The derivative part of the logarithmic density is harmonic, while the [height-term Laplacian calculation transfers curvature to the off-real-line model coordinate](lean:JJMath.ComplexProjectiveStructure.hasRegularLocusLocalPullbackDensityImaginaryLaplacian), where the density $\operatorname{Im}(z)^{-2}$ has curvature $-1$.
tags:
  milestone
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (hP : HasPGL2RHolonomy x₀ P) :
    P.InducesSingularHyperbolicMetric x₀ :=
  P.inducesSingularHyperbolicMetric hP

end

end JJMath
