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

/-- View a real projective Mobius representative as a complex Mobius representative. -/
def realProjectiveMobiusRepresentativeAsMobiusRepresentative :
    RealProjectiveMobiusRepresentative →* MobiusRepresentative :=
  Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)

/-- The complex projective class of a real projective Mobius representative. -/
def realProjectiveMobiusRepresentativeToMobiusGroup :
    RealProjectiveMobiusRepresentative →* MobiusGroup :=
  (Matrix.ProjGenLinGroup.mk : MobiusRepresentative →* MobiusGroup).comp
    realProjectiveMobiusRepresentativeAsMobiusRepresentative

/-- The subgroup of $\mathrm{PGL}_2(\mathbb C)$ represented by real matrices. -/
def pgl2rMobiusSubgroup : Subgroup MobiusGroup :=
  MonoidHom.range realProjectiveMobiusRepresentativeToMobiusGroup

/-- The complexified orientation-preserving real Mobius group lies in the real projective subgroup.

%%handwave
name:
  Real Möbius transformations define real projective classes
statement:
  The complex projective class obtained from any element of \(\mathrm{PSL}_2(\mathbb R)\) belongs to the embedded subgroup \(\mathrm{PGL}_2(\mathbb R)\subseteq\mathrm{PGL}_2(\mathbb C)\).
proof:
  Choose a determinant-one real matrix representing the class. Its complexification is also the complexification of the same invertible real matrix, so its projective class lies in the indicated image.
-/
theorem realMobiusToMobiusGroup_mem_pgl2rMobiusSubgroup
  (g : RealMobiusGroup) :
  realMobiusToMobiusGroup g ∈ pgl2rMobiusSubgroup := by
  induction g using QuotientGroup.induction_on with
  | H A =>
      change realMobiusToMobiusGroup (realMobiusProjection A) ∈ pgl2rMobiusSubgroup
      rw [realMobiusToMobiusGroup_realMobiusProjection]
      refine ⟨(A : GL (Fin 2) ℝ), ?_⟩
      have hgl :
          Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
              (Matrix.SpecialLinearGroup.toGL A) =
            Matrix.SpecialLinearGroup.mapGL ℂ A := by
        ext i j
        simp [Matrix.SpecialLinearGroup.mapGL]
      exact congrArg Matrix.ProjGenLinGroup.mk hgl

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
-/
def HasPGL2RHolonomy {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  Nonempty (P.PGL2RHolonomyData x₀)

namespace ComplexProjectiveStructure.RealHolonomyData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {P : ComplexProjectiveStructure X}

/-- A PSL-valued real-holonomy certificate is also a PGL-valued certificate. -/
def toPGL2RHolonomyData
    (H : P.RealHolonomyData x₀) :
    P.PGL2RHolonomyData x₀ where
  projectiveHolonomy := H.projectiveHolonomy
  holonomy_constructed_from_projective_charts :=
    H.holonomy_constructed_from_projective_charts
  projectiveHolonomy_real := by
    intro γ
    have hγ :
        H.projectiveHolonomy γ = realMobiusToMobiusGroup (H.realHolonomy γ) := by
      change H.projectiveHolonomy.toMonoidHom γ =
        (realMobiusToMobiusGroup.comp H.realHolonomy.toMonoidHom) γ
      rw [H.projectiveHolonomy_eq_real]
    rw [hγ]
    exact realMobiusToMobiusGroup_mem_pgl2rMobiusSubgroup (H.realHolonomy γ)

end ComplexProjectiveStructure.RealHolonomyData

/-- PSL-valued real holonomy is a special case of PGL-valued real projective holonomy.

%%handwave
name:
  Real special-linear holonomy implies real projective holonomy
statement:
  A complex projective structure whose based holonomy is induced from \(\mathrm{PSL}_2(\mathbb R)\) also has holonomy in \(\mathrm{PGL}_2(\mathbb R)\).
proof:
  Keep the same developing-map construction and complex holonomy representation, and regard each orientation-preserving real Möbius transformation as a real projective transformation.
-/
theorem hasPGL2RHolonomy_of_hasPSL2RHolonomy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : HasPSL2RHolonomy x₀ P) :
    HasPGL2RHolonomy x₀ P := by
  rcases h with ⟨H⟩
  exact ⟨H.toPGL2RHolonomyData⟩

/-- The real projective line inside the Riemann sphere. -/
def realProjectiveLineInRiemannSphere : Set RiemannSphere :=
  Set.range (OnePoint.map (algebraMap ℝ ℂ) : OnePoint ℝ → RiemannSphere)

/-- A point of the Riemann sphere lies on the real projective line. -/
def RiemannSphere.IsRealProjectivePoint (z : RiemannSphere) : Prop :=
  z ∈ realProjectiveLineInRiemannSphere

/-- The affine finite part of a point of the Riemann sphere, with infinity sent to `0`. -/
def RiemannSphere.finitePart (z : RiemannSphere) : ℂ :=
  z.elim 0 id

/--
%%handwave
name:
  Finite part of an affine sphere point
statement:
  For every \(z\in\mathbb C\), the finite coordinate of the point \([z:1]\in\mathbb P^1(\mathbb C)\) is \(z\).
proof:
  This is the affine branch of the definition of the finite coordinate.
-/
@[simp]
theorem RiemannSphere.finitePart_coe (z : ℂ) :
    RiemannSphere.finitePart (z : RiemannSphere) = z :=
  rfl

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

/-- A continuous Mobius normalization has closed real-projective preimage.

%%handwave
name:
  Closed real locus under a continuous Möbius map
statement:
  If a Möbius transformation \(A\) acts continuously on \(\mathbb P^1(\mathbb C)\), then \(\{p:A(p)\in\mathbb P^1(\mathbb R)\}\) is closed.
proof:
  This set is the inverse image of the closed real projective line under the continuous action of \(A\).
-/
theorem mobius_realProjectiveLine_preimage_closed_of_continuous
    (A : MobiusRepresentative)
    (hA : Continuous fun z : RiemannSphere ↦ A • z) :
    IsClosed {z : RiemannSphere | RiemannSphere.IsRealProjectivePoint (A • z)} := by
  change IsClosed ((fun z : RiemannSphere ↦ A • z) ⁻¹' realProjectiveLineInRiemannSphere)
  exact realProjectiveLineInRiemannSphere_closed.preimage hA

/-- A continuous Mobius normalization has open off-real-projective preimage.

%%handwave
name:
  Open nonreal locus under a continuous Möbius map
statement:
  If a Möbius transformation \(A\) acts continuously on \(\mathbb P^1(\mathbb C)\), then \(\{p:A(p)\notin\mathbb P^1(\mathbb R)\}\) is open.
proof:
  This set is the inverse image of the open complement of the real projective line under the continuous action of \(A\).
-/
theorem mobius_offRealProjectiveLine_preimage_open_of_continuous
    (A : MobiusRepresentative)
    (hA : Continuous fun z : RiemannSphere ↦ A • z) :
    IsOpen {z : RiemannSphere | ¬ RiemannSphere.IsRealProjectivePoint (A • z)} := by
  change IsOpen ((fun z : RiemannSphere ↦ A • z) ⁻¹' realProjectiveLineInRiemannSphereᶜ)
  exact realProjectiveLineInRiemannSphere_closed.isOpen_compl.preimage hA

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

/-- Real projective transformations reflect membership in the real projective line.

%%handwave
name:
  Real projective transformations reflect the real projective line
statement:
  If \(A\in\mathrm{GL}_2(\mathbb R)\) and \(A(p)\in\mathbb P^1(\mathbb R)\), then \(p\in\mathbb P^1(\mathbb R)\).
proof:
  Apply preservation of the real projective line to \(A^{-1}\) and use \(A^{-1}A(p)=p\).
-/
theorem realProjectiveMobius_reflects_realProjectiveLine
    (A : RealProjectiveMobiusRepresentative) {z : RiemannSphere}
    (hz : RiemannSphere.IsRealProjectivePoint
      (realProjectiveMobiusRepresentativeAsMobiusRepresentative A • z)) :
    RiemannSphere.IsRealProjectivePoint z := by
  have hpre := realProjectiveMobius_preserves_realProjectiveLine A⁻¹ hz
  have hcancel :
      realProjectiveMobiusRepresentativeAsMobiusRepresentative A⁻¹ •
        (realProjectiveMobiusRepresentativeAsMobiusRepresentative A • z) = z := by
    rw [← mul_smul]
    simp [realProjectiveMobiusRepresentativeAsMobiusRepresentative]
  simpa [hcancel] using hpre

/-- Real projective transformations preserve the complement of the real projective line.

%%handwave
name:
  Real projective transformations preserve the nonreal locus
statement:
  Every \(A\in\mathrm{GL}_2(\mathbb R)\) maps \(\mathbb P^1(\mathbb C)\setminus\mathbb P^1(\mathbb R)\) into itself.
proof:
  If \(A(p)\) were real projective, preservation under \(A^{-1}\) would force \(p\) to be real projective as well.
-/
theorem realProjectiveMobius_preserves_offRealProjectiveLine
    (A : RealProjectiveMobiusRepresentative) {z : RiemannSphere}
    (hz : ¬ RiemannSphere.IsRealProjectivePoint z) :
    ¬ RiemannSphere.IsRealProjectivePoint
      (realProjectiveMobiusRepresentativeAsMobiusRepresentative A • z) := by
  intro hreal
  exact hz (realProjectiveMobius_reflects_realProjectiveLine A hreal)

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

/-- Any representative of a real projective class preserves the off-real projective locus.

%%handwave
name:
  Complex representatives of real projective classes preserve the nonreal locus
statement:
  Let \(G\in\mathrm{PGL}_2(\mathbb R)\subseteq\mathrm{PGL}_2(\mathbb C)\). Every complex matrix representing \(G\) maps \(\mathbb P^1(\mathbb C)\setminus\mathbb P^1(\mathbb R)\) into itself.
proof:
  Replace the chosen matrix by a real representative without changing its projective action. A real projective transformation preserves the complement of the real projective line.
-/
theorem pgl2r_representative_preserves_offRealProjectiveLine
    {G : MobiusGroup} (hG : G ∈ pgl2rMobiusSubgroup)
    {A : MobiusRepresentative} (hA : Matrix.ProjGenLinGroup.mk A = G)
    {z : RiemannSphere} (hz : ¬ RiemannSphere.IsRealProjectivePoint z) :
    ¬ RiemannSphere.IsRealProjectivePoint (A • z) := by
  rcases hG with ⟨R, hR⟩
  have hAR : Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk (realProjectiveMobiusRepresentativeAsMobiusRepresentative R) := by
    rw [hA, ← hR]
    rfl
  intro hreal
  have hrealR :
      RiemannSphere.IsRealProjectivePoint
        (realProjectiveMobiusRepresentativeAsMobiusRepresentative R • z) := by
    rwa [mobiusRepresentative_smul_eq_of_mk_eq hAR] at hreal
  exact hz (realProjectiveMobius_reflects_realProjectiveLine R hrealR)

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

/-- Off-real membership of the developing map is constant on cover fibers.

%%handwave
name:
  The off-real developing locus is constant on cover fibers
statement:
  If two cover points project to the same surface point and one developing value lies outside ℝP¹, then the other also lies outside ℝP¹.
proof:
  Relate the lifts by a deck transformation and use that its PGL₂(ℝ) holonomy preserves the complement of ℝP¹.
-/
theorem developingMap_not_isRealProjectivePoint_of_same_fiber
    (H : P.PGL2RHolonomyData x₀)
    {y z : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (hyz : H.holonomy_constructed_from_projective_charts.developingData.cover.projection y =
      H.holonomy_constructed_from_projective_charts.developingData.cover.projection z)
    (hy : ¬ RiemannSphere.IsRealProjectivePoint
      (H.holonomy_constructed_from_projective_charts.developingData.developingMap y)) :
    ¬ RiemannSphere.IsRealProjectivePoint
      (H.holonomy_constructed_from_projective_charts.developingData.developingMap z) := by
  let cover := H.holonomy_constructed_from_projective_charts.developingData.cover
  rcases cover.deckAction_same_fiber_transitive y z hyz with ⟨γ, hγ⟩
  rcases (H.holonomy_constructed_from_projective_charts.developingData).equivariant_representatives γ with
    ⟨A, hA, hdev⟩
  rw [← hγ, hdev]
  exact pgl2r_representative_preserves_offRealProjectiveLine
    (H.projectiveHolonomy_real γ) hA hy

/-- Real-projective membership of the developing map is independent of the chosen lift.

%%handwave
name:
  Real-projective membership is independent of the lift
statement:
  Two developing-cover points over the same surface point have developing values in ℝP¹ simultaneously.
proof:
  Apply fiberwise preservation in each direction, reversing the equality of projections for the converse.
-/
theorem developingMap_isRealProjectivePoint_iff_same_fiber
    (H : P.PGL2RHolonomyData x₀)
    {y z : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (hyz : H.holonomy_constructed_from_projective_charts.developingData.cover.projection y =
      H.holonomy_constructed_from_projective_charts.developingData.cover.projection z) :
    RiemannSphere.IsRealProjectivePoint
        (H.holonomy_constructed_from_projective_charts.developingData.developingMap y) ↔
      RiemannSphere.IsRealProjectivePoint
        (H.holonomy_constructed_from_projective_charts.developingData.developingMap z) := by
  constructor
  · exact H.developingMap_isRealProjectivePoint_of_same_fiber hyz
  · exact H.developingMap_isRealProjectivePoint_of_same_fiber hyz.symm

/--
Two local developing-chart agreements over the same surface point differ by a
real projective Mobius transformation.

%%handwave
name:
  Normalized local developing charts have real-projective transitions
statement:
  Two local developing-chart agreements defined at the same surface point differ there by an element of PGL₂(ℝ) after their normalizations.
proof:
  Lift the point through both local sections, relate the lifts by a deck transformation, and use developing-map equivariance together with real projective holonomy.
-/
theorem localAgreement_normalizedChart_transition_realProjective
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
          (L₁.normalization • L₁.chart x) := by
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
  refine ⟨R, ?_⟩
  have hAR : Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk (realProjectiveMobiusRepresentativeAsMobiusRepresentative R) := by
    rw [hA, ← hR]
    rfl
  have hdev_eq :
      developingData.developingMap y₂x = A • developingData.developingMap y₁x := by
    rw [← hγ]
    exact hdev y₁x
  have hdev_eq_real :
      developingData.developingMap y₂x =
        realProjectiveMobiusRepresentativeAsMobiusRepresentative R •
          developingData.developingMap y₁x := by
    rw [hdev_eq, mobiusRepresentative_smul_eq_of_mk_eq hAR]
  have h₁ := L₁.developing_eq_normalized_chart ⟨x, hx₁⟩
  have h₂ := L₂.developing_eq_normalized_chart ⟨x, hx₂⟩
  rw [h₂, h₁] at hdev_eq_real
  exact hdev_eq_real

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

/--
Finite affine coordinates from two local developing-chart agreements differ by
the holomorphic fractional-linear formula of a real projective matrix.

%%handwave
name:
  Finite local developing values differ by a real fractional-linear map
statement:
  If two normalized local developing charts have finite off-real values z₁ and z₂ at the same point, then z₂=(az₁+b)/(cz₁+d) for some real projective matrix.
proof:
  Use the real-projective transition between the normalized charts and pass from projective to affine coordinates; the denominator is nonzero because z₁ is off real.
-/
theorem localAgreement_finiteCoordinate_transition_realProjective
    (H : P.PGL2RHolonomyData x₀)
    {y₁ y₂ : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L₁ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₁)
    (L₂ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₂)
    {x : X} (hx₁ : x ∈ L₁.chart.source) (hx₂ : x ∈ L₂.chart.source)
    {z₁ z₂ : ℂ}
    (hz₁_eq : L₁.normalization • L₁.chart x = (z₁ : RiemannSphere))
    (hz₂_eq : L₂.normalization • L₂.chart x = (z₂ : RiemannSphere))
    (hz₁_im : z₁.im ≠ 0) :
    ∃ R : RealProjectiveMobiusRepresentative,
      z₂ = UpperHalfPlane.num R z₁ / UpperHalfPlane.denom R z₁ := by
  rcases H.localAgreement_normalizedChart_transition_realProjective
      L₁ L₂ hx₁ hx₂ with
    ⟨R, htransition⟩
  refine ⟨R, ?_⟩
  rw [hz₂_eq, hz₁_eq] at htransition
  have hden :
      ¬ realProjectiveMobiusRepresentativeAsMobiusRepresentative R 1 0 * z₁ +
          realProjectiveMobiusRepresentativeAsMobiusRepresentative R 1 1 = 0 := by
    simpa [realProjectiveMobiusRepresentativeAsMobiusRepresentative, UpperHalfPlane.denom]
      using UpperHalfPlane.denom_ne_zero_of_im R hz₁_im
  rw [OnePoint.smul_some_eq_ite, if_neg hden] at htransition
  have hcomplex := OnePoint.coe_injective htransition
  simpa [realProjectiveMobiusRepresentativeAsMobiusRepresentative,
    UpperHalfPlane.num, UpperHalfPlane.denom] using hcomplex

/--
%%handwave
name:
  Local developing branches define the same hyperbolic density
statement:
  Suppose two normalized projective branches have finite values
  $z_1,z_2\in\mathbb C\setminus\mathbb R$ at the same point. Then there is
  $R\in\mathrm{GL}_2(\mathbb R)$ such that $z_2=R\cdot z_1$ and
  \[
    \frac{|(R\cdot)'(z_1)|^2}{(\operatorname{Im}z_2)^2}
      =\frac{1}{(\operatorname{Im}z_1)^2}.
  \]
proof:
  Real projective holonomy supplies the transition $R$ between the normalized branches. [The squared Poincaré density on $\mathbb C\setminus\mathbb R$ is invariant under real Möbius transformations](lean:JJMath.pgl2r_preserves_offRealLineDensity_holomorphic), which gives the displayed identity.
-/
theorem localAgreement_finiteCoordinate_preserves_density
    (H : P.PGL2RHolonomyData x₀)
    {y₁ y₂ : H.holonomy_constructed_from_projective_charts.developingData.cover.total}
    (L₁ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₁)
    (L₂ : ProjectiveHolonomyLocalChartAgreementData X P
      H.holonomy_constructed_from_projective_charts.developingData y₂)
    {x : X} (hx₁ : x ∈ L₁.chart.source) (hx₂ : x ∈ L₂.chart.source)
    {z₁ z₂ : ℂ}
    (hz₁_eq : L₁.normalization • L₁.chart x = (z₁ : RiemannSphere))
    (hz₂_eq : L₂.normalization • L₂.chart x = (z₂ : RiemannSphere))
    (hz₁_im : z₁.im ≠ 0) :
    ∃ R : RealProjectiveMobiusRepresentative,
      z₂ = UpperHalfPlane.num R z₁ / UpperHalfPlane.denom R z₁ ∧
        poincareDensitySqInChart z₂ *
            Complex.normSq
              (deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w) z₁) =
          poincareDensitySqInChart z₁ := by
  rcases H.localAgreement_finiteCoordinate_transition_realProjective
      L₁ L₂ hx₁ hx₂ hz₁_eq hz₂_eq hz₁_im with
    ⟨R, hz₂⟩
  refine ⟨R, hz₂, ?_⟩
  rw [hz₂]
  exact pgl2r_preserves_offRealLineDensity_holomorphic R hz₁_im

/-- The real-projective locus obtained by descending the developing-map preimage. -/
def realProjectiveLocus (H : P.PGL2RHolonomyData x₀) : Set X :=
  {x | RiemannSphere.IsRealProjectivePoint
      (H.holonomy_constructed_from_projective_charts.developingData.developingMap
      (Classical.choose
        ((H.holonomy_constructed_from_projective_charts.developingData.cover).projection_surjective x)))}

/-- The regular locus is the complement of the descended real-projective locus. -/
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

/-- The regular locus is exactly the projected off-real developing-map preimage.

%%handwave
name:
  The regular locus is the projected off-real developing locus
statement:
  A projected cover point is regular exactly when its developing value lies outside ℝP¹.
proof:
  Take complements in the characterization of the descended real-projective locus.
-/
theorem regularSet_eq_developing_offReal_preimage
    (H : P.PGL2RHolonomyData x₀)
    (y : H.holonomy_constructed_from_projective_charts.developingData.cover.total) :
    H.holonomy_constructed_from_projective_charts.developingData.cover.projection y
        ∈ H.regularSet ↔
      ¬ RiemannSphere.IsRealProjectivePoint
        (H.holonomy_constructed_from_projective_charts.developingData.developingMap y) := by
  rw [regularSet, Set.mem_compl_iff, H.realProjectiveLocus_eq_developing_preimage y]

/-- A point is regular exactly when one chosen lift has off-real developing value.

%%handwave
name:
  Regularity can be tested on any chosen lift
statement:
  If y projects to x, then x is regular exactly when dev(y) lies outside ℝP¹.
proof:
  Rewrite x as the projection of y and apply the cover-level characterization of the regular locus.
-/
theorem regularSet_iff_developing_offReal_of_lift
    (H : P.PGL2RHolonomyData x₀)
    {x : X}
    (y : H.holonomy_constructed_from_projective_charts.developingData.cover.total)
    (hy : H.holonomy_constructed_from_projective_charts.developingData.cover.projection y = x) :
    x ∈ H.regularSet ↔
      ¬ RiemannSphere.IsRealProjectivePoint
        (H.holonomy_constructed_from_projective_charts.developingData.developingMap y) := by
  rw [← hy]
  exact H.regularSet_eq_developing_offReal_preimage y

/--
The regular locus can be read directly from finite off-real values of the
developing map on the cover.

%%handwave
name:
  Regular points have finite nonreal developing values
statement:
  A surface point is regular exactly when some lift has developing value [z:1] with Im z ≠ 0.
proof:
  Choose a lift by surjectivity of the cover. A projective point avoids ℝP¹ exactly when it is a finite complex point with nonzero imaginary part.
-/
theorem regularSet_iff_exists_developing_finite_offReal
    (H : P.PGL2RHolonomyData x₀) {x : X} :
    x ∈ H.regularSet ↔
      ∃ y : H.holonomy_constructed_from_projective_charts.developingData.cover.total,
        H.holonomy_constructed_from_projective_charts.developingData.cover.projection y = x ∧
          ∃ z : ℂ,
            H.holonomy_constructed_from_projective_charts.developingData.developingMap y =
              (z : RiemannSphere) ∧
              z.im ≠ 0 := by
  let cover := H.holonomy_constructed_from_projective_charts.developingData.cover
  constructor
  · intro hx
    rcases cover.projection_surjective x with ⟨y, hy⟩
    have hy_reg : cover.projection y ∈ H.regularSet := by
      simpa [hy] using hx
    have hy_offReal :=
      (H.regularSet_eq_developing_offReal_preimage y).mp hy_reg
    exact
      ⟨y, hy,
        (RiemannSphere.not_isRealProjectivePoint_iff_exists_im_ne_zero
          (H.holonomy_constructed_from_projective_charts.developingData.developingMap y)).mp
            hy_offReal⟩
  · rintro ⟨y, hy, z, hz, hz_im⟩
    have hy_offReal :
        ¬ RiemannSphere.IsRealProjectivePoint
          (H.holonomy_constructed_from_projective_charts.developingData.developingMap y) :=
      (RiemannSphere.not_isRealProjectivePoint_iff_exists_im_ne_zero
        (H.holonomy_constructed_from_projective_charts.developingData.developingMap y)).mpr
        ⟨z, hz, hz_im⟩
    have hy_reg := (H.regularSet_eq_developing_offReal_preimage y).mpr hy_offReal
    simpa [hy] using hy_reg

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
Pointwise finite off-real projective coordinate data at a regular point.

This is the local coordinate seed for the forward pullback metric: after a
single Mobius normalization of a projective chart, the point has a finite
affine coordinate with nonzero imaginary part.
-/
structure RegularLocusFiniteCoordinateData
    (H : P.PGL2RHolonomyData x₀) (x : X) where
  /-- A projective chart around the point. -/
  chart : ProjectiveChart X
  /-- The chart belongs to the stored projective atlas. -/
  chart_mem : chart ∈ P.atlasSet
  /-- The point lies in the chart source. -/
  mem_chart_source : x ∈ chart.source
  /-- The Mobius normalization putting the point in the finite off-real affine coordinate. -/
  normalization : MobiusRepresentative
  /-- The finite affine coordinate value at the point. -/
  finiteCoordinateAt : ℂ
  /-- The normalized projective coordinate equals the finite affine coordinate. -/
  normalizedChart_eq_finiteCoordinateAt :
    normalization • chart x = (finiteCoordinateAt : RiemannSphere)
  /-- The finite affine coordinate is off the real line. -/
  finiteCoordinateAt_offReal :
    finiteCoordinateAt ∈ offRealLineInComplexPlane

/-- Existence form of the finite off-real coordinate data at a regular point.

%%handwave
name:
  Finite off-real coordinate data exist at every regular point
statement:
  Every regular point admits a projective chart, a Möbius normalization, and a finite coordinate value z with Im z ≠ 0 representing the normalized chart value.
proof:
  Choose the off-real normalized local chart at the point and package its chart, normalization, and finite value.
-/
theorem regularLocusFiniteCoordinateData_nonempty
    (H : P.PGL2RHolonomyData x₀) {x : X} (hreg : x ∈ H.regularSet) :
    Nonempty (H.RegularLocusFiniteCoordinateData x) := by
  rcases H.exists_localAgreement_normalizedChart_offReal_finiteCoordinate hreg with
    ⟨_y, L, _hy, hxsource, z, hz_eq, hz_offReal⟩
  exact
    ⟨{ chart := L.chart
       chart_mem := L.chart_mem
       mem_chart_source := hxsource
       normalization := L.normalization
       finiteCoordinateAt := z
       normalizedChart_eq_finiteCoordinateAt := hz_eq
       finiteCoordinateAt_offReal := hz_offReal }⟩

/-- A chosen finite off-real projective coordinate package at a regular point. -/
def regularLocusFiniteCoordinateData
    (H : P.PGL2RHolonomyData x₀) {x : X} (hreg : x ∈ H.regularSet) :
    H.RegularLocusFiniteCoordinateData x :=
  Classical.choice (H.regularLocusFiniteCoordinateData_nonempty hreg)

namespace RegularLocusFiniteCoordinateData

variable {H : P.PGL2RHolonomyData x₀} {x : X}

/-- The compatible complex chart selected by the projective structure for this projective chart. -/
def compatibleComplexChartData
    (D : H.RegularLocusFiniteCoordinateData x) :
    ProjectiveCompatibleComplexChartData D.chart :=
  P.chart_complex_compatible_of_mem D.chart_mem

/-- The selected ambient complex chart for the projective chart. -/
def compatibleComplexChart
    (D : H.RegularLocusFiniteCoordinateData x) :
    OpenPartialHomeomorph X ℂ :=
  D.compatibleComplexChartData.complexChart

/-- The finite coordinate expressing the projective chart in the selected complex chart. -/
def compatibleFiniteCoordinate
    (D : H.RegularLocusFiniteCoordinateData x) : ℂ → ℂ :=
  D.compatibleComplexChartData.compatibility.finiteCoordinate

/-- The regular point lies in the selected compatible complex chart.

%%handwave
name:
  The base point lies in the compatible complex chart
statement:
  The regular surface point underlying a selected projective chart lies in the source of its compatible complex chart.
proof:
  Projective–complex chart compatibility includes containment of the projective chart source in the complex chart source.
-/
theorem mem_compatibleComplexChart_source
    (D : H.RegularLocusFiniteCoordinateData x) :
    x ∈ D.compatibleComplexChart.source :=
  D.compatibleComplexChartData.projective_source_subset_complex_source D.mem_chart_source

/-- The compatible complex coordinate of the point lies in the chart-to-projective transition source.

%%handwave
name:
  The compatible coordinate lies in the projective transition domain
statement:
  The compatible complex coordinate of the base point belongs to the domain on which the compatible complex chart and selected projective chart may be composed.
proof:
  Use membership in both chart sources and the inverse-chart identities to verify the two conditions defining the transition domain.
-/
theorem compatibleCoordinate_mem_transition_source
    (D : H.RegularLocusFiniteCoordinateData x) :
    D.compatibleComplexChart x ∈ (D.compatibleComplexChart.symm.trans D.chart).source := by
  rw [OpenPartialHomeomorph.trans_source]
  have hxsource : x ∈ D.compatibleComplexChart.source :=
    D.mem_compatibleComplexChart_source
  constructor
  · simpa [OpenPartialHomeomorph.symm_source] using
      D.compatibleComplexChart.map_source hxsource
  · simpa [D.compatibleComplexChart.left_inv hxsource] using D.mem_chart_source

/--
In the selected compatible complex chart, the projective chart has a finite
holomorphic representative at the regular point.

%%handwave
name:
  A compatible finite coordinate represents the projective chart
statement:
  In a complex chart compatible with a selected projective chart, the compatibility Möbius representative sends the projective chart value to the finite coordinate value.
proof:
  Evaluate the projective–complex compatibility identity and simplify the chart inverse at the base point.
-/
theorem compatibleFiniteCoordinate_eq_projectiveChart
    (D : H.RegularLocusFiniteCoordinateData x) :
    D.compatibleComplexChartData.compatibility.representative • D.chart x =
      (D.compatibleFiniteCoordinate (D.compatibleComplexChart x) : RiemannSphere) := by
  have hsource := D.compatibleCoordinate_mem_transition_source
  have heq :=
    D.compatibleComplexChartData.compatibility.finiteCoordinate_eq
      (D.compatibleComplexChart x) hsource
  have hxsource : x ∈ D.compatibleComplexChart.source :=
    D.mem_compatibleComplexChart_source
  rw [OpenPartialHomeomorph.trans_apply] at heq
  have hleft :
      D.compatibleComplexChartData.complexChart.symm (D.compatibleComplexChart x) = x := by
    simpa [compatibleComplexChart] using D.compatibleComplexChart.left_inv hxsource
  rw [hleft] at heq
  simpa [compatibleFiniteCoordinate] using heq

/-- The compatible finite coordinate is holomorphic at the regular point.

%%handwave
name:
  Holomorphicity of a compatible finite projective coordinate
statement:
  The finite coordinate representing a projective chart in a compatible complex chart is holomorphic at the regular point.
proof:
  Apply the local holomorphicity field of the projective–complex chart compatibility.
-/
theorem compatibleFiniteCoordinate_holomorphic_at
    (D : H.RegularLocusFiniteCoordinateData x) :
    DifferentiableAt ℂ D.compatibleFiniteCoordinate (D.compatibleComplexChart x) :=
  D.compatibleComplexChartData.compatibility.finiteCoordinate_holomorphic
    (D.compatibleComplexChart x) D.compatibleCoordinate_mem_transition_source

/-- The compatible finite coordinate is locally biholomorphic at the regular point.

%%handwave
name:
  Nondegeneracy of the compatible finite coordinate
statement:
  The finite coordinate expressing a projective chart in a compatible complex chart has nonzero derivative at the selected point.
proof:
  Apply the local biholomorphism property included in projective–complex chart compatibility.
-/
theorem compatibleFiniteCoordinate_deriv_ne_zero
    (D : H.RegularLocusFiniteCoordinateData x) :
    deriv D.compatibleFiniteCoordinate (D.compatibleComplexChart x) ≠ 0 :=
  D.compatibleComplexChartData.compatibility.finiteCoordinate_deriv_ne_zero
    (D.compatibleComplexChart x) D.compatibleCoordinate_mem_transition_source

end RegularLocusFiniteCoordinateData

/--
At every regular point there is a projective chart with a compatible finite
complex coordinate that is locally biholomorphic, and after one Mobius
normalization the projective value is off the real line.

%%handwave
name:
  Regular points have nondegenerate compatible projective coordinates
statement:
  At every regular point there is a projective chart and compatible complex chart with a holomorphic finite coordinate of nonzero derivative, together with a Möbius normalization whose value is finite and nonreal.
proof:
  Choose the finite-coordinate package at the point and collect its chart compatibility, holomorphicity, nondegeneracy, and normalized off-real value.
-/
theorem regularSet_has_compatible_local_projective_coordinate
    (H : P.PGL2RHolonomyData x₀) {x : X} (hreg : x ∈ H.regularSet) :
    ∃ chart : ProjectiveChart X,
      ∃ complexChart : OpenPartialHomeomorph X ℂ,
        ∃ finiteCoordinate : ℂ → ℂ,
          ∃ normalization : MobiusRepresentative,
            chart ∈ P.atlasSet ∧
              x ∈ chart.source ∧
                x ∈ complexChart.source ∧
                  complexChart x ∈ (complexChart.symm.trans chart).source ∧
                    DifferentiableAt ℂ finiteCoordinate (complexChart x) ∧
                      deriv finiteCoordinate (complexChart x) ≠ 0 ∧
                        ∃ z : ℂ,
                          normalization • chart x = (z : RiemannSphere) ∧
                            z.im ≠ 0 := by
  let D := H.regularLocusFiniteCoordinateData hreg
  exact
    ⟨D.chart, D.compatibleComplexChart, D.compatibleFiniteCoordinate, D.normalization,
      D.chart_mem, D.mem_chart_source, D.mem_compatibleComplexChart_source,
      D.compatibleCoordinate_mem_transition_source,
      D.compatibleFiniteCoordinate_holomorphic_at,
      D.compatibleFiniteCoordinate_deriv_ne_zero,
      D.finiteCoordinateAt, D.normalizedChart_eq_finiteCoordinateAt,
      D.finiteCoordinateAt_offReal⟩

/--
The affine finite-part expression for a normalized projective chart in a chosen
complex coordinate.
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
At a regular point in any complex chart, there is a finite normalized
projective coordinate branch representing the developing coordinate locally.

%%handwave
name:
  A finite normalized developing branch exists in every regular chart
statement:
  At every regular chart point there is a complex function F, a projective chart, and a Möbius normalization such that [F:1] locally equals the normalized chart and Im F(z) ≠ 0.
proof:
  Choose a local developing-chart agreement and take the finite part of its normalized projective coordinate on a neighborhood avoiding infinity.
-/
theorem exists_normalizedFiniteCoordinateBranch
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    ∃ F : ℂ → ℂ, ∃ chart : ProjectiveChart X, ∃ normalization : MobiusRepresentative,
      chart ∈ P.atlasSet ∧
        e.symm z ∈ chart.source ∧
          (∀ᶠ w in 𝓝 z,
            ((F w : ℂ) : RiemannSphere) = normalization • chart (e.symm w)) ∧
            (F z).im ≠ 0 := by
  rcases H.exists_localAgreement_normalizedChart_offReal_finiteCoordinate hreg with
    ⟨_y, L, _hy, hxsource, _v, _hv, _hv_im⟩
  rcases H.normalizedChartFinitePart_eventually_eq L e hz hxsource hreg with
    ⟨hF_eq, hF_offReal⟩
  exact
    ⟨H.normalizedChartFinitePart L e, L.chart, L.normalization,
      L.chart_mem, hxsource, hF_eq, hF_offReal⟩

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

/-- A chosen local pullback-coordinate package at a regular chart point. -/
def regularLocusLocalPullbackCoordinateData
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    H.RegularLocusLocalPullbackCoordinateData e z :=
  Classical.choice (H.regularLocusLocalPullbackCoordinateData_nonempty e hz hreg)

namespace RegularLocusLocalPullbackCoordinateData

variable {H : P.PGL2RHolonomyData x₀}
    {e : OpenPartialHomeomorph X ℂ} {z : ℂ}

/-- The compatible complex chart selected by the projective structure for this branch. -/
def compatibleComplexChartData
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    ProjectiveCompatibleComplexChartData C.chart :=
  P.chart_complex_compatible_of_mem C.chart_mem

/-- The selected ambient complex chart for the projective chart underlying this branch. -/
def compatibleComplexChart
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    OpenPartialHomeomorph X ℂ :=
  C.compatibleComplexChartData.complexChart

/-- The finite coordinate expressing the projective chart in the compatible complex chart. -/
def compatibleFiniteCoordinate
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℂ :=
  C.compatibleComplexChartData.compatibility.finiteCoordinate

/--
The complex Mobius representative carrying the compatible finite projective
coordinate to this branch's normalized developing coordinate.
-/
def affineTransitionRepresentative
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    MobiusRepresentative :=
  C.normalization * C.compatibleComplexChartData.compatibility.representative⁻¹

/-- The squared pullback density represented by this finite developing-coordinate branch. -/
noncomputable def pullbackDensityFunction
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  fun w ↦ poincareDensitySqInChart (C.finiteCoordinate w) *
    Complex.normSq (deriv C.finiteCoordinate w)

/-- The logarithmic density of the local pullback-density branch. -/
noncomputable def pullbackLogDensityFunction
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  logDensityFromDensitySq C.pullbackDensityFunction

/-- The derivative part of the explicit local pullback logarithmic density. -/
noncomputable def pullbackLogDerivativeTerm
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  fun w : ℂ ↦
    Real.log (Complex.normSq (deriv C.finiteCoordinate w)) / 2

/-- The imaginary-coordinate part of the explicit local pullback logarithmic density. -/
noncomputable def pullbackLogImaginaryTerm
    (C : H.RegularLocusLocalPullbackCoordinateData e z) : ℂ → ℝ :=
  fun w : ℂ ↦ Real.log (C.finiteCoordinate w).im

/-- The explicit local formula for the pullback logarithmic density. -/
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
  Formula for the logarithmic pullback density
statement:
  The logarithmic density attached to a squared density $q$ is $\frac12\log q$.
proof:
  This is the definition of logarithmic density from a squared density.
-/
@[simp]
theorem pullbackLogDensityFunction_apply
    (C : H.RegularLocusLocalPullbackCoordinateData e z) (w : ℂ) :
    C.pullbackLogDensityFunction w =
      logDensityFromDensitySq C.pullbackDensityFunction w :=
  rfl

/--
%%handwave
name:
  Explicit split formula for the pullback log-density
statement:
  For a finite branch $F$, the explicit pullback logarithmic density is $\log|F'|-\log|\operatorname{Im}F|$.
proof:
  Expand the derivative and height terms in the defining difference.
-/
@[simp]
theorem pullbackLogDensityExpression_apply
    (C : H.RegularLocusLocalPullbackCoordinateData e z) (w : ℂ) :
    C.pullbackLogDensityExpression w =
      Real.log (Complex.normSq (deriv C.finiteCoordinate w)) / 2 -
        Real.log (C.finiteCoordinate w).im :=
  rfl

/--
%%handwave
name:
  Formula for the logarithmic derivative term
statement:
  The derivative contribution to the pullback logarithmic density is $\frac12\log|F'|^2=\log|F'|$.
proof:
  This is the definition of the derivative term.
-/
@[simp]
theorem pullbackLogDerivativeTerm_apply
    (C : H.RegularLocusLocalPullbackCoordinateData e z) (w : ℂ) :
    C.pullbackLogDerivativeTerm w =
      Real.log (Complex.normSq (deriv C.finiteCoordinate w)) / 2 :=
  rfl

/--
%%handwave
name:
  Formula for the logarithmic height term
statement:
  The height contribution to the pullback logarithmic density is $\log(\operatorname{Im}F)$ on the chosen half-plane branch.
proof:
  This is the definition of the height term.
-/
@[simp]
theorem pullbackLogImaginaryTerm_apply
    (C : H.RegularLocusLocalPullbackCoordinateData e z) (w : ℂ) :
    C.pullbackLogImaginaryTerm w =
      Real.log (C.finiteCoordinate w).im :=
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

/-- The derivative of the compatible finite projective coordinate is complex-smooth.

%%handwave
name:
  Smoothness of the compatible derivative
statement:
  The derivative of the compatible finite projective coordinate is complex C∞ at the selected point.
proof:
  The derivative of a holomorphic function remains holomorphic and smooth.
-/
theorem compatibleFiniteCoordinate_deriv_contDiffAt
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    ContDiffAt ℂ ⊤ (fun w : ℂ ↦ deriv C.compatibleFiniteCoordinate w)
      (C.compatibleComplexChart (e.symm z)) := by
  rcases C.compatibleComplexChartData.compatibility.finiteCoordinate_local
      (C.compatibleComplexChart (e.symm z))
      C.compatibleCoordinate_mem_transition_source with
    ⟨U, hUopen, hmem, _hsubset, hlocal⟩
  have hDiffOn : DifferentiableOn ℂ C.compatibleFiniteCoordinate U := by
    intro w hw
    exact (hlocal w hw).1.differentiableWithinAt
  have hDerivDiffOn : DifferentiableOn ℂ (deriv C.compatibleFiniteCoordinate) U :=
    hDiffOn.deriv hUopen
  exact (hDerivDiffOn.contDiffOn hUopen).contDiffAt (hUopen.mem_nhds hmem)

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

/-- Pointwise formula for the selected finite branch in compatible coordinates.

%%handwave
name:
  Pointwise affine formula for the finite branch
statement:
  At the base point, the selected finite branch is the fractional-linear affine transition applied to the compatible finite coordinate.
proof:
  Convert the projective factorization to affine coordinates using the nonzero denominator.
-/
theorem finiteCoordinate_eq_mobiusFiniteFormula_compatible_at
    (C : H.RegularLocusLocalPullbackCoordinateData e z) :
    C.finiteCoordinate z =
      mobiusFiniteFormula C.affineTransitionRepresentative
        (C.compatibleFiniteCoordinate (C.compatibleComplexChart (e.symm z))) := by
  have h :
      C.affineTransitionRepresentative •
          (C.compatibleFiniteCoordinate
            (C.compatibleComplexChart (e.symm z)) : RiemannSphere) =
        (C.finiteCoordinate z : RiemannSphere) := by
    calc
      C.affineTransitionRepresentative •
          (C.compatibleFiniteCoordinate
            (C.compatibleComplexChart (e.symm z)) : RiemannSphere) =
          C.normalization • C.chart (e.symm z) :=
        C.normalizedChart_eq_affineTransition_at.symm
      _ = (C.finiteCoordinate z : RiemannSphere) :=
        C.finiteCoordinate_eq_normalizedChart_at.symm
  exact (mobiusFiniteFormula_eq_of_smul_coe_eq_coe
    C.affineTransitionRepresentative h).symm

end RegularLocusLocalPullbackCoordinateData

/--
Two selected finite developing-coordinate branches at the same regular point
differ by a real projective fractional-linear map, and the off-real-line
hyperbolic density is invariant under that change.

%%handwave
name:
  Real-projective changes preserve the branch density
statement:
  If two normalized finite developing branches represent the same regular surface point, some R∈PGL₂(ℝ) relates their values and preserves the off-real Poincare density with the derivative factor.
proof:
  Compare their normalized chart agreements using real projective holonomy, then apply Poincare-density invariance under R.
-/
theorem localPullbackCoordinateData_finiteCoordinate_preserves_density
    (H : P.PGL2RHolonomyData x₀)
    {e₁ e₂ : OpenPartialHomeomorph X ℂ} {z₁ z₂ : ℂ}
    (C₁ : H.RegularLocusLocalPullbackCoordinateData e₁ z₁)
    (C₂ : H.RegularLocusLocalPullbackCoordinateData e₂ z₂)
    (hx : e₁.symm z₁ = e₂.symm z₂) :
    ∃ R : RealProjectiveMobiusRepresentative,
      C₂.finiteCoordinate z₂ =
          UpperHalfPlane.num R (C₁.finiteCoordinate z₁) /
            UpperHalfPlane.denom R (C₁.finiteCoordinate z₁) ∧
        poincareDensitySqInChart (C₂.finiteCoordinate z₂) *
            Complex.normSq
              (deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
                (C₁.finiteCoordinate z₁)) =
          poincareDensitySqInChart (C₁.finiteCoordinate z₁) := by
  have hx₁ : e₁.symm z₁ ∈ C₁.localAgreement.chart.source := by
    simpa [C₁.chart_eq_localAgreement_chart] using C₁.mem_chart_source
  have hx₂_at : e₂.symm z₂ ∈ C₂.localAgreement.chart.source := by
    simpa [C₂.chart_eq_localAgreement_chart] using C₂.mem_chart_source
  have hx₂ : e₁.symm z₁ ∈ C₂.localAgreement.chart.source := by
    simpa [hx] using hx₂_at
  have hz₁_eq :
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
    simpa [hx] using hz₂_eq_at
  exact
    H.localAgreement_finiteCoordinate_preserves_density
      C₁.localAgreement C₂.localAgreement hx₁ hx₂ hz₁_eq hz₂_eq
      C₁.finiteCoordinate_offReal

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

/-- The derivative of a complex chart change is smooth.

%%handwave
name:
  Smoothness of the chart-transition derivative
statement:
  The derivative of a complex chart transition is complex C∞ on the overlap.
proof:
  Differentiate the holomorphic smooth coordinate change; its derivative remains holomorphic.
-/
theorem complexChartTransition_deriv_contDiffAt
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    ContDiffAt ℂ ⊤
      (fun w : ℂ ↦ deriv (fun u : ℂ ↦ e' (e.symm u)) w) z := by
  have hτ : ContDiffAt ℂ ⊤ (fun w : ℂ ↦ e' (e.symm w)) z :=
    complexChartTransition_contDiffAt e he e' he' hz hz'
  simpa using hτ.derivWithin (m := ⊤) (by simp)

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
At the base point, the local pullback log-density is the usual expression
`log |F'| - log |Im F|`, written in squared-density form.

%%handwave
name:
  Logarithmic pullback density formula at the base point
statement:
  For an off-real locally univalent branch F, ½ log ρ²(z) = log|F′(z)| − log|Im F(z)| at the regular base point.
proof:
  Expand ρ²=|F′|²/(Im F)², use positivity and nonvanishing to split the logarithm of a quotient, and simplify ½ log|a|² = log|a|.
-/
theorem pullbackLogDensityFunction_eq_log_deriv_sub_log_im_at
    (C : H.RegularLocusLocalPullbackCoordinateData e z)
    (he : e ∈ atlas ℂ X) (hz : z ∈ e.target) :
    C.pullbackLogDensityFunction z = C.pullbackLogDensityExpression z := by
  have him_ne : (C.finiteCoordinate z).im ≠ 0 :=
    C.finiteCoordinate_offReal
  have hden_ne : (((C.finiteCoordinate z).im ^ 2)⁻¹ : ℝ) ≠ 0 :=
    inv_ne_zero (pow_ne_zero 2 him_ne)
  have hnorm_ne : Complex.normSq (deriv C.finiteCoordinate z) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (C.finiteCoordinate_deriv_ne_zero he hz)).ne'
  rw [pullbackLogDensityFunction, logDensityFromDensitySq,
    pullbackDensityFunction_apply, poincareDensitySqInChart]
  rw [Real.log_mul hden_ne hnorm_ne, Real.log_inv, Real.log_pow]
  unfold pullbackLogDensityExpression pullbackLogDerivativeTerm
    pullbackLogImaginaryTerm
  simp [Pi.sub_apply]
  ring_nf

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

/-- The canonical pullback-density candidate in a complex chart. -/
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
The canonical density candidate satisfies the conformal transition law once the
derivative chain rule is known for the real-projective transition between the
two selected finite developing-coordinate branches.

%%handwave
name:
  Density transition from a branch derivative identity
statement:
  Suppose two overlapping finite developing branches are related by a real projective Möbius map and their derivatives satisfy the corresponding chain rule. Then their canonical chart densities obey q_e=q_e′|(e′∘e⁻¹)′|² at the base point.
proof:
  Use invariance of the Poincare density under the real projective map and multiply the branch derivative identity by squared norms.
-/
theorem canonicalPullbackDensityInChart_transition_of_branch_derivative
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (hz' : e.symm z ∈ e'.source)
    (hderiv :
      ∀ R : RealProjectiveMobiusRepresentative,
        (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
              (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) =
            UpperHalfPlane.num R
                ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) /
              UpperHalfPlane.denom R
                ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) →
        deriv
            (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
              (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) *
            deriv (fun w : ℂ ↦ e' (e.symm w)) z =
          deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
              ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) *
            deriv
              (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) :
    H.canonicalPullbackDensityInChart e he z =
      H.canonicalPullbackDensityInChart e' he' (e' (e.symm z)) *
        Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z) := by
  let z' : ℂ := e' (e.symm z)
  have hz'_target : z' ∈ e'.target := e'.map_source hz'
  have hreg' : e'.symm z' ∈ H.regularSet := by
    simpa [z', e'.left_inv hz'] using hreg
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  let C' := H.regularLocusLocalPullbackCoordinateData e' hz'_target hreg'
  have hx_same : e.symm z = e'.symm z' := by
    simpa [z'] using (e'.left_inv hz').symm
  rcases H.localPullbackCoordinateData_finiteCoordinate_preserves_density C C' hx_same with
    ⟨R, hvalue, hdensity⟩
  have htransition :=
    H.localPullbackCoordinateData_pullbackDensity_transition_of_derivative
      C C' R hdensity (hderiv R (by simpa [C, C', z', hreg'] using hvalue))
  rw [H.canonicalPullbackDensityInChart_eq_pullbackDensity e he hz hreg]
  rw [H.canonicalPullbackDensityInChart_eq_pullbackDensity e' he' hz'_target hreg']
  exact htransition

/--
The canonical density candidate satisfies the conformal transition law once the
selected finite branches are differentiable and locally related by the
real-projective transition supplied at the point.

%%handwave
name:
  Density transition from local branch equality
statement:
  If two differentiable finite branches agree locally after a real projective Möbius transformation, then their canonical chart densities satisfy the conformal transition law at the overlap point.
proof:
  Differentiate the germ equality, apply the chart-transition chain rule, and invoke invariance of the Poincare density under the real projective map.
-/
theorem canonicalPullbackDensityInChart_transition_of_branch_eventuallyEq
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
    (hEq :
      ∀ R : RealProjectiveMobiusRepresentative,
        (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
              (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) =
            UpperHalfPlane.num R
                ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) /
              UpperHalfPlane.denom R
                ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) →
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
  refine H.canonicalPullbackDensityInChart_transition_of_branch_derivative
    e he e' he' hz hreg hz' ?_
  intro R hvalue
  exact
    H.localPullbackCoordinateData_transition_derivative_of_eventuallyEq_chartTransition
      he he' hz hz'
      (H.regularLocusLocalPullbackCoordinateData e hz hreg)
      (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
        (by simpa [e'.left_inv hz'] using hreg))
      R (hEq R hvalue) hC hC'

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
The canonical pullback-density candidate satisfies the conformal transition
law on the regular locus.  The real-projective branch transition is supplied
canonically by the developing map.

%%handwave
name:
  The canonical pullback density obeys the chart transition law
statement:
  At a regular point represented in two complex charts, the canonical squared density satisfies q_e(z) = q_e′(e′∘e⁻¹(z)) |(e′∘e⁻¹)′(z)|².
proof:
  Choose the canonical real-projective transition between the two finite developing branches. Invariance of the Poincare density under that transition and the derivative chain rule give the formula.
-/
theorem canonicalPullbackDensityInChart_transition
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (hz' : e.symm z ∈ e'.source) :
    H.canonicalPullbackDensityInChart e he z =
      H.canonicalPullbackDensityInChart e' he' (e' (e.symm z)) *
        Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z) :=
  H.canonicalPullbackDensityInChart_transition_of_branch_eventuallyEq_exists
    e he e' he' hz hreg hz'
    (H.regularLocusLocalPullbackCoordinateData_finiteCoordinate_differentiableAt
      e he z hz hreg)
    (H.regularLocusLocalPullbackCoordinateData_finiteCoordinate_differentiableAt
      e' he' (e' (e.symm z)) (e'.map_source hz')
      (by simpa [e'.left_inv hz'] using hreg))
    (H.regularLocusLocalPullbackCoordinateData_transition_eventuallyEq
      e he e' he' z hz hreg hz')

/--
Curvature transfer for the canonical density follows from local agreement with
the fixed branch pullback density and the curvature computation for that fixed
branch.

%%handwave
name:
  Curvature transfers through local density agreement
statement:
  If the canonical chart density agrees near z with a finite branch pullback density whose curvature equals the Poincare model curvature at F(z), then the canonical density has that same curvature at z.
proof:
  Gaussian curvature depends only on the germ of the squared density. Replace the canonical density by the locally equal branch density and apply the assumed curvature identity.
-/
theorem canonicalPullbackDensityInChart_curvature_transfer_of_eventuallyEq_pullbackDensityFunction
    (H : P.PGL2RHolonomyData x₀)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
    (hEq :
      H.canonicalPullbackDensityInChart e he =ᶠ[𝓝 z]
        (H.regularLocusLocalPullbackCoordinateData e hz hreg).pullbackDensityFunction)
    (hcurv :
      gaussianCurvatureOfDensitySq
          (H.regularLocusLocalPullbackCoordinateData e hz hreg).pullbackDensityFunction z =
        gaussianCurvatureOfDensitySq poincareDensitySqInChart
          ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z)) :
    gaussianCurvatureOfDensitySq (H.canonicalPullbackDensityInChart e he) z =
      gaussianCurvatureOfDensitySq poincareDensitySqInChart
        ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) := by
  calc
    gaussianCurvatureOfDensitySq (H.canonicalPullbackDensityInChart e he) z =
        gaussianCurvatureOfDensitySq
          (H.regularLocusLocalPullbackCoordinateData e hz hreg).pullbackDensityFunction z :=
      gaussianCurvatureOfDensitySq_congr_nhds hEq
    _ =
        gaussianCurvatureOfDensitySq poincareDensitySqInChart
          ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) :=
      hcurv

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

/--
For a local chart/developing agreement, the off-real part of the normalized
projective coordinate is open whenever the fixed normalization acts
continuously on the Riemann sphere.

%%handwave
name:
  The off-real locus of a normalized projective chart is open
statement:
  If a chart normalization acts continuously on ℂP¹, then the points of the chart whose normalized values avoid ℝP¹ form an open subset of the surface.
proof:
  Compose the continuous chart with the continuous normalization and take the inverse image of the open set ℂP¹ ∖ ℝP¹ inside the open chart domain.
-/
theorem normalized_offReal_locus_open
    (L : ProjectiveHolonomyLocalChartAgreementData X P developingData y)
    (hA : Continuous fun z : RiemannSphere ↦ L.normalization • z) :
    IsOpen (L.chart.source ∩
      {x : X | ¬ RiemannSphere.IsRealProjectivePoint (L.normalization • L.chart x)}) := by
  have hnorm : ContinuousOn
      (fun x : X ↦ L.normalization • L.chart x) L.chart.source := by
    exact hA.continuousOn.comp L.chart.continuousOn (by
      intro x hx
      exact Set.mem_univ _)
  exact hnorm.isOpen_inter_preimage L.chart.open_source
    offRealProjectiveLineInRiemannSphere_open

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

/--
Positivity of the squared density at regular points.

%%handwave
name:
  Positivity of a conformal squared density on its locus
statement:
  For a conformal metric defined on a locus U, its chartwise squared density is positive at every chart point representing a point of U.
proof:
  This is the positivity condition included in the definition of the conformal metric on U.
-/
theorem positive_densitySqInChart (g : ConformalMetricOn X U)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hzU : e.symm z ∈ U) :
    0 < g.densitySqInChart e he z :=
  g.densitySq_pos e he z hz hzU

/--
The chartwise coordinate-change law at regular points.

%%handwave
name:
  The coordinate-change law for a conformal squared density
statement:
  If two complex charts overlap at a point of U, then their squared densities satisfy q_e(z) = q_e′(e′∘e⁻¹(z)) |(e′∘e⁻¹)′(z)|².
proof:
  Apply the transition condition included in the conformal metric on U.
-/
theorem densitySq_transition' (g : ConformalMetricOn X U)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hzU : e.symm z ∈ U) (hz' : e.symm z ∈ e'.source) :
    g.densitySqInChart e he z =
      g.densitySqInChart e' he' (e' (e.symm z)) *
        Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z) :=
  g.densitySq_transition e he e' he' z hz hzU hz'

/-- Gaussian curvature computed from the regular-locus density in a chosen chart. -/
noncomputable def gaussianCurvatureInChart (g : ConformalMetricOn X U)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) : ℂ → ℝ :=
  gaussianCurvatureOfDensitySq (g.densitySqInChart e he)

/-- Smoothness of the squared density on the coordinate part of the chosen locus. -/
def smooth_in_charts (g : ConformalMetricOn X U) : Prop :=
  ∀ e he, ContDiffOn ℝ ⊤ (g.densitySqInChart e he) (e.target ∩ e.symm ⁻¹' U)

/-- Smoothness predicate for a regular-locus conformal metric. -/
def IsSmooth (g : ConformalMetricOn X U) : Prop :=
  g.smooth_in_charts

/-- The Gaussian-curvature predicate on the chosen locus. -/
def curvature_eq (g : ConformalMetricOn X U) (K : ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) z,
    z ∈ e.target → e.symm z ∈ U → g.gaussianCurvatureInChart e he z = K

/-- The metric has Gaussian curvature `-1` on the chosen locus. -/
def HasCurvatureMinusOne (g : ConformalMetricOn X U) : Prop :=
  g.curvature_eq (-1)

end ConformalMetricOn

/-- The hyperbolic conformal metric on the complement of the real line in the affine chart. -/
def offRealLineModelConformalMetric :
    ConformalMetricOn ℂ offRealLineInComplexPlane where
  densitySqInChart := fun _ _ ↦ poincareDensitySqInChart
  densitySq_pos := by
    intro e he z _hz hzU
    have heq : e = OpenPartialHomeomorph.refl ℂ := by
      simpa using he
    subst e
    exact poincareDensitySqInChart_pos_of_im_ne_zero hzU
  densitySq_transition := by
    intro e he e' he' z _hz _hzU _hz'
    have heq : e = OpenPartialHomeomorph.refl ℂ := by
      simpa using he
    have heq' : e' = OpenPartialHomeomorph.refl ℂ := by
      simpa using he'
    subst e
    subst e'
    simp [poincareDensitySqInChart]

/--
The off-real-line model density is smooth on its domain.

%%handwave
name:
  Smoothness of the off-real-line hyperbolic metric
statement:
  The squared density q(z) = (Im z)⁻² is smooth on ℂ ∖ ℝ.
proof:
  The imaginary part is smooth and nonzero off the real line, so inversion and squaring preserve smoothness.
-/
theorem offRealLineModelConformalMetric_smooth :
    offRealLineModelConformalMetric.IsSmooth := by
  intro e he
  have heq : e = OpenPartialHomeomorph.refl ℂ := by
    simpa using he
  subst e
  simpa [ConformalMetricOn.smooth_in_charts, offRealLineModelConformalMetric]
    using poincareDensitySqInChart_contDiffOn_offRealLine

/--
The off-real-line model metric has curvature `-1` in either half-plane.

%%handwave
name:
  Curvature of the off-real-line hyperbolic metric
statement:
  On either half-plane, the conformal metric (Im z)⁻²|dz|² has Gaussian curvature −1.
proof:
  Compute Δ log((Im z)⁻¹) = (Im z)⁻² and use K = −(Δ log ρ)/ρ².
-/
theorem offRealLineModelConformalMetric_curvature_minus_one :
    offRealLineModelConformalMetric.HasCurvatureMinusOne := by
  intro e he z _hz hzU
  have heq : e = OpenPartialHomeomorph.refl ℂ := by
    simpa using he
  subst e
  exact offRealLineDensitySq_gaussianCurvature_eq_minus_one (z := z) hzU

namespace ConformalMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Restrict a global conformal metric to a specified locus. -/
def restrictTo (g : ConformalMetric X) (U : Set X) : ConformalMetricOn X U where
  densitySqInChart := fun e he ↦ g.densitySqInChart e he
  densitySq_pos := by
    intro e he z hz _hzU
    exact g.positive_densitySqInChart e he hz
  densitySq_transition := by
    intro e he e' he' z hz _hzU hz'
    exact g.densitySq_transition e he e' he' hz hz'

/--
Curvature `-1` restricts from a global conformal metric to any locus.

%%handwave
name:
  Restriction preserves curvature minus one
statement:
  If a global conformal metric has Gaussian curvature −1, then its restriction to any subset has curvature −1 at every point where it is defined.
proof:
  The restricted metric uses the same chartwise density, so the original curvature identity applies pointwise.
-/
theorem restrictTo_hasCurvatureMinusOne (g : ConformalMetric X) {U : Set X}
    (h : g.HasCurvatureMinusOne) :
    (g.restrictTo U).HasCurvatureMinusOne := by
  intro e he z hz _hzU
  exact h e he z hz

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
-/
def regularLocusTopologicalData_of_mobiusAction_continuous
    (H : P.PGL2RHolonomyData x₀)
    (hcont : ∀ A : MobiusRepresentative, Continuous fun z : RiemannSphere ↦ A • z) :
    H.RegularLocusTopologicalData :=
  H.regularLocusTopologicalData_of_continuousLocalNormalizations
    (H.hasContinuousLocalNormalizations_of_mobiusAction_continuous hcont)

/-- The topological regular-locus data supplied by continuity of Mobius transformations. -/
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
Pullback metric data on the canonical regular locus of a real-projective
developing map.

This package isolates the geometric computation: the metric is built as a
pullback of the off-real-line model density, and its chartwise curvature is
computed by transferring to that model coordinate.
-/
structure RegularLocusPullbackMetricData (H : P.PGL2RHolonomyData x₀) where
  /-- The conformal metric on the regular locus. -/
  metric : ConformalMetricOn X H.regularSet
  /-- The regular-locus metric is smooth. -/
  metric_smooth_on_regularSet : metric.IsSmooth
  /--
  Chartwise curvature transfers to the off-real-line model coordinate.
  The model coordinate may lie in either half-plane.
  -/
  curvature_transfers_to_offRealLine :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ),
      z ∈ e.target →
      e.symm z ∈ H.regularSet →
        ∃ F : ℂ → ℂ,
          (F z).im ≠ 0 ∧
            metric.gaussianCurvatureInChart e he z =
              gaussianCurvatureOfDensitySq poincareDensitySqInChart (F z)
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
Ordinary curvature `-1` on the regular locus is enough to transfer curvature
to the canonical off-real model coordinate.

%%handwave
name:
  Curvature minus one transfers to the finite model coordinate
statement:
  If a conformal metric has curvature −1 on the regular locus, then at each regular point its curvature equals that of the off-real Poincare model at the canonical finite developing value.
proof:
  Both curvatures equal −1: the first by hypothesis and the second because the canonical finite value has nonzero imaginary part.
-/
theorem curvature_transfers_to_normalizedFiniteCoordinate_of_curvature_minus_one
    (metric : ConformalMetricOn X H.regularSet)
    (hcurv : metric.HasCurvatureMinusOne)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
    metric.gaussianCurvatureInChart e he z =
      gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z) := by
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  calc
    metric.gaussianCurvatureInChart e he z = -1 :=
      hcurv e he z hz hreg
    _ = gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z) :=
      (offRealLineDensitySq_gaussianCurvature_eq_minus_one
        (z := C.finiteCoordinate z) C.finiteCoordinate_offReal).symm

/--
Build canonical pullback data from a regular-locus metric, its curvature, and
the canonical density pullback formula.
-/
def ofCurvatureAndDensity
    (metric : ConformalMetricOn X H.regularSet)
    (metric_smooth_on_regularSet : metric.IsSmooth)
    (curvature_minus_one : metric.HasCurvatureMinusOne)
    (density_eq_normalizedFiniteCoordinate_pullback :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
          metric.densitySqInChart e he z =
            ((C.finiteCoordinate z).im ^ 2)⁻¹ *
              Complex.normSq (deriv C.finiteCoordinate z)) :
    H.RegularLocusCanonicalPullbackMetricData where
  metric := metric
  metric_smooth_on_regularSet := metric_smooth_on_regularSet
  curvature_transfers_to_normalizedFiniteCoordinate := by
    intro e he z hz hreg
    exact curvature_transfers_to_normalizedFiniteCoordinate_of_curvature_minus_one
      metric curvature_minus_one e he z hz hreg
  density_eq_normalizedFiniteCoordinate_pullback :=
    density_eq_normalizedFiniteCoordinate_pullback

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

/-- Forget canonical pullback provenance after deriving curvature from the model. -/
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

/--
The canonical finite coordinate branch is locally nondegenerate at every
regular point where it recovers the metric by pullback.

%%handwave
name:
  Metric recovery forces the finite branch derivative to be nonzero
statement:
  If a positive conformal density satisfies q(z) = |F′(z)|²/(Im F(z))² at a regular point, then F′(z) ≠ 0.
proof:
  If F′(z)=0, the pullback formula makes q(z)=0, contradicting positivity of the metric density.
-/
theorem finiteCoordinate_deriv_ne_zero
    (D : H.RegularLocusCanonicalPullbackMetricData)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (z : ℂ)
    (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet) :
    deriv (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z ≠ 0 := by
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  change deriv C.finiteCoordinate z ≠ 0
  intro hderiv
  have hmetric_pos : 0 < D.metric.densitySqInChart e he z :=
    D.metric.positive_densitySqInChart e he hz hreg
  have hdensity := D.density_eq_normalizedFiniteCoordinate_pullback e he z hz hreg
  have hnorm_zero : Complex.normSq (deriv C.finiteCoordinate z) = 0 := by
    simp [hderiv]
  rw [hdensity, hnorm_zero, mul_zero] at hmetric_pos
  exact (lt_irrefl (0 : ℝ)) hmetric_pos

/-- Canonical-branch data supplies the explicit pullback-metric package. -/
def toRegularLocusPullbackMetricData
    (D : H.RegularLocusCanonicalPullbackMetricData) :
    H.RegularLocusPullbackMetricData where
  metric := D.metric
  metric_smooth_on_regularSet := D.metric_smooth_on_regularSet
  curvature_transfers_to_offRealLine := by
    intro e he z hz hreg
    let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
    exact
      ⟨C.finiteCoordinate, C.finiteCoordinate_offReal,
        D.curvature_transfers_to_normalizedFiniteCoordinate e he z hz hreg⟩
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

/-- The conformal metric represented by the canonical density data. -/
noncomputable def toConformalMetricOn
    (_A : H.RegularLocusCanonicalDensityAnalyticData) :
    ConformalMetricOn X H.regularSet where
  densitySqInChart := H.canonicalPullbackDensityInChart
  densitySq_pos := by
    intro e he z hz hreg
    exact H.canonicalPullbackDensityInChart_pos_of_finiteCoordinate_deriv_ne_zero
      e he hz hreg
      (H.regularLocusLocalPullbackCoordinateData_finiteCoordinate_deriv_ne_zero
        e he z hz hreg)
  densitySq_transition := by
    intro e he e' he' z hz hreg hz'
    exact H.canonicalPullbackDensityInChart_transition e he e' he' hz hreg hz'

/-- Canonical density analytic data supplies canonical pullback metric data. -/
noncomputable def toRegularLocusCanonicalPullbackMetricData
    (A : H.RegularLocusCanonicalDensityAnalyticData) :
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

/-- Branch-level analytic data supplies canonical-density analytic data. -/
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
Build the branch-analytic package from the local derivative transition law,
plus smoothness and curvature-transfer inputs.
-/
noncomputable def ofDerivativeTransition
    (finiteCoordinate_deriv_ne_zero :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          deriv (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z ≠ 0)
    (finiteCoordinate_transition_derivative :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
        (e' : OpenPartialHomeomorph X ℂ) (_he' : e' ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
        (hz' : e.symm z ∈ e'.source),
          ∀ R : RealProjectiveMobiusRepresentative,
            (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
                  (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) =
                UpperHalfPlane.num R
                    ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) /
                  UpperHalfPlane.denom R
                    ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) →
            deriv
                (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
                  (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) *
                deriv (fun w : ℂ ↦ e' (e.symm w)) z =
              deriv (fun w : ℂ ↦ UpperHalfPlane.num R w / UpperHalfPlane.denom R w)
                  ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) *
                deriv
                  (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z)
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
  finiteCoordinate_deriv_ne_zero := finiteCoordinate_deriv_ne_zero
  densitySq_transition := by
    intro e he e' he' z hz hreg hz'
    exact H.canonicalPullbackDensityInChart_transition_of_branch_derivative
      e he e' he' hz hreg hz'
      (finiteCoordinate_transition_derivative e he e' he' z hz hreg hz')
  smooth_densitySq := smooth_densitySq
  curvature_transfers_to_normalizedFiniteCoordinate :=
    curvature_transfers_to_normalizedFiniteCoordinate

/--
Build the branch-analytic package from local eventual equality of branch
transitions, plus differentiability, smoothness, and curvature-transfer inputs.
-/
noncomputable def ofEventuallyEqTransition
    (finiteCoordinate_deriv_ne_zero :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          deriv (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z ≠ 0)
    (finiteCoordinate_differentiableAt :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
          DifferentiableAt ℂ
            (H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z)
    (finiteCoordinate_transition_eventuallyEq :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
        (e' : OpenPartialHomeomorph X ℂ) (_he' : e' ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
        (hz' : e.symm z ∈ e'.source),
          ∀ R : RealProjectiveMobiusRepresentative,
            (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
                  (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) =
                UpperHalfPlane.num R
                    ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) /
                  UpperHalfPlane.denom R
                    ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) →
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
  finiteCoordinate_deriv_ne_zero := finiteCoordinate_deriv_ne_zero
  densitySq_transition := by
    intro e he e' he' z hz hreg hz'
    exact H.canonicalPullbackDensityInChart_transition_of_branch_eventuallyEq
      e he e' he' hz hreg hz'
      (finiteCoordinate_differentiableAt e he z hz hreg)
      (finiteCoordinate_differentiableAt e' he' (e' (e.symm z))
        (e'.map_source hz') (by simpa [e'.left_inv hz'] using hreg))
      (finiteCoordinate_transition_eventuallyEq e he e' he' z hz hreg hz')
  smooth_densitySq := smooth_densitySq
  curvature_transfers_to_normalizedFiniteCoordinate :=
    curvature_transfers_to_normalizedFiniteCoordinate

/--
Build the branch-analytic package from local eventual equality of branch
transitions.  The first-order holomorphicity and nondegeneracy of the selected
branches are supplied by the projective-chart compatibility data above.
-/
noncomputable def ofEventuallyEqTransitionWithCanonicalDerivatives
    (finiteCoordinate_transition_eventuallyEq :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
        (e' : OpenPartialHomeomorph X ℂ) (_he' : e' ∈ atlas ℂ X) (z : ℂ)
        (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet)
        (hz' : e.symm z ∈ e'.source),
          ∀ R : RealProjectiveMobiusRepresentative,
            (H.regularLocusLocalPullbackCoordinateData e' (e'.map_source hz')
                  (by simpa [e'.left_inv hz'] using hreg)).finiteCoordinate (e' (e.symm z)) =
                UpperHalfPlane.num R
                    ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) /
                  UpperHalfPlane.denom R
                    ((H.regularLocusLocalPullbackCoordinateData e hz hreg).finiteCoordinate z) →
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
    H.RegularLocusCanonicalBranchAnalyticData :=
  ofEventuallyEqTransition
    (H := H)
    (fun e he z hz hreg ↦
      H.regularLocusLocalPullbackCoordinateData_finiteCoordinate_deriv_ne_zero
        e he z hz hreg)
    (fun e he z hz hreg ↦
      H.regularLocusLocalPullbackCoordinateData_finiteCoordinate_differentiableAt
        e he z hz hreg)
    finiteCoordinate_transition_eventuallyEq
    smooth_densitySq
    curvature_transfers_to_normalizedFiniteCoordinate

/--
Build the branch-analytic package from an actual local real-projective
transition representative on each chart overlap.  This is the non-tautological
form: the transition data is existential rather than asking every
point-matching real projective map to be the local transition.
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

/-- The conformal metric represented by the canonical pullback-density candidate. -/
noncomputable def toConformalMetricOn
    (A : H.RegularLocusCanonicalBranchAnalyticData) :
    ConformalMetricOn X H.regularSet where
  densitySqInChart := H.canonicalPullbackDensityInChart
  densitySq_pos := by
    intro e he z hz hreg
    exact H.canonicalPullbackDensityInChart_pos_of_finiteCoordinate_deriv_ne_zero
      e he hz hreg (A.finiteCoordinate_deriv_ne_zero e he z hz hreg)
  densitySq_transition := A.densitySq_transition

/-- Analytic branch data supplies the canonical regular-locus pullback metric data. -/
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

namespace RegularLocusPullbackMetricData

variable {H : P.PGL2RHolonomyData x₀}

/--
The pullback curvature transfer and the off-real-line model computation give
curvature `-1` on the regular locus.

%%handwave
name:
  Curvature transfer from the off-real model
statement:
  If the curvature of a regular-locus pullback metric agrees pointwise with the curvature of (Im w)⁻²|dw|² at an off-real developing value, then the metric has curvature −1.
proof:
  The model metric has curvature −1 at every point with nonzero imaginary part; substitute this into the curvature-transfer identity.
-/
theorem curvature_minus_one (D : H.RegularLocusPullbackMetricData) :
    D.metric.HasCurvatureMinusOne := by
  intro e he z hz hreg
  rcases D.curvature_transfers_to_offRealLine e he z hz hreg with
    ⟨F, hF_offReal, hcurv⟩
  rw [hcurv]
  exact offRealLineDensitySq_gaussianCurvature_eq_minus_one (z := F z) hF_offReal

/-- Forget pullback provenance after deriving curvature from the model. -/
def toRegularLocusConformalMetricData
    (D : H.RegularLocusPullbackMetricData) :
    H.RegularLocusConformalMetricData where
  metric := D.metric
  metric_smooth_on_regularSet := D.metric_smooth_on_regularSet
  curvature_minus_one := D.curvature_minus_one
  pullback_density_on_regularSet := D.pullback_density_on_regularSet

end RegularLocusPullbackMetricData

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

/-- Combine topological and conformal data into full regular-locus metric data. -/
def ofTopologicalAndConformal
    (T : H.RegularLocusTopologicalData)
    (M : H.RegularLocusConformalMetricData) :
    H.RegularLocusMetricData where
  toRegularLocusTopologicalData := T
  toRegularLocusConformalMetricData := M

/--
Full regular-locus metric data is exactly the topological and conformal pieces.

%%handwave
name:
  Regular-locus metric data split into topological and conformal parts
statement:
  Full regular-locus metric data exist exactly when both openness data for the regular locus and smooth curvature −1 conformal metric data exist.
proof:
  Project full data to its two components in one direction; in the other, combine the given topological and conformal records.
-/
theorem nonempty_iff :
    Nonempty H.RegularLocusMetricData ↔
      Nonempty H.RegularLocusTopologicalData ∧
        Nonempty H.RegularLocusConformalMetricData := by
  constructor
  · rintro ⟨M⟩
    exact ⟨⟨M.toRegularLocusTopologicalData⟩, ⟨M.toRegularLocusConformalMetricData⟩⟩
  · rintro ⟨⟨T⟩, ⟨M⟩⟩
    exact ⟨ofTopologicalAndConformal T M⟩

/-- The singular hyperbolic metric obtained from metric data on the canonical regular locus. -/
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

/--
Concrete forward-construction data for the singular hyperbolic metric attached
to a real projective structure.
-/
structure ComplexProjectiveStructure.ForwardSingularHyperbolicMetricData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) where
  /-- Real projective holonomy data tied to the projective atlas. -/
  pgl2rHolonomyData : P.PGL2RHolonomyData x₀
  /-- Metric data on the canonical regular locus. -/
  regularLocusMetricData : pgl2rHolonomyData.RegularLocusMetricData

namespace ComplexProjectiveStructure.ForwardSingularHyperbolicMetricData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {P : ComplexProjectiveStructure X}

/-- The singular hyperbolic metric obtained from the stored forward construction data. -/
def toSingularHyperbolicMetric
    (D : P.ForwardSingularHyperbolicMetricData x₀) :
    SingularHyperbolicMetric X :=
  D.regularLocusMetricData.toSingularHyperbolicMetric

end ComplexProjectiveStructure.ForwardSingularHyperbolicMetricData

namespace ComplexProjectiveStructure

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/-- The regular-locus metric construction package for the forward direction. -/
def HasRegularLocusMetricConstruction (x₀ : X) (P : ComplexProjectiveStructure X) :
    Prop :=
  ∀ H : P.PGL2RHolonomyData x₀, Nonempty H.RegularLocusCanonicalPullbackMetricData

/-- The branch-analytic construction package for the forward direction. -/
def HasRegularLocusCanonicalBranchAnalyticConstruction
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀, Nonempty H.RegularLocusCanonicalBranchAnalyticData

/--
Canonical-density analytic construction package: smoothness of the canonical
density and transfer of its curvature calculation to the off-real model
coordinate.
-/
def HasRegularLocusCanonicalDensityAnalyticConstruction
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀, Nonempty H.RegularLocusCanonicalDensityAnalyticData

/--
Branch-level analytic construction package for the forward direction:
smoothness and curvature transfer for the fixed local pullback-density
functions.
-/
def HasRegularLocusLocalPullbackDensityAnalyticConstruction
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀,
    Nonempty H.RegularLocusLocalPullbackDensityAnalyticData

/--
Curvature-transfer form of the local forward calculation.

At this stage, branch smoothness is proved from the smooth atlas and the
projective compatibility data, so this package isolates the curvature identity
for the pullback density.
-/
def HasRegularLocusLocalPullbackDensityCurvatureTransfer
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀,
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        gaussianCurvatureOfDensitySq C.pullbackDensityFunction z =
          gaussianCurvatureOfDensitySq poincareDensitySqInChart (C.finiteCoordinate z)

/--
The local pullback curvature-transfer calculation supplies the branch-level
analytic construction, since branch smoothness is now internal.

%%handwave
name:
  Curvature transfer gives local pullback-density analytic data
statement:
  If every finite developing branch transfers the curvature of its pullback density to the off-real-line Poincare model, then these branch densities are smooth and have curvature −1 on the regular locus.
proof:
  Use the internally proved smoothness of each finite branch and package the assumed pointwise curvature-transfer identity.
-/
theorem hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityCurvatureTransfer
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityCurvatureTransfer x₀) :
    P.HasRegularLocusLocalPullbackDensityAnalyticConstruction x₀ := by
  intro H
  exact
    ⟨PGL2RHolonomyData.RegularLocusLocalPullbackDensityAnalyticData.ofCurvatureTransfer
      (H := H) (h H)⟩

/--
Explicit-Laplacian form of the local calculation for the pullback density. This
asks for the Laplacian of the local expression `log |F'| - log |Im F|`.
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
Split-Laplacian form of the local calculation.  The derivative contribution
is harmonic, while the imaginary-coordinate contribution supplies the
negative of the pulled-back hyperbolic density.
-/
def HasRegularLocusLocalPullbackDensitySplitLaplacian
    (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  ∀ H : P.PGL2RHolonomyData x₀,
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ)
      (hz : z ∈ e.target) (hreg : e.symm z ∈ H.regularSet),
        let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
        Laplacian.laplacian C.pullbackLogDerivativeTerm z = 0 ∧
          Laplacian.laplacian C.pullbackLogImaginaryTerm z =
            - C.pullbackDensityFunction z

/--
Height-term form of the local calculation: after the derivative term has been
proved harmonic, the moving height term supplies minus the pulled-back
hyperbolic density.
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
The split local Laplacian calculation gives the explicit local Liouville
calculation for the pulled-back density.

%%handwave
name:
  The split Laplacian gives the explicit pullback formula
statement:
  If Δ log|F′| = 0 and Δ log|Im F| = −|F′|²/(Im F)², then Δ(log|F′| − log|Im F|) = |F′|²/(Im F)².
proof:
  Use linearity of the Laplacian on the difference and substitute the two assumed identities.
-/
theorem hasRegularLocusLocalPullbackDensityExplicitLaplacian_of_localPullbackDensitySplitLaplacian
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensitySplitLaplacian x₀) :
    P.HasRegularLocusLocalPullbackDensityExplicitLaplacian x₀ := by
  intro H e he z hz hreg
  let C := H.regularLocusLocalPullbackCoordinateData e hz hreg
  exact C.pullbackDensityFunction_laplacian_logDensityExpression_of_split he hz
    (h H e he z hz hreg).1 (h H e he z hz hreg).2

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
The split local Laplacian calculation gives the branch-level analytic
construction.

%%handwave
name:
  Local pullback-density analytic data from harmonicity of log|F′| and the height identity Δ log|Im F| = −ρ²
statement:
  If every regular finite developing branch satisfies harmonicity of log|F′| and the height identity Δ log|Im F| = −ρ², then its pullback density is smooth and has curvature −1.
proof:
  Convert the assumed local identity to the Liouville equation for the pullback density, then use K = −(Δ log ρ)/ρ². The necessary branch smoothness is already established.
-/
theorem hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensitySplitLaplacian
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensitySplitLaplacian x₀) :
    P.HasRegularLocusLocalPullbackDensityAnalyticConstruction x₀ :=
  P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityExplicitLaplacian
    (P.hasRegularLocusLocalPullbackDensityExplicitLaplacian_of_localPullbackDensitySplitLaplacian h)

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

/--
The reduced canonical-density analytic construction is enough for the
regular-locus metric construction.

%%handwave
name:
  The canonical density directly constructs the regular-locus metric
statement:
  A smooth canonical pullback density whose curvature transfers to normalized finite coordinates determines a curvature −1 conformal metric on the regular locus.
proof:
  Use the canonical density as the chartwise metric density, its proved transition law for gluing, and curvature transfer to the Poincare model.
-/
theorem hasRegularLocusMetricConstruction_of_canonicalDensityAnalyticConstruction
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusCanonicalDensityAnalyticConstruction x₀) :
    P.HasRegularLocusMetricConstruction x₀ := by
  intro H
  rcases h H with ⟨A⟩
  exact ⟨A.toRegularLocusCanonicalPullbackMetricData⟩

end ComplexProjectiveStructure

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
Forget the projective-structure witness and retain existence of a singular metric.

%%handwave
name:
  An induced singular metric exists
statement:
  If a projective structure induces a singular hyperbolic metric tied to a chosen base point, then a singular hyperbolic metric on the underlying surface exists.
proof:
  Forget the equalities identifying the inducing projective structure and base point, retaining the metric itself.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_induces
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.InducesSingularHyperbolicMetric x₀) :
    Nonempty (SingularHyperbolicMetric X) := by
  rcases h with ⟨metric, _hP, _hx₀⟩
  exact ⟨metric⟩

/--
Metric data on the canonical regular locus produces a singular hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from regular-locus metric data
statement:
  Let (P) be a complex projective structure whose holonomy lies in
  (mathrm{PGL}_2(mathbb R)). If its regular locus carries a conformal
  metric of curvature (-1) with the prescribed developing-map pullback
  formula, then the surface carries a singular hyperbolic metric.
proof:
  Use the given metric on the open regular locus and take the complementary
  real-projective locus as the singular set; the supplied curvature and
  pullback identities are exactly the required metric properties.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_regularLocusMetricData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    {H : P.PGL2RHolonomyData x₀}
    (M : H.RegularLocusMetricData) :
    Nonempty (SingularHyperbolicMetric X) :=
  ⟨M.toSingularHyperbolicMetric⟩

/--
Topological and conformal pieces on the regular locus produce a singular metric.

%%handwave
name:
  An open regular locus with a curvature minus one metric determines a singular hyperbolic metric
statement:
  Suppose the real-projective locus is closed and its complement carries a smooth conformal metric of curvature −1 with the prescribed developing-map pullback formula. Then this regular-locus metric extends to a singular hyperbolic metric whose singular set is the real-projective locus.
proof:
  Use closedness to identify the open regular locus, combine it with the curvature −1 conformal metric there, and declare the complementary real-projective locus to be singular.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_regularLocusPieces
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    {H : P.PGL2RHolonomyData x₀}
    (T : H.RegularLocusTopologicalData)
    (M : H.RegularLocusConformalMetricData) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_regularLocusMetricData
    (ComplexProjectiveStructure.PGL2RHolonomyData.RegularLocusMetricData.ofTopologicalAndConformal
      T M)

/--
Pullback metric data on the regular locus produces a singular metric.

%%handwave
name:
  A singular hyperbolic metric from smooth pullback metric data on the regular locus
statement:
  Let (P) be a complex projective structure whose holonomy lies in
  (mathrm{PGL}_2(mathbb R)). Smooth developing-map pullback metric data on
  its regular locus determine a singular hyperbolic metric on the surface.
proof:
  Derive curvature −1 from transfer to the off-real Poincare model, then combine with the canonical topological data.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_regularLocusPullbackData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    {H : P.PGL2RHolonomyData x₀}
    (D : H.RegularLocusPullbackMetricData) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_regularLocusPieces
    H.regularLocusTopologicalData D.toRegularLocusConformalMetricData

/--
Canonical pullback metric data on the regular locus produces a singular metric.

%%handwave
name:
  A singular hyperbolic metric from canonical pullback metric data on the regular locus
statement:
  Let (P) be a complex projective structure whose holonomy lies in
  (mathrm{PGL}_2(mathbb R)). Its canonical pullback metric on the regular
  locus determines a singular hyperbolic metric on the surface.
proof:
  Forget to general pullback metric data and construct the singular metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_regularLocusCanonicalPullbackData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    {H : P.PGL2RHolonomyData x₀}
    (D : H.RegularLocusCanonicalPullbackMetricData) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_regularLocusPullbackData
    D.toRegularLocusPullbackMetricData

/--
Canonical branch analytic data on the regular locus produces a singular metric.

%%handwave
name:
  A singular hyperbolic metric from compatible analytic normalized-branch data
statement:
  Let (P) be a complex projective structure whose holonomy lies in
  (mathrm{PGL}_2(mathbb R)). Compatible analytic normalized branches on
  its regular locus determine a singular hyperbolic metric on the surface.
proof:
  Turn the branch data into the canonical pullback conformal metric and package the singular metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_regularLocusBranchAnalyticData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    {H : P.PGL2RHolonomyData x₀}
    (A : H.RegularLocusCanonicalBranchAnalyticData) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_regularLocusCanonicalPullbackData
    A.toRegularLocusCanonicalPullbackMetricData

/--
Construction data for the forward metric produces a singular hyperbolic metric.

%%handwave
name:
  The canonical forward construction produces a singular hyperbolic metric
statement:
  A projective structure equipped with its canonical curvature −1 metric on the complement of the real-projective locus determines a singular hyperbolic metric on the whole surface.
proof:
  Take the constructed regular-locus metric, use the real-projective locus as the singular set, and retain the developing-map pullback formula.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_forwardData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (D : P.ForwardSingularHyperbolicMetricData x₀) :
    Nonempty (SingularHyperbolicMetric X) :=
  ⟨D.toSingularHyperbolicMetric⟩

/--
Regular-locus metric construction data for every real-projective holonomy
certificate produces a singular hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from a regular-locus curvature −1 metric construction
statement:
  If P has real projective holonomy and a regular-locus curvature −1 metric construction, then a singular hyperbolic metric exists on the underlying surface.
proof:
  Choose the given real-projective holonomy realization. The assumed
  construction supplies its canonical pullback metric on the regular locus,
  which determines the singular hyperbolic metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_metricConstruction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusMetricConstruction x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) := by
  rcases hP with ⟨H⟩
  rcases h H with ⟨D⟩
  exact P.induceSingularHyperbolicMetric_of_regularLocusCanonicalPullbackData D

/--
Branch analytic construction data for every real-projective holonomy
certificate produces a singular hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from compatible normalized branches with smooth curvature −1 densities
statement:
  If P has real projective holonomy and compatible normalized branches with smooth curvature −1 densities, then a singular hyperbolic metric exists on the underlying surface.
proof:
  Choose the given real-projective holonomy realization. The assumed
  construction supplies compatible normalized branches, whose canonical
  pullback metric determines the singular hyperbolic metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_branchAnalyticConstruction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusCanonicalBranchAnalyticConstruction x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) := by
  rcases hP with ⟨H⟩
  rcases h H with ⟨A⟩
  exact P.induceSingularHyperbolicMetric_of_regularLocusBranchAnalyticData A

/--
Canonical-density analytic construction data for the forward metric produces a
singular hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from a smooth canonical pullback density with curvature transfer
statement:
  If P has real projective holonomy and a smooth canonical pullback density with curvature transfer, then a singular hyperbolic metric exists on the underlying surface.
proof:
  Convert the smooth canonical density and its curvature transfer into
  compatible normalized-branch data, then use the corresponding regular-locus
  metric to obtain the singular hyperbolic metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_canonicalDensityAnalyticConstruction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusCanonicalDensityAnalyticConstruction x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_branchAnalyticConstruction
    (P.hasRegularLocusCanonicalBranchAnalyticConstruction_of_canonicalDensityAnalyticConstruction h)
    hP

/--
Branch-level smoothness and curvature transfer for the local pullback-density
functions produce the singular hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from smooth local branch pullback densities with curvature transfer
statement:
  If P has real projective holonomy and smooth local branch pullback densities with curvature transfer, then a singular hyperbolic metric exists on the underlying surface.
proof:
  The smooth local pullback densities and their curvature transfer determine
  the canonical density construction. Its regular-locus metric gives the
  singular hyperbolic metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_localPullbackDensityAnalyticConstruction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityAnalyticConstruction x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_canonicalDensityAnalyticConstruction
    (P.hasRegularLocusCanonicalDensityAnalyticConstruction_of_localPullbackDensityAnalyticConstruction h)
    hP

/--
The local pullback curvature-transfer calculation is enough to produce the
singular hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from local curvature transfer from branch pullbacks to the Poincare model
statement:
  If P has real projective holonomy and local curvature transfer from branch pullbacks to the Poincare model, then a singular hyperbolic metric exists on the underlying surface.
proof:
  The local curvature-transfer identity supplies smooth curvature-(-1)
  pullback densities. Apply the regular-locus metric construction to obtain
  the singular hyperbolic metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_localPullbackDensityCurvatureTransfer
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityCurvatureTransfer x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_localPullbackDensityAnalyticConstruction
    (P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityCurvatureTransfer h)
    hP

/--
The Liouville equation for the local pullback density is enough to produce
the singular hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from the local Liouville equation Δ log ρ = ρ²
statement:
  If P has real projective holonomy and the local Liouville equation Δ log ρ = ρ², then a singular hyperbolic metric exists on the underlying surface.
proof:
  The Liouville equation gives curvature (-1) for the local pullback
  densities. These densities define the regular-locus metric and hence the
  singular hyperbolic metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_localPullbackDensityLiouvilleEquation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityLiouvilleEquation x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_localPullbackDensityAnalyticConstruction
    (P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityLiouvilleEquation h)
    hP

/--
The explicit local Laplacian calculation for `log |F'| - log |Im F|` is enough
to produce the singular hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from the identity Δ(log|F′| − log|Im F|) = ρ²
statement:
  If P has real projective holonomy and the identity Δ(log|F′| − log|Im F|) = ρ², then a singular hyperbolic metric exists on the underlying surface.
proof:
  The displayed Laplacian identity is the Liouville equation for the local
  pullback density. It yields the regular-locus curvature-(-1) metric and
  therefore the singular hyperbolic metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_localPullbackDensityExplicitLaplacian
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityExplicitLaplacian x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_localPullbackDensityAnalyticConstruction
    (P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityExplicitLaplacian h)
    hP

/--
The split local Laplacian calculation for the derivative and
imaginary-coordinate terms is enough to produce the singular hyperbolic
metric.

%%handwave
name:
  A singular hyperbolic metric from the split derivative and height Laplacian identities
statement:
  If P has real projective holonomy and the split derivative and height Laplacian identities, then a singular hyperbolic metric exists on the underlying surface.
proof:
  Combine the derivative and height Laplacian identities to obtain the
  Liouville equation for the pullback density, then construct the
  curvature-(-1) regular-locus metric and the resulting singular metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_localPullbackDensitySplitLaplacian
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensitySplitLaplacian x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_localPullbackDensityAnalyticConstruction
    (P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensitySplitLaplacian h)
    hP

/--
The moving-height Laplacian calculation is enough to produce the singular
hyperbolic metric.

%%handwave
name:
  A singular hyperbolic metric from the height identity Δ log|Im F| = −ρ²
statement:
  If P has real projective holonomy and the height identity Δ log|Im F| = −ρ², then a singular hyperbolic metric exists on the underlying surface.
proof:
  The height identity, together with harmonicity of the logarithm of the
  nonvanishing derivative, gives the Liouville equation for the pullback
  density. The resulting regular-locus metric defines the singular metric.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_localPullbackDensityImaginaryLaplacian
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : P.HasRegularLocusLocalPullbackDensityImaginaryLaplacian x₀)
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_localPullbackDensityAnalyticConstruction
    (P.hasRegularLocusLocalPullbackDensityAnalyticConstruction_of_localPullbackDensityImaginaryLaplacian h)
    hP

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

/--
Forget the inducing projective structure and retain existence of a singular metric.

%%handwave
name:
  Existence of the induced singular hyperbolic metric
statement:
  Every complex projective structure with holonomy in PGL₂(ℝ) admits a singular hyperbolic metric on its underlying surface.
proof:
  Construct the metric together with its inducing projective-structure witness, then forget that witness.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (hP : HasPGL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_induces
    (P.induceSingularHyperbolicMetric hP)

/--
The orientation-preserving real-holonomy case follows from the real-projective version.

%%handwave
name:
  Orientation-preserving real holonomy induces a singular metric
statement:
  A complex projective structure with holonomy in PSL₂(ℝ) induces a singular hyperbolic metric on the complement of its real-projective locus.
proof:
  View PSL₂(ℝ) holonomy as PGL₂(ℝ) holonomy and apply the real-projective construction.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_of_hasPSL2RHolonomy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (hP : HasPSL2RHolonomy x₀ P) :
    P.InducesSingularHyperbolicMetric x₀ :=
  P.induceSingularHyperbolicMetric (hasPGL2RHolonomy_of_hasPSL2RHolonomy hP)

/--
The orientation-preserving real-holonomy case also gives plain metric existence.

%%handwave
name:
  A singular metric exists for orientation-preserving real holonomy
statement:
  Every complex projective structure with holonomy in PSL₂(ℝ) admits a singular hyperbolic metric.
proof:
  Promote the holonomy to PGL₂(ℝ), construct the induced metric, and forget the inducing witness.
-/
theorem ComplexProjectiveStructure.induceSingularHyperbolicMetric_nonempty_of_hasPSL2RHolonomy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (hP : HasPSL2RHolonomy x₀ P) :
    Nonempty (SingularHyperbolicMetric X) :=
  P.induceSingularHyperbolicMetric_of_induces
    (P.induceSingularHyperbolicMetric_of_hasPSL2RHolonomy hP)

end

end JJMath
