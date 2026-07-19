import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Mobius transformations of the Riemann sphere

This file collects the projective-line vocabulary needed for complex projective
structures.  Mathlib already has the action of `GL(2, K)` on `OnePoint K` by
fractional linear transformations, and it has `PGL(2, K)` as a quotient group.

For now we use `GL(2, ℂ)` representatives when talking about actual maps on the
Riemann sphere.  The quotient by scalar matrices is recorded separately as the
holonomy target.
-/

namespace JJMath

open scoped MatrixGroups Topology
open Filter

noncomputable section

local instance : DecidableEq ℂ := Classical.decEq ℂ

/-- The Riemann sphere, represented as the one-point compactification of `ℂ`. -/
abbrev RiemannSphere : Type :=
  OnePoint ℂ

/-- Matrix representatives for Mobius transformations of the Riemann sphere. -/
abbrev MobiusRepresentative : Type :=
  GL (Fin 2) ℂ

/-- The projective Mobius group `PGL(2, ℂ)`. -/
abbrev MobiusGroup : Type :=
  PGL(2, ℂ)

/-- A map of the Riemann sphere is Mobius if it is induced by a `GL(2, ℂ)` matrix. -/
def IsMobiusMap (f : RiemannSphere → RiemannSphere) : Prop :=
  ∃ g : MobiusRepresentative, f = fun z ↦ g • z

/--
%%handwave
name:
  Matrix actions are Möbius maps
statement:
  For every \(g\in\operatorname{GL}_2(\mathbb C)\), the map
  \(z\mapsto g\cdot z\) on \(\widehat{\mathbb C}\) is a Möbius map.
proof:
  Use \(g\) itself as the required matrix representative.
-/
theorem isMobiusMap_smul (g : MobiusRepresentative) :
    IsMobiusMap (fun z : RiemannSphere ↦ g • z) :=
  ⟨g, rfl⟩

/-- The numerator of a complex Mobius representative in the finite affine chart. -/
def mobiusFiniteNum (A : MobiusRepresentative) (z : ℂ) : ℂ :=
  A 0 0 * z + A 0 1

/-- The denominator of a complex Mobius representative in the finite affine chart. -/
def mobiusFiniteDenom (A : MobiusRepresentative) (z : ℂ) : ℂ :=
  A 1 0 * z + A 1 1

/-- The finite affine formula for a complex Mobius representative. -/
def mobiusFiniteFormula (A : MobiusRepresentative) (z : ℂ) : ℂ :=
  mobiusFiniteNum A z / mobiusFiniteDenom A z

/--
%%handwave
name:
  Finite formula for the Möbius action
statement:
  Let \(A=(a_{ij})\in\operatorname{GL}_2(\mathbb C)\) and \(z\in\mathbb C\).
  If \(a_{10}z+a_{11}\ne0\), then
  \(A\cdot z=(a_{00}z+a_{01})/(a_{10}z+a_{11})\) as a finite point of
  \(\widehat{\mathbb C}\).
proof:
  Evaluate the projective-line action; the nonzero-denominator hypothesis
  selects its finite branch.
-/
theorem mobiusRepresentative_smul_coe_eq_mobiusFiniteFormula
    (A : MobiusRepresentative) {z : ℂ} (hden : mobiusFiniteDenom A z ≠ 0) :
    A • (z : RiemannSphere) = (mobiusFiniteFormula A z : RiemannSphere) := by
  rw [OnePoint.smul_some_eq_ite]
  rw [if_neg (by simpa [mobiusFiniteDenom] using hden)]
  simp [mobiusFiniteFormula, mobiusFiniteNum, mobiusFiniteDenom]

/--
%%handwave
name:
  A finite Möbius value has nonzero denominator
statement:
  If \(A\in\operatorname{GL}_2(\mathbb C)\) sends the finite point \(z\) to the
  finite point \(w\), then \(a_{10}z+a_{11}\ne0\).
proof:
  If the denominator vanished, the projective-line action would send \(z\) to
  infinity, contradicting the assumed finite value.
-/
theorem mobiusFiniteDenom_ne_zero_of_smul_coe_eq_coe
    (A : MobiusRepresentative) {z w : ℂ}
    (h : A • (z : RiemannSphere) = (w : RiemannSphere)) :
    mobiusFiniteDenom A z ≠ 0 := by
  intro hden
  rw [OnePoint.smul_some_eq_ite] at h
  rw [if_pos (by simpa [mobiusFiniteDenom] using hden)] at h
  exact OnePoint.infty_ne_coe w h

/--
%%handwave
name:
  Recovering the affine fractional-linear formula
statement:
  If \(A\in\operatorname{GL}_2(\mathbb C)\) sends the finite point \(z\) to the
  finite point \(w\), then
  \((a_{00}z+a_{01})/(a_{10}z+a_{11})=w\).
proof:
  First deduce that the denominator is nonzero, apply the finite action formula,
  and use injectivity of the inclusion \(\mathbb C\hookrightarrow\widehat{\mathbb C}\).
-/
theorem mobiusFiniteFormula_eq_of_smul_coe_eq_coe
    (A : MobiusRepresentative) {z w : ℂ}
    (h : A • (z : RiemannSphere) = (w : RiemannSphere)) :
    mobiusFiniteFormula A z = w := by
  have hden := mobiusFiniteDenom_ne_zero_of_smul_coe_eq_coe A h
  have hformula := mobiusRepresentative_smul_coe_eq_mobiusFiniteFormula A hden
  exact OnePoint.coe_injective (by simpa [hformula] using h)

/--
%%handwave
name:
  Derivative of a fractional-linear map
statement:
  For \(A=(a_{ij})\in\operatorname{GL}_2(\mathbb C)\) and
  \(a_{10}z+a_{11}\ne0\), the fractional-linear map has complex derivative
  \(\det(A)/(a_{10}z+a_{11})^2\) at \(z\).
proof:
  Apply the quotient rule to the affine numerator and denominator.  Expanding
  the numerator of the derivative gives \(a_{00}a_{11}-a_{01}a_{10}=\det(A)\).
-/
theorem mobiusFiniteFormula_hasDerivAt
    (A : MobiusRepresentative) {z : ℂ} (hden : mobiusFiniteDenom A z ≠ 0) :
    HasDerivAt (mobiusFiniteFormula A)
      (A.det.val / (mobiusFiniteDenom A z) ^ 2) z := by
  have hnum :
      HasDerivAt (fun w : ℂ ↦ A 0 0 * w + A 0 1) (A 0 0) z := by
    simpa only [mul_one] using
      (((hasDerivAt_id' z).const_mul (A 0 0)).add_const (A 0 1))
  have hdenom :
      HasDerivAt (fun w : ℂ ↦ A 1 0 * w + A 1 1) (A 1 0) z := by
    simpa only [mul_one] using
      (((hasDerivAt_id' z).const_mul (A 1 0)).add_const (A 1 1))
  convert
    hnum.div hdenom hden
    using 1
  · simp [mobiusFiniteDenom, Matrix.det_fin_two]
    ring

/--
%%handwave
name:
  Fractional-linear maps are complex differentiable off their pole
statement:
  If \(a_{10}z+a_{11}\ne0\), then
  \(w\mapsto(a_{00}w+a_{01})/(a_{10}w+a_{11})\) is complex differentiable at \(z\).
proof:
  This is the differentiability consequence of [the derivative equals \(\det(A)/(a_{10}z+a_{11})^2\)](lean:JJMath.mobiusFiniteFormula_hasDerivAt).
-/
theorem mobiusFiniteFormula_differentiableAt
    (A : MobiusRepresentative) {z : ℂ} (hden : mobiusFiniteDenom A z ≠ 0) :
    DifferentiableAt ℂ (mobiusFiniteFormula A) z :=
  (mobiusFiniteFormula_hasDerivAt A hden).differentiableAt

/--
%%handwave
name:
  Fractional-linear maps are smooth off their pole
statement:
  If \(a_{10}z+a_{11}\ne0\), then
  \(w\mapsto(a_{00}w+a_{01})/(a_{10}w+a_{11})\) is complex smooth at \(z\).
proof:
  Affine functions are smooth, and the quotient of two smooth functions is
  smooth wherever the denominator is nonzero.
-/
theorem mobiusFiniteFormula_contDiffAt
    (A : MobiusRepresentative) {z : ℂ} (hden : mobiusFiniteDenom A z ≠ 0) :
    ContDiffAt ℂ ⊤ (mobiusFiniteFormula A) z := by
  have hnum :
      ContDiffAt ℂ ⊤ (fun w : ℂ ↦ A 0 0 * w + A 0 1) z :=
    (contDiff_const.mul contDiff_id).add contDiff_const |>.contDiffAt
  have hdenom :
      ContDiffAt ℂ ⊤ (fun w : ℂ ↦ A 1 0 * w + A 1 1) z :=
    (contDiff_const.mul contDiff_id).add contDiff_const |>.contDiffAt
  simpa [mobiusFiniteFormula, mobiusFiniteNum, mobiusFiniteDenom] using
    hnum.div hdenom hden

/--
%%handwave
name:
  Value of the derivative of a fractional-linear map
statement:
  For \(A=(a_{ij})\in\operatorname{GL}_2(\mathbb C)\) and
  \(a_{10}z+a_{11}\ne0\),
  \[\frac{d}{dz}\frac{a_{00}z+a_{01}}{a_{10}z+a_{11}}
    =\frac{\det A}{(a_{10}z+a_{11})^2}.\]
proof:
  Take the value supplied by [the derivative equals \(\det(A)/(a_{10}z+a_{11})^2\)](lean:JJMath.mobiusFiniteFormula_hasDerivAt).
-/
theorem mobiusFiniteFormula_deriv
    (A : MobiusRepresentative) {z : ℂ} (hden : mobiusFiniteDenom A z ≠ 0) :
    deriv (mobiusFiniteFormula A) z =
      A.det.val / (mobiusFiniteDenom A z) ^ 2 :=
  (mobiusFiniteFormula_hasDerivAt A hden).deriv

/--
%%handwave
name:
  A Möbius derivative never vanishes off its pole
statement:
  For \(A\in\operatorname{GL}_2(\mathbb C)\), the derivative
  \(\det(A)/(a_{10}z+a_{11})^2\) is nonzero whenever \(a_{10}z+a_{11}\ne0\).
proof:
  Substitute the derivative formula; both the determinant and the squared
  denominator are nonzero.
-/
theorem mobiusFiniteFormula_deriv_ne_zero
    (A : MobiusRepresentative) {z : ℂ} (hden : mobiusFiniteDenom A z ≠ 0) :
    deriv (mobiusFiniteFormula A) z ≠ 0 := by
  rw [mobiusFiniteFormula_deriv A hden]
  exact div_ne_zero A.det_ne_zero (pow_ne_zero 2 hden)

/-- Inversion on the finite part of the Riemann sphere, with `0` sent to infinity. -/
def riemannSphereInvFinite (z : ℂ) : RiemannSphere :=
  if z = 0 then OnePoint.infty else ((z⁻¹ : ℂ) : RiemannSphere)

/-- Inversion on the Riemann sphere, exchanging `0` and infinity. -/
def riemannSphereInv (z : RiemannSphere) : RiemannSphere :=
  z.elim ((0 : ℂ) : RiemannSphere) riemannSphereInvFinite

/--
%%handwave
name:
  Spherical inversion sends infinity to zero
statement:
  Under spherical inversion, \(\iota(\infty)=0\).
proof:
  This is the infinity branch in the definition of spherical inversion.
-/
@[simp]
theorem riemannSphereInv_infty :
    riemannSphereInv OnePoint.infty = ((0 : ℂ) : RiemannSphere) :=
  rfl

/--
%%handwave
name:
  Spherical inversion sends zero to infinity
statement:
  Under spherical inversion, \(\iota(0)=\infty\).
proof:
  Evaluate the finite branch at zero.
-/
@[simp]
theorem riemannSphereInv_zero :
    riemannSphereInv ((0 : ℂ) : RiemannSphere) = OnePoint.infty := by
  simp [riemannSphereInv, riemannSphereInvFinite]

/--
%%handwave
name:
  Spherical inversion at a nonzero finite point
statement:
  For \(z\in\mathbb C^\times\), spherical inversion sends the corresponding
  finite point to the finite point \(z^{-1}\).
proof:
  The nonzero hypothesis selects the reciprocal branch of the definition.
-/
@[simp]
theorem riemannSphereInv_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    riemannSphereInv (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := by
  simp [riemannSphereInv, riemannSphereInvFinite, hz]

/--
%%handwave
name:
  Finite-part spherical inversion is continuous
statement:
  The map \(\mathbb C\to\widehat{\mathbb C}\) sending (0) to infinity and
  \(z\ne0\) to \(z^{-1}\) is continuous.
proof:
  Away from zero this is ordinary inversion followed by the finite inclusion.
  At zero, \(z^{-1}\) escapes every compact set as \(z\to0\), hence converges to
  the point at infinity in the one-point compactification.
-/
theorem riemannSphereInvFinite_continuous :
    Continuous riemannSphereInvFinite := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    rw [ContinuousAt, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
    constructor
    · have hinv : Tendsto Inv.inv (𝓝[≠] (0 : ℂ)) (Filter.coclosedCompact ℂ) := by
        simpa [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
          (tendsto_inv₀_nhdsNE_zero (α := ℂ))
      have hpunct :
          Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere))
            (𝓝[≠] (0 : ℂ)) (𝓝 (OnePoint.infty : RiemannSphere)) :=
        OnePoint.tendsto_coe_infty.comp hinv
      simpa [riemannSphereInvFinite] using hpunct.congr' (by
        filter_upwards [eventually_mem_nhdsWithin] with w hw
        have hne : w ≠ 0 := by simpa using hw
        simp [riemannSphereInvFinite, hne])
    · exact tendsto_pure_nhds (f := riemannSphereInvFinite) (a := (0 : ℂ))
  · have hlocal :
        riemannSphereInvFinite =ᶠ[𝓝 z] fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp [riemannSphereInvFinite, hw]
    have hinv :
        Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere)) (𝓝 z)
          (𝓝 (((z⁻¹ : ℂ) : RiemannSphere))) :=
      OnePoint.continuous_coe.continuousAt.comp (tendsto_inv₀ hz)
    change Tendsto riemannSphereInvFinite (𝓝 z) (𝓝 (riemannSphereInvFinite z))
    simpa [riemannSphereInvFinite, hz] using hinv.congr' hlocal.symm

/--
%%handwave
name:
  Spherical inversion is continuous
statement:
  The map \(\iota:\widehat{\mathbb C}\to\widehat{\mathbb C}\) exchanging
  (0) with \(\infty\) and sending \(z\ne0\) to \(z^{-1}\) is continuous.
proof:
  On the finite chart use finite-part continuity.  At infinity, ordinary
  inversion tends to zero along the cocompact filter.
-/
theorem riemannSphereInv_continuous :
    Continuous riemannSphereInv := by
  rw [OnePoint.continuous_iff]
  constructor
  · have hinv : Tendsto Inv.inv (Filter.coclosedCompact ℂ) (𝓝 (0 : ℂ)) := by
      simpa [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded (α := ℂ))
    have hcoe :
        Tendsto (fun z : ℂ ↦ ((z⁻¹ : ℂ) : RiemannSphere))
          (Filter.coclosedCompact ℂ) (𝓝 (((0 : ℂ) : RiemannSphere))) :=
      (OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hinv
    have hzeroCompl : ({(0 : ℂ)} : Set ℂ)ᶜ ∈ Filter.coclosedCompact ℂ :=
      (isCompact_singleton (x := (0 : ℂ))).compl_mem_coclosedCompact_of_isClosed
        isClosed_singleton
    refine hcoe.congr' ?_
    filter_upwards [hzeroCompl] with z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp [riemannSphereInv, riemannSphereInvFinite, hz]
  · simpa [riemannSphereInv] using riemannSphereInvFinite_continuous

/-- Translation of the complex plane as a homeomorphism. -/
def complexTranslationHomeomorph (a : ℂ) : ℂ ≃ₜ ℂ where
  toFun z := z + a
  invFun z := z - a
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  continuous_toFun := continuous_id.add continuous_const
  continuous_invFun := continuous_id.sub continuous_const

/-- Translation on the Riemann sphere, fixing infinity. -/
def riemannSphereTranslation (a : ℂ) : RiemannSphere → RiemannSphere :=
  OnePoint.map (fun z : ℂ ↦ z + a)

/--
%%handwave
name:
  Affine translation extends continuously to the Riemann sphere
statement:
  For every \(a\in\mathbb C\), the extension of \(z\mapsto z+a\) that fixes
  infinity is continuous on \(\widehat{\mathbb C}\).
proof:
  Translation is a homeomorphism of \(\mathbb C\), and every homeomorphism
  extends continuously to its one-point compactification.
-/
theorem riemannSphereTranslation_continuous (a : ℂ) :
    Continuous (riemannSphereTranslation a) :=
  (Homeomorph.onePointCongr (complexTranslationHomeomorph a)).continuous

/--
%%handwave
name:
  Translation fixes infinity
statement:
  For every \(a\in\mathbb C\), the extended translation satisfies
  \(T_a(\infty)=\infty\).
proof:
  This is the infinity branch of the one-point extension.
-/
@[simp]
theorem riemannSphereTranslation_infty (a : ℂ) :
    riemannSphereTranslation a OnePoint.infty = OnePoint.infty :=
  rfl

/--
%%handwave
name:
  Translation on finite points
statement:
  For \(a,z\in\mathbb C\), the extended translation sends the finite point
  \(z\) to the finite point (z+a).
proof:
  This is the finite branch of the one-point extension.
-/
@[simp]
theorem riemannSphereTranslation_coe (a z : ℂ) :
    riemannSphereTranslation a (z : RiemannSphere) = ((z + a : ℂ) : RiemannSphere) :=
  rfl

/-- Nonzero dilation on the Riemann sphere, fixing infinity. -/
def riemannSphereDilation (a : ℂ) : RiemannSphere → RiemannSphere :=
  OnePoint.map (fun z : ℂ ↦ a * z)

/--
%%handwave
name:
  Nonzero dilation extends continuously to the Riemann sphere
statement:
  For \(a\in\mathbb C^\times\), the extension of \(z\mapsto az\) that fixes
  infinity is continuous on \(\widehat{\mathbb C}\).
proof:
  Multiplication by \(a\ne0\) is a homeomorphism of \(\mathbb C\), so its
  one-point extension is continuous.
-/
theorem riemannSphereDilation_continuous {a : ℂ} (ha : a ≠ 0) :
    Continuous (riemannSphereDilation a) := by
  simpa [riemannSphereDilation] using
    (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ a ha)).continuous

/--
%%handwave
name:
  Dilation fixes infinity
statement:
  For every \(a\in\mathbb C\), the extended dilation satisfies
  \(D_a(\infty)=\infty\).
proof:
  This is the infinity branch of the one-point extension.
-/
@[simp]
theorem riemannSphereDilation_infty (a : ℂ) :
    riemannSphereDilation a OnePoint.infty = OnePoint.infty :=
  rfl

/--
%%handwave
name:
  Dilation on finite points
statement:
  For \(a,z\in\mathbb C\), the extended dilation sends the finite point \(z\)
  to the finite point (az).
proof:
  This is the finite branch of the one-point extension.
-/
@[simp]
theorem riemannSphereDilation_coe (a z : ℂ) :
    riemannSphereDilation a (z : RiemannSphere) = ((a * z : ℂ) : RiemannSphere) :=
  rfl

/--
%%handwave
name:
  Upper-triangular Möbius matrices act continuously
statement:
  If \(A=(a_{ij})\in\operatorname{GL}_2(\mathbb C)\) has \(a_{10}=0\), then
  \(z\mapsto A\cdot z\) is continuous on \(\widehat{\mathbb C}\).
proof:
  Invertibility forces \(a_{00},a_{11}\ne0\).  Factor the action as dilation by
  \(a_{00}/a_{11}\), followed by translation by \(a_{01}/a_{11}\).
-/
theorem mobiusRepresentative_smul_continuous_of_lowerLeft_eq_zero
    (A : MobiusRepresentative) (hc : A 1 0 = 0) :
    Continuous fun z : RiemannSphere ↦ A • z := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0 := by
    simpa [Matrix.det_fin_two] using A.det_ne_zero
  have ha : A 0 0 ≠ 0 := by
    intro h
    exact hdet (by simp [h, hc])
  have hd : A 1 1 ≠ 0 := by
    intro h
    exact hdet (by simp [h, hc])
  let F : RiemannSphere → RiemannSphere :=
    riemannSphereTranslation (A 0 1 / A 1 1) ∘
      riemannSphereDilation (A 0 0 / A 1 1)
  have hF : Continuous F :=
    (riemannSphereTranslation_continuous (A 0 1 / A 1 1)).comp
      (riemannSphereDilation_continuous (div_ne_zero ha hd))
  refine hF.congr ?_
  intro z
  induction z using OnePoint.rec with
  | infty =>
      simp [F, OnePoint.smul_infty_eq_ite, hc]
  | coe z =>
      rw [OnePoint.smul_some_eq_ite]
      simp [F, hc, hd]
      field_simp [hd]

/--
%%handwave
name:
  Möbius matrices with nonzero lower-left entry act continuously
statement:
  If \(A=(a_{ij})\in\operatorname{GL}_2(\mathbb C)\) has \(a_{10}\ne0\), then
  \(z\mapsto A\cdot z\) is continuous on \(\widehat{\mathbb C}\).
proof:
  Writing \(\Delta=\det A\), factor the fractional-linear action into a
  translation, inversion, the nonzero dilation \(-\Delta/a_{10}^2\), and a
  final translation.  Each factor is continuous.
-/
theorem mobiusRepresentative_smul_continuous_of_lowerLeft_ne_zero
    (A : MobiusRepresentative) (hc : A 1 0 ≠ 0) :
    Continuous fun z : RiemannSphere ↦ A • z := by
  let Δ : ℂ := A 0 0 * A 1 1 - A 0 1 * A 1 0
  have hdet : Δ ≠ 0 := by
    simpa [Δ, Matrix.det_fin_two] using A.det_ne_zero
  have hk : -Δ / (A 1 0) ^ 2 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hdet) (pow_ne_zero 2 hc)
  let F : RiemannSphere → RiemannSphere :=
    riemannSphereTranslation (A 0 0 / A 1 0) ∘
      riemannSphereDilation (-Δ / (A 1 0) ^ 2) ∘
        riemannSphereInv ∘
          riemannSphereTranslation (A 1 1 / A 1 0)
  have hF : Continuous F :=
    (riemannSphereTranslation_continuous (A 0 0 / A 1 0)).comp
      ((riemannSphereDilation_continuous hk).comp
        (riemannSphereInv_continuous.comp
          (riemannSphereTranslation_continuous (A 1 1 / A 1 0))))
  refine hF.congr ?_
  intro z
  induction z using OnePoint.rec with
  | infty =>
      simp [F, OnePoint.smul_infty_eq_ite, hc]
  | coe z =>
      rw [OnePoint.smul_some_eq_ite]
      by_cases hden : A 1 0 * z + A 1 1 = 0
      · have htrans0 : z + A 1 1 / A 1 0 = 0 := by
          apply mul_left_cancel₀ hc
          field_simp [hc]
          simpa [mul_add, add_comm, add_left_comm, add_assoc] using hden
        simp [F, hden, htrans0]
      · have htrans_ne : z + A 1 1 / A 1 0 ≠ 0 := by
          intro hz
          apply hden
          calc
            A 1 0 * z + A 1 1 = A 1 0 * (z + A 1 1 / A 1 0) := by
              field_simp [hc]
            _ = 0 := by simp [hz]
        simp [F, hden, htrans_ne]
        field_simp [hc, hden, htrans_ne, Δ]
        ring

/--
%%handwave
name:
  Every Möbius matrix acts continuously
statement:
  For every \(A\in\operatorname{GL}_2(\mathbb C)\), the fractional-linear map
  \(z\mapsto A\cdot z\) is continuous on \(\widehat{\mathbb C}\).
proof:
  Split according as the lower-left entry of \(A\) is zero or nonzero and apply
  the corresponding factorization theorem.
-/
theorem mobiusRepresentative_smul_continuous
    (A : MobiusRepresentative) :
    Continuous fun z : RiemannSphere ↦ A • z := by
  by_cases hc : A 1 0 = 0
  · exact mobiusRepresentative_smul_continuous_of_lowerLeft_eq_zero A hc
  · exact mobiusRepresentative_smul_continuous_of_lowerLeft_ne_zero A hc

instance instContinuousConstSMulMobiusRepresentativeRiemannSphere :
    ContinuousConstSMul MobiusRepresentative RiemannSphere where
  continuous_const_smul := mobiusRepresentative_smul_continuous

end

end JJMath
