import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import JJMath.ProjectiveGeometry.Mobius

/-!
# Real Mobius group

This file records the real projective group used as the holonomy target for
hyperbolic developing maps.  Analytically, this is the orientation-preserving
isometry group of the upper half-plane.

Mathlib already supplies the `SL(2, ℝ)` action on the upper half-plane by
fractional linear transformations.  We keep both the representative group
`SL(2, ℝ)` and its quotient `PSL(2, ℝ)` visible.
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold MatrixGroups

noncomputable section

/-- Matrix representatives for orientation-preserving real Mobius transformations. -/
abbrev RealMobiusRepresentative : Type :=
  SL(2, ℝ)

/-- The real Mobius group acting on the upper half-plane, written as `PSL(2, ℝ)`. -/
abbrev RealMobiusGroup : Type :=
  PSL(2, ℝ)

/-- The quotient map from `SL(2, ℝ)` representatives to `PSL(2, ℝ)`. -/
def realMobiusProjection : RealMobiusRepresentative →* RealMobiusGroup :=
  QuotientGroup.mk' _

/-- The upper-half-plane action of an `SL(2, ℝ)` representative. -/
def realMobiusRepresentativeAction (g : RealMobiusRepresentative) (z : ℍ) : ℍ :=
  g • z

/--
View a real Mobius representative as a complex Mobius representative by
extension of scalars `ℝ → ℂ`.
-/
def realMobiusRepresentativeAsMobiusRepresentative :
    RealMobiusRepresentative →* MobiusRepresentative :=
  Matrix.SpecialLinearGroup.mapGL ℂ

/--
The induced map from lifted real Mobius representatives to the complex
projective Mobius group.
-/
def realMobiusRepresentativeToMobiusGroup :
    RealMobiusRepresentative →* MobiusGroup :=
  (Matrix.ProjGenLinGroup.mk : MobiusRepresentative →* MobiusGroup).comp
    realMobiusRepresentativeAsMobiusRepresentative

/--
The complexification of a central real Mobius representative is central in
`GL(2, ℂ)`.
-/
theorem realMobiusRepresentativeAsMobiusRepresentative_mem_center
    {g : RealMobiusRepresentative}
    (hg : g ∈ Subgroup.center RealMobiusRepresentative) :
    realMobiusRepresentativeAsMobiusRepresentative g ∈
      Subgroup.center MobiusRepresentative := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  rcases (Matrix.SpecialLinearGroup.mem_center_iff (A := g)).mp hg with
    ⟨r, hrpow, hscalar⟩
  let uR : ℝˣ := {
    val := r
    inv := r
    val_inv := by
      have hcard : Fintype.card (Fin 2) = 2 := by simp
      simpa [hcard, pow_two] using hrpow
    inv_val := by
      have hcard : Fintype.card (Fin 2) = 2 := by simp
      simpa [hcard, pow_two] using hrpow
  }
  let uC : ℂˣ := Units.map (algebraMap ℝ ℂ).toMonoidHom uR
  refine ⟨uC, ?_⟩
  ext i j
  have hentry : Matrix.diagonal (fun _ : Fin 2 ↦ r) i j =
      (g : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    simpa [Matrix.scalar_apply] using congr_fun₂ hscalar i j
  by_cases hij : i = j
  · subst j
    simp [realMobiusRepresentativeAsMobiusRepresentative, uR, uC] at hentry ⊢
    exact_mod_cast hentry
  · simp [realMobiusRepresentativeAsMobiusRepresentative, uR, uC,
      Matrix.diagonal_apply_ne (fun _ : Fin 2 ↦ r) hij,
      Matrix.diagonal_apply_ne (fun _ : Fin 2 ↦ (r : ℂ)) hij] at hentry ⊢
    exact_mod_cast hentry

/-- Central real Mobius representatives become trivial in complex projective holonomy. -/
theorem realMobiusRepresentativeToMobiusGroup_eq_one_of_mem_center
    {g : RealMobiusRepresentative}
    (hg : g ∈ Subgroup.center RealMobiusRepresentative) :
    realMobiusRepresentativeToMobiusGroup g = 1 := by
  change Matrix.ProjGenLinGroup.mk
    (realMobiusRepresentativeAsMobiusRepresentative g) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
  exact realMobiusRepresentativeAsMobiusRepresentative_mem_center hg

/-- The canonical complexification homomorphism `PSL(2, ℝ) → PGL(2, ℂ)`. -/
def realMobiusToMobiusGroup : RealMobiusGroup →* MobiusGroup :=
  QuotientGroup.lift (Subgroup.center RealMobiusRepresentative)
    realMobiusRepresentativeToMobiusGroup
    (by
      intro g hg
      rw [MonoidHom.mem_ker]
      exact realMobiusRepresentativeToMobiusGroup_eq_one_of_mem_center hg)

/-- The subgroup of `PGL(2, ℂ)` obtained by complexifying `PSL(2, ℝ)`. -/
def psl2rMobiusSubgroup : Subgroup MobiusGroup :=
  MonoidHom.range realMobiusToMobiusGroup

@[simp]
theorem realMobiusToMobiusGroup_realMobiusProjection
    (g : RealMobiusRepresentative) :
    realMobiusToMobiusGroup (realMobiusProjection g) =
      realMobiusRepresentativeToMobiusGroup g := by
  rfl

@[simp]
theorem realMobiusRepresentativeAction_one (z : ℍ) :
    realMobiusRepresentativeAction 1 z = z := by
  simp [realMobiusRepresentativeAction]

@[simp]
theorem realMobiusRepresentativeAction_mul
    (g h : RealMobiusRepresentative) (z : ℍ) :
    realMobiusRepresentativeAction (g * h) z =
      realMobiusRepresentativeAction g (realMobiusRepresentativeAction h z) := by
  simpa [realMobiusRepresentativeAction] using (mul_smul g h z)

/--
Central `SL(2, ℝ)` representatives act trivially on the upper half-plane, so
the representative action descends to `PSL(2, ℝ)`.
-/
theorem realMobiusRepresentativeAction_eq_self_of_mem_center
    {g : RealMobiusRepresentative}
    (hg : g ∈ Subgroup.center RealMobiusRepresentative) (z : ℍ) :
    realMobiusRepresentativeAction g z = z := by
  rcases (Matrix.SpecialLinearGroup.mem_center_iff (A := g)).mp hg with
    ⟨r, hrpow, hscalar⟩
  have hr_ne : r ≠ 0 := by
    intro hr
    subst r
    simp at hrpow
  ext
  change UpperHalfPlane.smulAux' (g : GL (Fin 2) ℝ) z = (z : ℂ)
  have hdet_pos : 0 < ((g : GL (Fin 2) ℝ).det : ℝ) := by
    simp
  rw [UpperHalfPlane.smulAux', UpperHalfPlane.σ, if_pos hdet_pos]
  simp only [ContinuousAlgEquiv.refl_apply]
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = r := by
    simp [← hscalar, Matrix.scalar_apply]
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
    simp [← hscalar, Matrix.scalar_apply]
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
    simp [← hscalar, Matrix.scalar_apply]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = r := by
    simp [← hscalar, Matrix.scalar_apply]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, h00, h01, h10, h11,
    div_eq_mul_inv]
  have hrc : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr_ne
  field_simp [hrc]

/-- The permutation action of `SL(2, ℝ)` representatives on `ℍ`. -/
def realMobiusRepresentativePerm :
    RealMobiusRepresentative →* Equiv.Perm ℍ :=
  MulAction.toPermHom RealMobiusRepresentative ℍ

/-- The canonical action homomorphism `PSL(2, ℝ) → Equiv.Perm ℍ`. -/
def realMobiusActionHom : RealMobiusGroup →* Equiv.Perm ℍ :=
  QuotientGroup.lift (Subgroup.center RealMobiusRepresentative)
    realMobiusRepresentativePerm
    (by
      intro g hg
      rw [MonoidHom.mem_ker]
      ext z : 1
      exact realMobiusRepresentativeAction_eq_self_of_mem_center hg z)

/-- The canonical upper-half-plane action of a real projective Mobius transformation. -/
def realMobiusAction (g : RealMobiusGroup) (z : ℍ) : ℍ :=
  realMobiusActionHom g z

@[simp]
theorem realMobiusAction_realMobiusProjection
    (g : RealMobiusRepresentative) (z : ℍ) :
    realMobiusAction (realMobiusProjection g) z =
      realMobiusRepresentativeAction g z := by
  rfl

@[simp]
theorem realMobiusAction_one (z : ℍ) :
    realMobiusAction 1 z = z := by
  simp [realMobiusAction]

@[simp]
theorem realMobiusAction_mul (g h : RealMobiusGroup) (z : ℍ) :
    realMobiusAction (g * h) z =
      realMobiusAction g (realMobiusAction h z) := by
  change (realMobiusActionHom (g * h)) z =
    (realMobiusActionHom g) ((realMobiusActionHom h) z)
  rw [map_mul]
  rfl

/-- A fixed real Mobius representative acts continuously on the upper half-plane. -/
theorem realMobiusRepresentativeAction_continuous
    (g : RealMobiusRepresentative) :
    Continuous (realMobiusRepresentativeAction g) := by
  change Continuous fun z : ℍ => ((g : GL (Fin 2) ℝ) • z)
  exact continuous_const_smul (g : GL (Fin 2) ℝ)

/-- A fixed real Mobius representative acts smoothly on the upper half-plane. -/
theorem realMobiusRepresentativeAction_contMDiff
    (g : RealMobiusRepresentative) {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (realMobiusRepresentativeAction g) := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) n fun z : ℍ => ((g : GL (Fin 2) ℝ) • z)
  exact UpperHalfPlane.contMDiff_smul (g := (g : GL (Fin 2) ℝ)) (by simp)

/-- A fixed real Mobius representative acts holomorphically on the upper half-plane. -/
theorem realMobiusRepresentativeAction_mdifferentiable
    (g : RealMobiusRepresentative) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (realMobiusRepresentativeAction g) :=
  (realMobiusRepresentativeAction_contMDiff (n := (⊤ : WithTop ℕ∞)) g).mdifferentiable
    (by simp)

/-- Pointwise holomorphicity of the representative action. -/
theorem realMobiusRepresentativeAction_mdifferentiableAt
    (g : RealMobiusRepresentative) (z : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (realMobiusRepresentativeAction g) z :=
  (realMobiusRepresentativeAction_mdifferentiable g) z

/-- Ambient complex differentiability of the representative action in the standard `ℍ` chart. -/
theorem realMobiusRepresentativeAction_differentiableAt
    (g : RealMobiusRepresentative) (z : ℍ) :
    DifferentiableAt ℂ
      (fun w : ℂ => ((realMobiusRepresentativeAction g (UpperHalfPlane.ofComplex w) : ℍ) : ℂ))
      (z : ℂ) := by
  change DifferentiableAt ℂ
    (fun w : ℂ => (((g : GL (Fin 2) ℝ) • UpperHalfPlane.ofComplex w : ℍ) : ℂ))
    (z : ℂ)
  exact (UpperHalfPlane.analyticAt_smul (g := (g : GL (Fin 2) ℝ)) (by simp) z).differentiableAt

/-- The derivative of a real Mobius representative action is nonzero in the standard chart. -/
theorem realMobiusRepresentativeAction_standardChart_deriv_ne_zero
    (g : RealMobiusRepresentative) (z : ℍ) :
    deriv
      (fun w : ℂ => ((realMobiusRepresentativeAction g (UpperHalfPlane.ofComplex w) : ℍ) : ℂ))
      (z : ℂ) ≠ 0 := by
  change deriv
    (fun w : ℂ => (((g : GL (Fin 2) ℝ) • UpperHalfPlane.ofComplex w : ℍ) : ℂ))
    (z : ℂ) ≠ 0
  exact UpperHalfPlane.deriv_smul_ne_zero (g := (g : GL (Fin 2) ℝ)) (by simp) z

/--
If an `SL(2, ℝ)` representative fixes three distinct points of the upper
half-plane, then it is central.  Algebraically, a fixed point satisfies the
quadratic equation
`c z^2 + (d - a) z - b = 0`; three distinct roots force `b = c = 0` and
`d = a`, and determinant one gives `a^2 = 1`.
-/
theorem realMobiusRepresentative_mem_center_of_fix_three
    (A : RealMobiusRepresentative) {z₁ z₂ z₃ : ℍ}
    (hz₁₂ : z₁ ≠ z₂) (hz₁₃ : z₁ ≠ z₃) (hz₂₃ : z₂ ≠ z₃)
    (h₁ : realMobiusRepresentativeAction A z₁ = z₁)
    (h₂ : realMobiusRepresentativeAction A z₂ = z₂)
    (h₃ : realMobiusRepresentativeAction A z₃ = z₃) :
    A ∈ Subgroup.center RealMobiusRepresentative := by
  let a : ℝ := A 0 0
  let b : ℝ := A 0 1
  let c : ℝ := A 1 0
  let d : ℝ := A 1 1
  have hquad :
      ∀ z : ℍ, realMobiusRepresentativeAction A z = z →
        (c : ℂ) * (z : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z : ℂ) -
            (b : ℂ) = 0 := by
    intro z hz
    have hcomplex := congrArg (fun q : ℍ => (q : ℂ)) hz
    have hdiv :
        ((a : ℂ) * (z : ℂ) + (b : ℂ)) /
            ((c : ℂ) * (z : ℂ) + (d : ℂ)) = (z : ℂ) := by
      simpa [a, b, c, d, realMobiusRepresentativeAction,
        UpperHalfPlane.coe_specialLinearGroup_apply] using hcomplex
    have hden :
        ((c : ℂ) * (z : ℂ) + (d : ℂ)) ≠ 0 := by
      simpa [c, d, UpperHalfPlane.denom] using
        UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) z
    have hcross :
        (a : ℂ) * (z : ℂ) + (b : ℂ) =
          (z : ℂ) * ((c : ℂ) * (z : ℂ) + (d : ℂ)) := by
      exact (div_eq_iff hden).mp hdiv
    calc
      (c : ℂ) * (z : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z : ℂ) -
          (b : ℂ)
          = (z : ℂ) * ((c : ℂ) * (z : ℂ) + (d : ℂ)) -
              ((a : ℂ) * (z : ℂ) + (b : ℂ)) := by
              rw [Complex.ofReal_sub]
              ring
      _ = 0 := by rw [← hcross, sub_self]
  have hP₁ := hquad z₁ h₁
  have hP₂ := hquad z₂ h₂
  have hP₃ := hquad z₃ h₃
  have hz₁₂c : ((z₁ : ℂ) - (z₂ : ℂ)) ≠ 0 := by
    intro h
    exact hz₁₂ (UpperHalfPlane.ext (sub_eq_zero.mp h))
  have hz₁₃c : ((z₁ : ℂ) - (z₃ : ℂ)) ≠ 0 := by
    intro h
    exact hz₁₃ (UpperHalfPlane.ext (sub_eq_zero.mp h))
  have hz₂₃c : ((z₂ : ℂ) - (z₃ : ℂ)) ≠ 0 := by
    intro h
    exact hz₂₃ (UpperHalfPlane.ext (sub_eq_zero.mp h))
  have hline₁₂ :
      (c : ℂ) * ((z₁ : ℂ) + (z₂ : ℂ)) + ((d - a : ℝ) : ℂ) = 0 := by
    have hdiff :
        ((c : ℂ) * (z₁ : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z₁ : ℂ) -
              (b : ℂ)) -
            ((c : ℂ) * (z₂ : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z₂ : ℂ) -
              (b : ℂ)) = 0 := by
      rw [hP₁, hP₂, sub_self]
    have hfactor :
        ((z₁ : ℂ) - (z₂ : ℂ)) *
            ((c : ℂ) * ((z₁ : ℂ) + (z₂ : ℂ)) + ((d - a : ℝ) : ℂ)) = 0 := by
      calc
        ((z₁ : ℂ) - (z₂ : ℂ)) *
            ((c : ℂ) * ((z₁ : ℂ) + (z₂ : ℂ)) + ((d - a : ℝ) : ℂ))
            =
          ((c : ℂ) * (z₁ : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z₁ : ℂ) -
              (b : ℂ)) -
            ((c : ℂ) * (z₂ : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z₂ : ℂ) -
              (b : ℂ)) := by
              ring
        _ = 0 := hdiff
    exact (mul_eq_zero.mp hfactor).resolve_left hz₁₂c
  have hline₁₃ :
      (c : ℂ) * ((z₁ : ℂ) + (z₃ : ℂ)) + ((d - a : ℝ) : ℂ) = 0 := by
    have hdiff :
        ((c : ℂ) * (z₁ : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z₁ : ℂ) -
              (b : ℂ)) -
            ((c : ℂ) * (z₃ : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z₃ : ℂ) -
              (b : ℂ)) = 0 := by
      rw [hP₁, hP₃, sub_self]
    have hfactor :
        ((z₁ : ℂ) - (z₃ : ℂ)) *
            ((c : ℂ) * ((z₁ : ℂ) + (z₃ : ℂ)) + ((d - a : ℝ) : ℂ)) = 0 := by
      calc
        ((z₁ : ℂ) - (z₃ : ℂ)) *
            ((c : ℂ) * ((z₁ : ℂ) + (z₃ : ℂ)) + ((d - a : ℝ) : ℂ))
            =
          ((c : ℂ) * (z₁ : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z₁ : ℂ) -
              (b : ℂ)) -
            ((c : ℂ) * (z₃ : ℂ) ^ 2 + ((d - a : ℝ) : ℂ) * (z₃ : ℂ) -
              (b : ℂ)) := by
              ring
        _ = 0 := hdiff
    exact (mul_eq_zero.mp hfactor).resolve_left hz₁₃c
  have hcC : (c : ℂ) = 0 := by
    have hdiff :
        ((c : ℂ) * ((z₁ : ℂ) + (z₂ : ℂ)) + ((d - a : ℝ) : ℂ)) -
          ((c : ℂ) * ((z₁ : ℂ) + (z₃ : ℂ)) + ((d - a : ℝ) : ℂ)) = 0 := by
      rw [hline₁₂, hline₁₃, sub_self]
    have hmul : (c : ℂ) * ((z₂ : ℂ) - (z₃ : ℂ)) = 0 := by
      calc
        (c : ℂ) * ((z₂ : ℂ) - (z₃ : ℂ))
            =
          ((c : ℂ) * ((z₁ : ℂ) + (z₂ : ℂ)) + ((d - a : ℝ) : ℂ)) -
            ((c : ℂ) * ((z₁ : ℂ) + (z₃ : ℂ)) + ((d - a : ℝ) : ℂ)) := by
              ring
        _ = 0 := hdiff
    exact (mul_eq_zero.mp hmul).resolve_right hz₂₃c
  have hc : c = 0 := by
    exact_mod_cast hcC
  have hdaC : (((d - a : ℝ) : ℂ)) = 0 := by
    simpa [hcC] using hline₁₂
  have hda : d - a = 0 := by
    exact_mod_cast hdaC
  have hd : d = a := sub_eq_zero.mp hda
  have hbC : (b : ℂ) = 0 := by
    have hneg : -(b : ℂ) = 0 := by
      simpa [hcC, hdaC] using hP₁
    exact neg_eq_zero.mp hneg
  have hb : b = 0 := by
    exact_mod_cast hbC
  have hdet : a * d - b * c = 1 := by
    have hdetMat : Matrix.det (A : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
      Matrix.SpecialLinearGroup.det_coe (A := A)
    simpa [-Matrix.SpecialLinearGroup.det_coe, a, b, c, d,
      Matrix.det_fin_two] using hdetMat
  have ha_sq : a ^ 2 = 1 := by
    simpa [hb, hc, hd, pow_two] using hdet
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨a, ?_, ?_⟩
  · simpa [Fintype.card_fin, pow_two] using ha_sq
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, a, b, c, d, hb, hc, hd]

/-- A PSL element fixing three distinct points of `ℍ` is the identity. -/
theorem realMobiusAction_eq_one_of_fix_three
    (g : RealMobiusGroup) {z₁ z₂ z₃ : ℍ}
    (hz₁₂ : z₁ ≠ z₂) (hz₁₃ : z₁ ≠ z₃) (hz₂₃ : z₂ ≠ z₃)
    (h₁ : realMobiusAction g z₁ = z₁)
    (h₂ : realMobiusAction g z₂ = z₂)
    (h₃ : realMobiusAction g z₃ = z₃) :
    g = 1 := by
  revert h₁ h₂ h₃
  refine QuotientGroup.induction_on g ?_
  intro A h₁ h₂ h₃
  change realMobiusRepresentativeAction A z₁ = z₁ at h₁
  change realMobiusRepresentativeAction A z₂ = z₂ at h₂
  change realMobiusRepresentativeAction A z₃ = z₃ at h₃
  change realMobiusProjection A = 1
  exact (QuotientGroup.eq_one_iff A).mpr
    (realMobiusRepresentative_mem_center_of_fix_three A
      hz₁₂ hz₁₃ hz₂₃ h₁ h₂ h₃)

/-- Three distinct upper-half-plane points determine a PSL action. -/
theorem realMobiusAction_determined_by_three_points
    (g h : RealMobiusGroup) (z₁ z₂ z₃ : ℍ)
    (hz₁₂ : z₁ ≠ z₂) (hz₁₃ : z₁ ≠ z₃) (hz₂₃ : z₂ ≠ z₃)
    (h₁ : realMobiusAction g z₁ = realMobiusAction h z₁)
    (h₂ : realMobiusAction g z₂ = realMobiusAction h z₂)
    (h₃ : realMobiusAction g z₃ = realMobiusAction h z₃) :
    g = h := by
  have hfix₁ : realMobiusAction (h⁻¹ * g) z₁ = z₁ := by
    rw [realMobiusAction_mul, h₁]
    rw [← realMobiusAction_mul, inv_mul_cancel, realMobiusAction_one]
  have hfix₂ : realMobiusAction (h⁻¹ * g) z₂ = z₂ := by
    rw [realMobiusAction_mul, h₂]
    rw [← realMobiusAction_mul, inv_mul_cancel, realMobiusAction_one]
  have hfix₃ : realMobiusAction (h⁻¹ * g) z₃ = z₃ := by
    rw [realMobiusAction_mul, h₃]
    rw [← realMobiusAction_mul, inv_mul_cancel, realMobiusAction_one]
  have hk : h⁻¹ * g = 1 :=
    realMobiusAction_eq_one_of_fix_three (h⁻¹ * g)
      hz₁₂ hz₁₃ hz₂₃ hfix₁ hfix₂ hfix₃
  calc
    g = h * (h⁻¹ * g) := by simp
    _ = h := by rw [hk, mul_one]

end

end JJMath
