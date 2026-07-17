import JJMath.Hyperbolic.Schwarzian.Developing.LocalBranches

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
Local real-transition theorem target for normalized Schwarzian ODE branches.

The analytic content still missing here is the uniqueness theorem for
orientation-preserving local isometries of the Poincare metric: two
metric-recovering `ℍ`-valued normalized branches on a connected overlap differ
by a real Mobius transformation.  This is the local input that makes the
holonomy of the analytically continued Schwarzian developing map land in
`PSL(2, ℝ)` after the chosen Mobius normalization.
-/
def MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂),
      u.SolvesLiouvilleEquation →
        IsPreconnected (H₁.domain ∩ H₂.domain) →
        H₁.HasRealMobiusTransition H₂

/--
Sharper branch-level real-transition uniqueness target.

The genuinely analytic case is the one where the connected overlap is
nonempty.  If the two branch domains are disjoint, the transition predicate is
vacuous and the identity real Mobius representative is enough.
-/
def MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂),
      u.SolvesLiouvilleEquation →
        IsPreconnected (H₁.domain ∩ H₂.domain) →
          Set.Nonempty (H₁.domain ∩ H₂.domain) →
            H₁.HasRealMobiusTransition H₂

/--
Pointed existence target for the real-transition theorem.

At any point of overlap, there should be a real Mobius transformation whose
one-jet carries the first metric-recovering branch to the second.
-/
def MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂) {z₀ : ℂ},
      u.SolvesLiouvilleEquation →
        z₀ ∈ H₁.domain →
          z₀ ∈ H₂.domain →
            ∃ A : RealMobiusRepresentative,
              H₁.HasPointedRealMobiusTransition H₂ A z₀

/--
Pointed real-Mobius one-jet transitivity, phrased in the exact form needed by
metric-recovering branches.

The only hypothesis on the two pointed branches is equality of the squared
hyperbolic norm of their complex derivatives at the base point.  For
metric-recovering branches this equality is formal from the pullback formulas.
-/
def PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂) {z₀ : ℂ},
      z₀ ∈ H₁.domain →
        z₀ ∈ H₂.domain →
          H₁.hyperbolicDerivativeNormSqAt z₀ =
            H₂.hyperbolicDerivativeNormSqAt z₀ →
            ∃ A : RealMobiusRepresentative,
              H₁.HasPointedRealMobiusTransition H₂ A z₀

/--
Value transitivity of real Mobius transformations on the upper half-plane.
-/
def RealMobiusValueTransitivityOnUpperHalfPlaneTheorem : Prop :=
  ∀ p q : ℍ, ∃ A : RealMobiusRepresentative,
    q = realMobiusRepresentativeAction A p

/--
An explicit real Mobius representative sending `i` to a prescribed point of
the upper half-plane.
-/
def realMobiusRepresentativeMapITo (p : ℍ) : RealMobiusRepresentative :=
  ⟨!![Real.sqrt p.im, p.re / Real.sqrt p.im; 0, (Real.sqrt p.im)⁻¹], by
    rw [Matrix.det_fin_two_of]
    have hs : Real.sqrt p.im ≠ 0 := (Real.sqrt_pos_of_pos p.im_pos).ne'
    field_simp [hs]
    ring⟩

/-- The explicit representative `realMobiusRepresentativeMapITo p` sends `i` to `p`. -/
theorem realMobiusRepresentativeMapITo_apply_I (p : ℍ) :
    realMobiusRepresentativeAction (realMobiusRepresentativeMapITo p) UpperHalfPlane.I = p := by
  apply UpperHalfPlane.coe_injective
  rw [realMobiusRepresentativeAction]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rw [← UpperHalfPlane.re_add_im p]
  have hs : Real.sqrt p.im ≠ 0 := (Real.sqrt_pos_of_pos p.im_pos).ne'
  have hs_sq : Real.sqrt p.im ^ 2 ≠ 0 := pow_ne_zero 2 hs
  simp [realMobiusRepresentativeMapITo, UpperHalfPlane.coe_I, Complex.ext_iff,
    Complex.div_re, Complex.div_im]
  constructor
  · field_simp [hs, hs_sq]
  · simpa [sq] using Real.sq_sqrt p.im_pos.le

/-- Real Mobius transformations act transitively on the upper half-plane. -/
theorem realMobiusValueTransitivityOnUpperHalfPlaneTheorem :
    RealMobiusValueTransitivityOnUpperHalfPlaneTheorem := by
  intro p q
  refine ⟨realMobiusRepresentativeMapITo q * (realMobiusRepresentativeMapITo p)⁻¹, ?_⟩
  rw [realMobiusRepresentativeAction_mul]
  have hp := realMobiusRepresentativeMapITo_apply_I p
  have hpinv :
      realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p)⁻¹) p =
        UpperHalfPlane.I := by
    conv_lhs =>
      arg 2
      rw [← hp]
    rw [← realMobiusRepresentativeAction_mul]
    simp
  rw [hpinv]
  exact (realMobiusRepresentativeMapITo_apply_I q).symm

/--
The complex derivative of a real Mobius representative acting on `ℍ`.

This is a thin wrapper around mathlib's `UpperHalfPlane.deriv_smul`, specialized
to determinant-one representatives.
-/
theorem realMobiusRepresentativeAction_deriv
    (A : RealMobiusRepresentative) (p : ℍ) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p =
      (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p ^ 2)⁻¹ := by
  have hdet : (A : GL (Fin 2) ℝ).val.det = 1 := by
    simp
  have hdet_pos : 0 < (A : GL (Fin 2) ℝ).val.det := by
    rw [hdet]
    norm_num
  have hderiv :=
    UpperHalfPlane.deriv_smul (g := (A : GL (Fin 2) ℝ)) hdet_pos p
  have hfun :
      (fun z : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)) =
        (fun z : ℂ ↦
          (((A : GL (Fin 2) ℝ) •
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℍ) : ℂ)) := by
    rfl
  rw [hfun, hderiv, hdet]
  simp

/--
The `HasDerivAt` form of the derivative formula for real Mobius
representatives acting on `ℍ`.
-/
theorem realMobiusRepresentativeAction_hasDerivAt
    (A : RealMobiusRepresentative) (p : ℍ) :
    HasDerivAt
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      ((UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p ^ 2)⁻¹)
      p := by
  have hdet : (A : GL (Fin 2) ℝ).val.det = 1 := by
    simp
  have hdet_pos : 0 < (A : GL (Fin 2) ℝ).val.det := by
    rw [hdet]
    norm_num
  have hstrict :=
    UpperHalfPlane.hasStrictDerivAt_smul (g := (A : GL (Fin 2) ℝ)) hdet_pos p
  have hfun :
      (fun z : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)) =
        (fun z : ℂ ↦
          (((A : GL (Fin 2) ℝ) •
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℍ) : ℂ)) := by
    rfl
  rw [hfun]
  simpa [hdet] using hstrict.hasDerivAt

/-- The derivative of a real Mobius representative acting on `ℍ` is nonzero. -/
theorem realMobiusRepresentativeAction_deriv_ne_zero
    (A : RealMobiusRepresentative) (p : ℍ) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p ≠ 0 := by
  rw [realMobiusRepresentativeAction_deriv]
  exact inv_ne_zero (pow_ne_zero 2 (UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p))

/-- The denominator of a real Mobius transformation has derivative `c`. -/
theorem realMobiusRepresentative_denom_hasDerivAt
    (A : RealMobiusRepresentative) (p : ℍ) :
    HasDerivAt
      (fun z : ℂ ↦ UpperHalfPlane.denom (A : GL (Fin 2) ℝ) z)
      ((A : GL (Fin 2) ℝ) 1 0 : ℂ) p := by
  simpa [UpperHalfPlane.denom] using
    (((hasDerivAt_id (p : ℂ)).const_mul ((A : GL (Fin 2) ℝ) 1 0 : ℂ)).const_add
      ((A : GL (Fin 2) ℝ) 1 1 : ℂ))

/-- The second derivative of a real Mobius representative acting on `ℍ`. -/
theorem realMobiusRepresentativeAction_second_deriv
    (A : RealMobiusRepresentative) (p : ℍ) :
    deriv
      (fun w : ℂ ↦
        deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
          w)
      p =
      -2 * ((A : GL (Fin 2) ℝ) 1 0 : ℂ) /
        (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p) ^ 3 := by
  let δ : ℂ → ℂ := fun z ↦ UpperHalfPlane.denom (A : GL (Fin 2) ℝ) z
  let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
          w) =ᶠ[nhds (p : ℂ)]
        fun w : ℂ ↦ (δ w ^ 2)⁻¹ := by
    have hopen : IsOpen {w : ℂ | 0 < w.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds p.im_pos] with w hw
    have h := realMobiusRepresentativeAction_deriv A (⟨w, hw⟩ : ℍ)
    simpa [δ, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using h
  have hδ : HasDerivAt δ c p := by
    simpa [δ, c] using realMobiusRepresentative_denom_hasDerivAt A p
  have hδ2 : HasDerivAt (fun z : ℂ ↦ δ z ^ 2) (2 * δ p * c) p := by
    simpa [pow_one, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using
      hδ.pow 2
  have hδ_ne : δ p ≠ 0 := by
    simpa [δ] using UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p
  have hδ2_ne : δ p ^ 2 ≠ 0 := pow_ne_zero 2 hδ_ne
  have hinv :
      HasDerivAt (fun z : ℂ ↦ (δ z ^ 2)⁻¹)
        (-2 * c / δ p ^ 3) p := by
    have h := hδ2.inv hδ2_ne
    convert h using 1
    field_simp [hδ2_ne, hδ_ne]
  calc
    deriv
        (fun w : ℂ ↦
          deriv
            (fun z : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
            w)
        p =
        deriv (fun z : ℂ ↦ (δ z ^ 2)⁻¹) p := hEq.deriv_eq
    _ = -2 * ((A : GL (Fin 2) ℝ) 1 0 : ℂ) /
        (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p) ^ 3 := by
      simpa [δ, c] using hinv.deriv

/-- The derivative multiplier of a real Mobius representative is differentiable. -/
theorem realMobiusRepresentativeAction_deriv_hasDerivAt
    (A : RealMobiusRepresentative) (p : ℍ) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
          w)
      (-2 * ((A : GL (Fin 2) ℝ) 1 0 : ℂ) /
        (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p) ^ 3)
      p := by
  let δ : ℂ → ℂ := fun z ↦ UpperHalfPlane.denom (A : GL (Fin 2) ℝ) z
  let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
          w) =ᶠ[nhds (p : ℂ)]
        fun w : ℂ ↦ (δ w ^ 2)⁻¹ := by
    have hopen : IsOpen {w : ℂ | 0 < w.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds p.im_pos] with w hw
    have h := realMobiusRepresentativeAction_deriv A (⟨w, hw⟩ : ℍ)
    simpa [δ, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using h
  have hδ : HasDerivAt δ c p := by
    simpa [δ, c] using realMobiusRepresentative_denom_hasDerivAt A p
  have hδ2 : HasDerivAt (fun z : ℂ ↦ δ z ^ 2) (2 * δ p * c) p := by
    simpa [pow_one, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using
      hδ.pow 2
  have hδ_ne : δ p ≠ 0 := by
    simpa [δ] using UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p
  have hδ2_ne : δ p ^ 2 ≠ 0 := pow_ne_zero 2 hδ_ne
  have hinv :
      HasDerivAt (fun z : ℂ ↦ (δ z ^ 2)⁻¹)
        (-2 * c / δ p ^ 3) p := by
    have h := hδ2.inv hδ2_ne
    convert h using 1
    field_simp [hδ2_ne, hδ_ne]
  exact (hinv.congr_of_eventuallyEq hEq).congr_deriv (by simp [δ, c])

/-- The third derivative of a real Mobius representative acting on `ℍ`. -/
theorem realMobiusRepresentativeAction_third_deriv
    (A : RealMobiusRepresentative) (p : ℍ) :
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun z : ℂ ↦
                (realMobiusRepresentativeAction A
                  ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
              t)
          w)
      p =
      6 * ((A : GL (Fin 2) ℝ) 1 0 : ℂ) ^ 2 /
        (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p) ^ 4 := by
  let δ : ℂ → ℂ := fun z ↦ UpperHalfPlane.denom (A : GL (Fin 2) ℝ) z
  let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun z : ℂ ↦
                (realMobiusRepresentativeAction A
                  ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
              t)
          w) =ᶠ[nhds (p : ℂ)]
        fun w : ℂ ↦ -2 * c / δ w ^ 3 := by
    have hopen : IsOpen {w : ℂ | 0 < w.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds p.im_pos] with w hw
    have h := realMobiusRepresentativeAction_second_deriv A (⟨w, hw⟩ : ℍ)
    simpa [δ, c, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using h
  have hδ : HasDerivAt δ c p := by
    simpa [δ, c] using realMobiusRepresentative_denom_hasDerivAt A p
  have hδ3 : HasDerivAt (fun z : ℂ ↦ δ z ^ 3) (3 * δ p ^ 2 * c) p := by
    simpa [pow_two, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using
      hδ.pow 3
  have hδ_ne : δ p ≠ 0 := by
    simpa [δ] using UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p
  have hδ3_ne : δ p ^ 3 ≠ 0 := pow_ne_zero 3 hδ_ne
  have hinv :
      HasDerivAt (fun z : ℂ ↦ (δ z ^ 3)⁻¹)
        (-(3 * δ p ^ 2 * c) / (δ p ^ 3) ^ 2) p :=
    hδ3.inv hδ3_ne
  have hscaled :
      HasDerivAt (fun z : ℂ ↦ -2 * c / δ z ^ 3)
        (6 * c ^ 2 / δ p ^ 4) p := by
    have h := (hasDerivAt_const (x := (p : ℂ)) (-2 * c)).mul hinv
    convert h using 1
    field_simp [hδ3_ne, hδ_ne]
    ring
  calc
    deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun z : ℂ ↦
                  (realMobiusRepresentativeAction A
                    ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
                t)
            w)
        p =
        deriv (fun z : ℂ ↦ -2 * c / δ z ^ 3) p := hEq.deriv_eq
    _ = 6 * ((A : GL (Fin 2) ℝ) 1 0 : ℂ) ^ 2 /
        (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p) ^ 4 := by
      simpa [δ, c] using hscaled.deriv

/-- The second derivative branch of a real Mobius representative is differentiable. -/
theorem realMobiusRepresentativeAction_second_deriv_hasDerivAt
    (A : RealMobiusRepresentative) (p : ℍ) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun z : ℂ ↦
                (realMobiusRepresentativeAction A
                  ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
              t)
          w)
      (6 * ((A : GL (Fin 2) ℝ) 1 0 : ℂ) ^ 2 /
        (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p) ^ 4)
      p := by
  let δ : ℂ → ℂ := fun z ↦ UpperHalfPlane.denom (A : GL (Fin 2) ℝ) z
  let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun z : ℂ ↦
                (realMobiusRepresentativeAction A
                  ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
              t)
          w) =ᶠ[nhds (p : ℂ)]
        fun w : ℂ ↦ -2 * c / δ w ^ 3 := by
    have hopen : IsOpen {w : ℂ | 0 < w.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds p.im_pos] with w hw
    have h := realMobiusRepresentativeAction_second_deriv A (⟨w, hw⟩ : ℍ)
    simpa [δ, c, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using h
  have hδ : HasDerivAt δ c p := by
    simpa [δ, c] using realMobiusRepresentative_denom_hasDerivAt A p
  have hδ3 : HasDerivAt (fun z : ℂ ↦ δ z ^ 3) (3 * δ p ^ 2 * c) p := by
    simpa [pow_two, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using
      hδ.pow 3
  have hδ_ne : δ p ≠ 0 := by
    simpa [δ] using UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p
  have hδ3_ne : δ p ^ 3 ≠ 0 := pow_ne_zero 3 hδ_ne
  have hinv :
      HasDerivAt (fun z : ℂ ↦ (δ z ^ 3)⁻¹)
        (-(3 * δ p ^ 2 * c) / (δ p ^ 3) ^ 2) p :=
    hδ3.inv hδ3_ne
  have hscaled :
      HasDerivAt (fun z : ℂ ↦ -2 * c / δ z ^ 3)
        (6 * c ^ 2 / δ p ^ 4) p := by
    have h := (hasDerivAt_const (x := (p : ℂ)) (-2 * c)).mul hinv
    convert h using 1
    field_simp [hδ3_ne, hδ_ne]
    ring
  exact (hscaled.congr_of_eventuallyEq hEq).congr_deriv (by simp [δ, c])

/-- The derivative multiplier of a fixed real Mobius map is continuous on `ℍ`. -/
theorem realMobiusRepresentativeAction_deriv_continuous
    (A : RealMobiusRepresentative) :
    Continuous
      (fun p : ℍ ↦
        deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
          p) := by
  have hden :
      Continuous (fun p : ℍ ↦ UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p) := by
    simpa [UpperHalfPlane.denom] using
      (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
  have hfactor :
      Continuous
        (fun p : ℍ ↦ (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p ^ 2)⁻¹) :=
    (hden.pow 2).inv₀
      (fun p ↦ pow_ne_zero 2 (UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p))
  convert hfactor using 1
  funext p
  rw [realMobiusRepresentativeAction_deriv]

/--
Real Mobius representatives preserve the squared hyperbolic norm of tangent
vectors, in derivative-density form.
-/
theorem realMobiusRepresentativeAction_deriv_hyperbolicNormSq
    (A : RealMobiusRepresentative) (p : ℍ) :
    Complex.normSq
        (deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
          p) /
        ((realMobiusRepresentativeAction A p : ℂ).im ^ 2) =
      1 / ((p : ℂ).im ^ 2) := by
  let D : ℝ := Complex.normSq (UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p)
  have hDpos : 0 < D := by
    dsimp [D]
    exact UpperHalfPlane.normSq_denom_pos (A : GL (Fin 2) ℝ) p.im_ne_zero
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hpim : (p : ℂ).im ≠ 0 := p.im_ne_zero
  have him :
      (realMobiusRepresentativeAction A p : ℂ).im = (p : ℂ).im / D := by
    rw [realMobiusRepresentativeAction]
    change (((A : GL (Fin 2) ℝ) • p : ℍ).im) = (p : ℂ).im / D
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    have hdet : |((A : GL (Fin 2) ℝ).det.val)| = 1 := by
      simp
    rw [hdet, one_mul]
    rfl
  rw [realMobiusRepresentativeAction_deriv, him]
  dsimp [D]
  rw [pow_two, Complex.normSq_inv, Complex.normSq_mul]
  field_simp [hDne, hpim]

/--
If two tangent vectors have equal hyperbolic norm and `A` sends the base point
of the first to the base point of the second, then applying the derivative of
`A` to the first vector gives a tangent vector with the same Euclidean norm as
the second.
-/
theorem realMobiusRepresentativeAction_deriv_mul_normSq_eq_of_hyperbolicNormSq
    (A : RealMobiusRepresentative) (p : ℍ) {v w : ℂ}
    (hNorm :
      Complex.normSq v / ((p : ℂ).im ^ 2) =
        Complex.normSq w / ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)) :
    Complex.normSq
        ((deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
          p) * v) =
      Complex.normSq w := by
  have hIso := realMobiusRepresentativeAction_deriv_hyperbolicNormSq A p
  have hp2_pos : 0 < ((p : ℂ).im ^ 2) := sq_pos_of_ne_zero p.im_ne_zero
  have hq2_pos : 0 < ((realMobiusRepresentativeAction A p : ℂ).im ^ 2) :=
    sq_pos_of_ne_zero (realMobiusRepresentativeAction A p).im_ne_zero
  let d : ℂ :=
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p
  let p2 : ℝ := (p : ℂ).im ^ 2
  let q2 : ℝ := (realMobiusRepresentativeAction A p : ℂ).im ^ 2
  have hp2_ne : p2 ≠ 0 := ne_of_gt (by simpa [p2] using hp2_pos)
  have hq2_ne : q2 ≠ 0 := ne_of_gt (by simpa [q2] using hq2_pos)
  have hIso' : Complex.normSq d / q2 = 1 / p2 := by
    simpa [d, p2, q2] using hIso
  have hNorm' : Complex.normSq v / p2 = Complex.normSq w / q2 := by
    simpa [p2, q2] using hNorm
  have hdiv :
      Complex.normSq (d * v) / q2 = Complex.normSq w / q2 := by
    calc
      Complex.normSq (d * v) / q2 =
          Complex.normSq v * (Complex.normSq d / q2) := by
        rw [Complex.normSq_mul]
        ring
      _ = Complex.normSq v / p2 := by
        rw [hIso']
        ring
      _ = Complex.normSq w / q2 := hNorm'
  have hmul := congrArg (fun x : ℝ => x * q2) hdiv
  field_simp [hq2_ne] at hmul
  simpa [d] using hmul

/--
Chain rule for derivatives of products of real Mobius representatives acting
on `ℍ`.
-/
theorem realMobiusRepresentativeAction_hasDerivAt_mul
    (A B : RealMobiusRepresentative) (p : ℍ) :
    HasDerivAt
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (A * B)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      (((UpperHalfPlane.denom (A : GL (Fin 2) ℝ)
            (realMobiusRepresentativeAction B p) ^ 2)⁻¹) *
        ((UpperHalfPlane.denom (B : GL (Fin 2) ℝ) p ^ 2)⁻¹))
      p := by
  let fA : ℂ → ℂ :=
    fun z ↦ (realMobiusRepresentativeAction A
      ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)
  let fB : ℂ → ℂ :=
    fun z ↦ (realMobiusRepresentativeAction B
      ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)
  have hA :
      HasDerivAt fA
        ((UpperHalfPlane.denom (A : GL (Fin 2) ℝ)
            (realMobiusRepresentativeAction B p) ^ 2)⁻¹)
        (fB p) := by
    have hA' :=
      realMobiusRepresentativeAction_hasDerivAt A
        (realMobiusRepresentativeAction B p)
    simpa [fB, UpperHalfPlane.ofComplex_apply] using hA'
  have hB :
      HasDerivAt fB
        ((UpperHalfPlane.denom (B : GL (Fin 2) ℝ) p ^ 2)⁻¹)
        p :=
    realMobiusRepresentativeAction_hasDerivAt B p
  have hcomp := hA.comp (x := (p : ℂ)) hB
  have hfun :
      fA ∘ fB =
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction (A * B)
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)) := by
    funext z
    dsimp [fA, fB, Function.comp_def]
    rw [UpperHalfPlane.ofComplex_apply
      (realMobiusRepresentativeAction B ((UpperHalfPlane.ofComplex : ℂ → ℍ) z))]
    rw [← realMobiusRepresentativeAction_mul]
  rw [← hfun]
  exact hcomp

/-- Chain rule for products of real Mobius representatives, in `deriv` form. -/
theorem realMobiusRepresentativeAction_deriv_mul
    (A B : RealMobiusRepresentative) (p : ℍ) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (A * B)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p =
      deriv
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
        (realMobiusRepresentativeAction B p) *
      deriv
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction B
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
        p := by
  have h := (realMobiusRepresentativeAction_hasDerivAt_mul A B p).deriv
  simpa [realMobiusRepresentativeAction_deriv] using h

/-- The derivative of the identity real Mobius representative is `1`. -/
theorem realMobiusRepresentativeAction_deriv_one (p : ℍ) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (1 : RealMobiusRepresentative)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p =
      1 := by
  rw [realMobiusRepresentativeAction_deriv]
  simp [UpperHalfPlane.denom]

/--
For the explicit map `M_p : i ↦ p`, the derivatives of `M_p` at `i` and
`M_p⁻¹` at `p` multiply to `1`.
-/
theorem realMobiusRepresentativeMapITo_deriv_mul_inv_deriv
    (p : ℍ) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (realMobiusRepresentativeMapITo p)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      UpperHalfPlane.I *
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p)⁻¹)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p =
      1 := by
  have hp_inv :
      realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p)⁻¹) p =
        UpperHalfPlane.I := by
    have hp := realMobiusRepresentativeMapITo_apply_I p
    conv_lhs =>
      arg 2
      rw [← hp]
    rw [← realMobiusRepresentativeAction_mul]
    simp
  have hmul :=
    realMobiusRepresentativeAction_deriv_mul
      (realMobiusRepresentativeMapITo p)
      ((realMobiusRepresentativeMapITo p)⁻¹) p
  rw [hp_inv] at hmul
  have hone :
      (realMobiusRepresentativeMapITo p) * (realMobiusRepresentativeMapITo p)⁻¹ =
        (1 : RealMobiusRepresentative) := by
    simp
  rw [hone, realMobiusRepresentativeAction_deriv_one] at hmul
  exact hmul.symm

/--
Parameters for the rotation subgroup fixing `i`.

The associated matrix is `[[c,s],[-s,c]]`, with determinant `c²+s² = 1`.
-/
structure RealMobiusRotationAtIParameters where
  /-- Cosine-like real coefficient. -/
  c : ℝ
  /-- Sine-like real coefficient. -/
  s : ℝ
  /-- The unit-circle relation. -/
  normSq_eq_one : c ^ 2 + s ^ 2 = 1

namespace RealMobiusRotationAtIParameters

/-- The real Mobius representative `[[c,s],[-s,c]]`. -/
def representative (θ : RealMobiusRotationAtIParameters) : RealMobiusRepresentative :=
  ⟨!![θ.c, θ.s; -θ.s, θ.c], by
    rw [Matrix.det_fin_two_of]
    nlinarith [θ.normSq_eq_one]⟩

/-- The complex denominator of the rotation representative at `i`. -/
def denominatorAtI (θ : RealMobiusRotationAtIParameters) : ℂ :=
  (θ.c : ℂ) - θ.s * Complex.I

/-- The derivative multiplier of the rotation representative at `i`. -/
def derivativeMultiplierAtI (θ : RealMobiusRotationAtIParameters) : ℂ :=
  (θ.denominatorAtI ^ 2)⁻¹

/-- The denominator `c - sI` of a rotation fixing `i` has unit norm square. -/
theorem denominatorAtI_normSq (θ : RealMobiusRotationAtIParameters) :
    Complex.normSq θ.denominatorAtI = 1 := by
  calc
    Complex.normSq θ.denominatorAtI =
        Complex.normSq ((θ.c : ℂ) + (-θ.s) * Complex.I) := by
      rw [denominatorAtI]
      ring_nf
    _ = θ.c ^ 2 + (-θ.s) ^ 2 :=
      by simpa using Complex.normSq_add_mul_I θ.c (-θ.s)
    _ = 1 := by
      nlinarith [θ.normSq_eq_one]

/-- Rotation derivative multipliers at `i` are unit complex scalars. -/
theorem derivativeMultiplierAtI_normSq (θ : RealMobiusRotationAtIParameters) :
    Complex.normSq θ.derivativeMultiplierAtI = 1 := by
  rw [derivativeMultiplierAtI, pow_two, Complex.normSq_inv, Complex.normSq_mul,
    denominatorAtI_normSq]
  norm_num

/-- The Mobius denominator of the rotation representative at `i`. -/
theorem denom_representative_I (θ : RealMobiusRotationAtIParameters) :
    UpperHalfPlane.denom (θ.representative : GL (Fin 2) ℝ) UpperHalfPlane.I =
      θ.denominatorAtI := by
  simp [representative, denominatorAtI, UpperHalfPlane.denom, UpperHalfPlane.coe_I]
  ring

/-- The rotation representative fixes `i`. -/
theorem representative_fixes_I (θ : RealMobiusRotationAtIParameters) :
    realMobiusRepresentativeAction θ.representative UpperHalfPlane.I =
      UpperHalfPlane.I := by
  rw [realMobiusRepresentativeAction]
  apply UpperHalfPlane.ext
  change ((θ.representative • UpperHalfPlane.I : ℍ) : ℂ) = (UpperHalfPlane.I : ℂ)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hden : θ.denominatorAtI ≠ 0 :=
    Complex.normSq_pos.mp (by rw [θ.denominatorAtI_normSq]; norm_num)
  have hden' : (-(θ.s * Complex.I) + θ.c : ℂ) ≠ 0 := by
    simpa [denominatorAtI, sub_eq_add_neg, add_comm, mul_comm] using hden
  simp [representative, UpperHalfPlane.coe_I]
  rw [div_eq_mul_inv]
  have hnum :
      (θ.c : ℂ) * Complex.I + θ.s =
        Complex.I * (-(θ.s * Complex.I) + θ.c) := by
    have hIs : Complex.I * (θ.s * Complex.I) = -(θ.s : ℂ) := by
      calc
        Complex.I * (θ.s * Complex.I) = (θ.s : ℂ) * (Complex.I * Complex.I) := by
          ring
        _ = -(θ.s : ℂ) := by
          rw [Complex.I_mul_I]
          ring
    calc
      (θ.c : ℂ) * Complex.I + θ.s = θ.s + (θ.c : ℂ) * Complex.I := by
        ring
      _ = Complex.I * (-(θ.s * Complex.I)) + Complex.I * θ.c := by
        rw [mul_neg, hIs]
        ring
      _ = Complex.I * (-(θ.s * Complex.I) + θ.c) := by
        ring
  rw [hnum, mul_assoc, mul_inv_cancel₀ hden', mul_one]

/--
The complex derivative of the rotation action at `i` is the stored derivative
multiplier.
-/
theorem derivative_representative_at_I (θ : RealMobiusRotationAtIParameters) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction θ.representative (UpperHalfPlane.ofComplex z) : ℂ))
      UpperHalfPlane.I =
      θ.derivativeMultiplierAtI := by
  have hdet : (θ.representative : GL (Fin 2) ℝ).val.det = 1 := by
    simp
  have hdet_pos : 0 < (θ.representative : GL (Fin 2) ℝ).val.det := by
    rw [hdet]
    norm_num
  have hderiv :=
    UpperHalfPlane.deriv_smul (g := (θ.representative : GL (Fin 2) ℝ))
      hdet_pos UpperHalfPlane.I
  have hfun :
      (fun z : ℂ ↦
          (realMobiusRepresentativeAction θ.representative
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)) =
        (fun z : ℂ ↦
          (((θ.representative : GL (Fin 2) ℝ) •
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℍ) : ℂ)) := by
    rfl
  rw [hfun]
  rw [hderiv, hdet, denom_representative_I]
  simp [derivativeMultiplierAtI]

end RealMobiusRotationAtIParameters

/--
Conjugate a rotation fixing `i` to a real Mobius representative fixing `p`.

The explicit representative `realMobiusRepresentativeMapITo p` sends `i` to
`p`, so this is the usual `M θ M⁻¹` stabilizer element at `p`.
-/
def realMobiusConjugatedRotationAt
    (p : ℍ) (θ : RealMobiusRotationAtIParameters) : RealMobiusRepresentative :=
  realMobiusRepresentativeMapITo p * θ.representative *
    (realMobiusRepresentativeMapITo p)⁻¹

/-- Conjugated rotations fix their target point. -/
theorem realMobiusConjugatedRotationAt_fixes
    (p : ℍ) (θ : RealMobiusRotationAtIParameters) :
    realMobiusRepresentativeAction (realMobiusConjugatedRotationAt p θ) p = p := by
  have hp := realMobiusRepresentativeMapITo_apply_I p
  have hpinv :
      realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p)⁻¹) p =
        UpperHalfPlane.I := by
    conv_lhs =>
      arg 2
      rw [← hp]
    rw [← realMobiusRepresentativeAction_mul]
    simp
  rw [realMobiusConjugatedRotationAt, realMobiusRepresentativeAction_mul,
    realMobiusRepresentativeAction_mul, hpinv,
    RealMobiusRotationAtIParameters.representative_fixes_I, hp]

/--
The derivative of a conjugated rotation factors through the maps
`i → p`, the rotation at `i`, and `p → i`.
-/
theorem realMobiusConjugatedRotationAt_hasDerivAt
    (p : ℍ) (θ : RealMobiusRotationAtIParameters) :
    HasDerivAt
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (realMobiusConjugatedRotationAt p θ)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      (((UpperHalfPlane.denom
            (realMobiusRepresentativeMapITo p : GL (Fin 2) ℝ) UpperHalfPlane.I ^ 2)⁻¹) *
        θ.derivativeMultiplierAtI *
        ((UpperHalfPlane.denom
            ((realMobiusRepresentativeMapITo p)⁻¹ : GL (Fin 2) ℝ) p ^ 2)⁻¹))
      p := by
  let M : RealMobiusRepresentative := realMobiusRepresentativeMapITo p
  let Minv : RealMobiusRepresentative := M⁻¹
  let R : RealMobiusRepresentative := θ.representative
  let fMR : ℂ → ℂ :=
    fun z ↦ (realMobiusRepresentativeAction (M * R)
      ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)
  let fMinv : ℂ → ℂ :=
    fun z ↦ (realMobiusRepresentativeAction Minv
      ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)
  have hMinv_p :
      realMobiusRepresentativeAction Minv p = UpperHalfPlane.I := by
    dsimp [Minv, M]
    have hp := realMobiusRepresentativeMapITo_apply_I p
    conv_lhs =>
      arg 2
      rw [← hp]
    rw [← realMobiusRepresentativeAction_mul]
    simp
  have hMR :
      HasDerivAt fMR
        (((UpperHalfPlane.denom (M : GL (Fin 2) ℝ) UpperHalfPlane.I ^ 2)⁻¹) *
          θ.derivativeMultiplierAtI)
        (fMinv p) := by
    have hMR' := realMobiusRepresentativeAction_hasDerivAt_mul M R UpperHalfPlane.I
    have hRI : realMobiusRepresentativeAction R UpperHalfPlane.I = UpperHalfPlane.I := by
      dsimp [R]
      exact θ.representative_fixes_I
    have hdenR :
        UpperHalfPlane.denom (R : GL (Fin 2) ℝ) UpperHalfPlane.I =
          θ.denominatorAtI := by
      dsimp [R]
      exact θ.denom_representative_I
    have hfMinv : fMinv p = (UpperHalfPlane.I : ℂ) := by
      dsimp [fMinv]
      rw [UpperHalfPlane.ofComplex_apply p, hMinv_p]
      simp [UpperHalfPlane.coe_I]
    rw [hfMinv]
    rw [hRI, hdenR] at hMR'
    simpa [fMR, R, RealMobiusRotationAtIParameters.derivativeMultiplierAtI] using hMR'
  have hMinv :
      HasDerivAt fMinv
        ((UpperHalfPlane.denom (Minv : GL (Fin 2) ℝ) p ^ 2)⁻¹)
        p :=
    realMobiusRepresentativeAction_hasDerivAt Minv p
  have hcomp := hMR.comp (x := (p : ℂ)) hMinv
  have hfun :
      fMR ∘ fMinv =
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction (realMobiusConjugatedRotationAt p θ)
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)) := by
    funext z
    dsimp [fMR, fMinv, realMobiusConjugatedRotationAt, M, Minv, R, Function.comp_def]
    rw [UpperHalfPlane.ofComplex_apply
      (realMobiusRepresentativeAction (realMobiusRepresentativeMapITo p)⁻¹
        ((UpperHalfPlane.ofComplex : ℂ → ℍ) z))]
    rw [← realMobiusRepresentativeAction_mul]
  rw [← hfun]
  simpa [M, Minv, R, mul_assoc] using hcomp

/-- The `deriv` form of the conjugated-rotation derivative factorization. -/
theorem realMobiusConjugatedRotationAt_deriv
    (p : ℍ) (θ : RealMobiusRotationAtIParameters) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (realMobiusConjugatedRotationAt p θ)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p =
      (((UpperHalfPlane.denom
            (realMobiusRepresentativeMapITo p : GL (Fin 2) ℝ) UpperHalfPlane.I ^ 2)⁻¹) *
        θ.derivativeMultiplierAtI *
        ((UpperHalfPlane.denom
            ((realMobiusRepresentativeMapITo p)⁻¹ : GL (Fin 2) ℝ) p ^ 2)⁻¹)) :=
  (realMobiusConjugatedRotationAt_hasDerivAt p θ).deriv

/--
The derivative of a conjugated rotation acts on tangent vectors by moving the
tangent vector to `i`, applying the rotation multiplier there, and moving back.
-/
theorem realMobiusConjugatedRotationAt_deriv_mul
    (p : ℍ) (θ : RealMobiusRotationAtIParameters) (v : ℂ) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (realMobiusConjugatedRotationAt p θ)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p * v =
      deriv
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction (realMobiusRepresentativeMapITo p)
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
        UpperHalfPlane.I *
        (θ.derivativeMultiplierAtI *
          (deriv
            (fun z : ℂ ↦
              (realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p)⁻¹)
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
            p * v)) := by
  rw [realMobiusConjugatedRotationAt_deriv]
  rw [realMobiusRepresentativeAction_deriv, realMobiusRepresentativeAction_deriv]
  rw [map_inv]
  ring_nf

/--
If the transported tangent vectors at `i` differ by the rotation multiplier,
then the conjugated rotation sends the original tangent vector to the target
tangent vector at `p`.
-/
theorem realMobiusConjugatedRotationAt_deriv_mul_eq_of_transported
    (p : ℍ) (θ : RealMobiusRotationAtIParameters) (v w : ℂ)
    (hθ :
      deriv
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p)⁻¹)
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
        p * w =
        θ.derivativeMultiplierAtI *
          (deriv
            (fun z : ℂ ↦
              (realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p)⁻¹)
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
            p * v)) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (realMobiusConjugatedRotationAt p θ)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p * v =
      w := by
  let dM : ℂ :=
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (realMobiusRepresentativeMapITo p)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      UpperHalfPlane.I
  let dMinv : ℂ :=
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p)⁻¹)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p
  have hcancel : dM * dMinv = 1 := by
    dsimp [dM, dMinv]
    exact realMobiusRepresentativeMapITo_deriv_mul_inv_deriv p
  calc
    deriv
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction (realMobiusConjugatedRotationAt p θ)
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
        p * v =
        dM * (θ.derivativeMultiplierAtI * (dMinv * v)) := by
          dsimp [dM, dMinv]
          exact realMobiusConjugatedRotationAt_deriv_mul p θ v
    _ = dM * (dMinv * w) := by
          rw [← hθ]
    _ = (dM * dMinv) * w := by ring
    _ = w := by rw [hcancel]; ring

/-- Product derivative rewritten using a named value of the intermediate point. -/
theorem realMobiusRepresentativeAction_deriv_mul_of_action_eq
    (R A : RealMobiusRepresentative) (p q : ℍ)
    (hA : q = realMobiusRepresentativeAction A p) :
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction (R * A)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p =
      deriv
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction R
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
        q *
      deriv
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
        p := by
  simpa [hA] using realMobiusRepresentativeAction_deriv_mul R A p

/--
Rotation-parameter transitivity for tangent directions at `i`.

This is the remaining scalar algebra behind stabilizer tangent transitivity:
given two nonzero tangent vectors of equal Euclidean norm, a rotation fixing
`i` should carry the first derivative to the second.
-/
def RealMobiusRotationAtITangentTransitivityTheorem : Prop :=
  ∀ v w : ℂ,
    v ≠ 0 →
      Complex.normSq v = Complex.normSq w →
        ∃ θ : RealMobiusRotationAtIParameters,
          w = θ.derivativeMultiplierAtI * v

/--
Unit complex scalars are realized by derivative multipliers of rotations
fixing `i`.

This is the remaining elementary unit-circle calculation behind tangent
transitivity at `i`: write a unit complex number as the inverse square of
`c - sI`, with `c² + s² = 1`.
-/
def UnitComplexRotationMultiplierTheorem : Prop :=
  ∀ mu : ℂ,
    Complex.normSq mu = 1 →
      ∃ θ : RealMobiusRotationAtIParameters,
        mu = θ.derivativeMultiplierAtI

/--
Half-angle formula for rotation derivative multipliers at `i`.

This is the trigonometric core of the unit-scalar statement: for every real
angle `t`, the complex number `exp (tI)` is the derivative multiplier of a
rotation fixing `i`.
-/
def RealMobiusRotationHalfAngleMultiplierFormulaTheorem : Prop :=
  ∀ t : ℝ,
    ∃ θ : RealMobiusRotationAtIParameters,
      θ.derivativeMultiplierAtI = Complex.exp (t * Complex.I)

/-- The half-angle formula for rotation derivative multipliers at `i`. -/
theorem realMobiusRotationHalfAngleMultiplierFormulaTheorem :
    RealMobiusRotationHalfAngleMultiplierFormulaTheorem := by
  intro t
  let θ : RealMobiusRotationAtIParameters :=
    { c := Real.cos (t / 2)
      s := Real.sin (t / 2)
      normSq_eq_one := by
        simp [Real.cos_sq_add_sin_sq] }
  refine ⟨θ, ?_⟩
  have hden :
      θ.denominatorAtI = Complex.exp (-(t / 2) * Complex.I) := by
    rw [RealMobiusRotationAtIParameters.denominatorAtI]
    dsimp [θ]
    rw [Complex.exp_mul_I]
    simp
    ring
  calc
    θ.derivativeMultiplierAtI =
        (Complex.exp (-(t / 2) * Complex.I) ^ 2)⁻¹ := by
      rw [RealMobiusRotationAtIParameters.derivativeMultiplierAtI, hden]
    _ = Complex.exp (t * Complex.I) := by
      rw [pow_two, ← Complex.exp_add, ← Complex.exp_neg]
      congr 1
      ring

/--
The half-angle multiplier formula implies that every unit complex scalar is a
rotation derivative multiplier.

Here the nontrivial parametrization of the unit circle by `exp (tI)` is
provided by mathlib; only the real half-angle formula remains.
-/
theorem unitComplexRotationMultiplierTheorem_of_halfAngleFormula
    (hHalf : RealMobiusRotationHalfAngleMultiplierFormulaTheorem) :
    UnitComplexRotationMultiplierTheorem := by
  intro mu hmu
  have hnorm_sq : ‖mu‖ ^ 2 = 1 := by
    rwa [← Complex.normSq_eq_norm_sq]
  have hnorm : ‖mu‖ = 1 := by
    nlinarith [norm_nonneg mu, hnorm_sq]
  rcases (Complex.norm_eq_one_iff mu).mp hnorm with ⟨t, ht⟩
  rcases hHalf t with ⟨θ, hθ⟩
  refine ⟨θ, ?_⟩
  rw [← ht, ← hθ]

/-- Every unit complex scalar is a rotation derivative multiplier at `i`. -/
theorem unitComplexRotationMultiplierTheorem :
    UnitComplexRotationMultiplierTheorem :=
  unitComplexRotationMultiplierTheorem_of_halfAngleFormula
    realMobiusRotationHalfAngleMultiplierFormulaTheorem

/--
The unit-scalar rotation multiplier statement implies tangent transitivity at
`i`.

The proof is now just norm algebra: for nonzero `v`, the scalar `w / v` has
unit norm square exactly when `v` and `w` have equal norm square.
-/
theorem realMobiusRotationAtITangentTransitivityTheorem_of_unitMultiplier
    (hUnit : UnitComplexRotationMultiplierTheorem) :
    RealMobiusRotationAtITangentTransitivityTheorem := by
  intro v w hv hnorm
  let mu : ℂ := w / v
  have hvnorm : Complex.normSq v ≠ 0 :=
    (Complex.normSq_pos.mpr hv).ne'
  have hmunorm : Complex.normSq mu = 1 := by
    rw [show mu = w / v from rfl, Complex.normSq_div, ← hnorm,
      div_self hvnorm]
  have hUnit' :
      ∀ mu : ℂ,
        Complex.normSq mu = 1 →
          ∃ θ : RealMobiusRotationAtIParameters,
            mu = θ.derivativeMultiplierAtI := hUnit
  rcases hUnit' mu hmunorm with ⟨θ, hθ⟩
  refine ⟨θ, ?_⟩
  rw [← hθ]
  change w = (w / v) * v
  rw [div_mul_cancel₀ w hv]

/-- Rotation derivative multipliers act transitively on tangent directions at `i`. -/
theorem realMobiusRotationAtITangentTransitivityTheorem :
    RealMobiusRotationAtITangentTransitivityTheorem :=
  realMobiusRotationAtITangentTransitivityTheorem_of_unitMultiplier
    unitComplexRotationMultiplierTheorem

/--
Stabilizer transitivity on pointed tangent directions, in the form needed
after the value of one branch has already been matched by a real Mobius map.

Given a real Mobius representative `A` sending the first branch value to the
second at `z₀`, equal hyperbolic derivative norm squares should allow a
stabilizer element `R` of the target point to rotate the tangent direction so
that `R * A` matches the complex derivative one-jet.
-/
def RealMobiusStabilizerAdjustsPointedDerivativeTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) {z₀ : ℂ},
      z₀ ∈ H₁.domain →
        z₀ ∈ H₂.domain →
          H₂.upperHalfPlaneMap z₀ =
            realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z₀) →
          H₁.hyperbolicDerivativeNormSqAt z₀ =
            H₂.hyperbolicDerivativeNormSqAt z₀ →
            ∃ R : RealMobiusRepresentative,
              realMobiusRepresentativeAction R (H₂.upperHalfPlaneMap z₀) =
                H₂.upperHalfPlaneMap z₀ ∧
              deriv (fun z : ℂ ↦ (H₂.upperHalfPlaneMap z : ℂ)) z₀ =
                deriv
                  (fun z : ℂ ↦
                    (realMobiusRepresentativeAction (R * A) (H₁.upperHalfPlaneMap z) : ℂ))
                  z₀

/--
Reduction target from rotations at `i` to stabilizer tangent transitivity at
an arbitrary point of `ℍ`.

Conjugating rotations at `i` by the explicit maps `i ↦ p` should give all
stabilizer rotations at `p`, with the chain rule transporting the derivative
matching statement.
-/
def RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem : Prop :=
  RealMobiusRotationAtITangentTransitivityTheorem →
    RealMobiusStabilizerAdjustsPointedDerivativeTheorem

/--
Branch-level chain rule for postcomposition by a real Mobius map.

This is the remaining analytic differentiability bridge for the stabilizer
uniqueness proof: once the upper-half-plane branch is known to be differentiable
in the strong `HasDerivAt` sense, this should follow from mathlib's chain rule.
-/
def RealMobiusBranchPostcompositionDerivativeChainRuleTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) {z₀ : ℂ},
      z₀ ∈ H.domain →
        deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℂ))
          z₀ =
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H.upperHalfPlaneMap z₀) *
          deriv (fun z : ℂ ↦ (H.upperHalfPlaneMap z : ℂ)) z₀

/--
The branch postcomposition chain rule follows from the nonzero derivative
stored by a metric-recovering upper-half-plane branch and mathlib's chain rule.
-/
theorem realMobiusBranchPostcompositionDerivativeChainRuleTheorem :
    RealMobiusBranchPostcompositionDerivativeChainRuleTheorem := by
  intro u S H A z₀ hz
  let f : ℂ → ℂ := fun z ↦ (H.upperHalfPlaneMap z : ℂ)
  have hf_deriv_ne : deriv f z₀ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, f] at hpos
    exact Complex.normSq_pos.mp hpos
  have hf : HasDerivAt f (deriv f z₀) z₀ :=
    (differentiableAt_of_deriv_ne_zero hf_deriv_ne).hasDerivAt
  have hA :
      HasDerivAt
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        (deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
          (H.upperHalfPlaneMap z₀))
        (H.upperHalfPlaneMap z₀) :=
    (differentiableAt_of_deriv_ne_zero
      (realMobiusRepresentativeAction_deriv_ne_zero A (H.upperHalfPlaneMap z₀))).hasDerivAt
  have hcomp := hA.comp z₀ hf
  have hfun :
      ((fun w : ℂ ↦
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)) ∘ f) =
        (fun z : ℂ ↦
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℂ)) := by
    funext z
    dsimp [f, Function.comp_def]
    rw [UpperHalfPlane.ofComplex_apply (H.upperHalfPlaneMap z)]
  rw [hfun] at hcomp
  simpa [f] using hcomp.deriv

/--
The only remaining analytic input needed to transport rotation transitivity at
`i` to stabilizer tangent transitivity is the branch postcomposition chain rule.
-/
theorem realMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem_of_branchChainRule
    (hChain : RealMobiusBranchPostcompositionDerivativeChainRuleTheorem) :
    RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem := by
  intro hRot u S₁ S₂ H₁ H₂ A z₀ hz₁ hz₂ hA hNorm
  let p₁ : ℍ := H₁.upperHalfPlaneMap z₀
  let p₂ : ℍ := H₂.upperHalfPlaneMap z₀
  let d₁ : ℂ := deriv (fun z : ℂ ↦ (H₁.upperHalfPlaneMap z : ℂ)) z₀
  let d₂ : ℂ := deriv (fun z : ℂ ↦ (H₂.upperHalfPlaneMap z : ℂ)) z₀
  let dA : ℂ :=
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p₁
  let dMinv : ℂ :=
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo p₂)⁻¹)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      p₂
  have hd₁_ne : d₁ ≠ 0 := by
    have hpos := H₁.upperHalfPlaneDerivativeNormSq_pos hz₁
    dsimp [complexDerivativeNormSq, d₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hdA_ne : dA ≠ 0 := by
    dsimp [dA, p₁]
    exact realMobiusRepresentativeAction_deriv_ne_zero A (H₁.upperHalfPlaneMap z₀)
  have hdMinv_ne : dMinv ≠ 0 := by
    dsimp [dMinv, p₂]
    exact realMobiusRepresentativeAction_deriv_ne_zero
      ((realMobiusRepresentativeMapITo (H₂.upperHalfPlaneMap z₀))⁻¹)
      (H₂.upperHalfPlaneMap z₀)
  have hNormA :
      Complex.normSq d₁ / ((p₁ : ℂ).im ^ 2) =
        Complex.normSq d₂ /
          ((realMobiusRepresentativeAction A p₁ : ℂ).im ^ 2) := by
    have hNorm' := hNorm
    rw [LocalUpperHalfPlaneDevelopingMap.hyperbolicDerivativeNormSqAt,
      LocalUpperHalfPlaneDevelopingMap.hyperbolicDerivativeNormSqAt,
      complexDerivativeNormSq, complexDerivativeNormSq] at hNorm'
    rw [hA] at hNorm'
    simpa [p₁, p₂, d₁, d₂] using hNorm'
  have hNorm_dA :
      Complex.normSq (dA * d₁) = Complex.normSq d₂ := by
    exact
      realMobiusRepresentativeAction_deriv_mul_normSq_eq_of_hyperbolicNormSq
        A p₁ (v := d₁) (w := d₂) hNormA
  let x : ℂ := dMinv * (dA * d₁)
  let y : ℂ := dMinv * d₂
  have hx_ne : x ≠ 0 := by
    dsimp [x]
    exact mul_ne_zero hdMinv_ne (mul_ne_zero hdA_ne hd₁_ne)
  have hxy_norm : Complex.normSq x = Complex.normSq y := by
    calc
      Complex.normSq x =
          Complex.normSq dMinv * Complex.normSq (dA * d₁) := by
            dsimp [x]
            rw [Complex.normSq_mul]
      _ = Complex.normSq dMinv * Complex.normSq d₂ := by rw [hNorm_dA]
      _ = Complex.normSq y := by
            dsimp [y]
            rw [Complex.normSq_mul]
  rcases hRot x y hx_ne hxy_norm with ⟨θ, hθ⟩
  let R : RealMobiusRepresentative := realMobiusConjugatedRotationAt p₂ θ
  refine ⟨R, ?_, ?_⟩
  · dsimp [R, p₂]
    exact realMobiusConjugatedRotationAt_fixes (H₂.upperHalfPlaneMap z₀) θ
  · have hRAderiv :
        deriv
          (fun z : ℂ ↦
            (realMobiusRepresentativeAction (R * A)
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
          p₁ * d₁ =
          d₂ := by
      have hprod :=
        realMobiusRepresentativeAction_deriv_mul_of_action_eq R A p₁ p₂ hA
      have hRmul :
          deriv
            (fun z : ℂ ↦
              (realMobiusRepresentativeAction R
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
            p₂ * (dA * d₁) =
            d₂ := by
        dsimp [R]
        exact
          realMobiusConjugatedRotationAt_deriv_mul_eq_of_transported
            p₂ θ (dA * d₁) d₂ (by simpa [x, y] using hθ)
      calc
        deriv
            (fun z : ℂ ↦
              (realMobiusRepresentativeAction (R * A)
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
            p₁ * d₁ =
            (deriv
              (fun z : ℂ ↦
                (realMobiusRepresentativeAction R
                  ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
              p₂ *
              dA) * d₁ := by rw [hprod]
        _ =
            deriv
              (fun z : ℂ ↦
                (realMobiusRepresentativeAction R
                  ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
              p₂ * (dA * d₁) := by ring
        _ = d₂ := hRmul
    have hbranch := hChain H₁ (R * A) hz₁
    calc
      deriv (fun z : ℂ ↦ (H₂.upperHalfPlaneMap z : ℂ)) z₀ = d₂ := rfl
      _ =
          deriv
            (fun z : ℂ ↦
              (realMobiusRepresentativeAction (R * A)
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
            p₁ * d₁ := hRAderiv.symm
      _ =
          deriv
            (fun z : ℂ ↦
              (realMobiusRepresentativeAction (R * A) (H₁.upperHalfPlaneMap z) : ℂ))
            z₀ := by
          exact hbranch.symm

/-- Rotation transitivity at `i` transports to arbitrary stabilizers. -/
theorem realMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem :
    RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem :=
  realMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem_of_branchChainRule
    realMobiusBranchPostcompositionDerivativeChainRuleTheorem

/-- Real Mobius stabilizers match pointed tangent directions of equal hyperbolic norm. -/
theorem realMobiusStabilizerAdjustsPointedDerivativeTheorem :
    RealMobiusStabilizerAdjustsPointedDerivativeTheorem :=
  realMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem
    realMobiusRotationAtITangentTransitivityTheorem

/--
Value transitivity plus stabilizer transitivity give pointed real-Mobius
one-jet transitivity for equal hyperbolic derivative norm.
-/
theorem pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_value_stabilizer
    (hValue : RealMobiusValueTransitivityOnUpperHalfPlaneTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem) :
    PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem := by
  intro u S₁ S₂ H₁ H₂ z₀ hz₁ hz₂ hNorm
  rcases hValue (H₁.upperHalfPlaneMap z₀) (H₂.upperHalfPlaneMap z₀) with
    ⟨A, hA⟩
  rcases hStabilizer H₁ H₂ A hz₁ hz₂ hA hNorm with ⟨R, hRfix, hRderiv⟩
  refine ⟨R * A, ?_⟩
  refine ⟨hz₁, hz₂, ?_, hRderiv⟩
  rw [realMobiusRepresentativeAction_mul, ← hA]
  exact hRfix.symm

/--
Since value transitivity on `ℍ` is explicit, stabilizer tangent transitivity
alone gives pointed real-Mobius one-jet transitivity.
-/
theorem pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_stabilizer
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem) :
    PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem :=
  pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_value_stabilizer
    realMobiusValueTransitivityOnUpperHalfPlaneTheorem hStabilizer

/--
Rotation tangent transitivity at `i`, together with the conjugation transport
to arbitrary stabilizers, gives pointed real-Mobius one-jet transitivity.
-/
theorem pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_rotations
    (hRot : RealMobiusRotationAtITangentTransitivityTheorem)
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem) :
    PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem :=
  pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_stabilizer
    (hTransport hRot)

/--
The unit-complex rotation multiplier theorem, plus transport to arbitrary
stabilizers, gives pointed real-Mobius one-jet transitivity.
-/
theorem pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_unitMultiplier
    (hUnit : UnitComplexRotationMultiplierTheorem)
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem) :
    PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem :=
  pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_rotations
    (realMobiusRotationAtITangentTransitivityTheorem_of_unitMultiplier hUnit)
    hTransport

/--
Since rotation tangent transitivity at `i` is proved, conjugation transport to
arbitrary stabilizers gives pointed real-Mobius one-jet transitivity.
-/
theorem pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_rotationTransport
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem) :
    PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem :=
  pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_rotations
    realMobiusRotationAtITangentTransitivityTheorem hTransport

/--
The branch postcomposition chain rule is now the only remaining input for
pointed real-Mobius one-jet transitivity.
-/
theorem pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_branchChainRule
    (hChain : RealMobiusBranchPostcompositionDerivativeChainRuleTheorem) :
    PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem :=
  pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_rotationTransport
    (realMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem_of_branchChainRule
      hChain)

/-- Pointed real-Mobius one-jet transitivity for equal hyperbolic derivative norm. -/
theorem pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem :
    PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem :=
  pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_branchChainRule
    realMobiusBranchPostcompositionDerivativeChainRuleTheorem

/--
The equal-hyperbolic-derivative-norm one-jet transitivity theorem gives
pointed real-Mobius transitions for metric-recovering branches.
-/
theorem metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_hyperbolicDerivativeNorm
    (h :
      PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem := by
  intro u S₁ S₂ H₁ H₂ z₀ _hu hz₁ hz₂
  exact h H₁ H₂ hz₁ hz₂
    (H₁.hyperbolicDerivativeNormSqAt_eq_of_mem_inter H₂ hz₁ hz₂)

/--
Value transitivity plus stabilizer tangent transitivity give pointed
real-Mobius transitions for metric-recovering branches.
-/
theorem metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_value_stabilizer
    (hValue : RealMobiusValueTransitivityOnUpperHalfPlaneTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :=
  metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_hyperbolicDerivativeNorm
    (pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_value_stabilizer
      hValue hStabilizer)

/--
The proved value transitivity theorem reduces pointed transitions for
metric-recovering branches to stabilizer tangent transitivity.
-/
theorem metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_stabilizer
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :=
  metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_value_stabilizer
    realMobiusValueTransitivityOnUpperHalfPlaneTheorem hStabilizer

/--
Rotation tangent transitivity at `i`, plus transport to arbitrary stabilizers,
gives pointed transitions for metric-recovering branches.
-/
theorem metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_rotations
    (hRot : RealMobiusRotationAtITangentTransitivityTheorem)
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :=
  metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_stabilizer
    (hTransport hRot)

/--
The unit-complex rotation multiplier theorem, plus transport to arbitrary
stabilizers, gives pointed transitions for metric-recovering branches.
-/
theorem metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_unitMultiplier
    (hUnit : UnitComplexRotationMultiplierTheorem)
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :=
  metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_rotations
    (realMobiusRotationAtITangentTransitivityTheorem_of_unitMultiplier hUnit)
    hTransport

/--
Since rotation tangent transitivity at `i` is proved, stabilizer transport gives
pointed transitions for metric-recovering branches.
-/
theorem metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_rotationTransport
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :=
  metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_rotations
    realMobiusRotationAtITangentTransitivityTheorem hTransport

/--
For metric-recovering branches, the branch postcomposition chain rule is the
only remaining local input for pointed real-Mobius transitions.
-/
theorem metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_branchChainRule
    (hChain : RealMobiusBranchPostcompositionDerivativeChainRuleTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :=
  metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_hyperbolicDerivativeNorm
    (pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem_of_branchChainRule
      hChain)

/--
%%handwave
name:
  Pointed real Möbius matching
statement:
  Let $F_1,F_2$ be local maps to $\mathbb H$ which pull back the Poincaré
  metric to the same conformal metric. At every point $z_0$ in their common
  domain there is an element $A\in\mathrm{PSL}_2(\mathbb R)$ such that
  $$F_2(z_0)=A(F_1(z_0)),\qquad
    F_2'(z_0)=(A\circ F_1)'(z_0).$$
proof:
  [Equality of the recovered hyperbolic derivative norms gives a real Möbius transformation matching the two one-jets](lean:JJMath.metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_hyperbolicDerivativeNorm). Apply this to the two metric-recovering branches.
-/
theorem metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :
    MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem :=
  metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_hyperbolicDerivativeNorm
    pointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem

end

end JJMath
