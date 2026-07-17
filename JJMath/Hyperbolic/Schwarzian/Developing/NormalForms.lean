import JJMath.Hyperbolic.Schwarzian.Developing.Uniqueness

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
A nondegenerate finite two-jet of a holomorphic local coordinate.

The value is finite, the first derivative is nonzero, and the second
derivative is recorded explicitly.  This is the natural datum on which a
Mobius postcomposition acts simply transitively.
-/
structure NondegenerateFiniteTwoJet where
  /-- The finite value of the local coordinate. -/
  value : ℂ
  /-- The first derivative, assumed nonzero. -/
  firstDeriv : ℂ
  /-- The second derivative. -/
  secondDeriv : ℂ
  /-- Nondegeneracy of the local coordinate. -/
  firstDeriv_ne_zero : firstDeriv ≠ 0

namespace NondegenerateFiniteTwoJet

/-- The first derivative that the postcomposing Mobius map must have at the source value. -/
def postcompositionFirstDeriv
    (source target : NondegenerateFiniteTwoJet) : ℂ :=
  target.firstDeriv / source.firstDeriv

/-- The second derivative that the postcomposing Mobius map must have at the source value. -/
def postcompositionSecondDeriv
    (source target : NondegenerateFiniteTwoJet) : ℂ :=
  (target.secondDeriv - source.postcompositionFirstDeriv target * source.secondDeriv) /
    source.firstDeriv ^ 2

/--
The explicit normal-form parameter for the Mobius map
`w ↦ target.value + B (w - source.value) / (1 + κ (w - source.value))`.

Here `B = target.firstDeriv / source.firstDeriv` and
`κ = -C / (2B)`, where `C` is the required second derivative of the
postcomposing Mobius map at `source.value`.
-/
def postcompositionDenominatorParameter
    (source target : NondegenerateFiniteTwoJet) : ℂ :=
  - source.postcompositionSecondDeriv target /
    (2 * source.postcompositionFirstDeriv target)

/--
The explicit finite Mobius normal form matching the source value to the
target value and using the prescribed first- and second-derivative
parameters.

It is written as

`w ↦ p + B (w-a)/(1 + κ(w-a))`,

where `a` is the source value, `p` is the target value,
`B = target.firstDeriv / source.firstDeriv`, and `κ` is the denominator
parameter above.
-/
def postcompositionNormalForm
    (source target : NondegenerateFiniteTwoJet) : ℂ → ℂ :=
  fun w =>
    target.value +
      source.postcompositionFirstDeriv target * (w - source.value) /
        (1 + source.postcompositionDenominatorParameter target * (w - source.value))

/--
The explicit first derivative of the normal-form postcomposition away from its
pole.
-/
def postcompositionNormalFormDeriv
    (source target : NondegenerateFiniteTwoJet) : ℂ → ℂ :=
  fun w =>
    source.postcompositionFirstDeriv target /
      (1 + source.postcompositionDenominatorParameter target *
        (w - source.value)) ^ 2

/--
The explicit second derivative of the normal-form postcomposition away from
its pole.
-/
def postcompositionNormalFormSecondDeriv
    (source target : NondegenerateFiniteTwoJet) : ℂ → ℂ :=
  fun w =>
    (-2 * source.postcompositionFirstDeriv target *
      source.postcompositionDenominatorParameter target) /
        (1 + source.postcompositionDenominatorParameter target *
          (w - source.value)) ^ 3

/--
The explicit third derivative of the normal-form postcomposition away from
its pole.
-/
def postcompositionNormalFormThirdDeriv
    (source target : NondegenerateFiniteTwoJet) : ℂ → ℂ :=
  fun w =>
    (6 * source.postcompositionFirstDeriv target *
      source.postcompositionDenominatorParameter target ^ 2) /
        (1 + source.postcompositionDenominatorParameter target *
          (w - source.value)) ^ 4

/--
The `2 × 2` matrix representing the normal-form Mobius map
`w ↦ p + B(w-a)/(1+κ(w-a))`.

In affine coordinates it is
`[(pκ+B), p-(pκ+B)a; κ, 1-κa]`.
-/
def postcompositionNormalFormMatrix
    (source target : NondegenerateFiniteTwoJet) : Matrix (Fin 2) (Fin 2) ℂ :=
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  let p := target.value
  !![p * κ + B, p - (p * κ + B) * a;
     κ, 1 - κ * a]

/-- The required first derivative of the postcomposition is nonzero. -/
theorem postcompositionFirstDeriv_ne_zero
    (source target : NondegenerateFiniteTwoJet) :
    source.postcompositionFirstDeriv target ≠ 0 := by
  rw [postcompositionFirstDeriv]
  exact div_ne_zero target.firstDeriv_ne_zero source.firstDeriv_ne_zero

/-- The chosen first derivative reconstructs the target first derivative. -/
theorem postcompositionFirstDeriv_mul_source
    (source target : NondegenerateFiniteTwoJet) :
    source.postcompositionFirstDeriv target * source.firstDeriv =
      target.firstDeriv := by
  rw [postcompositionFirstDeriv]
  field_simp [source.firstDeriv_ne_zero]

/--
The required second derivative of the postcomposition is exactly the value
which makes the second-order chain rule recover the target two-jet.
-/
theorem postcompositionSecondDeriv_chain_rule
    (source target : NondegenerateFiniteTwoJet) :
    source.postcompositionFirstDeriv target * source.secondDeriv +
      source.postcompositionSecondDeriv target * source.firstDeriv ^ 2 =
        target.secondDeriv := by
  rw [postcompositionSecondDeriv]
  field_simp [source.firstDeriv_ne_zero]
  ring

/--
The normal-form denominator parameter has the prescribed second derivative:
for `w ↦ p + B (w-a)/(1+κ(w-a))`, the second derivative at `a` is `-2Bκ`.
-/
theorem postcompositionDenominatorParameter_spec
    (source target : NondegenerateFiniteTwoJet) :
    -2 * source.postcompositionFirstDeriv target *
        source.postcompositionDenominatorParameter target =
      source.postcompositionSecondDeriv target := by
  rw [postcompositionDenominatorParameter]
  have hB : source.postcompositionFirstDeriv target ≠ 0 :=
    source.postcompositionFirstDeriv_ne_zero target
  field_simp [hB]

/-- The normal-form postcomposition sends the source value to the target value. -/
theorem postcompositionNormalForm_apply_source
    (source target : NondegenerateFiniteTwoJet) :
    source.postcompositionNormalForm target source.value = target.value := by
  simp [postcompositionNormalForm]

/--
The explicit first-derivative function of the normal form has value `B` at the
source value.
-/
theorem postcompositionNormalFormDeriv_apply_source
    (source target : NondegenerateFiniteTwoJet) :
    source.postcompositionNormalFormDeriv target source.value =
      source.postcompositionFirstDeriv target := by
  simp [postcompositionNormalFormDeriv]

/--
The explicit second-derivative function of the normal form has the prescribed
value at the source point.
-/
theorem postcompositionNormalFormSecondDeriv_apply_source
    (source target : NondegenerateFiniteTwoJet) :
    source.postcompositionNormalFormSecondDeriv target source.value =
      source.postcompositionSecondDeriv target := by
  simpa [postcompositionNormalFormSecondDeriv] using
    source.postcompositionDenominatorParameter_spec target

/-- The normal-form denominator is nonzero at the source value. -/
theorem postcompositionNormalForm_denominator_source_ne_zero
    (source target : NondegenerateFiniteTwoJet) :
    1 + source.postcompositionDenominatorParameter target *
        (source.value - source.value) ≠ 0 := by
  simp

/-- The normal-form denominator has the expected derivative at the source value. -/
theorem postcompositionNormalForm_denominator_hasDerivAt_source
    (source target : NondegenerateFiniteTwoJet) :
    HasDerivAt
      (fun w : ℂ =>
        1 + source.postcompositionDenominatorParameter target *
          (w - source.value))
      (source.postcompositionDenominatorParameter target) source.value := by
  have hsub : HasDerivAt (fun w : ℂ => w - source.value) 1 source.value :=
    (hasDerivAt_id' source.value).sub_const source.value
  simpa using
    (HasDerivAt.const_mul
      (source.postcompositionDenominatorParameter target) hsub).const_add 1

/-- The normal-form denominator is continuous at the source value. -/
theorem postcompositionNormalForm_denominator_continuousAt_source
    (source target : NondegenerateFiniteTwoJet) :
    ContinuousAt
      (fun w : ℂ =>
        1 + source.postcompositionDenominatorParameter target *
          (w - source.value))
      source.value :=
  (source.postcompositionNormalForm_denominator_hasDerivAt_source target).continuousAt

/--
After shrinking to a metric ball around the source value, the normal-form
denominator is nonzero everywhere on the ball.
-/
theorem exists_ball_postcompositionNormalForm_denominator_ne_zero
    (source target : NondegenerateFiniteTwoJet) :
    ∃ r : ℝ, 0 < r ∧
      ∀ w ∈ Metric.ball source.value r,
        1 + source.postcompositionDenominatorParameter target *
          (w - source.value) ≠ 0 := by
  have hcont := source.postcompositionNormalForm_denominator_continuousAt_source target
  have hmem :
      (fun w : ℂ =>
        1 + source.postcompositionDenominatorParameter target *
          (w - source.value)) ⁻¹' ({w : ℂ | w ≠ 0}) ∈
        nhds source.value :=
    hcont.preimage_mem_nhds
      (isOpen_ne.mem_nhds
        (source.postcompositionNormalForm_denominator_source_ne_zero target))
  rcases Metric.mem_nhds_iff.mp hmem with ⟨r, hr_pos, hr_subset⟩
  exact ⟨r, hr_pos, fun w hw => hr_subset hw⟩

/--
The normal-form postcomposition is analytic on any set where its denominator
does not vanish.
-/
theorem postcompositionNormalForm_analyticOnNhd
    (source target : NondegenerateFiniteTwoJet) {U : Set ℂ}
    (hden_ne : ∀ w ∈ U,
      1 + source.postcompositionDenominatorParameter target *
        (w - source.value) ≠ 0) :
    AnalyticOnNhd ℂ (source.postcompositionNormalForm target) U := by
  have hsub : AnalyticOnNhd ℂ (fun w : ℂ => w - source.value) U := by
    simpa using (analyticOnNhd_id.sub analyticOnNhd_const)
  have hnum :
      AnalyticOnNhd ℂ
        (fun w : ℂ =>
          source.postcompositionFirstDeriv target * (w - source.value)) U := by
    simpa using (analyticOnNhd_const.mul hsub)
  have hden :
      AnalyticOnNhd ℂ
        (fun w : ℂ =>
          1 + source.postcompositionDenominatorParameter target *
            (w - source.value)) U := by
    simpa using (analyticOnNhd_const.add (analyticOnNhd_const.mul hsub))
  have hfrac :
      AnalyticOnNhd ℂ
        (fun w : ℂ =>
          source.postcompositionFirstDeriv target * (w - source.value) /
            (1 + source.postcompositionDenominatorParameter target *
              (w - source.value))) U :=
    hnum.div hden hden_ne
  simpa [postcompositionNormalForm] using
    (analyticOnNhd_const.add hfrac)

/--
There is a metric ball around the source value on which the normal-form
postcomposition is analytic and its denominator is nonzero.
-/
theorem exists_ball_postcompositionNormalForm_analyticOnNhd
    (source target : NondegenerateFiniteTwoJet) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (source.postcompositionNormalForm target)
        (Metric.ball source.value r) ∧
      ∀ w ∈ Metric.ball source.value r,
        1 + source.postcompositionDenominatorParameter target *
          (w - source.value) ≠ 0 := by
  rcases source.exists_ball_postcompositionNormalForm_denominator_ne_zero target with
    ⟨r, hr_pos, hden_ne⟩
  exact ⟨r, hr_pos,
    source.postcompositionNormalForm_analyticOnNhd target hden_ne, hden_ne⟩

/--
The normal-form postcomposition has the prescribed first derivative at the
source value.
-/
theorem postcompositionNormalForm_hasDerivAt_source
    (source target : NondegenerateFiniteTwoJet) :
    HasDerivAt (source.postcompositionNormalForm target)
      (source.postcompositionFirstDeriv target) source.value := by
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  let p := target.value
  have hsub : HasDerivAt (fun w : ℂ => w - a) 1 a :=
    (hasDerivAt_id' a).sub_const a
  have hnum : HasDerivAt (fun w : ℂ => B * (w - a)) B a := by
    simpa using HasDerivAt.const_mul B hsub
  have hden : HasDerivAt (fun w : ℂ => 1 + κ * (w - a)) κ a := by
    simpa using (HasDerivAt.const_mul κ hsub).const_add 1
  have hden_ne : (1 + κ * (a - a)) ≠ 0 := by
    simp
  change HasDerivAt
    (fun w : ℂ => p + B * (w - a) / (1 + κ * (w - a))) B a
  simpa using
    (hnum.fun_div hden hden_ne).const_add p

/--
Away from its pole, the normal-form postcomposition has derivative
`B/(1+κ(w-a))^2`.
-/
theorem postcompositionNormalForm_hasDerivAt
    (source target : NondegenerateFiniteTwoJet) {w : ℂ}
    (hden_ne :
      1 + source.postcompositionDenominatorParameter target *
        (w - source.value) ≠ 0) :
    HasDerivAt (source.postcompositionNormalForm target)
      (source.postcompositionNormalFormDeriv target w) w := by
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  let p := target.value
  have hsub : HasDerivAt (fun z : ℂ => z - a) 1 w :=
    (hasDerivAt_id' w).sub_const a
  have hnum : HasDerivAt (fun z : ℂ => B * (z - a)) B w := by
    simpa using HasDerivAt.const_mul B hsub
  have hden : HasDerivAt (fun z : ℂ => 1 + κ * (z - a)) κ w := by
    simpa using (HasDerivAt.const_mul κ hsub).const_add 1
  change HasDerivAt
    (fun z : ℂ => p + B * (z - a) / (1 + κ * (z - a)))
    (B / (1 + κ * (w - a)) ^ 2) w
  convert (hnum.fun_div hden (by simpa [κ, a] using hden_ne)).const_add p using 1
  ring

/--
Away from the pole, the explicit first derivative of the normal form is
nonzero.
-/
theorem postcompositionNormalFormDeriv_ne_zero
    (source target : NondegenerateFiniteTwoJet) {w : ℂ}
    (hden_ne :
      1 + source.postcompositionDenominatorParameter target *
        (w - source.value) ≠ 0) :
    source.postcompositionNormalFormDeriv target w ≠ 0 := by
  rw [postcompositionNormalFormDeriv]
  exact div_ne_zero (source.postcompositionFirstDeriv_ne_zero target)
    (pow_ne_zero 2 hden_ne)

/--
The explicit first derivative of the normal form has derivative `-2Bκ` at the
source value.
-/
theorem postcompositionNormalFormDeriv_hasDerivAt_source_aux
    (source target : NondegenerateFiniteTwoJet) :
    HasDerivAt (source.postcompositionNormalFormDeriv target)
      (-2 * source.postcompositionFirstDeriv target *
        source.postcompositionDenominatorParameter target) source.value := by
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  have hsub : HasDerivAt (fun w : ℂ => w - a) 1 a :=
    (hasDerivAt_id' a).sub_const a
  have hden : HasDerivAt (fun w : ℂ => 1 + κ * (w - a)) κ a := by
    simpa using (HasDerivAt.const_mul κ hsub).const_add 1
  have hden_sq :
      HasDerivAt (fun w : ℂ => (1 + κ * (w - a)) ^ 2) (2 * κ) a := by
    convert hden.pow 2 using 1
    ring
  have hden_sq_ne : (1 + κ * (a - a)) ^ 2 ≠ 0 := by
    simp
  change HasDerivAt
    (fun w : ℂ => B / (1 + κ * (w - a)) ^ 2) (-2 * B * κ) a
  convert (hasDerivAt_const (x := a) (c := B)).fun_div hden_sq hden_sq_ne using 1
  ring

/--
The explicit first derivative of the normal form has the prescribed second
derivative at the source value.
-/
theorem postcompositionNormalFormDeriv_hasDerivAt_source
    (source target : NondegenerateFiniteTwoJet) :
    HasDerivAt (source.postcompositionNormalFormDeriv target)
      (source.postcompositionSecondDeriv target) source.value := by
  convert source.postcompositionNormalFormDeriv_hasDerivAt_source_aux target using 1
  exact (source.postcompositionDenominatorParameter_spec target).symm

/--
Away from the pole, the explicit first derivative of the normal form has the
explicit second derivative.
-/
theorem postcompositionNormalFormDeriv_hasDerivAt
    (source target : NondegenerateFiniteTwoJet) {w : ℂ}
    (hden_ne :
      1 + source.postcompositionDenominatorParameter target *
        (w - source.value) ≠ 0) :
    HasDerivAt (source.postcompositionNormalFormDeriv target)
      (source.postcompositionNormalFormSecondDeriv target w) w := by
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  have hsub : HasDerivAt (fun z : ℂ => z - a) 1 w :=
    (hasDerivAt_id' w).sub_const a
  have hden : HasDerivAt (fun z : ℂ => 1 + κ * (z - a)) κ w := by
    simpa using (HasDerivAt.const_mul κ hsub).const_add 1
  have hden_sq :
      HasDerivAt (fun z : ℂ => (1 + κ * (z - a)) ^ 2)
        (2 * (1 + κ * (w - a)) * κ) w := by
    convert hden.pow 2 using 1
    ring
  have hden_sq_ne : (1 + κ * (w - a)) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (by simpa [κ, a] using hden_ne)
  change HasDerivAt
    (fun z : ℂ => B / (1 + κ * (z - a)) ^ 2)
    ((-2 * B * κ) / (1 + κ * (w - a)) ^ 3) w
  convert (hasDerivAt_const (x := w) (c := B)).fun_div hden_sq hden_sq_ne using 1
  field_simp [hden_ne]
  ring

/--
Away from the pole, the explicit second derivative of the normal form has the
explicit third derivative.
-/
theorem postcompositionNormalFormSecondDeriv_hasDerivAt
    (source target : NondegenerateFiniteTwoJet) {w : ℂ}
    (hden_ne :
      1 + source.postcompositionDenominatorParameter target *
        (w - source.value) ≠ 0) :
    HasDerivAt (source.postcompositionNormalFormSecondDeriv target)
      (source.postcompositionNormalFormThirdDeriv target w) w := by
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  have hsub : HasDerivAt (fun z : ℂ => z - a) 1 w :=
    (hasDerivAt_id' w).sub_const a
  have hden : HasDerivAt (fun z : ℂ => 1 + κ * (z - a)) κ w := by
    simpa using (HasDerivAt.const_mul κ hsub).const_add 1
  have hden_cube :
      HasDerivAt (fun z : ℂ => (1 + κ * (z - a)) ^ 3)
        (3 * (1 + κ * (w - a)) ^ 2 * κ) w := by
    convert hden.pow 3 using 1
  have hden_cube_ne : (1 + κ * (w - a)) ^ 3 ≠ 0 := by
    exact pow_ne_zero 3 (by simpa [κ, a] using hden_ne)
  change HasDerivAt
    (fun z : ℂ => (-2 * B * κ) / (1 + κ * (z - a)) ^ 3)
    ((6 * B * κ ^ 2) / (1 + κ * (w - a)) ^ 4) w
  convert
    (hasDerivAt_const (x := w) (c := -2 * B * κ)).fun_div
      hden_cube hden_cube_ne using 1
  field_simp [hden_ne]
  ring

/-- The determinant of the normal-form Mobius matrix is the parameter `B`. -/
theorem postcompositionNormalFormMatrix_det
    (source target : NondegenerateFiniteTwoJet) :
    Matrix.det (source.postcompositionNormalFormMatrix target) =
      source.postcompositionFirstDeriv target := by
  simp [postcompositionNormalFormMatrix, Matrix.det_fin_two]
  ring

/--
The normal form is represented by an actual `GL(2, ℂ)` Mobius
representative.
-/
def postcompositionNormalFormRepresentative
    (source target : NondegenerateFiniteTwoJet) : MobiusRepresentative :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (source.postcompositionNormalFormMatrix target)
    (by
      rw [source.postcompositionNormalFormMatrix_det target]
      exact source.postcompositionFirstDeriv_ne_zero target)

/--
The projective action of the normal-form representative agrees with the
explicit affine normal-form function wherever the affine denominator is
nonzero.
-/
theorem postcompositionNormalFormRepresentative_smul_coe
    (source target : NondegenerateFiniteTwoJet) {w : ℂ}
    (hden_ne :
      1 + source.postcompositionDenominatorParameter target *
        (w - source.value) ≠ 0) :
    source.postcompositionNormalFormRepresentative target • (w : RiemannSphere) =
      (source.postcompositionNormalForm target w : RiemannSphere) := by
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  let p := target.value
  have hκ : source.postcompositionDenominatorParameter target = κ := rfl
  have ha : source.value = a := rfl
  have hp : target.value = p := rfl
  have hB : source.postcompositionFirstDeriv target = B := rfl
  rw [OnePoint.smul_some_eq_ite]
  have hden_linear :
      κ * w + (1 - κ * a) = 1 + κ * (w - a) := by
    ring
  have hden_ne' :
      (source.postcompositionNormalFormRepresentative target) 1 0 * w +
          (source.postcompositionNormalFormRepresentative target) 1 1 ≠ 0 := by
    simpa [postcompositionNormalFormRepresentative, postcompositionNormalFormMatrix,
      B, κ, a, p, hden_linear] using hden_ne
  rw [if_neg hden_ne']
  rw [OnePoint.coe_eq_coe]
  simp [postcompositionNormalFormRepresentative, postcompositionNormalFormMatrix,
    postcompositionNormalForm]
  change
    ((p * κ + B) * w + (p - (p * κ + B) * a)) /
        (κ * w + (1 - κ * a)) =
      p + B * (w - a) / (1 + κ * (w - a))
  rw [hden_linear]
  rw [div_eq_iff hden_ne]
  rw [hκ, ha]
  have hden_compact : 1 + κ * (w - a) ≠ 0 := by
    simpa [hκ, ha] using hden_ne
  have hden_ne_nf : 1 + κ * w - κ * a ≠ 0 := by
    convert hden_ne using 1
    ring
  field_simp [hden_compact, hden_ne_nf]
  ring_nf

/--
At the source finite point, the normal-form representative sends the source
value to the target value in the Riemann sphere.
-/
theorem postcompositionNormalFormRepresentative_smul_source
    (source target : NondegenerateFiniteTwoJet) :
    source.postcompositionNormalFormRepresentative target •
        (source.value : RiemannSphere) =
      (target.value : RiemannSphere) := by
  have hden :
      1 + source.postcompositionDenominatorParameter target *
        (source.value - source.value) ≠ 0 := by
    simp
  calc
    source.postcompositionNormalFormRepresentative target •
        (source.value : RiemannSphere)
        = (source.postcompositionNormalForm target source.value : RiemannSphere) :=
          source.postcompositionNormalFormRepresentative_smul_coe target hden
    _ = (target.value : RiemannSphere) := by
          simp [postcompositionNormalForm_apply_source]

/--
The concrete normal-form Mobius postcomposition realizes the target finite
two-jet at the source finite point.

This packages the algebraic and analytic facts that downstream construction
steps need: value, first derivative, differentiated first derivative, and the
projective action at the base finite point.
-/
structure PostcompositionNormalFormRealizesTarget
    (source target : NondegenerateFiniteTwoJet) : Prop where
  /-- The normal form sends the source value to the target value. -/
  value_eq :
    source.postcompositionNormalForm target source.value = target.value
  /-- The normal form has the required first derivative at the source value. -/
  hasDerivAt_source :
    HasDerivAt (source.postcompositionNormalForm target)
      (source.postcompositionFirstDeriv target) source.value
  /--
  The explicit first derivative of the normal form has the required second
  derivative at the source value.
  -/
  deriv_hasDerivAt_source :
    HasDerivAt (source.postcompositionNormalFormDeriv target)
      (source.postcompositionSecondDeriv target) source.value
  /-- The Mobius representative sends the source finite point to the target. -/
  representative_smul_source :
    source.postcompositionNormalFormRepresentative target •
        (source.value : RiemannSphere) =
      (target.value : RiemannSphere)

/--
The explicit normal form realizes every nondegenerate target finite two-jet.
-/
theorem postcompositionNormalForm_realizesTarget
    (source target : NondegenerateFiniteTwoJet) :
    PostcompositionNormalFormRealizesTarget source target where
  value_eq := source.postcompositionNormalForm_apply_source target
  hasDerivAt_source := source.postcompositionNormalForm_hasDerivAt_source target
  deriv_hasDerivAt_source :=
    source.postcompositionNormalFormDeriv_hasDerivAt_source target
  representative_smul_source :=
    source.postcompositionNormalFormRepresentative_smul_source target

end NondegenerateFiniteTwoJet

/-- The finite two-jet of a local projective developing map at a point of its domain. -/
def LocalProjectiveDevelopingMap.finiteTwoJet
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) {z₀ : ℂ} (hz₀ : z₀ ∈ D.domain) :
    NondegenerateFiniteTwoJet where
  value := D.affineMap z₀
  firstDeriv := D.affineMapDeriv z₀
  secondDeriv := D.affineMapSecondDeriv z₀
  firstDeriv_ne_zero := D.affineMapDeriv_ne_zero z₀ hz₀

/--
The explicit affine map obtained by postcomposing a local projective
developing coordinate with the normal-form Mobius map attached to a base
finite two-jet.
-/
def LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) {z₀ : ℂ} (hz₀ : z₀ ∈ D.domain)
    (target : NondegenerateFiniteTwoJet) : ℂ → ℂ :=
  fun z ↦ (D.finiteTwoJet hz₀).postcompositionNormalForm target (D.affineMap z)

/--
The explicit symbolic first derivative of the normal-form postcomposition.
-/
def LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapDeriv
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) {z₀ : ℂ} (hz₀ : z₀ ∈ D.domain)
    (target : NondegenerateFiniteTwoJet) : ℂ → ℂ :=
  fun z ↦
    (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv target (D.affineMap z) *
      D.affineMapDeriv z

/--
The explicit symbolic second derivative of the normal-form postcomposition,
written in chain-rule form.
-/
def LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapSecondDeriv
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) {z₀ : ℂ} (hz₀ : z₀ ∈ D.domain)
    (target : NondegenerateFiniteTwoJet) : ℂ → ℂ :=
  fun z ↦
    (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv target (D.affineMap z) *
        D.affineMapSecondDeriv z +
      (D.finiteTwoJet hz₀).postcompositionNormalFormSecondDeriv target (D.affineMap z) *
        D.affineMapDeriv z ^ 2

/--
The explicit symbolic third derivative of the normal-form postcomposition,
written in chain-rule form.
-/
def LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapThirdDeriv
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) {z₀ : ℂ} (hz₀ : z₀ ∈ D.domain)
    (target : NondegenerateFiniteTwoJet) : ℂ → ℂ :=
  fun z ↦
    (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv target (D.affineMap z) *
        D.affineMapThirdDeriv z +
      3 * (D.finiteTwoJet hz₀).postcompositionNormalFormSecondDeriv target
          (D.affineMap z) *
        D.affineMapDeriv z * D.affineMapSecondDeriv z +
      (D.finiteTwoJet hz₀).postcompositionNormalFormThirdDeriv target (D.affineMap z) *
        D.affineMapDeriv z ^ 3

/--
The symbolic Schwarzian expression is invariant under explicit normal-form
Mobius postcomposition.

This is the project-local chain-rule algebra: after substituting the explicit
first, second, and third derivative fields for `M ∘ f`, all terms involving
the normal-form parameters cancel and the original Schwarzian remains.
-/
theorem LocalProjectiveDevelopingMap.schwarzianExpression_normalFormPostcomposition_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) {z₀ z : ℂ} (hz₀ : z₀ ∈ D.domain)
    (hz : z ∈ D.domain) (target : NondegenerateFiniteTwoJet)
    (hden :
      1 + (D.finiteTwoJet hz₀).postcompositionDenominatorParameter target *
        (D.affineMap z - D.affineMap z₀) ≠ 0) :
    schwarzianExpression
        (D.normalFormPostcompositionAffineMapDeriv hz₀ target)
        (D.normalFormPostcompositionAffineMapSecondDeriv hz₀ target)
        (D.normalFormPostcompositionAffineMapThirdDeriv hz₀ target) z =
      schwarzianExpression D.affineMapDeriv D.affineMapSecondDeriv D.affineMapThirdDeriv z := by
  let source := D.finiteTwoJet hz₀
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  let den : ℂ := 1 + κ * (D.affineMap z - source.value)
  let f₁ := D.affineMapDeriv z
  let f₂ := D.affineMapSecondDeriv z
  let f₃ := D.affineMapThirdDeriv z
  have hB : B ≠ 0 := by
    simpa [B, source] using source.postcompositionFirstDeriv_ne_zero target
  have hden' : den ≠ 0 := by
    simpa [den, κ, source, LocalProjectiveDevelopingMap.finiteTwoJet] using hden
  have hf₁ : f₁ ≠ 0 := by
    simpa [f₁] using D.affineMapDeriv_ne_zero z hz
  rw [schwarzianExpression, schwarzianExpression,
    LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapDeriv,
    LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapSecondDeriv,
    LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapThirdDeriv,
    NondegenerateFiniteTwoJet.postcompositionNormalFormDeriv,
    NondegenerateFiniteTwoJet.postcompositionNormalFormSecondDeriv,
    NondegenerateFiniteTwoJet.postcompositionNormalFormThirdDeriv]
  change
    ((B / den ^ 2 * f₃ + 3 * ((-2 * B * κ) / den ^ 3) * f₁ * f₂ +
          ((6 * B * κ ^ 2) / den ^ 4) * f₁ ^ 3) /
        (B / den ^ 2 * f₁) -
      (3 / 2 : ℂ) *
        (((B / den ^ 2 * f₂ + ((-2 * B * κ) / den ^ 3) * f₁ ^ 2) /
              (B / den ^ 2 * f₁)) ^ 2)) =
      f₃ / f₁ - (3 / 2 : ℂ) * (f₂ / f₁) ^ 2
  field_simp [hB, hden', hf₁]
  ring

/--
The explicit normal-form postcomposition is continuous wherever the original
affine developing coordinate is continuous and the normal-form denominator is
nonzero.
-/
theorem LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMap_continuousAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) {z₀ z : ℂ} (hz₀ : z₀ ∈ D.domain)
    (target : NondegenerateFiniteTwoJet)
    (hcont : ContinuousAt D.affineMap z)
    (hden :
      1 + (D.finiteTwoJet hz₀).postcompositionDenominatorParameter target *
        (D.affineMap z - D.affineMap z₀) ≠ 0) :
    ContinuousAt (D.normalFormPostcompositionAffineMap hz₀ target) z := by
  let source := D.finiteTwoJet hz₀
  let B := source.postcompositionFirstDeriv target
  let κ := source.postcompositionDenominatorParameter target
  have hsub :
      ContinuousAt (fun x : ℂ => D.affineMap x - source.value) z := by
    simpa [source, LocalProjectiveDevelopingMap.finiteTwoJet] using
      hcont.sub continuousAt_const
  have hnum :
      ContinuousAt (fun x : ℂ => B * (D.affineMap x - source.value)) z :=
    hsub.const_mul B
  have hden_cont :
      ContinuousAt (fun x : ℂ => 1 + κ * (D.affineMap x - source.value)) z :=
    (hsub.const_mul κ).const_add 1
  have hden' :
      (fun x : ℂ => 1 + κ * (D.affineMap x - source.value)) z ≠ 0 := by
    simpa [source, κ, LocalProjectiveDevelopingMap.finiteTwoJet] using hden
  have hquot :
      ContinuousAt
        (fun x : ℂ =>
          B * (D.affineMap x - source.value) /
            (1 + κ * (D.affineMap x - source.value))) z :=
    hnum.div hden_cont hden'
  have hmain :
      ContinuousAt
        (fun x : ℂ =>
          target.value +
            B * (D.affineMap x - source.value) /
              (1 + κ * (D.affineMap x - source.value))) z :=
    hquot.const_add target.value
  simpa [LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMap,
    NondegenerateFiniteTwoJet.postcompositionNormalForm, source, B, κ] using hmain

/--
The hyperbolic base 2-jet prescribed at a point for a Mobius-normalized
Schwarzian solution.

The field `uZ` is the Wirtinger derivative `u_z z₀`, tied to the canonical
Frechet-level field on `LocalConformalFactor`.
-/
structure HyperbolicSchwarzianBaseJet (u : LocalConformalFactor) (z₀ : ℂ) where
  /-- The value of the Wirtinger derivative `u_z` at `z₀`. -/
  uZ : ℂ
  /-- The jet uses the canonical Frechet-Wirtinger derivative of `u.logDensity`. -/
  agrees_with_logDensity_derivative : uZ = u.wirtingerZ z₀

namespace HyperbolicSchwarzianBaseJet

/-- The target value for the normalized developing map: `i ∈ ℍ`. -/
def targetValue {u : LocalConformalFactor} {z₀ : ℂ}
    (_J : HyperbolicSchwarzianBaseJet u z₀) : ℂ :=
  Complex.I

/-- The target first derivative: the positive real number `exp (u z₀)`. -/
def targetDeriv {u : LocalConformalFactor} {z₀ : ℂ}
    (_J : HyperbolicSchwarzianBaseJet u z₀) : ℂ :=
  (Real.exp (u.logDensity z₀) : ℂ)

/--
The target second derivative:

`F''(z₀) = F'(z₀) * (2 * u_z(z₀) - i * F'(z₀))`.
-/
def targetSecondDeriv {u : LocalConformalFactor} {z₀ : ℂ}
    (J : HyperbolicSchwarzianBaseJet u z₀) : ℂ :=
  J.targetDeriv * (2 * J.uZ - Complex.I * J.targetDeriv)

/-- The hyperbolic target first derivative is nonzero. -/
theorem targetDeriv_ne_zero {u : LocalConformalFactor} {z₀ : ℂ}
    (J : HyperbolicSchwarzianBaseJet u z₀) :
    J.targetDeriv ≠ 0 := by
  change ((Real.exp (u.logDensity z₀) : ℂ) ≠ 0)
  exact_mod_cast Real.exp_ne_zero (u.logDensity z₀)

/-- The hyperbolic target two-jet as a nondegenerate finite two-jet. -/
def toNondegenerateFiniteTwoJet {u : LocalConformalFactor} {z₀ : ℂ}
    (J : HyperbolicSchwarzianBaseJet u z₀) :
    NondegenerateFiniteTwoJet where
  value := J.targetValue
  firstDeriv := J.targetDeriv
  secondDeriv := J.targetSecondDeriv
  firstDeriv_ne_zero := J.targetDeriv_ne_zero

/-- The base-jet derivative is the canonical Frechet-Wirtinger derivative. -/
theorem uZ_eq_wirtingerZ {u : LocalConformalFactor} {z₀ : ℂ}
    (J : HyperbolicSchwarzianBaseJet u z₀) :
    J.uZ = u.wirtingerZ z₀ :=
  J.agrees_with_logDensity_derivative

end HyperbolicSchwarzianBaseJet

/--
A local projective developing map obtained from another one by Mobius
postcomposition and realizing a prescribed finite two-jet at a base point.

This is the purely projective part of the hyperbolic normalization: it does not
yet assert that the normalized affine coordinate takes values in `ℍ`.
-/
structure LocalProjectiveMobiusTwoJetNormalization
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) (z₀ : ℂ)
    (target : NondegenerateFiniteTwoJet) where
  /-- The normalized local projective developing map. -/
  projective : LocalProjectiveDevelopingMap S
  /-- Mobius postcomposition used to normalize the original projective map. -/
  postcomposition : MobiusRepresentative
  /-- The normalized domain is a shrink of the original domain. -/
  domain_subset_original : projective.domain ⊆ D.domain
  /-- The normalized projective map is the Mobius postcomposition of the original. -/
  projective_eq_postcompose_original :
    ∀ z, z ∈ projective.domain →
      projective.projectiveMap z = postcomposition • D.projectiveMap z
  /-- The base point lies in the normalized domain. -/
  base_mem : z₀ ∈ projective.domain
  /-- The normalized finite value realizes the target value. -/
  value_eq : projective.affineMap z₀ = target.value
  /-- The normalized first derivative realizes the target first derivative. -/
  firstDeriv_eq : projective.affineMapDeriv z₀ = target.firstDeriv
  /-- The normalized second derivative realizes the target second derivative. -/
  secondDeriv_eq : projective.affineMapSecondDeriv z₀ = target.secondDeriv

namespace LocalProjectiveMobiusTwoJetNormalization

/-- The normalized domain. -/
def domain {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) : Set ℂ :=
  N.projective.domain

/-- The source two-jet of the original branch at the base point. -/
def sourceTwoJet {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) :
    NondegenerateFiniteTwoJet :=
  D.finiteTwoJet (N.domain_subset_original N.base_mem)

/--
The normal-form denominator parameter for the Mobius postcomposition selected
by this source and target two-jet.
-/
def denominatorParameter {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) : ℂ :=
  N.sourceTwoJet.postcompositionDenominatorParameter target

/--
The concrete normal-form Mobius map attached to the source and target
two-jets of a normalization.
-/
def normalForm {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) : ℂ → ℂ :=
  N.sourceTwoJet.postcompositionNormalForm target

/-- The explicit first derivative of the concrete normal form. -/
def normalFormDeriv {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) : ℂ → ℂ :=
  N.sourceTwoJet.postcompositionNormalFormDeriv target

/-- The `GL(2, ℂ)` representative of the concrete normal-form Mobius map. -/
def normalFormRepresentative {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) :
    MobiusRepresentative :=
  N.sourceTwoJet.postcompositionNormalFormRepresentative target

/--
The packaged normal-form representative acts on finite affine points by the
packaged normal-form function wherever the denominator is nonzero.
-/
theorem normalFormRepresentative_smul_coe {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} {D : LocalProjectiveDevelopingMap S}
    {z₀ : ℂ} {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) {w : ℂ}
    (hden_ne : 1 + N.denominatorParameter * (w - D.affineMap z₀) ≠ 0) :
    N.normalFormRepresentative • (w : RiemannSphere) =
      (N.normalForm w : RiemannSphere) := by
  simpa [normalFormRepresentative, normalForm, denominatorParameter, sourceTwoJet] using
    N.sourceTwoJet.postcompositionNormalFormRepresentative_smul_coe target
      (by simpa [denominatorParameter, sourceTwoJet] using hden_ne)

/--
At the base finite value, the packaged normal-form representative sends the
source point to the target point in the Riemann sphere.
-/
theorem normalFormRepresentative_smul_sourceValue {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} {D : LocalProjectiveDevelopingMap S}
    {z₀ : ℂ} {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) :
    N.normalFormRepresentative • (D.affineMap z₀ : RiemannSphere) =
      (target.value : RiemannSphere) := by
  have hden :
      1 + N.denominatorParameter * (D.affineMap z₀ - D.affineMap z₀) ≠ 0 := by
    simp
  calc
    N.normalFormRepresentative • (D.affineMap z₀ : RiemannSphere)
        = (N.normalForm (D.affineMap z₀) : RiemannSphere) :=
          N.normalFormRepresentative_smul_coe hden
    _ = (target.value : RiemannSphere) := by
          have hvalue : N.normalForm (D.affineMap z₀) = target.value := by
            simpa [normalForm, sourceTwoJet] using
              N.sourceTwoJet.postcompositionNormalForm_apply_source target
          simp [hvalue]

/--
If a packaged normalization uses the explicit normal-form representative, then
its recorded postcomposition sends the source finite point to the target point.
-/
theorem postcomposition_smul_sourceValue_of_eq_normalFormRepresentative
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target)
    (hpost : N.postcomposition = N.normalFormRepresentative) :
    N.postcomposition • (D.affineMap z₀ : RiemannSphere) =
      (target.value : RiemannSphere) := by
  simpa [hpost] using N.normalFormRepresentative_smul_sourceValue

/-- The concrete normal form sends the source finite value to the target value. -/
theorem normalForm_apply_sourceValue {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} {D : LocalProjectiveDevelopingMap S}
    {z₀ : ℂ} {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) :
    N.normalForm (D.affineMap z₀) = target.value := by
  simpa [normalForm, sourceTwoJet] using
    N.sourceTwoJet.postcompositionNormalForm_apply_source target

/-- The concrete normal form has the target first derivative at the source finite value. -/
theorem normalForm_hasDerivAt_sourceValue {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} {D : LocalProjectiveDevelopingMap S}
    {z₀ : ℂ} {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) :
    HasDerivAt N.normalForm
      (N.sourceTwoJet.postcompositionFirstDeriv target) (D.affineMap z₀) := by
  simpa [normalForm, sourceTwoJet] using
    N.sourceTwoJet.postcompositionNormalForm_hasDerivAt_source target

/--
Away from the pole, the concrete normal form has the packaged explicit
derivative.
-/
theorem normalForm_hasDerivAt {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} {D : LocalProjectiveDevelopingMap S}
    {z₀ : ℂ} {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) {w : ℂ}
    (hden_ne : 1 + N.denominatorParameter * (w - D.affineMap z₀) ≠ 0) :
    HasDerivAt N.normalForm (N.normalFormDeriv w) w := by
  simpa [normalForm, normalFormDeriv, denominatorParameter, sourceTwoJet] using
    N.sourceTwoJet.postcompositionNormalForm_hasDerivAt target
      (by simpa [denominatorParameter, sourceTwoJet] using hden_ne)

/--
The explicit first derivative of the concrete normal form has the prescribed
second derivative at the source value.
-/
theorem normalFormDeriv_hasDerivAt_sourceValue {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} {D : LocalProjectiveDevelopingMap S}
    {z₀ : ℂ} {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) :
    HasDerivAt N.normalFormDeriv
      (N.sourceTwoJet.postcompositionSecondDeriv target) (D.affineMap z₀) := by
  simpa [normalFormDeriv, sourceTwoJet] using
    N.sourceTwoJet.postcompositionNormalFormDeriv_hasDerivAt_source target

/--
The concrete normal-form Mobius map attached to a packaged normalization
realizes the target finite two-jet at the base value.
-/
theorem normalForm_realizesTarget {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} {D : LocalProjectiveDevelopingMap S}
    {z₀ : ℂ} {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) :
    N.sourceTwoJet.PostcompositionNormalFormRealizesTarget target := by
  exact N.sourceTwoJet.postcompositionNormalForm_realizesTarget target

/--
The concrete normal form attached to a two-jet normalization is analytic on
some metric ball around the original finite value.
-/
theorem exists_ball_normalForm_analyticOnNhd {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} {D : LocalProjectiveDevelopingMap S}
    {z₀ : ℂ} {target : NondegenerateFiniteTwoJet}
    (N : LocalProjectiveMobiusTwoJetNormalization D z₀ target) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ N.normalForm (Metric.ball (D.affineMap z₀) r) ∧
      ∀ w ∈ Metric.ball (D.affineMap z₀) r,
        1 + N.denominatorParameter * (w - D.affineMap z₀) ≠ 0 := by
  rcases N.sourceTwoJet.exists_ball_postcompositionNormalForm_analyticOnNhd target with
    ⟨r, hr_pos, hanalytic, hden⟩
  exact ⟨r, hr_pos, by simpa [normalForm, sourceTwoJet] using hanalytic, by
    simpa [denominatorParameter, sourceTwoJet] using hden⟩

end LocalProjectiveMobiusTwoJetNormalization

/--
Concrete data for postcomposing a local projective developing map by the
explicit normal-form Mobius representative.

This is a sharper construction boundary than
`LocalProjectiveMobiusTwoJetNormalization`: it asks the geometric/analytic
construction to provide the postcomposed projective map, the pole-avoiding
domain shrink, and the base-point chain-rule values.  Lean then derives the
target two-jet equations from the already-proved normal-form algebra.
-/
structure LocalProjectiveNormalFormPostcompositionData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) (z₀ : ℂ) (hz₀ : z₀ ∈ D.domain)
    (target : NondegenerateFiniteTwoJet) where
  /-- The postcomposed local projective developing map. -/
  projective : LocalProjectiveDevelopingMap S
  /-- The postcomposed domain is a shrink of the original domain. -/
  domain_subset_original : projective.domain ⊆ D.domain
  /-- The base point lies in the postcomposed domain. -/
  base_mem : z₀ ∈ projective.domain
  /--
  The projective map is the explicit normal-form Mobius postcomposition of the
  original map.
  -/
  projective_eq_postcompose_original :
    ∀ z, z ∈ projective.domain →
      projective.projectiveMap z =
        (D.finiteTwoJet hz₀).postcompositionNormalFormRepresentative target •
          D.projectiveMap z
  /-- The affine coordinate at the base is the explicit normal-form value. -/
  affineMap_eq_base :
    projective.affineMap z₀ =
      (D.finiteTwoJet hz₀).postcompositionNormalForm target (D.affineMap z₀)
  /-- The first derivative at the base is the first-order chain-rule value. -/
  affineMapDeriv_eq_base :
    projective.affineMapDeriv z₀ =
      (D.finiteTwoJet hz₀).postcompositionFirstDeriv target * D.affineMapDeriv z₀
  /-- The second derivative at the base is the second-order chain-rule value. -/
  affineMapSecondDeriv_eq_base :
    projective.affineMapSecondDeriv z₀ =
      (D.finiteTwoJet hz₀).postcompositionFirstDeriv target * D.affineMapSecondDeriv z₀ +
        (D.finiteTwoJet hz₀).postcompositionSecondDeriv target *
          D.affineMapDeriv z₀ ^ 2

namespace LocalProjectiveNormalFormPostcompositionData

/--
Package normal-form postcomposition data as a finite two-jet normalization.

The target two-jet fields are proved here from the normal-form reconstruction
identities, so the construction boundary above only has to supply the
chain-rule values.
-/
def toMobiusTwoJetNormalization
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (P : LocalProjectiveNormalFormPostcompositionData D z₀ hz₀ target) :
    LocalProjectiveMobiusTwoJetNormalization D z₀ target where
  projective := P.projective
  postcomposition :=
    (D.finiteTwoJet hz₀).postcompositionNormalFormRepresentative target
  domain_subset_original := P.domain_subset_original
  projective_eq_postcompose_original := P.projective_eq_postcompose_original
  base_mem := P.base_mem
  value_eq := by
    calc
      P.projective.affineMap z₀ =
          (D.finiteTwoJet hz₀).postcompositionNormalForm target (D.affineMap z₀) :=
        P.affineMap_eq_base
      _ = target.value := by
        simpa [LocalProjectiveDevelopingMap.finiteTwoJet] using
          (D.finiteTwoJet hz₀).postcompositionNormalForm_apply_source target
  firstDeriv_eq := by
    calc
      P.projective.affineMapDeriv z₀ =
          (D.finiteTwoJet hz₀).postcompositionFirstDeriv target * D.affineMapDeriv z₀ :=
        P.affineMapDeriv_eq_base
      _ = target.firstDeriv := by
        simpa [LocalProjectiveDevelopingMap.finiteTwoJet] using
          (D.finiteTwoJet hz₀).postcompositionFirstDeriv_mul_source target
  secondDeriv_eq := by
    calc
      P.projective.affineMapSecondDeriv z₀ =
          (D.finiteTwoJet hz₀).postcompositionFirstDeriv target * D.affineMapSecondDeriv z₀ +
            (D.finiteTwoJet hz₀).postcompositionSecondDeriv target *
              D.affineMapDeriv z₀ ^ 2 :=
        P.affineMapSecondDeriv_eq_base
      _ = target.secondDeriv := by
        simpa [LocalProjectiveDevelopingMap.finiteTwoJet] using
          (D.finiteTwoJet hz₀).postcompositionSecondDeriv_chain_rule target

/--
The normalization produced from normal-form postcomposition data uses exactly
the explicit normal-form representative.
-/
theorem toMobiusTwoJetNormalization_postcomposition
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (P : LocalProjectiveNormalFormPostcompositionData D z₀ hz₀ target) :
    P.toMobiusTwoJetNormalization.postcomposition =
      (D.finiteTwoJet hz₀).postcompositionNormalFormRepresentative target := rfl

end LocalProjectiveNormalFormPostcompositionData

/--
A pole-avoiding open shrink for explicit normal-form postcomposition.

This is the topological part of the explicit Mobius postcomposition
construction: the domain is shrunk so that it still contains the base point,
lies in the original developing-map domain, and avoids the pole of the
normal-form denominator.
-/
structure LocalProjectiveNormalFormPoleAvoidingShrink
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) (z₀ : ℂ) (hz₀ : z₀ ∈ D.domain)
    (target : NondegenerateFiniteTwoJet) where
  /-- The shrunk domain. -/
  domain : Set ℂ
  /-- The shrunk domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The shrunk domain lies in the original developing-map domain. -/
  domain_subset_original : domain ⊆ D.domain
  /-- The base point lies in the shrunk domain. -/
  base_mem : z₀ ∈ domain
  /-- The normal-form denominator does not vanish on the shrunk domain. -/
  denominator_ne_zero :
    ∀ z, z ∈ domain →
      1 + (D.finiteTwoJet hz₀).postcompositionDenominatorParameter target *
        (D.affineMap z - D.affineMap z₀) ≠ 0

namespace LocalProjectiveNormalFormPoleAvoidingShrink

/--
The pole-avoiding shrink exists as soon as the original affine coordinate is
continuous at the base point.
-/
theorem exists_of_affineMap_continuousAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (hcont : ContinuousAt D.affineMap z₀) :
    Nonempty (LocalProjectiveNormalFormPoleAvoidingShrink D z₀ hz₀ target) := by
  let κ := (D.finiteTwoJet hz₀).postcompositionDenominatorParameter target
  have hsub : ContinuousAt (fun z : ℂ => D.affineMap z - D.affineMap z₀) z₀ :=
    hcont.sub continuousAt_const
  have hden_cont :
      ContinuousAt (fun z : ℂ => 1 + κ * (D.affineMap z - D.affineMap z₀)) z₀ := by
    simpa using (hsub.const_mul κ).const_add 1
  have hden_base :
      (fun z : ℂ => 1 + κ * (D.affineMap z - D.affineMap z₀)) z₀ ≠ 0 := by
    simp
  have hden_mem :
      (fun z : ℂ => 1 + κ * (D.affineMap z - D.affineMap z₀)) ⁻¹'
          ({w : ℂ | w ≠ 0}) ∈ nhds z₀ :=
    hden_cont.preimage_mem_nhds (isOpen_ne.mem_nhds hden_base)
  have hdomain_mem : D.domain ∈ nhds z₀ :=
    D.isOpen_domain.mem_nhds hz₀
  have hboth :
      D.domain ∩
          (fun z : ℂ => 1 + κ * (D.affineMap z - D.affineMap z₀)) ⁻¹'
            ({w : ℂ | w ≠ 0}) ∈ nhds z₀ :=
    Filter.inter_mem hdomain_mem hden_mem
  rcases Metric.mem_nhds_iff.mp hboth with ⟨r, hr_pos, hr_subset⟩
  exact ⟨{
    domain := Metric.ball z₀ r
    isOpen_domain := Metric.isOpen_ball
    domain_subset_original := by
      intro z hz
      exact (hr_subset hz).1
    base_mem := Metric.mem_ball_self hr_pos
    denominator_ne_zero := by
      intro z hz
      exact (hr_subset hz).2
  }⟩

end LocalProjectiveNormalFormPoleAvoidingShrink

/--
Explicit normal-form postcomposition data.

Here the postcomposed affine coordinate and its first two symbolic derivatives
are fixed by the normal-form chain-rule formulas.  The only analytic invariant
still requested is the third-derivative/Schwarzian calculation for these
explicit fields on a pole-avoiding shrunk domain.
-/
structure LocalProjectiveNormalFormPostcompositionExplicitData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) (z₀ : ℂ) (hz₀ : z₀ ∈ D.domain)
    (target : NondegenerateFiniteTwoJet) where
  /-- The shrunk domain on which the normal-form denominator avoids zero. -/
  domain : Set ℂ
  /-- The shrunk domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The shrunk domain lies in the original developing-map domain. -/
  domain_subset_original : domain ⊆ D.domain
  /-- The base point lies in the shrunk domain. -/
  base_mem : z₀ ∈ domain
  /-- The normal-form denominator does not vanish on the shrunk domain. -/
  denominator_ne_zero :
    ∀ z, z ∈ domain →
      1 + (D.finiteTwoJet hz₀).postcompositionDenominatorParameter target *
        (D.affineMap z - D.affineMap z₀) ≠ 0
  /-- The symbolic third derivative of the postcomposed affine coordinate. -/
  affineMapThirdDeriv : ℂ → ℂ
  /--
  The Schwarzian of the explicit postcomposed derivative fields remains the
  original Schwarzian coefficient.
  -/
  schwarzian_eq_coefficient :
    ∀ z, z ∈ domain →
      schwarzianExpression
          (D.normalFormPostcompositionAffineMapDeriv hz₀ target)
          (D.normalFormPostcompositionAffineMapSecondDeriv hz₀ target)
          affineMapThirdDeriv z =
        S.coefficient z

namespace LocalProjectiveNormalFormPostcompositionExplicitData

/--
The explicit postcomposition data determines a local projective developing map.

Lean proves the finite-chart projective action and nonzero derivative facts
from the normal-form representative and denominator nonvanishing; the only
Schwarzian input is the field carried by the explicit-data package.
-/
def toLocalProjectiveDevelopingMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target) :
    LocalProjectiveDevelopingMap S where
  domain := E.domain
  isOpen_domain := E.isOpen_domain
  domain_subset := fun z hz ↦ D.domain_subset (E.domain_subset_original hz)
  affineMap := D.normalFormPostcompositionAffineMap hz₀ target
  projectiveMap := fun z ↦
    (D.normalFormPostcompositionAffineMap hz₀ target z : RiemannSphere)
  projectiveMap_eq_affine := by
    intro z hz
    rfl
  projectiveMap_ne_infty := by
    intro z hz
    exact OnePoint.coe_ne_infty _
  affineMapDeriv := D.normalFormPostcompositionAffineMapDeriv hz₀ target
  affineMapSecondDeriv := D.normalFormPostcompositionAffineMapSecondDeriv hz₀ target
  affineMapThirdDeriv := E.affineMapThirdDeriv
  affineMapDeriv_ne_zero := by
    intro z hz
    rw [LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapDeriv]
    exact mul_ne_zero
      ((D.finiteTwoJet hz₀).postcompositionNormalFormDeriv_ne_zero target
        (by
          simpa [LocalProjectiveDevelopingMap.finiteTwoJet] using
            E.denominator_ne_zero z hz))
      (D.affineMapDeriv_ne_zero z (E.domain_subset_original hz))
  schwarzian_eq_coefficient := E.schwarzian_eq_coefficient

/--
Explicit normal-form postcomposition data gives the data-level construction
used by the Mobius two-jet normalization boundary.
-/
def toPostcompositionData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target) :
    LocalProjectiveNormalFormPostcompositionData D z₀ hz₀ target where
  projective := E.toLocalProjectiveDevelopingMap
  domain_subset_original := E.domain_subset_original
  base_mem := E.base_mem
  projective_eq_postcompose_original := by
    intro z hz
    rw [D.projectiveMap_eq_affine z (E.domain_subset_original hz)]
    exact ((D.finiteTwoJet hz₀).postcompositionNormalFormRepresentative_smul_coe
      target
      (by
        simpa [LocalProjectiveDevelopingMap.finiteTwoJet] using
          E.denominator_ne_zero z hz)).symm
  affineMap_eq_base := by
    rfl
  affineMapDeriv_eq_base := by
    have hderiv :
        (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv target (D.affineMap z₀) =
          (D.finiteTwoJet hz₀).postcompositionFirstDeriv target := by
      simpa [LocalProjectiveDevelopingMap.finiteTwoJet] using
        (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv_apply_source target
    change
      (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv target (D.affineMap z₀) *
          D.affineMapDeriv z₀ =
        (D.finiteTwoJet hz₀).postcompositionFirstDeriv target * D.affineMapDeriv z₀
    rw [hderiv]
  affineMapSecondDeriv_eq_base := by
    have hderiv :
        (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv target (D.affineMap z₀) =
          (D.finiteTwoJet hz₀).postcompositionFirstDeriv target := by
      simpa [LocalProjectiveDevelopingMap.finiteTwoJet] using
        (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv_apply_source target
    have hsecond :
        (D.finiteTwoJet hz₀).postcompositionNormalFormSecondDeriv target
            (D.affineMap z₀) =
          (D.finiteTwoJet hz₀).postcompositionSecondDeriv target := by
      simpa [LocalProjectiveDevelopingMap.finiteTwoJet] using
        (D.finiteTwoJet hz₀).postcompositionNormalFormSecondDeriv_apply_source target
    change
      (D.finiteTwoJet hz₀).postcompositionNormalFormDeriv target (D.affineMap z₀) *
          D.affineMapSecondDeriv z₀ +
        (D.finiteTwoJet hz₀).postcompositionNormalFormSecondDeriv target
            (D.affineMap z₀) *
          D.affineMapDeriv z₀ ^ 2 =
      (D.finiteTwoJet hz₀).postcompositionFirstDeriv target *
          D.affineMapSecondDeriv z₀ +
        (D.finiteTwoJet hz₀).postcompositionSecondDeriv target *
          D.affineMapDeriv z₀ ^ 2
    rw [hderiv, hsecond]

/--
The affine coordinate of explicit normal-form postcomposition data is
continuous at every point where the original affine coordinate is continuous.
-/
theorem affineMap_continuousAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {z : ℂ} (hz : z ∈ E.domain)
    (hcont : ContinuousAt D.affineMap z) :
    ContinuousAt E.toLocalProjectiveDevelopingMap.affineMap z :=
  D.normalFormPostcompositionAffineMap_continuousAt hz₀ target hcont
    (E.denominator_ne_zero z hz)

/--
Explicit normal-form postcomposition preserves `C^3` regularity of the affine
coordinate on the pole-avoiding domain.
-/
theorem affineMap_contDiffOn_of_original
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (hD : ContDiffOn ℝ 3 D.affineMap E.domain) :
    ContDiffOn ℝ 3 E.toLocalProjectiveDevelopingMap.affineMap E.domain := by
  let source := D.finiteTwoJet hz₀
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  let B := source.postcompositionFirstDeriv target
  let p := target.value
  have hden :
      ContDiffOn ℝ 3 (fun z : ℂ ↦ 1 + κ * (D.affineMap z - a)) E.domain := by
    exact contDiffOn_const.add (contDiffOn_const.mul (hD.sub contDiffOn_const))
  have hden_ne :
      ∀ z ∈ E.domain, 1 + κ * (D.affineMap z - a) ≠ 0 := by
    intro z hz
    simpa [source, κ, a, LocalProjectiveDevelopingMap.finiteTwoJet] using
      E.denominator_ne_zero z hz
  have hnum :
      ContDiffOn ℝ 3 (fun z : ℂ ↦ B * (D.affineMap z - a)) E.domain := by
    exact contDiffOn_const.mul (hD.sub contDiffOn_const)
  have hquot :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ B * (D.affineMap z - a) *
          (1 + κ * (D.affineMap z - a))⁻¹) E.domain := by
    exact hnum.mul (hden.inv hden_ne)
  have hres :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ p + B * (D.affineMap z - a) *
          (1 + κ * (D.affineMap z - a))⁻¹) E.domain := by
    exact contDiffOn_const.add hquot
  refine hres.congr ?_
  intro z hz
  simp [toLocalProjectiveDevelopingMap,
    LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMap,
    NondegenerateFiniteTwoJet.postcompositionNormalForm,
    source, κ, a, B, p, div_eq_mul_inv]

/--
Explicit normal-form postcomposition preserves `C^3` regularity of the
symbolic first derivative branch, assuming `C^3` regularity of the original
affine coordinate and its first derivative branch.
-/
theorem affineMapDeriv_contDiffOn_of_original
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (hD : ContDiffOn ℝ 3 D.affineMap E.domain)
    (hD' : ContDiffOn ℝ 3 D.affineMapDeriv E.domain) :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv z) E.domain := by
  let source := D.finiteTwoJet hz₀
  let κ := source.postcompositionDenominatorParameter target
  let a := source.value
  let B := source.postcompositionFirstDeriv target
  have hden :
      ContDiffOn ℝ 3 (fun z : ℂ ↦ 1 + κ * (D.affineMap z - a)) E.domain := by
    exact contDiffOn_const.add (contDiffOn_const.mul (hD.sub contDiffOn_const))
  have hden_ne :
      ∀ z ∈ E.domain, 1 + κ * (D.affineMap z - a) ≠ 0 := by
    intro z hz
    simpa [source, κ, a, LocalProjectiveDevelopingMap.finiteTwoJet] using
      E.denominator_ne_zero z hz
  have hpost :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ B * ((1 + κ * (D.affineMap z - a)) ^ 2)⁻¹) E.domain := by
    exact contDiffOn_const.mul
      ((hden.pow 2).inv (by
        intro z hz
        exact pow_ne_zero 2 (hden_ne z hz)))
  have hres :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦
          (B * ((1 + κ * (D.affineMap z - a)) ^ 2)⁻¹) * D.affineMapDeriv z)
        E.domain := by
    exact hpost.mul hD'
  simpa [toLocalProjectiveDevelopingMap,
    LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapDeriv,
    NondegenerateFiniteTwoJet.postcompositionNormalFormDeriv,
    source, κ, a, B, div_eq_mul_inv, mul_assoc] using hres

/--
The explicit normal-form postcomposition has the expected actual derivative
whenever the original affine developing coordinate does.

This is the analytic chain-rule bridge between the projective Mobius algebra
and the still-local Frobenius differentiability input.
-/
theorem affineMap_hasDerivAt_of_original
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {z : ℂ} (hz : z ∈ E.domain)
    (hD : HasDerivAt D.affineMap (D.affineMapDeriv z) z) :
    HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
      (E.toLocalProjectiveDevelopingMap.affineMapDeriv z) z := by
  let source := D.finiteTwoJet hz₀
  have hden :
      1 + source.postcompositionDenominatorParameter target *
        (D.affineMap z - source.value) ≠ 0 := by
    simpa [source, LocalProjectiveDevelopingMap.finiteTwoJet] using
      E.denominator_ne_zero z hz
  have hM :
      HasDerivAt (source.postcompositionNormalForm target)
        (source.postcompositionNormalFormDeriv target (D.affineMap z))
        (D.affineMap z) :=
    source.postcompositionNormalForm_hasDerivAt target hden
  have hcomp :
      HasDerivAt
        (fun w : ℂ ↦ source.postcompositionNormalForm target (D.affineMap w))
        (source.postcompositionNormalFormDeriv target (D.affineMap z) *
          D.affineMapDeriv z) z :=
    hM.comp z hD
  simpa [toLocalProjectiveDevelopingMap,
    LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMap,
    LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapDeriv,
    source] using hcomp

/--
Derivative equality for explicit normal-form postcomposition follows from the
corresponding actual derivative statement for the original affine developing
coordinate.
-/
theorem deriv_eq_affineMapDeriv_of_original_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {z : ℂ} (hz : z ∈ E.domain)
    (hD : HasDerivAt D.affineMap (D.affineMapDeriv z) z) :
    deriv E.toLocalProjectiveDevelopingMap.affineMap z =
      E.toLocalProjectiveDevelopingMap.affineMapDeriv z :=
  (E.affineMap_hasDerivAt_of_original hz hD).deriv

/--
The explicit first-derivative branch of the normal-form postcomposition has
the expected actual derivative whenever the original affine coordinate and its
first symbolic derivative have their expected actual derivatives.
-/
theorem affineMapDeriv_hasDerivAt_of_original
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {z : ℂ} (hz : z ∈ E.domain)
    (hD : HasDerivAt D.affineMap (D.affineMapDeriv z) z)
    (hD' : HasDerivAt (fun w : ℂ ↦ D.affineMapDeriv w)
      (D.affineMapSecondDeriv z) z) :
    HasDerivAt
      (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w)
      (E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv z) z := by
  let source := D.finiteTwoJet hz₀
  have hden :
      1 + source.postcompositionDenominatorParameter target *
        (D.affineMap z - source.value) ≠ 0 := by
    simpa [source, LocalProjectiveDevelopingMap.finiteTwoJet] using
      E.denominator_ne_zero z hz
  have hM' :
      HasDerivAt (source.postcompositionNormalFormDeriv target)
        (source.postcompositionNormalFormSecondDeriv target (D.affineMap z))
        (D.affineMap z) :=
    source.postcompositionNormalFormDeriv_hasDerivAt target hden
  have hcomp :
      HasDerivAt
        (fun w : ℂ ↦ source.postcompositionNormalFormDeriv target (D.affineMap w))
        (source.postcompositionNormalFormSecondDeriv target (D.affineMap z) *
          D.affineMapDeriv z) z :=
    hM'.comp z hD
  have hprod :
      HasDerivAt
        (fun w : ℂ ↦
          source.postcompositionNormalFormDeriv target (D.affineMap w) *
            D.affineMapDeriv w)
        (source.postcompositionNormalFormSecondDeriv target (D.affineMap z) *
            D.affineMapDeriv z * D.affineMapDeriv z +
          source.postcompositionNormalFormDeriv target (D.affineMap z) *
            D.affineMapSecondDeriv z) z :=
    hcomp.mul hD'
  convert hprod using 1
  · simp [toLocalProjectiveDevelopingMap,
      LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapSecondDeriv,
      source, pow_two]
    ring

/--
Derivative equality for the explicit first-derivative branch follows from the
corresponding actual derivative statements for the original affine branch.
-/
theorem deriv_affineMapDeriv_eq_affineMapSecondDeriv_of_original_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {z : ℂ} (hz : z ∈ E.domain)
    (hD : HasDerivAt D.affineMap (D.affineMapDeriv z) z)
    (hD' : HasDerivAt (fun w : ℂ ↦ D.affineMapDeriv w)
      (D.affineMapSecondDeriv z) z) :
    deriv (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w) z =
      E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv z :=
  (E.affineMapDeriv_hasDerivAt_of_original hz hD hD').deriv

/--
The explicit second-derivative branch of the normal-form postcomposition has
the expected actual derivative whenever the original affine branch has its
expected actual derivatives through the second derivative branch.
-/
theorem affineMapSecondDeriv_hasDerivAt_of_original
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {z : ℂ} (hz : z ∈ E.domain)
    (hD : HasDerivAt D.affineMap (D.affineMapDeriv z) z)
    (hD' : HasDerivAt (fun w : ℂ ↦ D.affineMapDeriv w)
      (D.affineMapSecondDeriv z) z)
    (hD'' : HasDerivAt (fun w : ℂ ↦ D.affineMapSecondDeriv w)
      (D.affineMapThirdDeriv z) z)
    (hthird :
      E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z =
        (D.normalFormPostcompositionAffineMapThirdDeriv hz₀ target) z) :
    HasDerivAt
      (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w)
      (E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z) z := by
  let source := D.finiteTwoJet hz₀
  have hden :
      1 + source.postcompositionDenominatorParameter target *
        (D.affineMap z - source.value) ≠ 0 := by
    simpa [source, LocalProjectiveDevelopingMap.finiteTwoJet] using
      E.denominator_ne_zero z hz
  have hM' :
      HasDerivAt (source.postcompositionNormalFormDeriv target)
        (source.postcompositionNormalFormSecondDeriv target (D.affineMap z))
        (D.affineMap z) :=
    source.postcompositionNormalFormDeriv_hasDerivAt target hden
  have hM'' :
      HasDerivAt (source.postcompositionNormalFormSecondDeriv target)
        (source.postcompositionNormalFormThirdDeriv target (D.affineMap z))
        (D.affineMap z) :=
    source.postcompositionNormalFormSecondDeriv_hasDerivAt target hden
  have hcomp' :
      HasDerivAt
        (fun w : ℂ ↦ source.postcompositionNormalFormDeriv target (D.affineMap w))
        (source.postcompositionNormalFormSecondDeriv target (D.affineMap z) *
          D.affineMapDeriv z) z :=
    hM'.comp z hD
  have hcomp'' :
      HasDerivAt
        (fun w : ℂ ↦
          source.postcompositionNormalFormSecondDeriv target (D.affineMap w))
        (source.postcompositionNormalFormThirdDeriv target (D.affineMap z) *
          D.affineMapDeriv z) z :=
    hM''.comp z hD
  have hterm₁ :
      HasDerivAt
        (fun w : ℂ ↦
          source.postcompositionNormalFormDeriv target (D.affineMap w) *
            D.affineMapSecondDeriv w)
        (source.postcompositionNormalFormSecondDeriv target (D.affineMap z) *
            D.affineMapDeriv z * D.affineMapSecondDeriv z +
          source.postcompositionNormalFormDeriv target (D.affineMap z) *
            D.affineMapThirdDeriv z) z :=
    hcomp'.mul hD''
  have hsq :
      HasDerivAt (fun w : ℂ ↦ D.affineMapDeriv w ^ 2)
        (2 * D.affineMapDeriv z * D.affineMapSecondDeriv z) z := by
    convert hD'.pow 2 using 1
    ring
  have hterm₂ :
      HasDerivAt
        (fun w : ℂ ↦
          source.postcompositionNormalFormSecondDeriv target (D.affineMap w) *
            D.affineMapDeriv w ^ 2)
        (source.postcompositionNormalFormThirdDeriv target (D.affineMap z) *
            D.affineMapDeriv z * D.affineMapDeriv z ^ 2 +
          source.postcompositionNormalFormSecondDeriv target (D.affineMap z) *
            (2 * D.affineMapDeriv z * D.affineMapSecondDeriv z)) z :=
    hcomp''.mul hsq
  have hsum :
      HasDerivAt
        (fun w : ℂ ↦
          source.postcompositionNormalFormDeriv target (D.affineMap w) *
              D.affineMapSecondDeriv w +
            source.postcompositionNormalFormSecondDeriv target (D.affineMap w) *
              D.affineMapDeriv w ^ 2)
        (source.postcompositionNormalFormSecondDeriv target (D.affineMap z) *
            D.affineMapDeriv z * D.affineMapSecondDeriv z +
          source.postcompositionNormalFormDeriv target (D.affineMap z) *
            D.affineMapThirdDeriv z +
          (source.postcompositionNormalFormThirdDeriv target (D.affineMap z) *
              D.affineMapDeriv z * D.affineMapDeriv z ^ 2 +
            source.postcompositionNormalFormSecondDeriv target (D.affineMap z) *
              (2 * D.affineMapDeriv z * D.affineMapSecondDeriv z))) z :=
    hterm₁.add hterm₂
  convert hsum using 1
  rw [hthird]
  simp [LocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapThirdDeriv,
    source]
  ring

/--
Derivative equality for the explicit second-derivative branch follows from
the corresponding actual derivative statements for the original affine branch.
-/
theorem deriv_affineMapSecondDeriv_eq_affineMapThirdDeriv_of_original_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {z : ℂ} (hz : z ∈ E.domain)
    (hD : HasDerivAt D.affineMap (D.affineMapDeriv z) z)
    (hD' : HasDerivAt (fun w : ℂ ↦ D.affineMapDeriv w)
      (D.affineMapSecondDeriv z) z)
    (hD'' : HasDerivAt (fun w : ℂ ↦ D.affineMapSecondDeriv w)
      (D.affineMapThirdDeriv z) z)
    (hthird :
      E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z =
        (D.normalFormPostcompositionAffineMapThirdDeriv hz₀ target) z) :
    deriv (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) z =
      E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z :=
  (E.affineMapSecondDeriv_hasDerivAt_of_original hz hD hD' hD'' hthird).deriv

/--
The explicit normal-form postcomposition sends the base point to the target
finite value.
-/
theorem affineMap_eq_targetValue_base
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target) :
    E.toLocalProjectiveDevelopingMap.affineMap z₀ = target.value := by
  simpa using E.toPostcompositionData.toMobiusTwoJetNormalization.value_eq

/--
If the target finite value is `i`, then explicit normal-form postcomposition
lands in the upper half-plane after shrinking to a small metric ball around the
base point.

This proves the topological landing part from mathlib continuity and openness
of `{w : ℂ | 0 < w.im}`; the separate analytic derivative-equality obligations
in `LocalUpperHalfPlaneProjectiveNormalization` remain outside this lemma.
-/
theorem exists_ball_mapsTo_upperHalfPlane_of_targetValue_eq_I
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (hcont : ContinuousAt D.affineMap z₀)
    (hvalue : target.value = Complex.I) :
    ∃ r : ℝ, 0 < r ∧
      ∀ z, z ∈ Metric.ball z₀ r →
        0 < (E.toLocalProjectiveDevelopingMap.affineMap z).im := by
  have hEcont :
      ContinuousAt E.toLocalProjectiveDevelopingMap.affineMap z₀ :=
    E.affineMap_continuousAt E.base_mem hcont
  have hpos :
      0 < (E.toLocalProjectiveDevelopingMap.affineMap z₀).im := by
    simp [E.affineMap_eq_targetValue_base, hvalue]
  have hopen : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hpre :
      E.toLocalProjectiveDevelopingMap.affineMap ⁻¹' {w : ℂ | 0 < w.im} ∈
        nhds z₀ :=
    hEcont.preimage_mem_nhds (hopen.mem_nhds hpos)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨r, hr_pos, hr_subset⟩
  exact ⟨r, hr_pos, by
    intro z hz
    exact hr_subset hz⟩

/--
If the target finite value is `i`, the upper-half-plane landing ball can be
chosen inside the explicit postcomposition domain.
-/
theorem exists_ball_subset_domain_mapsTo_upperHalfPlane_of_targetValue_eq_I
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (hcont : ContinuousAt D.affineMap z₀)
    (hvalue : target.value = Complex.I) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ E.domain ∧
      ∀ z, z ∈ Metric.ball z₀ r →
        0 < (E.toLocalProjectiveDevelopingMap.affineMap z).im := by
  have hEcont :
      ContinuousAt E.toLocalProjectiveDevelopingMap.affineMap z₀ :=
    E.affineMap_continuousAt E.base_mem hcont
  have hpos :
      0 < (E.toLocalProjectiveDevelopingMap.affineMap z₀).im := by
    simp [E.affineMap_eq_targetValue_base, hvalue]
  have hopen : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hpre :
      E.toLocalProjectiveDevelopingMap.affineMap ⁻¹' {w : ℂ | 0 < w.im} ∈
        nhds z₀ :=
    hEcont.preimage_mem_nhds (hopen.mem_nhds hpos)
  have hdomain : E.domain ∈ nhds z₀ :=
    E.isOpen_domain.mem_nhds E.base_mem
  have hboth :
      E.domain ∩
          E.toLocalProjectiveDevelopingMap.affineMap ⁻¹' {w : ℂ | 0 < w.im} ∈
        nhds z₀ :=
    Filter.inter_mem hdomain hpre
  rcases Metric.mem_nhds_iff.mp hboth with ⟨r, hr_pos, hr_subset⟩
  exact ⟨r, hr_pos, by
    intro z hz
    exact (hr_subset hz).1, by
    intro z hz
    exact (hr_subset hz).2⟩

/--
Restrict explicit normal-form postcomposition data to a metric ball inside its
domain.
-/
def restrictToBall
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (r : ℝ) (hsubset : Metric.ball z₀ r ⊆ E.domain) :
    LocalProjectiveDevelopingMap S where
  domain := Metric.ball z₀ r
  isOpen_domain := Metric.isOpen_ball
  domain_subset := by
    intro z hz
    exact E.toLocalProjectiveDevelopingMap.domain_subset (hsubset hz)
  affineMap := E.toLocalProjectiveDevelopingMap.affineMap
  projectiveMap := E.toLocalProjectiveDevelopingMap.projectiveMap
  projectiveMap_eq_affine := by
    intro z hz
    exact E.toLocalProjectiveDevelopingMap.projectiveMap_eq_affine z (hsubset hz)
  projectiveMap_ne_infty := by
    intro z hz
    exact E.toLocalProjectiveDevelopingMap.projectiveMap_ne_infty z (hsubset hz)
  affineMapDeriv := E.toLocalProjectiveDevelopingMap.affineMapDeriv
  affineMapSecondDeriv := E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv
  affineMapThirdDeriv := E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv
  affineMapDeriv_ne_zero := by
    intro z hz
    exact E.toLocalProjectiveDevelopingMap.affineMapDeriv_ne_zero z (hsubset hz)
  schwarzian_eq_coefficient := by
    intro z hz
    exact E.toLocalProjectiveDevelopingMap.schwarzian_eq_coefficient z (hsubset hz)

/--
The `ℍ`-valued lift obtained from a proof that the affine branch lands in
the upper half-plane on the chosen ball.

Outside the ball we put the harmless value `i`; the branch is only used on the
ball, and local equality on the open ball gives the derivative statement.
-/
noncomputable def upperHalfPlaneMapOfLanding
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (r : ℝ)
    (hmaps :
      ∀ z, z ∈ Metric.ball z₀ r →
        0 < (E.toLocalProjectiveDevelopingMap.affineMap z).im) :
    ℂ → ℍ := by
  classical
  exact
  fun z =>
    if hz : z ∈ Metric.ball z₀ r then
      ⟨E.toLocalProjectiveDevelopingMap.affineMap z, hmaps z hz⟩
    else
      ⟨Complex.I, by simp⟩

/-- On the landing ball, the constructed `ℍ`-lift agrees with the affine branch. -/
theorem upperHalfPlaneMapOfLanding_eq_affine
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {r : ℝ}
    (hmaps :
      ∀ z, z ∈ Metric.ball z₀ r →
        0 < (E.toLocalProjectiveDevelopingMap.affineMap z).im)
    {z : ℂ} (hz : z ∈ Metric.ball z₀ r) :
    (E.upperHalfPlaneMapOfLanding r hmaps z : ℂ) =
      E.toLocalProjectiveDevelopingMap.affineMap z := by
  classical
  rw [upperHalfPlaneMapOfLanding]
  simp [hz]

/--
The coerced `ℍ`-lift is locally equal to the affine branch at every point of
the landing ball.
-/
theorem upperHalfPlaneMapOfLanding_eventuallyEq_affine
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {r : ℝ}
    (hmaps :
      ∀ z, z ∈ Metric.ball z₀ r →
        0 < (E.toLocalProjectiveDevelopingMap.affineMap z).im)
    {z : ℂ} (hz : z ∈ Metric.ball z₀ r) :
    (fun w : ℂ ↦ (E.upperHalfPlaneMapOfLanding r hmaps w : ℂ)) =ᶠ[nhds z]
      E.toLocalProjectiveDevelopingMap.affineMap := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact E.upperHalfPlaneMapOfLanding_eq_affine hmaps hw

/--
The explicit upper-half-plane lift is `C^3` on the landing ball whenever the
underlying affine normal-form branch is `C^3` there.
-/
theorem upperHalfPlaneMapOfLanding_contDiffOn_of_affineMap_contDiffOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {r : ℝ}
    (hmaps :
      ∀ z, z ∈ Metric.ball z₀ r →
        0 < (E.toLocalProjectiveDevelopingMap.affineMap z).im)
    (hF :
      ContDiffOn ℝ 3 E.toLocalProjectiveDevelopingMap.affineMap
        (Metric.ball z₀ r)) :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (E.upperHalfPlaneMapOfLanding r hmaps z : ℂ))
      (Metric.ball z₀ r) :=
  hF.congr (by
    intro z hz
    exact E.upperHalfPlaneMapOfLanding_eq_affine hmaps hz)

end LocalProjectiveNormalFormPostcompositionExplicitData

/--
The remaining derivative-identification data for an explicit normal-form
branch restricted to a ball.

The actual `ℍ`-valued lift is constructed from the landing proof; this
structure only records that the symbolic projective derivative agrees with the
actual complex derivative of the affine normal-form branch.
-/
structure LocalProjectiveNormalFormDerivativeIdentificationData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (r : ℝ) where
  /-- The normal-form affine branch has the expected actual derivative on the ball. -/
  affineMap_hasDerivAt :
    ∀ z, z ∈ Metric.ball z₀ r →
      HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
        (E.toLocalProjectiveDevelopingMap.affineMapDeriv z) z
  /-- The symbolic projective derivative is the actual derivative on the ball. -/
  deriv_eq_projectiveDeriv :
    ∀ z, z ∈ Metric.ball z₀ r →
      deriv E.toLocalProjectiveDevelopingMap.affineMap z =
        E.toLocalProjectiveDevelopingMap.affineMapDeriv z

/--
Derivative-identification data through the first derivative branch for an
explicit normal-form branch restricted to a ball.

This is the normal-form part of the higher pullback boundary: the Mobius
postcomposition chain rule is proved, so the remaining hypotheses can be
placed on the original affine branch and its first symbolic derivative.
-/
structure LocalProjectiveNormalFormSecondDerivativeIdentificationData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (r : ℝ) where
  /-- The normal-form affine branch has the expected actual derivative on the ball. -/
  affineMap_hasDerivAt :
    ∀ z, z ∈ Metric.ball z₀ r →
      HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
        (E.toLocalProjectiveDevelopingMap.affineMapDeriv z) z
  /-- The symbolic projective derivative is the actual derivative on the ball. -/
  deriv_eq_projectiveDeriv :
    ∀ z, z ∈ Metric.ball z₀ r →
      deriv E.toLocalProjectiveDevelopingMap.affineMap z =
        E.toLocalProjectiveDevelopingMap.affineMapDeriv z
  /-- The symbolic second derivative is the actual derivative of the first one. -/
  deriv_affineMapDeriv_eq_secondDeriv :
    ∀ z, z ∈ Metric.ball z₀ r →
      deriv (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w) z =
        E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv z

/--
Derivative-identification data through the second derivative branch for an
explicit normal-form branch restricted to a ball.

This is the part needed by the pullback calculation through the explicit
second Wirtinger expression: the normal-form chain rule is proved, provided
the stored third derivative is the explicit normal-form third derivative on
the ball.
-/
structure LocalProjectiveNormalFormThirdDerivativeIdentificationData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (r : ℝ) where
  /-- The normal-form affine branch has the expected actual derivative on the ball. -/
  affineMap_hasDerivAt :
    ∀ z, z ∈ Metric.ball z₀ r →
      HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
        (E.toLocalProjectiveDevelopingMap.affineMapDeriv z) z
  /-- The symbolic projective derivative is the actual derivative on the ball. -/
  deriv_eq_projectiveDeriv :
    ∀ z, z ∈ Metric.ball z₀ r →
      deriv E.toLocalProjectiveDevelopingMap.affineMap z =
        E.toLocalProjectiveDevelopingMap.affineMapDeriv z
  /-- The symbolic second derivative is the actual derivative of the first one. -/
  deriv_affineMapDeriv_eq_secondDeriv :
    ∀ z, z ∈ Metric.ball z₀ r →
      deriv (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w) z =
        E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv z
  /-- The symbolic third derivative is the actual derivative of the second one. -/
  deriv_affineMapSecondDeriv_eq_thirdDeriv :
    ∀ z, z ∈ Metric.ball z₀ r →
      deriv (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) z =
        E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z

namespace LocalProjectiveNormalFormSecondDerivativeIdentificationData

/-- Forget the second derivative identification, retaining the first one. -/
def toDerivativeIdentificationData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    {E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target}
    {r : ℝ}
    (A : LocalProjectiveNormalFormSecondDerivativeIdentificationData E r) :
    LocalProjectiveNormalFormDerivativeIdentificationData E r where
  affineMap_hasDerivAt := A.affineMap_hasDerivAt
  deriv_eq_projectiveDeriv := A.deriv_eq_projectiveDeriv

end LocalProjectiveNormalFormSecondDerivativeIdentificationData

namespace LocalProjectiveNormalFormThirdDerivativeIdentificationData

/-- Forget the third derivative identification, retaining data through `F'`. -/
def toSecondDerivativeIdentificationData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    {E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target}
    {r : ℝ}
    (A : LocalProjectiveNormalFormThirdDerivativeIdentificationData E r) :
    LocalProjectiveNormalFormSecondDerivativeIdentificationData E r where
  affineMap_hasDerivAt := A.affineMap_hasDerivAt
  deriv_eq_projectiveDeriv := A.deriv_eq_projectiveDeriv
  deriv_affineMapDeriv_eq_secondDeriv := A.deriv_affineMapDeriv_eq_secondDeriv

/-- Forget to the first derivative-identification package. -/
def toDerivativeIdentificationData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    {E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target}
    {r : ℝ}
    (A : LocalProjectiveNormalFormThirdDerivativeIdentificationData E r) :
    LocalProjectiveNormalFormDerivativeIdentificationData E r :=
  A.toSecondDerivativeIdentificationData.toDerivativeIdentificationData

end LocalProjectiveNormalFormThirdDerivativeIdentificationData

namespace LocalProjectiveNormalFormPostcompositionExplicitData

/--
Actual first and second derivative statements for the original affine branch
give derivative-identification data through the first derivative branch for
the explicit normal-form postcomposition.
-/
def secondDerivativeIdentificationDataOfOriginalHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {r : ℝ}
    (hsubset : Metric.ball z₀ r ⊆ E.domain)
    (hD :
      ∀ z, z ∈ Metric.ball z₀ r →
        HasDerivAt D.affineMap (D.affineMapDeriv z) z)
    (hD' :
      ∀ z, z ∈ Metric.ball z₀ r →
        HasDerivAt (fun w : ℂ ↦ D.affineMapDeriv w)
          (D.affineMapSecondDeriv z) z) :
    LocalProjectiveNormalFormSecondDerivativeIdentificationData E r where
  affineMap_hasDerivAt := by
    intro z hz
    exact E.affineMap_hasDerivAt_of_original
      (hsubset hz) (hD z hz)
  deriv_eq_projectiveDeriv := by
    intro z hz
    exact E.deriv_eq_affineMapDeriv_of_original_hasDerivAt
      (hsubset hz) (hD z hz)
  deriv_affineMapDeriv_eq_secondDeriv := by
    intro z hz
    exact E.deriv_affineMapDeriv_eq_affineMapSecondDeriv_of_original_hasDerivAt
      (hsubset hz) (hD z hz) (hD' z hz)

/--
Actual derivatives through the second derivative branch, plus identification
of the stored third derivative with the explicit normal-form third derivative,
give derivative-identification data through the second derivative branch.
-/
def thirdDerivativeIdentificationDataOfOriginalHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {r : ℝ}
    (hsubset : Metric.ball z₀ r ⊆ E.domain)
    (hthird :
      ∀ z, z ∈ Metric.ball z₀ r →
        E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z =
          (D.normalFormPostcompositionAffineMapThirdDeriv hz₀ target) z)
    (hD :
      ∀ z, z ∈ Metric.ball z₀ r →
        HasDerivAt D.affineMap (D.affineMapDeriv z) z)
    (hD' :
      ∀ z, z ∈ Metric.ball z₀ r →
        HasDerivAt (fun w : ℂ ↦ D.affineMapDeriv w)
          (D.affineMapSecondDeriv z) z)
    (hD'' :
      ∀ z, z ∈ Metric.ball z₀ r →
        HasDerivAt (fun w : ℂ ↦ D.affineMapSecondDeriv w)
          (D.affineMapThirdDeriv z) z) :
    LocalProjectiveNormalFormThirdDerivativeIdentificationData E r where
  affineMap_hasDerivAt := by
    intro z hz
    exact E.affineMap_hasDerivAt_of_original
      (hsubset hz) (hD z hz)
  deriv_eq_projectiveDeriv := by
    intro z hz
    exact E.deriv_eq_affineMapDeriv_of_original_hasDerivAt
      (hsubset hz) (hD z hz)
  deriv_affineMapDeriv_eq_secondDeriv := by
    intro z hz
    exact E.deriv_affineMapDeriv_eq_affineMapSecondDeriv_of_original_hasDerivAt
      (hsubset hz) (hD z hz) (hD' z hz)
  deriv_affineMapSecondDeriv_eq_thirdDeriv := by
    intro z hz
    exact E.deriv_affineMapSecondDeriv_eq_affineMapThirdDeriv_of_original_hasDerivAt
      (hsubset hz) (hD z hz) (hD' z hz) (hD'' z hz) (hthird z hz)

end LocalProjectiveNormalFormPostcompositionExplicitData

/--
The remaining analytic lift data for turning an explicit finite normal-form
branch, restricted to an upper-half-plane landing ball, into an actual
`ℍ`-valued projective normalization.

The actual `ℍ`-valued map can now be constructed from the landing proof; this
structure is retained as the bundled output needed by downstream
normalization code.
-/
structure LocalProjectiveNormalFormUpperHalfPlaneLiftData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    (r : ℝ) where
  /-- The explicit branch, regarded as an upper-half-plane-valued map. -/
  upperHalfPlaneMap : ℂ → ℍ
  /-- The `ℍ`-valued map agrees with the restricted affine coordinate. -/
  upperHalfPlaneMap_eq_affine :
    ∀ z, z ∈ Metric.ball z₀ r →
      (upperHalfPlaneMap z : ℂ) = E.toLocalProjectiveDevelopingMap.affineMap z
  /-- The symbolic projective derivative is the actual derivative. -/
  deriv_eq_projectiveDeriv :
    ∀ z, z ∈ Metric.ball z₀ r →
      deriv E.toLocalProjectiveDevelopingMap.affineMap z =
        E.toLocalProjectiveDevelopingMap.affineMapDeriv z
  /-- The `ℍ`-valued branch has the expected actual derivative. -/
  upperHalfPlaneMap_hasDerivAt :
    ∀ z, z ∈ Metric.ball z₀ r →
      HasDerivAt (fun w : ℂ ↦ (upperHalfPlaneMap w : ℂ))
        (E.toLocalProjectiveDevelopingMap.affineMapDeriv z) z
  /-- The actual derivative of the `ℍ`-valued branch is the projective derivative. -/
  upperHalfPlane_deriv_eq_projectiveDeriv :
    ∀ z, z ∈ Metric.ball z₀ r →
      deriv (fun w : ℂ ↦ (upperHalfPlaneMap w : ℂ)) z =
        E.toLocalProjectiveDevelopingMap.affineMapDeriv z

namespace LocalProjectiveNormalFormPostcompositionExplicitData

/--
Derivative-identification data plus the landing proof produce the full
upper-half-plane lift data.
-/
noncomputable def liftDataOfDerivativeIdentification
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (E : LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target)
    {r : ℝ}
    (hmaps :
      ∀ z, z ∈ Metric.ball z₀ r →
        0 < (E.toLocalProjectiveDevelopingMap.affineMap z).im)
    (A : LocalProjectiveNormalFormDerivativeIdentificationData E r) :
    LocalProjectiveNormalFormUpperHalfPlaneLiftData E r where
  upperHalfPlaneMap := E.upperHalfPlaneMapOfLanding r hmaps
  upperHalfPlaneMap_eq_affine := by
    intro z hz
    exact E.upperHalfPlaneMapOfLanding_eq_affine hmaps hz
  deriv_eq_projectiveDeriv := A.deriv_eq_projectiveDeriv
  upperHalfPlaneMap_hasDerivAt := by
    intro z hz
    exact (A.affineMap_hasDerivAt z hz).congr_of_eventuallyEq
      (E.upperHalfPlaneMapOfLanding_eventuallyEq_affine hmaps hz)
  upperHalfPlane_deriv_eq_projectiveDeriv := by
    intro z hz
    exact ((A.affineMap_hasDerivAt z hz).congr_of_eventuallyEq
      (E.upperHalfPlaneMapOfLanding_eventuallyEq_affine hmaps hz)).deriv

end LocalProjectiveNormalFormPostcompositionExplicitData

namespace LocalProjectiveNormalFormPoleAvoidingShrink

/--
A pole-avoiding shrink plus the Schwarzian-invariance calculation gives the
explicit normal-form postcomposition data.
-/
def toExplicitData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (P : LocalProjectiveNormalFormPoleAvoidingShrink D z₀ hz₀ target)
    (affineMapThirdDeriv : ℂ → ℂ)
    (hschwarzian :
      ∀ z, z ∈ P.domain →
        schwarzianExpression
            (D.normalFormPostcompositionAffineMapDeriv hz₀ target)
            (D.normalFormPostcompositionAffineMapSecondDeriv hz₀ target)
            affineMapThirdDeriv z =
          S.coefficient z) :
    LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target where
  domain := P.domain
  isOpen_domain := P.isOpen_domain
  domain_subset_original := P.domain_subset_original
  base_mem := P.base_mem
  denominator_ne_zero := P.denominator_ne_zero
  affineMapThirdDeriv := affineMapThirdDeriv
  schwarzian_eq_coefficient := hschwarzian

/--
A pole-avoiding shrink gives the canonical explicit normal-form
postcomposition data, with the stored third derivative fixed to the explicit
normal-form chain-rule expression.
-/
def toCanonicalExplicitData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (P : LocalProjectiveNormalFormPoleAvoidingShrink D z₀ hz₀ target) :
    LocalProjectiveNormalFormPostcompositionExplicitData D z₀ hz₀ target :=
  P.toExplicitData
    (D.normalFormPostcompositionAffineMapThirdDeriv hz₀ target)
    (by
      intro w hw
      calc
        schwarzianExpression
            (D.normalFormPostcompositionAffineMapDeriv hz₀ target)
            (D.normalFormPostcompositionAffineMapSecondDeriv hz₀ target)
            (D.normalFormPostcompositionAffineMapThirdDeriv hz₀ target) w
            =
              schwarzianExpression D.affineMapDeriv D.affineMapSecondDeriv
                D.affineMapThirdDeriv w :=
              D.schwarzianExpression_normalFormPostcomposition_eq hz₀
                (P.domain_subset_original hw) target (P.denominator_ne_zero w hw)
        _ = S.coefficient w :=
              D.schwarzian_eq_coefficient w (P.domain_subset_original hw))

/-- The canonical explicit data stores the explicit normal-form third derivative. -/
theorem toCanonicalExplicitData_affineMapThirdDeriv_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {target : NondegenerateFiniteTwoJet}
    (P : LocalProjectiveNormalFormPoleAvoidingShrink D z₀ hz₀ target)
    (z : ℂ) :
    P.toCanonicalExplicitData.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z =
      (D.normalFormPostcompositionAffineMapThirdDeriv hz₀ target) z :=
  rfl

end LocalProjectiveNormalFormPoleAvoidingShrink

/--
An upper-half-plane-valued Mobius normalization candidate for a local
projective Schwarzian solution.

This records the postcomposition and the `ℍ`-valued branch, but not yet the
Poincare pullback formula.  The metric-recovery formula is deliberately a
separate theorem target below, driven by the hyperbolic 2-jet normalization.
-/
structure LocalUpperHalfPlaneProjectiveNormalization {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} (D : LocalProjectiveDevelopingMap S) where
  /-- The normalized finite projective map after Mobius postcomposition. -/
  projective : LocalProjectiveDevelopingMap S
  /-- The same affine coordinate, now regarded as upper-half-plane-valued. -/
  upperHalfPlaneMap : ℂ → ℍ
  /-- The upper-half-plane branch agrees with the affine projective coordinate. -/
  upperHalfPlaneMap_eq_affine :
    ∀ z, z ∈ projective.domain → (upperHalfPlaneMap z : ℂ) = projective.affineMap z
  /-- The upper-half-plane branch is holomorphic on the local domain. -/
  holomorphic_on_domain :
    LocalUpperHalfPlaneMapHolomorphicOn projective.domain upperHalfPlaneMap
  /-- The symbolic derivative in the projective package is the actual derivative. -/
  deriv_eq_projectiveDeriv :
    ∀ z, z ∈ projective.domain → deriv projective.affineMap z = projective.affineMapDeriv z
  /-- The actual derivative of the upper-half-plane branch is the projective derivative. -/
  upperHalfPlane_deriv_eq_projectiveDeriv :
    ∀ z, z ∈ projective.domain →
      deriv (fun w : ℂ ↦ (upperHalfPlaneMap w : ℂ)) z = projective.affineMapDeriv z
  /-- Mobius postcomposition used to normalize the original projective map. -/
  postcomposition : MobiusRepresentative
  /-- The normalized domain is a shrink of the original projective solution domain. -/
  domain_subset_original : projective.domain ⊆ D.domain
  /-- The normalized projective map is the Mobius postcomposition of the original map. -/
  projective_eq_postcompose_original :
    ∀ z, z ∈ projective.domain →
      projective.projectiveMap z = postcomposition • D.projectiveMap z

namespace LocalUpperHalfPlaneProjectiveNormalization

/-- The domain of an upper-half-plane-valued projective normalization candidate. -/
def domain {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S}
    (N : LocalUpperHalfPlaneProjectiveNormalization D) : Set ℂ :=
  N.projective.domain

/-- The complex-valued normalized upper-half-plane branch is differentiable at domain points. -/
theorem differentiableAt_upperHalfPlaneMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S}
    (N : LocalUpperHalfPlaneProjectiveNormalization D) {z : ℂ}
    (hz : z ∈ N.domain) :
    DifferentiableAt ℂ (fun w : ℂ ↦ (N.upperHalfPlaneMap w : ℂ)) z :=
  N.holomorphic_on_domain z hz

/-- Upgrade a normalization candidate to a metric-recovering branch once the density formula is known. -/
def toLocalUpperHalfPlaneDevelopingMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S}
    (N : LocalUpperHalfPlaneProjectiveNormalization D)
    (hDensity :
      ∀ z, z ∈ N.domain →
        u.densitySq z =
          Complex.normSq (N.projective.affineMapDeriv z) /
            ((N.upperHalfPlaneMap z : ℂ).im ^ 2)) :
    LocalUpperHalfPlaneDevelopingMap S where
  projective := N.projective
  upperHalfPlaneMap := N.upperHalfPlaneMap
  upperHalfPlaneMap_eq_affine := N.upperHalfPlaneMap_eq_affine
  holomorphic_on_domain := N.holomorphic_on_domain
  deriv_eq_projectiveDeriv := N.deriv_eq_projectiveDeriv
  upperHalfPlane_deriv_eq_projectiveDeriv := N.upperHalfPlane_deriv_eq_projectiveDeriv
  densitySq_eq_pullback := hDensity

end LocalUpperHalfPlaneProjectiveNormalization

/--
A Mobius normalization candidate satisfying the prescribed hyperbolic 2-jet at
the base point.
-/
structure LocalHyperbolicTwoJetUpperHalfPlaneNormalization
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) (z₀ : ℂ) where
  /-- The prescribed hyperbolic base jet. -/
  jet : HyperbolicSchwarzianBaseJet u z₀
  /-- The upper-half-plane-valued Mobius normalization candidate. -/
  normalized : LocalUpperHalfPlaneProjectiveNormalization D
  /-- The base point lies in the normalized domain. -/
  base_mem : z₀ ∈ normalized.domain
  /--
  The normalized branch has already been shrunk to a complex metric ball.

  This is part of the branch-selection construction, not a later analytic
  uniqueness input: once the `ℍ`-valued normalization is found on an open
  neighborhood of the base point, shrink it to a ball before packaging it here.
  -/
  domain_eq_ball : ∃ c r, normalized.domain = Metric.ball c r
  /-- The normalized branch sends the base point to `i`. -/
  value_eq :
    (normalized.upperHalfPlaneMap z₀ : ℂ) = jet.targetValue
  /-- The normalized first derivative is `exp (u z₀)`, as a positive real. -/
  firstDeriv_eq :
    normalized.projective.affineMapDeriv z₀ = jet.targetDeriv
  /-- The normalized second derivative matches the hyperbolic 2-jet formula. -/
  secondDeriv_eq :
    normalized.projective.affineMapSecondDeriv z₀ = jet.targetSecondDeriv

namespace LocalHyperbolicTwoJetUpperHalfPlaneNormalization

/-- The normalized domain. -/
def domain {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Set ℂ :=
  N.normalized.domain

/-- The normalization's base-jet derivative is the canonical derivative of `u`. -/
theorem jet_uZ_eq_wirtingerZ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) :
    N.jet.uZ = u.wirtingerZ z₀ :=
  N.jet.uZ_eq_wirtingerZ

/-- The canonical Poincare pullback squared density of the normalized branch. -/
def pullbackDensitySq {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) (z : ℂ) : ℝ :=
  Complex.normSq (N.normalized.projective.affineMapDeriv z) /
    ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2)

/--
The canonical logarithmic density for the Poincare pullback.

This is the squared-density-friendly representative
`(1 / 2) log (|F'|² / (Im F)²)`, equivalent to
`log |F'| - log Im(F)` when expanded.
-/
def pullbackLogDensity {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) (z : ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (N.pullbackDensitySq z)

/-- The upper-half-plane branch has positive imaginary part everywhere. -/
theorem upperHalfPlaneMap_im_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) (z : ℂ) :
    0 < (N.normalized.upperHalfPlaneMap z : ℂ).im :=
  (N.normalized.upperHalfPlaneMap z).im_pos

/-- The Poincare denominator is positive for the normalized branch. -/
theorem upperHalfPlaneMap_im_sq_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) (z : ℂ) :
    0 < (N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2 :=
  sq_pos_of_pos (N.upperHalfPlaneMap_im_pos z)

/-- The normalized projective derivative has positive squared norm on the domain. -/
theorem affineDerivativeNormSq_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {z : ℂ} (hz : z ∈ N.domain) :
    0 < Complex.normSq (N.normalized.projective.affineMapDeriv z) :=
  Complex.normSq_pos.mpr (N.normalized.projective.affineMapDeriv_ne_zero z hz)

/-- The canonical Poincare pullback squared density is positive on the domain. -/
theorem pullbackDensitySq_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {z : ℂ} (hz : z ∈ N.domain) :
    0 < N.pullbackDensitySq z := by
  exact div_pos (N.affineDerivativeNormSq_pos hz) (N.upperHalfPlaneMap_im_sq_pos z)

/--
The canonical logarithmic pullback density exponentiates to the Poincare
pullback squared density.
-/
theorem exp_two_pullbackLogDensity_eq_pullbackDensitySq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {z : ℂ} (hz : z ∈ N.domain) :
    Real.exp (2 * N.pullbackLogDensity z) = N.pullbackDensitySq z := by
  have hpos : 0 < N.pullbackDensitySq z := N.pullbackDensitySq_pos hz
  have htwo :
      2 * ((1 / 2 : ℝ) * Real.log (N.pullbackDensitySq z)) =
        Real.log (N.pullbackDensitySq z) := by
    ring
  rw [pullbackLogDensity, htwo, Real.exp_log hpos]

/--
At the normalized base point, the canonical Poincare pullback squared density
matches the original conformal squared density.

This is only the algebra of the prescribed hyperbolic two-jet:
`F(z₀)=i`, `F'(z₀)=exp(u(z₀))`.
-/
theorem pullbackDensitySq_base_eq_densitySq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) :
    N.pullbackDensitySq z₀ = u.densitySq z₀ := by
  rw [pullbackDensitySq]
  rw [N.firstDeriv_eq, N.value_eq]
  simp only [HyperbolicSchwarzianBaseJet.targetDeriv,
    HyperbolicSchwarzianBaseJet.targetValue, LocalConformalFactor.densitySq,
    Complex.I_im, one_pow, div_one]
  rw [Complex.normSq_ofReal]
  rw [← Real.exp_add]
  ring_nf

/--
At the normalized base point, the canonical logarithmic pullback density has
the same squared density as the original conformal factor.
-/
theorem exp_two_pullbackLogDensity_base_eq_densitySq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) :
    Real.exp (2 * N.pullbackLogDensity z₀) = u.densitySq z₀ := by
  rw [N.exp_two_pullbackLogDensity_eq_pullbackDensitySq N.base_mem,
    N.pullbackDensitySq_base_eq_densitySq]

/--
The canonical logarithmic pullback density itself agrees with the original
log-density at the normalized base point.
-/
theorem pullbackLogDensity_base_eq_logDensity
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) :
    N.pullbackLogDensity z₀ = u.logDensity z₀ := by
  have hExp :
      Real.exp (2 * N.pullbackLogDensity z₀) =
        Real.exp (2 * u.logDensity z₀) := by
    simpa [LocalConformalFactor.densitySq] using
      N.exp_two_pullbackLogDensity_base_eq_densitySq
  have hTwo :
      2 * N.pullbackLogDensity z₀ = 2 * u.logDensity z₀ :=
    Real.exp_injective hExp
  linarith

/--
The normalized hyperbolic two-jet recovers the prescribed canonical
Wirtinger derivative from the first two derivatives of the normalized branch.

Classically, for an `ℍ`-valued local isometry one has at the normalized base
point
`v_z = (F'' / F' + i F') / 2`.  This theorem proves the purely algebraic
two-jet part: after substituting the prescribed hyperbolic second derivative,
that expression is exactly the base jet field `N.jet.uZ`.
-/
theorem base_uZ_eq_of_twoJet_formula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) :
    (N.normalized.projective.affineMapSecondDeriv z₀ /
        N.normalized.projective.affineMapDeriv z₀ +
      Complex.I * N.normalized.projective.affineMapDeriv z₀) / 2 = N.jet.uZ := by
  have hderiv_ne : N.jet.targetDeriv ≠ 0 := N.jet.targetDeriv_ne_zero
  rw [N.secondDeriv_eq, N.firstDeriv_eq]
  rw [HyperbolicSchwarzianBaseJet.targetSecondDeriv]
  field_simp [hderiv_ne]
  ring

/--
The numerator part of the canonical pullback squared-density derivative at the
base point.

For the intended holomorphic branch this is the calculation
`∂z |F'|² = |F'|² * F'' / F'` at the normalized base point, using that
`F'(z₀)` is a positive real.
-/
def PullbackDensitySqBaseNumeratorDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Prop :=
  frechetDZValue
      (fun z : ℂ ↦ (Complex.normSq (N.normalized.projective.affineMapDeriv z) : ℂ)) z₀ =
    (Complex.normSq (N.normalized.projective.affineMapDeriv z₀) : ℂ) *
      (N.normalized.projective.affineMapSecondDeriv z₀ /
        N.normalized.projective.affineMapDeriv z₀)

/--
A genuine complex derivative for the derivative branch implies
differentiability of the numerator `|F'|²` at the base point.
-/
theorem numerator_differentiableAt_base_of_affineMapDeriv_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF' :
      HasDerivAt (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z)
        (N.normalized.projective.affineMapSecondDeriv z₀) z₀) :
    DifferentiableAt ℝ
      (fun z : ℂ ↦ Complex.normSq (N.normalized.projective.affineMapDeriv z)) z₀ := by
  have hFR : DifferentiableAt ℝ
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) z₀ :=
    hF'.complexToReal_fderiv.differentiableAt
  simpa [Complex.normSq_apply] using
    ((Complex.reCLM.differentiableAt.comp z₀ hFR).mul
        (Complex.reCLM.differentiableAt.comp z₀ hFR)).add
      ((Complex.imCLM.differentiableAt.comp z₀ hFR).mul
        (Complex.imCLM.differentiableAt.comp z₀ hFR))

/--
A genuine complex derivative for the derivative branch implies the numerator
derivative formula.
-/
theorem numerator_base_derivative_formula_of_affineMapDeriv_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF' :
      HasDerivAt (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z)
        (N.normalized.projective.affineMapSecondDeriv z₀) z₀) :
    N.PullbackDensitySqBaseNumeratorDerivativeFormula := by
  rw [PullbackDensitySqBaseNumeratorDerivativeFormula]
  rw [frechetDZValue_complex_ofReal_normSq_of_hasDerivAt hF']
  rw [N.firstDeriv_eq]
  have hDeriv_ne : N.jet.targetDeriv ≠ 0 := N.jet.targetDeriv_ne_zero
  have hStar : star N.jet.targetDeriv = N.jet.targetDeriv := by
    dsimp [HyperbolicSchwarzianBaseJet.targetDeriv]
    apply Complex.ext <;> simp
  have hNorm :
      (Complex.normSq N.jet.targetDeriv : ℂ) = N.jet.targetDeriv * N.jet.targetDeriv := by
    change ((Complex.normSq (Real.exp (u.logDensity z₀) : ℂ) : ℝ) : ℂ) =
      (Real.exp (u.logDensity z₀) : ℂ) * (Real.exp (u.logDensity z₀) : ℂ)
    rw [Complex.normSq_ofReal]
    norm_num
  rw [hStar, hNorm]
  field_simp [hDeriv_ne]

/--
The denominator part of the canonical pullback squared-density derivative at
the base point.

For the intended holomorphic branch this is the calculation
`∂z (Im F)^2 = -i F'` at `F(z₀)=i`.
-/
def PullbackDensitySqBaseDenominatorDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Prop :=
  frechetDZValue
      (fun z : ℂ ↦ (((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2 : ℝ) : ℂ)) z₀ =
    -Complex.I * N.normalized.projective.affineMapDeriv z₀

/--
A genuine complex derivative for the upper-half-plane branch implies
differentiability of the denominator `(Im F)^2` at the base point.
-/
theorem denominator_differentiableAt_base_of_upperHalfPlaneMap_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      HasDerivAt (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ))
        (N.normalized.projective.affineMapDeriv z₀) z₀) :
    DifferentiableAt ℝ
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2) z₀ := by
  have hFR : DifferentiableAt ℝ (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) z₀ :=
    hF.complexToReal_fderiv.differentiableAt
  simpa [Function.comp_apply, Complex.imCLM_apply, pow_two] using
    ((Complex.imCLM.differentiableAt.comp z₀ hFR).mul
      (Complex.imCLM.differentiableAt.comp z₀ hFR))

/--
A genuine complex derivative for the upper-half-plane branch implies the
denominator derivative formula.
-/
theorem denominator_base_derivative_formula_of_upperHalfPlaneMap_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      HasDerivAt (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ))
        (N.normalized.projective.affineMapDeriv z₀) z₀) :
    N.PullbackDensitySqBaseDenominatorDerivativeFormula := by
  rw [PullbackDensitySqBaseDenominatorDerivativeFormula]
  exact frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt hF
    (by
      rw [N.value_eq]
      simp [HyperbolicSchwarzianBaseJet.targetValue])

/--
Smoothness of the derivative branch gives smoothness of the numerator
`|F'|²`.
-/
theorem numerator_contDiffOn_of_affineMapDeriv_contDiffOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain) :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ Complex.normSq (N.normalized.projective.affineMapDeriv z))
        N.domain := by
  have hRe : ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.projective.affineMapDeriv z).re) N.domain := by
    simpa [Function.comp_apply, Complex.reCLM_apply] using
      (Complex.reCLM.contDiff.comp_contDiffOn hF')
  have hIm : ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.projective.affineMapDeriv z).im) N.domain := by
    simpa [Function.comp_apply, Complex.imCLM_apply] using
      (Complex.imCLM.contDiff.comp_contDiffOn hF')
  simpa [Complex.normSq_apply] using hRe.mul hRe |>.add (hIm.mul hIm)

/--
Smoothness of the upper-half-plane branch gives smoothness of the denominator
`(Im F)²`.
-/
theorem denominator_contDiffOn_of_upperHalfPlaneMap_contDiffOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain) :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2) N.domain := by
  have hIm : ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ).im) N.domain := by
    simpa [Function.comp_apply, Complex.imCLM_apply] using
      (Complex.imCLM.contDiff.comp_contDiffOn hF)
  simpa [pow_two] using hIm.mul hIm

/--
Smoothness of the two branch ingredients gives smoothness of the Poincare
pullback squared density.
-/
theorem pullbackDensitySq_contDiffOn_of_branch_contDiffOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain) :
    ContDiffOn ℝ 3 N.pullbackDensitySq N.domain := by
  have hNum := N.numerator_contDiffOn_of_affineMapDeriv_contDiffOn hF'
  have hDen := N.denominator_contDiffOn_of_upperHalfPlaneMap_contDiffOn hF
  have hDen_ne :
      ∀ z, z ∈ N.domain → (N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2 ≠ 0 := by
    intro z _hz
    exact (N.upperHalfPlaneMap_im_sq_pos z).ne'
  simpa [pullbackDensitySq] using hNum.fun_div hDen hDen_ne

/--
Smoothness of the two branch ingredients gives smoothness of the canonical
logarithmic Poincare pullback density.
-/
theorem pullbackLogDensity_contDiffOn_of_branch_contDiffOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain) :
    ContDiffOn ℝ 3 N.pullbackLogDensity N.domain := by
  have hρ := N.pullbackDensitySq_contDiffOn_of_branch_contDiffOn hF hF'
  have hlog :
      ContDiffOn ℝ 3 (fun z : ℂ ↦ Real.log (N.pullbackDensitySq z)) N.domain :=
    hρ.log (by
      intro z hz
      exact (N.pullbackDensitySq_pos hz).ne')
  change ContDiffOn ℝ 3
    (fun z : ℂ ↦ (1 / 2 : ℝ) * Real.log (N.pullbackDensitySq z)) N.domain
  simpa using
    (ContDiffOn.const_smul (1 / 2 : ℝ) hlog)

/-- The concrete `C^2` regularity proposition for the canonical pullback log-density. -/
def PullbackLogDensityTwiceDifferentiable
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Prop :=
  ContDiffOn ℝ 2 N.pullbackLogDensity N.domain

/--
The local conformal factor determined by the canonical Poincare pullback
log-density, once branch smoothness supplies the `C^3` field.
-/
def pullbackConformalFactor
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain)
    (_twice_differentiable_on_domain : Prop) :
    LocalConformalFactor where
  coordinateDomain := N.domain
  isOpen_coordinateDomain := by
    simpa [domain, LocalUpperHalfPlaneProjectiveNormalization.domain] using
      N.normalized.projective.isOpen_domain
  logDensity := N.pullbackLogDensity
  logDensity_contDiffOn := N.pullbackLogDensity_contDiffOn_of_branch_contDiffOn hF hF'
  twice_differentiable_on_domain :=
    (N.pullbackLogDensity_contDiffOn_of_branch_contDiffOn hF hF').of_le (by norm_num)

/--
The precise Schwarzian-compatibility proposition for the canonical Poincare
pullback factor.

This is the remaining Schwarzian calculation in fixed form:
the metric Schwarzian coefficient of
`v = (1 / 2) log (|F'|² / (Im F)²)` must agree with the original coefficient.
-/
def PullbackSchwarzianCompatibility
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain)
    (twice_differentiable_on_domain : Prop) : Prop :=
  ∀ z, z ∈ N.domain →
    LocalSchwarzianData.metricSchwarzianCoefficient
      ((N.pullbackConformalFactor hF hF' twice_differentiable_on_domain).halfSchwarzianCoefficient)
        z =
      S.coefficient z

/--
The core Schwarzian identity for the canonical Poincare pullback factor:
the metric Schwarzian of the pullback conformal factor equals the ordinary
Schwarzian expression of the branch.
-/
def PullbackMetricSchwarzianEqualsBranchSchwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain)
    (twice_differentiable_on_domain : Prop) : Prop :=
  ∀ z, z ∈ N.domain →
    LocalSchwarzianData.metricSchwarzianCoefficient
      ((N.pullbackConformalFactor hF hF' twice_differentiable_on_domain).halfSchwarzianCoefficient)
        z =
      schwarzianExpression
        N.normalized.projective.affineMapDeriv
        N.normalized.projective.affineMapSecondDeriv
        N.normalized.projective.affineMapThirdDeriv z

/--
The explicit right-hand side of the first Wirtinger derivative formula for
the canonical Poincare pullback log-density.
-/
def pullbackFirstWirtingerExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (z : ℂ) : ℂ :=
  (N.normalized.projective.affineMapSecondDeriv z /
      N.normalized.projective.affineMapDeriv z +
    Complex.I * N.normalized.projective.affineMapDeriv z /
      ((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ)) / 2

/--
The explicit right-hand side of the second Wirtinger derivative formula for
the canonical Poincare pullback log-density.
-/
def pullbackSecondWirtingerExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (z : ℂ) : ℂ :=
  (N.normalized.projective.affineMapThirdDeriv z /
      N.normalized.projective.affineMapDeriv z -
    (N.normalized.projective.affineMapSecondDeriv z /
      N.normalized.projective.affineMapDeriv z) ^ 2 +
    Complex.I * N.normalized.projective.affineMapSecondDeriv z /
      ((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ) -
    N.normalized.projective.affineMapDeriv z ^ 2 /
      (2 * ((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ) ^ 2)) / 2

/--
The first Wirtinger derivative formula for the canonical Poincare pullback
log-density.
-/
def PullbackFirstWirtingerFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain)
    (twice_differentiable_on_domain : Prop) : Prop :=
  ∀ z, z ∈ N.domain →
    (N.pullbackConformalFactor hF hF' twice_differentiable_on_domain).wirtingerZ z =
      N.pullbackFirstWirtingerExpression z

/--
The second Wirtinger derivative formula for the canonical Poincare pullback
log-density.
-/
def PullbackSecondWirtingerFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain)
    (twice_differentiable_on_domain : Prop) : Prop :=
  ∀ z, z ∈ N.domain →
    (N.pullbackConformalFactor hF hF' twice_differentiable_on_domain).wirtingerZZ z =
      N.pullbackSecondWirtingerExpression z

/--
Mixed-Wirtinger form of the Poincare pullback Laplacian identity.

For the canonical pullback conformal factor
`v = (1 / 2) log (|F'|² / (Im F)²)`, this states
`∂_{\bar z} ∂_z v = (1 / 4) |F'|² / (Im F)²`.
Together with the already-proved bridge
`∂_{\bar z} ∂_z v = (1 / 4) Δv`, it implies the real Laplacian formula.
-/
def PullbackMixedWirtingerLaplacianFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain)
    (twice_differentiable_on_domain : Prop) : Prop :=
  ∀ z, z ∈ N.domain →
    (N.pullbackConformalFactor hF hF' twice_differentiable_on_domain).wirtingerZBar z =
      (1 / 4 : ℂ) * (N.pullbackDensitySq z : ℂ)

/--
Local agreement of the first Wirtinger derivative with its explicit branch
expression.

This is the exact congruence input needed to replace a derivative of
`V.wirtingerZ` by a derivative of the closed-form expression.
-/
def PullbackFirstWirtingerEventuallyEqExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain)
    (hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain)
    (twice_differentiable_on_domain : Prop) : Prop :=
  ∀ z, z ∈ N.domain →
    (N.pullbackConformalFactor hF hF' twice_differentiable_on_domain).wirtingerZ
      =ᶠ[nhds z] N.pullbackFirstWirtingerExpression

/--
The remaining second-derivative pullback calculation, isolated as a Frechet
`∂z` derivative of the explicit first Wirtinger expression.
-/
def PullbackSecondWirtingerExpressionDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Prop :=
  ∀ z, z ∈ N.domain →
    frechetDZValue N.pullbackFirstWirtingerExpression z =
      N.pullbackSecondWirtingerExpression z

/--
Mixed-Wirtinger derivative calculation for the explicit first Poincare
pullback expression.

This is the remaining concrete calculation behind
`∂_{\bar z} ∂_z v = (1 / 4) |F'|² / (Im F)²`, after the first Wirtinger
formula has identified `v_z` with the explicit branch expression.
-/
def PullbackMixedWirtingerExpressionDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Prop :=
  ∀ z, z ∈ N.domain →
    frechetDBarValue N.pullbackFirstWirtingerExpression z =
      (1 / 4 : ℂ) * (N.pullbackDensitySq z : ℂ)

/-- Algebra for differentiating the explicit first pullback Wirtinger expression. -/
theorem pullbackSecondWirtingerExpressionDerivativeFormula_algebra
    (F₁ F₂ F₃ y : ℂ) (hF₁ : F₁ ≠ 0) (hy : y ≠ 0) :
    (((F₃ * F₁ - F₂ * F₂) / F₁ ^ 2) +
        Complex.I * ((F₂ * y - F₁ * (-Complex.I * F₁ / 2)) / y ^ 2)) / 2 =
      (F₃ / F₁ - (F₂ / F₁) ^ 2 + Complex.I * F₂ / y -
        F₁ ^ 2 / (2 * y ^ 2)) / 2 := by
  field_simp [hF₁, hy]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Algebra for the mixed derivative of the explicit first pullback expression. -/
theorem pullbackMixedWirtingerExpressionDerivativeFormula_algebra
    (F₁ y : ℂ) (hy : y ≠ 0) :
    (Complex.I * ((0 * y - F₁ * (Complex.I * star F₁ / 2)) / y ^ 2)) / 2 =
      (1 / 4 : ℂ) * ((Complex.normSq F₁ : ℂ) / y ^ 2) := by
  have hnorm : (Complex.normSq F₁ : ℂ) = star F₁ * F₁ := by
    simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := F₁))
  rw [hnorm]
  field_simp [hy]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/--
Actual derivative identities for `F`, `F'`, and `F''` imply the explicit
Frechet derivative formula for the first pullback Wirtinger expression.
-/
theorem pullbackSecondWirtingerExpressionDerivativeFormula_of_branch_hasDerivAt_on
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ∀ z, z ∈ N.domain →
        HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
          (N.normalized.projective.affineMapDeriv z) z)
    (hF' :
      ∀ z, z ∈ N.domain →
        HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
          (N.normalized.projective.affineMapSecondDeriv z) z)
    (hF'' :
      ∀ z, z ∈ N.domain →
        HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w)
          (N.normalized.projective.affineMapThirdDeriv z) z) :
    N.PullbackSecondWirtingerExpressionDerivativeFormula := by
  intro z hz
  let F : ℂ → ℂ := fun w ↦ (N.normalized.upperHalfPlaneMap w : ℂ)
  let F₁ : ℂ → ℂ := fun w ↦ N.normalized.projective.affineMapDeriv w
  let F₂ : ℂ → ℂ := fun w ↦ N.normalized.projective.affineMapSecondDeriv w
  let y : ℂ → ℂ := fun w ↦ (((F w).im : ℝ) : ℂ)
  have hFz : HasDerivAt F (F₁ z) z := by
    simpa [F, F₁] using hF z hz
  have hF₁z : HasDerivAt F₁ (F₂ z) z := by
    simpa [F₁, F₂] using hF' z hz
  have hF₂z :
      HasDerivAt F₂ (N.normalized.projective.affineMapThirdDeriv z) z := by
    simpa [F₂] using hF'' z hz
  have hF₁Diff : DifferentiableAt ℝ F₁ z :=
    hF₁z.complexToReal_fderiv.differentiableAt
  have hF₂Diff : DifferentiableAt ℝ F₂ z :=
    hF₂z.complexToReal_fderiv.differentiableAt
  have hyDiff : DifferentiableAt ℝ y z := by
    simpa [F, y] using differentiableAt_complex_ofReal_im_of_hasDerivAt hFz
  have hF₁nz : F₁ z ≠ 0 := by
    simpa [F₁] using N.normalized.projective.affineMapDeriv_ne_zero z hz
  have hynz : y z ≠ 0 := by
    have hpos : 0 < (F z).im := by
      simpa [F] using N.upperHalfPlaneMap_im_pos z
    simpa [y] using (show (((F z).im : ℂ) ≠ 0) from by
      exact_mod_cast hpos.ne')
  have hq :
      frechetDZValue (fun w : ℂ ↦ F₂ w / F₁ w) z =
        (N.normalized.projective.affineMapThirdDeriv z * F₁ z -
          F₂ z * F₂ z) / (F₁ z) ^ 2 := by
    rw [frechetDZValue_div_of_differentiableAt hF₂Diff hF₁Diff hF₁nz]
    rw [frechetDZValue_of_hasDerivAt hF₂z]
    rw [frechetDZValue_of_hasDerivAt hF₁z]
  have hyderiv :
      frechetDZValue y z = -Complex.I * F₁ z / 2 := by
    simpa [F, F₁, y] using frechetDZValue_complex_ofReal_im_of_hasDerivAt_general hFz
  have ht :
      frechetDZValue (fun w : ℂ ↦ Complex.I * F₁ w / y w) z =
        Complex.I * ((F₂ z * y z - F₁ z * (-Complex.I * F₁ z / 2)) / (y z) ^ 2) := by
    have hF₁divyDiff : DifferentiableAt ℝ (fun w : ℂ ↦ F₁ w / y w) z := by
      rw [show (fun w : ℂ ↦ F₁ w / y w) =
          (fun w : ℂ ↦ F₁ w * (y w)⁻¹) by
            ext w
            rw [div_eq_mul_inv]]
      exact hF₁Diff.mul (hyDiff.inv hynz)
    rw [show (fun w : ℂ ↦ Complex.I * F₁ w / y w) =
        (fun w : ℂ ↦ Complex.I * (F₁ w / y w)) by
          ext w
          rw [mul_div_assoc]]
    rw [frechetDZValue_const_mul_of_differentiableAt hF₁divyDiff]
    rw [frechetDZValue_div_of_differentiableAt hF₁Diff hyDiff hynz]
    rw [frechetDZValue_of_hasDerivAt hF₁z, hyderiv]
  have hsumDiff :
      DifferentiableAt ℝ (fun w : ℂ ↦ F₂ w / F₁ w + Complex.I * F₁ w / y w) z := by
    have hF₂divF₁Diff : DifferentiableAt ℝ (fun w : ℂ ↦ F₂ w / F₁ w) z := by
      rw [show (fun w : ℂ ↦ F₂ w / F₁ w) =
          (fun w : ℂ ↦ F₂ w * (F₁ w)⁻¹) by
            ext w
            rw [div_eq_mul_inv]]
      exact hF₂Diff.mul (hF₁Diff.inv hF₁nz)
    have hF₁divyDiff : DifferentiableAt ℝ (fun w : ℂ ↦ F₁ w / y w) z := by
      rw [show (fun w : ℂ ↦ F₁ w / y w) =
          (fun w : ℂ ↦ F₁ w * (y w)⁻¹) by
            ext w
            rw [div_eq_mul_inv]]
      exact hF₁Diff.mul (hyDiff.inv hynz)
    have hIF₁divyDiff : DifferentiableAt ℝ (fun w : ℂ ↦ Complex.I * F₁ w / y w) z := by
      rw [show (fun w : ℂ ↦ Complex.I * F₁ w / y w) =
          (fun w : ℂ ↦ Complex.I * (F₁ w / y w)) by
            ext w
            rw [mul_div_assoc]]
      exact hF₁divyDiff.const_mul Complex.I
    exact hF₂divF₁Diff.add hIF₁divyDiff
  rw [show N.pullbackFirstWirtingerExpression =
      (fun w : ℂ ↦ (F₂ w / F₁ w + Complex.I * F₁ w / y w) / 2) by
        ext w
        simp [pullbackFirstWirtingerExpression, F, F₁, F₂, y]]
  rw [show (fun w : ℂ ↦ (F₂ w / F₁ w + Complex.I * F₁ w / y w) / 2) =
      (fun w : ℂ ↦ (2 : ℂ)⁻¹ *
        (F₂ w / F₁ w + Complex.I * F₁ w / y w)) by
        ext w
        rw [div_eq_inv_mul]]
  rw [frechetDZValue_const_mul_of_differentiableAt hsumDiff]
  have hF₂divF₁Diff : DifferentiableAt ℝ (fun w : ℂ ↦ F₂ w / F₁ w) z := by
    rw [show (fun w : ℂ ↦ F₂ w / F₁ w) =
        (fun w : ℂ ↦ F₂ w * (F₁ w)⁻¹) by
          ext w
          rw [div_eq_mul_inv]]
    exact hF₂Diff.mul (hF₁Diff.inv hF₁nz)
  have hIF₁divyDiff : DifferentiableAt ℝ (fun w : ℂ ↦ Complex.I * F₁ w / y w) z := by
    rw [show (fun w : ℂ ↦ Complex.I * F₁ w / y w) =
        (fun w : ℂ ↦ Complex.I * (F₁ w / y w)) by
          ext w
          rw [mul_div_assoc]]
    have hF₁divyDiff : DifferentiableAt ℝ (fun w : ℂ ↦ F₁ w / y w) z := by
      rw [show (fun w : ℂ ↦ F₁ w / y w) =
          (fun w : ℂ ↦ F₁ w * (y w)⁻¹) by
            ext w
            rw [div_eq_mul_inv]]
      exact hF₁Diff.mul (hyDiff.inv hynz)
    exact hF₁divyDiff.const_mul Complex.I
  rw [frechetDZValue_add_of_differentiableAt
    hF₂divF₁Diff hIF₁divyDiff]
  rw [hq, ht]
  dsimp [pullbackSecondWirtingerExpression, F, F₁, F₂, y]
  rw [← div_eq_inv_mul]
  simpa using pullbackSecondWirtingerExpressionDerivativeFormula_algebra
    (N.normalized.projective.affineMapDeriv z)
    (N.normalized.projective.affineMapSecondDeriv z)
    (N.normalized.projective.affineMapThirdDeriv z)
    (((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ))
    (N.normalized.projective.affineMapDeriv_ne_zero z hz)
    (by exact_mod_cast (N.upperHalfPlaneMap_im_pos z).ne')

/--
Actual derivative identities for `F`, `F'`, and `F''` imply the explicit
mixed Frechet derivative formula for the first pullback Wirtinger expression.
-/
theorem pullbackMixedWirtingerExpressionDerivativeFormula_of_branch_hasDerivAt_on
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ∀ z, z ∈ N.domain →
        HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
          (N.normalized.projective.affineMapDeriv z) z)
    (hF' :
      ∀ z, z ∈ N.domain →
        HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
          (N.normalized.projective.affineMapSecondDeriv z) z)
    (hF'' :
      ∀ z, z ∈ N.domain →
        HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w)
          (N.normalized.projective.affineMapThirdDeriv z) z) :
    N.PullbackMixedWirtingerExpressionDerivativeFormula := by
  intro z hz
  let F : ℂ → ℂ := fun w ↦ (N.normalized.upperHalfPlaneMap w : ℂ)
  let F₁ : ℂ → ℂ := fun w ↦ N.normalized.projective.affineMapDeriv w
  let F₂ : ℂ → ℂ := fun w ↦ N.normalized.projective.affineMapSecondDeriv w
  let y : ℂ → ℂ := fun w ↦ (((F w).im : ℝ) : ℂ)
  have hFz : HasDerivAt F (F₁ z) z := by
    simpa [F, F₁] using hF z hz
  have hF₁z : HasDerivAt F₁ (F₂ z) z := by
    simpa [F₁, F₂] using hF' z hz
  have hF₂z :
      HasDerivAt F₂ (N.normalized.projective.affineMapThirdDeriv z) z := by
    simpa [F₂] using hF'' z hz
  have hF₁Diff : DifferentiableAt ℝ F₁ z :=
    hF₁z.complexToReal_fderiv.differentiableAt
  have hF₂Diff : DifferentiableAt ℝ F₂ z :=
    hF₂z.complexToReal_fderiv.differentiableAt
  have hyDiff : DifferentiableAt ℝ y z := by
    simpa [F, y] using differentiableAt_complex_ofReal_im_of_hasDerivAt hFz
  have hF₁nz : F₁ z ≠ 0 := by
    simpa [F₁] using N.normalized.projective.affineMapDeriv_ne_zero z hz
  have hynz : y z ≠ 0 := by
    have hpos : 0 < (F z).im := by
      simpa [F] using N.upperHalfPlaneMap_im_pos z
    simpa [y] using (show (((F z).im : ℂ) ≠ 0) from by
      exact_mod_cast hpos.ne')
  have hq :
      frechetDBarValue (fun w : ℂ ↦ F₂ w / F₁ w) z = 0 := by
    rw [frechetDBarValue_div_of_differentiableAt hF₂Diff hF₁Diff hF₁nz]
    rw [frechetDBarValue_of_hasDerivAt hF₂z]
    rw [frechetDBarValue_of_hasDerivAt hF₁z]
    ring
  have hyderiv :
      frechetDBarValue y z = Complex.I * star (F₁ z) / 2 := by
    simpa [F, F₁, y] using frechetDBarValue_complex_ofReal_im_of_hasDerivAt_general hFz
  have ht :
      frechetDBarValue (fun w : ℂ ↦ Complex.I * F₁ w / y w) z =
        Complex.I * ((0 * y z - F₁ z * (Complex.I * star (F₁ z) / 2)) / (y z) ^ 2) := by
    have hF₁divyDiff : DifferentiableAt ℝ (fun w : ℂ ↦ F₁ w / y w) z := by
      rw [show (fun w : ℂ ↦ F₁ w / y w) =
          (fun w : ℂ ↦ F₁ w * (y w)⁻¹) by
            ext w
            rw [div_eq_mul_inv]]
      exact hF₁Diff.mul (hyDiff.inv hynz)
    rw [show (fun w : ℂ ↦ Complex.I * F₁ w / y w) =
        (fun w : ℂ ↦ Complex.I * (F₁ w / y w)) by
          ext w
          rw [mul_div_assoc]]
    rw [frechetDBarValue_const_mul_of_differentiableAt hF₁divyDiff]
    rw [frechetDBarValue_div_of_differentiableAt hF₁Diff hyDiff hynz]
    rw [frechetDBarValue_of_hasDerivAt hF₁z, hyderiv]
  have hF₂divF₁Diff : DifferentiableAt ℝ (fun w : ℂ ↦ F₂ w / F₁ w) z := by
    rw [show (fun w : ℂ ↦ F₂ w / F₁ w) =
        (fun w : ℂ ↦ F₂ w * (F₁ w)⁻¹) by
          ext w
          rw [div_eq_mul_inv]]
    exact hF₂Diff.mul (hF₁Diff.inv hF₁nz)
  have hIF₁divyDiff : DifferentiableAt ℝ (fun w : ℂ ↦ Complex.I * F₁ w / y w) z := by
    rw [show (fun w : ℂ ↦ Complex.I * F₁ w / y w) =
        (fun w : ℂ ↦ Complex.I * (F₁ w / y w)) by
          ext w
          rw [mul_div_assoc]]
    have hF₁divyDiff : DifferentiableAt ℝ (fun w : ℂ ↦ F₁ w / y w) z := by
      rw [show (fun w : ℂ ↦ F₁ w / y w) =
          (fun w : ℂ ↦ F₁ w * (y w)⁻¹) by
            ext w
            rw [div_eq_mul_inv]]
      exact hF₁Diff.mul (hyDiff.inv hynz)
    exact hF₁divyDiff.const_mul Complex.I
  have hsumDiff :
      DifferentiableAt ℝ (fun w : ℂ ↦ F₂ w / F₁ w + Complex.I * F₁ w / y w) z :=
    hF₂divF₁Diff.add hIF₁divyDiff
  rw [show N.pullbackFirstWirtingerExpression =
      (fun w : ℂ ↦ (F₂ w / F₁ w + Complex.I * F₁ w / y w) / 2) by
        ext w
        simp [pullbackFirstWirtingerExpression, F, F₁, F₂, y]]
  rw [show (fun w : ℂ ↦ (F₂ w / F₁ w + Complex.I * F₁ w / y w) / 2) =
      (fun w : ℂ ↦ (2 : ℂ)⁻¹ *
        (F₂ w / F₁ w + Complex.I * F₁ w / y w)) by
        ext w
        rw [div_eq_inv_mul]]
  rw [frechetDBarValue_const_mul_of_differentiableAt hsumDiff]
  rw [frechetDBarValue_add_of_differentiableAt hF₂divF₁Diff hIF₁divyDiff]
  rw [hq, ht]
  dsimp [pullbackDensitySq, F, F₁, F₂, y]
  rw [Complex.ofReal_div, Complex.ofReal_pow]
  rw [← div_eq_inv_mul]
  simpa [F₁, y] using pullbackMixedWirtingerExpressionDerivativeFormula_algebra
    (N.normalized.projective.affineMapDeriv z)
    (((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ))
    (by exact_mod_cast (N.upperHalfPlaneMap_im_pos z).ne')

/--
The pointwise first Wirtinger formula gives local equality with the explicit
first expression on the open normalized domain.
-/
theorem pullbackFirstWirtingerEventuallyEqExpression_of_firstWirtingerFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (hZ : N.PullbackFirstWirtingerFormula hF hF' twice_differentiable_on_domain) :
    N.PullbackFirstWirtingerEventuallyEqExpression
      hF hF' twice_differentiable_on_domain := by
  intro z hz
  have hopen : IsOpen N.domain := by
    simpa [domain, LocalUpperHalfPlaneProjectiveNormalization.domain] using
      N.normalized.projective.isOpen_domain
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact hZ w hw

/--
Once the first derivative has been identified locally with its explicit branch
expression, the derivative formula for that expression implies the old second
Wirtinger formula.
-/
theorem pullbackSecondWirtingerFormula_of_first_eventuallyEq_and_expressionDerivative
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (hEq :
      N.PullbackFirstWirtingerEventuallyEqExpression
        hF hF' twice_differentiable_on_domain)
    (hDeriv : N.PullbackSecondWirtingerExpressionDerivativeFormula) :
    N.PullbackSecondWirtingerFormula hF hF' twice_differentiable_on_domain := by
  intro z hz
  let V := N.pullbackConformalFactor hF hF' twice_differentiable_on_domain
  have hfderiv :
      fderiv ℝ V.wirtingerZ z =
        fderiv ℝ N.pullbackFirstWirtingerExpression z :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (hEq z hz)
  dsimp [PullbackSecondWirtingerFormula, LocalConformalFactor.wirtingerZZ,
    frechetDZValue, V]
  rw [hfderiv]
  exact hDeriv z hz

/--
The first Wirtinger formula plus the explicit Frechet derivative calculation
for its right-hand side imply the second Wirtinger formula.
-/
theorem pullbackSecondWirtingerFormula_of_firstWirtingerFormula_and_expressionDerivative
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (hZ : N.PullbackFirstWirtingerFormula hF hF' twice_differentiable_on_domain)
    (hDeriv : N.PullbackSecondWirtingerExpressionDerivativeFormula) :
    N.PullbackSecondWirtingerFormula hF hF' twice_differentiable_on_domain :=
  N.pullbackSecondWirtingerFormula_of_first_eventuallyEq_and_expressionDerivative
    (N.pullbackFirstWirtingerEventuallyEqExpression_of_firstWirtingerFormula hZ)
    hDeriv

/--
Once the first Wirtinger derivative has been identified locally with its
explicit branch expression, the mixed derivative calculation for that
expression implies the mixed-Wirtinger Poincare Laplacian formula.
-/
theorem pullbackMixedWirtingerLaplacianFormula_of_first_eventuallyEq_and_mixedExpressionDerivative
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (hEq :
      N.PullbackFirstWirtingerEventuallyEqExpression
        hF hF' twice_differentiable_on_domain)
    (hDeriv : N.PullbackMixedWirtingerExpressionDerivativeFormula) :
    N.PullbackMixedWirtingerLaplacianFormula
      hF hF' twice_differentiable_on_domain := by
  intro z hz
  let V := N.pullbackConformalFactor hF hF' twice_differentiable_on_domain
  have hfderiv :
      fderiv ℝ V.wirtingerZ z =
        fderiv ℝ N.pullbackFirstWirtingerExpression z :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (hEq z hz)
  dsimp [PullbackMixedWirtingerLaplacianFormula, LocalConformalFactor.wirtingerZBar,
    frechetDBarValue, V]
  rw [hfderiv]
  exact hDeriv z hz

/--
The first Wirtinger formula plus the explicit mixed derivative calculation for
its right-hand side imply the mixed-Wirtinger Poincare Laplacian formula.
-/
theorem pullbackMixedWirtingerLaplacianFormula_of_firstWirtingerFormula_and_mixedExpressionDerivative
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (hZ : N.PullbackFirstWirtingerFormula hF hF' twice_differentiable_on_domain)
    (hDeriv : N.PullbackMixedWirtingerExpressionDerivativeFormula) :
    N.PullbackMixedWirtingerLaplacianFormula
      hF hF' twice_differentiable_on_domain :=
  N.pullbackMixedWirtingerLaplacianFormula_of_first_eventuallyEq_and_mixedExpressionDerivative
    (N.pullbackFirstWirtingerEventuallyEqExpression_of_firstWirtingerFormula hZ)
    hDeriv

/--
Actual differentiability of the affine projective branch gives actual
differentiability of the upper-half-plane-valued lift.

The proof is pure locality: on the open normalized domain, the `ℍ`-valued
branch agrees with the affine coordinate as a complex-valued function, so
mathlib's `HasDerivAt.congr_of_eventuallyEq` transfers the derivative.
-/
theorem upperHalfPlaneMap_hasDerivAt_of_affineMap_hasDerivAt_on
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hAffine :
      ∀ z, z ∈ N.domain →
        HasDerivAt N.normalized.projective.affineMap
          (N.normalized.projective.affineMapDeriv z) z) :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
        (N.normalized.projective.affineMapDeriv z) z := by
  intro z hz
  have hopen : IsOpen N.domain := by
    simpa [domain, LocalUpperHalfPlaneProjectiveNormalization.domain] using
      N.normalized.projective.isOpen_domain
  have hEq :
      (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
        =ᶠ[nhds z] N.normalized.projective.affineMap := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact N.normalized.upperHalfPlaneMap_eq_affine w hw
  exact (hAffine z hz).congr_of_eventuallyEq hEq

/--
Complex differentiability plus an identified value of `deriv` gives the
corresponding `HasDerivAt` statement.
-/
theorem hasDerivAt_of_differentiableAt_deriv_eq
    {f : ℂ → ℂ} {z f' : ℂ}
    (hf : DifferentiableAt ℂ f z) (hderiv : deriv f z = f') :
    HasDerivAt f f' z := by
  simpa [hderiv] using hf.hasDerivAt

/--
The first and second Wirtinger formulas imply the core Schwarzian identity.

The proof is only the classical cancellation
`2 (v_zz - v_z^2) = F'''/F' - (3/2) (F''/F')^2`.
-/
theorem metricSchwarzian_eq_branchSchwarzian_of_wirtinger_formulas
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (hZ : N.PullbackFirstWirtingerFormula hF hF' twice_differentiable_on_domain)
    (hZZ : N.PullbackSecondWirtingerFormula hF hF' twice_differentiable_on_domain) :
    N.PullbackMetricSchwarzianEqualsBranchSchwarzian
      hF hF' twice_differentiable_on_domain := by
  intro z hz
  let V := N.pullbackConformalFactor hF hF' twice_differentiable_on_domain
  let y : ℂ := ((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ)
  let F₁ := N.normalized.projective.affineMapDeriv z
  let F₂ := N.normalized.projective.affineMapSecondDeriv z
  let F₃ := N.normalized.projective.affineMapThirdDeriv z
  have hF₁ : F₁ ≠ 0 := by
    exact N.normalized.projective.affineMapDeriv_ne_zero z hz
  have hy : y ≠ 0 := by
    simpa [y] using (show (((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ) ≠ 0) from by
      exact_mod_cast (N.upperHalfPlaneMap_im_pos z).ne')
  have hF₁_unfold : N.normalized.projective.affineMapDeriv z ≠ 0 := by
    simpa [F₁] using hF₁
  have hy_unfold : ((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ) ≠ 0 := by
    simpa [y] using hy
  dsimp [PullbackMetricSchwarzianEqualsBranchSchwarzian]
  dsimp [LocalSchwarzianData.metricSchwarzianCoefficient,
    LocalConformalFactor.halfSchwarzianCoefficient, schwarzianExpression, V, y, F₁, F₂, F₃]
  rw [hZ z hz, hZZ z hz]
  dsimp [pullbackFirstWirtingerExpression, pullbackSecondWirtingerExpression, y, F₁, F₂, F₃]
  field_simp [hF₁, hy, hF₁_unfold, hy_unfold]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/--
The core Schwarzian identity, together with the projective branch's stored
Schwarzian equation, gives compatibility with the original coefficient.
-/
theorem pullbackSchwarzianCompatibility_of_metricSchwarzian_eq_branchSchwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (h :
      N.PullbackMetricSchwarzianEqualsBranchSchwarzian
        hF hF' twice_differentiable_on_domain) :
    N.PullbackSchwarzianCompatibility hF hF' twice_differentiable_on_domain := by
  intro z hz
  rw [h z hz]
  exact N.normalized.projective.schwarzian_eq_coefficient z hz

/--
The pointwise first derivative formula for the canonical Poincare pullback
squared density.

This is the squared-density form of the first Wirtinger formula.  Passing from
it to the logarithmic formula is just the already-proved Frechet-Wirtinger
chain rule for `(1 / 2) log`.
-/
def PullbackDensitySqDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Prop :=
  ∀ z, z ∈ N.domain →
    frechetDZValue (fun w : ℂ ↦ (N.pullbackDensitySq w : ℂ)) z =
      (N.pullbackDensitySq z : ℂ) *
        (N.normalized.projective.affineMapSecondDeriv z /
            N.normalized.projective.affineMapDeriv z +
          Complex.I * N.normalized.projective.affineMapDeriv z /
            ((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ))

/--
Algebra behind the pointwise first derivative of the Poincare squared density.

If `ρ = |F₁|² / y²`, `∂z |F₁|² = \bar F₁ F₂`, and
`∂z y² = -i y F₁`, then `∂z ρ = ρ (F₂/F₁ + iF₁/y)`.
-/
theorem pullbackDensitySqDerivativeFormula_algebra
    (F₁ F₂ : ℂ) {y : ℝ}
    (hF₁ : F₁ ≠ 0) (hy : (y : ℂ) ≠ 0) :
    ((star F₁ * F₂) * (y : ℂ) ^ 2 -
        (Complex.normSq F₁ : ℂ) * (-Complex.I * (y : ℂ) * F₁)) /
        ((y : ℂ) ^ 2) ^ 2 =
      ((Complex.normSq F₁ / y ^ 2 : ℝ) : ℂ) *
        (F₂ / F₁ + Complex.I * F₁ / (y : ℂ)) := by
  have hnorm : (Complex.normSq F₁ : ℂ) = star F₁ * F₁ := by
    simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := F₁))
  have hcast :
      ((Complex.normSq F₁ / y ^ 2 : ℝ) : ℂ) =
        (Complex.normSq F₁ : ℂ) / (y : ℂ) ^ 2 := by
    rw [Complex.ofReal_div, Complex.ofReal_pow]
  have hy2 : (y : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hy
  rw [hcast, hnorm]
  field_simp [hF₁, hy, hy2]
  ring_nf

/--
First-derivative regularity proves the squared-density derivative formula for
a metric-recovering upper-half-plane branch.
-/
theorem localUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem_of_firstDerivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem := by
  intro u S H z _hu hz
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let F₁ : ℂ → ℂ := fun w ↦ H.projective.affineMapDeriv w
  let F₂ : ℂ → ℂ := fun w ↦ H.projective.affineMapSecondDeriv w
  let A : ℂ → ℝ := fun w ↦ Complex.normSq (F₁ w)
  let B : ℂ → ℝ := fun w ↦ (F w).im ^ 2
  let ρ : ℂ → ℝ := fun w ↦ A w / B w
  have hOpen : IsOpen H.domain := H.projective.isOpen_domain
  have hF_deriv_ne : deriv F z ≠ 0 := by
    rw [show deriv F z = H.projective.affineMapDeriv z by
      simpa [F] using H.upperHalfPlane_deriv_eq_projectiveDeriv z hz]
    exact H.projective.affineMapDeriv_ne_zero z hz
  have hFz : HasDerivAt F (F₁ z) z := by
    have h := (differentiableAt_of_deriv_ne_zero hF_deriv_ne).hasDerivAt
    convert h using 1
    simpa [F, F₁] using (H.upperHalfPlane_deriv_eq_projectiveDeriv z hz).symm
  have hF₁z : HasDerivAt F₁ (F₂ z) z := by
    have hEq :
        (fun w : ℂ ↦ deriv F w) =ᶠ[nhds z] F₁ := by
      filter_upwards [hOpen.mem_nhds hz] with w hw
      simpa [F, F₁] using H.upperHalfPlane_deriv_eq_projectiveDeriv w hw
    exact (hFirst H hz).congr_of_eventuallyEq hEq.symm
  have hA : DifferentiableAt ℝ A z := by
    have hFR : DifferentiableAt ℝ F₁ z :=
      hF₁z.complexToReal_fderiv.differentiableAt
    simpa [A, Complex.normSq_apply] using
      ((Complex.reCLM.differentiableAt.comp z hFR).mul
          (Complex.reCLM.differentiableAt.comp z hFR)).add
        ((Complex.imCLM.differentiableAt.comp z hFR).mul
          (Complex.imCLM.differentiableAt.comp z hFR))
  have hB : DifferentiableAt ℝ B z := by
    have hFR : DifferentiableAt ℝ F z :=
      hFz.complexToReal_fderiv.differentiableAt
    simpa [B, F, Function.comp_apply, Complex.imCLM_apply, pow_two] using
      ((Complex.imCLM.differentiableAt.comp z hFR).mul
        (Complex.imCLM.differentiableAt.comp z hFR))
  have hB_ne : B z ≠ 0 := by
    exact (sq_pos_of_pos (H.upperHalfPlaneMap z).im_pos).ne'
  have hρ_deriv :
      frechetDZValue (fun w : ℂ ↦ (ρ w : ℂ)) z =
        (ρ z : ℂ) *
          (F₂ z / F₁ z + Complex.I * F₁ z / (((F z).im : ℝ) : ℂ)) := by
    rw [show (fun w : ℂ ↦ (ρ w : ℂ)) =
        (fun w : ℂ ↦ ((A w / B w : ℝ) : ℂ)) by rfl]
    rw [frechetDZValue_complex_ofReal_div_of_differentiableAt
      (A := A) (B := B) (z₀ := z) hA hB hB_ne]
    rw [frechetDZValue_complex_ofReal_normSq_of_hasDerivAt hF₁z]
    rw [frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt_general hFz]
    dsimp [A, B, ρ, F, F₁, F₂]
    simpa only [Complex.ofReal_pow, starRingEnd_apply] using
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.pullbackDensitySqDerivativeFormula_algebra
        (H.projective.affineMapDeriv z)
        (H.projective.affineMapSecondDeriv z)
        (H.projective.affineMapDeriv_ne_zero z hz)
        (by exact_mod_cast (H.upperHalfPlaneMap z).im_pos.ne')
  have hEq :
      (fun w : ℂ ↦ (u.densitySq w : ℂ)) =ᶠ[nhds z]
        (fun w : ℂ ↦ (ρ w : ℂ)) := by
    filter_upwards [hOpen.mem_nhds hz] with w hw
    have h :
        (u.densitySq w : ℂ) =
          ((Complex.normSq (H.projective.affineMapDeriv w) /
              ((H.upperHalfPlaneMap w : ℂ).im ^ 2) : ℝ) : ℂ) := by
      exact_mod_cast H.densitySq_eq_pullback w hw
    simpa [ρ, A, B, F, F₁] using h
  have hdz_eq :
      frechetDZValue (fun w : ℂ ↦ (u.densitySq w : ℂ)) z =
        frechetDZValue (fun w : ℂ ↦ (ρ w : ℂ)) z := by
    dsimp [frechetDZValue]
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq]
  rw [hdz_eq, hρ_deriv]
  have hDensity_z :
      (u.densitySq z : ℂ) =
        ((Complex.normSq (H.projective.affineMapDeriv z) /
            ((H.upperHalfPlaneMap z : ℂ).im ^ 2) : ℝ) : ℂ) := by
    exact_mod_cast H.densitySq_eq_pullback z hz
  have hDeriv_z :
      deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z =
        H.projective.affineMapDeriv z := by
    simpa using H.upperHalfPlane_deriv_eq_projectiveDeriv z hz
  have hSecondDeriv_z :
      deriv
          (fun w : ℂ ↦
            deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z =
        H.projective.affineMapSecondDeriv z := by
    simpa using (hFirst H hz).deriv
  rw [hDensity_z, hDeriv_z, hSecondDeriv_z]

/--
The pointwise squared-density derivative formula implies the first Wirtinger
formula for the canonical logarithmic pullback.
-/
theorem pullbackFirstWirtingerFormula_of_densitySqDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {hF :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {hF' :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (hDiff : ∀ z, z ∈ N.domain → DifferentiableAt ℝ N.pullbackDensitySq z)
    (hρ : N.PullbackDensitySqDerivativeFormula) :
    N.PullbackFirstWirtingerFormula hF hF' twice_differentiable_on_domain := by
  intro z hz
  let V := N.pullbackConformalFactor hF hF' twice_differentiable_on_domain
  dsimp [PullbackFirstWirtingerFormula, LocalConformalFactor.wirtingerZ,
    LocalConformalFactor.complexLogDensity, V, pullbackConformalFactor]
  change frechetDZValue (fun w : ℂ ↦ (N.pullbackLogDensity w : ℂ)) z =
    (N.normalized.projective.affineMapSecondDeriv z /
          N.normalized.projective.affineMapDeriv z +
        Complex.I * N.normalized.projective.affineMapDeriv z /
          ((N.normalized.upperHalfPlaneMap z : ℂ).im : ℂ)) / 2
  rw [show (fun w : ℂ ↦ (N.pullbackLogDensity w : ℂ)) =
      (fun w : ℂ ↦ (((1 / 2 : ℝ) * Real.log (N.pullbackDensitySq w) : ℝ) : ℂ)) by
        ext w
        simp [pullbackLogDensity]]
  rw [frechetDZValue_complex_ofReal_half_log_of_differentiableAt
    (ρ := N.pullbackDensitySq) (z₀ := z) (hDiff z hz) (N.pullbackDensitySq_pos hz)]
  rw [hρ z hz]
  have hρ_ne : (N.pullbackDensitySq z : ℂ) ≠ 0 := by
    exact_mod_cast (N.pullbackDensitySq_pos hz).ne'
  field_simp [hρ_ne]

/--
Actual complex derivatives of the normalized branch and its derivative branch
imply the pointwise squared-density derivative formula.
-/
theorem pullbackDensitySqDerivativeFormula_of_branch_hasDerivAt_on
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hF :
      ∀ z, z ∈ N.domain →
        HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
          (N.normalized.projective.affineMapDeriv z) z)
    (hF' :
      ∀ z, z ∈ N.domain →
        HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
          (N.normalized.projective.affineMapSecondDeriv z) z) :
    N.PullbackDensitySqDerivativeFormula := by
  intro z hz
  dsimp [PullbackDensitySqDerivativeFormula]
  let A : ℂ → ℝ := fun w ↦ Complex.normSq (N.normalized.projective.affineMapDeriv w)
  let B : ℂ → ℝ := fun w ↦ (N.normalized.upperHalfPlaneMap w : ℂ).im ^ 2
  have hA : DifferentiableAt ℝ A z := by
    have hFR : DifferentiableAt ℝ
        (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w) z :=
      (hF' z hz).complexToReal_fderiv.differentiableAt
    simpa [A, Complex.normSq_apply] using
      ((Complex.reCLM.differentiableAt.comp z hFR).mul
          (Complex.reCLM.differentiableAt.comp z hFR)).add
        ((Complex.imCLM.differentiableAt.comp z hFR).mul
          (Complex.imCLM.differentiableAt.comp z hFR))
  have hB : DifferentiableAt ℝ B z := by
    have hFR : DifferentiableAt ℝ
        (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ)) z :=
      (hF z hz).complexToReal_fderiv.differentiableAt
    simpa [B, Function.comp_apply, Complex.imCLM_apply, pow_two] using
      ((Complex.imCLM.differentiableAt.comp z hFR).mul
        (Complex.imCLM.differentiableAt.comp z hFR))
  have hB_ne : B z ≠ 0 := (N.upperHalfPlaneMap_im_sq_pos z).ne'
  rw [show (fun w : ℂ ↦ (N.pullbackDensitySq w : ℂ)) =
      (fun w : ℂ ↦ ((A w / B w : ℝ) : ℂ)) by
        ext w
        simp [pullbackDensitySq, A, B]]
  rw [frechetDZValue_complex_ofReal_div_of_differentiableAt
    (A := A) (B := B) (z₀ := z) hA hB hB_ne]
  rw [frechetDZValue_complex_ofReal_normSq_of_hasDerivAt (hF' z hz)]
  rw [frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt_general (hF z hz)]
  dsimp [A, B, pullbackDensitySq]
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using
    pullbackDensitySqDerivativeFormula_algebra
    (N.normalized.projective.affineMapDeriv z)
    (N.normalized.projective.affineMapSecondDeriv z)
    (N.normalized.projective.affineMapDeriv_ne_zero z hz)
    (by exact_mod_cast (N.upperHalfPlaneMap_im_pos z).ne')

/--
Actual complex derivatives of the normalized branch and its derivative branch
give differentiability of the Poincare pullback squared density.
-/
theorem pullbackDensitySq_differentiableAt_of_branch_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {z : ℂ}
    (hF :
      HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
        (N.normalized.projective.affineMapDeriv z) z)
    (hF' :
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
        (N.normalized.projective.affineMapSecondDeriv z) z) :
    DifferentiableAt ℝ N.pullbackDensitySq z := by
  let A : ℂ → ℝ := fun w ↦ Complex.normSq (N.normalized.projective.affineMapDeriv w)
  let B : ℂ → ℝ := fun w ↦ (N.normalized.upperHalfPlaneMap w : ℂ).im ^ 2
  have hA : DifferentiableAt ℝ A z := by
    have hFR : DifferentiableAt ℝ
        (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w) z :=
      hF'.complexToReal_fderiv.differentiableAt
    simpa [A, Complex.normSq_apply] using
      ((Complex.reCLM.differentiableAt.comp z hFR).mul
          (Complex.reCLM.differentiableAt.comp z hFR)).add
        ((Complex.imCLM.differentiableAt.comp z hFR).mul
          (Complex.imCLM.differentiableAt.comp z hFR))
  have hB : DifferentiableAt ℝ B z := by
    have hFR : DifferentiableAt ℝ
        (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ)) z :=
      hF.complexToReal_fderiv.differentiableAt
    simpa [B, Function.comp_apply, Complex.imCLM_apply, pow_two] using
      ((Complex.imCLM.differentiableAt.comp z hFR).mul
        (Complex.imCLM.differentiableAt.comp z hFR))
  have hB_ne : B z ≠ 0 := (N.upperHalfPlaneMap_im_sq_pos z).ne'
  rw [show N.pullbackDensitySq = (fun w : ℂ ↦ A w / B w) by
    ext w
    simp [pullbackDensitySq, A, B]]
  have hBinv : DifferentiableAt ℝ (fun w : ℂ ↦ (B w)⁻¹) z :=
    hB.inv hB_ne
  simpa [div_eq_mul_inv] using hA.mul hBinv

/--
The analytic base derivative formula for the canonical Poincare pullback
squared density.

This is the squared-density version of the remaining local calculus statement:
differentiate `ρ = |F'|² / (Im F)²` at the normalized base point and use
`F(z₀)=i`.  The logarithmic formula follows from the blue
Frechet-Wirtinger chain rule for `(1 / 2) log ρ`.
-/
def PullbackDensitySqBaseDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Prop :=
  frechetDZValue (fun z : ℂ ↦ (N.pullbackDensitySq z : ℂ)) z₀ =
    (N.pullbackDensitySq z₀ : ℂ) *
      (N.normalized.projective.affineMapSecondDeriv z₀ /
          N.normalized.projective.affineMapDeriv z₀ +
        Complex.I * N.normalized.projective.affineMapDeriv z₀)

/--
The numerator and denominator base derivative formulas imply the full
squared-density base derivative formula.

This is the blue quotient-calculus bridge for the Poincare density
`|F'|² / (Im F)²`.
-/
theorem pullbackDensitySq_base_derivativeFormula_of_num_den
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hNumDiff : DifferentiableAt ℝ
      (fun z : ℂ ↦ Complex.normSq (N.normalized.projective.affineMapDeriv z)) z₀)
    (hDenDiff : DifferentiableAt ℝ
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2) z₀)
    (hNum : N.PullbackDensitySqBaseNumeratorDerivativeFormula)
    (hDen : N.PullbackDensitySqBaseDenominatorDerivativeFormula) :
    N.PullbackDensitySqBaseDerivativeFormula := by
  rw [PullbackDensitySqBaseDerivativeFormula]
  let A : ℂ → ℝ := fun z ↦ Complex.normSq (N.normalized.projective.affineMapDeriv z)
  let B : ℂ → ℝ := fun z ↦ (N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2
  have hB_ne : B z₀ ≠ 0 :=
    (N.upperHalfPlaneMap_im_sq_pos z₀).ne'
  rw [show (fun z : ℂ ↦ (N.pullbackDensitySq z : ℂ)) =
      (fun z : ℂ ↦ ((A z / B z : ℝ) : ℂ)) by
        ext z
        simp [pullbackDensitySq, A, B]]
  rw [frechetDZValue_complex_ofReal_div_of_differentiableAt
    (A := A) (B := B) (z₀ := z₀) (by simpa [A] using hNumDiff)
    (by simpa [B] using hDenDiff) hB_ne]
  rw [hNum, hDen]
  dsimp [A, B]
  rw [pullbackDensitySq]
  rw [N.value_eq]
  simp [HyperbolicSchwarzianBaseJet.targetValue]
  have hImR : (N.normalized.upperHalfPlaneMap z₀ : ℂ).im = 1 := by
    rw [N.value_eq]
    simp [HyperbolicSchwarzianBaseJet.targetValue]
  have hderiv_ne : N.normalized.projective.affineMapDeriv z₀ ≠ 0 :=
    N.normalized.projective.affineMapDeriv_ne_zero z₀ N.base_mem
  field_simp [hderiv_ne]
  change
    (N.normalized.projective.affineMapSecondDeriv z₀ *
          (((N.normalized.upperHalfPlaneMap z₀ : ℂ).im : ℂ) ^ 2) +
        N.normalized.projective.affineMapDeriv z₀ ^ 2 * Complex.I) /
        (((N.normalized.upperHalfPlaneMap z₀ : ℂ).im : ℂ) ^ 4) =
      N.normalized.projective.affineMapSecondDeriv z₀ +
        N.normalized.projective.affineMapDeriv z₀ ^ 2 * Complex.I
  have hImC : (((N.normalized.upperHalfPlaneMap z₀ : ℂ).im : ℝ) : ℂ) = 1 := by
    exact_mod_cast hImR
  rw [hImC]
  ring_nf

/--
The analytic base derivative formula for the canonical Poincare pullback
logarithmic density.

This is the exact remaining local calculus statement at the base point:
differentiate
`v = (1 / 2) log (|F'|² / (Im F)²)` and use `F(z₀)=i`.
The algebraic conversion from the right-hand side to the prescribed `u_z`
is proved separately by `base_uZ_eq_of_twoJet_formula`.
-/
def PullbackLogDensityBaseDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) : Prop :=
  frechetDZValue (fun z : ℂ ↦ (N.pullbackLogDensity z : ℂ)) z₀ =
    (N.normalized.projective.affineMapSecondDeriv z₀ /
        N.normalized.projective.affineMapDeriv z₀ +
      Complex.I * N.normalized.projective.affineMapDeriv z₀) / 2

/--
The analytic base derivative formula implies agreement with the prescribed
canonical base value `u_z`.
-/
theorem pullbackLogDensity_base_uZ_eq_of_derivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (h :
      N.PullbackLogDensityBaseDerivativeFormula) :
    frechetDZValue (fun z : ℂ ↦ (N.pullbackLogDensity z : ℂ)) z₀ = N.jet.uZ := by
  rw [h]
  exact N.base_uZ_eq_of_twoJet_formula

/--
The squared-density base derivative formula implies the logarithmic base
derivative formula.

This is now a mathlib-backed chain-rule reduction: the only remaining
calculus is the derivative of the squared Poincare pullback density itself.
-/
theorem pullbackLogDensity_base_derivativeFormula_of_densitySqDerivative
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hDiff : DifferentiableAt ℝ N.pullbackDensitySq z₀)
    (hSq : N.PullbackDensitySqBaseDerivativeFormula) :
    N.PullbackLogDensityBaseDerivativeFormula := by
  rw [PullbackLogDensityBaseDerivativeFormula]
  rw [show (fun z : ℂ ↦ (N.pullbackLogDensity z : ℂ)) =
      (fun z : ℂ ↦ (((1 / 2 : ℝ) * Real.log (N.pullbackDensitySq z) : ℝ) : ℂ)) by
        ext z
        simp [pullbackLogDensity]]
  rw [frechetDZValue_complex_ofReal_half_log_of_differentiableAt
    hDiff (N.pullbackDensitySq_pos N.base_mem)]
  rw [hSq]
  have hρ_ne : (N.pullbackDensitySq z₀ : ℂ) ≠ 0 := by
    exact_mod_cast (N.pullbackDensitySq_pos N.base_mem).ne'
  field_simp [hρ_ne]

end LocalHyperbolicTwoJetUpperHalfPlaneNormalization

/--
Global alias for the squared-density derivative formula of a
metric-recovering upper-half-plane branch.
-/
theorem localUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem_of_firstDerivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem :=
  LocalHyperbolicTwoJetUpperHalfPlaneNormalization.localUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem_of_firstDerivative
    hFirst

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity proves the pointwise
squared-density derivative formula for that metric-recovering branch.
-/
theorem densitySqDerivativeFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (_hu : u.SolvesLiouvilleEquation) (hz : z ∈ H.domain) :
    frechetDZValue (fun w : ℂ ↦ (u.densitySq w : ℂ)) z =
      (u.densitySq z : ℂ) *
        (deriv
            (fun w : ℂ ↦
              deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z /
          deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z +
          Complex.I * deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z /
            (((H.upperHalfPlaneMap z : ℂ).im : ℝ) : ℂ)) := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let F₁ : ℂ → ℂ := fun w ↦ H.projective.affineMapDeriv w
  let F₂ : ℂ → ℂ := fun w ↦ H.projective.affineMapSecondDeriv w
  let A : ℂ → ℝ := fun w ↦ Complex.normSq (F₁ w)
  let B : ℂ → ℝ := fun w ↦ (F w).im ^ 2
  let ρ : ℂ → ℝ := fun w ↦ A w / B w
  have hOpen : IsOpen H.domain := H.projective.isOpen_domain
  have hF_deriv_ne : deriv F z ≠ 0 := by
    rw [show deriv F z = H.projective.affineMapDeriv z by
      simpa [F] using H.upperHalfPlane_deriv_eq_projectiveDeriv z hz]
    exact H.projective.affineMapDeriv_ne_zero z hz
  have hFz : HasDerivAt F (F₁ z) z := by
    have h := (differentiableAt_of_deriv_ne_zero hF_deriv_ne).hasDerivAt
    convert h using 1
    simpa [F, F₁] using (H.upperHalfPlane_deriv_eq_projectiveDeriv z hz).symm
  have hF₁z : HasDerivAt F₁ (F₂ z) z := by
    simpa [F₁, F₂] using R.projectiveFirstDerivative_hasDerivAt hz
  have hA : DifferentiableAt ℝ A z := by
    have hFR : DifferentiableAt ℝ F₁ z :=
      hF₁z.complexToReal_fderiv.differentiableAt
    simpa [A, Complex.normSq_apply] using
      ((Complex.reCLM.differentiableAt.comp z hFR).mul
          (Complex.reCLM.differentiableAt.comp z hFR)).add
        ((Complex.imCLM.differentiableAt.comp z hFR).mul
          (Complex.imCLM.differentiableAt.comp z hFR))
  have hB : DifferentiableAt ℝ B z := by
    have hFR : DifferentiableAt ℝ F z :=
      hFz.complexToReal_fderiv.differentiableAt
    simpa [B, F, Function.comp_apply, Complex.imCLM_apply, pow_two] using
      ((Complex.imCLM.differentiableAt.comp z hFR).mul
        (Complex.imCLM.differentiableAt.comp z hFR))
  have hB_ne : B z ≠ 0 := by
    exact (sq_pos_of_pos (H.upperHalfPlaneMap z).im_pos).ne'
  have hρ_deriv :
      frechetDZValue (fun w : ℂ ↦ (ρ w : ℂ)) z =
        (ρ z : ℂ) *
          (F₂ z / F₁ z + Complex.I * F₁ z / (((F z).im : ℝ) : ℂ)) := by
    rw [show (fun w : ℂ ↦ (ρ w : ℂ)) =
        (fun w : ℂ ↦ ((A w / B w : ℝ) : ℂ)) by rfl]
    rw [frechetDZValue_complex_ofReal_div_of_differentiableAt
      (A := A) (B := B) (z₀ := z) hA hB hB_ne]
    rw [frechetDZValue_complex_ofReal_normSq_of_hasDerivAt hF₁z]
    rw [frechetDZValue_complex_ofReal_im_sq_of_hasDerivAt_general hFz]
    dsimp [A, B, ρ, F, F₁, F₂]
    simpa only [Complex.ofReal_pow, starRingEnd_apply] using
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.pullbackDensitySqDerivativeFormula_algebra
        (H.projective.affineMapDeriv z)
        (H.projective.affineMapSecondDeriv z)
        (H.projective.affineMapDeriv_ne_zero z hz)
        (by exact_mod_cast (H.upperHalfPlaneMap z).im_pos.ne')
  have hEq :
      (fun w : ℂ ↦ (u.densitySq w : ℂ)) =ᶠ[nhds z]
        (fun w : ℂ ↦ (ρ w : ℂ)) := by
    filter_upwards [hOpen.mem_nhds hz] with w hw
    have h :
        (u.densitySq w : ℂ) =
          ((Complex.normSq (H.projective.affineMapDeriv w) /
              ((H.upperHalfPlaneMap w : ℂ).im ^ 2) : ℝ) : ℂ) := by
      exact_mod_cast H.densitySq_eq_pullback w hw
    simpa [ρ, A, B, F, F₁] using h
  have hdz_eq :
      frechetDZValue (fun w : ℂ ↦ (u.densitySq w : ℂ)) z =
        frechetDZValue (fun w : ℂ ↦ (ρ w : ℂ)) z := by
    dsimp [frechetDZValue]
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq]
  rw [hdz_eq, hρ_deriv]
  have hDensity_z :
      (u.densitySq z : ℂ) =
        ((Complex.normSq (H.projective.affineMapDeriv z) /
            ((H.upperHalfPlaneMap z : ℂ).im ^ 2) : ℝ) : ℂ) := by
    exact_mod_cast H.densitySq_eq_pullback z hz
  have hDeriv_z :
      deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z =
        H.projective.affineMapDeriv z := by
    simpa using H.upperHalfPlane_deriv_eq_projectiveDeriv z hz
  have hSecondDeriv_z :
      deriv
          (fun w : ℂ ↦
            deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z =
        H.projective.affineMapSecondDeriv z := by
    simpa using (R.firstDerivative_hasDerivAt hz).deriv
  rw [hDensity_z, hDeriv_z, hSecondDeriv_z]

/--
Fixed-branch projective derivative regularity proves the first-Wirtinger
formula for that metric-recovering branch.
-/
theorem pullbackFirstWirtingerFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hu : u.SolvesLiouvilleEquation) (hz : z ∈ H.domain) :
    u.wirtingerZ z =
      localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H z := by
  have hDomain : z ∈ u.coordinateDomain := H.projective.domain_subset hz
  have hlogDiff : DifferentiableAt ℝ u.logDensity z :=
    (u.logDensity_contDiffOn.differentiableOn (by norm_num) z hDomain).differentiableAt
      (u.isOpen_coordinateDomain.mem_nhds hDomain)
  have hDensityDiff : DifferentiableAt ℝ u.densitySq z := by
    simpa [LocalConformalFactor.densitySq] using
      ((hlogDiff.const_mul (2 : ℝ)).exp)
  rw [LocalConformalFactor.wirtingerZ]
  change frechetDZValue (fun w : ℂ ↦ (u.logDensity w : ℂ)) z =
    localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H z
  rw [show (fun w : ℂ ↦ (u.logDensity w : ℂ)) =
      (fun w : ℂ ↦ (((1 / 2 : ℝ) * Real.log (u.densitySq w) : ℝ) : ℂ)) by
        ext w
        simp [LocalConformalFactor.densitySq]]
  rw [frechetDZValue_complex_ofReal_half_log_of_differentiableAt
    (ρ := u.densitySq) (z₀ := z) hDensityDiff (u.densitySq_pos z)]
  rw [R.densitySqDerivativeFormula hu hz]
  have hρ_ne : (u.densitySq z : ℂ) ≠ 0 := by
    exact_mod_cast (u.densitySq_pos z).ne'
  dsimp [localUpperHalfPlaneDevelopingMapFirstWirtingerExpression]
  field_simp [hρ_ne]

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-pair projective derivative regularity gives the metric second-jet step:
a pointed real-Mobius one-jet match forces equality of the actual second
derivatives at the point.
-/
theorem pointedRealMobiusTransition_metricOneJetDeterminesSecondJet_of_pairProjectiveDerivative
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (_z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : u.SolvesLiouvilleEquation)
    (_hpoint : H₁.HasPointedRealMobiusTransition H₂ A _z₀)
    (_hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    {z : ℂ} (hz₁ : z ∈ H₁.domain) (hz₂ : z ∈ H₂.domain)
    (hval :
      H₂.upperHalfPlaneMap z =
        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z))
    (hderiv :
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          z) :
    deriv (fun w : ℂ ↦
          deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z =
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A
                (H₁.upperHalfPlaneMap t) : ℂ))
            w)
        z := by
  let F' : ℂ := deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z
  let F'' : ℂ :=
    deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z
  let G' : ℂ :=
    deriv
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ)) z
  let G'' : ℂ :=
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap t) : ℂ))
          w) z
  let Y : ℂ := (((H₂.upperHalfPlaneMap z : ℂ).im : ℝ) : ℂ)
  have hF'_ne : F' ≠ 0 := by
    have hF'_eq :
        F' = H₂.projective.affineMapDeriv z := by
      simpa [F'] using H₂.upperHalfPlane_deriv_eq_projectiveDeriv z hz₂
    rw [hF'_eq]
    exact H₂.projective.affineMapDeriv_ne_zero z hz₂
  have h₂ :
      u.wirtingerZ z =
        (F'' / F' + Complex.I * F' / Y) / 2 := by
    simpa [localUpperHalfPlaneDevelopingMapFirstWirtingerExpression, F', F'', Y] using
      R₂.pullbackFirstWirtingerFormula hu hz₂
  have hvalue_complex :
      ((H₂.upperHalfPlaneMap z : ℍ) : ℂ) =
        ((realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) : ℍ) : ℂ) :=
    congrArg (fun p : ℍ ↦ (p : ℂ)) hval
  have hA :
      u.wirtingerZ z =
        (G'' / G' +
            Complex.I * G' /
              ((((realMobiusRepresentativeAction A
                (H₁.upperHalfPlaneMap z) : ℍ) : ℂ).im : ℝ) : ℂ)) / 2 := by
    calc
      u.wirtingerZ z =
          localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H₁ z :=
        R₁.pullbackFirstWirtingerFormula hu hz₁
      _ = realMobiusPostcompositionFirstWirtingerExpression H₁ A z :=
        (R₁.realMobiusPostcomposition_firstWirtingerExpression A hz₁).symm
      _ =
          (G'' / G' +
              Complex.I * G' /
                ((((realMobiusRepresentativeAction A
                  (H₁.upperHalfPlaneMap z) : ℍ) : ℂ).im : ℝ) : ℂ)) / 2 := by
        rfl
  have hterms :
      (F'' / F' + Complex.I * F' / Y) / 2 =
        (G'' / F' + Complex.I * F' / Y) / 2 := by
    have hraw := h₂.symm.trans hA
    simpa [F', F'', G', G'', Y, hderiv.symm, hvalue_complex.symm] using hraw
  have hsum :
      F'' / F' + Complex.I * F' / Y =
        G'' / F' + Complex.I * F' / Y := by
    have hmul := congrArg (fun x : ℂ ↦ (2 : ℂ) * x) hterms
    simpa [div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc] using hmul
  have hdiv : F'' / F' = G'' / F' := by
    exact add_right_cancel hsum
  have hsecond : F'' = G'' := by
    rwa [div_left_inj' hF'_ne] at hdiv
  simpa [F'', G''] using hsecond

/--
Fixed-pair projective derivative regularity gives the value part of the local
two-jet Schwarzian identity principle.
-/
theorem pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreement_of_pairProjectiveDerivative
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (_z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (_hu : u.SolvesLiouvilleEquation)
    (_hpoint : H₁.HasPointedRealMobiusTransition H₂ A _z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hScalar :
      ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem)
    {z : ℂ} (hz₁ : z ∈ H₁.domain) (hz₂ : z ∈ H₂.domain)
    (hval :
      H₂.upperHalfPlaneMap z =
        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z))
    (hderiv :
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          z)
    (hsecond :
      deriv (fun w : ℂ ↦
            deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z =
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                (realMobiusRepresentativeAction A
                  (H₁.upperHalfPlaneMap t) : ℂ))
              w)
          z) :
    ∃ V : Set ℂ,
      IsOpen V ∧ z ∈ V ∧ V ⊆ H₁.domain ∩ H₂.domain ∧
        ∀ w, w ∈ V →
          H₂.upperHalfPlaneMap w =
            realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) := by
  let f : ℂ → ℂ := fun w ↦ (H₂.upperHalfPlaneMap w : ℂ)
  let g : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ)
  let U : Set ℂ := H₁.domain ∩ H₂.domain
  have hUopen : IsOpen U := H₁.projective.isOpen_domain.inter H₂.projective.isOpen_domain
  have hzU : z ∈ U := ⟨hz₁, hz₂⟩
  have hf_ne : ∀ w, w ∈ U → deriv f w ≠ 0 := by
    intro w hw
    have hpos := H₂.upperHalfPlaneDerivativeNormSq_pos hw.2
    dsimp [complexDerivativeNormSq, f] at hpos
    exact Complex.normSq_pos.mp hpos
  have hg_ne : ∀ w, w ∈ U → deriv g w ≠ 0 := by
    intro w hw
    have hchain :=
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A hw.1
    have hα :
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
          (H₁.upperHalfPlaneMap w) ≠ 0 :=
      realMobiusRepresentativeAction_deriv_ne_zero A (H₁.upperHalfPlaneMap w)
    have hF :
        deriv (fun t : ℂ ↦ (H₁.upperHalfPlaneMap t : ℂ)) w ≠ 0 := by
      have hpos := H₁.upperHalfPlaneDerivativeNormSq_pos hw.1
      dsimp [complexDerivativeNormSq] at hpos
      exact Complex.normSq_pos.mp hpos
    rw [show deriv g w =
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap t) : ℂ))
          w by rfl]
    rw [hchain]
    exact mul_ne_zero hα hF
  have hf₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w := by
    intro w hw
    simpa [f] using R₂.derivative_hasDerivAt hw.2
  have hf₂ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
          (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w := by
    intro w hw
    have h := R₂.secondDerivative_hasDerivAt hw.2
    convert h using 1
    exact h.deriv
  have hg₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv g t)
          (deriv (fun t : ℂ ↦ deriv g t) w) w := by
    intro w hw
    simpa [g] using
      R₁.realMobiusPostcomposition_firstDerivativeHasDerivAt A hw.1
  have hg₂ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t)
          (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t) w) w := by
    intro w hw
    simpa [g] using
      R₁.realMobiusPostcomposition_secondDerivativeHasDerivAt A hw.1
  have hschw : ∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian g w := by
    intro w hw
    calc
      actualSchwarzian f w = S₂.coefficient w := by
        simpa [f] using R₂.actualSchwarzian_eq_coefficient hw.2
      _ = S₁.coefficient w := (hCoeff w hw.1 hw.2).symm
      _ = actualSchwarzian g w := by
        simpa [g] using
          (R₁.realMobiusPostcomposition_actualSchwarzian_eq_coefficient A hw.1).symm
  rcases hScalar f g U z hUopen hzU hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw
      (by simpa [f, g] using congrArg (fun p : ℍ ↦ (p : ℂ)) hval)
      (by simpa [f, g] using hderiv)
      (by simpa [f, g] using hsecond) with
    ⟨V, hVopen, hzV, hVsubset, hVeq⟩
  refine ⟨V, hVopen, hzV, hVsubset, ?_⟩
  intro w hw
  exact UpperHalfPlane.coe_inj.mp (by simpa [f, g] using hVeq w hw)

/--
%%handwave
name:
  Local uniqueness of normalized hyperbolic branches
statement:
  Let $F_1,F_2$ be regular local maps to $\mathbb H$ which recover the same
  hyperbolic metric, and suppose their Schwarzian coefficients agree on an
  overlap. Fix $A\in\mathrm{PSL}_2(\mathbb R)$ which matches their one-jets at
  a base point $z_0$. If $F_2$ and $A\circ F_1$ also have the same value and
  first derivative at a point $z$ of the overlap, then they, together with
  their first derivatives, agree on a neighborhood of $z$.
proof:
  Differentiating the common Poincaré pullback formula shows that equality of
  the first jets forces equality of the second jets. [Two locally univalent maps with the same Schwarzian and the same two-jet agree locally](lean:JJMath.scalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem_of_preSchwarzian). Möbius invariance identifies the Schwarzian of $A\circ F_1$ with that of $F_1$; differentiating the resulting local equality also gives equality of first derivatives.
-/
theorem pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_proved :
    PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ R₁ R₂ hu hpoint hCoeff z hz₁ hz₂ hval hderiv
  have hsecond :
      deriv (fun w : ℂ ↦
            deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z =
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                (realMobiusRepresentativeAction A
                  (H₁.upperHalfPlaneMap t) : ℂ))
              w)
          z :=
    pointedRealMobiusTransition_metricOneJetDeterminesSecondJet_of_pairProjectiveDerivative
      H₁ H₂ A z₀ R₁ R₂ hu hpoint hCoeff hz₁ hz₂ hval hderiv
  rcases pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreement_of_pairProjectiveDerivative
      H₁ H₂ A z₀ R₁ R₂ hu hpoint hCoeff
      (scalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem_of_preSchwarzian
        scalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem_proved
        scalarPreSchwarzianValueDerivativeLocalUniquenessTheorem_of_derivativeQuotient)
      hz₁ hz₂ hval hderiv hsecond with
    ⟨U, hUopen, hzU, hUsubset, hUeq⟩
  refine ⟨U, hUopen, hzU, hUsubset, ?_⟩
  intro w hw
  constructor
  · exact hUeq w hw
  · let F : ℂ → ℂ := fun t ↦ (H₂.upperHalfPlaneMap t : ℂ)
    let G : ℂ → ℂ :=
      fun t ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap t) : ℂ)
    have hEq : F =ᶠ[nhds w] G := by
      filter_upwards [hUopen.mem_nhds hw] with t ht
      exact congrArg (fun p : ℍ ↦ (p : ℂ)) (hUeq t ht)
    simpa [F, G] using hEq.deriv_eq

/--
Projective-symbolic derivative regularity closes the coefficient-aware local
one-jet uniqueness input: the first-Wirtinger formula, real-Mobius
postcomposition invariance, actual-Schwarzian equations, and scalar
Schwarzian identity principle are all supplied by proved reductions.
-/
theorem pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_projectiveFirstSecondDerivative_scalarClosed
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem := by
  have hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem :=
    localUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem_of_projectiveFirstDerivative
      hProjFirst
  have hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem :=
    localUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem_of_projectiveFirstSecondDerivative
      hProjFirst hProjSecond
  have hBranchDeriv :
      LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem :=
    localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
      hFirst
  have hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem :=
    realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
      hBranchDeriv
  have hFirstFormula :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem :=
    localUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem_of_densitySqDerivative
      (localUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem_of_firstDerivative
        hFirst)
  have hPostFirst :
      RealMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem :=
    realMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem_of_expressionInvariant
      (realMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem_of_secondChainRule
        hSecondChain)
  have hMetricSecond :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem :=
    pointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem_of_pullbackFirstWirtingerFormula
      (pointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem_of_branchFormula_postcomposition
        hFirstFormula hPostFirst)
  have hBranchSchwarzian :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem :=
    localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_first_second_derivative
      hFirst hSecond
  have hThirdChain :
      RealMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem :=
    realMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem_of_first_secondDerivative
      hFirst hSecond
  have hInvariant :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem :=
    realMobiusPostcompositionActualSchwarzianInvariantTheorem_of_thirdChainRule_zero
      hSecondChain hThirdChain realMobiusActualSchwarzianZeroTheorem
  have hScalarC3 :
      ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem :=
    scalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem_of_preSchwarzian
      scalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem_proved
      scalarPreSchwarzianValueDerivativeLocalUniquenessTheorem_of_derivativeQuotient
  have hTwoJetValue :
      PointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem :=
    pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem_of_actualSchwarzian_c3
      hBranchSchwarzian
      (realMobiusPostcompositionActualSchwarzianEquationTheorem_of_invariant
        hBranchSchwarzian hInvariant)
      hFirst hSecond hScalarC3
  have hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem :=
    pointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem_of_value
      hTwoJetValue
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv
  exact
    pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_metricSecondJet_twoJetUniqueness
      hMetricSecond hTwoJet H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv

/--
The fixed-pair one-jet uniqueness interface is now closed directly from the
two selected branches' projective derivative regularity.
-/
theorem pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_of_projectiveFirstSecondDerivative_scalarClosed
    (_hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (_hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem := by
  exact pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_proved

/--
With coefficient agreement on overlaps, projective-symbolic derivative
regularity makes the one-jet equality locus open.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_projectiveFirstSecondDerivative_scalarClosed
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem :=
  pointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_localUniqueness
    (pointedRealMobiusTransitionOneJetLocalUniquenessTheorem_of_coefficientAgreement
      hCoeff
      (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_projectiveFirstSecondDerivative_scalarClosed
        hProjFirst hProjSecond))

/--
Fixed-pair version of the one-jet equality-locus openness theorem.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_projectiveFirstSecondDerivative_scalarClosed
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    IsOpen (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A) :=
  pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_coefficientAgreement
    H₁ H₂ A z₀ hu hpoint hCoeff
    (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_projectiveFirstSecondDerivative_scalarClosed
      hProjFirst hProjSecond)

/--
With coefficient agreement on overlaps, projective-symbolic derivative
regularity proves the nonempty-overlap branch real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_projectiveFirstSecondDerivative_scalarClosed
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem := by
  have hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem :=
    localUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem_of_projectiveFirstDerivative
      hProjFirst
  have hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem :=
    localUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem_of_firstDerivative
      hFirst
  have hLocal :
      PointedRealMobiusTransitionOneJetLocalUniquenessTheorem :=
    pointedRealMobiusTransitionOneJetLocalUniquenessTheorem_of_coefficientAgreement
      hCoeff
      (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_projectiveFirstSecondDerivative_scalarClosed
        hProjFirst hProjSecond)
  intro u S₁ S₂ H₁ H₂ hu hconn hne
  exact
    metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_branch_continuity_localUniqueness
      localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem hAffine hLocal
      H₁ H₂ hu hconn hne

/--
With coefficient agreement on overlaps, projective-symbolic derivative
regularity proves the ordinary branch real-transition theorem; empty overlaps
are handled by vacuity.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_projectiveFirstSecondDerivative_scalarClosed
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_nonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_projectiveFirstSecondDerivative_scalarClosed
      hCoeff hProjFirst hProjSecond)

namespace LocalProjectiveNormalFormUpperHalfPlaneLiftData

/--
Explicit normal-form data, a landing ball inside its domain, and the remaining
lift/derivative-identification data produce a hyperbolic two-jet
upper-half-plane normalization.
-/
def toLocalHyperbolicTwoJetUpperHalfPlaneNormalization
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ} {hz₀ : z₀ ∈ D.domain}
    {J : HyperbolicSchwarzianBaseJet u z₀}
    {E :
      LocalProjectiveNormalFormPostcompositionExplicitData
        D z₀ hz₀ J.toNondegenerateFiniteTwoJet}
    {r : ℝ} (L : LocalProjectiveNormalFormUpperHalfPlaneLiftData E r)
    (hr_pos : 0 < r) (hsubset : Metric.ball z₀ r ⊆ E.domain) :
    LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀ where
  jet := J
  normalized := {
    projective := E.restrictToBall r hsubset
    upperHalfPlaneMap := L.upperHalfPlaneMap
    upperHalfPlaneMap_eq_affine := by
      intro z hz
      exact L.upperHalfPlaneMap_eq_affine z hz
    holomorphic_on_domain :=
      LocalUpperHalfPlaneMapHolomorphicOn.of_hasDerivAt
        L.upperHalfPlaneMap_hasDerivAt
    deriv_eq_projectiveDeriv := by
      intro z hz
      exact L.deriv_eq_projectiveDeriv z hz
    upperHalfPlane_deriv_eq_projectiveDeriv := by
      intro z hz
      exact L.upperHalfPlane_deriv_eq_projectiveDeriv z hz
    postcomposition :=
      (D.finiteTwoJet hz₀).postcompositionNormalFormRepresentative
        J.toNondegenerateFiniteTwoJet
    domain_subset_original := by
      intro z hz
      exact E.domain_subset_original (hsubset hz)
    projective_eq_postcompose_original := by
      intro z hz
      exact E.toPostcompositionData.projective_eq_postcompose_original z (hsubset hz)
  }
  base_mem := Metric.mem_ball_self hr_pos
  domain_eq_ball := ⟨z₀, r, rfl⟩
  value_eq := by
    have hbase : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
    calc
      (L.upperHalfPlaneMap z₀ : ℂ) =
          E.toLocalProjectiveDevelopingMap.affineMap z₀ :=
        L.upperHalfPlaneMap_eq_affine z₀ hbase
      _ = J.targetValue := by
        simpa [HyperbolicSchwarzianBaseJet.toNondegenerateFiniteTwoJet] using
          E.affineMap_eq_targetValue_base
  firstDeriv_eq := by
    simpa [LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall,
      HyperbolicSchwarzianBaseJet.toNondegenerateFiniteTwoJet] using
      E.toPostcompositionData.toMobiusTwoJetNormalization.firstDeriv_eq
  secondDeriv_eq := by
    simpa [LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall,
      HyperbolicSchwarzianBaseJet.toNondegenerateFiniteTwoJet] using
      E.toPostcompositionData.toMobiusTwoJetNormalization.secondDeriv_eq

end LocalProjectiveNormalFormUpperHalfPlaneLiftData

end

end JJMath
