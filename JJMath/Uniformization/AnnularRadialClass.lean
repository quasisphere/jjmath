import JJMath.Uniformization.AnnularLogarithm
import JJMath.Uniformization.SmoothUnitPhaseRestriction

/-!
# The normalized radial class on the annular cylinder

The unit direction on the circle factor has logarithmic differential of
period one after division by `2 * pi`.  Using the two slit-circle angle lifts,
its de Rham class is computed by the same Mayer--Vietoris connecting map as
the repository's chosen annular angular representative.  The two classes
therefore agree up to orientation.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

/-- Rotate the circle coordinate so that the chosen cut is the standard
logarithm cut, viewed as a smooth unit-complex phase. -/
noncomputable def annularCutRotationPhase (v : Circle) :
    ContMDiffMap AnnularCylinderModel (modelWithCornersSelf ℝ ℂ)
      (Circle × ℝ) ℂ ∞ where
  val := fun q ↦ (annularCutRotation v q.1 : ℂ)
  property := by
    have hcircleCoe : ContMDiff (𝓡 1) SurfaceRealModel ∞
        (fun z : Circle ↦ (z : ℂ)) :=
      contMDiff_coe_sphere
    have hdir : ContMDiff AnnularCylinderModel SurfaceRealModel ∞
        (fun q : Circle × ℝ ↦ (q.1 : ℂ)) :=
      hcircleCoe.comp contMDiff_fst
    let L : ℂ →L[ℝ] ℂ :=
      ContinuousLinearMap.mulLeftRight ℝ ℂ (-((v⁻¹ : Circle) : ℂ)) 1
    have hL : ContMDiff SurfaceRealModel SurfaceRealModel ∞ L := L.contMDiff
    simpa [L, annularCutRotation, circleAntipode,
      ContinuousLinearMap.mulLeftRight_apply, Function.comp_def, neg_mul]
      using hL.comp hdir

/--
%%handwave
name:
  The rotated circle coordinate has unit norm
statement:
  For every cut point \(v\in S^1\) and cylinder point \(q\in S^1\times
  \mathbb R\), the rotated circle phase at \(q\) has complex modulus one.
proof:
  The rotated value is again a point of the unit circle, whose inclusion in
  \(\mathbb C\) has norm one.
-/
theorem norm_annularCutRotationPhase (v : Circle) (q : Circle × ℝ) :
    ‖annularCutRotationPhase v q‖ = 1 :=
  Circle.norm_coe _

/--
%%handwave
name:
  Rotation based at the antipode of one is the identity
statement:
  For every \(q\in S^1\), rotating the circle coordinate using the cut at the
  antipode of \(1\) leaves \(q\) unchanged.
proof:
  Expand the antipode and the cut rotation; the scalar rotation reduces to
  multiplication by one.
-/
@[simp]
theorem annularCutRotation_antipode_one (q : Circle) :
    annularCutRotation (circleAntipode 1) q = q := by
  apply Subtype.ext
  simp [annularCutRotation, circleAntipode]

/-- The logarithmic one-form of the rotated circle coordinate. -/
noncomputable def annularCutRotationClosedOneForm (v : Circle) :
    DeRhamClosedForms (I := AnnularCylinderModel)
      (M := Circle × ℝ) (A := ℝ) 1 :=
  (smoothUnitPhaseCirclePrimitive AnnularCylinderModel
    (annularCutRotationPhase v) (norm_annularCutRotationPhase v)
    |>.toClosedForm AnnularCylinderModel)

/-- Divide the logarithmic circle-coordinate form by `2 * pi`. -/
noncomputable def annularRadialNormalizedClosedOneForm (v : Circle) :
    DeRhamClosedForms (I := AnnularCylinderModel)
      (M := Circle × ℝ) (A := ℝ) 1 :=
  (2 * Real.pi)⁻¹ • annularCutRotationClosedOneForm v

/--
%%handwave
name:
  Exponential of the left annular angle lift
statement:
  On the cylinder slit at \(v\), if \(\theta_L\) is the left angle lift, then
  \[
    e^{i\theta_L(q)}=R_v(q_1),
  \]
  where \(R_v\) is the rotated unit-circle coordinate and \(q_1\) is the
  circle component of \(q\).
proof:
  The rotated coordinate has modulus one.  The standard identity
  \(e^{i\arg z}=z/|z|\) therefore reduces to the desired equality, since the
  left lift is the argument of the rotated coordinate.
-/
theorem annularLeftAngleLift_exp_eq_cutRotation (v : Circle)
    (q : annularPunctureOpen v) :
    Complex.exp ((((annularLeftAngleLift v q : ℝ) : ℂ) * Complex.I)) =
      (annularCutRotation v ((q : Circle × ℝ).1) : ℂ) := by
  let z : ℂ :=
    (annularCutRotation v ((q : Circle × ℝ).1) : Circle)
  have hzNorm : ‖z‖ = 1 := Circle.norm_coe _
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hzNorm] at h
  norm_num at h
  simpa [z, annularLeftAngleLift, Complex.log_im] using h

/--
%%handwave
name:
  Exponential of the right annular angle lift
statement:
  On the cylinder slit at the point opposite \(v\), if \(\theta_R\) is the
  right angle lift, then
  \[
    e^{i\theta_R(q)}=R_v(q_1).
  \]
proof:
  Write the right lift as \(\arg(-R_v(q_1))+\pi\).  Exponentiating the sum
  gives the unit phase of \(-R_v(q_1)\) times \(e^{i\pi}=-1\), hence recovers
  \(R_v(q_1)\).
-/
theorem annularRightAngleLift_exp_eq_cutRotation (v : Circle)
    (q : annularPunctureOpen (annularOpposite v)) :
    Complex.exp ((((annularRightAngleLift v q : ℝ) : ℂ) * Complex.I)) =
      (annularCutRotation v ((q : Circle × ℝ).1) : ℂ) := by
  let z : ℂ :=
    (annularCutRotation v ((q : Circle × ℝ).1) : Circle)
  let w : ℂ := -z
  have hwNorm : ‖w‖ = 1 := by
    simp [w, z]
  have hw := Complex.norm_mul_exp_arg_mul_I w
  rw [hwNorm] at hw
  norm_num at hw
  have hsplit :
      ((((annularRightAngleLift v q : ℝ) : ℂ) * Complex.I)) =
        ((Complex.arg w : ℂ) * Complex.I) +
          ((Real.pi : ℂ) * Complex.I) := by
    simp only [annularRightAngleLift, Complex.log_im]
    change (((Complex.arg w + Real.pi : ℝ) : ℂ) * Complex.I) = _
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  rw [show Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w from hw]
  simp [Complex.exp_mul_I, w]
  rfl

/--
%%handwave
name:
  Logarithmic circle form on the left slit cylinder
statement:
  On the cylinder with the cut point \(v\) removed, the logarithmic one-form
  of the rotated circle coordinate equals \(d\theta_L\), where \(\theta_L\)
  is the left angle lift.
proof:
  Compare the restricted logarithmic primitive with the primitive obtained
  from the global argument \(\theta_L\).  Their unit phases agree by
  \(e^{i\theta_L}=R_v\), so their one-forms agree.
-/
theorem annularCutRotationClosedOneForm_restrict_left (v : Circle) :
    restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
        (annularPunctureOpen v) 1 (annularCutRotationClosedOneForm v).1 =
      deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen v) (A := ℝ) 0
        (annularLeftAngleZeroForm v) := by
  let P :=
    (smoothUnitPhaseCirclePrimitive AnnularCylinderModel
      (annularCutRotationPhase v) (norm_annularCutRotationPhase v)).restrictToOpen
        AnnularCylinderModel (annularPunctureOpen v)
  let Q := smoothCirclePrimitiveOfGlobalArgument AnnularCylinderModel
    (annularLeftAngleSmoothFunction v)
  apply SmoothCirclePrimitive.oneForm_eq_of_phase_eq AnnularCylinderModel P Q
  intro q
  change (annularCutRotation v ((q : Circle × ℝ).1) : ℂ) =
    Complex.exp ((((annularLeftAngleLift v q : ℝ) : ℂ) * Complex.I))
  exact (annularLeftAngleLift_exp_eq_cutRotation v q).symm

/--
%%handwave
name:
  Logarithmic circle form on the right slit cylinder
statement:
  On the cylinder with the point opposite \(v\) removed, the logarithmic
  one-form of the rotated circle coordinate equals \(d\theta_R\), where
  \(\theta_R\) is the right angle lift.
proof:
  Compare the restricted logarithmic primitive with the primitive defined by
  the global argument \(\theta_R\).  The equality
  \(e^{i\theta_R}=R_v\) identifies their phases and therefore their one-forms.
-/
theorem annularCutRotationClosedOneForm_restrict_right (v : Circle) :
    restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
        (annularPunctureOpen (annularOpposite v)) 1
        (annularCutRotationClosedOneForm v).1 =
      deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen (annularOpposite v)) (A := ℝ) 0
        (annularRightAngleZeroForm v) := by
  let P :=
    (smoothUnitPhaseCirclePrimitive AnnularCylinderModel
      (annularCutRotationPhase v) (norm_annularCutRotationPhase v)).restrictToOpen
        AnnularCylinderModel (annularPunctureOpen (annularOpposite v))
  let Q := smoothCirclePrimitiveOfGlobalArgument AnnularCylinderModel
    (annularRightAngleSmoothFunction v)
  apply SmoothCirclePrimitive.oneForm_eq_of_phase_eq AnnularCylinderModel P Q
  intro q
  change (annularCutRotation v ((q : Circle × ℝ).1) : ℂ) =
    Complex.exp ((((annularRightAngleLift v q : ℝ) : ℂ) * Complex.I))
  exact (annularRightAngleLift_exp_eq_cutRotation v q).symm

/-- The normalized angle jump on the overlap. -/
noncomputable def annularRadialTransitionClosedForm (v : Circle) :
    DeRhamClosedForms (I := AnnularCylinderModel)
      (M := annularDoublePunctureOpen v) (A := ℝ) 0 :=
  (2 * Real.pi)⁻¹ • annularAngleTransitionClosedForm v

/-- Connecting data computing the normalized radial class from the two
normalized slit-circle angle lifts. -/
noncomputable def annularRadialConnectingData (v : Circle) :
    DeRhamMayerVietorisConnectingData (I := AnnularCylinderModel) (A := ℝ)
      (annularPunctureOpen v)
      (annularPunctureOpen (annularOpposite v))
      (annularPunctures_cover v) 0 (annularRadialTransitionClosedForm v) where
  lift :=
    ((2 * Real.pi)⁻¹ • annularLeftAngleZeroForm v,
      (2 * Real.pi)⁻¹ • annularRightAngleZeroForm v)
  lift_difference := by
    change
      restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
          inf_le_left 0 ((2 * Real.pi)⁻¹ • annularLeftAngleZeroForm v) -
        restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
          inf_le_right 0 ((2 * Real.pi)⁻¹ • annularRightAngleZeroForm v) =
      ((2 * Real.pi)⁻¹ • annularAngleTransitionClosedForm v).1
    change
      restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
          inf_le_left 0 ((2 * Real.pi)⁻¹ • annularLeftAngleZeroForm v) -
        restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
          inf_le_right 0 ((2 * Real.pi)⁻¹ • annularRightAngleZeroForm v) =
      (2 * Real.pi)⁻¹ • (annularAngleTransitionClosedForm v).1
    rw [map_smul, map_smul]
    have hbase :
        restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
            inf_le_left 0 (annularLeftAngleZeroForm v) -
          restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
            inf_le_right 0 (annularRightAngleZeroForm v) =
        (annularAngleTransitionClosedForm v).1 := by
      apply DifferentialForm.ext
      intro x
      ext q
      rw [show q = (fun i : Fin 0 ↦ nomatch i) from Subsingleton.elim _ _]
      rfl
    rw [← hbase]
    exact (smul_sub (2 * Real.pi)⁻¹
      (restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
        inf_le_left 0 (annularLeftAngleZeroForm v))
      (restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
        inf_le_right 0 (annularRightAngleZeroForm v))).symm
  glued := annularRadialNormalizedClosedOneForm v
  glued_restriction := by
    apply Prod.ext
    · change restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
          (annularPunctureOpen v) 1
          ((2 * Real.pi)⁻¹ • (annularCutRotationClosedOneForm v).1) =
        deRhamDifferential (I := AnnularCylinderModel)
          (M := annularPunctureOpen v) (A := ℝ) 0
          ((2 * Real.pi)⁻¹ • annularLeftAngleZeroForm v)
      rw [map_smul, map_smul,
        annularCutRotationClosedOneForm_restrict_left]
    · change restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
          (annularPunctureOpen (annularOpposite v)) 1
          ((2 * Real.pi)⁻¹ • (annularCutRotationClosedOneForm v).1) =
        deRhamDifferential (I := AnnularCylinderModel)
          (M := annularPunctureOpen (annularOpposite v)) (A := ℝ) 0
          ((2 * Real.pi)⁻¹ • annularRightAngleZeroForm v)
      rw [map_smul, map_smul,
        annularCutRotationClosedOneForm_restrict_right]

/--
%%handwave
name:
  The normalized radial class equals the annular angular class up to sign
statement:
  The de Rham class of \((2\pi)^{-1}d\log R_v\) on
  \(S^1\times\mathbb R\) is either the chosen annular angular class or its
  negative.
proof:
  Compute the radial class by the Mayer--Vietoris connecting map for the two
  slit cylinders, using the normalized difference of their angle lifts on the
  overlap.  Linearity pulls out the factor \((2\pi)^{-1}\).  The unnormalized
  angle transition has coefficient \(2\pi\) or \(-2\pi\) relative to the
  chosen angular generator, so normalization leaves coefficient \(1\) or
  \(-1\).
-/
theorem annularRadialNormalizedClosedOneForm_class_eq_or_neg (v : Circle) :
    (DeRhamExactClosedForms (I := AnnularCylinderModel)
        (M := Circle × ℝ) (A := ℝ) 1).mkQ
          (annularRadialNormalizedClosedOneForm v) =
        (DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1).mkQ
            (annularAngularClosedForm v) ∨
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
        (M := Circle × ℝ) (A := ℝ) 1).mkQ
          (annularRadialNormalizedClosedOneForm v) =
        -(DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1).mkQ
            (annularAngularClosedForm v) := by
  let connecting :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ)
      AnnularCylinderModel (annularPunctureOpen v)
      (annularPunctureOpen (annularOpposite v))
      (annularPunctures_cover v) 0
  have hradial :
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1).mkQ
            (annularRadialNormalizedClosedOneForm v) =
        connecting
          ((DeRhamExactClosedForms (I := AnnularCylinderModel)
            (M := annularDoublePunctureOpen v) (A := ℝ) 0).mkQ
              (annularRadialTransitionClosedForm v)) := by
    symm
    exact deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
      (A := ℝ) AnnularCylinderModel
      (annularPunctureOpen v)
      (annularPunctureOpen (annularOpposite v))
      (annularPunctures_cover v) 0
      (annularRadialTransitionClosedForm v)
      (annularRadialConnectingData v)
  have htransition :
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := annularDoublePunctureOpen v) (A := ℝ) 0).mkQ
            (annularRadialTransitionClosedForm v) =
        (2 * Real.pi)⁻¹ • annularAngleTransitionClass v := by
    simp [annularRadialTransitionClosedForm, annularAngleTransitionClass]
  have hconnectSmul :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity_smul
      AnnularCylinderModel (annularPunctureOpen v)
      (annularPunctureOpen (annularOpposite v))
      (annularPunctures_cover v) 0 (2 * Real.pi)⁻¹
      (annularAngleTransitionClass v)
  change connecting ((2 * Real.pi)⁻¹ • annularAngleTransitionClass v) =
      (2 * Real.pi)⁻¹ • connecting (annularAngleTransitionClass v)
    at hconnectSmul
  have hangle :
      connecting (annularAngleTransitionClass v) =
        annularAngleTransitionCoefficient v •
          (DeRhamExactClosedForms (I := AnnularCylinderModel)
            (M := Circle × ℝ) (A := ℝ) 1).mkQ
              (annularAngularClosedForm v) := by
    simpa [connecting] using
      annularAngleTransition_connecting_eq_angular_class v
  have hclass :
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1).mkQ
            (annularRadialNormalizedClosedOneForm v) =
        ((2 * Real.pi)⁻¹ * annularAngleTransitionCoefficient v) •
          (DeRhamExactClosedForms (I := AnnularCylinderModel)
            (M := Circle × ℝ) (A := ℝ) 1).mkQ
              (annularAngularClosedForm v) := by
    rw [hradial, htransition, hconnectSmul, hangle, smul_smul]
  rcases annularAngleTransitionCoefficient_eq_two_pi_or_neg v with h | h
  · left
    rw [h] at hclass
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hscalar : (2 * Real.pi)⁻¹ * (2 * Real.pi) = (1 : ℝ) :=
      inv_mul_cancel₀ htwoPi
    rw [hscalar, one_smul] at hclass
    exact hclass
  · right
    rw [h] at hclass
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hscalar : (2 * Real.pi)⁻¹ * (-(2 * Real.pi)) = (-1 : ℝ) := by
      rw [mul_neg, inv_mul_cancel₀ htwoPi]
    rw [hscalar, neg_one_smul] at hclass
    exact hclass

end

end JJMath.Uniformization
