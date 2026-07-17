import JJMath.Uniformization.ExteriorAngularExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.RealDeriv

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

local instance isScalarTowerRealComplexComplex :
    IsScalarTower ℝ ℂ ℂ := IsScalarTower.right

noncomputable def circleAntipode (v : Circle) : Circle :=
  ⟨-(v : ℂ), by
    simp [Submonoid.unitSphere, Circle.norm_coe v]⟩

theorem annularOpposite_eq_antipode (v : Circle) :
    annularOpposite v = circleAntipode v := by
  apply Subtype.ext
  change (((stereographic' 1 v).symm 0 : Circle) : ℂ) = -(v : ℂ)
  rw [stereographic'_symm_apply]
  simp

@[simp]
theorem circleAntipode_coe (v : Circle) :
    (circleAntipode v : ℂ) = -(v : ℂ) := rfl

theorem circle_mem_slitPlane_iff_ne_negOne (q : Circle) :
    (q : ℂ) ∈ Complex.slitPlane ↔ q ≠ circleAntipode 1 := by
  let s : Set ℂ := {(q : ℂ)}
  have hs : s ⊆ Metric.sphere (0 : ℂ) 1 := by
    intro z hz
    simp only [s, Set.mem_singleton_iff] at hz
    subst z
    simpa [Metric.mem_sphere] using Circle.norm_coe q
  have h := Complex.subset_slitPlane_iff_of_subset_sphere hs
  constructor
  · intro hq heq
    have hcoe := congrArg Subtype.val heq
    have : (q : ℂ) = -1 := by simpa [circleAntipode] using hcoe
    rw [this] at hq
    norm_num [Complex.mem_slitPlane_iff] at hq
  · intro hq
    have hneg : (-1 : ℂ) ∉ s := by
      intro hmem
      have heq : (-1 : ℂ) = (q : ℂ) := by simpa [s] using hmem
      apply hq
      apply Subtype.ext
      simpa [circleAntipode] using heq.symm
    exact h.mpr hneg (by simp [s])

@[simp]
theorem circleAntipode_involutive (q : Circle) :
    circleAntipode (circleAntipode q) = q := by
  apply Subtype.ext
  simp [circleAntipode]

@[simp]
theorem mul_circleAntipode_one (q : Circle) :
    q * circleAntipode 1 = circleAntipode q := by
  apply Subtype.ext
  simp [circleAntipode]

noncomputable def annularCutRotation (v q : Circle) : Circle :=
  circleAntipode (v⁻¹ * q)

@[simp]
theorem annularCutRotation_self (v : Circle) :
    annularCutRotation v v = circleAntipode 1 := by
  simp [annularCutRotation]

theorem annularCutRotation_ne_negOne_iff (v q : Circle) :
    annularCutRotation v q ≠ circleAntipode 1 ↔ q ≠ v := by
  constructor
  · intro hrot hq
    rw [hq] at hrot
    exact hrot (annularCutRotation_self v)
  · intro hq heq
    have hcoe := congrArg Subtype.val heq
    have hrot : (v⁻¹ : Circle) * q = 1 := by
      apply Subtype.ext
      simpa [annularCutRotation] using hcoe
    have hqv : q = v := by
      calc
        q = v * (v⁻¹ * q) := by simp
        _ = v * 1 := congrArg (fun w : Circle => v * w) hrot
        _ = v := mul_one v
    exact hq hqv

theorem annularCutRotation_mem_slitPlane_iff (v q : Circle) :
    (annularCutRotation v q : ℂ) ∈ Complex.slitPlane ↔ q ≠ v := by
  rw [circle_mem_slitPlane_iff_ne_negOne,
    annularCutRotation_ne_negOne_iff]

theorem annularCutRotation_eq_one_iff (v q : Circle) :
    annularCutRotation v q = 1 ↔ q = annularOpposite v := by
  constructor
  · intro hrot
    have hbase := congrArg circleAntipode hrot
    have hbase' : v⁻¹ * q = circleAntipode 1 := by
      simpa [annularCutRotation] using hbase
    calc
      q = v * (v⁻¹ * q) := by simp
      _ = v * circleAntipode 1 :=
        congrArg (fun w : Circle => v * w) hbase'
      _ = circleAntipode v := mul_circleAntipode_one v
      _ = annularOpposite v := (annularOpposite_eq_antipode v).symm
  · intro hq
    rw [hq, annularOpposite_eq_antipode]
    apply Subtype.ext
    simp [annularCutRotation, circleAntipode]

theorem secondCut_mem_slitPlane_iff (v q : Circle) :
    (circleAntipode (annularCutRotation v q) : ℂ) ∈
        Complex.slitPlane ↔ q ≠ annularOpposite v := by
  rw [circle_mem_slitPlane_iff_ne_negOne]
  constructor
  · intro h hq
    apply h
    rw [hq, annularOpposite_eq_antipode]
    apply Subtype.ext
    simp [annularCutRotation, circleAntipode]
  · intro hq h
    have hrot : annularCutRotation v q = 1 := by
      have := congrArg circleAntipode h
      simpa using this
    exact hq ((annularCutRotation_eq_one_iff v q).mp hrot)

noncomputable def annularLeftAngleLift (v : Circle)
    (q : annularPunctureOpen v) : ℝ :=
  (Complex.log
    (annularCutRotation v ((q : Circle × ℝ).1) : ℂ)).im

noncomputable def annularRightAngleLift (v : Circle)
    (q : annularPunctureOpen (annularOpposite v)) : ℝ :=
  (Complex.log
    (circleAntipode
      (annularCutRotation v ((q : Circle × ℝ).1)) : ℂ)).im +
    Real.pi

theorem contMDiff_annularCutRotation_val (v : Circle)
    (U : TopologicalSpace.Opens (Circle × ℝ)) :
    ContMDiff AnnularCylinderModel 𝓘(ℝ, ℂ) ∞
      (fun q : U =>
        (annularCutRotation v ((q : Circle × ℝ).1) : ℂ)) := by
  have hcircleCoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  have hdir : ContMDiff AnnularCylinderModel 𝓘(ℝ, ℂ) ∞
      (fun q : U => (((q : Circle × ℝ).1 : Circle) : ℂ)) :=
    hcircleCoe.comp (contMDiff_fst.comp contMDiff_subtype_val)
  have hconst : ContMDiff AnnularCylinderModel 𝓘(ℝ, ℂ) ∞
      (fun _ : U => -((v⁻¹ : Circle) : ℂ)) := contMDiff_const
  let L : ℂ →L[ℝ] ℂ :=
    ContinuousLinearMap.mulLeftRight ℝ ℂ (-((v⁻¹ : Circle) : ℂ)) 1
  have hL : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ L := L.contMDiff
  simpa [L, ContinuousLinearMap.mulLeftRight_apply, Function.comp_def,
    annularCutRotation, circleAntipode, neg_mul] using
    hL.comp hdir

theorem contMDiff_complexLog_comp_annularCutRotation (v : Circle) :
    ContMDiff AnnularCylinderModel 𝓘(ℝ, ℂ) ∞
      (fun q : annularPunctureOpen v =>
        Complex.log
          (annularCutRotation v ((q : Circle × ℝ).1) : ℂ)) := by
  have hlogC : ContDiffOn ℂ ∞ Complex.log Complex.slitPlane :=
    (analyticOnNhd_id.clog (fun z hz => hz)).contDiffOn
      Complex.isOpen_slitPlane.uniqueDiffOn
  have hlogR : ContDiffOn ℝ ∞ Complex.log Complex.slitPlane :=
    @ContDiffOn.restrict_scalars ℝ inferInstance
      ℂ inferInstance inferInstance ℂ inferInstance inferInstance
      Complex.slitPlane Complex.log ∞
      ℂ inferInstance inferInstance inferInstance
      (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      inferInstance (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      hlogC
  have hlogM : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      Complex.log Complex.slitPlane :=
    contMDiffOn_iff_contDiffOn.mpr hlogR
  have hrot := contMDiff_annularCutRotation_val v
    (annularPunctureOpen v)
  rw [← contMDiffOn_univ]
  have hrotOn : ContMDiffOn AnnularCylinderModel 𝓘(ℝ, ℂ) ∞
      (fun q : annularPunctureOpen v =>
        (annularCutRotation v ((q : Circle × ℝ).1) : ℂ))
      Set.univ := hrot.contMDiffOn
  have hcomp := hlogM.comp hrotOn (by
    intro q _hq
    exact (annularCutRotation_mem_slitPlane_iff
      v ((q : Circle × ℝ).1)).mpr
        ((mem_annularPunctureOpen_iff v (q : Circle × ℝ)).mp q.2))
  simpa [Function.comp_def] using hcomp

theorem contMDiff_annularLeftAngleLift (v : Circle) :
    ContMDiff AnnularCylinderModel 𝓘(ℝ, ℝ) ∞
      (annularLeftAngleLift v) := by
  have him : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun z : ℂ => z.im) :=
    contMDiff_iff_contDiff.mpr Complex.imCLM.contDiff
  simpa [annularLeftAngleLift] using
    him.comp (contMDiff_complexLog_comp_annularCutRotation v)

theorem contMDiff_complexLog_comp_secondCut (v : Circle) :
    ContMDiff AnnularCylinderModel 𝓘(ℝ, ℂ) ∞
      (fun q : annularPunctureOpen (annularOpposite v) =>
        Complex.log
          (circleAntipode
            (annularCutRotation v ((q : Circle × ℝ).1)) : ℂ)) := by
  have hlogC : ContDiffOn ℂ ∞ Complex.log Complex.slitPlane :=
    (analyticOnNhd_id.clog (fun z hz => hz)).contDiffOn
      Complex.isOpen_slitPlane.uniqueDiffOn
  have hlogR : ContDiffOn ℝ ∞ Complex.log Complex.slitPlane :=
    @ContDiffOn.restrict_scalars ℝ inferInstance
      ℂ inferInstance inferInstance ℂ inferInstance inferInstance
      Complex.slitPlane Complex.log ∞
      ℂ inferInstance inferInstance inferInstance
      (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      inferInstance (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      hlogC
  have hlogM : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      Complex.log Complex.slitPlane :=
    contMDiffOn_iff_contDiffOn.mpr hlogR
  have hrot := contMDiff_annularCutRotation_val v
    (annularPunctureOpen (annularOpposite v))
  have hneg : ContMDiff AnnularCylinderModel 𝓘(ℝ, ℂ) ∞
      (fun q : annularPunctureOpen (annularOpposite v) =>
        (circleAntipode
          (annularCutRotation v ((q : Circle × ℝ).1)) : ℂ)) := by
    simpa [circleAntipode] using hrot.neg
  rw [← contMDiffOn_univ]
  have hnegOn : ContMDiffOn AnnularCylinderModel 𝓘(ℝ, ℂ) ∞
      (fun q : annularPunctureOpen (annularOpposite v) =>
        (circleAntipode
          (annularCutRotation v ((q : Circle × ℝ).1)) : ℂ))
      Set.univ := hneg.contMDiffOn
  have hcomp := hlogM.comp hnegOn (by
    intro q _hq
    exact (secondCut_mem_slitPlane_iff
      v ((q : Circle × ℝ).1)).mpr
        ((mem_annularPunctureOpen_iff (annularOpposite v)
          (q : Circle × ℝ)).mp q.2))
  simpa [Function.comp_def] using hcomp

theorem contMDiff_annularRightAngleLift (v : Circle) :
    ContMDiff AnnularCylinderModel 𝓘(ℝ, ℝ) ∞
      (annularRightAngleLift v) := by
  have him : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun z : ℂ => z.im) :=
    contMDiff_iff_contDiff.mpr Complex.imCLM.contDiff
  have hbase := him.comp
    (contMDiff_complexLog_comp_secondCut v)
  simpa [annularRightAngleLift] using hbase.add contMDiff_const

theorem circle_im_ne_zero_of_ne_one_ne_negOne
    (q : Circle) (hone : q ≠ 1)
    (hneg : q ≠ circleAntipode 1) :
    (q : ℂ).im ≠ 0 := by
  intro him
  have hnormSq : Complex.normSq (q : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  have hreSq : (q : ℂ).re ^ 2 = 1 := by
    rw [Complex.normSq_apply, him, mul_zero, add_zero] at hnormSq
    simpa [pow_two] using hnormSq
  rcases sq_eq_one_iff.mp hreSq with hre | hre
  · apply hone
    apply Subtype.ext
    apply Complex.ext
    · simpa using hre
    · simp [him]
  · apply hneg
    apply Subtype.ext
    apply Complex.ext
    · simpa [circleAntipode] using hre
    · simp [circleAntipode, him]

theorem annularCutRotation_im_ne_zero_on_overlap
    (v : Circle) (x : annularDoublePunctureOpen v) :
    ((annularCutRotation v ((x : Circle × ℝ).1) : Circle) : ℂ).im ≠ 0 := by
  apply circle_im_ne_zero_of_ne_one_ne_negOne
  · intro hone
    have hqopp := (annularCutRotation_eq_one_iff
      v ((x : Circle × ℝ).1)).mp hone
    exact ((mem_annularPunctureOpen_iff (annularOpposite v)
      (x : Circle × ℝ)).mp x.2.2) hqopp
  · exact (annularCutRotation_ne_negOne_iff
      v ((x : Circle × ℝ).1)).mpr
        ((mem_annularPunctureOpen_iff v (x : Circle × ℝ)).mp x.2.1)

theorem annularAngleLift_difference (v : Circle)
    (x : annularDoublePunctureOpen v) :
    annularLeftAngleLift v
        (TopologicalSpace.Opens.inclusion inf_le_left x) -
      annularRightAngleLift v
        (TopologicalSpace.Opens.inclusion inf_le_right x) =
      if 0 <
          ((annularCutRotation v ((x : Circle × ℝ).1) : Circle) : ℂ).im
        then 0 else -(2 * Real.pi) := by
  let z : ℂ :=
    (annularCutRotation v ((x : Circle × ℝ).1) : Circle)
  have hzim : z.im ≠ 0 :=
    annularCutRotation_im_ne_zero_on_overlap v x
  by_cases hpos : 0 < z.im
  · rw [if_pos hpos]
    change (Complex.log z).im -
      ((Complex.log (-z)).im + Real.pi) = 0
    rw [Complex.log_im, Complex.log_im]
    rw [show Complex.arg (-z) = Complex.arg z - Real.pi from
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hpos]
    ring
  · have hneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzim
    rw [if_neg hpos]
    change (Complex.log z).im -
      ((Complex.log (-z)).im + Real.pi) = -(2 * Real.pi)
    rw [Complex.log_im, Complex.log_im]
    rw [show Complex.arg (-z) = Complex.arg z + Real.pi from
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hneg]
    ring

theorem annularPositiveComponent_isPreconnected (v : Circle) :
    IsPreconnected (Set.univ : Set (annularPositiveComponent v)) := by
  rcases annularPositiveComponent_diffeomorph v with ⟨phi⟩
  letI : PreconnectedSpace annularPositiveTarget :=
    Subtype.preconnectedSpace annularPositiveTarget_convex.isPreconnected
  have hpre :=
    (phi.toHomeomorph.isPreconnected_preimage (s := Set.univ)).mpr
      (isPreconnected_univ : IsPreconnected
        (Set.univ : Set annularPositiveTarget))
  simpa using hpre

theorem annularNegativeComponent_isPreconnected (v : Circle) :
    IsPreconnected (Set.univ : Set (annularNegativeComponent v)) := by
  rcases annularNegativeComponent_diffeomorph v with ⟨phi⟩
  letI : PreconnectedSpace annularNegativeTarget :=
    Subtype.preconnectedSpace annularNegativeTarget_convex.isPreconnected
  have hpre :=
    (phi.toHomeomorph.isPreconnected_preimage (s := Set.univ)).mpr
      (isPreconnected_univ : IsPreconnected
        (Set.univ : Set annularNegativeTarget))
  simpa using hpre

noncomputable def annularCutUpperIndicator (v : Circle)
    (x : annularDoublePunctureOpen v) : ℝ :=
  if 0 <
      ((annularCutRotation v ((x : Circle × ℝ).1) : Circle) : ℂ).im
    then 1 else 0

theorem annularCutUpperIndicator_isLocallyConstant (v : Circle) :
    IsLocallyConstant (annularCutUpperIndicator v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let f : annularDoublePunctureOpen v → ℝ := fun y =>
    ((annularCutRotation v ((y : Circle × ℝ).1) : Circle) : ℂ).im
  have hf : Continuous f := by
    have hrot := contMDiff_annularCutRotation_val v
      (annularDoublePunctureOpen v)
    have him : Continuous (fun z : ℂ => z.im) := Complex.imCLM.continuous
    simpa [f, Function.comp_def] using him.comp hrot.continuous
  by_cases hx : 0 < f x
  · filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hx] with y hy
    simp [annularCutUpperIndicator, f, hx, hy]
  · have hxne : f x ≠ 0 :=
      annularCutRotation_im_ne_zero_on_overlap v x
    have hxneg : f x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
    filter_upwards [(isOpen_lt hf continuous_const).mem_nhds hxneg] with y hy
    have hynot : ¬0 < f y := not_lt.mpr hy.le
    simp [annularCutUpperIndicator, f, hx, hynot]

theorem annularCutUpperIndicator_eq_on_positive (v : Circle)
    (a b : annularPositiveComponent v) :
    annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) a) =
      annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) b) := by
  have hloc := (annularCutUpperIndicator_isLocallyConstant v).comp_continuous
    (continuous_inclusion (annularPositiveComponent_le_doublePuncture v))
  exact hloc.apply_eq_of_isPreconnected
    (annularPositiveComponent_isPreconnected v) (Set.mem_univ a) (Set.mem_univ b)

theorem annularCutUpperIndicator_eq_on_negative (v : Circle)
    (a b : annularNegativeComponent v) :
    annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularNegativeComponent_le_doublePuncture v) a) =
      annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularNegativeComponent_le_doublePuncture v) b) := by
  have hloc := (annularCutUpperIndicator_isLocallyConstant v).comp_continuous
    (continuous_inclusion (annularNegativeComponent_le_doublePuncture v))
  exact hloc.apply_eq_of_isPreconnected
    (annularNegativeComponent_isPreconnected v) (Set.mem_univ a) (Set.mem_univ b)

noncomputable def annularCutRotationInverse (v r : Circle) : Circle :=
  v * circleAntipode r

@[simp]
theorem annularCutRotation_inverse (v r : Circle) :
    annularCutRotation v (annularCutRotationInverse v r) = r := by
  simp [annularCutRotation, annularCutRotationInverse]

noncomputable def annularRotationPoint (v r : Circle)
    (hneg : r ≠ circleAntipode 1) (hone : r ≠ 1) :
    annularDoublePunctureOpen v := by
  refine ⟨(annularCutRotationInverse v r, 0), ?_⟩
  constructor
  · apply (mem_annularPunctureOpen_iff v _).mpr
    apply (annularCutRotation_ne_negOne_iff v _).mp
    simpa using hneg
  · apply (mem_annularPunctureOpen_iff (annularOpposite v) _).mpr
    intro hq
    have hrot : annularCutRotation v
        (annularCutRotationInverse v r) = 1 :=
      (annularCutRotation_eq_one_iff v _).mpr hq
    rw [annularCutRotation_inverse] at hrot
    exact hone hrot

noncomputable def circleI : Circle := Circle.exp (Real.pi / 2)

@[simp]
theorem circleI_coe : (circleI : ℂ) = Complex.I := by
  rw [circleI, Circle.coe_exp, Complex.exp_mul_I]
  simp

theorem circleI_ne_one : circleI ≠ 1 := by
  intro h
  have hcoe := congrArg Subtype.val h
  have him := congrArg Complex.im hcoe
  norm_num at him

theorem circleI_ne_negOne :
    circleI ≠ circleAntipode 1 := by
  intro h
  have hcoe := congrArg Subtype.val h
  have him := congrArg Complex.im hcoe
  norm_num [circleAntipode] at him

noncomputable def circleNegI : Circle :=
  circleAntipode circleI

@[simp]
theorem circleNegI_coe : (circleNegI : ℂ) = -Complex.I := by
  simp [circleNegI, circleAntipode]

theorem circleNegI_ne_one : circleNegI ≠ 1 := by
  intro h
  have hcoe := congrArg Subtype.val h
  have him := congrArg Complex.im hcoe
  norm_num [circleNegI, circleAntipode] at him

theorem circleNegI_ne_negOne :
    circleNegI ≠ circleAntipode 1 := by
  intro h
  have hcoe := congrArg Subtype.val h
  have him := congrArg Complex.im hcoe
  norm_num [circleNegI, circleAntipode] at him

noncomputable def annularUpperTestPoint (v : Circle) :
    annularDoublePunctureOpen v :=
  annularRotationPoint v circleI
    circleI_ne_negOne circleI_ne_one

noncomputable def annularLowerTestPoint (v : Circle) :
    annularDoublePunctureOpen v :=
  annularRotationPoint v circleNegI
    circleNegI_ne_negOne circleNegI_ne_one

theorem annularUpperTestPoint_indicator (v : Circle) :
    annularCutUpperIndicator v (annularUpperTestPoint v) = 1 := by
  simp [annularCutUpperIndicator, annularUpperTestPoint,
    annularRotationPoint, circleI]

theorem annularLowerTestPoint_indicator (v : Circle) :
    annularCutUpperIndicator v (annularLowerTestPoint v) = 0 := by
  simp [annularCutUpperIndicator, annularLowerTestPoint,
    annularRotationPoint, circleNegI, circleI]

theorem annularOverlap_mem_positive_or_negative (v : Circle)
    (x : annularDoublePunctureOpen v) :
    (x : Circle × ℝ) ∈ (annularPositiveComponent v : Set (Circle × ℝ)) ∨
      (x : Circle × ℝ) ∈ (annularNegativeComponent v : Set (Circle × ℝ)) := by
  have hx : (x : Circle × ℝ) ∈
      (annularPositiveComponent v ⊔ annularNegativeComponent v :
        TopologicalSpace.Opens (Circle × ℝ)) := by
    rw [annularComponents_cover_doublePuncture v]
    exact x.2
  exact hx

theorem annularCutUpperIndicator_eq_positive_reference
    (v : Circle) (x : annularDoublePunctureOpen v)
    (hx : (x : Circle × ℝ) ∈
      (annularPositiveComponent v : Set (Circle × ℝ)))
    (a : annularPositiveComponent v) :
    annularCutUpperIndicator v x =
      annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) a) := by
  let xPos : annularPositiveComponent v := ⟨(x : Circle × ℝ), hx⟩
  simpa [xPos] using
    (annularCutUpperIndicator_eq_on_positive v xPos a)

theorem annularCutUpperIndicator_eq_negative_reference
    (v : Circle) (x : annularDoublePunctureOpen v)
    (hx : (x : Circle × ℝ) ∈
      (annularNegativeComponent v : Set (Circle × ℝ)))
    (b : annularNegativeComponent v) :
    annularCutUpperIndicator v x =
      annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularNegativeComponent_le_doublePuncture v) b) := by
  let xNeg : annularNegativeComponent v := ⟨(x : Circle × ℝ), hx⟩
  simpa [xNeg] using
    (annularCutUpperIndicator_eq_on_negative v xNeg b)

theorem annularCutUpperIndicator_positive_ne_negative
    (v : Circle) (a : annularPositiveComponent v)
    (b : annularNegativeComponent v) :
    annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) a) ≠
      annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularNegativeComponent_le_doublePuncture v) b) := by
  intro hab
  let u := annularUpperTestPoint v
  let l := annularLowerTestPoint v
  have huCover := annularOverlap_mem_positive_or_negative v u
  have hlCover := annularOverlap_mem_positive_or_negative v l
  have huEq : annularCutUpperIndicator v u =
      annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) a) := by
    rcases huCover with huPos | huNeg
    · exact annularCutUpperIndicator_eq_positive_reference
        v u huPos a
    · calc
        annularCutUpperIndicator v u =
            annularCutUpperIndicator v
              (TopologicalSpace.Opens.inclusion
                (annularNegativeComponent_le_doublePuncture v) b) :=
          annularCutUpperIndicator_eq_negative_reference v u huNeg b
        _ = annularCutUpperIndicator v
              (TopologicalSpace.Opens.inclusion
                (annularPositiveComponent_le_doublePuncture v) a) := hab.symm
  have hlEq : annularCutUpperIndicator v l =
      annularCutUpperIndicator v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) a) := by
    rcases hlCover with hlPos | hlNeg
    · exact annularCutUpperIndicator_eq_positive_reference
        v l hlPos a
    · calc
        annularCutUpperIndicator v l =
            annularCutUpperIndicator v
              (TopologicalSpace.Opens.inclusion
                (annularNegativeComponent_le_doublePuncture v) b) :=
          annularCutUpperIndicator_eq_negative_reference v l hlNeg b
        _ = annularCutUpperIndicator v
              (TopologicalSpace.Opens.inclusion
                (annularPositiveComponent_le_doublePuncture v) a) := hab.symm
  have hul : annularCutUpperIndicator v u =
      annularCutUpperIndicator v l := huEq.trans hlEq.symm
  rw [show annularCutUpperIndicator v u = 1 by
        simpa [u] using annularUpperTestPoint_indicator v,
      show annularCutUpperIndicator v l = 0 by
        simpa [l] using annularLowerTestPoint_indicator v] at hul
  norm_num at hul

noncomputable def annularAngleTransition (v : Circle)
    (x : annularDoublePunctureOpen v) : ℝ :=
  annularLeftAngleLift v
      (TopologicalSpace.Opens.inclusion inf_le_left x) -
    annularRightAngleLift v
      (TopologicalSpace.Opens.inclusion inf_le_right x)

theorem annularAngleTransition_eq_indicator (v : Circle)
    (x : annularDoublePunctureOpen v) :
    annularAngleTransition v x =
      -(2 * Real.pi) * (1 - annularCutUpperIndicator v x) := by
  unfold annularAngleTransition
  rw [annularAngleLift_difference]
  by_cases hpos : 0 <
      ((annularCutRotation v ((x : Circle × ℝ).1) : Circle) : ℂ).im
  · simp [annularCutUpperIndicator, hpos]
  · simp [annularCutUpperIndicator, hpos]

theorem annularCutUpperIndicator_eq_zero_or_one (v : Circle)
    (x : annularDoublePunctureOpen v) :
    annularCutUpperIndicator v x = 0 ∨
      annularCutUpperIndicator v x = 1 := by
  by_cases hpos : 0 <
      ((annularCutRotation v ((x : Circle × ℝ).1) : Circle) : ℂ).im
  · exact Or.inr (by simp [annularCutUpperIndicator, hpos])
  · exact Or.inl (by simp [annularCutUpperIndicator, hpos])

theorem annularAngleTransition_eq_on_positive (v : Circle)
    (a b : annularPositiveComponent v) :
    annularAngleTransition v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) a) =
      annularAngleTransition v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) b) := by
  rw [annularAngleTransition_eq_indicator,
    annularAngleTransition_eq_indicator,
    annularCutUpperIndicator_eq_on_positive v a b]

theorem annularAngleTransition_eq_on_negative (v : Circle)
    (a b : annularNegativeComponent v) :
    annularAngleTransition v
        (TopologicalSpace.Opens.inclusion
          (annularNegativeComponent_le_doublePuncture v) a) =
      annularAngleTransition v
        (TopologicalSpace.Opens.inclusion
          (annularNegativeComponent_le_doublePuncture v) b) := by
  rw [annularAngleTransition_eq_indicator,
    annularAngleTransition_eq_indicator,
    annularCutUpperIndicator_eq_on_negative v a b]

theorem annularAngleTransition_coefficient (v : Circle)
    (a : annularPositiveComponent v) (b : annularNegativeComponent v) :
    let epsilon :=
      annularAngleTransition v
          (TopologicalSpace.Opens.inclusion
            (annularPositiveComponent_le_doublePuncture v) a) -
        annularAngleTransition v
          (TopologicalSpace.Opens.inclusion
            (annularNegativeComponent_le_doublePuncture v) b)
    epsilon = 2 * Real.pi ∨ epsilon = -(2 * Real.pi) := by
  dsimp only
  let aO : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularPositiveComponent_le_doublePuncture v) a
  let bO : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularNegativeComponent_le_doublePuncture v) b
  have hne : annularCutUpperIndicator v aO ≠
      annularCutUpperIndicator v bO :=
    annularCutUpperIndicator_positive_ne_negative v a b
  rcases annularCutUpperIndicator_eq_zero_or_one v aO with ha | ha <;>
    rcases annularCutUpperIndicator_eq_zero_or_one v bO with hb | hb
  · exact (hne (ha.trans hb.symm)).elim
  · right
    rw [annularAngleTransition_eq_indicator,
      annularAngleTransition_eq_indicator, ha, hb]
    ring
  · left
    rw [annularAngleTransition_eq_indicator,
      annularAngleTransition_eq_indicator, ha, hb]
    ring
  · exact (hne (ha.trans hb.symm)).elim

theorem annularAngleTransition_decomposition (v : Circle)
    (a : annularPositiveComponent v) (b : annularNegativeComponent v)
    (x : annularDoublePunctureOpen v) :
    let aO : annularDoublePunctureOpen v :=
      TopologicalSpace.Opens.inclusion
        (annularPositiveComponent_le_doublePuncture v) a
    let bO : annularDoublePunctureOpen v :=
      TopologicalSpace.Opens.inclusion
        (annularNegativeComponent_le_doublePuncture v) b
    annularAngleTransition v x =
      annularAngleTransition v bO +
        (annularAngleTransition v aO -
          annularAngleTransition v bO) *
            annularOverlapStepFunction v x := by
  dsimp only
  rcases annularOverlap_mem_positive_or_negative v x with hxPos | hxNeg
  · let xPos : annularPositiveComponent v := ⟨(x : Circle × ℝ), hxPos⟩
    have hxEq := annularAngleTransition_eq_on_positive v xPos a
    have hxStep : x ∈ annularOverlapPositiveSet v := hxPos
    simpa [xPos, annularOverlapStepFunction, hxStep] using hxEq
  · let xNeg : annularNegativeComponent v := ⟨(x : Circle × ℝ), hxNeg⟩
    have hxEq := annularAngleTransition_eq_on_negative v xNeg b
    have hxStep : x ∉ annularOverlapPositiveSet v := by
      intro hpos
      have hmem : (x : Circle × ℝ) ∈
          (annularPositiveComponent v ⊓ annularNegativeComponent v :
            TopologicalSpace.Opens (Circle × ℝ)) := ⟨hpos, hxNeg⟩
      rw [annularComponents_disjoint v] at hmem
      exact hmem
    simpa [xNeg, annularOverlapStepFunction, hxStep] using hxEq

noncomputable def annularLeftAngleSmoothFunction (v : Circle) :
    C^∞⟮AnnularCylinderModel, annularPunctureOpen v; ℝ⟯ where
  val := annularLeftAngleLift v
  property := contMDiff_annularLeftAngleLift v

noncomputable def annularRightAngleSmoothFunction (v : Circle) :
    C^∞⟮AnnularCylinderModel,
      annularPunctureOpen (annularOpposite v); ℝ⟯ where
  val := annularRightAngleLift v
  property := contMDiff_annularRightAngleLift v

noncomputable def annularLeftAngleZeroForm (v : Circle) :
    SmoothForms (I := AnnularCylinderModel)
      (M := annularPunctureOpen v) ℝ 0 :=
  smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
    (annularLeftAngleSmoothFunction v)

noncomputable def annularRightAngleZeroForm (v : Circle) :
    SmoothForms (I := AnnularCylinderModel)
      (M := annularPunctureOpen (annularOpposite v)) ℝ 0 :=
  smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
    (annularRightAngleSmoothFunction v)

theorem annularAngleTransition_isLocallyConstant (v : Circle) :
    IsLocallyConstant (annularAngleTransition v) := by
  have h := (annularCutUpperIndicator_isLocallyConstant v).comp
    (fun t : ℝ => -(2 * Real.pi) * (1 - t))
  have heq : annularAngleTransition v =
      fun x => -(2 * Real.pi) *
        (1 - annularCutUpperIndicator v x) := by
    funext x
    exact annularAngleTransition_eq_indicator v x
  rw [heq]
  simpa only [Function.comp_def] using h

noncomputable def annularAngleTransitionClosedForm (v : Circle) :
    DeRhamClosedForms (I := AnnularCylinderModel)
      (M := annularDoublePunctureOpen v) (A := ℝ) 0 :=
  ⟨smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
      (smoothRealFunctionOfIsLocallyConstant AnnularCylinderModel
        (annularAngleTransition v)
        (annularAngleTransition_isLocallyConstant v)),
    deRhamDifferential_locallyConstant_zeroForm_eq_zero (I0 := AnnularCylinderModel)
      (annularAngleTransition v)
      (annularAngleTransition_isLocallyConstant v)⟩

noncomputable def annularAngleTransitionClass (v : Circle) :
    DeRhamCohomology (I := AnnularCylinderModel)
      (M := annularDoublePunctureOpen v) (A := ℝ) 0 :=
  (DeRhamExactClosedForms (I := AnnularCylinderModel)
    (M := annularDoublePunctureOpen v) (A := ℝ) 0).mkQ
      (annularAngleTransitionClosedForm v)

noncomputable def annularPositiveBasepoint (v : Circle) :
    annularPositiveComponent v :=
  Classical.choice (annularPositiveComponent_nonempty v)

noncomputable def annularNegativeBasepoint (v : Circle) :
    annularNegativeComponent v :=
  Classical.choice (annularNegativeComponent_nonempty v)

noncomputable def annularAngleTransitionCoefficient (v : Circle) : ℝ :=
  let aO : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularPositiveComponent_le_doublePuncture v)
      (annularPositiveBasepoint v)
  let bO : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularNegativeComponent_le_doublePuncture v)
      (annularNegativeBasepoint v)
  annularAngleTransition v aO - annularAngleTransition v bO

theorem annularAngleTransitionCoefficient_eq_two_pi_or_neg (v : Circle) :
    annularAngleTransitionCoefficient v = 2 * Real.pi ∨
      annularAngleTransitionCoefficient v = -(2 * Real.pi) := by
  simpa [annularAngleTransitionCoefficient] using
    annularAngleTransition_coefficient v
      (annularPositiveBasepoint v)
      (annularNegativeBasepoint v)

theorem annularAngleTransitionClosedForm_decomposition (v : Circle) :
    let bO : annularDoublePunctureOpen v :=
      TopologicalSpace.Opens.inclusion
        (annularNegativeComponent_le_doublePuncture v)
        (annularNegativeBasepoint v)
    annularAngleTransitionClosedForm v =
      deRhamConstantZeroClosedForm (I0 := AnnularCylinderModel)
          (M0 := annularDoublePunctureOpen v)
          (annularAngleTransition v bO) +
        annularAngleTransitionCoefficient v •
          annularOverlapStepClosedForm v := by
  dsimp only
  apply Subtype.ext
  apply DifferentialForm.ext
  intro x
  ext q
  rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
  have hdecomp := annularAngleTransition_decomposition v
    (annularPositiveBasepoint v)
    (annularNegativeBasepoint v) x
  simpa [annularAngleTransitionClosedForm,
    annularAngleTransitionCoefficient,
    deRhamConstantZeroClosedForm, annularOverlapStepClosedForm,
    smoothRealFunctionToZeroForm, smoothRealFunctionOfIsLocallyConstant,
    smoothRealConstantFunction] using hdecomp

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 400000 in
theorem annularAngleTransitionClass_decomposition (v : Circle) :
    let bO : annularDoublePunctureOpen v :=
      TopologicalSpace.Opens.inclusion
        (annularNegativeComponent_le_doublePuncture v)
        (annularNegativeBasepoint v)
    annularAngleTransitionClass v =
      deRhamConstantH0Class (I0 := AnnularCylinderModel)
          (M0 := annularDoublePunctureOpen v)
          (annularAngleTransition v bO) +
        annularAngleTransitionCoefficient v •
          annularOverlapStepClass v := by
  dsimp only
  simp only [annularAngleTransitionClass,
    deRhamConstantH0Class, annularOverlapStepClass]
  have h := congrArg
    (DeRhamExactClosedForms (I := AnnularCylinderModel)
      (M := annularDoublePunctureOpen v) (A := ℝ) 0).mkQ
    (annularAngleTransitionClosedForm_decomposition v)
  simpa only [map_add, map_smul] using h

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 400000 in
theorem annularConnecting_constant_eq_zero (v : Circle) (c : ℝ) :
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ)
        AnnularCylinderModel (annularPunctureOpen v)
        (annularPunctureOpen (annularOpposite v))
        (annularPunctures_cover v) 0
        (deRhamConstantH0Class (I0 := AnnularCylinderModel)
          (M0 := annularDoublePunctureOpen v) c) = 0 := by
  let U := annularPunctureOpen v
  let V := annularPunctureOpen (annularOpposite v)
  let hcover : U ⊔ V = ⊤ := annularPunctures_cover v
  let connecting :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ)
      AnnularCylinderModel U V hcover 0
  have hconstant_range :
      deRhamConstantH0Class (I0 := AnnularCylinderModel)
          (M0 := annularDoublePunctureOpen v) c ∈
        Set.range
          (deRhamMayerVietorisDifference (I := AnnularCylinderModel) (A := ℝ)
            U V 0) := by
    refine ⟨
      (deRhamConstantH0Class (I0 := AnnularCylinderModel) (M0 := U) c,
        0), ?_⟩
    change
      deRhamCohomologyRestrictionOfLE (I := AnnularCylinderModel) (A := ℝ)
          (W := annularDoublePunctureOpen v) (V := U) inf_le_left 0
          (deRhamConstantH0Class (I0 := AnnularCylinderModel) (M0 := U) c) -
        deRhamCohomologyRestrictionOfLE (I := AnnularCylinderModel) (A := ℝ)
          (W := annularDoublePunctureOpen v) (V := V) inf_le_right 0 0 =
        deRhamConstantH0Class (I0 := AnnularCylinderModel)
          (M0 := annularDoublePunctureOpen v) c
    rw [deRhamCohomologyRestrictionOfLE_constant]
    simp
  have hexact0 :=
    deRham_mayerVietoris_exact_difference_connecting_of_partitionOfUnity
      (A := ℝ) AnnularCylinderModel U V hcover 0
  change connecting
      (deRhamConstantH0Class (I0 := AnnularCylinderModel)
        (M0 := annularDoublePunctureOpen v) c) = 0
  exact (hexact0 _).mpr hconstant_range

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
theorem annularAngleTransition_connecting_class (v : Circle) :
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ)
        AnnularCylinderModel (annularPunctureOpen v)
        (annularPunctureOpen (annularOpposite v))
        (annularPunctures_cover v) 0
        (annularAngleTransitionClass v) =
      annularAngleTransitionCoefficient v •
        annularStepConnectingClass v := by
  let U := annularPunctureOpen v
  let V := annularPunctureOpen (annularOpposite v)
  let hcover : U ⊔ V = ⊤ := annularPunctures_cover v
  let connecting :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ)
      AnnularCylinderModel U V hcover 0
  let bO : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularNegativeComponent_le_doublePuncture v)
      (annularNegativeBasepoint v)
  have hdecomp := annularAngleTransitionClass_decomposition v
  calc
    connecting (annularAngleTransitionClass v) =
        connecting
          (deRhamConstantH0Class (I0 := AnnularCylinderModel)
              (M0 := annularDoublePunctureOpen v)
              (annularAngleTransition v bO) +
            annularAngleTransitionCoefficient v •
              annularOverlapStepClass v) := congrArg connecting hdecomp
    _ = connecting
          (deRhamConstantH0Class (I0 := AnnularCylinderModel)
            (M0 := annularDoublePunctureOpen v)
            (annularAngleTransition v bO)) +
        connecting (annularAngleTransitionCoefficient v •
          annularOverlapStepClass v) :=
      deRhamMayerVietorisConnectingOfPartitionOfUnity_add
        AnnularCylinderModel U V hcover 0 _ _
    _ = 0 + annularAngleTransitionCoefficient v •
        connecting (annularOverlapStepClass v) := by
      rw [show connecting
          (deRhamConstantH0Class (I0 := AnnularCylinderModel)
            (M0 := annularDoublePunctureOpen v)
            (annularAngleTransition v bO)) = 0 by
        simpa [connecting, U, V, hcover] using
          annularConnecting_constant_eq_zero v
            (annularAngleTransition v bO)]
      have hsmul :=
        deRhamMayerVietorisConnectingOfPartitionOfUnity_smul
          AnnularCylinderModel U V hcover 0
          (annularAngleTransitionCoefficient v)
          (annularOverlapStepClass v)
      change connecting
          (annularAngleTransitionCoefficient v •
            annularOverlapStepClass v) =
        annularAngleTransitionCoefficient v •
          connecting (annularOverlapStepClass v) at hsmul
      rw [hsmul]
    _ = annularAngleTransitionCoefficient v •
        annularStepConnectingClass v := by
      simp [annularStepConnectingClass, connecting, U, V]

theorem annularAngleTransition_connecting_eq_angular_class (v : Circle) :
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ)
        AnnularCylinderModel (annularPunctureOpen v)
        (annularPunctureOpen (annularOpposite v))
        (annularPunctures_cover v) 0
        (annularAngleTransitionClass v) =
      annularAngleTransitionCoefficient v •
        (DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1).mkQ
            (annularAngularClosedForm v) := by
  rw [annularAngleTransition_connecting_class,
    annularAngularClosedForm_class]

end
end Uniformization
end JJMath
