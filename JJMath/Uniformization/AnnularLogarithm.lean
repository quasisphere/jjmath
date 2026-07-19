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

/--
%%handwave
name:
  The annular opposite direction is the circle antipode
statement:
  For every \(v\in S^1\), the opposite direction defined by the annular
  stereographic chart equals \(-v\).
proof:
  Evaluate the inverse stereographic chart at zero and simplify its complex
  coordinate.
-/
theorem annularOpposite_eq_antipode (v : Circle) :
    annularOpposite v = circleAntipode v := by
  apply Subtype.ext
  change (((stereographic' 1 v).symm 0 : Circle) : ℂ) = -(v : ℂ)
  rw [stereographic'_symm_apply]
  simp

/--
%%handwave
name:
  Complex coordinate of the circle antipode
statement:
  The antipode of \(v\in S^1\), viewed in \(\mathbb C\), is \(-v\).
proof:
  This is the definition of the circle antipode.
-/
@[simp]
theorem circleAntipode_coe (v : Circle) :
    (circleAntipode v : ℂ) = -(v : ℂ) := rfl

/--
%%handwave
name:
  Unit-circle membership in the principal slit plane
statement:
  A point \(q\in S^1\) belongs to the complex plane slit along the
  nonpositive real axis if and only if \(q\ne-1\).
proof:
  On the unit circle, the only point lying on the deleted nonpositive real
  ray is \(-1\).
-/
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

/--
%%handwave
name:
  The circle antipode is an involution
statement:
  For every \(q\in S^1\), one has \(-(-q)=q\).
proof:
  This is double negation in \(\mathbb C\).
-/
@[simp]
theorem circleAntipode_involutive (q : Circle) :
    circleAntipode (circleAntipode q) = q := by
  apply Subtype.ext
  simp [circleAntipode]

/--
%%handwave
name:
  Multiplication by minus one is the circle antipode
statement:
  For every \(q\in S^1\), \(q(-1)=-q\).
proof:
  Compute after inclusion into \(\mathbb C\).
-/
@[simp]
theorem mul_circleAntipode_one (q : Circle) :
    q * circleAntipode 1 = circleAntipode q := by
  apply Subtype.ext
  simp [circleAntipode]

noncomputable def annularCutRotation (v q : Circle) : Circle :=
  circleAntipode (v⁻¹ * q)

/--
%%handwave
name:
  The cut direction rotates to minus one
statement:
  Under the rotation \(q\mapsto-v^{-1}q\), the chosen cut direction \(v\)
  is sent to \(-1\).
proof:
  Substitute \(q=v\) and cancel \(v^{-1}v\).
-/
@[simp]
theorem annularCutRotation_self (v : Circle) :
    annularCutRotation v v = circleAntipode 1 := by
  simp [annularCutRotation]

/--
%%handwave
name:
  The rotated direction avoids minus one exactly off the cut
statement:
  For \(v,q\in S^1\), one has \(-v^{-1}q\ne-1\) if and only if \(q\ne v\).
proof:
  One implication follows by substituting \(q=v\).  Conversely,
  \(-v^{-1}q=-1\) implies \(v^{-1}q=1\), hence \(q=v\).
-/
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

/--
%%handwave
name:
  Slit-plane criterion for the first annular cut
statement:
  The rotated unit direction \(-v^{-1}q\) lies in the principal slit plane
  if and only if \(q\ne v\).
proof:
  A circle point is in the slit plane exactly when it is not \(-1\), and the
  cut rotation reaches \(-1\) exactly at \(q=v\).
-/
theorem annularCutRotation_mem_slitPlane_iff (v q : Circle) :
    (annularCutRotation v q : ℂ) ∈ Complex.slitPlane ↔ q ≠ v := by
  rw [circle_mem_slitPlane_iff_ne_negOne,
    annularCutRotation_ne_negOne_iff]

/--
%%handwave
name:
  The cut rotation reaches one at the opposite direction
statement:
  For \(v,q\in S^1\), \(-v^{-1}q=1\) if and only if \(q=-v\).
proof:
  Multiplying the equation by \(v\) gives \(q=-v\), and direct substitution
  proves the converse.
-/
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

/--
%%handwave
name:
  Slit-plane criterion for the opposite annular cut
statement:
  The opposite rotated direction \(v^{-1}q\) lies in the principal slit
  plane if and only if \(q\ne-v\).
proof:
  The opposite rotation is excluded from the slit plane exactly when it is
  \(-1\), equivalently when the first cut rotation is \(1\), which occurs at
  \(q=-v\).
-/
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

/--
%%handwave
name:
  Smoothness of annular cut rotation
statement:
  On every open subset of the cylinder, the complex-valued map
  \((q,t)\mapsto-v^{-1}q\) is smooth.
proof:
  The circle projection and its inclusion into \(\mathbb C\) are smooth, and
  multiplication by the fixed complex number \(-v^{-1}\) is a continuous
  linear map.
-/
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

/--
%%handwave
name:
  Smoothness of the first annular logarithm
statement:
  On the cylinder with direction \(v\) removed, the function
  \[
    (q,t)\longmapsto\log(-v^{-1}q)
  \]
  is smooth.
proof:
  The rotated direction is smooth and lies in the principal slit plane on
  this punctured cylinder.  The principal logarithm is smooth on that plane,
  so the composite is smooth.
-/
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

/--
%%handwave
name:
  Smoothness of the first annular angle lift
statement:
  The angle lift \((q,t)\mapsto\operatorname{Im}\log(-v^{-1}q)\) is smooth
  on the cylinder with direction \(v\) removed.
proof:
  Compose the smooth first annular logarithm with the real-linear imaginary
  part map.
-/
theorem contMDiff_annularLeftAngleLift (v : Circle) :
    ContMDiff AnnularCylinderModel 𝓘(ℝ, ℝ) ∞
      (annularLeftAngleLift v) := by
  have him : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun z : ℂ => z.im) :=
    contMDiff_iff_contDiff.mpr Complex.imCLM.contDiff
  simpa [annularLeftAngleLift] using
    him.comp (contMDiff_complexLog_comp_annularCutRotation v)

/--
%%handwave
name:
  Smoothness of the opposite annular logarithm
statement:
  On the cylinder with direction \(-v\) removed, the function
  \[
    (q,t)\longmapsto\log(v^{-1}q)
  \]
  is smooth.
proof:
  The opposite rotated direction is smooth and belongs to the principal slit
  plane away from \(-v\).  Compose it with the smooth principal logarithm.
-/
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

/--
%%handwave
name:
  Smoothness of the opposite annular angle lift
statement:
  The function
  \((q,t)\mapsto\operatorname{Im}\log(v^{-1}q)+\pi\) is smooth on the
  cylinder with direction \(-v\) removed.
proof:
  Take the imaginary part of the smooth opposite annular logarithm and add
  the constant \(\pi\).
-/
theorem contMDiff_annularRightAngleLift (v : Circle) :
    ContMDiff AnnularCylinderModel 𝓘(ℝ, ℝ) ∞
      (annularRightAngleLift v) := by
  have him : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun z : ℂ => z.im) :=
    contMDiff_iff_contDiff.mpr Complex.imCLM.contDiff
  have hbase := him.comp
    (contMDiff_complexLog_comp_secondCut v)
  simpa [annularRightAngleLift] using hbase.add contMDiff_const

/--
%%handwave
name:
  A nonreal unit-circle point has nonzero imaginary part
statement:
  If \(q\in S^1\) is neither \(1\) nor \(-1\), then
  \(\operatorname{Im}q\ne0\).
proof:
  If the imaginary part vanished, the unit-norm identity would give
  \((\operatorname{Re}q)^2=1\), so \(q=1\) or \(q=-1\).
-/
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

/--
%%handwave
name:
  The rotated direction is nonreal on the double-puncture overlap
statement:
  On the cylinder with both \(v\) and \(-v\) removed, the rotated direction
  \(-v^{-1}q\) has nonzero imaginary part.
proof:
  It cannot equal \(-1\), since \(q\ne v\), and it cannot equal \(1\), since
  \(q\ne-v\).  A unit-circle point distinct from both real endpoints has
  nonzero imaginary part.
-/
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

/--
%%handwave
name:
  Difference of the two annular angle lifts
statement:
  On the double-puncture overlap, let \(z=-v^{-1}q\).  Then
  \[
    \operatorname{Im}\log z-
      \bigl(\operatorname{Im}\log(-z)+\pi\bigr)
    =\begin{cases}0,&\operatorname{Im}z>0,\\-2\pi,&\operatorname{Im}z<0.
      \end{cases}
  \]
proof:
  The imaginary part of the principal logarithm is the principal argument.
  For \(z\) in the upper half-plane,
  \(\arg(-z)=\arg z-\pi\); in the lower half-plane it is
  \(\arg z+\pi\).  Substitute these two formulas.
-/
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

/--
%%handwave
name:
  Preconnectedness of the positive annular overlap component
statement:
  The positive connected piece of the cylinder with the two opposite angular
  directions removed is preconnected.
proof:
  Its standard global chart identifies it with a convex target, and
  preconnectedness is preserved by homeomorphism.
-/
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

/--
%%handwave
name:
  Preconnectedness of the negative annular overlap component
statement:
  The negative connected piece of the cylinder with the two opposite angular
  directions removed is preconnected.
proof:
  A global chart identifies this component with a convex set, hence with a
  preconnected space.
-/
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

/--
%%handwave
name:
  Local constancy of the rotated upper-half indicator
statement:
  On the double-puncture overlap, the function that is \(1\) when the rotated
  circle direction has positive imaginary part and \(0\) otherwise is locally
  constant.
proof:
  The rotated direction depends continuously on the point and its imaginary
  part never vanishes on the overlap.  Its sign is therefore locally
  constant.
-/
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

/--
%%handwave
name:
  Constancy of the upper-half indicator on the positive component
statement:
  The rotated upper-half indicator has the same value at any two points of
  the positive annular overlap component.
proof:
  Restrict the locally constant indicator to the preconnected positive
  component; every locally constant function on a preconnected space is
  constant.
-/
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

/--
%%handwave
name:
  Constancy of the upper-half indicator on the negative component
statement:
  The rotated upper-half indicator has the same value at any two points of
  the negative annular overlap component.
proof:
  Its restriction is locally constant, and the negative component is
  preconnected.
-/
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

/--
%%handwave
name:
  Inverse point for annular cut rotation
statement:
  For \(v,r\in S^1\), rotating the point \(-vr\) by the cut rotation based at
  \(v\) gives \(r\).
proof:
  Expand the rotation as multiplication by \(-v^{-1}\) and cancel the unit
  circle factors.
-/
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

/--
%%handwave
name:
  The quarter-turn circle point is the imaginary unit
statement:
  The unit-circle point \(e^{i\pi/2}\), viewed as a complex number, equals
  \(i\).
proof:
  Evaluate the complex exponential at angle \(\pi/2\).
-/
@[simp]
theorem circleI_coe : (circleI : ℂ) = Complex.I := by
  rw [circleI, Circle.coe_exp, Complex.exp_mul_I]
  simp

/--
%%handwave
name:
  The imaginary unit is not one on the circle
statement:
  The unit-circle point \(i\) is not \(1\).
proof:
  Their imaginary parts are respectively \(1\) and \(0\).
-/
theorem circleI_ne_one : circleI ≠ 1 := by
  intro h
  have hcoe := congrArg Subtype.val h
  have him := congrArg Complex.im hcoe
  norm_num at him

/--
%%handwave
name:
  The imaginary unit is not minus one on the circle
statement:
  The unit-circle point \(i\) is not \(-1\).
proof:
  Their imaginary parts are respectively \(1\) and \(0\).
-/
theorem circleI_ne_negOne :
    circleI ≠ circleAntipode 1 := by
  intro h
  have hcoe := congrArg Subtype.val h
  have him := congrArg Complex.im hcoe
  norm_num [circleAntipode] at him

noncomputable def circleNegI : Circle :=
  circleAntipode circleI

/--
%%handwave
name:
  The antipode of the imaginary unit is minus the imaginary unit
statement:
  The antipode of \(i\) on the unit circle, viewed in \(\mathbb C\), is
  \(-i\).
proof:
  The circle antipode is complex negation.
-/
@[simp]
theorem circleNegI_coe : (circleNegI : ℂ) = -Complex.I := by
  simp [circleNegI, circleAntipode]

/--
%%handwave
name:
  Minus the imaginary unit is not one on the circle
statement:
  The unit-circle point \(-i\) is not \(1\).
proof:
  Compare imaginary parts, which are \(-1\) and \(0\).
-/
theorem circleNegI_ne_one : circleNegI ≠ 1 := by
  intro h
  have hcoe := congrArg Subtype.val h
  have him := congrArg Complex.im hcoe
  norm_num [circleNegI, circleAntipode] at him

/--
%%handwave
name:
  Minus the imaginary unit is not minus one on the circle
statement:
  The unit-circle point \(-i\) is not \(-1\).
proof:
  Their imaginary parts are \(-1\) and \(0\), respectively.
-/
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

/--
%%handwave
name:
  Indicator value at the upper test point
statement:
  At the overlap point whose cut-rotated direction is \(i\), the upper-half
  indicator equals \(1\).
proof:
  The rotated direction is \(i\), whose imaginary part is positive.
-/
theorem annularUpperTestPoint_indicator (v : Circle) :
    annularCutUpperIndicator v (annularUpperTestPoint v) = 1 := by
  simp [annularCutUpperIndicator, annularUpperTestPoint,
    annularRotationPoint, circleI]

/--
%%handwave
name:
  Indicator value at the lower test point
statement:
  At the overlap point whose cut-rotated direction is \(-i\), the upper-half
  indicator equals \(0\).
proof:
  The imaginary part of \(-i\) is negative, so the positivity test fails.
-/
theorem annularLowerTestPoint_indicator (v : Circle) :
    annularCutUpperIndicator v (annularLowerTestPoint v) = 0 := by
  simp [annularCutUpperIndicator, annularLowerTestPoint,
    annularRotationPoint, circleNegI, circleI]

/--
%%handwave
name:
  The double-puncture overlap has two angular components
statement:
  Every point of the cylinder with the two opposite cut directions removed
  belongs either to the positive angular component or to the negative angular
  component.
proof:
  The two component opens cover the double-puncture overlap.
-/
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

/--
%%handwave
name:
  Indicator value equals any positive-component reference value
statement:
  If an overlap point \(x\) lies in the positive angular component, then its
  upper-half indicator equals the indicator at any chosen point \(a\) of that
  component.
proof:
  Regard \(x\) as a point of the positive component and use constancy there.
-/
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

/--
%%handwave
name:
  Indicator value equals any negative-component reference value
statement:
  If an overlap point \(x\) lies in the negative angular component, then its
  upper-half indicator equals the indicator at any chosen point \(b\) of that
  component.
proof:
  View \(x\) inside the negative component and apply constancy of the
  indicator on that component.
-/
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

/--
%%handwave
name:
  The two overlap components have different indicator values
statement:
  The upper-half indicator at a point of the positive angular component is
  different from its value at a point of the negative angular component.
proof:
  If the two component values agreed, constancy on each component would force
  the upper test point \(i\) and lower test point \(-i\) to have the same
  value.  Their values are \(1\) and \(0\), a contradiction.
-/
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

/--
%%handwave
name:
  Angular transition expressed by the upper-half indicator
statement:
  On the overlap of the two punctured-cylinder charts, the difference of the
  two angle lifts is
  \[
    \tau_v(x)=-2\pi\bigl(1-\mathbf 1_{\mathrm{upper}}(x)\bigr).
  \]
proof:
  The explicit logarithm calculation gives transition \(0\) when the rotated
  direction lies in the upper half-plane and \(-2\pi\) otherwise, exactly as
  encoded by the indicator.
-/
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

/--
%%handwave
name:
  The upper-half indicator is binary
statement:
  At every point of the double-puncture overlap, the upper-half indicator is
  either \(0\) or \(1\).
proof:
  Split according to whether the imaginary part of the rotated direction is
  positive.
-/
theorem annularCutUpperIndicator_eq_zero_or_one (v : Circle)
    (x : annularDoublePunctureOpen v) :
    annularCutUpperIndicator v x = 0 ∨
      annularCutUpperIndicator v x = 1 := by
  by_cases hpos : 0 <
      ((annularCutRotation v ((x : Circle × ℝ).1) : Circle) : ℂ).im
  · exact Or.inr (by simp [annularCutUpperIndicator, hpos])
  · exact Or.inl (by simp [annularCutUpperIndicator, hpos])

/--
%%handwave
name:
  Constancy of the angle transition on the positive overlap component
statement:
  The difference of the two angle lifts has the same value at any two points
  of the positive component of the double-puncture overlap.
proof:
  Express the transition through the upper-half indicator, which is constant
  on that connected component.
-/
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

/--
%%handwave
name:
  Constancy of the angle transition on the negative overlap component
statement:
  The difference of the two angle lifts has the same value at any two points
  of the negative component of the double-puncture overlap.
proof:
  Use the indicator formula for the transition and constancy of the
  upper-half indicator on the negative component.
-/
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

/--
%%handwave
name:
  Jump of the annular angle transition
statement:
  If \(a\) and \(b\) lie in the two connected components of the overlap,
  then
  \[
    \tau_v(a)-\tau_v(b)\in\{2\pi,-2\pi\}.
  \]
proof:
  The binary indicator takes different values on the two components.
  Substitution in \(\tau_v=-2\pi(1-\mathbf 1_{\mathrm{upper}})\) gives one
  of the two signs.
-/
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

/--
%%handwave
name:
  Decomposition of the annular angle transition
statement:
  Choose points \(a\) and \(b\) in the positive and negative overlap
  components.  For every overlap point \(x\),
  \[
    \tau_v(x)=\tau_v(b)+\bigl(\tau_v(a)-\tau_v(b)\bigr)s_v(x),
  \]
  where \(s_v\) is the step function equal to one on the positive component
  and zero on the negative component.
proof:
  Split \(x\) between the two overlap components, use constancy of \(\tau_v\)
  on each, and substitute the corresponding value of the step function.
-/
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

/--
%%handwave
name:
  Local constancy of the annular angle transition
statement:
  The difference \(\tau_v\) of the two annular angle lifts is locally
  constant on their double-puncture overlap.
proof:
  It is an affine function of the locally constant upper-half indicator.
-/
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

/--
%%handwave
name:
  The canonical angle-transition coefficient is plus or minus two pi
statement:
  The difference between the transition values at the chosen basepoints of
  the two overlap components is \(2\pi\) or \(-2\pi\).
proof:
  Apply the general jump calculation to the chosen positive and negative
  basepoints.
-/
theorem annularAngleTransitionCoefficient_eq_two_pi_or_neg (v : Circle) :
    annularAngleTransitionCoefficient v = 2 * Real.pi ∨
      annularAngleTransitionCoefficient v = -(2 * Real.pi) := by
  simpa [annularAngleTransitionCoefficient] using
    annularAngleTransition_coefficient v
      (annularPositiveBasepoint v)
      (annularNegativeBasepoint v)

/--
%%handwave
name:
  Zero-form decomposition of the annular angle transition
statement:
  As a closed zero-form on the double-puncture overlap, the angular
  transition decomposes as
  \[
    \tau_v=\tau_v(b)+\varepsilon_v s_v,
  \]
  where \(b\) is the chosen negative-component basepoint and
  \(\varepsilon_v=\tau_v(a)-\tau_v(b)\).
proof:
  Evaluate both zero-forms at an arbitrary point and apply the pointwise
  transition decomposition.
-/
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
/--
%%handwave
name:
  Cohomology decomposition of the annular angle transition
statement:
  In degree-zero de Rham cohomology of the overlap,
  \[
    [\tau_v]=[\tau_v(b)]+\varepsilon_v[s_v].
  \]
proof:
  Apply the quotient map from closed zero-forms to the zero-form
  decomposition; it preserves addition and scalar multiplication.
-/
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
/--
%%handwave
name:
  The annular connecting map kills constant zero-classes
statement:
  For the cover of the cylinder by the two complementary punctured charts,
  the Mayer--Vietoris connecting homomorphism sends every constant
  degree-zero class on the overlap to zero.
proof:
  A constant on the overlap is the difference of the same constant on the
  first chart and zero on the second.  It therefore lies in the image of the
  preceding difference map, hence in the kernel of the connecting map by
  exactness.
-/
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
/--
%%handwave
name:
  Connecting class of the annular angle transition
statement:
  Under the Mayer--Vietoris connecting homomorphism for the two punctured
  cylinder charts,
  \[
    \delta[\tau_v]=\varepsilon_v\,\delta[s_v],
  \]
  where \(\varepsilon_v\in\{2\pi,-2\pi\}\) is the transition jump.
proof:
  Apply the connecting map to the decomposition of \([\tau_v]\).  Additivity
  and linearity pass through the scalar term, while the constant term maps
  to zero.
-/
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

/--
%%handwave
name:
  The logarithmic transition generates the angular cohomology class
statement:
  The Mayer--Vietoris connecting class of the annular logarithm transition is
  \[
    \delta[\tau_v]=\varepsilon_v[\omega_v],
  \]
  where \([\omega_v]\) is the chosen angular class and
  \(\varepsilon_v\in\{2\pi,-2\pi\}\).
proof:
  The connecting image is the transition coefficient times the step-function
  connecting class, and the chosen angular form represents that class.
-/
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
