import JJMath.Uniformization.CoordinateDiskSmoothBoundary
import JJMath.Uniformization.ExteriorAngularExtension
import JJMath.Uniformization.PuncturedGreenConjugate
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Angular forms around a puncture

This file constructs the topological angular datum needed to exponentiate a
Green potential on a surface with vanishing first de Rham cohomology.  A small
coordinate disk around the pole has connected exterior, and the exterior
angular-extension theorem transports its angular class to infinity.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

/-- The complex plane with its origin removed, as an open real manifold. -/
def complexPuncturedPlaneOpen : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | z ≠ 0}, isOpen_ne⟩

/-- The unit direction of a nonzero complex number. -/
noncomputable def complexPuncturedPlaneDirection
    (z : complexPuncturedPlaneOpen) : Circle :=
  ⟨NormedSpace.normalize (z : ℂ),
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize z.2)⟩

/-- Polar coordinates identify the punctured complex plane with the standard
annular cylinder. -/
noncomputable def complexPuncturedPlaneDiffeomorphAnnularCylinder :
    complexPuncturedPlaneOpen ≃ₘ⟮SurfaceRealModel,
      AnnularCylinderModel⟯ Circle × ℝ := by
  let e : complexPuncturedPlaneOpen ≃ Circle × ℝ :=
    { toFun := fun z =>
        (complexPuncturedPlaneDirection z, Real.log ‖(z : ℂ)‖)
      invFun := fun q =>
        ⟨Real.exp q.2 • (q.1 : ℂ), by
          exact smul_ne_zero (Real.exp_pos q.2).ne' q.1.coe_ne_zero⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change Real.exp (Real.log ‖(z : ℂ)‖) •
            NormedSpace.normalize (z : ℂ) = (z : ℂ)
        rw [Real.exp_log (norm_pos_iff.mpr z.2)]
        exact NormedSpace.norm_smul_normalize (z : ℂ)
      right_inv := by
        intro q
        apply Prod.ext
        · apply Circle.ext
          simp only [complexPuncturedPlaneDirection]
          calc
            NormedSpace.normalize (Real.exp q.2 • (q.1 : ℂ)) =
                NormedSpace.normalize (q.1 : ℂ) :=
              NormedSpace.normalize_smul_of_pos (Real.exp_pos q.2) _
            _ = (q.1 : ℂ) :=
              NormedSpace.normalize_eq_self_of_norm_eq_one
                (Circle.norm_coe q.1)
        · change Real.log ‖Real.exp q.2 • (q.1 : ℂ)‖ = q.2
          rw [show Real.exp q.2 • (q.1 : ℂ) =
              (Real.exp q.2 : ℂ) * (q.1 : ℂ) by rfl,
            norm_mul]
          simp }
  have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun z : complexPuncturedPlaneOpen => (z : ℂ)) :=
    contMDiff_subtype_val
  have hnorm : ContMDiff SurfaceRealModel (𝓘(ℝ, ℝ)) ∞
      (fun z : complexPuncturedPlaneOpen => ‖(z : ℂ)‖) := by
    intro z
    exact (contDiffAt_norm ℝ z.2).contMDiffAt.comp z (hval z)
  have hnormalizeRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun z : complexPuncturedPlaneOpen =>
        NormedSpace.normalize (z : ℂ)) := by
    convert (hnorm.inv₀ (fun z => norm_ne_zero_iff.mpr z.2)).smul hval using 1
  have hnormalize : ContMDiff SurfaceRealModel (𝓡 1) ∞
      complexPuncturedPlaneDirection := by
    change ContMDiff SurfaceRealModel (𝓡 1) ∞
      (Set.codRestrict
        (fun z : complexPuncturedPlaneOpen =>
          NormedSpace.normalize (z : ℂ))
        (Metric.sphere (0 : ℂ) 1) _)
    exact hnormalizeRaw.codRestrict_sphere _
  have hlog : ContMDiff SurfaceRealModel (𝓘(ℝ, ℝ)) ∞
      (fun z : complexPuncturedPlaneOpen => Real.log ‖(z : ℂ)‖) := by
    intro z
    exact (Real.contDiffAt_log.mpr
      (norm_ne_zero_iff.mpr z.2)).contMDiffAt.comp z (hnorm z)
  have hto : ContMDiff SurfaceRealModel AnnularCylinderModel ∞ e :=
    hnormalize.prodMk hlog
  have hcircleCoe : ContMDiff (𝓡 1) SurfaceRealModel ∞
      (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  have hinvRaw : ContMDiff AnnularCylinderModel SurfaceRealModel ∞
      (fun q : Circle × ℝ => Real.exp q.2 • (q.1 : ℂ)) :=
    (Real.contDiff_exp.contMDiff.comp contMDiff_snd).smul
      (hcircleCoe.comp contMDiff_fst)
  have hinv : ContMDiff AnnularCylinderModel SurfaceRealModel ∞ e.symm :=
    ContMDiff.codRestrict_open hinvRaw complexPuncturedPlaneOpen
      (fun q => smul_ne_zero (Real.exp_pos q.2).ne' q.1.coe_ne_zero)
  exact
    { toEquiv := e
      contMDiff_toFun := hto
      contMDiff_invFun := hinv }

/-- An open Euclidean ball with its center removed. -/
def complexPuncturedBallOpen (c : ℂ) (r : ℝ) :
    TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball c r \ {c}, Metric.isOpen_ball.sdiff isClosed_singleton⟩

/-- Radial compression identifies the punctured plane with a punctured open
ball, taking the origin to the center before the punctures are removed. -/
noncomputable def complexPuncturedPlaneDiffeomorphPuncturedBall
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    complexPuncturedPlaneOpen ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯
      complexPuncturedBallOpen c r := by
  let b : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.univBall c r
  have hbsource : b.source = Set.univ :=
    OpenPartialHomeomorph.univBall_source c r
  have hbtarget : b.target = Metric.ball c r :=
    OpenPartialHomeomorph.univBall_target c hr
  let e : complexPuncturedPlaneOpen ≃ complexPuncturedBallOpen c r :=
    { toFun := fun z =>
        ⟨b (z : ℂ), by
          constructor
          · rw [← hbtarget]
            exact b.map_source (by rw [hbsource]; exact Set.mem_univ _)
          · intro hbzc
            have hbz0 : b (z : ℂ) = b 0 := by
              simpa [b] using hbzc
            have hz0 := b.injOn
              (by rw [hbsource]; exact Set.mem_univ (z : ℂ))
              (by rw [hbsource]; exact Set.mem_univ (0 : ℂ)) hbz0
            exact z.2 hz0⟩
      invFun := fun w =>
        ⟨b.symm (w : ℂ), by
          intro hzero
          have hwtarget : (w : ℂ) ∈ b.target := by
            rw [hbtarget]
            exact w.2.1
          have hright := b.right_inv hwtarget
          rw [hzero] at hright
          have hwc : (w : ℂ) = c := by
            simpa [b] using hright.symm
          exact w.2.2 hwc⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact b.left_inv (by rw [hbsource]; exact Set.mem_univ _)
      right_inv := by
        intro w
        apply Subtype.ext
        exact b.right_inv (by rw [hbtarget]; exact w.2.1) }
  have hbSmooth : ContMDiff SurfaceRealModel SurfaceRealModel ∞ b :=
    OpenPartialHomeomorph.contDiff_univBall.contMDiff
  have htoRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun z : complexPuncturedPlaneOpen => b (z : ℂ)) :=
    hbSmooth.comp contMDiff_subtype_val
  have hto : ContMDiff SurfaceRealModel SurfaceRealModel ∞ e :=
    ContMDiff.codRestrict_open htoRaw (complexPuncturedBallOpen c r)
      (fun z => e.toFun z |>.2)
  have hinvRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun w : complexPuncturedBallOpen c r => b.symm (w : ℂ)) := by
    intro w
    have hwball : (w : ℂ) ∈ Metric.ball c r := w.2.1
    have hsmoothAt : ContDiffAt ℝ ∞ b.symm (w : ℂ) :=
      (OpenPartialHomeomorph.contDiffOn_univBall_symm.contDiffAt
        (Metric.isOpen_ball.mem_nhds hwball))
    exact hsmoothAt.contMDiffAt.comp w (contMDiff_subtype_val w)
  have hinv : ContMDiff SurfaceRealModel SurfaceRealModel ∞ e.symm :=
    ContMDiff.codRestrict_open hinvRaw complexPuncturedPlaneOpen
      (fun w => e.invFun w |>.2)
  exact
    { toEquiv := e
      contMDiff_toFun := hto
      contMDiff_invFun := hinv }

/-- The unit direction from the center of a punctured ball. -/
noncomputable def complexPuncturedBallDirection
    (c : ℂ) (r : ℝ) (z : complexPuncturedBallOpen c r) : Circle :=
  ⟨NormedSpace.normalize ((z : ℂ) - c),
    mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize (sub_ne_zero.mpr z.2.2))⟩

/-- A ball of radius twice (R), punctured at its center, is an annular
cylinder whose normal coordinate is negative inside radius (R) and positive
outside radius (R). -/
noncomputable def complexPuncturedDoubleBallDiffeomorphAnnularCylinder
    (c : ℂ) (R : ℝ) (hR : 0 < R) :
    complexPuncturedBallOpen c (2 * R) ≃ₘ⟮SurfaceRealModel,
      AnnularCylinderModel⟯ Circle × ℝ := by
  let eta := symmetricOpenIntervalDiffeomorphReal R hR
  have hdelta : ∀ z : complexPuncturedBallOpen c (2 * R),
      ‖(z : ℂ) - c‖ - R ∈ Set.Ioo (-R) R := by
    intro z
    have hzpos : 0 < ‖(z : ℂ) - c‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr z.2.2)
    have hzlt : ‖(z : ℂ) - c‖ < 2 * R := by
      simpa [Metric.mem_ball, dist_eq_norm] using z.2.1
    constructor <;> linarith
  have hinvMem : ∀ q : Circle × ℝ,
      c + (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ) ∈
        complexPuncturedBallOpen c (2 * R) := by
    intro q
    have hs := (eta.symm q.2).2
    change -R < (eta.symm q.2 : ℝ) ∧
      (eta.symm q.2 : ℝ) < R at hs
    have haPos : 0 < R + (eta.symm q.2 : ℝ) := by linarith
    have haLt : R + (eta.symm q.2 : ℝ) < 2 * R := by linarith
    constructor
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsub :
          c + (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ) - c =
            ((R + (eta.symm q.2 : ℝ) : ℝ) : ℂ) * (q.1 : ℂ) := by
        simp
      rw [hsub, norm_mul]
      simpa [← Complex.ofReal_add, abs_of_pos haPos] using haLt
    · intro heq
      have heq' :
          c + (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ) = c := by
        simpa using heq
      have hzero :
          (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ) = 0 := by
        apply add_left_cancel (a := c)
        simpa using heq'
      exact (smul_ne_zero haPos.ne' q.1.coe_ne_zero) hzero
  let e : complexPuncturedBallOpen c (2 * R) ≃ Circle × ℝ :=
    { toFun := fun z =>
        (complexPuncturedBallDirection c (2 * R) z,
          eta ⟨‖(z : ℂ) - c‖ - R, hdelta z⟩)
      invFun := fun q =>
        ⟨c + (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ), hinvMem q⟩
      left_inv := by
        intro z
        apply Subtype.ext
        have hzpos : 0 < ‖(z : ℂ) - c‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr z.2.2)
        have heta :
            (eta.symm (eta ⟨‖(z : ℂ) - c‖ - R, hdelta z⟩) : ℝ) =
              ‖(z : ℂ) - c‖ - R := by
          exact congrArg Subtype.val (eta.symm_apply_apply _)
        simp only [heta]
        rw [show R + (‖(z : ℂ) - c‖ - R) = ‖(z : ℂ) - c‖ by ring]
        change c + ‖(z : ℂ) - c‖ •
            NormedSpace.normalize ((z : ℂ) - c) = (z : ℂ)
        calc
          c + ‖(z : ℂ) - c‖ •
              NormedSpace.normalize ((z : ℂ) - c) =
              c + ((z : ℂ) - c) := by
            apply congrArg (fun w : ℂ => c + w)
              (NormedSpace.norm_smul_normalize ((z : ℂ) - c))
          _ = (z : ℂ) := by ring
      right_inv := by
        intro q
        apply Prod.ext
        · apply Circle.ext
          simp only [complexPuncturedBallDirection]
          have hs := (eta.symm q.2).2
          change -R < (eta.symm q.2 : ℝ) ∧
            (eta.symm q.2 : ℝ) < R at hs
          have haPos : 0 < R + (eta.symm q.2 : ℝ) := by linarith
          have hsub :
              c + (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ) - c =
                (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ) := by
            abel
          rw [hsub]
          calc
            NormedSpace.normalize
                ((R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ)) =
                NormedSpace.normalize (q.1 : ℂ) :=
              NormedSpace.normalize_smul_of_pos haPos _
            _ = (q.1 : ℂ) :=
              NormedSpace.normalize_eq_self_of_norm_eq_one
                (Circle.norm_coe q.1)
        · have hs := (eta.symm q.2).2
          change -R < (eta.symm q.2 : ℝ) ∧
            (eta.symm q.2 : ℝ) < R at hs
          have haPos : 0 < R + (eta.symm q.2 : ℝ) := by linarith
          have hsub :
              c + (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ) - c =
                ((R + (eta.symm q.2 : ℝ) : ℝ) : ℂ) * (q.1 : ℂ) := by
            simp
          let lhs : symmetricOpenInterval R :=
            ⟨‖c + (R + (eta.symm q.2 : ℝ)) •
                (q.1 : ℂ) - c‖ - R,
              hdelta ⟨c + (R + (eta.symm q.2 : ℝ)) •
                (q.1 : ℂ), hinvMem q⟩⟩
          have hlhs : lhs = eta.symm q.2 := by
            apply Subtype.ext
            change ‖c + (R + (eta.symm q.2 : ℝ)) •
                (q.1 : ℂ) - c‖ - R = (eta.symm q.2 : ℝ)
            rw [hsub, norm_mul]
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos haPos]
            simp
          change eta lhs = q.2
          rw [hlhs]
          exact eta.apply_symm_apply q.2 }
  have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun z : complexPuncturedBallOpen c (2 * R) => (z : ℂ)) :=
    contMDiff_subtype_val
  have hshift : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun z : complexPuncturedBallOpen c (2 * R) => (z : ℂ) - c) :=
    hval.sub contMDiff_const
  have hnorm : ContMDiff SurfaceRealModel (𝓘(ℝ, ℝ)) ∞
      (fun z : complexPuncturedBallOpen c (2 * R) => ‖(z : ℂ) - c‖) := by
    intro z
    exact (contDiffAt_norm ℝ (sub_ne_zero.mpr z.2.2)).contMDiffAt.comp
      z (hshift z)
  have hdirectionRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun z : complexPuncturedBallOpen c (2 * R) =>
        NormedSpace.normalize ((z : ℂ) - c)) := by
    convert (hnorm.inv₀ (fun z => norm_ne_zero_iff.mpr
      (sub_ne_zero.mpr z.2.2))).smul hshift using 1
  have hdirection : ContMDiff SurfaceRealModel (𝓡 1) ∞
      (complexPuncturedBallDirection c (2 * R)) := by
    change ContMDiff SurfaceRealModel (𝓡 1) ∞
      (Set.codRestrict
        (fun z : complexPuncturedBallOpen c (2 * R) =>
          NormedSpace.normalize ((z : ℂ) - c))
        (Metric.sphere (0 : ℂ) 1) _)
    exact hdirectionRaw.codRestrict_sphere _
  have hdeltaSmooth : ContMDiff SurfaceRealModel (𝓘(ℝ, ℝ)) ∞
      (fun z : complexPuncturedBallOpen c (2 * R) => ‖(z : ℂ) - c‖ - R) :=
    hnorm.sub contMDiff_const
  have hdeltaSubtype : ContMDiff SurfaceRealModel (𝓘(ℝ, ℝ)) ∞
      (fun z : complexPuncturedBallOpen c (2 * R) =>
        (⟨‖(z : ℂ) - c‖ - R, hdelta z⟩ : symmetricOpenInterval R)) :=
    ContMDiff.codRestrict_open hdeltaSmooth (symmetricOpenInterval R) hdelta
  have hto : ContMDiff SurfaceRealModel AnnularCylinderModel ∞ e :=
    hdirection.prodMk (eta.contMDiff.comp hdeltaSubtype)
  have hetaInvVal : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (eta.symm t : ℝ)) :=
    contMDiff_subtype_val.comp eta.symm.contMDiff
  have hsecond : ContMDiff AnnularCylinderModel (𝓘(ℝ, ℝ)) ∞
      (fun q : Circle × ℝ => (eta.symm q.2 : ℝ)) :=
    hetaInvVal.comp contMDiff_snd
  have hcircleCoe : ContMDiff (𝓡 1) SurfaceRealModel ∞
      (fun z : Circle => (z : ℂ)) := contMDiff_coe_sphere
  have hinvRaw : ContMDiff AnnularCylinderModel SurfaceRealModel ∞
      (fun q : Circle × ℝ =>
        c + (R + (eta.symm q.2 : ℝ)) • (q.1 : ℂ)) :=
    contMDiff_const.add ((contMDiff_const.add hsecond).smul
      (hcircleCoe.comp contMDiff_fst))
  have hinv : ContMDiff AnnularCylinderModel SurfaceRealModel ∞ e.symm :=
    ContMDiff.codRestrict_open hinvRaw
      (complexPuncturedBallOpen c (2 * R)) (fun q => e.invFun q |>.2)
  exact
    { toEquiv := e
      contMDiff_toFun := hto
      contMDiff_invFun := hinv }

/--
%%handwave
name:
  Negative cylinder coordinate characterizes the inner punctured ball
statement:
  Under the radial diffeomorphism from \(B(c,2R)\setminus\{c\}\) to
  \(S^1\times\mathbb R\), with \(R>0\), the second coordinate is negative
  exactly when
  \[
    |z-c|<R.
  \]
proof:
  The second coordinate is the sign-preserving tangent reparametrization of
  \(|z-c|-R\), so it is negative precisely when that quantity is negative.
-/
theorem complexPuncturedDoubleBallDiffeomorphAnnularCylinder_second_lt_zero_iff
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (z : complexPuncturedBallOpen c (2 * R)) :
    (complexPuncturedDoubleBallDiffeomorphAnnularCylinder c R hR z).2 < 0 ↔
      dist (z : ℂ) c < R := by
  change symmetricOpenIntervalDiffeomorphReal R hR
      ⟨‖(z : ℂ) - c‖ - R, _⟩ < 0 ↔ dist (z : ℂ) c < R
  rw [symmetricOpenIntervalDiffeomorphReal_lt_zero_iff]
  simp [dist_eq_norm]

/--
%%handwave
name:
  Positive cylinder coordinate characterizes the exterior annulus
statement:
  Under the same radial diffeomorphism, the second coordinate is positive
  exactly when
  \[
    R<|z-c|.
  \]
proof:
  The sign-preserving transverse reparametrization is positive exactly when
  \(|z-c|-R>0\).
-/
theorem complexPuncturedDoubleBallDiffeomorphAnnularCylinder_second_pos_iff
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (z : complexPuncturedBallOpen c (2 * R)) :
    0 < (complexPuncturedDoubleBallDiffeomorphAnnularCylinder c R hR z).2 ↔
      R < dist (z : ℂ) c := by
  change 0 < symmetricOpenIntervalDiffeomorphReal R hR
      ⟨‖(z : ℂ) - c‖ - R, _⟩ ↔ R < dist (z : ℂ) c
  rw [symmetricOpenIntervalDiffeomorphReal_pos_iff]
  simp [dist_eq_norm]

/-- The part of a coordinate disk left after removing a chosen point. -/
def ClosedCoordinateDisk.puncturedExpandedOpenDisk
    {X : Type} [TopologicalSpace X] [T1Space X]
    [ChartedSpace ℂ X] (D : ClosedCoordinateDisk X) (p : X) (rho : ℝ) :
    TopologicalSpace.Opens X :=
  puncturedSurfaceOpen p ⊓
    ⟨D.expandedOpenDisk rho, D.expandedOpenDisk_isOpen rho⟩

/--
%%handwave
name:
  A punctured coordinate disk is diffeomorphic to a punctured plane ball
statement:
  Suppose \(p\) lies in a coordinate chart, its chart value is the prescribed
  center \(c\), and the coordinate ball \(B(c,\rho)\) lies in the chart
  target.  Then the coordinate disk of radius \(\rho\), punctured at \(p\),
  is smoothly diffeomorphic to \(B(c,\rho)\setminus\{c\}\).
proof:
  Restrict the smooth chart diffeomorphism to the two punctured open subsets.
  Chart injectivity identifies omission of \(p\) with omission of \(c\).
-/
theorem ClosedCoordinateDisk.puncturedExpandedOpenDisk_diffeomorphic_puncturedBall
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) (p : X) (rho : ℝ)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hrho : rho ≤ D.openDisk.radius) :
    Nonempty
      (D.puncturedExpandedOpenDisk p rho ≃ₘ⟮SurfaceRealModel,
        SurfaceRealModel⟯
        complexPuncturedBallOpen D.openDisk.center rho) := by
  let B : TopologicalSpace.Opens ℂ :=
    complexPuncturedBallOpen D.openDisk.center rho
  apply deRham_boundarylessExtendedChart_restriction_diffeomorph
    SurfaceRealModel D.openDisk.chart D.openDisk.chart_mem_atlas
      (D.puncturedExpandedOpenDisk p rho) B
  · ext x
    simp only [ClosedCoordinateDisk.puncturedExpandedOpenDisk,
      puncturedSurfaceOpen, TopologicalSpace.Opens.coe_inf,
      Set.mem_inter_iff,
      ClosedCoordinateDisk.expandedOpenDisk,
      B, complexPuncturedBallOpen]
    simp only [deRham_boundarylessExtendedChart, SurfaceRealModel,
      OpenPartialHomeomorph.extend_source]
    constructor
    · rintro ⟨hxp, hx_source, hx_ball⟩
      refine ⟨hx_source, hx_ball, ?_⟩
      intro hxeq
      apply hxp
      apply D.openDisk.chart.injOn hx_source hp_source
      simpa [hcenter] using hxeq
    · rintro ⟨hx_source, hx_ball, hxne⟩
      refine ⟨?_, hx_source, hx_ball⟩
      intro hxp
      apply hxne
      simpa [hxp] using hcenter
  · intro y hy
    have hytarget : y ∈ D.openDisk.chart.target :=
      D.openDisk.ball_subset_target
        (Metric.ball_subset_ball hrho hy.1)
    simpa [deRham_boundarylessExtendedChart, SurfaceRealModel] using hytarget

/-- The defining chart, restricted to a punctured expanded coordinate disk. -/
noncomputable def ClosedCoordinateDisk.puncturedExpandedOpenDiskChartDiffeomorph
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) (p : X) (rho : ℝ)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hrho : rho ≤ D.openDisk.radius) :
    D.puncturedExpandedOpenDisk p rho ≃ₘ⟮SurfaceRealModel,
      SurfaceRealModel⟯ complexPuncturedBallOpen D.openDisk.center rho := by
  let B : TopologicalSpace.Opens ℂ :=
    complexPuncturedBallOpen D.openDisk.center rho
  apply deRham_boundarylessExtendedChart_restrictionDiffeomorph
    SurfaceRealModel D.openDisk.chart D.openDisk.chart_mem_atlas
      (D.puncturedExpandedOpenDisk p rho) B
  · ext x
    simp only [ClosedCoordinateDisk.puncturedExpandedOpenDisk,
      puncturedSurfaceOpen, TopologicalSpace.Opens.coe_inf,
      Set.mem_inter_iff,
      ClosedCoordinateDisk.expandedOpenDisk,
      B, complexPuncturedBallOpen]
    simp only [deRham_boundarylessExtendedChart, SurfaceRealModel,
      OpenPartialHomeomorph.extend_source]
    constructor
    · rintro ⟨hxp, hx_source, hx_ball⟩
      refine ⟨hx_source, hx_ball, ?_⟩
      intro hxeq
      apply hxp
      apply D.openDisk.chart.injOn hx_source hp_source
      simpa [hcenter] using hxeq
    · rintro ⟨hx_source, hx_ball, hxne⟩
      refine ⟨?_, hx_source, hx_ball⟩
      intro hxp
      apply hxne
      simpa [hxp] using hcenter
  · intro y hy
    have hytarget : y ∈ D.openDisk.chart.target :=
      D.openDisk.ball_subset_target
        (Metric.ball_subset_ball hrho hy.1)
    simpa [deRham_boundarylessExtendedChart, SurfaceRealModel] using hytarget

/--
%%handwave
name:
  Underlying coordinate formula for the punctured-disk chart diffeomorphism
statement:
  The Euclidean value of the punctured-disk chart diffeomorphism at \(y\) is
  exactly the original chart coordinate \(z(y)\).
proof:
  The diffeomorphism is defined by restricting the chart, so the equality is
  immediate.
-/
@[simp]
theorem ClosedCoordinateDisk.puncturedExpandedOpenDiskChartDiffeomorph_coe_apply
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) (p : X) (rho : ℝ)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hrho : rho ≤ D.openDisk.radius)
    (y : D.puncturedExpandedOpenDisk p rho) :
    ((D.puncturedExpandedOpenDiskChartDiffeomorph
      p rho hp_source hcenter hrho y :
        complexPuncturedBallOpen D.openDisk.center rho) : ℂ) =
      D.openDisk.chart (y : X) := by
  rfl

/-- The radial annular coordinate on a doubled coordinate disk. -/
noncomputable def ClosedCoordinateDisk.radialPuncturedCollarDiffeomorph
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hdouble : 2 * D.closedRadius ≤ D.openDisk.radius) :
    D.puncturedExpandedOpenDisk p (2 * D.closedRadius) ≃ₘ⟮
      SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ :=
  (D.puncturedExpandedOpenDiskChartDiffeomorph p
      (2 * D.closedRadius) hp_source hcenter hdouble).trans
    (complexPuncturedDoubleBallDiffeomorphAnnularCylinder
      D.openDisk.center D.closedRadius D.closedRadius_pos)

/--
%%handwave
name:
  The negative radial collar side is the coordinate-disk interior
statement:
  For the radial annular collar of a doubled coordinate disk,
  \[
    \Phi(y)_2<0
    \quad\Longleftrightarrow\quad
    y\in D^\circ.
  \]
proof:
  In Euclidean coordinates, negativity is equivalent to distance from the
  center being below the closed-disk radius.  The chart formula translates
  this precisely into membership in the open coordinate disk.
-/
theorem ClosedCoordinateDisk.radialPuncturedCollarDiffeomorph_second_lt_zero_iff
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hdouble : 2 * D.closedRadius ≤ D.openDisk.radius)
    (y : D.puncturedExpandedOpenDisk p (2 * D.closedRadius)) :
    (D.radialPuncturedCollarDiffeomorph p hp_source hcenter hdouble y).2 < 0 ↔
      (y : X) ∈ D.toSmoothBoundaryDomain.carrier := by
  change
    (complexPuncturedDoubleBallDiffeomorphAnnularCylinder
      D.openDisk.center D.closedRadius D.closedRadius_pos
      (D.puncturedExpandedOpenDiskChartDiffeomorph p
        (2 * D.closedRadius) hp_source hcenter hdouble y)).2 < 0 ↔ _
  rw [complexPuncturedDoubleBallDiffeomorphAnnularCylinder_second_lt_zero_iff]
  rw [D.puncturedExpandedOpenDiskChartDiffeomorph_coe_apply]
  simp only [ClosedCoordinateDisk.toSmoothBoundaryDomain,
    ClosedCoordinateDisk.expandedOpenDisk]
  constructor
  · intro hdist
    exact ⟨y.2.2.1, by simpa [Metric.mem_ball] using hdist⟩
  · rintro ⟨_hsource, hball⟩
    simpa [Metric.mem_ball] using hball

/--
%%handwave
name:
  The positive radial collar side is outside the closed disk
statement:
  For the radial annular collar of a doubled coordinate disk,
  \[
    \Phi(y)_2>0
    \quad\Longleftrightarrow\quad
    y\notin\overline{D^\circ}.
  \]
proof:
  Positivity means that the chart distance from the center exceeds the
  closed-disk radius.  Since the closure of the open coordinate disk is the
  corresponding closed coordinate disk, this is exactly exterior membership.
-/
theorem ClosedCoordinateDisk.radialPuncturedCollarDiffeomorph_second_pos_iff
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hdouble : 2 * D.closedRadius ≤ D.openDisk.radius)
    (y : D.puncturedExpandedOpenDisk p (2 * D.closedRadius)) :
    0 < (D.radialPuncturedCollarDiffeomorph
      p hp_source hcenter hdouble y).2 ↔
      (y : X) ∉ closure D.toSmoothBoundaryDomain.carrier := by
  change
    0 < (complexPuncturedDoubleBallDiffeomorphAnnularCylinder
      D.openDisk.center D.closedRadius D.closedRadius_pos
      (D.puncturedExpandedOpenDiskChartDiffeomorph p
        (2 * D.closedRadius) hp_source hcenter hdouble y)).2 ↔ _
  rw [complexPuncturedDoubleBallDiffeomorphAnnularCylinder_second_pos_iff]
  rw [D.puncturedExpandedOpenDiskChartDiffeomorph_coe_apply]
  change D.closedRadius < dist (D.openDisk.chart (y : X))
      D.openDisk.center ↔
    (y : X) ∉ closure (D.expandedOpenDisk D.closedRadius)
  rw [D.closure_expandedOpenDisk_closedRadius]
  rw [D.carrier_eq]
  constructor
  · intro hdist hy
    exact (not_lt_of_ge (by
      simpa [Metric.mem_closedBall] using hy.2)) hdist
  · intro hy
    have hnotle : ¬ dist (D.openDisk.chart (y : X))
        D.openDisk.center ≤ D.closedRadius := by
      intro hle
      apply hy
      exact ⟨y.2.2.1, by simpa [Metric.mem_closedBall] using hle⟩
    exact lt_of_not_ge hnotle

/--
%%handwave
name:
  The doubled radial collar and disk exterior cover the punctured surface
statement:
  If \(p\) is the center of a closed coordinate disk \(D\), then
  \[
    \bigl(D_{2R}\setminus\{p\}\bigr)\cup(X\setminus D)
      =X\setminus\{p\}.
  \]
proof:
  A point outside \(D\) is in the exterior piece.  A point of \(D\) distinct
  from \(p\) has coordinate radius at most \(R<2R\), so it lies in the doubled
  punctured disk.
-/
theorem ClosedCoordinateDisk.radialPuncturedCollarUnion_eq_puncturedSurfaceOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hVopen : IsOpen D.carrierᶜ) :
    exteriorComponentCollarUnion
        (D.puncturedExpandedOpenDisk p (2 * D.closedRadius))
        D.carrierᶜ hVopen =
      puncturedSurfaceOpen p := by
  have hp_carrier : p ∈ D.carrier := by
    rw [D.carrier_eq]
    refine ⟨hp_source, ?_⟩
    simpa [Metric.mem_closedBall, hcenter] using D.closedRadius_pos.le
  have hRdouble : D.closedRadius < 2 * D.closedRadius := by
    linarith [D.closedRadius_pos]
  ext x
  constructor
  · rintro (hxW | hxV)
    · exact hxW.1
    · intro hxp
      apply hxV
      simpa [hxp] using hp_carrier
  · intro hxp
    by_cases hxD : x ∈ D.carrier
    · left
      rw [D.carrier_eq] at hxD
      refine ⟨hxp, hxD.1, ?_⟩
      change D.openDisk.chart x ∈
        Metric.ball D.openDisk.center (2 * D.closedRadius)
      rw [Metric.mem_ball]
      have hle : dist (D.openDisk.chart x) D.openDisk.center ≤
          D.closedRadius := by
        simpa [Metric.mem_closedBall] using hxD.2
      exact hle.trans_lt hRdouble
    · exact Or.inr hxD

/--
%%handwave
name:
  The domain half of the doubled collar is the punctured inner disk
statement:
  Intersecting the doubled punctured coordinate disk with the open inner disk
  gives exactly the punctured coordinate disk of radius \(R\).
proof:
  Membership in the inner disk already implies the stronger radius bound
  \(R<2R\); the puncture condition is unchanged.
-/
theorem ClosedCoordinateDisk.radialPuncturedCollarDomain_eq_puncturedExpandedOpenDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : ClosedCoordinateDisk X) (p : X) :
    (D.puncturedExpandedOpenDisk p (2 * D.closedRadius) ⊓
        ⟨D.toSmoothBoundaryDomain.carrier,
          D.toSmoothBoundaryDomain.isOpen⟩ : TopologicalSpace.Opens X) =
      D.puncturedExpandedOpenDisk p D.closedRadius := by
  ext x
  constructor
  · rintro ⟨⟨hxp, _hxdouble⟩, hxinner⟩
    exact ⟨hxp, hxinner⟩
  · rintro ⟨hxp, hxinner⟩
    refine ⟨⟨hxp, ?_⟩, hxinner⟩
    rcases hxinner with ⟨hxsource, hxball⟩
    refine ⟨hxsource, ?_⟩
    apply Metric.ball_subset_ball _ hxball
    linarith [D.closedRadius_pos]

/--
%%handwave
name:
  A punctured coordinate disk is an annular cylinder
statement:
  A coordinate disk punctured at its coordinate center is smoothly
  diffeomorphic to \(S^1\times\mathbb R\).
proof:
  The chart identifies it with a punctured Euclidean ball.  Radial compression
  identifies that ball with the punctured plane, and polar coordinates identify
  the punctured plane with the annular cylinder.
-/
theorem ClosedCoordinateDisk.puncturedExpandedOpenDisk_diffeomorphic_annularCylinder
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) (p : X)
    (hp : p ∈ D.expandedOpenDisk D.closedRadius)
    (hcenter : D.openDisk.chart p = D.openDisk.center) :
    Nonempty
      (D.puncturedExpandedOpenDisk p D.closedRadius ≃ₘ⟮SurfaceRealModel,
        AnnularCylinderModel⟯ Circle × ℝ) := by
  let B : TopologicalSpace.Opens ℂ :=
    complexPuncturedBallOpen D.openDisk.center D.closedRadius
  have hp_source : p ∈ D.openDisk.chart.source := by
    exact hp.1
  have hchart : Nonempty
      (D.puncturedExpandedOpenDisk p D.closedRadius ≃ₘ⟮SurfaceRealModel,
        SurfaceRealModel⟯ B) := by
    exact D.puncturedExpandedOpenDisk_diffeomorphic_puncturedBall
      p D.closedRadius hp_source hcenter D.closedRadius_lt_openRadius.le
  rcases hchart with ⟨chartPhi⟩
  let radialPhi :=
    (complexPuncturedPlaneDiffeomorphPuncturedBall
      D.openDisk.center D.closedRadius D.closedRadius_pos).symm
  exact ⟨chartPhi.trans (radialPhi.trans
    complexPuncturedPlaneDiffeomorphAnnularCylinder)⟩

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Injectivity of restriction to a punctured coordinate disk
statement:
  If \(H^1_{\mathrm{dR}}(X)=0\), then restriction
  \[
    H^1_{\mathrm{dR}}(X\setminus\{p\})
      \longrightarrow
    H^1_{\mathrm{dR}}(D^\circ\setminus\{p\})
  \]
  is injective for every coordinate disk containing \(p\).
proof:
  The punctured surface together with the unpunctured coordinate disk covers
  \(X\), and the disk has trivial first de Rham cohomology.  The
  Mayer–Vietoris restriction criterion, together with vanishing of ambient
  \(H^1\), gives injectivity on their intersection.
-/
theorem puncturedSurfaceOpen_coordinateDisk_restriction_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (p : X) (D : ClosedCoordinateDisk X)
    (hp : p ∈ D.expandedOpenDisk D.closedRadius) :
    let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
    let V : TopologicalSpace.Opens X :=
      ⟨D.expandedOpenDisk D.closedRadius,
        D.expandedOpenDisk_isOpen D.closedRadius⟩
    Function.Injective
      (deRhamCohomologyRestrictionOfLE
        (I := SurfaceRealModel) (A := ℝ)
        (W := (U ⊓ V : TopologicalSpace.Opens X)) (V := U)
        inf_le_left 1) := by
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  let V : TopologicalSpace.Opens X :=
    ⟨D.expandedOpenDisk D.closedRadius,
      D.expandedOpenDisk_isOpen D.closedRadius⟩
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : SigmaCompactSpace X := by infer_instance
  letI : Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := V) (A := ℝ) 1) := by
    simpa [V] using D.expandedOpenDisk_deRhamH1_subsingleton
  apply deRhamH1_left_restriction_injective_of_ambient_right_subsingleton
    SurfaceRealModel U V
  ext x
  simp only [TopologicalSpace.Opens.coe_sup,
    TopologicalSpace.Opens.coe_top, Set.mem_union, Set.mem_univ, iff_true]
  by_cases hxp : x = p
  · right
    simpa [V, hxp] using hp
  · left
    exact hxp

/--
%%handwave
name:
  The exterior of a coordinate disk is its unique exterior component
statement:
  In a connected noncompact Riemann surface, the complement of a closed
  coordinate disk is the unique component of that complement and escapes
  every compact subset of the surface.
proof:
  Coordinate-disk path surgery makes the complement path connected.  It is
  nonempty because the disk is compact and the surface is noncompact.  Given
  any other compact set, its union with the disk is still compact and hence
  cannot cover the noncompact surface; a point outside that union witnesses
  escape.
-/
theorem closedCoordinateDisk_complement_isExteriorComponent
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [NoncompactSpace X]
    (D : ClosedCoordinateDisk X) :
    IsExteriorComponent D.carrier D.carrierᶜ := by
  have hnonempty : D.carrierᶜ.Nonempty :=
    Set.nonempty_compl.mpr D.compact.ne_univ
  have hcomponent : IsComponentOf D.carrierᶜ D.carrierᶜ := by
    rcases hnonempty with ⟨x, hx⟩
    apply isComponentOf_iff_exists_connectedComponentIn.mpr
    refine ⟨x, hx, ?_⟩
    exact (closedCoordinateDisk_complement_preconnected D).connectedComponentIn hx |>.symm
  refine hcomponent.isExteriorComponent_of_escapes ?_
  intro L hL
  have hunion : IsCompact (D.carrier ∪ L) := D.compact.union hL
  rcases Set.nonempty_compl.mpr hunion.ne_univ with ⟨x, hx⟩
  refine ⟨x, ?_, ?_⟩
  · intro hxD
    exact hx (Or.inl hxD)
  · intro hxL
    exact hx (Or.inr hxL)

/--
%%handwave
name:
  The smooth interior of a coordinate disk has one exterior component
statement:
  The complement of the closure of the smooth open coordinate disk is exactly
  the exterior component given by the complement of the corresponding closed
  coordinate disk.
proof:
  The open coordinate disk closes up to the closed coordinate disk, and the
  preceding theorem identifies the latter's complement as an exterior
  component.
-/
theorem ClosedCoordinateDisk.smoothDomain_complement_isExteriorComponent
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [NoncompactSpace X]
    (D : ClosedCoordinateDisk X) :
    IsExteriorComponent
      (closure D.toSmoothBoundaryDomain.carrier) D.carrierᶜ := by
  simpa [ClosedCoordinateDisk.toSmoothBoundaryDomain,
    D.closure_expandedOpenDisk_closedRadius] using
      closedCoordinateDisk_complement_isExteriorComponent D

/--
%%handwave
name:
  A global closed angular form around a puncture
statement:
  On a noncompact Riemann surface with \(H^1_{\mathrm{dR}}(X)=0\), a radial
  coordinate disk centered at \(p\) determines a closed one-form \(\eta\) on
  \(X\setminus\{p\}\) whose restriction to the inner half of the radial collar
  is the pullback of the standard angular form on \(S^1\times\mathbb R\).
proof:
  The complement of the closed coordinate disk is its exterior component.
  Apply the exterior angular-extension theorem to the side-preserving radial
  collar, then transport the resulting closed form from the collar–exterior
  union, which equals the punctured surface.
-/
theorem ClosedCoordinateDisk.exists_closed_puncturedAngularForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hdouble : 2 * D.closedRadius ≤ D.openDisk.radius)
    (v : Circle) :
    let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
    let Q := W ⊓
      ⟨D.toSmoothBoundaryDomain.carrier,
        D.toSmoothBoundaryDomain.isOpen⟩
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := puncturedSurfaceOpen p)
          (inf_le_left.trans inf_le_left) 1 eta.1 =
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := W) inf_le_left 1
            (exteriorCutoffAngularCollarOneForm W
              (D.radialPuncturedCollarDiffeomorph
                p hp_source hcenter hdouble) v) := by
  dsimp only
  let D₀ : SmoothBoundaryDomain X := D.toSmoothBoundaryDomain
  let V : Set X := D.carrierᶜ
  let hVext : IsExteriorComponent (closure D₀.carrier) V := by
    simpa [D₀, V] using D.smoothDomain_complement_isExteriorComponent
  let hV := hVext.isComponentOf
  let hVopen : IsOpen V :=
    hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
  let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
  let phi := D.radialPuncturedCollarDiffeomorph
    p hp_source hcenter hdouble
  have hnoncompact : ¬ CompactSpace X :=
    not_compactSpace_iff.mpr inferInstance
  have hDpre : IsPreconnected D₀.carrier := by
    simpa [D₀] using
      D.toSmoothBoundaryDomain_isPathConnected.isConnected.isPreconnected
  rcases complementComponentCollarData_nonempty
      hnoncompact D₀ hDpre V hV with ⟨C⟩
  have hp_frontier : (C.p : X) ∈
      frontier (D.expandedOpenDisk D.closedRadius) := by
    simpa [D₀, ClosedCoordinateDisk.toSmoothBoundaryDomain] using C.p.2
  have hp_circle := D.frontier_expandedOpenDisk_subset_radiusBoundaryCircle
    D.closedRadius_lt_openRadius hp_frontier
  have hp_dist : dist (D.openDisk.chart (C.p : X))
      D.openDisk.center = D.closedRadius := by
    simpa [ClosedCoordinateDisk.radiusBoundaryCircle,
      Metric.mem_sphere, dist_eq_norm] using hp_circle.2
  have hp_ne : (C.p : X) ≠ p := by
    intro heq
    have : (0 : ℝ) = D.closedRadius := by
      simpa [heq, hcenter] using hp_dist
    exact D.closedRadius_pos.ne' this.symm
  have hpW : (C.p : X) ∈ W := by
    refine ⟨hp_ne, hp_circle.1, ?_⟩
    change D.openDisk.chart (C.p : X) ∈
      Metric.ball D.openDisk.center (2 * D.closedRadius)
    rw [Metric.mem_ball, hp_dist]
    linarith [D.closedRadius_pos]
  rcases hVext.exists_closed_exteriorAngularExtension
      E D₀ W phi
      (fun y => by
        simpa [D₀, phi] using
          (D.radialPuncturedCollarDiffeomorph_second_pos_iff
            p hp_source hcenter hdouble y).symm)
      V C.p hpW C.p_mem_frontier v with
    ⟨eta, heta⟩
  have hS : exteriorComponentCollarUnion W V hVopen =
      puncturedSurfaceOpen p := by
    simpa [W, V] using
      D.radialPuncturedCollarUnion_eq_puncturedSurfaceOpen
        p hp_source hcenter hVopen
  let S : TopologicalSpace.Opens X :=
    exteriorComponentCollarUnion W V hVopen
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  let etaU : DeRhamClosedForms (I := SurfaceRealModel)
      (M := U) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel SurfaceRealModel
      (opensDiffeomorphOfMutualLE U S hS.ge hS.le) 1 eta
  refine ⟨etaU, ?_⟩
  let Q : TopologicalSpace.Opens X :=
    W ⊓ ⟨D₀.carrier, D₀.isOpen⟩
  have hQU : Q ≤ U := inf_le_left.trans inf_le_left
  have hQS : Q ≤ S := inf_le_left.trans le_sup_left
  have htransport := restrictSmoothFormsOfLE_transportOpenMutualLE
    Q S U hQS hQU hS.le hS.ge eta.1
  calc
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := Q) (V := U) hQU 1 etaU.1 =
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := Q) (V := S) hQS 1 eta.1 := by
          simpa [etaU, S, U, smoothFormsTransportOpenMutualLE] using htransport
    _ = restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := Q) (V := W) inf_le_left 1
          (exteriorCutoffAngularCollarOneForm W phi v) := by
            simpa [S, Q] using heta

/--
%%handwave
name:
  A puncture angular form with normalized local period
statement:
  The global closed puncture form can be chosen with a smooth cycle \(c\) in
  the punctured inner coordinate disk such that
  \[
    \partial c=0,
    \qquad
    \int_c\eta=-1.
  \]
proof:
  Choose the global form agreeing with the standard angular collar form on
  the inner half.  Pull back the standard negative-half-cylinder cycle whose
  angular period is \(-1\); equality of the restricted forms transfers that
  period to \(\eta\).
-/
theorem ClosedCoordinateDisk.exists_closed_puncturedAngularForm_normalized
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hdouble : 2 * D.closedRadius ≤ D.openDisk.radius)
    (v : Circle) :
    let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
    let Q := W ⊓
      ⟨D.toSmoothBoundaryDomain.carrier,
        D.toSmoothBoundaryDomain.isOpen⟩
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      ∃ c : SingularChain (I := SurfaceRealModel) (M := Q) 1 ∞,
        boundary (I := SurfaceRealModel) c = 0 ∧
          integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ)
              (inf_le_left.trans inf_le_left) 1 eta).1 c = -1 := by
  dsimp only
  let D₀ : SmoothBoundaryDomain X := D.toSmoothBoundaryDomain
  let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
  let Q : TopologicalSpace.Opens X :=
    W ⊓ ⟨D₀.carrier, D₀.isOpen⟩
  let phi := D.radialPuncturedCollarDiffeomorph
    p hp_source hcenter hdouble
  have hside : ∀ y : W,
      ((y : X) ∈ D₀.carrier ↔ (phi y).2 < 0) := by
    intro y
    simpa [D₀, phi] using
      (D.radialPuncturedCollarDiffeomorph_second_lt_zero_iff
        p hp_source hcenter hdouble y).symm
  let psi := sidePreservingAnnularCollarDomainRestriction D₀ W phi hside
  rcases D.exists_closed_puncturedAngularForm
      E p hp_source hcenter hdouble v with ⟨eta, heta⟩
  rcases exists_sidePreservingAnnularCollarDomainCycle_angular_period_eq_neg_one
      D₀ W phi hside v with ⟨c, hcycle, hperiod⟩
  refine ⟨eta, c, hcycle, ?_⟩
  have hetaQ :
      (deRhamClosedFormsRestrictionOfLE
        (I := SurfaceRealModel) (A := ℝ)
        (inf_le_left.trans inf_le_left) 1 eta).1 =
      smoothFormsPullbackDiffeomorph SurfaceRealModel
        AnnularCylinderModel psi 1
        (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
          negativeAnnularCylinderOpen 1
          (annularAngularClosedForm v).1) := by
    calc
      (deRhamClosedFormsRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ)
          (inf_le_left.trans inf_le_left) 1 eta).1 =
        restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q)
          (V := puncturedSurfaceOpen p)
          (inf_le_left.trans inf_le_left) 1 eta.1 := rfl
      _ = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q) (V := W) inf_le_left 1
            (exteriorCutoffAngularCollarOneForm W phi v) := by
              simpa [D₀, W, Q, phi] using heta
      _ = smoothFormsPullbackDiffeomorph SurfaceRealModel
          AnnularCylinderModel psi 1
          (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            negativeAnnularCylinderOpen 1
            (annularAngularClosedForm v).1) := by
              simpa [psi] using
                (restrict_exteriorCutoffAngularCollarOneForm_domain_eq_pullback_negative
                  D₀ W phi hside v)
  rw [hetaQ]
  simpa [D₀, W, Q, phi, psi] using hperiod

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Surjectivity of restriction to a punctured coordinate disk
statement:
  Under the noncompactness and vanishing ambient cohomology hypotheses,
  restriction
  \[
    H^1_{\mathrm{dR}}(X\setminus\{p\})
      \longrightarrow
    H^1_{\mathrm{dR}}(D^\circ\setminus\{p\})
  \]
  is surjective.
proof:
  The global angular extension restricts to the pullback of the standard
  angular form on an annular cylinder and hence gives a nonzero class in the
  target.  Since the target annulus has one-dimensional first cohomology, any
  linear map whose range contains a nonzero class is surjective.
-/
theorem puncturedSurfaceOpen_coordinateDisk_restriction_surjective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hdouble : 2 * D.closedRadius ≤ D.openDisk.radius)
    (v : Circle) :
    let U := puncturedSurfaceOpen p
    let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
    let Q := W ⊓
      ⟨D.toSmoothBoundaryDomain.carrier,
        D.toSmoothBoundaryDomain.isOpen⟩
    Function.Surjective
      (deRhamCohomologyRestrictionOfLE
        (I := SurfaceRealModel) (A := ℝ)
        (W := Q) (V := U) (inf_le_left.trans inf_le_left) 1) := by
  dsimp only
  let U := puncturedSurfaceOpen p
  let D₀ : SmoothBoundaryDomain X := D.toSmoothBoundaryDomain
  let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
  let Q : TopologicalSpace.Opens X :=
    W ⊓ ⟨D₀.carrier, D₀.isOpen⟩
  let phi := D.radialPuncturedCollarDiffeomorph
    p hp_source hcenter hdouble
  have hside : ∀ y : W,
      ((y : X) ∈ D₀.carrier ↔ (phi y).2 < 0) := by
    intro y
    simpa [D₀, phi] using
      (D.radialPuncturedCollarDiffeomorph_second_lt_zero_iff
        p hp_source hcenter hdouble y).symm
  let psi := sidePreservingAnnularCollarDomainRestriction D₀ W phi hside
  let psiFull : Q ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ :=
    psi.trans negativeAnnularCylinderOpenDiffeomorphAnnularCylinder
  rcases D.exists_closed_puncturedAngularForm
      E p hp_source hcenter hdouble v with ⟨eta, heta⟩
  let betaNeg : DeRhamClosedForms (I := AnnularCylinderModel)
      (M := negativeAnnularCylinderOpen) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionToOpen (I := AnnularCylinderModel)
      (A := ℝ) negativeAnnularCylinderOpen 1 (annularAngularClosedForm v)
  let betaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
      AnnularCylinderModel psi 1 betaNeg
  let etaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      (inf_le_left.trans inf_le_left) 1 eta
  have hetaQForm : etaQ.1 = betaQ.1 := by
    calc
      etaQ.1 = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q) (V := U)
          (inf_le_left.trans inf_le_left) 1 eta.1 := rfl
      _ = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q) (V := W) inf_le_left 1
            (exteriorCutoffAngularCollarOneForm W phi v) := by
              simpa [U, D₀, W, Q, phi] using heta
      _ = smoothFormsPullbackDiffeomorph SurfaceRealModel
          AnnularCylinderModel psi 1
          (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            negativeAnnularCylinderOpen 1 (annularAngularClosedForm v).1) :=
        restrict_exteriorCutoffAngularCollarOneForm_domain_eq_pullback_negative
          D₀ W phi hside v
      _ = betaQ.1 := rfl
  have hetaQ : etaQ = betaQ := by
    apply Subtype.ext
    exact hetaQForm
  have hbetaNeg :
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
        (M := negativeAnnularCylinderOpen) (A := ℝ) 1).mkQ betaNeg ≠ 0 := by
    simpa [betaNeg] using annularAngularClosedForm_negative_class_ne_zero v
  have hbetaQ :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1).mkQ betaQ ≠ 0 := by
    intro hzero
    have hpullzero :
        deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
            AnnularCylinderModel psi 1
            ((DeRhamExactClosedForms (I := AnnularCylinderModel)
              (M := negativeAnnularCylinderOpen) (A := ℝ) 1).mkQ betaNeg) = 0 := by
      simpa [betaQ, deRhamCohomologyPullbackDiffeomorph,
        Submodule.mapQ_apply] using hzero
    have hinverse := congrArg
      (deRhamCohomologyPullbackDiffeomorph AnnularCylinderModel
        SurfaceRealModel psi.symm 1) hpullzero
    have hinverseZero :
        deRhamCohomologyPullbackDiffeomorph AnnularCylinderModel
          SurfaceRealModel psi.symm 1
          (0 : DeRhamCohomology (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1) = 0 :=
      LinearMap.map_zero _
    rw [hinverseZero,
      deRhamCohomologyPullbackDiffeomorph_symm_comp] at hinverse
    exact hbetaNeg hinverse
  have hetaQClass :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1).mkQ etaQ ≠ 0 := by
    rw [hetaQ]
    exact hbetaQ
  apply deRhamH1_map_surjective_of_annular_nonzero_mem_range
    SurfaceRealModel SurfaceRealModel psiFull v
    (deRhamCohomologyRestrictionOfLE
      (I := SurfaceRealModel) (A := ℝ)
      (W := Q) (V := U) (inf_le_left.trans inf_le_left) 1)
    ((DeRhamExactClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1).mkQ etaQ) hetaQClass
  refine ⟨
    (DeRhamExactClosedForms (I := SurfaceRealModel)
      (M := U) (A := ℝ) 1).mkQ eta, ?_⟩
  rfl

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Cohomology of the punctured surface is detected on a punctured disk
statement:
  If \(X\) is noncompact and \(H^1_{\mathrm{dR}}(X)=0\), then restriction
  gives an isomorphism
  \[
    H^1_{\mathrm{dR}}(X\setminus\{p\})
      \cong
    H^1_{\mathrm{dR}}(D^\circ\setminus\{p\})
  \]
  for a centered coordinate disk \(D\).
proof:
  The restriction is injective by the Mayer–Vietoris argument and surjective
  because the global angular extension supplies the annular generator.
-/
theorem puncturedSurfaceOpen_coordinateDisk_restriction_bijective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hdouble : 2 * D.closedRadius ≤ D.openDisk.radius)
    (v : Circle) :
    let U := puncturedSurfaceOpen p
    let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
    let Q := W ⊓
      ⟨D.toSmoothBoundaryDomain.carrier,
        D.toSmoothBoundaryDomain.isOpen⟩
    Function.Bijective
      (deRhamCohomologyRestrictionOfLE
        (I := SurfaceRealModel) (A := ℝ)
        (W := Q) (V := U) (inf_le_left.trans inf_le_left) 1) := by
  dsimp only
  constructor
  · have hp : p ∈ D.expandedOpenDisk D.closedRadius := by
      refine ⟨hp_source, ?_⟩
      simpa [Metric.mem_ball, hcenter] using D.closedRadius_pos
    let U := puncturedSurfaceOpen p
    let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
    let Q := W ⊓
      ⟨D.toSmoothBoundaryDomain.carrier,
        D.toSmoothBoundaryDomain.isOpen⟩
    let Qsmall := D.puncturedExpandedOpenDisk p D.closedRadius
    have hQ : Q = Qsmall := by
      simpa [Q, Qsmall, W] using
        D.radialPuncturedCollarDomain_eq_puncturedExpandedOpenDisk p
    have hQsmallQ : Qsmall ≤ Q := hQ.ge
    have hQU : Q ≤ U := inf_le_left.trans inf_le_left
    have hinj : Function.Injective
        (deRhamCohomologyRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ)
          (W := Qsmall) (V := U) inf_le_left 1) := by
      simpa [U, Qsmall, ClosedCoordinateDisk.puncturedExpandedOpenDisk] using
        (puncturedSurfaceOpen_coordinateDisk_restriction_injective p D hp)
    intro a b hab
    apply hinj
    calc
      deRhamCohomologyRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ)
          (W := Qsmall) (V := U) (hQsmallQ.trans hQU) 1 a =
        deRhamCohomologyRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ)
          (W := Qsmall) (V := Q) hQsmallQ 1
          (deRhamCohomologyRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ)
            (W := Q) (V := U) hQU 1 a) :=
        deRhamCohomologyRestrictionOfLE_trans
          Qsmall Q U hQsmallQ hQU 1 a
      _ = deRhamCohomologyRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ)
          (W := Qsmall) (V := Q) hQsmallQ 1
          (deRhamCohomologyRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ)
            (W := Q) (V := U) hQU 1 b) := congrArg _ hab
      _ = deRhamCohomologyRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ)
          (W := Qsmall) (V := U) (hQsmallQ.trans hQU) 1 b :=
        (deRhamCohomologyRestrictionOfLE_trans
          Qsmall Q U hQsmallQ hQU 1 b).symm
  · exact puncturedSurfaceOpen_coordinateDisk_restriction_surjective
      E D p hp_source hcenter hdouble v

/-- The collar and closed angular extension attached to a coordinate disk. -/
structure ClosedCoordinateDiskExteriorAngularExtensionData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : ClosedCoordinateDisk X) (v : Circle) where
  collar : ComplementComponentCollarData D.toSmoothBoundaryDomain D.carrierᶜ
    D.smoothDomain_complement_isExteriorComponent.isComponentOf
  eta : DeRhamClosedForms (I := SurfaceRealModel)
    (M := exteriorComponentCollarUnion collar.W D.carrierᶜ
      (D.smoothDomain_complement_isExteriorComponent.isComponentOf
        |>.isOpen_of_isOpen isClosed_closure.isOpen_compl))
    (A := ℝ) 1
  restrict_eq :
    let S := exteriorComponentCollarUnion collar.W D.carrierᶜ
      (D.smoothDomain_complement_isExteriorComponent.isComponentOf
        |>.isOpen_of_isOpen isClosed_closure.isOpen_compl)
    let Q := collar.W ⊓
      ⟨D.toSmoothBoundaryDomain.carrier,
        D.toSmoothBoundaryDomain.isOpen⟩
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := Q) (V := S) (inf_le_left.trans le_sup_left) 1 eta.1 =
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := Q) (V := collar.W) inf_le_left 1
          (exteriorCutoffAngularCollarOneForm collar.W collar.phi v)

/--
%%handwave
name:
  The angular class of a coordinate circle extends toward infinity
statement:
  Let a closed coordinate disk lie in a connected noncompact Riemann surface
  with vanishing first de Rham cohomology.  For every normalized angular class
  on a collar of its boundary, there is a closed smooth one-form on the union
  of that collar with the disk exterior which agrees with the angular class on
  the inner half-collar.
proof:
  The coordinate disk has path-connected interior and its complement is the
  unique exterior component.  A side-preserving annular collar therefore
  exists.  Cut off the angular form only on the exterior side.  Its derivative
  is a compactly supported two-form in the exterior component; transport this
  mass to infinity and subtract a primitive of the resulting defect.  The
  correction is supported away from the inner half-collar, so the resulting
  one-form is closed and retains the prescribed angular class there.
-/
theorem closedCoordinateDiskExteriorAngularExtensionData_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : ClosedCoordinateDisk X) (v : Circle) :
    Nonempty (ClosedCoordinateDiskExteriorAngularExtensionData X E D v) := by
  let D₀ : SmoothBoundaryDomain X := D.toSmoothBoundaryDomain
  let V : Set X := D.carrierᶜ
  let hVext : IsExteriorComponent (closure D₀.carrier) V := by
    simpa [D₀, V] using D.smoothDomain_complement_isExteriorComponent
  let hV : IsComponentOf V (closure D₀.carrier)ᶜ := hVext.isComponentOf
  have hnoncompact : ¬ CompactSpace X :=
    not_compactSpace_iff.mpr inferInstance
  have hDpre : IsPreconnected D₀.carrier := by
    simpa [D₀] using
      D.toSmoothBoundaryDomain_isPathConnected.isConnected.isPreconnected
  rcases complementComponentCollarData_nonempty
      hnoncompact D₀ hDpre V hV with ⟨C⟩
  rcases hVext.exists_closed_exteriorAngularExtension
      E D₀ C.W C.phi C.exterior_side V C.p C.p_mem_collar
        C.p_mem_frontier v with ⟨eta, heta⟩
  refine ⟨{ collar := ?_, eta := ?_, restrict_eq := ?_ }⟩
  · simpa [D₀, V, hV] using C
  · simpa [D₀, V, hV] using eta
  · simpa [D₀, V, hV] using heta

end
end JJMath.Uniformization
