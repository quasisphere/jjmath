import JJMath.Analysis.Weyl
import JJMath.Quasiconformal.LinearAlgebra
import JJMath.Quasiconformal.LocalSobolev
import JJMath.Quasiconformal.SobolevBeurling
import JJMath.Quasiconformal.SobolevMorrey
import JJMath.Quasiconformal.ChangeOfVariables
import JJMath.Quasiconformal.CapacitySeparation
import JJMath.Topology.PlanarDegree

/-!
# Open and discrete theorem for planar maps of bounded distortion

This file isolates the central topological-analytic theorem for planar
quasiregular maps.  Its proof is the remaining analytic leaf needed to turn
the constructed principal Beltrami solution into a homeomorphism.
-/

namespace JJMath

open Set MeasureTheory
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Positive-Jacobian affine maps have local index one
statement:
  Let $L:\mathbb C\to\mathbb C$ be real linear with $J(L)>0$, and set
  $g(\xi)=w+L(\xi-z)$. For every $r>0$, the loop
  $g|_{\partial B(z,r)}$ avoids $w$ and has winding number $1$ about $w$.
proof:
  Write $L(\xi)=a\xi+b\overline\xi$. Positivity of the Jacobian gives
  $|b|<|a|$. Thus the restriction of $L$ to every centered circle is closer
  to the complex-linear map $\xi\mapsto a\xi$ than that reference loop is to
  zero. The two loops have the same winding number, while normalization
  cancels the nonzero scalar $a$ from the reference loop and leaves the
  standard positive circle.
-/
theorem exists_planarCircleIndex_affine_eq_one_of_weakJacobian_pos
    (L : ℂ →L[ℝ] ℂ) (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hJ : 0 < weakJacobian L) :
    ∃ havoid : ∀ t,
        imageCircleLoop (fun ξ ↦ w + L (ξ - z))
          (by fun_prop) z r t ≠ w,
      planarCircleIndex (fun ξ ↦ w + L (ξ - z))
        (by fun_prop) z w r hr havoid = 1 := by
  let a : ℂ := weakDZ L
  let b : ℂ := weakDBar L
  let f : ℂ → ℂ := fun ξ ↦ w + a * (ξ - z)
  let g : ℂ → ℂ := fun ξ ↦ w + L (ξ - z)
  have hf : Continuous f := by fun_prop
  have hg : Continuous g := by fun_prop
  have hba : ‖b‖ < ‖a‖ := by
    simpa [a, b] using
      norm_weakDBar_lt_norm_weakDZ_of_weakJacobian_pos hJ
  have ha : a ≠ 0 := by
    intro ha
    exact (not_lt_of_ge (norm_nonneg b)) (by simpa [ha] using hba)
  have hfavoid : ∀ t, imageCircleLoop f hf z r t ≠ w := by
    intro t ht
    have hzero : a * (complexCircleLoop z r t - z) = 0 := by
      simpa [imageCircleLoop, f] using sub_eq_zero.mpr ht
    exact complexCircleLoop_ne_center z hr t
      (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left ha))
  have hgavoid : ∀ t, imageCircleLoop g hg z r t ≠ w := by
    intro t ht
    have hzero : L (complexCircleLoop z r t - z) = 0 := by
      simpa [imageCircleLoop, g] using sub_eq_zero.mpr ht
    have hlower :
        (‖a‖ - ‖b‖) * ‖complexCircleLoop z r t - z‖ ≤
          ‖L (complexCircleLoop z r t - z)‖ := by
      simpa [a, b] using
        norm_weakDZ_sub_norm_weakDBar_mul_le L
          (complexCircleLoop z r t - z)
    rw [hzero, norm_zero] at hlower
    have hpos : 0 < ‖a‖ - ‖b‖ := sub_pos.mpr hba
    have hnormpos : 0 < ‖complexCircleLoop z r t - z‖ :=
      norm_pos_iff.mpr
        (sub_ne_zero.mpr (complexCircleLoop_ne_center z hr t))
    exact (not_lt_of_ge hlower) (mul_pos hpos hnormpos)
  refine ⟨hgavoid, ?_⟩
  have hindex :
      planarCircleIndex f hf z w r hr hfavoid =
        planarCircleIndex g hg z w r hr hgavoid := by
    apply planarCircleIndex_eq_of_norm_sub_lt
      f g hf hg z w hr hfavoid hgavoid
    intro t
    rw [show
        imageCircleLoop g hg z r t - imageCircleLoop f hf z r t =
          b * starRingEnd ℂ (complexCircleLoop z r t - z) by
      simp only [imageCircleLoop, ContinuousMap.coe_mk, g, f]
      rw [apply_eq_weakDZ_mul_add_weakDBar_mul_conj]
      simp only [a, b]
      ring]
    rw [show imageCircleLoop f hf z r t - w =
        a * (complexCircleLoop z r t - z) by
      simp [imageCircleLoop, f]]
    rw [norm_mul, Complex.norm_conj, norm_mul]
    have hnormpos : 0 < ‖complexCircleLoop z r t - z‖ :=
      norm_pos_iff.mpr
        (sub_ne_zero.mpr (complexCircleLoop_ne_center z hr t))
    exact mul_lt_mul_of_pos_right hba hnormpos
  rw [← hindex]
  unfold planarCircleIndex
  have hnormalized :
      normalizedLoopAround (imageCircleLoop f hf z r) w hfavoid
          (imageCircleLoop_one_eq_zero f hf z r) =
        positiveCircleLoop := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change
      ((f (circlePoint z r t) - w) / (f (circlePoint z r 0) - w)) =
        Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I)
    simp only [f, add_sub_cancel_left, circlePoint_zero]
    rw [circlePoint]
    simp only [add_sub_cancel_left]
    change
      (a * ((r : ℂ) *
          Complex.exp
            (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I))) /
          (a * (r : ℂ)) =
        Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I)
    field_simp [ha, Complex.ofReal_ne_zero.mpr hr.ne']
    congr 1
    push_cast
    ring
  rw [hnormalized, puncturedLoopWindingNumber_positiveCircleLoop]

/--
%%handwave
name:
  Negative-Jacobian affine maps have local index minus one
statement:
  Let $L:\mathbb C\to\mathbb C$ be real linear with $J(L)<0$, and set
  $g(\xi)=w+L(\xi-z)$. For every $r>0$, the loop
  $g|_{\partial B(z,r)}$ avoids $w$ and has winding number $-1$ about $w$.
proof:
  Write $L(\xi)=a\xi+b\overline\xi$. Negativity of the Jacobian gives
  $|a|<|b|$. Thus the restriction of $L$ to every centered circle is closer
  to the conjugate-linear map $\xi\mapsto b\overline\xi$ than that reference
  loop is to zero. The reference loop is the standard negatively oriented
  circle after normalization.
-/
theorem exists_planarCircleIndex_affine_eq_neg_one_of_weakJacobian_neg
    (L : ℂ →L[ℝ] ℂ) (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hJ : weakJacobian L < 0) :
    ∃ havoid : ∀ t,
        imageCircleLoop (fun ξ ↦ w + L (ξ - z))
          (by fun_prop) z r t ≠ w,
      planarCircleIndex (fun ξ ↦ w + L (ξ - z))
        (by fun_prop) z w r hr havoid = -1 := by
  let a : ℂ := weakDZ L
  let b : ℂ := weakDBar L
  let f : ℂ → ℂ :=
    fun ξ ↦ w + b * starRingEnd ℂ (ξ - z)
  let g : ℂ → ℂ := fun ξ ↦ w + L (ξ - z)
  have hf : Continuous f := by fun_prop
  have hg : Continuous g := by fun_prop
  have hab : ‖a‖ < ‖b‖ := by
    simpa [a, b] using
      norm_weakDZ_lt_norm_weakDBar_of_weakJacobian_neg hJ
  have hb : b ≠ 0 := by
    intro hb
    exact (not_lt_of_ge (norm_nonneg a)) (by simpa [hb] using hab)
  have hfavoid : ∀ t, imageCircleLoop f hf z r t ≠ w := by
    intro t ht
    have hzero :
        b * starRingEnd ℂ (complexCircleLoop z r t - z) = 0 := by
      simpa [imageCircleLoop, f] using sub_eq_zero.mpr ht
    have hconj :
        starRingEnd ℂ (complexCircleLoop z r t - z) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hb
    have harg : complexCircleLoop z r t - z = 0 := by
      simpa using congrArg (starRingEnd ℂ) hconj
    exact complexCircleLoop_ne_center z hr t (sub_eq_zero.mp harg)
  have hgavoid : ∀ t, imageCircleLoop g hg z r t ≠ w := by
    intro t ht
    have hzero : L (complexCircleLoop z r t - z) = 0 := by
      simpa [imageCircleLoop, g] using sub_eq_zero.mpr ht
    have hlower :
        (‖b‖ - ‖a‖) * ‖complexCircleLoop z r t - z‖ ≤
          ‖L (complexCircleLoop z r t - z)‖ := by
      simpa [a, b] using
        norm_weakDBar_sub_norm_weakDZ_mul_le L
          (complexCircleLoop z r t - z)
    rw [hzero, norm_zero] at hlower
    have hpos : 0 < ‖b‖ - ‖a‖ := sub_pos.mpr hab
    have hnormpos : 0 < ‖complexCircleLoop z r t - z‖ :=
      norm_pos_iff.mpr
        (sub_ne_zero.mpr (complexCircleLoop_ne_center z hr t))
    exact (not_lt_of_ge hlower) (mul_pos hpos hnormpos)
  refine ⟨hgavoid, ?_⟩
  have hindex :
      planarCircleIndex f hf z w r hr hfavoid =
        planarCircleIndex g hg z w r hr hgavoid := by
    apply planarCircleIndex_eq_of_norm_sub_lt
      f g hf hg z w hr hfavoid hgavoid
    intro t
    rw [show
        imageCircleLoop g hg z r t - imageCircleLoop f hf z r t =
          a * (complexCircleLoop z r t - z) by
      simp only [imageCircleLoop, ContinuousMap.coe_mk, g, f]
      rw [apply_eq_weakDZ_mul_add_weakDBar_mul_conj]
      simp only [a, b]
      ring]
    rw [show imageCircleLoop f hf z r t - w =
        b * starRingEnd ℂ (complexCircleLoop z r t - z) by
      simp [imageCircleLoop, f]]
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hnormpos : 0 < ‖complexCircleLoop z r t - z‖ :=
      norm_pos_iff.mpr
        (sub_ne_zero.mpr (complexCircleLoop_ne_center z hr t))
    exact mul_lt_mul_of_pos_right hab hnormpos
  rw [← hindex]
  unfold planarCircleIndex
  have hnormalized :
      normalizedLoopAround (imageCircleLoop f hf z r) w hfavoid
          (imageCircleLoop_one_eq_zero f hf z r) =
        negativeCircleLoop := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change
      ((f (circlePoint z r t) - w) /
          (f (circlePoint z r 0) - w)) =
        Complex.exp ((-(2 * Real.pi * (t : ℝ))) * Complex.I)
    simp only [f, add_sub_cancel_left, circlePoint_zero]
    rw [circlePoint]
    simp only [add_sub_cancel_left, map_mul, Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show
        (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * -Complex.I) =
          -(((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) by
      ring]
    field_simp [hb, Complex.ofReal_ne_zero.mpr hr.ne']
    congr 1
    push_cast
    ring
  rw [hnormalized, puncturedLoopWindingNumber_negativeCircleLoop]

/--
%%handwave
name:
  Positive-Jacobian regular points have local index one
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and Fréchet differentiable at
  $z$. If $J_f(z)>0$, then there is an $r>0$ such that $z$ is the only point
  of $\overline B(z,r)$ mapped to $f(z)$ and
  $$
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},f(z)\bigr)=1.
  $$
proof:
  The differentiability remainder is $o(|\xi-z|)$. The positive-Jacobian
  derivative has the lower bound
  $(|\partial_zf(z)|-|\partial_{\bar z}f(z)|)|\xi-z|$, with a strictly
  positive coefficient. On a sufficiently small circle the remainder is
  less than half this bound, so the image loop avoids $f(z)$ and is a strict
  relative perturbation of the affine derivative model. [That affine model has winding number one](lean:JJMath.Quasiconformal.exists_planarCircleIndex_affine_eq_one_of_weakJacobian_pos).
-/
theorem HasFDerivAt.exists_planarCircleIndex_eq_one_of_weakJacobian_pos
    {f : ℂ → ℂ} (hf : Continuous f) {L : ℂ →L[ℝ] ℂ} {z : ℂ}
    (hderiv : HasFDerivAt f L z) (hJ : 0 < weakJacobian L) :
    ∃ r : ℝ, ∃ hr : IsFiberIsolatingRadius f z (f z) r,
      planarCircleIndex f hf z (f z) r hr.1
          (imageCircleLoop_ne_of_isFiberIsolatingRadius
            f hf z (f z) hr) =
        1 := by
  let c : ℝ := ‖weakDZ L‖ - ‖weakDBar L‖
  have hc : 0 < c := by
    exact sub_pos.mpr
      (norm_weakDBar_lt_norm_weakDZ_of_weakJacobian_pos hJ)
  have hrem_event : ∀ᶠ x in nhds z,
      ‖f x - f z - L (x - z)‖ ≤ (c / 2) * ‖x - z‖ :=
    hderiv.isLittleO.bound (half_pos hc)
  obtain ⟨ρ, hρ, hrem⟩ :=
    Metric.eventually_nhds_iff.mp hrem_event
  let r : ℝ := ρ / 2
  have hr : 0 < r := half_pos hρ
  let g : ℂ → ℂ := fun x ↦ f z + L (x - z)
  have hg : Continuous g := by fun_prop
  have hstrict (x : ℂ) (hxne : x ≠ z) (hxdist : dist x z < ρ) :
      ‖f x - g x‖ < ‖g x - f z‖ := by
    have hrem_x := hrem hxdist
    rw [show f x - g x = f x - f z - L (x - z) by
      simp [g]
      ring]
    rw [show g x - f z = L (x - z) by simp [g]]
    calc
      ‖f x - f z - L (x - z)‖ ≤
          (c / 2) * ‖x - z‖ := hrem_x
      _ < c * ‖x - z‖ := by
        have hnormpos : 0 < ‖x - z‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr hxne)
        exact mul_lt_mul_of_pos_right (half_lt_self hc) hnormpos
      _ ≤ ‖L (x - z)‖ := by
        simpa [c] using
          norm_weakDZ_sub_norm_weakDBar_mul_le L (x - z)
  have hriso : IsFiberIsolatingRadius f z (f z) r := by
    refine ⟨hr, ?_⟩
    intro x hx hfx
    by_contra hxne
    have hxdist : dist x z < ρ := by
      dsimp [r] at hx
      linarith
    have hlt := hstrict x hxne hxdist
    rw [hfx, norm_sub_rev] at hlt
    exact (lt_irrefl _) hlt
  obtain ⟨hgavoid, hgindex⟩ :=
    exists_planarCircleIndex_affine_eq_one_of_weakJacobian_pos
      L z (f z) hr hJ
  have hclose : ∀ t,
      ‖imageCircleLoop f hf z r t - imageCircleLoop g hg z r t‖ <
        ‖imageCircleLoop g hg z r t - f z‖ := by
    intro t
    have hdist : dist (complexCircleLoop z r t) z < ρ := by
      change dist (circlePoint z r t) z < ρ
      rw [dist_circlePoint_center z hr t]
      dsimp [r]
      linarith
    exact hstrict _ (complexCircleLoop_ne_center z hr t) hdist
  let hfavoid :=
    imageCircleLoop_ne_of_isFiberIsolatingRadius
      f hf z (f z) hriso
  refine ⟨r, hriso, ?_⟩
  have hindex :
      planarCircleIndex g hg z (f z) r hr hgavoid =
        planarCircleIndex f hf z (f z) r hr hfavoid :=
    planarCircleIndex_eq_of_norm_sub_lt
      g f hg hf z (f z) hr hgavoid hfavoid hclose
  calc
    planarCircleIndex f hf z (f z) r hr hfavoid =
        planarCircleIndex g hg z (f z) r hr hgavoid := hindex.symm
    _ = 1 := hgindex

/--
%%handwave
name:
  Negative-Jacobian regular points have local index minus one
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and Fréchet differentiable at
  $z$. If $J_f(z)<0$, then there is an $r>0$ such that $z$ is the only point
  of $\overline B(z,r)$ mapped to $f(z)$ and
  $$
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},f(z)\bigr)=-1.
  $$
proof:
  The differentiability remainder is $o(|\xi-z|)$. The negative-Jacobian
  derivative has lower bound
  $(|\partial_{\bar z}f(z)|-|\partial_zf(z)|)|\xi-z|$, with a strictly
  positive coefficient. On a sufficiently small disk the map is a strict
  relative perturbation of its affine derivative model. [That affine model has winding number minus one](lean:JJMath.Quasiconformal.exists_planarCircleIndex_affine_eq_neg_one_of_weakJacobian_neg).
-/
theorem HasFDerivAt.exists_planarCircleIndex_eq_neg_one_of_weakJacobian_neg
    {f : ℂ → ℂ} (hf : Continuous f) {L : ℂ →L[ℝ] ℂ} {z : ℂ}
    (hderiv : HasFDerivAt f L z) (hJ : weakJacobian L < 0) :
    ∃ r : ℝ, ∃ hr : IsFiberIsolatingRadius f z (f z) r,
      planarCircleIndex f hf z (f z) r hr.1
          (imageCircleLoop_ne_of_isFiberIsolatingRadius
            f hf z (f z) hr) =
        -1 := by
  let c : ℝ := ‖weakDBar L‖ - ‖weakDZ L‖
  have hc : 0 < c := by
    exact sub_pos.mpr
      (norm_weakDZ_lt_norm_weakDBar_of_weakJacobian_neg hJ)
  have hrem_event : ∀ᶠ x in nhds z,
      ‖f x - f z - L (x - z)‖ ≤ (c / 2) * ‖x - z‖ :=
    hderiv.isLittleO.bound (half_pos hc)
  obtain ⟨ρ, hρ, hrem⟩ :=
    Metric.eventually_nhds_iff.mp hrem_event
  let r : ℝ := ρ / 2
  have hr : 0 < r := half_pos hρ
  let g : ℂ → ℂ := fun x ↦ f z + L (x - z)
  have hg : Continuous g := by fun_prop
  have hstrict (x : ℂ) (hxne : x ≠ z) (hxdist : dist x z < ρ) :
      ‖f x - g x‖ < ‖g x - f z‖ := by
    have hrem_x := hrem hxdist
    rw [show f x - g x = f x - f z - L (x - z) by
      simp [g]
      ring]
    rw [show g x - f z = L (x - z) by simp [g]]
    calc
      ‖f x - f z - L (x - z)‖ ≤
          (c / 2) * ‖x - z‖ := hrem_x
      _ < c * ‖x - z‖ := by
        have hnormpos : 0 < ‖x - z‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr hxne)
        exact mul_lt_mul_of_pos_right (half_lt_self hc) hnormpos
      _ ≤ ‖L (x - z)‖ := by
        simpa [c] using
          norm_weakDBar_sub_norm_weakDZ_mul_le L (x - z)
  have hriso : IsFiberIsolatingRadius f z (f z) r := by
    refine ⟨hr, ?_⟩
    intro x hx hfx
    by_contra hxne
    have hxdist : dist x z < ρ := by
      dsimp [r] at hx
      linarith
    have hlt := hstrict x hxne hxdist
    rw [hfx, norm_sub_rev] at hlt
    exact (lt_irrefl _) hlt
  obtain ⟨hgavoid, hgindex⟩ :=
    exists_planarCircleIndex_affine_eq_neg_one_of_weakJacobian_neg
      L z (f z) hr hJ
  have hclose : ∀ t,
      ‖imageCircleLoop f hf z r t - imageCircleLoop g hg z r t‖ <
        ‖imageCircleLoop g hg z r t - f z‖ := by
    intro t
    have hdist : dist (complexCircleLoop z r t) z < ρ := by
      change dist (circlePoint z r t) z < ρ
      rw [dist_circlePoint_center z hr t]
      dsimp [r]
      linarith
    exact hstrict _ (complexCircleLoop_ne_center z hr t) hdist
  let hfavoid :=
    imageCircleLoop_ne_of_isFiberIsolatingRadius
      f hf z (f z) hriso
  refine ⟨r, hriso, ?_⟩
  have hindex :
      planarCircleIndex g hg z (f z) r hr hgavoid =
        planarCircleIndex f hf z (f z) r hr hfavoid :=
    planarCircleIndex_eq_of_norm_sub_lt
      g f hg hf z (f z) hr hgavoid hfavoid hclose
  calc
    planarCircleIndex f hf z (f z) r hr hfavoid =
        planarCircleIndex g hg z (f z) r hr hgavoid := hindex.symm
    _ = -1 := hgindex

/--
%%handwave
name:
  Local index at a positive regular point
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, suppose the fiber
  $f^{-1}(f(z))$ is discrete, and suppose $f$ is Fréchet differentiable at
  $z$ with $J_f(z)>0$. Then
  $$
    i(f,z;f(z))=1.
  $$
proof:
  [A sufficiently small fiber-isolating circle has index one](lean:JJMath.Quasiconformal.HasFDerivAt.exists_planarCircleIndex_eq_one_of_weakJacobian_pos), and the circle definition of local index is independent of the chosen isolating radius.
-/
theorem planarLocalIndex_eq_one_of_hasFDerivAt_of_weakJacobian_pos
    {f : ℂ → ℂ} (hf : Continuous f) {L : ℂ →L[ℝ] ℂ} {z : ℂ}
    (hderiv : HasFDerivAt f L z) (hJ : 0 < weakJacobian L)
    (hdiscrete : IsDiscrete {x : ℂ | f x = f z}) :
    planarLocalIndex f hf z (f z) rfl hdiscrete = 1 := by
  obtain ⟨r, hriso, hindex⟩ :=
    HasFDerivAt.exists_planarCircleIndex_eq_one_of_weakJacobian_pos
      hf hderiv hJ
  rw [planarLocalIndex_eq_planarCircleIndex
    f hf z (f z) rfl hdiscrete hriso]
  exact hindex

/--
%%handwave
name:
  Local index at a negative regular point
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, suppose the fiber
  $f^{-1}(f(z))$ is discrete, and suppose $f$ is Fréchet differentiable at
  $z$ with $J_f(z)<0$. Then
  $$
    i(f,z;f(z))=-1.
  $$
proof:
  [A sufficiently small fiber-isolating circle has index minus one](lean:JJMath.Quasiconformal.HasFDerivAt.exists_planarCircleIndex_eq_neg_one_of_weakJacobian_neg), and the circle definition of local index is independent of the chosen isolating radius.
-/
theorem planarLocalIndex_eq_neg_one_of_hasFDerivAt_of_weakJacobian_neg
    {f : ℂ → ℂ} (hf : Continuous f) {L : ℂ →L[ℝ] ℂ} {z : ℂ}
    (hderiv : HasFDerivAt f L z) (hJ : weakJacobian L < 0)
    (hdiscrete : IsDiscrete {x : ℂ | f x = f z}) :
    planarLocalIndex f hf z (f z) rfl hdiscrete = -1 := by
  obtain ⟨r, hriso, hindex⟩ :=
    HasFDerivAt.exists_planarCircleIndex_eq_neg_one_of_weakJacobian_neg
      hf hderiv hJ
  rw [planarLocalIndex_eq_planarCircleIndex
    f hf z (f z) rfl hdiscrete hriso]
  exact hindex

/--
%%handwave
name:
  Regular fibers are discrete
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and let $w\in\mathbb C$.
  Suppose that at every $z\in f^{-1}(w)$ the map $f$ is Fréchet
  differentiable and $J_f(z)\ne0$. Then the fiber $f^{-1}(w)$ is discrete.
proof:
  At a regular point the Jacobian is either positive or negative.
  [The positive case](lean:JJMath.Quasiconformal.HasFDerivAt.exists_planarCircleIndex_eq_one_of_weakJacobian_pos) and [the negative case](lean:JJMath.Quasiconformal.HasFDerivAt.exists_planarCircleIndex_eq_neg_one_of_weakJacobian_neg) both provide a fiber-isolating disk. Its open interior meets the fiber only at its center.
-/
theorem isDiscrete_fiber_of_forall_hasFDerivAt_of_weakJacobian_ne_zero
    {f : ℂ → ℂ} (hf : Continuous f) {w : ℂ}
    (hregular : ∀ z, f z = w →
      ∃ L : ℂ →L[ℝ] ℂ,
        HasFDerivAt f L z ∧ weakJacobian L ≠ 0) :
    IsDiscrete {z : ℂ | f z = w} := by
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro z hz
  have hz' : f z = w := hz
  obtain ⟨L, hderiv, hJ⟩ := hregular z hz'
  obtain hJneg | hJpos := lt_or_gt_of_ne hJ
  · obtain ⟨r, hriso, _hindex⟩ :=
      HasFDerivAt.exists_planarCircleIndex_eq_neg_one_of_weakJacobian_neg
        hf hderiv hJneg
    refine ⟨Metric.ball z r, Metric.isOpen_ball, Set.ext ?_⟩
    intro x
    constructor
    · rintro ⟨hxball, hxfiber⟩
      have hxfiber' : f x = f z := hxfiber.trans hz'.symm
      have hxz :=
        hriso.2 x (Metric.mem_ball.mp hxball).le hxfiber'
      simp [hxz]
    · intro hx
      have hxz : x = z := by simpa using hx
      subst x
      exact ⟨Metric.mem_ball_self hriso.1, hz⟩
  · obtain ⟨r, hriso, _hindex⟩ :=
      HasFDerivAt.exists_planarCircleIndex_eq_one_of_weakJacobian_pos
        hf hderiv hJpos
    refine ⟨Metric.ball z r, Metric.isOpen_ball, Set.ext ?_⟩
    intro x
    constructor
    · rintro ⟨hxball, hxfiber⟩
      have hxfiber' : f x = f z := hxfiber.trans hz'.symm
      have hxz :=
        hriso.2 x (Metric.mem_ball.mp hxball).le hxfiber'
      simp [hxz]
    · intro hx
      have hxz : x = z := by simpa using hx
      subst x
      exact ⟨Metric.mem_ball_self hriso.1, hz⟩

/--
%%handwave
name:
  Regular fibers are locally finite
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and let $w\in\mathbb C$.
  Suppose that at every point of $f^{-1}(w)$ the map is Fréchet
  differentiable with nonzero Jacobian. Then the intersection of
  $f^{-1}(w)$ with every closed disk is finite.
proof:
  [The regular fiber is discrete](lean:JJMath.Quasiconformal.isDiscrete_fiber_of_forall_hasFDerivAt_of_weakJacobian_ne_zero). Continuity makes it closed, so its intersection with a compact closed disk is compact and discrete, hence finite.
-/
theorem finite_closedBall_inter_fiber_of_forall_hasFDerivAt_of_weakJacobian_ne_zero
    {f : ℂ → ℂ} (hf : Continuous f) {w c : ℂ} {r : ℝ}
    (hregular : ∀ z, f z = w →
      ∃ L : ℂ →L[ℝ] ℂ,
        HasFDerivAt f L z ∧ weakJacobian L ≠ 0) :
    (Metric.closedBall c r ∩ {z : ℂ | f z = w}).Finite := by
  have hdiscrete : IsDiscrete {z : ℂ | f z = w} :=
    isDiscrete_fiber_of_forall_hasFDerivAt_of_weakJacobian_ne_zero
      hf hregular
  have hclosed : IsClosed {z : ℂ | f z = w} := by
    change IsClosed (f ⁻¹' {w})
    exact isClosed_singleton.preimage hf
  exact ((isCompact_closedBall c r).inter_right hclosed).finite
    (hdiscrete.mono inter_subset_right)

/--
%%handwave
name:
  Pairwise isolating disks for the fiber inside a disk
statement:
  Let $f^{-1}(w)$ be discrete. For every point
  $x\in f^{-1}(w)\cap B(z,r)$ one can choose a radius $\rho_x>0$ such that
  $\overline B(x,\rho_x)$ isolates $x$ in the full fiber, these closed disks
  are pairwise disjoint, and every one of them is contained in $B(z,r)$.
proof:
  Choose an isolating radius at each fiber point and shrink it to one third
  of the minimum of that radius and the distance to the outer boundary.
  Isolation bounds the radii for two distinct centers by their mutual
  distance, while the boundary-distance bound keeps every closed disk inside
  the outer disk.
-/
theorem exists_pairwiseDisjoint_isolatingRadii_of_fiber_inter_ball
    (f : ℂ → ℂ) (z w : ℂ) {r : ℝ}
    (hdiscrete : IsDiscrete {x : ℂ | f x = w}) :
    ∃ ρ : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w} → ℝ,
      (∀ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
        IsFiberIsolatingRadius f x w (ρ x)) ∧
      (∀ x y : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
        x ≠ y →
          Disjoint (Metric.closedBall (x : ℂ) (ρ x))
            (Metric.closedBall (y : ℂ) (ρ y))) ∧
      (∀ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
        Metric.closedBall (x : ℂ) (ρ x) ⊆ Metric.ball z r) := by
  have hex (x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w}) :
      ∃ s : ℝ, IsFiberIsolatingRadius f x w s :=
    exists_isFiberIsolatingRadius_of_isDiscrete_fiber
      f x w x.2.2 hdiscrete
  choose s hs using hex
  let ρ :
      {x : ℂ // x ∈ Metric.ball z r ∧ f x = w} → ℝ :=
    fun x ↦ min (s x) (r - dist (x : ℂ) z) / 3
  have hmargin
      (x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w}) :
      0 < r - dist (x : ℂ) z := by
    have hx := Metric.mem_ball.mp x.2.1
    linarith
  have hρpos
      (x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w}) :
      0 < ρ x := by
    have hmin : 0 < min (s x) (r - dist (x : ℂ) z) :=
      lt_min (hs x).1 (hmargin x)
    dsimp [ρ]
    positivity
  have hρle_s
      (x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w}) :
      ρ x ≤ s x := by
    have hmin := min_le_left (s x) (r - dist (x : ℂ) z)
    dsimp [ρ]
    nlinarith [(hs x).1, hmargin x]
  have hρle_margin_third
      (x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w}) :
      ρ x ≤ (r - dist (x : ℂ) z) / 3 :=
    div_le_div_of_nonneg_right
      (min_le_right (s x) (r - dist (x : ℂ) z)) (by norm_num)
  refine
    ⟨ρ, fun x ↦ (hs x).mono (hρpos x) (hρle_s x), ?_, ?_⟩
  · intro x y hxy
    have hsx_lt : s x < dist (y : ℂ) x := by
      by_contra h
      have hyx : (y : ℂ) = x :=
        (hs x).2 y (le_of_not_gt h) y.2.2
      exact hxy (Subtype.ext hyx).symm
    have hsy_lt : s y < dist (x : ℂ) y := by
      by_contra h
      have hxy' : (x : ℂ) = y :=
        (hs y).2 x (le_of_not_gt h) x.2.2
      exact hxy (Subtype.ext hxy')
    apply Metric.closedBall_disjoint_closedBall
    have hxthird : ρ x ≤ s x / 3 :=
      div_le_div_of_nonneg_right
        (min_le_left (s x) (r - dist (x : ℂ) z)) (by norm_num)
    have hythird : ρ y ≤ s y / 3 :=
      div_le_div_of_nonneg_right
        (min_le_left (s y) (r - dist (y : ℂ) z)) (by norm_num)
    rw [dist_comm (y : ℂ) x] at hsx_lt
    nlinarith [dist_pos.mpr (Subtype.coe_ne_coe.mpr hxy)]
  · intro x q hq
    rw [Metric.mem_ball]
    have hqx : dist q (x : ℂ) ≤ ρ x := by
      simpa [Metric.mem_closedBall] using hq
    have htriangle :
        dist q z ≤ dist q (x : ℂ) + dist (x : ℂ) z :=
      dist_triangle _ _ _
    have hρmargin : ρ x < r - dist (x : ℂ) z := by
      nlinarith [hρle_margin_third x, hmargin x]
    linarith

/--
%%handwave
name:
  Disk boundary degree is the sum of interior local indices
statement:
  Let $f:\mathbb C\to\mathbb C$ be smooth, let $r>0$, and suppose
  $f(\partial B(z,r))$ avoids $w$. If $f^{-1}(w)$ is discrete and its
  intersection with $B(z,r)$ is finite, then
  $$
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)
      =
    \sum_{\substack{x\in B(z,r)\\f(x)=w}} i(f,x;w).
  $$
proof:
  [Choose pairwise disjoint fiber-isolating disks around the interior preimages](lean:JJMath.Quasiconformal.exists_pairwiseDisjoint_isolatingRadii_of_fiber_inter_ball). The map avoids $w$ on the complementary perforated disk. Smooth boundary additivity expresses the outer index as the sum of the inner circle indices, and radius independence identifies each inner circle index with the corresponding local index.
-/
theorem planarCircleIndex_eq_finsum_localIndex_fiber_inter_ball
    (f : ℂ → ℂ) (hfdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (houter : ∀ t, imageCircleLoop f hfdiff.continuous z r t ≠ w)
    (hdiscrete : IsDiscrete {x : ℂ | f x = w})
    (hfinite :
      {x : ℂ | x ∈ Metric.ball z r ∧ f x = w}.Finite) :
    planarCircleIndex f hfdiff.continuous z w r hr houter =
      ∑ᶠ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
        planarLocalIndex f hfdiff.continuous x w x.2.2 hdiscrete := by
  letI : Fintype {x : ℂ // x ∈ Metric.ball z r ∧ f x = w} :=
    hfinite.fintype
  obtain ⟨ρ, hρiso, hpair, hinside⟩ :=
    exists_pairwiseDisjoint_isolatingRadii_of_fiber_inter_ball
      f z w hdiscrete
  let c :
      {x : ℂ // x ∈ Metric.ball z r ∧ f x = w} → ℂ :=
    fun x ↦ x
  have hρpos
      (x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w}) :
      0 < ρ x :=
    (hρiso x).1
  have hfavoid (q : ℂ)
      (hq : q ∈ perforatedClosedDisk z r c ρ) :
      f q ≠ w := by
    intro hqw
    have hqball : q ∈ Metric.ball z r := by
      rw [Metric.mem_ball]
      have hqle : dist q z ≤ r :=
        Metric.mem_closedBall.mp hq.1
      apply lt_of_le_of_ne hqle
      intro hqeq
      obtain ⟨t, ht⟩ :=
        exists_circlePoint_eq_of_dist_eq z q hr hqeq
      apply houter t
      have ht' : f (circlePoint z r t) = w := by
        rw [ht]
        exact hqw
      simpa [imageCircleLoop] using ht'
    let x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w} :=
      ⟨q, hqball, hqw⟩
    have hqinner : q ∈ Metric.ball (c x) (ρ x) := by
      rw [Metric.mem_ball]
      simpa [c, x] using hρpos x
    exact hq.2 (Set.mem_iUnion.mpr ⟨x, hqinner⟩)
  let houterP :=
    imageCircleLoop_ne_of_avoids_perforatedClosedDisk_outer
      f hfdiff.continuous z w hr c ρ hinside hfavoid
  let hinner
      (x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w}) :=
    imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
      f hfdiff.continuous z w r c ρ hρpos hpair hinside hfavoid x
  have hadd :
      planarCircleIndex f hfdiff.continuous z w r hr houterP =
        ∑ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
          planarCircleIndex f hfdiff.continuous (c x) w (ρ x)
            (hρpos x) (hinner x) := by
    simpa [houterP, hinner] using
      planarCircleIndex_eq_sum_of_contDiff_of_avoids_perforatedClosedDisk
        f hfdiff z w hr c ρ hρpos hpair hinside hfavoid
  have hinnerLocal
      (x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w}) :
      planarCircleIndex f hfdiff.continuous (c x) w (ρ x)
          (hρpos x) (hinner x) =
        planarLocalIndex f hfdiff.continuous x w x.2.2
          hdiscrete := by
    have hlocalCircle :=
      planarLocalIndex_eq_planarCircleIndex
        f hfdiff.continuous x w x.2.2 hdiscrete (hρiso x)
    simpa [c] using hlocalCircle.symm
  calc
    planarCircleIndex f hfdiff.continuous z w r hr houter =
        planarCircleIndex f hfdiff.continuous z w r hr houterP := by
      congr
    _ = ∑ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
          planarCircleIndex f hfdiff.continuous (c x) w (ρ x)
            (hρpos x) (hinner x) := hadd
    _ = ∑ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
          planarLocalIndex f hfdiff.continuous x w x.2.2
            hdiscrete := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hinnerLocal x
    _ = ∑ᶠ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
          planarLocalIndex f hfdiff.continuous x w x.2.2
            hdiscrete := by
      rw [finsum_eq_sum_of_fintype]

/--
%%handwave
name:
  Boundary degree is the signed count of regular preimages
statement:
  Let $f:\mathbb C\to\mathbb C$ be smooth, let $r>0$, and suppose
  $f(\partial B(z,r))$ avoids the regular value $w$. Then
  $$
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)
      =
    \sum_{\substack{x\in B(z,r)\\f(x)=w}}
      \operatorname{sgn}J_f(x).
  $$
proof:
  [The boundary degree is the sum of the local indices of the interior fiber](lean:JJMath.Quasiconformal.planarCircleIndex_eq_finsum_localIndex_fiber_inter_ball). At a regular point the Jacobian is either positive or negative; [the corresponding local index is $1$](lean:JJMath.Quasiconformal.planarLocalIndex_eq_one_of_hasFDerivAt_of_weakJacobian_pos) in the first case and [$-1$](lean:JJMath.Quasiconformal.planarLocalIndex_eq_neg_one_of_hasFDerivAt_of_weakJacobian_neg) in the second.
-/
theorem planarCircleIndex_eq_finsum_jacobianSign_fiber_inter_ball_of_regular
    (f : ℂ → ℂ) (hfdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (houter : ∀ t, imageCircleLoop f hfdiff.continuous z r t ≠ w)
    (hregular : ∀ x, f x = w →
      weakJacobian (fderiv ℝ f x) ≠ 0) :
    planarCircleIndex f hfdiff.continuous z w r hr houter =
      ∑ᶠ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = w},
        if 0 < weakJacobian (fderiv ℝ f x) then (1 : ℤ) else -1 := by
  have hdiff : Differentiable ℝ f :=
    hfdiff.differentiable (by simp)
  have hregular' : ∀ x, f x = w →
      ∃ L : ℂ →L[ℝ] ℂ,
        HasFDerivAt f L x ∧ weakJacobian L ≠ 0 := by
    intro x hx
    exact
      ⟨fderiv ℝ f x, hdiff.differentiableAt.hasFDerivAt,
        hregular x hx⟩
  have hdiscrete : IsDiscrete {x : ℂ | f x = w} :=
    isDiscrete_fiber_of_forall_hasFDerivAt_of_weakJacobian_ne_zero
      hfdiff.continuous hregular'
  have hfiniteClosed :
      (Metric.closedBall z r ∩ {x : ℂ | f x = w}).Finite :=
    finite_closedBall_inter_fiber_of_forall_hasFDerivAt_of_weakJacobian_ne_zero
      hfdiff.continuous hregular'
  have hfinite :
      {x : ℂ | x ∈ Metric.ball z r ∧ f x = w}.Finite := by
    apply hfiniteClosed.subset
    intro x hx
    exact ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩
  have hsum :=
    planarCircleIndex_eq_finsum_localIndex_fiber_inter_ball
      f hfdiff z w hr houter hdiscrete hfinite
  rw [hsum]
  apply finsum_congr
  intro x
  have hdiscrete_x : IsDiscrete {y : ℂ | f y = f x} := by
    simpa [x.2.2] using hdiscrete
  by_cases hJpos : 0 < weakJacobian (fderiv ℝ f x)
  · simp only [hJpos, ↓reduceIte]
    simpa [x.2.2] using
      planarLocalIndex_eq_one_of_hasFDerivAt_of_weakJacobian_pos
        hfdiff.continuous hdiff.differentiableAt.hasFDerivAt
          hJpos hdiscrete_x
  · have hJneg : weakJacobian (fderiv ℝ f x) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hJpos) (hregular x x.2.2)
    simp only [hJpos, ↓reduceIte]
    simpa [x.2.2] using
      planarLocalIndex_eq_neg_one_of_hasFDerivAt_of_weakJacobian_neg
        hfdiff.continuous hdiff.differentiableAt.hasFDerivAt
          hJneg hdiscrete_x

/--
%%handwave
name:
  Almost every target is a regular value of a smooth planar map
statement:
  If $f:\mathbb C\to\mathbb C$ is smooth, then for almost every
  $y\in\mathbb C$, every $x\in f^{-1}(y)$ satisfies $J_f(x)\neq0$.
proof:
  The image of the zero-Jacobian locus is null by the fixed-dimensional
  Sard theorem. Every target outside that image is a regular value.
-/
theorem eventually_forall_weakJacobian_fderiv_ne_zero_of_contDiff
    (f : ℂ → ℂ) (hfdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ∀ᵐ y ∂volume,
      ∀ x, f x = y →
        weakJacobian (fderiv ℝ f x) ≠ 0 := by
  let Z : Set ℂ :=
    {x | weakJacobian (fderiv ℝ f x) = 0}
  have hdiff : Differentiable ℝ f :=
    hfdiff.differentiable (by simp)
  have hcritical : volume (f '' Z) = 0 := by
    apply
      MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
        (μ := volume)
    · intro x _hx
      exact hdiff.differentiableAt.hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      simpa [weakJacobian] using hx
  filter_upwards [compl_mem_ae_iff.mpr hcritical] with y hy
  intro x hxy hxJ
  exact hy ⟨x, hxJ, hxy⟩

/--
%%handwave
name:
  Disk degree is almost everywhere the signed regular-fiber count
statement:
  Let $f:\mathbb C\to\mathbb C$ be smooth and let $r,\varepsilon>0$.
  Suppose every point of the boundary image
  $f(\partial B(z,r))$ has distance at least $\varepsilon$ from $w$.
  Then, for almost every $y\in B(w,\varepsilon)$,
  $$
    \deg(f,B(z,r),y)
      =
    \sum_{\substack{x\in B(z,r)\\f(x)=y}}
      \operatorname{sgn}J_f(x).
  $$
proof:
  Sard's theorem makes the image of the zero-Jacobian locus null. Every
  target in the protected ball avoids the boundary image, and outside that
  null critical-value set [the boundary degree is the signed count of its regular preimages](lean:JJMath.Quasiconformal.planarCircleIndex_eq_finsum_jacobianSign_fiber_inter_ball_of_regular).
-/
theorem eventually_planarDiskDegree_eq_finsum_jacobianSign_fiber_inter_ball
    (f : ℂ → ℂ) (hfdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z w : ℂ) {r ε : ℝ} (hr : 0 < r) (_hε : 0 < ε)
    (hsep : ∀ t, ε ≤
      ‖imageCircleLoop f hfdiff.continuous z r t - w‖) :
    ∀ᵐ y ∂volume.restrict (Metric.ball w ε),
      planarDiskDegree f hfdiff.continuous z r hr y =
        ∑ᶠ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = y},
          if 0 < weakJacobian (fderiv ℝ f x) then (1 : ℤ) else -1 := by
  have hregular_ae : ∀ᵐ y ∂volume,
      ∀ x, f x = y →
        weakJacobian (fderiv ℝ f x) ≠ 0 :=
    eventually_forall_weakJacobian_fderiv_ne_zero_of_contDiff f hfdiff
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet),
    ae_restrict_of_ae hregular_ae] with y hyball hyregular
  have hyavoid :
      ∀ t, imageCircleLoop f hfdiff.continuous z r t ≠ y := by
    intro t ht
    have hylt : ‖y - w‖ < ε := by
      simpa [Complex.dist_eq] using Metric.mem_ball.mp hyball
    have hyle :
        ε ≤ ‖imageCircleLoop f hfdiff.continuous z r t - w‖ :=
      hsep t
    rw [ht] at hyle
    exact (not_le_of_gt hylt) hyle
  rw [planarDiskDegree_eq_planarCircleIndex
    f hfdiff.continuous z y hr hyavoid]
  exact
    planarCircleIndex_eq_finsum_jacobianSign_fiber_inter_ball_of_regular
      f hfdiff z y hr hyavoid hyregular

/--
%%handwave
name:
  Signed regular-fiber count as a difference of multiplicities
statement:
  Let $f:\mathbb C\to\mathbb C$ be smooth, let $r>0$, and suppose $y$ is a
  regular value. Then
  $$
    \sum_{\substack{x\in B(z,r)\\f(x)=y}}\operatorname{sgn}J_f(x)
      =
    N\bigl(f,B(z,r)\cap\{J_f>0\},y\bigr)
      -
    N\bigl(f,B(z,r)\cap\{J_f<0\},y\bigr).
  $$
  The multiplicities on the right are finite and are viewed as real
  numbers.
proof:
  The regular fiber is discrete, hence finite in the closed disk. Partition
  its interior points into the positive- and negative-Jacobian subsets.
  The two subset cardinalities are exactly the corresponding preimage
  multiplicities, while summing the signs gives their difference.
-/
theorem coe_finsum_jacobianSign_eq_preimageMultiplicity_pos_sub_neg_of_regular
    (f : ℂ → ℂ) (hfdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z y : ℂ) {r : ℝ} (_hr : 0 < r)
    (hregular : ∀ x, f x = y →
      weakJacobian (fderiv ℝ f x) ≠ 0) :
    ((∑ᶠ x : {x : ℂ // x ∈ Metric.ball z r ∧ f x = y},
        if 0 < weakJacobian (fderiv ℝ f x) then (1 : ℤ) else -1 : ℤ) : ℝ) =
      (preimageMultiplicity f
        (Metric.ball z r ∩
          {x | 0 < weakJacobian (fderiv ℝ f x)}) y).toReal -
      (preimageMultiplicity f
        (Metric.ball z r ∩
          {x | weakJacobian (fderiv ℝ f x) < 0}) y).toReal := by
  classical
  let X : Type :=
    {x : ℂ // x ∈ Metric.ball z r ∧ f x = y}
  let P : Set ℂ :=
    Metric.ball z r ∩
      {x | 0 < weakJacobian (fderiv ℝ f x)}
  let N : Set ℂ :=
    Metric.ball z r ∩
      {x | weakJacobian (fderiv ℝ f x) < 0}
  have hdiff : Differentiable ℝ f :=
    hfdiff.differentiable (by simp)
  have hregular' : ∀ x, f x = y →
      ∃ L : ℂ →L[ℝ] ℂ,
        HasFDerivAt f L x ∧ weakJacobian L ≠ 0 := by
    intro x hx
    exact
      ⟨fderiv ℝ f x, hdiff.differentiableAt.hasFDerivAt,
        hregular x hx⟩
  have hfiniteClosed :
      (Metric.closedBall z r ∩ {x : ℂ | f x = y}).Finite :=
    finite_closedBall_inter_fiber_of_forall_hasFDerivAt_of_weakJacobian_ne_zero
      hfdiff.continuous hregular'
  have hfiniteX :
      {x : ℂ | x ∈ Metric.ball z r ∧ f x = y}.Finite := by
    apply hfiniteClosed.subset
    intro x hx
    exact ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩
  letI : Fintype X := hfiniteX.fintype
  have hfiniteP :
      (P ∩ f ⁻¹' {y}).Finite := by
    apply hfiniteX.subset
    intro x hx
    exact ⟨hx.1.1, by simpa using hx.2⟩
  have hfiniteN :
      (N ∩ f ⁻¹' {y}).Finite := by
    apply hfiniteX.subset
    intro x hx
    exact ⟨hx.1.1, by simpa using hx.2⟩
  letI : Fintype {x : ℂ // x ∈ P ∩ f ⁻¹' {y}} :=
    hfiniteP.fintype
  letI : Fintype {x : ℂ // x ∈ N ∩ f ⁻¹' {y}} :=
    hfiniteN.fintype
  let p : X → Prop :=
    fun x ↦ 0 < weakJacobian (fderiv ℝ f x)
  let eP :
      {x : X // p x} ≃
        {x : ℂ // x ∈ P ∩ f ⁻¹' {y}} :=
    { toFun := fun x ↦
        ⟨x.1, ⟨⟨x.1.2.1, x.2⟩, by simpa using x.1.2.2⟩⟩
      invFun := fun x ↦
        ⟨⟨x.1, x.2.1.1, by simpa using x.2.2⟩, x.2.1.2⟩
      left_inv := fun x ↦ by ext; rfl
      right_inv := fun x ↦ by ext; rfl }
  let eN :
      {x : X // ¬ p x} ≃
        {x : ℂ // x ∈ N ∩ f ⁻¹' {y}} :=
    { toFun := fun x ↦
        ⟨x.1, ⟨⟨x.1.2.1,
          lt_of_le_of_ne (le_of_not_gt x.2)
            (hregular x.1 x.1.2.2)⟩, by simpa using x.1.2.2⟩⟩
      invFun := fun x ↦
        ⟨⟨x.1, x.2.1.1, by simpa using x.2.2⟩,
          not_lt.mpr (le_of_lt x.2.1.2)⟩
      left_inv := fun x ↦ by ext; rfl
      right_inv := fun x ↦ by ext; rfl }
  have hPcard :
      (preimageMultiplicity f P y).toReal =
        ((Finset.univ.filter p).card : ℝ) := by
    rw [preimageMultiplicity, Set.encard_eq_coe_toFinset_card,
      Set.toFinset_card, Fintype.card_congr eP.symm]
    rw [Fintype.card_subtype p]
    simp
  have hNcard :
      (preimageMultiplicity f N y).toReal =
        ((Finset.univ.filter (fun x ↦ ¬ p x)).card : ℝ) := by
    rw [preimageMultiplicity, Set.encard_eq_coe_toFinset_card,
      Set.toFinset_card, Fintype.card_congr eN.symm]
    rw [Fintype.card_subtype (fun x : X ↦ ¬ p x)]
    simp
  change
    ((∑ᶠ x : X, if p x then (1 : ℤ) else -1 : ℤ) : ℝ) =
      (preimageMultiplicity f P y).toReal -
        (preimageMultiplicity f N y).toReal
  rw [finsum_eq_sum_of_fintype, hPcard, hNcard]
  have hsumInt :
      (∑ x : X, if p x then (1 : ℤ) else -1) =
        ((Finset.univ.filter p).card : ℤ) -
          ((Finset.univ.filter (fun x ↦ ¬ p x)).card : ℤ) := by
    calc
      (∑ x : X, if p x then (1 : ℤ) else -1) =
          ∑ x : X, ((if p x then (1 : ℤ) else 0) -
            (if ¬ p x then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        split_ifs <;> simp_all
      _ = (∑ x : X, if p x then (1 : ℤ) else 0) -
          ∑ x : X, if ¬ p x then (1 : ℤ) else 0 := by
        rw [Finset.sum_sub_distrib]
      _ = ((Finset.univ.filter p).card : ℤ) -
          ((Finset.univ.filter (fun x ↦ ¬ p x)).card : ℤ) := by
        congr 1
        · rw [← Finset.sum_filter]
          simp
        · rw [← Finset.sum_filter]
          simp
  exact_mod_cast hsumInt

/--
%%handwave
name:
  Disk degree is almost everywhere the difference of signed-sheet multiplicities
statement:
  Let $f:\mathbb C\to\mathbb C$ be smooth and suppose the boundary image
  $f(\partial B(z,r))$ stays at distance at least $\varepsilon>0$ from $w$.
  For almost every $y\in B(w,\varepsilon)$,
  $$
    \deg(f,B(z,r),y)
      =
    N\bigl(f,B(z,r)\cap\{J_f>0\},y\bigr)
      -
    N\bigl(f,B(z,r)\cap\{J_f<0\},y\bigr).
  $$
proof:
  Almost every target is a regular value. For such a target, [disk degree is the signed regular-fiber count](lean:JJMath.Quasiconformal.eventually_planarDiskDegree_eq_finsum_jacobianSign_fiber_inter_ball), and [that signed count is the positive-sheet multiplicity minus the negative-sheet multiplicity](lean:JJMath.Quasiconformal.coe_finsum_jacobianSign_eq_preimageMultiplicity_pos_sub_neg_of_regular).
-/
theorem eventually_coe_planarDiskDegree_eq_preimageMultiplicity_pos_sub_neg
    (f : ℂ → ℂ) (hfdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hsep : ∀ t, ε ≤
      ‖imageCircleLoop f hfdiff.continuous z r t - w‖) :
    ∀ᵐ y ∂volume.restrict (Metric.ball w ε),
      (planarDiskDegree f hfdiff.continuous z r hr y : ℝ) =
        (preimageMultiplicity f
          (Metric.ball z r ∩
            {x | 0 < weakJacobian (fderiv ℝ f x)}) y).toReal -
        (preimageMultiplicity f
          (Metric.ball z r ∩
            {x | weakJacobian (fderiv ℝ f x) < 0}) y).toReal := by
  have hsigned :=
    eventually_planarDiskDegree_eq_finsum_jacobianSign_fiber_inter_ball
      f hfdiff z w hr hε hsep
  have hregular :=
    ae_restrict_of_ae (s := Metric.ball w ε)
      (eventually_forall_weakJacobian_fderiv_ne_zero_of_contDiff f hfdiff)
  filter_upwards [hsigned, hregular] with y hsigned_y hregular_y
  rw [hsigned_y]
  exact
    coe_finsum_jacobianSign_eq_preimageMultiplicity_pos_sub_neg_of_regular
      f hfdiff z y hr hregular_y

/--
%%handwave
name:
  Compact subsets of an open ball lie in a smaller ball
statement:
  If $K\subset B(w,\varepsilon)$ is compact and $\varepsilon>0$, then there
  is $\varepsilon'$ with
  $$
    0<\varepsilon'<\varepsilon,
    \qquad
    K\subset B(w,\varepsilon').
  $$
proof:
  If $K$ is nonempty, the distance to $w$ attains a maximum $M<\varepsilon$
  on $K$; take $\varepsilon'=(M+\varepsilon)/2$. If $K$ is empty, take
  $\varepsilon/2$.
-/
theorem exists_intermediate_ball_of_isCompact_subset_ball
    {K : Set ℂ} (hK : IsCompact K) {w : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hKball : K ⊆ Metric.ball w ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' < ε ∧
      K ⊆ Metric.ball w ε' := by
  by_cases hKne : K.Nonempty
  · let d : ℂ → ℝ := fun y ↦ dist y w
    have hdcont : Continuous d := by
      fun_prop
    obtain ⟨y₀, hy₀K, hy₀max⟩ :=
      hK.exists_isMaxOn hKne hdcont.continuousOn
    have hy₀lt : d y₀ < ε :=
      Metric.mem_ball.mp (hKball hy₀K)
    have hdnonneg : 0 ≤ d y₀ :=
      dist_nonneg
    let ε' : ℝ := (d y₀ + ε) / 2
    have hε'pos : 0 < ε' := by
      dsimp [ε']
      linarith
    have hε'lt : ε' < ε := by
      dsimp [ε']
      linarith
    refine ⟨ε', hε'pos, hε'lt, ?_⟩
    intro y hyK
    rw [Metric.mem_ball]
    have hymax : d y ≤ d y₀ :=
      hy₀max hyK
    dsimp [d] at hymax ⊢
    dsimp [ε']
    linarith
  · refine ⟨ε / 2, half_pos hε, half_lt_self hε, ?_⟩
    simpa [Set.not_nonempty_iff_eq_empty.mp hKne]

/--
%%handwave
name:
  Smooth local distributional degree formula for nonnegative tests
statement:
  Let $f:\mathbb C\to\mathbb C$ be smooth and let $r,\varepsilon>0$.
  Suppose $f(\partial B(z,r))$ avoids $w$ and stays at distance at least
  $\varepsilon$ from it. If $\psi:\mathbb C\to[0,\infty)$ is continuous,
  compactly supported, and
  $\operatorname{supp}\psi\subset B(w,\varepsilon)$, then
  $$
    \int_{B(z,r)}J_f(x)\psi(f(x))\,dx
      =
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)
      \int_{\mathbb C}\psi(y)\,dy.
  $$
proof:
  Split the disk into its positive-, negative-, and zero-Jacobian parts.
  [The real positive-sheet area formula](lean:JJMath.Quasiconformal.integral_preimageMultiplicity_toReal_mul_eq_integral_weakJacobian_mul_of_pos) and [the real negative-sheet area formula](lean:JJMath.Quasiconformal.integral_preimageMultiplicity_toReal_mul_eq_integral_neg_weakJacobian_mul_of_neg) express the first two source integrals through their target multiplicities; the zero part contributes nothing. [Almost everywhere the difference of those multiplicities is the disk degree](lean:JJMath.Quasiconformal.eventually_coe_planarDiskDegree_eq_preimageMultiplicity_pos_sub_neg), and the degree is constant on the protected support of $\psi$.
-/
theorem integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral_of_contDiff_of_nonneg
    (f : ℂ → ℂ) (hfdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (havoid : ∀ t,
      imageCircleLoop f hfdiff.continuous z r t ≠ w)
    (hsep : ∀ t, ε ≤
      ‖imageCircleLoop f hfdiff.continuous z r t - w‖)
    (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (hψcompact : HasCompactSupport ψ)
    (hψsupport : tsupport ψ ⊆ Metric.ball w ε)
    (hψnonneg : ∀ y, 0 ≤ ψ y) :
    (∫ x in Metric.ball z r,
        weakJacobian (fderiv ℝ f x) * ψ (f x) ∂volume) =
      (planarCircleIndex f hfdiff.continuous z w r hr havoid : ℝ) *
        ∫ y : ℂ, ψ y ∂volume := by
  let J : ℂ → ℝ :=
    fun x ↦ weakJacobian (fderiv ℝ f x)
  let B : Set ℂ := Metric.ball z r
  let P : Set ℂ := B ∩ {x | 0 < J x}
  let N : Set ℂ := B ∩ {x | J x < 0}
  let Z : Set ℂ := B ∩ {x | J x = 0}
  let q : ℂ → ℝ := fun x ↦ J x * ψ (f x)
  have hdiff : Differentiable ℝ f :=
    hfdiff.differentiable (by simp)
  have hJcont : Continuous J := by
    exact continuous_weakJacobian.comp
      (hfdiff.continuous_fderiv (by simp))
  have hqcont : Continuous q := by
    exact hJcont.mul (hψ.comp hfdiff.continuous)
  have _hψint : Integrable ψ volume :=
    hψ.integrable_of_hasCompactSupport hψcompact
  have hBmeas : MeasurableSet B :=
    Metric.isOpen_ball.measurableSet
  have hPmeas : MeasurableSet P :=
    hBmeas.inter (measurableSet_Ioi.preimage hJcont.measurable)
  have hNmeas : MeasurableSet N :=
    hBmeas.inter (measurableSet_Iio.preimage hJcont.measurable)
  have hZmeas : MeasurableSet Z :=
    hBmeas.inter
      ((measurableSet_singleton 0).preimage hJcont.measurable)
  have hqClosed :
      IntegrableOn q (Metric.closedBall z r) :=
    hqcont.continuousOn.integrableOn_compact (isCompact_closedBall z r)
  have hqB : IntegrableOn q B :=
    hqClosed.mono_set Metric.ball_subset_closedBall
  have hqP : IntegrableOn q P :=
    hqB.mono_set inter_subset_left
  have hqN : IntegrableOn q N :=
    hqB.mono_set inter_subset_left
  have hqZ : IntegrableOn q Z :=
    hqB.mono_set inter_subset_left
  have hderivP :
      ∀ x ∈ P,
        HasFDerivWithinAt f (fderiv ℝ f x) P x := by
    intro x _hx
    exact hdiff.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hderivN :
      ∀ x ∈ N,
        HasFDerivWithinAt f (fderiv ℝ f x) N x := by
    intro x _hx
    exact hdiff.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hJP : ∀ x ∈ P, 0 < weakJacobian (fderiv ℝ f x) := by
    intro x hx
    exact hx.2
  have hJN : ∀ x ∈ N, weakJacobian (fderiv ℝ f x) < 0 := by
    intro x hx
    exact hx.2
  have hnegqN :
      IntegrableOn
        (fun x ↦ -weakJacobian (fderiv ℝ f x) * ψ (f x)) N := by
    have hneg := hqN.neg
    simpa [q, J, neg_mul] using hneg
  have hareaP :=
    integral_preimageMultiplicity_toReal_mul_eq_integral_weakJacobian_mul_of_pos
      hPmeas hderivP hJP ψ hψ.measurable hψnonneg
        (by simpa [q, J] using hqP)
  have hareaN :=
    integral_preimageMultiplicity_toReal_mul_eq_integral_neg_weakJacobian_mul_of_neg
      hNmeas hderivN hJN ψ hψ.measurable hψnonneg
        hnegqN
  have htargetP :
      Integrable
        (fun y ↦ (preimageMultiplicity f P y).toReal * ψ y)
        volume :=
    integrable_preimageMultiplicity_toReal_mul_of_pos
      hPmeas hderivP hJP ψ hψ.measurable hψnonneg
        (by simpa [q, J] using hqP)
  have htargetN :
      Integrable
        (fun y ↦ (preimageMultiplicity f N y).toReal * ψ y)
        volume :=
    integrable_preimageMultiplicity_toReal_mul_of_neg
      hNmeas hderivN hJN ψ hψ.measurable hψnonneg
        hnegqN
  have hPN : Disjoint P N := by
    apply Set.disjoint_left.mpr
    intro x hxP hxN
    have hxP' : 0 < J x := hxP.2
    have hxN' : J x < 0 := hxN.2
    exact (not_lt_of_ge (le_of_lt hxP')) hxN'
  have hUNZ : Disjoint (P ∪ N) Z := by
    apply Set.disjoint_left.mpr
    intro x hxU hxZ
    rcases hxU with hxP | hxN
    · exact (ne_of_gt hxP.2) hxZ.2
    · exact (ne_of_lt hxN.2) hxZ.2
  have hpartition : B = (P ∪ N) ∪ Z := by
    ext x
    constructor
    · intro hxB
      rcases lt_trichotomy (J x) 0 with hneg | hzero | hpos
      · exact Or.inl (Or.inr ⟨hxB, hneg⟩)
      · exact Or.inr ⟨hxB, hzero⟩
      · exact Or.inl (Or.inl ⟨hxB, hpos⟩)
    · rintro ((hxP | hxN) | hxZ)
      · exact hxP.1
      · exact hxN.1
      · exact hxZ.1
  have hqU : IntegrableOn q (P ∪ N) :=
    hqB.mono_set (union_subset inter_subset_left inter_subset_left)
  have hZzero :
      ∫ x in Z, q x ∂volume = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hxJ : J x = 0 := hx.2
    simp [q, hxJ]
  have hsourceSplit :
      ∫ x in B, q x ∂volume =
        (∫ x in P, q x ∂volume) +
          ∫ x in N, q x ∂volume := by
    rw [hpartition,
      setIntegral_union hUNZ hZmeas hqU hqZ,
      setIntegral_union hPN hNmeas hqP hqN,
      hZzero, add_zero]
  have hdegreeBall :
      ∀ y ∈ Metric.ball w ε,
        planarDiskDegree f hfdiff.continuous z r hr y =
          planarCircleIndex f hfdiff.continuous z w r hr havoid := by
    intro y hy
    have hylt : ‖y - w‖ < ε := by
      simpa [Complex.dist_eq] using Metric.mem_ball.mp hy
    have hclose :
        ∀ t, ‖y - w‖ <
          ‖imageCircleLoop f hfdiff.continuous z r t - w‖ := by
      intro t
      exact hylt.trans_le (hsep t)
    obtain ⟨hyavoid, hindex⟩ :=
      exists_planarCircleIndex_eq_of_target_norm_sub_lt
        f hfdiff.continuous z w y hr havoid hclose
    rw [planarDiskDegree_eq_planarCircleIndex
      f hfdiff.continuous z y hr hyavoid]
    exact hindex.symm
  have hdegreeMultiplicity :=
    eventually_coe_planarDiskDegree_eq_preimageMultiplicity_pos_sub_neg
      f hfdiff z w hr hε hsep
  have hdegreeMultiplicityGlobal :
      ∀ᵐ y ∂volume,
        y ∈ Metric.ball w ε →
          (planarDiskDegree f hfdiff.continuous z r hr y : ℝ) =
            (preimageMultiplicity f P y).toReal -
              (preimageMultiplicity f N y).toReal := by
    simpa [P, N, B, J] using
      ae_imp_of_ae_restrict hdegreeMultiplicity
  have hweighted :
      ∀ᵐ y ∂volume,
        ((planarCircleIndex f hfdiff.continuous z w r hr havoid : ℤ) : ℝ) *
            ψ y =
          ((preimageMultiplicity f P y).toReal -
            (preimageMultiplicity f N y).toReal) * ψ y := by
    filter_upwards [hdegreeMultiplicityGlobal] with y hy
    by_cases hyball : y ∈ Metric.ball w ε
    · rw [← hy hyball, hdegreeBall y hyball]
    · have hψzero : ψ y = 0 := by
        by_contra hne
        exact hyball (hψsupport
          (subset_tsupport ψ (Function.mem_support.mpr hne)))
      simp [hψzero]
  have htargetDifference :
      (∫ y : ℂ,
          ((preimageMultiplicity f P y).toReal -
            (preimageMultiplicity f N y).toReal) * ψ y ∂volume) =
        (∫ y : ℂ,
            (preimageMultiplicity f P y).toReal * ψ y ∂volume) -
          ∫ y : ℂ,
            (preimageMultiplicity f N y).toReal * ψ y ∂volume := by
    have hfun :
        (fun y : ℂ ↦
          ((preimageMultiplicity f P y).toReal -
            (preimageMultiplicity f N y).toReal) * ψ y) =
          (fun y ↦
            (preimageMultiplicity f P y).toReal * ψ y -
              (preimageMultiplicity f N y).toReal * ψ y) := by
      funext y
      ring
    rw [hfun, integral_sub htargetP htargetN]
  have hnegativeSource :
      (∫ x in N,
          -weakJacobian (fderiv ℝ f x) * ψ (f x) ∂volume) =
        -(∫ x in N,
          weakJacobian (fderiv ℝ f x) * ψ (f x) ∂volume) := by
    have hneg := integral_neg (μ := volume.restrict N) q
    simpa [q, J, neg_mul] using hneg
  calc
    (∫ x in Metric.ball z r,
        weakJacobian (fderiv ℝ f x) * ψ (f x) ∂volume) =
        (∫ x in P, q x ∂volume) +
          ∫ x in N, q x ∂volume := by
      simpa [B, q, J] using hsourceSplit
    _ = (∫ y : ℂ,
          (preimageMultiplicity f P y).toReal * ψ y ∂volume) -
        ∫ y : ℂ,
          (preimageMultiplicity f N y).toReal * ψ y ∂volume := by
      rw [hareaP, hareaN, hnegativeSource]
      simp [q, J]
    _ = ∫ y : ℂ,
        ((preimageMultiplicity f P y).toReal -
          (preimageMultiplicity f N y).toReal) * ψ y ∂volume :=
      htargetDifference.symm
    _ = ∫ y : ℂ,
        ((planarCircleIndex f hfdiff.continuous z w r hr havoid : ℤ) : ℝ) *
          ψ y ∂volume := by
      exact integral_congr_ae (hweighted.mono fun _ hy ↦ hy.symm)
    _ = (planarCircleIndex f hfdiff.continuous z w r hr havoid : ℝ) *
        ∫ y : ℂ, ψ y ∂volume := by
      rw [integral_const_mul]

/--
%%handwave
name:
  Smooth local distributional degree formula
statement:
  Let $f:\mathbb C\to\mathbb C$ be smooth and let $r,\varepsilon>0$.
  Suppose $f(\partial B(z,r))$ avoids $w$ and stays at distance at least
  $\varepsilon$ from it. If $\varphi:\mathbb C\to\mathbb R$ is smooth,
  compactly supported, and
  $\operatorname{supp}\varphi\subset B(w,\varepsilon)$, then
  $$
    \int_{B(z,r)}J_f(x)\varphi(f(x))\,dx
      =
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)
      \int_{\mathbb C}\varphi(y)\,dy.
  $$
proof:
  Write $\varphi=\varphi_+-\varphi_-$, where
  $\varphi_+=\max(\varphi,0)$ and
  $\varphi_-=\max(-\varphi,0)$. Both parts are continuous, nonnegative,
  compactly supported in the same protected target ball. Apply [the nonnegative-test distributional degree formula](lean:JJMath.Quasiconformal.integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral_of_contDiff_of_nonneg) to both parts and subtract.
-/
theorem integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral_of_contDiff
    (f : ℂ → ℂ) (hfdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (havoid : ∀ t,
      imageCircleLoop f hfdiff.continuous z r t ≠ w)
    (hsep : ∀ t, ε ≤
      ‖imageCircleLoop f hfdiff.continuous z r t - w‖)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hφcompact : HasCompactSupport φ)
    (hφsupport : tsupport φ ⊆ Metric.ball w ε) :
    (∫ x in Metric.ball z r,
        weakJacobian (fderiv ℝ f x) * φ (f x) ∂volume) =
      (planarCircleIndex f hfdiff.continuous z w r hr havoid : ℝ) *
        ∫ y : ℂ, φ y ∂volume := by
  let φpos : ℂ → ℝ := fun y ↦ max (φ y) 0
  let φneg : ℂ → ℝ := fun y ↦ max (-φ y) 0
  have hφposCont : Continuous φpos :=
    hφ.continuous.max continuous_const
  have hφnegCont : Continuous φneg :=
    hφ.continuous.neg.max continuous_const
  have hφposNonneg : ∀ y, 0 ≤ φpos y := by
    intro y
    exact le_max_right _ _
  have hφnegNonneg : ∀ y, 0 ≤ φneg y := by
    intro y
    exact le_max_right _ _
  have hφposSupport :
      Function.support φpos ⊆ Function.support φ := by
    intro y hy
    intro hφy
    apply hy
    simp [φpos, hφy]
  have hφnegSupport :
      Function.support φneg ⊆ Function.support φ := by
    intro y hy
    intro hφy
    apply hy
    simp [φneg, hφy]
  have hφposCompact : HasCompactSupport φpos :=
    hφcompact.mono hφposSupport
  have hφnegCompact : HasCompactSupport φneg :=
    hφcompact.mono hφnegSupport
  have hφposTSupport :
      tsupport φpos ⊆ Metric.ball w ε := by
    exact (closure_mono hφposSupport).trans hφsupport
  have hφnegTSupport :
      tsupport φneg ⊆ Metric.ball w ε := by
    exact (closure_mono hφnegSupport).trans hφsupport
  have hφdecomp : ∀ y, φ y = φpos y - φneg y := by
    intro y
    by_cases hy : 0 ≤ φ y
    · simp [φpos, φneg, max_eq_left hy,
        max_eq_right (neg_nonpos.mpr hy)]
    · have hy' : φ y ≤ 0 := le_of_not_ge hy
      simp [φpos, φneg, max_eq_right hy',
        max_eq_left (neg_nonneg.mpr hy')]
  have hposFormula :=
    integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral_of_contDiff_of_nonneg
      f hfdiff z w hr hε havoid hsep φpos hφposCont
        hφposCompact hφposTSupport hφposNonneg
  have hnegFormula :=
    integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral_of_contDiff_of_nonneg
      f hfdiff z w hr hε havoid hsep φneg hφnegCont
        hφnegCompact hφnegTSupport hφnegNonneg
  have hJcont :
      Continuous (fun x ↦ weakJacobian (fderiv ℝ f x)) :=
    continuous_weakJacobian.comp
      (hfdiff.continuous_fderiv (by simp))
  have hsourcePos :
      IntegrableOn
        (fun x ↦ weakJacobian (fderiv ℝ f x) * φpos (f x))
        (Metric.ball z r) := by
    apply IntegrableOn.mono_set
      ((hJcont.mul (hφposCont.comp hfdiff.continuous)).continuousOn
        |>.integrableOn_compact (isCompact_closedBall z r))
    exact Metric.ball_subset_closedBall
  have hsourceNeg :
      IntegrableOn
        (fun x ↦ weakJacobian (fderiv ℝ f x) * φneg (f x))
        (Metric.ball z r) := by
    apply IntegrableOn.mono_set
      ((hJcont.mul (hφnegCont.comp hfdiff.continuous)).continuousOn
        |>.integrableOn_compact (isCompact_closedBall z r))
    exact Metric.ball_subset_closedBall
  have htargetPos : Integrable φpos volume :=
    hφposCont.integrable_of_hasCompactSupport hφposCompact
  have htargetNeg : Integrable φneg volume :=
    hφnegCont.integrable_of_hasCompactSupport hφnegCompact
  calc
    (∫ x in Metric.ball z r,
        weakJacobian (fderiv ℝ f x) * φ (f x) ∂volume) =
        ∫ x in Metric.ball z r,
          (weakJacobian (fderiv ℝ f x) * φpos (f x) -
            weakJacobian (fderiv ℝ f x) * φneg (f x)) ∂volume := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x _hx
      change
        weakJacobian (fderiv ℝ f x) * φ (f x) =
          weakJacobian (fderiv ℝ f x) * φpos (f x) -
            weakJacobian (fderiv ℝ f x) * φneg (f x)
      rw [hφdecomp (f x)]
      ring
    _ = (∫ x in Metric.ball z r,
          weakJacobian (fderiv ℝ f x) * φpos (f x) ∂volume) -
        ∫ x in Metric.ball z r,
          weakJacobian (fderiv ℝ f x) * φneg (f x) ∂volume := by
      rw [integral_sub hsourcePos hsourceNeg]
    _ = (planarCircleIndex f hfdiff.continuous z w r hr havoid : ℝ) *
          (∫ y : ℂ, φpos y ∂volume) -
        (planarCircleIndex f hfdiff.continuous z w r hr havoid : ℝ) *
          ∫ y : ℂ, φneg y ∂volume := by
      rw [hposFormula, hnegFormula]
    _ = (planarCircleIndex f hfdiff.continuous z w r hr havoid : ℝ) *
        ((∫ y : ℂ, φpos y ∂volume) -
          ∫ y : ℂ, φneg y ∂volume) := by
      ring
    _ = (planarCircleIndex f hfdiff.continuous z w r hr havoid : ℝ) *
        ∫ y : ℂ, φ y ∂volume := by
      rw [← integral_sub htargetPos htargetNeg]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      exact (hφdecomp y).symm

/--
%%handwave
name:
  Local distributional degree formula on a disk
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$ with weak differential $Df$. Let $r>0$, suppose
  $f(\partial B(z,r))$ avoids $w$, and choose $\varepsilon>0$ no larger than
  the distance from $w$ to that boundary image. If
  $\varphi:\mathbb C\to\mathbb R$ is smooth and compactly supported in
  $B(w,\varepsilon)$, then
  $$
    \int_{B(z,r)}J_f(x)\varphi(f(x))\,dx
      =
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)
      \int_{\mathbb C}\varphi(y)\,dy.
  $$
proof:
  Approximate $f$ smoothly on the closed disk while preserving the boundary
  index throughout the protected target ball. Sard makes almost every target
  regular for each approximant, and [the boundary degree is then the signed count of regular preimages](lean:JJMath.Quasiconformal.planarCircleIndex_eq_finsum_jacobianSign_fiber_inter_ball_of_regular). Apply the differentiable area formula separately on the positive- and negative-Jacobian sheets and pass to the Sobolev limit.
-/
theorem IsLocalW12On.integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Set.univ f df) (hf : Continuous f)
    (z w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (havoid : ∀ t, imageCircleLoop f hf z r t ≠ w)
    (hsep : ∀ t, ε ≤ ‖imageCircleLoop f hf z r t - w‖)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hφcompact : HasCompactSupport φ)
    (hφsupport : tsupport φ ⊆ Metric.ball w ε) :
    (∫ x in Metric.ball z r,
        weakJacobian (df x) * φ (f x) ∂volume) =
      (planarCircleIndex f hf z w r hr havoid : ℝ) *
        ∫ y : ℂ, φ y ∂volume := by
  obtain ⟨ε', hε'pos, hε'lt, hφsupport'⟩ :=
    exists_intermediate_ball_of_isCompact_subset_ball
      hφcompact hε hφsupport
  let Q : Set ℂ := Metric.closedBall z r
  let P : Set ℂ := Metric.cthickening 1 Q
  have hQ : IsCompact Q := by
    simpa [Q] using isCompact_closedBall z r
  have hP : IsCompact P := by
    exact hQ.cthickening
  have hQP :
      ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P := by
    exact ⟨1, zero_lt_one, by rfl⟩
  obtain ⟨hgraph, huniform⟩ :=
    IsLocalW12On.exists_smoothApproxGraphL2Data_on_compact_tendstoUniformlyOn
      hW hf hQ hP hQP (by simp [P])
  have hdfQ : MemLp df 2 (volume.restrict Q) :=
    (hW.2.2 Q hQ (by simp [Q])).2
  have hconvClosed :=
    hgraph.weakJacobian_test_comp_integral_tendsto_of_tendstoUniformlyOn
      hQ hdfQ huniform φ hφ hφcompact
  have hQball :
      Q =ᵐ[volume] Metric.ball z r := by
    simpa [Q] using complex_closedBall_ae_eq_ball z r
  have hconvBall :
      Filter.Tendsto
        (fun n ↦ ∫ x in Metric.ball z r,
          weakJacobian
              (fderiv ℝ (hgraph.approximants n) x) *
            φ (hgraph.approximants n x) ∂volume)
        Filter.atTop
        (𝓝 (∫ x in Metric.ball z r,
          weakJacobian (df x) * φ (f x) ∂volume)) := by
    have hsource :
        (fun n ↦ ∫ x in Q,
          weakJacobian
              (fderiv ℝ (hgraph.approximants n) x) *
            φ (hgraph.approximants n x) ∂volume) =ᶠ[Filter.atTop]
          (fun n ↦ ∫ x in Metric.ball z r,
            weakJacobian
                (fderiv ℝ (hgraph.approximants n) x) *
              φ (hgraph.approximants n x) ∂volume) :=
      Filter.Eventually.of_forall fun _ ↦
        setIntegral_congr_set hQball
    have htarget :
        (∫ x in Q, weakJacobian (df x) * φ (f x) ∂volume) =
          ∫ x in Metric.ball z r,
            weakJacobian (df x) * φ (f x) ∂volume :=
      setIntegral_congr_set hQball
    rw [← htarget]
    exact Filter.Tendsto.congr' hsource hconvClosed
  let δ : ℝ := (ε - ε') / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  have hδlt : δ < ε - ε' := by
    dsimp [δ]
    linarith
  have huniformEventually :
      ∀ᶠ n in Filter.atTop, ∀ x ∈ Q,
        dist (f x) (hgraph.approximants n x) < δ :=
    (Metric.tendstoUniformlyOn_iff.mp huniform) δ hδpos
  have heventFormula :
      ∀ᶠ n in Filter.atTop,
        (∫ x in Metric.ball z r,
            weakJacobian
                (fderiv ℝ (hgraph.approximants n) x) *
              φ (hgraph.approximants n x) ∂volume) =
          (planarCircleIndex f hf z w r hr havoid : ℝ) *
            ∫ y : ℂ, φ y ∂volume := by
    filter_upwards [huniformEventually] with n hn
    let T : ℂ → ℂ := hgraph.approximants n
    have hTdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) T :=
      hgraph.smooth n
    have hcircleQ :
        ∀ t : unitInterval, circlePoint z r t ∈ Q := by
      intro t
      change dist (circlePoint z r t) z ≤ r
      rw [dist_circlePoint_center z hr t]
    have hcloseδ :
        ∀ t : unitInterval,
          ‖imageCircleLoop f hf z r t -
              imageCircleLoop T hTdiff.continuous z r t‖ < δ := by
      intro t
      have ht := hn (circlePoint z r t) (hcircleQ t)
      simpa [imageCircleLoop, complexCircleLoop, T, Complex.dist_eq] using ht
    have hTsep :
        ∀ t : unitInterval,
          ε' ≤
            ‖imageCircleLoop T hTdiff.continuous z r t - w‖ := by
      intro t
      have htriangle :
          ‖imageCircleLoop f hf z r t - w‖ ≤
            ‖imageCircleLoop f hf z r t -
                imageCircleLoop T hTdiff.continuous z r t‖ +
              ‖imageCircleLoop T hTdiff.continuous z r t - w‖ := by
        calc
          ‖imageCircleLoop f hf z r t - w‖ =
              ‖(imageCircleLoop f hf z r t -
                    imageCircleLoop T hTdiff.continuous z r t) +
                (imageCircleLoop T hTdiff.continuous z r t - w)‖ := by
              congr 1
              ring
          _ ≤
              ‖imageCircleLoop f hf z r t -
                  imageCircleLoop T hTdiff.continuous z r t‖ +
                ‖imageCircleLoop T hTdiff.continuous z r t - w‖ :=
            norm_add_le _ _
      linarith [hsep t, hcloseδ t]
    have hTavoid :
        ∀ t : unitInterval,
          imageCircleLoop T hTdiff.continuous z r t ≠ w := by
      intro t ht
      have hzero :
          ‖imageCircleLoop T hTdiff.continuous z r t - w‖ = 0 := by
        rw [ht, sub_self, norm_zero]
      linarith [hTsep t]
    have hclose :
        ∀ t : unitInterval,
          ‖imageCircleLoop T hTdiff.continuous z r t -
              imageCircleLoop f hf z r t‖ <
            ‖imageCircleLoop f hf z r t - w‖ := by
      intro t
      rw [norm_sub_rev]
      exact (hcloseδ t).trans
        (hδlt.trans_le (by linarith [hsep t]))
    have hindex :
        planarCircleIndex f hf z w r hr havoid =
          planarCircleIndex T hTdiff.continuous z w r hr hTavoid :=
      planarCircleIndex_eq_of_norm_sub_lt
        f T hf hTdiff.continuous z w hr havoid hTavoid hclose
    have hsmooth :=
      integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral_of_contDiff
        T hTdiff z w hr hε'pos hTavoid hTsep
          φ hφ hφcompact hφsupport'
    rw [← hindex] at hsmooth
    simpa [T] using hsmooth
  have hconstant :
      Filter.Tendsto
        (fun n ↦ ∫ x in Metric.ball z r,
          weakJacobian
              (fderiv ℝ (hgraph.approximants n) x) *
            φ (hgraph.approximants n x) ∂volume)
        Filter.atTop
        (𝓝 ((planarCircleIndex f hf z w r hr havoid : ℝ) *
          ∫ y : ℂ, φ y ∂volume)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    exact heventFormula.mono fun _ hn ↦ hn.symm
  exact tendsto_nhds_unique hconvBall hconstant

/--
%%handwave
name:
  Jacobian alternatives for a bounded-distortion differential field
statement:
  Let $K\ge1$ and suppose a planar differential field satisfies
  $\|Df(z)\|_{\mathrm{op}}^2\le KJ_f(z)$ almost everywhere. Then
  $J_f\ge0$ almost everywhere, and at almost every point where $J_f=0$ one
  has $Df=0$.
proof:
  Apply the pointwise nonnegative-Jacobian and zero-Jacobian consequences of
  the distortion inequality wherever that inequality holds.
-/
theorem boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
    {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)) :
    (∀ᵐ z ∂(volume : Measure ℂ),
        0 ≤ weakJacobian (df z)) ∧
      ∀ᵐ z ∂(volume : Measure ℂ),
        weakJacobian (df z) = 0 → df z = 0 := by
  constructor
  · filter_upwards [hdist] with z hz
    exact weakJacobian_nonneg_of_distortion
      (df z) (lt_of_lt_of_le zero_lt_one hK) hz
  · filter_upwards [hdist] with z hz
    exact fun hJ ↦
      eq_zero_of_weakJacobian_eq_zero_of_distortion
        (df z) hz hJ

/--
%%handwave
name:
  Beltrami data associated with a bounded-distortion map
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\mathbb C,\mathbb C)$ have weak
  differential $Df$, and suppose
  $\|Df(z)\|_{\mathrm{op}}^2\le KJ_f(z)$ almost everywhere for some $K\ge1$.
  Set
  $$
    k=\frac{K-1}{K+1},\qquad
    \mu(z)=
      \begin{cases}
        0,&\partial_zf(z)=0,\\
        \partial_{\bar z}f(z)/\partial_zf(z),
          &\partial_zf(z)\ne0.
      \end{cases}
  $$
  Then $0\le k<1$, $\mu$ is measurable up to a null set,
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere, and
  $|\mu|\le k$ almost everywhere.
proof:
  The coefficient is a measurable Borel function of the weak differential.
  Apply the pointwise equivalence between metric distortion and the
  Wirtinger ratio at almost every point.
-/
theorem IsLocalW12On.boundedDistortion_beltramiData
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)) :
    0 ≤ (K - 1) / (K + 1) ∧
      (K - 1) / (K + 1) < 1 ∧
      AEStronglyMeasurable (beltramiCoefficient df) volume ∧
      WeakBeltramiEquationOn Set.univ
        (beltramiCoefficient df) df ∧
      HasEssentialNormLEOn Set.univ
        (beltramiCoefficient df) ((K - 1) / (K + 1)) := by
  have hKp : 0 < K + 1 := by linarith
  have hk0 : 0 ≤ (K - 1) / (K + 1) :=
    div_nonneg (sub_nonneg.mpr hK) hKp.le
  have hk1 : (K - 1) / (K + 1) < 1 :=
    (div_lt_one hKp).2 (by linarith)
  have hμmeas :
      AEStronglyMeasurable
        (beltramiCoefficient df) volume := by
    simpa using
      hW.beltramiCoefficient_aestronglyMeasurable
  obtain ⟨heq, hμ⟩ :=
    weakBeltramiEquationOn_beltramiCoefficient_of_boundedDistortion
      hK hdist
  exact ⟨hk0, hk1, hμmeas, heq, hμ⟩

/--
%%handwave
name:
  Local higher integrability for maps of bounded distortion
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally $W^{1,2}$, with
  weak differential $Df$. Suppose $K\geq1$ and
  $$
    \|Df(z)\|_{\mathrm{op}}^2\leq KJ_f(z)
  $$
  almost everywhere. Then for every compact set $Q\subset\mathbb C$ there is
  an exponent $p$ with $2<p<3$ such that
  $$
    Df\in L^p(Q).
  $$
proof:
  The distortion inequality produces the measurable coefficient
  $\mu=\partial_{\bar z}f/\partial_zf$, with the zero branch included, and
  gives
  $|\mu|\leq(K-1)/(K+1)<1$. Apply local higher integrability for continuous
  weak Beltrami solutions.
-/
theorem IsLocalW12On.boundedDistortion_derivative_memLpOn_compact_nearTwo
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df) (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    {Q : Set ℂ} (hQ : IsCompact Q) :
    ∃ p : ℝ, 2 < p ∧ p < 3 ∧
      MemLp df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict Q) := by
  obtain ⟨hk0, hk1, hμmeas, heq, hμbound⟩ :=
    hW.boundedDistortion_beltramiData hK hdist
  have hμbound_global :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖beltramiCoefficient df z‖ ≤ (K - 1) / (K + 1) := by
    simpa [HasEssentialNormLEOn] using hμbound
  exact hW.exists_derivative_memLpOn_compact_nearTwo
    hf hμmeas hk0 hk1 hμbound_global heq hQ (Set.subset_univ Q)

/--
%%handwave
name:
  Lusin property from higher integrability on compact sets
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$. Suppose that for every compact
  $Q\subset\mathbb C$ there is an exponent $p>2$ such that
  $Df\in L^p(Q)$. Then every null set $N\subset\mathbb C$ has null image:
  $$
    |N|=0\quad\Longrightarrow\quad |f(N)|=0.
  $$
proof:
  Decompose $N$ into its intersections with the closed balls
  $\overline B(0,n)$. Each such intersection lies in the interior of
  $\overline B(0,n+1)$, where the assumed higher integrability and [the bounded Lusin theorem above the planar dimension](lean:JJMath.Quasiconformal.IsLocalW12On.volume_image_eq_zero_of_null_of_memLp) show that its image is null. Countable subadditivity finishes the proof.
-/
theorem IsLocalW12On.hasLusinNOn_of_derivative_memLpOn_compact_above_two
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Set.univ f df) (hf : Continuous f)
    (hLp : ∀ {Q : Set ℂ}, IsCompact Q →
      ∃ p : ℝ, 2 < p ∧
        MemLp df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict Q)) :
    HasLusinNOn Set.univ f := by
  intro N hNuniv hNzero
  let A : ℕ → Set ℂ :=
    fun n => N ∩ Metric.closedBall 0 n
  have hAimage (n : ℕ) :
      volume (f '' A n) = 0 := by
    let C : Set ℂ :=
      Metric.closedBall 0 (n + 1)
    have hC : IsCompact C :=
      isCompact_closedBall 0 (n + 1)
    obtain ⟨p, hp, hdfp⟩ :=
      hLp hC
    have hAC : A n ⊆ interior C := by
      intro z hz
      apply Metric.ball_subset_interior_closedBall
      rw [Metric.mem_ball]
      have hzdist :
          dist z 0 ≤ (n : ℝ) := by
        simpa [A, Metric.mem_closedBall] using hz.2
      exact hzdist.trans_lt (by norm_num)
    exact
      hW.volume_image_eq_zero_of_null_of_memLp
        hf.continuousOn hp hC hAC (Set.subset_univ C)
        (measure_mono_null inter_subset_left hNzero) hdfp
  have hcover :
      N ⊆ ⋃ n : ℕ, A n := by
    intro z hz
    have hzball :
        z ∈ ⋃ n : ℕ, Metric.closedBall (0 : ℂ) n := by
      rw [Metric.iUnion_closedBall_nat]
      trivial
    rcases Set.mem_iUnion.mp hzball with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hz, hn⟩
  have himage :
      f '' N ⊆ ⋃ n : ℕ, f '' A n := by
    rintro y ⟨z, hz, rfl⟩
    rcases Set.mem_iUnion.mp (hcover hz) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨z, hn, rfl⟩⟩
  apply le_antisymm
  · calc
      volume (f '' N) ≤
          volume (⋃ n : ℕ, f '' A n) :=
        measure_mono himage
      _ ≤ ∑' n : ℕ, volume (f '' A n) :=
        measure_iUnion_le _
      _ = 0 := by
        simp [hAimage]
  · exact bot_le

/--
%%handwave
name:
  Lusin property for planar maps of bounded distortion
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$. Suppose $K\geq1$ and
  $$
    \lVert Df(z)\rVert_{\mathrm{op}}^2
      \leq KJ_f(z)
  $$
  almost everywhere. Then every null set $N\subset\mathbb C$ has null
  image:
  $$
    |N|=0\quad\Longrightarrow\quad |f(N)|=0.
  $$
proof:
  [Bounded distortion gives an exponent $p>2$ for the weak differential on every compact set](lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_derivative_memLpOn_compact_nearTwo). Apply [the compact-exhaustion criterion for the Lusin property](lean:JJMath.Quasiconformal.IsLocalW12On.hasLusinNOn_of_derivative_memLpOn_compact_above_two).
-/
theorem IsLocalW12On.boundedDistortion_hasLusinNOn
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df) (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)) :
    HasLusinNOn Set.univ f := by
  apply
    hW.hasLusinNOn_of_derivative_memLpOn_compact_above_two
      hf
  intro Q hQ
  obtain ⟨p, hp, hp3, hdfp⟩ :=
    hW.boundedDistortion_derivative_memLpOn_compact_nearTwo
      hf hK hdist hQ
  exact ⟨p, hp, hdfp⟩

/--
%%handwave
name:
  Multiplicity area formula for planar maps of bounded distortion
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$. Suppose $K\geq1$ and
  $$
    \lVert Df(z)\rVert_{\mathrm{op}}^2
      \leq KJ_f(z)
  $$
  almost everywhere. For every measurable $S\subseteq\mathbb C$ and every
  almost-everywhere measurable $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S J_f(x)g(f(x))\,dx.
  $$
proof:
  The distortion inequality gives $J_f\geq0$ almost everywhere, while [local higher integrability gives the Lusin property](lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_hasLusinNOn). Apply [the Sobolev multiplicity area formula](lean:JJMath.Quasiconformal.IsLocalW12On.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae).
-/
theorem IsLocalW12On.boundedDistortion_areaFormula_preimageMultiplicity
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
      ∫⁻ x in S,
        ENNReal.ofReal (weakJacobian (df x)) *
          g (f x) ∂volume := by
  apply
    hW.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      (hW.boundedDistortion_hasLusinNOn
        hf hK hdist)
      (ae_restrict_of_ae
        (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
          hK hdist).1)
      hSmeas (Set.subset_univ S) g hg

/--
%%handwave
name:
  Multiplicity agrees almost everywhere with protected disk degree
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. Let $r,\varepsilon>0$, suppose
  $f(\partial B(z,r))$ avoids $w$, and suppose its distance from $w$ is at
  least $\varepsilon$. Then for almost every $y\in B(w,\varepsilon)$,
  $$
    N(f,B(z,r),y)
      =
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr).
  $$
  The extended multiplicity is interpreted as a real number.
proof:
  The weak differential is square-integrable on the source disk, so its
  Jacobian is integrable there. The Lusin property and nonnegative Jacobian
  give an integrable real-valued multiplicity and its weighted area formula.
  For every smooth test function compactly supported in the protected target
  ball, split the test into its positive and negative parts and apply that
  area formula. [The local distributional degree formula](lean:JJMath.Quasiconformal.IsLocalW12On.integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral) identifies the same source integral with the disk index times the test integral. Uniqueness of locally integrable distributions gives the almost-everywhere equality.
-/
theorem IsLocalW12On.eventually_preimageMultiplicity_toReal_eq_planarCircleIndex_of_boundedDistortion
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ x ∂(volume : Measure ℂ),
      ‖df x‖ ^ 2 ≤ K * weakJacobian (df x))
    (z w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (havoid : ∀ t, imageCircleLoop f hf z r t ≠ w)
    (hsep : ∀ t, ε ≤ ‖imageCircleLoop f hf z r t - w‖) :
    ∀ᵐ y ∂volume,
      y ∈ Metric.ball w ε →
        (preimageMultiplicity f (Metric.ball z r) y).toReal =
          (planarCircleIndex f hf z w r hr havoid : ℝ) := by
  let d : ℝ :=
    (planarCircleIndex f hf z w r hr havoid : ℝ)
  have hLusin :
      HasLusinNOn Set.univ f :=
    hW.boundedDistortion_hasLusinNOn hf hK hdist
  have hJglobal :
      ∀ᵐ x ∂(volume : Measure ℂ),
        0 ≤ weakJacobian (df x) :=
    (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
      hK hdist).1
  have hJuniv :
      ∀ᵐ x ∂volume.restrict Set.univ,
        0 ≤ weakJacobian (df x) :=
    ae_restrict_of_ae hJglobal
  have hdfClosed :
      MemLp df 2
        (volume.restrict (Metric.closedBall z r)) :=
    (hW.2.2 (Metric.closedBall z r)
      (isCompact_closedBall z r) (Set.subset_univ _)).2
  have hdfBall :
      MemLp df 2
        (volume.restrict (Metric.ball z r)) :=
    hdfClosed.mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hJint :
      Integrable (fun x ↦ weakJacobian (df x))
        (volume.restrict (Metric.ball z r)) :=
    weakJacobian_integrable_of_memLp_two hdfBall
  have hNint :
      Integrable
        (fun y ↦
          (preimageMultiplicity f (Metric.ball z r) y).toReal)
        volume := by
    have hsource :
        Integrable
          (fun x ↦ weakJacobian (df x) * (1 : ℝ))
          (volume.restrict (Metric.ball z r)) := by
      simpa using hJint
    have h :=
      hW.integrable_preimageMultiplicity_toReal_mul_of_hasLusinNOn_of_weakJacobian_nonneg_ae
        hLusin hJuniv Metric.isOpen_ball.measurableSet
        (Set.subset_univ _) (fun _ ↦ (1 : ℝ))
        measurable_const (fun _ ↦ zero_le_one) hsource
    simpa using h
  have hlocal :
      LocallyIntegrableOn
        (fun y ↦
          (preimageMultiplicity f (Metric.ball z r) y).toReal - d)
        (Metric.ball w ε) volume := by
    exact
      (hNint.locallyIntegrable.locallyIntegrableOn
        (Metric.ball w ε)).sub
          (locallyIntegrableOn_const d)
  suffices
      ∀ᵐ y ∂volume,
        y ∈ Metric.ball w ε →
          (preimageMultiplicity f (Metric.ball z r) y).toReal - d = 0 by
    filter_upwards [this] with y hy
    intro hyball
    simpa [d, sub_eq_zero] using hy hyball
  apply
    Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hlocal
  intro φ hφ hφcompact hφsupport
  let φpos : ℂ → ℝ := fun y ↦ max (φ y) 0
  let φneg : ℂ → ℝ := fun y ↦ max (-φ y) 0
  have hφposCont : Continuous φpos :=
    hφ.continuous.max continuous_const
  have hφnegCont : Continuous φneg :=
    hφ.continuous.neg.max continuous_const
  have hφposNonneg : ∀ y, 0 ≤ φpos y := by
    intro y
    exact le_max_right _ _
  have hφnegNonneg : ∀ y, 0 ≤ φneg y := by
    intro y
    exact le_max_right _ _
  have hφposSupport :
      Function.support φpos ⊆ Function.support φ := by
    intro y hy
    intro hφy
    apply hy
    simp [φpos, hφy]
  have hφnegSupport :
      Function.support φneg ⊆ Function.support φ := by
    intro y hy
    intro hφy
    apply hy
    simp [φneg, hφy]
  have hφposCompact : HasCompactSupport φpos :=
    hφcompact.mono hφposSupport
  have hφnegCompact : HasCompactSupport φneg :=
    hφcompact.mono hφnegSupport
  have hφdecomp : ∀ y, φ y = φpos y - φneg y := by
    intro y
    by_cases hy : 0 ≤ φ y
    · simp [φpos, φneg, max_eq_left hy,
        max_eq_right (neg_nonpos.mpr hy)]
    · have hy' : φ y ≤ 0 := le_of_not_ge hy
      simp [φpos, φneg, max_eq_right hy',
        max_eq_left (neg_nonneg.mpr hy')]
  rcases hφposCont.bounded_above_of_compact_support hφposCompact with
    ⟨Cpos, hCpos⟩
  rcases hφnegCont.bounded_above_of_compact_support hφnegCompact with
    ⟨Cneg, hCneg⟩
  have hsourcePos :
      Integrable
        (fun x ↦ weakJacobian (df x) * φpos (f x))
        (volume.restrict (Metric.ball z r)) := by
    exact hJint.mul_bdd
      (hφposCont.comp hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ hCpos (f x))
  have hsourceNeg :
      Integrable
        (fun x ↦ weakJacobian (df x) * φneg (f x))
        (volume.restrict (Metric.ball z r)) := by
    exact hJint.mul_bdd
      (hφnegCont.comp hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ hCneg (f x))
  have htargetPos :
      Integrable
        (fun y ↦
          (preimageMultiplicity f (Metric.ball z r) y).toReal *
            φpos y) volume :=
    hW.integrable_preimageMultiplicity_toReal_mul_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hLusin hJuniv Metric.isOpen_ball.measurableSet
      (Set.subset_univ _) φpos hφposCont.measurable
      hφposNonneg hsourcePos
  have htargetNeg :
      Integrable
        (fun y ↦
          (preimageMultiplicity f (Metric.ball z r) y).toReal *
            φneg y) volume :=
    hW.integrable_preimageMultiplicity_toReal_mul_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hLusin hJuniv Metric.isOpen_ball.measurableSet
      (Set.subset_univ _) φneg hφnegCont.measurable
      hφnegNonneg hsourceNeg
  have hposFormula :=
    hW.integral_preimageMultiplicity_toReal_mul_eq_integral_weakJacobian_mul_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hLusin hJuniv Metric.isOpen_ball.measurableSet
      (Set.subset_univ _) φpos hφposCont.measurable
      hφposNonneg hsourcePos
  have hnegFormula :=
    hW.integral_preimageMultiplicity_toReal_mul_eq_integral_weakJacobian_mul_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hLusin hJuniv Metric.isOpen_ball.measurableSet
      (Set.subset_univ _) φneg hφnegCont.measurable
      hφnegNonneg hsourceNeg
  have htarget :
      (∫ y : ℂ,
          (preimageMultiplicity f (Metric.ball z r) y).toReal *
            φ y ∂volume) =
        ∫ x in Metric.ball z r,
          weakJacobian (df x) * φ (f x) ∂volume := by
    calc
      (∫ y : ℂ,
          (preimageMultiplicity f (Metric.ball z r) y).toReal *
            φ y ∂volume) =
          ∫ y : ℂ,
            ((preimageMultiplicity f (Metric.ball z r) y).toReal *
                φpos y -
              (preimageMultiplicity f (Metric.ball z r) y).toReal *
                φneg y) ∂volume := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hφdecomp y]
        ring
      _ =
          (∫ y : ℂ,
              (preimageMultiplicity f (Metric.ball z r) y).toReal *
                φpos y ∂volume) -
            ∫ y : ℂ,
              (preimageMultiplicity f (Metric.ball z r) y).toReal *
                φneg y ∂volume := by
        rw [integral_sub htargetPos htargetNeg]
      _ =
          (∫ x in Metric.ball z r,
              weakJacobian (df x) * φpos (f x) ∂volume) -
            ∫ x in Metric.ball z r,
              weakJacobian (df x) * φneg (f x) ∂volume := by
        rw [hposFormula, hnegFormula]
      _ =
          ∫ x in Metric.ball z r,
            weakJacobian (df x) * φ (f x) ∂volume := by
        rw [← integral_sub hsourcePos hsourceNeg]
        apply integral_congr_ae
        filter_upwards with x
        rw [hφdecomp (f x)]
        ring
  have hdegree :=
    hW.integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral
      hf z w hr hε havoid hsep φ hφ hφcompact hφsupport
  have htargetDegree :
      (∫ y : ℂ,
          (preimageMultiplicity f (Metric.ball z r) y).toReal *
            φ y ∂volume) =
        d * ∫ y : ℂ, φ y ∂volume := by
    exact htarget.trans (by simpa [d] using hdegree)
  rcases hφ.continuous.bounded_above_of_compact_support hφcompact with
    ⟨Cφ, hCφ⟩
  have hNφ :
      Integrable
        (fun y ↦
          (preimageMultiplicity f (Metric.ball z r) y).toReal * φ y)
        volume :=
    hNint.mul_bdd hφ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hCφ)
  have hφint : Integrable φ volume :=
    hφ.continuous.integrable_of_hasCompactSupport hφcompact
  calc
    (∫ y : ℂ,
        φ y •
          ((preimageMultiplicity f (Metric.ball z r) y).toReal - d)
        ∂volume) =
        ∫ y : ℂ,
          ((preimageMultiplicity f (Metric.ball z r) y).toReal * φ y -
            d * φ y) ∂volume := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [smul_eq_mul]
      ring
    _ =
        (∫ y : ℂ,
            (preimageMultiplicity f (Metric.ball z r) y).toReal * φ y
            ∂volume) -
          ∫ y : ℂ, d * φ y ∂volume := by
      rw [integral_sub hNφ (hφint.const_mul d)]
    _ =
        (∫ y : ℂ,
            (preimageMultiplicity f (Metric.ball z r) y).toReal * φ y
            ∂volume) -
          d * ∫ y : ℂ, φ y ∂volume := by
      rw [integral_const_mul]
    _ = 0 := by
      rw [htargetDegree, sub_self]

/--
%%handwave
name:
  Extended multiplicity agrees almost everywhere with protected disk degree
statement:
  Under the hypotheses of the protected disk-degree comparison, for almost
  every $y\in B(w,\varepsilon)$ the extended multiplicity is finite and
  $$
    N(f,B(z,r),y)
      =
    \operatorname{ofReal}\!\left(
      \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)\right).
  $$
proof:
  The multiplicity area formula with weight one has a finite source side
  because a square-integrable planar differential has integrable Jacobian.
  Hence the extended multiplicity is finite almost everywhere. Combine this
  with [the real-valued multiplicity-degree equality](lean:JJMath.Quasiconformal.IsLocalW12On.eventually_preimageMultiplicity_toReal_eq_planarCircleIndex_of_boundedDistortion) and convert back to extended nonnegative reals.
-/
theorem IsLocalW12On.eventually_preimageMultiplicity_eq_ofReal_planarCircleIndex_of_boundedDistortion
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ x ∂(volume : Measure ℂ),
      ‖df x‖ ^ 2 ≤ K * weakJacobian (df x))
    (z w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (havoid : ∀ t, imageCircleLoop f hf z r t ≠ w)
    (hsep : ∀ t, ε ≤ ‖imageCircleLoop f hf z r t - w‖) :
    ∀ᵐ y ∂volume,
      y ∈ Metric.ball w ε →
        preimageMultiplicity f (Metric.ball z r) y =
          ENNReal.ofReal
            (planarCircleIndex f hf z w r hr havoid : ℝ) := by
  have hreal :=
    hW.eventually_preimageMultiplicity_toReal_eq_planarCircleIndex_of_boundedDistortion
      hf hK hdist z w hr hε havoid hsep
  have hLusin :
      HasLusinNOn Set.univ f :=
    hW.boundedDistortion_hasLusinNOn hf hK hdist
  have hJuniv :
      ∀ᵐ x ∂volume.restrict Set.univ,
        0 ≤ weakJacobian (df x) :=
    ae_restrict_of_ae
      (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
        hK hdist).1
  have hmultAE :
      AEMeasurable
        (preimageMultiplicity f (Metric.ball z r)) volume :=
    hW.aemeasurable_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hLusin hJuniv Metric.isOpen_ball.measurableSet
      (Set.subset_univ _)
  have hdfClosed :
      MemLp df 2
        (volume.restrict (Metric.closedBall z r)) :=
    (hW.2.2 (Metric.closedBall z r)
      (isCompact_closedBall z r) (Set.subset_univ _)).2
  have hdfBall :
      MemLp df 2
        (volume.restrict (Metric.ball z r)) :=
    hdfClosed.mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hJint :
      Integrable (fun x ↦ weakJacobian (df x))
        (volume.restrict (Metric.ball z r)) :=
    weakJacobian_integrable_of_memLp_two hdfBall
  have harea :=
    hW.boundedDistortion_areaFormula_preimageMultiplicity
      hf hK hdist (S := Metric.ball z r)
      Metric.isOpen_ball.measurableSet
      (fun _ ↦ (1 : ℝ≥0∞)) measurable_const.aemeasurable
  have hlintegral_ne_top :
      (∫⁻ y,
        preimageMultiplicity f (Metric.ball z r) y ∂volume) ≠ ∞ := by
    have harea' :
        (∫⁻ y,
          preimageMultiplicity f (Metric.ball z r) y ∂volume) =
          ∫⁻ x in Metric.ball z r,
            ENNReal.ofReal (weakJacobian (df x)) ∂volume := by
      simpa using harea
    have hsource_ne_top :
        (∫⁻ x in Metric.ball z r,
          ENNReal.ofReal (weakJacobian (df x)) ∂volume) ≠ ∞ :=
      hJint.lintegral_lt_top.ne
    exact harea'.trans_ne hsource_ne_top
  have hfinite :
      ∀ᵐ y ∂volume,
        preimageMultiplicity f (Metric.ball z r) y < ∞ :=
    ae_lt_top' hmultAE hlintegral_ne_top
  filter_upwards [hreal, hfinite] with y hyreal hyfinite
  intro hyball
  calc
    preimageMultiplicity f (Metric.ball z r) y =
        ENNReal.ofReal
          (preimageMultiplicity f (Metric.ball z r) y).toReal :=
      (ENNReal.ofReal_toReal hyfinite.ne).symm
    _ =
        ENNReal.ofReal
          (planarCircleIndex f hf z w r hr havoid : ℝ) := by
      rw [hyreal hyball]

/--
%%handwave
name:
  Images of circles under maps of bounded distortion are null
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. For every $z\in\mathbb C$ and every $r>0$,
  $$
    \bigl|f(\partial B(z,r))\bigr|=0.
  $$
proof:
  Every Euclidean circle has planar measure zero, and [maps of bounded distortion have the Lusin property](lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_hasLusinNOn).
-/
theorem IsLocalW12On.boundedDistortion_volume_image_sphere_eq_zero
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ x ∂(volume : Measure ℂ),
      ‖df x‖ ^ 2 ≤ K * weakJacobian (df x))
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    volume (f '' Metric.sphere z r) = 0 := by
  apply hW.boundedDistortion_hasLusinNOn hf hK hdist
    (Metric.sphere z r) (Set.subset_univ _)
  exact JJMath.Uniformization.euclidean_volume_sphere_zero hr

/--
%%handwave
name:
  Nonnegative boundary degree for maps of bounded distortion
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. If $r>0$ and $w\notin f(\partial B(z,r))$, then
  $$
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)\geq0.
  $$
proof:
  Compactness of the boundary loop gives a positive target ball about $w$
  disjoint from its image. On that ball, [multiplicity agrees almost everywhere with the boundary index](lean:JJMath.Quasiconformal.IsLocalW12On.eventually_preimageMultiplicity_toReal_eq_planarCircleIndex_of_boundedDistortion). Since the ball has positive measure, choose one target where equality holds. Multiplicity is nonnegative there, so the constant boundary index is nonnegative.
-/
theorem IsLocalW12On.planarCircleIndex_nonneg_of_boundedDistortion
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ x ∂(volume : Measure ℂ),
      ‖df x‖ ^ 2 ≤ K * weakJacobian (df x))
    (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (havoid : ∀ t, imageCircleLoop f hf z r t ≠ w) :
    0 ≤ planarCircleIndex f hf z w r hr havoid := by
  let C : Set ℂ := Set.range (imageCircleLoop f hf z r)
  have hCcompact : IsCompact C := by
    exact isCompact_range (imageCircleLoop f hf z r).continuous
  have hCnonempty : C.Nonempty :=
    Set.range_nonempty _
  have hwC : w ∉ C := by
    rintro ⟨t, ht⟩
    exact havoid t ht
  let ε : ℝ := Metric.infDist w C
  have hε : 0 < ε := by
    exact
      (hCcompact.isClosed.notMem_iff_infDist_pos hCnonempty).1 hwC
  have hsep :
      ∀ t, ε ≤ ‖imageCircleLoop f hf z r t - w‖ := by
    intro t
    have hle :
        ε ≤ dist w (imageCircleLoop f hf z r t) := by
      exact Metric.infDist_le_dist_of_mem ⟨t, rfl⟩
    simpa [Complex.dist_eq, norm_sub_rev] using hle
  have hae :=
    hW.eventually_preimageMultiplicity_toReal_eq_planarCircleIndex_of_boundedDistortion
      hf hK hdist z w hr hε havoid hsep
  have haeBall :
      ∀ᵐ y ∂volume.restrict (Metric.ball w ε),
        (preimageMultiplicity f (Metric.ball z r) y).toReal =
          (planarCircleIndex f hf z w r hr havoid : ℝ) := by
    filter_upwards
        [ae_restrict_of_ae hae,
          ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hyball
    exact hy hyball
  obtain ⟨y, _hyball, hy⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (ne_of_gt (Metric.measure_ball_pos volume w hε)) haeBall
  have hreal :
      (0 : ℝ) ≤
        (planarCircleIndex f hf z w r hr havoid : ℝ) := by
    rw [← hy]
    exact ENNReal.toReal_nonneg
  exact_mod_cast hreal

/--
%%handwave
name:
  Pullback energy inequality with multiplicity
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. For every measurable $S\subseteq\mathbb C$ and every measurable
  field $a(y):\mathbb C\to_{\mathbb R}\mathbb R$,
  $$
    \int_S\lVert a(f(x))\circ Df(x)\rVert^2\,dx
      \leq
    K\int_{\mathbb C}
      N(f,S,y)\lVert a(y)\rVert^2\,dy.
  $$
proof:
  Pointwise submultiplicativity and the distortion inequality bound the source integrand by $KJ_f(x)\lVert a(f(x))\rVert^2$. Integrate and apply [the multiplicity area formula for maps of bounded distortion](lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_areaFormula_preimageMultiplicity).
-/
theorem IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_multiplicity
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (a : ℂ → ℂ →L[ℝ] ℝ)
    (ha :
      AEMeasurable
        (fun y =>
          ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)))
        volume) :
    (∫⁻ x in S,
        ENNReal.ofReal
          (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ))
          ∂volume) ≤
      ENNReal.ofReal K *
        ∫⁻ y,
          preimageMultiplicity f S y *
            ENNReal.ofReal
              (‖a y‖ ^ (2 : ℕ)) ∂volume := by
  have hKnonneg : 0 ≤ K :=
    le_trans zero_le_one hK
  have hJnonneg :=
    (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
      hK hdist).1
  have hpoint :
      ∀ᵐ x ∂volume.restrict S,
        ENNReal.ofReal
            (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ)) ≤
          ENNReal.ofReal K *
            (ENNReal.ofReal
                (weakJacobian (df x)) *
              ENNReal.ofReal
                (‖a (f x)‖ ^ (2 : ℕ))) := by
    filter_upwards
        [ae_restrict_of_ae hdist,
          ae_restrict_of_ae hJnonneg] with x hdistx hJx
    have hcomp :=
      (a (f x)).opNorm_comp_le (df x)
    have hsq :
        ‖(a (f x)).comp (df x)‖ ^ (2 : ℕ) ≤
          ‖a (f x)‖ ^ (2 : ℕ) *
            ‖df x‖ ^ (2 : ℕ) := by
      calc
        ‖(a (f x)).comp (df x)‖ ^ (2 : ℕ) =
            ‖(a (f x)).comp (df x)‖ *
              ‖(a (f x)).comp (df x)‖ := by
          ring
        _ ≤
            (‖a (f x)‖ * ‖df x‖) *
              (‖a (f x)‖ * ‖df x‖) :=
          mul_self_le_mul_self
            (norm_nonneg _) hcomp
        _ =
            ‖a (f x)‖ ^ (2 : ℕ) *
              ‖df x‖ ^ (2 : ℕ) := by
          ring
    have hreal :
        ‖(a (f x)).comp (df x)‖ ^ (2 : ℕ) ≤
          K * weakJacobian (df x) *
            ‖a (f x)‖ ^ (2 : ℕ) := by
      calc
        ‖(a (f x)).comp (df x)‖ ^ (2 : ℕ) ≤
            ‖a (f x)‖ ^ (2 : ℕ) *
              ‖df x‖ ^ (2 : ℕ) :=
          hsq
        _ ≤
            ‖a (f x)‖ ^ (2 : ℕ) *
              (K * weakJacobian (df x)) := by
          exact mul_le_mul_of_nonneg_left
            hdistx (sq_nonneg _)
        _ =
            K * weakJacobian (df x) *
              ‖a (f x)‖ ^ (2 : ℕ) := by
          ring
    calc
      ENNReal.ofReal
          (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ)) ≤
          ENNReal.ofReal
            (K * weakJacobian (df x) *
              ‖a (f x)‖ ^ (2 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ =
          ENNReal.ofReal K *
            (ENNReal.ofReal
                (weakJacobian (df x)) *
              ENNReal.ofReal
                (‖a (f x)‖ ^ (2 : ℕ))) := by
        rw [show
            K * weakJacobian (df x) *
                ‖a (f x)‖ ^ (2 : ℕ) =
              K * (weakJacobian (df x) *
                ‖a (f x)‖ ^ (2 : ℕ)) by
              ring,
          ENNReal.ofReal_mul hKnonneg,
          ENNReal.ofReal_mul hJx]
  calc
    (∫⁻ x in S,
        ENNReal.ofReal
          (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ))
          ∂volume) ≤
        ∫⁻ x in S,
          ENNReal.ofReal K *
            (ENNReal.ofReal
                (weakJacobian (df x)) *
              ENNReal.ofReal
                (‖a (f x)‖ ^ (2 : ℕ)))
          ∂volume :=
      lintegral_mono_ae hpoint
    _ =
        ENNReal.ofReal K *
          ∫⁻ x in S,
            ENNReal.ofReal
                (weakJacobian (df x)) *
              ENNReal.ofReal
                (‖a (f x)‖ ^ (2 : ℕ))
            ∂volume := by
      rw [lintegral_const_mul'
        _ _ ENNReal.ofReal_ne_top]
    _ =
        ENNReal.ofReal K *
          ∫⁻ y,
            preimageMultiplicity f S y *
              ENNReal.ofReal
                (‖a y‖ ^ (2 : ℕ))
            ∂volume := by
      rw [← hW.boundedDistortion_areaFormula_preimageMultiplicity
        hf hK hdist hSmeas
          (fun y =>
            ENNReal.ofReal
              (‖a y‖ ^ (2 : ℕ))) ha]

/--
%%handwave
name:
  Pullback energy under a multiplicity bound on the field support
statement:
  Under the hypotheses of the pullback energy inequality, let
  $a(y):\mathbb C\to_{\mathbb R}\mathbb R$ vanish outside $U$. If
  $N(f,S,y)\leq M<\infty$ for almost every $y\in U$, then
  $$
    \int_S\lVert a(f(x))\circ Df(x)\rVert^2\,dx
      \leq
    KM\int_{\mathbb C}\lVert a(y)\rVert^2\,dy.
  $$
proof:
  Apply [the pullback energy inequality with multiplicity](lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_multiplicity). On $U$ use the assumed multiplicity bound; outside $U$ the target energy density is zero. Move the finite constant $M$ outside the target integral.
-/
theorem IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_of_multiplicity_le_on
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (a : ℂ → ℂ →L[ℝ] ℝ)
    (ha :
      AEMeasurable
        (fun y =>
          ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)))
        volume)
    {U : Set ℂ}
    (ha_zero : ∀ y ∉ U, a y = 0)
    (M : ℝ≥0∞)
    (hMtop : M ≠ ∞)
    (hM :
      ∀ᵐ y ∂volume,
        y ∈ U →
          preimageMultiplicity f S y ≤ M) :
    (∫⁻ x in S,
        ENNReal.ofReal
          (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ))
          ∂volume) ≤
      ENNReal.ofReal K *
        (M *
          ∫⁻ y,
            ENNReal.ofReal
              (‖a y‖ ^ (2 : ℕ)) ∂volume) := by
  calc
    (∫⁻ x in S,
        ENNReal.ofReal
          (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ))
          ∂volume) ≤
        ENNReal.ofReal K *
          ∫⁻ y,
            preimageMultiplicity f S y *
              ENNReal.ofReal
                (‖a y‖ ^ (2 : ℕ))
            ∂volume :=
      hW.boundedDistortion_lintegral_norm_comp_sq_le_multiplicity
        hf hK hdist hSmeas a ha
    _ ≤
        ENNReal.ofReal K *
          ∫⁻ y,
            M *
              ENNReal.ofReal
                (‖a y‖ ^ (2 : ℕ))
            ∂volume := by
      apply mul_le_mul_left'
      apply lintegral_mono_ae
      filter_upwards [hM] with y hy
      by_cases hyU : y ∈ U
      · exact mul_le_mul_right' (hy hyU) _
      · simp [ha_zero y hyU]
    _ =
        ENNReal.ofReal K *
          (M *
            ∫⁻ y,
              ENNReal.ofReal
                (‖a y‖ ^ (2 : ℕ))
              ∂volume) := by
      rw [lintegral_const_mul' _ _ hMtop]

/--
%%handwave
name:
  Protected disk pullback energy bound
statement:
  Let $f:\mathbb C\to\mathbb C$ have bounded distortion, and suppose the
  image of $\partial B(z,r)$ stays at distance at least $\varepsilon>0$ from
  $w$. If a measurable covector field $a$ vanishes outside
  $B(w,\varepsilon)$, then
  $$
    \int_{B(z,r)}\lVert a(f(x))\circ Df(x)\rVert^2\,dx
      \leq
    K\,\operatorname{ofReal}\!\left(
      \operatorname{ind}(f|_{\partial B(z,r)},w)\right)
      \int_{\mathbb C}\lVert a(y)\rVert^2\,dy.
  $$
proof:
  [Extended multiplicity equals the nonnegative disk index almost everywhere in the protected ball](lean:JJMath.Quasiconformal.IsLocalW12On.eventually_preimageMultiplicity_eq_ofReal_planarCircleIndex_of_boundedDistortion). Apply [the pullback estimate whose multiplicity bound is required only on the support of the covector field](lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_of_multiplicity_le_on).
-/
theorem IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_planarCircleIndex
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (z w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (havoid : ∀ t, imageCircleLoop f hf z r t ≠ w)
    (hsep : ∀ t, ε ≤ ‖imageCircleLoop f hf z r t - w‖)
    (a : ℂ → ℂ →L[ℝ] ℝ)
    (ha :
      AEMeasurable
        (fun y =>
          ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)))
        volume)
    (ha_zero : ∀ y ∉ Metric.ball w ε, a y = 0) :
    (∫⁻ x in Metric.ball z r,
        ENNReal.ofReal
          (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ))
          ∂volume) ≤
      ENNReal.ofReal K *
        (ENNReal.ofReal
            (planarCircleIndex f hf z w r hr havoid : ℝ) *
          ∫⁻ y,
            ENNReal.ofReal
              (‖a y‖ ^ (2 : ℕ)) ∂volume) := by
  apply
    hW.boundedDistortion_lintegral_norm_comp_sq_le_of_multiplicity_le_on
      hf hK hdist Metric.isOpen_ball.measurableSet a ha
      ha_zero
      (ENNReal.ofReal
        (planarCircleIndex f hf z w r hr havoid : ℝ))
      ENNReal.ofReal_ne_top
  have heq :=
    hW.eventually_preimageMultiplicity_eq_ofReal_planarCircleIndex_of_boundedDistortion
      hf hK hdist z w hr hε havoid hsep
  filter_upwards [heq] with y hy
  intro hyball
  exact (hy hyball).le

/--
%%handwave
name:
  Pullback energy under a finite multiplicity bound
statement:
  Under the hypotheses of the pullback energy inequality, suppose additionally
  that $N(f,S,y)\leq M<\infty$ for almost every $y$. Then
  $$
    \int_S\lVert a(f(x))\circ Df(x)\rVert^2\,dx
      \leq
    KM\int_{\mathbb C}\lVert a(y)\rVert^2\,dy.
  $$
proof:
  Apply [the pullback energy inequality with multiplicity](lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_multiplicity), use the almost-everywhere bound $N(f,S,\cdot)\leq M$, and move the finite constant $M$ outside the target integral.
-/
theorem IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_of_multiplicity_le
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (a : ℂ → ℂ →L[ℝ] ℝ)
    (ha :
      AEMeasurable
        (fun y =>
          ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)))
        volume)
    (M : ℝ≥0∞)
    (hMtop : M ≠ ∞)
    (hM :
      ∀ᵐ y ∂volume,
        preimageMultiplicity f S y ≤ M) :
    (∫⁻ x in S,
        ENNReal.ofReal
          (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ))
          ∂volume) ≤
      ENNReal.ofReal K *
        (M *
          ∫⁻ y,
            ENNReal.ofReal
              (‖a y‖ ^ (2 : ℕ)) ∂volume) := by
  calc
    (∫⁻ x in S,
        ENNReal.ofReal
          (‖(a (f x)).comp (df x)‖ ^ (2 : ℕ))
          ∂volume) ≤
        ENNReal.ofReal K *
          ∫⁻ y,
            preimageMultiplicity f S y *
              ENNReal.ofReal
                (‖a y‖ ^ (2 : ℕ))
            ∂volume :=
      hW.boundedDistortion_lintegral_norm_comp_sq_le_multiplicity
        hf hK hdist hSmeas a ha
    _ ≤
        ENNReal.ofReal K *
          ∫⁻ y,
            M *
              ENNReal.ofReal
                (‖a y‖ ^ (2 : ℕ))
            ∂volume := by
      apply mul_le_mul_left'
      apply lintegral_mono_ae
      filter_upwards [hM] with y hy
      exact mul_le_mul_right' hy _
    _ =
        ENNReal.ofReal K *
          (M *
            ∫⁻ y,
              ENNReal.ofReal
                (‖a y‖ ^ (2 : ℕ))
              ∂volume) := by
      rw [lintegral_const_mul' _ _ hMtop]

/--
%%handwave
name:
  Compact continua in fibers of proper bounded-distortion maps are points
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, proper, and locally
  $W^{1,2}$, with weak differential $Df$. Suppose $K\geq1$ and
  $$
    \lVert Df(z)\rVert_{\mathrm{op}}^2\leq KJ_f(z)
  $$
  almost everywhere. If a compact connected set $E$ is contained in one
  fiber $f^{-1}(w)$, then $E$ is a singleton or empty.
proof:
  If $E$ were nontrivial, compare it with a closed unbounded source ray
  outside the proper inverse image of $\overline B(w,2)$. Their condenser
  capacity is positive. Composing $f$ with smooth logarithmic cutoffs around
  $w$ gives admissible competitors for this fixed condenser. The
  [protected pullback estimate](lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_planarCircleIndex)
  bounds their energies by a fixed boundary degree times
  $O(1/\log(1/r))$, which tends to zero as $r\downarrow0$, contradicting
  the positive capacity.
-/
theorem IsLocalW12On.compact_connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (hproper : IsProperMap f)
    (w : ℂ) {E : Set ℂ}
    (hEcompact : IsCompact E)
    (hEconnected : IsConnected E)
    (hEfiber : E ⊆ {x : ℂ | f x = w}) :
    E.Subsingleton := by
  by_contra hnot
  have hEnontrivial : E.Nontrivial :=
    Set.not_subsingleton_iff.mp hnot
  let P : Set ℂ := f ⁻¹' Metric.closedBall w 2
  have hPcompact : IsCompact P :=
    hproper.isCompact_preimage (isCompact_closedBall w 2)
  obtain ⟨R, hPR⟩ :=
    hPcompact.isBounded.subset_ball (0 : ℂ)
  obtain ⟨x, hxE⟩ := hEconnected.nonempty
  have hxP : x ∈ P := by
    change f x ∈ Metric.closedBall w 2
    rw [hEfiber hxE]
    simp
  have hxball := hPR hxP
  have hR : 0 < R := by
    rw [Metric.mem_ball, dist_zero_right] at hxball
    exact (norm_nonneg x).trans_lt hxball
  have hRcomplex : (R : ℂ) ≠ 0 := by
    exact_mod_cast hR.ne'
  let T : ℂ ≃ₜ ℂ :=
    Homeomorph.mulLeft₀ (R : ℂ) hRcomplex
  let E₁ : Set ℂ := T '' planarUnitRay
  have hE₁closed : IsClosed E₁ :=
    T.isClosedMap _ planarUnitRay_properties.1
  have hE₁connected : IsConnected E₁ :=
    planarUnitRay_properties.2.1.image T T.continuous.continuousOn
  have hE₁unbounded : ∀ S : ℝ, ∃ z ∈ E₁, S ≤ ‖z‖ :=
    Homeomorph.image_unbounded T planarUnitRay_properties.2.2.2
  have hE₁norm : ∀ z ∈ E₁, R ≤ ‖z‖ := by
    rintro z ⟨u, ⟨t, ht, rfl⟩, rfl⟩
    have ht1 : 1 ≤ t := ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht1
    simp only [T, Homeomorph.coe_mulLeft₀, Complex.norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      Complex.norm_real, abs_of_nonneg ht0]
    nlinarith
  have hEPE₁ : Disjoint E E₁ := by
    rw [Set.disjoint_left]
    intro z hzE hzE₁
    have hzP : z ∈ P := by
      change f z ∈ Metric.closedBall w 2
      rw [hEfiber hzE]
      simp
    have hzball := hPR hzP
    rw [Metric.mem_ball, dist_zero_right] at hzball
    exact (not_lt_of_ge (hE₁norm z hzE₁)) hzball
  have hcap :
      0 < planarCondenserCapacity Set.univ E E₁ :=
    planarCondenserCapacity_pos_of_compact_nontrivial_continuum_of_unbounded_continuum
      hEcompact hEconnected hEnontrivial hE₁closed hE₁connected
      hE₁unbounded hEPE₁
  have hsep :
      ∀ t, 2 ≤ ‖imageCircleLoop f hf 0 R t - w‖ := by
    intro t
    have hnotP :
        circlePoint 0 R t ∉ f ⁻¹' Metric.closedBall w 2 := by
      intro htP
      have htball := hPR htP
      rw [Metric.mem_ball, dist_circlePoint_center 0 hR t] at htball
      exact (lt_irrefl R) htball
    have hnotclosed :
        f (circlePoint 0 R t) ∉ Metric.closedBall w 2 := hnotP
    have hlt : 2 < dist (f (circlePoint 0 R t)) w := by
      simpa [Metric.mem_closedBall] using hnotclosed
    simpa [imageCircleLoop, Complex.dist_eq] using hlt.le
  have havoid :
      ∀ t, imageCircleLoop f hf 0 R t ≠ w := by
    intro t ht
    have htsep := hsep t
    rw [ht, sub_self, norm_zero] at htsep
    norm_num at htsep
  let d : ℤ :=
    planarCircleIndex f hf 0 w R hR havoid
  obtain ⟨C, hC0, hC⟩ :=
    exists_smoothTransition_fderiv_norm_bound
  let A : ℝ≥0∞ :=
    (ENNReal.ofReal K * ENNReal.ofReal (d : ℝ)) *
      ENNReal.ofReal (C ^ (2 : ℕ))
  have hAtop : A ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hvanish :
      Filter.Tendsto
        (fun n : ℕ ↦
          A * planarRingCapacity (Real.exp (-(n : ℝ))) 1)
        Filter.atTop (nhds 0) := by
    simpa using
      ENNReal.Tendsto.const_mul
        tendsto_planarRingCapacity_exp_neg_nat (Or.inr hAtop)
  have heventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        A * planarRingCapacity (Real.exp (-(n : ℝ))) 1 <
          planarCondenserCapacity Set.univ E E₁ :=
    hvanish (Iio_mem_nhds hcap)
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨N, hN⟩ := heventually
  let n : ℕ := max N 1
  have hn : 1 ≤ n :=
    le_max_right _ _
  have hsmall :
      A * planarRingCapacity (Real.exp (-(n : ℝ))) 1 <
        planarCondenserCapacity Set.univ E E₁ :=
    hN n (le_max_left _ _)
  let r : ℝ := Real.exp (-(n : ℝ))
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hr : 0 < r :=
    Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  let a : ℂ → ℂ →L[ℝ] ℝ := fun y ↦
    fderiv ℝ (planarSmoothLogRingCutoffAt w r 1) y
  have ha :
      AEMeasurable
        (fun y =>
          ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)))
        volume := by
    exact
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((measurable_fderiv ℝ
          (planarSmoothLogRingCutoffAt w r 1)).norm.pow_const 2).aemeasurable)
  have ha_zero : ∀ y ∉ Metric.ball w 2, a y = 0 := by
    intro y hy
    dsimp [a]
    rw [fderiv_planarSmoothLogRingCutoffAt hr hr1]
    apply
      fderiv_planarSmoothLogRingCutoff_eq_zero_of_lt_norm hr hr1
    have htwo : 2 ≤ dist y w := by
      simpa [Metric.mem_ball] using hy
    rw [Complex.dist_eq] at htwo
    linarith
  have houtside :
      ∀ z ∉ Metric.ball 0 R, 2 < ‖f z - w‖ := by
    intro z hz
    have hznotP : z ∉ P := by
      intro hzP
      exact hz (hPR hzP)
    have hnotclosed : f z ∉ Metric.closedBall w 2 := hznotP
    have hlt : 2 < dist (f z) w := by
      simpa [Metric.mem_closedBall] using hnotclosed
    simpa [Complex.dist_eq] using hlt
  let u : PlanarCondenserCompetitor Set.univ E E₁ := {
    toFun := fun z ↦ planarSmoothLogRingCutoffAt w r 1 (f z)
    weakDifferential := fun z ↦ (a (f z)).comp (df z)
    zeroPlate_subset := Set.subset_univ _
    onePlate_subset := Set.subset_univ _
    isLocalW12 := by
      simpa [a] using
        hW.postcomp_planarSmoothLogRingCutoffAt w hr hr1
    continuousOn :=
      ((planarSmoothLogRingCutoffAt_contDiff hr hr1).continuous.comp
        hf).continuousOn
    eq_zero_on := by
      intro z hzE
      apply planarSmoothLogRingCutoffAt_eq_zero_of_norm_sub_le
      rw [hEfiber hzE, sub_self, norm_zero]
      exact hr.le
    eq_one_on := by
      intro z hzE₁
      apply
        planarSmoothLogRingCutoffAt_eq_one_of_le_norm_sub hr hr1
      have hzout : z ∉ Metric.ball 0 R := by
        simpa [Metric.mem_ball, dist_zero_right] using
          not_lt_of_ge (hE₁norm z hzE₁)
      linarith [houtside z hzout]
    }
  let e : ℂ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (‖(a (f z)).comp (df z)‖ ^ (2 : ℕ))
  have hesupport :
      Function.support e ⊆ Metric.ball 0 R := by
    intro z hz
    by_contra hzball
    have hfnotball : f z ∉ Metric.ball w 2 := by
      intro hfball
      exact hzball (hPR (Metric.ball_subset_closedBall hfball))
    have hazero : a (f z) = 0 :=
      ha_zero _ hfnotball
    have hcomp : (a (f z)).comp (df z) = 0 := by
      rw [hazero]
      ext v
      simp
    apply hz
    rw [show e z =
        ENNReal.ofReal (‖(a (f z)).comp (df z)‖ ^ (2 : ℕ)) by
      rfl, hcomp]
    simp
  have hsetIntegral :=
    MeasureTheory.setLIntegral_eq_of_support_subset
      (μ := volume) hesupport
  have huEnergy :
      u.dirichletEnergy =
        ∫⁻ z in Metric.ball 0 R,
          ENNReal.ofReal
            (‖(a (f z)).comp (df z)‖ ^ (2 : ℕ))
          ∂volume := by
    simpa [PlanarCondenserCompetitor.dirichletEnergy, u, e] using
      hsetIntegral.symm
  have hpull :=
    hW.boundedDistortion_lintegral_norm_comp_sq_le_planarCircleIndex
      hf hK hdist 0 w hR (by norm_num : (0 : ℝ) < 2)
      havoid hsep a ha ha_zero
  have htarget :
      (∫⁻ y : ℂ,
          ENNReal.ofReal (‖a y‖ ^ (2 : ℕ))
          ∂volume) ≤
        ENNReal.ofReal (C ^ (2 : ℕ)) *
          planarRingCapacity r 1 := by
    have henergy :=
      lintegral_norm_fderiv_planarSmoothLogRingCutoffAt_sq_le
        (w := w) hr hr1 hC0 hC
    rw [← planarRingCapacity_eq_logarithmicEnergy hr hr1] at henergy
    simpa [a] using henergy
  have hcontra :
      planarCondenserCapacity Set.univ E E₁ <
        planarCondenserCapacity Set.univ E E₁ := by
    calc
      planarCondenserCapacity Set.univ E E₁ ≤
          u.dirichletEnergy :=
        planarCondenserCapacity_le_dirichletEnergy u
      _ =
          ∫⁻ z in Metric.ball 0 R,
            ENNReal.ofReal
              (‖(a (f z)).comp (df z)‖ ^ (2 : ℕ))
            ∂volume := huEnergy
      _ ≤
          ENNReal.ofReal K *
            (ENNReal.ofReal (d : ℝ) *
              ∫⁻ y : ℂ,
                ENNReal.ofReal (‖a y‖ ^ (2 : ℕ))
                ∂volume) := by
        simpa [d] using hpull
      _ ≤
          ENNReal.ofReal K *
            (ENNReal.ofReal (d : ℝ) *
              (ENNReal.ofReal (C ^ (2 : ℕ)) *
                planarRingCapacity r 1)) := by
        gcongr
      _ =
          A * planarRingCapacity r 1 := by
        simp [A, mul_assoc]
      _ <
          planarCondenserCapacity Set.univ E E₁ := by
        simpa [r] using hsmall
  exact (lt_irrefl _ hcontra)

/--
%%handwave
name:
  A light planar map admits a degree cutoff over a target ball
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and light, let $f(x)=w$, and
  let $U$ be an open neighborhood of $x$. There are a smooth compactly
  supported function $\chi:\mathbb C\to\mathbb R$ and $r>0$ such that
  $$
    \chi(x)=1,\qquad
    \operatorname{supp}\chi\subseteq U,\qquad
    D\chi(z)=0\quad\text{whenever }|f(z)-w|\leq r.
  $$
proof:
  Choose [a normal source domain whose boundary image stays outside a target
  ball](lean:JJMath.Quasiconformal.exists_normalSourceDomain_of_light). The
  part of the closed-ball preimage in the closure of that domain is compact
  and, by the boundary separation, lies in its interior. Choose a smooth
  cutoff equal to one on this compact set and supported in the normal
  domain. Over the target ball, every point is either in the compact
  one-set or outside the cutoff support, so the cutoff differential
  vanishes.
-/
theorem exists_degreeCutoff_of_light
    {f : ℂ → ℂ} (hf : Continuous f)
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton)
    {x w : ℂ} (hxw : f x = w)
    {U : Set ℂ} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ χ :
        JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
          (Set.univ : Set ℂ),
      ∃ r : ℝ, 0 < r ∧ χ x = 1 ∧
        tsupport (χ : ℂ → ℝ) ⊆ U ∧
        ∀ z, dist (f z) w ≤ r →
          fderiv ℝ (χ : ℂ → ℝ) z = 0 := by
  obtain ⟨W, r, hWopen, _hWconnected, hxW,
      hWclosureU, hWcompact, hr, hWseparated⟩ :=
    exists_normalSourceDomain_of_light
      hf hlight hxw hU hxU
  let K : Set ℂ :=
    closure W ∩ f ⁻¹' Metric.closedBall w r
  have hKcompact : IsCompact K :=
    hWcompact.inter_right
      (Metric.isClosed_closedBall.preimage hf)
  have hKsubW : K ⊆ W := by
    intro z hzK
    by_contra hzW
    have hzfront : z ∈ frontier W :=
      ⟨hzK.1, fun hzInterior =>
        hzW (interior_subset hzInterior)⟩
    exact
      (not_lt_of_ge
        (Metric.mem_closedBall.mp hzK.2))
        (hWseparated z hzfront)
  obtain ⟨χ⟩ :=
    JJMath.Uniformization.exists_scalarWeakSobolevCutoff
      hKcompact hKsubW hWopen
  let χ' :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ) :=
    { toFun := χ
      smooth := χ.smooth
      support_subset := Set.subset_univ _
      compact_support := χ.compact_support }
  refine ⟨χ', r, hr, ?_, ?_, ?_⟩
  · exact χ.eq_one_on x
      ⟨subset_closure hxW, by
        change dist (f x) w ≤ r
        rw [hxw, dist_self]
        exact hr.le⟩
  · exact χ.support_subset.trans
      (subset_closure.trans hWclosureU)
  · intro z hz
    by_cases hzK : z ∈ K
    · exact χ.fderiv_eq_zero_on z hzK
    · have hzsupport :
          z ∉ tsupport (χ : ℂ → ℝ) := by
        intro hzsupport
        apply hzK
        exact
          ⟨subset_closure
              (χ.support_subset hzsupport),
            Metric.mem_closedBall.mpr hz⟩
      exact
        fderiv_of_notMem_tsupport
          (𝕜 := ℝ) (f := (χ : ℂ → ℝ))
          hzsupport

/--
%%handwave
name:
  Continuous planar Sobolev maps with zero differential are constant
statement:
  Let $\Omega\subseteq\mathbb C$ be open and connected, and let
  $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ be continuous on
  $\Omega$. If $Df=0$ almost everywhere on $\Omega$, then there is
  $a\in\mathbb C$ such that $f=a$ throughout $\Omega$.
proof:
  Apply the scalar Sobolev zero-gradient theorem to the real and imaginary
  parts of $f$. They are almost everywhere constant, hence so is $f$.
  Continuity upgrades the almost-everywhere equality to pointwise equality
  on the open set.
-/
theorem IsLocalW12On.eqOn_const_of_differential_eq_zero_ae
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hΩpre : IsPreconnected Ω)
    (hf : ContinuousOn f Ω)
    (hdfzero : ∀ᵐ z ∂volume.restrict Ω, df z = 0) :
    ∃ a : ℂ, EqOn f (fun _ ↦ a) Ω := by
  have hre := hW.re
  have him := hW.im
  have hdrezero :
      ∀ᵐ z ∂volume.restrict Ω,
        Complex.reCLM.comp (df z) = 0 := by
    filter_upwards [hdfzero] with z hz
    simp [hz]
  have hdimezero :
      ∀ᵐ z ∂volume.restrict Ω,
        Complex.imCLM.comp (df z) = 0 := by
    filter_upwards [hdfzero] with z hz
    simp [hz]
  obtain ⟨a, ha⟩ :=
    JJMath.Uniformization.euclideanSobolev_zero_gradient_constant_on_preconnected_finiteDimensional
      hre.1 hΩpre hre.2.1 hre.2.2 hdrezero
  obtain ⟨b, hb⟩ :=
    JJMath.Uniformization.euclideanSobolev_zero_gradient_constant_on_preconnected_finiteDimensional
      him.1 hΩpre him.2.1 him.2.2 hdimezero
  let c : ℂ := ⟨a, b⟩
  have hae :
      f =ᵐ[volume.restrict Ω] (fun _ : ℂ ↦ c) := by
    filter_upwards [ha, hb] with z hza hzb
    apply Complex.ext
    · simpa [c] using hza
    · simpa [c] using hzb
  exact
    ⟨c,
      Measure.eqOn_open_of_ae_eq hae hW.1 hf
        continuousOn_const⟩

/--
%%handwave
name:
  Light maps of bounded distortion have positive Jacobian mass on balls
statement:
  Let $f:\mathbb C\to\mathbb C$ be a continuous light map in
  $W^{1,2}_{\mathrm{loc}}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. Then every ball $B(x,\delta)$ with $\delta>0$ satisfies
  $$
    \int_{B(x,\delta)}J_f(z)\,dz>0.
  $$
proof:
  The Jacobian is nonnegative. If its integral on a ball vanished, then
  $J_f=0$ almost everywhere there, and bounded distortion would force
  $Df=0$ almost everywhere. By [continuous zero-differential rigidity](lean:JJMath.Quasiconformal.IsLocalW12On.eqOn_const_of_differential_eq_zero_ae), $f$ would be constant on the ball. The ball is a nontrivial connected subset of a point fiber, contradicting lightness.
-/
theorem IsLocalW12On.integral_weakJacobian_pos_on_ball_of_boundedDistortion_of_light
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton)
    (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    0 < ∫ z in Metric.ball x δ,
      weakJacobian (df z) ∂volume := by
  have hclosedCompact : IsCompact (Metric.closedBall x δ) :=
    isCompact_closedBall x δ
  have hJclosed :
      Integrable (fun z ↦ weakJacobian (df z))
        (volume.restrict (Metric.closedBall x δ)) :=
    weakJacobian_integrable_of_memLp_two
      (hW.2.2 (Metric.closedBall x δ) hclosedCompact
        (Set.subset_univ _)).2
  have hJball :
      Integrable (fun z ↦ weakJacobian (df z))
        (volume.restrict (Metric.ball x δ)) :=
    hJclosed.mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hJnonneg :
      ∀ᵐ z ∂volume.restrict (Metric.ball x δ),
        0 ≤ weakJacobian (df z) :=
    ae_restrict_of_ae
      (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
        hK hdist).1
  have hintnonneg :
      0 ≤ ∫ z in Metric.ball x δ,
        weakJacobian (df z) ∂volume :=
    integral_nonneg_of_ae hJnonneg
  apply lt_of_le_of_ne hintnonneg
  intro hintzero
  have hJzero :
      ∀ᵐ z ∂volume.restrict (Metric.ball x δ),
        weakJacobian (df z) = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hJnonneg hJball).1
      hintzero.symm
  have hzeroBranch :
      ∀ᵐ z ∂volume.restrict (Metric.ball x δ),
        weakJacobian (df z) = 0 → df z = 0 :=
    ae_restrict_of_ae
      (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
        hK hdist).2
  have hdfzero :
      ∀ᵐ z ∂volume.restrict (Metric.ball x δ), df z = 0 := by
    filter_upwards [hJzero, hzeroBranch] with z hz hbranch
    exact hbranch hz
  have hWball :
      IsLocalW12On (Metric.ball x δ) f df :=
    hW.mono Metric.isOpen_ball (Set.subset_univ _)
  obtain ⟨a, ha⟩ :=
    hWball.eqOn_const_of_differential_eq_zero_ae
      (Metric.isConnected_ball hδ).isPreconnected
      hf.continuousOn hdfzero
  have hxball : x ∈ Metric.ball x δ :=
    Metric.mem_ball_self hδ
  have hfiber :
      Metric.ball x δ ⊆ {z : ℂ | f z = f x} := by
    intro z hz
    change f z = f x
    rw [ha hz, ha hxball]
  have hsub :
      (Metric.ball x δ).Subsingleton :=
    hlight (f x) (Metric.ball x δ)
      (Metric.isConnected_ball hδ) hfiber
  let y : ℂ := x + (δ / 2 : ℝ)
  have hyball : y ∈ Metric.ball x δ := by
    change dist (x + (δ / 2 : ℝ)) x < δ
    rw [Complex.dist_eq, add_sub_cancel_left]
    simpa [Complex.norm_real, abs_of_pos hδ,
      abs_of_pos (half_pos hδ)] using
      (half_lt_self hδ)
  have hyne : y ≠ x := by
    intro hyx
    have : (δ / 2 : ℂ) = 0 := by
      simpa [y] using sub_eq_zero.mpr hyx
    have : δ / 2 = 0 := by
      exact_mod_cast this
    linarith
  exact hyne (hsub hyball hxball)

/--
%%handwave
name:
  Protected cutoff density is stationary on the target ball
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. Let $\chi$ be smooth and compactly supported, and suppose
  $$
    D\chi(x)=0\qquad\text{whenever }f(x)\in\overline B(w,r).
  $$
  If
  $$
    \rho=
      \frac{d\,f_\#\!\left(\chi^2J_f\,dx\right)}{dy},
  $$
  then for every smooth compactly supported $\varphi$ with
  $\operatorname{supp}\varphi\subseteq B(w,r)$ and every
  $v\in\mathbb C$,
  $$
    \int_{\mathbb C}\rho(y)D\varphi(y)v\,dy=0.
  $$
proof:
  The cutoff-weighted Jacobian measure is finite, and [its pushforward is absolutely continuous with respect to area](lean:JJMath.Quasiconformal.IsLocalW12On.map_weightedWeakJacobianMeasureOn_absolutelyContinuous). Expand the Radon--Nikodym pairing back to the source integral. Apply [the protected scalar Piola identity](lean:JJMath.Quasiconformal.IsLocalW12On.integral_cutoff_jacobian_fderiv_comp_eq_zero) to the squared cutoff; its differential also vanishes over the protected target ball.
-/
theorem IsLocalW12On.weightedWeakJacobianDensity_sq_stationary_on_ball
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (χ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ))
    {w : ℂ} {r : ℝ}
    (hχzero :
      ∀ z, dist (f z) w ≤ r →
        fderiv ℝ (χ : ℂ → ℝ) z = 0)
    (φ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ))
    (hφsupport :
      tsupport (φ : ℂ → ℝ) ⊆ Metric.ball w r)
    (v : ℂ) :
    ∫ y : ℂ,
        weightedWeakJacobianDensity f
            (tsupport (χ : ℂ → ℝ)) df
            (fun z ↦ χ z ^ 2) y *
          fderiv ℝ (φ : ℂ → ℝ) y v
        ∂volume = 0 := by
  let S : Set ℂ :=
    tsupport (χ : ℂ → ℝ)
  let q : ℂ → ℝ :=
    fun z ↦ χ z ^ 2
  let g : ℂ → ℝ :=
    fun y ↦ fderiv ℝ (φ : ℂ → ℝ) y v
  have hScompact : IsCompact S :=
    χ.compact_support
  have hSmeas : MeasurableSet S :=
    hScompact.measurableSet
  have hSsub : S ⊆ Set.univ :=
    Set.subset_univ S
  have hJglobal :
      ∀ᵐ z ∂(volume : Measure ℂ),
        0 ≤ weakJacobian (df z) :=
    (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
      hK hdist).1
  have hJuniv :
      ∀ᵐ z ∂volume.restrict Set.univ,
        0 ≤ weakJacobian (df z) :=
    ae_restrict_of_ae hJglobal
  have hJS :
      ∀ᵐ z ∂volume.restrict S,
        0 ≤ weakJacobian (df z) :=
    ae_restrict_of_ae hJglobal
  have hLusin :
      HasLusinNOn Set.univ f :=
    hW.boundedDistortion_hasLusinNOn
      hf hK hdist
  haveI hweightedFinite :
      IsFiniteMeasure
        (weightedWeakJacobianMeasureOn S df q) := by
    dsimp [q]
    exact
      hW.isFiniteMeasure_weightedWeakJacobianMeasureOn_sq_of_compact
        hScompact hSsub χ
  have hAC :
      Measure.map f
          (weightedWeakJacobianMeasureOn S df q) ≪
        volume :=
    hW.map_weightedWeakJacobianMeasureOn_absolutelyContinuous
      hf.measurable hLusin hJuniv hSmeas hSsub q
  have hgcont : Continuous g := by
    exact
      (φ.smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const
  have hpair :
      (∫ y : ℂ,
          weightedWeakJacobianDensity f S df q y • g y
          ∂volume) =
        ∫ y : ℂ, g y ∂
          Measure.map f
            (weightedWeakJacobianMeasureOn S df q) :=
    integral_weightedWeakJacobianDensity_smul
      hAC g
  have hmap :
      (∫ y : ℂ, g y ∂
          Measure.map f
            (weightedWeakJacobianMeasureOn S df q)) =
        ∫ z : ℂ, g (f z) ∂
          weightedWeakJacobianMeasureOn S df q := by
    exact
      integral_map
        hf.measurable.aemeasurable
        hgcont.aestronglyMeasurable
  have hqmeas : Measurable q :=
    (χ.smooth.continuous.pow 2).measurable
  have hqnonneg : ∀ z, 0 ≤ q z :=
    fun z ↦ sq_nonneg (χ z)
  have hsource :
      (∫ z : ℂ, g (f z) ∂
          weightedWeakJacobianMeasureOn S df q) =
        ∫ z in S,
          q z * weakJacobian (df z) * g (f z)
          ∂volume :=
    hW.integral_comp_weightedWeakJacobianMeasureOn
      hSsub q hqmeas hqnonneg hJS g
  have hdensitySource :
      (∫ y : ℂ,
          weightedWeakJacobianDensity f S df q y • g y
          ∂volume) =
        ∫ z in S,
          q z * weakJacobian (df z) * g (f z)
          ∂volume :=
    hpair.trans (hmap.trans hsource)
  have hsqSupport :
      tsupport (fun z : ℂ ↦ χ z ^ 2) ⊆ S := by
    dsimp [S]
    rw [tsupport, tsupport]
    apply closure_mono
    intro z hz
    exact fun hχz ↦ hz (by simp [hχz])
  let χsq :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ) :=
    { toFun := fun z ↦ χ z ^ 2
      smooth := χ.smooth.pow 2
      support_subset := hsqSupport.trans (Set.subset_univ _)
      compact_support :=
        hScompact.of_isClosed_subset
          (isClosed_tsupport _) hsqSupport }
  have hχsqzero :
      ∀ z, dist (f z) w ≤ r →
        fderiv ℝ (χsq : ℂ → ℝ) z = 0 := by
    intro z hz
    have hχdiff : DifferentiableAt ℝ (χ : ℂ → ℝ) z :=
      χ.smooth.differentiable (by simp) z
    change fderiv ℝ (fun y : ℂ ↦ χ y ^ 2) z = 0
    rw [show
        (fun y : ℂ ↦ χ y ^ 2) =
          fun y ↦ χ y * χ y by
        funext y
        ring]
    rw [fderiv_fun_mul hχdiff hχdiff,
      hχzero z hz]
    simp
  have hpiola :=
    hW.integral_cutoff_jacobian_fderiv_comp_eq_zero
      χsq φ hφsupport hχsqzero v
  have houtside :
      ∀ z, z ∉ S →
        q z * weakJacobian (df z) * g (f z) = 0 := by
    intro z hz
    have hχz : χ z = 0 :=
      image_eq_zero_of_notMem_tsupport hz
    simp [q, hχz]
  have hset :
      (∫ z in S,
          q z * weakJacobian (df z) * g (f z)
          ∂volume) =
        ∫ z : ℂ,
          q z * weakJacobian (df z) * g (f z)
          ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := S) houtside
  have hsourceZero :
      (∫ z in S,
          q z * weakJacobian (df z) * g (f z)
          ∂volume) = 0 := by
    rw [hset]
    simpa [χsq, q, g] using hpiola
  have hfinal :
      (∫ y : ℂ,
          weightedWeakJacobianDensity f S df q y • g y
          ∂volume) = 0 :=
    hdensitySource.trans hsourceZero
  simpa [S, q, g, smul_eq_mul] using hfinal

/--
%%handwave
name:
  Protected cutoff density is constant on the target ball
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally
  $W^{1,2}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. Let $\chi$ be smooth and compactly supported, with
  $D\chi(x)=0$ whenever $f(x)\in\overline B(w,r)$. If
  $$
    \rho=
      \frac{d\,f_\#\!\left(\chi^2J_f\,dx\right)}{dy},
  $$
  then $\rho$ is almost everywhere equal to a constant on $B(w,r)$.
proof:
  The density is globally integrable and [its distributional gradient vanishes on the target ball](lean:JJMath.Quasiconformal.IsLocalW12On.weightedWeakJacobianDensity_sq_stationary_on_ball). Apply the theorem that an integrable function with zero distributional gradient is almost everywhere constant on a ball.
-/
theorem IsLocalW12On.weightedWeakJacobianDensity_sq_ae_eq_const_on_ball
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (χ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ))
    {w : ℂ} {r : ℝ}
    (hχzero :
      ∀ z, dist (f z) w ≤ r →
        fderiv ℝ (χ : ℂ → ℝ) z = 0) :
    ∃ a : ℝ,
      ∀ᵐ y ∂volume.restrict (Metric.ball w r),
        weightedWeakJacobianDensity f
            (tsupport (χ : ℂ → ℝ)) df
            (fun z ↦ χ z ^ 2) y = a := by
  let S : Set ℂ :=
    tsupport (χ : ℂ → ℝ)
  let q : ℂ → ℝ :=
    fun z ↦ χ z ^ 2
  have hScompact : IsCompact S :=
    χ.compact_support
  have hSsub : S ⊆ Set.univ :=
    Set.subset_univ S
  haveI :
      IsFiniteMeasure
        (weightedWeakJacobianMeasureOn S df q) := by
    dsimp [q]
    exact
        hW.isFiniteMeasure_weightedWeakJacobianMeasureOn_sq_of_compact
          hScompact hSsub χ
  apply
    JJMath.Uniformization.integrable_ae_eq_const_on_ball_of_distributionalGradient_zero
      (u := weightedWeakJacobianDensity f S df q)
      integrable_weightedWeakJacobianDensity
  intro φ hφsupport v
  simpa [S, q] using
    hW.weightedWeakJacobianDensity_sq_stationary_on_ball
      hf hK hdist χ hχzero φ hφsupport v

/--
%%handwave
name:
  Protected cutoff density is a positive constant
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, light, and locally
  $W^{1,2}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. Suppose $f(x)=w$, $\chi(x)=1$, and $\chi$ is a smooth compactly
  supported function satisfying $D\chi(z)=0$ whenever
  $f(z)\in\overline B(w,r)$, where $r>0$. If
  $$
    \rho=
      \frac{d\,f_\#\!\left(\chi^2J_f\,dz\right)}{dy},
  $$
  then there is a constant $a>0$ such that $\rho=a$ almost everywhere on
  $B(w,r)$.
proof:
  By [stationarity and distributional rigidity, the density is constant almost everywhere on the target ball](lean:JJMath.Quasiconformal.IsLocalW12On.weightedWeakJacobianDensity_sq_ae_eq_const_on_ball), and it is nonnegative because it is a Radon--Nikodym density. If the constant were zero, the weighted source measure of the preimage of the target ball would vanish. Continuity provides a source ball about $x$ on which the cutoff is nonzero and whose image lies in the target ball. Removing the nonzero cutoff factors would force zero Jacobian mass on this source ball, contradicting [positivity of Jacobian mass for light maps of bounded distortion](lean:JJMath.Quasiconformal.IsLocalW12On.integral_weakJacobian_pos_on_ball_of_boundedDistortion_of_light).
-/
theorem IsLocalW12On.weightedWeakJacobianDensity_sq_ae_eq_pos_const_on_ball
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton)
    (χ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ))
    {x w : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hxw : f x = w)
    (hχx : χ x = 1)
    (hχzero :
      ∀ z, dist (f z) w ≤ r →
        fderiv ℝ (χ : ℂ → ℝ) z = 0) :
    ∃ a : ℝ, 0 < a ∧
      ∀ᵐ y ∂volume.restrict (Metric.ball w r),
        weightedWeakJacobianDensity f
            (tsupport (χ : ℂ → ℝ)) df
            (fun z ↦ χ z ^ 2) y = a := by
  let S : Set ℂ := tsupport (χ : ℂ → ℝ)
  let q : ℂ → ℝ := fun z ↦ χ z ^ 2
  let ν : Measure ℂ := weightedWeakJacobianMeasureOn S df q
  let μ : Measure ℂ := Measure.map f ν
  have hScompact : IsCompact S := χ.compact_support
  have hSmeas : MeasurableSet S := hScompact.measurableSet
  have hSsub : S ⊆ Set.univ := Set.subset_univ S
  haveI hνfin : IsFiniteMeasure ν := by
    dsimp [ν, q]
    exact
      hW.isFiniteMeasure_weightedWeakJacobianMeasureOn_sq_of_compact
        hScompact hSsub χ
  haveI hμfin : IsFiniteMeasure μ := by
    dsimp [μ]
    exact Measure.isFiniteMeasure_map ν f
  obtain ⟨a, ha⟩ :=
    hW.weightedWeakJacobianDensity_sq_ae_eq_const_on_ball
      hf hK hdist χ hχzero
  have hballne :
      volume (Metric.ball w r) ≠ 0 :=
    ne_of_gt (Metric.measure_ball_pos volume w hr)
  obtain ⟨y, _hyball, hya⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hballne ha
  have hanonneg : 0 ≤ a := by
    rw [← hya]
    exact ENNReal.toReal_nonneg
  refine ⟨a, lt_of_le_of_ne hanonneg ?_, ha⟩
  intro hazero
  have haeq : a = 0 :=
    hazero.symm
  have hAC :
      μ ≪ volume := by
    have hJ :
        ∀ᵐ z ∂volume.restrict Set.univ,
          0 ≤ weakJacobian (df z) :=
      ae_restrict_of_ae
        (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
          hK hdist).1
    have hN : HasLusinNOn Set.univ f :=
      hW.boundedDistortion_hasLusinNOn hf hK hdist
    dsimp [μ, ν]
    exact
      hW.map_weightedWeakJacobianMeasureOn_absolutelyContinuous
        hf.measurable hN hJ hSmeas hSsub q
  have hdensityzero :
      weightedWeakJacobianDensity f S df q
          =ᵐ[volume.restrict (Metric.ball w r)]
        (fun _ ↦ 0) := by
    simpa [S, q, haeq] using ha
  have hintzero :
      (∫ y in Metric.ball w r,
        weightedWeakJacobianDensity f S df q y ∂volume) = 0 := by
    rw [integral_congr_ae hdensityzero]
    simp
  have hμrealzero :
      μ.real (Metric.ball w r) = 0 := by
    rw [← Measure.setIntegral_toReal_rnDeriv' hAC
      Metric.isOpen_ball.measurableSet]
    simpa [weightedWeakJacobianDensity, μ, ν, S, q] using
      hintzero
  have hμzero :
      μ (Metric.ball w r) = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hμrealzero
    exact hμrealzero.resolve_right (measure_ne_top _ _)
  let O : Set ℂ :=
    f ⁻¹' Metric.ball w r ∩
      (χ : ℂ → ℝ) ⁻¹' ({0}ᶜ : Set ℝ)
  have hOopen : IsOpen O := by
    exact
      (Metric.isOpen_ball.preimage hf).inter
        (isOpen_compl_singleton.preimage χ.smooth.continuous)
  have hxO : x ∈ O := by
    refine ⟨?_, ?_⟩
    · change dist (f x) w < r
      rw [hxw, dist_self]
      exact hr
    · simpa [hχx]
  obtain ⟨δ, hδ, hδO⟩ :=
    Metric.isOpen_iff.mp hOopen x hxO
  let V : Set ℂ := Metric.ball x δ
  have hVmeas : MeasurableSet V :=
    Metric.isOpen_ball.measurableSet
  have hVpre :
      V ⊆ f ⁻¹' Metric.ball w r :=
    fun z hz ↦ (hδO hz).1
  have hVχ :
      ∀ z ∈ V, χ z ≠ 0 := by
    intro z hz
    exact by simpa using (hδO hz).2
  have hsourcePrezero :
      ν (f ⁻¹' Metric.ball w r) = 0 := by
    rw [← Measure.map_apply hf.measurable
      Metric.isOpen_ball.measurableSet]
    exact hμzero
  have hνVzero : ν V = 0 :=
    measure_mono_null hVpre hsourcePrezero
  have hqAEM :
      AEMeasurable (fun z ↦ ENNReal.ofReal (q z))
        (weakJacobianMeasureOn S df) :=
    (ENNReal.continuous_ofReal.comp
      (χ.smooth.continuous.pow 2)).aemeasurable
  have hweakSetZero :
      weakJacobianMeasureOn S df
          ({z | ENNReal.ofReal (q z) ≠ 0} ∩ V) = 0 := by
    exact
      (withDensity_apply_eq_zero' hqAEM).1
        (by simpa [ν, weightedWeakJacobianMeasureOn] using hνVzero)
  have hVq :
      V ⊆ {z | ENNReal.ofReal (q z) ≠ 0} ∩ V := by
    intro z hz
    refine ⟨?_, hz⟩
    change ENNReal.ofReal (q z) ≠ 0
    rw [ENNReal.ofReal_ne_zero_iff]
    dsimp [q]
    exact sq_pos_of_ne_zero (hVχ z hz)
  have hweakVzero :
      weakJacobianMeasureOn S df V = 0 :=
    measure_mono_null hVq hweakSetZero
  have hJAEM :
      AEMeasurable
        (fun z ↦ ENNReal.ofReal (weakJacobian (df z)))
        (volume.restrict S) :=
    (continuous_weakJacobian.comp_aestronglyMeasurable
      ((hW.2.2 S hScompact hSsub).2.aestronglyMeasurable)
        ).aemeasurable.ennreal_ofReal
  have hbaseSetZero :
      (volume.restrict S)
          ({z |
            ENNReal.ofReal (weakJacobian (df z)) ≠ 0} ∩ V) = 0 := by
    exact
      (withDensity_apply_eq_zero' hJAEM).1
        (by simpa [weakJacobianMeasureOn] using hweakVzero)
  rw [Measure.restrict_apply' hSmeas] at hbaseSetZero
  have hVsubS : V ⊆ S := by
    intro z hz
    exact subset_tsupport (χ : ℂ → ℝ) (hVχ z hz)
  have hAS :
      ({z |
          ENNReal.ofReal (weakJacobian (df z)) ≠ 0} ∩ V) ∩ S =
        {z |
          ENNReal.ofReal (weakJacobian (df z)) ≠ 0} ∩ V := by
    exact inter_eq_left.mpr (inter_subset_right.trans hVsubS)
  rw [hAS] at hbaseSetZero
  have hofRealZero :
      ∀ᵐ z ∂volume.restrict V,
        ENNReal.ofReal (weakJacobian (df z)) = 0 := by
    rw [ae_iff, Measure.restrict_apply' hVmeas]
    simpa [compl_setOf, and_comm] using hbaseSetZero
  have hJnonneg :
      ∀ᵐ z ∂volume.restrict V,
        0 ≤ weakJacobian (df z) :=
    ae_restrict_of_ae
      (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
        hK hdist).1
  have hJzero :
      ∀ᵐ z ∂volume.restrict V,
        weakJacobian (df z) = 0 := by
    filter_upwards [hofRealZero, hJnonneg] with z hz hnonneg
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) hnonneg
  have hpositive :=
    hW.integral_weakJacobian_pos_on_ball_of_boundedDistortion_of_light
      hf hK hdist hlight x hδ
  have hintegralzero :
      (∫ z in V, weakJacobian (df z) ∂volume) = 0 := by
    rw [integral_congr_ae hJzero]
    simp
  exact (ne_of_gt hpositive) (by simpa [V] using hintegralzero)

/--
%%handwave
name:
  A protected cutoff covers its target ball
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, light, and locally
  $W^{1,2}$, with weak differential $Df$, and suppose
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. Suppose $f(x)=w$, $\chi(x)=1$, and $\chi$ is a smooth compactly
  supported function satisfying $D\chi(z)=0$ whenever
  $f(z)\in\overline B(w,r)$, where $r>0$. Then
  $$
    B(w,r)\subseteq f(\operatorname{supp}\chi).
  $$
proof:
  The weighted Jacobian pushforward has [an almost-everywhere positive constant density on the target ball](lean:JJMath.Quasiconformal.IsLocalW12On.weightedWeakJacobianDensity_sq_ae_eq_pos_const_on_ball). If a point of the ball lay outside the image of the compact cutoff support, a smaller target ball about that point would also avoid the image. The weighted pushforward would vanish on the smaller ball, whereas integration of its positive density over a positive-area ball would be strictly positive.
-/
theorem IsLocalW12On.ball_subset_image_tsupport_of_degreeCutoff
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton)
    (χ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ))
    {x w : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hxw : f x = w)
    (hχx : χ x = 1)
    (hχzero :
      ∀ z, dist (f z) w ≤ r →
        fderiv ℝ (χ : ℂ → ℝ) z = 0) :
    Metric.ball w r ⊆
      f '' tsupport (χ : ℂ → ℝ) := by
  let S : Set ℂ := tsupport (χ : ℂ → ℝ)
  let q : ℂ → ℝ := fun z ↦ χ z ^ 2
  let ν : Measure ℂ := weightedWeakJacobianMeasureOn S df q
  let μ : Measure ℂ := Measure.map f ν
  have hScompact : IsCompact S := χ.compact_support
  have hSmeas : MeasurableSet S := hScompact.measurableSet
  have hSsub : S ⊆ Set.univ := Set.subset_univ S
  haveI hνfin : IsFiniteMeasure ν := by
    dsimp [ν, q]
    exact
      hW.isFiniteMeasure_weightedWeakJacobianMeasureOn_sq_of_compact
        hScompact hSsub χ
  haveI hμfin : IsFiniteMeasure μ := by
    dsimp [μ]
    exact Measure.isFiniteMeasure_map ν f
  obtain ⟨a, ha_pos, ha⟩ :=
    hW.weightedWeakJacobianDensity_sq_ae_eq_pos_const_on_ball
      hf hK hdist hlight χ hr hxw hχx hχzero
  have hAC :
      μ ≪ volume := by
    have hJ :
        ∀ᵐ z ∂volume.restrict Set.univ,
          0 ≤ weakJacobian (df z) :=
      ae_restrict_of_ae
        (boundedDistortion_weakJacobian_nonneg_and_zeroBranch_ae
          hK hdist).1
    have hN : HasLusinNOn Set.univ f :=
      hW.boundedDistortion_hasLusinNOn hf hK hdist
    dsimp [μ, ν]
    exact
      hW.map_weightedWeakJacobianMeasureOn_absolutelyContinuous
        hf.measurable hN hJ hSmeas hSsub q
  intro y hyball
  by_contra hyimage
  let O : Set ℂ := Metric.ball w r \ f '' S
  have hOopen : IsOpen O :=
    Metric.isOpen_ball.sdiff (hScompact.image hf).isClosed
  have hyO : y ∈ O :=
    ⟨hyball, by simpa [S] using hyimage⟩
  obtain ⟨ε, hε, hεO⟩ :=
    Metric.isOpen_iff.mp hOopen y hyO
  let A : Set ℂ := Metric.ball y ε
  have hAmeas : MeasurableSet A :=
    Metric.isOpen_ball.measurableSet
  have hAB : A ⊆ Metric.ball w r :=
    fun z hz ↦ (hεO hz).1
  have hpreInter :
      (f ⁻¹' A) ∩ S = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    exact (hεO hz.1).2 ⟨z, hz.2, rfl⟩
  have hrestrictzero :
      (volume.restrict S) (f ⁻¹' A) = 0 := by
    rw [Measure.restrict_apply' hSmeas, hpreInter]
    simp
  have hνAC : ν ≪ volume.restrict S := by
    dsimp [ν, weightedWeakJacobianMeasureOn,
      weakJacobianMeasureOn]
    exact
      (withDensity_absolutelyContinuous _ _).trans
        (withDensity_absolutelyContinuous _ _)
  have hνprezero :
      ν (f ⁻¹' A) = 0 :=
    hνAC hrestrictzero
  have hμzero : μ A = 0 := by
    dsimp [μ]
    rw [Measure.map_apply hf.measurable hAmeas]
    exact hνprezero
  have hμrealzero : μ.real A = 0 := by
    simp [measureReal_def, hμzero]
  have haA :
      weightedWeakJacobianDensity f S df q
          =ᵐ[volume.restrict A] (fun _ ↦ a) :=
    ae_restrict_of_ae_restrict_of_subset hAB
      (by simpa [S, q] using ha)
  have hformula :
      (∫ z in A,
        weightedWeakJacobianDensity f S df q z ∂volume) =
        μ.real A := by
    simpa [weightedWeakJacobianDensity, μ, ν, S, q] using
      Measure.setIntegral_toReal_rnDeriv' hAC hAmeas
  rw [integral_congr_ae haA, hμrealzero] at hformula
  have hAvolpos : 0 < volume.real A := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact
      ⟨Metric.measure_ball_pos volume y hε,
        measure_ball_lt_top⟩
  have hintpos :
      0 < ∫ _z in A, a ∂volume := by
    simpa only [integral_const,
      measureReal_restrict_apply_univ,
      smul_eq_mul] using
      mul_pos hAvolpos ha_pos
  exact (ne_of_gt hintpos) hformula

/--
%%handwave
name:
  Light planar maps of bounded distortion are open
statement:
  Let $f:\mathbb C\to\mathbb C$ be a continuous light map in
  $W^{1,2}_{\mathrm{loc}}$, with weak differential $Df$, and suppose
  $$
    \lVert Df(z)\rVert_{\mathrm{op}}^2\leq KJ_f(z)
  $$
  almost everywhere for some $K\geq1$. Then $f$ is an open map.
proof:
  Around a point $x$ in an arbitrary open source set, choose a protected
  cutoff supported in that set. By [the cutoff coverage theorem](lean:JJMath.Quasiconformal.IsLocalW12On.ball_subset_image_tsupport_of_degreeCutoff), the image of its support contains a target ball about $f(x)$. Thus the image of every open source set is a neighborhood of each of its points.
-/
theorem IsLocalW12On.isOpenMap_of_boundedDistortion_of_light
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton) :
    IsOpenMap f := by
  intro U hU
  apply isOpen_iff_forall_mem_open.mpr
  intro w hw
  obtain ⟨x, hxU, hxw⟩ := hw
  obtain ⟨χ, r, hr, hχx, hχsupport, hχzero⟩ :=
    exists_degreeCutoff_of_light hf hlight hxw hU hxU
  have hball :=
    hW.ball_subset_image_tsupport_of_degreeCutoff
      hf hK hdist hlight χ hr hxw hχx hχzero
  exact
    ⟨Metric.ball w r,
      hball.trans (Set.image_mono hχsupport),
      Metric.isOpen_ball, Metric.mem_ball_self hr⟩

/--
%%handwave
name:
  Finite fibers from open maps with finite almost-everywhere multiplicity
statement:
  Let $f:\mathbb C\to\mathbb C$ be open, let $S\subset\mathbb C$ be open,
  and let $\varepsilon>0$. Suppose that for almost every
  $y\in B(w,\varepsilon)$,
  $$
    N(f,S,y)=M<+\infty.
  $$
  Then $S\cap f^{-1}(w)$ is finite.
proof:
  If the fiber contained more than $M$ points, choose finitely many such
  points and pairwise disjoint open neighborhoods of them inside $S$.
  Openness gives a common target neighborhood of $w$ met by the image of
  every selected source neighborhood. Every target in that neighborhood
  therefore has multiplicity at least the number of selected points,
  contradicting the almost-everywhere equality.
-/
theorem finite_fiber_inter_of_isOpenMap_of_eventually_preimageMultiplicity_eq
    {f : ℂ → ℂ} (hopen : IsOpenMap f)
    {S : Set ℂ} (hS : IsOpen S) {w : ℂ} {ε : ℝ} (hε : 0 < ε)
    {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hae : ∀ᵐ y ∂volume, y ∈ Metric.ball w ε →
      preimageMultiplicity f S y = M) :
    (S ∩ f ⁻¹' {w}).Finite := by
  classical
  by_contra hfinite
  have hinfinite : (S ∩ f ⁻¹' {w}).Infinite := hfinite
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hM
  obtain ⟨T, hTsub, hTfinite, hTcard⟩ :=
    hinfinite.exists_subset_ncard_eq n
  obtain ⟨U, hU, hUpair⟩ := hTfinite.t2_separation
  let V : Set ℂ :=
    ⋂ x ∈ hTfinite.toFinset, f '' (U x ∩ S)
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isOpen_biInter_finset fun x _hx ↦
      hopen _ ((hU x).2.inter hS)
  have hwV : w ∈ V := by
    simp only [V, Set.mem_iInter]
    intro x hxT
    have hxT' : x ∈ T := hTfinite.mem_toFinset.mp hxT
    have hxF := hTsub hxT'
    exact ⟨x, ⟨(hU x).1, hxF.1⟩, by simpa using hxF.2⟩
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.mp hVopen w hwV
  let δ : ℝ := min ρ ε
  have hδ : 0 < δ := lt_min hρ hε
  have hδV : Metric.ball w δ ⊆ V :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hρV
  have hδE : Metric.ball w δ ⊆ Metric.ball w ε :=
    Metric.ball_subset_ball (min_le_right _ _)
  have haeBall :
      ∀ᵐ y ∂volume.restrict (Metric.ball w δ),
        preimageMultiplicity f S y = M := by
    filter_upwards
        [ae_restrict_of_ae hae,
          ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hyball
    exact hy (hδE hyball)
  obtain ⟨y, hyball, hymult⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (ne_of_gt (Metric.measure_ball_pos volume w hδ)) haeBall
  have hyV : y ∈ V := hδV hyball
  have hex :
      ∀ x : T, ∃ z : ℂ, z ∈ U x.1 ∩ S ∧ f z = y := by
    intro x
    have hyimage :
        y ∈ f '' (U x.1 ∩ S) := by
      exact Set.mem_iInter₂.mp hyV x.1
        (hTfinite.mem_toFinset.mpr x.2)
    simpa only [Set.mem_image] using hyimage
  choose g hgmem hgf using hex
  have hginj : Function.Injective g := by
    intro x x' hxx'
    apply Subtype.ext
    by_contra hne
    have hdisjoint : Disjoint (U x.1) (U x'.1) :=
      hUpair x.2 x'.2 hne
    exact
      (Set.disjoint_left.mp hdisjoint
        (hgmem x).1 (hxx' ▸ (hgmem x').1)).elim
  have hrange :
      Set.range g ⊆ S ∩ f ⁻¹' {y} := by
    rintro z ⟨x, rfl⟩
    exact ⟨(hgmem x).2, by simpa using hgf x⟩
  have hnle :
      (n : ℕ∞) ≤ (S ∩ f ⁻¹' {y}).encard := by
    calc
      (n : ℕ∞) = T.encard := by
        rw [hTfinite.encard_eq_coe_toFinset_card]
        exact_mod_cast
          (hTcard.symm.trans (Set.ncard_eq_toFinset_card T hTfinite))
      _ ≤ (Set.range g).encard := hginj.encard_range
      _ ≤ (S ∩ f ⁻¹' {y}).encard := Set.encard_le_encard hrange
  have hnle' : (n : ℝ≥0∞) ≤ preimageMultiplicity f S y := by
    simpa [preimageMultiplicity] using ENat.toENNReal_mono hnle
  rw [hymult] at hnle'
  exact (not_le_of_gt hn) hnle'

/--
%%handwave
name:
  Positive index on an isolating circle for an open map of bounded distortion
statement:
  Let $f:\mathbb C\to\mathbb C$ be an open continuous map in
  $W^{1,2}_{\mathrm{loc}}$ satisfying
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere, with
  $K\geq1$. If $f(z)=w$ and $r>0$ isolates $z$ in $f^{-1}(w)$, then
  $$
    \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)>0.
  $$
proof:
  The image of a smaller concentric disk is an open neighborhood of $w$.
  Choose a target in that neighborhood where
  [multiplicity equals the protected disk index](lean:JJMath.Quasiconformal.IsLocalW12On.eventually_preimageMultiplicity_eq_ofReal_planarCircleIndex_of_boundedDistortion).
  This target has a preimage in the smaller disk, so its multiplicity in the
  isolating disk is nonzero. Hence the index is strictly positive.
-/
theorem IsLocalW12On.planarCircleIndex_pos_of_boundedDistortion_of_isOpenMap
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ x ∂(volume : Measure ℂ),
      ‖df x‖ ^ 2 ≤ K * weakJacobian (df x))
    (hopen : IsOpenMap f)
    (z w : ℂ) {r : ℝ}
    (hr : IsFiberIsolatingRadius f z w r)
    (hzw : f z = w) :
    0 < planarCircleIndex f hf z w r hr.1
      (imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr) := by
  let C : Set ℂ := Set.range (imageCircleLoop f hf z r)
  have hCcompact : IsCompact C := by
    exact isCompact_range (imageCircleLoop f hf z r).continuous
  have hCnonempty : C.Nonempty :=
    Set.range_nonempty _
  have hwC : w ∉ C := by
    rintro ⟨t, ht⟩
    exact
      imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr t ht
  let ε : ℝ := Metric.infDist w C
  have hε : 0 < ε := by
    exact
      (hCcompact.isClosed.notMem_iff_infDist_pos hCnonempty).1 hwC
  have hsep :
      ∀ t, ε ≤ ‖imageCircleLoop f hf z r t - w‖ := by
    intro t
    have hle :
        ε ≤ dist w (imageCircleLoop f hf z r t) := by
      exact Metric.infDist_le_dist_of_mem ⟨t, rfl⟩
    simpa [Complex.dist_eq, norm_sub_rev] using hle
  have hhalf : 0 < r / 2 := half_pos hr.1
  have hwimage : w ∈ f '' Metric.ball z (r / 2) :=
    ⟨z, Metric.mem_ball_self hhalf, hzw⟩
  have himageOpen : IsOpen (f '' Metric.ball z (r / 2)) :=
    hopen _ Metric.isOpen_ball
  obtain ⟨δ, hδ, hδimage⟩ :=
    Metric.isOpen_iff.mp himageOpen w hwimage
  let η : ℝ := min δ ε
  have hη : 0 < η := lt_min hδ hε
  have hηε : Metric.ball w η ⊆ Metric.ball w ε :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hηimage : Metric.ball w η ⊆ f '' Metric.ball z (r / 2) :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hδimage
  have hae :=
    hW.eventually_preimageMultiplicity_eq_ofReal_planarCircleIndex_of_boundedDistortion
      hf hK hdist z w hr.1 hε
        (imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr) hsep
  have haeBall :
      ∀ᵐ y ∂volume.restrict (Metric.ball w η),
        preimageMultiplicity f (Metric.ball z r) y =
          ENNReal.ofReal
            (planarCircleIndex f hf z w r hr.1
              (imageCircleLoop_ne_of_isFiberIsolatingRadius
                f hf z w hr) : ℝ) := by
    filter_upwards
        [ae_restrict_of_ae hae,
          ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hyball
    exact hy (hηε hyball)
  obtain ⟨y, hyball, hymult⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (ne_of_gt (Metric.measure_ball_pos volume w hη)) haeBall
  obtain ⟨x, hxsmall, hxy⟩ := hηimage hyball
  have hxball : x ∈ Metric.ball z r := by
    exact
      Metric.ball_subset_ball (by linarith [hr.1]) hxsmall
  have hxpreimage :
      x ∈ Metric.ball z r ∩ f ⁻¹' {y} :=
    ⟨hxball, by simpa using hxy⟩
  have hmultpos :
      0 < preimageMultiplicity f (Metric.ball z r) y := by
    change
      (0 : ℝ≥0∞) <
        ((Metric.ball z r ∩ f ⁻¹' {y}).encard : ℝ≥0∞)
    simpa only [ENat.toENNReal_zero] using
      ENat.toENNReal_strictMono
        (Set.encard_pos.mpr ⟨x, hxpreimage⟩)
  have hreal :
      0 < (planarCircleIndex f hf z w r hr.1
        (imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr) : ℝ) := by
    rw [← ENNReal.ofReal_pos, ← hymult]
    exact hmultpos
  exact_mod_cast hreal

/--
%%handwave
name:
  Positive local index for open maps of bounded distortion
statement:
  Let $f:\mathbb C\to\mathbb C$ be an open continuous map in
  $W^{1,2}_{\mathrm{loc}}$ satisfying
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere, with
  $K\geq1$. If the fiber $f^{-1}(w)$ is discrete and $f(z)=w$, then the
  local index of $f$ at $z$ over $w$ is strictly positive.
proof:
  Choose a fiber-isolating radius. The local index is the circle index on
  that radius, which is [strictly positive](lean:JJMath.Quasiconformal.IsLocalW12On.planarCircleIndex_pos_of_boundedDistortion_of_isOpenMap).
-/
theorem IsLocalW12On.planarLocalIndex_pos_of_boundedDistortion_of_isOpenMap
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ x ∂(volume : Measure ℂ),
      ‖df x‖ ^ 2 ≤ K * weakJacobian (df x))
    (hopen : IsOpenMap f)
    (w : ℂ) (z : {z : ℂ | f z = w})
    (hdiscrete : IsDiscrete {z : ℂ | f z = w}) :
    0 < planarLocalIndex f hf z w z.2 hdiscrete := by
  obtain ⟨r, hr⟩ :=
    exists_isFiberIsolatingRadius_of_isDiscrete_fiber
      f z w z.2 hdiscrete
  rw [planarLocalIndex_eq_planarCircleIndex
    f hf z w z.2 hdiscrete hr]
  exact
    hW.planarCircleIndex_pos_of_boundedDistortion_of_isOpenMap
      hf hK hdist hopen z w hr z.2

/--
%%handwave
name:
  Proper planar maps of bounded distortion are light
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, proper, and locally
  $W^{1,2}$, with weak differential $Df$. If $K\geq1$ and
  $$
    \lVert Df(z)\rVert_{\mathrm{op}}^2\leq KJ_f(z)
  $$
  almost everywhere, then every connected subset of every fiber
  $f^{-1}(w)$ is a singleton or empty.
proof:
  Properness makes each fiber compact. The closure of a connected subset of
  a fiber is again connected, remains in that fiber, and is compact. Apply
  [the logarithmic-condenser exclusion of compact fiber continua](lean:JJMath.Quasiconformal.IsLocalW12On.compact_connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap)
  to this closure.
-/
theorem IsLocalW12On.connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (hproper : IsProperMap f)
    (w : ℂ) {E : Set ℂ}
    (hEconnected : IsConnected E)
    (hEfiber : E ⊆ {x : ℂ | f x = w}) :
    E.Subsingleton := by
  have hfiberCompact : IsCompact {x : ℂ | f x = w} := by
    simpa using
      hproper.isCompact_preimage
        (K := ({w} : Set ℂ)) isCompact_singleton
  have hclosureFiber : closure E ⊆ {x : ℂ | f x = w} :=
    closure_minimal hEfiber hfiberCompact.isClosed
  have hclosureCompact : IsCompact (closure E) :=
    hfiberCompact.of_isClosed_subset isClosed_closure hclosureFiber
  have hclosureSubsingleton : (closure E).Subsingleton :=
    hW.compact_connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap
      hf hK hdist hproper w hclosureCompact hEconnected.closure
      hclosureFiber
  intro x hx y hy
  exact hclosureSubsingleton (subset_closure hx) (subset_closure hy)

/--
%%handwave
name:
  Proper planar maps of bounded distortion have finite fibers
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, proper, and locally
  $W^{1,2}$, with
  $\lVert Df\rVert_{\mathrm{op}}^2\leq KJ_f$ almost everywhere for
  $K\geq1$. Then every fiber $f^{-1}(w)$ is finite.
proof:
  [The condenser argument makes every fiber light](lean:JJMath.Quasiconformal.IsLocalW12On.connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap), hence [the direct Jacobian-measure argument makes $f$ open](lean:JJMath.Quasiconformal.IsLocalW12On.isOpenMap_of_boundedDistortion_of_light). Properness puts the fiber, and even the inverse image of a small closed target disk, inside one source disk. Its boundary is uniformly separated from $w$, so multiplicity on a protected target ball equals a finite disk index almost everywhere. [Openness and finite almost-everywhere multiplicity force the fiber inside that disk to be finite](lean:JJMath.Quasiconformal.finite_fiber_inter_of_isOpenMap_of_eventually_preimageMultiplicity_eq).
-/
theorem IsLocalW12On.finite_fiber_of_boundedDistortion_of_isProperMap
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hW : IsLocalW12On Set.univ f df)
    (hf : Continuous f)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (hproper : IsProperMap f) :
    ∀ w, {z : ℂ | f z = w}.Finite := by
  have hlight :
      ∀ w (E : Set ℂ), IsConnected E →
        E ⊆ {z : ℂ | f z = w} → E.Subsingleton := by
    intro w E hEconnected hEfiber
    exact
      hW.connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap
        hf hK hdist hproper w hEconnected hEfiber
  have hopen : IsOpenMap f :=
    hW.isOpenMap_of_boundedDistortion_of_light
      hf hK hdist hlight
  intro w
  by_cases hw : {z : ℂ | f z = w}.Nonempty
  · let P : Set ℂ := f ⁻¹' Metric.closedBall w 1
    have hPcompact : IsCompact P :=
      hproper.isCompact_preimage (isCompact_closedBall w 1)
    obtain ⟨R, hPR⟩ :=
      hPcompact.isBounded.subset_ball (0 : ℂ)
    obtain ⟨x, hx⟩ := hw
    have hxP : x ∈ P := by
      change f x ∈ Metric.closedBall w 1
      rw [hx]
      simp
    have hxball := hPR hxP
    have hR : 0 < R := by
      rw [Metric.mem_ball, dist_zero_right] at hxball
      exact (norm_nonneg x).trans_lt hxball
    have hcircleOutside :
        ∀ t, complexCircleLoop 0 R t ∉ P := by
      intro t ht
      have htball := hPR ht
      rw [Metric.mem_ball, dist_zero_right] at htball
      have hnorm :
          ‖complexCircleLoop 0 R t‖ = R := by
        simp only [complexCircleLoop, circlePoint, zero_add]
        change ‖(R : ℂ) *
          Complex.exp ((2 * Real.pi * (t : ℝ) : ℝ) * Complex.I)‖ = R
        simp [abs_of_pos hR, Complex.norm_exp]
      rw [hnorm] at htball
      exact (lt_irrefl R) htball
    have hsep :
        ∀ t, (1 : ℝ) ≤
          ‖imageCircleLoop f hf 0 R t - w‖ := by
      intro t
      have hout := hcircleOutside t
      change f (complexCircleLoop 0 R t) ∉ Metric.closedBall w 1 at hout
      rw [Metric.mem_closedBall, Complex.dist_eq] at hout
      simpa [imageCircleLoop, norm_sub_rev] using
        (le_of_lt (not_le.mp hout))
    have havoid :
        ∀ t, imageCircleLoop f hf 0 R t ≠ w := by
      intro t ht
      have := hsep t
      rw [ht, sub_self, norm_zero] at this
      norm_num at this
    have hae :=
      hW.eventually_preimageMultiplicity_eq_ofReal_planarCircleIndex_of_boundedDistortion
        hf hK hdist 0 w hR zero_lt_one havoid hsep
    have hfiniteBall :
        (Metric.ball 0 R ∩ f ⁻¹' {w}).Finite :=
      finite_fiber_inter_of_isOpenMap_of_eventually_preimageMultiplicity_eq
        hopen Metric.isOpen_ball zero_lt_one ENNReal.ofReal_ne_top hae
    apply hfiniteBall.subset
    intro z hz
    have hzP : z ∈ P := by
      change f z ∈ Metric.closedBall w 1
      rw [hz]
      simp
    exact ⟨hPR hzP, by simpa using hz⟩
  · simpa [Set.not_nonempty_iff_eq_empty.mp hw]

/--
%%handwave
name:
  Proper planar maps of bounded distortion are open and discrete
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, proper, and locally
  $W^{1,2}$, with weak differential $Df$. Suppose $K\geq1$ and
  $$
    \lVert Df(z)\rVert_{\mathrm{op}}^2\leq KJ_f(z)
  $$
  almost everywhere. Then $f$ is open, every fiber $f^{-1}(w)$ is
  discrete, and the local index at each point of each fiber is positive.
proof:
  [The logarithmic condenser argument makes every fiber light](lean:JJMath.Quasiconformal.IsLocalW12On.connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap), and [the direct Jacobian-measure argument makes the map open](lean:JJMath.Quasiconformal.IsLocalW12On.isOpenMap_of_boundedDistortion_of_light). [Properness and the protected multiplicity formula then make every fiber finite](lean:JJMath.Quasiconformal.IsLocalW12On.finite_fiber_of_boundedDistortion_of_isProperMap), hence discrete. Finally [openness makes the local index at every isolated fiber point strictly positive](lean:JJMath.Quasiconformal.IsLocalW12On.planarLocalIndex_pos_of_boundedDistortion_of_isOpenMap).
-/
theorem open_discrete_and_localIndex_pos_of_boundedDistortion_of_isProperMap
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hf : Continuous f) (hW : IsLocalW12On Set.univ f df)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (hproper : IsProperMap f) :
    IsOpenMap f ∧
      ∃ hdiscrete : ∀ w, IsDiscrete {z : ℂ | f z = w},
        ∀ w (z : {z : ℂ | f z = w}),
          0 < planarLocalIndex f hf z w z.2 (hdiscrete w) := by
  have hlight :
      ∀ w (E : Set ℂ), IsConnected E →
        E ⊆ {z : ℂ | f z = w} → E.Subsingleton := by
    intro w E hEconnected hEfiber
    exact
      hW.connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap
        hf hK hdist hproper w hEconnected hEfiber
  have hopen : IsOpenMap f :=
    hW.isOpenMap_of_boundedDistortion_of_light
      hf hK hdist hlight
  have hfinite : ∀ w, {z : ℂ | f z = w}.Finite :=
    hW.finite_fiber_of_boundedDistortion_of_isProperMap
      hf hK hdist hproper
  let hdiscrete : ∀ w, IsDiscrete {z : ℂ | f z = w} :=
    fun w ↦ (hfinite w).isDiscrete
  refine ⟨hopen, ⟨hdiscrete, ?_⟩⟩
  intro w z
  exact
    hW.planarLocalIndex_pos_of_boundedDistortion_of_isOpenMap
      hf hK hdist hopen w z (hdiscrete w)

end

end Quasiconformal

end JJMath
