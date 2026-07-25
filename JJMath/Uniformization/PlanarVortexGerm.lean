import JJMath.Manifold.CirclePrimitiveUniqueness
import JJMath.Uniformization.PlanarVortexPair
import JJMath.Uniformization.SmoothUnitPhaseCirclePrimitive

/-!
# The radial germ of a compact planar vortex

Near its zero, the compact zero--pole vortex is the ordinary radial phase,
up to a constant rotation and the exponential of a smooth real function.  The
real correction is the negative imaginary part of a logarithm of the
normalized denominator.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

/--
%%handwave
name: Normalized denominator of a planar vortex pair
statement:
  For marked points $a,b$, define $D_{a,b}(z)=(z-b)/(a-b)$, normalized so
  that $D_{a,b}(a)=1$ when $a\ne b$.
-/
def planarVortexNormalizedDenominator (a b z : ℂ) : ℂ :=
  (z - b) / (a - b)

/--
%%handwave
name:
  The normalized vortex denominator equals one at the zero endpoint
statement:
  If \(a\ne b\), then
  \[
    \frac{a-b}{a-b}=1,
  \]
  so the normalized denominator of the zero--pole vortex takes the value one
  at \(a\).
proof:
  Cancel the nonzero number \(a-b\).
-/
@[simp]
theorem planarVortexNormalizedDenominator_left {a b : ℂ} (hab : a ≠ b) :
    planarVortexNormalizedDenominator a b a = 1 := by
  rw [planarVortexNormalizedDenominator, div_self]
  exact sub_ne_zero.mpr hab

/--
%%handwave
name: Left logarithmic germ of a planar vortex pair
statement:
  For $a\ne b$, define the open germ of points
  $z\in\mathbb C\setminus\{a,b\}$ satisfying
  $|A_{a,b}(z)|<2$ and $D_{a,b}(z)\in\mathbb C_{\mathrm{slit}}$.
-/
def planarVortexLeftGermOpen {a b : ℂ} (_hab : a ≠ b) :
    TopologicalSpace.Opens (planarVortexPairOpenAt a b) := by
  let f : planarVortexPairOpenAt a b → ℂ := fun z ↦
    planarVortexAffine a b z
  let g : planarVortexPairOpenAt a b → ℂ := fun z ↦
    planarVortexNormalizedDenominator a b z
  have hf : Continuous f := by
    dsimp [f, planarVortexAffine]
    fun_prop
  have hg : Continuous g := by
    dsimp [g, planarVortexNormalizedDenominator]
    fun_prop
  exact
    ⟨{z | ‖f z‖ < 2 ∧ g z ∈ Complex.slitPlane},
      (isOpen_lt (continuous_norm.comp hf) continuous_const).inter
        (Complex.isOpen_slitPlane.preimage hg)⟩

/--
%%handwave
name: Denominator function on the left vortex germ
statement:
  Restrict $D_{a,b}(z)=(z-b)/(a-b)$ to the left logarithmic germ.
-/
def planarVortexLeftGermDenominator {a b : ℂ} (hab : a ≠ b)
    (z : planarVortexLeftGermOpen hab) : ℂ :=
  planarVortexNormalizedDenominator a b z

/--
%%handwave
name:
  Nonvanishing of the normalized denominator on the left vortex germ
statement:
  For \(a\ne b\) and every point \(z\) of the punctured left vortex germ,
  the normalized denominator \((z-b)/(a-b)\) is nonzero.
proof:
  Points of the twice-punctured germ satisfy \(z\ne b\), while \(a\ne b\) by
  hypothesis; hence both numerator and denominator are nonzero.
-/
theorem planarVortexLeftGermDenominator_ne_zero {a b : ℂ} (hab : a ≠ b)
    (z : planarVortexLeftGermOpen hab) :
    planarVortexLeftGermDenominator hab z ≠ 0 := by
  rw [planarVortexLeftGermDenominator, planarVortexNormalizedDenominator,
    div_ne_zero_iff]
  exact ⟨sub_ne_zero.mpr z.1.2.2, sub_ne_zero.mpr hab⟩

/--
%%handwave
name: Logarithmic denominator correction on the left germ
statement:
  On the left germ, define
  $h_{a,b}(z)=-\operatorname{Im}\log D_{a,b}(z)$.
-/
def planarVortexLeftGermCorrection {a b : ℂ} (hab : a ≠ b)
    (z : planarVortexLeftGermOpen hab) : ℝ :=
  -(Complex.log (planarVortexLeftGermDenominator hab z)).im

/--
%%handwave
name:
  Smoothness of the planar vortex denominator correction
statement:
  On the left logarithmic germ of a planar vortex, the real function
  \[
    h(z)=-\operatorname{Im}\log\frac{z-b}{a-b}
  \]
  is smooth.
proof:
  The normalized denominator is a smooth map into the slit plane.  The
  principal logarithm is smooth on the slit plane, and taking its imaginary
  part and negating preserves smoothness.
-/
theorem contMDiff_planarVortexLeftGermCorrection {a b : ℂ} (hab : a ≠ b) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      (planarVortexLeftGermCorrection hab) := by
  have hden : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (planarVortexLeftGermDenominator hab) := by
    have hraw : ContDiff ℝ ∞
        (fun z : ℂ ↦ planarVortexNormalizedDenominator a b z) := by
      dsimp [planarVortexNormalizedDenominator]
      fun_prop
    exact hraw.contMDiff.comp
      (contMDiff_subtype_val.comp contMDiff_subtype_val)
  have hlogC : ContDiffOn ℂ ∞ Complex.log Complex.slitPlane :=
    (analyticOnNhd_id.clog (fun z hz ↦ hz)).contDiffOn
      Complex.isOpen_slitPlane.uniqueDiffOn
  have hlogR : ContDiffOn ℝ ∞ Complex.log Complex.slitPlane := by
    exact @ContDiffOn.restrict_scalars ℝ inferInstance
      ℂ inferInstance inferInstance ℂ inferInstance inferInstance
      Complex.slitPlane Complex.log ∞
      ℂ inferInstance inferInstance inferInstance
      (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      inferInstance (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      hlogC
  have hlogM : ContMDiffOn (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞ Complex.log Complex.slitPlane :=
    contMDiffOn_iff_contDiffOn.mpr hlogR
  have hlog : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexLeftGermOpen hab ↦
        Complex.log (planarVortexLeftGermDenominator hab z)) := by
    rw [← contMDiffOn_univ]
    exact hlogM.comp hden.contMDiffOn (by
      intro z _hz
      exact z.2.2)
  have him : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) ∞ (fun z : ℂ ↦ z.im) :=
    Complex.imCLM.contDiff.contMDiff
  exact (him.comp hlog).neg

/--
%%handwave
name: Rotated radial phase at the vortex zero
statement:
  On the left germ, define
  $R_{a,b}(z)=\frac{z-a}{|z-a|}\frac{|a-b|}{a-b}$.
-/
def planarVortexLeftRotatedRadialPhase {a b : ℂ} (hab : a ≠ b)
    (z : planarVortexLeftGermOpen hab) : ℂ :=
  ((z : ℂ) - a) / ‖(z : ℂ) - a‖ * (‖a - b‖ / (a - b))

/--
%%handwave
name:
  Smoothness of the rotated radial vortex phase
statement:
  On the punctured left germ, the phase
  \[
    z\longmapsto \frac{z-a}{|z-a|}\frac{|a-b|}{a-b}
  \]
  is smooth.
proof:
  The function \(z-a\) never vanishes on the germ, so its norm and reciprocal
  are smooth there.  Multiply its normalized radial direction by the fixed
  complex rotation \(|a-b|/(a-b)\).
-/
theorem contMDiff_planarVortexLeftRotatedRadialPhase
    {a b : ℂ} (hab : a ≠ b) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (planarVortexLeftRotatedRadialPhase hab) := by
  have hsub : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexLeftGermOpen hab ↦ (z : ℂ) - a) := by
    have hraw : ContDiff ℝ ∞ (fun z : ℂ ↦ z - a) := by fun_prop
    exact hraw.contMDiff.comp
      (contMDiff_subtype_val.comp contMDiff_subtype_val)
  have hne : ∀ z : planarVortexLeftGermOpen hab, (z : ℂ) - a ≠ 0 :=
    fun z ↦ sub_ne_zero.mpr z.1.2.1
  have hnorm : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : planarVortexLeftGermOpen hab ↦ ‖(z : ℂ) - a‖) := by
    intro z
    exact (contDiffAt_norm ℝ (hne z)).contMDiffAt.comp z (hsub z)
  have hradial : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexLeftGermOpen hab ↦
        ‖(z : ℂ) - a‖⁻¹ • ((z : ℂ) - a)) :=
    (hnorm.inv₀ (fun z ↦ norm_ne_zero_iff.mpr (hne z))).smul hsub
  let k : ℂ := ((‖a - b‖ : ℝ) : ℂ) * (a - b)⁻¹
  let L : ℂ →L[ℝ] ℂ :=
    ContinuousLinearMap.mulLeftRight ℝ ℂ 1 k
  have hL : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞ L := L.contMDiff
  have heq :
      (L ∘ fun z : planarVortexLeftGermOpen hab ↦
        ‖(z : ℂ) - a‖⁻¹ • ((z : ℂ) - a)) =
        planarVortexLeftRotatedRadialPhase hab := by
    funext z
    simp [planarVortexLeftRotatedRadialPhase, div_eq_mul_inv,
      L, k,
      ContinuousLinearMap.mulLeftRight_apply]
    exact Or.inl (mul_comm _ _)
  rw [← heq]
  exact hL.comp hradial

/--
%%handwave
name: Smooth map of the rotated radial phase
statement:
  Bundle $z\mapsto R_{a,b}(z)$ as a smooth complex-valued map on the left
  logarithmic germ.
-/
def planarVortexLeftRotatedRadialPhaseMap {a b : ℂ} (hab : a ≠ b) :
    ContMDiffMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (planarVortexLeftGermOpen hab) ℂ ∞ where
  val := planarVortexLeftRotatedRadialPhase hab
  property := contMDiff_planarVortexLeftRotatedRadialPhase hab

/--
%%handwave
name: Radial phase at the vortex zero
statement:
  On the left germ, define the unit radial direction
  $U_a(z)=(z-a)/|z-a|$.
-/
def planarVortexLeftRadialPhase {a b : ℂ} (hab : a ≠ b)
    (z : planarVortexLeftGermOpen hab) : ℂ :=
  ((z : ℂ) - a) / ‖(z : ℂ) - a‖

/--
%%handwave
name:
  Smoothness of the radial phase near the vortex zero
statement:
  On the punctured left germ, the radial direction
  \(z\mapsto(z-a)/|z-a|\) is smooth.
proof:
  The difference \(z-a\) is nonzero on the germ, so its norm is a positive
  smooth function and division by that norm is smooth.
-/
theorem contMDiff_planarVortexLeftRadialPhase
    {a b : ℂ} (hab : a ≠ b) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (planarVortexLeftRadialPhase hab) := by
  have hsub : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexLeftGermOpen hab ↦ (z : ℂ) - a) := by
    have hraw : ContDiff ℝ ∞ (fun z : ℂ ↦ z - a) := by fun_prop
    exact hraw.contMDiff.comp
      (contMDiff_subtype_val.comp contMDiff_subtype_val)
  have hne : ∀ z : planarVortexLeftGermOpen hab, (z : ℂ) - a ≠ 0 :=
    fun z ↦ sub_ne_zero.mpr z.1.2.1
  have hnorm : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : planarVortexLeftGermOpen hab ↦ ‖(z : ℂ) - a‖) := by
    intro z
    exact (contDiffAt_norm ℝ (hne z)).contMDiffAt.comp z (hsub z)
  have hradial :=
    (hnorm.inv₀ (fun z ↦ norm_ne_zero_iff.mpr (hne z))).smul hsub
  have heq :
      (fun z : planarVortexLeftGermOpen hab ↦
        ‖(z : ℂ) - a‖⁻¹ • ((z : ℂ) - a)) =
        planarVortexLeftRadialPhase hab := by
    funext z
    simp [planarVortexLeftRadialPhase, div_eq_mul_inv,
      mul_comm]
  rw [← heq]
  exact hradial

/--
%%handwave
name:
  Unit norm of the radial phase near the vortex zero
statement:
  For every \(z\ne a\), the normalized radial direction
  \((z-a)/|z-a|\) has complex modulus one.
proof:
  Take norms and cancel the nonzero real number \(|z-a|\).
-/
theorem norm_planarVortexLeftRadialPhase
    {a b : ℂ} (hab : a ≠ b) (z : planarVortexLeftGermOpen hab) :
    ‖planarVortexLeftRadialPhase hab z‖ = 1 := by
  simp [planarVortexLeftRadialPhase,
    div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.1.2.1))]

/--
%%handwave
name: Smooth map of the radial vortex phase
statement:
  Bundle $z\mapsto U_a(z)$ as a smooth unit-complex phase on the left germ.
-/
def planarVortexLeftRadialPhaseMap {a b : ℂ} (hab : a ≠ b) :
    ContMDiffMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (planarVortexLeftGermOpen hab) ℂ ∞ where
  val := planarVortexLeftRadialPhase hab
  property := contMDiff_planarVortexLeftRadialPhase hab

/--
%%handwave
name:
  Radial factorization of the compact planar vortex
statement:
  On the left logarithmic germ of the zero--pole vortex,
  \[
    P_{a,b}(z)=
    \frac{z-a}{|z-a|}\frac{|a-b|}{a-b}
    \exp\!\left(-i\operatorname{Im}\log\frac{z-b}{a-b}\right).
  \]
proof:
  On this germ the compact cutoff is inactive, so the vortex is the normalized
  phase of \((z-a)/(z-b)\).  Put \(w=(z-b)/(a-b)\).  The principal-log identity
  gives \(e^{-i\operatorname{Im}\log w}=|w|/w\); substituting this and comparing
  norms yields the factorization.
-/
theorem planarVortexCompactPhaseAt_eq_rotatedRadial_mul_exp_correction
    {a b : ℂ} (hab : a ≠ b) (z : planarVortexLeftGermOpen hab) :
    planarVortexCompactPhaseAt hab z.1 =
      planarVortexLeftRotatedRadialPhase hab z *
        Complex.exp ((((planarVortexLeftGermCorrection hab z : ℝ) : ℂ) *
          Complex.I)) := by
  let x : ℂ := (z : ℂ) - a
  let d : ℂ := (z : ℂ) - b
  let c : ℂ := a - b
  let w : ℂ := planarVortexLeftGermDenominator hab z
  have hx : x ≠ 0 := sub_ne_zero.mpr z.1.2.1
  have hd : d ≠ 0 := sub_ne_zero.mpr z.1.2.2
  have hc : c ≠ 0 := sub_ne_zero.mpr hab
  have hw : w ≠ 0 := planarVortexLeftGermDenominator_ne_zero hab z
  have hw_eq : w = d / c := rfl
  have hexp :
      Complex.exp ((((planarVortexLeftGermCorrection hab z : ℝ) : ℂ) *
        Complex.I)) = (‖w‖ : ℂ) / w := by
    have harg := complex_exp_im_log_mul_I_eq_div_norm hw
    rw [planarVortexLeftGermCorrection]
    change Complex.exp ((((-(Complex.log w).im : ℝ) : ℂ) * Complex.I)) = _
    push_cast
    rw [neg_mul, Complex.exp_neg, harg, inv_div]
  rw [planarVortexCompactPhaseAt_eq_normalized_ratio_of_affine_norm_lt_two
    hab z.1 z.2.1, planarVortexLeftRotatedRadialPhase, hexp]
  change (x / d) / ‖x / d‖ =
    (x / ‖x‖) * (‖c‖ / c) * ((‖w‖ : ℂ) / w)
  have hnormw : ‖w‖ = ‖d‖ / ‖c‖ := by rw [hw_eq, norm_div]
  rw [norm_div, hnormw, hw_eq]
  push_cast
  field_simp [hx, hd, hc, norm_ne_zero_iff.mpr hx,
    norm_ne_zero_iff.mpr hd, norm_ne_zero_iff.mpr hc]

/--
%%handwave
name: Compact vortex phase on the left logarithmic germ
statement:
  Restrict the compact phase of the vortex pair at $a,b$ to its left
  logarithmic germ and bundle the restriction as a smooth complex-valued map.
-/
def planarVortexLeftGermCompactPhaseMap {a b : ℂ} (hab : a ≠ b) :
    ContMDiffMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (planarVortexLeftGermOpen hab) ℂ ∞ where
  val := fun z ↦ planarVortexCompactPhaseAt hab z.1
  property := (contMDiff_planarVortexCompactPhaseAt hab).comp
    contMDiff_subtype_val

end

end JJMath.Uniformization
