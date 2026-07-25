import JJMath.Quasiconformal.LocalSobolev
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Conformal changes of planar coordinates

This file applies the local Sobolev chain rule to inversion, the transition
map between the two standard finite charts of the Riemann sphere.
-/

namespace JJMath

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Complex inversion preserves planar null sets
statement:
  The map $\iota:\mathbb C\to\mathbb C$ given by
  $\iota(z)=z^{-1}$, with $\iota(0)=0$, is quasi-measure-preserving for
  planar Lebesgue measure.
proof:
  For a null measurable set, remove the origin and apply the classical
  change-of-variables formula to inversion on the remainder. Its image is
  null, and adjoining the singleton $\{0\}$ does not change this.
-/
theorem inversion_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun z : ℂ ↦ z⁻¹)
      MeasureTheory.volume MeasureTheory.volume := by
  refine ⟨measurable_inv, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs_zero
  rw [Measure.map_apply measurable_inv hs]
  have hinv_preimage : (fun z : ℂ ↦ z⁻¹) ⁻¹' s =
      (fun z : ℂ ↦ z⁻¹) '' s := by
    ext z
    constructor
    · intro hz
      exact ⟨z⁻¹, hz, inv_inv z⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [hinv_preimage]
  let t : Set ℂ := s \ {0}
  have ht_meas : MeasurableSet t := hs.diff (MeasurableSet.singleton 0)
  have ht_zero : MeasureTheory.volume t = 0 :=
    measure_mono_null diff_subset hs_zero
  let dinv : ℂ → ℂ →L[ℝ] ℂ := fun z ↦
    (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹)).restrictScalars ℝ
  have hderiv : ∀ z ∈ t,
      HasFDerivWithinAt (fun z : ℂ ↦ z⁻¹) (dinv z) t z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      simpa [t] using hz.2
    exact ((hasFDerivAt_inv hz0).restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn (fun z : ℂ ↦ z⁻¹) t := by
    intro z hz w hw hzw
    simpa only [inv_inj] using hzw
  have hcov :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (MeasureTheory.volume : Measure ℂ) ht_meas hderiv hinj
      (fun _ : ℂ ↦ (1 : ℝ≥0∞))
  have himage_t_zero :
      MeasureTheory.volume ((fun z : ℂ ↦ z⁻¹) '' t) = 0 := by
    rw [MeasureTheory.setLIntegral_one] at hcov
    rw [hcov]
    exact setLIntegral_measure_zero t _ ht_zero
  have hsubset :
      (fun z : ℂ ↦ z⁻¹) '' s ⊆
        (fun z : ℂ ↦ z⁻¹) '' t ∪ {0} := by
    rintro z ⟨w, hw, rfl⟩
    by_cases hw0 : w = 0
    · right
      simp [hw0]
    · left
      exact ⟨w, ⟨hw, by simpa using hw0⟩, rfl⟩
  exact measure_mono_null hsubset
    (measure_union_null himage_t_zero (measure_singleton 0))

/--
%%handwave
name:
  Inversion is locally Lipschitz off the origin
statement:
  The map $\iota(z)=z^{-1}$ is locally Lipschitz on
  $\mathbb C^\times=\mathbb C\setminus\{0\}$.
proof:
  At every nonzero point inversion is continuously differentiable, hence
  Lipschitz on some neighborhood of that point.
-/
theorem inversion_locallyLipschitzOn_puncturedPlane :
    LocallyLipschitzOn ({0}ᶜ : Set ℂ) (fun z : ℂ ↦ z⁻¹) := by
  intro z hz
  rcases (contDiffAt_inv ℝ hz).exists_lipschitzOnWith with
    ⟨C, V, hV, hlip⟩
  refine ⟨C, V, ?_, hlip⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨V, hV, inter_subset_left⟩

/--
%%handwave
name:
  Real differential of complex inversion
statement:
  For $z\ne0$, the real differential of $\iota(z)=z^{-1}$ is the
  complex-linear map
  $$
  D\iota(z)(\xi)=-z^{-2}\xi.
  $$
proof:
  Restrict the usual complex derivative of inversion to real scalars.
-/
theorem fderiv_inversion (z : ℂ) (hz : z ≠ 0) :
    fderiv ℝ (fun w : ℂ ↦ w⁻¹) z =
      realLinearMapOfWirtinger (-(z ^ 2)⁻¹) 0 := by
  rw [((hasFDerivAt_inv hz).restrictScalars ℝ).fderiv]
  ext ξ
  simp
  ring

/--
%%handwave
name:
  Local Sobolev regularity under inversion
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\mathbb C^\times,\mathbb C)$ has weak
  differential $Df$, then $z\mapsto f(z^{-1})$ is locally Sobolev on
  $\mathbb C^\times$ with weak differential
  $$
  z\mapsto Df(z^{-1})\circ D\iota(z).
  $$
proof:
  Apply the locally bi-Lipschitz Sobolev chain rule. Inversion is its own
  inverse, is locally Lipschitz off the origin, and preserves null sets in
  both directions.
-/
theorem IsLocalW12On.comp_inversion
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On ({0}ᶜ : Set ℂ) f df) :
    IsLocalW12On ({0}ᶜ : Set ℂ) (fun z ↦ f z⁻¹)
      (fun z ↦ (df z⁻¹).comp (fderiv ℝ (fun w : ℂ ↦ w⁻¹) z)) := by
  apply h.comp_locallyBiLipschitz
    isOpen_compl_singleton
    (T := fun z : ℂ ↦ z⁻¹) (S := fun z : ℂ ↦ z⁻¹)
  · intro z hz
    exact inv_ne_zero hz
  · intro z hz
    exact inv_ne_zero hz
  · intro z _hz
    exact inv_inv z
  · intro z _hz
    exact inv_inv z
  · exact inversion_locallyLipschitzOn_puncturedPlane
  · exact inversion_locallyLipschitzOn_puncturedPlane
  · exact inversion_quasiMeasurePreserving.restrict fun z hz ↦ inv_ne_zero hz
  · exact inversion_quasiMeasurePreserving.restrict fun z hz ↦ inv_ne_zero hz

/--
%%handwave
name:
  Local Sobolev regularity of inversion
statement:
  The map $\iota(z)=z^{-1}$ belongs to
  $W^{1,2}_{\mathrm{loc}}(\mathbb C^\times,\mathbb C)$ with weak
  differential equal to its classical real differential
  $$
    D\iota(z)(\xi)=-z^{-2}\xi.
  $$
proof:
  Start with the identity map and apply the local Sobolev source-composition
  theorem for inversion. The identity differential drops out of the
  resulting chain-rule field.
-/
theorem isLocalW12On_inversion :
    IsLocalW12On ({0}ᶜ : Set ℂ) (fun z : ℂ ↦ z⁻¹)
      (fun z ↦ fderiv ℝ (fun w : ℂ ↦ w⁻¹) z) := by
  have hid := isLocalW12On_affineMap
    (Ω := ({0}ᶜ : Set ℂ)) isOpen_compl_singleton 1 0 0
  have hinv := hid.comp_inversion
  convert hinv using 1
  · funext z
    simp [affineMap, realLinearMapOfWirtinger]
  · funext z
    ext v
    simp [realLinearMapOfWirtinger]

/--
%%handwave
name:
  Pullback of a Beltrami coefficient by a conformal coordinate change
statement:
  For a conformal change of variables $T$ with complex derivative $a$, define
  the pulled-back coefficient by
  $$
    (T^*\mu)(z)
      =\mu(T(z))\frac{\overline{a(z)}}{a(z)}.
  $$
-/
def conformalPullbackBeltrami
    (T a μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  μ (T z) * starRingEnd ℂ (a z) / a z

/--
%%handwave
name:
  Beltrami equation under a conformal source-coordinate change
statement:
  Let $T:U\to\Omega$ preserve null sets and have nonzero complex derivative
  $a(z)$. If $\partial_{\bar z}f=\mu\,\partial_z f$ almost everywhere on
  $\Omega$, then the pulled-back differential satisfies
  $$
  \partial_{\bar z}(f\circ T)
    =\left((\mu\circ T)\frac{\overline a}{a}\right)
      \partial_z(f\circ T)
  $$
  almost everywhere on $U$.
proof:
  Pull the original almost-everywhere equation back through $T$, then use
  $\partial_z(f\circ T)=(\partial_z f\circ T)a$ and
  $\partial_{\bar z}(f\circ T)=(\partial_{\bar z}f\circ T)\overline a$.
-/
theorem WeakBeltramiEquationOn.comp_conformal
    {U Ω : Set ℂ} {T a μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hU : MeasurableSet U)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (ha : ∀ z ∈ U, a z ≠ 0)
    (heq : WeakBeltramiEquationOn Ω μ df) :
    WeakBeltramiEquationOn U (conformalPullbackBeltrami T a μ)
      (fun z ↦ (df (T z)).comp (realLinearMapOfWirtinger (a z) 0)) := by
  have hpull := hT_qmp.ae heq
  filter_upwards [hpull, ae_restrict_mem hU] with z hz hzU
  change weakDBar ((df (T z)).comp (realLinearMapOfWirtinger (a z) 0)) =
    conformalPullbackBeltrami T a μ z *
      weakDZ ((df (T z)).comp (realLinearMapOfWirtinger (a z) 0))
  rw [weakDBar_comp_complexLinear, weakDZ_comp_complexLinear]
  change weakDBar (df (T z)) = μ (T z) * weakDZ (df (T z)) at hz
  rw [hz]
  dsimp [conformalPullbackBeltrami]
  field_simp [ha z hzU]

/--
%%handwave
name:
  Metric distortion under a conformal source-coordinate change
statement:
  Let $T:U\to\Omega$ preserve null sets and have complex derivative $a(z)$.
  If $Df$ satisfies
  $\|Df\|_{\mathrm{op}}^2\leq K\operatorname{Jac}f$ almost everywhere on
  $\Omega$, then the pulled-back differential
  $Df(T(z))\circ(\xi\mapsto a(z)\xi)$ satisfies the same inequality almost
  everywhere on $U$.
proof:
  Pull the original inequality back through $T$ and apply
  [metric distortion invariance under complex-linear precomposition](lean:JJMath.Quasiconformal.distortion_comp_complexLinear) pointwise.
-/
theorem metricDistortion_comp_conformal
    {U Ω : Set ℂ} {T a : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (h : ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict U,
      ‖(df (T z)).comp (realLinearMapOfWirtinger (a z) 0)‖ ^ 2 ≤
        K * weakJacobian
          ((df (T z)).comp (realLinearMapOfWirtinger (a z) 0)) := by
  have hpull := hT_qmp.ae h
  filter_upwards [hpull] with z hz
  exact distortion_comp_complexLinear _ _ _ hz

/--
%%handwave
name:
  Beltrami equation under complex-linear target postcomposition
statement:
  If $\partial_{\bar z}f=\mu\,\partial_z f$ almost everywhere on $\Omega$,
  then for every $a\in\mathbb C$ the postcomposed differential of $af$
  satisfies the same equation with coefficient $\mu$.
proof:
  Complex-linear postcomposition multiplies both Wirtinger derivatives by
  $a$.
-/
theorem WeakBeltramiEquationOn.postcomp_complexLinear
    {Ω : Set ℂ} {μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (a : ℂ) (heq : WeakBeltramiEquationOn Ω μ df) :
    WeakBeltramiEquationOn Ω μ
      (fun z ↦ (realLinearMapOfWirtinger a 0).comp (df z)) := by
  filter_upwards [heq] with z hz
  change weakDBar ((realLinearMapOfWirtinger a 0).comp (df z)) =
    μ z * weakDZ ((realLinearMapOfWirtinger a 0).comp (df z))
  rw [weakDBar_complexLinear_comp, weakDZ_complexLinear_comp]
  change weakDBar (df z) = μ z * weakDZ (df z) at hz
  rw [hz]
  ring

/--
%%handwave
name:
  Beltrami equation under a varying complex-linear target differential
statement:
  If $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere on $\Omega$
  and $a:\Omega\to\mathbb C$ is arbitrary, then the field
  $$
    z\longmapsto (\xi\mapsto a(z)\xi)\circ Df(z)
  $$
  satisfies the same Beltrami equation with coefficient $\mu$.
proof:
  At each point where the original equation holds, complex-linear
  postcomposition multiplies both Wirtinger derivatives by the same number
  $a(z)$.
-/
theorem WeakBeltramiEquationOn.postcomp_complexLinearField
    {Ω : Set ℂ} {μ a : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (heq : WeakBeltramiEquationOn Ω μ df) :
    WeakBeltramiEquationOn Ω μ
      (fun z ↦ (realLinearMapOfWirtinger (a z) 0).comp (df z)) := by
  filter_upwards [heq] with z hz
  change weakDBar ((realLinearMapOfWirtinger (a z) 0).comp (df z)) =
    μ z * weakDZ ((realLinearMapOfWirtinger (a z) 0).comp (df z))
  rw [weakDBar_complexLinear_comp, weakDZ_complexLinear_comp]
  change weakDBar (df z) = μ z * weakDZ (df z) at hz
  rw [hz]
  ring

/--
%%handwave
name:
  Beltrami equation under target inversion
statement:
  Let $f:\Omega\to\mathbb C^\times$ and suppose that $Df$ satisfies
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere on $\Omega$.
  Then the chain-rule field
  $$
    D\iota(f(z))\circ Df(z),\qquad \iota(w)=w^{-1},
  $$
  satisfies the same Beltrami equation with coefficient $\mu$.
proof:
  The real differential of inversion at every nonzero target value is
  complex-linear. Apply invariance under a varying complex-linear target
  differential and substitute the explicit differential of inversion.
-/
theorem WeakBeltramiEquationOn.postcomp_inversion
    {Ω : Set ℂ} {f μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hΩ : MeasurableSet Ω)
    (hf0 : ∀ z ∈ Ω, f z ≠ 0)
    (heq : WeakBeltramiEquationOn Ω μ df) :
    WeakBeltramiEquationOn Ω μ
      (fun z ↦ (fderiv ℝ (fun w : ℂ ↦ w⁻¹) (f z)).comp (df z)) := by
  have hfield := heq.postcomp_complexLinearField
    (a := fun z ↦ -(f z ^ 2)⁻¹)
  filter_upwards [hfield, ae_restrict_mem hΩ] with z hz hzΩ
  change weakDBar
      ((fderiv ℝ (fun w : ℂ ↦ w⁻¹) (f z)).comp (df z)) =
    μ z * weakDZ
      ((fderiv ℝ (fun w : ℂ ↦ w⁻¹) (f z)).comp (df z))
  change weakDBar
      ((realLinearMapOfWirtinger (-(f z ^ 2)⁻¹) 0).comp (df z)) =
    μ z * weakDZ
      ((realLinearMapOfWirtinger (-(f z ^ 2)⁻¹) 0).comp (df z)) at hz
  rw [fderiv_inversion (f z) (hf0 z hzΩ)]
  exact hz

/--
%%handwave
name:
  Metric distortion under complex-linear target postcomposition
statement:
  If $Df$ satisfies
  $\|Df\|_{\mathrm{op}}^2\leq K\operatorname{Jac}f$ almost everywhere on
  $\Omega$, then the postcomposed differential of $af$ satisfies the same
  inequality for every $a\in\mathbb C$.
proof:
  Apply [metric distortion invariance under complex-linear postcomposition](lean:JJMath.Quasiconformal.distortion_complexLinear_comp) almost everywhere.
-/
theorem metricDistortion_postcomp_complexLinear
    {Ω : Set ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ} (a : ℂ)
    (h : ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      ‖(realLinearMapOfWirtinger a 0).comp (df z)‖ ^ 2 ≤
        K * weakJacobian ((realLinearMapOfWirtinger a 0).comp (df z)) := by
  filter_upwards [h] with z hz
  exact distortion_complexLinear_comp _ _ _ hz

/--
%%handwave
name:
  Pullback of a Beltrami coefficient by inversion
statement:
  For $\iota(z)=z^{-1}$, define the reciprocal-coordinate coefficient by
  $$
    (\iota^*\mu)(z)
      =\mu(z^{-1})\frac{\overline{-z^{-2}}}{-z^{-2}},
  $$
  using totalized inversion at $z=0$.
-/
def inversionPullbackBeltrami (μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  conformalPullbackBeltrami (fun w : ℂ ↦ w⁻¹)
    (fun w : ℂ ↦ -(w ^ 2)⁻¹) μ z

/--
%%handwave
name:
  Measurability of the reciprocal-chart Beltrami coefficient
statement:
  If $\mu:\mathbb C\to\mathbb C$ is measurable up to a null set, then so is
  $$
    z\longmapsto \mu(z^{-1})
      \frac{\overline{-z^{-2}}}{-z^{-2}},
  $$
  where inversion is assigned its usual totalized value at $0$.
proof:
  Inversion preserves null sets, so $\mu\circ\iota$ is measurable up to a
  null set. The remaining factor is a quotient of measurable functions.
-/
theorem AEStronglyMeasurable.inversionPullbackBeltrami
    {μ : ℂ → ℂ} (hμ : AEStronglyMeasurable μ volume) :
    AEStronglyMeasurable (inversionPullbackBeltrami μ) volume := by
  have hcomp : AEStronglyMeasurable (fun z : ℂ ↦ μ z⁻¹) volume := by
    simpa [Function.comp_def] using
      hμ.comp_quasiMeasurePreserving inversion_quasiMeasurePreserving
  have ha : AEStronglyMeasurable (fun z : ℂ ↦ -(z ^ 2)⁻¹) volume := by
    exact (measurable_id.pow_const 2).inv.neg.aestronglyMeasurable
  have haInv : AEStronglyMeasurable
      (fun z : ℂ ↦ (-(z ^ 2)⁻¹)⁻¹) volume := by
    simpa only [inv_neg, inv_inv] using
      (measurable_id.pow_const 2).neg.aestronglyMeasurable
  change AEStronglyMeasurable
    (fun z : ℂ ↦ μ z⁻¹ * starRingEnd ℂ (-(z ^ 2)⁻¹) / (-(z ^ 2)⁻¹)) volume
  convert hcomp.mul (ha.star.mul haInv) using 1
  funext z
  simp only [Pi.mul_apply, Pi.star_apply, starRingEnd_apply,
    div_eq_mul_inv, mul_assoc]

/--
%%handwave
name:
  Almost-everywhere convergence of reciprocal-chart Beltrami coefficients
statement:
  If $\mu_\alpha(z)\to\mu(z)$ along a filter $\mathcal F$ for almost every
  $z\in\mathbb C$, then
  $$
    \mu_\alpha(z^{-1})\frac{\overline{-z^{-2}}}{-z^{-2}}
      \longrightarrow
    \mu(z^{-1})\frac{\overline{-z^{-2}}}{-z^{-2}}
  $$
  along $\mathcal F$ for almost every $z\in\mathbb C$.
proof:
  Pull the full-measure convergence set back through inversion, which
  preserves null sets, and multiply by the fixed reciprocal-chart factor.
-/
theorem ae_tendsto_inversionPullbackBeltrami
    {ι : Type*} {l : Filter ι} {μs : ι → ℂ → ℂ} {μ : ℂ → ℂ}
    (h : ∀ᵐ z ∂volume,
      Tendsto (fun a ↦ μs a z) l (nhds (μ z))) :
    ∀ᵐ z ∂volume, Tendsto
      (fun a ↦ inversionPullbackBeltrami (μs a) z) l
      (nhds (inversionPullbackBeltrami μ z)) := by
  have hpull := inversion_quasiMeasurePreserving.ae h
  filter_upwards [hpull] with z hz
  have ht := (hz.mul_const (starRingEnd ℂ (-(z ^ 2)⁻¹))).mul_const
    (-(z ^ 2)⁻¹)⁻¹
  simpa [inversionPullbackBeltrami, conformalPullbackBeltrami,
    div_eq_mul_inv, mul_assoc] using ht

/--
%%handwave
name:
  Global essential bound for a reciprocal-chart Beltrami coefficient
statement:
  If $|\mu(z)|\leq C$ for almost every $z\in\mathbb C$, then
  $$
    \left|\mu(z^{-1})
      \frac{\overline{-z^{-2}}}{-z^{-2}}\right|\leq C
  $$
  for almost every $z\in\mathbb C$.
proof:
  Pull the original bound back through inversion. Away from the null
  singleton $\{0\}$, the additional quotient has absolute value one.
-/
theorem ae_norm_inversionPullbackBeltrami_le
    {μ : ℂ → ℂ} {C : ℝ}
    (h : ∀ᵐ z ∂volume, ‖μ z‖ ≤ C) :
    ∀ᵐ z ∂volume, ‖inversionPullbackBeltrami μ z‖ ≤ C := by
  have hpull := inversion_quasiMeasurePreserving.ae h
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ)) :
        ∀ᵐ z : ℂ ∂volume, z ∈ ({0} : Set ℂ)ᶜ)
  filter_upwards [hpull, hne] with z hz hz0
  have ha0 : -(z ^ 2)⁻¹ ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hz0))
  have hfactor :
      ‖starRingEnd ℂ (-(z ^ 2)⁻¹) / (-(z ^ 2)⁻¹)‖ = 1 := by
    rw [norm_div, Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr ha0)]
  calc
    ‖inversionPullbackBeltrami μ z‖ =
        ‖μ z⁻¹‖ * ‖starRingEnd ℂ (-(z ^ 2)⁻¹) / (-(z ^ 2)⁻¹)‖ := by
      rw [inversionPullbackBeltrami, conformalPullbackBeltrami,
        mul_div_assoc, norm_mul]
    _ = ‖μ z⁻¹‖ := by rw [hfactor, mul_one]
    _ ≤ C := hz

/--
%%handwave
name:
  Whole-plane essential norm under inversion
statement:
  If $|\mu|\leq C$ almost everywhere on $\mathbb C$, then the coefficient
  obtained by reciprocal source coordinates also has essential norm at most
  $C$ on $\mathbb C$.
proof:
  Apply the global almost-everywhere reciprocal-coordinate bound and use
  that restricting planar measure to the whole plane changes nothing.
-/
theorem HasEssentialNormLEOn.inversionPullbackBeltrami_univ
    {μ : ℂ → ℂ} {C : ℝ}
    (hμ : HasEssentialNormLEOn Set.univ μ C) :
    HasEssentialNormLEOn Set.univ (inversionPullbackBeltrami μ) C := by
  have hglobal : ∀ᵐ z ∂volume, ‖μ z‖ ≤ C := by
    simpa [HasEssentialNormLEOn] using hμ
  simpa [HasEssentialNormLEOn] using
    ae_norm_inversionPullbackBeltrami_le hglobal

/--
%%handwave
name:
  Beltrami equation under inversion
statement:
  If $\partial_{\bar z}f=\mu\,\partial_z f$ almost everywhere on
  $\mathbb C^\times$, then $f\circ\iota$, where $\iota(z)=z^{-1}$, satisfies
  the Beltrami equation with coefficient
  $$
  \widetilde\mu(z)=\mu(z^{-1})
    \frac{\overline{-z^{-2}}}{-z^{-2}}
  $$
  almost everywhere on $\mathbb C^\times$.
proof:
  Apply the conformal source-coordinate formula with the differential of
  inversion, then identify that differential with multiplication by
  $-z^{-2}$ away from the origin.
-/
theorem WeakBeltramiEquationOn.comp_inversion
    {μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (heq : WeakBeltramiEquationOn ({0}ᶜ : Set ℂ) μ df) :
    WeakBeltramiEquationOn ({0}ᶜ : Set ℂ)
      (inversionPullbackBeltrami μ)
      (fun z ↦ (df z⁻¹).comp
        (fderiv ℝ (fun w : ℂ ↦ w⁻¹) z)) := by
  have hgen := heq.comp_conformal
    (U := ({0}ᶜ : Set ℂ)) (Ω := ({0}ᶜ : Set ℂ))
    isOpen_compl_singleton.measurableSet
    (inversion_quasiMeasurePreserving.restrict fun z hz ↦ inv_ne_zero hz)
    (fun z hz ↦ neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hz)))
  filter_upwards [hgen,
      ae_restrict_mem isOpen_compl_singleton.measurableSet] with z hz hz0
  change weakDBar ((df z⁻¹).comp (fderiv ℝ (fun w : ℂ ↦ w⁻¹) z)) =
    inversionPullbackBeltrami μ z *
      weakDZ ((df z⁻¹).comp (fderiv ℝ (fun w : ℂ ↦ w⁻¹) z))
  rw [fderiv_inversion z hz0]
  simpa [weakDBarField, weakDZField, inversionPullbackBeltrami] using hz

/--
%%handwave
name:
  Metric distortion under inversion
statement:
  If $Df$ satisfies
  $\|Df\|_{\mathrm{op}}^2\leq K\operatorname{Jac}f$ almost everywhere on
  $\mathbb C^\times$, then the pulled-back differential
  $Df(z^{-1})\circ D\iota(z)$ satisfies the same inequality almost everywhere
  on $\mathbb C^\times$.
proof:
  Pull the inequality back through inversion, replace $D\iota(z)$ by
  multiplication by $-z^{-2}$ away from zero, and use conformal invariance of
  pointwise metric distortion.
-/
theorem metricDistortion_comp_inversion
    {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (h : ∀ᵐ z ∂MeasureTheory.volume.restrict ({0}ᶜ : Set ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict ({0}ᶜ : Set ℂ),
      ‖(df z⁻¹).comp (fderiv ℝ (fun w : ℂ ↦ w⁻¹) z)‖ ^ 2 ≤
        K * weakJacobian
          ((df z⁻¹).comp (fderiv ℝ (fun w : ℂ ↦ w⁻¹) z)) := by
  have hgen := metricDistortion_comp_conformal
    (a := fun z : ℂ ↦ -(z ^ 2)⁻¹)
    (inversion_quasiMeasurePreserving.restrict
      (s := ({0}ᶜ : Set ℂ)) (t := ({0}ᶜ : Set ℂ))
      (fun z hz ↦ inv_ne_zero hz)) h
  filter_upwards [hgen,
      ae_restrict_mem isOpen_compl_singleton.measurableSet] with z hz hz0
  rw [fderiv_inversion z hz0]
  exact hz

end

end Quasiconformal

end JJMath
