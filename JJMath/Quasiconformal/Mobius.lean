import JJMath.Quasiconformal.ConformalChange
import JJMath.Quasiconformal.Basic
import JJMath.ProjectiveGeometry.RiemannSphere

/-!
# Möbius changes of planar coordinates

This file packages the fractional-linear action of a projective Möbius
representative as a conformal coordinate change between its two finite-chart
domains.  The pole is excluded from the local formulas and shown to be a null
set when proving global null-set preservation.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Finite domain of a Möbius transformation
statement:
  For a matrix
  $A=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)
  \in\operatorname{GL}_2(\mathbb C)$, define its finite source domain by
  $$
    U_A=\{z\in\mathbb C:cz+d\ne0\}.
  $$
-/
def mobiusFiniteDomain (A : MobiusRepresentative) : Set ℂ :=
  {z | mobiusFiniteDenom A z ≠ 0}

/--
%%handwave
name:
  The finite domain of a Möbius map is open
statement:
  For $A=(a_{ij})\in\operatorname{GL}_2(\mathbb C)$, the set
  $$
  U_A=\{z\in\mathbb C:a_{10}z+a_{11}\ne0\}
  $$
  is open.
proof:
  It is the inverse image of $\mathbb C\setminus\{0\}$ under the continuous
  affine denominator $z\mapsto a_{10}z+a_{11}$.
-/
theorem isOpen_mobiusFiniteDomain (A : MobiusRepresentative) :
    IsOpen (mobiusFiniteDomain A) := by
  have hcont : Continuous (mobiusFiniteDenom A) := by
    exact ((continuous_const.mul continuous_id).add continuous_const)
  exact isOpen_compl_singleton.preimage hcont

/--
%%handwave
name:
  The pole of a Möbius map is a null set
statement:
  For every $A\in\operatorname{GL}_2(\mathbb C)$, the complement of $U_A$
  has planar Lebesgue measure zero.
proof:
  If $a_{10}=0$, invertibility forces $a_{11}\ne0$ and the complement is
  empty. Otherwise it is the singleton $\{-a_{11}/a_{10}\}$.
-/
theorem volume_compl_mobiusFiniteDomain (A : MobiusRepresentative) :
    MeasureTheory.volume (mobiusFiniteDomain A)ᶜ = 0 := by
  by_cases hc : A 1 0 = 0
  · have hd : A 1 1 ≠ 0 := by
      intro hd
      apply A.det_ne_zero
      simp [Matrix.det_fin_two, hc, hd]
    have hU : mobiusFiniteDomain A = Set.univ := by
      ext z
      simp [mobiusFiniteDomain, mobiusFiniteDenom, hc, hd]
    simp [hU]
  · have hzero : (mobiusFiniteDomain A)ᶜ = {-A 1 1 / A 1 0} := by
      ext z
      simp only [mobiusFiniteDomain, mem_compl_iff, mem_setOf_eq,
        not_not, mem_singleton_iff]
      constructor
      · intro hz
        apply (eq_div_iff hc).2
        simp only [mobiusFiniteDenom] at hz
        linear_combination hz
      · intro hz
        simp only [mobiusFiniteDenom]
        rw [hz]
        field_simp [hc]
        ring
    rw [hzero]
    exact measure_singleton _

/--
%%handwave
name:
  A finite Möbius map lands in the inverse finite domain
statement:
  If $z\in U_A$, then
  $$
  T_A(z)=\frac{a_{00}z+a_{01}}{a_{10}z+a_{11}}
  $$
  belongs to $U_{A^{-1}}$.
proof:
  The spherical actions of $A$ and $A^{-1}$ are inverse. Since $T_A(z)$ and
  $z$ are finite, the denominator of the inverse finite formula cannot
  vanish at $T_A(z)$.
-/
theorem mobiusFiniteFormula_mapsTo_inverseDomain (A : MobiusRepresentative) :
    MapsTo (mobiusFiniteFormula A) (mobiusFiniteDomain A)
      (mobiusFiniteDomain A⁻¹) := by
  intro z hz
  have hforward :=
    mobiusRepresentative_smul_coe_eq_mobiusFiniteFormula A hz
  have hinverse :
      A⁻¹ • ((mobiusFiniteFormula A z : ℂ) : RiemannSphere) =
        (z : RiemannSphere) := by
    rw [← hforward]
    simp
  exact mobiusFiniteDenom_ne_zero_of_smul_coe_eq_coe A⁻¹ hinverse

/--
%%handwave
name:
  Inverse finite Möbius formula
statement:
  For every $z\in U_A$,
  $$
  T_{A^{-1}}(T_A(z))=z.
  $$
proof:
  Apply the inverse projective action to the finite spherical identity for
  $T_A(z)$ and recover the inverse fractional-linear formula.
-/
theorem mobiusFiniteFormula_inverse (A : MobiusRepresentative) (z : ℂ)
    (hz : z ∈ mobiusFiniteDomain A) :
    mobiusFiniteFormula A⁻¹ (mobiusFiniteFormula A z) = z := by
  have hforward :=
    mobiusRepresentative_smul_coe_eq_mobiusFiniteFormula A hz
  have hinverse :
      A⁻¹ • ((mobiusFiniteFormula A z : ℂ) : RiemannSphere) =
        (z : RiemannSphere) := by
    rw [← hforward]
    simp
  exact mobiusFiniteFormula_eq_of_smul_coe_eq_coe A⁻¹ hinverse

/--
%%handwave
name:
  Finite Möbius formulas are locally Lipschitz off their pole
statement:
  The fractional-linear map $T_A$ is locally Lipschitz on $U_A$.
proof:
  At every point of $U_A$ the denominator is nonzero, so $T_A$ is complex
  smooth and therefore Lipschitz on a sufficiently small neighborhood.
-/
theorem mobiusFiniteFormula_locallyLipschitzOn (A : MobiusRepresentative) :
    LocallyLipschitzOn (mobiusFiniteDomain A)
      (mobiusFiniteFormula A) := by
  intro z hz
  rcases ((mobiusFiniteFormula_contDiffAt A hz).restrict_scalars ℝ).of_le
      (by simp : (1 : WithTop ℕ∞) ≤ ⊤) |>.exists_lipschitzOnWith with
    ⟨C, V, hV, hlip⟩
  refine ⟨C, V, ?_, hlip⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨V, hV, inter_subset_left⟩

/--
%%handwave
name:
  Finite Möbius homeomorphism
statement:
  The fractional-linear formula
  $$
    T_A(z)=\frac{az+b}{cz+d}
  $$
  defines a homeomorphism $U_A\to U_{A^{-1}}$ whose inverse is
  $T_{A^{-1}}$.
-/
def mobiusFiniteHomeomorph (A : MobiusRepresentative) :
    mobiusFiniteDomain A ≃ₜ mobiusFiniteDomain A⁻¹ where
  toFun z := ⟨mobiusFiniteFormula A z,
    mobiusFiniteFormula_mapsTo_inverseDomain A z.2⟩
  invFun z := ⟨mobiusFiniteFormula A⁻¹ z,
    mobiusFiniteFormula_mapsTo_inverseDomain A⁻¹ z.2⟩
  left_inv z := Subtype.ext (mobiusFiniteFormula_inverse A z z.2)
  right_inv z := Subtype.ext (mobiusFiniteFormula_inverse A⁻¹ z z.2)
  continuous_toFun :=
    (mobiusFiniteFormula_locallyLipschitzOn A).continuousOn.mapsToRestrict
      (mobiusFiniteFormula_mapsTo_inverseDomain A)
  continuous_invFun :=
    (mobiusFiniteFormula_locallyLipschitzOn A⁻¹).continuousOn.mapsToRestrict
      (mobiusFiniteFormula_mapsTo_inverseDomain A⁻¹)

/--
%%handwave
name:
  Evaluation of the finite Möbius homeomorphism
statement:
  For every $z\in U_A$, the underlying complex value of the finite Möbius
  homeomorphism is
  $$
  T_A(z)=\frac{a_{00}z+a_{01}}{a_{10}z+a_{11}}.
  $$
proof:
  This is the defining formula of the homeomorphism.
-/
@[simp] theorem mobiusFiniteHomeomorph_apply (A : MobiusRepresentative)
    (z : mobiusFiniteDomain A) :
    (mobiusFiniteHomeomorph A z : ℂ) = mobiusFiniteFormula A z := rfl

/--
%%handwave
name:
  Ambient representative of a finite Möbius homeomorphism
statement:
  The extension by zero of $T_A:U_A\to U_{A^{-1}}$ agrees on all of
  $\mathbb C$ with the totalized fractional-linear formula
  $$
  z\longmapsto\frac{a_{00}z+a_{01}}{a_{10}z+a_{11}}.
  $$
proof:
  On $U_A$ this is the defining formula. Outside $U_A$ the denominator
  vanishes, so both the ambient extension and the totalized quotient are
  zero.
-/
theorem ambientMap_mobiusFiniteHomeomorph (A : MobiusRepresentative) :
    ambientMap (mobiusFiniteHomeomorph A) = mobiusFiniteFormula A := by
  funext z
  by_cases hz : z ∈ mobiusFiniteDomain A
  · simp [ambientMap, hz]
  · have hden : mobiusFiniteDenom A z = 0 := by
      simpa [mobiusFiniteDomain] using hz
    simp [ambientMap, hz, mobiusFiniteFormula, hden]

/--
%%handwave
name:
  Difference of two finite Möbius values
statement:
  If $z,w\in U_A$, then
  $$
  T_A(w)-T_A(z)=
    \frac{\det(A)(w-z)}
      {(a_{10}w+a_{11})(a_{10}z+a_{11})}.
  $$
proof:
  Put the two fractions over their common denominator; the numerator
  simplifies to $\det(A)(w-z)$.
-/
theorem mobiusFiniteFormula_sub (A : MobiusRepresentative) {z w : ℂ}
    (hz : mobiusFiniteDenom A z ≠ 0) (hw : mobiusFiniteDenom A w ≠ 0) :
    mobiusFiniteFormula A w - mobiusFiniteFormula A z =
      A.det.val * (w - z) /
        (mobiusFiniteDenom A w * mobiusFiniteDenom A z) := by
  rw [mobiusFiniteFormula, mobiusFiniteFormula,
    div_sub_div _ _ hw hz]
  congr 1
  simp only [mobiusFiniteNum, mobiusFiniteDenom]
  have hdet : A.det.val = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    simp [Matrix.det_fin_two]
  rw [hdet]
  ring

/--
%%handwave
name:
  Finite Möbius homeomorphisms preserve planar orientation
statement:
  The homeomorphism $T_A:U_A\to U_{A^{-1}}$ preserves planar orientation.
proof:
  Around $z\in U_A$, choose a circle contained in $U_A$.  After translating
  by $T_A(z)$ and normalizing at the initial point, its image loop is
  $$
  e^{2\pi i t}\frac{D+cr}{D+cr e^{2\pi i t}},
  \qquad D=a_{10}z+a_{11},\quad c=a_{10}.
  $$
  Replacing $r$ continuously by $(1-s)r$ deforms this loop through
  nonzero loops to $e^{2\pi i t}$, so its winding number is positive.
-/
theorem preservesPlanarOrientation_mobiusFiniteHomeomorph
    (A : MobiusRepresentative) :
    PreservesPlanarOrientation (mobiusFiniteHomeomorph A) := by
  intro z
  obtain ⟨ε, hε, hεball⟩ :=
    (Metric.isOpen_iff.mp (isOpen_mobiusFiniteDomain A)) z z.2
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; linarith
  have hball : Metric.closedBall (z : ℂ) r ⊆ mobiusFiniteDomain A := by
    intro w hw
    apply hεball
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hrε
  let hcircle := circlePoint_mem_of_closedBall_subset z hr hball
  let D : ℂ := mobiusFiniteDenom A z
  let c : ℂ := A 1 0
  let E : unitInterval → ℂ := fun t ↦
    Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  let ρ : unitInterval → ℝ := fun s ↦ 1 - (s : ℝ)
  have hρ_nonneg (s : unitInterval) : 0 ≤ ρ s := by
    exact sub_nonneg.mpr s.2.2
  have hρ_le (s : unitInterval) : ρ s ≤ 1 := by
    dsimp [ρ]
    linarith [s.2.1]
  have hscaled_mem (s t : unitInterval) :
      circlePoint z (ρ s * r) t ∈ mobiusFiniteDomain A := by
    apply hball
    rw [Metric.mem_closedBall]
    by_cases hs : ρ s = 0
    · simp [hs, circlePoint, hr.le]
    · have hscaled_pos : 0 < ρ s * r :=
        mul_pos (lt_of_le_of_ne (hρ_nonneg s) (Ne.symm hs)) hr
      rw [dist_circlePoint_center z hscaled_pos t]
      exact mul_le_of_le_one_left hr.le (hρ_le s)
  have hden_scaled (s t : unitInterval) :
      D + (ρ s : ℂ) * (c * r) * E t ≠ 0 := by
    have hm := hscaled_mem s t
    have heq : D + (ρ s : ℂ) * (c * r) * E t =
        mobiusFiniteDenom A (circlePoint z (ρ s * r) t) := by
      simp [D, c, E, circlePoint, mobiusFiniteDenom]
      ring
    rw [heq]
    exact hm
  have hnum_scaled (s : unitInterval) :
      D + (ρ s : ℂ) * (c * r) ≠ 0 := by
    have hm := hscaled_mem s 0
    have heq : D + (ρ s : ℂ) * (c * r) =
        mobiusFiniteDenom A (circlePoint z (ρ s * r) 0) := by
      simp [D, c, circlePoint, mobiusFiniteDenom]
      ring
    rw [heq]
    exact hm
  have hD : D ≠ 0 := by exact z.2
  let H : C(unitInterval × unitInterval, PuncturedComplex) :=
    ⟨fun x ↦
      ⟨E x.2 *
          ((D + (ρ x.1 : ℂ) * (c * r)) /
            (D + (ρ x.1 : ℂ) * (c * r) * E x.2)),
        mul_ne_zero (Complex.exp_ne_zero _)
          (div_ne_zero (hnum_scaled x.1) (hden_scaled x.1 x.2))⟩, by
      apply Continuous.subtype_mk
      apply Continuous.mul
      · exact Complex.continuous_exp.comp (by fun_prop)
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · exact fun x ↦ hden_scaled x.1 x.2⟩
  refine ⟨r, hr, hball, ⟨{
    toFun := H
    continuous_toFun := H.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro t
    apply Subtype.ext
    change E t * ((D + (ρ 0 : ℂ) * (c * r)) /
        (D + (ρ 0 : ℂ) * (c * r) * E t)) =
      ((mobiusFiniteFormula A (circlePoint z r t) -
        mobiusFiniteFormula A z) /
      (mobiusFiniteFormula A (circlePoint z r 0) -
        mobiusFiniteFormula A z))
    have hz : mobiusFiniteDenom A z ≠ 0 := z.2
    have ht : mobiusFiniteDenom A (circlePoint z r t) ≠ 0 := hcircle t
    have h0 : mobiusFiniteDenom A (circlePoint z r 0) ≠ 0 := hcircle 0
    have hden_t_eq : mobiusFiniteDenom A (circlePoint z r t) =
        D + c * r * E t := by
      simp [D, c, E, circlePoint, mobiusFiniteDenom]
      ring
    have hden_0_eq : mobiusFiniteDenom A (circlePoint z r 0) =
        D + c * r := by
      simp [D, c, circlePoint, mobiusFiniteDenom]
      ring
    have hdiff_t : circlePoint z r t - z = (r : ℂ) * E t := by
      simp [circlePoint, E]
    have hdiff_0 : circlePoint z r 0 - z = (r : ℂ) := by
      simp [circlePoint]
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    rw [mobiusFiniteFormula_sub A hz ht, mobiusFiniteFormula_sub A hz h0]
    rw [hden_t_eq, hden_0_eq, hdiff_t, hdiff_0]
    simp only [ρ, Set.Icc.coe_zero, sub_zero, Complex.ofReal_one, one_mul]
    field_simp [A.det_ne_zero, hD, hrC, hnum_scaled 0,
      hden_scaled 0 t]
  · intro t
    apply Subtype.ext
    simp [H, ρ, E, positiveCircleLoop, hD]
  · intro s t ht
    apply Subtype.ext
    rcases ht with rfl | rfl
    · simp [H, E, hnum_scaled]
    · simp [H, E, hnum_scaled, Complex.exp_mul_I]

/--
%%handwave
name:
  Complex derivative of a finite Möbius transformation
statement:
  For
  $A=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$, define
  $$
    T_A'(z)=\frac{\det A}{(cz+d)^2}.
  $$
-/
def mobiusFiniteDerivative (A : MobiusRepresentative) (z : ℂ) : ℂ :=
  A.det.val / (mobiusFiniteDenom A z) ^ 2

/--
%%handwave
name:
  Real differential of a finite Möbius formula
statement:
  For $z\in U_A$, the real differential of $T_A$ is
  $$
  DT_A(z)(\xi)=\frac{\det A}{(a_{10}z+a_{11})^2}\,\xi.
  $$
proof:
  Restrict the complex derivative of the fractional-linear formula to real
  scalars and identify the resulting complex-linear map.
-/
theorem fderiv_mobiusFiniteFormula (A : MobiusRepresentative) {z : ℂ}
    (hz : z ∈ mobiusFiniteDomain A) :
    fderiv ℝ (mobiusFiniteFormula A) z =
      realLinearMapOfWirtinger (mobiusFiniteDerivative A z) 0 := by
  rw [(mobiusFiniteFormula_hasDerivAt A hz).complexToReal_fderiv.fderiv]
  ext ξ
  simp [mobiusFiniteDerivative, realLinearMapOfWirtinger]

/--
%%handwave
name:
  Finite Möbius formulas preserve planar null sets
statement:
  For every $A\in\operatorname{GL}_2(\mathbb C)$, the totalized finite formula
  $T_A:\mathbb C\to\mathbb C$ is quasi-measure-preserving for planar
  Lebesgue measure.
proof:
  Given a null set, remove the pole of $T_{A^{-1}}$ and apply the classical
  change-of-variables formula to $T_{A^{-1}}$ there. Its image is null and
  contains the preimage under $T_A$ except possibly for the pole of $T_A$,
  which is a singleton or empty.
-/
theorem mobiusFiniteFormula_quasiMeasurePreserving
    (A : MobiusRepresentative) :
    Measure.QuasiMeasurePreserving (mobiusFiniteFormula A)
      MeasureTheory.volume MeasureTheory.volume := by
  have hmeas_num : Measurable (mobiusFiniteNum A) := by
    exact ((measurable_const.mul measurable_id).add measurable_const)
  have hmeas_den : Measurable (mobiusFiniteDenom A) := by
    exact ((measurable_const.mul measurable_id).add measurable_const)
  have hmeas : Measurable (mobiusFiniteFormula A) := by
    exact hmeas_num.div hmeas_den
  refine ⟨hmeas, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs_zero
  rw [Measure.map_apply hmeas hs]
  let V := mobiusFiniteDomain A⁻¹
  let t : Set ℂ := s ∩ V
  have ht_meas : MeasurableSet t :=
    hs.inter (isOpen_mobiusFiniteDomain A⁻¹).measurableSet
  have ht_zero : MeasureTheory.volume t = 0 :=
    measure_mono_null inter_subset_left hs_zero
  let dS : ℂ → ℂ →L[ℝ] ℂ := fun z ↦
    realLinearMapOfWirtinger (mobiusFiniteDerivative A⁻¹ z) 0
  have hderiv : ∀ z ∈ t,
      HasFDerivWithinAt (mobiusFiniteFormula A⁻¹) (dS z) t z := by
    intro z hz
    convert ((mobiusFiniteFormula_hasDerivAt A⁻¹ hz.2).complexToReal_fderiv).hasFDerivWithinAt
      using 1
    ext ξ
    simp [dS, mobiusFiniteDerivative, realLinearMapOfWirtinger]
  have hinj : Set.InjOn (mobiusFiniteFormula A⁻¹) t := by
    intro z hz w hw hzw
    have hz' := mobiusFiniteFormula_inverse A⁻¹ z hz.2
    have hw' := mobiusFiniteFormula_inverse A⁻¹ w hw.2
    rw [hzw] at hz'
    exact hz'.symm.trans hw'
  have hcov :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (MeasureTheory.volume : Measure ℂ) ht_meas hderiv hinj
      (fun _ : ℂ ↦ (1 : ℝ≥0∞))
  have himage_zero :
      MeasureTheory.volume (mobiusFiniteFormula A⁻¹ '' t) = 0 := by
    rw [MeasureTheory.setLIntegral_one] at hcov
    rw [hcov]
    exact setLIntegral_measure_zero t _ ht_zero
  have hsubset :
      mobiusFiniteFormula A ⁻¹' s ⊆
        mobiusFiniteFormula A⁻¹ '' t ∪ (mobiusFiniteDomain A)ᶜ := by
    intro z hz
    by_cases hzU : z ∈ mobiusFiniteDomain A
    · left
      refine ⟨mobiusFiniteFormula A z,
        ⟨hz, mobiusFiniteFormula_mapsTo_inverseDomain A hzU⟩, ?_⟩
      exact mobiusFiniteFormula_inverse A z hzU
    · right
      exact hzU
  exact measure_mono_null hsubset
    (measure_union_null himage_zero (volume_compl_mobiusFiniteDomain A))

/--
%%handwave
name:
  Local Sobolev regularity under a finite Möbius coordinate change
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(U_{A^{-1}},\mathbb C)$ have weak
  differential $Df$. Then $f\circ T_A$ belongs to
  $W^{1,2}_{\mathrm{loc}}(U_A,\mathbb C)$ with weak differential
  $$
  z\longmapsto Df(T_A(z))\circ DT_A(z).
  $$
proof:
  The maps $T_A:U_A\to U_{A^{-1}}$ and $T_{A^{-1}}$ are inverse, locally
  Lipschitz, and preserve null sets in both directions. Apply the local
  Sobolev chain rule.
-/
theorem IsLocalW12On.comp_mobiusFiniteFormula
    (A : MobiusRepresentative) {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On (mobiusFiniteDomain A⁻¹) f df) :
    IsLocalW12On (mobiusFiniteDomain A)
      (fun z ↦ f (mobiusFiniteFormula A z))
      (fun z ↦ (df (mobiusFiniteFormula A z)).comp
        (fderiv ℝ (mobiusFiniteFormula A) z)) := by
  apply h.comp_locallyBiLipschitz
    (isOpen_mobiusFiniteDomain A)
    (mobiusFiniteFormula_mapsTo_inverseDomain A)
    (mobiusFiniteFormula_mapsTo_inverseDomain A⁻¹)
  · exact mobiusFiniteFormula_inverse A
  · exact mobiusFiniteFormula_inverse A⁻¹
  · exact mobiusFiniteFormula_locallyLipschitzOn A
  · exact mobiusFiniteFormula_locallyLipschitzOn A⁻¹
  · exact (mobiusFiniteFormula_quasiMeasurePreserving A).restrict
      (mobiusFiniteFormula_mapsTo_inverseDomain A)
  · exact (mobiusFiniteFormula_quasiMeasurePreserving A⁻¹).restrict
      (mobiusFiniteFormula_mapsTo_inverseDomain A⁻¹)

/--
%%handwave
name:
  Local Sobolev regularity of a finite Möbius formula
statement:
  The map $T_A$ belongs to $W^{1,2}_{\mathrm{loc}}(U_A,\mathbb C)$ with
  weak differential given by its classical real differential.
proof:
  Compose the locally Sobolev identity map on $U_{A^{-1}}$ with the locally
  bi-Lipschitz change of coordinates $T_A:U_A\to U_{A^{-1}}$ and apply the
  local Sobolev chain rule.
-/
theorem isLocalW12On_mobiusFiniteFormula (A : MobiusRepresentative) :
    IsLocalW12On (mobiusFiniteDomain A) (mobiusFiniteFormula A)
      (fun z ↦ (realLinearMapOfWirtinger 1 0).comp
        (fderiv ℝ (mobiusFiniteFormula A) z)) := by
  have h :=
    (isLocalW12On_affineMap (isOpen_mobiusFiniteDomain A⁻¹) 1 0 0).comp_mobiusFiniteFormula A
  simpa [affineMap] using h

/--
%%handwave
name:
  Finite Möbius homeomorphisms are one-quasiconformal
statement:
  For every $A\in\operatorname{GL}_2(\mathbb C)$, the homeomorphism
  $T_A:U_A\to U_{A^{-1}}$ is $1$-quasiconformal.
proof:
  The map preserves orientation and is locally Sobolev. At each point of
  $U_A$ its differential is complex multiplication by
  $\det(A)/(a_{10}z+a_{11})^2$, whose operator norm squared equals its real
  Jacobian.
-/
theorem isOneQuasiconformalBetween_mobiusFiniteHomeomorph
    (A : MobiusRepresentative) :
    IsKQuasiconformalBetween 1 (mobiusFiniteHomeomorph A) := by
  refine ⟨le_rfl, isOpen_mobiusFiniteDomain A⁻¹,
    preservesPlanarOrientation_mobiusFiniteHomeomorph A, ?_⟩
  let df : ℂ → ℂ →L[ℝ] ℂ := fun z ↦
    (realLinearMapOfWirtinger 1 0).comp
      (fderiv ℝ (mobiusFiniteFormula A) z)
  refine ⟨df, ?_, ?_⟩
  · rw [ambientMap_mobiusFiniteHomeomorph]
    exact isLocalW12On_mobiusFiniteFormula A
  · filter_upwards [ae_restrict_mem
      (isOpen_mobiusFiniteDomain A).measurableSet] with z hz
    rw [show df z = (realLinearMapOfWirtinger 1 0).comp
        (realLinearMapOfWirtinger (mobiusFiniteDerivative A z) 0) by
      dsimp [df]
      rw [fderiv_mobiusFiniteFormula A hz]]
    rw [realLinearMapOfWirtinger_comp]
    simp

end

end Quasiconformal

end JJMath
