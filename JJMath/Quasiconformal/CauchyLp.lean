import JJMath.Quasiconformal.BeurlingAboveTwo
import JJMath.Quasiconformal.BeurlingApproximation

/-!
# The Cauchy transform of compactly supported `Lᵖ` data

This file extends the pointwise Cauchy integral from smooth test functions to
compactly supported data in an exponent strictly above two.  The conjugate
exponent is then strictly below two, exactly the local integrability range of
the planar reciprocal kernel.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Local integrability of a power of the reciprocal kernel
statement:
  If $0<q<2$, then
  $$
    z\longmapsto |z^{-1}|^q
  $$
  is locally integrable on the complex plane.
proof:
  The integrand equals $|z|^{-q}$, and the singularity is locally
  integrable in real dimension two precisely when $q<2$.
-/
theorem locallyIntegrable_norm_inv_complex_rpow
    {q : ℝ} (_hq0 : 0 < q) (hq2 : q < 2) :
    LocallyIntegrable (fun z : ℂ ↦ ‖z⁻¹‖ ^ q)
    (volume : Measure ℂ) := by
  refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℝ)
    (μ := (volume : Measure ℂ)) (C := 1) (α := q)
    (by simp) (by simpa using hq2) ?_ ?_
  · filter_upwards with z
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) q),
      norm_inv, Real.inv_rpow (norm_nonneg z), Real.rpow_neg (norm_nonneg z)]
    simp
  · simpa only [Function.comp_apply] using
      ((measurable_inv.comp measurable_id).norm.pow_const q).aestronglyMeasurable

/--
%%handwave
name:
  Local integrability of powers of centered Cauchy kernels
statement:
  If $0<q<2$ and $z\in\mathbb C$, then
  $$
    w\longmapsto |z-w|^{-q}
  $$
  is locally integrable on the complex plane.
proof:
  Translate and reflect the locally integrable function
  $w\mapsto|w|^{-q}$ by the measure-preserving isometry $w\mapsto z-w$.
-/
theorem locallyIntegrable_norm_planarCauchyKernel_rpow
    (z : ℂ) {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) :
    LocallyIntegrable (fun w : ℂ ↦ ‖planarCauchyKernel z w‖ ^ q)
      (volume : Measure ℂ) := by
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.neg ℂ).trans (Homeomorph.addRight z)
  have he_map : Measure.map e (volume : Measure ℂ) = volume := by
    change Measure.map ((Homeomorph.addRight z) ∘ (Homeomorph.neg ℂ))
      (volume : Measure ℂ) = volume
    rw [← Measure.map_map (Homeomorph.addRight z).continuous.measurable
      (Homeomorph.neg ℂ).continuous.measurable]
    change Measure.map (fun w : ℂ ↦ w + z)
      (Measure.map (fun w : ℂ ↦ -w) volume) = volume
    rw [Measure.map_neg_eq_self]
    exact map_add_right_eq_self volume z
  have hcomp : LocallyIntegrable
      ((fun w : ℂ ↦ ‖w⁻¹‖ ^ q) ∘ e) (volume : Measure ℂ) := by
    rw [← locallyIntegrable_map_homeomorph e, he_map]
    exact locallyIntegrable_norm_inv_complex_rpow hq0 hq2
  simpa [planarCauchyKernel, e, Function.comp_def, sub_eq_add_neg,
    add_comm] using hcomp

/--
%%handwave
name:
  A compactly truncated Cauchy kernel belongs to $L^q$
statement:
  Let $0<q<2$, let $z\in\mathbb C$, and let $K\subseteq\mathbb C$ be
  compact. Then
  $$
    \mathbf 1_K(w)(z-w)^{-1}\in L^q(\mathbb C).
  $$
proof:
  The $q$th power of the kernel norm is locally integrable, hence integrable
  on $K$. The usual integral characterization of finite-exponent $L^q$
  membership gives the result after extending by zero outside $K$.
-/
theorem memLp_indicator_planarCauchyKernel_of_isCompact
    (z : ℂ) {K : Set ℂ} (hK : IsCompact K)
    {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) :
    MemLp (K.indicator (planarCauchyKernel z)) (ENNReal.ofReal q)
      (volume : Measure ℂ) := by
  have hlocal := locallyIntegrable_norm_planarCauchyKernel_rpow z hq0 hq2
  have hpow : Integrable
      (fun w : ℂ ↦ ‖planarCauchyKernel z w‖ ^ q)
      (volume.restrict K) :=
    hlocal.integrableOn_isCompact hK
  have hmeas : AEStronglyMeasurable (planarCauchyKernel z)
      (volume.restrict K) :=
    (locallyIntegrable_planarCauchyKernel z).aestronglyMeasurable.restrict
  have hmem : MemLp (planarCauchyKernel z) (ENNReal.ofReal q)
      (volume.restrict K) := by
    apply (integrable_norm_rpow_iff hmeas
      (ENNReal.ofReal_ne_zero_iff.mpr hq0)
      ENNReal.ofReal_ne_top).1
    simpa [ENNReal.toReal_ofReal hq0.le] using hpow
  exact (memLp_indicator_iff_restrict hK.measurableSet).2 hmem

/--
%%handwave
name:
  Measure preservation of a reflected translation
statement:
  For every $z\in\mathbb C$, the affine isometry
  $$
    w\longmapsto z-w
  $$
  preserves planar Lebesgue measure.
proof:
  Negation preserves planar Lebesgue measure, as does translation. Their
  composition is $w\mapsto z-w$.
-/
theorem measurePreserving_sub_left_volume (z : ℂ) :
    MeasurePreserving (fun w : ℂ ↦ z - w)
      (volume : Measure ℂ) (volume : Measure ℂ) := by
  have h := (MeasureTheory.measurePreserving_add_right
      (volume : Measure ℂ) z).comp
    (Measure.measurePreserving_neg (volume : Measure ℂ))
  simpa [Function.comp_def, sub_eq_add_neg, add_comm] using h

/--
%%handwave
name:
  Translation invariance of truncated Cauchy-kernel seminorms
statement:
  For every exponent $q$, center $z\in\mathbb C$, and radius $R$,
  $$
    \left\|\mathbf 1_{\overline B(z,R)}(w)(z-w)^{-1}\right\|_{L^q_w}
      =
    \left\|\mathbf 1_{\overline B(0,R)}(u)u^{-1}\right\|_{L^q_u}.
  $$
proof:
  Compose the function on the right with the measure-preserving affine
  isometry $w\mapsto z-w$. Its pullback is exactly the function on the
  left.
-/
theorem eLpNorm_indicator_planarCauchyKernel_closedBall_eq
    (z : ℂ) (R : ℝ) (q : ENNReal) :
    eLpNorm
        ((Metric.closedBall z R).indicator (planarCauchyKernel z))
        q (volume : Measure ℂ) =
      eLpNorm
        ((Metric.closedBall (0 : ℂ) R).indicator (fun u : ℂ ↦ u⁻¹))
        q (volume : Measure ℂ) := by
  let g : ℂ → ℂ :=
    (Metric.closedBall (0 : ℂ) R).indicator (fun u : ℂ ↦ u⁻¹)
  have hgmeas : AEStronglyMeasurable g (volume : Measure ℂ) :=
    locallyIntegrable_inv_complex.aestronglyMeasurable.indicator
      measurableSet_closedBall
  have heq := eLpNorm_comp_measurePreserving (p := q) hgmeas
    (measurePreserving_sub_left_volume z)
  calc
    eLpNorm
        ((Metric.closedBall z R).indicator (planarCauchyKernel z))
        q (volume : Measure ℂ) =
        eLpNorm (g ∘ fun w : ℂ ↦ z - w) q (volume : Measure ℂ) := by
      congr 1
      funext w
      simp only [g, Function.comp_apply]
      by_cases hw : w ∈ Metric.closedBall z R
      · rw [Set.indicator_of_mem hw]
        have hzw : z - w ∈ Metric.closedBall (0 : ℂ) R := by
          simpa [Metric.mem_closedBall, dist_zero_right, norm_sub_rev,
            dist_eq_norm] using hw
        rw [Set.indicator_of_mem hzw]
        rfl
      · rw [Set.indicator_of_notMem hw]
        have hzw : z - w ∉ Metric.closedBall (0 : ℂ) R := by
          intro hzw
          apply hw
          simpa [Metric.mem_closedBall, dist_zero_right, norm_sub_rev,
            dist_eq_norm] using hzw
        rw [Set.indicator_of_notMem hzw]
    _ = eLpNorm g q (volume : Measure ℂ) := heq
    _ = eLpNorm
        ((Metric.closedBall (0 : ℂ) R).indicator (fun u : ℂ ↦ u⁻¹))
        q (volume : Measure ℂ) := rfl

/--
%%handwave
name:
  Uniform local bound for truncated Cauchy kernels
statement:
  Let $z\in\overline B(z_0,A)$. For every radius $B$ and exponent $q$,
  $$
    \left\|\mathbf 1_{\overline B(0,B)}(w)(z-w)^{-1}\right\|_{L^q_w}
      \leq
    \left\|\mathbf 1_{\overline B(0,|z_0|+A+B)}(u)u^{-1}\right\|_{L^q_u}.
  $$
proof:
  If $|w|\leq B$ and $|z-z_0|\leq A$, then
  $|w-z|\leq |z_0|+A+B$. Enlarge the support disk of the centered kernel
  and then use translation invariance of its $L^q$ seminorm.
-/
theorem eLpNorm_indicator_planarCauchyKernel_closedBall_le
    {z z0 : ℂ} {A B : ℝ} (hz : z ∈ Metric.closedBall z0 A)
    (q : ENNReal) :
    eLpNorm
        ((Metric.closedBall (0 : ℂ) B).indicator
          (planarCauchyKernel z)) q (volume : Measure ℂ) ≤
      eLpNorm
        ((Metric.closedBall (0 : ℂ) (‖z0‖ + A + B)).indicator
          (fun u : ℂ ↦ u⁻¹)) q (volume : Measure ℂ) := by
  calc
    eLpNorm
        ((Metric.closedBall (0 : ℂ) B).indicator
          (planarCauchyKernel z)) q (volume : Measure ℂ) ≤
        eLpNorm
          ((Metric.closedBall z (‖z0‖ + A + B)).indicator
            (planarCauchyKernel z)) q (volume : Measure ℂ) := by
      apply eLpNorm_mono_ae
      filter_upwards with w
      by_cases hw : w ∈ Metric.closedBall (0 : ℂ) B
      · have hzNorm : ‖z‖ ≤ ‖z0‖ + A := by
          calc
            ‖z‖ = dist z 0 := by simp [dist_eq_norm]
            _ ≤ dist z z0 + dist z0 0 := dist_triangle z z0 0
            _ ≤ A + ‖z0‖ := by
              gcongr
              · exact hz
              · simp [dist_eq_norm]
            _ = ‖z0‖ + A := add_comm _ _
        have hwBig : w ∈ Metric.closedBall z (‖z0‖ + A + B) := by
          rw [Metric.mem_closedBall]
          calc
            dist w z ≤ dist w 0 + dist 0 z := dist_triangle w 0 z
            _ = ‖w‖ + ‖z‖ := by simp [dist_eq_norm]
            _ ≤ B + (‖z0‖ + A) := by
              gcongr
              · simpa [Metric.mem_closedBall, dist_zero_right] using hw
            _ = ‖z0‖ + A + B := by ring
        rw [Set.indicator_of_mem hw, Set.indicator_of_mem hwBig]
      · rw [Set.indicator_of_notMem hw]
        simpa only [norm_zero] using
          norm_nonneg
            ((Metric.closedBall z (‖z0‖ + A + B)).indicator
              (planarCauchyKernel z) w)
    _ = eLpNorm
        ((Metric.closedBall (0 : ℂ) (‖z0‖ + A + B)).indicator
          (fun u : ℂ ↦ u⁻¹)) q (volume : Measure ℂ) :=
      eLpNorm_indicator_planarCauchyKernel_closedBall_eq
        z (‖z0‖ + A + B) q

/--
%%handwave
name:
  Rough planar Cauchy transform
statement:
  For a measurable function $h:\mathbb C\to\mathbb C$, its rough normalized
  Cauchy transform is the pointwise integral
  $$
    \mathcal C_ph(z)=\frac1\pi\int_{\mathbb C}\frac{h(w)}{z-w}\,dw.
  $$
  Subsequent results supply hypotheses under which this integral is
  absolutely convergent.
-/
def cauchyTransformLp (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ *
    ∫ w : ℂ, planarCauchyKernel z w * h w ∂volume

/--
%%handwave
name:
  Agreement of the rough and smooth Cauchy transforms
statement:
  For every $\varphi\in C_c^\infty(\mathbb C)$, the rough Cauchy integral
  agrees pointwise with the smooth Cauchy transform:
  $$
    \mathcal C_p\varphi(z)=\mathcal C\varphi(z).
  $$
proof:
  Both sides are defined by the same normalized integral.
-/
@[simp]
theorem cauchyTransformLp_planeTestFunction
    (φ : PlaneTestFunction) (z : ℂ) :
    cauchyTransformLp (φ : ℂ → ℂ) z = cauchyTransform φ z := rfl

/--
%%handwave
name:
  Additivity of the pointwise rough Cauchy integral
statement:
  Suppose the Cauchy integrands associated with $f$ and $g$ are integrable
  at $z$. Then
  $$
    \mathcal C_p(f-g)(z)=\mathcal C_pf(z)-\mathcal C_pg(z).
  $$
proof:
  Distribute the kernel over $f-g$ and use linearity of the Bochner
  integral.
-/
theorem cauchyTransformLp_sub
    {f g : ℂ → ℂ} (z : ℂ)
    (hf : Integrable (fun w : ℂ ↦ planarCauchyKernel z w * f w)
      (volume : Measure ℂ))
    (hg : Integrable (fun w : ℂ ↦ planarCauchyKernel z w * g w)
      (volume : Measure ℂ)) :
    cauchyTransformLp (f - g) z =
      cauchyTransformLp f z - cauchyTransformLp g z := by
  simp only [cauchyTransformLp]
  rw [← mul_sub, ← integral_sub hf hg]
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  change planarCauchyKernel z w * (f w - g w) =
    planarCauchyKernel z w * f w - planarCauchyKernel z w * g w
  ring

/--
%%handwave
name:
  Hölder bound for the rough Cauchy transform
statement:
  Let $p$ and $q$ be Hölder conjugate, with $p>2$. If
  $h\in L^p(\mathbb C)$ vanishes almost everywhere outside a compact set
  $K$, then for every $z\in\mathbb C$,
  $$
    |\mathcal C_ph(z)|
      \leq \frac1\pi
        \left\|\mathbf 1_K(w)(z-w)^{-1}\right\|_{L^q_w}
        \|h\|_{L^p}.
  $$
proof:
  Insert the indicator of $K$, which does not change the integrand almost
  everywhere, and apply Hölder's inequality to the Cauchy kernel and $h$.
-/
theorem norm_cauchyTransformLp_le
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 < p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ᵐ w ∂(volume : Measure ℂ), w ∉ K → h w = 0)
    (z : ℂ) :
    ‖cauchyTransformLp h z‖ ≤
      ‖(Real.pi : ℂ)⁻¹‖ *
        lpNorm (K.indicator (planarCauchyKernel z))
          (ENNReal.ofReal q) (volume : Measure ℂ) *
        lpNorm h (ENNReal.ofReal p) (volume : Measure ℂ) := by
  have hq0 : 0 < q := hpq.symm.pos
  have hq2 : q < 2 := by
    rw [hpq.conjugate_eq, div_lt_iff₀ hpq.sub_one_pos]
    linarith
  let k : ℂ → ℂ := K.indicator (planarCauchyKernel z)
  have hkq : MemLp k (ENNReal.ofReal q) (volume : Measure ℂ) :=
    memLp_indicator_planarCauchyKernel_of_isCompact z hK hq0 hq2
  have hae : (fun w : ℂ ↦ planarCauchyKernel z w * h w)
      =ᵐ[volume] fun w : ℂ ↦ k w * h w := by
    filter_upwards [hzero] with w hw
    by_cases hwK : w ∈ K
    · simp [k, hwK]
    · simp [k, hwK, hw hwK]
  calc
    ‖cauchyTransformLp h z‖ =
        ‖(Real.pi : ℂ)⁻¹‖ *
          ‖∫ w : ℂ, k w * h w ∂volume‖ := by
      rw [cauchyTransformLp, norm_mul, integral_congr_ae hae]
    _ ≤ ‖(Real.pi : ℂ)⁻¹‖ *
          (lpNorm k (ENNReal.ofReal q) (volume : Measure ℂ) *
            lpNorm h (ENNReal.ofReal p) (volume : Measure ℂ)) := by
      gcongr
      exact norm_integral_mul_le_lpNorm_mul_lpNorm hpq.symm hkq hhp
    _ = ‖(Real.pi : ℂ)⁻¹‖ *
        lpNorm (K.indicator (planarCauchyKernel z))
          (ENNReal.ofReal q) (volume : Measure ℂ) *
        lpNorm h (ENNReal.ofReal p) (volume : Measure ℂ) := by
      simp only [k]
      ring

/--
%%handwave
name:
  Cauchy-potential error under $L^p$ approximation
statement:
  Let $p$ and $q$ be Hölder conjugate with $p>2$. Suppose
  $h\in L^p(\mathbb C)$ and $\varphi\in C_c^\infty(\mathbb C)$ both vanish
  outside a compact set $K$. Then
  $$
    |\mathcal C_ph(z)-\mathcal C\varphi(z)|
      \leq \frac1\pi
        \left\|\mathbf 1_K(w)(z-w)^{-1}\right\|_{L^q_w}
        \|h-\varphi\|_{L^p}.
  $$
proof:
  Linearity identifies the difference of the two potentials with the
  Cauchy transform of $h-\varphi$. This difference is supported in $K$, so
  the Hölder bound for the rough transform applies.
-/
theorem norm_cauchyTransformLp_sub_cauchyTransform_le
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 < p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ᵐ w ∂(volume : Measure ℂ), w ∉ K → h w = 0)
    (φ : PlaneTestFunction)
    (hφzero : ∀ w : ℂ, w ∉ K → φ w = 0)
    (z : ℂ) :
    ‖cauchyTransformLp h z - cauchyTransform φ z‖ ≤
      ‖(Real.pi : ℂ)⁻¹‖ *
        lpNorm (K.indicator (planarCauchyKernel z))
          (ENNReal.ofReal q) (volume : Measure ℂ) *
        lpNorm (h - (φ : ℂ → ℂ))
          (ENNReal.ofReal p) (volume : Measure ℂ) := by
  have hφp : MemLp (φ : ℂ → ℂ) (ENNReal.ofReal p)
      (volume : Measure ℂ) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hup : MemLp (h - (φ : ℂ → ℂ)) (ENNReal.ofReal p)
      (volume : Measure ℂ) := hhp.sub hφp
  have huzero : ∀ᵐ w ∂(volume : Measure ℂ), w ∉ K →
      (h - (φ : ℂ → ℂ)) w = 0 := by
    filter_upwards [hzero] with w hw
    intro hwK
    change h w - φ w = 0
    rw [hw hwK, hφzero w hwK, sub_zero]
  have hq0 : 0 < q := hpq.symm.pos
  have hq2 : q < 2 := by
    rw [hpq.conjugate_eq, div_lt_iff₀ hpq.sub_one_pos]
    linarith
  letI : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p) 1 :=
    hpq.symm.ennrealOfReal
  let k : ℂ → ℂ := K.indicator (planarCauchyKernel z)
  have hkq : MemLp k (ENNReal.ofReal q) (volume : Measure ℂ) :=
    memLp_indicator_planarCauchyKernel_of_isCompact z hK hq0 hq2
  have hkprod : Integrable (k * h) (volume : Measure ℂ) :=
    hkq.integrable_mul hhp
  have hfint : Integrable
      (fun w : ℂ ↦ planarCauchyKernel z w * h w)
      (volume : Measure ℂ) := by
    apply hkprod.congr
    filter_upwards [hzero] with w hw
    by_cases hwK : w ∈ K
    · simp [k, hwK]
    · simp [k, hwK, hw hwK]
  have hφint := integrable_planarCauchyKernel_mul_testFunction φ z
  rw [← cauchyTransformLp_planeTestFunction,
    ← cauchyTransformLp_sub z hfint hφint]
  exact norm_cauchyTransformLp_le hpq hp2 hup hK huzero z

/--
%%handwave
name:
  Uniform Cauchy-potential error on a disk
statement:
  Let $p$ and $q$ be Hölder conjugate with $p>2$. Suppose
  $h\in L^p(\mathbb C)$ and $\varphi\in C_c^\infty(\mathbb C)$ vanish
  outside $\overline B(0,B)$. If $z\in\overline B(z_0,A)$, then
  $$
    |\mathcal C_ph(z)-\mathcal C\varphi(z)|
      \leq \frac1\pi
      \left\|\mathbf 1_{\overline B(0,|z_0|+A+B)}(u)u^{-1}
      \right\|_{L^q_u}\|h-\varphi\|_{L^p}.
  $$
proof:
  Apply the pointwise approximation estimate on
  $\overline B(0,B)$ and then use the uniform translated-kernel bound for
  centers in $\overline B(z_0,A)$.
-/
theorem norm_cauchyTransformLp_sub_cauchyTransform_le_on_closedBall
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 < p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {B : ℝ}
    (hzero : ∀ᵐ w ∂(volume : Measure ℂ),
      w ∉ Metric.closedBall (0 : ℂ) B → h w = 0)
    (φ : PlaneTestFunction)
    (hφzero : ∀ w : ℂ,
      w ∉ Metric.closedBall (0 : ℂ) B → φ w = 0)
    {z z0 : ℂ} {A : ℝ} (hz : z ∈ Metric.closedBall z0 A) :
    ‖cauchyTransformLp h z - cauchyTransform φ z‖ ≤
      ‖(Real.pi : ℂ)⁻¹‖ *
        lpNorm
          ((Metric.closedBall (0 : ℂ) (‖z0‖ + A + B)).indicator
            (fun u : ℂ ↦ u⁻¹))
          (ENNReal.ofReal q) (volume : Measure ℂ) *
        lpNorm (h - (φ : ℂ → ℂ))
          (ENNReal.ofReal p) (volume : Measure ℂ) := by
  have hq0 : 0 < q := hpq.symm.pos
  have hq2 : q < 2 := by
    rw [hpq.conjugate_eq, div_lt_iff₀ hpq.sub_one_pos]
    linarith
  let K : Set ℂ := Metric.closedBall (0 : ℂ) B
  let M : ℝ := ‖z0‖ + A + B
  let base : ℂ → ℂ :=
    (Metric.closedBall (0 : ℂ) M).indicator (fun u : ℂ ↦ u⁻¹)
  have hpoint := norm_cauchyTransformLp_sub_cauchyTransform_le
    hpq hp2 hhp (K := K) (isCompact_closedBall (0 : ℂ) B)
      hzero φ hφzero z
  have heLp := eLpNorm_indicator_planarCauchyKernel_closedBall_le
    (B := B) hz (ENNReal.ofReal q)
  have hleftmeas : AEStronglyMeasurable
      (K.indicator (planarCauchyKernel z)) (volume : Measure ℂ) :=
    (memLp_indicator_planarCauchyKernel_of_isCompact
      z (isCompact_closedBall (0 : ℂ) B) hq0 hq2).aestronglyMeasurable
  have hbasemeas : AEStronglyMeasurable base (volume : Measure ℂ) :=
    locallyIntegrable_inv_complex.aestronglyMeasurable.indicator
      measurableSet_closedBall
  have hk0 : MemLp
      ((Metric.closedBall (0 : ℂ) M).indicator
        (planarCauchyKernel (0 : ℂ)))
      (ENNReal.ofReal q) (volume : Measure ℂ) :=
    memLp_indicator_planarCauchyKernel_of_isCompact
      0 (isCompact_closedBall (0 : ℂ) M) hq0 hq2
  have hbase_ne_top :
      eLpNorm base (ENNReal.ofReal q) (volume : Measure ℂ) ≠ ∞ := by
    rw [show eLpNorm base (ENNReal.ofReal q) (volume : Measure ℂ) =
        eLpNorm
          ((Metric.closedBall (0 : ℂ) M).indicator
            (planarCauchyKernel (0 : ℂ)))
          (ENNReal.ofReal q) (volume : Measure ℂ) by
      exact (eLpNorm_indicator_planarCauchyKernel_closedBall_eq
        0 M (ENNReal.ofReal q)).symm]
    exact hk0.eLpNorm_ne_top
  have hlp :
      lpNorm (K.indicator (planarCauchyKernel z))
          (ENNReal.ofReal q) (volume : Measure ℂ) ≤
        lpNorm base (ENNReal.ofReal q) (volume : Measure ℂ) := by
    rw [← toReal_eLpNorm hleftmeas, ← toReal_eLpNorm hbasemeas]
    exact ENNReal.toReal_mono hbase_ne_top (by simpa [K, M, base] using heLp)
  calc
    ‖cauchyTransformLp h z - cauchyTransform φ z‖ ≤
        ‖(Real.pi : ℂ)⁻¹‖ *
          lpNorm (K.indicator (planarCauchyKernel z))
            (ENNReal.ofReal q) (volume : Measure ℂ) *
          lpNorm (h - (φ : ℂ → ℂ))
            (ENNReal.ofReal p) (volume : Measure ℂ) := hpoint
    _ ≤ ‖(Real.pi : ℂ)⁻¹‖ *
          lpNorm base (ENNReal.ofReal q) (volume : Measure ℂ) *
          lpNorm (h - (φ : ℂ → ℂ))
            (ENNReal.ofReal p) (volume : Measure ℂ) := by
      gcongr
      exact lpNorm_nonneg
    _ = ‖(Real.pi : ℂ)⁻¹‖ *
        lpNorm
          ((Metric.closedBall (0 : ℂ) (‖z0‖ + A + B)).indicator
            (fun u : ℂ ↦ u⁻¹))
          (ENNReal.ofReal q) (volume : Measure ℂ) *
        lpNorm (h - (φ : ℂ → ℂ))
          (ENNReal.ofReal p) (volume : Measure ℂ) := rfl

/--
%%handwave
name:
  Integrability of disk-supported $L^p$ data
statement:
  Let $p\geq1$. If $h\in L^p(\mathbb C)$ vanishes almost everywhere
  outside a disk, then $h\in L^1(\mathbb C)$.
proof:
  Replace $h$ by its indicator truncation to the disk. On a set of finite
  area, Hölder monotonicity lowers the exponent from $p$ to $1$.
-/
theorem integrable_of_memLp_of_ae_zero_outside_closedBall
    {p : ℝ} (hp1 : 1 ≤ p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ w ∂(volume : Measure ℂ), R ≤ ‖w‖ → h w = 0) :
    Integrable h (volume : Measure ℂ) := by
  let K : Set ℂ := Metric.closedBall (0 : ℂ) R
  let b : ℂ → ℂ := K.indicator h
  have hbp : MemLp b (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hhp.indicator measurableSet_closedBall
  have h1p : (1 : ENNReal) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr hp1
  have hb1 : MemLp b 1 (volume : Measure ℂ) :=
    hbp.mono_exponent_of_measure_support_ne_top
      (s := K) (fun w hw ↦ Set.indicator_of_notMem hw h)
      measure_closedBall_lt_top.ne h1p
  have hbeq : b =ᵐ[volume] h := by
    filter_upwards [hzero] with w hw
    by_cases hwK : w ∈ K
    · exact Set.indicator_of_mem hwK h
    · have hRw : R ≤ ‖w‖ := by
        have : ¬ ‖w‖ ≤ R := by
          simpa [K, Metric.mem_closedBall, dist_zero_right] using hwK
        exact (lt_of_not_ge this).le
      change K.indicator h w = h w
      rw [Set.indicator_of_notMem hwK, hw hRw]
  exact (memLp_one_iff_integrable.mp hb1).congr hbeq

/--
%%handwave
name:
  Far-field bound for a rough Cauchy transform
statement:
  Let $p\geq1$, let $h\in L^p(\mathbb C)$ vanish almost everywhere when
  $R\leq|w|$, and suppose $2R\leq|z|$ with $z\ne0$. Then
  $$
    |\mathcal C_ph(z)|\leq
      \frac{2}{\pi|z|}\int_{\mathbb C}|h(w)|\,dw.
  $$
proof:
  On the essential support of $h$, the reverse triangle inequality gives
  $|z-w|\geq|z|/2$. Bound the Cauchy kernel pointwise and apply the norm
  estimate for the Bochner integral.
-/
theorem norm_cauchyTransformLp_le_of_ae_zero_outside_closedBall
    {p : ℝ} (hp1 : 1 ≤ p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ w ∂(volume : Measure ℂ), R ≤ ‖w‖ → h w = 0)
    {z : ℂ} (hzR : 2 * R ≤ ‖z‖) (hz : 0 < ‖z‖) :
    ‖cauchyTransformLp h z‖ ≤
      (Real.pi)⁻¹ * (2 / ‖z‖) * ∫ w : ℂ, ‖h w‖ ∂volume := by
  have hh1 := integrable_of_memLp_of_ae_zero_outside_closedBall
    hp1 hhp hzero
  have hmajor_int : Integrable
      (fun w : ℂ ↦ (2 / ‖z‖) * ‖h w‖)
      (volume : Measure ℂ) := hh1.norm.const_mul _
  have hpoint : ∀ᵐ w ∂(volume : Measure ℂ),
      ‖planarCauchyKernel z w * h w‖ ≤
        (2 / ‖z‖) * ‖h w‖ := by
    filter_upwards [hzero] with w hw
    by_cases hhw : h w = 0
    · simp [hhw]
    have hwR : ‖w‖ ≤ R := by
      by_contra hn
      exact hhw (hw (lt_of_not_ge hn).le)
    have hhalf : ‖z‖ / 2 ≤ ‖z - w‖ := by
      calc
        ‖z‖ / 2 ≤ ‖z‖ - R := by linarith
        _ ≤ ‖z - w‖ := by
          linarith [norm_sub_norm_le z w]
    have hzw : 0 < ‖z - w‖ := lt_of_lt_of_le (half_pos hz) hhalf
    have hinv : ‖(z - w)⁻¹‖ ≤ 2 / ‖z‖ := by
      rw [norm_inv]
      have hle := one_div_le_one_div_of_le (half_pos hz) hhalf
      simpa [one_div] using hle
    rw [planarCauchyKernel, norm_mul]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  rw [cauchyTransformLp, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  calc
    (Real.pi)⁻¹ *
        ‖∫ w : ℂ, planarCauchyKernel z w * h w ∂volume‖ ≤
      (Real.pi)⁻¹ *
        ∫ w : ℂ, (2 / ‖z‖) * ‖h w‖ ∂volume := by
          exact mul_le_mul_of_nonneg_left
            (norm_integral_le_of_norm_le hmajor_int hpoint)
            (inv_nonneg.mpr Real.pi_pos.le)
    _ = (Real.pi)⁻¹ * (2 / ‖z‖) *
        ∫ w : ℂ, ‖h w‖ ∂volume := by
          rw [integral_const_mul]
          ring

/--
%%handwave
name:
  A rough Cauchy transform vanishes at infinity
statement:
  Let $p\geq1$. If $h\in L^p(\mathbb C)$ vanishes almost everywhere
  outside a disk, then
  $$
    \mathcal C_ph(z)\longrightarrow0
    \qquad\text{as }|z|\longrightarrow\infty.
  $$
proof:
  The far-field estimate bounds the transform by a fixed constant times
  $|z|^{-1}$, which tends to zero at infinity.
-/
theorem tendsto_cauchyTransformLp_cocompact_zero
    {p : ℝ} (hp1 : 1 ≤ p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ w ∂(volume : Measure ℂ), R ≤ ‖w‖ → h w = 0) :
    Tendsto (cauchyTransformLp h) (cocompact ℂ) (𝓝 0) := by
  let A : ℝ := (Real.pi)⁻¹ * 2 * ∫ w : ℂ, ‖h w‖ ∂volume
  have hden : Tendsto (fun z : ℂ ↦ ‖z‖) (cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  have hupper : Tendsto (fun z : ℂ ↦ A / ‖z‖)
      (cocompact ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hlarge : ∀ᶠ z : ℂ in cocompact ℂ,
      2 * R ≤ ‖z‖ ∧ 0 < ‖z‖ := by
    filter_upwards [hden.eventually_gt_atTop (max (2 * R) 0)] with z hz
    constructor
    · exact (le_max_left _ _).trans hz.le
    · exact (le_max_right _ _).trans_lt hz
  have hnorm : Tendsto (fun z : ℂ ↦ ‖cauchyTransformLp h z‖)
      (cocompact ℂ) (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards with z
      exact norm_nonneg _
    · filter_upwards [hlarge] with z hz
      have hbound := norm_cauchyTransformLp_le_of_ae_zero_outside_closedBall
        hp1 hhp hzero hz.1 hz.2
      calc
        ‖cauchyTransformLp h z‖ ≤
            (Real.pi)⁻¹ * (2 / ‖z‖) *
              ∫ w : ℂ, ‖h w‖ ∂volume := hbound
        _ = A / ‖z‖ := by
          dsimp [A]
          ring
    · exact hupper
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/--
%%handwave
name:
  Support-controlled test approximation of disk-supported $L^p$ data
statement:
  Let $1\leq p<\infty$, let $0<r$, and suppose $R\leq r$. If
  $h\in L^p(\mathbb C)$ vanishes almost everywhere when $R\leq|z|$, then
  for every $\varepsilon>0$ there is
  $\varphi\in C_c^\infty(\mathbb C)$ such that
  $$
    \operatorname{supp}\varphi\subseteq\overline B(0,3r/2),
    \qquad
    \|h-\varphi\|_{L^p}\leq\varepsilon.
  $$
proof:
  Replace $h$ by its indicator truncation to $\overline B(0,r)$; the two
  functions agree almost everywhere. Apply support-controlled smooth
  density to the truncated representative.
-/
theorem exists_planeTestFunction_eLpNorm_sub_le_of_ae_zero_outside_closedBall
    {p : ENNReal} (hp1 : 1 ≤ p) (hptop : p ≠ ∞)
    {h : ℂ → ℂ} (hhp : MemLp h p (volume : Measure ℂ))
    {R r : ℝ} (hr : 0 < r) (hRr : R ≤ r)
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → h z = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : PlaneTestFunction,
      tsupport (φ : ℂ → ℂ) ⊆ Metric.closedBall 0 (3 * r / 2) ∧
      eLpNorm (h - (φ : ℂ → ℂ)) p volume ≤ ENNReal.ofReal ε := by
  let B : Set ℂ := Metric.closedBall 0 r
  let b : ℂ → ℂ := B.indicator h
  have hbmem : MemLp b p (volume : Measure ℂ) :=
    hhp.indicator measurableSet_closedBall
  have hbeq : b =ᵐ[volume] h := by
    filter_upwards [hzero] with z hz
    by_cases hzB : z ∈ B
    · exact Set.indicator_of_mem hzB h
    · have hrz : r < ‖z‖ := by
        have : ¬ ‖z‖ ≤ r := by
          simpa [B, Metric.mem_closedBall, dist_zero_right] using hzB
        exact lt_of_not_ge this
      change B.indicator h z = h z
      rw [Set.indicator_of_notMem hzB, hz (hRr.trans hrz.le)]
  have hbsupp : ∀ z : ℂ, b z ≠ 0 → ‖z - 0‖ ≤ r := by
    intro z hbz
    by_contra hz
    have hzB : z ∉ B := by
      simpa [B, Metric.mem_closedBall, dist_eq_norm] using hz
    exact hbz (Set.indicator_of_notMem hzB h)
  obtain ⟨φ, hφsupp, hφapprox⟩ :=
    exists_planeTestFunction_eLpNorm_sub_le_tsupport_subset_intermediateDisk_of_memLp
      hp1 hptop hbmem hr hbsupp hε
  refine ⟨φ, hφsupp, ?_⟩
  calc
    eLpNorm (h - (φ : ℂ → ℂ)) p volume =
        eLpNorm (b - (φ : ℂ → ℂ)) p volume := by
      apply eLpNorm_congr_ae
      filter_upwards [hbeq] with z hz
      change h z - φ z = b z - φ z
      rw [hz]
    _ ≤ ENNReal.ofReal ε := hφapprox

/--
%%handwave
name:
  A fixed-support smooth $L^p$ approximation sequence
statement:
  Let $1\leq p<\infty$. If $h\in L^p(\mathbb C)$ vanishes almost
  everywhere outside a disk of radius $R$, then there are $r>0$ with
  $R\leq r$ and functions $\varphi_n\in C_c^\infty(\mathbb C)$ such that
  $$
    \operatorname{supp}\varphi_n\subseteq\overline B(0,3r/2)
    \quad\text{for every }n,
    \qquad
    \|h-\varphi_n\|_{L^p}\longrightarrow0.
  $$
proof:
  Take $r=\max\{R,1\}$ and, for the $n$th approximant, apply
  support-controlled smooth density with error $(n+1)^{-1}$. These errors
  tend to zero.
-/
theorem exists_planeTestFunction_sequence_tendsto_eLpNorm_of_ae_zero_outside_closedBall
    {p : ENNReal} (hp1 : 1 ≤ p) (hptop : p ≠ ∞)
    {h : ℂ → ℂ} (hhp : MemLp h p (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → h z = 0) :
    ∃ r : ℝ, 0 < r ∧ R ≤ r ∧
      ∃ φ : ℕ → PlaneTestFunction,
        (∀ n, tsupport (φ n : ℂ → ℂ) ⊆
          Metric.closedBall 0 (3 * r / 2)) ∧
        Tendsto
          (fun n ↦ eLpNorm (h - (φ n : ℂ → ℂ)) p volume)
          atTop (𝓝 0) := by
  let r : ℝ := max R 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hRr : R ≤ r := le_max_left R 1
  have hexists (n : ℕ) :
      ∃ φ : PlaneTestFunction,
        tsupport (φ : ℂ → ℂ) ⊆ Metric.closedBall 0 (3 * r / 2) ∧
        eLpNorm (h - (φ : ℂ → ℂ)) p volume ≤
          ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
    exact exists_planeTestFunction_eLpNorm_sub_le_of_ae_zero_outside_closedBall
      hp1 hptop hhp hr hRr hzero (by positivity)
  let φ : ℕ → PlaneTestFunction := fun n ↦ Classical.choose (hexists n)
  have hφsupp (n : ℕ) :
      tsupport (φ n : ℂ → ℂ) ⊆ Metric.closedBall 0 (3 * r / 2) :=
    (Classical.choose_spec (hexists n)).1
  have hφbound (n : ℕ) :
      eLpNorm (h - (φ n : ℂ → ℂ)) p volume ≤
        ENNReal.ofReal (((n : ℝ) + 1)⁻¹) :=
    (Classical.choose_spec (hexists n)).2
  have hreal : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹)
      atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hupper : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) + 1)⁻¹))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  refine ⟨r, hr, hRr, φ, hφsupp, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ : ℕ ↦ bot_le) hφbound

/--
%%handwave
name:
  Compactly supported $L^p$ data are square-integrable above exponent two
statement:
  Let $2\leq p<\infty$. If $h\in L^p(\mathbb C)$ vanishes almost
  everywhere outside a disk, then $h\in L^2(\mathbb C)$.
proof:
  Replace $h$ almost everywhere by its restriction to the disk and lower
  the exponent from $p$ to $2$ on this finite-measure support.
-/
theorem memLp_two_of_memLp_of_ae_zero_outside_closedBall_compl
    {p : ℝ} (hp2 : 2 ≤ p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ),
      z ∉ Metric.closedBall (0 : ℂ) R → h z = 0) :
    MemLp h 2 (volume : Measure ℂ) := by
  let K : Set ℂ := Metric.closedBall (0 : ℂ) R
  let b : ℂ → ℂ := K.indicator h
  have hbp : MemLp b (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hhp.indicator measurableSet_closedBall
  have h2p : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp2
  have hb2 : MemLp b 2 (volume : Measure ℂ) :=
    hbp.mono_exponent_of_measure_support_ne_top
      (s := K) (fun z hz ↦ Set.indicator_of_notMem hz h)
      measure_closedBall_lt_top.ne h2p
  have hbeq : b =ᵐ[volume] h := by
    filter_upwards [hzero] with z hz
    by_cases hzK : z ∈ K
    · change K.indicator h z = h z
      exact Set.indicator_of_mem hzK h
    · change K.indicator h z = h z
      rw [Set.indicator_of_notMem hzK, hz hzK]
  exact MemLp.ae_eq hbeq hb2

/--
%%handwave
name:
  Common-support $L^p$ convergence implies $L^2$ convergence
statement:
  Let $2\leq p<\infty$, and suppose every $u_n\in L^p(\mathbb C)$
  vanishes almost everywhere outside one fixed disk. If
  $\|u_n\|_{L^p}\to0$, then $\|u_n\|_{L^2}\to0$.
proof:
  Hölder monotonicity on the common disk gives
  $$
    \|u_n\|_{L^2}
      \leq |\overline B|^{1/2-1/p}\|u_n\|_{L^p}.
  $$
  The disk has finite area, so the fixed factor is finite and the right-hand
  side tends to zero.
-/
theorem tendsto_eLpNorm_two_of_tendsto_eLpNorm_of_common_closedBall_support
    {p : ℝ} (hp2 : 2 ≤ p)
    (u : ℕ → ℂ → ℂ)
    (hup : ∀ n, MemLp (u n) (ENNReal.ofReal p)
      (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ),
      z ∉ Metric.closedBall (0 : ℂ) R → u n z = 0)
    (hconv : Tendsto
      (fun n ↦ eLpNorm (u n) (ENNReal.ofReal p) volume)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (u n) 2 volume) atTop (𝓝 0) := by
  let K : Set ℂ := Metric.closedBall (0 : ℂ) R
  let C : ENNReal := volume K ^
    (1 / (2 : ENNReal).toReal -
      1 / (ENNReal.ofReal p).toReal)
  have h2p : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp2
  have hp0 : 0 ≤ p := by linarith
  have hexp : 0 ≤ 1 / (2 : ENNReal).toReal -
      1 / (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hp0]
    norm_num only [ENNReal.toReal_ofNat, Nat.cast_ofNat, one_div]
    exact sub_nonneg.mpr (by
      simpa only [one_div] using
        ((inv_le_inv₀ (by linarith) (by norm_num)).2 hp2))
  have hCtop : C ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg hexp measure_closedBall_lt_top.ne
  have hbound (n : ℕ) :
      eLpNorm (u n) 2 volume ≤
        eLpNorm (u n) (ENNReal.ofReal p) volume * C := by
    have heq : K.indicator (u n) =ᵐ[volume] u n := by
      filter_upwards [hzero n] with z hz
      by_cases hzK : z ∈ K
      · exact Set.indicator_of_mem hzK (u n)
      · rw [Set.indicator_of_notMem hzK, hz hzK]
    have hmono := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := (volume : Measure ℂ).restrict K) (f := u n)
      (p := (2 : ENNReal)) (q := ENNReal.ofReal p)
      h2p (hup n).aestronglyMeasurable.restrict
    calc
      eLpNorm (u n) 2 volume =
          eLpNorm (K.indicator (u n)) 2 volume :=
        eLpNorm_congr_ae heq.symm
      _ = eLpNorm (u n) 2 (volume.restrict K) :=
        eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall
      _ ≤ eLpNorm (u n) (ENNReal.ofReal p) (volume.restrict K) * C := by
        simpa [C, Measure.restrict_apply_univ] using hmono
      _ = eLpNorm (K.indicator (u n)) (ENNReal.ofReal p) volume * C := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
      _ = eLpNorm (u n) (ENNReal.ofReal p) volume * C := by
        rw [eLpNorm_congr_ae heq]
  have hupper : Tendsto
      (fun n ↦ eLpNorm (u n) (ENNReal.ofReal p) volume * C)
      atTop (𝓝 0) := by
    simpa using
      (ENNReal.continuous_mul_const hCtop).continuousAt.tendsto.comp hconv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ ↦ bot_le) hbound

/--
%%handwave
name:
  Local uniform convergence of Cauchy transforms
statement:
  Let $p$ and $q$ be Hölder conjugate with $p>2$. Suppose
  $h\in L^p(\mathbb C)$ and $\varphi_n\in C_c^\infty(\mathbb C)$ all vanish
  outside one disk, and
  $\|h-\varphi_n\|_{L^p}\to0$. Then for every compact
  $K\subseteq\mathbb C$,
  $$
    \mathcal C\varphi_n\longrightarrow\mathcal C_ph
  $$
  uniformly on $K$.
proof:
  Enclose $K$ in a disk. The uniform Cauchy-potential error estimate bounds
  the supremum error on that disk by a fixed finite kernel norm times
  $\|h-\varphi_n\|_{L^p}$, which tends to zero.
-/
theorem tendstoUniformlyOn_cauchyTransform_of_tendsto_eLpNorm
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 < p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {B : ℝ}
    (hzero : ∀ᵐ w ∂(volume : Measure ℂ),
      w ∉ Metric.closedBall (0 : ℂ) B → h w = 0)
    (φ : ℕ → PlaneTestFunction)
    (hφsupp : ∀ n, tsupport (φ n : ℂ → ℂ) ⊆
      Metric.closedBall (0 : ℂ) B)
    (hconv : Tendsto
      (fun n ↦ eLpNorm (h - (φ n : ℂ → ℂ)) (ENNReal.ofReal p) volume)
      atTop (𝓝 0))
    (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n z ↦ cauchyTransform (φ n) z)
      (cauchyTransformLp h) atTop K := by
  have hφp (n : ℕ) : MemLp (φ n : ℂ → ℂ) (ENNReal.ofReal p)
      (volume : Measure ℂ) :=
    (φ n).continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport
  have hup (n : ℕ) : MemLp (h - (φ n : ℂ → ℂ)) (ENNReal.ofReal p)
      (volume : Measure ℂ) := hhp.sub (hφp n)
  have hlp : Tendsto
      (fun n ↦ lpNorm (h - (φ n : ℂ → ℂ))
        (ENNReal.ofReal p) (volume : Measure ℂ))
      atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
    have heq :
        (ENNReal.toReal ∘ fun n ↦
          eLpNorm (h - (φ n : ℂ → ℂ)) (ENNReal.ofReal p) volume) =
        fun n ↦ lpNorm (h - (φ n : ℂ → ℂ))
          (ENNReal.ofReal p) (volume : Measure ℂ) := by
      funext n
      exact toReal_eLpNorm (hup n).aestronglyMeasurable
    rw [heq] at ht
    simpa only [ENNReal.toReal_zero] using ht
  obtain ⟨A, hKA⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let C : ℝ := ‖(Real.pi : ℂ)⁻¹‖ *
    lpNorm
      ((Metric.closedBall (0 : ℂ) (A + B)).indicator
        (fun u : ℂ ↦ u⁻¹))
      (ENNReal.ofReal q) (volume : Measure ℂ)
  have hupper : Tendsto
      (fun n ↦ C * lpNorm (h - (φ n : ℂ → ℂ))
        (ENNReal.ofReal p) (volume : Measure ℂ))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlp
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hevent : ∀ᶠ n in atTop,
      C * lpNorm (h - (φ n : ℂ → ℂ))
        (ENNReal.ofReal p) (volume : Measure ℂ) < ε :=
    (tendsto_order.1 hupper).2 ε hε
  filter_upwards [hevent] with n hn
  intro z hzK
  have hzA : z ∈ Metric.closedBall (0 : ℂ) A := hKA hzK
  have hφzero : ∀ w : ℂ,
      w ∉ Metric.closedBall (0 : ℂ) B → φ n w = 0 := by
    intro w hw
    exact image_eq_zero_of_notMem_tsupport
      (fun hwt ↦ hw (hφsupp n hwt))
  have hbound :=
    norm_cauchyTransformLp_sub_cauchyTransform_le_on_closedBall
      hpq hp2 hhp hzero (φ n) hφzero hzA
  rw [dist_eq_norm]
  exact hbound.trans_lt (by simpa [C, zero_add] using hn)

/--
%%handwave
name:
  Continuity of the Cauchy transform above exponent two
statement:
  Let $p$ and $q$ be Hölder conjugate with $p>2$. If
  $h\in L^p(\mathbb C)$ vanishes almost everywhere outside a disk, then the
  pointwise Cauchy integral
  $$
    \mathcal C_ph(z)=\frac1\pi\int_{\mathbb C}\frac{h(w)}{z-w}\,dw
  $$
  is continuous on $\mathbb C$.
proof:
  Approximate $h$ in $L^p$ by smooth functions whose supports lie in one
  fixed disk. The Hölder estimate for the Cauchy kernel is uniform when the
  evaluation point ranges over a compact disk, so the smooth Cauchy
  transforms converge locally uniformly to $\mathcal C_ph$. A locally
  uniform limit of continuous functions is continuous.
-/
theorem continuous_cauchyTransformLp
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 < p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ w ∂(volume : Measure ℂ), R ≤ ‖w‖ → h w = 0) :
    Continuous (cauchyTransformLp h) := by
  rw [continuous_iff_continuousAt]
  intro z0
  apply Metric.continuousAt_iff'.2
  intro ε hε
  let r : ℝ := max R 1
  let B : ℝ := 3 * r / 2
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hRr : R ≤ r := le_max_left R 1
  have hrB : r ≤ B := by
    dsimp [B]
    linarith
  have hzeroB : ∀ᵐ w ∂(volume : Measure ℂ),
      w ∉ Metric.closedBall (0 : ℂ) B → h w = 0 := by
    filter_upwards [hzero] with w hw
    intro hwB
    have hBnorm : B < ‖w‖ := by
      have : ¬ ‖w‖ ≤ B := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hwB
      exact lt_of_not_ge this
    exact hw (hRr.trans (hrB.trans hBnorm.le))
  let C : ℝ := ‖(Real.pi : ℂ)⁻¹‖ *
    lpNorm
      ((Metric.closedBall (0 : ℂ) (‖z0‖ + 1 + B)).indicator
        (fun u : ℂ ↦ u⁻¹))
      (ENNReal.ofReal q) (volume : Measure ℂ)
  have hC0 : 0 ≤ C := by
    exact mul_nonneg (norm_nonneg _) lpNorm_nonneg
  let δ : ℝ := (ε / 6) / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos (div_pos hε (by norm_num)) hC1
  have hCδ : C * δ ≤ ε / 6 := by
    calc
      C * δ ≤ (C + 1) * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 6 := by
        dsimp [δ]
        field_simp
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    apply ENNReal.one_le_ofReal.mpr
    linarith
  obtain ⟨φ, hφsupp, hφapprox⟩ :=
    exists_planeTestFunction_eLpNorm_sub_le_of_ae_zero_outside_closedBall
      hp1 ENNReal.ofReal_ne_top hhp hr hRr hzero hδ
  have hφp : MemLp (φ : ℂ → ℂ) (ENNReal.ofReal p)
      (volume : Measure ℂ) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hup : MemLp (h - (φ : ℂ → ℂ)) (ENNReal.ofReal p)
      (volume : Measure ℂ) := hhp.sub hφp
  have hlp : lpNorm (h - (φ : ℂ → ℂ))
      (ENNReal.ofReal p) (volume : Measure ℂ) ≤ δ := by
    rw [← toReal_eLpNorm hup.aestronglyMeasurable]
    calc
      (eLpNorm (h - (φ : ℂ → ℂ)) (ENNReal.ofReal p)
          (volume : Measure ℂ)).toReal ≤ (ENNReal.ofReal δ).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hφapprox
      _ = δ := ENNReal.toReal_ofReal hδ.le
  have hφzero : ∀ w : ℂ,
      w ∉ Metric.closedBall (0 : ℂ) B → φ w = 0 := by
    intro w hwB
    exact image_eq_zero_of_notMem_tsupport (fun hw ↦ hwB (hφsupp hw))
  have herror (z : ℂ) (hz : z ∈ Metric.closedBall z0 1) :
      ‖cauchyTransformLp h z - cauchyTransform φ z‖ ≤ ε / 6 := by
    have hbound :=
      norm_cauchyTransformLp_sub_cauchyTransform_le_on_closedBall
        hpq hp2 hhp hzeroB φ hφzero hz
    calc
      ‖cauchyTransformLp h z - cauchyTransform φ z‖ ≤
          C * lpNorm (h - (φ : ℂ → ℂ))
            (ENNReal.ofReal p) (volume : Measure ℂ) := by
        simpa [C] using hbound
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hlp hC0
      _ ≤ ε / 6 := hCδ
  have hmiddle : ∀ᶠ z in 𝓝 z0,
      dist (cauchyTransform φ z) (cauchyTransform φ z0) < ε / 3 :=
    (Metric.continuousAt_iff'.1
      (contDiff_cauchyTransform φ).continuous.continuousAt)
      (ε / 3) (div_pos hε (by norm_num))
  filter_upwards [Metric.closedBall_mem_nhds z0 zero_lt_one, hmiddle] with
      z hz hmid
  rw [dist_eq_norm] at hmid ⊢
  have hz0 : z0 ∈ Metric.closedBall z0 1 := by simp
  calc
    ‖cauchyTransformLp h z - cauchyTransformLp h z0‖ =
        ‖(cauchyTransformLp h z - cauchyTransform φ z) +
          (cauchyTransform φ z - cauchyTransform φ z0) +
          (cauchyTransform φ z0 - cauchyTransformLp h z0)‖ := by
      congr 1
      ring
    _ ≤ ‖cauchyTransformLp h z - cauchyTransform φ z‖ +
          ‖cauchyTransform φ z - cauchyTransform φ z0‖ +
          ‖cauchyTransform φ z0 - cauchyTransformLp h z0‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_left (norm_add_le _ _) _)
    _ < ε := by
      have hlast :
          ‖cauchyTransform φ z0 - cauchyTransformLp h z0‖ ≤ ε / 6 := by
        rw [norm_sub_rev]
        exact herror z0 hz0
      nlinarith [herror z hz]

end

end Quasiconformal

end JJMath
