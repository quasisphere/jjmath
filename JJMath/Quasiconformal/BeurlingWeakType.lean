import JJMath.Analysis.Harmonic.CalderonZygmundPieces
import JJMath.Analysis.Harmonic.OperatorBounds
import JJMath.Quasiconformal.BeurlingBadPart
import JJMath.Quasiconformal.BeurlingTransform

/-!
# Weak-type estimates for the Beurling transform

This file connects the reusable Calderón--Zygmund decomposition to the
Fourier-multiplier Beurling transform. It places the good and total bad parts
in planar `L²`, proves the complete `L²` contribution to the weak `(1,1)`
estimate, and combines the countable off-support formula with the enlarged
bad-region estimate and the exterior physical tail. The result is the full
weak `(1,1)` distribution bound for $L^1\cap L^2$ data. Its density extension
and the subsequent strong-type interpolation belong to the next layer.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  $L^2$ Beurling estimate for the Calderón--Zygmund good part
statement:
  Let $f:\mathbb C\to\mathbb C$ be integrable and let $\alpha>0$. If $g$ is
  its Calderón--Zygmund good part at level $\alpha$, then
  $$
    \|\mathcal Sg\|_{L^2}^2
      \leq4\alpha\int_{\mathbb C}|f(z)|\,dz.
  $$
proof:
  The Beurling transform is an isometry on $L^2$. Its squared norm is
  therefore the integral of $|g|^2$, which is bounded by the
  Calderón--Zygmund good-part energy estimate.
-/
theorem norm_beurlingTransformL2_goodPart_sq_le
    {f : ℂ → ℂ} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    let hg := HarmonicAnalysis.memLp_two_calderonZygmundGoodPart hf hlevel
    ‖beurlingTransformL2
        (hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level))‖ ^ 2 ≤
      (4 * level) * ∫ z, ‖f z‖ ∂volume := by
  dsimp only
  rw [norm_beurlingTransformL2_apply]
  rw [HarmonicAnalysis.norm_toLp_two_sq_eq_integral_norm_sq]
  exact HarmonicAnalysis.integral_norm_sq_calderonZygmundGoodPart_le hf hlevel

/--
%%handwave
name:
  Good-part superlevel estimate for the Beurling transform
statement:
  Let $f:\mathbb C\to\mathbb C$ be integrable, let $\alpha>0$, and let $g$
  be its Calderón--Zygmund good part at level $\alpha$. For every
  $t\in[0,\infty]$,
  $$
    t^2\,\bigl|\{z:t\leq|\mathcal Sg(z)|\}\bigr|
      \leq 4\alpha\int_{\mathbb C}|f(z)|\,dz.
  $$
proof:
  Apply the $L^2$ Chebyshev inequality to $\mathcal Sg$ and then use the
  $L^2$ good-part Beurling estimate.
-/
theorem beurlingTransformL2_goodPart_superlevel
    {f : ℂ → ℂ} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) (t : ENNReal) :
    let hg := HarmonicAnalysis.memLp_two_calderonZygmundGoodPart hf hlevel
    let Sg : PlaneL2 := beurlingTransformL2
      (hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level))
    t ^ (2 : ENNReal).toReal * volume {z : ℂ | t ≤ ‖Sg z‖₊} ≤
      ENNReal.ofReal ((4 * level) * ∫ z, ‖f z‖ ∂volume) := by
  dsimp only
  let hg := HarmonicAnalysis.memLp_two_calderonZygmundGoodPart hf hlevel
  let Sg : PlaneL2 := beurlingTransformL2
    (hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level))
  calc
    t ^ (2 : ENNReal).toReal * volume {z : ℂ | t ≤ ‖Sg z‖₊} ≤
        ENNReal.ofReal ‖Sg‖ ^ (2 : ENNReal).toReal :=
      Lp.mul_meas_ge_le_pow_enorm' Sg (by norm_num) (by norm_num) t
    _ = ENNReal.ofReal (‖Sg‖ ^ 2) := by
      norm_num [ENNReal.ofReal_pow]
    _ ≤ ENNReal.ofReal ((4 * level) * ∫ z, ‖f z‖ ∂volume) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp only [Sg, hg]
      exact norm_beurlingTransformL2_goodPart_sq_le hf hlevel

/--
%%handwave
name:
  Good-part contribution to the weak $(1,1)$ estimate
statement:
  Let $f:\mathbb C\to\mathbb C$ be integrable, let $\alpha>0$, and let $g$
  be its Calderón--Zygmund good part at level $\alpha$. Then
  $$
    \alpha
      \left|\left\{z:\frac{\alpha}2
        \leq|\mathcal Sg(z)|\right\}\right|
      \leq16\int_{\mathbb C}|f|.
  $$
proof:
  Apply [the $L^2$ good-part superlevel estimate](lean:JJMath.Quasiconformal.beurlingTransformL2_goodPart_superlevel) at threshold $\alpha/2$. Its right-hand side is finite, so the superlevel set has finite measure. Taking real values reduces the result to
  $(\alpha/2)^2|E|\leq4\alpha\|f\|_1$, and cancellation of the positive
  factor $\alpha$ gives the stated constant sixteen.
-/
theorem ofReal_level_mul_volume_beurlingTransformL2_goodPart_superlevel_half_le
    {f : ℂ → ℂ} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    let hg := HarmonicAnalysis.memLp_two_calderonZygmundGoodPart hf hlevel
    let Sg : PlaneL2 := beurlingTransformL2
      (hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level))
    ENNReal.ofReal level *
        volume {z : ℂ | ENNReal.ofReal level / 2 ≤ ‖Sg z‖ₑ} ≤
      ENNReal.ofReal (16 * ∫ z, ‖f z‖ ∂volume) := by
  dsimp only
  let hg := HarmonicAnalysis.memLp_two_calderonZygmundGoodPart hf hlevel
  let Sg : PlaneL2 := beurlingTransformL2
    (hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level))
  let q : ENNReal := ENNReal.ofReal level / 2
  let m : ENNReal := volume {z : ℂ | q ≤ ‖Sg z‖ₑ}
  have hq0 : q ≠ 0 := by
    dsimp only [q]
    exact ENNReal.div_ne_zero.2
      ⟨ENNReal.ofReal_ne_zero_iff.mpr hlevel, by norm_num⟩
  have hraw : q ^ (2 : ENNReal).toReal * m ≤
      ENNReal.ofReal ((4 * level) * ∫ z, ‖f z‖ ∂volume) := by
    simpa only [q, m, enorm_eq_nnnorm] using
      beurlingTransformL2_goodPart_superlevel hf hlevel q
  have hm : m ≠ ∞ := by
    have hmul : q ^ (2 : ENNReal).toReal * m ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hraw
    exact (ENNReal.lt_top_of_mul_ne_top_right hmul (by positivity)).ne
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm)
    ENNReal.ofReal_ne_top).1
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hraw
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlevel.le,
    ENNReal.toReal_ofNat, q, m] at hreal ⊢
  rw [← ENNReal.toReal_rpow] at hreal
  simp only [ENNReal.toReal_ofReal hlevel.le,
    ENNReal.toReal_div, ENNReal.toReal_ofNat] at hreal
  norm_num at hreal ⊢
  have hI : 0 ≤ ∫ z, ‖f z‖ ∂volume :=
    integral_nonneg fun z ↦ norm_nonneg (f z)
  have hmreal : 0 ≤ m.toReal := ENNReal.toReal_nonneg
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (mul_nonneg (by norm_num) hlevel.le) hI)] at hreal
  rw [ENNReal.toReal_ofReal hI]
  nlinarith

/--
%%handwave
name:
  $L^2$ Beurling transform respects the good--bad decomposition
statement:
  Let $f:\mathbb C\to\mathbb C$ be integrable and square-integrable, and let
  $\alpha>0$. If $f=g+b$ is its Calderón--Zygmund decomposition, then in
  $L^2(\mathbb C)$
  $$
    \mathcal Sf=\mathcal Sg+\mathcal Sb.
  $$
proof:
  The pointwise identity $f=g+b$ gives the corresponding identity of
  $L^2$ classes. Apply linearity of the Beurling transform.
-/
theorem beurlingTransformL2_goodPart_add_badSum
    {f : ℂ → ℂ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {level : ℝ} (hlevel : 0 < level) :
    let hg := HarmonicAnalysis.memLp_two_calderonZygmundGoodPart hf₁ hlevel
    let hb := HarmonicAnalysis.memLp_two_calderonZygmundBadSum
      hf₁ hf₂ hlevel
    beurlingTransformL2 (hf₂.toLp f) =
      beurlingTransformL2
          (hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level)) +
        beurlingTransformL2
          (hb.toLp (HarmonicAnalysis.calderonZygmundBadSum f level)) := by
  dsimp only
  let hg := HarmonicAnalysis.memLp_two_calderonZygmundGoodPart hf₁ hlevel
  let hb := HarmonicAnalysis.memLp_two_calderonZygmundBadSum hf₁ hf₂ hlevel
  have hclasses : hf₂.toLp f =
      hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level) +
        hb.toLp (HarmonicAnalysis.calderonZygmundBadSum f level) := by
    apply Lp.ext
    filter_upwards
        [hf₂.coeFn_toLp,
          hg.coeFn_toLp,
          hb.coeFn_toLp,
          Lp.coeFn_add
            (hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level))
            (hb.toLp (HarmonicAnalysis.calderonZygmundBadSum f level))]
        with x hf_x hg_x hb_x hadd_x
    rw [hf_x, hadd_x, Pi.add_apply, hg_x, hb_x]
    exact (HarmonicAnalysis.calderonZygmundGoodPart_add_badSum f level x).symm
  rw [hclasses, map_add]

/--
%%handwave
name:
  Exterior bad-part contribution to the weak $(1,1)$ estimate
statement:
  Let $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$, let $\alpha>0$, and let $b$
  be its total Calderón--Zygmund bad part. On the complement of the enlarged
  bad region $\Omega^*$,
  $$
    \alpha
      \left|\left\{z:\frac{\alpha}2
        \leq|\mathcal Sb(z)|\right\}\right|
      \leq24\int_{\mathbb C}|f|.
  $$
proof:
  On $(\Omega^*)^c$, [the transform $\mathcal Sb$ equals the countable physical kernel series](lean:JJMath.Quasiconformal.beurlingTransformL2_badSum_eq_tsum_kernelIntegral_ae_compl_enlarged). That series is integrable there and its $L^1$ norm is at most $12\|f\|_1$, because the Beurling first-difference constant is $6/\pi$. Markov's inequality at threshold $\alpha/2$ gives the factor twenty-four.
-/
theorem ofReal_level_mul_restrict_compl_enlarged_volume_beurlingTransformL2_badSum_superlevel_half_le
    {f : ℂ → ℂ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {level : ℝ} (hlevel : 0 < level) :
    let hb := HarmonicAnalysis.memLp_two_calderonZygmundBadSum hf₁ hf₂ hlevel
    let Sb : PlaneL2 := beurlingTransformL2
      (hb.toLp (HarmonicAnalysis.calderonZygmundBadSum f level))
    ENNReal.ofReal level *
        (volume.restrict
          (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ)
          {z : ℂ | ENNReal.ofReal level / 2 ≤ ‖Sb z‖ₑ} ≤
      ENNReal.ofReal (24 * ∫ z, ‖f z‖ ∂volume) := by
  dsimp only
  let S := HarmonicAnalysis.maximalBadDyadicSquares f level
  letI := (HarmonicAnalysis.countable_maximalBadDyadicSquares f level).toEncodable
  let E : Set ℂ :=
    (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ
  let μE : Measure ℂ := volume.restrict E
  let hb := HarmonicAnalysis.memLp_two_calderonZygmundBadSum hf₁ hf₂ hlevel
  let Sb : PlaneL2 := beurlingTransformL2
    (hb.toLp (HarmonicAnalysis.calderonZygmundBadSum f level))
  let T : ℂ → ℂ := fun x ↦ ∑' Q : S,
    beurlingKernelIntegral
      (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) x
  let q : ENNReal := ENNReal.ofReal level / 2
  let B : Set ℂ := {z : ℂ | q ≤ ‖Sb z‖ₑ}
  have hrep : (Sb : ℂ → ℂ) =ᵐ[μE] T := by
    simpa only [Sb, hb, μE, E, T] using
      beurlingTransformL2_badSum_eq_tsum_kernelIntegral_ae_compl_enlarged
        hf₁ hf₂ hlevel
  have hKm : Measurable planarBeurlingKernel := by
    unfold planarBeurlingKernel
    fun_prop
  have hTint : Integrable T μE := by
    simpa only [T, μE, E, beurlingKernelIntegral] using
      (HarmonicAnalysis.HasKernelFirstDifference.integrableOn_tsum_badPart
        planarBeurlingKernel planarBeurlingKernel_hasKernelFirstDifference
        hKm (by positivity : 0 ≤ 6 * (Real.pi)⁻¹) hf₁ level)
  have htail : (∫ x, ‖T x‖ ∂μE) ≤
      12 * ∫ y, ‖f y‖ ∂volume := by
    have h :=
      HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_tsum_badPart_le
        planarBeurlingKernel planarBeurlingKernel_hasKernelFirstDifference
        hKm (by positivity : 0 ≤ 6 * (Real.pi)⁻¹) hf₁ level
    simpa only [T, μE, E, beurlingKernelIntegral] using h.trans_eq (by
      congr 1
      field_simp [Real.pi_ne_zero]
      norm_num)
  have hqmarkov : q * μE B ≤
      ENNReal.ofReal (12 * ∫ y, ‖f y‖ ∂volume) := by
    calc
      q * μE B ≤ ∫⁻ x, ‖(Sb : ℂ → ℂ) x‖ₑ ∂μE := by
        simpa only [B] using mul_meas_ge_le_lintegral₀
          ((Lp.aestronglyMeasurable Sb).mono_measure
            Measure.restrict_le_self).enorm q
      _ = ∫⁻ x, ‖T x‖ₑ ∂μE := by
        apply lintegral_congr_ae
        filter_upwards [hrep] with x hx
        rw [hx]
      _ = ENNReal.ofReal (∫ x, ‖T x‖ ∂μE) :=
        (ofReal_integral_norm_eq_lintegral_enorm hTint).symm
      _ ≤ ENNReal.ofReal (12 * ∫ y, ‖f y‖ ∂volume) :=
        ENNReal.ofReal_le_ofReal htail
  calc
    ENNReal.ofReal level * μE B = (q + q) * μE B := by
      rw [ENNReal.add_halves]
    _ = q * μE B + q * μE B := add_mul _ _ _
    _ ≤ ENNReal.ofReal (12 * ∫ y, ‖f y‖ ∂volume) +
        ENNReal.ofReal (12 * ∫ y, ‖f y‖ ∂volume) :=
      add_le_add hqmarkov hqmarkov
    _ = ENNReal.ofReal (24 * ∫ y, ‖f y‖ ∂volume) := by
      rw [← ENNReal.ofReal_add]
      · congr 1
        ring
      · positivity
      · positivity

/--
%%handwave
name:
  Weak $(1,1)$ distribution estimate for the $L^2$ Beurling transform
statement:
  If $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$ and
  $0<t<\infty$, then
  $$
    t\,\bigl|\{z:t\leq|\mathcal Sf(z)|\}\bigr|
      \leq(40+16\pi)\int_{\mathbb C}|f(z)|\,dz.
  $$
proof:
  Regard the finite positive threshold $t$ as a positive real number and
  decompose at level $\alpha=t$. Up to a null set,
  the superlevel set of $\mathcal Sf=\mathcal Sg+\mathcal Sb$ lies in the
  union of $\Omega^*$, the $t/2$ superlevel set of $\mathcal Sg$, and the
  exterior $t/2$ superlevel set of $\mathcal Sb$. The three contributions
  are bounded respectively by [the exceptional-area estimate](lean:JJMath.HarmonicAnalysis.ofReal_level_mul_volume_enlargedMaximalBadDyadicRegion_le), [the good-part estimate](lean:JJMath.Quasiconformal.ofReal_level_mul_volume_beurlingTransformL2_goodPart_superlevel_half_le), and [the exterior bad-part estimate](lean:JJMath.Quasiconformal.ofReal_level_mul_restrict_compl_enlarged_volume_beurlingTransformL2_badSum_superlevel_half_le), with constants $16\pi$, $16$, and $24$.
-/
theorem beurlingTransformL2_distribution_le_of_integrable_memLp_two
    {f : ℂ → ℂ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {t : ENNReal} (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    t * HarmonicAnalysis.distributionFunction
        (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) volume t ≤
      ENNReal.ofReal
        ((40 + 16 * Real.pi) * ∫ z, ‖f z‖ ∂volume) := by
  let level : ℝ := t.toReal
  have hlevel : 0 < level := ENNReal.toReal_pos ht0 httop
  have htlevel : ENNReal.ofReal level = t := ENNReal.ofReal_toReal httop
  let hg := HarmonicAnalysis.memLp_two_calderonZygmundGoodPart hf₁ hlevel
  let hb := HarmonicAnalysis.memLp_two_calderonZygmundBadSum hf₁ hf₂ hlevel
  let Sf : PlaneL2 := beurlingTransformL2 (hf₂.toLp f)
  let Sg : PlaneL2 := beurlingTransformL2
    (hg.toLp (HarmonicAnalysis.calderonZygmundGoodPart f level))
  let Sb : PlaneL2 := beurlingTransformL2
    (hb.toLp (HarmonicAnalysis.calderonZygmundBadSum f level))
  let Ω : Set ℂ := HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level
  let E : Set ℂ := Ωᶜ
  let A : Set ℂ := {z : ℂ | t ≤ ‖Sf z‖ₑ}
  let G : Set ℂ := {z : ℂ | t / 2 ≤ ‖Sg z‖ₑ}
  let B : Set ℂ := {z : ℂ | t / 2 ≤ ‖Sb z‖ₑ}
  have hdecomp : (Sf : ℂ → ℂ) =ᵐ[volume]
      fun z ↦ (Sg : ℂ → ℂ) z + (Sb : ℂ → ℂ) z := by
    have hL2 := beurlingTransformL2_goodPart_add_badSum hf₁ hf₂ hlevel
    dsimp only at hL2
    have hSf : Sf = Sg + Sb := by
      simpa only [Sf, Sg, Sb, hg, hb] using hL2
    filter_upwards [Lp.coeFn_add Sg Sb] with z hz
    rw [hSf]
    exact hz
  have hsubset : ∀ᵐ z ∂volume,
      z ∈ A → z ∈ Ω ∪ (G ∪ (B ∩ E)) := by
    filter_upwards [hdecomp] with z hz
    intro hzA
    by_cases hzΩ : z ∈ Ω
    · exact Or.inl hzΩ
    · right
      by_cases hzG : z ∈ G
      · exact Or.inl hzG
      · right
        refine ⟨?_, hzΩ⟩
        by_contra hzB
        have hGlt : ‖(Sg : ℂ → ℂ) z‖ₑ < t / 2 := by
          simpa only [G, mem_setOf_eq, not_le] using hzG
        have hBlt : ‖(Sb : ℂ → ℂ) z‖ₑ < t / 2 := by
          simpa only [B, mem_setOf_eq, not_le] using hzB
        have hsum : ‖(Sf : ℂ → ℂ) z‖ₑ < t := by
          rw [hz]
          calc
            ‖(Sg : ℂ → ℂ) z + (Sb : ℂ → ℂ) z‖ₑ ≤
                ‖(Sg : ℂ → ℂ) z‖ₑ + ‖(Sb : ℂ → ℂ) z‖ₑ :=
              enorm_add_le _ _
            _ < t / 2 + t / 2 :=
              ENNReal.add_lt_add_of_lt_of_le
                (ne_top_of_lt hBlt) hGlt hBlt.le
            _ = t := ENNReal.add_halves t
        exact (not_lt_of_ge hzA) hsum
  have hmeasure : volume A ≤
      volume Ω + (volume G + volume (B ∩ E)) := by
    calc
      volume A ≤ volume (Ω ∪ (G ∪ (B ∩ E))) := measure_mono_ae hsubset
      _ ≤ volume Ω + volume (G ∪ (B ∩ E)) := measure_union_le _ _
      _ ≤ volume Ω + (volume G + volume (B ∩ E)) :=
        add_le_add le_rfl (measure_union_le G (B ∩ E))
  have hregion : t * volume Ω ≤
      ENNReal.ofReal ((16 * Real.pi) * ∫ z, ‖f z‖ ∂volume) := by
    rw [← htlevel]
    simpa only [Ω] using
      HarmonicAnalysis.ofReal_level_mul_volume_enlargedMaximalBadDyadicRegion_le
        hf₁ hlevel
  have hgood : t * volume G ≤
      ENNReal.ofReal (16 * ∫ z, ‖f z‖ ∂volume) := by
    rw [← htlevel]
    simpa only [G, htlevel, Sg, hg] using
      ofReal_level_mul_volume_beurlingTransformL2_goodPart_superlevel_half_le
        hf₁ hlevel
  have hbad : t * volume (B ∩ E) ≤
      ENNReal.ofReal (24 * ∫ z, ‖f z‖ ∂volume) := by
    rw [← htlevel]
    have hEmeas : MeasurableSet E :=
      (HarmonicAnalysis.measurableSet_enlargedMaximalBadDyadicRegion
        f level).compl
    rw [← Measure.restrict_apply' hEmeas]
    simpa only [B, E, htlevel, Sb, hb] using
      ofReal_level_mul_restrict_compl_enlarged_volume_beurlingTransformL2_badSum_superlevel_half_le
        hf₁ hf₂ hlevel
  calc
    t * HarmonicAnalysis.distributionFunction
        (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) volume t =
        t * volume A := rfl
    _ ≤ t * (volume Ω + (volume G + volume (B ∩ E))) :=
      by gcongr
    _ = t * volume Ω + t * volume G + t * volume (B ∩ E) := by ring
    _ ≤ ENNReal.ofReal ((16 * Real.pi) * ∫ z, ‖f z‖ ∂volume) +
        ENNReal.ofReal (16 * ∫ z, ‖f z‖ ∂volume) +
        ENNReal.ofReal (24 * ∫ z, ‖f z‖ ∂volume) :=
      add_le_add (add_le_add hregion hgood) hbad
    _ = ENNReal.ofReal
        ((40 + 16 * Real.pi) * ∫ z, ‖f z‖ ∂volume) := by
      rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add]
      · congr 1
        ring
      all_goals positivity

/--
%%handwave
name:
  Weak $(1,1)$ bound in lower-integral form for the $L^2$ Beurling transform
statement:
  If $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$ and
  $0<t<\infty$, then
  $$
    t\,\bigl|\{z:t\leq|\mathcal Sf(z)|\}\bigr|
      \leq(40+16\pi)\int_{\mathbb C}^{-}|f(z)|\,dz.
  $$
proof:
  Apply [the distribution estimate with the ordinary $L^1$ integral](lean:JJMath.Quasiconformal.beurlingTransformL2_distribution_le_of_integrable_memLp_two). Integrability identifies the lower integral of the extended norm with the extended-real image of the ordinary norm integral, and nonnegativity lets that image commute with multiplication by $40+16\pi$.
-/
theorem beurlingTransformL2_distribution_le_lintegral_of_integrable_memLp_two
    {f : ℂ → ℂ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {t : ENNReal} (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    t * HarmonicAnalysis.distributionFunction
        (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) volume t ≤
      ENNReal.ofReal (40 + 16 * Real.pi) * ∫⁻ z, ‖f z‖ₑ ∂volume := by
  calc
    t * HarmonicAnalysis.distributionFunction
        (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) volume t ≤
        ENNReal.ofReal
          ((40 + 16 * Real.pi) * ∫ z, ‖f z‖ ∂volume) :=
      beurlingTransformL2_distribution_le_of_integrable_memLp_two
        hf₁ hf₂ ht0 httop
    _ = ENNReal.ofReal (40 + 16 * Real.pi) *
        ∫⁻ z, ‖f z‖ₑ ∂volume := by
      rw [ENNReal.ofReal_mul]
      · rw [ofReal_integral_norm_eq_lintegral_enorm hf₁]
      · positivity

end

end Quasiconformal

end JJMath
