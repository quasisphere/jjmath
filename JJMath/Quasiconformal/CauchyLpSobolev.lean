import JJMath.Quasiconformal.CauchyLp
import JJMath.Quasiconformal.Compactness

/-!
# Sobolev identities for rough Cauchy transforms

This file passes the test-function Cauchy--Beurling identities to compactly
supported `Lᵖ` data above exponent two.  The passage is local: Cauchy
potentials converge uniformly on compact sets, while their two Wirtinger
derivatives converge in `L²`.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Uniform convergence on a compact set implies local $L^2$ convergence
statement:
  Let $K\subseteq\mathbb C$ be compact. If measurable functions
  $f_n,g:K\to\mathbb C$ are square-integrable and $f_n\to g$ uniformly on
  $K$, then
  $$
    \|f_n-g\|_{L^2(K)}\longrightarrow0.
  $$
proof:
  Discard finitely many terms so that $|f_n-g|\leq1$ on $K$. Pointwise
  convergence and domination by the square-integrable constant function
  then give $L^2$ convergence by dominated convergence.
-/
theorem tendsto_eLpNorm_two_restrict_of_tendstoUniformlyOn
    (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (K : Set ℂ) (hK : IsCompact K)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K))
    (hconv : TendstoUniformlyOn f g atTop K) :
    Tendsto
      (fun n ↦ eLpNorm (f n - g) 2 (volume.restrict K))
      atTop (𝓝 0) := by
  let μK : Measure ℂ := volume.restrict K
  let b : ℕ → ℂ → ℂ := fun n z ↦ f n z - g z
  have hbmeas (n : ℕ) : AEStronglyMeasurable (b n) μK :=
    (hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable
  have hevent : ∀ᶠ n in atTop,
      ∀ z ∈ K, dist (g z) (f n z) < 1 := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    exact hconv 1 zero_lt_one
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  let bs : ℕ → ℂ → ℂ := fun n ↦ b (n + N)
  let a : ℂ → ℝ := fun _ ↦ 1
  haveI : IsFiniteMeasure μK :=
    isFiniteMeasure_restrict.2 hK.measure_ne_top
  have ha : MemLp a 2 μK := by
    apply MemLp.of_bound aestronglyMeasurable_const 1
    filter_upwards with z
    simp
  have hbsmeas (n : ℕ) : AEStronglyMeasurable (bs n) μK :=
    hbmeas (n + N)
  have hbsbound (n : ℕ) : ∀ᵐ z ∂μK,
      ‖bs n z‖ ≤ (1 : ℝ) * ‖a z‖ := by
    apply ae_restrict_of_forall_mem hK.measurableSet
    intro z hz
    have hnN : N ≤ n + N := by omega
    have hdist := hN (n + N) hnN z hz
    dsimp only [bs, b, a]
    rw [one_mul, norm_one]
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hdist.le
  have hbszero : ∀ᵐ z ∂μK,
      Tendsto (fun n ↦ bs n z) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have hzconv := hconv.tendsto_at hz
    have hzshift := hzconv.comp (tendsto_add_atTop_nat N)
    simpa [bs, b] using hzshift.sub_const (g z)
  obtain ⟨_hbsmem, hshift⟩ :=
    memLp_and_tendsto_zero_of_ae_tendsto_of_norm_le_mul
      ha hbsmeas hbsbound hbszero
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa [bs, b, Pi.sub_apply] using hshift

/--
%%handwave
name:
  Strong $L^2$ convergence restricts to measurable subsets
statement:
  If $F_n\to F$ strongly in $L^2(\mathbb C)$ and $K\subseteq\mathbb C$ is
  measurable, then the restrictions satisfy
  $$
    F_n|_K\longrightarrow F|_K
    \quad\hbox{strongly in }L^2(K).
  $$
proof:
  The $L^2$ distance on $K$ is at most the whole-plane $L^2$ distance,
  because restricted Lebesgue measure is bounded by Lebesgue measure.
-/
theorem Lp.tendsto_toLp_restrict_of_tendsto
    (F : ℕ → PlaneL2) (G : PlaneL2)
    (hFG : Tendsto F atTop (𝓝 G)) (K : Set ℂ) :
    Tendsto
      (fun n ↦ ((Lp.memLp (F n)).restrict K).toLp (F n : ℂ → ℂ))
      atTop
      (𝓝 (((Lp.memLp G).restrict K).toLp (G : ℂ → ℂ))) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n ↦ (F n : ℂ → ℂ))
    (fun n ↦ (Lp.memLp (F n)).restrict K)
    (G : ℂ → ℂ) ((Lp.memLp G).restrict K)).2
  have hglobal := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F G).1 hFG
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hglobal (fun _ ↦ bot_le) (fun n ↦
      eLpNorm_mono_measure ((F n : ℂ → ℂ) - (G : ℂ → ℂ))
        Measure.restrict_le_self)

/--
%%handwave
name:
  Weak differential attached to a rough Cauchy potential
statement:
  Given measurable fields $h,S:\mathbb C\to\mathbb C$, the candidate weak
  differential of a Cauchy potential with
  $\partial_{\bar z}\mathcal C h=h$ and $\partial_z\mathcal C h=S$ is
  $$
    D\mathcal C h(z)(v)=S(z)v+h(z)\overline v.
  $$
-/
def cauchyTransformLpWeakDifferential
    (h S : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  realLinearMapOfWirtinger (S z) (h z)

/--
%%handwave
name:
  Sobolev Cauchy--Beurling identities above exponent two
statement:
  Let $p>2$, let $q$ be its Hölder conjugate, and suppose
  $h\in L^p(\mathbb C)$ vanishes almost everywhere outside a disk. Then the
  rough Cauchy potential
  $$
    \mathcal C_ph(z)=\frac1\pi\int_{\mathbb C}\frac{h(w)}{z-w}\,dw
  $$
  belongs to $W^{1,2}_{\mathrm{loc}}(\mathbb C)$. Writing
  $\mathcal S_2h$ for the $L^2$ Beurling transform of $h$, its weak
  Wirtinger derivatives are
  $$
    \partial_{\bar z}\mathcal C_ph=h,
    \qquad
    \partial_z\mathcal C_ph=\mathcal S_2h
  $$
  almost everywhere.
proof:
  Approximate $h$ in $L^p$ by smooth functions supported in one fixed disk.
  Finite support lowers this convergence to $L^2$, so the smooth data and
  their Beurling transforms converge strongly in $L^2$. Their Cauchy
  potentials converge uniformly on compact sets and hence locally in
  $L^2$. On every closed disk, weak-derivative closure passes the two smooth
  Cauchy--Beurling identities to the limit. Exhausting the plane by integer
  disks gives the global distributional identities; the same fields supply
  the required local square-integrability.
-/
theorem cauchyTransformLp_isLocalW12On
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 < p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → h z = 0) :
    let hh2 : MemLp h 2 (volume : Measure ℂ) :=
      memLp_two_of_memLp_of_ae_zero_outside_closedBall_compl hp2.le hhp (by
        filter_upwards [hzero] with z hz
        intro hzout
        apply hz
        have : ¬ ‖z‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hzout
        exact (lt_of_not_ge this).le)
    IsLocalW12On Set.univ (cauchyTransformLp h)
      (cauchyTransformLpWeakDifferential h
        (beurlingTransformL2 (hh2.toLp h) : ℂ → ℂ)) := by
  let hzeroBall : ∀ᵐ z ∂(volume : Measure ℂ),
      z ∉ Metric.closedBall (0 : ℂ) R → h z = 0 := by
    filter_upwards [hzero] with z hz
    intro hzout
    apply hz
    have : ¬ ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hzout
    exact (lt_of_not_ge this).le
  let hh2 : MemLp h 2 (volume : Measure ℂ) :=
    memLp_two_of_memLp_of_ae_zero_outside_closedBall_compl hp2.le hhp hzeroBall
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr (by linarith)
  obtain ⟨r, hr, hRr, φ, hφsupp, hconvp⟩ :=
    exists_planeTestFunction_sequence_tendsto_eLpNorm_of_ae_zero_outside_closedBall
      hp1 ENNReal.ofReal_ne_top hhp hzero
  let B : ℝ := 3 * r / 2
  have hrB : r ≤ B := by dsimp [B]; linarith
  have hzeroB : ∀ᵐ z ∂(volume : Measure ℂ),
      z ∉ Metric.closedBall (0 : ℂ) B → h z = 0 := by
    filter_upwards [hzero] with z hz
    intro hzout
    apply hz
    have hBn : B < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hzout
    exact hRr.trans (hrB.trans hBn.le)
  have hφzero (n : ℕ) (z : ℂ) :
      z ∉ Metric.closedBall (0 : ℂ) B → φ n z = 0 := by
    intro hz
    exact image_eq_zero_of_notMem_tsupport
      (fun hzt ↦ hz (hφsupp n hzt))
  have hφp (n : ℕ) : MemLp (φ n : ℂ → ℂ) (ENNReal.ofReal p)
      (volume : Measure ℂ) :=
    (φ n).continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport
  have hsubp (n : ℕ) : MemLp (h - (φ n : ℂ → ℂ))
      (ENNReal.ofReal p) (volume : Measure ℂ) := hhp.sub (hφp n)
  have hsubzero (n : ℕ) : ∀ᵐ z ∂(volume : Measure ℂ),
      z ∉ Metric.closedBall (0 : ℂ) B →
        (h - (φ n : ℂ → ℂ)) z = 0 := by
    filter_upwards [hzeroB] with z hz
    intro hzout
    simp only [Pi.sub_apply, hz hzout, hφzero n z hzout, sub_self]
  have hconv2 : Tendsto
      (fun n ↦ eLpNorm (h - (φ n : ℂ → ℂ)) 2 volume)
      atTop (𝓝 0) :=
    tendsto_eLpNorm_two_of_tendsto_eLpNorm_of_common_closedBall_support
      hp2.le (fun n ↦ h - (φ n : ℂ → ℂ)) hsubp hsubzero hconvp
  have hconv2rev : Tendsto
      (fun n ↦ eLpNorm ((φ n : ℂ → ℂ) - h) 2 volume)
      atTop (𝓝 0) := by
    apply hconv2.congr'
    filter_upwards with n
    exact eLpNorm_sub_comm h (φ n : ℂ → ℂ) 2 volume
  have hφ2 (n : ℕ) : MemLp (φ n : ℂ → ℂ) 2
      (volume : Measure ℂ) :=
    (φ n).continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport
  let H : PlaneL2 := hh2.toLp h
  let Φ : ℕ → PlaneL2 := fun n ↦ testFunctionPlaneL2 (φ n)
  have hΦeq (n : ℕ) : Φ n = (hφ2 n).toLp (φ n : ℂ → ℂ) := by
    simpa only [Φ, Lp.toLp_coeFn] using
      (MemLp.toLp_congr (Lp.memLp (testFunctionPlaneL2 (φ n)))
        (hφ2 n) (testFunctionPlaneL2_coeFn (φ n)))
  have hΦ : Tendsto Φ atTop (𝓝 H) := by
    have hraw := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n ↦ (φ n : ℂ → ℂ)) hφ2 h hh2).2 hconv2rev
    exact hraw.congr' (Filter.Eventually.of_forall fun n ↦ hΦeq n)
  let SΦ : ℕ → PlaneL2 := fun n ↦ beurlingTransformL2 (Φ n)
  let SH : PlaneL2 := beurlingTransformL2 H
  have hSΦ : Tendsto SΦ atTop (𝓝 SH) := by
    exact beurlingTransformL2.continuous.continuousAt.tendsto.comp hΦ
  let X : ℕ → PlaneL2 := fun n ↦ SΦ n + Φ n
  let X0 : PlaneL2 := SH + H
  have hX : Tendsto X atTop (𝓝 X0) := by
    exact hSΦ.add hΦ
  let Y : ℕ → PlaneL2 := fun n ↦ Complex.I • (SΦ n - Φ n)
  let Y0 : PlaneL2 := Complex.I • (SH - H)
  have hY : Tendsto Y atTop (𝓝 Y0) := by
    exact tendsto_const_nhds.smul (hSΦ.sub hΦ)
  let D : ℂ → ℂ →L[ℝ] ℂ := cauchyTransformLpWeakDifferential h (SH : ℂ → ℂ)
  let U : ℂ → ℂ := cauchyTransformLp h
  have hcoordX (n : ℕ) :
      (fun z ↦ cauchyTransformWeakDifferential (φ n) z 1)
        =ᵐ[volume] (X n : ℂ → ℂ) := by
    filter_upwards [Lp.coeFn_add (SΦ n) (Φ n),
      testFunctionPlaneL2_coeFn (φ n)] with z hsum hφz
    rw [show (X n : ℂ → ℂ) z = (SΦ n + Φ n : PlaneL2) z by rfl,
      hsum]
    simp [cauchyTransformWeakDifferential, realLinearMapOfWirtinger_apply,
      SΦ, Φ, hφz]
  have hcoordY (n : ℕ) :
      (fun z ↦ cauchyTransformWeakDifferential (φ n) z Complex.I)
        =ᵐ[volume] (Y n : ℂ → ℂ) := by
    filter_upwards [Lp.coeFn_smul Complex.I (SΦ n - Φ n),
      Lp.coeFn_sub (SΦ n) (Φ n), testFunctionPlaneL2_coeFn (φ n)] with
        z hsmul hsub hφz
    rw [show (Y n : ℂ → ℂ) z =
        (Complex.I • (SΦ n - Φ n) : PlaneL2) z by rfl,
      hsmul]
    change (cauchyTransformWeakDifferential (φ n) z) Complex.I =
      Complex.I * ((SΦ n - Φ n : PlaneL2) : ℂ → ℂ) z
    rw [hsub]
    simp [cauchyTransformWeakDifferential, realLinearMapOfWirtinger_apply,
      SΦ, Φ, hφz]
    ring
  have hcoordX0 : (fun z ↦ D z 1) =ᵐ[volume] (X0 : ℂ → ℂ) := by
    filter_upwards [hh2.coeFn_toLp,
      Lp.coeFn_add SH H] with z hHz hsum
    rw [show (X0 : ℂ → ℂ) z = (SH + H : PlaneL2) z by rfl, hsum]
    have hH : (H : ℂ → ℂ) z = h z := by simpa [H] using hHz
    change D z 1 = (SH : ℂ → ℂ) z + (H : ℂ → ℂ) z
    rw [hH]
    simp [D, cauchyTransformLpWeakDifferential,
      realLinearMapOfWirtinger_apply]
  have hcoordY0 : (fun z ↦ D z Complex.I) =ᵐ[volume] (Y0 : ℂ → ℂ) := by
    filter_upwards [hh2.coeFn_toLp, Lp.coeFn_smul Complex.I (SH - H),
      Lp.coeFn_sub SH H] with z hHz hsmul hsub
    rw [show (Y0 : ℂ → ℂ) z =
        (Complex.I • (SH - H) : PlaneL2) z by rfl,
      hsmul]
    change D z Complex.I = Complex.I * ((SH - H : PlaneL2) : ℂ → ℂ) z
    have hH : (H : ℂ → ℂ) z = h z := by simpa [H] using hHz
    rw [hsub]
    change D z Complex.I =
      Complex.I * ((SH : ℂ → ℂ) z - (H : ℂ → ℂ) z)
    rw [hH]
    simp [D, cauchyTransformLpWeakDifferential,
      realLinearMapOfWirtinger_apply]
    ring
  have hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Set.univ U D := by
    apply isWeakDerivativeOn_univ_of_closedBall_exhaustion
    intro m
    let K : Set ℂ := Metric.closedBall (0 : ℂ) (m : ℝ)
    let μK : Measure ℂ := volume.restrict K
    let u : ℕ → ℂ → ℂ := fun n ↦ cauchyTransform (φ n)
    let du : ℕ → ℂ → ℂ →L[ℝ] ℂ := fun n ↦
      cauchyTransformWeakDifferential (φ n)
    have hsmooth (n : ℕ) := cauchyTransform_isLocalW12On (φ n)
    have hweakn (n : ℕ) :
        JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
          K (u n) (du n) := by
      exact (hsmooth n).2.1.mono_set (Set.subset_univ _)
    have hmemu (n : ℕ) : MemLp (u n) 2 μK :=
      ((hsmooth n).2.2 K (isCompact_closedBall _ _) (Set.subset_univ _)).1
    have hmemdu (n : ℕ) : MemLp (du n) 2 μK :=
      ((hsmooth n).2.2 K (isCompact_closedBall _ _) (Set.subset_univ _)).2
    have hmemx (n : ℕ) : MemLp (fun z ↦ du n z 1) 2 μK := by
      simpa only [Function.comp_def] using
        ((ContinuousLinearMap.apply ℝ ℂ) 1).comp_memLp' (hmemdu n)
    have hmemy (n : ℕ) : MemLp (fun z ↦ du n z Complex.I) 2 μK := by
      simpa only [Function.comp_def] using
        ((ContinuousLinearMap.apply ℝ ℂ) Complex.I).comp_memLp' (hmemdu n)
    have hmemU : MemLp U 2 μK :=
      memLp_restrict_of_isCompact_of_continuousOn
        (isCompact_closedBall _ _) (continuous_cauchyTransformLp
          hpq hp2 hhp hzero).continuousOn
    let uLim : Lp ℂ 2 μK := hmemU.toLp U
    have huNorm : Tendsto
        (fun n ↦ eLpNorm (u n - U) 2 μK) atTop (𝓝 0) := by
      exact tendsto_eLpNorm_two_restrict_of_tendstoUniformlyOn
        u U K (isCompact_closedBall _ _) hmemu hmemU
          (tendstoUniformlyOn_cauchyTransform_of_tendsto_eLpNorm
            hpq hp2 hhp hzeroB φ hφsupp hconvp K
              (isCompact_closedBall _ _))
    have huStrong : Tendsto
        (fun n ↦ (hmemu n).toLp (u n)) atTop (𝓝 uLim) := by
      exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        u hmemu U hmemU).2 huNorm
    have hu : Tendsto
        (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μK) ((hmemu n).toLp (u n)))
        atTop (𝓝 (toWeakSpace ℝ (Lp ℂ 2 μK) uLim)) := by
      simpa only [toWeakSpaceCLM_eq_toWeakSpace] using
        ((toWeakSpaceCLM ℝ (Lp ℂ 2 μK)).continuous.tendsto
          (toWeakSpace ℝ (Lp ℂ 2 μK) uLim)).comp huStrong
    let dxLim : Lp ℂ 2 μK :=
      ((Lp.memLp X0).restrict K).toLp (X0 : ℂ → ℂ)
    let dyLim : Lp ℂ 2 μK :=
      ((Lp.memLp Y0).restrict K).toLp (Y0 : ℂ → ℂ)
    have hxClass (n : ℕ) :
        (hmemx n).toLp (fun z ↦ du n z 1) =
          ((Lp.memLp (X n)).restrict K).toLp (X n : ℂ → ℂ) := by
      apply MemLp.toLp_congr
      exact ae_restrict_of_ae (by simpa [du] using hcoordX n)
    have hyClass (n : ℕ) :
        (hmemy n).toLp (fun z ↦ du n z Complex.I) =
          ((Lp.memLp (Y n)).restrict K).toLp (Y n : ℂ → ℂ) := by
      apply MemLp.toLp_congr
      exact ae_restrict_of_ae (by simpa [du] using hcoordY n)
    have hxStrong : Tendsto
        (fun n ↦ (hmemx n).toLp (fun z ↦ du n z 1))
        atTop (𝓝 dxLim) := by
      simpa only [hxClass, dxLim] using
        Lp.tendsto_toLp_restrict_of_tendsto X X0 hX K
    have hyStrong : Tendsto
        (fun n ↦ (hmemy n).toLp (fun z ↦ du n z Complex.I))
        atTop (𝓝 dyLim) := by
      simpa only [hyClass, dyLim] using
        Lp.tendsto_toLp_restrict_of_tendsto Y Y0 hY K
    have hx : Tendsto
        (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μK)
          ((hmemx n).toLp (fun z ↦ du n z 1)))
        atTop (𝓝 (toWeakSpace ℝ (Lp ℂ 2 μK) dxLim)) := by
      simpa only [toWeakSpaceCLM_eq_toWeakSpace] using
        ((toWeakSpaceCLM ℝ (Lp ℂ 2 μK)).continuous.tendsto
          (toWeakSpace ℝ (Lp ℂ 2 μK) dxLim)).comp hxStrong
    have hy : Tendsto
        (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μK)
          ((hmemy n).toLp (fun z ↦ du n z Complex.I)))
        atTop (𝓝 (toWeakSpace ℝ (Lp ℂ 2 μK) dyLim)) := by
      simpa only [toWeakSpaceCLM_eq_toWeakSpace] using
        ((toWeakSpaceCLM ℝ (Lp ℂ 2 μK)).continuous.tendsto
          (toWeakSpace ℝ (Lp ℂ 2 μK) dyLim)).comp hyStrong
    have hclosed :=
      isWeakDerivativeOnEuclideanRegionWithValues_of_weak_tendsto_coordinates
        u du hweakn hmemu hmemx hmemy uLim dxLim dyLim hu hx hy
    have hvalue : U =ᵐ[μK] fun z ↦ uLim z :=
      hmemU.coeFn_toLp.symm
    have hderiv : D =ᵐ[μK] fun z ↦
        realLinearMapOfCoordinateValues (dxLim z) (dyLim z) := by
      filter_upwards [ae_restrict_of_ae hcoordX0,
        ae_restrict_of_ae hcoordY0,
        ((Lp.memLp X0).restrict K).coeFn_toLp,
        ((Lp.memLp Y0).restrict K).coeFn_toLp] with z hx0 hy0 hdx hdy
      rw [hdx, hdy, ← hx0, ← hy0]
      exact (realLinearMapOfCoordinateValues_apply_eq (D z)).symm
    exact (hclosed.congr_ae hvalue).congr_derivative_ae hderiv
  refine ⟨isOpen_univ, hweak, ?_⟩
  intro K hK _hKuniv
  have hmemX0 : MemLp (fun z ↦ D z 1) 2
      (volume : Measure ℂ) := MemLp.ae_eq hcoordX0.symm (Lp.memLp X0)
  have hmemY0 : MemLp (fun z ↦ D z Complex.I) 2
      (volume : Measure ℂ) := MemLp.ae_eq hcoordY0.symm (Lp.memLp Y0)
  refine ⟨memLp_restrict_of_isCompact_of_continuousOn hK
      (continuous_cauchyTransformLp hpq hp2 hhp hzero).continuousOn, ?_⟩
  have hcoordmem := realLinearMapOfCoordinateValues_memLp
    (hmemX0.restrict K) (hmemY0.restrict K)
  exact hcoordmem.ae_eq (Filter.Eventually.of_forall fun z ↦
    (realLinearMapOfCoordinateValues_apply_eq (D z)))

end

end Quasiconformal

end JJMath
