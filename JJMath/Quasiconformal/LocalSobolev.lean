import JJMath.Analysis.Sobolev.Pullback
import JJMath.Quasiconformal.LinearAlgebra
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Local planar Sobolev maps

This file packages the repository's regional weak-derivative predicate as the
standard local $W^{1,2}$ condition for complex-valued maps on planar domains.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Local planar Sobolev regularity
statement:
  A map $f:\Omega\to\mathbb C$ belongs to $W^{1,2}_{\mathrm{loc}}$ with weak
  differential $Df$ if $\Omega$ is open, the distributional first-derivative
  identities hold there, and $f$ and $Df$ are square-integrable on every
  compact subset of $\Omega$.
-/
def IsLocalW12On (Ω : Set ℂ) (f : ℂ → ℂ)
    (df : ℂ → ℂ →L[ℝ] ℂ) : Prop :=
  IsOpen Ω ∧
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω f df ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      MemLp f 2 (MeasureTheory.volume.restrict K) ∧
        MemLp df 2 (MeasureTheory.volume.restrict K)

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Addition in local planar $W^{1,2}$
statement:
  If $f,g\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak
  differentials $Df,Dg$, then $f+g$ belongs to the same local Sobolev class
  and has weak differential $Df+Dg$.
proof:
  Add the two distributional integration-by-parts identities. On every
  compact subset, the triangle inequality preserves square-integrability of
  both the values and the differential fields.
-/
theorem isLocalW12On_add
    {Ω : Set ℂ} {f g : ℂ → ℂ} {df dg : ℂ → ℂ →L[ℝ] ℂ}
    (hf : IsLocalW12On Ω f df) (hg : IsLocalW12On Ω g dg) :
    IsLocalW12On Ω (f + g) (df + dg) := by
  refine ⟨hf.1, ?_, ?_⟩
  · exact hf.2.1.add hg.2.1
  · intro K hK hKΩ
    constructor
    · exact MeasureTheory.MemLp.add
        (p := (2 : ENNReal)) (μ := volume.restrict K)
        (f := f) (g := g)
        (hf.2.2 K hK hKΩ).1 (hg.2.2 K hK hKΩ).1
    · exact MeasureTheory.MemLp.add
        (p := (2 : ENNReal)) (μ := volume.restrict K)
        (f := df) (g := dg)
        (hf.2.2 K hK hKΩ).2 (hg.2.2 K hK hKΩ).2

set_option maxHeartbeats 200000

/--
%%handwave
name:
  Local integrability of a planar Sobolev map
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$, then
  $f\in L^1_{\mathrm{loc}}(\Omega,\mathbb C)$.
proof:
  On every compact subset of $\Omega$, the local $L^2$ hypothesis and
  finiteness of planar volume imply $L^1$ integrability.
-/
theorem IsLocalW12On.value_locallyIntegrableOn
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    LocallyIntegrableOn f Ω MeasureTheory.volume := by
  rw [locallyIntegrableOn_iff h.1.isLocallyClosed]
  intro K hKΩ hKcompact
  let μK : Measure ℂ := MeasureTheory.volume.restrict K
  haveI : IsFiniteMeasure μK :=
    isFiniteMeasure_restrict.2 hKcompact.measure_ne_top
  simpa [IntegrableOn, μK] using
    (h.2.2 K hKcompact hKΩ).1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/--
%%handwave
name:
  Local integrability of the weak differential
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then $Df\in L^1_{\mathrm{loc}}(\Omega)$ as a field of real-linear
  maps.
proof:
  On every compact subset of $\Omega$, the local $L^2$ hypothesis for $Df$
  and finiteness of planar volume imply $L^1$ integrability.
-/
theorem IsLocalW12On.differential_locallyIntegrableOn
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    LocallyIntegrableOn df Ω MeasureTheory.volume := by
  rw [locallyIntegrableOn_iff h.1.isLocallyClosed]
  intro K hKΩ hKcompact
  let μK : Measure ℂ := MeasureTheory.volume.restrict K
  haveI : IsFiniteMeasure μK :=
    isFiniteMeasure_restrict.2 hKcompact.measure_ne_top
  simpa [IntegrableOn, μK] using
    (h.2.2 K hKcompact hKΩ).2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/--
%%handwave
name:
  Continuous functions are square-integrable on compact planar sets
statement:
  If $K\subseteq\mathbb C$ is compact and $f:K\to E$ is the restriction of a
  continuous normed-space-valued function, then $f\in L^2(K)$.
proof:
  A continuous function is measurable and bounded on a compact set, and a
  compact planar set has finite Lebesgue measure.
-/
theorem memLp_restrict_of_isCompact_of_continuousOn
    {E : Type} [NormedAddCommGroup E] {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → E} (hf : ContinuousOn f K) :
    MemLp f 2 (MeasureTheory.volume.restrict K) := by
  classical
  let μK : Measure ℂ := MeasureTheory.volume.restrict K
  haveI : IsFiniteMeasure μK := isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hf_aesm : AEStronglyMeasurable f μK := by
    simpa [μK] using
      hf.aestronglyMeasurable_of_isCompact hK hK.measurableSet
  rcases hK.exists_bound_of_continuousOn hf with ⟨C, hC⟩
  exact MemLp.of_bound (μ := μK) (p := (2 : ℝ≥0∞)) hf_aesm C
    (ae_restrict_of_forall_mem hK.measurableSet hC)

/--
%%handwave
name:
  Continuous linear postcomposition preserves weak differentials
statement:
  Let $u:\Omega\to E$ have weak differential $du$ and let
  $A:E\to F$ be continuous and real-linear. Then $A\circ u$ has weak
  differential $x\mapsto A\circ du_x$ on $\Omega$.
proof:
  Apply $A$ to both sides of the vector-valued integration-by-parts identity
  and commute it through the two Bochner integrals.
-/
theorem weakDerivative_postcomp_continuousLinearMap
    {H E F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {Ω : Set H} {u : H → E} {du : H → H →L[ℝ] E}
    (A : E →L[ℝ] F)
    (hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω u du) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun z ↦ A (u z)) (fun z ↦ A.comp (du z)) := by
  intro φ v
  rcases hweak φ v with ⟨hleft, hright, heq⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_smul] using A.integrable_comp hleft
  · simpa only [ContinuousLinearMap.comp_apply, map_smul] using
      A.integrable_comp hright
  · have hmapped := congrArg A heq
    rw [← A.integral_comp_comm hleft, map_neg,
      ← A.integral_comp_comm hright] at hmapped
    simpa only [map_neg, map_smul, ContinuousLinearMap.comp_apply] using hmapped

/--
%%handwave
name:
  Differential field of a cutoff-localized complex Sobolev map
statement:
  For a real-valued cutoff $\chi$, a complex-valued map $f$, and a
  differential field $Df$, the product-rule differential of $\chi f$ is
  $$
    z\longmapsto \chi(z)Df(z)+D\chi(z)\otimes f(z),
  $$
  where $(D\chi(z)\otimes f(z))(v)=D\chi(z)(v)f(z)$.
-/
noncomputable def complexWeakSobolevCutoffDerivative
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (χ : H → ℝ) (f : H → ℂ) (df : H → H →L[ℝ] ℂ) :
    H → H →L[ℝ] ℂ :=
  fun z ↦ χ z • df z + (fderiv ℝ χ z).smulRight (f z)

set_option maxHeartbeats 2000000 in
/--
%%handwave
name:
  Global square-integrability of a cutoff-localized planar Sobolev map
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak
  differential $Df$, and let $\chi$ be a smooth real-valued cutoff with
  compact support in $\Omega$. Then
  $$
    \chi f\in L^2(\mathbb C),\qquad
    \chi Df+D\chi\otimes f\in
      L^2\bigl(\mathbb C;\operatorname{Lin}_{\mathbb R}
        (\mathbb C,\mathbb C)\bigr).
  $$
proof:
  Restrict the local $L^2$ bounds for $f$ and $Df$ to the compact support of
  $\chi$. The functions $\chi$ and $D\chi$ are bounded there, so the two
  product-rule terms are square-integrable. Both localized fields vanish
  outside that compact set, which turns the restricted estimates into global
  ones.
-/
theorem IsLocalW12On.complexWeakSobolevCutoff_memLp
    {Q Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω) :
    MemLp (fun z : ℂ ↦ χ z • f z) 2 volume ∧
      MemLp
        (complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df)
        2 volume := by
  let K : Set ℂ := tsupport (χ : ℂ → ℝ)
  let μK : Measure ℂ := volume.restrict K
  have hK : IsCompact K := χ.compact_support
  have hKΩ : K ⊆ Ω := χ.support_subset
  have hfK : MemLp f 2 μK := by
    simpa [μK] using (hW.2.2 K hK hKΩ).1
  have hdfK : MemLp df 2 μK := by
    simpa [μK] using (hW.2.2 K hK hKΩ).2
  have hχ_cont : Continuous (χ : ℂ → ℝ) := χ.smooth.continuous
  have hχ_aesm : AEStronglyMeasurable (χ : ℂ → ℝ) μK :=
    hχ_cont.aestronglyMeasurable
  rcases hK.exists_bound_of_continuousOn hχ_cont.continuousOn with
    ⟨Cχ, hCχ⟩
  have hvalueK : MemLp (fun z : ℂ ↦ χ z • f z) 2 μK := by
    apply MemLp.of_le_mul hfK (hχ_aesm.smul hfK.aestronglyMeasurable)
    exact ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hCχ z hz) (norm_nonneg _)
  have hfirstK : MemLp (fun z : ℂ ↦ χ z • df z) 2 μK := by
    apply MemLp.of_le_mul hdfK (hχ_aesm.smul hdfK.aestronglyMeasurable)
    exact ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hCχ z hz) (norm_nonneg _)
  have hdχ_cont :
      Continuous (fun z : ℂ ↦ fderiv ℝ (χ : ℂ → ℝ) z) :=
    χ.smooth.continuous_fderiv (by simp)
  have hdχ_aesm :
      AEStronglyMeasurable
        (fun z : ℂ ↦ fderiv ℝ (χ : ℂ → ℝ) z) μK :=
    hdχ_cont.aestronglyMeasurable
  rcases hK.exists_bound_of_continuousOn hdχ_cont.continuousOn with
    ⟨Cdχ, hCdχ⟩
  have herror_aesm :
      AEStronglyMeasurable
        (fun z : ℂ ↦ (fderiv ℝ (χ : ℂ → ℝ) z).smulRight (f z)) μK :=
    (ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous₂
      |>.comp_aestronglyMeasurable₂ hdχ_aesm hfK.aestronglyMeasurable
  have herrorK :
      MemLp
        (fun z : ℂ ↦ (fderiv ℝ (χ : ℂ → ℝ) z).smulRight (f z))
        2 μK := by
    apply MemLp.of_le_mul hfK herror_aesm
    exact ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hCdχ z hz) (norm_nonneg _)
  have hderivK :
      MemLp
        (complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df)
        2 μK := by
    change MemLp
      (fun z : ℂ ↦
        χ z • df z + (fderiv ℝ (χ : ℂ → ℝ) z).smulRight (f z))
      2 μK
    have hsum :
        MemLp
          ((fun z : ℂ ↦ χ z • df z) +
            fun z : ℂ ↦ (fderiv ℝ (χ : ℂ → ℝ) z).smulRight (f z))
          (2 : ENNReal) μK :=
      MeasureTheory.MemLp.add
        (p := (2 : ENNReal)) (μ := μK)
        (f := fun z : ℂ ↦ χ z • df z)
        (g := fun z : ℂ ↦
          (fderiv ℝ (χ : ℂ → ℝ) z).smulRight (f z))
        hfirstK herrorK
    simpa only [Pi.add_apply] using hsum
  have hvalue_support :
      Function.support (fun z : ℂ ↦ χ z • f z) ⊆ K := by
    intro z hz
    by_contra hzK
    have hχ_zero : χ z = 0 := image_eq_zero_of_notMem_tsupport hzK
    exact hz (by simp [hχ_zero])
  have hderiv_support :
      Function.support
        (complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df) ⊆ K := by
    intro z hz
    by_contra hzK
    have hχ_zero : χ z = 0 := image_eq_zero_of_notMem_tsupport hzK
    have hdχ_zero : fderiv ℝ (χ : ℂ → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (χ : ℂ → ℝ)) hzK
    exact hz (by simp [complexWeakSobolevCutoffDerivative, hχ_zero, hdχ_zero])
  change MemLp (fun z : ℂ ↦ χ z • f z) 2 (volume.restrict K) at hvalueK
  change
    MemLp
      (complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df)
      2 (volume.restrict K) at hderivK
  constructor
  · have hindicator :
        K.indicator (fun z : ℂ ↦ χ z • f z) =
          fun z : ℂ ↦ χ z • f z :=
      Set.indicator_eq_self.2 hvalue_support
    rw [← hindicator]
    exact
      (memLp_indicator_iff_restrict
        (f := fun z : ℂ ↦ χ z • f z)
        (p := (2 : ENNReal)) (μ := volume) hK.measurableSet).2
        hvalueK
  · have hindicator :
        K.indicator
            (complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df) =
          complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df :=
      Set.indicator_eq_self.2 hderiv_support
    rw [← hindicator]
    exact
      (memLp_indicator_iff_restrict
        (f := complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df)
        (p := (2 : ENNReal)) (μ := volume) hK.measurableSet).2
        hderivK

private def postcompReCLM :
    (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (isBoundedBilinearMap_comp
    (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
      Complex.reCLM

private def postcompImCLM :
    (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (isBoundedBilinearMap_comp
    (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
      Complex.imCLM

private def imOfRealCLM : ℝ →L[ℝ] ℂ :=
  (realLinearMapOfWirtinger Complex.I 0).comp Complex.ofRealCLM

/--
%%handwave
name:
  Complex weak chain rule for locally bi-Lipschitz coordinate changes
statement:
  Let $T:U\to\Omega$ be a locally bi-Lipschitz bijection of open planar
  domains with locally Lipschitz inverse, and suppose both directions preserve
  null sets. If $f$ has weak differential $Df$ on $\Omega$, and $f$ and $Df$
  are square-integrable on every compact subset, then $f\circ T$ has weak
  differential
  $$
  D(f\circ T)(z)=Df(T(z))\circ DT(z)
  $$
  on $U$.
proof:
  Apply the real-valued local weak pullback theorem to the real and imaginary
  parts of $f$. Embed the resulting two scalar identities in $\mathbb C$ and
  add them to recover the complex-valued identity.
-/
theorem weakDerivative_comp_locallyBiLipschitz
    {U Ω : Set ℂ} {T S f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hU_open : IsOpen U) (hΩ_open : IsOpen Ω)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (hT_lip : LocallyLipschitzOn U T)
    (hS_lip : LocallyLipschitzOn Ω S)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω f df)
    (hf : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      MemLp f 2 (MeasureTheory.volume.restrict K))
    (hdf : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      MemLp df 2 (MeasureTheory.volume.restrict K)) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues U
      (fun z ↦ f (T z))
      (fun z ↦ (df (T z)).comp (fderiv ℝ T z)) := by
  have hweakRe :=
    weakDerivative_postcomp_continuousLinearMap Complex.reCLM hweak
  have hweakIm :=
    weakDerivative_postcomp_continuousLinearMap Complex.imCLM hweak
  have hRe := hweakRe.comp_locallyBiLipschitz
    hU_open hΩ_open hT_maps hS_maps hS_left hT_left
    hT_lip hS_lip hT_qmp hS_qmp
    (fun K hK hKΩ ↦ Complex.reCLM.comp_memLp' (hf K hK hKΩ))
    (fun K hK hKΩ ↦ postcompReCLM.comp_memLp' (hdf K hK hKΩ))
  have hIm := hweakIm.comp_locallyBiLipschitz
    hU_open hΩ_open hT_maps hS_maps hS_left hT_left
    hT_lip hS_lip hT_qmp hS_qmp
    (fun K hK hKΩ ↦ Complex.imCLM.comp_memLp' (hf K hK hKΩ))
    (fun K hK hKΩ ↦ postcompImCLM.comp_memLp' (hdf K hK hKΩ))
  have hReC :=
    weakDerivative_postcomp_continuousLinearMap Complex.ofRealCLM hRe
  have hImC :=
    weakDerivative_postcomp_continuousLinearMap imOfRealCLM hIm
  have hadd := hReC.add hImC
  convert hadd using 1
  · funext z
    apply Complex.ext <;> simp [imOfRealCLM]
  · funext z
    ext v
    apply Complex.ext <;>
      simp [imOfRealCLM, ContinuousLinearMap.comp_apply]

/--
%%handwave
name:
  Local planar Sobolev regularity under bi-Lipschitz coordinate changes
statement:
  Let $T:U\to\Omega$ be a locally bi-Lipschitz bijection of open planar
  domains with locally Lipschitz inverse, and suppose both directions preserve
  null sets. If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ with weak
  differential $Df$, then $f\circ T\in W^{1,2}_{\mathrm{loc}}(U,\mathbb C)$
  with weak differential $z\mapsto Df(T(z))\circ DT(z)$.
proof:
  The weak identity is the [complex weak chain rule](lean:JJMath.Quasiconformal.weakDerivative_comp_locallyBiLipschitz). On each compact subset of $U$, finite measure distortion pulls back the local $L^2$ bounds for $f$ and $Df$, while the differential of $T$ is uniformly bounded there.
-/
theorem IsLocalW12On.comp_locallyBiLipschitz
    {U Ω : Set ℂ} {T S f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df)
    (hU_open : IsOpen U)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (hT_lip : LocallyLipschitzOn U T)
    (hS_lip : LocallyLipschitzOn Ω S)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U)) :
    IsLocalW12On U (fun z ↦ f (T z))
      (fun z ↦ (df (T z)).comp (fderiv ℝ T z)) := by
  refine ⟨hU_open, weakDerivative_comp_locallyBiLipschitz
    hU_open h.1 hT_maps hS_maps hS_left hT_left
    hT_lip hS_lip hT_qmp hS_qmp h.2.1
    (fun K hK hKΩ ↦ (h.2.2 K hK hKΩ).1)
    (fun K hK hKΩ ↦ (h.2.2 K hK hKΩ).2), ?_⟩
  intro K hK hKU
  let Q : Set ℂ := T '' K
  have hT_cont_K : ContinuousOn T K :=
    (hT_lip.mono hKU).continuousOn
  have hQ_compact : IsCompact Q := by
    simpa [Q] using hK.image_of_continuousOn hT_cont_K
  have hQΩ : Q ⊆ Ω := by
    rintro y ⟨z, hzK, rfl⟩
    exact hT_maps (hKU hzK)
  have hf_pull : MemLp (fun z : ℂ ↦ f (T z)) 2
      (MeasureTheory.volume.restrict K) :=
    JJMath.Uniformization.locallyBiLipschitz_pullback_memLp_on_compact_of_image_subset
      hU_open h.1 hT_maps hS_maps hS_left hT_left
      hT_lip hS_lip hT_qmp hS_qmp hK hKU (Q := Q)
      (by simp [Q]) (h.2.2 Q hQ_compact hQΩ).1
  have hdf_pull : MemLp (fun z : ℂ ↦ df (T z)) 2
      (MeasureTheory.volume.restrict K) :=
    JJMath.Uniformization.locallyBiLipschitz_pullback_memLp_on_compact_of_image_subset
      hU_open h.1 hT_maps hS_maps hS_left hT_left
      hT_lip hS_lip hT_qmp hS_qmp hK hKU (Q := Q)
      (by simp [Q]) (h.2.2 Q hQ_compact hQΩ).2
  let compCLM :
      (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℂ)).toContinuousLinearMap
  have hDT_aesm : AEStronglyMeasurable (fun z : ℂ ↦ fderiv ℝ T z)
      (MeasureTheory.volume.restrict K) :=
    (measurable_fderiv ℝ T).aestronglyMeasurable
  have hfield_aesm :
      AEStronglyMeasurable
        (fun z : ℂ ↦ (df (T z)).comp (fderiv ℝ T z))
        (MeasureTheory.volume.restrict K) := by
    simpa [compCLM] using
      compCLM.aestronglyMeasurable_comp₂
        hdf_pull.aestronglyMeasurable hDT_aesm
  rcases
      JJMath.Uniformization.locallyLipschitzOn_fderiv_norm_bound_on_compact
        hU_open hT_lip hK hKU with
    ⟨C, _hC, hC_bound⟩
  have hfield : MemLp
      (fun z : ℂ ↦ (df (T z)).comp (fderiv ℝ T z)) 2
      (MeasureTheory.volume.restrict K) :=
    MemLp.of_le_mul hdf_pull hfield_aesm
      (ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ by
        calc
          ‖(df (T z)).comp (fderiv ℝ T z)‖
              ≤ ‖df (T z)‖ * ‖fderiv ℝ T z‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖df (T z)‖ * C :=
            mul_le_mul_of_nonneg_left (hC_bound z hz) (norm_nonneg _)
          _ = C * ‖df (T z)‖ := mul_comm _ _)
  exact ⟨hf_pull, hfield⟩

/--
%%handwave
name:
  Local Sobolev regularity under source translation
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then for every $c\in\mathbb C$ the translated map
  $z\mapsto f(z+c)$ belongs to
  $W^{1,2}_{\mathrm{loc}}(\{z:z+c\in\Omega\},\mathbb C)$ with weak
  differential $z\mapsto Df(z+c)$.
proof:
  Apply [the locally bi-Lipschitz Sobolev chain rule](lean:JJMath.Quasiconformal.IsLocalW12On.comp_locallyBiLipschitz) to the mutually inverse translations $z\mapsto z+c$ and $z\mapsto z-c$. Both are isometries and preserve planar volume, and the differential of a translation is the identity.
-/
theorem IsLocalW12On.comp_addRight
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) (c : ℂ) :
    IsLocalW12On ((fun z : ℂ => z + c) ⁻¹' Ω)
      (fun z => f (z + c)) (fun z => df (z + c)) := by
  let U := (fun z : ℂ => z + c) ⁻¹' Ω
  let T : ℂ → ℂ := fun z => z + c
  let S : ℂ → ℂ := fun z => z - c
  have hU : IsOpen U := h.1.preimage (continuous_id.add continuous_const)
  have hT_maps : MapsTo T U Ω := by
    intro z hz
    exact hz
  have hS_maps : MapsTo S Ω U := by
    intro z hz
    change z - c + c ∈ Ω
    simpa using hz
  have hT_lip : LocallyLipschitzOn U T :=
    (IsometryEquiv.addRight c).isometry.lipschitz.locallyLipschitz.locallyLipschitzOn
  have hS_lip : LocallyLipschitzOn Ω S := by
    simpa [S, sub_eq_add_neg] using
      (IsometryEquiv.addRight (-c)).isometry.lipschitz.locallyLipschitz.locallyLipschitzOn
  have hT_qmp : Measure.QuasiMeasurePreserving T
      (volume.restrict U) (volume.restrict Ω) :=
    (JJMath.Uniformization.measurePreserving_add_right_volume c).quasiMeasurePreserving.restrict
      hT_maps
  have hS_qmp : Measure.QuasiMeasurePreserving S
      (volume.restrict Ω) (volume.restrict U) := by
    simpa [S, sub_eq_add_neg] using
      (JJMath.Uniformization.measurePreserving_add_right_volume (-c)).quasiMeasurePreserving.restrict
        hS_maps
  have hpull := h.comp_locallyBiLipschitz hU hT_maps hS_maps
    (by intro z hz; simp [T, S]) (by intro z hz; simp [T, S])
    hT_lip hS_lip hT_qmp hS_qmp
  simpa [U, T, S] using hpull

/--
%%handwave
name:
  Classical differentials are weak differentials
statement:
  If $f:\mathbb C\to\mathbb C$ is continuously differentiable, then its
  classical real differential is a weak differential of $f$ on every planar
  set $\Omega$.
proof:
  Apply integration by parts to $f$ and each smooth compactly supported test
  function. The test and its directional derivative have compact support in
  $\Omega$, so the full-plane identity equals the corresponding identity over
  $\Omega$.
-/
theorem weakDerivativeOn_of_contDiff {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω f
      (fun z ↦ fderiv ℝ f z) := by
  intro φ v
  let dφ : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  have hφ_cont : Continuous (φ : ℂ → ℝ) := φ.smooth.continuous
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hf_cont : Continuous f := hf.continuous
  have hdf_cont : Continuous (fun z ↦ fderiv ℝ f z) :=
    hf.continuous_fderiv (by norm_num)
  have hdφ_compact : IsCompact (tsupport dφ) :=
    φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (by
        simpa [dφ] using
          tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (φ : ℂ → ℝ)) v)
  have hleft_full : Integrable (fun z ↦ dφ z • f z)
      MeasureTheory.volume := by
    apply (hdφ_cont.smul hf_cont).integrable_of_hasCompactSupport
    exact hdφ_compact.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left dφ f)
  have hright_full : Integrable (fun z ↦ φ z • fderiv ℝ f z v)
      MeasureTheory.volume := by
    apply (hφ_cont.smul
      (hdf_cont.clm_apply continuous_const)).integrable_of_hasCompactSupport
    exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left (φ : ℂ → ℝ)
        (fun z ↦ fderiv ℝ f z v))
  have hprod_full : Integrable (fun z ↦ φ z • f z)
      MeasureTheory.volume := by
    apply (hφ_cont.smul hf_cont).integrable_of_hasCompactSupport
    exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left (φ : ℂ → ℝ) f)
  have hibp :
      ∫ z, φ z • fderiv ℝ f z v ∂MeasureTheory.volume =
        -∫ z, dφ z • f z ∂MeasureTheory.volume := by
    simpa [dφ] using
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (μ := (MeasureTheory.volume : Measure ℂ))
        (f := (φ : ℂ → ℝ)) (g := f) (v := v)
        hleft_full hright_full hprod_full
        (fun z _ ↦ (φ.smooth.differentiable (by simp)) z)
        (fun z _ ↦ hf.differentiable (by norm_num) z)
  have hdφ_support : tsupport dφ ⊆ Ω := by
    simpa [dφ] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : ℂ → ℝ)) v).trans φ.support_subset
  have hleft_set :
      ∫ z, dφ z • f z ∂MeasureTheory.volume =
        ∫ z in Ω, dφ z • f z ∂MeasureTheory.volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
      image_eq_zero_of_notMem_tsupport (fun htz ↦
        hz (((tsupport_smul_subset_left dφ f).trans hdφ_support) htz))).symm
  have hright_set :
      ∫ z, φ z • fderiv ℝ f z v ∂MeasureTheory.volume =
        ∫ z in Ω, φ z • fderiv ℝ f z v ∂MeasureTheory.volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
      image_eq_zero_of_notMem_tsupport (fun htz ↦
        hz (((tsupport_smul_subset_left (φ : ℂ → ℝ)
          (fun z ↦ fderiv ℝ f z v)).trans φ.support_subset) htz))).symm
  refine ⟨?_, ?_, ?_⟩
  · simpa [dφ] using hleft_full.restrict (s := Ω)
  · simpa using hright_full.restrict (s := Ω)
  · rw [← hleft_set, ← hright_set]
    exact (neg_eq_iff_eq_neg.mpr hibp).symm

/--
%%handwave
name:
  Classical differentials on open regions are weak differentials
statement:
  Let $\Omega\subseteq\mathbb C$ be open. If
  $f:\mathbb C\to\mathbb C$ is continuously real differentiable on $\Omega$,
  then $z\mapsto Df(z)$ is a weak differential of $f$ on $\Omega$.
proof:
  Integrate by parts against each compactly supported test. Every test and
  its directional derivative are supported in a compact subset of $\Omega$,
  where $f$ and $Df$ are continuous and hence integrable; the resulting
  full-plane identity therefore equals the identity over $\Omega$.
-/
theorem weakDerivativeOn_of_contDiffOn
    {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω f
      (fun z ↦ fderiv ℝ f z) := by
  intro φ v
  let dφ : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  have hφ_cont : Continuous (φ : ℂ → ℝ) := φ.smooth.continuous
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hf_cont : ContinuousOn f Ω := hf.continuousOn
  have hdf_cont : ContinuousOn (fun z ↦ fderiv ℝ f z) Ω :=
    hf.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  have hdφ_compact : IsCompact (tsupport dφ) :=
    φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (by
        simpa [dφ] using
          tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (φ : ℂ → ℝ)) v)
  have hdφ_support : tsupport dφ ⊆ Ω := by
    simpa [dφ] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : ℂ → ℝ)) v).trans φ.support_subset
  have hleft_full : Integrable (fun z ↦ dφ z • f z) volume := by
    apply
      JJMath.Uniformization.integrable_of_continuousOn_of_tsupport_subset_isCompact
        (hdφ_cont.continuousOn.smul hf_cont)
        hΩ
        ((tsupport_smul_subset_left dφ f).trans hdφ_support)
    exact hdφ_compact.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left dφ f)
  have hright_full :
      Integrable (fun z ↦ φ z • fderiv ℝ f z v) volume := by
    apply
      JJMath.Uniformization.integrable_of_continuousOn_of_tsupport_subset_isCompact
        (hφ_cont.continuousOn.smul
          (hdf_cont.clm_apply continuousOn_const))
        hΩ
        ((tsupport_smul_subset_left (φ : ℂ → ℝ)
          (fun z ↦ fderiv ℝ f z v)).trans φ.support_subset)
    exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left (φ : ℂ → ℝ)
        (fun z ↦ fderiv ℝ f z v))
  have hprod_full : Integrable (fun z ↦ φ z • f z) volume := by
    apply
      JJMath.Uniformization.integrable_of_continuousOn_of_tsupport_subset_isCompact
        (hφ_cont.continuousOn.smul hf_cont)
        hΩ
        ((tsupport_smul_subset_left (φ : ℂ → ℝ) f).trans
          φ.support_subset)
    exact φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left (φ : ℂ → ℝ) f)
  have hibp :
      ∫ z, φ z • fderiv ℝ f z v ∂volume =
        -∫ z, dφ z • f z ∂volume := by
    simpa [dφ] using
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (μ := (volume : Measure ℂ))
        (f := (φ : ℂ → ℝ)) (g := f) (v := v)
        hleft_full hright_full hprod_full
        (fun z _ ↦ (φ.smooth.differentiable (by simp)) z)
        (fun z hz ↦
          ((hf z (φ.support_subset hz)).contDiffAt
            (hΩ.mem_nhds (φ.support_subset hz))).differentiableAt
              (by norm_num))
  have hleft_set :
      ∫ z, dφ z • f z ∂volume =
        ∫ z in Ω, dφ z • f z ∂volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
      image_eq_zero_of_notMem_tsupport (fun htz ↦
        hz (((tsupport_smul_subset_left dφ f).trans hdφ_support) htz))).symm
  have hright_set :
      ∫ z, φ z • fderiv ℝ f z v ∂volume =
        ∫ z in Ω, φ z • fderiv ℝ f z v ∂volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
      image_eq_zero_of_notMem_tsupport (fun htz ↦
        hz (((tsupport_smul_subset_left (φ : ℂ → ℝ)
          (fun z ↦ fderiv ℝ f z v)).trans φ.support_subset) htz))).symm
  refine ⟨?_, ?_, ?_⟩
  · simpa [dφ] using hleft_full.restrict (s := Ω)
  · simpa using hright_full.restrict (s := Ω)
  · rw [← hleft_set, ← hright_set]
    exact (neg_eq_iff_eq_neg.mpr hibp).symm

/--
%%handwave
name:
  Continuously differentiable maps are locally Sobolev
statement:
  Let $\Omega\subseteq\mathbb C$ be open. If
  $f:\mathbb C\to\mathbb C$ is continuously real differentiable on $\Omega$,
  then
  $$
    f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)
  $$
  with weak differential $Df$.
proof:
  The classical differential is a weak differential on the open region.
  On each compact subset of $\Omega$, continuity of $f$ and $Df$ gives
  boundedness and hence square-integrability.
-/
theorem isLocalW12On_of_contDiffOn
    {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) :
    IsLocalW12On Ω f (fun z ↦ fderiv ℝ f z) := by
  refine ⟨hΩ, weakDerivativeOn_of_contDiffOn hΩ hf, ?_⟩
  intro K hK hKΩ
  have hf_cont : ContinuousOn f K :=
    hf.continuousOn.mono hKΩ
  have hdf_cont : ContinuousOn (fun z ↦ fderiv ℝ f z) K :=
    (hf.continuousOn_fderiv_of_isOpen hΩ (by norm_num)).mono hKΩ
  exact
    ⟨memLp_restrict_of_isCompact_of_continuousOn hK hf_cont,
      memLp_restrict_of_isCompact_of_continuousOn hK hdf_cont⟩

/--
%%handwave
name:
  Local Sobolev regularity under real-affine postcomposition
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, $A:\mathbb C\to\mathbb C$ is continuous and real-linear, and
  $c\in\mathbb C$, then $A\circ f+c$ is locally Sobolev with weak
  differential $z\mapsto A\circ Df(z)$.
proof:
  Postcompose the weak identity by $A$ and add the constant map, whose weak
  differential is zero. Continuous linear maps preserve local $L^2$ bounds,
  while constants are square-integrable on compact sets.
-/
theorem IsLocalW12On.postcomp_realAffine
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) (A : ℂ →L[ℝ] ℂ) (c : ℂ) :
    IsLocalW12On Ω (fun z ↦ A (f z) + c)
      (fun z ↦ A.comp (df z)) := by
  have hA :=
    weakDerivative_postcomp_continuousLinearMap A h.2.1
  have hc := weakDerivativeOn_of_contDiff
    (Ω := Ω) (f := fun _ : ℂ ↦ c) contDiff_const
  have hweak := hA.add hc
  refine ⟨h.1, ?_, ?_⟩
  · simpa using hweak
  · intro K hK hKΩ
    have hAK : MemLp (fun z : ℂ ↦ A (f z)) 2
        (MeasureTheory.volume.restrict K) := by
      simpa [Function.comp_def] using
        A.comp_memLp' (h.2.2 K hK hKΩ).1
    have hcK : MemLp (fun _ : ℂ ↦ c) 2
        (MeasureTheory.volume.restrict K) :=
      memLp_restrict_of_isCompact_of_continuousOn
        hK continuous_const.continuousOn
    let postA : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
      (isBoundedBilinearMap_comp
        (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℂ)).toContinuousLinearMap A
    have hdfK : MemLp (fun z : ℂ ↦ A.comp (df z)) 2
        (MeasureTheory.volume.restrict K) := by
      simpa [postA, Function.comp_def] using
        postA.comp_memLp' (h.2.2 K hK hKΩ).2
    exact ⟨hAK.add hcK, hdfK⟩

/--
%%handwave
name:
  Local Sobolev regularity under conformal affine postcomposition
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then $z\mapsto af(z)+c$ is locally Sobolev with weak differential
  $z\mapsto(\xi\mapsto a\xi)\circ Df(z)$.
proof:
  Apply real-affine postcomposition to the complex-linear map
  $\xi\mapsto a\xi$.
-/
theorem IsLocalW12On.postcomp_complexAffine
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) (a c : ℂ) :
    IsLocalW12On Ω (fun z ↦ a * f z + c)
      (fun z ↦ (realLinearMapOfWirtinger a 0).comp (df z)) := by
  simpa using h.postcomp_realAffine (realLinearMapOfWirtinger a 0) c

/--
%%handwave
name:
  Affine maps are locally Sobolev
statement:
  On every open planar set $\Omega$, the real-affine map
  $f(z)=az+b\overline z+c$ belongs to $W^{1,2}_{\mathrm{loc}}(\Omega)$ with
  constant weak differential $\xi\mapsto a\xi+b\overline\xi$.
proof:
  The affine map is continuously differentiable with the stated differential,
  hence satisfies the weak integration-by-parts identity. Both the map and its
  constant differential are continuous and therefore square-integrable on
  compact subsets.
-/
theorem isLocalW12On_affineMap {Ω : Set ℂ} (hΩ : IsOpen Ω) (a b c : ℂ) :
    IsLocalW12On Ω (affineMap a b c)
      (fun _ ↦ realLinearMapOfWirtinger a b) := by
  have hcont : ContDiff ℝ 1 (affineMap a b c) :=
    (realLinearMapOfWirtinger a b).contDiff.add contDiff_const
  have hweak := weakDerivativeOn_of_contDiff (Ω := Ω) hcont
  refine ⟨hΩ, ?_, ?_⟩
  · simpa only [(hasFDerivAt_affineMap a b c _).fderiv] using hweak
  · intro K hK _hKΩ
    exact ⟨memLp_restrict_of_isCompact_of_continuousOn hK hcont.continuous.continuousOn,
      memLp_restrict_of_isCompact_of_continuousOn hK continuous_const.continuousOn⟩

/--
%%handwave
name:
  Regional weak derivatives restrict to smaller planar sets
statement:
  If $Df$ is a weak differential of $f$ on $\Omega$ and $U\subseteq\Omega$,
  then $Df$ is a weak differential of $f$ on $U$.
proof:
  Regard a compactly supported test on $U$ as a test on $\Omega$. Both the test
  and its directional derivative vanish outside $U$, so the integrals over the
  two regions agree.
-/
theorem weakDerivative_mono_set
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U Ω : Set ℂ} {f : ℂ → E} {df : ℂ → ℂ →L[ℝ] E}
    (hweak : JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω f df)
    (hUΩ : U ⊆ Ω) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues U f df := by
  intro φ v
  let ψ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := φ
      smooth := φ.smooth
      support_subset := φ.support_subset.trans hUΩ
      compact_support := φ.compact_support }
  rcases hweak ψ v with ⟨hleftΩ, hrightΩ, heqΩ⟩
  let left : ℂ → E := fun z ↦ (fderiv ℝ (φ : ℂ → ℝ) z v) • f z
  let right : ℂ → E := fun z ↦ φ z • df z v
  have hleft_int_U : Integrable left (MeasureTheory.volume.restrict U) := by
    have hres := hleftΩ.restrict (s := U)
    simpa [left, ψ, Measure.restrict_restrict_of_subset hUΩ] using hres
  have hright_int_U : Integrable right (MeasureTheory.volume.restrict U) := by
    have hres := hrightΩ.restrict (s := U)
    simpa [right, ψ, Measure.restrict_restrict_of_subset hUΩ] using hres
  have hleft_zero_U : ∀ z : ℂ, z ∉ U → left z = 0 := by
    intro z hzU
    have hz_not : z ∉ tsupport (fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v) := by
      intro hz
      exact hzU <| φ.support_subset <|
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : ℂ → ℝ)) v) hz
    have hzero : fderiv ℝ (φ : ℂ → ℝ) z v = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : ℂ ↦ fderiv ℝ (φ : ℂ → ℝ) y v) hz_not
    simp [left, hzero]
  have hright_zero_U : ∀ z : ℂ, z ∉ U → right z = 0 := by
    intro z hzU
    have hz_not : z ∉ tsupport (φ : ℂ → ℝ) := by
      intro hz
      exact hzU (φ.support_subset hz)
    have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hz_not
    simp [right, hzero]
  have hleft_zero_Ω : ∀ z : ℂ, z ∉ Ω → left z = 0 := by
    intro z hzΩ
    exact hleft_zero_U z (fun hzU ↦ hzΩ (hUΩ hzU))
  have hright_zero_Ω : ∀ z : ℂ, z ∉ Ω → right z = 0 := by
    intro z hzΩ
    exact hright_zero_U z (fun hzU ↦ hzΩ (hUΩ hzU))
  have hleft_U_eq_Ω :
      ∫ z in U, left z ∂MeasureTheory.volume =
        ∫ z in Ω, left z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero_U,
      setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero_Ω]
  have hright_U_eq_Ω :
      ∫ z in U, right z ∂MeasureTheory.volume =
        ∫ z in Ω, right z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero_U,
      setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero_Ω]
  refine ⟨?_, ?_, ?_⟩
  · simpa [left] using hleft_int_U
  · simpa [right] using hright_int_U
  · calc
      ∫ z in U, (fderiv ℝ (φ : ℂ → ℝ) z v) • f z ∂MeasureTheory.volume =
          ∫ z in U, left z ∂MeasureTheory.volume := rfl
      _ = ∫ z in Ω, left z ∂MeasureTheory.volume := hleft_U_eq_Ω
      _ = -∫ z in Ω, right z ∂MeasureTheory.volume := by
        simpa [left, right, ψ] using heqΩ
      _ = -∫ z in U, right z ∂MeasureTheory.volume := by rw [hright_U_eq_Ω]
      _ = -∫ z in U, φ z • df z v ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Local Sobolev regularity restricts to open subdomains
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ with weak differential
  $Df$ and $U\subseteq\Omega$ is open, then
  $f\in W^{1,2}_{\mathrm{loc}}(U,\mathbb C)$ with the same weak differential.
proof:
  Restrict the weak integration-by-parts identity to $U$. Every compact subset
  of $U$ is a compact subset of $\Omega$, so the local square-integrability
  conditions are inherited unchanged.
-/
theorem IsLocalW12On.mono {U Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ} (h : IsLocalW12On Ω f df)
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) :
    IsLocalW12On U f df := by
  refine ⟨hU, weakDerivative_mono_set h.2.1 hUΩ, ?_⟩
  intro K hK hKU
  exact h.2.2 K hK (hKU.trans hUΩ)

/--
%%handwave
name:
  Local Sobolev regularity is unchanged by an almost-everywhere representative
statement:
  Suppose $f=g$ almost everywhere on $\Omega$. If
  $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then $g$ belongs to the same local Sobolev class with the same weak
  differential $Df$.
proof:
  Almost-everywhere equality preserves the map-side integrability and integral
  in every weak-derivative identity. Restrict the equality to each compact
  subset to transfer the local $L^2$ condition.
-/
theorem IsLocalW12On.congr_ae
    {Ω : Set ℂ} {f g : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df)
    (hgf : g =ᵐ[MeasureTheory.volume.restrict Ω] f) :
    IsLocalW12On Ω g df := by
  refine ⟨h.1, ?_, ?_⟩
  · intro φ v
    rcases h.2.1 φ v with ⟨hleft, hright, heq⟩
    have hleft_ae :
        (fun z ↦ (fderiv ℝ (φ : ℂ → ℝ) z v) • f z) =ᵐ[
          MeasureTheory.volume.restrict Ω]
        (fun z ↦ (fderiv ℝ (φ : ℂ → ℝ) z v) • g z) := by
      filter_upwards [hgf.symm] with z hz
      rw [hz]
    refine ⟨hleft.congr hleft_ae, hright, ?_⟩
    calc
      ∫ z in Ω, (fderiv ℝ (φ : ℂ → ℝ) z v) • g z
          ∂MeasureTheory.volume =
          ∫ z in Ω, (fderiv ℝ (φ : ℂ → ℝ) z v) • f z
            ∂MeasureTheory.volume := integral_congr_ae hleft_ae.symm
      _ = -∫ z in Ω, φ z • df z v ∂MeasureTheory.volume := heq
  · intro K hK hKΩ
    have hgfK := ae_restrict_of_ae_restrict_of_subset hKΩ hgf
    exact ⟨(memLp_congr_ae hgfK).mpr (h.2.2 K hK hKΩ).1,
      (h.2.2 K hK hKΩ).2⟩

/--
%%handwave
name:
  Holomorphic weak Wirtinger field
statement:
  For a weak differential field $Df$, the holomorphic Wirtinger field is
  $z\mapsto\partial_z f(z)$.
-/
def weakDZField (df : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) : ℂ :=
  weakDZ (df z)

/--
%%handwave
name:
  Antiholomorphic weak Wirtinger field
statement:
  For a weak differential field $Df$, the antiholomorphic Wirtinger field is
  $z\mapsto\partial_{\bar z}f(z)$.
-/
def weakDBarField (df : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) : ℂ :=
  weakDBar (df z)

/--
%%handwave
name:
  Integrability of the holomorphic Wirtinger field
statement:
  Let $Df$ be a measurable planar differential field. If
  $Df\in L^p(\mu)$, then its holomorphic Wirtinger component
  $\partial_z f$ also belongs to $L^p(\mu)$.
proof:
  The holomorphic Wirtinger component depends continuously on the
  differential and satisfies
  $|\partial_zf|\leq\lVert Df\rVert_{\mathrm{op}}$ pointwise.
-/
theorem MemLp.weakDZField
    {μ : Measure ℂ} {p : ENNReal} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : MemLp df p μ) :
    MemLp (weakDZField df) p μ := by
  apply MemLp.of_le_mul hdf
    (continuous_weakDZ.comp_aestronglyMeasurable
      hdf.aestronglyMeasurable)
  filter_upwards with z
  rw [one_mul, norm_eq_norm_weakDZ_add_norm_weakDBar]
  exact le_add_of_nonneg_right (norm_nonneg _)

/--
%%handwave
name:
  Integrability of the antiholomorphic Wirtinger field
statement:
  Let $Df$ be a measurable planar differential field. If
  $Df\in L^p(\mu)$, then its antiholomorphic Wirtinger component
  $\partial_{\bar z}f$ also belongs to $L^p(\mu)$.
proof:
  The antiholomorphic Wirtinger component depends continuously on the
  differential and satisfies
  $|\partial_{\bar z}f|\leq\lVert Df\rVert_{\mathrm{op}}$ pointwise.
-/
theorem MemLp.weakDBarField
    {μ : Measure ℂ} {p : ENNReal} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : MemLp df p μ) :
    MemLp (weakDBarField df) p μ := by
  apply MemLp.of_le_mul hdf
    (continuous_weakDBar.comp_aestronglyMeasurable
      hdf.aestronglyMeasurable)
  filter_upwards with z
  rw [one_mul, norm_eq_norm_weakDZ_add_norm_weakDBar]
  exact le_add_of_nonneg_left (norm_nonneg _)

/--
%%handwave
name:
  Holomorphic cutoff error
statement:
  For a real-valued cutoff $\chi$ and a complex-valued map $f$, the
  contribution of $D\chi\otimes f$ to the holomorphic Wirtinger derivative
  of $\chi f$ is
  $$
    A_{\chi,f}(z)=\partial_z\bigl(D\chi(z)\otimes f(z)\bigr).
  $$
-/
noncomputable def complexWeakSobolevCutoffDZError
    (χ : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  weakDZ ((fderiv ℝ χ z).smulRight (f z))

/--
%%handwave
name:
  Antiholomorphic cutoff error
statement:
  For a real-valued cutoff $\chi$ and a complex-valued map $f$, the
  contribution of $D\chi\otimes f$ to the antiholomorphic Wirtinger
  derivative of $\chi f$ is
  $$
    B_{\chi,f}(z)=
      \partial_{\bar z}\bigl(D\chi(z)\otimes f(z)\bigr).
  $$
-/
noncomputable def complexWeakSobolevCutoffDBarError
    (χ : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  weakDBar ((fderiv ℝ χ z).smulRight (f z))

/--
%%handwave
name:
  Inhomogeneous error of cutoff localization in the Beltrami equation
statement:
  For a coefficient $\mu$, a real-valued cutoff $\chi$, and a
  complex-valued map $f$, define
  $$
    G_{\chi,f,\mu}
      =B_{\chi,f}-\mu A_{\chi,f},
  $$
  where $A_{\chi,f}$ and $B_{\chi,f}$ are respectively the holomorphic and
  antiholomorphic Wirtinger components of $D\chi\otimes f$.
-/
noncomputable def complexWeakSobolevCutoffBeltramiError
    (χ : ℂ → ℝ) (f μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  complexWeakSobolevCutoffDBarError χ f z -
    μ z * complexWeakSobolevCutoffDZError χ f z

/--
%%handwave
name:
  Holomorphic derivative of a cutoff product
statement:
  If $Df$ is a differential field, then the holomorphic Wirtinger component
  of the product-rule differential of $\chi f$ is
  $$
    \partial_z(\chi f)
      =\chi\,\partial_z f+A_{\chi,f}.
  $$
proof:
  The holomorphic Wirtinger component is real-linear in the differential.
  Apply it to $\chi Df+D\chi\otimes f$.
-/
theorem weakDZField_complexWeakSobolevCutoffDerivative
    (χ : ℂ → ℝ) (f : ℂ → ℂ) (df : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) :
    weakDZField (complexWeakSobolevCutoffDerivative χ f df) z =
      χ z • weakDZField df z + complexWeakSobolevCutoffDZError χ f z := by
  simp [weakDZField, complexWeakSobolevCutoffDerivative,
    complexWeakSobolevCutoffDZError, weakDZ]
  ring

/--
%%handwave
name:
  Antiholomorphic derivative of a cutoff product
statement:
  If $Df$ is a differential field, then the antiholomorphic Wirtinger
  component of the product-rule differential of $\chi f$ is
  $$
    \partial_{\bar z}(\chi f)
      =\chi\,\partial_{\bar z} f+B_{\chi,f}.
  $$
proof:
  The antiholomorphic Wirtinger component is real-linear in the differential.
  Apply it to $\chi Df+D\chi\otimes f$.
-/
theorem weakDBarField_complexWeakSobolevCutoffDerivative
    (χ : ℂ → ℝ) (f : ℂ → ℂ) (df : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) :
    weakDBarField (complexWeakSobolevCutoffDerivative χ f df) z =
      χ z • weakDBarField df z +
        complexWeakSobolevCutoffDBarError χ f z := by
  simp [weakDBarField, complexWeakSobolevCutoffDerivative,
    complexWeakSobolevCutoffDBarError, weakDBar]
  ring

/--
%%handwave
name:
  Localized inhomogeneous Beltrami equation
statement:
  Suppose at a point $z$ that
  $\partial_{\bar z}f(z)=\mu(z)\partial_zf(z)$. Then the product-rule
  differential of $\chi f$ satisfies
  $$
    \partial_{\bar z}(\chi f)(z)
      =\mu(z)\partial_z(\chi f)(z)
        +B_{\chi,f}(z)-\mu(z)A_{\chi,f}(z).
  $$
proof:
  Expand both Wirtinger derivatives of the cutoff product, substitute the
  Beltrami equation for $f$, and collect the two cutoff-error terms.
-/
theorem weakDBarField_complexWeakSobolevCutoffDerivative_eq
    (χ : ℂ → ℝ) (f : ℂ → ℂ) (df : ℂ → ℂ →L[ℝ] ℂ)
    (μ : ℂ → ℂ) (z : ℂ)
    (heq : weakDBarField df z = μ z * weakDZField df z) :
    weakDBarField (complexWeakSobolevCutoffDerivative χ f df) z =
      μ z * weakDZField (complexWeakSobolevCutoffDerivative χ f df) z +
        complexWeakSobolevCutoffBeltramiError χ f μ z := by
  rw [weakDBarField_complexWeakSobolevCutoffDerivative,
    weakDZField_complexWeakSobolevCutoffDerivative, heq]
  simp only [Complex.real_smul, complexWeakSobolevCutoffBeltramiError]
  ring

/--
%%handwave
name:
  Weak Beltrami equation on a planar domain
statement:
  A weak differential field $Df$ solves the Beltrami equation with coefficient
  $\mu$ on $\Omega$ if
  $$\partial_{\bar z}f=\mu\,\partial_z f$$
  almost everywhere in $\Omega$.
-/
def WeakBeltramiEquationOn (Ω : Set ℂ) (μ : ℂ → ℂ)
    (df : ℂ → ℂ →L[ℝ] ℂ) : Prop :=
  ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
    weakDBarField df z = μ z * weakDZField df z

/--
%%handwave
name:
  Restriction of a weak Beltrami equation
statement:
  If $D f$ satisfies
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere on $\Omega$ and
  $U\subseteq\Omega$, then the same equation holds almost everywhere on $U$.
proof:
  Lebesgue measure restricted to $U$ is dominated by Lebesgue measure
  restricted to $\Omega$.
-/
theorem WeakBeltramiEquationOn.mono
    {Ω U : Set ℂ} {μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : WeakBeltramiEquationOn Ω μ df) (hUΩ : U ⊆ Ω) :
    WeakBeltramiEquationOn U μ df := by
  exact ae_mono (Measure.restrict_mono hUΩ le_rfl) h

/--
%%handwave
name:
  Almost-everywhere invariance of a weak Beltrami equation in the differential
statement:
  Suppose $D f=D'f$ almost everywhere on $\Omega$. Then $D f$ satisfies
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere on $\Omega$ if and
  only if $D'f$ does.
proof:
  At every point where the two real-linear maps agree, both of their
  Wirtinger components agree.
-/
theorem WeakBeltramiEquationOn.congr_derivative_ae
    {Ω : Set ℂ} {μ : ℂ → ℂ} {df dg : ℂ → ℂ →L[ℝ] ℂ}
    (h : WeakBeltramiEquationOn Ω μ df)
    (hdf : df =ᵐ[MeasureTheory.volume.restrict Ω] dg) :
    WeakBeltramiEquationOn Ω μ dg := by
  filter_upwards [h, hdf] with z hz hdfz
  simpa [weakDBarField, weakDZField, hdfz] using hz

/--
%%handwave
name:
  Almost-everywhere invariance of a weak Beltrami equation in the coefficient
statement:
  Suppose $\mu=\nu$ almost everywhere on $\Omega$. Then a weak differential
  $D f$ satisfies $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere on
  $\Omega$ if and only if it satisfies
  $\partial_{\bar z}f=\nu\,\partial_zf$ there.
proof:
  Substitute the almost-everywhere equality of the two coefficients in the
  right-hand side of the equation.
-/
theorem WeakBeltramiEquationOn.congr_coefficient_ae
    {Ω : Set ℂ} {μ ν : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : WeakBeltramiEquationOn Ω μ df)
    (hμ : μ =ᵐ[MeasureTheory.volume.restrict Ω] ν) :
    WeakBeltramiEquationOn Ω ν df := by
  filter_upwards [h, hμ] with z hz hμz
  simpa [hμz] using hz

/--
%%handwave
name:
  Essential coefficient bound on a planar domain
statement:
  A complex coefficient $\mu$ has essential norm at most $k$ on $\Omega$ if
  $|\mu(z)|\leq k$ for almost every $z\in\Omega$.
-/
def HasEssentialNormLEOn (Ω : Set ℂ) (μ : ℂ → ℂ) (k : ℝ) : Prop :=
  ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, ‖μ z‖ ≤ k

/--
%%handwave
name:
  Beltrami coefficient of a weak differential
statement:
  The Beltrami coefficient associated with a weak differential field $Df$ is
  $$
    \mu(z)=
      \begin{cases}
        0,&\partial_zf(z)=0,\\
        \partial_{\bar z}f(z)/\partial_zf(z),
          &\partial_zf(z)\ne0.
      \end{cases}
  $$
-/
def beltramiCoefficient (df : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) : ℂ :=
  if weakDZField df z = 0 then 0 else weakDBarField df z / weakDZField df z

/--
%%handwave
name:
  Distortion gives the Beltrami equation pointwise
statement:
  Let $L:\mathbb C\to_{\mathbb R}\mathbb C$, let $K\ge1$, and suppose
  $\|L\|_{\mathrm{op}}^2\le K\det_{\mathbb R}L$. If
  $\mu_L=0$ when $L_z=0$ and $\mu_L=L_{\bar z}/L_z$ otherwise, then
  $$
    L_{\bar z}=\mu_L L_z.
  $$
proof:
  The distortion inequality is equivalent to
  $|L_{\bar z}|\le (K-1)(K+1)^{-1}|L_z|$. Thus $L_z=0$ also forces
  $L_{\bar z}=0$; away from that case the formula follows by cancellation.
-/
theorem weakDBar_eq_beltramiCoefficient_mul_weakDZ_of_distortion
    (L : ℂ →L[ℝ] ℂ) {K : ℝ} (hK : 1 ≤ K)
    (hdist : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    weakDBar L =
      (if weakDZ L = 0 then 0 else weakDBar L / weakDZ L) *
        weakDZ L := by
  have hratio :
      ‖weakDBar L‖ ≤
        ((K - 1) / (K + 1)) * ‖weakDZ L‖ :=
    (norm_weakDBar_le_ratio_iff_norm_sq_le_mul_weakJacobian
      L hK).2 hdist
  by_cases hz : weakDZ L = 0
  · have hb : weakDBar L = 0 := by
      apply norm_eq_zero.mp
      rw [hz, norm_zero, mul_zero] at hratio
      exact le_antisymm hratio (norm_nonneg _)
    simp [hz, hb]
  · simp [hz]

/--
%%handwave
name:
  Distortion bounds the Beltrami coefficient pointwise
statement:
  Under the hypotheses
  $K\ge1$ and $\|L\|_{\mathrm{op}}^2\le K\det_{\mathbb R}L$, the coefficient
  $\mu_L$ associated with $L$ satisfies
  $$
    |\mu_L|\le\frac{K-1}{K+1}.
  $$
proof:
  Use the equivalent inequality
  $|L_{\bar z}|\le (K-1)(K+1)^{-1}|L_z|$. If $L_z=0$ the coefficient is
  zero; otherwise divide by $|L_z|>0$.
-/
theorem norm_beltramiCoefficient_le_ratio_of_distortion
    (L : ℂ →L[ℝ] ℂ) {K : ℝ} (hK : 1 ≤ K)
    (hdist : ‖L‖ ^ 2 ≤ K * weakJacobian L) :
    ‖if weakDZ L = 0 then 0 else weakDBar L / weakDZ L‖ ≤
      (K - 1) / (K + 1) := by
  have hratio :
      ‖weakDBar L‖ ≤
        ((K - 1) / (K + 1)) * ‖weakDZ L‖ :=
    (norm_weakDBar_le_ratio_iff_norm_sq_le_mul_weakJacobian
      L hK).2 hdist
  by_cases hz : weakDZ L = 0
  · simp [hz]
    exact div_nonneg (sub_nonneg.mpr hK) (by linarith)
  · rw [if_neg hz, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hz)).2 hratio

/--
%%handwave
name:
  Measurability of the weak Beltrami coefficient
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then its associated Beltrami coefficient is strongly measurable up
  to a null set on $\Omega$.
proof:
  The weak differential is strongly measurable up to a null set. The two
  Wirtinger projections are continuous, while the quotient with value zero
  on the measurable zero set of $\partial_zf$ is a Borel measurable function
  of the differential.
-/
theorem IsLocalW12On.beltramiCoefficient_aestronglyMeasurable
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df) :
    AEStronglyMeasurable (beltramiCoefficient df)
      (MeasureTheory.volume.restrict Ω) := by
  have hB :
      Measurable
        (fun L : ℂ →L[ℝ] ℂ ↦
          if weakDZ L = 0 then 0
          else weakDBar L / weakDZ L) := by
    apply Measurable.ite
    · exact (measurableSet_singleton 0).preimage
        continuous_weakDZ.measurable
    · fun_prop
    · exact continuous_weakDBar.measurable.div
        continuous_weakDZ.measurable
  rw [aestronglyMeasurable_iff_aemeasurable]
  exact hB.comp_aemeasurable
    hW.differential_locallyIntegrableOn.aestronglyMeasurable.aemeasurable

/--
%%handwave
name:
  Bounded distortion as a bounded weak Beltrami equation
statement:
  Let $Df$ satisfy
  $\|Df(z)\|_{\mathrm{op}}^2\le KJ_f(z)$ almost everywhere on the plane, with
  $K\ge1$. Then its associated coefficient $\mu$ satisfies
  $$
    \partial_{\bar z}f=\mu\,\partial_zf,
    \qquad
    |\mu|\le\frac{K-1}{K+1}
  $$
  almost everywhere.
proof:
  Apply the pointwise Beltrami equation and coefficient bound at every point
  where the distortion inequality holds.
-/
theorem weakBeltramiEquationOn_beltramiCoefficient_of_boundedDistortion
    {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)) :
    WeakBeltramiEquationOn Set.univ
        (beltramiCoefficient df) df ∧
      HasEssentialNormLEOn Set.univ
        (beltramiCoefficient df) ((K - 1) / (K + 1)) := by
  constructor
  · rw [WeakBeltramiEquationOn, Measure.restrict_univ]
    filter_upwards [hdist] with z hz
    simpa [weakDBarField, weakDZField,
      beltramiCoefficient] using
        weakDBar_eq_beltramiCoefficient_mul_weakDZ_of_distortion
          (df z) hK hz
  · rw [HasEssentialNormLEOn, Measure.restrict_univ]
    filter_upwards [hdist] with z hz
    simpa [beltramiCoefficient, weakDZField,
      weakDBarField] using
        norm_beltramiCoefficient_le_ratio_of_distortion
          (df z) hK hz

/--
%%handwave
name:
  A bounded Beltrami coefficient bounds the weak Wirtinger ratio
statement:
  If $\partial_{\bar z}f=\mu\,\partial_z f$ almost everywhere on $\Omega$ and
  $|\mu|\leq k$ almost everywhere there, then
  $$|\partial_{\bar z}f|\leq k|\partial_z f|$$
  almost everywhere on $\Omega$.
proof:
  Take norms in the Beltrami equation and use the pointwise bound on $|\mu|$.
-/
theorem WeakBeltramiEquationOn.norm_weakDBar_le
    {Ω : Set ℂ} {μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {k : ℝ}
    (heq : WeakBeltramiEquationOn Ω μ df)
    (hμ : HasEssentialNormLEOn Ω μ k) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      ‖weakDBarField df z‖ ≤ k * ‖weakDZField df z‖ := by
  filter_upwards [heq, hμ] with z hz hμz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hμz (norm_nonneg _)

/--
%%handwave
name:
  Bounded Beltrami equation implies metric distortion
statement:
  If $0\leq k<1$, $\partial_{\bar z}f=\mu\,\partial_z f$ almost everywhere on
  $\Omega$,
  and $|\mu|\leq k$ almost everywhere, then
  $$\|Df\|_{\mathrm{op}}^2\leq\frac{1+k}{1-k}J_f$$
  almost everywhere on $\Omega$.
proof:
  First bound $|\partial_{\bar z}f|$ by $k|\partial_z f|$, then apply the
  pointwise real-linear distortion equivalence.
-/
theorem WeakBeltramiEquationOn.norm_sq_le_distortion_mul_weakJacobian
    {Ω : Set ℂ} {μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {k : ℝ}
    (heq : WeakBeltramiEquationOn Ω μ df)
    (hμ : HasEssentialNormLEOn Ω μ k) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      ‖df z‖ ^ 2 ≤ ((1 + k) / (1 - k)) * weakJacobian (df z) := by
  filter_upwards [heq.norm_weakDBar_le hμ] with z hz
  exact (norm_weakDBar_le_iff_norm_sq_le_distortion (df z) hk0 hk1).mp hz

/--
%%handwave
name:
  Uniqueness of the local weak differential
statement:
  If $Df$ and $D'f$ both exhibit the same complex-valued map as locally
  $W^{1,2}$ on an open planar domain $\Omega$, then $Df=D'f$ almost everywhere
  on $\Omega$.
proof:
  Subtract the two weak-derivative identities. For each of the real basis
  directions $1,i$, the difference has zero pairing with every smooth compactly
  supported test. The fundamental lemma of distributions makes both evaluated
  differences vanish almost everywhere, and real linearity finishes the proof.
-/
theorem IsLocalW12On.weakDifferential_ae_eq
    {Ω : Set ℂ} {f : ℂ → ℂ} {df dg : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω f df) (hdg : IsLocalW12On Ω f dg) :
    df =ᵐ[MeasureTheory.volume.restrict Ω] dg := by
  have hΩ : IsOpen Ω := hdf.1
  have hweak := hdf.2.1.sub hdg.2.1
  have heval_zero (v : ℂ) :
      ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, (df z - dg z) v = 0 := by
    have hloc :
        LocallyIntegrableOn (fun z : ℂ ↦ (df z - dg z) v) Ω
          MeasureTheory.volume := by
      rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
      intro K hKΩ hK
      have hfield :
          MemLp (fun z : ℂ ↦ df z - dg z) 2
            (MeasureTheory.volume.restrict K) :=
        (hdf.2.2 K hK hKΩ).2.sub (hdg.2.2 K hK hKΩ).2
      have heval := hfield.continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ ℂ v)
      haveI : IsFiniteMeasure (MeasureTheory.volume.restrict K) :=
        isFiniteMeasure_restrict.2 hK.measure_ne_top
      exact heval.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hzero :
        ∀ᵐ z ∂MeasureTheory.volume, z ∈ Ω → (df z - dg z) v = 0 := by
      refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
      intro g hg_smooth hg_compact hg_support
      let φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
        { toFun := g
          smooth := hg_smooth
          support_subset := hg_support
          compact_support := hg_compact }
      have hset :
          ∫ z in Ω, g z • (df z - dg z) v ∂MeasureTheory.volume = 0 := by
        have hidentity := (hweak φ v).2.2
        simpa [φ] using hidentity
      calc
        ∫ z, g z • (df z - dg z) v ∂MeasureTheory.volume =
            ∫ z in Ω, g z • (df z - dg z) v ∂MeasureTheory.volume := by
              symm
              exact setIntegral_eq_integral_of_forall_compl_eq_zero
                (s := Ω) (μ := MeasureTheory.volume)
                (f := fun z ↦ g z • (df z - dg z) v)
                fun z hzΩ ↦ by
                  have hz_tsupport : z ∉ tsupport g := fun hz ↦ hzΩ (hg_support hz)
                  simp [image_eq_zero_of_notMem_tsupport hz_tsupport]
        _ = 0 := hset
    exact (ae_restrict_iff' hΩ.measurableSet).2 hzero
  filter_upwards [heval_zero 1, heval_zero Complex.I] with z hz_one hz_I
  apply sub_eq_zero.mp
  ext ξ
  have hξ : ξ = ξ.re • (1 : ℂ) + ξ.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hξ, map_add, map_smul, map_smul]
  simp [hz_one, hz_I]

end

end Quasiconformal

end JJMath
