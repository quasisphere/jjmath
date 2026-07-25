import JJMath.Analysis.Harmonic.LpDuality
import JJMath.Quasiconformal.BeurlingDuality

/-!
# The Beurling transform above exponent two

This file uses bilinear symmetry and quantitative `Lᵖ` duality to transfer
the completed Beurling estimate below exponent two to the conjugate exponent
above two. The first step treats finite-support simple functions, for which
the weak-`L¹` transform is already available.
-/

namespace JJMath

open MeasureTheory
open scoped ENNReal

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Hölder bound for a complex bilinear integral
statement:
  If $p$ and $q$ are Hölder conjugate, $f\in L^p(X;\mathbb C)$, and
  $g\in L^q(X;\mathbb C)$, then
  $$
    \left|\int_X f(x)g(x)\,d\mu(x)\right|
      \leq \|f\|_p\|g\|_q.
  $$
proof:
  Bound the norm of the integral by the integral of $|f||g|$, apply
  Hölder's inequality, and identify the two real-power expressions with
  the corresponding $L^p$ seminorms.
-/
theorem norm_integral_mul_le_lpNorm_mul_lpNorm
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℂ} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤
      lpNorm f (ENNReal.ofReal p) μ *
        lpNorm g (ENNReal.ofReal q) μ := by
  calc
    ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact norm_mul (f x) (g x)
    _ ≤ lpNorm f (ENNReal.ofReal p) μ *
          lpNorm g (ENNReal.ofReal q) μ := by
      rw [lpNorm_eq_integral_norm_rpow_toReal
          (ENNReal.ofReal_ne_zero_iff.mpr hpq.pos)
          ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
        lpNorm_eq_integral_norm_rpow_toReal
          (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
          ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
        ENNReal.toReal_ofReal hpq.nonneg,
        ENNReal.toReal_ofReal hpq.symm.nonneg]
      simpa only [one_div] using integral_mul_norm_le_Lp_mul_Lq hpq hf hg

/--
%%handwave
name:
  $L^p$ norm of the simple-function inclusion into $L^1$
statement:
  Let $0<p<\infty$. If $F$ is a finite-support $L^p$ simple function and
  $F_1$ is the same function regarded as an $L^1$ class, then
  $$
    \|F_1\|_p=\|F\|_p.
  $$
proof:
  The chosen representative of $F_1$ agrees almost everywhere with the
  original simple function, so their $L^p$ seminorms agree.
-/
theorem lpNorm_simpleFuncToL1LinearMap_eq_norm
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ENNReal) [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (F : Lp.simpleFunc ℂ p μ) :
    lpNorm
        ((simpleFuncToL1LinearMap μ p hp0 hptop F : α →₁[μ] ℂ) : α → ℂ)
        p μ = ‖F‖ := by
  have hcoe :
      ((simpleFuncToL1LinearMap μ p hp0 hptop F : α →₁[μ] ℂ) : α → ℂ)
        =ᵐ[μ] Lp.simpleFunc.toSimpleFunc F :=
    (integrable_simpleFunc_toSimpleFunc hp0 hptop F).coeFn_toL1
  calc
    lpNorm
        ((simpleFuncToL1LinearMap μ p hp0 hptop F : α →₁[μ] ℂ) : α → ℂ)
        p μ =
        (eLpNorm
          ((simpleFuncToL1LinearMap μ p hp0 hptop F : α →₁[μ] ℂ) : α → ℂ)
          p μ).toReal :=
      (toReal_eLpNorm
        (memLp_simpleFuncToL1LinearMap μ p hp0 hptop F).aestronglyMeasurable).symm
    _ = (eLpNorm (Lp.simpleFunc.toSimpleFunc F : α → ℂ) p μ).toReal :=
      congrArg ENNReal.toReal (eLpNorm_congr_ae hcoe)
    _ = ‖F‖ := (Lp.simpleFunc.norm_toSimpleFunc F).symm

/--
%%handwave
name:
  Norm of a simple function in its $L^p$ class
statement:
  If a simple function $s$ belongs to $L^p(X;\mathbb C)$, then its
  $L^p$ seminorm equals the norm of the corresponding finite-support
  simple-function class:
  $$
    \|[s]\|_p=\|s\|_p.
  $$
proof:
  The canonical representative of the $L^p$ simple-function class agrees
  almost everywhere with $s$.
-/
theorem norm_simpleFunc_toLp_eq_lpNorm
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p : ENNReal) [Fact (1 ≤ p)] (s : SimpleFunc α ℂ)
    (hs : MemLp (s : α → ℂ) p μ) :
    ‖(s.toLp hs : Lp ℂ p μ)‖ = lpNorm (s : α → ℂ) p μ := by
  rw [Lp.simpleFunc.toLp_eq_toLp, Lp.norm_toLp,
    toReal_eLpNorm hs.aestronglyMeasurable]

/--
%%handwave
name:
  Strong conjugate-exponent estimate for simple inputs
statement:
  Let $p$ and $q$ be Hölder conjugate, with $1<p<2\leq q$. For every
  finite-support simple $F\in L^q(\mathbb C)$, regard $F$ as an $L^1$
  class $F_1$. Then its weak Beurling transform belongs to $L^q$ and
  satisfies
  $$
    \|\mathcal S F_1\|_q\leq A_p\|F\|_q,
  $$
  where $A_p$ is the previously obtained strong $L^p$ bound.
proof:
  Test $\mathcal S F_1$ against an arbitrary finite-support simple
  $s\in L^p$. Bilinear symmetry moves the transform from $F_1$ to $s$.
  On simple inputs the latter weak transform agrees with the completed
  $L^p$ transform, so Hölder's inequality and the strong $L^p$ estimate
  bound the pairing by $A_p\|F\|_q\|s\|_p$. Quantitative $L^p$ duality
  gives the asserted membership and norm bound.
-/
theorem memLp_and_lpNorm_beurlingTransformL1_simpleFunc_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    MemLp
        (beurlingTransformL1
          (simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
            (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
            ENNReal.ofReal_ne_top F) : ℂ → ℂ)
        (ENNReal.ofReal q) volume ∧
      lpNorm
          (beurlingTransformL1
            (simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
              (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
              ENNReal.ofReal_ne_top F) : ℂ → ℂ)
          (ENNReal.ofReal q) volume ≤
        (beurlingInterpolationNorm p).toReal * ‖F‖ := by
  let hp0 : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hpq.pos
  let hq0 : ENNReal.ofReal q ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
      hq0 ENNReal.ofReal_ne_top F
  have hFq : MemLp (F₁ : ℂ → ℂ) (ENNReal.ofReal q) volume :=
    memLp_simpleFuncToL1LinearMap (volume : Measure ℂ)
      (ENNReal.ofReal q) hq0 ENNReal.ofReal_ne_top F
  have hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
    memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
      (ENNReal.ofReal q) hq0 ENNReal.ofReal_ne_top F
  apply HarmonicAnalysis.memLp_and_lpNorm_le_of_simpleFunc_pairing
    hpq hq2 (beurlingTransformL1 F₁).stronglyMeasurable
    (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg F))
  intro s hs
  let sLp : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    s.toLp hs
  let s₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal p)
      hp0 ENNReal.ofReal_ne_top sLp
  have hs₂ : MemLp (s₁ : ℂ → ℂ) 2 volume :=
    memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
      (ENNReal.ofReal p) hp0 ENNReal.ofReal_ne_top sLp
  have hs₁_ae : (s₁ : ℂ → ℂ) =ᵐ[volume] (s : ℂ → ℂ) :=
    (integrable_simpleFunc_toSimpleFunc hp0 ENNReal.ofReal_ne_top sLp).coeFn_toL1.trans
      (show Lp.simpleFunc.toSimpleFunc sLp =ᵐ[volume] (s : ℂ → ℂ) by
        dsimp only [sLp]
        exact Lp.simpleFunc.toSimpleFunc_toLp s hs)
  have hTs_ae :
      (beurlingTransformL1 s₁ : ℂ → ℂ) =ᵐ[volume]
        (beurlingTransformLp p hpq.lt hp2
          (sLp : Lp ℂ (ENNReal.ofReal p) volume) : ℂ → ℂ) := by
    have hsimple :=
      (beurlingTransformLpSimpleFunc_coeFn p hpq.lt hp2 sLp).symm
    have hcompleted :
        (beurlingTransformLp p hpq.lt hp2
            (sLp : Lp ℂ (ENNReal.ofReal p) volume) : ℂ → ℂ) =ᵐ[volume]
          (beurlingTransformLpSimpleFunc p hpq.lt hp2 sLp : ℂ → ℂ) := by
      rw [beurlingTransformLp_apply_simpleFunc]
    exact hsimple.trans hcompleted.symm
  have hsymm :=
    integral_beurlingTransformL1_mul_eq_integral_mul_beurlingTransformL1
      F₁ s₁ hF₂ hs₂
  have hTs_norm :
      ‖beurlingTransformLp p hpq.lt hp2
          (sLp : Lp ℂ (ENNReal.ofReal p) volume)‖ ≤
        (beurlingInterpolationNorm p).toReal *
        ‖(sLp : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ))‖ := by
    apply norm_beurlingTransformLp_le
  have hsLp_norm :
      ‖(sLp : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ))‖ =
        lpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume := by
    dsimp only [sLp]
    exact norm_simpleFunc_toLp_eq_lpNorm (ENNReal.ofReal p) s hs
  calc
    ‖∫ z, (beurlingTransformL1 F₁ : ℂ → ℂ) z * s z‖ =
        ‖∫ z, (beurlingTransformL1 F₁ : ℂ → ℂ) z * s₁ z‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hs₁_ae] with z hz
      rw [hz]
    _ = ‖∫ z, F₁ z * (beurlingTransformL1 s₁ : ℂ → ℂ) z‖ :=
      congrArg norm hsymm
    _ = ‖∫ z, F₁ z *
        (beurlingTransformLp p hpq.lt hp2
          (sLp : Lp ℂ (ENNReal.ofReal p) volume)) z‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hTs_ae] with z hz
      rw [hz]
    _ ≤ lpNorm (F₁ : ℂ → ℂ) (ENNReal.ofReal q) volume *
          lpNorm
            (beurlingTransformLp p hpq.lt hp2
              (sLp : Lp ℂ (ENNReal.ofReal p) volume) : ℂ → ℂ)
            (ENNReal.ofReal p) volume :=
      norm_integral_mul_le_lpNorm_mul_lpNorm hpq.symm hFq
        (Lp.memLp (beurlingTransformLp p hpq.lt hp2
          (sLp : Lp ℂ (ENNReal.ofReal p) volume)))
    _ = ‖F‖ * ‖beurlingTransformLp p hpq.lt hp2
          (sLp : Lp ℂ (ENNReal.ofReal p) volume)‖ := by
      rw [lpNorm_simpleFuncToL1LinearMap_eq_norm
          (volume : Measure ℂ) (ENNReal.ofReal q) hq0
          ENNReal.ofReal_ne_top F,
        ← toReal_eLpNorm
          (Lp.memLp (beurlingTransformLp p hpq.lt hp2
            (sLp : Lp ℂ (ENNReal.ofReal p) volume))).aestronglyMeasurable,
        ← Lp.norm_def]
    _ ≤ ‖F‖ * ((beurlingInterpolationNorm p).toReal *
          ‖(sLp : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ))‖) := by
      exact mul_le_mul_of_nonneg_left hTs_norm (norm_nonneg F)
    _ = ((beurlingInterpolationNorm p).toReal * ‖F‖) *
          lpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume := by
      rw [hsLp_norm]
      ring

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module
  Lp.simpleFunc.normedSpace Lp.simpleFunc.isBoundedSMul

/--
%%handwave
name:
  Beurling transform of a simple function above exponent two
statement:
  Let $p$ and $q$ be Hölder conjugate with $1<p<2\leq q$. Regard a
  finite-support simple $F\in L^q(\mathbb C)$ as an $L^1$ function, apply
  the weak Beurling transform, and take the resulting $L^q$ class.
-/
def beurlingTransformLpAboveSimpleFunc
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ) :=
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
      (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
      ENNReal.ofReal_ne_top F
  (memLp_and_lpNorm_beurlingTransformL1_simpleFunc_le
      p q hpq hp2 hq2 F).1.toLp
    (beurlingTransformL1 F₁ : ℂ → ℂ)

/--
%%handwave
name:
  Representative of the above-two simple-function transform
statement:
  Under the conjugate-exponent hypotheses, the function representative of
  the $L^q$ Beurling transform of a finite-support simple function $F$
  agrees almost everywhere with the weak transform of the same function
  regarded as an $L^1$ class.
proof:
  This is the representative used to define the resulting $L^q$ class.
-/
theorem beurlingTransformLpAboveSimpleFunc_coeFn
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    (beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F : ℂ → ℂ)
      =ᵐ[volume]
        (beurlingTransformL1
          (simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
            (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
            ENNReal.ofReal_ne_top F) : ℂ → ℂ) := by
  dsimp only [beurlingTransformLpAboveSimpleFunc]
  exact MemLp.coeFn_toLp _

/--
%%handwave
name:
  Additivity of the above-two simple-function transform
statement:
  Under the conjugate-exponent hypotheses, finite-support simple functions
  $F,G\in L^q(\mathbb C)$ satisfy
  $$
    \mathcal S_q(F+G)=\mathcal S_qF+\mathcal S_qG.
  $$
proof:
  The inclusion into $L^1$ and the weak Beurling transform are additive,
  and the corresponding representatives determine the same $L^q$ class.
-/
theorem beurlingTransformLpAboveSimpleFunc_add
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (F G : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 (F + G) =
      beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F +
        beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 G := by
  let hq0 : ENNReal.ofReal q ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos
  let ι := simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
    hq0 ENNReal.ofReal_ne_top
  have hT :
      (beurlingTransformL1 (ι (F + G)) : ℂ → ℂ) =ᵐ[volume]
        (beurlingTransformL1 (ι F) : ℂ → ℂ) +
          (beurlingTransformL1 (ι G) : ℂ → ℂ) := by
    rw [map_add, beurlingTransformL1_add]
    exact AEEqFun.coeFn_add _ _
  apply Lp.ext
  filter_upwards [
    beurlingTransformLpAboveSimpleFunc_coeFn p q hpq hp2 hq2 (F + G),
    beurlingTransformLpAboveSimpleFunc_coeFn p q hpq hp2 hq2 F,
    beurlingTransformLpAboveSimpleFunc_coeFn p q hpq hp2 hq2 G,
    Lp.coeFn_add (beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F)
      (beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 G), hT]
      with z hsum hF hG hadd hTz
  exact hsum.trans (hTz.trans (hadd ▸ congrArg₂ (· + ·) hF.symm hG.symm))

/--
%%handwave
name:
  Complex homogeneity of the above-two simple-function transform
statement:
  Under the conjugate-exponent hypotheses, $c\in\mathbb C$ and every
  finite-support simple $F\in L^q(\mathbb C)$ satisfy
  $$
    \mathcal S_q(cF)=c\,\mathcal S_qF.
  $$
proof:
  The inclusion into $L^1$ and the weak Beurling transform are complex
  homogeneous, and their representatives agree almost everywhere with the
  asserted $L^q$ classes.
-/
theorem beurlingTransformLpAboveSimpleFunc_smul
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (c : ℂ)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 (c • F) =
      c • beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F := by
  let hq0 : ENNReal.ofReal q ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos
  let ι := simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
    hq0 ENNReal.ofReal_ne_top
  have hT :
      (beurlingTransformL1 (ι (c • F)) : ℂ → ℂ) =ᵐ[volume]
        c • (beurlingTransformL1 (ι F) : ℂ → ℂ) := by
    rw [map_smul, beurlingTransformL1_smul]
    exact AEEqFun.coeFn_smul _ _
  apply Lp.ext
  filter_upwards [
    beurlingTransformLpAboveSimpleFunc_coeFn p q hpq hp2 hq2 (c • F),
    beurlingTransformLpAboveSimpleFunc_coeFn p q hpq hp2 hq2 F,
    Lp.coeFn_smul c (beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F),
    hT] with z hscaled hF hsmul hTz
  rw [hscaled, hTz, Pi.smul_apply, hsmul, Pi.smul_apply, hF]

/--
%%handwave
name:
  Linear Beurling transform on simple functions above two
statement:
  If $p$ and $q$ are Hölder conjugate with $1<p<2\leq q$, then the
  Beurling transform defines a complex-linear map
  $$
    \mathcal S_q:L^q_{\mathrm{simple}}(\mathbb C)
      \longrightarrow L^q(\mathbb C).
  $$
-/
def beurlingTransformLpAboveSimpleFuncLinearMap
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q) :
    Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ) where
  toFun := beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2
  map_add' := beurlingTransformLpAboveSimpleFunc_add p q hpq hp2 hq2
  map_smul' := beurlingTransformLpAboveSimpleFunc_smul p q hpq hp2 hq2

/--
%%handwave
name:
  Norm bound on simple functions above two
statement:
  If $p$ and $q$ are Hölder conjugate with $1<p<2\leq q$, then every
  finite-support simple $F\in L^q(\mathbb C)$ satisfies
  $$
    \|\mathcal S_qF\|_q\leq A_p\|F\|_q.
  $$
proof:
  The chosen representative is the weak transform of the corresponding
  $L^1$ class, and its quantitative $L^q$ bound is the conclusion of the
  simple-input duality argument.
-/
theorem norm_beurlingTransformLpAboveSimpleFunc_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    ‖beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F‖ ≤
      (beurlingInterpolationNorm p).toReal * ‖F‖ := by
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
      (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
      ENNReal.ofReal_ne_top F
  have hmem :=
    (memLp_and_lpNorm_beurlingTransformL1_simpleFunc_le
      p q hpq hp2 hq2 F).1
  calc
    ‖beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F‖ =
        lpNorm (beurlingTransformL1 F₁ : ℂ → ℂ)
          (ENNReal.ofReal q) volume := by
      rw [show beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F =
          hmem.toLp (beurlingTransformL1 F₁ : ℂ → ℂ) from rfl,
        Lp.norm_toLp, toReal_eLpNorm hmem.aestronglyMeasurable]
    _ ≤ (beurlingInterpolationNorm p).toReal * ‖F‖ :=
      (memLp_and_lpNorm_beurlingTransformL1_simpleFunc_le
        p q hpq hp2 hq2 F).2

/--
%%handwave
name:
  Strong Beurling transform above exponent two
statement:
  If $p$ and $q$ are Hölder conjugate with $1<p<2\leq q$, the bounded
  transform on finite-support $L^q$ simple functions extends uniquely to a
  continuous complex-linear map
  $$
    \mathcal S_q:L^q(\mathbb C)\longrightarrow L^q(\mathbb C).
  $$
-/
def beurlingTransformLpAbove
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q) :
    Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ) := by
  let T := beurlingTransformLpAboveSimpleFuncLinearMap
    p q hpq hp2 hq2
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  exact T.extendOfNorm e

/--
%%handwave
name:
  Agreement of the above-two completed transform on simple functions
statement:
  Under the conjugate-exponent hypotheses, the completed $L^q$ Beurling
  transform evaluated on a finite-support simple function equals its
  previously constructed simple-function transform.
proof:
  Extension of a bounded linear map agrees with that map on its dense
  simple-function domain.
-/
theorem beurlingTransformLpAbove_apply_simpleFunc
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    beurlingTransformLpAbove p q hpq hp2 hq2
        (F : Lp ℂ (ENNReal.ofReal q) volume) =
      beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F := by
  let T := beurlingTransformLpAboveSimpleFuncLinearMap
    p q hpq hp2 hq2
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  change T.extendOfNorm e (e F) = T F
  exact LinearMap.extendOfNorm_eq
    (Lp.simpleFunc.denseRange ENNReal.ofReal_ne_top)
    ⟨(beurlingInterpolationNorm p).toReal,
      norm_beurlingTransformLpAboveSimpleFunc_le p q hpq hp2 hq2⟩ F

/--
%%handwave
name:
  Strong norm bound above exponent two
statement:
  If $p$ and $q$ are Hölder conjugate with $1<p<2\leq q$, then every
  $F\in L^q(\mathbb C)$ satisfies
  $$
    \|\mathcal S_qF\|_q\leq A_p\|F\|_q.
  $$
proof:
  The estimate holds on the dense finite-support simple functions, and the
  bounded extension preserves the same norm bound.
-/
theorem norm_beurlingTransformLpAbove_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    ‖beurlingTransformLpAbove p q hpq hp2 hq2 F‖ ≤
      (beurlingInterpolationNorm p).toReal * ‖F‖ := by
  let T := beurlingTransformLpAboveSimpleFuncLinearMap
    p q hpq hp2 hq2
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  change ‖T.extendOfNorm e F‖ ≤ (beurlingInterpolationNorm p).toReal * ‖F‖
  exact LinearMap.norm_extendOfNorm_apply_le
    (Lp.simpleFunc.denseRange ENNReal.ofReal_ne_top)
    (beurlingInterpolationNorm p).toReal
    (norm_beurlingTransformLpAboveSimpleFunc_le p q hpq hp2 hq2) F

/--
%%handwave
name:
  Weak and Fourier Beurling transforms agree on finite-support simple data
statement:
  Let $0<r<\infty$, let $F$ be a finite-support $L^r$ simple function, and
  let $F_1$ be the same function regarded as an $L^1$ class. Then
  $$
    \mathcal S_1F_1=\mathcal S_2F_1
    \quad\text{almost everywhere},
  $$
  where the right side is the Fourier-multiplier transform of the
  $L^2$ class represented by $F_1$.
proof:
  The representative of $F_1$ is integrable and square-integrable. Apply
  compatibility of the weak transform with the Fourier-multiplier transform,
  and identify the $L^1$ class reconstructed from its representative with
  $F_1$ itself.
-/
theorem beurlingTransformL1_simpleFuncToL1LinearMap_ae_eq_beurlingTransformL2
    {r : ENNReal} (hr0 : r ≠ 0) (hrtop : r ≠ ∞)
    (F : Lp.simpleFunc ℂ r (volume : Measure ℂ)) :
    let F₁ : ℂ →₁[volume] ℂ :=
      simpleFuncToL1LinearMap (volume : Measure ℂ) r hr0 hrtop F
    let hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
      memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
        r hr0 hrtop F
    (beurlingTransformL1 F₁ : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL2 (hF₂.toLp (F₁ : ℂ → ℂ)) : ℂ → ℂ) := by
  dsimp only
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) r hr0 hrtop F
  let hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
    memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
      r hr0 hrtop F
  let hF₁ : MemLp (F₁ : ℂ → ℂ) 1 volume :=
    memLp_one_iff_integrable.mpr (L1.integrable_coeFn F₁)
  have hFclass : hF₁.toLp (F₁ : ℂ → ℂ) = F₁ :=
    Lp.toLp_coeFn F₁ hF₁
  have h := beurlingTransformL1_ae_eq_beurlingTransformL2
    (F₁ : ℂ → ℂ) (L1.integrable_coeFn F₁) hF₂
  dsimp only at h
  rw [hFclass] at h
  exact h

/--
%%handwave
name:
  Above-two completion agrees with the Fourier transform on simple data
statement:
  If $p$ and $q$ are Hölder conjugate with $1<p<2\leq q$, and $F$ is a
  finite-support planar $L^q$ simple function, then the completed $L^q$
  Beurling transform of $F$ agrees almost everywhere with the exact
  Fourier-multiplier $L^2$ transform of the same function.
proof:
  The completed $L^q$ operator agrees with its simple-function construction,
  whose representative is the weak transform. Apply compatibility of the
  weak and Fourier transforms on finite-support simple data.
-/
theorem beurlingTransformLpAbove_apply_simpleFunc_ae_eq_beurlingTransformL2
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) :
    let F₁ : ℂ →₁[volume] ℂ :=
      simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
        (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
        ENNReal.ofReal_ne_top F
    let hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
      memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
        (ENNReal.ofReal q) (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
        ENNReal.ofReal_ne_top F
    (beurlingTransformLpAbove p q hpq hp2 hq2
        (F : Lp ℂ (ENNReal.ofReal q) volume) : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL2 (hF₂.toLp (F₁ : ℂ → ℂ)) : ℂ → ℂ) := by
  dsimp only
  let hq0 : ENNReal.ofReal q ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
      hq0 ENNReal.ofReal_ne_top F
  let hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
    memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
      (ENNReal.ofReal q) hq0 ENNReal.ofReal_ne_top F
  have hcompleted :
      (beurlingTransformLpAbove p q hpq hp2 hq2
          (F : Lp ℂ (ENNReal.ofReal q) volume) : ℂ → ℂ) =ᵐ[volume]
        (beurlingTransformLpAboveSimpleFunc p q hpq hp2 hq2 F : ℂ → ℂ) := by
    rw [beurlingTransformLpAbove_apply_simpleFunc]
  exact hcompleted.trans <|
    (beurlingTransformLpAboveSimpleFunc_coeFn p q hpq hp2 hq2 F).trans <|
      beurlingTransformL1_simpleFuncToL1LinearMap_ae_eq_beurlingTransformL2
        hq0 ENNReal.ofReal_ne_top F

end

end Quasiconformal

end JJMath
