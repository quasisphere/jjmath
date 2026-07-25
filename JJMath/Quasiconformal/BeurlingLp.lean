import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import JJMath.Quasiconformal.BeurlingInterpolation

/-!
# The Beurling transform on `Lᵖ`

This file completes the strong estimate below exponent two from integrable
inputs to the full planar `Lᵖ` space. The dense domain is the space of
finite-support `Lᵖ` simple functions.
-/

namespace JJMath

open MeasureTheory
open scoped ENNReal

namespace Quasiconformal

noncomputable section

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module
  Lp.simpleFunc.normedSpace Lp.simpleFunc.isBoundedSMul

/--
%%handwave
name:
  An $L^p$ simple function is integrable
statement:
  Let $0<p<\infty$. If a simple function represents an element of
  $L^p(X;E)$, then it is integrable.
proof:
  Membership in a finite positive $L^p$ space forces every nonzero level set
  of the simple function to have finite measure. This condition is also
  equivalent to integrability of a simple function.
-/
theorem integrable_simpleFunc_toSimpleFunc
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {q : ENNReal} (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (F : Lp.simpleFunc E q μ) :
    Integrable (Lp.simpleFunc.toSimpleFunc F) μ := by
  exact (SimpleFunc.memLp_iff_integrable hq0 hqtop).mp
    (Lp.simpleFunc.memLp F)

/--
%%handwave
name:
  Dense simple-function inclusion into $L^1$
statement:
  For $0<p<\infty$, sending an $L^p$ simple function to the same
  almost-everywhere class in $L^1$ defines a complex-linear map
  $$
    L^p_{\mathrm{simple}}(X;\mathbb C)\longrightarrow L^1(X;\mathbb C).
  $$
-/
def simpleFuncToL1LinearMap
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q : ENNReal) (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    Lp.simpleFunc ℂ q μ →ₗ[ℂ] (α →₁[μ] ℂ) where
  toFun F :=
    (integrable_simpleFunc_toSimpleFunc hq0 hqtop F).toL1
      (Lp.simpleFunc.toSimpleFunc F)
  map_add' F G := by
    apply Lp.ext
    filter_upwards [
      (integrable_simpleFunc_toSimpleFunc hq0 hqtop (F + G)).coeFn_toL1,
      (integrable_simpleFunc_toSimpleFunc hq0 hqtop F).coeFn_toL1,
      (integrable_simpleFunc_toSimpleFunc hq0 hqtop G).coeFn_toL1,
      Lp.coeFn_add
        ((integrable_simpleFunc_toSimpleFunc hq0 hqtop F).toL1
          (Lp.simpleFunc.toSimpleFunc F))
        ((integrable_simpleFunc_toSimpleFunc hq0 hqtop G).toL1
          (Lp.simpleFunc.toSimpleFunc G)),
      Lp.simpleFunc.add_toSimpleFunc F G] with z hsum hF hG hadd hsimple
    rw [hsum, hsimple, hadd]
    change (Lp.simpleFunc.toSimpleFunc F) z +
        (Lp.simpleFunc.toSimpleFunc G) z =
      ((integrable_simpleFunc_toSimpleFunc hq0 hqtop F).toL1
          (Lp.simpleFunc.toSimpleFunc F) : α → ℂ) z +
        ((integrable_simpleFunc_toSimpleFunc hq0 hqtop G).toL1
          (Lp.simpleFunc.toSimpleFunc G) : α → ℂ) z
    exact congrArg₂ (· + ·) hF.symm hG.symm
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [
      (integrable_simpleFunc_toSimpleFunc hq0 hqtop (c • F)).coeFn_toL1,
      (integrable_simpleFunc_toSimpleFunc hq0 hqtop F).coeFn_toL1,
      Lp.coeFn_smul c
        ((integrable_simpleFunc_toSimpleFunc hq0 hqtop F).toL1
          (Lp.simpleFunc.toSimpleFunc F)),
      Lp.simpleFunc.smul_toSimpleFunc c F] with z hscaled hF hsmul hsimple
    rw [hscaled, hsimple]
    calc
      (c • (Lp.simpleFunc.toSimpleFunc F : α → ℂ)) z =
          c • (Lp.simpleFunc.toSimpleFunc F) z := rfl
      _ = c • ((integrable_simpleFunc_toSimpleFunc hq0 hqtop F).toL1
          (Lp.simpleFunc.toSimpleFunc F) : α → ℂ) z :=
        congrArg (c • ·) hF.symm
      _ = (c • ((integrable_simpleFunc_toSimpleFunc hq0 hqtop F).toL1
          (Lp.simpleFunc.toSimpleFunc F) : α → ℂ)) z := rfl
      _ = ((c • (integrable_simpleFunc_toSimpleFunc hq0 hqtop F).toL1
          (Lp.simpleFunc.toSimpleFunc F) : α →₁[μ] ℂ) : α → ℂ) z := hsmul.symm
      _ = (((RingHom.id ℂ) c •
          (integrable_simpleFunc_toSimpleFunc hq0 hqtop F).toL1
            (Lp.simpleFunc.toSimpleFunc F) : α →₁[μ] ℂ) : α → ℂ) z := rfl

/--
%%handwave
name:
  The simple-function inclusion preserves the $L^p$ class
statement:
  Let $0<p<\infty$. If $F$ is an $L^p$ simple function and $F_1$ is its
  image in $L^1$, then the function representative of $F_1$ still belongs
  to $L^p$.
proof:
  The $L^1$ representative agrees almost everywhere with the original
  simple function, which belongs to $L^p$ by construction.
-/
theorem memLp_simpleFuncToL1LinearMap
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q : ENNReal) (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (F : Lp.simpleFunc ℂ q μ) :
    MemLp ((simpleFuncToL1LinearMap μ q hq0 hqtop F : α →₁[μ] ℂ) : α → ℂ)
      q μ := by
  exact MemLp.ae_eq
    (integrable_simpleFunc_toSimpleFunc hq0 hqtop F).coeFn_toL1.symm
    (Lp.simpleFunc.memLp F)

/--
%%handwave
name:
  Beurling transform of a planar $L^p$ simple function
statement:
  Let $1<p<2$. Regard a planar $L^p$ simple function as an integrable
  function, apply the weak-$L^1$ Beurling transform, and use its strong
  $L^p$ membership to obtain an element of $L^p(\mathbb C)$.
-/
def beurlingTransformLpSimpleFunc
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
  let hp0 : 0 < p := lt_trans zero_lt_one hp1
  let hp_ne_zero : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  let hp_ne_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal p)
      hp_ne_zero hp_ne_top F
  let hF₁p : MemLp (F₁ : ℂ → ℂ) (ENNReal.ofReal p) volume :=
    memLp_simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal p)
      hp_ne_zero hp_ne_top F
  (memLp_beurlingTransformL1 F₁ hp1 hp2 hF₁p).toLp
    (beurlingTransformL1 F₁ : ℂ → ℂ)

/--
%%handwave
name:
  Representative of the simple-function $L^p$ Beurling transform
statement:
  For $1<p<2$ and every planar $L^p$ simple function $F$, the function
  representative of its $L^p$ Beurling transform agrees almost everywhere
  with the weak-$L^1$ transform of the same simple function.
proof:
  This is the defining representative of the resulting $L^p$ class.
-/
theorem beurlingTransformLpSimpleFunc_coeFn
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    (beurlingTransformLpSimpleFunc p hp1 hp2 F : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL1
        (simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal p)
          (ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hp1))
          ENNReal.ofReal_ne_top F) : ℂ → ℂ) := by
  dsimp only [beurlingTransformLpSimpleFunc]
  exact MemLp.coeFn_toLp _

/--
%%handwave
name:
  Additivity on planar $L^p$ simple functions
statement:
  For $1<p<2$ and planar $L^p$ simple functions $F,G$,
  $$
    \mathcal S_p(F+G)=\mathcal S_pF+\mathcal S_pG.
  $$
proof:
  The inclusion of simple functions into $L^1$ is linear, the weak-$L^1$
  Beurling transform is additive, and the resulting function
  representatives determine the same $L^p$ class.
-/
theorem beurlingTransformLpSimpleFunc_add
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (F G : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    beurlingTransformLpSimpleFunc p hp1 hp2 (F + G) =
      beurlingTransformLpSimpleFunc p hp1 hp2 F +
        beurlingTransformLpSimpleFunc p hp1 hp2 G := by
  let hp0 : 0 < p := lt_trans zero_lt_one hp1
  let hp_ne_zero : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  let ι := simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal p)
    hp_ne_zero ENNReal.ofReal_ne_top
  have hT :
      (beurlingTransformL1 (ι (F + G)) : ℂ → ℂ) =ᵐ[volume]
        (beurlingTransformL1 (ι F) : ℂ → ℂ) +
          (beurlingTransformL1 (ι G) : ℂ → ℂ) := by
    rw [map_add, beurlingTransformL1_add]
    exact AEEqFun.coeFn_add _ _
  apply Lp.ext
  filter_upwards [beurlingTransformLpSimpleFunc_coeFn p hp1 hp2 (F + G),
    beurlingTransformLpSimpleFunc_coeFn p hp1 hp2 F,
    beurlingTransformLpSimpleFunc_coeFn p hp1 hp2 G,
    Lp.coeFn_add (beurlingTransformLpSimpleFunc p hp1 hp2 F)
      (beurlingTransformLpSimpleFunc p hp1 hp2 G), hT]
    with z hsum hF hG hadd hTz
  exact hsum.trans (hTz.trans (hadd ▸ congrArg₂ (· + ·) hF.symm hG.symm))

/--
%%handwave
name:
  Complex homogeneity on planar $L^p$ simple functions
statement:
  For $1<p<2$, $c\in\mathbb C$, and every planar $L^p$ simple function $F$,
  $$
    \mathcal S_p(cF)=c\,\mathcal S_pF.
  $$
proof:
  The inclusion into $L^1$ and the weak-$L^1$ Beurling transform are both
  complex homogeneous, and the resulting representatives agree almost
  everywhere.
-/
theorem beurlingTransformLpSimpleFunc_smul
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (c : ℂ)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    beurlingTransformLpSimpleFunc p hp1 hp2 (c • F) =
      c • beurlingTransformLpSimpleFunc p hp1 hp2 F := by
  let hp0 : 0 < p := lt_trans zero_lt_one hp1
  let hp_ne_zero : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  let ι := simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal p)
    hp_ne_zero ENNReal.ofReal_ne_top
  have hT :
      (beurlingTransformL1 (ι (c • F)) : ℂ → ℂ) =ᵐ[volume]
        c • (beurlingTransformL1 (ι F) : ℂ → ℂ) := by
    rw [map_smul, beurlingTransformL1_smul]
    exact AEEqFun.coeFn_smul _ _
  apply Lp.ext
  filter_upwards [beurlingTransformLpSimpleFunc_coeFn p hp1 hp2 (c • F),
    beurlingTransformLpSimpleFunc_coeFn p hp1 hp2 F,
    Lp.coeFn_smul c (beurlingTransformLpSimpleFunc p hp1 hp2 F), hT]
    with z hscaled hF hsmul hTz
  rw [hscaled, hTz, Pi.smul_apply, hsmul, Pi.smul_apply, hF]

/--
%%handwave
name:
  Complex-linear Beurling transform on planar $L^p$ simple functions
statement:
  For $1<p<2$, the Beurling transform defines a complex-linear map
  $$
    \mathcal S_p:L^p_{\mathrm{simple}}(\mathbb C)
      \longrightarrow L^p(\mathbb C).
  $$
-/
def beurlingTransformLpSimpleFuncLinearMap
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2) :
    Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) where
  toFun := beurlingTransformLpSimpleFunc p hp1 hp2
  map_add' := beurlingTransformLpSimpleFunc_add p hp1 hp2
  map_smul' := beurlingTransformLpSimpleFunc_smul p hp1 hp2

/--
%%handwave
name:
  Real-interpolation norm constant
statement:
  For $1<p<2$, set
  $$
    A_p=\left[p\left(
      \frac{2(40+16\pi)}{p-1}+\frac4{2-p}
    \right)\right]^{1/p}.
  $$
-/
def beurlingInterpolationNorm (p : ℝ) : ENNReal :=
  (ENNReal.ofReal p *
      (ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
            (ENNReal.ofReal (p - 1))⁻¹ +
        ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹)) ^ (1 / p)

/--
%%handwave
name:
  Finiteness of the real-interpolation norm constant
statement:
  If $1<p<2$, then
  $$
    A_p=\left[p\left(
      \frac{2(40+16\pi)}{p-1}+\frac4{2-p}
    \right)\right]^{1/p}<\infty.
  $$
proof:
  Both denominators are strictly positive, all remaining factors are finite,
  and a finite nonnegative number raised to the positive power $1/p$ is
  finite.
-/
theorem beurlingInterpolationNorm_lt_top
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    beurlingInterpolationNorm p < ∞ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hq1 : 0 < ENNReal.ofReal (p - 1) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr hp1)
  have hq2 : 0 < ENNReal.ofReal (2 - p) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr hp2)
  have hsum :
      ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
            (ENNReal.ofReal (p - 1))⁻¹ +
          ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹ < ∞ := by
    rw [ENNReal.add_lt_top]
    constructor
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.inv_lt_top.mpr hq1)
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.inv_lt_top.mpr hq2)
  apply ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp0.le)
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum).ne

/--
%%handwave
name:
  Strong norm bound on planar $L^p$ simple functions
statement:
  If $1<p<2$ and $F$ is a planar $L^p$ simple function, then
  $$
    \|\mathcal S_pF\|_p\leq A_p\|F\|_p.
  $$
proof:
  Apply [the strong norm estimate on integrable inputs](lean:JJMath.Quasiconformal.eLpNorm_beurlingTransformL1_le) to the $L^1$ class of $F$. Both the input and output representatives agree almost everywhere with the corresponding $L^p$ classes, and the finite extended-real inequality can therefore be converted to the ordinary norm inequality.
-/
theorem norm_beurlingTransformLpSimpleFunc_le
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    ‖beurlingTransformLpSimpleFunc p hp1 hp2 F‖ ≤
      (beurlingInterpolationNorm p).toReal * ‖F‖ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hp0
  let ι := simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal p)
    hp_ne_zero ENNReal.ofReal_ne_top
  have hinput :
      ((ι F : ℂ →₁[volume] ℂ) : ℂ → ℂ) =ᵐ[volume]
        Lp.simpleFunc.toSimpleFunc F :=
    (integrable_simpleFunc_toSimpleFunc hp_ne_zero ENNReal.ofReal_ne_top F).coeFn_toL1
  have hnorm_ennreal :
      eLpNorm (beurlingTransformLpSimpleFunc p hp1 hp2 F : ℂ → ℂ)
          (ENNReal.ofReal p) volume ≤
        beurlingInterpolationNorm p *
          eLpNorm (Lp.simpleFunc.toSimpleFunc F)
            (ENNReal.ofReal p) volume := by
    calc
      _ = eLpNorm (beurlingTransformL1 (ι F) : ℂ → ℂ)
          (ENNReal.ofReal p) volume :=
        eLpNorm_congr_ae (beurlingTransformLpSimpleFunc_coeFn p hp1 hp2 F)
      _ ≤ beurlingInterpolationNorm p *
          eLpNorm ((ι F : ℂ →₁[volume] ℂ) : ℂ → ℂ)
            (ENNReal.ofReal p) volume := by
        simpa only [beurlingInterpolationNorm] using
          (eLpNorm_beurlingTransformL1_le (ι F) hp1 hp2)
      _ = _ := by
        rw [eLpNorm_congr_ae hinput]
  calc
    ‖beurlingTransformLpSimpleFunc p hp1 hp2 F‖ =
        (eLpNorm (beurlingTransformLpSimpleFunc p hp1 hp2 F : ℂ → ℂ)
          (ENNReal.ofReal p) volume).toReal := Lp.norm_def _
    _ ≤ (beurlingInterpolationNorm p *
          eLpNorm (Lp.simpleFunc.toSimpleFunc F)
            (ENNReal.ofReal p) volume).toReal := by
      exact ENNReal.toReal_mono
        (ENNReal.mul_ne_top (beurlingInterpolationNorm_lt_top hp1 hp2).ne
          (Lp.simpleFunc.memLp F).eLpNorm_ne_top)
        hnorm_ennreal
    _ = (beurlingInterpolationNorm p).toReal * ‖F‖ := by
      rw [ENNReal.toReal_mul, Lp.simpleFunc.norm_toSimpleFunc]

/--
%%handwave
name:
  Strong Beurling transform below exponent two
statement:
  For $1<p<2$, the bounded transform on planar $L^p$ simple functions
  extends uniquely to a continuous complex-linear map
  $$
    \mathcal S_p:L^p(\mathbb C)\longrightarrow L^p(\mathbb C).
  $$
-/
def beurlingTransformLp
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) := by
  let T := beurlingTransformLpSimpleFuncLinearMap p hp1 hp2
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  exact T.extendOfNorm e

/--
%%handwave
name:
  Agreement of the completed transform with the simple-function transform
statement:
  If $1<p<2$ and $F$ is a planar $L^p$ simple function, then the completed
  transform evaluated at its $L^p$ class equals the previously constructed
  simple-function transform:
  $$
    \mathcal S_p[F]=\mathcal S_pF.
  $$
proof:
  The finite-support simple functions are dense in $L^p$, and extension of a
  bounded linear map agrees with that map on its dense domain.
-/
theorem beurlingTransformLp_apply_simpleFunc
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    beurlingTransformLp p hp1 hp2 (F : Lp ℂ (ENNReal.ofReal p) volume) =
      beurlingTransformLpSimpleFunc p hp1 hp2 F := by
  let T := beurlingTransformLpSimpleFuncLinearMap p hp1 hp2
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  change T.extendOfNorm e (e F) = T F
  exact LinearMap.extendOfNorm_eq
    (Lp.simpleFunc.denseRange ENNReal.ofReal_ne_top)
    ⟨(beurlingInterpolationNorm p).toReal,
      norm_beurlingTransformLpSimpleFunc_le p hp1 hp2⟩ F

/--
%%handwave
name:
  Strong $L^p$ bound for the completed Beurling transform
statement:
  If $1<p<2$, then every $F\in L^p(\mathbb C)$ satisfies
  $$
    \|\mathcal S_pF\|_p\leq A_p\|F\|_p,
    \qquad
    A_p=\left[p\left(
      \frac{2(40+16\pi)}{p-1}+\frac4{2-p}
    \right)\right]^{1/p}.
  $$
proof:
  The estimate holds on the dense simple-function subspace. The bounded
  linear extension preserves the same norm bound on the completion.
-/
theorem norm_beurlingTransformLp_le
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    ‖beurlingTransformLp p hp1 hp2 F‖ ≤
      (beurlingInterpolationNorm p).toReal * ‖F‖ := by
  let T := beurlingTransformLpSimpleFuncLinearMap p hp1 hp2
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  change ‖T.extendOfNorm e F‖ ≤ (beurlingInterpolationNorm p).toReal * ‖F‖
  exact LinearMap.norm_extendOfNorm_apply_le
    (Lp.simpleFunc.denseRange ENNReal.ofReal_ne_top)
    (beurlingInterpolationNorm p).toReal
    (norm_beurlingTransformLpSimpleFunc_le p hp1 hp2) F

end

end Quasiconformal

end JJMath
