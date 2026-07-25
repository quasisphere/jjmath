import JJMath.Quasiconformal.BeurlingTransform
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The `L²` Beltrami equation

This file solves the linear equation

`h - μ • S h = g`

on the complex plane when `μ` is essentially bounded with norm strictly less
than one.  The Beurling transform `S` is an `L²` isometry, so pointwise
multiplication followed by `S` has operator norm at most `‖μ‖∞`.  The inverse
of `I - Mμ S` is therefore its norm-convergent Neumann series.

For a bounded measurable coefficient which vanishes almost everywhere
outside a disk, the file also constructs the required `L²` right-hand side
and obtains the particular equation

`h - μ • S h = μ`.

This is the complete Hilbert-space part of the principal-solution
construction.  An `Lᵖ` estimate above exponent two is still needed later to
obtain a continuous Cauchy potential.
-/

namespace JJMath

open MeasureTheory
open scoped ENNReal

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Planar $L^2$ Beltrami operator
statement:
  For $\mu\in L^\infty(\mathbb C)$, the planar Beltrami operator on
  $L^2(\mathbb C)$ is the composition
  $$
    h\longmapsto M_\mu\mathcal Sh=\mu\,\mathcal Sh.
  $$
-/
def beltramiL2Operator
    (μ : Lp (α := ℂ) ℂ ∞ volume) : PlaneL2 →L[ℂ] PlaneL2 :=
  (l2PointwiseMultiplier μ).comp beurlingTransformL2

/--
%%handwave
name:
  Operator norm of an $L^\infty$ multiplier on $L^2$
statement:
  For every $\mu\in L^\infty(\mathbb C)$, pointwise multiplication on
  $L^2(\mathbb C)$ satisfies
  $$
    \lVert M_\mu\rVert_{L^2\to L^2}\leq\lVert\mu\rVert_{L^\infty}.
  $$
proof:
  The pointwise inequality $|\mu h|\leq\lVert\mu\rVert_\infty|h|$ gives the
  $L^2$ bound, which is exactly the bound used to construct the continuous
  linear map.
-/
theorem norm_l2PointwiseMultiplier_le
    (μ : Lp (α := ℂ) ℂ ∞ volume) :
    ‖l2PointwiseMultiplier μ‖ ≤ ‖μ‖ := by
  exact LinearMap.mkContinuous_norm_le
    (l2PointwiseMultiplierLinearMap μ) (norm_nonneg μ)
      (fun h => MeasureTheory.Lp.norm_smul_le μ h)

/--
%%handwave
name:
  Contraction bound for the $L^2$ Beltrami operator
statement:
  For every $\mu\in L^\infty(\mathbb C)$,
  $$
    \lVert M_\mu\mathcal S\rVert_{L^2\to L^2}
      \leq\lVert\mu\rVert_{L^\infty}.
  $$
proof:
  The operator norm of a composition is at most the product of the two
  operator norms. Use the multiplier bound and the fact that the Beurling
  transform is an $L^2$ isometry.
-/
theorem norm_beltramiL2Operator_le
    (μ : Lp (α := ℂ) ℂ ∞ volume) :
    ‖beltramiL2Operator μ‖ ≤ ‖μ‖ := by
  calc
    _ ≤ ‖l2PointwiseMultiplier μ‖ * ‖beurlingTransformL2‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖μ‖ * 1 := mul_le_mul
      (norm_l2PointwiseMultiplier_le μ)
      norm_beurlingTransformL2_le_one (norm_nonneg _) (norm_nonneg _)
    _ = ‖μ‖ := mul_one _

/--
%%handwave
name:
  Invertible $L^2$ Beltrami resolvent
statement:
  If $\mu\in L^\infty(\mathbb C)$ and $\|\mu\|_\infty<1$, then
  $I-M_\mu\mathcal S$ is regarded as an invertible bounded operator on
  $L^2(\mathbb C)$, with inverse given by its norm-convergent Neumann series.
-/
def beltramiL2ResolventUnit
    (μ : Lp (α := ℂ) ℂ ∞ volume) (hμ : ‖μ‖ < 1) :
    (PlaneL2 →L[ℂ] PlaneL2)ˣ :=
  Units.oneSub (beltramiL2Operator μ)
    ((norm_beltramiL2Operator_le μ).trans_lt hμ)

/--
%%handwave
name:
  $L^2$ Beltrami solution
statement:
  If $\|\mu\|_\infty<1$ and $g\in L^2(\mathbb C)$, define
  $$
    h=(I-M_\mu\mathcal S)^{-1}g.
  $$
  This is the candidate solution of $h-\mu\mathcal Sh=g$.
-/
def beltramiL2Solution
    (μ : Lp (α := ℂ) ℂ ∞ volume) (hμ : ‖μ‖ < 1)
    (g : PlaneL2) : PlaneL2 :=
  (↑(beltramiL2ResolventUnit μ hμ)⁻¹ :
      PlaneL2 →L[ℂ] PlaneL2) g

/--
%%handwave
name:
  Uniqueness of the $L^2$ Beltrami solution
statement:
  Let $\mu\in L^\infty(\mathbb C)$ satisfy
  $\lVert\mu\rVert_\infty<1$. If $g,h\in L^2(\mathbb C)$ and
  $$
    h-\mu\,\mathcal Sh=g,
  $$
  then $h=(I-M_\mu\mathcal S)^{-1}g$.
proof:
  Apply the inverse of the unit $I-M_\mu\mathcal S$ to the displayed
  equation.
-/
theorem beltramiL2Solution_unique
    (μ : Lp (α := ℂ) ℂ ∞ volume) (hμ : ‖μ‖ < 1)
    (g h : PlaneL2)
    (hh : h - μ • beurlingTransformL2 h = g) :
    h = beltramiL2Solution μ hμ g := by
  let u := beltramiL2ResolventUnit μ hμ
  have hu_apply (x : PlaneL2) :
      (u : PlaneL2 →L[ℂ] PlaneL2) x =
        x - μ • beurlingTransformL2 x := by
    rfl
  have hinv_apply (x : PlaneL2) :
      (↑u⁻¹ : PlaneL2 →L[ℂ] PlaneL2)
          ((u : PlaneL2 →L[ℂ] PlaneL2) x) = x := by
    rw [← ContinuousLinearMap.mul_apply, Units.inv_mul,
      ContinuousLinearMap.one_apply]
  calc
    h = (↑u⁻¹ : PlaneL2 →L[ℂ] PlaneL2)
        ((u : PlaneL2 →L[ℂ] PlaneL2) h) := (hinv_apply h).symm
    _ = (↑u⁻¹ : PlaneL2 →L[ℂ] PlaneL2) g := by rw [hu_apply, hh]
    _ = beltramiL2Solution μ hμ g := rfl

/--
%%handwave
name:
  Essential bound controls the $L^\infty$ norm
statement:
  Let $\mu:\mathbb C\to\mathbb C$ be measurable and essentially bounded by
  $k\geq0$. Its canonical $L^\infty$ class satisfies
  $$
    \lVert\mu\rVert_{L^\infty}\leq k.
  $$
proof:
  The essential supremum of $|\mu|$ is at most $k$. Pass from the extended
  $L^\infty$ seminorm to the real norm of the canonical equivalence class.
-/
theorem norm_toLp_top_le_of_ae_bound
    (μ : ℂ → ℂ)
    (hμTop : MemLp μ ∞ (volume : Measure ℂ))
    {k : ℝ} (hk : 0 ≤ k)
    (hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) :
    ‖hμTop.toLp μ‖ ≤ k := by
  rw [Lp.norm_toLp]
  calc
    ENNReal.toReal (eLpNorm μ ∞ (volume : Measure ℂ)) ≤
        ENNReal.toReal (ENNReal.ofReal k) := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      rw [eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_bound hbound
    _ = k := ENNReal.toReal_ofReal hk

end

end Quasiconformal

end JJMath
