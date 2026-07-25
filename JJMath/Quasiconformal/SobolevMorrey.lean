import JJMath.Quasiconformal.ApproxDifferentiability
import JJMath.Quasiconformal.SquareBoundary
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Morrey estimates for planar Sobolev maps

This file develops the quantitative bridge from a planar weak differential in
`L^p`, with `p > 2`, to oscillation estimates and the Lusin property.  The
first step combines the scale-covariant complex-valued `L²` Poincaré
inequality with finite-measure comparison of `L^p` norms.
-/

namespace JJMath

open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Lowering a planar ball exponent from $p$ to $2$
statement:
  Let $p>2$, let $B\subset\mathbb C$ be a ball, and let
  $g:B\to E$ be strongly measurable almost everywhere. Then
  $$
    \|g\|_{L^2(B)}
      \leq
      \|g\|_{L^p(B)}
      |B|^{1/2-1/p}.
  $$
proof:
  Apply the finite-measure comparison inequality between $L^p$ seminorms
  with exponents $2\leq p$.
-/
theorem eLpNorm_two_restrict_ball_le_eLpNorm_ofReal_mul_volume_rpow
    {E : Type*} [NormedAddCommGroup E]
    {g : ℂ → E} {c : ℂ} {r p : ℝ}
    (hp : 2 ≤ p)
    (hg : AEStronglyMeasurable g
      ((volume : Measure ℂ).restrict (ball c r))) :
    eLpNorm g 2 ((volume : Measure ℂ).restrict (ball c r)) ≤
      eLpNorm g (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict (ball c r)) *
        volume (ball c r) ^
          (1 / (2 : ENNReal).toReal -
            1 / (ENNReal.ofReal p).toReal) := by
  have h2p : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  simpa [Measure.restrict_apply_univ] using
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := (volume : Measure ℂ).restrict (ball c r))
      (f := g) h2p hg)

/--
%%handwave
name:
  Planar $L^p$ Poincaré estimate above the dimension
statement:
  There is a finite constant $C$ such that, for every $p>2$, every
  $r>0$, and every complex-valued weak Sobolev function $u$ on
  $B(c,r)$ with $Du\in L^p(B(c,r))$, some $a\in\mathbb C$ satisfies
  $$
    \|u-a\|_{L^2(B(c,r))}
      \leq
      Cr\,\|Du\|_{L^p(B(c,r))}
      |B(c,r)|^{1/2-1/p}.
  $$
proof:
  The scale-covariant complex-valued $L^2$ Poincaré inequality bounds the
  left side by $Cr\|Du\|_{L^2}$. Since the ball has finite area, lower the
  differential exponent from $p$ to $2$ and insert the exact
  finite-measure norm-comparison factor.
-/
theorem complex_valued_euclideanSobolev_poincare_Lp_scale_covariant :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {c : ℂ} {r p : ℝ}, 0 < r → 2 < p →
        ∀ {u : ℂ → ℂ} {du : ℂ → ℂ →L[ℝ] ℂ},
          JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
              (ball c r) u du →
          MemLp u 2 ((volume : Measure ℂ).restrict (ball c r)) →
          MemLp du (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict (ball c r)) →
          ∃ a : ℂ,
            AEStronglyMeasurable (fun z : ℂ ↦ u z - a)
              ((volume : Measure ℂ).restrict (ball c r)) ∧
            eLpNorm (fun z : ℂ ↦ u z - a) 2
                ((volume : Measure ℂ).restrict (ball c r)) ≤
              C * ENNReal.ofReal r *
                (eLpNorm du (ENNReal.ofReal p)
                    ((volume : Measure ℂ).restrict (ball c r)) *
                  volume (ball c r) ^
                    (1 / (2 : ENNReal).toReal -
                      1 / (ENNReal.ofReal p).toReal)) := by
  rcases complex_valued_euclideanSobolev_poincare_L2_scale_covariant with
    ⟨C, hCtop, hPoincare⟩
  refine ⟨C, hCtop, ?_⟩
  intro c r p hr hp u du hweak hu hdup
  let μ : Measure ℂ := (volume : Measure ℂ).restrict (ball c r)
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 (measure_ball_ne_top :
      volume (ball c r) ≠ ∞)
  have h2p : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hdu2 : MemLp du 2 μ :=
    hdup.mono_exponent h2p
  obtain ⟨a, hameas, ha⟩ :=
    hPoincare hr hweak hu hdu2
  refine ⟨a, hameas, ha.trans ?_⟩
  have hcompare :
      eLpNorm du 2 μ ≤
        eLpNorm du (ENNReal.ofReal p) μ *
          volume (ball c r) ^
            (1 / (2 : ENNReal).toReal -
              1 / (ENNReal.ofReal p).toReal) := by
    simpa [μ] using
      eLpNorm_two_restrict_ball_le_eLpNorm_ofReal_mul_volume_rpow
        (g := du) (c := c) (r := r) hp.le hdup.aestronglyMeasurable
  change
    C * ENNReal.ofReal r * eLpNorm du 2 μ ≤
      C * ENNReal.ofReal r *
        (eLpNorm du (ENNReal.ofReal p) μ *
          volume (ball c r) ^
            (1 / (2 : ENNReal).toReal -
              1 / (ENNReal.ofReal p).toReal))
  gcongr

/--
%%handwave
name:
  Dyadic factorization of the Morrey scale
statement:
  For $R>0$, $p\in\mathbb R$, and $n\in\mathbb N$,
  $$
    (R2^{-n})^{2-2/p}
      =
      R^{1-2/p}
      \left(2^{-(1-2/p)}\right)^n
      R2^{-n}.
  $$
proof:
  Write $2-2/p=(1-2/p)+1$, use multiplicativity of real powers on
  positive factors, and commute the real exponent $1-2/p$ with the
  natural exponent $n$.
-/
theorem dyadic_radius_rpow_two_sub_two_div
    {R p : ℝ} (hR : 0 < R) (n : ℕ) :
    (R / (2 : ℝ) ^ n) ^ (2 - 2 / p) =
      R ^ (1 - 2 / p) *
        (((2 : ℝ)⁻¹) ^ (1 - 2 / p)) ^ n *
          (R / (2 : ℝ) ^ n) := by
  let α : ℝ := 1 - 2 / p
  have hr : 0 < R / (2 : ℝ) ^ n :=
    div_pos hR (pow_pos (by norm_num) n)
  have hrform :
      R / (2 : ℝ) ^ n = R * ((2 : ℝ)⁻¹) ^ n := by
    rw [inv_pow]
    field_simp
  have hhalf : 0 ≤ ((2 : ℝ)⁻¹) := by positivity
  have hpow :
      ((((2 : ℝ)⁻¹) ^ n) ^ α : ℝ) =
        (((2 : ℝ)⁻¹) ^ α) ^ n := by
    calc
      ((((2 : ℝ)⁻¹) ^ n) ^ α : ℝ) =
          ((2 : ℝ)⁻¹) ^ ((n : ℝ) * α) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul hhalf (n : ℝ) α).symm
      _ = ((2 : ℝ)⁻¹) ^ (α * (n : ℝ)) := by
        congr 1
        ring
      _ = (((2 : ℝ)⁻¹) ^ α) ^ (n : ℝ) :=
        Real.rpow_mul hhalf α (n : ℝ)
      _ = (((2 : ℝ)⁻¹) ^ α) ^ n :=
        Real.rpow_natCast _ _
  have hexp : 2 - 2 / p = α + 1 := by
    dsimp [α]
    ring
  rw [show 1 - 2 / p = α by rfl]
  rw [hexp, Real.rpow_add hr α 1, Real.rpow_one]
  rw [hrform, Real.mul_rpow hR.le (by positivity), hpow]

/--
%%handwave
name:
  The Morrey dyadic ratio lies between zero and one
statement:
  If $p>2$, then
  $$
    0\leq 2^{-(1-2/p)}<1.
  $$
proof:
  The exponent $1-2/p$ is positive, while the base $1/2$ lies strictly
  between zero and one.
-/
theorem dyadic_morrey_ratio_nonneg_and_lt_one
    {p : ℝ} (hp : 2 < p) :
    0 ≤ ((2 : ℝ)⁻¹) ^ (1 - 2 / p) ∧
      ((2 : ℝ)⁻¹) ^ (1 - 2 / p) < 1 := by
  have hp0 : 0 < p := by linarith
  have hexp : 0 < 1 - 2 / p := by
    rw [sub_pos, div_lt_one hp0]
    exact hp
  constructor
  · exact (Real.rpow_pos_of_pos (by positivity) _).le
  · exact Real.rpow_lt_one (by positivity) (by norm_num) hexp

/--
%%handwave
name:
  Planar ball volume at the Morrey exponent
statement:
  If $r>0$ and $p>2$, then
  $$
    |B(c,r)|^{1/2-1/p}
      =
      \pi^{1/2-1/p}r^{1-2/p}.
  $$
  Here the left side is converted from an extended nonnegative real to a
  real number.
proof:
  Use $|B(c,r)|=\pi r^2$, multiplicativity of real powers on nonnegative
  factors, and
  $2(1/2-1/p)=1-2/p$.
-/
theorem volume_ball_rpow_morrey_toReal
    {c : ℂ} {r p : ℝ} (hr : 0 < r) (hp : 2 < p) :
    (volume (ball c r) ^
      (1 / (2 : ENNReal).toReal -
        1 / (ENNReal.ofReal p).toReal)).toReal =
      Real.pi ^ (1 / 2 - 1 / p) *
        r ^ (1 - 2 / p) := by
  have hp0 : 0 < p := by linarith
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  rw [← ENNReal.toReal_rpow, Complex.volume_ball]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
    ENNReal.coe_toReal]
  rw [ENNReal.toReal_ofReal hp0.le]
  change (r ^ 2 * Real.pi) ^ (1 / 2 - 1 / p) =
    Real.pi ^ (1 / 2 - 1 / p) * r ^ (1 - 2 / p)
  rw [Real.mul_rpow (sq_nonneg r) hpi]
  rw [show (r ^ 2 : ℝ) = r ^ (2 : ℝ) by
    norm_num [Real.rpow_natCast]]
  rw [← Real.rpow_mul (by positivity : 0 ≤ r)]
  rw [mul_sub]
  have hexp :
      2 * (1 / 2 : ℝ) - 2 * (1 / p) = 1 - 2 / p := by
    ring
  rw [hexp]
  ring

/--
%%handwave
name:
  Real-valued planar Morrey--Poincaré estimate
statement:
  There is a finite constant $C$ such that, whenever $p>2$, $r>0$, and
  $u$ has weak differential $Du\in L^p(B(c,r))$, some $a\in\mathbb C$
  satisfies
  $$
    \|u-a\|_{L^2(B(c,r))}
      \leq
      C\pi^{1/2-1/p}
      \|Du\|_{L^p(B(c,r))}
      r^{2-2/p}.
  $$
proof:
  Start from the scale-covariant $L^p$ Poincaré estimate and convert its
  finite extended-real bound to real numbers. Then use the exact planar
  ball-volume power formula and combine
  $r\,r^{1-2/p}=r^{2-2/p}$.
-/
theorem complex_valued_euclideanSobolev_poincare_Lp_real_scale :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {c : ℂ} {r p : ℝ}, 0 < r → 2 < p →
        ∀ {u : ℂ → ℂ} {du : ℂ → ℂ →L[ℝ] ℂ},
          JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
              (ball c r) u du →
          MemLp u 2 ((volume : Measure ℂ).restrict (ball c r)) →
          MemLp du (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict (ball c r)) →
          ∃ a : ℂ,
            AEStronglyMeasurable (fun z : ℂ ↦ u z - a)
              ((volume : Measure ℂ).restrict (ball c r)) ∧
            (eLpNorm (fun z : ℂ ↦ u z - a) 2
                ((volume : Measure ℂ).restrict (ball c r))).toReal ≤
              C.toReal *
                (eLpNorm du (ENNReal.ofReal p)
                  ((volume : Measure ℂ).restrict (ball c r))).toReal *
                Real.pi ^ (1 / 2 - 1 / p) *
                r ^ (2 - 2 / p) := by
  rcases complex_valued_euclideanSobolev_poincare_Lp_scale_covariant with
    ⟨C, hCtop, hPoincare⟩
  refine ⟨C, hCtop, ?_⟩
  intro c r p hr hp u du hweak hu hdup
  obtain ⟨a, hameas, hbound⟩ :=
    hPoincare hr hp hweak hu hdup
  refine ⟨a, hameas, ?_⟩
  have hp0 : 0 < p := by linarith
  have hexponent :
      0 ≤ 1 / (2 : ENNReal).toReal -
        1 / (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hp0.le]
    have hinv :
        1 / p < 1 / (2 : ℝ) :=
      one_div_lt_one_div_of_lt (by norm_num) hp
    linarith
  have hright_ne :
      C * ENNReal.ofReal r *
        (eLpNorm du (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict (ball c r)) *
          volume (ball c r) ^
            (1 / (2 : ENNReal).toReal -
              1 / (ENNReal.ofReal p).toReal)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top hCtop.ne ENNReal.ofReal_ne_top
    · apply ENNReal.mul_ne_top hdup.eLpNorm_ne_top
      exact ENNReal.rpow_ne_top_of_nonneg hexponent
        (measure_ball_ne_top : volume (ball c r) ≠ ∞)
  have hreal := ENNReal.toReal_mono hright_ne hbound
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr.le] at hreal
  rw [volume_ball_rpow_morrey_toReal hr hp] at hreal
  have hscale :
      r * r ^ (1 - 2 / p) = r ^ (2 - 2 / p) := by
    rw [show 2 - 2 / p = 1 + (1 - 2 / p) by ring,
      Real.rpow_add hr, Real.rpow_one]
  rw [← hscale]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hreal

/--
%%handwave
name:
  Fixed planar Morrey--Poincaré constant
statement:
  $\mathcal C_{\mathrm{MP}}\in[0,\infty]$ is a fixed choice of the
  universal constant in the planar complex-valued Morrey--Poincaré
  inequality.
-/
def planarMorreyPoincareConstant : ℝ≥0∞ :=
  Classical.choose
    complex_valued_euclideanSobolev_poincare_Lp_real_scale

/--
%%handwave
name:
  The fixed Morrey--Poincaré constant is admissible
statement:
  The constant $\mathcal C_{\mathrm{MP}}$ is finite. For every $p>2$,
  every $r>0$, and every complex-valued weak Sobolev function $u$ on
  $B(c,r)$ with $Du\in L^p(B(c,r))$, some $a\in\mathbb C$ satisfies
  $$
    \|u-a\|_{L^2(B(c,r))}
      \leq
      \mathcal C_{\mathrm{MP}}\pi^{1/2-1/p}
      \|Du\|_{L^p(B(c,r))}r^{2-2/p}.
  $$
proof:
  This is the defining property of the fixed choice from the universal
  real-valued planar Morrey--Poincaré estimate.
-/
theorem planarMorreyPoincareConstant_spec :
    planarMorreyPoincareConstant < ⊤ ∧
      ∀ {c : ℂ} {r p : ℝ}, 0 < r → 2 < p →
        ∀ {u : ℂ → ℂ} {du : ℂ → ℂ →L[ℝ] ℂ},
          JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
              (ball c r) u du →
          MemLp u 2 ((volume : Measure ℂ).restrict (ball c r)) →
          MemLp du (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict (ball c r)) →
          ∃ a : ℂ,
            AEStronglyMeasurable (fun z : ℂ ↦ u z - a)
              ((volume : Measure ℂ).restrict (ball c r)) ∧
            (eLpNorm (fun z : ℂ ↦ u z - a) 2
                ((volume : Measure ℂ).restrict (ball c r))).toReal ≤
              planarMorreyPoincareConstant.toReal *
                (eLpNorm du (ENNReal.ofReal p)
                  ((volume : Measure ℂ).restrict (ball c r))).toReal *
                Real.pi ^ (1 / 2 - 1 / p) *
                r ^ (2 - 2 / p) :=
  Classical.choose_spec
    complex_valued_euclideanSobolev_poincare_Lp_real_scale

/--
%%handwave
name:
  Comparison of constants on overlapping planar balls
statement:
  Let $r>0$ and $\operatorname{dist}(x,y)\leq r/2$. If
  $u-a\in L^2(B(x,r))$ and $u-b\in L^2(B(y,r))$, then
  $$
    \|a-b\|\frac r2\sqrt\pi
      \leq
      \|u-a\|_{L^2(B(x,r))}
        +\|u-b\|_{L^2(B(y,r))}.
  $$
proof:
  The ball $B(x,r/2)$ is contained in both radius-$r$ balls. Restrict
  both errors to this common ball, compare the two constants there, and
  enlarge the two $L^2$ seminorms back to their original balls.
-/
theorem norm_sub_mul_half_radius_mul_sqrt_pi_le_eLpNorm_add_of_dist_le
    {E : Type} [NormedAddCommGroup E] {u : ℂ → E}
    {x y : ℂ} {r : ℝ} (hr : 0 < r)
    (hxy : dist x y ≤ r / 2) {a b : E}
    (hua : MemLp (fun z : ℂ ↦ u z - a) 2
      ((volume : Measure ℂ).restrict (ball x r)))
    (hub : MemLp (fun z : ℂ ↦ u z - b) 2
      ((volume : Measure ℂ).restrict (ball y r))) :
    ‖a - b‖ * ((r / 2) * Real.sqrt Real.pi) ≤
      (eLpNorm (fun z : ℂ ↦ u z - a) 2
        ((volume : Measure ℂ).restrict (ball x r))).toReal +
      (eLpNorm (fun z : ℂ ↦ u z - b) 2
        ((volume : Measure ℂ).restrict (ball y r))).toReal := by
  have hhalf : 0 < r / 2 := by linarith
  have hcommon_x : ball x (r / 2) ⊆ ball x r :=
    ball_subset_ball (by linarith)
  have hcommon_y : ball x (r / 2) ⊆ ball y r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc
      dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add_of_lt_of_le hz hxy
      _ = r := by ring
  let μcommon : Measure ℂ :=
    (volume : Measure ℂ).restrict (ball x (r / 2))
  have hua_common : MemLp (fun z : ℂ ↦ u z - a) 2 μcommon :=
    hua.mono_measure (Measure.restrict_mono hcommon_x le_rfl)
  have hub_common : MemLp (fun z : ℂ ↦ u z - b) 2 μcommon :=
    hub.mono_measure (Measure.restrict_mono hcommon_y le_rfl)
  have hcompare :=
    norm_sub_mul_radius_mul_sqrt_pi_le_eLpNorm_add
      (u := u) (x := x) (r := r / 2) (s := r / 2)
      (a := a) (b := b) hhalf le_rfl hua_common hub_common
  have ha_mono :
      (eLpNorm (fun z : ℂ ↦ u z - a) 2 μcommon).toReal ≤
        (eLpNorm (fun z : ℂ ↦ u z - a) 2
          ((volume : Measure ℂ).restrict (ball x r))).toReal := by
    exact ENNReal.toReal_mono hua.eLpNorm_ne_top
      (eLpNorm_mono_measure _
        (Measure.restrict_mono hcommon_x le_rfl))
  have hb_mono :
      (eLpNorm (fun z : ℂ ↦ u z - b) 2 μcommon).toReal ≤
        (eLpNorm (fun z : ℂ ↦ u z - b) 2
          ((volume : Measure ℂ).restrict (ball y r))).toReal := by
    exact ENNReal.toReal_mono hub.eLpNorm_ne_top
      (eLpNorm_mono_measure _
        (Measure.restrict_mono hcommon_y le_rfl))
  exact hcompare.trans (add_le_add ha_mono hb_mono)

/--
%%handwave
name:
  Geometrically decaying Campanato centers converge
statement:
  Let $R>0$, $0\leq q<1$, and let $a_n$ be constants associated with the
  dyadic balls $B(x,R2^{-n})$. Suppose $u-a_n\in L^2(B(x,R2^{-n}))$ and
  $$
    \|u-a_n\|_{L^2(B(x,R2^{-n}))}
      \leq A q^n R2^{-n}
  $$
  for every $n$, where $A\geq0$. Then $a_n$ converges to a constant $a$,
  and
  $$
    \|a_n-a\|
      \leq
      \frac{3A}{\sqrt\pi}\frac{q^n}{1-q}.
  $$
proof:
  Compare the constants on two consecutive nested balls. The larger-ball
  error contributes at most $2Aq^n$ after division by the smaller radius,
  while the smaller-ball error contributes at most $Aq^{n+1}\leq Aq^n$.
  Thus consecutive centers have distance at most
  $3Aq^n/\sqrt\pi$. Sum this geometric estimate in the complete target
  space.
-/
theorem exists_limit_dyadicCenters_of_eLpNorm_le_geometric
    {E : Type} [NormedAddCommGroup E] [CompleteSpace E]
    {u : ℂ → E} {x : ℂ} {R q A : ℝ} {a : ℕ → E}
    (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A)
    (hmem : ∀ n : ℕ,
      MemLp (fun y : ℂ ↦ u y - a n) 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n))))
    (herror : ∀ n : ℕ,
      (eLpNorm (fun y : ℂ ↦ u y - a n) 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n)))).toReal ≤
        A * q ^ n * (R / (2 : ℝ) ^ n)) :
    ∃ aLim : E, Tendsto a atTop (𝓝 aLim) ∧
      ∀ n : ℕ,
        ‖a n - aLim‖ ≤
          (3 * A / Real.sqrt Real.pi) * q ^ n / (1 - q) := by
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hrpos (n : ℕ) : 0 < R / (2 : ℝ) ^ n :=
    div_pos hR (pow_pos (by norm_num) n)
  have hr_succ (n : ℕ) :
      R / (2 : ℝ) ^ n =
        2 * (R / (2 : ℝ) ^ (n + 1)) := by
    rw [pow_succ]
    field_simp
  have hqpow (n : ℕ) : q ^ (n + 1) ≤ q ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hq0 n) hq1.le
  have hincrement (n : ℕ) :
      dist (a n) (a (n + 1)) ≤
        (3 * A / Real.sqrt Real.pi) * q ^ n := by
    let r := R / (2 : ℝ) ^ n
    let s := R / (2 : ℝ) ^ (n + 1)
    have hs : 0 < s := hrpos (n + 1)
    have hsr : s ≤ r := by
      rw [show r = 2 * s by simpa [r, s] using hr_succ n]
      linarith
    have hcompare :=
      norm_sub_mul_radius_mul_sqrt_pi_le_eLpNorm_add
        (u := u) (x := x) (r := r) (s := s)
        (a := a n) (b := a (n + 1)) hs hsr
        (by simpa [r] using hmem n)
        (by simpa [s] using hmem (n + 1))
    have herrors :
        (eLpNorm (fun y : ℂ ↦ u y - a n) 2
            ((volume : Measure ℂ).restrict (ball x r))).toReal +
          (eLpNorm (fun y : ℂ ↦ u y - a (n + 1)) 2
            ((volume : Measure ℂ).restrict (ball x s))).toReal ≤
          3 * A * q ^ n * s := by
      calc
        _ ≤ A * q ^ n * r + A * q ^ (n + 1) * s :=
          add_le_add (by simpa [r] using herror n)
            (by simpa [s] using herror (n + 1))
        _ ≤ A * q ^ n * r + A * q ^ n * s := by
          have hterm : A * q ^ (n + 1) * s ≤ A * q ^ n * s :=
            mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hqpow n) hA) hs.le
          linarith
        _ = 3 * A * q ^ n * s := by
          rw [show r = 2 * s by simpa [r, s] using hr_succ n]
          ring
    have hscaled :
        ‖a n - a (n + 1)‖ * (s * Real.sqrt Real.pi) ≤
          3 * A * q ^ n * s :=
      hcompare.trans herrors
    have hcancel :
        ‖a n - a (n + 1)‖ * Real.sqrt Real.pi ≤
          3 * A * q ^ n := by
      apply le_of_mul_le_mul_right _ hs
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
    rw [dist_eq_norm]
    calc
      ‖a n - a (n + 1)‖ ≤
          (3 * A * q ^ n) / Real.sqrt Real.pi :=
        (le_div_iff₀ hsqrt).2 hcancel
      _ = (3 * A / Real.sqrt Real.pi) * q ^ n := by ring
  have hcauchy : CauchySeq a :=
    cauchySeq_of_le_geometric q (3 * A / Real.sqrt Real.pi) hq1
      hincrement
  obtain ⟨aLim, haLim⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨aLim, haLim, ?_⟩
  intro n
  simpa [dist_eq_norm] using
    dist_le_of_le_geometric_of_tendsto
      q (3 * A / Real.sqrt Real.pi) hq1 hincrement haLim n

/--
%%handwave
name:
  Continuous values have vanishing scale-normalized mean oscillation
statement:
  If $f:\mathbb C\to E$ is continuous at $x$, then
  $$
    \frac{\|f-f(x)\|_{L^2(B(x,r))}}r\longrightarrow0
    \qquad(r\downarrow0).
  $$
proof:
  Given $\varepsilon>0$, continuity bounds
  $\|f(y)-f(x)\|$ by $\varepsilon/(2\sqrt\pi)$ on a sufficiently small
  ball. Monotonicity of the $L^2$ seminorm and
  $|B(x,r)|=\pi r^2$ then bound the displayed quotient by
  $\varepsilon/2$.
-/
theorem continuousAt_tendsto_eLpNorm_sub_value_div_radius
    {E : Type} [NormedAddCommGroup E]
    {f : ℂ → E} {x : ℂ} (hf : ContinuousAt f x) :
    Tendsto
      (fun r : ℝ ↦
        (eLpNorm (fun y : ℂ ↦ f y - f x) 2
          ((volume : Measure ℂ).restrict (ball x r))).toReal / r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  let δ : ℝ := ε / (2 * Real.sqrt Real.pi)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hsqrt)
  have hclose : {y : ℂ | ‖f y - f x‖ < δ} ∈ 𝓝 x := by
    have htendsto := hf.tendsto
    rw [Metric.tendsto_nhds] at htendsto
    simpa only [dist_eq_norm] using htendsto δ hδ
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hclose
  have hrho : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < ρ :=
    Filter.Eventually.filter_mono inf_le_left
      ((tendsto_order.1 tendsto_id).2 ρ hρ)
  filter_upwards [self_mem_nhdsWithin, hrho] with r hr hrρ
  have hr0 : 0 < r := hr
  let μ : Measure ℂ := (volume : Measure ℂ).restrict (ball x r)
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 (measure_ball_ne_top :
      volume (ball x r) ≠ ∞)
  have hpoint :
      ∀ᵐ y : ℂ ∂μ, ‖f y - f x‖ ≤ ‖δ‖ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hyρ : y ∈ ball x ρ := by
      rw [mem_ball] at hy ⊢
      exact hy.trans hrρ
    exact (hball hyρ).le.trans_eq (by
      rw [Real.norm_eq_abs, abs_of_pos hδ])
  have hmono :
      eLpNorm (fun y : ℂ ↦ f y - f x) 2 μ ≤
        eLpNorm (fun _ : ℂ ↦ δ) 2 μ :=
    eLpNorm_mono_ae hpoint
  have hreal :
      (eLpNorm (fun y : ℂ ↦ f y - f x) 2 μ).toReal ≤
        (eLpNorm (fun _ : ℂ ↦ δ) 2 μ).toReal :=
    ENNReal.toReal_mono (memLp_const δ).eLpNorm_ne_top hmono
  have hconst :=
    eLpNorm_const_two_ball_toReal δ x hr0
  change
    dist
      ((eLpNorm (fun y : ℂ ↦ f y - f x) 2 μ).toReal / r)
      0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg ENNReal.toReal_nonneg hr0.le)]
  have hdiv :
      (eLpNorm (fun y : ℂ ↦ f y - f x) 2 μ).toReal / r ≤
        δ * Real.sqrt Real.pi := by
    apply (div_le_iff₀ hr0).2
    rw [show
      (eLpNorm (fun _ : ℂ ↦ δ) 2 μ).toReal =
        ‖δ‖ * (r * Real.sqrt Real.pi) by simpa [μ] using hconst] at hreal
    simpa [Real.norm_eq_abs, abs_of_pos hδ, mul_assoc, mul_left_comm,
      mul_comm] using hreal
  have hδsqrt : δ * Real.sqrt Real.pi = ε / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hsqrt]
  rw [hδsqrt] at hdiv
  linarith

/--
%%handwave
name:
  Dyadic Campanato centers converge to the continuous value
statement:
  Let $f:\mathbb C\to E$ be continuous at $x$, let $R>0$, and let
  $0\leq q<1$. Suppose $a_n$ is a constant on the scale
  $r_n=R2^{-n}$ with
  $$
    f-a_n\in L^2(B(x,r_n)),\qquad
    \|f-a_n\|_{L^2(B(x,r_n))}
      \leq A q^n r_n
  $$
  for some real constant $A$. Then $a_n\to f(x)$.
proof:
  Compare $a_n$ with $f(x)$ on the same ball. After dividing by
  $r_n\sqrt\pi$, the first error is at most $Aq^n$, while the second is
  the scale-normalized mean oscillation of $f$ about its continuous
  value. Both tend to zero.
-/
theorem tendsto_dyadicCenters_to_value_of_continuousAt
    {E : Type} [NormedAddCommGroup E]
    {f : ℂ → E} {x : ℂ} {R q A : ℝ} {a : ℕ → E}
    (hf : ContinuousAt f x)
    (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hmem : ∀ n : ℕ,
      MemLp (fun y : ℂ ↦ f y - a n) 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n))))
    (herror : ∀ n : ℕ,
      (eLpNorm (fun y : ℂ ↦ f y - a n) 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n)))).toReal ≤
        A * q ^ n * (R / (2 : ℝ) ^ n)) :
    Tendsto a atTop (𝓝 (f x)) := by
  let r : ℕ → ℝ := fun n ↦ R / (2 : ℝ) ^ n
  have hrpos (n : ℕ) : 0 < r n :=
    div_pos hR (pow_pos (by norm_num) n)
  have hr_tendsto : Tendsto r atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hpow :
          Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one
          (by positivity : 0 ≤ ((2 : ℝ)⁻¹))
          (by norm_num : ((2 : ℝ)⁻¹) < 1)
      simpa only [r, div_eq_mul_inv, inv_pow, mul_zero] using
        (tendsto_const_nhds.mul hpow :
          Tendsto (fun n : ℕ ↦ R * ((2 : ℝ)⁻¹) ^ n)
            atTop (𝓝 (R * 0)))
    · exact Filter.Eventually.of_forall hrpos
  have href :
      Tendsto
        (fun n : ℕ ↦
          (eLpNorm (fun y : ℂ ↦ f y - f x) 2
            ((volume : Measure ℂ).restrict (ball x (r n)))).toReal /
              r n)
        atTop (𝓝 0) := by
    exact
      (continuousAt_tendsto_eLpNorm_sub_value_div_radius hf).comp
        hr_tendsto
  have hq :
      Tendsto (fun n : ℕ ↦ q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  let upper : ℕ → ℝ := fun n ↦
    (A * q ^ n +
      (eLpNorm (fun y : ℂ ↦ f y - f x) 2
        ((volume : Measure ℂ).restrict (ball x (r n)))).toReal /
          r n) / Real.sqrt Real.pi
  have hupper : Tendsto upper atTop (𝓝 0) := by
    dsimp [upper]
    simpa using ((tendsto_const_nhds.mul hq).add href).div_const
      (Real.sqrt Real.pi)
  have hbound (n : ℕ) : ‖a n - f x‖ ≤ upper n := by
    let μ : Measure ℂ :=
      (volume : Measure ℂ).restrict (ball x (r n))
    letI : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.2 (measure_ball_ne_top :
        volume (ball x (r n)) ≠ ∞)
    have hmem_center :
        MemLp (fun y : ℂ ↦ f y - a n) 2 μ := by
      simpa [μ, r] using hmem n
    have hmem_reference :
        MemLp (fun y : ℂ ↦ f y - f x) 2 μ := by
      have hadd :=
        hmem_center.add (memLp_const (a n - f x) :
          MemLp (fun _ : ℂ ↦ a n - f x) 2 μ)
      apply (memLp_congr_ae
        (Filter.Eventually.of_forall fun y ↦ by
          change f y - f x =
            (f y - a n) + (a n - f x)
          abel)).2
      simpa only [Pi.add_apply] using hadd
    have hcompare :=
      norm_sub_mul_radius_mul_sqrt_pi_le_eLpNorm_add
        (u := f) (x := x) (r := r n) (s := r n)
        (a := a n) (b := f x) (hrpos n) le_rfl
        hmem_center hmem_reference
    have hsqrt : 0 < Real.sqrt Real.pi :=
      Real.sqrt_pos.2 Real.pi_pos
    have hscaled :
        ‖a n - f x‖ * Real.sqrt Real.pi ≤
          (eLpNorm (fun y : ℂ ↦ f y - a n) 2 μ).toReal / r n +
          (eLpNorm (fun y : ℂ ↦ f y - f x) 2 μ).toReal / r n := by
      calc
        ‖a n - f x‖ * Real.sqrt Real.pi ≤
            ((eLpNorm (fun y : ℂ ↦ f y - a n) 2 μ).toReal +
              (eLpNorm (fun y : ℂ ↦ f y - f x) 2 μ).toReal) / r n := by
          apply (le_div_iff₀ (hrpos n)).2
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hcompare
        _ = (eLpNorm (fun y : ℂ ↦ f y - a n) 2 μ).toReal / r n +
            (eLpNorm (fun y : ℂ ↦ f y - f x) 2 μ).toReal / r n := by
          rw [add_div]
    have hcenter :
        (eLpNorm (fun y : ℂ ↦ f y - a n) 2 μ).toReal / r n ≤
          A * q ^ n := by
      apply (div_le_iff₀ (hrpos n)).2
      simpa [μ, r, mul_assoc] using herror n
    dsimp [upper]
    apply (le_div_iff₀ hsqrt).2
    exact hscaled.trans (add_le_add_left hcenter _)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ norm_nonneg (a n - f x))
    (Filter.Eventually.of_forall hbound) hupper

/--
%%handwave
name:
  Quantitative dyadic-center estimate at a continuous point
statement:
  Let $f:\mathbb C\to E$ be continuous at $x$, let $R>0$, let
  $0\leq q<1$, and let $A\geq0$. If constants $a_n$ satisfy
  $$
    f-a_n\in L^2(B(x,R2^{-n})),\qquad
    \|f-a_n\|_{L^2(B(x,R2^{-n}))}
      \leq A q^nR2^{-n},
  $$
  then
  $$
    \|a_n-f(x)\|
      \leq
      \frac{3A}{\sqrt\pi}\frac{q^n}{1-q}.
  $$
proof:
  The geometric Campanato estimate gives the same bound from $a_n$ to
  the limit of the center sequence. The continuous-value identification
  shows that this limit is $f(x)$.
-/
theorem norm_dyadicCenter_sub_value_le_of_continuousAt
    {E : Type} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℂ → E} {x : ℂ} {R q A : ℝ} {a : ℕ → E}
    (hf : ContinuousAt f x)
    (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A)
    (hmem : ∀ n : ℕ,
      MemLp (fun y : ℂ ↦ f y - a n) 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n))))
    (herror : ∀ n : ℕ,
      (eLpNorm (fun y : ℂ ↦ f y - a n) 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n)))).toReal ≤
        A * q ^ n * (R / (2 : ℝ) ^ n)) :
    ∀ n : ℕ,
      ‖a n - f x‖ ≤
        (3 * A / Real.sqrt Real.pi) * q ^ n / (1 - q) := by
  obtain ⟨aLim, haLim, htail⟩ :=
    exists_limit_dyadicCenters_of_eLpNorm_le_geometric
      hR hq0 hq1 hA hmem herror
  have hvalue : Tendsto a atTop (𝓝 (f x)) :=
    tendsto_dyadicCenters_to_value_of_continuousAt
      hf hR hq0 hq1 hmem herror
  have haLim_eq : aLim = f x :=
    tendsto_nhds_unique haLim hvalue
  simpa only [haLim_eq] using htail

/--
%%handwave
name:
  Dyadic Poincaré centers for a planar $W^{1,p}$ map
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$, let
  $\overline B(x,R)\subset\Omega$, and suppose
  $Df\in L^p(\overline B(x,R))$ for some $p>2$. There is a finite universal
  constant $C$ and a sequence of centers $a_n\in\mathbb C$ such that, with
  $r_n=R2^{-n}$,
  $$
    \|f-a_n\|_{L^2(B(x,r_n))}
      \leq
      Cr_n\|Df\|_{L^p(B(x,r_n))}
      |B(x,r_n)|^{1/2-1/p}
  $$
  for every $n$.
  One may take
  $$
    A=\mathcal C_{\mathrm{MP}}\pi^{1/2-1/p}
      \|Df\|_{L^p(\overline B(x,R))}R^{1-2/p}.
  $$
proof:
  Every dyadic ball is contained in $\overline B(x,R)$. Restrict the local
  weak derivative and the $L^2$ value bound to that ball, restrict the given
  $L^p$ differential bound, and apply the scale-covariant planar
  $L^p$ Poincaré estimate independently at each scale.
-/
theorem IsLocalW12On.exists_dyadic_poincareCenters
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    {x : ℂ} {R p : ℝ} (hR : 0 < R) (hp : 2 < p)
    (hclosed : closedBall x R ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall x R))) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∃ a : ℕ → ℂ, ∀ n : ℕ,
        let r := R / (2 : ℝ) ^ n
        AEStronglyMeasurable (fun z : ℂ ↦ f z - a n)
            ((volume : Measure ℂ).restrict (ball x r)) ∧
          eLpNorm (fun z : ℂ ↦ f z - a n) 2
              ((volume : Measure ℂ).restrict (ball x r)) ≤
            C * ENNReal.ofReal r *
              (eLpNorm df (ENNReal.ofReal p)
                  ((volume : Measure ℂ).restrict (ball x r)) *
                volume (ball x r) ^
                  (1 / (2 : ENNReal).toReal -
                    1 / (ENNReal.ofReal p).toReal)) := by
  rcases complex_valued_euclideanSobolev_poincare_Lp_scale_covariant with
    ⟨C, hCtop, hPoincare⟩
  refine ⟨C, hCtop, ?_⟩
  have hlocal :=
    hW.2.2 (closedBall x R) (isCompact_closedBall x R) hclosed
  have hball_closed (n : ℕ) :
      ball x (R / (2 : ℝ) ^ n) ⊆ closedBall x R := by
    have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hrle : R / (2 : ℝ) ^ n ≤ R :=
      div_le_self hR.le hpow
    exact ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrle)
  have hrpos (n : ℕ) : 0 < R / (2 : ℝ) ^ n :=
    div_pos hR (pow_pos (by norm_num) n)
  have hexists : ∀ n : ℕ, ∃ a : ℂ,
      AEStronglyMeasurable (fun z : ℂ ↦ f z - a)
          ((volume : Measure ℂ).restrict
            (ball x (R / (2 : ℝ) ^ n))) ∧
        eLpNorm (fun z : ℂ ↦ f z - a) 2
            ((volume : Measure ℂ).restrict
              (ball x (R / (2 : ℝ) ^ n))) ≤
          C * ENNReal.ofReal (R / (2 : ℝ) ^ n) *
            (eLpNorm df (ENNReal.ofReal p)
                ((volume : Measure ℂ).restrict
                  (ball x (R / (2 : ℝ) ^ n))) *
              volume (ball x (R / (2 : ℝ) ^ n)) ^
                (1 / (2 : ENNReal).toReal -
                  1 / (ENNReal.ofReal p).toReal)) := by
    intro n
    have hμ :
        (volume : Measure ℂ).restrict
            (ball x (R / (2 : ℝ) ^ n)) ≤
          (volume : Measure ℂ).restrict (closedBall x R) :=
      Measure.restrict_mono (hball_closed n) le_rfl
    have hf2 : MemLp f 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n))) :=
      hlocal.1.mono_measure hμ
    have hdfpn : MemLp df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n))) :=
      hdfp.mono_measure hμ
    have hweak :
        JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
          (ball x (R / (2 : ℝ) ^ n)) f df :=
      hW.2.1.mono_set
        ((hball_closed n).trans hclosed)
    exact hPoincare (hrpos n) hp hweak hf2 hdfpn
  choose a ha using hexists
  exact ⟨a, fun n ↦ ha n⟩

/--
%%handwave
name:
  Geometrically decaying dyadic Poincaré errors
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$, let
  $\overline B(x,R)\subset\Omega$, and suppose
  $Df\in L^p(\overline B(x,R))$ for some $p>2$. Set
  $q=2^{-(1-2/p)}$. Then there are $A\geq0$ and constants
  $a_n\in\mathbb C$ such that, for $r_n=R2^{-n}$,
  $$
    f-a_n\in L^2(B(x,r_n)),\qquad
    \|f-a_n\|_{L^2(B(x,r_n))}\leq Aq^nr_n
  $$
  for every $n$.
proof:
  Apply the real-valued Morrey--Poincaré estimate on every dyadic ball
  and bound its local $L^p$ differential norm by the norm on
  $\overline B(x,R)$. The identity
  $r_n^{2-2/p}=R^{1-2/p}q^nr_n$ puts the resulting estimate in geometric
  form.
-/
theorem IsLocalW12On.exists_dyadic_poincareCenters_geometric
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    {x : ℂ} {R p : ℝ} (hR : 0 < R) (hp : 2 < p)
    (hclosed : closedBall x R ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall x R))) :
    ∃ A : ℝ,
      A = planarMorreyPoincareConstant.toReal *
        (eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict (closedBall x R))).toReal *
        Real.pi ^ (1 / 2 - 1 / p) *
        R ^ (1 - 2 / p) ∧
      0 ≤ A ∧
      ∃ a : ℕ → ℂ, ∀ n : ℕ,
        let r := R / (2 : ℝ) ^ n
        MemLp (fun z : ℂ ↦ f z - a n) 2
            ((volume : Measure ℂ).restrict (ball x r)) ∧
          (eLpNorm (fun z : ℂ ↦ f z - a n) 2
              ((volume : Measure ℂ).restrict (ball x r))).toReal ≤
            A * (((2 : ℝ)⁻¹) ^ (1 - 2 / p)) ^ n * r := by
  let C : ℝ≥0∞ := planarMorreyPoincareConstant
  let E : ℝ := (eLpNorm df (ENNReal.ofReal p)
    ((volume : Measure ℂ).restrict (closedBall x R))).toReal
  let A : ℝ :=
    C.toReal * E * Real.pi ^ (1 / 2 - 1 / p) *
      R ^ (1 - 2 / p)
  have hA : 0 ≤ A := by
    dsimp [A, E]
    positivity
  refine ⟨A, ?_, hA, ?_⟩
  · rfl
  have hlocal :=
    hW.2.2 (closedBall x R) (isCompact_closedBall x R) hclosed
  have hball_closed (n : ℕ) :
      ball x (R / (2 : ℝ) ^ n) ⊆ closedBall x R := by
    have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hrle : R / (2 : ℝ) ^ n ≤ R :=
      div_le_self hR.le hpow
    exact ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrle)
  have hrpos (n : ℕ) : 0 < R / (2 : ℝ) ^ n :=
    div_pos hR (pow_pos (by norm_num) n)
  have hexists : ∀ n : ℕ, ∃ a : ℂ,
      MemLp (fun z : ℂ ↦ f z - a) 2
          ((volume : Measure ℂ).restrict
            (ball x (R / (2 : ℝ) ^ n))) ∧
        (eLpNorm (fun z : ℂ ↦ f z - a) 2
            ((volume : Measure ℂ).restrict
              (ball x (R / (2 : ℝ) ^ n)))).toReal ≤
          A * (((2 : ℝ)⁻¹) ^ (1 - 2 / p)) ^ n *
            (R / (2 : ℝ) ^ n) := by
    intro n
    let r : ℝ := R / (2 : ℝ) ^ n
    let μ : Measure ℂ := (volume : Measure ℂ).restrict (ball x r)
    have hμ :
        μ ≤ (volume : Measure ℂ).restrict (closedBall x R) := by
      exact Measure.restrict_mono (by simpa [μ, r] using hball_closed n)
        le_rfl
    have hf2 : MemLp f 2 μ :=
      hlocal.1.mono_measure hμ
    have hdfpn : MemLp df (ENNReal.ofReal p) μ :=
      hdfp.mono_measure hμ
    have hweak :
        JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
          (ball x r) f df :=
      hW.2.1.mono_set (by
        simpa [r] using (hball_closed n).trans hclosed)
    obtain ⟨a, hameas, herror⟩ :=
      planarMorreyPoincareConstant_spec.2
        (by simpa [r] using hrpos n) hp hweak hf2 hdfpn
    letI : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.2 (by
        simpa [μ] using (measure_ball_ne_top :
          volume (ball x r) ≠ ∞))
    have hmem_center :
        MemLp (fun z : ℂ ↦ f z - a) 2 μ := by
      exact hf2.sub (memLp_const a)
    refine ⟨a, hmem_center, ?_⟩
    have hnorm_en :
        eLpNorm df (ENNReal.ofReal p) μ ≤
          eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict (closedBall x R)) :=
      eLpNorm_mono_measure df hμ
    have hnorm_real :
        (eLpNorm df (ENNReal.ofReal p) μ).toReal ≤ E := by
      dsimp [E]
      exact ENNReal.toReal_mono hdfp.eLpNorm_ne_top hnorm_en
    calc
      (eLpNorm (fun z : ℂ ↦ f z - a) 2 μ).toReal
          ≤ C.toReal *
              (eLpNorm df (ENNReal.ofReal p) μ).toReal *
              Real.pi ^ (1 / 2 - 1 / p) *
              r ^ (2 - 2 / p) := by
        simpa [μ] using herror
      _ ≤ C.toReal * E * Real.pi ^ (1 / 2 - 1 / p) *
              r ^ (2 - 2 / p) := by
        gcongr
      _ = A * (((2 : ℝ)⁻¹) ^ (1 - 2 / p)) ^ n * r := by
        rw [show r ^ (2 - 2 / p) =
          R ^ (1 - 2 / p) *
            (((2 : ℝ)⁻¹) ^ (1 - 2 / p)) ^ n * r by
              simpa [r] using dyadic_radius_rpow_two_sub_two_div
                (p := p) hR n]
        dsimp [A]
        ring
  choose a ha using hexists
  exact ⟨a, fun n ↦ by simpa using ha n⟩

/--
%%handwave
name:
  Dyadic Morrey centers controlled by the point value
statement:
  Under the hypotheses of the dyadic Morrey estimate, suppose moreover
  that $f$ is continuous at $x$. With
  $q=2^{-(1-2/p)}$, there are $A\geq0$ and constants $a_n$ satisfying
  the geometric Poincaré error bound
  $$
    \|f-a_n\|_{L^2(B(x,R2^{-n}))}\leq Aq^nR2^{-n}
  $$
  and the pointwise bound
  $$
    \|a_n-f(x)\|
      \leq
      \frac{3A}{\sqrt\pi}\frac{q^n}{1-q}.
  $$
  The amplitude is
  $$
    A=\mathcal C_{\mathrm{MP}}\pi^{1/2-1/p}
      \|Df\|_{L^p(\overline B(x,R))}R^{1-2/p}.
  $$
proof:
  Choose the geometrically decaying dyadic Poincaré centers. Since
  $p>2$, their ratio $q$ lies in $[0,1)$. The quantitative
  continuous-point Campanato estimate then gives the second bound.
-/
theorem IsLocalW12On.exists_dyadic_poincareCenters_with_value_bound
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    {x : ℂ} {R p : ℝ} (hfx : ContinuousAt f x)
    (hR : 0 < R) (hp : 2 < p)
    (hclosed : closedBall x R ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall x R))) :
    ∃ A : ℝ,
      A = planarMorreyPoincareConstant.toReal *
        (eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict (closedBall x R))).toReal *
        Real.pi ^ (1 / 2 - 1 / p) *
        R ^ (1 - 2 / p) ∧
      0 ≤ A ∧
      ∃ a : ℕ → ℂ,
        (∀ n : ℕ,
          let r := R / (2 : ℝ) ^ n
          MemLp (fun z : ℂ ↦ f z - a n) 2
              ((volume : Measure ℂ).restrict (ball x r)) ∧
            (eLpNorm (fun z : ℂ ↦ f z - a n) 2
                ((volume : Measure ℂ).restrict (ball x r))).toReal ≤
              A * (((2 : ℝ)⁻¹) ^ (1 - 2 / p)) ^ n * r) ∧
        ∀ n : ℕ,
          ‖a n - f x‖ ≤
            (3 * A / Real.sqrt Real.pi) *
              (((2 : ℝ)⁻¹) ^ (1 - 2 / p)) ^ n /
                (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)) := by
  obtain ⟨A, hAeq, hA, a, ha⟩ :=
    hW.exists_dyadic_poincareCenters_geometric
      hR hp hclosed hdfp
  let q : ℝ := ((2 : ℝ)⁻¹) ^ (1 - 2 / p)
  obtain ⟨hq0, hq1⟩ :=
    dyadic_morrey_ratio_nonneg_and_lt_one hp
  have hmem : ∀ n : ℕ,
      MemLp (fun z : ℂ ↦ f z - a n) 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n))) :=
    fun n ↦ (ha n).1
  have herror : ∀ n : ℕ,
      (eLpNorm (fun z : ℂ ↦ f z - a n) 2
        ((volume : Measure ℂ).restrict
          (ball x (R / (2 : ℝ) ^ n)))).toReal ≤
        A * q ^ n * (R / (2 : ℝ) ^ n) :=
    fun n ↦ by simpa [q] using (ha n).2
  have hvalue :=
    norm_dyadicCenter_sub_value_le_of_continuousAt
      hfx hR (by simpa [q] using hq0) (by simpa [q] using hq1)
        hA hmem herror
  exact ⟨A, hAeq, hA, a, ha,
    fun n ↦ by simpa [q] using hvalue n⟩

/--
%%handwave
name:
  Morrey estimate across two overlapping balls
statement:
  Let $p>2$, $R>0$, and
  $q=2^{-(1-2/p)}$. Suppose $f$ is continuous at $x$ and $y$,
  $\operatorname{dist}(x,y)\leq R/2$, both closed radius-$R$ balls lie
  in $\Omega$, and $Df$ belongs to $L^p$ on both balls. Then
  $$
    \|f(x)-f(y)\|
      \leq
      \left(\frac2{\sqrt\pi}
        +\frac3{\sqrt\pi(1-q)}\right)
      \mathcal C_{\mathrm{MP}}\pi^{1/2-1/p}
      \left(
        \|Df\|_{L^p(\overline B(x,R))}
        +\|Df\|_{L^p(\overline B(y,R))}
      \right)R^{1-2/p}.
  $$
proof:
  Choose the radius-$R$ terms of the dyadic Poincaré-center sequences at
  $x$ and $y$. Each center is within
  $3A/(\sqrt\pi(1-q))$ of the corresponding point value. The common
  half-radius ball compares the two centers by
  $2(A_x+A_y)/\sqrt\pi$. Add these three bounds and substitute the
  explicit amplitudes.
-/
theorem IsLocalW12On.norm_sub_le_morrey_of_two_closedBalls
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    {x y : ℂ} {R p : ℝ}
    (hfx : ContinuousAt f x) (hfy : ContinuousAt f y)
    (hR : 0 < R) (hp : 2 < p)
    (hxy : dist x y ≤ R / 2)
    (hxclosed : closedBall x R ⊆ Ω)
    (hyclosed : closedBall y R ⊆ Ω)
    (hdfx : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall x R)))
    (hdfy : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall y R))) :
    ‖f x - f y‖ ≤
      (2 / Real.sqrt Real.pi +
        3 / (Real.sqrt Real.pi *
          (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
      (planarMorreyPoincareConstant.toReal *
        ((eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict (closedBall x R))).toReal +
          (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict (closedBall y R))).toReal) *
        Real.pi ^ (1 / 2 - 1 / p) *
        R ^ (1 - 2 / p)) := by
  let q : ℝ := ((2 : ℝ)⁻¹) ^ (1 - 2 / p)
  obtain ⟨Ax, hAxeq, hAx, ax, hax, haxvalue⟩ :=
    hW.exists_dyadic_poincareCenters_with_value_bound
      hfx hR hp hxclosed hdfx
  obtain ⟨Ay, hAyeq, hAy, ay, hay, hayvalue⟩ :=
    hW.exists_dyadic_poincareCenters_with_value_bound
      hfy hR hp hyclosed hdfy
  have hmemx :
      MemLp (fun z : ℂ ↦ f z - ax 0) 2
        ((volume : Measure ℂ).restrict (ball x R)) := by
    simpa using (hax 0).1
  have hmemy :
      MemLp (fun z : ℂ ↦ f z - ay 0) 2
        ((volume : Measure ℂ).restrict (ball y R)) := by
    simpa using (hay 0).1
  have herrorx :
      (eLpNorm (fun z : ℂ ↦ f z - ax 0) 2
        ((volume : Measure ℂ).restrict (ball x R))).toReal ≤
          Ax * R := by
    simpa using (hax 0).2
  have herrory :
      (eLpNorm (fun z : ℂ ↦ f z - ay 0) 2
        ((volume : Measure ℂ).restrict (ball y R))).toReal ≤
          Ay * R := by
    simpa using (hay 0).2
  have hpointx :
      ‖ax 0 - f x‖ ≤
        3 * Ax / Real.sqrt Real.pi / (1 - q) := by
    simpa [q] using haxvalue 0
  have hpointy :
      ‖ay 0 - f y‖ ≤
        3 * Ay / Real.sqrt Real.pi / (1 - q) := by
    simpa [q] using hayvalue 0
  have hcenters_scaled :=
    norm_sub_mul_half_radius_mul_sqrt_pi_le_eLpNorm_add_of_dist_le
      (u := f) (x := x) (y := y) (r := R)
      (a := ax 0) (b := ay 0) hR hxy hmemx hmemy
  have hcenters_error :
      ‖ax 0 - ay 0‖ * ((R / 2) * Real.sqrt Real.pi) ≤
        (Ax + Ay) * R := by
    exact hcenters_scaled.trans
      ((add_le_add herrorx herrory).trans_eq (by ring))
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hq1 : q < 1 := by
    simpa [q] using
      (dyadic_morrey_ratio_nonneg_and_lt_one hp).2
  have hqden : 0 < 1 - q := sub_pos.2 hq1
  have hcenters_cancel :
      ‖ax 0 - ay 0‖ * Real.sqrt Real.pi / 2 ≤ Ax + Ay := by
    apply le_of_mul_le_mul_right _ hR
    simpa only [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      using hcenters_error
  have hcenters :
      ‖ax 0 - ay 0‖ ≤
        2 * (Ax + Ay) / Real.sqrt Real.pi := by
    apply (le_div_iff₀ hsqrt).2
    linarith
  calc
    ‖f x - f y‖ =
        ‖(f x - ax 0) + (ax 0 - ay 0) + (ay 0 - f y)‖ := by
      congr 1
      abel
    _ ≤ ‖f x - ax 0‖ + ‖ax 0 - ay 0‖ + ‖ay 0 - f y‖ :=
      norm_add₃_le
    _ ≤ 3 * Ax / Real.sqrt Real.pi / (1 - q) +
          2 * (Ax + Ay) / Real.sqrt Real.pi +
          3 * Ay / Real.sqrt Real.pi / (1 - q) := by
      exact add_le_add
        (add_le_add (by simpa [norm_sub_rev] using hpointx) hcenters)
        hpointy
    _ = (2 / Real.sqrt Real.pi +
          3 / (Real.sqrt Real.pi * (1 - q))) * (Ax + Ay) := by
      field_simp [ne_of_gt hsqrt, ne_of_gt hqden]
      ring
    _ = (2 / Real.sqrt Real.pi +
          3 / (Real.sqrt Real.pi *
            (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
        (planarMorreyPoincareConstant.toReal *
          ((eLpNorm df (ENNReal.ofReal p)
              ((volume : Measure ℂ).restrict (closedBall x R))).toReal +
            (eLpNorm df (ENNReal.ofReal p)
              ((volume : Measure ℂ).restrict (closedBall y R))).toReal) *
          Real.pi ^ (1 / 2 - 1 / p) *
          R ^ (1 - 2 / p)) := by
      rw [hAxeq, hAyeq]
      dsimp [q]
      ring

/--
%%handwave
name:
  Same-ball radial Morrey constant
statement:
  For $p>2$, put $\alpha=1-2/p$ and
  $$
    C_p^{\mathrm{rad}}
      =
      \frac{
        \left(\frac2{\sqrt\pi}
          +\frac3{\sqrt\pi(1-2^{-\alpha})}\right)
        \mathcal C_{\mathrm{MP}}\,2\pi^{1/2-1/p}
        (1/2)^\alpha
      }{
        1-(3/4)^\alpha
      }.
  $$
  This is the constant obtained by summing the Morrey estimates along a
  geometric radial chain contained in one closed ball.
-/
def morreySameBallPointConstant (p : ℝ) : ℝ :=
  ((2 / Real.sqrt Real.pi +
      3 / (Real.sqrt Real.pi *
        (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
    (planarMorreyPoincareConstant.toReal * 2 *
      Real.pi ^ (1 / 2 - 1 / p) *
      (1 / 2 : ℝ) ^ (1 - 2 / p))) /
    (1 - (3 / 4 : ℝ) ^ (1 - 2 / p))

/--
%%handwave
name:
  Radial Morrey estimate using only one closed ball
statement:
  Let $p>2$, $r>0$, and suppose that $f$ is continuous and locally
  $W^{1,2}$ on $\Omega$, with
  $\overline B(c,r)\subset\Omega$ and
  $Df\in L^p(\overline B(c,r))$. Then every
  $x\in\overline B(c,r)$ satisfies
  $$
    |f(c)-f(x)|
      \leq
      C_p^{\mathrm{rad}}\,
      \|Df\|_{L^p(\overline B(c,r))}
      r^{1-2/p}.
  $$
proof:
  Approach $x$ from $c$ along the radial sequence
  $x_n=c+(1-(3/4)^n)(x-c)$. Compare consecutive points on balls of
  radius $\frac12(3/4)^nr$. Both comparison balls remain inside
  $\overline B(c,r)$, so [the two-ball Morrey estimate](lean:JJMath.Quasiconformal.IsLocalW12On.norm_sub_le_morrey_of_two_closedBalls) uses only the $L^p$ energy of the original ball. The increments form a geometric series with ratio $(3/4)^{1-2/p}$, and continuity identifies the limiting value with $f(x)$.
-/
theorem IsLocalW12On.norm_center_sub_le_morrey_on_same_closedBall
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {c x : ℂ} {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hx : x ∈ closedBall c r)
    (hclosed : closedBall c r ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))) :
    ‖f c - f x‖ ≤ morreySameBallPointConstant p *
      (eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict (closedBall c r))).toReal *
      r ^ (1 - 2 / p) := by
  let α : ℝ := 1 - 2 / p
  let q : ℝ := 3 / 4
  let s : ℝ := q ^ α
  let E : ℝ :=
    (eLpNorm df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))).toReal
  let a : ℕ → ℂ := fun n => c + (1 - q ^ n) • (x - c)
  let R : ℕ → ℝ := fun n => (1 / 2 : ℝ) * q ^ n * r
  let A : ℝ :=
    (2 / Real.sqrt Real.pi +
      3 / (Real.sqrt Real.pi *
        (1 - ((2 : ℝ)⁻¹) ^ α))) *
      (planarMorreyPoincareConstant.toReal *
        (2 * E) * Real.pi ^ (1 / 2 - 1 / p) *
        ((1 / 2 : ℝ) ^ α * r ^ α))
  have hp0 : 0 < p := by
    linarith
  have hα : 0 < α := by
    dsimp [α]
    rw [sub_pos, div_lt_one hp0]
    exact hp
  have hq0 : 0 ≤ q := by
    norm_num [q]
  have hq1 : q < 1 := by
    norm_num [q]
  have hs0 : 0 ≤ s :=
    (Real.rpow_pos_of_pos (by norm_num [q]) α).le
  have hs1 : s < 1 := by
    dsimp [s]
    exact Real.rpow_lt_one (by norm_num [q]) hq1 hα
  have hE : 0 ≤ E := ENNReal.toReal_nonneg
  have hR (n : ℕ) : 0 < R n := by
    dsimp [R]
    positivity
  have ha_zero : a 0 = c := by
    simp [a]
  have ha_tendsto : Tendsto a atTop (𝓝 x) := by
    have hpow :
        Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq1
    have hcoef :
        Tendsto (fun n : ℕ => 1 - q ^ n) atTop (𝓝 1) := by
      convert (tendsto_const_nhds.sub hpow) using 1 <;> simp
    have h := (hcoef.smul_const (x - c)).const_add c
    convert h using 1 <;> simp [a]
  have hxc : dist x c ≤ r := by
    simpa [mem_closedBall] using hx
  have hball (n : ℕ) :
      closedBall (a n) (R n) ⊆ closedBall c r := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    have hpow0 : 0 ≤ q ^ n := pow_nonneg hq0 n
    have hpow_le : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1.le
    have hcenter :
        dist (a n) c = (1 - q ^ n) * dist x c := by
      rw [dist_eq_norm]
      simp only [a, add_sub_cancel_left]
      rw [norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg (sub_nonneg.2 hpow_le), dist_eq_norm]
    calc
      dist z c ≤ dist z (a n) + dist (a n) c :=
        dist_triangle _ _ _
      _ ≤ R n + (1 - q ^ n) * dist x c := by
        rw [hcenter]
        gcongr
      _ ≤ R n + (1 - q ^ n) * r := by
        gcongr
      _ ≤ r := by
        dsimp [R, q]
        nlinarith
  have hball_succ (n : ℕ) :
      closedBall (a (n + 1)) (R n) ⊆ closedBall c r := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    have hpow0 : 0 ≤ q ^ n := pow_nonneg hq0 n
    have hpow_le : q ^ (n + 1) ≤ 1 :=
      pow_le_one₀ hq0 hq1.le
    have hcenter :
        dist (a (n + 1)) c =
          (1 - q ^ (n + 1)) * dist x c := by
      rw [dist_eq_norm]
      simp only [a, add_sub_cancel_left]
      rw [norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg (sub_nonneg.2 hpow_le), dist_eq_norm]
    calc
      dist z c ≤
          dist z (a (n + 1)) + dist (a (n + 1)) c :=
        dist_triangle _ _ _
      _ ≤ R n + (1 - q ^ (n + 1)) * dist x c := by
        rw [hcenter]
        gcongr
      _ ≤ R n + (1 - q ^ (n + 1)) * r := by
        gcongr
      _ ≤ r := by
        rw [pow_succ]
        dsimp [R, q]
        nlinarith
  have hdist (n : ℕ) :
      dist (a n) (a (n + 1)) ≤ R n / 2 := by
    have heq :
        dist (a n) (a (n + 1)) =
          (1 / 4 : ℝ) * q ^ n * dist c x := by
      rw [dist_eq_norm]
      simp only [a, add_sub_add_left_eq_sub]
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      have hpow0 : 0 ≤ q ^ n := pow_nonneg hq0 n
      rw [pow_succ]
      have habs :
          |(1 - q ^ n) - (1 - q ^ n * q)| =
            (1 / 4 : ℝ) * q ^ n := by
        rw [abs_of_nonpos]
        · dsimp [q]
          ring
        · dsimp [q]
          nlinarith
      rw [habs, dist_eq_norm, norm_sub_rev]
    rw [heq]
    have hcx : dist c x ≤ r := by
      simpa [dist_comm] using hxc
    have hpow0 : 0 ≤ q ^ n := pow_nonneg hq0 n
    dsimp [R]
    nlinarith
  have hpoint (n : ℕ) : a n ∈ Ω := by
    apply hclosed
    apply hball n
    exact mem_closedBall_self (hR n).le
  have hpoint_succ (n : ℕ) : a (n + 1) ∈ Ω := by
    apply hclosed
    apply hball_succ n
    exact mem_closedBall_self (hR n).le
  have hdf (n : ℕ) :
      MemLp df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (closedBall (a n) (R n))) :=
    hdfp.mono_measure
      (Measure.restrict_mono (hball n) le_rfl)
  have hdf_succ (n : ℕ) :
      MemLp df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (closedBall (a (n + 1)) (R n))) :=
    hdfp.mono_measure
      (Measure.restrict_mono (hball_succ n) le_rfl)
  have hnorm (n : ℕ) :
      (eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (closedBall (a n) (R n)))).toReal ≤ E := by
    dsimp [E]
    exact ENNReal.toReal_mono hdfp.eLpNorm_ne_top
      (eLpNorm_mono_measure df
        (Measure.restrict_mono (hball n) le_rfl))
  have hnorm_succ (n : ℕ) :
      (eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (closedBall (a (n + 1)) (R n)))).toReal ≤ E := by
    dsimp [E]
    exact ENNReal.toReal_mono hdfp.eLpNorm_ne_top
      (eLpNorm_mono_measure df
        (Measure.restrict_mono (hball_succ n) le_rfl))
  have hRpow (n : ℕ) :
      (R n) ^ α =
        (1 / 2 : ℝ) ^ α * r ^ α * s ^ n := by
    dsimp [R]
    rw [Real.mul_rpow
      (mul_nonneg (by norm_num) (pow_nonneg hq0 n)) hr.le]
    rw [Real.mul_rpow
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (pow_nonneg hq0 n)]
    have hpow :
        ((q ^ n) ^ α : ℝ) = (q ^ α) ^ n := by
      calc
        ((q ^ n) ^ α : ℝ) =
            q ^ ((n : ℝ) * α) := by
          rw [← Real.rpow_natCast]
          exact (Real.rpow_mul hq0 (n : ℝ) α).symm
        _ = q ^ (α * (n : ℝ)) := by
          congr 1
          ring
        _ = ((q ^ α) ^ (n : ℝ)) :=
          Real.rpow_mul hq0 α (n : ℝ)
        _ = (q ^ α) ^ n :=
          Real.rpow_natCast _ _
    rw [hpow]
    dsimp [s]
    ring
  have hK0 :
      0 ≤ 2 / Real.sqrt Real.pi +
        3 / (Real.sqrt Real.pi *
          (1 - ((2 : ℝ)⁻¹) ^ α)) := by
    have hqdyadic :=
      (dyadic_morrey_ratio_nonneg_and_lt_one hp).2
    have hsqrt : 0 < Real.sqrt Real.pi :=
      Real.sqrt_pos.2 Real.pi_pos
    have hden :
        0 < 1 - ((2 : ℝ)⁻¹) ^ α := by
      dsimp [α] at hqdyadic ⊢
      linarith
    positivity
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hincrement (n : ℕ) :
      dist (f (a n)) (f (a (n + 1))) ≤ A * s ^ n := by
    have htwo :=
      hW.norm_sub_le_morrey_of_two_closedBalls
        (hcont.continuousAt (hW.1.mem_nhds (hpoint n)))
        (hcont.continuousAt
          (hW.1.mem_nhds (hpoint_succ n)))
        (hR n) hp (hdist n)
        ((hball n).trans hclosed)
        ((hball_succ n).trans hclosed)
        (hdf n) (hdf_succ n)
    have hsum :
        (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall (a n) (R n)))).toReal +
          (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall (a (n + 1)) (R n)))).toReal ≤
            2 * E := by
      linarith [hnorm n, hnorm_succ n]
    rw [dist_eq_norm]
    calc
      ‖f (a n) - f (a (n + 1))‖ ≤
          (2 / Real.sqrt Real.pi +
            3 / (Real.sqrt Real.pi *
              (1 - ((2 : ℝ)⁻¹) ^ α))) *
          (planarMorreyPoincareConstant.toReal *
            ((eLpNorm df (ENNReal.ofReal p)
                ((volume : Measure ℂ).restrict
                  (closedBall (a n) (R n)))).toReal +
              (eLpNorm df (ENNReal.ofReal p)
                ((volume : Measure ℂ).restrict
                  (closedBall
                    (a (n + 1)) (R n)))).toReal) *
            Real.pi ^ (1 / 2 - 1 / p) *
            (R n) ^ α) := by
        simpa [α] using htwo
      _ ≤
          (2 / Real.sqrt Real.pi +
            3 / (Real.sqrt Real.pi *
              (1 - ((2 : ℝ)⁻¹) ^ α))) *
          (planarMorreyPoincareConstant.toReal *
            (2 * E) * Real.pi ^ (1 / 2 - 1 / p) *
            (R n) ^ α) := by
        gcongr
      _ = A * s ^ n := by
        rw [hRpow]
        dsimp [A]
        ring
  have hftendsto :
      Tendsto (fun n => f (a n)) atTop (𝓝 (f x)) :=
    (hcont.continuousAt
      (hW.1.mem_nhds (hclosed hx))).tendsto.comp ha_tendsto
  have hsum :=
    dist_le_of_le_geometric_of_tendsto
      s A hs1 hincrement hftendsto 0
  rw [ha_zero] at hsum
  have hsum' :
      ‖f c - f x‖ ≤ A / (1 - s) := by
    simpa [dist_eq_norm] using hsum
  have hformula :
      A / (1 - s) =
        morreySameBallPointConstant p * E * r ^ α := by
    dsimp [A, morreySameBallPointConstant, s, α]
    ring
  rw [hformula] at hsum'
  simpa [E, α] using hsum'

/--
%%handwave
name:
  Nonnegativity of the same-ball radial Morrey constant
statement:
  If $p>2$, then $C_p^{\mathrm{rad}}\geq0$.
proof:
  The exponent $1-2/p$ is positive. Hence both geometric ratios
  $2^{-(1-2/p)}$ and $(3/4)^{1-2/p}$ are strictly less than one, so all
  factors and both denominators in the definition are nonnegative.
-/
theorem morreySameBallPointConstant_nonneg
    {p : ℝ} (hp : 2 < p) :
    0 ≤ morreySameBallPointConstant p := by
  have hp0 : 0 < p := by
    linarith
  have hα : 0 < 1 - 2 / p := by
    rw [sub_pos, div_lt_one hp0]
    exact hp
  have hqdyadic :=
    (dyadic_morrey_ratio_nonneg_and_lt_one hp).2
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hdyadicden :
      0 < 1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p) :=
    sub_pos.2 hqdyadic
  have hradialden :
      0 < 1 - (3 / 4 : ℝ) ^ (1 - 2 / p) := by
    apply sub_pos.2
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hα
  unfold morreySameBallPointConstant
  positivity

/--
%%handwave
name:
  Same-ball Morrey diameter constant
statement:
  For $p>2$, define
  $$
    C_p^{\mathrm{ball}}=2C_p^{\mathrm{rad}}.
  $$
  The factor two comes from comparing two points through the center of
  the ball.
-/
def morreySameBallDiameterConstant (p : ℝ) : ℝ :=
  2 * morreySameBallPointConstant p

/--
%%handwave
name:
  Same-ball Morrey estimate
statement:
  Let $p>2$, $r>0$, and suppose that $f$ is continuous and locally
  $W^{1,2}$ on $\Omega$, with
  $\overline B(c,r)\subset\Omega$ and
  $Df\in L^p(\overline B(c,r))$. For all
  $x,y\in\overline B(c,r)$,
  $$
    |f(x)-f(y)|
      \leq
      C_p^{\mathrm{ball}}\,
      \|Df\|_{L^p(\overline B(c,r))}
      r^{1-2/p}.
  $$
proof:
  Apply [the radial same-ball estimate](lean:JJMath.Quasiconformal.IsLocalW12On.norm_center_sub_le_morrey_on_same_closedBall) to $x$ and $y$, and use the triangle inequality through $f(c)$.
-/
theorem IsLocalW12On.norm_sub_le_morrey_on_same_closedBall
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {c x y : ℂ} {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r)
    (hclosed : closedBall c r ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))) :
    ‖f x - f y‖ ≤ morreySameBallDiameterConstant p *
      (eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict (closedBall c r))).toReal *
      r ^ (1 - 2 / p) := by
  have hx' :=
    hW.norm_center_sub_le_morrey_on_same_closedBall
      hcont hr hp hx hclosed hdfp
  have hy' :=
    hW.norm_center_sub_le_morrey_on_same_closedBall
      hcont hr hp hy hclosed hdfp
  calc
    ‖f x - f y‖ =
        ‖(f x - f c) + (f c - f y)‖ := by
      congr 1
      abel
    _ ≤ ‖f x - f c‖ + ‖f c - f y‖ :=
      norm_add_le _ _
    _ ≤
        morreySameBallPointConstant p *
            (eLpNorm df (ENNReal.ofReal p)
              ((volume : Measure ℂ).restrict
                (closedBall c r))).toReal *
            r ^ (1 - 2 / p) +
          morreySameBallPointConstant p *
            (eLpNorm df (ENNReal.ofReal p)
              ((volume : Measure ℂ).restrict
                (closedBall c r))).toReal *
            r ^ (1 - 2 / p) :=
      add_le_add (by simpa [norm_sub_rev] using hx') hy'
    _ =
        morreySameBallDiameterConstant p *
          (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall c r))).toReal *
          r ^ (1 - 2 / p) := by
      unfold morreySameBallDiameterConstant
      ring

/--
%%handwave
name:
  Same-ball Morrey diameter bound
statement:
  For a differential field $Df$, center $c$, radius $r$, and exponent
  $p$, define the extended nonnegative diameter majorant
  $$
    \mathcal D_{\mathrm{ball}}(Df;c,r,p)
      =
      \max\!\left\{
        C_p^{\mathrm{ball}}
        \|Df\|_{L^p(\overline B(c,r))}
        r^{1-2/p},0
      \right\}.
  $$
-/
def morreySameBallDiameterBound
    (df : ℂ → ℂ →L[ℝ] ℂ) (c : ℂ) (r p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (morreySameBallDiameterConstant p *
      (eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (closedBall c r))).toReal *
      r ^ (1 - 2 / p))

/--
%%handwave
name:
  Same-ball image-diameter estimate
statement:
  Let $p>2$, $r>0$, and suppose that $f$ is continuous and locally
  $W^{1,2}$ on $\Omega$, with
  $\overline B(c,r)\subset\Omega$ and
  $Df\in L^p(\overline B(c,r))$. Then
  $$
    \operatorname{diam} f(\overline B(c,r))
      \leq
      \mathcal D_{\mathrm{ball}}(Df;c,r,p).
  $$
proof:
  Apply [the same-ball point-pair estimate](lean:JJMath.Quasiconformal.IsLocalW12On.norm_sub_le_morrey_on_same_closedBall) to every two points of the closed ball and use the pairwise characterization of extended diameter.
-/
theorem IsLocalW12On.ediam_image_closedBall_le_morrey_sameBall
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {c : ℂ} {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hclosed : closedBall c r ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))) :
    ediam (f '' closedBall c r) ≤
      morreySameBallDiameterBound df c r p := by
  unfold morreySameBallDiameterBound
  rw [Metric.ediam_image_le_iff]
  intro x hx y hy
  rw [edist_dist, dist_eq_norm]
  exact ENNReal.ofReal_le_ofReal
    (hW.norm_sub_le_morrey_on_same_closedBall
      hcont hr hp hx hy hclosed hdfp)

/--
%%handwave
name:
  Area of an image controlled from the same closed ball
statement:
  Under the hypotheses of the same-ball image-diameter estimate,
  $$
    |f(\overline B(c,r))|
      \leq
      \mathcal D_{\mathrm{ball}}(Df;c,r,p)^2.
  $$
proof:
  The image of the closed ball is nonempty and compact. Its area is at
  most the square of the extended diameter of its frontier, which is at
  most the square of the image diameter. Apply [the same-ball diameter estimate](lean:JJMath.Quasiconformal.IsLocalW12On.ediam_image_closedBall_le_morrey_sameBall).
-/
theorem IsLocalW12On.volume_image_closedBall_le_morrey_sameBall
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {c : ℂ} {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hclosed : closedBall c r ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))) :
    volume (f '' closedBall c r) ≤
      morreySameBallDiameterBound df c r p ^ 2 := by
  have himage :
      IsCompact (f '' closedBall c r) :=
    (isCompact_closedBall c r).image_of_continuousOn
      (hcont.mono hclosed)
  have hne : (f '' closedBall c r).Nonempty :=
    ⟨f c, c, by simp [hr.le], rfl⟩
  have hvolume :=
    complex_volume_le_ediam_frontier_sq himage hne
  have hfrontier :
      ediam (frontier (f '' closedBall c r)) ≤
        ediam (f '' closedBall c r) :=
    Metric.ediam_mono himage.isClosed.frontier_subset
  have hdiam :=
    hW.ediam_image_closedBall_le_morrey_sameBall
      hcont hr hp hclosed hdfp
  exact hvolume.trans
    ((pow_le_pow_left₀ (by simp) hfrontier 2).trans
      (pow_le_pow_left₀ (by simp) hdiam 2))

/--
%%handwave
name:
  Factorization of the same-ball Morrey diameter bound
statement:
  Let $p>2$, $r>0$, and suppose
  $Df\in L^p(\overline B(c,r))$. Then
  $$
    \mathcal D_{\mathrm{ball}}(Df;c,r,p)
      =
      C_p^{\mathrm{ball}}\,
      \|Df\|_{L^p(\overline B(c,r))}
      r^{1-2/p}.
  $$
  The equality is in the extended nonnegative reals.
proof:
  The constant and the real power are nonnegative, and the local
  $L^p$ seminorm is finite. Thus each real factor may be converted
  separately to an extended nonnegative real.
-/
theorem morreySameBallDiameterBound_eq_constant_mul
    (df : ℂ → ℂ →L[ℝ] ℂ) (c : ℂ) {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hdf : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))) :
    morreySameBallDiameterBound df c r p =
      ENNReal.ofReal (morreySameBallDiameterConstant p) *
        eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict (closedBall c r)) *
        ENNReal.ofReal r ^ (1 - 2 / p) := by
  have hconst :
      0 ≤ morreySameBallDiameterConstant p := by
    unfold morreySameBallDiameterConstant
    exact mul_nonneg (by norm_num)
      (morreySameBallPointConstant_nonneg hp)
  have hnormtop :
      eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (closedBall c r)) ≠ ⊤ :=
    hdf.eLpNorm_lt_top.ne
  unfold morreySameBallDiameterBound
  rw [ENNReal.ofReal_mul
    (mul_nonneg hconst ENNReal.toReal_nonneg)]
  rw [ENNReal.ofReal_mul hconst]
  rw [ENNReal.ofReal_toReal hnormtop]
  rw [← ENNReal.ofReal_rpow_of_pos hr]

/--
%%handwave
name:
  Hölder factorization of the squared same-ball Morrey bound
statement:
  Under the same hypotheses,
  $$
    \mathcal D_{\mathrm{ball}}(Df;c,r,p)^2
      =
      (C_p^{\mathrm{ball}})^2
      \bigl(r^2\bigr)^{1-2/p}
      \left(
        \|Df\|_{L^p(\overline B(c,r))}^{p}
      \right)^{2/p}.
  $$
proof:
  Apply [the factorization of the same-ball diameter bound](lean:JJMath.Quasiconformal.morreySameBallDiameterBound_eq_constant_mul), then use the identities $(r^{1-2/p})^2=(r^2)^{1-2/p}$ and $(E^p)^{2/p}=E^2$.
-/
theorem morreySameBallDiameterBound_sq_eq_holderFactors
    (df : ℂ → ℂ →L[ℝ] ℂ) (c : ℂ) {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hdf : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))) :
    morreySameBallDiameterBound df c r p ^ 2 =
      ENNReal.ofReal (morreySameBallDiameterConstant p) ^ 2 *
        (ENNReal.ofReal r ^ 2) ^ (1 - 2 / p) *
        (eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict
            (closedBall c r)) ^ p) ^ (2 / p) := by
  rw [morreySameBallDiameterBound_eq_constant_mul
    df c hr hp hdf]
  let C : ℝ≥0∞ :=
    ENNReal.ofReal (morreySameBallDiameterConstant p)
  let E : ℝ≥0∞ :=
    eLpNorm df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))
  let X : ℝ≥0∞ := ENNReal.ofReal r
  have hp0 : 0 < p := by
    linarith
  have hX :
      (X ^ 2) ^ (1 - 2 / p) =
        (X ^ (1 - 2 / p)) ^ 2 := by
    calc
      (X ^ 2) ^ (1 - 2 / p) =
          X ^ ((2 : ℝ) * (1 - 2 / p)) :=
        (ENNReal.rpow_natCast_mul X 2
          (1 - 2 / p)).symm
      _ = X ^ ((1 - 2 / p) * (2 : ℝ)) := by
        ring_nf
      _ = (X ^ (1 - 2 / p)) ^ (2 : ℝ) :=
        ENNReal.rpow_mul _ _ _
      _ = (X ^ (1 - 2 / p)) ^ 2 :=
        ENNReal.rpow_natCast _ 2
  have hE :
      (E ^ p) ^ (2 / p) = E ^ 2 := by
    calc
      (E ^ p) ^ (2 / p) = E ^ (p * (2 / p)) :=
        (ENNReal.rpow_mul _ _ _).symm
      _ = E ^ (2 : ℝ) := by
        congr 1
        field_simp
      _ = E ^ 2 :=
        ENNReal.rpow_natCast _ 2
  change
    (C * E * X ^ (1 - 2 / p)) ^ 2 =
      C ^ 2 * (X ^ 2) ^ (1 - 2 / p) *
        (E ^ p) ^ (2 / p)
  rw [hX, hE]
  ring

/--
%%handwave
name:
  Weighted Morrey product bounded by the sum
statement:
  Let $p>2$ and let $w,e\in[0,\infty)$ be finite. Then
  $$
    w^{1-2/p}e^{2/p}\leq w+e.
  $$
proof:
  Put $a=1-2/p$ and $b=2/p$. Both exponents are positive and
  $a+b=1$. Since $w,e\leq w+e$, monotonicity of real powers gives
  $w^ae^b\leq(w+e)^{a+b}=w+e$; the zero case is immediate.
-/
theorem ennreal_rpow_one_sub_two_div_mul_rpow_two_div_le_add
    {w e : ℝ≥0∞} {p : ℝ} (hp : 2 < p)
    (hw : w ≠ ⊤) (he : e ≠ ⊤) :
    w ^ (1 - 2 / p) * e ^ (2 / p) ≤ w + e := by
  let a : ℝ := 1 - 2 / p
  let b : ℝ := 2 / p
  let m : ℝ≥0∞ := w + e
  have hp0 : 0 < p := by
    linarith
  have ha : 0 < a := by
    dsimp [a]
    rw [sub_pos, div_lt_one hp0]
    exact hp
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hab : a + b = 1 := by
    dsimp [a, b]
    ring
  have hmtop : m ≠ ⊤ := by
    dsimp [m]
    exact ENNReal.add_ne_top.2 ⟨hw, he⟩
  rw [show 1 - 2 / p = a by rfl,
    show 2 / p = b by rfl]
  by_cases hm0 : m = 0
  · have hw0 : w = 0 := by
      apply le_antisymm _ bot_le
      simpa [m, hm0] using
        (show w ≤ m from le_add_right le_rfl)
    have he0 : e = 0 := by
      apply le_antisymm _ bot_le
      simpa [m, hm0] using
        (show e ≤ m from le_add_left le_rfl)
    rw [hw0, he0, ENNReal.zero_rpow_of_pos ha,
      ENNReal.zero_rpow_of_pos hb]
    simp
  · calc
      w ^ a * e ^ b ≤ m ^ a * m ^ b := by
        gcongr
        · exact le_add_right le_rfl
        · exact le_add_left le_rfl
      _ = m ^ (a + b) :=
        (ENNReal.rpow_add a b hm0 hmtop).symm
      _ = m := by
        rw [hab, ENNReal.rpow_one]
      _ = w + e := rfl

/--
%%handwave
name:
  Interior Morrey estimate from one enclosing ball
statement:
  Let $p>2$, $r>0$, and
  $q=2^{-(1-2/p)}$. Suppose $f$ is continuous on $\Omega$,
  $\overline B(c,5r)\subset\Omega$, and
  $Df\in L^p(\overline B(c,5r))$. For
  $x,y\in\overline B(c,r)$,
  $$
    \|f(x)-f(y)\|
      \leq
      \left(\frac2{\sqrt\pi}
        +\frac3{\sqrt\pi(1-q)}\right)
      \mathcal C_{\mathrm{MP}}\,
      2\|Df\|_{L^p(\overline B(c,5r))}
      \pi^{1/2-1/p}
      (2\operatorname{dist}(x,y))^{1-2/p}.
  $$
proof:
  If $x=y$ the claim is immediate. Otherwise put
  $R=2\operatorname{dist}(x,y)$. Since
  $x,y\in\overline B(c,r)$, both closed radius-$R$ balls lie in
  $\overline B(c,5r)$. Restrict the enclosing $L^p$ bound to these two
  balls and apply the overlapping-ball Morrey estimate. Each local
  differential norm is at most the enclosing norm.
-/
theorem IsLocalW12On.norm_sub_le_morrey_on_closedBall
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {c x y : ℂ} {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r)
    (hclosed : closedBall c (5 * r) ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c (5 * r)))) :
    ‖f x - f y‖ ≤
      (2 / Real.sqrt Real.pi +
        3 / (Real.sqrt Real.pi *
          (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
      (planarMorreyPoincareConstant.toReal *
        (2 * (eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict
            (closedBall c (5 * r)))).toReal) *
        Real.pi ^ (1 / 2 - 1 / p) *
        (2 * dist x y) ^ (1 - 2 / p)) := by
  let q : ℝ := ((2 : ℝ)⁻¹) ^ (1 - 2 / p)
  let K : ℝ :=
    2 / Real.sqrt Real.pi +
      3 / (Real.sqrt Real.pi * (1 - q))
  let E : ℝ :=
    (eLpNorm df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c (5 * r)))).toReal
  obtain ⟨hq0, hq1⟩ :=
    dyadic_morrey_ratio_nonneg_and_lt_one hp
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hqden : 0 < 1 - q := by
    dsimp [q]
    linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hE : 0 ≤ E := ENNReal.toReal_nonneg
  by_cases hxeq : x = y
  · subst y
    rw [sub_self, norm_zero]
    positivity
  have hd : 0 < dist x y := dist_pos.2 hxeq
  let R : ℝ := 2 * dist x y
  have hR : 0 < R := mul_pos (by norm_num) hd
  have hxc : dist x c ≤ r := by
    simpa [mem_closedBall] using hx
  have hyc : dist y c ≤ r := by
    simpa [mem_closedBall] using hy
  have hdle : dist x y ≤ 2 * r := by
    calc
      dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hxc (by simpa [dist_comm] using hyc)
      _ = 2 * r := by ring
  have hRle : R ≤ 4 * r := by
    dsimp [R]
    linarith
  have hxglobal : closedBall x R ⊆ closedBall c (5 * r) := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    calc
      dist z c ≤ dist z x + dist x c := dist_triangle _ _ _
      _ ≤ R + r := add_le_add hz hxc
      _ ≤ 5 * r := by linarith
  have hyglobal : closedBall y R ⊆ closedBall c (5 * r) := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    calc
      dist z c ≤ dist z y + dist y c := dist_triangle _ _ _
      _ ≤ R + r := add_le_add hz hyc
      _ ≤ 5 * r := by linarith
  have hsmall : closedBall c r ⊆ closedBall c (5 * r) :=
    closedBall_subset_closedBall (by linarith)
  have hxΩ : x ∈ Ω := hclosed (hsmall hx)
  have hyΩ : y ∈ Ω := hclosed (hsmall hy)
  have hfx : ContinuousAt f x :=
    hcont.continuousAt (hW.1.mem_nhds hxΩ)
  have hfy : ContinuousAt f y :=
    hcont.continuousAt (hW.1.mem_nhds hyΩ)
  have hdfx : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall x R)) :=
    hdfp.mono_measure (Measure.restrict_mono hxglobal le_rfl)
  have hdfy : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall y R)) :=
    hdfp.mono_measure (Measure.restrict_mono hyglobal le_rfl)
  have hEx :
      (eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict (closedBall x R))).toReal ≤ E := by
    dsimp [E]
    exact ENNReal.toReal_mono hdfp.eLpNorm_ne_top
      (eLpNorm_mono_measure df
        (Measure.restrict_mono hxglobal le_rfl))
  have hEy :
      (eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict (closedBall y R))).toReal ≤ E := by
    dsimp [E]
    exact ENNReal.toReal_mono hdfp.eLpNorm_ne_top
      (eLpNorm_mono_measure df
        (Measure.restrict_mono hyglobal le_rfl))
  have htwo :=
    hW.norm_sub_le_morrey_of_two_closedBalls
      hfx hfy hR hp (by dsimp [R]; linarith)
        (hxglobal.trans hclosed) (hyglobal.trans hclosed) hdfx hdfy
  have hsum :
      (eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict (closedBall x R))).toReal +
        (eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict (closedBall y R))).toReal ≤
          2 * E := by
    linarith
  calc
    ‖f x - f y‖ ≤
        K * (planarMorreyPoincareConstant.toReal *
          ((eLpNorm df (ENNReal.ofReal p)
              ((volume : Measure ℂ).restrict (closedBall x R))).toReal +
            (eLpNorm df (ENNReal.ofReal p)
              ((volume : Measure ℂ).restrict (closedBall y R))).toReal) *
          Real.pi ^ (1 / 2 - 1 / p) *
          R ^ (1 - 2 / p)) := by
      simpa [K, q] using htwo
    _ ≤ K * (planarMorreyPoincareConstant.toReal *
          (2 * E) * Real.pi ^ (1 / 2 - 1 / p) *
          R ^ (1 - 2 / p)) := by
      gcongr
    _ = (2 / Real.sqrt Real.pi +
          3 / (Real.sqrt Real.pi *
            (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
        (planarMorreyPoincareConstant.toReal *
          (2 * (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall c (5 * r)))).toReal) *
          Real.pi ^ (1 / 2 - 1 / p) *
          (2 * dist x y) ^ (1 - 2 / p)) := by
      rfl

/--
%%handwave
name:
  Morrey diameter bound of a planar ball
statement:
  For a differential field $Df$, a center $c$, a radius $r$, and an
  exponent $p$, define
  $$
    \mathcal D(Df;c,r,p)=
      \left(\frac2{\sqrt\pi}
        +\frac3{\sqrt\pi(1-2^{-(1-2/p)})}\right)
      \mathcal C_{\mathrm{MP}}\,
      2\|Df\|_{L^p(\overline B(c,5r))}
      \pi^{1/2-1/p}(4r)^{1-2/p}.
  $$
  It is regarded as an extended nonnegative real.
-/
def morreyBallDiameterBound
    (df : ℂ → ℂ →L[ℝ] ℂ) (c : ℂ) (r p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((2 / Real.sqrt Real.pi +
      3 / (Real.sqrt Real.pi *
        (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
    (planarMorreyPoincareConstant.toReal *
      (2 * (eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (closedBall c (5 * r)))).toReal) *
      Real.pi ^ (1 / 2 - 1 / p) *
      (4 * r) ^ (1 - 2 / p)))

/--
%%handwave
name:
  Local image-diameter estimate above the planar dimension
statement:
  Let $p>2$, $r>0$, and
  $q=2^{-(1-2/p)}$. Suppose $f$ is continuous on $\Omega$,
  $\overline B(c,5r)\subset\Omega$, and
  $Df\in L^p(\overline B(c,5r))$. Then
  $$
    \operatorname{diam} f(\overline B(c,r))
      \leq
      \left(\frac2{\sqrt\pi}
        +\frac3{\sqrt\pi(1-q)}\right)
      \mathcal C_{\mathrm{MP}}\,
      2\|Df\|_{L^p(\overline B(c,5r))}
      \pi^{1/2-1/p}(4r)^{1-2/p}.
  $$
  The diameter is the extended metric diameter.
proof:
  Apply the interior Morrey estimate to every two points of the closed
  ball. Their distance is at most $2r$, so
  $2\operatorname{dist}(x,y)\leq4r$; monotonicity of the positive real
  power gives the uniform bound. The pairwise estimate is exactly the
  characterization of extended image diameter.
-/
theorem IsLocalW12On.ediam_image_closedBall_le_morrey
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {c : ℂ} {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hclosed : closedBall c (5 * r) ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c (5 * r)))) :
    ediam (f '' closedBall c r) ≤
      morreyBallDiameterBound df c r p := by
  unfold morreyBallDiameterBound
  rw [Metric.ediam_image_le_iff]
  intro x hx y hy
  have hpoint :=
    hW.norm_sub_le_morrey_on_closedBall
      hcont hr hp hx hy hclosed hdfp
  have hxc : dist x c ≤ r := by
    simpa [mem_closedBall] using hx
  have hyc : dist y c ≤ r := by
    simpa [mem_closedBall] using hy
  have hdle : 2 * dist x y ≤ 4 * r := by
    have hdist :
        dist x y ≤ 2 * r := by
      calc
        dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
        _ ≤ r + r := add_le_add hxc (by simpa [dist_comm] using hyc)
        _ = 2 * r := by ring
    linarith
  have hexponent : 0 ≤ 1 - 2 / p := by
    have hp0 : 0 < p := by linarith
    rw [sub_nonneg, div_le_one hp0]
    exact hp.le
  have hpower :
      (2 * dist x y) ^ (1 - 2 / p) ≤
        (4 * r) ^ (1 - 2 / p) :=
    Real.rpow_le_rpow (by positivity) hdle hexponent
  have hq1 :
      ((2 : ℝ)⁻¹) ^ (1 - 2 / p) < 1 :=
    (dyadic_morrey_ratio_nonneg_and_lt_one hp).2
  have hK :
      0 ≤ 2 / Real.sqrt Real.pi +
        3 / (Real.sqrt Real.pi *
          (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p))) := by
    have hsqrt : 0 < Real.sqrt Real.pi :=
      Real.sqrt_pos.2 Real.pi_pos
    have hden :
        0 < 1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p) :=
      sub_pos.2 hq1
    positivity
  have hinner :
      planarMorreyPoincareConstant.toReal *
          (2 * (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall c (5 * r)))).toReal) *
          Real.pi ^ (1 / 2 - 1 / p) *
          (2 * dist x y) ^ (1 - 2 / p) ≤
        planarMorreyPoincareConstant.toReal *
          (2 * (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall c (5 * r)))).toReal) *
          Real.pi ^ (1 / 2 - 1 / p) *
          (4 * r) ^ (1 - 2 / p) := by
    gcongr
  have hreal :
      ‖f x - f y‖ ≤
        (2 / Real.sqrt Real.pi +
          3 / (Real.sqrt Real.pi *
            (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
        (planarMorreyPoincareConstant.toReal *
          (2 * (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall c (5 * r)))).toReal) *
          Real.pi ^ (1 / 2 - 1 / p) *
          (4 * r) ^ (1 - 2 / p)) := by
    exact hpoint.trans (mul_le_mul_of_nonneg_left hinner hK)
  rw [edist_dist, dist_eq_norm]
  exact ENNReal.ofReal_le_ofReal hreal

/--
%%handwave
name:
  Area of one Morrey-controlled ball image
statement:
  Under the hypotheses of the local image-diameter estimate, put
  $$
    D=
      \left(\frac2{\sqrt\pi}
        +\frac3{\sqrt\pi(1-2^{-(1-2/p)})}\right)
      \mathcal C_{\mathrm{MP}}\,
      2\|Df\|_{L^p(\overline B(c,5r))}
      \pi^{1/2-1/p}(4r)^{1-2/p}.
  $$
  Then
  $$
    |f(\overline B(c,r))|\leq D^2.
  $$
proof:
  The closed-ball image is nonempty and compact by continuity. Planar
  volume is bounded by the squared diameter of its frontier; because the
  image is closed, that frontier lies in the image itself. Apply the
  local image-diameter estimate and square the resulting bound.
-/
theorem IsLocalW12On.volume_image_closedBall_le_morrey
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {c : ℂ} {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hclosed : closedBall c (5 * r) ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c (5 * r)))) :
    volume (f '' closedBall c r) ≤
      (morreyBallDiameterBound df c r p) ^ 2 := by
  have hsmall : closedBall c r ⊆ closedBall c (5 * r) :=
    closedBall_subset_closedBall (by linarith)
  have hballΩ : closedBall c r ⊆ Ω :=
    hsmall.trans hclosed
  have himage :
      IsCompact (f '' closedBall c r) :=
    (isCompact_closedBall c r).image_of_continuousOn
      (hcont.mono hballΩ)
  have hne : (f '' closedBall c r).Nonempty := by
    exact ⟨f c, c, by simp [hr.le], rfl⟩
  have hvolume :=
    complex_volume_le_ediam_frontier_sq himage hne
  have hfrontier :
      ediam (frontier (f '' closedBall c r)) ≤
        ediam (f '' closedBall c r) :=
    Metric.ediam_mono himage.isClosed.frontier_subset
  have himage_diam :=
    hW.ediam_image_closedBall_le_morrey
      hcont hr hp hclosed hdfp
  exact hvolume.trans
    ((pow_le_pow_left₀ (by simp) hfrontier 2).trans
      (pow_le_pow_left₀ (by simp) himage_diam 2))

/--
%%handwave
name:
  Image area under a finite Morrey ball cover
statement:
  Let $p>2$ and suppose $f$ is continuous and locally
  $W^{1,2}$ on $\Omega$. If finitely many positive-radius closed balls
  $\overline B(c_i,r_i)$ cover $K$, every
  $\overline B(c_i,5r_i)$ lies in $\Omega$, and
  $Df\in L^p(\overline B(c_i,5r_i))$, then
  $$
    |f(K)|
      \leq
      \sum_i \mathcal D(Df;c_i,r_i,p)^2.
  $$
proof:
  The image of $K$ is contained in the union of the images of the
  covering balls. Use countable subadditivity, which is a finite sum here,
  and apply the one-ball Morrey image-area estimate to every summand.
-/
theorem IsLocalW12On.volume_image_of_subset_iUnion_closedBalls_le_morrey
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (r : ι → ℝ) {p : ℝ} (hp : 2 < p)
    (hr : ∀ i, 0 < r i)
    (hclosed : ∀ i, closedBall (c i) (5 * r i) ⊆ Ω)
    (hdfp : ∀ i, MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict
        (closedBall (c i) (5 * r i))))
    (K : Set ℂ)
    (hcover : K ⊆ ⋃ i, closedBall (c i) (r i)) :
    volume (f '' K) ≤
      ∑ i, (morreyBallDiameterBound df (c i) (r i) p) ^ 2 := by
  have himage :
      f '' K ⊆ ⋃ i, f '' closedBall (c i) (r i) := by
    rintro w ⟨z, hz, rfl⟩
    rcases Set.mem_iUnion.mp (hcover hz) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨z, hi, rfl⟩⟩
  refine (measure_mono himage).trans ((measure_iUnion_le _).trans ?_)
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro i hi
  exact hW.volume_image_closedBall_le_morrey
    hcont (hr i) hp (hclosed i) (hdfp i)

/--
%%handwave
name:
  Exponent-dependent constant in the planar Morrey diameter bound
statement:
  For $p>2$, put
  $$
    A_p=
      \left(\frac2{\sqrt\pi}
        +\frac3{\sqrt\pi(1-2^{-(1-2/p)})}\right)
      \mathcal C_{\mathrm{MP}}\,2\pi^{1/2-1/p}.
  $$
-/
def morreyBallDiameterConstant (p : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi +
      3 / (Real.sqrt Real.pi *
        (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
    (planarMorreyPoincareConstant.toReal * 2 *
      Real.pi ^ (1 / 2 - 1 / p))

/--
%%handwave
name:
  Factorization of the planar Morrey diameter bound
statement:
  Let $p>2$, $r>0$, and suppose
  $Df\in L^p(\overline B(c,5r))$. Then the diameter majorant factors as
  $$
    \mathcal D(Df;c,r,p)
      =A_p\,
        \|Df\|_{L^p(\overline B(c,5r))}
        (4r)^{1-2/p}.
  $$
  The equality is in the extended nonnegative reals.
proof:
  Regroup the defining real factors. The local $L^p$ seminorm is finite,
  so converting it to a real number and back does not change it.
-/
theorem morreyBallDiameterBound_eq_constant_mul
    (df : ℂ → ℂ →L[ℝ] ℂ) (c : ℂ) {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hdf : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c (5 * r)))) :
    morreyBallDiameterBound df c r p =
      ENNReal.ofReal (morreyBallDiameterConstant p) *
        eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict (closedBall c (5 * r))) *
        ENNReal.ofReal (4 * r) ^ (1 - 2 / p) := by
  have hq1 :
      ((2 : ℝ)⁻¹) ^ (1 - 2 / p) < 1 :=
    (dyadic_morrey_ratio_nonneg_and_lt_one hp).2
  have hfirst :
      0 ≤ 2 / Real.sqrt Real.pi +
        3 / (Real.sqrt Real.pi *
          (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p))) := by
    have hsqrt : 0 < Real.sqrt Real.pi :=
      Real.sqrt_pos.2 Real.pi_pos
    have hden :
        0 < 1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p) :=
      sub_pos.2 hq1
    positivity
  have hsecond :
      0 ≤ planarMorreyPoincareConstant.toReal * 2 *
        Real.pi ^ (1 / 2 - 1 / p) := by
    positivity
  have hconst :
      0 ≤ morreyBallDiameterConstant p :=
    mul_nonneg hfirst hsecond
  have hnormtop :
      eLpNorm df (ENNReal.ofReal p)
        ((volume : Measure ℂ).restrict
          (closedBall c (5 * r))) ≠ ⊤ :=
    hdf.eLpNorm_lt_top.ne
  unfold morreyBallDiameterBound
  rw [show
      (2 / Real.sqrt Real.pi +
        3 / (Real.sqrt Real.pi *
          (1 - ((2 : ℝ)⁻¹) ^ (1 - 2 / p)))) *
        (planarMorreyPoincareConstant.toReal *
          (2 * (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall c (5 * r)))).toReal) *
          Real.pi ^ (1 / 2 - 1 / p) *
          (4 * r) ^ (1 - 2 / p)) =
        morreyBallDiameterConstant p *
          (eLpNorm df (ENNReal.ofReal p)
            ((volume : Measure ℂ).restrict
              (closedBall c (5 * r)))).toReal *
          (4 * r) ^ (1 - 2 / p) by
      unfold morreyBallDiameterConstant
      ring]
  rw [ENNReal.ofReal_mul
    (mul_nonneg hconst ENNReal.toReal_nonneg)]
  rw [ENNReal.ofReal_mul hconst]
  rw [ENNReal.ofReal_toReal hnormtop]
  rw [← ENNReal.ofReal_rpow_of_pos
    (by positivity : 0 < 4 * r)]

/--
%%handwave
name:
  Hölder factorization of the squared Morrey diameter bound
statement:
  Under the same hypotheses, the square of the diameter majorant is
  $$
    \mathcal D(Df;c,r,p)^2
      =A_p^2
        \bigl((4r)^2\bigr)^{1-2/p}
        \left(
          \|Df\|_{L^p(\overline B(c,5r))}^{p}
        \right)^{2/p}.
  $$
proof:
  Apply [the factorization of the diameter majorant](lean:JJMath.Quasiconformal.morreyBallDiameterBound_eq_constant_mul). The identities $((4r)^{1-2/p})^2=((4r)^2)^{1-2/p}$ and $(E^p)^{2/p}=E^2$ give the two Hölder factors.
-/
theorem morreyBallDiameterBound_sq_eq_holderFactors
    (df : ℂ → ℂ →L[ℝ] ℂ) (c : ℂ) {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hdf : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c (5 * r)))) :
    morreyBallDiameterBound df c r p ^ 2 =
      ENNReal.ofReal (morreyBallDiameterConstant p) ^ 2 *
        (ENNReal.ofReal (4 * r) ^ 2) ^ (1 - 2 / p) *
        (eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict
            (closedBall c (5 * r))) ^ p) ^ (2 / p) := by
  rw [morreyBallDiameterBound_eq_constant_mul
    df c hr hp hdf]
  let C : ℝ≥0∞ :=
    ENNReal.ofReal (morreyBallDiameterConstant p)
  let E : ℝ≥0∞ :=
    eLpNorm df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c (5 * r)))
  let X : ℝ≥0∞ := ENNReal.ofReal (4 * r)
  have hp0 : 0 < p := by
    linarith
  have hX :
      (X ^ 2) ^ (1 - 2 / p) =
        (X ^ (1 - 2 / p)) ^ 2 := by
    calc
      (X ^ 2) ^ (1 - 2 / p) =
          X ^ ((2 : ℝ) * (1 - 2 / p)) :=
        (ENNReal.rpow_natCast_mul X 2 (1 - 2 / p)).symm
      _ = X ^ ((1 - 2 / p) * (2 : ℝ)) := by
        ring_nf
      _ = (X ^ (1 - 2 / p)) ^ (2 : ℝ) :=
        ENNReal.rpow_mul _ _ _
      _ = (X ^ (1 - 2 / p)) ^ 2 :=
        ENNReal.rpow_natCast _ 2
  have hE :
      (E ^ p) ^ (2 / p) = E ^ 2 := by
    calc
      (E ^ p) ^ (2 / p) = E ^ (p * (2 / p)) :=
        (ENNReal.rpow_mul _ _ _).symm
      _ = E ^ (2 : ℝ) := by
        congr 1
        field_simp
      _ = E ^ 2 :=
        ENNReal.rpow_natCast _ 2
  change
    (C * E * X ^ (1 - 2 / p)) ^ 2 =
      C ^ 2 * (X ^ 2) ^ (1 - 2 / p) *
        (E ^ p) ^ (2 / p)
  rw [hX, hE]
  ring

/--
%%handwave
name:
  Local $L^p$ energy measure
statement:
  For a differential field $Df$ and a real exponent $p$, define the
  weighted measure
  $$
    \nu_{p,Df}(A)=\int_A\lVert Df(z)\rVert^p\,dz.
  $$
-/
def lpEnergyMeasure
    (df : ℂ → ℂ →L[ℝ] ℂ) (p : ℝ) : Measure ℂ :=
  volume.withDensity fun z => ‖df z‖ₑ ^ p

/--
%%handwave
name:
  $L^p$ energy as the $p$th power of the local seminorm
statement:
  If $p>0$ and $A\subset\mathbb C$ is measurable, then
  $$
    \nu_{p,Df}(A)=\|Df\|_{L^p(A)}^p.
  $$
proof:
  Evaluate the weighted measure on $A$ and use the defining integral
  formula for the $L^p$ seminorm. Raising its $p$th-root expression to the
  power $p$ recovers the energy integral.
-/
theorem lpEnergyMeasure_apply_eq_eLpNorm_rpow
    (df : ℂ → ℂ →L[ℝ] ℂ) {p : ℝ} (hp : 0 < p)
    {A : Set ℂ} (hA : MeasurableSet A) :
    lpEnergyMeasure df p A =
      eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict A) ^ p := by
  rw [lpEnergyMeasure, withDensity_apply]
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
    · rw [ENNReal.toReal_ofReal hp.le]
      rw [← ENNReal.rpow_mul]
      have hmul : 1 / p * p = 1 := by
        field_simp
      rw [hmul, ENNReal.rpow_one]
    · rw [ne_eq, ENNReal.ofReal_eq_zero]
      exact not_le_of_gt hp
    · exact ENNReal.ofReal_ne_top
  · exact hA

/--
%%handwave
name:
  $L^p$ energy of a closed ball
statement:
  If $p>0$, then for every closed ball $\overline B(c,r)$,
  $$
    \nu_{p,Df}(\overline B(c,r))
      =\|Df\|_{L^p(\overline B(c,r))}^{p}.
  $$
proof:
  Evaluate the weighted measure on the measurable closed ball and use the
  defining integral formula for the $L^p$ seminorm. Raising its
  $p$th-root expression to the power $p$ recovers the energy integral.
-/
theorem lpEnergyMeasure_closedBall_eq_eLpNorm_rpow
    (df : ℂ → ℂ →L[ℝ] ℂ) {p : ℝ} (hp : 0 < p)
    (c : ℂ) (r : ℝ) :
    lpEnergyMeasure df p (closedBall c r) =
      eLpNorm df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict (closedBall c r)) ^ p := by
  exact
    lpEnergyMeasure_apply_eq_eLpNorm_rpow
      df hp measurableSet_closedBall

/--
%%handwave
name:
  Same-ball image area controlled by area plus energy
statement:
  Let $p>2$, $r>0$, and suppose that $f$ is continuous and locally
  $W^{1,2}$ on $\Omega$, with
  $\overline B(c,r)\subset\Omega$ and
  $Df\in L^p(\overline B(c,r))$. Then
  $$
    |f(\overline B(c,r))|
      \leq
      (C_p^{\mathrm{ball}})^2
      \left(
        |\overline B(c,r)|
        +\int_{\overline B(c,r)}|Df|^p
      \right).
  $$
proof:
  Use [the image-area bound](lean:JJMath.Quasiconformal.IsLocalW12On.volume_image_closedBall_le_morrey_sameBall) and [factor its squared diameter majorant into the radius and energy terms](lean:JJMath.Quasiconformal.morreySameBallDiameterBound_sq_eq_holderFactors). The radius square is at most the area of the ball, and [the weighted product of area and energy is at most their sum](lean:JJMath.Quasiconformal.ennreal_rpow_one_sub_two_div_mul_rpow_two_div_le_add).
-/
theorem IsLocalW12On.volume_image_closedBall_le_constant_mul_add_energy
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {c : ℂ} {r p : ℝ}
    (hr : 0 < r) (hp : 2 < p)
    (hclosed : closedBall c r ⊆ Ω)
    (hdfp : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r))) :
    volume (f '' closedBall c r) ≤
      ENNReal.ofReal (morreySameBallDiameterConstant p) ^ 2 *
        (((volume : Measure ℂ) + lpEnergyMeasure df p)
          (closedBall c r)) := by
  let w : ℝ≥0∞ := ENNReal.ofReal r ^ 2
  let e : ℝ≥0∞ :=
    eLpNorm df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict (closedBall c r)) ^ p
  have hp0 : 0 < p := by
    linarith
  have hwtop : w ≠ ⊤ := by
    dsimp [w]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hetop : e ≠ ⊤ := by
    dsimp [e]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le
      hdfp.eLpNorm_lt_top.ne
  have hweight :
      w ≤ volume (closedBall c r) := by
    rw [Complex.volume_closedBall]
    have hpireal : (1 : ℝ) ≤ Real.pi := by
      linarith [Real.pi_gt_three]
    have hpi :
        (1 : ℝ≥0∞) ≤ (NNReal.pi : ℝ≥0∞) := by
      exact_mod_cast hpireal
    calc
      w = w * 1 := by
        simp
      _ ≤ w * (NNReal.pi : ℝ≥0∞) := by
        gcongr
  have henergy :
      e = lpEnergyMeasure df p (closedBall c r) := by
    exact
      (lpEnergyMeasure_closedBall_eq_eLpNorm_rpow
        df hp0 c r).symm
  calc
    volume (f '' closedBall c r) ≤
        morreySameBallDiameterBound df c r p ^ 2 :=
      hW.volume_image_closedBall_le_morrey_sameBall
        hcont hr hp hclosed hdfp
    _ =
        ENNReal.ofReal
            (morreySameBallDiameterConstant p) ^ 2 *
          w ^ (1 - 2 / p) *
          e ^ (2 / p) := by
      simpa [w, e] using
        morreySameBallDiameterBound_sq_eq_holderFactors
          df c hr hp hdfp
    _ =
        ENNReal.ofReal
            (morreySameBallDiameterConstant p) ^ 2 *
          (w ^ (1 - 2 / p) * e ^ (2 / p)) := by
      ring
    _ ≤
        ENNReal.ofReal
            (morreySameBallDiameterConstant p) ^ 2 *
          (w + e) :=
      mul_le_mul_right
        (ennreal_rpow_one_sub_two_div_mul_rpow_two_div_le_add
          hp hwtop hetop) _
    _ ≤
        ENNReal.ofReal
            (morreySameBallDiameterConstant p) ^ 2 *
          (volume (closedBall c r) +
            lpEnergyMeasure df p (closedBall c r)) := by
      rw [henergy]
      gcongr
    _ =
        ENNReal.ofReal
            (morreySameBallDiameterConstant p) ^ 2 *
          (((volume : Measure ℂ) + lpEnergyMeasure df p)
            (closedBall c r)) := by
      simp only [Measure.add_apply]

/--
%%handwave
name:
  Lusin null-set preservation above the planar dimension
statement:
  Let $p>2$. Suppose $f$ is continuous and locally $W^{1,2}$ on
  $\Omega$, with weak differential $Df$. Let
  $N\subset\operatorname{int}C$, where $C\subset\Omega$ is compact,
  $|N|=0$, and $Df\in L^p(C)$. Then
  $$
    |f(N)|=0.
  $$
proof:
  Restrict the finite measure
  $$
    \nu(A)=|A|+\int_A|Df|^p
  $$
  to $C$. It vanishes on $N$. For each $x\in N$, allow every sufficiently
  small closed ball centered at $x$ that lies in
  $\operatorname{int}C$. The Besicovitch covering theorem gives a
  countable cover whose total $\nu$-mass is arbitrarily small. Apply [the same-ball image-area estimate](lean:JJMath.Quasiconformal.IsLocalW12On.volume_image_closedBall_le_constant_mul_add_energy) to each ball and sum by countable subadditivity.
-/
theorem IsLocalW12On.volume_image_eq_zero_of_null_of_memLp
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    {p : ℝ} (hp : 2 < p)
    {N C : Set ℂ} (hC : IsCompact C)
    (hNC : N ⊆ interior C) (hCΩ : C ⊆ Ω)
    (hNzero : volume N = 0)
    (hdf : MemLp df (ENNReal.ofReal p)
      ((volume : Measure ℂ).restrict C)) :
    volume (f '' N) = 0 := by
  let ν : Measure ℂ :=
    volume + lpEnergyMeasure df p
  let μ : Measure ℂ := ν.restrict C
  have hp0 : 0 < p := by
    linarith
  have henergyC :
      lpEnergyMeasure df p C ≠ ⊤ := by
    rw [lpEnergyMeasure_apply_eq_eLpNorm_rpow
      df hp0 hC.measurableSet]
    exact
      ENNReal.rpow_ne_top_of_nonneg hp0.le
        hdf.eLpNorm_lt_top.ne
  have hνC : ν C ≠ ⊤ := by
    change
      volume C + lpEnergyMeasure df p C ≠ ⊤
    exact ENNReal.add_ne_top.2
      ⟨hC.measure_ne_top, henergyC⟩
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 hνC
  letI : Measure.OuterRegular μ := by
    infer_instance
  have hνac : ν ≪ (volume : Measure ℂ) := by
    dsimp [ν, lpEnergyMeasure]
    exact Measure.AbsolutelyContinuous.add_left
      Measure.AbsolutelyContinuous.rfl
      (withDensity_absolutelyContinuous
        volume fun z : ℂ => ‖df z‖ₑ ^ p)
  have hνN : ν N = 0 :=
    hνac hNzero
  have hμN : μ N = 0 := by
    apply le_antisymm
    · exact
        (Measure.restrict_apply_le C N).trans_eq hνN
    · exact bot_le
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hεtop
    let B : ℝ≥0∞ :=
      ENNReal.ofReal
        (morreySameBallDiameterConstant p) ^ 2
    let η : ℝ≥0∞ := (ε : ℝ≥0∞) / (B + 1)
    have hBtop : B ≠ ⊤ := by
      dsimp [B]
      finiteness
    have hden0 : B + 1 ≠ 0 := by
      simp
    have hdentop : B + 1 ≠ ⊤ := by
      exact ENNReal.add_ne_top.2 ⟨hBtop, by simp⟩
    have hεne : (ε : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hε.ne'
    have hηpos : 0 < η :=
      ENNReal.div_pos hεne hdentop
    have hηne : η ≠ 0 :=
      ne_of_gt hηpos
    let admissible : ℂ → Set ℝ :=
      fun x =>
        {r : ℝ |
          0 < r ∧ closedBall x r ⊆ interior C}
    have hadmissible :
        ∀ x ∈ N, ∀ δ > 0,
          (admissible x ∩ Ioo 0 δ).Nonempty := by
      intro x hx δ hδ
      obtain ⟨R, hR, hball⟩ :=
        Metric.mem_nhds_iff.mp
          (isOpen_interior.mem_nhds (hNC hx))
      let r : ℝ := min (R / 2) (δ / 2)
      have hr : 0 < r :=
        lt_min (half_pos hR) (half_pos hδ)
      have hrR : r < R :=
        (min_le_left _ _).trans_lt
          (half_lt_self hR)
      have hrδ : r < δ :=
        (min_le_right _ _).trans_lt
          (half_lt_self hδ)
      refine ⟨r, ⟨?_, hr, hrδ⟩⟩
      refine ⟨hr, ?_⟩
      exact (closedBall_subset_ball hrR).trans hball
    obtain
        ⟨t, ρ, htcount, htN, hρ, hcover, hsum⟩ :=
      Besicovitch.exists_closedBall_covering_tsum_measure_le
        μ hηne admissible N hadmissible
    letI : Encodable t := htcount.toEncodable
    have hρpos (x : t) : 0 < ρ x := by
      have hx := hρ x x.2
      exact hx.1
    have hballInterior (x : t) :
        closedBall (x : ℂ) (ρ x) ⊆ interior C := by
      have hx := hρ x x.2
      exact hx.2
    have hballC (x : t) :
        closedBall (x : ℂ) (ρ x) ⊆ C :=
      (hballInterior x).trans interior_subset
    have hdfball (x : t) :
        MemLp df (ENNReal.ofReal p)
          ((volume : Measure ℂ).restrict
            (closedBall (x : ℂ) (ρ x))) :=
      hdf.mono_measure
        (Measure.restrict_mono (hballC x) le_rfl)
    have hμball (x : t) :
        μ (closedBall (x : ℂ) (ρ x)) =
          ν (closedBall (x : ℂ) (ρ x)) := by
      dsimp [μ]
      rw [Measure.restrict_apply measurableSet_closedBall,
        inter_eq_left.2 (hballC x)]
    have hballImage (x : t) :
        volume (f '' closedBall (x : ℂ) (ρ x)) ≤
          B * μ (closedBall (x : ℂ) (ρ x)) := by
      have h :=
        hW.volume_image_closedBall_le_constant_mul_add_energy
          hcont (hρpos x) hp
          ((hballC x).trans hCΩ) (hdfball x)
      rw [hμball x]
      simpa [B, ν] using h
    have himage :
        f '' N ⊆
          ⋃ x : t, f '' closedBall (x : ℂ) (ρ x) := by
      rintro y ⟨x, hxN, rfl⟩
      rcases Set.mem_iUnion.mp (hcover hxN) with
        ⟨z, hz⟩
      rcases Set.mem_iUnion.mp hz with
        ⟨hzt, hxball⟩
      exact Set.mem_iUnion.mpr
        ⟨⟨z, hzt⟩, ⟨x, hxball, rfl⟩⟩
    have hsum' :
        (∑' x : t,
          μ (closedBall (x : ℂ) (ρ x))) ≤ η := by
      simpa [hμN, zero_add] using hsum
    have himageη :
        volume (f '' N) ≤ B * η := by
      calc
        volume (f '' N) ≤
            volume
              (⋃ x : t,
                f '' closedBall (x : ℂ) (ρ x)) :=
          measure_mono himage
        _ ≤
            ∑' x : t,
              volume
                (f '' closedBall (x : ℂ) (ρ x)) :=
          measure_iUnion_le _
        _ ≤
            ∑' x : t,
              B * μ (closedBall (x : ℂ) (ρ x)) :=
          ENNReal.tsum_le_tsum hballImage
        _ =
            B * ∑' x : t,
              μ (closedBall (x : ℂ) (ρ x)) :=
          ENNReal.tsum_mul_left
        _ ≤ B * η :=
          mul_le_mul_right hsum' B
    have hBη : B * η ≤ (ε : ℝ≥0∞) := by
      calc
        B * η ≤ (B + 1) * η :=
          mul_le_mul_left (le_add_right le_rfl) η
        _ = (ε : ℝ≥0∞) :=
          ENNReal.mul_div_cancel hden0 hdentop
    simpa [zero_add] using himageη.trans hBη
  · exact bot_le

end

end Quasiconformal

end JJMath
