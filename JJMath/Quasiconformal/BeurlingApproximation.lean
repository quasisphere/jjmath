import JJMath.Quasiconformal.CauchyTransform
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Support-controlled smooth approximation for the Beurling transform

The off-support representation of the Beurling transform must be extended
from test functions to rough Calderón--Zygmund bad pieces.  Global smooth
density alone is insufficient because the approximants could approach the
evaluation region.  This file inserts a fixed smooth cutoff: data supported
in a disk of radius `r` are approximated by test functions supported in the
concentric disk of radius `3r/2`, leaving a strict gap before radius `2r`.
-/

namespace JJMath

open Set MeasureTheory Metric
open scoped ENNReal ContDiff

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Intermediate disk cutoff
statement:
  For $c\in\mathbb C$ and $r>0$, the intermediate disk cutoff
  $\beta_{c,r}$ is smooth, equals one on $\overline B(c,r)$, and is
  supported in $\overline B(c,3r/2)$.
-/
def intermediateDiskCutoff (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ContDiffBump c where
  rIn := r
  rOut := 3 * r / 2
  rIn_pos := hr
  rIn_lt_rOut := by linarith

/--
%%handwave
name:
  The intermediate cutoff is one on the inner disk
statement:
  If $|z-c|\leq r$, then $\beta_{c,r}(z)=1$.
proof:
  This is the inner-disk property of the smooth bump defining
  $\beta_{c,r}$.
-/
@[simp]
theorem intermediateDiskCutoff_eq_one_of_norm_sub_le
    {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z - c‖ ≤ r) :
    intermediateDiskCutoff c r hr z = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hz

/--
%%handwave
name:
  Closed support of the intermediate cutoff
statement:
  For $r>0$,
  $$
    \operatorname{supp}\beta_{c,r}
      =\overline B(c,3r/2).
  $$
proof:
  A smooth bump has closed support equal to the closed disk determined by
  its outer radius.
-/
theorem tsupport_intermediateDiskCutoff
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    tsupport (intermediateDiskCutoff c r hr : ℂ → ℝ) =
      Metric.closedBall c (3 * r / 2) := by
  simpa [intermediateDiskCutoff] using
    (ContDiffBump.tsupport_eq (intermediateDiskCutoff c r hr))

/--
%%handwave
name:
  Smooth function localized as a planar test function
statement:
  If $g:\mathbb C\to\mathbb C$ is smooth and $\beta$ is a smooth compactly
  supported bump, then $z\mapsto\beta(z)g(z)$ is a planar test function.
-/
def smoothCutoffPlaneTestFunction
    (c : ℂ) (β : ContDiffBump c) (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) :
    PlaneTestFunction where
  toFun z := β z • g z
  contDiff' := β.contDiff.smul hg
  hasCompactSupport' := β.hasCompactSupport.smul_right
  tsupport_subset' := Set.subset_univ _

/--
%%handwave
name:
  Support of a localized smooth test function
statement:
  The closed support of $\beta g$ is contained in the closed support of
  $\beta$.
proof:
  The product vanishes wherever the cutoff vanishes, and taking closures
  preserves the inclusion.
-/
theorem tsupport_smoothCutoffPlaneTestFunction_subset
    (c : ℂ) (β : ContDiffBump c) (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) :
    tsupport (smoothCutoffPlaneTestFunction c β g hg : ℂ → ℂ) ⊆
      tsupport (β : ℂ → ℝ) := by
  exact tsupport_smul_subset_left (β : ℂ → ℝ) g

/--
%%handwave
name:
  Support-controlled smooth density in planar $L^p$
statement:
  Let $0<p<\infty$, let $r>0$, and suppose
  $b\in L^p(\mathbb C)$ vanishes pointwise outside
  $\overline B(c,r)$. For every $\varepsilon>0$ there is
  $\varphi\in C_c^\infty(\mathbb C)$ such that
  $$
    \operatorname{supp}\varphi\subseteq\overline B(c,3r/2),
    \qquad
    \|b-\varphi\|_{L^p}\leq\varepsilon.
  $$
proof:
  Approximate $b$ globally in $L^p$ by a smooth compactly supported
  function and multiply the approximant by the intermediate disk cutoff.
  The cutoff is one wherever $b$ can be nonzero and has absolute value at
  most one, so it does not increase the approximation error.
-/
theorem exists_planeTestFunction_eLpNorm_sub_le_tsupport_subset_intermediateDisk_of_memLp
    {p : ENNReal} (hp1 : 1 ≤ p) (hptop : p ≠ (∞ : ENNReal))
    {b : ℂ → ℂ} (hb : MemLp b p volume)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hbsupp : ∀ z : ℂ, b z ≠ 0 → ‖z - c‖ ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : PlaneTestFunction,
      tsupport (φ : ℂ → ℂ) ⊆ Metric.closedBall c (3 * r / 2) ∧
      eLpNorm (b - (φ : ℂ → ℂ)) p volume ≤ ENNReal.ofReal ε := by
  obtain ⟨g, _hgcompact, hg, happrox⟩ :=
    hb.exist_eLpNorm_sub_le hptop hp1 hε
  let β : ContDiffBump c := intermediateDiskCutoff c r hr
  let φ : PlaneTestFunction := smoothCutoffPlaneTestFunction c β g hg
  refine ⟨φ, ?_, ?_⟩
  · calc
      tsupport (φ : ℂ → ℂ) ⊆ tsupport (β : ℂ → ℝ) := by
        exact tsupport_smoothCutoffPlaneTestFunction_subset c β g hg
      _ = Metric.closedBall c (3 * r / 2) := by
        exact tsupport_intermediateDiskCutoff c hr
  · calc
      eLpNorm (b - (φ : ℂ → ℂ)) p volume ≤
          eLpNorm (b - g) p volume := by
        apply eLpNorm_mono_ae
        filter_upwards with z
        change ‖b z - β z • g z‖ ≤ ‖b z - g z‖
        by_cases hbz : b z = 0
        · have hβnonneg : 0 ≤ β z := β.nonneg
          have hβle : β z ≤ 1 := β.le_one
          rw [hbz, zero_sub, zero_sub, norm_neg, norm_neg, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg hβnonneg]
          exact mul_le_of_le_one_left (norm_nonneg (g z)) hβle
        · rw [show β z = 1 by
            exact intermediateDiskCutoff_eq_one_of_norm_sub_le hr
              (hbsupp z hbz), one_smul]
      _ ≤ ENNReal.ofReal ε := happrox

/--
%%handwave
name:
  Support-controlled smooth density in planar $L^2$
statement:
  Let $b\in L^2(\mathbb C)$ vanish outside $\overline B(c,r)$, where
  $r>0$. For every $\varepsilon>0$ there is
  $\varphi\in C_c^\infty(\mathbb C)$ such that
  $$
    \operatorname{supp}\varphi\subseteq\overline B(c,3r/2),
    \qquad
    \|b-\varphi\|_{L^2}\leq\varepsilon.
  $$
proof:
  Approximate $b$ globally in $L^2$ by a smooth compactly supported
  function $g$, then multiply $g$ by the intermediate cutoff
  $\beta_{c,r}$. Since $\beta_{c,r}=1$ wherever $b$ can be nonzero and
  $0\leq\beta_{c,r}\leq1$, multiplication by the cutoff does not increase
  the approximation error.
-/
theorem exists_planeTestFunction_eLpNorm_sub_le_tsupport_subset_intermediateDisk
    {b : ℂ → ℂ} (hb : MemLp b 2 volume)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hbsupp : ∀ z : ℂ, b z ≠ 0 → ‖z - c‖ ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : PlaneTestFunction,
      tsupport (φ : ℂ → ℂ) ⊆ Metric.closedBall c (3 * r / 2) ∧
      eLpNorm (b - (φ : ℂ → ℂ)) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨g, _hgcompact, hg, happrox⟩ :=
    hb.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε
  let β : ContDiffBump c := intermediateDiskCutoff c r hr
  let φ : PlaneTestFunction := smoothCutoffPlaneTestFunction c β g hg
  refine ⟨φ, ?_, ?_⟩
  · calc
      tsupport (φ : ℂ → ℂ) ⊆ tsupport (β : ℂ → ℝ) := by
        exact tsupport_smoothCutoffPlaneTestFunction_subset c β g hg
      _ = Metric.closedBall c (3 * r / 2) := by
        exact tsupport_intermediateDiskCutoff c hr
  · calc
      eLpNorm (b - (φ : ℂ → ℂ)) 2 volume ≤
          eLpNorm (b - g) 2 volume := by
        apply eLpNorm_mono_ae
        filter_upwards with z
        change ‖b z - β z • g z‖ ≤ ‖b z - g z‖
        by_cases hbz : b z = 0
        · have hβnonneg : 0 ≤ β z := β.nonneg
          have hβle : β z ≤ 1 := β.le_one
          rw [hbz, zero_sub, zero_sub, norm_neg, norm_neg, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg hβnonneg]
          exact mul_le_of_le_one_left (norm_nonneg (g z)) hβle
        · rw [show β z = 1 by
            exact intermediateDiskCutoff_eq_one_of_norm_sub_le hr
              (hbsupp z hbz), one_smul]
      _ ≤ ENNReal.ofReal ε := happrox

end

end Quasiconformal

end JJMath
