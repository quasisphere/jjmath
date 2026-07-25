import JJMath.Quasiconformal.Capacity
import JJMath.Quasiconformal.Examples
import JJMath.ComplexAnalysis.KoebeQuarter
import JJMath.Analysis.Sobolev.BallTrace
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Model geometry for planar condenser capacity

This file develops conformal normalizations and model ring estimates for the
planar condenser capacity.  These are the geometric inputs needed to turn
quasiconformal capacity distortion into equicontinuity.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Locally Lipschitz real functions are locally Sobolev
statement:
  If $\Omega\subseteq\mathbb C$ is open and
  $u:\mathbb C\to\mathbb R$ is locally Lipschitz on $\Omega$, then
  $u\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb R)$ and its weak differential
  is its almost-everywhere classical real Fréchet differential.
proof:
  The ACL theorem for locally Lipschitz functions identifies the pointwise
  Fréchet differential with the distributional derivative. On every compact
  subset, local Lipschitz continuity gives uniform bounds for both $u$ and
  its differential, hence square-integrability against the finite restricted
  area measure.
-/
theorem isLocalW12RealOn_of_locallyLipschitzOn
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hu : LocallyLipschitzOn Ω u) :
    IsLocalW12RealOn Ω u (fun z ↦ fderiv ℝ u z) := by
  refine ⟨hΩ,
    JJMath.Uniformization.locallyLipschitzOn_isWeakDerivative_fderiv hΩ hu,
    ?_⟩
  intro K hK hKΩ
  have huK : ContinuousOn u K :=
    hu.continuousOn.mono hKΩ
  rcases JJMath.Uniformization.locallyLipschitzOn_fderiv_norm_bound_on_compact
      hΩ hu hK hKΩ with ⟨C, _hC, hCbound⟩
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_ne_top
  refine ⟨memLp_restrict_of_isCompact_of_continuousOn hK huK, ?_⟩
  exact MemLp.of_bound
    (measurable_fderiv ℝ u).aestronglyMeasurable C
    (ae_restrict_of_forall_mem hK.measurableSet hCbound)

/--
%%handwave
name:
  Concentric planar ring capacity
statement:
  For radii $r,R\in\mathbb R$, the concentric ring capacity is the planar
  condenser capacity whose zero plate is the closed disk
  $\{z:|z|\leq r\}$ and whose one plate is the exterior
  $\{z:|z|\geq R\}$.
-/
def planarRingCapacity (r R : ℝ) : ℝ≥0∞ :=
  planarCondenserCapacity Set.univ
    (Metric.closedBall (0 : ℂ) r) (Metric.ball (0 : ℂ) R)ᶜ

/--
%%handwave
name:
  Logarithmic planar ring cutoff
statement:
  For radii $0<r<R$, the logarithmic ring cutoff is
  $$
    u_{r,R}(z)=\min\left\{1,
      \frac{\log(\max\{r,|z|\})-\log r}{\log R-\log r}\right\}.
  $$
  It is identically $0$ on $|z|\le r$, identically $1$ on $|z|\ge R$,
  and logarithmic on the intervening annulus.
-/
def planarLogRingCutoff (r R : ℝ) (z : ℂ) : ℝ :=
  min 1
    ((Real.log (max r ‖z‖) - Real.log r) /
      (Real.log R - Real.log r))

/--
%%handwave
name:
  The logarithmic ring cutoff vanishes on the inner disk
statement:
  If $|z|\le r$, then $u_{r,R}(z)=0$.
proof:
  The maximum of $r$ and $|z|$ is $r$, so the logarithmic numerator
  vanishes.
-/
@[simp]
theorem planarLogRingCutoff_eq_zero_of_norm_le
    {r R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) :
    planarLogRingCutoff r R z = 0 := by
  simp [planarLogRingCutoff, max_eq_left hz]

/--
%%handwave
name:
  The logarithmic ring cutoff equals one outside the outer disk
statement:
  If $0<r<R\le |z|$, then $u_{r,R}(z)=1$.
proof:
  Monotonicity of the logarithm makes the logarithmic quotient at least
  $1$, so truncation by the minimum with $1$ gives exactly $1$.
-/
@[simp]
theorem planarLogRingCutoff_eq_one_of_le_norm
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : R ≤ ‖z‖) :
    planarLogRingCutoff r R z = 1 := by
  have hR : 0 < R := hr.trans hrR
  have hrlogR : Real.log r < Real.log R :=
    Real.strictMonoOn_log hr hR hrR
  have hrnorm : r ≤ ‖z‖ := hrR.le.trans hz
  have hlogRnorm : Real.log R ≤ Real.log ‖z‖ :=
    Real.strictMonoOn_log.monotoneOn hR (hR.trans_le hz) hz
  have hden : 0 < Real.log R - Real.log r := sub_pos.mpr hrlogR
  have hquot : 1 ≤
      (Real.log ‖z‖ - Real.log r) /
        (Real.log R - Real.log r) := by
    rw [le_div_iff₀ hden]
    linarith
  simp [planarLogRingCutoff, max_eq_right hrnorm, min_eq_left hquot]

/--
%%handwave
name:
  The logarithmic ring cutoff is locally Lipschitz
statement:
  If $r>0$, then for every real $R$ the function
  $u_{r,R}:\mathbb C\to\mathbb R$ is locally Lipschitz.
proof:
  The map $z\mapsto\max\{r,|z|\}$ is globally Lipschitz and takes values in
  the positive real axis. The logarithm is continuously differentiable near
  every such value, so their composition is locally Lipschitz. Affine scalar
  operations and truncation by $\min\{1,\cdot\}$ preserve local Lipschitz
  regularity.
-/
theorem planarLogRingCutoff_locallyLipschitz
    {r R : ℝ} (hr : 0 < r) :
    LocallyLipschitz (planarLogRingCutoff r R) := by
  let g : ℂ → ℝ := fun z ↦ max r ‖z‖
  have hg : LipschitzWith 1 g := by
    simpa [g] using (lipschitzWith_one_norm.const_max r :
      LipschitzWith 1 (fun z : ℂ ↦ max r ‖z‖))
  have hlogg : LocallyLipschitz (fun z : ℂ ↦ Real.log (g z)) := by
    intro z
    have hgz : 0 < g z := hr.trans_le (le_max_left r ‖z‖)
    have hlogAt : ContDiffAt ℝ 1 Real.log (g z) :=
      (Real.contDiffAt_log (n := 1)).2 hgz.ne'
    rcases hlogAt.exists_lipschitzOnWith with ⟨K, t, ht, hlog⟩
    refine ⟨K, g ⁻¹' t, hg.continuous.continuousAt ht, ?_⟩
    simpa [Function.comp_def] using
      hlog.comp (hg.lipschitzOnWith (s := g ⁻¹' t))
        (mapsTo_preimage g t)
  let scale : ℝ →L[ℝ] ℝ :=
    (Real.log R - Real.log r)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  have hscale : LocallyLipschitz scale :=
    scale.lipschitz.locallyLipschitz
  have hratio : LocallyLipschitz
      (fun z : ℂ ↦
        (Real.log (g z) - Real.log r) *
          (Real.log R - Real.log r)⁻¹) := by
    simpa [scale, Function.comp_def, mul_comm] using
      hscale.comp (hlogg.sub (LocallyLipschitz.const (Real.log r)))
  simpa [planarLogRingCutoff, g, div_eq_mul_inv] using
    hratio.const_min 1

/--
%%handwave
name:
  The logarithmic ring cutoff is locally Sobolev
statement:
  If $r>0$, then for every real $R$ one has
  $u_{r,R}\in W^{1,2}_{\mathrm{loc}}(\mathbb C)$, with weak differential
  given by its almost-everywhere classical Fréchet differential.
proof:
  Apply the local Sobolev theorem for locally Lipschitz real functions to the
  locally Lipschitz logarithmic ring cutoff.
-/
theorem planarLogRingCutoff_isLocalW12
    {r R : ℝ} (hr : 0 < r) :
    IsLocalW12RealOn Set.univ (planarLogRingCutoff r R)
      (fun z ↦ fderiv ℝ (planarLogRingCutoff r R) z) := by
  exact isLocalW12RealOn_of_locallyLipschitzOn isOpen_univ
    (planarLogRingCutoff_locallyLipschitz hr).locallyLipschitzOn

/--
%%handwave
name:
  The logarithmic cutoff is a planar ring competitor
statement:
  If $0<r<R$, the function $u_{r,R}$, together with its almost-everywhere
  classical Fréchet differential, is an admissible competitor for the
  whole-plane condenser with plates $\{|z|\le r\}$ and $\{|z|\ge R\}$.
proof:
  Local Sobolev regularity and continuity follow from local Lipschitz
  regularity. The two plate conditions are the inner- and outer-value formulas
  for the logarithmic cutoff.
-/
def planarLogRingCompetitor
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    PlanarCondenserCompetitor Set.univ
      (Metric.closedBall (0 : ℂ) r) (Metric.ball (0 : ℂ) R)ᶜ where
  toFun := planarLogRingCutoff r R
  weakDifferential := fun z ↦ fderiv ℝ (planarLogRingCutoff r R) z
  zeroPlate_subset := Set.subset_univ _
  onePlate_subset := Set.subset_univ _
  isLocalW12 := planarLogRingCutoff_isLocalW12 hr
  continuousOn :=
    (planarLogRingCutoff_locallyLipschitz hr).continuous.continuousOn
  eq_zero_on := by
    intro z hz
    apply planarLogRingCutoff_eq_zero_of_norm_le
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  eq_one_on := by
    intro z hz
    apply planarLogRingCutoff_eq_one_of_le_norm hr hrR
    simpa [Metric.mem_ball, dist_eq_norm] using hz

/--
%%handwave
name:
  Formula for the logarithmic cutoff on the open annulus
statement:
  If $0<r<|z|<R$, then
  $$
    u_{r,R}(z)=\frac{\log|z|-\log r}{\log R-\log r}.
  $$
proof:
  On the open annulus the maximum with $r$ selects $|z|$. Strict
  monotonicity of the logarithm shows that the displayed quotient is less
  than $1$, so the outer minimum does not truncate it.
-/
theorem planarLogRingCutoff_eq_log_of_norm_mem_Ioo
    {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ∈ Set.Ioo r R) :
    planarLogRingCutoff r R z =
      (Real.log ‖z‖ - Real.log r) /
        (Real.log R - Real.log r) := by
  have hR : 0 < R := hr.trans hz.1 |>.trans hz.2
  have hrlogR : Real.log r < Real.log R :=
    Real.strictMonoOn_log hr hR (hz.1.trans hz.2)
  have hlognormR : Real.log ‖z‖ < Real.log R :=
    Real.strictMonoOn_log (hr.trans hz.1) hR hz.2
  have hden : 0 < Real.log R - Real.log r := sub_pos.mpr hrlogR
  have hquot :
      (Real.log ‖z‖ - Real.log r) /
          (Real.log R - Real.log r) < 1 := by
    rw [div_lt_iff₀ hden]
    linarith
  simp [planarLogRingCutoff, max_eq_right hz.1.le,
    min_eq_right hquot.le]

/--
%%handwave
name:
  Differential of the logarithmic ring cutoff on the open annulus
statement:
  If $0<r<|z|<R$, then $u_{r,R}$ is Fréchet differentiable at $z$ and
  $$
    Du_{r,R}(z)=
      \frac{1}{(\log R-\log r)|z|}\,D|\cdot|(z).
  $$
proof:
  The cutoff agrees on a neighborhood of $z$ with the untruncated
  logarithmic quotient. Apply the chain rule to the norm, logarithm,
  subtraction of the constant $\log r$, and multiplication by the reciprocal
  logarithmic width.
-/
theorem hasFDerivAt_planarLogRingCutoff_of_norm_mem_Ioo
    {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ∈ Set.Ioo r R) :
    HasFDerivAt (planarLogRingCutoff r R)
      (((Real.log R - Real.log r)⁻¹ * ‖z‖⁻¹) •
        fderiv ℝ (norm : ℂ → ℝ) z) z := by
  have hz0 : z ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (hr.trans hz.1))
  have hnorm : DifferentiableAt ℝ (norm : ℂ → ℝ) z :=
    (contDiffAt_norm (n := 1) ℂ hz0).differentiableAt (by norm_num)
  have hlognorm : HasFDerivAt (fun w : ℂ ↦ Real.log ‖w‖)
      (‖z‖⁻¹ • fderiv ℝ (norm : ℂ → ℝ) z) z := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (norm_ne_zero_iff.mpr hz0)).comp_hasFDerivAt
        z hnorm.hasFDerivAt
  have hraw : HasFDerivAt
      (fun w : ℂ ↦
        (Real.log ‖w‖ - Real.log r) /
          (Real.log R - Real.log r))
      (((Real.log R - Real.log r)⁻¹ * ‖z‖⁻¹) •
        fderiv ℝ (norm : ℂ → ℝ) z) z := by
    simpa [div_eq_mul_inv, smul_smul, mul_comm] using
      (hlognorm.sub_const (Real.log r)).mul_const
        (Real.log R - Real.log r)⁻¹
  have hopen : IsOpen {w : ℂ | ‖w‖ ∈ Set.Ioo r R} := by
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have heq : planarLogRingCutoff r R =ᶠ[𝓝 z]
      fun w : ℂ ↦
        (Real.log ‖w‖ - Real.log r) /
          (Real.log R - Real.log r) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact planarLogRingCutoff_eq_log_of_norm_mem_Ioo hr hw
  exact hraw.congr_of_eventuallyEq heq

/--
%%handwave
name:
  Fréchet derivative formula for the logarithmic ring cutoff
statement:
  If $0<r<|z|<R$, then
  $$
    Du_{r,R}(z)=
      \frac{1}{(\log R-\log r)|z|}\,D|\cdot|(z).
  $$
proof:
  Take the Fréchet derivative identified by the preceding differentiability
  theorem.
-/
theorem fderiv_planarLogRingCutoff_of_norm_mem_Ioo
    {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ∈ Set.Ioo r R) :
    fderiv ℝ (planarLogRingCutoff r R) z =
      ((Real.log R - Real.log r)⁻¹ * ‖z‖⁻¹) •
        fderiv ℝ (norm : ℂ → ℝ) z :=
  (hasFDerivAt_planarLogRingCutoff_of_norm_mem_Ioo hr hz).fderiv

/--
%%handwave
name:
  Norm of the logarithmic ring cutoff differential on the annulus
statement:
  If $0<r<|z|<R$, then
  $$
    \lVert Du_{r,R}(z)\rVert
      =\frac{1}{(\log R-\log r)|z|}.
  $$
proof:
  In a real inner-product space the norm function is differentiable away
  from the origin and its differential has operator norm $1$. Take norms in
  the differential formula; both scalar reciprocal factors are positive.
-/
theorem norm_fderiv_planarLogRingCutoff_of_norm_mem_Ioo
    {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ∈ Set.Ioo r R) :
    ‖fderiv ℝ (planarLogRingCutoff r R) z‖ =
      (Real.log R - Real.log r)⁻¹ * ‖z‖⁻¹ := by
  have hR : 0 < R := hr.trans (hz.1.trans hz.2)
  have hden : 0 < Real.log R - Real.log r := by
    exact sub_pos.mpr (Real.strictMonoOn_log hr hR (hz.1.trans hz.2))
  have hnormz : 0 < ‖z‖ := hr.trans hz.1
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp hnormz.ne'
  have hnorm : DifferentiableAt ℝ (norm : ℂ → ℝ) z :=
    (contDiffAt_norm (n := 1) ℂ hz0).differentiableAt (by norm_num)
  rw [fderiv_planarLogRingCutoff_of_norm_mem_Ioo hr hz, norm_smul,
    norm_fderiv_norm hnorm, mul_one, Real.norm_eq_abs,
    abs_of_pos (mul_pos (inv_pos.mpr hden) (inv_pos.mpr hnormz))]

/--
%%handwave
name:
  The logarithmic cutoff differential vanishes inside the inner circle
statement:
  If $|z|<r$, then $Du_{r,R}(z)=0$.
proof:
  On the open disk $|w|<r$ the cutoff is identically zero, so its Fréchet
  derivative vanishes.
-/
theorem fderiv_planarLogRingCutoff_eq_zero_of_norm_lt
    {r R : ℝ} {z : ℂ} (hz : ‖z‖ < r) :
    fderiv ℝ (planarLogRingCutoff r R) z = 0 := by
  have hopen : IsOpen {w : ℂ | ‖w‖ < r} :=
    isOpen_lt continuous_norm continuous_const
  have heq : planarLogRingCutoff r R =ᶠ[𝓝 z] fun _ : ℂ ↦ 0 := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact planarLogRingCutoff_eq_zero_of_norm_le hw.le
  exact ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq heq).fderiv

/--
%%handwave
name:
  The logarithmic cutoff differential vanishes outside the outer circle
statement:
  If $0<r<R<|z|$, then $Du_{r,R}(z)=0$.
proof:
  On the open exterior $R<|w|$ the cutoff is identically one, so its Fréchet
  derivative vanishes.
-/
theorem fderiv_planarLogRingCutoff_eq_zero_of_lt_norm
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : R < ‖z‖) :
    fderiv ℝ (planarLogRingCutoff r R) z = 0 := by
  have hopen : IsOpen {w : ℂ | R < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  have heq : planarLogRingCutoff r R =ᶠ[𝓝 z] fun _ : ℂ ↦ 1 := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact planarLogRingCutoff_eq_one_of_le_norm hr hrR hw.le
  exact ((hasFDerivAt_const (1 : ℝ) z).congr_of_eventuallyEq heq).fderiv

/--
%%handwave
name:
  Smooth logarithmic planar ring cutoff
statement:
  For real radii $r,R$, define
  $$
    \widetilde u_{r,R}(z)
      =\vartheta\bigl(u_{r,R}(z)\bigr),
  $$
  where $u_{r,R}$ is the logarithmic ring cutoff and $\vartheta$ is the
  standard smooth transition from $0$ to $1$.
-/
def planarSmoothLogRingCutoff (r R : ℝ) (z : ℂ) : ℝ :=
  Real.smoothTransition (planarLogRingCutoff r R z)

/--
%%handwave
name:
  The smooth logarithmic cutoff vanishes on the inner disk
statement:
  If $|z|\leq r$, then $\widetilde u_{r,R}(z)=0$.
proof:
  The logarithmic cutoff is zero there and the smooth transition fixes zero.
-/
@[simp]
theorem planarSmoothLogRingCutoff_eq_zero_of_norm_le
    {r R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) :
    planarSmoothLogRingCutoff r R z = 0 := by
  simp [planarSmoothLogRingCutoff,
    planarLogRingCutoff_eq_zero_of_norm_le hz]

/--
%%handwave
name:
  The smooth logarithmic cutoff equals one outside the outer disk
statement:
  If $0<r<R\leq|z|$, then $\widetilde u_{r,R}(z)=1$.
proof:
  The logarithmic cutoff is one there and the smooth transition fixes one.
-/
@[simp]
theorem planarSmoothLogRingCutoff_eq_one_of_le_norm
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : R ≤ ‖z‖) :
    planarSmoothLogRingCutoff r R z = 1 := by
  simp [planarSmoothLogRingCutoff,
    planarLogRingCutoff_eq_one_of_le_norm hr hrR hz]

/--
%%handwave
name:
  Formula for the smooth logarithmic cutoff away from the origin
statement:
  If $0<r<R$ and $z\neq0$, then
  $$
    \widetilde u_{r,R}(z)
      =
    \vartheta\left(
      \frac{\log|z|-\log r}{\log R-\log r}\right).
  $$
proof:
  Below the inner radius both sides are zero, above the outer radius both are
  one, and on the intervening annulus this is the defining logarithmic
  formula.
-/
theorem planarSmoothLogRingCutoff_eq_smoothTransition_log_of_ne
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : z ≠ 0) :
    planarSmoothLogRingCutoff r R z =
      Real.smoothTransition
        ((Real.log ‖z‖ - Real.log r) /
          (Real.log R - Real.log r)) := by
  have hR : 0 < R := hr.trans hrR
  by_cases hin : ‖z‖ ≤ r
  · rw [planarSmoothLogRingCutoff_eq_zero_of_norm_le hin]
    apply (Real.smoothTransition.zero_of_nonpos ?_).symm
    have hlog : Real.log ‖z‖ ≤ Real.log r :=
      Real.strictMonoOn_log.monotoneOn
        (norm_pos_iff.mpr hz) hr hin
    have hd : 0 < Real.log R - Real.log r :=
      sub_pos.mpr (Real.strictMonoOn_log hr hR hrR)
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlog) hd.le
  · have hir : r < ‖z‖ := lt_of_not_ge hin
    by_cases hout : R ≤ ‖z‖
    · rw [planarSmoothLogRingCutoff_eq_one_of_le_norm hr hrR hout]
      apply (Real.smoothTransition.one_of_one_le ?_).symm
      have hlog : Real.log R ≤ Real.log ‖z‖ :=
        Real.strictMonoOn_log.monotoneOn hR
          (norm_pos_iff.mpr hz) hout
      have hd : 0 < Real.log R - Real.log r :=
        sub_pos.mpr (Real.strictMonoOn_log hr hR hrR)
      rw [le_div_iff₀ hd]
      linarith
    · have hzI : ‖z‖ ∈ Set.Ioo r R :=
        ⟨hir, lt_of_not_ge hout⟩
      rw [planarSmoothLogRingCutoff,
        planarLogRingCutoff_eq_log_of_norm_mem_Ioo hr hzI]

/--
%%handwave
name:
  Smoothness of the smooth logarithmic cutoff
statement:
  If $0<r<R$, then
  $\widetilde u_{r,R}:\mathbb C\to\mathbb R$ is smooth.
proof:
  Near the origin it is identically zero. Away from the origin it is the
  smooth transition function composed with the smooth function
  $(\log|z|-\log r)/(\log R-\log r)$.
-/
theorem planarSmoothLogRingCutoff_contDiff
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (planarSmoothLogRingCutoff r R) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have heq :
        planarSmoothLogRingCutoff r R =ᶠ[𝓝 (0 : ℂ)]
          fun _ ↦ 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with y hy
      have hynorm : ‖y‖ ≤ r :=
        (by
          simpa [Metric.mem_ball, dist_eq_norm] using hy :
            ‖y‖ < r).le
      exact planarSmoothLogRingCutoff_eq_zero_of_norm_le hynorm
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · let q : ℂ → ℝ := fun y ↦
      (Real.log ‖y‖ - Real.log r) /
        (Real.log R - Real.log r)
    have hnorm :
        ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ ↦ ‖y‖) z :=
      contDiffAt_norm ℝ hz
    have hlog :
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y : ℂ ↦ Real.log ‖y‖) z :=
      hnorm.log (norm_ne_zero_iff.mpr hz)
    have hq : ContDiffAt ℝ (⊤ : ℕ∞) q z :=
      (hlog.sub contDiffAt_const).div_const _
    have hcomp :
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y ↦ Real.smoothTransition (q y)) z :=
      Real.smoothTransition.contDiffAt.comp z hq
    have heq :
        planarSmoothLogRingCutoff r R =ᶠ[𝓝 z]
          fun y ↦ Real.smoothTransition (q y) := by
      filter_upwards [compl_singleton_mem_nhds_iff.mpr hz] with y hy
      exact
        planarSmoothLogRingCutoff_eq_smoothTransition_log_of_ne
          hr hrR hy
    exact hcomp.congr_of_eventuallyEq heq

/--
%%handwave
name:
  Smooth logarithmic cutoff centered at a point
statement:
  For $w\in\mathbb C$, the centered smooth logarithmic cutoff is
  $$
    \widetilde u_{w;r,R}(y)=\widetilde u_{r,R}(y-w).
  $$
-/
def planarSmoothLogRingCutoffAt
    (w : ℂ) (r R : ℝ) (y : ℂ) : ℝ :=
  planarSmoothLogRingCutoff r R (y - w)

/--
%%handwave
name:
  The centered smooth logarithmic cutoff vanishes near its center
statement:
  If $|y-w|\leq r$, then
  $\widetilde u_{w;r,R}(y)=0$.
proof:
  Translate by $-w$ and apply the inner-disk value of the centered-at-zero
  cutoff.
-/
@[simp]
theorem planarSmoothLogRingCutoffAt_eq_zero_of_norm_sub_le
    {w y : ℂ} {r R : ℝ} (hy : ‖y - w‖ ≤ r) :
    planarSmoothLogRingCutoffAt w r R y = 0 := by
  exact planarSmoothLogRingCutoff_eq_zero_of_norm_le hy

/--
%%handwave
name:
  The centered smooth logarithmic cutoff equals one away from its center
statement:
  If $0<r<R\leq|y-w|$, then
  $\widetilde u_{w;r,R}(y)=1$.
proof:
  Translate by $-w$ and apply the outer value of the centered-at-zero
  cutoff.
-/
@[simp]
theorem planarSmoothLogRingCutoffAt_eq_one_of_le_norm_sub
    {w y : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hy : R ≤ ‖y - w‖) :
    planarSmoothLogRingCutoffAt w r R y = 1 := by
  exact planarSmoothLogRingCutoff_eq_one_of_le_norm hr hrR hy

/--
%%handwave
name:
  Smoothness of the centered smooth logarithmic cutoff
statement:
  If $0<r<R$, then
  $\widetilde u_{w;r,R}:\mathbb C\to\mathbb R$ is smooth.
proof:
  Compose the smooth centered-at-zero cutoff with translation by $-w$.
-/
theorem planarSmoothLogRingCutoffAt_contDiff
    {w : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞)
      (planarSmoothLogRingCutoffAt w r R) := by
  exact
    (planarSmoothLogRingCutoff_contDiff hr hrR).comp
      (contDiff_id.sub contDiff_const)

/--
%%handwave
name:
  Compactly supported tail of a centered smooth logarithmic cutoff
statement:
  If $0<r<R$, then
  $\widetilde u_{w;r,R}-1$ is smooth and compactly supported in
  $\overline B(w,R)$.
-/
def planarSmoothLogRingTailAt
    (w : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
      (Set.univ : Set ℂ) where
  toFun := fun y ↦ planarSmoothLogRingCutoffAt w r R y - 1
  smooth :=
    (planarSmoothLogRingCutoffAt_contDiff hr hrR).sub contDiff_const
  support_subset := Set.subset_univ _
  compact_support := by
    apply
      (isCompact_closedBall w R).of_isClosed_subset
        (isClosed_tsupport _)
    apply closure_minimal
    · intro y hy
      change planarSmoothLogRingCutoffAt w r R y - 1 ≠ 0 at hy
      have hnorm : ‖y - w‖ ≤ R := by
        by_contra h
        have hRnorm : R ≤ ‖y - w‖ := (lt_of_not_ge h).le
        exact hy (by
          rw [planarSmoothLogRingCutoffAt_eq_one_of_le_norm_sub
            hr hrR hRnorm]
          simp)
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
    · exact Metric.isClosed_closedBall

/--
%%handwave
name:
  Smooth logarithmic postcomposition preserves local Sobolev regularity
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak
  differential $Df$, and let $0<r<R$. Then
  $\widetilde u_{w;r,R}\circ f$ belongs to
  $W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb R)$ with weak differential
  $$
    D(\widetilde u_{w;r,R}\circ f)(x)
      =D\widetilde u_{w;r,R}(f(x))\circ Df(x).
  $$
proof:
  The function $\widetilde u_{w;r,R}-1$ is smooth and compactly supported,
  so the smooth outer chain rule applies to its composition with $f$.
  Adding the constant $1$ leaves the weak differential unchanged.
-/
theorem IsLocalW12On.postcomp_planarSmoothLogRingCutoffAt
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (w : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IsLocalW12RealOn Ω
      (fun x ↦ planarSmoothLogRingCutoffAt w r R (f x))
      (fun x ↦
        (fderiv ℝ (planarSmoothLogRingCutoffAt w r R) (f x)).comp
          (df x)) := by
  have htail :=
    hW.postcomp_smoothCompactlySupported
      (planarSmoothLogRingTailAt w hr hrR)
  have hplus := htail.sub_const (-1)
  simpa [planarSmoothLogRingTailAt, fderiv_sub_const] using hplus

/--
%%handwave
name:
  A uniform derivative bound for the standard smooth transition
statement:
  There is a constant $C\geq0$ such that
  $$
    \|D\vartheta(t)\|\leq C
  $$
  for every $t\in\mathbb R$, where $\vartheta$ is the standard smooth
  transition from $0$ to $1$.
proof:
  The derivative is continuous and hence bounded on $[0,1]$. Outside that
  interval the transition is locally constant, so its derivative vanishes.
-/
theorem exists_smoothTransition_fderiv_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖fderiv ℝ Real.smoothTransition t‖ ≤ C := by
  have hsmooth : ContDiff ℝ 1 Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hcont : Continuous (fderiv ℝ Real.smoothTransition) :=
    hsmooth.continuous_fderiv (by norm_num)
  rcases
      isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn with
    ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · exact (hC₀ t ht).trans (le_max_left _ _)
  · have hout : t < 0 ∨ 1 < t := by
      change ¬ (0 ≤ t ∧ t ≤ 1) at ht
      rcases not_and_or.mp ht with ht | ht
      · exact Or.inl (lt_of_not_ge ht)
      · exact Or.inr (lt_of_not_ge ht)
    rcases hout with ht | ht
    · have heq :
          Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 0 := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]
      simp [C]
    · have heq :
          Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 1 := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]
      simp [C]

/--
%%handwave
name:
  Differential of the smooth logarithmic cutoff on the annulus
statement:
  If $0<r<|z|<R$, then
  $$
    D\widetilde u_{r,R}(z)
      =
    D\vartheta(u_{r,R}(z))\circ Du_{r,R}(z).
  $$
proof:
  Both factors are differentiable on the open annulus, so this is the
  classical chain rule.
-/
theorem fderiv_planarSmoothLogRingCutoff_of_norm_mem_Ioo
    {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ∈ Set.Ioo r R) :
    fderiv ℝ (planarSmoothLogRingCutoff r R) z =
      (fderiv ℝ Real.smoothTransition
        (planarLogRingCutoff r R z)).comp
          (fderiv ℝ (planarLogRingCutoff r R) z) := by
  have hinner :=
    (hasFDerivAt_planarLogRingCutoff_of_norm_mem_Ioo hr hz).differentiableAt
  have houter :
      DifferentiableAt ℝ Real.smoothTransition
        (planarLogRingCutoff r R z) :=
    (Real.smoothTransition.contDiff :
      ContDiff ℝ 1 Real.smoothTransition).differentiable
        (by norm_num) _
  simpa [planarSmoothLogRingCutoff] using
    fderiv_comp z houter hinner

/--
%%handwave
name:
  Differential bound for the smooth logarithmic cutoff
statement:
  Suppose $\|D\vartheta(t)\|\leq C$ for every $t$. If
  $0<r<|z|<R$, then
  $$
    \|D\widetilde u_{r,R}(z)\|
      \leq C\|Du_{r,R}(z)\|.
  $$
proof:
  Combine the annular chain rule with the operator-norm bound for a
  composition.
-/
theorem norm_fderiv_planarSmoothLogRingCutoff_le
    {r R C : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ∈ Set.Ioo r R)
    (hC : ∀ t : ℝ,
      ‖fderiv ℝ Real.smoothTransition t‖ ≤ C) :
    ‖fderiv ℝ (planarSmoothLogRingCutoff r R) z‖ ≤
      C * ‖fderiv ℝ (planarLogRingCutoff r R) z‖ := by
  rw [fderiv_planarSmoothLogRingCutoff_of_norm_mem_Ioo hr hz]
  exact
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))

/--
%%handwave
name:
  The smooth logarithmic cutoff has zero differential inside
statement:
  If $|z|<r$, then $D\widetilde u_{r,R}(z)=0$.
proof:
  The cutoff is identically zero on a neighborhood of $z$.
-/
theorem fderiv_planarSmoothLogRingCutoff_eq_zero_of_norm_lt
    {r R : ℝ} {z : ℂ} (hz : ‖z‖ < r) :
    fderiv ℝ (planarSmoothLogRingCutoff r R) z = 0 := by
  have hopen : IsOpen {w : ℂ | ‖w‖ < r} :=
    isOpen_lt continuous_norm continuous_const
  have heq :
      planarSmoothLogRingCutoff r R =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact planarSmoothLogRingCutoff_eq_zero_of_norm_le hw.le
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]
  simp

/--
%%handwave
name:
  The smooth logarithmic cutoff has zero differential outside
statement:
  If $0<r<R<|z|$, then $D\widetilde u_{r,R}(z)=0$.
proof:
  The cutoff is identically one on a neighborhood of $z$.
-/
theorem fderiv_planarSmoothLogRingCutoff_eq_zero_of_lt_norm
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : R < ‖z‖) :
    fderiv ℝ (planarSmoothLogRingCutoff r R) z = 0 := by
  have hopen : IsOpen {w : ℂ | R < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  have heq :
      planarSmoothLogRingCutoff r R =ᶠ[𝓝 z] fun _ ↦ 1 := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact
      planarSmoothLogRingCutoff_eq_one_of_le_norm hr hrR hw.le
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]
  simp

/--
%%handwave
name:
  Differential of a centered smooth logarithmic cutoff
statement:
  If $0<r<R$, then for every $y,w\in\mathbb C$,
  $$
    D\widetilde u_{w;r,R}(y)
      =D\widetilde u_{r,R}(y-w).
  $$
proof:
  Apply the chain rule to translation by $-w$, whose differential is the
  identity.
-/
theorem fderiv_planarSmoothLogRingCutoffAt
    {w y : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    fderiv ℝ (planarSmoothLogRingCutoffAt w r R) y =
      fderiv ℝ (planarSmoothLogRingCutoff r R) (y - w) := by
  have houter :
      DifferentiableAt ℝ (planarSmoothLogRingCutoff r R) (y - w) :=
    (planarSmoothLogRingCutoff_contDiff hr hrR).differentiable
      (by simp) _
  have hinner :
      DifferentiableAt ℝ (fun z : ℂ ↦ z - w) y :=
    differentiableAt_id.sub_const w
  have htrans :
      fderiv ℝ (fun z : ℂ ↦ z - w) y =
        ContinuousLinearMap.id ℝ ℂ := by
    simpa using
      ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const w).fderiv
  rw [show
    fderiv ℝ (planarSmoothLogRingCutoffAt w r R) y =
      (fderiv ℝ (planarSmoothLogRingCutoff r R) (y - w)).comp
        (fderiv ℝ (fun z : ℂ ↦ z - w) y) by
      simpa [planarSmoothLogRingCutoffAt, Function.comp_def] using
        fderiv_comp y houter hinner]
  rw [htrans]
  exact ContinuousLinearMap.comp_id _

/--
%%handwave
name:
  Almost-everywhere energy density of the logarithmic ring cutoff
statement:
  If $0<r<R$, then for almost every $z\in\mathbb C$,
  $$
    \lVert Du_{r,R}(z)\rVert^2
      =\mathbf 1_{\{r<|z|<R\}}(z)
        \frac{1}{(\log R-\log r)^2|z|^2}.
  $$
proof:
  On the open annulus use the norm formula for the differential. On the two
  complementary open regions the cutoff is locally constant. The two boundary
  circles have planar measure zero and may be discarded.
-/
theorem norm_fderiv_planarLogRingCutoff_sq_ae
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (fun z : ℂ ↦ ‖fderiv ℝ (planarLogRingCutoff r R) z‖ ^ (2 : ℕ))
      =ᵐ[volume]
    Set.indicator {z : ℂ | ‖z‖ ∈ Set.Ioo r R}
      (fun z : ℂ ↦
        ((Real.log R - Real.log r)⁻¹ * ‖z‖⁻¹) ^ (2 : ℕ)) := by
  have hR : 0 < R := hr.trans hrR
  have hrsphere : volume (Metric.sphere (0 : ℂ) r) = 0 :=
    JJMath.Uniformization.euclidean_volume_sphere_zero hr
  have hRsphere : volume (Metric.sphere (0 : ℂ) R) = 0 :=
    JJMath.Uniformization.euclidean_volume_sphere_zero hR
  filter_upwards [compl_mem_ae_iff.mpr hrsphere,
    compl_mem_ae_iff.mpr hRsphere] with z hzr hzR
  have hzr' : ‖z‖ ≠ r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hzr
  have hzR' : ‖z‖ ≠ R := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hzR
  by_cases hzA : ‖z‖ ∈ Set.Ioo r R
  · rw [Set.indicator_of_mem
        (show z ∈ {w : ℂ | ‖w‖ ∈ Set.Ioo r R} from hzA),
      norm_fderiv_planarLogRingCutoff_of_norm_mem_Ioo hr hzA]
  · rw [Set.indicator_of_notMem
        (show z ∉ {w : ℂ | ‖w‖ ∈ Set.Ioo r R} from hzA)]
    have hout : ‖z‖ < r ∨ R < ‖z‖ := by
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hzA
      rcases hzA with hle | hle
      · exact Or.inl (lt_of_le_of_ne hle hzr')
      · exact Or.inr (lt_of_le_of_ne hle hzR'.symm)
    rcases hout with hin | hout
    · rw [fderiv_planarLogRingCutoff_eq_zero_of_norm_lt hin]
      simp
    · rw [fderiv_planarLogRingCutoff_eq_zero_of_lt_norm hr hrR hout]
      simp

/--
%%handwave
name:
  Energy integral of the logarithmic annular density
statement:
  If $0<r<R$, then
  $$
    \int_{r<|z|<R}
      \frac{dz}{(\log R-\log r)^2|z|^2}
      =\frac{2\pi}{\log R-\log r}.
  $$
proof:
  In polar coordinates the area element is $\rho\,d\rho\,dt$, so the
  integral becomes
  $2\pi(\log R-\log r)^{-2}\int_r^R\rho^{-1}\,d\rho$.
  The last integral is $\log R-\log r$.
-/
theorem integral_planarLogRingEnergyDensity
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Set.Ioo r R},
        ((Real.log R - Real.log r)⁻¹ * ‖z‖⁻¹) ^ (2 : ℕ)) =
      2 * Real.pi / (Real.log R - Real.log r) := by
  let d : ℝ := Real.log R - Real.log r
  let F : ℂ → ℝ := fun z ↦ (d⁻¹ * ‖z‖⁻¹) ^ (2 : ℕ)
  have hR : 0 < R := hr.trans hrR
  have hd : 0 < d := by
    exact sub_pos.mpr (Real.strictMonoOn_log hr hR hrR)
  have hFcont : ContinuousOn F
      {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    intro z hz
    have hz0 : ‖z‖ ≠ 0 := ne_of_gt (hr.trans_le hz.1)
    unfold F
    fun_prop
  rw [show {z : ℂ | ‖z‖ ∈ Set.Ioo r R} =
      {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} by rfl,
    JJMath.ComplexAnalysis.setIntegral_openAnnulus_eq_iterated hr hrR hFcont]
  have hinner : ∀ ρ ∈ Set.Icc r R,
      (∫ t in (-Real.pi)..Real.pi,
        ρ * F (circleMap (0 : ℂ) ρ t)) =
        2 * Real.pi * d⁻¹ ^ (2 : ℕ) * ρ⁻¹ := by
    intro ρ hρ
    have hρpos : 0 < ρ := hr.trans_le hρ.1
    simp only [F, norm_circleMap_zero, abs_of_pos hρpos]
    rw [intervalIntegral.integral_const]
    simp only [mul_pow, inv_pow]
    field_simp [hd.ne', hρpos.ne']
    simp only [smul_eq_mul]
    field_simp [hd.ne', hρpos.ne']
    all_goals ring
  calc
    (∫ ρ in r..R, ∫ t in (-Real.pi)..Real.pi,
        ρ * F (circleMap (0 : ℂ) ρ t)) =
        ∫ ρ in r..R, 2 * Real.pi * d⁻¹ ^ (2 : ℕ) * ρ⁻¹ := by
      apply intervalIntegral.integral_congr
      intro ρ hρ
      exact hinner ρ (by simpa [Set.uIcc_of_le hrR.le] using hρ)
    _ = (2 * Real.pi * d⁻¹ ^ (2 : ℕ)) *
        (∫ ρ in r..R, ρ⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 2 * Real.pi / d := by
      rw [integral_inv_of_pos hr hR,
        Real.log_div hR.ne' hr.ne']
      field_simp [inv_pow, hd.ne']
      all_goals ring
    _ = 2 * Real.pi / (Real.log R - Real.log r) := by rfl

/--
%%handwave
name:
  Dirichlet energy of the logarithmic planar ring competitor
statement:
  If $0<r<R$, then the logarithmic competitor for the concentric planar
  ring has extended Dirichlet energy
  $$
    \mathcal E(u_{r,R})=
      \frac{2\pi}{\log R-\log r}.
  $$
proof:
  The weak differential is the classical differential of the locally
  Lipschitz cutoff. Its squared norm agrees almost everywhere with the
  logarithmic annular density. Integrate that density by the preceding polar
  coordinate computation and pass from the finite real integral to the
  extended nonnegative integral.
-/
theorem planarLogRingCompetitor_dirichletEnergy
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (planarLogRingCompetitor hr hrR).dirichletEnergy =
      ENNReal.ofReal
        (2 * Real.pi / (Real.log R - Real.log r)) := by
  let A : Set ℂ := {z : ℂ | ‖z‖ ∈ Set.Ioo r R}
  let K : Set ℂ := {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  let F : ℂ → ℝ := fun z ↦
    ((Real.log R - Real.log r)⁻¹ * ‖z‖⁻¹) ^ (2 : ℕ)
  have hAmeas : MeasurableSet A := by
    exact ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hFcont : ContinuousOn F K := by
    intro z hz
    have hz0 : ‖z‖ ≠ 0 := ne_of_gt (hr.trans_le hz.1)
    unfold F
    fun_prop
  have hKcompact : IsCompact K := by
    have hKclosed : IsClosed K :=
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    have hKsub : K ⊆ Metric.closedBall (0 : ℂ) R := by
      intro z hz
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2
    exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
      hKclosed hKsub
  have hFint : Integrable F (volume.restrict A) := by
    exact (hFcont.integrableOn_compact hKcompact).mono_set
      (fun _z hz ↦ ⟨hz.1.le, hz.2.le⟩)
  have hFnonneg : 0 ≤ᵐ[volume.restrict A] F :=
    Filter.Eventually.of_forall (fun z ↦ sq_nonneg _)
  have hlintegral :
      (∫⁻ z in A, ENNReal.ofReal (F z) ∂volume) =
        ENNReal.ofReal
          (2 * Real.pi / (Real.log R - Real.log r)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hFint hFnonneg]
    exact congrArg ENNReal.ofReal
      (integral_planarLogRingEnergyDensity hr hrR)
  unfold PlanarCondenserCompetitor.dirichletEnergy
  rw [setLIntegral_univ]
  calc
    (∫⁻ z : ℂ,
        ENNReal.ofReal
          (‖fderiv ℝ (planarLogRingCutoff r R) z‖ ^ (2 : ℕ))
        ∂volume) =
        ∫⁻ z : ℂ, ENNReal.ofReal (A.indicator F z) ∂volume := by
      apply lintegral_congr_ae
      exact (norm_fderiv_planarLogRingCutoff_sq_ae hr hrR).fun_comp
        ENNReal.ofReal
    _ = ∫⁻ z in A, ENNReal.ofReal (F z) ∂volume := by
      rw [← lintegral_indicator hAmeas]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ A <;> simp [Set.indicator, hz]
    _ = ENNReal.ofReal
          (2 * Real.pi / (Real.log R - Real.log r)) := hlintegral

/--
%%handwave
name:
  Energy bound for the smooth logarithmic cutoff
statement:
  Suppose $C\geq0$ and
  $\|D\vartheta(t)\|\leq C$ for all $t\in\mathbb R$. If $0<r<R$, then
  $$
    \int_{\mathbb C}
      \|D\widetilde u_{r,R}(z)\|^2\,dz
      \leq
    C^2\frac{2\pi}{\log R-\log r}.
  $$
proof:
  Away from the two boundary circles, the smooth cutoff has zero
  differential off the annulus and its differential on the annulus is at
  most $C$ times that of the logarithmic cutoff. The circles are null, and
  the logarithmic cutoff has energy
  $2\pi/(\log R-\log r)$.
-/
theorem lintegral_norm_fderiv_planarSmoothLogRingCutoff_sq_le
    {r R C : ℝ} (hr : 0 < r) (hrR : r < R)
    (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ,
      ‖fderiv ℝ Real.smoothTransition t‖ ≤ C) :
    (∫⁻ z : ℂ,
        ENNReal.ofReal
          (‖fderiv ℝ (planarSmoothLogRingCutoff r R) z‖ ^ (2 : ℕ))
        ∂volume) ≤
      ENNReal.ofReal (C ^ (2 : ℕ)) *
        ENNReal.ofReal
          (2 * Real.pi / (Real.log R - Real.log r)) := by
  have hR : 0 < R := hr.trans hrR
  have hrsphere : volume (Metric.sphere (0 : ℂ) r) = 0 :=
    JJMath.Uniformization.euclidean_volume_sphere_zero hr
  have hRsphere : volume (Metric.sphere (0 : ℂ) R) = 0 :=
    JJMath.Uniformization.euclidean_volume_sphere_zero hR
  have hae : ∀ᵐ z ∂volume,
      ‖fderiv ℝ (planarSmoothLogRingCutoff r R) z‖ ^ (2 : ℕ) ≤
        C ^ (2 : ℕ) *
          ‖fderiv ℝ (planarLogRingCutoff r R) z‖ ^ (2 : ℕ) := by
    filter_upwards [compl_mem_ae_iff.mpr hrsphere,
      compl_mem_ae_iff.mpr hRsphere] with z hzr hzR
    have hzr' : ‖z‖ ≠ r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hzr
    have hzR' : ‖z‖ ≠ R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hzR
    by_cases hzA : ‖z‖ ∈ Set.Ioo r R
    · have hb :=
        norm_fderiv_planarSmoothLogRingCutoff_le hr hzA hC
      have hCnonneg :
          0 ≤ C *
            ‖fderiv ℝ (planarLogRingCutoff r R) z‖ :=
        mul_nonneg hC0 (norm_nonneg _)
      nlinarith [hCnonneg,
        norm_nonneg
          (fderiv ℝ (planarSmoothLogRingCutoff r R) z),
        norm_nonneg (fderiv ℝ (planarLogRingCutoff r R) z)]
    · have hout : ‖z‖ < r ∨ R < ‖z‖ := by
        simp only [Set.mem_Ioo, not_and_or, not_lt] at hzA
        rcases hzA with hle | hle
        · exact Or.inl (lt_of_le_of_ne hle hzr')
        · exact Or.inr (lt_of_le_of_ne hle hzR'.symm)
      rcases hout with hin | hout
      · rw [fderiv_planarSmoothLogRingCutoff_eq_zero_of_norm_lt hin]
        simp only [norm_zero, pow_two, zero_mul]
        exact
          mul_nonneg (mul_self_nonneg C)
            (mul_self_nonneg _)
      · rw [fderiv_planarSmoothLogRingCutoff_eq_zero_of_lt_norm
          hr hrR hout]
        simp only [norm_zero, pow_two, zero_mul]
        exact
          mul_nonneg (mul_self_nonneg C)
            (mul_self_nonneg _)
  calc
    (∫⁻ z : ℂ,
        ENNReal.ofReal
          (‖fderiv ℝ (planarSmoothLogRingCutoff r R) z‖ ^ (2 : ℕ))
        ∂volume) ≤
        ∫⁻ z : ℂ,
          ENNReal.ofReal
            (C ^ (2 : ℕ) *
              ‖fderiv ℝ (planarLogRingCutoff r R) z‖ ^ (2 : ℕ))
          ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [hae] with z hz
      exact ENNReal.ofReal_le_ofReal hz
    _ =
        ENNReal.ofReal (C ^ (2 : ℕ)) *
          (∫⁻ z : ℂ,
            ENNReal.ofReal
              (‖fderiv ℝ (planarLogRingCutoff r R) z‖ ^ (2 : ℕ))
            ∂volume) := by
      simp_rw [ENNReal.ofReal_mul (sq_nonneg C)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ =
        ENNReal.ofReal (C ^ (2 : ℕ)) *
          ENNReal.ofReal
            (2 * Real.pi / (Real.log R - Real.log r)) := by
      rw [show
        (∫⁻ z : ℂ,
            ENNReal.ofReal
              (‖fderiv ℝ (planarLogRingCutoff r R) z‖ ^ (2 : ℕ))
            ∂volume) =
          ENNReal.ofReal
            (2 * Real.pi / (Real.log R - Real.log r)) by
        simpa [PlanarCondenserCompetitor.dirichletEnergy,
          planarLogRingCompetitor] using
            planarLogRingCompetitor_dirichletEnergy hr hrR]

/--
%%handwave
name:
  Energy bound for a centered smooth logarithmic cutoff
statement:
  Suppose $C\geq0$ and
  $\|D\vartheta(t)\|\leq C$ for all $t\in\mathbb R$. If $0<r<R$, then for
  every $w\in\mathbb C$,
  $$
    \int_{\mathbb C}
      \|D\widetilde u_{w;r,R}(y)\|^2\,dy
      \leq
    C^2\frac{2\pi}{\log R-\log r}.
  $$
proof:
  Translation by $-w$ preserves planar area and changes the centered
  differential into the centered-at-zero differential. Apply the
  centered-at-zero energy bound.
-/
theorem lintegral_norm_fderiv_planarSmoothLogRingCutoffAt_sq_le
    {w : ℂ} {r R C : ℝ} (hr : 0 < r) (hrR : r < R)
    (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ,
      ‖fderiv ℝ Real.smoothTransition t‖ ≤ C) :
    (∫⁻ y : ℂ,
        ENNReal.ofReal
          (‖fderiv ℝ (planarSmoothLogRingCutoffAt w r R) y‖ ^
            (2 : ℕ))
        ∂volume) ≤
      ENNReal.ofReal (C ^ (2 : ℕ)) *
        ENNReal.ofReal
          (2 * Real.pi / (Real.log R - Real.log r)) := by
  let F : ℂ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal
      (‖fderiv ℝ (planarSmoothLogRingCutoff r R) z‖ ^ (2 : ℕ))
  have hshift :
      (∫⁻ y : ℂ, F (y - w) ∂volume) =
        ∫⁻ z : ℂ, F z ∂volume := by
    have hmp :=
      MeasureTheory.measurePreserving_add_right
        (volume : Measure ℂ) (-w)
    have hemb :
        MeasurableEmbedding (fun y : ℂ ↦ y - w) := by
      simpa [sub_eq_add_neg] using
        (Homeomorph.addRight (-w)).isClosedEmbedding.measurableEmbedding
    simpa [sub_eq_add_neg] using
      hmp.lintegral_comp_emb hemb F
  rw [show
    (∫⁻ y : ℂ,
        ENNReal.ofReal
          (‖fderiv ℝ (planarSmoothLogRingCutoffAt w r R) y‖ ^
            (2 : ℕ))
        ∂volume) =
      ∫⁻ y : ℂ, F (y - w) ∂volume by
        apply lintegral_congr
        intro y
        rw [fderiv_planarSmoothLogRingCutoffAt hr hrR],
    hshift]
  exact
    lintegral_norm_fderiv_planarSmoothLogRingCutoff_sq_le
      hr hrR hC0 hC

/--
%%handwave
name:
  Logarithmic upper bound for concentric planar ring capacity
statement:
  If $0<r<R$, then
  $$
    \operatorname{cap}(r,R)
      \leq \frac{2\pi}{\log R-\log r}.
  $$
proof:
  Use the logarithmic cutoff as an admissible condenser competitor and
  insert its exact Dirichlet energy into the variational definition of
  capacity.
-/
theorem planarRingCapacity_le_logarithmicEnergy
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    planarRingCapacity r R ≤
      ENNReal.ofReal
        (2 * Real.pi / (Real.log R - Real.log r)) := by
  exact (planarCondenserCapacity_le_dirichletEnergy
    (planarLogRingCompetitor hr hrR)).trans_eq
      (planarLogRingCompetitor_dirichletEnergy hr hrR)

/--
%%handwave
name:
  Weighted radial Cauchy--Schwarz inequality
statement:
  Let $0<a$ and let $h:(a,b)\to[0,\infty]$ be measurable. Then
  $$
    \int_a^b h(t)\,dt
      \leq
    \left(\int_a^b t h(t)^2\,dt\right)^{1/2}
    \left(\int_a^b \frac{dt}{t}\right)^{1/2}.
  $$
proof:
  Apply Hölder's inequality with exponents $2$ and $2$ to
  $t^{1/2}h(t)$ and $t^{-1/2}$. Positivity of $t$ on $(a,b)$ makes their
  product equal to $h(t)$ and identifies their squared integrals with the two
  displayed weighted factors.
-/
theorem lintegral_le_weighted_rpow_two_mul_reciprocal
    {h : ℝ → ℝ≥0∞} {a b : ℝ} (ha : 0 < a)
    (hh : AEMeasurable h
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a b))) :
    (∫⁻ t in Set.Ioo a b, h t ∂MeasureTheory.volume) ≤
      (∫⁻ t in Set.Ioo a b,
          ENNReal.ofReal t * h t ^ (2 : ℝ) ∂MeasureTheory.volume) ^
          ((2 : ℝ)⁻¹) *
        (∫⁻ t in Set.Ioo a b,
          (ENNReal.ofReal t)⁻¹ ∂MeasureTheory.volume) ^ ((2 : ℝ)⁻¹) := by
  let μ : Measure ℝ :=
    (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a b)
  let wt : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal t
  let f : ℝ → ℝ≥0∞ := fun t ↦ wt t ^ ((2 : ℝ)⁻¹) * h t
  let g : ℝ → ℝ≥0∞ := fun t ↦ wt t ^ (-(2 : ℝ)⁻¹)
  have hwt : AEMeasurable wt μ := by
    exact measurable_id.ennreal_ofReal.aemeasurable
  have hf : AEMeasurable f μ :=
    (hwt.pow_const ((2 : ℝ)⁻¹)).mul hh
  have hg : AEMeasurable g μ :=
    hwt.pow_const (-(2 : ℝ)⁻¹)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
    (f := f) (g := g) Real.HolderConjugate.two_two hf hg
  have hfg :
      (fun t ↦ f t * g t) =ᵐ[μ] h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htpos : 0 < t := ha.trans ht.1
    have hwt_zero : wt t ≠ 0 := by
      exact (ENNReal.ofReal_pos.mpr htpos).ne'
    have hwt_top : wt t ≠ ⊤ := ENNReal.ofReal_ne_top
    dsimp [f, g]
    calc
      wt t ^ ((2 : ℝ)⁻¹) * h t * wt t ^ (-(2 : ℝ)⁻¹) =
          (wt t ^ ((2 : ℝ)⁻¹) * wt t ^ (-(2 : ℝ)⁻¹)) * h t := by
        ac_rfl
      _ = h t := by
        rw [← ENNReal.rpow_add
          ((2 : ℝ)⁻¹) (-(2 : ℝ)⁻¹) hwt_zero hwt_top]
        norm_num
  have hf_sq :
      (fun t ↦ f t ^ (2 : ℝ)) =ᵐ[μ]
        fun t ↦ wt t * h t ^ (2 : ℝ) := by
    filter_upwards with t
    dsimp [f]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.rpow_mul]
    norm_num
  have hg_sq :
      (fun t ↦ g t ^ (2 : ℝ)) =ᵐ[μ]
        fun t ↦ (wt t)⁻¹ := by
    filter_upwards with t
    dsimp [g]
    rw [← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_neg_one]
  have hholder' :
      (∫⁻ t, f t * g t ∂μ) ≤
        (∫⁻ t, f t ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫⁻ t, g t ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa only [Pi.mul_apply] using hholder
  rw [lintegral_congr_ae hfg,
    lintegral_congr_ae hf_sq, lintegral_congr_ae hg_sq] at hholder'
  simpa [μ, wt, one_div] using hholder'

/--
%%handwave
name:
  Logarithmic reciprocal integral
statement:
  If $0<a<b$, then
  $$
    \int_a^b \frac{dt}{t}=\log b-\log a,
  $$
  with both sides regarded as extended nonnegative real numbers.
proof:
  The reciprocal is continuous and positive on $[a,b]$, hence integrable.
  Convert its nonnegative Lebesgue integral to the ordinary real integral and
  use the fundamental theorem of calculus for $\log$.
-/
theorem lintegral_ennreal_reciprocal_Ioo
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫⁻ t in Set.Ioo a b, (ENNReal.ofReal t)⁻¹
        ∂MeasureTheory.volume) =
      ENNReal.ofReal (Real.log b - Real.log a) := by
  have hb : 0 < b := ha.trans hab
  have hcont : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc a b) := by
    exact continuousOn_inv₀.mono (by
      intro t ht htzero
      subst t
      exact (not_le_of_gt ha) ht.1)
  have hint_interval : IntervalIntegrable (fun t : ℝ ↦ t⁻¹)
      MeasureTheory.volume a b :=
    hcont.intervalIntegrable_of_Icc hab.le
  have hint : Integrable (fun t : ℝ ↦ t⁻¹)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hint_interval
  have hnonneg :
      0 ≤ᵐ[(MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a b)]
        fun t : ℝ ↦ t⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (inv_pos.mpr (ha.trans ht.1)).le
  have hrecip :
      (fun t : ℝ ↦ (ENNReal.ofReal t)⁻¹) =ᵐ[
          (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a b)]
        fun t : ℝ ↦ ENNReal.ofReal t⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (ENNReal.ofReal_inv_of_pos (ha.trans ht.1)).symm
  have hset_interval :
      (∫ t in Set.Ioo a b, t⁻¹ ∂MeasureTheory.volume) =
        ∫ t in a..b, t⁻¹ ∂MeasureTheory.volume := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact (integral_Ioc_eq_integral_Ioo
      (f := fun t : ℝ ↦ t⁻¹)
      (μ := MeasureTheory.volume) (x := a) (y := b)).symm
  calc
    (∫⁻ t in Set.Ioo a b, (ENNReal.ofReal t)⁻¹
        ∂MeasureTheory.volume) =
        ∫⁻ t in Set.Ioo a b, ENNReal.ofReal t⁻¹
          ∂MeasureTheory.volume := lintegral_congr_ae hrecip
    _ = ENNReal.ofReal
        (∫ t in Set.Ioo a b, t⁻¹ ∂MeasureTheory.volume) := by
      exact (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal (∫ t in a..b, t⁻¹ ∂MeasureTheory.volume) := by
      rw [hset_interval]
    _ = ENNReal.ofReal (Real.log b - Real.log a) := by
      rw [integral_inv_of_pos ha hb, Real.log_div hb.ne' ha.ne']

/--
%%handwave
name:
  Total angular measure in the complex plane
statement:
  The spherical measure induced by planar Lebesgue measure assigns the unit
  circle total mass
  $$
    2\pi.
  $$
proof:
  The total spherical mass induced by Haar measure is the real dimension
  times the volume of the unit ball.  The complex plane has real dimension
  two and its unit disk has area $\pi$.
-/
theorem complex_toSphere_apply_univ :
    (MeasureTheory.volume : Measure ℂ).toSphere Set.univ =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.toSphere_apply_univ, Complex.volume_ball]
  norm_num [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)),
    ← NNReal.coe_real_pi]

/--
%%handwave
name:
  Removing the square roots from a weighted energy estimate
statement:
  If $E,L\in[0,\infty]$, $0<L<\infty$, and
  $$
    1\leq E^{1/2}L^{1/2},
  $$
  then $L^{-1}\leq E$.
proof:
  Square the displayed inequality to obtain $1\leq EL$, then divide by the
  positive finite factor $L$.
-/
theorem inv_le_of_one_le_rpow_half_mul_rpow_half
    {E L : ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ∞)
    (h : 1 ≤ E ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹)) :
    L⁻¹ ≤ E := by
  rw [ENNReal.inv_le_iff_le_mul (fun _ ↦ hL.ne')
    (fun htop ↦ (hLtop htop).elim)]
  have hs := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (1 : ℝ≥0∞) = (1 : ℝ≥0∞) ^ (2 : ℝ) := by simp
    _ ≤ (E ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) := hs
    _ = E * L := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num
    _ = L * E := mul_comm _ _

/--
%%handwave
name:
  Polar decomposition of planar nonnegative integrals
statement:
  If $F:\mathbb C\to[0,\infty]$ is measurable, then
  $$
    \int_{\mathbb C}F(z)\,dz
      =\int_{S^1}\int_0^\infty F(t\theta)\,d\rho_1(t)\,d\sigma(\theta),
  $$
  where $d\sigma$ is the spherical measure induced by planar Lebesgue
  measure and $d\rho_1(t)=t\,dt$.
proof:
  The origin is null.  On its complement, use the measure-preserving
  homeomorphism taking a nonzero point to its direction and radius, then
  apply Tonelli's theorem to the resulting product measure.
-/
theorem lintegral_complex_eq_lintegral_toSphere_volumeIoiPow
    (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : ℂ, F z ∂MeasureTheory.volume) =
      ∫⁻ θ : Metric.sphere (0 : ℂ) 1,
        ∫⁻ t : Set.Ioi (0 : ℝ),
          F ((t : ℝ) • (θ : ℂ))
          ∂MeasureTheory.Measure.volumeIoiPow 1
        ∂((MeasureTheory.volume : Measure ℂ).toSphere) := by
  let e := homeomorphUnitSphereProd ℂ
  let μNZ : Measure ({0}ᶜ : Set ℂ) :=
    (MeasureTheory.volume : Measure ℂ).comap
      ((↑) : ({0}ᶜ : Set ℂ) → ℂ)
  let μS : Measure (Metric.sphere (0 : ℂ) 1) :=
    (MeasureTheory.volume : Measure ℂ).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow 1
  have hmp : MeasurePreserving e μNZ (μS.prod μR) := by
    simpa [e, μNZ, μS, μR] using
      (MeasureTheory.volume : Measure ℂ).measurePreserving_homeomorphUnitSphereProd
  calc
    (∫⁻ z : ℂ, F z ∂MeasureTheory.volume) =
        ∫⁻ z in ({0}ᶜ : Set ℂ), F z ∂MeasureTheory.volume := by
      rw [restrict_compl_singleton]
    _ = ∫⁻ z : ({0}ᶜ : Set ℂ), F (z : ℂ) ∂μNZ := by
      exact (MeasureTheory.lintegral_subtype_comap
        (measurableSet_singleton (0 : ℂ)).compl F).symm
    _ = ∫⁻ p, F ((p.2 : ℝ) • (p.1 : ℂ)) ∂μS.prod μR := by
      simpa [e, homeomorphUnitSphereProd_symm_apply_coe] using
        hmp.lintegral_comp_emb e.measurableEmbedding
          (fun p ↦ F (e.symm p))
    _ = ∫⁻ θ, ∫⁻ t, F ((t : ℝ) • (θ : ℂ)) ∂μR ∂μS := by
      rw [MeasureTheory.lintegral_prod]
      exact (hF.comp (by fun_prop : Measurable
        (fun p : Metric.sphere (0 : ℂ) 1 × Set.Ioi (0 : ℝ) ↦
          (p.2 : ℝ) • (p.1 : ℂ)))).aemeasurable
    _ = _ := by rfl

/--
%%handwave
name:
  The planar radial measure is $t\,dt$
statement:
  For every measurable $h:\mathbb R\to[0,\infty]$,
  $$
    \int_{(0,\infty)}h(t)\,d\rho_1(t)
      =\int_0^\infty t h(t)\,dt,
  $$
  where $d\rho_1$ is the radial measure in the polar decomposition of
  planar Lebesgue measure.
proof:
  Expand the definition of the radial measure as the pullback of Lebesgue
  measure to $(0,\infty)$ with density $t^1$.
-/
theorem lintegral_volumeIoiPow_one_eq_weighted
    (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ t : Set.Ioi (0 : ℝ), h (t : ℝ)
        ∂MeasureTheory.Measure.volumeIoiPow 1) =
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal t * h t ∂MeasureTheory.volume := by
  rw [MeasureTheory.Measure.volumeIoiPow,
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul]
  · change (∫⁻ t : Set.Ioi (0 : ℝ),
        (fun x : ℝ ↦ ENNReal.ofReal (x ^ 1) * h x) (t : ℝ)
        ∂Measure.comap Subtype.val MeasureTheory.volume) = _
    simpa using
      (MeasureTheory.lintegral_subtype_comap
        (μ := (MeasureTheory.volume : Measure ℝ))
        (show MeasurableSet (Set.Ioi (0 : ℝ)) from measurableSet_Ioi)
        (fun x : ℝ ↦ ENNReal.ofReal x * h x))
  · exact (measurable_subtype_coe.pow_const 1).ennreal_ofReal
  · exact hh.comp measurable_subtype_coe

/--
%%handwave
name:
  Dilation change of variables on a planar disk
statement:
  Let $S>0$ and let $H:\mathbb C\to[0,\infty]$ be measurable almost
  everywhere on $|w|<S$. Then
  $$
    \int_{|z|<1}H(Sz)\,dz
      =S^{-2}\int_{|w|<S}H(w)\,dw.
  $$
proof:
  The pushforward of planar Lebesgue measure under $z\mapsto Sz$ is
  $S^{-2}$ times planar Lebesgue measure. Apply the nonnegative change of
  variables formula to $H$ cut off to the disk $|w|<S$; dilation carries
  the unit disk exactly onto that disk.
-/
theorem lintegral_comp_const_smul_restrict_ball_one
    {S : ℝ} (hS : 0 < S) (H : ℂ → ℝ≥0∞)
    (hH : AEMeasurable H
      ((MeasureTheory.volume : Measure ℂ).restrict (Metric.ball 0 S))) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1, H (S • z)
        ∂MeasureTheory.volume) =
      ENNReal.ofReal |(S ^ (2 : ℕ))⁻¹| *
        ∫⁻ w in Metric.ball (0 : ℂ) S, H w ∂MeasureTheory.volume := by
  let F : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) S).indicator H
  let c : ℝ≥0∞ := ENNReal.ofReal |(S ^ (2 : ℕ))⁻¹|
  have hF : AEMeasurable F (MeasureTheory.volume : Measure ℂ) := by
    exact (aemeasurable_indicator_iff measurableSet_ball).2 hH
  have hc : c ≠ 0 := by
    simp [c, hS.ne']
  have hmap_measure :
      Measure.map (fun z : ℂ ↦ S • z) MeasureTheory.volume =
        c • (MeasureTheory.volume : Measure ℂ) := by
    simpa [c] using
      (MeasureTheory.volume : Measure ℂ).map_addHaar_smul hS.ne'
  have hFmap : AEMeasurable F
      (Measure.map (fun z : ℂ ↦ S • z) MeasureTheory.volume) := by
    rw [hmap_measure, aemeasurable_smul_measure_iff hc]
    exact hF
  have hmap := MeasureTheory.lintegral_map' hFmap
    (measurable_const_smul S).aemeasurable
  rw [hmap_measure, MeasureTheory.lintegral_smul_measure] at hmap
  have hcomp :
      (∫⁻ z : ℂ, F (S • z) ∂MeasureTheory.volume) =
        ∫⁻ z in Metric.ball (0 : ℂ) 1, H (S • z)
          ∂MeasureTheory.volume := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_ball]
    refine MeasureTheory.lintegral_congr fun z ↦ ?_
    by_cases hz : z ∈ Metric.ball (0 : ℂ) 1
    · have hSz : S • z ∈ Metric.ball (0 : ℂ) S := by
        simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
        simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hS] using
          (mul_lt_mul_of_pos_left hz hS)
      change (Metric.ball (0 : ℂ) S).indicator H (S • z) =
        (Metric.ball (0 : ℂ) 1).indicator (fun w ↦ H (S • w)) z
      rw [Set.indicator_of_mem hSz H,
        Set.indicator_of_mem hz (fun w ↦ H (S • w))]
    · have hSz : S • z ∉ Metric.ball (0 : ℂ) S := by
        simp only [Metric.mem_ball, dist_zero_right, not_lt] at hz ⊢
        simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hS] using
          (mul_le_mul_of_nonneg_left hz hS.le)
      change (Metric.ball (0 : ℂ) S).indicator H (S • z) =
        (Metric.ball (0 : ℂ) 1).indicator (fun w ↦ H (S • w)) z
      rw [Set.indicator_of_notMem hSz H,
        Set.indicator_of_notMem hz (fun w ↦ H (S • w))]
  rw [hcomp] at hmap
  have hFint :
      (∫⁻ w : ℂ, F w ∂MeasureTheory.volume) =
        ∫⁻ w in Metric.ball (0 : ℂ) S, H w ∂MeasureTheory.volume := by
    exact MeasureTheory.lintegral_indicator measurableSet_ball H
  rw [hFint] at hmap
  exact hmap.symm

/--
%%handwave
name:
  Planar Dirichlet energy is invariant under dilation
statement:
  Let $S>0$ and let
  $D:\mathbb C\to\mathcal L(\mathbb C,\mathbb R)$ be measurable almost
  everywhere on $|w|<S$. Then
  $$
    \int_{|z|<1}\lVert S D(Sz)\rVert^2\,dz
      =\int_{|w|<S}\lVert D(w)\rVert^2\,dw.
  $$
proof:
  Pull the factor $S^2$ out of the integrand and apply
  [the dilation change of variables on a disk](lean:JJMath.Quasiconformal.lintegral_comp_const_smul_restrict_ball_one).
  Its Jacobian factor is $S^{-2}$, so the two factors cancel.
-/
theorem lintegral_norm_const_smul_comp_sq_restrict_ball_one
    {S : ℝ} (hS : 0 < S) (D : ℂ → ℂ →L[ℝ] ℝ)
    (hD : AEMeasurable D
      ((MeasureTheory.volume : Measure ℂ).restrict (Metric.ball 0 S))) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖S • D (S • z)‖ ^ (2 : ℕ))
        ∂MeasureTheory.volume) =
      ∫⁻ w in Metric.ball (0 : ℂ) S,
        ENNReal.ofReal (‖D w‖ ^ (2 : ℕ)) ∂MeasureTheory.volume := by
  let H : ℂ → ℝ≥0∞ := fun w ↦ ENNReal.ofReal (‖D w‖ ^ (2 : ℕ))
  have hH : AEMeasurable H
      ((MeasureTheory.volume : Measure ℂ).restrict (Metric.ball 0 S)) :=
    (hD.norm.pow_const 2).ennreal_ofReal
  have hscale := lintegral_comp_const_smul_restrict_ball_one hS H hH
  have hcoeff :
      ENNReal.ofReal (S ^ (2 : ℕ)) *
        ENNReal.ofReal |(S ^ (2 : ℕ))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg S)]
    simp [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hS)), hS.ne']
  calc
    (∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖S • D (S • z)‖ ^ (2 : ℕ))
        ∂MeasureTheory.volume) =
        ∫⁻ z in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (S ^ (2 : ℕ)) * H (S • z)
          ∂MeasureTheory.volume := by
      refine MeasureTheory.lintegral_congr fun z ↦ ?_
      simp only [H, norm_smul, Real.norm_eq_abs, abs_of_pos hS, mul_pow]
      rw [ENNReal.ofReal_mul (sq_nonneg S)]
    _ = ENNReal.ofReal (S ^ (2 : ℕ)) *
        (∫⁻ z in Metric.ball (0 : ℂ) 1, H (S • z)
          ∂MeasureTheory.volume) := by
      rw [MeasureTheory.lintegral_const_mul'
        (ENNReal.ofReal (S ^ (2 : ℕ))) _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (S ^ (2 : ℕ)) *
        (ENNReal.ofReal |(S ^ (2 : ℕ))⁻¹| *
          ∫⁻ w in Metric.ball (0 : ℂ) S, H w
            ∂MeasureTheory.volume) := by rw [hscale]
    _ = ∫⁻ w in Metric.ball (0 : ℂ) S,
          ENNReal.ofReal (‖D w‖ ^ (2 : ℕ)) ∂MeasureTheory.volume := by
      rw [← mul_assoc, hcoeff, one_mul]

/--
%%handwave
name:
  Polar energy on a radial interval is bounded by total planar energy
statement:
  Let $0<a<b$ and let $F:\mathbb C\to[0,\infty]$ be measurable. Then
  $$
    \int_{S^1}\int_a^b tF(t\theta)\,dt\,d\sigma(\theta)
      \leq \int_{\mathbb C}F(z)\,dz.
  $$
proof:
  Use
  [the polar decomposition of planar nonnegative integrals](lean:JJMath.Quasiconformal.lintegral_complex_eq_lintegral_toSphere_volumeIoiPow)
  and
  [the identity $d\rho_1(t)=t\,dt$](lean:JJMath.Quasiconformal.lintegral_volumeIoiPow_one_eq_weighted),
  then restrict each radial integral from $(0,\infty)$ to $(a,b)$.
-/
theorem lintegral_toSphere_weighted_Ioo_le_lintegral_complex
    {a b : ℝ} (ha : 0 < a) (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ θ : Metric.sphere (0 : ℂ) 1,
        ∫⁻ t in Set.Ioo a b,
          ENNReal.ofReal t * F (t • (θ : ℂ)) ∂MeasureTheory.volume
        ∂((MeasureTheory.volume : Measure ℂ).toSphere)) ≤
      ∫⁻ z : ℂ, F z ∂MeasureTheory.volume := by
  rw [lintegral_complex_eq_lintegral_toSphere_volumeIoiPow F hF]
  refine MeasureTheory.lintegral_mono fun θ ↦ ?_
  change (∫⁻ t in Set.Ioo a b,
      ENNReal.ofReal t * F (t • (θ : ℂ)) ∂MeasureTheory.volume) ≤
    ∫⁻ t : Set.Ioi (0 : ℝ),
      (fun s : ℝ ↦ F (s • (θ : ℂ))) (t : ℝ)
      ∂MeasureTheory.Measure.volumeIoiPow 1
  rw [lintegral_volumeIoiPow_one_eq_weighted
    (fun s : ℝ ↦ F (s • (θ : ℂ))) (hF.comp (by fun_prop))]
  · exact MeasureTheory.lintegral_mono_set fun t ht ↦ ha.trans ht.1

/--
%%handwave
name:
  From almost-everywhere radial oscillation to planar energy
statement:
  Let $0<a<b<1$, let $G:\mathbb C\to\mathcal L(\mathbb C,\mathbb R)$ be
  measurable, and let $\ell>0$. If for almost every $\theta\in S^1$,
  $$
    1\leq
    \left(\int_a^b t\,|G(t\theta)\theta|^2\,dt\right)^{1/2}
    \ell^{1/2},
  $$
  then
  $$
    \frac{2\pi}{\ell}
      \leq \int_{|z|<1}\lVert G(z)\rVert^2\,dz.
  $$
proof:
  Square the raywise estimate and divide by $\ell$. The directional norm is
  at most the operator norm because $|\theta|=1$. Integrate over the unit
  circle, whose spherical measure is
  [equal to $2\pi$](lean:JJMath.Quasiconformal.complex_toSphere_apply_univ),
  and apply
  [the polar interval energy bound](lean:JJMath.Quasiconformal.lintegral_toSphere_weighted_Ioo_le_lintegral_complex)
  to the operator-norm energy cut off to the unit disk.
-/
theorem two_pi_mul_inv_le_lintegral_ball_of_weightedRadialEnergy_ae
    {a b ell : ℝ} (ha : 0 < a) (hb : b < 1) (hell : 0 < ell)
    (G : ℂ → ℂ →L[ℝ] ℝ) (hG : Measurable G)
    (hray : ∀ᵐ θ : Metric.sphere (0 : ℂ) 1
        ∂((MeasureTheory.volume : Measure ℂ).toSphere),
      (1 : ℝ≥0∞) ≤
        (∫⁻ t in Set.Ioo a b,
            ENNReal.ofReal t *
              (ENNReal.ofReal ‖G (t • (θ : ℂ)) (θ : ℂ)‖) ^ (2 : ℝ)
            ∂MeasureTheory.volume) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal ell ^ ((2 : ℝ)⁻¹)) :
    ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal ell)⁻¹ ≤
      ∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖G z‖ ^ (2 : ℕ)) ∂MeasureTheory.volume := by
  let H : ℂ → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (‖G z‖ ^ (2 : ℕ))
  let F : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) 1).indicator H
  have hH : Measurable H := (hG.norm.pow_const 2).ennreal_ofReal
  have hF : Measurable F := hH.indicator measurableSet_ball
  have hLpos : 0 < ENNReal.ofReal ell := ENNReal.ofReal_pos.2 hell
  have hLtop : ENNReal.ofReal ell ≠ ∞ := ENNReal.ofReal_ne_top
  have hpoint : ∀ᵐ θ : Metric.sphere (0 : ℂ) 1
      ∂((MeasureTheory.volume : Measure ℂ).toSphere),
      (ENNReal.ofReal ell)⁻¹ ≤
        ∫⁻ t in Set.Ioo a b,
          ENNReal.ofReal t * H (t • (θ : ℂ)) ∂MeasureTheory.volume := by
    filter_upwards [hray] with θ hθ
    refine (inv_le_of_one_le_rpow_half_mul_rpow_half
      hLpos hLtop hθ).trans ?_
    refine MeasureTheory.lintegral_mono fun t ↦ ?_
    gcongr
    have hnorm : ‖G (t • (θ : ℂ)) (θ : ℂ)‖ ≤
        ‖G (t • (θ : ℂ))‖ := by
      simpa [norm_eq_of_mem_sphere θ] using
        (G (t • (θ : ℂ))).le_opNorm (θ : ℂ)
    have hof := ENNReal.ofReal_mono hnorm
    have hsquare := ENNReal.rpow_le_rpow hof
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa [H, ENNReal.rpow_two,
      ENNReal.ofReal_pow (norm_nonneg _) 2] using hsquare
  have hinter : ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal ell)⁻¹ ≤
      ∫⁻ θ : Metric.sphere (0 : ℂ) 1,
        ∫⁻ t in Set.Ioo a b,
          ENNReal.ofReal t * H (t • (θ : ℂ)) ∂MeasureTheory.volume
        ∂((MeasureTheory.volume : Measure ℂ).toSphere) := by
    have hint := MeasureTheory.lintegral_mono_ae hpoint
    calc
      ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal ell)⁻¹ =
          (ENNReal.ofReal ell)⁻¹ *
            (MeasureTheory.volume : Measure ℂ).toSphere Set.univ := by
        rw [complex_toSphere_apply_univ]
        exact mul_comm _ _
      _ = ∫⁻ _θ : Metric.sphere (0 : ℂ) 1,
          (ENNReal.ofReal ell)⁻¹
          ∂((MeasureTheory.volume : Measure ℂ).toSphere) := by
        rw [MeasureTheory.lintegral_const]
      _ ≤ _ := hint
  have hpolar :=
    lintegral_toSphere_weighted_Ioo_le_lintegral_complex (b := b) ha F hF
  have hinterval_eq :
      (∫⁻ θ : Metric.sphere (0 : ℂ) 1,
          ∫⁻ t in Set.Ioo a b,
            ENNReal.ofReal t * H (t • (θ : ℂ)) ∂MeasureTheory.volume
          ∂((MeasureTheory.volume : Measure ℂ).toSphere)) =
        ∫⁻ θ : Metric.sphere (0 : ℂ) 1,
          ∫⁻ t in Set.Ioo a b,
            ENNReal.ofReal t * F (t • (θ : ℂ)) ∂MeasureTheory.volume
          ∂((MeasureTheory.volume : Measure ℂ).toSphere) := by
    refine MeasureTheory.lintegral_congr fun θ ↦ ?_
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    have htpos : 0 < t := ha.trans ht.1
    have htball : t • (θ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      simp [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
        abs_of_pos htpos, norm_eq_of_mem_sphere θ, ht.2.trans hb]
    congr 1
    exact (Set.indicator_of_mem htball H).symm
  calc
    ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal ell)⁻¹ ≤
        ∫⁻ θ : Metric.sphere (0 : ℂ) 1,
          ∫⁻ t in Set.Ioo a b,
            ENNReal.ofReal t * H (t • (θ : ℂ)) ∂MeasureTheory.volume
          ∂((MeasureTheory.volume : Measure ℂ).toSphere) := hinter
    _ = ∫⁻ θ : Metric.sphere (0 : ℂ) 1,
          ∫⁻ t in Set.Ioo a b,
            ENNReal.ofReal t * F (t • (θ : ℂ)) ∂MeasureTheory.volume
          ∂((MeasureTheory.volume : Measure ℂ).toSphere) := hinterval_eq
    _ ≤ ∫⁻ z : ℂ, F z ∂MeasureTheory.volume := hpolar
    _ = ∫⁻ z in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (‖G z‖ ^ (2 : ℕ)) ∂MeasureTheory.volume := by
      simpa [F, H] using
        (MeasureTheory.lintegral_indicator measurableSet_ball H)

/--
%%handwave
name:
  Weighted radial Cauchy--Schwarz with logarithmic factor
statement:
  If $0<a<b$ and $h:(a,b)\to[0,\infty]$ is measurable, then
  $$
    \int_a^b h(t)\,dt
      \leq
    \left(\int_a^b t h(t)^2\,dt\right)^{1/2}
      (\log b-\log a)^{1/2}.
  $$
proof:
  Combine
  [the weighted radial Cauchy--Schwarz inequality](lean:JJMath.Quasiconformal.lintegral_le_weighted_rpow_two_mul_reciprocal)
  with
  [the identity $\int_a^b t^{-1}\,dt=\log b-\log a$](lean:JJMath.Quasiconformal.lintegral_ennreal_reciprocal_Ioo).
-/
theorem lintegral_le_weighted_rpow_two_mul_log
    {h : ℝ → ℝ≥0∞} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hh : AEMeasurable h
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a b))) :
    (∫⁻ t in Set.Ioo a b, h t ∂MeasureTheory.volume) ≤
      (∫⁻ t in Set.Ioo a b,
          ENNReal.ofReal t * h t ^ (2 : ℝ) ∂MeasureTheory.volume) ^
          ((2 : ℝ)⁻¹) *
        ENNReal.ofReal (Real.log b - Real.log a) ^ ((2 : ℝ)⁻¹) := by
  simpa [lintegral_ennreal_reciprocal_Ioo ha hab] using
    lintegral_le_weighted_rpow_two_mul_reciprocal ha hh

/--
%%handwave
name:
  Measurable weighted ray-energy bound for a ring competitor
statement:
  Let $0<r<R<S$, and let $u$ be a continuous local $W^{1,2}$ competitor
  which is $0$ on $|z|\leq r$ and $1$ on $|z|\geq R$. There is a measurable
  field $G(z)=S\,D u(Sz)$ almost everywhere on the unit ball such that, for
  almost every unit direction $\theta$,
  $$
    1\leq
    \left(\int_{r/S}^{R/S}
      t\,|G(t\theta)\theta|^2\,dt\right)^{1/2}
    (\log R-\log r)^{1/2}.
  $$
proof:
  Dilate the competitor to the unit ball and use
  [the measurable weak differential with endpoint-preserving radial ACL](lean:JJMath.Uniformization.scalarWeakSobolev_unit_ball_exists_measurable_weakDifferential_radial_acl_all_segments_of_continuousOn).
  The plate values give unit oscillation on almost every ray. Apply
  [weighted Cauchy--Schwarz with its logarithmic factor](lean:JJMath.Quasiconformal.lintegral_le_weighted_rpow_two_mul_log); the two occurrences of $\log S$ cancel from
  $\log(R/S)-\log(r/S)$.
-/
theorem
    PlanarCondenserCompetitor.exists_measurable_scaledWeakDifferential_one_le_weightedRadialEnergy_ae
    {r R S : ℝ} (hr : 0 < r) (hrR : r < R) (hRS : R < S)
    (u : PlanarCondenserCompetitor Set.univ
      (Metric.closedBall (0 : ℂ) r) (Metric.ball (0 : ℂ) R)ᶜ) :
    ∃ G : ℂ → ℂ →L[ℝ] ℝ,
      Measurable G ∧
      G =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)]
        (fun z ↦ S • u.weakDifferential (S • z)) ∧
      ∀ᵐ θ : Metric.sphere (0 : ℂ) 1
          ∂((MeasureTheory.volume : Measure ℂ).toSphere),
        (1 : ℝ≥0∞) ≤
          (∫⁻ t in Set.Ioo (r / S) (R / S),
              ENNReal.ofReal t *
                (ENNReal.ofReal ‖G (t • (θ : ℂ)) (θ : ℂ)‖) ^ (2 : ℝ)
              ∂MeasureTheory.volume) ^ ((2 : ℝ)⁻¹) *
            ENNReal.ofReal (Real.log R - Real.log r) ^ ((2 : ℝ)⁻¹) := by
  let w : ℂ → ℝ := fun z ↦ u (S • z)
  let dw : ℂ → ℂ →L[ℝ] ℝ :=
    fun z ↦ S • u.weakDifferential (S • z)
  have hR : 0 < R := hr.trans hrR
  have hS : 0 < S := hR.trans hRS
  have hweak_all :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Set.univ w dw := by
    have hraw := u.isLocalW12.2.1.comp_smul hS.ne'
    simpa [w, dw] using hraw
  have hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball (0 : ℂ) 1) w dw :=
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues.mono_set
      hweak_all (Set.subset_univ _)
  have hlocal := u.isLocalW12.2.2
    (Metric.closedBall (0 : ℂ) S) (isCompact_closedBall (0 : ℂ) S)
    (Set.subset_univ _)
  have huS : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) S)) :=
    hlocal.1.mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hduS : MemLp u.weakDifferential 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) S)) :=
    hlocal.2.mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    simpa [w] using
      JJMath.Uniformization.memLp_comp_const_smul_of_memLp_restrict_ball_zero
        (a := S) (R := (1 : ℝ)) hS (by simpa using huS)
  have hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    have hcomp :=
      JJMath.Uniformization.memLp_comp_const_smul_of_memLp_restrict_ball_zero
        (a := S) (R := (1 : ℝ)) hS (by simpa using hduS)
    simpa [dw] using hcomp.const_smul S
  have hw_cont : ContinuousOn w (Metric.ball (0 : ℂ) 1) := by
    exact u.continuousOn.comp
      (continuous_const_smul S).continuousOn (Set.mapsTo_univ _ _)
  rcases
      JJMath.Uniformization.scalarWeakSobolev_unit_ball_exists_measurable_weakDifferential_radial_acl_all_segments_of_continuousOn
        hw_cont hweak hw hdw with
    ⟨G, hG_meas, hG_eq, hG_acl⟩
  refine ⟨G, hG_meas, by simpa [dw] using hG_eq, ?_⟩
  have hrS_pos : 0 < r / S := div_pos hr hS
  have hrS_RS : r / S < R / S :=
    (div_lt_div_iff_of_pos_right hS).2 hrR
  have hRS_one : R / S < 1 := (div_lt_one hS).2 hRS
  have hlog :
      Real.log (R / S) - Real.log (r / S) =
        Real.log R - Real.log r := by
    rw [Real.log_div hR.ne' hS.ne', Real.log_div hr.ne' hS.ne']
    ring
  filter_upwards [hG_acl] with θ hθ
  have hsegment := hθ (r / S) (R / S) hrS_pos hrS_RS hRS_one
  have hθnorm : ‖(θ : ℂ)‖ = 1 := norm_eq_of_mem_sphere θ
  have hpoint_r : S • ((r / S) • (θ : ℂ)) = r • (θ : ℂ) := by
    rw [smul_smul]
    congr 1
    field_simp [hS.ne']
  have hpoint_R : S • ((R / S) • (θ : ℂ)) = R • (θ : ℂ) := by
    rw [smul_smul]
    congr 1
    field_simp [hS.ne']
  have hinner_mem : r • (θ : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
    simp [Metric.mem_closedBall, dist_eq_norm,
      Real.norm_eq_abs, abs_of_pos hr, hθnorm]
  have houter_mem : R • (θ : ℂ) ∈ (Metric.ball (0 : ℂ) R)ᶜ := by
    simp [Metric.mem_ball, dist_eq_norm,
      Real.norm_eq_abs, abs_of_pos hR, hθnorm]
  have hzero : w ((r / S) • (θ : ℂ)) = 0 := by
    change u (S • ((r / S) • (θ : ℂ))) = 0
    rw [hpoint_r]
    exact u.eq_zero_on (r • (θ : ℂ)) hinner_mem
  have hone : w ((R / S) • (θ : ℂ)) = 1 := by
    change u (S • ((R / S) • (θ : ℂ))) = 1
    rw [hpoint_R]
    exact u.eq_one_on (R • (θ : ℂ)) houter_mem
  rw [hzero, hone] at hsegment
  have hunit :
      (1 : ℝ≥0∞) ≤
        ∫⁻ t in Set.Ioo (r / S) (R / S),
          ENNReal.ofReal ‖G (t • (θ : ℂ)) (θ : ℂ)‖
          ∂MeasureTheory.volume := by
    norm_num at hsegment
    simpa [Set.Ioo] using hsegment
  have hmeas :
      AEMeasurable
        (fun t : ℝ ↦ ENNReal.ofReal ‖G (t • (θ : ℂ)) (θ : ℂ)‖)
        ((MeasureTheory.volume : Measure ℝ).restrict
          (Set.Ioo (r / S) (R / S))) := by
    have hpoint : Measurable (fun t : ℝ ↦ t • (θ : ℂ)) := by
      fun_prop
    have hGcomp : Measurable (fun t : ℝ ↦ G (t • (θ : ℂ))) :=
      hG_meas.comp hpoint
    have happly : Continuous
        (fun p : (ℂ →L[ℝ] ℝ) × ℂ ↦ p.1 p.2) := by
      fun_prop
    have hval : Measurable
        (fun t : ℝ ↦ G (t • (θ : ℂ)) (θ : ℂ)) :=
      happly.measurable.comp (hGcomp.prodMk measurable_const)
    exact hval.norm.ennreal_ofReal.aemeasurable
  have hweighted :=
    lintegral_le_weighted_rpow_two_mul_log hrS_pos hrS_RS hmeas
  exact hunit.trans (by simpa [hlog] using hweighted)

/--
%%handwave
name:
  Scaled unit-disk energy lower bound for a ring competitor
statement:
  Let $0<r<R<S$, and let $u$ be a continuous local $W^{1,2}$ competitor
  which is $0$ on $|z|\leq r$ and $1$ on $|z|\geq R$. There is a measurable
  field $G$ equal almost everywhere on the unit disk to
  $S\,Du(Sz)$ such that
  $$
    \frac{2\pi}{\log R-\log r}
      \leq \int_{|z|<1}\lVert G(z)\rVert^2\,dz.
  $$
proof:
  Use
  [the measurable weighted ray-energy estimate](lean:JJMath.Quasiconformal.PlanarCondenserCompetitor.exists_measurable_scaledWeakDifferential_one_le_weightedRadialEnergy_ae).
  Since $0<r/S<R/S<1$, apply
  [the passage from radial oscillation to planar energy](lean:JJMath.Quasiconformal.two_pi_mul_inv_le_lintegral_ball_of_weightedRadialEnergy_ae)
  with logarithmic factor $\log R-\log r$.
-/
theorem
    PlanarCondenserCompetitor.exists_measurable_scaledWeakDifferential_two_pi_mul_inv_le_lintegral_ball
    {r R S : ℝ} (hr : 0 < r) (hrR : r < R) (hRS : R < S)
    (u : PlanarCondenserCompetitor Set.univ
      (Metric.closedBall (0 : ℂ) r) (Metric.ball (0 : ℂ) R)ᶜ) :
    ∃ G : ℂ → ℂ →L[ℝ] ℝ,
      Measurable G ∧
      G =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)]
        (fun z ↦ S • u.weakDifferential (S • z)) ∧
      ENNReal.ofReal (2 * Real.pi) *
          (ENNReal.ofReal (Real.log R - Real.log r))⁻¹ ≤
        ∫⁻ z in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (‖G z‖ ^ (2 : ℕ)) ∂MeasureTheory.volume := by
  rcases
      u.exists_measurable_scaledWeakDifferential_one_le_weightedRadialEnergy_ae
        hr hrR hRS with
    ⟨G, hG, hG_eq, hray⟩
  have hR : 0 < R := hr.trans hrR
  have hS : 0 < S := hR.trans hRS
  have hrS_pos : 0 < r / S := div_pos hr hS
  have hRS_one : R / S < 1 := (div_lt_one hS).2 hRS
  have hlog_pos : 0 < Real.log R - Real.log r :=
    sub_pos.mpr (Real.strictMonoOn_log hr hR hrR)
  refine ⟨G, hG, hG_eq, ?_⟩
  exact two_pi_mul_inv_le_lintegral_ball_of_weightedRadialEnergy_ae
    hrS_pos hRS_one hlog_pos G hG hray

/--
%%handwave
name:
  Dirichlet energy lower bound for every concentric-ring competitor
statement:
  If $0<r<R$ and $u$ is a continuous local $W^{1,2}$ function on
  $\mathbb C$ which is $0$ on $|z|\leq r$ and $1$ on $|z|\geq R$, then
  $$
    \frac{2\pi}{\log R-\log r}\leq
      \int_{\mathbb C}\lVert Du(z)\rVert^2\,dz.
  $$
proof:
  Choose $S>R$ and use
  [the scaled unit-disk lower bound](lean:JJMath.Quasiconformal.PlanarCondenserCompetitor.exists_measurable_scaledWeakDifferential_two_pi_mul_inv_le_lintegral_ball).
  Replace the measurable representative by $S\,Du(Sz)$ almost everywhere,
  then apply
  [dilation invariance of planar Dirichlet energy](lean:JJMath.Quasiconformal.lintegral_norm_const_smul_comp_sq_restrict_ball_one).
  The resulting energy over $|z|<S$ is at most the total energy.
-/
theorem PlanarCondenserCompetitor.two_pi_mul_inv_log_sub_log_le_dirichletEnergy
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u : PlanarCondenserCompetitor Set.univ
      (Metric.closedBall (0 : ℂ) r) (Metric.ball (0 : ℂ) R)ᶜ) :
    ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (Real.log R - Real.log r))⁻¹ ≤
      u.dirichletEnergy := by
  let S : ℝ := R + 1
  have hR : 0 < R := hr.trans hrR
  have hRS : R < S := by simp [S]
  have hS : 0 < S := hR.trans hRS
  rcases
      u.exists_measurable_scaledWeakDifferential_two_pi_mul_inv_le_lintegral_ball
        hr hrR hRS with
    ⟨G, _hG, hG_eq, hbound⟩
  have hlocal := u.isLocalW12.2.2
    (Metric.closedBall (0 : ℂ) S) (isCompact_closedBall (0 : ℂ) S)
    (Set.subset_univ _)
  have hD_ball : MemLp u.weakDifferential 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) S)) :=
    hlocal.2.mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hD_ae : AEMeasurable u.weakDifferential
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) S)) :=
    hD_ball.aestronglyMeasurable.aemeasurable
  have hGint :
      (∫⁻ z in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (‖G z‖ ^ (2 : ℕ)) ∂MeasureTheory.volume) =
        ∫⁻ z in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal
            (‖S • u.weakDifferential (S • z)‖ ^ (2 : ℕ))
          ∂MeasureTheory.volume := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hG_eq] with z hz
    rw [hz]
  have hscale :=
    lintegral_norm_const_smul_comp_sq_restrict_ball_one
      hS u.weakDifferential hD_ae
  have hball_le :
      (∫⁻ z in Metric.ball (0 : ℂ) S,
          ENNReal.ofReal (‖u.weakDifferential z‖ ^ (2 : ℕ))
          ∂MeasureTheory.volume) ≤ u.dirichletEnergy := by
    unfold PlanarCondenserCompetitor.dirichletEnergy
    exact MeasureTheory.lintegral_mono_set (Set.subset_univ _)
  calc
    ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (Real.log R - Real.log r))⁻¹ ≤
        ∫⁻ z in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (‖G z‖ ^ (2 : ℕ)) ∂MeasureTheory.volume := hbound
    _ = ∫⁻ z in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal
            (‖S • u.weakDifferential (S • z)‖ ^ (2 : ℕ))
          ∂MeasureTheory.volume := hGint
    _ = ∫⁻ z in Metric.ball (0 : ℂ) S,
          ENNReal.ofReal (‖u.weakDifferential z‖ ^ (2 : ℕ))
          ∂MeasureTheory.volume := hscale
    _ ≤ u.dirichletEnergy := hball_le

/--
%%handwave
name:
  Lower bound for concentric planar ring capacity
statement:
  If $0<r<R$, then
  $$
    \frac{2\pi}{\log R-\log r}
      \leq \operatorname{cap}(|z|\leq r,\ |z|\geq R;\mathbb C).
  $$
proof:
  [Every admissible competitor has energy at least $2\pi/(\log R-\log r)$](lean:JJMath.Quasiconformal.PlanarCondenserCompetitor.two_pi_mul_inv_log_sub_log_le_dirichletEnergy).
  Take the infimum of their energies.
-/
theorem two_pi_mul_inv_log_sub_log_le_planarRingCapacity
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (Real.log R - Real.log r))⁻¹ ≤
      planarRingCapacity r R := by
  unfold planarRingCapacity planarCondenserCapacity
  refine le_sInf ?_
  rintro _ ⟨u, rfl⟩
  exact u.two_pi_mul_inv_log_sub_log_le_dirichletEnergy hr hrR

/--
%%handwave
name:
  Exact capacity of a concentric planar ring
statement:
  If $0<r<R$, then
  $$
    \operatorname{cap}(|z|\leq r,\ |z|\geq R;\mathbb C)
      =\frac{2\pi}{\log R-\log r}.
  $$
proof:
  The logarithmic cutoff gives
  [the matching upper bound](lean:JJMath.Quasiconformal.planarRingCapacity_le_logarithmicEnergy),
  while
  [the radial Sobolev argument gives the reverse inequality](lean:JJMath.Quasiconformal.two_pi_mul_inv_log_sub_log_le_planarRingCapacity).
-/
theorem planarRingCapacity_eq_logarithmicEnergy
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    planarRingCapacity r R =
      ENNReal.ofReal (2 * Real.pi / (Real.log R - Real.log r)) := by
  have hR : 0 < R := hr.trans hrR
  have hlog : 0 < Real.log R - Real.log r :=
    sub_pos.mpr (Real.strictMonoOn_log hr hR hrR)
  apply le_antisymm
  · exact planarRingCapacity_le_logarithmicEnergy hr hrR
  · rw [ENNReal.ofReal_div_of_pos hlog, div_eq_mul_inv]
    exact two_pi_mul_inv_log_sub_log_le_planarRingCapacity hr hrR

/--
%%handwave
name:
  Complex-affine invariance of planar condenser capacity
statement:
  Let $a,c\in\mathbb C$ with $a\neq0$, and write $T(z)=az+c$. For arbitrary
  plates $E_0,E_1\subseteq\mathbb C$,
  $$
    \operatorname{cap}_{\mathbb C}(T(E_0),T(E_1))
      =\operatorname{cap}_{\mathbb C}(E_0,E_1).
  $$
proof:
  The complex-affine homeomorphism is $1$-quasiconformal. Apply
  [the two-sided quasiconformal capacity-distortion theorem](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.planarCondenserCapacity_distortion); both multiplicative constants are $1$, so the two inequalities give equality.
-/
theorem planarCondenserCapacity_affineMap_image
    (a c : ℂ) (ha : a ≠ 0) (E₀ E₁ : Set ℂ) :
    planarCondenserCapacity Set.univ
        (affineMap a 0 c '' E₀) (affineMap a 0 c '' E₁) =
      planarCondenserCapacity Set.univ E₀ E₁ := by
  have hdist :=
    (isOneQuasiconformalBetween_complexAffine a c ha).planarCondenserCapacity_distortion
      (Set.subset_univ E₀) (Set.subset_univ E₁)
  rw [ambientMap_complexAffine a c ha] at hdist
  exact le_antisymm (by simpa using hdist.1) (by simpa using hdist.2)

/--
%%handwave
name:
  Scale invariance of concentric planar ring capacity
statement:
  If $a\in\mathbb C$ is nonzero, then for all real radii $r,R$,
  $$
    \operatorname{cap}(|a|r,|a|R)=\operatorname{cap}(r,R).
  $$
proof:
  Multiplication by $a$ sends the closed disk of radius $r$ to the closed
  disk of radius $|a|r$ and the exterior of the disk of radius $R$ to the
  exterior of the disk of radius $|a|R$. Apply complex-affine invariance of
  planar condenser capacity.
-/
theorem planarRingCapacity_norm_mul
    (a : ℂ) (ha : a ≠ 0) (r R : ℝ) :
    planarRingCapacity (‖a‖ * r) (‖a‖ * R) =
      planarRingCapacity r R := by
  have h := planarCondenserCapacity_affineMap_image a 0 ha
    (Metric.closedBall (0 : ℂ) r) (Metric.ball (0 : ℂ) R)ᶜ
  have hclosed :
      affineMap a 0 0 '' Metric.closedBall (0 : ℂ) r =
        Metric.closedBall (0 : ℂ) (‖a‖ * r) := by
    simpa [affineMap, realLinearMapOfWirtinger] using
      (Metric.smul_image_closedBall ha (0 : ℂ) r)
  have hball :
      affineMap a 0 0 '' Metric.ball (0 : ℂ) R =
        Metric.ball (0 : ℂ) (‖a‖ * R) := by
    simpa [affineMap, realLinearMapOfWirtinger] using
      (Metric.smul_image_ball ha (0 : ℂ) R)
  have hcompl :
      affineMap a 0 0 '' (Metric.ball (0 : ℂ) R)ᶜ =
        (Metric.ball (0 : ℂ) (‖a‖ * R))ᶜ := by
    calc
      affineMap a 0 0 '' (Metric.ball (0 : ℂ) R)ᶜ =
          (affineMap a 0 0 '' Metric.ball (0 : ℂ) R)ᶜ := by
        simpa [affineMap, realLinearMapOfWirtinger] using
          (Equiv.mulLeft₀ a ha).image_compl (Metric.ball (0 : ℂ) R)
      _ = (Metric.ball (0 : ℂ) (‖a‖ * R))ᶜ := by rw [hball]
  simpa [planarRingCapacity, hclosed, hcompl] using h

/--
%%handwave
name:
  Concentric planar ring capacity depends only on the radius ratio
statement:
  If $r>0$, then for every real $R$,
  $$
    \operatorname{cap}(r,R)=\operatorname{cap}(1,R/r).
  $$
proof:
  Apply scale invariance to multiplication by the positive real number
  $r^{-1}$, whose norm is $r^{-1}$.
-/
theorem planarRingCapacity_eq_one_div
    {r R : ℝ} (hr : 0 < r) :
    planarRingCapacity r R = planarRingCapacity 1 (R / r) := by
  have hscale := planarRingCapacity_norm_mul (r⁻¹ : ℂ)
    (by exact_mod_cast inv_ne_zero hr.ne') r R
  have hnorm : ‖(r⁻¹ : ℂ)‖ = r⁻¹ := by
    simp [Real.norm_eq_abs, abs_of_pos hr]
  rw [hnorm] at hscale
  simpa [hr.ne', div_eq_mul_inv, mul_comm] using hscale.symm

end

end Quasiconformal

end JJMath
