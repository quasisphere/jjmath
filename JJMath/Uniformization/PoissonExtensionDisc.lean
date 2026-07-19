import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Poisson extension on a Euclidean disk

This file isolates the Euclidean disk computation used by Perron's method.
The final theorem is the continuous Dirichlet problem on a disk, solved by the
Poisson integral.
-/

namespace JJMath

open scoped Topology

namespace Uniformization

/--
%%handwave
name:
  Euclidean disk Dirichlet problem
statement:
  A function solves the Euclidean disk Dirichlet problem if it is harmonic on
  the disk, continuous on the closed disk, and assumes the prescribed boundary
  values on the circle.
-/
def SolvesEuclideanDiskDirichletProblem
    (c : ℂ) (r : ℝ) (φ u : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u (Metric.ball c r) ∧
    ContinuousOn u (closure (Metric.ball c r)) ∧
      ∀ z ∈ frontier (Metric.ball c r), u z = φ z

/--
%%handwave
name:
  Poisson disk extension
statement:
  The Poisson disk extension of boundary data is the circle average of the
  boundary data weighted by the Poisson kernel.
-/
noncomputable def poissonDiskExtension (c : ℂ) (r : ℝ) (φ : ℂ → ℝ) : ℂ → ℝ :=
  fun w ↦ Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * φ z) c r

/--
%%handwave
name:
  Cauchy boundary average
statement:
  The Cauchy boundary average is the circle average of the boundary data
  weighted by the Cauchy kernel \((z-w)^{-1}\).
-/
noncomputable def cauchyBoundaryAverage (c : ℂ) (r : ℝ) (φ : ℂ → ℝ) : ℂ → ℂ :=
  fun w ↦ Real.circleAverage (fun z : ℂ ↦ (z - w)⁻¹ * (φ z : ℂ)) c r

/--
%%handwave
name:
  Complex Poisson disk potential
statement:
  The complex Poisson disk potential is the Schwarz integral whose real part
  is the Poisson extension.
-/
noncomputable def poissonDiskComplexPotential
    (c : ℂ) (r : ℝ) (φ : ℂ → ℝ) : ℂ → ℂ :=
  fun w ↦
    Real.circleAverage (fun z : ℂ ↦ (φ z : ℂ)) c r +
      (2 * (w - c)) * cauchyBoundaryAverage c r φ w

/--
%%handwave
name:
  Poisson kernel at the center
statement:
  On the boundary circle, the Poisson kernel with pole at the center is equal
  to \(1\).
proof:
  For \(|z-c|=r>0\), the defining quotient is
  \((|z-c|^2-0)/|z-c|^2=1\).
-/
theorem poissonKernel_center_eq_one_of_mem_frontier
    (c : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ frontier (Metric.ball c r)) :
    poissonKernel c c z = 1 := by
  rw [frontier_ball c hr.ne'] at hz
  have hnorm : ‖z - c‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hnorm_ne : ‖z - c‖ ^ 2 ≠ 0 := by
    rw [hnorm]
    positivity
  rw [poissonKernel_def]
  simp [hnorm_ne]

/--
%%handwave
name:
  Poisson kernel has average one
statement:
  If the pole lies in the disk, then the circle average of the Poisson kernel
  over the boundary circle is \(1\).
proof:
  Apply the Poisson integral formula from Mathlib to the constant harmonic
  function \(1\).
-/
theorem circleAverage_poissonKernel_eq_one
    (c : ℂ) {r : ℝ} {w : ℂ} (hw : w ∈ Metric.ball c r) :
    Real.circleAverage (poissonKernel c w) c r = 1 := by
  have h :
      Real.circleAverage (poissonKernel c w * fun _ : ℂ ↦ (1 : ℝ)) c r = 1 :=
    (InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
      (f := fun _ : ℂ ↦ (1 : ℝ))
      (c := c) (R := r) (by simp) hw)
  calc
    Real.circleAverage (poissonKernel c w) c r
        = Real.circleAverage (poissonKernel c w * fun _ : ℂ ↦ (1 : ℝ)) c r := by
          apply Real.circleAverage_congr_sphere
          intro z _hz
          simp
    _ = 1 := h

/--
%%handwave
name:
  Poisson kernel is nonnegative
statement:
  If the boundary variable lies on the boundary circle and the pole lies in
  the disk, then the Poisson kernel is nonnegative.
proof:
  Use the lower Herglotz-Riesz estimate from Mathlib and identify the real
  part of the Herglotz-Riesz kernel with the Poisson kernel.
-/
theorem poissonKernel_nonneg_of_mem_sphere_of_mem_ball
    (c : ℂ) {r : ℝ} {w z : ℂ}
    (hz : z ∈ Metric.sphere c r) (hw : w ∈ Metric.ball c r) :
    0 ≤ poissonKernel c w z := by
  have hw_norm : ‖w - c‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hleft_nonneg : 0 ≤ (r - ‖w - c‖) / (r + ‖w - c‖) := by
    exact div_nonneg (sub_nonneg.mpr hw_norm.le)
      (add_nonneg (le_trans (norm_nonneg _) hw_norm.le) (norm_nonneg _))
  have hlower :=
    le_re_herglotzRieszKernel (c := c) (z := z) (w := w) hz hw
  rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
    herglotzRieszKernel_def]
  exact hleft_nonneg.trans hlower

/--
%%handwave
name:
  Poisson kernel is positive
statement:
  If the boundary variable lies on the boundary circle and the pole lies
  strictly inside the disk, then the Poisson kernel is positive.
proof:
  The numerator is \(r^2-|w-c|^2>0\).  The denominator is positive because a
  point \(z\) with \(|z-c|=r\) cannot equal an interior point \(w\).
-/
theorem poissonKernel_pos_of_mem_sphere_of_mem_ball
    (c : ℂ) {r : ℝ} {w z : ℂ}
    (hz : z ∈ Metric.sphere c r) (hw : w ∈ Metric.ball c r) :
    0 < poissonKernel c w z := by
  have hz_norm : ‖z - c‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hw_norm : ‖w - c‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hr : 0 < r := (norm_nonneg (w - c)).trans_lt hw_norm
  have hnum_pos : 0 < ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2 := by
    rw [hz_norm]
    nlinarith [norm_nonneg (w - c)]
  have hden_pos : 0 < ‖(z - c) - (w - c)‖ ^ 2 := by
    refine sq_pos_of_ne_zero ?_
    intro hnorm
    have hsub : (z - c) - (w - c) = 0 := norm_eq_zero.mp hnorm
    have heq : z - c = w - c := sub_eq_zero.mp hsub
    have hnorm_eq : ‖z - c‖ = ‖w - c‖ := by rw [heq]
    nlinarith
  rw [poissonKernel_def]
  exact div_pos hnum_pos hden_pos

/--
%%handwave
name:
  Poisson kernel disk bound
statement:
  If the boundary variable lies on the boundary circle and the pole lies in
  the disk, then the Poisson kernel is bounded above by the usual ratio
  \((r+\lVert w-c\rVert)/(r-\lVert w-c\rVert)\).
proof:
  This is the upper Herglotz-Riesz estimate from Mathlib, rewritten using the
  identity between the Herglotz-Riesz kernel and the Poisson kernel.
-/
theorem poissonKernel_le_disk_bound_of_mem_sphere_of_mem_ball
    (c : ℂ) {r : ℝ} {w z : ℂ}
    (hz : z ∈ Metric.sphere c r) (hw : w ∈ Metric.ball c r) :
    poissonKernel c w z ≤ (r + ‖w - c‖) / (r - ‖w - c‖) := by
  have hupper :=
    re_herglotzRieszKernel_le (c := c) (z := z) (w := w) hz hw
  rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
    herglotzRieszKernel_def]
  exact hupper

/--
%%handwave
name:
  Poisson kernel is continuous on the boundary circle
statement:
  For an interior pole, the Poisson kernel is continuous as a function of the
  boundary variable on the boundary circle.
proof:
  The kernel is a quotient of continuous functions of \(z\), and its
  denominator \(|z-w|^2\) does not vanish when \(|z-c|=r>|w-c|\).
-/
theorem poissonKernel_continuousOn_sphere_of_mem_ball
    (c : ℂ) {r : ℝ} {w : ℂ} (hw : w ∈ Metric.ball c r) :
    ContinuousOn (fun z : ℂ ↦ poissonKernel c w z) (Metric.sphere c r) := by
  have hden : ∀ z ∈ Metric.sphere c r, ‖(z - c) - (w - c)‖ ^ 2 ≠ 0 := by
    intro z hz hzero
    have hz_norm : ‖z - c‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hw_norm : ‖w - c‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hnorm : ‖(z - c) - (w - c)‖ = 0 := sq_eq_zero_iff.mp hzero
    have hsub : (z - c) - (w - c) = 0 := norm_eq_zero.mp hnorm
    have heq : z - c = w - c := sub_eq_zero.mp hsub
    have hnorm_eq : ‖z - c‖ = ‖w - c‖ := by rw [heq]
    nlinarith
  change ContinuousOn
    (fun z : ℂ ↦ (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) /
      ‖(z - c) - (w - c)‖ ^ 2) (Metric.sphere c r)
  exact
    (by fun_prop :
      ContinuousOn (fun z : ℂ ↦ ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) (Metric.sphere c r)).div
    (by fun_prop :
      ContinuousOn (fun z : ℂ ↦ ‖(z - c) - (w - c)‖ ^ 2) (Metric.sphere c r))
    hden

/--
%%handwave
name:
  Poisson integrand is circle-integrable
statement:
  If the boundary data is continuous on the boundary circle and the pole lies
  inside the disk, then the Poisson kernel multiplied by the boundary data is
  integrable over the boundary circle.
proof:
  [The Poisson kernel is continuous on the boundary circle](lean:JJMath.Uniformization.poissonKernel_continuousOn_sphere_of_mem_ball); multiplying by the continuous boundary data gives a continuous, hence circle-integrable, function.
-/
theorem poissonKernel_mul_boundaryData_circleIntegrable
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * φ z) c r := by
  have hφ_sphere : ContinuousOn φ (Metric.sphere c r) := by
    rw [← frontier_ball c hr.ne']
    exact hφ
  exact ContinuousOn.circleIntegrable hr.le
    ((poissonKernel_continuousOn_sphere_of_mem_ball c hw).mul hφ_sphere)

/--
%%handwave
name:
  Complex boundary data is circle-integrable
statement:
  Continuous real boundary data, regarded as complex-valued boundary data, is
  integrable over the boundary circle.
proof:
  Composition with the continuous embedding \(\mathbb R\hookrightarrow\mathbb C\)
  preserves continuity on the circle, and continuous functions on a circle
  are circle-integrable.
-/
theorem boundaryData_complex_circleIntegrable
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    CircleIntegrable (fun z : ℂ ↦ (φ z : ℂ)) c r := by
  have hφ_sphere : ContinuousOn φ (Metric.sphere c r) := by
    rw [← frontier_ball c hr.ne']
    exact hφ
  exact ContinuousOn.circleIntegrable hr.le
    (Complex.continuous_ofReal.comp_continuousOn hφ_sphere)

/--
%%handwave
name:
  Cauchy boundary integrand is circle-integrable
statement:
  If the pole is inside the disk, then the Cauchy kernel times continuous
  boundary data is integrable over the boundary circle.
proof:
  Since an interior point \(w\) is not on the boundary circle, \(z\mapsto
  (z-w)^{-1}\) is continuous there.  Its product with the complexified
  boundary data is therefore circle-integrable.
-/
theorem cauchyBoundaryAverage_integrand_circleIntegrable
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    CircleIntegrable (fun z : ℂ ↦ (z - w)⁻¹ * (φ z : ℂ)) c r := by
  have hφ_sphere : ContinuousOn (fun z : ℂ ↦ (φ z : ℂ)) (Metric.sphere c r) := by
    have hφ_sphere_real : ContinuousOn φ (Metric.sphere c r) := by
      rw [← frontier_ball c hr.ne']
      exact hφ
    exact Complex.continuous_ofReal.comp_continuousOn hφ_sphere_real
  have hkernel : ContinuousOn (fun z : ℂ ↦ (z - w)⁻¹) (Metric.sphere c r) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz hzero
    have hz_norm : ‖z - c‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hw_norm : ‖w - c‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hzw : z = w := sub_eq_zero.mp hzero
    have hnorm_eq : ‖z - c‖ = ‖w - c‖ := by rw [hzw]
    nlinarith
  exact ContinuousOn.circleIntegrable hr.le (hkernel.mul hφ_sphere)

/--
%%handwave
name:
  Cauchy-weighted boundary data is circle-integrable
statement:
  The boundary data multiplied by \((z-c)^{-1}\) is circle-integrable on the
  boundary circle.
proof:
  The positive radius ensures that \(z-c\ne0\) on the boundary circle, so the
  reciprocal factor and the complexified boundary data are continuous there.
-/
theorem cauchyWeightedBoundaryData_circleIntegrable
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    CircleIntegrable (fun z : ℂ ↦ (z - c)⁻¹ * (φ z : ℂ)) c r := by
  have hφ_sphere : ContinuousOn (fun z : ℂ ↦ (φ z : ℂ)) (Metric.sphere c r) := by
    have hφ_sphere_real : ContinuousOn φ (Metric.sphere c r) := by
      rw [← frontier_ball c hr.ne']
      exact hφ
    exact Complex.continuous_ofReal.comp_continuousOn hφ_sphere_real
  have hkernel : ContinuousOn (fun z : ℂ ↦ (z - c)⁻¹) (Metric.sphere c r) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz hzero
    have hz_norm : ‖z - c‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzc : z - c = 0 := hzero
    have : ‖z - c‖ = 0 := by rw [hzc, norm_zero]
    nlinarith
  exact ContinuousOn.circleIntegrable hr.le (hkernel.mul hφ_sphere)

/--
%%handwave
name:
  Cauchy boundary average as a Cauchy integral
statement:
  The circle-average definition of the Cauchy boundary average equals the
  normalized Cauchy integral of the boundary data multiplied by \((z-c)^{-1}\).
proof:
  Replace the circle average by its normalized circle-integral expression and
  combine the two reciprocal factors by elementary complex algebra.
-/
theorem cauchyBoundaryAverage_eq_cauchyIntegral
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ) (w : ℂ) :
    cauchyBoundaryAverage c r φ w =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(c, r), (z - w)⁻¹ • ((z - c)⁻¹ * (φ z : ℂ)) := by
  rw [cauchyBoundaryAverage, Real.circleAverage_eq_circleIntegral hr.ne']
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  simp only [smul_eq_mul]
  ring

/--
%%handwave
name:
  Cauchy boundary average is analytic
statement:
  The Cauchy boundary average is analytic in the pole throughout the open disk.
proof:
  [The weighted boundary data is circle-integrable](lean:JJMath.Uniformization.cauchyWeightedBoundaryData_circleIntegrable), so its Cauchy integral is analytic off the circle; [the circle-average formula is that normalized Cauchy integral](lean:JJMath.Uniformization.cauchyBoundaryAverage_eq_cauchyIntegral).
-/
theorem cauchyBoundaryAverage_analyticOnNhd
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    AnalyticOnNhd ℂ (cauchyBoundaryAverage c r φ) (Metric.ball c r) := by
  have hf : CircleIntegrable (fun z : ℂ ↦ (z - c)⁻¹ * (φ z : ℂ)) c r :=
    cauchyWeightedBoundaryData_circleIntegrable c hr φ hφ
  have hf_nn :
      CircleIntegrable (fun z : ℂ ↦ (z - c)⁻¹ * (φ z : ℂ))
        c (↑(Real.toNNReal r) : ℝ) := by
    simpa [Real.coe_toNNReal, hr.le] using hf
  have hR_nn : 0 < Real.toNNReal r := by
    exact NNReal.coe_pos.mp (by simpa [Real.coe_toNNReal, hr.le] using hr)
  have hCauchy :
      AnalyticOnNhd ℂ
        (fun w ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ z in C(c, r), (z - w)⁻¹ • ((z - c)⁻¹ * (φ z : ℂ)))
        (Metric.ball c r) := by
      have h :=
        (hasFPowerSeriesOn_cauchy_integral (c := c) (R := Real.toNNReal r)
          hf_nn hR_nn).analyticOnNhd
      simpa [Real.coe_toNNReal, hr.le, Metric.eball_coe] using h
  refine hCauchy.congr Metric.isOpen_ball ?_
  intro w hw
  exact (cauchyBoundaryAverage_eq_cauchyIntegral c hr φ w).symm

/--
%%handwave
name:
  Complex Poisson potential is analytic
statement:
  The complex Poisson disk potential is analytic in the open disk.
proof:
  It is the sum of a constant and the product of the affine function
  \(2(w-c)\) with [an analytic Cauchy boundary average](lean:JJMath.Uniformization.cauchyBoundaryAverage_analyticOnNhd).
-/
theorem poissonDiskComplexPotential_analyticOnNhd
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    AnalyticOnNhd ℂ (poissonDiskComplexPotential c r φ) (Metric.ball c r) := by
  have hconst :
      AnalyticOnNhd ℂ
        (fun _ : ℂ ↦ Real.circleAverage (fun z : ℂ ↦ (φ z : ℂ)) c r)
        (Metric.ball c r) := analyticOnNhd_const
  have hlinear :
      AnalyticOnNhd ℂ (fun w : ℂ ↦ (2 : ℂ) * (w - c)) (Metric.ball c r) := by
    exact analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const)
  have hcauchy := cauchyBoundaryAverage_analyticOnNhd c hr φ hφ
  simpa [poissonDiskComplexPotential] using hconst.add (hlinear.mul hcauchy)

/--
%%handwave
name:
  Complex Poisson potential has Poisson real part
statement:
  Inside the disk, the real part of the complex Poisson potential is the
  Poisson extension.
proof:
  Combine the constant term and Cauchy term into the circle average of the
  Herglotz--Riesz kernel times \(\varphi\).  Taking real parts through this
  integral replaces that kernel by the Poisson kernel and gives the Poisson
  extension.
-/
theorem poissonDiskComplexPotential_re_eq_poissonDiskExtension_of_mem_ball
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    (poissonDiskComplexPotential c r φ w).re = poissonDiskExtension c r φ w := by
  have hφ_int : CircleIntegrable (fun z : ℂ ↦ (φ z : ℂ)) c r :=
    boundaryData_complex_circleIntegrable c hr φ hφ
  have hcauchy_int :
      CircleIntegrable (fun z : ℂ ↦ (z - w)⁻¹ * (φ z : ℂ)) c r :=
    cauchyBoundaryAverage_integrand_circleIntegrable c hr hw φ hφ
  have hherg_int :
      CircleIntegrable (fun z : ℂ ↦ herglotzRieszKernel c w z * (φ z : ℂ)) c r := by
    have hφ_sphere : ContinuousOn (fun z : ℂ ↦ (φ z : ℂ)) (Metric.sphere c r) := by
      have hφ_sphere_real : ContinuousOn φ (Metric.sphere c r) := by
        rw [← frontier_ball c hr.ne']
        exact hφ
      exact Complex.continuous_ofReal.comp_continuousOn hφ_sphere_real
    have hkernel : ContinuousOn (fun z : ℂ ↦ herglotzRieszKernel c w z) (Metric.sphere c r) := by
      have hden : ∀ z ∈ Metric.sphere c r, (z - c) - (w - c) ≠ 0 := by
        intro z hz hzero
        have hz_norm : ‖z - c‖ = r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hz
        have hw_norm : ‖w - c‖ < r := by
          simpa [Metric.mem_ball, dist_eq_norm] using hw
        have heq : z - c = w - c := sub_eq_zero.mp hzero
        have hnorm_eq : ‖z - c‖ = ‖w - c‖ := by rw [heq]
        nlinarith
      rw [herglotzRieszKernel_fun_def]
      exact ((continuousOn_id.sub continuousOn_const).add
        (continuousOn_const.sub continuousOn_const)).div
        ((continuousOn_id.sub continuousOn_const).sub
          (continuousOn_const.sub continuousOn_const)) hden
    exact ContinuousOn.circleIntegrable hr.le (hkernel.mul hφ_sphere)
  have hcomplex :
      poissonDiskComplexPotential c r φ w =
        Real.circleAverage (fun z : ℂ ↦ herglotzRieszKernel c w z * (φ z : ℂ)) c r := by
    rw [poissonDiskComplexPotential, cauchyBoundaryAverage]
    change
      Real.circleAverage (fun z : ℂ ↦ (φ z : ℂ)) c r +
        ((2 : ℂ) * (w - c)) •
          Real.circleAverage (fun z : ℂ ↦ (z - w)⁻¹ * (φ z : ℂ)) c r =
        Real.circleAverage (fun z : ℂ ↦ herglotzRieszKernel c w z * (φ z : ℂ)) c r
    rw [← Real.circleAverage_fun_smul (a := (2 : ℂ) * (w - c))
      (f := fun z : ℂ ↦ (z - w)⁻¹ * (φ z : ℂ)) (c := c) (R := r)]
    rw [← Real.circleAverage_fun_add hφ_int]
    · apply Real.circleAverage_congr_sphere
      intro z hz
      have hz_norm : ‖z - c‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm, abs_of_pos hr] using hz
      have hw_norm : ‖w - c‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hzw : z - w ≠ 0 := by
        intro hzero
        have hsub : z = w := sub_eq_zero.mp hzero
        have hnorm_eq : ‖z - c‖ = ‖w - c‖ := by rw [hsub]
        nlinarith
      change (φ z : ℂ) + (2 * (w - c)) * ((z - w)⁻¹ * (φ z : ℂ)) =
        herglotzRieszKernel c w z * (φ z : ℂ)
      rw [herglotzRieszKernel_def]
      field_simp [hzw]
      ring_nf
    · simpa only [Pi.smul_apply, smul_eq_mul] using
        (hcauchy_int.const_smul)
  rw [hcomplex]
  rw [← Complex.reCLM_apply,
    ← Complex.reCLM.circleAverage_comp_comm hherg_int]
  apply Real.circleAverage_congr_sphere
  intro z hz
  simp only [Function.comp_apply, Complex.reCLM_apply]
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  simp [mul_comm]

/--
%%handwave
name:
  Poisson disk Dirichlet candidate
statement:
  The Dirichlet candidate is the Poisson extension in the open disk and the
  prescribed boundary function outside the open disk.
-/
noncomputable def poissonDiskDirichletCandidate
    (c : ℂ) (r : ℝ) (φ : ℂ → ℝ) : ℂ → ℝ :=
  by
    classical
    exact fun w ↦ if w ∈ Metric.ball c r then poissonDiskExtension c r φ w else φ w

/--
%%handwave
name:
  Poisson candidate inside the disk
statement:
  Inside the disk, the Poisson Dirichlet candidate is the Poisson extension.
proof:
  This is the interior branch of the piecewise definition of the candidate.
-/
theorem poissonDiskDirichletCandidate_eq_extension_of_mem
    (c : ℂ) (r : ℝ) (φ : ℂ → ℝ) {w : ℂ}
    (hw : w ∈ Metric.ball c r) :
    poissonDiskDirichletCandidate c r φ w = poissonDiskExtension c r φ w := by
  simp [poissonDiskDirichletCandidate, hw]

/--
%%handwave
name:
  Poisson candidate outside the disk
statement:
  Outside the open disk, the Poisson Dirichlet candidate is the prescribed
  ambient boundary function.
proof:
  This is the exterior branch of the piecewise definition of the candidate.
-/
theorem poissonDiskDirichletCandidate_eq_data_of_not_mem
    (c : ℂ) (r : ℝ) (φ : ℂ → ℝ) {w : ℂ}
    (hw : w ∉ Metric.ball c r) :
    poissonDiskDirichletCandidate c r φ w = φ w := by
  simp [poissonDiskDirichletCandidate, hw]

/--
%%handwave
name:
  Poisson extension at the center
statement:
  At the center of the disk, the Poisson extension is the ordinary circle
  average of the boundary data.
proof:
  [The centered Poisson kernel is \(1\) on the boundary circle](lean:JJMath.Uniformization.poissonKernel_center_eq_one_of_mem_frontier), so the Poisson integral reduces to the circle average of \(\varphi\).
-/
theorem poissonDiskExtension_center_eq_circleAverage
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ) :
    poissonDiskExtension c r φ c = Real.circleAverage φ c r := by
  rw [poissonDiskExtension]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hz_frontier : z ∈ frontier (Metric.ball c r) := by
    rw [frontier_ball c hr.ne']
    simpa [abs_of_pos hr] using hz
  change poissonKernel c c z * φ z = φ z
  rw [poissonKernel_center_eq_one_of_mem_frontier c hr hz_frontier]
  simp

/--
%%handwave
name:
  Poisson candidate at the center
statement:
  At the center of a positive-radius disk, the Poisson Dirichlet candidate is
  the ordinary circle average of the boundary data.
proof:
  The center lies in the disk, so [the candidate equals the Poisson extension there](lean:JJMath.Uniformization.poissonDiskDirichletCandidate_eq_extension_of_mem), and [the centered extension is the circle average](lean:JJMath.Uniformization.poissonDiskExtension_center_eq_circleAverage).
-/
theorem poissonDiskDirichletCandidate_center_eq_circleAverage
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ) :
    poissonDiskDirichletCandidate c r φ c = Real.circleAverage φ c r := by
  have hc : c ∈ Metric.ball c r := by
    simpa [Metric.mem_ball] using hr
  rw [poissonDiskDirichletCandidate_eq_extension_of_mem c r φ hc,
    poissonDiskExtension_center_eq_circleAverage c hr φ]

/--
%%handwave
name:
  Poisson extension of constant boundary data
statement:
  If the boundary data is constant and the pole lies inside the disk, then the
  Poisson extension has that same constant value.
proof:
  Apply the Poisson integral formula from Mathlib to the corresponding
  constant harmonic function.
-/
theorem poissonDiskExtension_const_of_mem_ball
    (c : ℂ) {r : ℝ} {w : ℂ} (hw : w ∈ Metric.ball c r) (a : ℝ) :
    poissonDiskExtension c r (fun _ : ℂ ↦ a) w = a := by
  simpa [poissonDiskExtension, Pi.mul_apply] using
    (InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
      (f := fun _ : ℂ ↦ a)
      (c := c) (R := r) (by simp) hw)

/--
%%handwave
name:
  Poisson extension respects upper boundary bounds
statement:
  If continuous boundary data is bounded above by a constant on the boundary
  circle, then its Poisson extension is bounded above by the same constant at
  every interior point.
proof:
  The Poisson kernel is nonnegative on the boundary circle and has average
  one.  Multiply the boundary inequality by the kernel and average.
-/
theorem poissonDiskExtension_le_of_boundaryData_le
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) {M : ℝ}
    (hM : ∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) :
    poissonDiskExtension c r φ w ≤ M := by
  have hint : CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * φ z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw φ hφ
  have hconst_int :
      CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * (fun _ : ℂ ↦ M) z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw (fun _ : ℂ ↦ M) (by fun_prop)
  calc
    poissonDiskExtension c r φ w
        = Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * φ z) c r := rfl
    _ ≤ Real.circleAverage
          (fun z : ℂ ↦ poissonKernel c w z * (fun _ : ℂ ↦ M) z) c r := by
        apply Real.circleAverage_mono hint hconst_int
        intro z hz
        have hz_sphere : z ∈ Metric.sphere c r := by
          simpa [abs_of_pos hr] using hz
        have hz_frontier : z ∈ frontier (Metric.ball c r) := by
          rw [frontier_ball c hr.ne']
          exact hz_sphere
        exact mul_le_mul_of_nonneg_left (hM z hz_frontier)
          (poissonKernel_nonneg_of_mem_sphere_of_mem_ball c hz_sphere hw)
    _ = M := by
        simpa [poissonDiskExtension] using
          poissonDiskExtension_const_of_mem_ball c hw M

/--
%%handwave
name:
  Poisson extension respects lower boundary bounds
statement:
  If continuous boundary data is bounded below by a constant on the boundary
  circle, then its Poisson extension is bounded below by the same constant at
  every interior point.
proof:
  The Poisson kernel is nonnegative on the boundary circle and has average
  one.  Multiply the boundary inequality by the kernel and average.
-/
theorem le_poissonDiskExtension_of_le_boundaryData
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) {m : ℝ}
    (hm : ∀ z ∈ frontier (Metric.ball c r), m ≤ φ z) :
    m ≤ poissonDiskExtension c r φ w := by
  have hconst_int :
      CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * (fun _ : ℂ ↦ m) z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw (fun _ : ℂ ↦ m) (by fun_prop)
  have hint : CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * φ z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw φ hφ
  calc
    m = Real.circleAverage
          (fun z : ℂ ↦ poissonKernel c w z * (fun _ : ℂ ↦ m) z) c r := by
        simpa [poissonDiskExtension] using
          (poissonDiskExtension_const_of_mem_ball c hw m).symm
    _ ≤ Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * φ z) c r := by
        apply Real.circleAverage_mono hconst_int hint
        intro z hz
        have hz_sphere : z ∈ Metric.sphere c r := by
          simpa [abs_of_pos hr] using hz
        have hz_frontier : z ∈ frontier (Metric.ball c r) := by
          rw [frontier_ball c hr.ne']
          exact hz_sphere
        exact mul_le_mul_of_nonneg_left (hm z hz_frontier)
          (poissonKernel_nonneg_of_mem_sphere_of_mem_ball c hz_sphere hw)
    _ = poissonDiskExtension c r φ w := rfl

/--
%%handwave
name:
  Subtracting a constant from a Poisson extension
statement:
  Subtracting a constant from the Poisson extension is the same as applying
  the Poisson kernel to the boundary data with that constant subtracted.
proof:
  Use linearity of circle averages and the fact that the Poisson extension of
  constant boundary data is constant.
-/
theorem poissonDiskExtension_sub_const_eq_circleAverage
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r))) (a : ℝ) :
    poissonDiskExtension c r φ w - a =
      Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * (φ z - a)) c r := by
  have hφ_int : CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * φ z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw φ hφ
  have hconst_int :
      CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * (fun _ : ℂ ↦ a) z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw (fun _ : ℂ ↦ a) (by fun_prop)
  calc
    poissonDiskExtension c r φ w - a
        = Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * φ z) c r -
            Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * (fun _ : ℂ ↦ a) z) c r := by
          change
            Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * φ z) c r - a =
              Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * φ z) c r -
                Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * (fun _ : ℂ ↦ a) z) c r
          nth_rw 1 [← poissonDiskExtension_const_of_mem_ball c hw a]
          rfl
    _ = Real.circleAverage
          (fun z : ℂ ↦ poissonKernel c w z * φ z -
            poissonKernel c w z * (fun _ : ℂ ↦ a) z) c r := by
          rw [Real.circleAverage_fun_sub hφ_int hconst_int]
    _ = Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * (φ z - a)) c r := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          ring

/--
%%handwave
name:
  Poisson extension preserves uniform closeness to a constant
statement:
  If boundary data is uniformly within \(\varepsilon\) of a constant on the
  boundary circle, then its Poisson extension is also within
  \(\varepsilon\) of that constant at every interior point.
proof:
  Convert the absolute-value bound into upper and lower constant bounds, then
  use the upper and lower bound preservation theorems for the Poisson
  extension.
-/
theorem abs_poissonDiskExtension_sub_const_le_of_boundaryData
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (frontier (Metric.ball c r)))
    {a ε : ℝ}
    (hε : ∀ z ∈ frontier (Metric.ball c r), |φ z - a| ≤ ε) :
    |poissonDiskExtension c r φ w - a| ≤ ε := by
  have hupper : ∀ z ∈ frontier (Metric.ball c r), φ z ≤ a + ε := by
    intro z hz
    have hzε := (abs_sub_le_iff.1 (hε z hz)).1
    linarith
  have hlower : ∀ z ∈ frontier (Metric.ball c r), a - ε ≤ φ z := by
    intro z hz
    have hzε := (abs_sub_le_iff.1 (hε z hz)).2
    linarith
  have hu :
      poissonDiskExtension c r φ w ≤ a + ε :=
    poissonDiskExtension_le_of_boundaryData_le c hr hw φ hφ hupper
  have hl :
      a - ε ≤ poissonDiskExtension c r φ w :=
    le_poissonDiskExtension_of_le_boundaryData c hr hw φ hφ hlower
  rw [abs_sub_le_iff]
  constructor <;> linarith

/--
%%handwave
name:
  Difference of two Poisson extensions
statement:
  The difference between the Poisson extensions of two boundary functions is
  the circle average of the Poisson kernel multiplied by the difference of the
  boundary functions.
proof:
  Expand both Poisson extensions and use linearity of circle averages.
-/
theorem poissonDiskExtension_sub_eq_circleAverage
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ ψ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r)))
    (hψ : ContinuousOn ψ (frontier (Metric.ball c r))) :
    poissonDiskExtension c r φ w - poissonDiskExtension c r ψ w =
      Real.circleAverage
        (fun z : ℂ ↦ poissonKernel c w z * (φ z - ψ z)) c r := by
  have hφ_int : CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * φ z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw φ hφ
  have hψ_int : CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * ψ z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw ψ hψ
  calc
    poissonDiskExtension c r φ w - poissonDiskExtension c r ψ w
        = Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * φ z) c r -
            Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * ψ z) c r := rfl
    _ = Real.circleAverage
          (fun z : ℂ ↦ poissonKernel c w z * φ z -
            poissonKernel c w z * ψ z) c r := by
          rw [Real.circleAverage_fun_sub hφ_int hψ_int]
    _ = Real.circleAverage
          (fun z : ℂ ↦ poissonKernel c w z * (φ z - ψ z)) c r := by
          apply Real.circleAverage_congr_sphere
          intro z _hz
          ring

/--
%%handwave
name:
  Poisson extension is uniformly continuous in the boundary data
statement:
  If two boundary functions differ by at most \(\varepsilon\) on the boundary
  circle, then their Poisson extensions differ by at most \(\varepsilon\) at
  every point of the open disk.
proof:
  Write the difference as the circle average of the Poisson kernel times the
  boundary difference.  The Poisson kernel is nonnegative and has average one.
-/
theorem abs_poissonDiskExtension_sub_poissonDiskExtension_le_of_boundaryData
    (c : ℂ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Metric.ball c r)
    (φ ψ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r)))
    (hψ : ContinuousOn ψ (frontier (Metric.ball c r)))
    {ε : ℝ}
    (hε : ∀ z ∈ frontier (Metric.ball c r), |φ z - ψ z| ≤ ε) :
    |poissonDiskExtension c r φ w - poissonDiskExtension c r ψ w| ≤ ε := by
  have hdiff_cont :
      ContinuousOn (fun z : ℂ ↦ φ z - ψ z) (frontier (Metric.ball c r)) :=
    hφ.sub hψ
  have hdiff_int :
      CircleIntegrable
        (fun z : ℂ ↦ poissonKernel c w z * (φ z - ψ z)) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw
      (fun z : ℂ ↦ φ z - ψ z) hdiff_cont
  have habs_int :
      CircleIntegrable
        (fun z : ℂ ↦ |poissonKernel c w z * (φ z - ψ z)|) c r :=
    hdiff_int.abs
  have hconst_int :
      CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * ε) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw
      (fun _ : ℂ ↦ ε) (by fun_prop)
  have hpoint :
      ∀ z ∈ Metric.sphere c |r|,
        |poissonKernel c w z * (φ z - ψ z)| ≤ poissonKernel c w z * ε := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c r := by
      simpa [abs_of_pos hr] using hz
    have hz_frontier : z ∈ frontier (Metric.ball c r) := by
      rw [frontier_ball c hr.ne']
      exact hz_sphere
    have hP_nonneg : 0 ≤ poissonKernel c w z :=
      poissonKernel_nonneg_of_mem_sphere_of_mem_ball c hz_sphere hw
    calc
      |poissonKernel c w z * (φ z - ψ z)|
          = poissonKernel c w z * |φ z - ψ z| := by
              rw [abs_mul, abs_of_nonneg hP_nonneg]
      _ ≤ poissonKernel c w z * ε :=
              mul_le_mul_of_nonneg_left (hε z hz_frontier) hP_nonneg
  calc
    |poissonDiskExtension c r φ w - poissonDiskExtension c r ψ w|
        = |Real.circleAverage
            (fun z : ℂ ↦ poissonKernel c w z * (φ z - ψ z)) c r| := by
          rw [poissonDiskExtension_sub_eq_circleAverage c hr hw φ ψ hφ hψ]
    _ ≤ Real.circleAverage
          (fun z : ℂ ↦ |poissonKernel c w z * (φ z - ψ z)|) c r :=
        Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * ε) c r := by
        exact Real.circleAverage_mono habs_int hconst_int hpoint
    _ = ε := by
        simpa [poissonDiskExtension] using
          poissonDiskExtension_const_of_mem_ball c hw ε

/--
%%handwave
name:
  Poisson kernel is small away from a nearby boundary point
statement:
  Let \(r,\delta>0\), let \(a,\zeta\in\partial B(c,r)\), and let
  \(w\in\overline B(c,r)\).  If \(d(\zeta,a)\ge\delta\) and
  \(d(w,a)<\delta/2\), then
  \[P_{c,r}(w,\zeta)\le \frac{2r\,d(w,a)}{(\delta/2)^2}.\]
proof:
  The reverse triangle inequality bounds the numerator by
  \(2r\,d(w,a)\), while \(d(\zeta,w)\ge \delta/2\) bounds the denominator
  below by \((\delta/2)^2\).  Dividing gives
  \[P(w,\zeta)\le \frac{2r\,d(w,a)}{(\delta/2)^2}.\]
-/
theorem poissonKernel_le_far_of_mem_closedBall
    (c : ℂ) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    {a w ζ : ℂ} (ha : a ∈ frontier (Metric.ball c r))
    (hw : w ∈ closure (Metric.ball c r)) (hζ : ζ ∈ Metric.sphere c r)
    (hfar : δ ≤ dist ζ a) (hw_near : dist w a < δ / 2) :
    poissonKernel c w ζ ≤ (2 * r * dist w a) / (δ / 2) ^ 2 := by
  have ha_sphere : a ∈ Metric.sphere c r := by
    rw [frontier_ball c hr.ne'] at ha
    exact ha
  have ha_norm : ‖a - c‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using ha_sphere
  have hζ_norm : ‖ζ - c‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hζ
  have hw_closed : w ∈ Metric.closedBall c r := by
    simpa [closure_ball c hr.ne'] using hw
  have hw_norm_le : ‖w - c‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw_closed
  have hdist_nonneg : 0 ≤ dist w a := dist_nonneg
  have hnorm_w_nonneg : 0 ≤ ‖w - c‖ := norm_nonneg _
  have hdist_norm :
      r - ‖w - c‖ ≤ dist w a := by
    have h := norm_sub_norm_le (a - c) (w - c)
    rw [ha_norm] at h
    have hsub : (a - c) - (w - c) = a - w := by ring
    rw [hsub] at h
    simpa [dist_eq_norm, norm_sub_rev] using h
  have hnum_nonneg : 0 ≤ ‖ζ - c‖ ^ 2 - ‖w - c‖ ^ 2 := by
    rw [hζ_norm]
    nlinarith
  have hnum_le : ‖ζ - c‖ ^ 2 - ‖w - c‖ ^ 2 ≤ 2 * r * dist w a := by
    rw [hζ_norm]
    nlinarith
  have hdistζw_ge : δ / 2 ≤ dist ζ w := by
    have htri : dist ζ a ≤ dist ζ w + dist w a := dist_triangle ζ w a
    nlinarith [hfar, hw_near]
  have hden_ge :
      (δ / 2) ^ 2 ≤ ‖(ζ - c) - (w - c)‖ ^ 2 := by
    have hsub : (ζ - c) - (w - c) = ζ - w := by ring
    rw [hsub, ← dist_eq_norm]
    nlinarith [(dist_nonneg : 0 ≤ dist ζ w), hdistζw_ge]
  have hden_pos : 0 < ‖(ζ - c) - (w - c)‖ ^ 2 := by
    have hδhalf_pos : 0 < δ / 2 := by positivity
    nlinarith
  rw [poissonKernel_def]
  calc
    (‖ζ - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(ζ - c) - (w - c)‖ ^ 2
        ≤ (2 * r * dist w a) / ‖(ζ - c) - (w - c)‖ ^ 2 := by
          exact div_le_div_of_nonneg_right hnum_le (sq_nonneg _)
    _ ≤ (2 * r * dist w a) / (δ / 2) ^ 2 := by
          have htop_nonneg : 0 ≤ 2 * r * dist w a := by positivity
          have hδhalf_sq_pos : 0 < (δ / 2) ^ 2 := by positivity
          exact div_le_div_of_nonneg_left htop_nonneg hδhalf_sq_pos hden_ge

/--
%%handwave
name:
  Poisson extension is close to a boundary value near that boundary point
statement:
  Let \(r,\delta>0\), \(\eta,M\ge0\), \(a\in\partial B(c,r)\), and
  \(w\in B(c,r)\) with \(d(w,a)<\delta/2\).  If the continuous boundary
  function \(\varphi\) satisfies
  \(|\varphi(\zeta)-\varphi(a)|\le\eta\) when \(d(\zeta,a)<\delta\) and is
  everywhere bounded by \(M\) relative to \(\varphi(a)\), then
  \[|P[\varphi](w)-\varphi(a)|\le \eta+M\frac{2r}{(\delta/2)^2}d(w,a).\]
proof:
  Write the difference as the Poisson average of
  \(\varphi(\zeta)-\varphi(a)\).  On \(d(\zeta,a)<\delta\) use the local
  oscillation bound \(\eta\); on its complement use [the far-field kernel estimate \(P(w,\zeta)\le 2r\,d(w,a)/(\delta/2)^2\)](lean:JJMath.Uniformization.poissonKernel_le_far_of_mem_closedBall) and the global bound \(M\).  Positivity and average one for the kernel then yield the stated estimate.
-/
theorem abs_poissonDiskExtension_sub_boundary_value_le
    (c : ℂ) {r δ η M : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hη : 0 ≤ η) (hM : 0 ≤ M) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r)))
    {a w : ℂ} (ha : a ∈ frontier (Metric.ball c r))
    (hw : w ∈ Metric.ball c r) (hw_near : dist w a < δ / 2)
    (hlocal :
      ∀ ζ ∈ frontier (Metric.ball c r), dist ζ a < δ → |φ ζ - φ a| ≤ η)
    (hbound : ∀ ζ ∈ frontier (Metric.ball c r), |φ ζ - φ a| ≤ M) :
    |poissonDiskExtension c r φ w - φ a| ≤
      η + M * (2 * r / (δ / 2) ^ 2) * dist w a := by
  let A : ℝ := M * (2 * r / (δ / 2) ^ 2)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hdiff_cont :
      ContinuousOn (fun ζ : ℂ ↦ φ ζ - φ a) (frontier (Metric.ball c r)) :=
    hφ.sub continuousOn_const
  have hdiff_int :
      CircleIntegrable
        (fun ζ : ℂ ↦ poissonKernel c w ζ * (φ ζ - φ a)) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw
      (fun ζ : ℂ ↦ φ ζ - φ a) hdiff_cont
  have habs_int :
      CircleIntegrable
        (fun ζ : ℂ ↦ |poissonKernel c w ζ * (φ ζ - φ a)|) c r :=
    hdiff_int.abs
  have hPη_int :
      CircleIntegrable (fun ζ : ℂ ↦ poissonKernel c w ζ * η) c r := by
    simpa using
      poissonKernel_mul_boundaryData_circleIntegrable c hr hw
        (fun _ : ℂ ↦ η) (by fun_prop)
  have hconst_int :
      CircleIntegrable (fun _ : ℂ ↦ A * dist w a) c r :=
    circleIntegrable_const (A * dist w a) c r
  have hRhs_int :
      CircleIntegrable
        (fun ζ : ℂ ↦ poissonKernel c w ζ * η + A * dist w a) c r :=
    hPη_int.add hconst_int
  have hpoint :
      ∀ ζ ∈ Metric.sphere c |r|,
        |poissonKernel c w ζ * (φ ζ - φ a)| ≤
          poissonKernel c w ζ * η + A * dist w a := by
    intro ζ hζ_abs
    have hζ : ζ ∈ Metric.sphere c r := by
      simpa [abs_of_pos hr] using hζ_abs
    have hζ_frontier : ζ ∈ frontier (Metric.ball c r) := by
      rw [frontier_ball c hr.ne']
      exact hζ
    have hP_nonneg : 0 ≤ poissonKernel c w ζ :=
      poissonKernel_nonneg_of_mem_sphere_of_mem_ball c hζ hw
    by_cases hnear : dist ζ a < δ
    · have hdiff_le : |φ ζ - φ a| ≤ η := hlocal ζ hζ_frontier hnear
      calc
        |poissonKernel c w ζ * (φ ζ - φ a)|
            = poissonKernel c w ζ * |φ ζ - φ a| := by
              rw [abs_mul, abs_of_nonneg hP_nonneg]
        _ ≤ poissonKernel c w ζ * η :=
              mul_le_mul_of_nonneg_left hdiff_le hP_nonneg
        _ ≤ poissonKernel c w ζ * η + A * dist w a := by
              have htail_nonneg : 0 ≤ A * dist w a := by positivity
              linarith
    · have hfar : δ ≤ dist ζ a := le_of_not_gt hnear
      have hP_le :
          poissonKernel c w ζ ≤ (2 * r * dist w a) / (δ / 2) ^ 2 :=
        poissonKernel_le_far_of_mem_closedBall c hr hδ ha (subset_closure hw)
          hζ hfar hw_near
      have hdiff_le : |φ ζ - φ a| ≤ M := hbound ζ hζ_frontier
      have hB_nonneg : 0 ≤ (2 * r * dist w a) / (δ / 2) ^ 2 := by
        positivity
      have hmain :
          poissonKernel c w ζ * |φ ζ - φ a| ≤ A * dist w a := by
        calc
          poissonKernel c w ζ * |φ ζ - φ a|
              ≤ ((2 * r * dist w a) / (δ / 2) ^ 2) * M :=
                  mul_le_mul hP_le hdiff_le (abs_nonneg _) hB_nonneg
          _ = A * dist w a := by
                  dsimp [A]
                  ring
      calc
        |poissonKernel c w ζ * (φ ζ - φ a)|
            = poissonKernel c w ζ * |φ ζ - φ a| := by
              rw [abs_mul, abs_of_nonneg hP_nonneg]
        _ ≤ A * dist w a := hmain
        _ ≤ poissonKernel c w ζ * η + A * dist w a := by
              have hhead_nonneg : 0 ≤ poissonKernel c w ζ * η := by
                positivity
              linarith
  calc
    |poissonDiskExtension c r φ w - φ a|
        = |Real.circleAverage
            (fun ζ : ℂ ↦ poissonKernel c w ζ * (φ ζ - φ a)) c r| := by
          rw [poissonDiskExtension_sub_const_eq_circleAverage c hr hw φ hφ (φ a)]
    _ ≤ Real.circleAverage
          (fun ζ : ℂ ↦ |poissonKernel c w ζ * (φ ζ - φ a)|) c r :=
        Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage
          (fun ζ : ℂ ↦ poissonKernel c w ζ * η + A * dist w a) c r := by
        exact Real.circleAverage_mono habs_int hRhs_int hpoint
    _ = η + A * dist w a := by
        rw [Real.circleAverage_fun_add hPη_int hconst_int]
        have hPη_avg :
            Real.circleAverage (fun ζ : ℂ ↦ poissonKernel c w ζ * η) c r = η := by
          simpa [poissonDiskExtension] using
            poissonDiskExtension_const_of_mem_ball c hw η
        have hconst_avg :
            Real.circleAverage (fun _ : ℂ ↦ A * dist w a) c r =
              A * dist w a :=
          Real.circleAverage_const (A * dist w a) c r
        rw [hPη_avg, hconst_avg]
    _ = η + M * (2 * r / (δ / 2) ^ 2) * dist w a := by
        dsimp [A]

/--
%%handwave
name:
  Poisson candidate respects upper boundary bounds
statement:
  On the closed disk, the Poisson Dirichlet candidate is bounded above by any
  constant that bounds the boundary data above.
proof:
  At interior points apply the upper bound for the Poisson extension; at
  boundary points the candidate equals the prescribed data.
-/
theorem poissonDiskDirichletCandidate_le_of_boundaryData_le
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r))) {M : ℝ}
    (hM : ∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) :
    ∀ w ∈ closure (Metric.ball c r),
      poissonDiskDirichletCandidate c r φ w ≤ M := by
  intro w hw
  by_cases hw_ball : w ∈ Metric.ball c r
  · rw [poissonDiskDirichletCandidate_eq_extension_of_mem c r φ hw_ball]
    exact poissonDiskExtension_le_of_boundaryData_le c hr hw_ball φ hφ hM
  · have hw_frontier : w ∈ frontier (Metric.ball c r) := by
      simpa [frontier, Metric.isOpen_ball.interior_eq] using And.intro hw hw_ball
    rw [poissonDiskDirichletCandidate_eq_data_of_not_mem c r φ hw_ball]
    exact hM w hw_frontier

/--
%%handwave
name:
  Poisson candidate respects lower boundary bounds
statement:
  On the closed disk, the Poisson Dirichlet candidate is bounded below by any
  constant that bounds the boundary data below.
proof:
  At interior points apply the lower bound for the Poisson extension; at
  boundary points the candidate equals the prescribed data.
-/
theorem le_poissonDiskDirichletCandidate_of_le_boundaryData
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r))) {m : ℝ}
    (hm : ∀ z ∈ frontier (Metric.ball c r), m ≤ φ z) :
    ∀ w ∈ closure (Metric.ball c r),
      m ≤ poissonDiskDirichletCandidate c r φ w := by
  intro w hw
  by_cases hw_ball : w ∈ Metric.ball c r
  · rw [poissonDiskDirichletCandidate_eq_extension_of_mem c r φ hw_ball]
    exact le_poissonDiskExtension_of_le_boundaryData c hr hw_ball φ hφ hm
  · have hw_frontier : w ∈ frontier (Metric.ball c r) := by
      simpa [frontier, Metric.isOpen_ball.interior_eq] using And.intro hw hw_ball
    rw [poissonDiskDirichletCandidate_eq_data_of_not_mem c r φ hw_ball]
    exact hm w hw_frontier

/--
%%handwave
name:
  Poisson candidate for constant boundary data
statement:
  The Poisson Dirichlet candidate for constant boundary data is the same
  constant function.
proof:
  Split into interior and exterior points.  The Poisson extension of the
  constant \(a\) is \(a\) inside, while the exterior branch is the boundary
  datum itself.
-/
theorem poissonDiskDirichletCandidate_const
    (c : ℂ) (r : ℝ) (a : ℝ) :
    poissonDiskDirichletCandidate c r (fun _ : ℂ ↦ a) = fun _ : ℂ ↦ a := by
  funext w
  by_cases hw : w ∈ Metric.ball c r
  · rw [poissonDiskDirichletCandidate_eq_extension_of_mem c r (fun _ : ℂ ↦ a) hw,
      poissonDiskExtension_const_of_mem_ball c hw a]
  · rw [poissonDiskDirichletCandidate_eq_data_of_not_mem c r (fun _ : ℂ ↦ a) hw]

/--
%%handwave
name:
  Constant functions solve the disk Dirichlet problem
statement:
  A constant function solves the Euclidean disk Dirichlet problem with the
  same constant boundary value.
proof:
  A constant is harmonic, continuous on the closed disk, and equals its
  prescribed constant boundary value pointwise.
-/
theorem constant_solves_euclidean_disk_dirichlet_problem
    (c : ℂ) (r : ℝ) (a : ℝ) :
    SolvesEuclideanDiskDirichletProblem c r (fun _ : ℂ ↦ a) (fun _ : ℂ ↦ a) := by
  exact ⟨by simp, by fun_prop, by intro z hz; rfl⟩

/--
%%handwave
name:
  Poisson candidate solves constant boundary data
statement:
  For constant boundary data, the Poisson Dirichlet candidate solves the
  Euclidean disk Dirichlet problem.
proof:
  [The Poisson candidate is the same constant function](lean:JJMath.Uniformization.poissonDiskDirichletCandidate_const),
  and [constant functions solve the disk Dirichlet problem](lean:JJMath.Uniformization.constant_solves_euclidean_disk_dirichlet_problem).
-/
theorem poissonDiskDirichletCandidate_const_solves
    (c : ℂ) (r : ℝ) (a : ℝ) :
    SolvesEuclideanDiskDirichletProblem c r (fun _ : ℂ ↦ a)
      (poissonDiskDirichletCandidate c r (fun _ : ℂ ↦ a)) := by
  simpa [poissonDiskDirichletCandidate_const] using
    constant_solves_euclidean_disk_dirichlet_problem c r a

/--
%%handwave
name:
  Poisson extension is harmonic
statement:
  The Poisson extension of continuous boundary data is harmonic in the open
  disk.
proof:
  Use the Schwarz integral: [the complex Poisson potential is analytic in the open disk](lean:JJMath.Uniformization.poissonDiskComplexPotential_analyticOnNhd),
  and [its real part is the Poisson extension](lean:JJMath.Uniformization.poissonDiskComplexPotential_re_eq_poissonDiskExtension_of_mem_ball).
  Since real parts of holomorphic functions are harmonic, the Poisson
  extension is harmonic.
-/
theorem poissonDiskExtension_harmonicOn
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    InnerProductSpace.HarmonicOnNhd
      (poissonDiskExtension c r φ) (Metric.ball c r) := by
  intro w hw
  have hcomplex :
      AnalyticAt ℂ (poissonDiskComplexPotential c r φ) w :=
    poissonDiskComplexPotential_analyticOnNhd c hr φ hφ w hw
  have hreal :
      InnerProductSpace.HarmonicAt
        (fun w ↦ (poissonDiskComplexPotential c r φ w).re) w :=
    hcomplex.harmonicAt_re
  have h_eq :
      poissonDiskExtension c r φ =ᶠ[𝓝 w]
        fun w ↦ (poissonDiskComplexPotential c r φ w).re := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with y hy
    exact (poissonDiskComplexPotential_re_eq_poissonDiskExtension_of_mem_ball
      c hr hy φ hφ).symm
  exact (InnerProductSpace.harmonicAt_congr_nhds h_eq).2 hreal

/--
%%handwave
name:
  Poisson candidate is harmonic
statement:
  The Poisson Dirichlet candidate is harmonic in the open disk.
proof:
  [The Poisson extension is harmonic in the disk](lean:JJMath.Uniformization.poissonDiskExtension_harmonicOn), and inside
  the open disk [the Poisson candidate equals the Poisson extension](lean:JJMath.Uniformization.poissonDiskDirichletCandidate_eq_extension_of_mem).
-/
theorem poissonDiskDirichletCandidate_harmonicOn
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    InnerProductSpace.HarmonicOnNhd
      (poissonDiskDirichletCandidate c r φ) (Metric.ball c r) := by
  intro w hw
  have h_eq :
      poissonDiskDirichletCandidate c r φ =ᶠ[𝓝 w] poissonDiskExtension c r φ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with y hy
    exact poissonDiskDirichletCandidate_eq_extension_of_mem c r φ hy
  exact (InnerProductSpace.harmonicAt_congr_nhds h_eq).2
    (poissonDiskExtension_harmonicOn c hr φ hφ w hw)

/--
%%handwave
name:
  Poisson candidate is continuous at the boundary
statement:
  At each boundary point, the Poisson Dirichlet candidate is continuous from
  within the closed disk.
proof:
  The Poisson kernels form an approximate identity on the boundary circle.
  Since the boundary data is continuous at the chosen point,
  [the Poisson extension at a nearby interior point is close to that boundary value](lean:JJMath.Uniformization.abs_poissonDiskExtension_sub_boundary_value_le).
  On the boundary itself the candidate is defined to be the prescribed value.
-/
theorem poissonDiskDirichletCandidate_continuousWithinAt_frontier
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r))) {z : ℂ}
    (hz : z ∈ frontier (Metric.ball c r)) :
    ContinuousWithinAt (poissonDiskDirichletCandidate c r φ)
      (closure (Metric.ball c r)) z := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hz_not_mem : z ∉ Metric.ball c r := by
    intro hz_ball
    have hz_inter : z ∈ Metric.ball c r ∩ frontier (Metric.ball c r) :=
      ⟨hz_ball, hz⟩
    simp [Metric.isOpen_ball.inter_frontier_eq] at hz_inter
  have hz_value : poissonDiskDirichletCandidate c r φ z = φ z :=
    poissonDiskDirichletCandidate_eq_data_of_not_mem c r φ hz_not_mem
  have hη_pos : 0 < ε / 3 := by positivity
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ :=
    (Metric.continuousWithinAt_iff.mp (hφ z hz)) (ε / 3) hη_pos
  have hlocal :
      ∀ ζ ∈ frontier (Metric.ball c r), dist ζ z < δ₀ → |φ ζ - φ z| ≤ ε / 3 := by
    intro ζ hζ hdist
    have hζφ : dist (φ ζ) (φ z) < ε / 3 := hδ₀ hζ hdist
    exact le_of_lt (by simpa [Real.dist_eq] using hζφ)
  have hfront_compact : IsCompact (frontier (Metric.ball c r)) := by
    rw [frontier_ball c hr.ne']
    exact isCompact_sphere c r
  have hdiff_cont :
      ContinuousOn (fun ζ : ℂ ↦ φ ζ - φ z) (frontier (Metric.ball c r)) :=
    hφ.sub continuousOn_const
  obtain ⟨C, hC⟩ := hfront_compact.exists_bound_of_continuousOn hdiff_cont
  let M : ℝ := C + 1
  have hC_nonneg : 0 ≤ C := by
    have hzC := hC z hz
    simpa using hzC
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    linarith
  have hbound : ∀ ζ ∈ frontier (Metric.ball c r), |φ ζ - φ z| ≤ M := by
    intro ζ hζ
    have hζC := hC ζ hζ
    rw [Real.norm_eq_abs] at hζC
    dsimp [M]
    linarith
  let A : ℝ := M * (2 * r / (δ₀ / 2) ^ 2)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA1_pos : 0 < A + 1 := by positivity
  refine ⟨min (δ₀ / 2) (ε / (3 * (A + 1))), ?_, ?_⟩
  · exact lt_min (by positivity) (div_pos hε (mul_pos (by norm_num) hA1_pos))
  intro w hw_closed hwdist
  rw [hz_value]
  have hwdist_half : dist w z < δ₀ / 2 :=
    hwdist.trans_le (min_le_left _ _)
  by_cases hw_ball : w ∈ Metric.ball c r
  · rw [poissonDiskDirichletCandidate_eq_extension_of_mem c r φ hw_ball]
    have hA_dist_lt : A * dist w z < ε / 3 := by
      have hwdist_A : dist w z < ε / (3 * (A + 1)) :=
        hwdist.trans_le (min_le_right _ _)
      calc
        A * dist w z ≤ (A + 1) * dist w z := by
          exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
        _ < (A + 1) * (ε / (3 * (A + 1))) := by
          exact mul_lt_mul_of_pos_left hwdist_A hA1_pos
        _ = ε / 3 := by
          field_simp [hA1_pos.ne']
    have hle :
        |poissonDiskExtension c r φ w - φ z| ≤ ε / 3 + A * dist w z := by
      simpa [A] using
        abs_poissonDiskExtension_sub_boundary_value_le c hr hδ₀_pos
          (by positivity : 0 ≤ ε / 3) hM_nonneg φ hφ hz hw_ball
          hwdist_half hlocal hbound
    have hlt : |poissonDiskExtension c r φ w - φ z| < ε := by
      calc
        |poissonDiskExtension c r φ w - φ z|
            ≤ ε / 3 + A * dist w z := hle
        _ < ε / 3 + ε / 3 := by linarith
        _ < ε := by linarith
    simpa [Real.dist_eq] using hlt
  · have hw_frontier : w ∈ frontier (Metric.ball c r) := by
      simpa [frontier, Metric.isOpen_ball.interior_eq] using
        And.intro hw_closed hw_ball
    rw [poissonDiskDirichletCandidate_eq_data_of_not_mem c r φ hw_ball]
    have hwdist_δ₀ : dist w z < δ₀ := by
      linarith
    have hwφ : dist (φ w) (φ z) < ε / 3 := hδ₀ hw_frontier hwdist_δ₀
    linarith

/--
%%handwave
name:
  Poisson extension is continuous on the closed disk
statement:
  The Poisson Dirichlet candidate is continuous on the closed disk when the
  boundary data is continuous on the circle.
proof:
  Interior continuity follows by dominated convergence for the Poisson kernel.
  At a boundary point, the Poisson kernels form an approximate identity on the
  circle, so the interior limit of the Poisson extension is the prescribed
  boundary value.  The candidate was defined to equal the boundary value on
  the boundary.
-/
theorem poissonDiskDirichletCandidate_continuousOn_closedBall
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    ContinuousOn (poissonDiskDirichletCandidate c r φ)
      (closure (Metric.ball c r)) := by
  intro w hw
  by_cases hw_ball : w ∈ Metric.ball c r
  · have h_ext_cont : ContinuousAt (poissonDiskExtension c r φ) w :=
      (poissonDiskExtension_harmonicOn c hr φ hφ w hw_ball).1.continuousAt
    have h_eq :
        poissonDiskDirichletCandidate c r φ =ᶠ[𝓝 w] poissonDiskExtension c r φ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw_ball] with y hy
      exact poissonDiskDirichletCandidate_eq_extension_of_mem c r φ hy
    exact (h_ext_cont.congr_of_eventuallyEq h_eq).continuousWithinAt
  · have hw_frontier : w ∈ frontier (Metric.ball c r) := by
      simpa [frontier, Metric.isOpen_ball.interior_eq] using And.intro hw hw_ball
    exact poissonDiskDirichletCandidate_continuousWithinAt_frontier c hr φ hφ hw_frontier

/--
%%handwave
name:
  Poisson candidate has the prescribed boundary values
statement:
  The Poisson Dirichlet candidate agrees with the prescribed boundary function
  on the boundary circle.
proof:
  No frontier point of an open disk lies in the disk.  Thus the candidate uses
  its exterior branch and equals \(\varphi\).
-/
theorem poissonDiskDirichletCandidate_boundary_eq
    (c : ℂ) (r : ℝ) (φ : ℂ → ℝ) :
    ∀ z ∈ frontier (Metric.ball c r),
      poissonDiskDirichletCandidate c r φ z = φ z := by
  classical
  intro z hz
  have hz_not_mem : z ∉ Metric.ball c r := by
    intro hz_ball
    have hz_inter : z ∈ Metric.ball c r ∩ frontier (Metric.ball c r) :=
      ⟨hz_ball, hz⟩
    simp [Metric.isOpen_ball.inter_frontier_eq] at hz_inter
  simp [poissonDiskDirichletCandidate, hz_not_mem]

/--
%%handwave
name:
  Poisson candidate solves the disk Dirichlet problem
statement:
  The Poisson Dirichlet candidate solves the harmonic Dirichlet problem on the
  Euclidean disk for continuous boundary data.
proof:
  Combine [the Poisson extension is harmonic in the disk](lean:JJMath.Uniformization.poissonDiskDirichletCandidate_harmonicOn),
  [the Poisson candidate is continuous on the closed disk](lean:JJMath.Uniformization.poissonDiskDirichletCandidate_continuousOn_closedBall),
  and [the candidate has the prescribed boundary values](lean:JJMath.Uniformization.poissonDiskDirichletCandidate_boundary_eq).
-/
theorem poissonDiskDirichletCandidate_solves
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    SolvesEuclideanDiskDirichletProblem c r φ
      (poissonDiskDirichletCandidate c r φ) := by
  exact ⟨poissonDiskDirichletCandidate_harmonicOn c hr φ hφ,
    poissonDiskDirichletCandidate_continuousOn_closedBall c hr φ hφ,
    poissonDiskDirichletCandidate_boundary_eq c r φ⟩

/--
%%handwave
name:
  Euclidean disk solution by the Poisson integral
statement:
  The Poisson integral solves the harmonic Dirichlet problem on a Euclidean
  disk for every continuous boundary value.
proof:
  Parametrize the boundary circle, integrate the boundary data against the
  Poisson kernel, prove harmonicity in the disk by differentiating under the
  integral, and prove convergence to the boundary values using the approximate
  identity property of the Poisson kernels.
tags:
  milestone
-/
theorem euclidean_disk_dirichlet_solution_by_poisson
    (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (frontier (Metric.ball c r))) :
    ∃ u : ℂ → ℝ, SolvesEuclideanDiskDirichletProblem c r φ u := by
  exact ⟨poissonDiskDirichletCandidate c r φ,
    poissonDiskDirichletCandidate_solves c hr φ hφ⟩

end Uniformization

end JJMath
