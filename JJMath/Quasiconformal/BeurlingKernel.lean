import JJMath.Quasiconformal.CauchyKernel
import JJMath.Analysis.Harmonic.FourierMode
import JJMath.Analysis.Harmonic.Kernel
import JJMath.Analysis.Harmonic.Polar
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The planar Beurling kernel

This file records the physical-space kernel estimates needed for a future
Calderón--Zygmund construction of the Beurling transform on `Lᵖ`. The kernel
is `-1 / (π z²)`. Its inverse-square size and first-difference estimate are
the elementary analytic inputs behind the singular-integral argument.
-/

namespace JJMath

open Set MeasureTheory

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Planar Beurling kernel
statement:
  The physical-space kernel of the Beurling transform is
  $K(z)=-1/(\pi z^2)$, with inversion interpreted as zero at $z=0$.
-/
def planarBeurlingKernel (z : ℂ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * z⁻¹ ^ (2 : ℕ)

/--
%%handwave
name:
  Size of the planar Beurling kernel
statement:
  For every $z\in\mathbb C$,
  $$
    \left|-\frac{1}{\pi z^2}\right|
      =\frac{1}{\pi}|z|^{-2}.
  $$
proof:
  Complex inversion sends the norm to its reciprocal, powers multiply the
  corresponding norm powers, and $\pi>0$.
-/
@[simp]
theorem norm_planarBeurlingKernel (z : ℂ) :
    ‖planarBeurlingKernel z‖ = (Real.pi)⁻¹ * ‖z‖⁻¹ ^ (2 : ℕ) := by
  simp [planarBeurlingKernel, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]

/--
%%handwave
name:
  First-difference estimate for the planar Beurling kernel
statement:
  If $z,h\in\mathbb C$ and $2|h|\leq|z|$, then
  $$
    \left|K(z-h)-K(z)\right|
      \leq \frac{6}{\pi}\frac{|h|}{|z|^3},
    \qquad K(w)=-\frac1{\pi w^2}.
  $$
proof:
  The reverse triangle inequality gives $|z-h|\geq|z|/2$. Factor the
  difference of inverse squares as
  $(u^{-1}-z^{-1})(u^{-1}+z^{-1})$ with $u=z-h$. The first factor is at most
  $2|h|/|z|^2$ and the second at most $3/|z|$.
-/
theorem norm_planarBeurlingKernel_sub_le
    (z h : ℂ) (hhz : 2 * ‖h‖ ≤ ‖z‖) :
    ‖planarBeurlingKernel (z - h) - planarBeurlingKernel z‖ ≤
      6 * (Real.pi)⁻¹ * ‖h‖ / ‖z‖ ^ (3 : ℕ) := by
  by_cases hh : h = 0
  · simp [hh]
  have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hhz
  have hhalf : ‖z‖ / 2 ≤ ‖z - h‖ := by
    calc
      ‖z‖ / 2 ≤ ‖z‖ - ‖h‖ := by linarith
      _ ≤ ‖z - h‖ := by linarith [norm_sub_norm_le z h]
  have huzpos : 0 < ‖z - h‖ := (half_pos hzpos).trans_le hhalf
  have hzinv : ‖z⁻¹‖ = 1 / ‖z‖ := by
    rw [norm_inv, one_div]
  have huinv : ‖(z - h)⁻¹‖ ≤ 2 / ‖z‖ := by
    rw [norm_inv]
    have hone := one_div_le_one_div_of_le (half_pos hzpos) hhalf
    simpa [one_div] using hone
  have hdiffinv : ‖(z - h)⁻¹ - z⁻¹‖ ≤ 2 * ‖h‖ / ‖z‖ ^ 2 := by
    have halg : (z - h)⁻¹ - z⁻¹ = (z - h)⁻¹ * h * z⁻¹ := by
      field_simp [norm_ne_zero_iff.mp huzpos.ne',
        norm_ne_zero_iff.mp hzpos.ne']
      ring
    rw [halg, norm_mul, norm_mul, hzinv]
    calc
      ‖(z - h)⁻¹‖ * ‖h‖ * (1 / ‖z‖) ≤
          (2 / ‖z‖) * ‖h‖ * (1 / ‖z‖) := by gcongr
      _ = 2 * ‖h‖ / ‖z‖ ^ 2 := by field_simp [hzpos.ne']
  have hsuminv : ‖(z - h)⁻¹ + z⁻¹‖ ≤ 3 / ‖z‖ := by
    calc
      ‖(z - h)⁻¹ + z⁻¹‖ ≤ ‖(z - h)⁻¹‖ + ‖z⁻¹‖ := norm_add_le _ _
      _ ≤ 2 / ‖z‖ + 1 / ‖z‖ := by
        rw [hzinv]
        gcongr
      _ = 3 / ‖z‖ := by ring
  have hsq : (z - h)⁻¹ ^ 2 - z⁻¹ ^ 2 =
      ((z - h)⁻¹ - z⁻¹) * ((z - h)⁻¹ + z⁻¹) := by ring
  rw [planarBeurlingKernel, planarBeurlingKernel]
  rw [show -(Real.pi : ℂ)⁻¹ * (z - h)⁻¹ ^ 2 -
      (-(Real.pi : ℂ)⁻¹ * z⁻¹ ^ 2) =
        -(Real.pi : ℂ)⁻¹ * ((z - h)⁻¹ ^ 2 - z⁻¹ ^ 2) by ring,
    hsq, norm_mul, norm_mul]
  have hpi : ‖-(Real.pi : ℂ)⁻¹‖ = (Real.pi)⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hpi]
  calc
    (Real.pi)⁻¹ *
        (‖(z - h)⁻¹ - z⁻¹‖ * ‖(z - h)⁻¹ + z⁻¹‖) ≤
      (Real.pi)⁻¹ *
        ((2 * ‖h‖ / ‖z‖ ^ 2) * (3 / ‖z‖)) := by
        gcongr
    _ = 6 * (Real.pi)⁻¹ * ‖h‖ / ‖z‖ ^ 3 := by
      field_simp [hzpos.ne', Real.pi_ne_zero]
      ring

/--
%%handwave
name:
  Calderón--Zygmund regularity estimate for the Beurling kernel
statement:
  If $2|h|\leq|z|$, then the planar Beurling kernel satisfies
  $$
    |K(z-h)-K(z)|
      \leq \frac{6}{\pi}\frac{|h|}{|z|^3}.
  $$
proof:
  Apply the proved first-difference estimate and identify the ambient
  dimension as two.
-/
theorem planarBeurlingKernel_hasKernelFirstDifference :
    HarmonicAnalysis.HasKernelFirstDifference
      planarBeurlingKernel 2 (6 * (Real.pi)⁻¹) := by
  intro z h hhz
  simpa only [Nat.reduceAdd] using
    norm_planarBeurlingKernel_sub_le z h hhz

end

end Quasiconformal

end JJMath
