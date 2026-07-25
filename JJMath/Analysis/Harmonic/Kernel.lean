import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Translation-invariant Calderón--Zygmund kernel conditions

This file introduces small, reusable predicates for the elementary
physical-space estimates of a translation-invariant singular kernel.  The
ambient dimension is recorded explicitly as a natural number.  Operator
construction, truncations, weak type, and interpolation belong in later
files; the definitions here do not bundle any of those analytic conclusions.
-/

namespace JJMath

open Set MeasureTheory

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Kernel first-difference estimate
statement:
  A kernel $K:X\to E$ has a first-difference estimate of dimension $d$ with
  constant $C$ if
  $$
    |K(x-h)-K(x)|\leq C\frac{|h|}{|x|^{d+1}}
  $$
  whenever $2|h|\leq|x|$.
-/
def HasKernelFirstDifference
    {X E : Type*} [NormedAddCommGroup X] [NormedAddCommGroup E]
    (K : X → E) (d : ℕ) (C : ℝ) : Prop :=
  ∀ x h : X, 2 * ‖h‖ ≤ ‖x‖ →
    ‖K (x - h) - K x‖ ≤ C * ‖h‖ / ‖x‖ ^ (d + 1)

/--
%%handwave
name:
  Translated form of a kernel first-difference estimate
statement:
  Suppose $K:X\to E$ satisfies
  $$
    |K(u-v)-K(u)|\leq C\frac{|v|}{|u|^{d+1}}
    \quad\text{when }2|v|\leq|u|.
  $$
  If $2|y-c|\leq|x-c|$, then
  $$
    |K(x-y)-K(x-c)|
      \leq C\frac{|y-c|}{|x-c|^{d+1}}.
  $$
proof:
  Apply the original estimate with $u=x-c$ and $v=y-c$, using
  $(x-c)-(y-c)=x-y$.
-/
theorem HasKernelFirstDifference.sub_sub_le
    {X E : Type*} [NormedAddCommGroup X] [NormedAddCommGroup E]
    {K : X → E} {d : ℕ} {C : ℝ}
    (hK : HasKernelFirstDifference K d C)
    (x y c : X) (hscale : 2 * ‖y - c‖ ≤ ‖x - c‖) :
    ‖K (x - y) - K (x - c)‖ ≤
      C * ‖y - c‖ / ‖x - c‖ ^ (d + 1) := by
  have h := hK (x - c) (y - c) hscale
  rw [show (x - c) - (y - c) = x - y by abel] at h
  exact h

end

end HarmonicAnalysis

end JJMath
