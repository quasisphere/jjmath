import JJMath.Quasiconformal.Basic

/-!
# Basic quasiconformal examples

This file checks the complete planar definition on nonconstant complex-affine
maps. It connects the topological orientation predicate, local Sobolev
regularity, weak differential, and metric distortion inequality.
-/

namespace JJMath

open MeasureTheory Set
open scoped Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Complex-affine homeomorphism of the plane
statement:
  For $a,c\in\mathbb C$ with $a\ne0$, define the whole-plane homeomorphism
  $$
    F_{a,c}(z)=az+c.
  $$
-/
def complexAffineHomeomorph (a c : ℂ) (ha : a ≠ 0) :
    (Set.univ : Set ℂ) ≃ₜ (Set.univ : Set ℂ) :=
  (((Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight c)).subtype
    (p := fun z : ℂ ↦ z ∈ (Set.univ : Set ℂ))
    (q := fun z : ℂ ↦ z ∈ (Set.univ : Set ℂ)) (by simp))

/--
%%handwave
name:
  Value of a complex-affine homeomorphism
statement:
  The whole-plane homeomorphism determined by $a\ne0$ and $c$ takes $z$ to
  $az+c$.
proof:
  Expand multiplication followed by translation.
-/
@[simp]
theorem complexAffineHomeomorph_apply (a c : ℂ) (ha : a ≠ 0)
    (z : (Set.univ : Set ℂ)) :
    (complexAffineHomeomorph a c ha z : ℂ) = a * z + c := by
  simp [complexAffineHomeomorph]

/--
%%handwave
name:
  Normalized complex-affine boundary loop
statement:
  For $a\ne0$, the normalized image under $z\mapsto az+c$ of every positive
  circle is exactly the positive unit-circle loop.
proof:
  Translation by $c$, multiplication by $a$, and the positive radius all
  cancel against the value at the loop's base point, leaving $e^{2\pi i t}$.
-/
theorem normalizedBoundaryLoop_complexAffine (a c : ℂ) (ha : a ≠ 0)
    (z : (Set.univ : Set ℂ)) (r : ℝ) (hr : 0 < r)
    (hcircle : ∀ t : unitInterval,
      circlePoint z r t ∈ (Set.univ : Set ℂ)) :
    normalizedBoundaryLoop (complexAffineHomeomorph a c ha) z r hr hcircle =
      positiveCircleLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (((a * circlePoint z r t + c) - (a * z + c)) /
    ((a * circlePoint z r 0 + c) - (a * z + c))) =
      Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I)
  rw [circlePoint_zero]
  simp only [circlePoint]
  ring_nf
  field_simp [ha, Complex.ofReal_ne_zero.mpr (ne_of_gt hr)]
  congr 1
  push_cast
  ring

/--
%%handwave
name:
  Complex-affine maps preserve planar orientation
statement:
  Every whole-plane homeomorphism $z\mapsto az+c$ with $a\ne0$ preserves
  planar orientation.
proof:
  Use a unit closed disk around each point. Its normalized boundary image is
  exactly the positive unit-circle loop.
-/
theorem preservesPlanarOrientation_complexAffine (a c : ℂ) (ha : a ≠ 0) :
    PreservesPlanarOrientation (complexAffineHomeomorph a c ha) := by
  intro z
  refine ⟨1, zero_lt_one, ?_, ?_⟩
  · simp
  · rw [normalizedBoundaryLoop_complexAffine]

/--
%%handwave
name:
  Ambient complex-affine representative
statement:
  The ambient representative of the whole-plane homeomorphism
  $z\mapsto az+c$ is the same complex-affine map on all of $\mathbb C$.
proof:
  Every complex number belongs to the source, so the extension-by-zero branch
  is never used.
-/
theorem ambientMap_complexAffine (a c : ℂ) (ha : a ≠ 0) :
    ambientMap (complexAffineHomeomorph a c ha) = affineMap a 0 c := by
  funext z
  simp [ambientMap, affineMap]

/--
%%handwave
name:
  Complex-affine maps are one-quasiconformal
statement:
  Every whole-plane homeomorphism $z\mapsto az+c$ with $a\ne0$ is
  $1$-quasiconformal.
proof:
  The map preserves orientation and is locally $W^{1,2}$ with constant weak
  differential $ξ\mapsto a\xi$. Its operator norm squared and real Jacobian
  are both $|a|^2$.
-/
theorem isOneQuasiconformalBetween_complexAffine (a c : ℂ) (ha : a ≠ 0) :
    IsKQuasiconformalBetween 1 (complexAffineHomeomorph a c ha) := by
  refine ⟨le_rfl, isOpen_univ,
    preservesPlanarOrientation_complexAffine a c ha, ?_⟩
  let df : ℂ → ℂ →L[ℝ] ℂ := fun _ ↦ realLinearMapOfWirtinger a 0
  refine ⟨df, ?_, ?_⟩
  · rw [ambientMap_complexAffine]
    exact isLocalW12On_affineMap isOpen_univ a 0 c
  · filter_upwards [] with z
    simp [df]

end

end Quasiconformal

end JJMath
