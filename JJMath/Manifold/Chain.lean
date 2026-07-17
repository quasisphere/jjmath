import JJMath.Manifold.DifferentialForm
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Module.NatInt
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Smooth singular chains and integration

This file starts the integration side of the de Rham comparison.  A smooth
singular simplex is recorded as a continuous singular simplex in Mathlib's
standard topological simplex, together with a chart-independent smoothness
condition expressed by extension from the ambient affine space.

The chain groups are finitely supported integer combinations of such
simplices.  We also introduce the first geometric equivalence relation on
chains: changing the ordered vertices of the parameter simplex changes the
orientation by the sign of the permutation.  Integration over chains descends
through this quotient once the usual change-of-variables theorem for
differential forms on a simplex is available.
-/

open CategoryTheory
open MeasureTheory
open Set
open scoped Manifold ContDiff Topology Interval

namespace JJMath
namespace Manifold

noncomputable section

universe u v w z

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The ambient affine space of the standard `k`-simplex. -/
abbrev SimplexAmbient (k : ℕ) : Type :=
  Fin (k + 1) → ℝ

/-- The standard topological `k`-simplex, as used by Mathlib's singular set. -/
abbrev StandardSimplex (k : ℕ) : Type :=
  stdSimplex ℝ (Fin (k + 1))

/-- The usual affine coordinate domain for the standard `k`-simplex. -/
def simplexCoordinateDomain (k : ℕ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}

theorem measurableSet_simplexCoordinateDomain (k : ℕ) :
    MeasurableSet (simplexCoordinateDomain k) := by
  classical
  simp [simplexCoordinateDomain]
  measurability

theorem isClosed_simplexCoordinateDomain (k : ℕ) :
    IsClosed (simplexCoordinateDomain k) := by
  classical
  have hnonneg : IsClosed {x : Fin k → ℝ | ∀ i, 0 ≤ x i} := by
    simpa [Set.setOf_forall] using
      (isClosed_iInter fun i : Fin k =>
        isClosed_le continuous_const (continuous_apply i))
  have hsum : IsClosed {x : Fin k → ℝ | ∑ i : Fin k, x i ≤ 1} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  simpa [simplexCoordinateDomain, Set.setOf_and] using hnonneg.inter hsum

theorem isCompact_simplexCoordinateDomain (k : ℕ) :
    IsCompact (simplexCoordinateDomain k) := by
  classical
  have hsubset : simplexCoordinateDomain k ⊆ Icc (0 : Fin k → ℝ) (1 : Fin k → ℝ) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · intro i
      exact hx.1 i
    · intro i
      have hsingle : x i ≤ ∑ j : Fin k, x j := by
        simpa using
          Finset.single_le_sum (fun j _hj => hx.1 j) (Finset.mem_univ i)
      exact hsingle.trans hx.2
  exact isCompact_Icc.of_isClosed_subset (isClosed_simplexCoordinateDomain k) hsubset

/-- The affine coordinate simplex is convex. -/
theorem convex_simplexCoordinateDomain (k : ℕ) :
    Convex ℝ (simplexCoordinateDomain k) := by
  classical
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · calc
      ∑ i : Fin k, (a • x + b • y) i =
          ∑ i : Fin k, a * x i + ∑ i : Fin k, b * y i := by
            simp [Finset.sum_add_distrib]
      _ = a * (∑ i : Fin k, x i) + b * (∑ i : Fin k, y i) := by
            simp [Finset.mul_sum]
      _ ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
            (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by nlinarith

/-- The affine coordinate simplex has nonempty interior. -/
theorem interior_simplexCoordinateDomain_nonempty (k : ℕ) :
    (interior (simplexCoordinateDomain k)).Nonempty := by
  classical
  let c : Fin k → ℝ := fun _ ↦ (1 : ℝ) / ((k : ℝ) + 1)
  let u : Set (Fin k → ℝ) :=
    {x | (∀ i, 0 < x i) ∧ ∑ i : Fin k, x i < 1}
  have hu_open : IsOpen u := by
    have hpos : IsOpen {x : Fin k → ℝ | ∀ i, 0 < x i} := by
      simpa [Set.setOf_forall] using
        (isOpen_iInter_of_finite fun i : Fin k =>
          isOpen_lt continuous_const (continuous_apply i))
    have hsum : IsOpen {x : Fin k → ℝ | ∑ i : Fin k, x i < 1} :=
      isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    simpa [u, Set.setOf_and] using hpos.inter hsum
  have hu_subset : u ⊆ simplexCoordinateDomain k := by
    intro x hx
    exact ⟨fun i ↦ (hx.1 i).le, hx.2.le⟩
  have hc_pos : ∀ i : Fin k, 0 < c i := by
    intro i
    dsimp [c]
    positivity
  have hc_sum : ∑ i : Fin k, c i < 1 := by
    have hden : 0 < (k : ℝ) + 1 := by positivity
    calc
      ∑ i : Fin k, c i = (k : ℝ) / ((k : ℝ) + 1) := by
        simp [c, div_eq_mul_inv]
      _ < 1 := by
        rw [div_lt_one hden]
        nlinarith
  have hc_u : c ∈ u := ⟨hc_pos, hc_sum⟩
  exact ⟨c, interior_maximal hu_subset hu_open hc_u⟩

/-- The affine coordinate simplex is a set of unique differentiability. -/
theorem uniqueDiffOn_simplexCoordinateDomain (k : ℕ) :
    UniqueDiffOn ℝ (simplexCoordinateDomain k) :=
  uniqueDiffOn_convex (convex_simplexCoordinateDomain k)
    (interior_simplexCoordinateDomain_nonempty k)

/-- Every point of the closed affine simplex is a limit of interior points. -/
theorem simplexCoordinateDomain_subset_closure_interior (k : ℕ) :
    simplexCoordinateDomain k ⊆ closure (interior (simplexCoordinateDomain k)) := by
  intro x hx
  rw [(convex_simplexCoordinateDomain k).closure_interior_eq_closure_of_nonempty_interior
    (interior_simplexCoordinateDomain_nonempty k)]
  exact subset_closure hx

/-- Reassemble a point of the next affine simplex from a base point and the last coordinate. -/
def simplexCoordinateSliceMap (k : ℕ) (x : Fin k → ℝ) (t : ℝ) :
    Fin (k + 1) → ℝ :=
  Fin.snoc x t

/-- The sliced form of the next affine simplex inside `simplexCoordinateDomain k × ℝ`. -/
def simplexCoordinateSliceDomain (k : ℕ) : Set ((Fin k → ℝ) × ℝ) :=
  {p | p.1 ∈ simplexCoordinateDomain k ∧
    p.2 ∈ Icc (0 : ℝ) (1 - ∑ i : Fin k, p.1 i)}

theorem measurableSet_simplexCoordinateSliceDomain (k : ℕ) :
    MeasurableSet (simplexCoordinateSliceDomain k) := by
  classical
  simp [simplexCoordinateSliceDomain, simplexCoordinateDomain]
  measurability

@[simp]
theorem simplexCoordinateSliceMap_castSucc
    (k : ℕ) (x : Fin k → ℝ) (t : ℝ) (i : Fin k) :
    simplexCoordinateSliceMap k x t i.castSucc = x i := by
  simp [simplexCoordinateSliceMap]

@[simp]
theorem simplexCoordinateSliceMap_last
    (k : ℕ) (x : Fin k → ℝ) (t : ℝ) :
    simplexCoordinateSliceMap k x t (Fin.last k) = t := by
  simp [simplexCoordinateSliceMap]

/--
A point of the \((k+1)\)-dimensional affine simplex is the same as a point of
the \(k\)-dimensional affine simplex together with a final coordinate between
\(0\) and the remaining barycentric mass.
-/
theorem simplexCoordinateSliceMap_mem_domain_iff
    (k : ℕ) (x : Fin k → ℝ) (t : ℝ) :
    simplexCoordinateSliceMap k x t ∈ simplexCoordinateDomain (k + 1) ↔
      x ∈ simplexCoordinateDomain k ∧
        t ∈ Icc (0 : ℝ) (1 - ∑ i : Fin k, x i) := by
  classical
  constructor
  · intro h
    have hx_nonneg : ∀ i : Fin k, 0 ≤ x i := by
      intro i
      simpa [simplexCoordinateSliceMap] using h.1 i.castSucc
    have ht_nonneg : 0 ≤ t := by
      simpa [simplexCoordinateSliceMap] using h.1 (Fin.last k)
    have hsum : (∑ i : Fin k, x i) + t ≤ 1 := by
      simpa [simplexCoordinateSliceMap, Fin.sum_univ_castSucc] using h.2
    have hx_sum : ∑ i : Fin k, x i ≤ 1 := by
      linarith
    have ht_upper : t ≤ 1 - ∑ i : Fin k, x i := by
      linarith
    exact ⟨⟨hx_nonneg, hx_sum⟩, ⟨ht_nonneg, ht_upper⟩⟩
  · rintro ⟨hx, ht⟩
    refine ⟨?_, ?_⟩
    · intro j
      cases j using Fin.lastCases
      · simpa [simplexCoordinateSliceMap] using ht.1
      · simpa [simplexCoordinateSliceMap] using hx.1 _
    · have hsum : (∑ i : Fin k, x i) + t ≤ 1 := by
        linarith [ht.2]
      simpa [simplexCoordinateSliceMap, Fin.sum_univ_castSucc] using hsum

/-- The measurable equivalence obtained by slicing off the last affine coordinate. -/
noncomputable def simplexCoordinateSliceMeasurableEquiv (k : ℕ) :
    (Fin k → ℝ) × ℝ ≃ᵐ (Fin (k + 1) → ℝ) :=
  (MeasurableEquiv.prodComm :
      (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ)).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm)

@[simp]
theorem simplexCoordinateSliceMeasurableEquiv_apply
    (k : ℕ) (x : Fin k → ℝ) (t : ℝ) :
    simplexCoordinateSliceMeasurableEquiv k (x, t) =
      simplexCoordinateSliceMap k x t := by
  ext j
  cases j using Fin.lastCases
  · simp [simplexCoordinateSliceMeasurableEquiv, simplexCoordinateSliceMap,
      MeasurableEquiv.prodComm, Equiv.prodComm_apply]
  · simp [simplexCoordinateSliceMeasurableEquiv, simplexCoordinateSliceMap,
      MeasurableEquiv.prodComm, Equiv.prodComm_apply]

/-- The slicing equivalence preserves the finite-dimensional Lebesgue measure. -/
theorem measurePreserving_simplexCoordinateSliceMeasurableEquiv (k : ℕ) :
    MeasurePreserving (simplexCoordinateSliceMeasurableEquiv k) := by
  classical
  let eLast : ℝ × (Fin k → ℝ) ≃ᵐ (Fin (k + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm
  have heLast : MeasurePreserving eLast :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm _
  have hswap :
      MeasurePreserving
        (MeasurableEquiv.prodComm :
          (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ)) := by
    simpa [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure (Fin k → ℝ)))
        (ν := (volume : Measure ℝ)))
  change MeasurePreserving
    (eLast ∘
      (MeasurableEquiv.prodComm :
        (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ)))
  exact heLast.comp hswap

theorem simplexCoordinateSliceMeasurableEquiv_preimage_domain (k : ℕ) :
    simplexCoordinateSliceMeasurableEquiv k ⁻¹'
        simplexCoordinateDomain (k + 1) =
      simplexCoordinateSliceDomain k := by
  ext p
  rcases p with ⟨x, t⟩
  simp [simplexCoordinateSliceDomain, simplexCoordinateSliceMap_mem_domain_iff]

theorem integral_simplexCoordinateDomain_succ_eq_sliceDomain
    {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (f : (Fin (k + 1) → ℝ) → F) :
    (∫ y in simplexCoordinateDomain (k + 1), f y) =
      ∫ p in simplexCoordinateSliceDomain k,
        f (simplexCoordinateSliceMap k p.1 p.2) := by
  classical
  let e := simplexCoordinateSliceMeasurableEquiv k
  have he : MeasurePreserving e :=
    measurePreserving_simplexCoordinateSliceMeasurableEquiv k
  rw [← he.map_eq]
  rw [setIntegral_map_equiv e f (simplexCoordinateDomain (k + 1))]
  rw [simplexCoordinateSliceMeasurableEquiv_preimage_domain]
  have hfun :
      (fun p : (Fin k → ℝ) × ℝ => f (e p)) =
        fun p => f (simplexCoordinateSliceMap k p.1 p.2) := by
    funext p
    rcases p with ⟨x, t⟩
    simp [e]
  rw [hfun]

/-- Fubini on the sliced simplex: integrate first in the last affine coordinate. -/
theorem integral_simplexCoordinateSliceDomain_eq_iterated
    {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (f : ((Fin k → ℝ) × ℝ) → F)
    (hf : IntegrableOn f (simplexCoordinateSliceDomain k)) :
    (∫ p in simplexCoordinateSliceDomain k, f p) =
      ∫ x in simplexCoordinateDomain k,
        ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i), f (x, t) := by
  classical
  let D : Set (Fin k → ℝ) := simplexCoordinateDomain k
  let S : Set ((Fin k → ℝ) × ℝ) := simplexCoordinateSliceDomain k
  let u : (Fin k → ℝ) → ℝ := fun x => 1 - ∑ i : Fin k, x i
  have hD : MeasurableSet D := by
    simpa [D] using measurableSet_simplexCoordinateDomain k
  have hS : MeasurableSet S := by
    simpa [S] using measurableSet_simplexCoordinateSliceDomain k
  have hfi : Integrable (S.indicator f) (volume : Measure ((Fin k → ℝ) × ℝ)) := by
    simpa [S] using hf.integrable_indicator (measurableSet_simplexCoordinateSliceDomain k)
  have houter :
      (fun x : Fin k → ℝ => ∫ t : ℝ, S.indicator f (x, t)) =
        D.indicator
          (fun x : Fin k → ℝ => ∫ t in Icc (0 : ℝ) (u x), f (x, t)) := by
    funext x
    by_cases hx : x ∈ D
    · have hfun :
          (fun t : ℝ => S.indicator f (x, t)) =
            (Icc (0 : ℝ) (u x)).indicator (fun t : ℝ => f (x, t)) := by
        funext t
        by_cases ht : t ∈ Icc (0 : ℝ) (u x)
        · have hp : (x, t) ∈ S := by
            simpa [S, D, u, simplexCoordinateSliceDomain] using And.intro hx ht
          simp [Set.indicator_of_mem hp, Set.indicator_of_mem ht]
        · have hp : (x, t) ∉ S := by
            intro hp
            exact ht (by simpa [S, u, simplexCoordinateSliceDomain] using hp.2)
          simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem ht]
      rw [hfun, integral_indicator measurableSet_Icc]
      simp [Set.indicator_of_mem hx]
    · have hfun : (fun t : ℝ => S.indicator f (x, t)) = fun _ : ℝ => 0 := by
        funext t
        have hp : (x, t) ∉ S := by
          intro hp
          exact hx (by simpa [S, D, simplexCoordinateSliceDomain] using hp.1)
        simp [Set.indicator_of_notMem hp]
      rw [hfun]
      simp [Set.indicator_of_notMem hx]
  calc
    (∫ p in simplexCoordinateSliceDomain k, f p)
        = ∫ p, S.indicator f p := by
          simpa [S] using (integral_indicator hS (f := f)
            (μ := (volume : Measure ((Fin k → ℝ) × ℝ)))).symm
    _ = ∫ x : Fin k → ℝ, ∫ t : ℝ, S.indicator f (x, t) := by
          rw [Measure.volume_eq_prod] at hfi ⊢
          exact integral_prod (S.indicator f) hfi
    _ = ∫ x : Fin k → ℝ,
          D.indicator
            (fun x : Fin k → ℝ => ∫ t in Icc (0 : ℝ) (u x), f (x, t)) x := by
          rw [houter]
    _ = ∫ x in D, ∫ t in Icc (0 : ℝ) (u x), f (x, t) := by
          exact integral_indicator hD
    _ = ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i), f (x, t) := by
          rfl

/-- Fubini on the affine simplex, written in last-coordinate slices. -/
theorem integral_simplexCoordinateDomain_succ_eq_iterated
    {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (f : (Fin (k + 1) → ℝ) → F)
    (hf : IntegrableOn f (simplexCoordinateDomain (k + 1))) :
    (∫ y in simplexCoordinateDomain (k + 1), f y) =
      ∫ x in simplexCoordinateDomain k,
        ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
          f (simplexCoordinateSliceMap k x t) := by
  classical
  let e := simplexCoordinateSliceMeasurableEquiv k
  let g : ((Fin k → ℝ) × ℝ) → F :=
    fun p => f (simplexCoordinateSliceMap k p.1 p.2)
  have hg : IntegrableOn g (simplexCoordinateSliceDomain k) := by
    have hpre :
        e ⁻¹' simplexCoordinateDomain (k + 1) =
          simplexCoordinateSliceDomain k :=
      simplexCoordinateSliceMeasurableEquiv_preimage_domain k
    have hcomp : g = f ∘ e := by
      funext p
      rcases p with ⟨x, t⟩
      simp [g, e]
    have he : MeasurePreserving e :=
      measurePreserving_simplexCoordinateSliceMeasurableEquiv k
    have hge :
        IntegrableOn (f ∘ e) (e ⁻¹' simplexCoordinateDomain (k + 1)) :=
      (e.measurableEmbedding.integrableOn_map_iff (μ := volume)
        (f := f) (s := simplexCoordinateDomain (k + 1))).1
        (by simpa [he.map_eq] using hf)
    simpa [hpre, hcomp] using hge
  calc
    (∫ y in simplexCoordinateDomain (k + 1), f y)
        = ∫ p in simplexCoordinateSliceDomain k, g p := by
          simpa [g] using integral_simplexCoordinateDomain_succ_eq_sliceDomain
            (k := k) f
    _ = ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i), g (x, t) :=
          integral_simplexCoordinateSliceDomain_eq_iterated (k := k) g hg
    _ = ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            f (simplexCoordinateSliceMap k x t) := by
          rfl

/-- Reassemble a point of the next affine simplex by inserting one coordinate
in an arbitrary slot. -/
def simplexCoordinateInsertMap {k : ℕ} (i : Fin (k + 1))
    (x : Fin k → ℝ) (t : ℝ) : Fin (k + 1) → ℝ :=
  i.insertNth t x

@[simp]
theorem simplexCoordinateInsertMap_same
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ) (t : ℝ) :
    simplexCoordinateInsertMap i x t i = t := by
  simp [simplexCoordinateInsertMap]

@[simp]
theorem simplexCoordinateInsertMap_succAbove
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ) (t : ℝ) (j : Fin k) :
    simplexCoordinateInsertMap i x t (i.succAbove j) = x j := by
  simp [simplexCoordinateInsertMap]

theorem simplexCoordinateInsertMap_sum
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ) (t : ℝ) :
    ∑ j : Fin (k + 1), simplexCoordinateInsertMap i x t j =
      t + ∑ j : Fin k, x j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp [simplexCoordinateInsertMap]

/-- Inserting one coordinate into the affine simplex is equivalent to choosing
the remaining coordinates in the lower-dimensional simplex and the inserted
coordinate between zero and the remaining mass. -/
theorem simplexCoordinateInsertMap_mem_domain_iff
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ) (t : ℝ) :
    simplexCoordinateInsertMap i x t ∈ simplexCoordinateDomain (k + 1) ↔
      x ∈ simplexCoordinateDomain k ∧
        t ∈ Icc (0 : ℝ) (1 - ∑ j : Fin k, x j) := by
  classical
  constructor
  · intro h
    have hx_nonneg : ∀ j : Fin k, 0 ≤ x j := by
      intro j
      simpa [simplexCoordinateInsertMap] using h.1 (i.succAbove j)
    have ht_nonneg : 0 ≤ t := by
      simpa [simplexCoordinateInsertMap] using h.1 i
    have hsum : t + ∑ j : Fin k, x j ≤ 1 := by
      simpa [simplexCoordinateInsertMap_sum i x t] using h.2
    have hx_sum : ∑ j : Fin k, x j ≤ 1 := by
      linarith
    have ht_upper : t ≤ 1 - ∑ j : Fin k, x j := by
      linarith
    exact ⟨⟨hx_nonneg, hx_sum⟩, ⟨ht_nonneg, ht_upper⟩⟩
  · rintro ⟨hx, ht⟩
    refine ⟨?_, ?_⟩
    · intro j
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
      · simpa [simplexCoordinateInsertMap] using ht.1
      · simpa [simplexCoordinateInsertMap] using hx.1 a
    · have hsum : t + ∑ j : Fin k, x j ≤ 1 := by
        linarith [ht.2]
      simpa [simplexCoordinateInsertMap_sum i x t] using hsum

/-- The upper inserted-coordinate endpoint depends continuously on the
remaining affine coordinates. -/
theorem continuous_simplexCoordinateInsertMap_upper
    {k : ℕ} (i : Fin (k + 1)) :
    Continuous (fun x : Fin k → ℝ =>
      simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j)) := by
  classical
  refine continuous_pi ?_
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
  · simpa [simplexCoordinateInsertMap] using
      (continuous_const.sub
        (continuous_finsetSum _ fun j _ => continuous_apply j))
  · simpa [simplexCoordinateInsertMap] using (continuous_apply a)

/-- The lower inserted-coordinate endpoint depends continuously on the
remaining affine coordinates. -/
theorem continuous_simplexCoordinateInsertMap_zero
    {k : ℕ} (i : Fin (k + 1)) :
    Continuous (fun x : Fin k → ℝ => simplexCoordinateInsertMap i x 0) := by
  classical
  refine continuous_pi ?_
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
  · simpa [simplexCoordinateInsertMap] using
      (continuous_const : Continuous (fun _ : Fin k → ℝ => (0 : ℝ)))
  · simpa [simplexCoordinateInsertMap] using (continuous_apply a)

/-- Varying the inserted coordinate is an affine line in the ambient affine
coordinate space, with tangent vector the corresponding coordinate basis
vector. -/
theorem hasDerivWithinAt_simplexCoordinateInsertMap_line
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ)
    {s : Set ℝ} {t : ℝ} :
    HasDerivWithinAt (fun u : ℝ => simplexCoordinateInsertMap i x u)
      (Pi.single i (1 : ℝ)) s t := by
  classical
  refine hasDerivWithinAt_pi.2 ?_
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
  · simpa [simplexCoordinateInsertMap] using
      (hasDerivWithinAt_id t s)
  · simpa [simplexCoordinateInsertMap] using
      (hasDerivWithinAt_const (c := x a) (x := t) (s := s))

/-- Varying the inserted coordinate is smooth as a map from the line into the
ambient affine coordinate space. -/
theorem contDiffOn_simplexCoordinateInsertMap_line
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ)
    {r : WithTop ℕ∞} {s : Set ℝ} :
    ContDiffOn ℝ r (fun u : ℝ => simplexCoordinateInsertMap i x u) s := by
  classical
  refine contDiffOn_pi.2 ?_
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
  · simpa [simplexCoordinateInsertMap] using
      (contDiffOn_id : ContDiffOn ℝ r (fun u : ℝ => u) s)
  · simpa [simplexCoordinateInsertMap] using
      (contDiffOn_const : ContDiffOn ℝ r (fun _ : ℝ => x a) s)

/-- The measurable equivalence obtained by inserting one affine coordinate in
an arbitrary slot. -/
noncomputable def simplexCoordinateInsertMeasurableEquiv
    {k : ℕ} (i : Fin (k + 1)) :
    (Fin k → ℝ) × ℝ ≃ᵐ (Fin (k + 1) → ℝ) :=
  (MeasurableEquiv.prodComm :
      (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ)).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm)

@[simp]
theorem simplexCoordinateInsertMeasurableEquiv_apply
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ) (t : ℝ) :
    simplexCoordinateInsertMeasurableEquiv i (x, t) =
      simplexCoordinateInsertMap i x t := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
  · simp [simplexCoordinateInsertMeasurableEquiv, simplexCoordinateInsertMap,
      MeasurableEquiv.prodComm, Equiv.prodComm_apply]
  · simp [simplexCoordinateInsertMeasurableEquiv, simplexCoordinateInsertMap,
      MeasurableEquiv.prodComm, Equiv.prodComm_apply]

/-- Inserting an arbitrary coordinate preserves finite-dimensional Lebesgue
measure. -/
theorem measurePreserving_simplexCoordinateInsertMeasurableEquiv
    {k : ℕ} (i : Fin (k + 1)) :
    MeasurePreserving (simplexCoordinateInsertMeasurableEquiv i) := by
  classical
  let eInsert : ℝ × (Fin k → ℝ) ≃ᵐ (Fin (k + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm
  have heInsert : MeasurePreserving eInsert :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm _
  have hswap :
      MeasurePreserving
        (MeasurableEquiv.prodComm :
          (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ)) := by
    simpa [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure (Fin k → ℝ)))
        (ν := (volume : Measure ℝ)))
  change MeasurePreserving
    (eInsert ∘
      (MeasurableEquiv.prodComm :
        (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ)))
  exact heInsert.comp hswap

theorem simplexCoordinateInsertMeasurableEquiv_preimage_domain
    {k : ℕ} (i : Fin (k + 1)) :
    simplexCoordinateInsertMeasurableEquiv i ⁻¹'
        simplexCoordinateDomain (k + 1) =
      simplexCoordinateSliceDomain k := by
  ext p
  rcases p with ⟨x, t⟩
  simp [simplexCoordinateSliceDomain, simplexCoordinateInsertMap_mem_domain_iff]

theorem integral_simplexCoordinateDomain_eq_insertSliceDomain
    {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (i : Fin (k + 1)) (f : (Fin (k + 1) → ℝ) → F) :
    (∫ y in simplexCoordinateDomain (k + 1), f y) =
      ∫ p in simplexCoordinateSliceDomain k,
        f (simplexCoordinateInsertMap i p.1 p.2) := by
  classical
  let e := simplexCoordinateInsertMeasurableEquiv i
  have he : MeasurePreserving e :=
    measurePreserving_simplexCoordinateInsertMeasurableEquiv i
  rw [← he.map_eq]
  rw [setIntegral_map_equiv e f (simplexCoordinateDomain (k + 1))]
  rw [simplexCoordinateInsertMeasurableEquiv_preimage_domain]
  have hfun :
      (fun p : (Fin k → ℝ) × ℝ => f (e p)) =
        fun p => f (simplexCoordinateInsertMap i p.1 p.2) := by
    funext p
    rcases p with ⟨x, t⟩
    simp [e]
  rw [hfun]

/-- Fubini on the affine simplex after inserting an arbitrary affine
coordinate. -/
theorem integral_simplexCoordinateDomain_eq_insertIterated
    {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (i : Fin (k + 1)) (f : (Fin (k + 1) → ℝ) → F)
    (hf : IntegrableOn f (simplexCoordinateDomain (k + 1))) :
    (∫ y in simplexCoordinateDomain (k + 1), f y) =
      ∫ x in simplexCoordinateDomain k,
        ∫ t in Icc (0 : ℝ) (1 - ∑ j : Fin k, x j),
          f (simplexCoordinateInsertMap i x t) := by
  classical
  let e := simplexCoordinateInsertMeasurableEquiv i
  let g : ((Fin k → ℝ) × ℝ) → F :=
    fun p => f (simplexCoordinateInsertMap i p.1 p.2)
  have hg : IntegrableOn g (simplexCoordinateSliceDomain k) := by
    have hpre :
        e ⁻¹' simplexCoordinateDomain (k + 1) =
          simplexCoordinateSliceDomain k :=
      simplexCoordinateInsertMeasurableEquiv_preimage_domain i
    have hcomp : g = f ∘ e := by
      funext p
      rcases p with ⟨x, t⟩
      simp [g, e]
    have he : MeasurePreserving e :=
      measurePreserving_simplexCoordinateInsertMeasurableEquiv i
    have hge :
        IntegrableOn (f ∘ e) (e ⁻¹' simplexCoordinateDomain (k + 1)) :=
      (e.measurableEmbedding.integrableOn_map_iff (μ := volume)
        (f := f) (s := simplexCoordinateDomain (k + 1))).1
        (by simpa [he.map_eq] using hf)
    simpa [hpre, hcomp] using hge
  calc
    (∫ y in simplexCoordinateDomain (k + 1), f y)
        = ∫ p in simplexCoordinateSliceDomain k, g p := by
          simpa [g] using integral_simplexCoordinateDomain_eq_insertSliceDomain
            (k := k) i f
    _ = ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ j : Fin k, x j), g (x, t) :=
          integral_simplexCoordinateSliceDomain_eq_iterated (k := k) g hg
    _ = ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ j : Fin k, x j),
            f (simplexCoordinateInsertMap i x t) := by
          rfl

/-- Barycentric coordinates obtained from the first `k` affine coordinates. -/
def simplexCoordinateMap (k : ℕ) (x : Fin k → ℝ) : SimplexAmbient k :=
  Fin.snoc x (1 - ∑ i : Fin k, x i)

/-- The first `k` barycentric coordinates, viewed as affine simplex coordinates. -/
def simplexCoordinateOfBarycentric (k : ℕ) (y : SimplexAmbient k) : Fin k → ℝ :=
  fun i ↦ y i.castSucc

/-- The linear projection from barycentric coordinates to the first `k` affine coordinates. -/
noncomputable def simplexCoordinateProjectionLinearMap (k : ℕ) :
    SimplexAmbient k →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin k =>
    ContinuousLinearMap.proj (R := ℝ) i.castSucc

@[simp]
theorem simplexCoordinateProjectionLinearMap_apply (k : ℕ) (y : SimplexAmbient k) :
    simplexCoordinateProjectionLinearMap k y =
      simplexCoordinateOfBarycentric k y := by
  ext i
  rfl

theorem simplexCoordinateMap_mem_stdSimplex {k : ℕ} {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexCoordinateMap k x ∈ stdSimplex ℝ (Fin (k + 1)) := by
  refine ⟨?_, ?_⟩
  · intro j
    cases j using Fin.lastCases
    · simpa [simplexCoordinateMap] using sub_nonneg.mpr hx.2
    · simpa [simplexCoordinateMap] using hx.1 _
  · rw [simplexCoordinateMap, Fin.sum_univ_castSucc]
    simp [sub_eq_add_neg, add_comm]

@[simp]
theorem simplexCoordinateOfBarycentric_simplexCoordinateMap
    (k : ℕ) (x : Fin k → ℝ) :
    simplexCoordinateOfBarycentric k (simplexCoordinateMap k x) = x := by
  ext i
  simp [simplexCoordinateOfBarycentric, simplexCoordinateMap]

theorem simplexCoordinateOfBarycentric_mem {k : ℕ} {y : SimplexAmbient k}
    (hy : y ∈ stdSimplex ℝ (Fin (k + 1))) :
    simplexCoordinateOfBarycentric k y ∈ simplexCoordinateDomain k := by
  refine ⟨?_, ?_⟩
  · intro i
    exact hy.1 i.castSucc
  · change ∑ i : Fin k, y i.castSucc ≤ 1
    have hlast : 0 ≤ y (Fin.last k) := hy.1 (Fin.last k)
    have hsum : ∑ i : Fin k, y i.castSucc + y (Fin.last k) = 1 := by
      simpa [Fin.sum_univ_castSucc] using hy.2
    nlinarith

theorem simplexCoordinateMap_simplexCoordinateOfBarycentric
    {k : ℕ} {y : SimplexAmbient k} (hy : y ∈ stdSimplex ℝ (Fin (k + 1))) :
    simplexCoordinateMap k (simplexCoordinateOfBarycentric k y) = y := by
  ext j
  cases j using Fin.lastCases
  · rw [simplexCoordinateMap]
    have hsum : ∑ i : Fin k, y i.castSucc + y (Fin.last k) = 1 := by
      simpa [Fin.sum_univ_castSucc] using hy.2
    simp [simplexCoordinateOfBarycentric]
    nlinarith
  · simp [simplexCoordinateMap, simplexCoordinateOfBarycentric]

/-- An upper endpoint for any inserted coordinate is a point on the final
face, written in the standard last-coordinate parametrization of that face. -/
theorem simplexCoordinateInsertMap_upper_eq_slice_of_barycentric
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ) :
    simplexCoordinateSliceMap k
      (simplexCoordinateOfBarycentric k
        (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j)))
      (1 - ∑ j : Fin k,
        simplexCoordinateOfBarycentric k
          (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j)) j) =
    simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j) := by
  classical
  let y : Fin (k + 1) → ℝ :=
    simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j)
  have hsum_y : ∑ a : Fin (k + 1), y a = 1 := by
    simp [y, simplexCoordinateInsertMap_sum]
  ext a
  cases a using Fin.lastCases with
  | last =>
      have hsplit :
          ∑ a : Fin (k + 1), y a =
            ∑ j : Fin k, y j.castSucc + y (Fin.last k) := by
        simp [Fin.sum_univ_castSucc]
      simp only [simplexCoordinateSliceMap_last, simplexCoordinateOfBarycentric]
      change 1 - ∑ j : Fin k, y j.castSucc = y (Fin.last k)
      linarith
  | cast a =>
      simp [simplexCoordinateSliceMap, simplexCoordinateOfBarycentric]

/-- The upper inserted coordinate vector is a barycentric point of the final
face of the surrounding simplex. -/
theorem simplexCoordinateInsertMap_upper_mem_stdSimplex
    {k : ℕ} (i : Fin (k + 1)) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j) ∈
      stdSimplex ℝ (Fin (k + 1)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro a
    rcases Fin.eq_self_or_eq_succAbove i a with rfl | ⟨j, rfl⟩
    · simp [sub_nonneg.mpr hx.2]
    · simpa [simplexCoordinateInsertMap] using hx.1 j
  · rw [simplexCoordinateInsertMap_sum]
    ring

/-- Taking the explicit barycentric coordinates of an upper inserted endpoint
lands back in the standard affine coordinate simplex. -/
theorem simplexCoordinateOfBarycentric_insert_upper_mem
    {k : ℕ} (i : Fin (k + 1)) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexCoordinateOfBarycentric k
        (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j)) ∈
      simplexCoordinateDomain k :=
  simplexCoordinateOfBarycentric_mem
    (simplexCoordinateInsertMap_upper_mem_stdSimplex i hx)

/-- The derivative of the barycentric coordinate map. -/
noncomputable def simplexCoordinateLinearMap (k : ℕ) :
    (Fin k → ℝ) →L[ℝ] SimplexAmbient k :=
  ContinuousLinearMap.pi fun j : Fin (k + 1) =>
    if h : j = Fin.last k then
      -∑ i : Fin k, ContinuousLinearMap.proj (R := ℝ) i
    else
      ContinuousLinearMap.proj (R := ℝ) (j.castPred h)

@[simp]
theorem simplexCoordinateLinearMap_castSucc (k : ℕ) (x : Fin k → ℝ) (i : Fin k) :
    simplexCoordinateLinearMap k x i.castSucc = x i := by
  simp [simplexCoordinateLinearMap]

@[simp]
theorem simplexCoordinateLinearMap_last (k : ℕ) (x : Fin k → ℝ) :
    simplexCoordinateLinearMap k x (Fin.last k) = -∑ i : Fin k, x i := by
  simp [simplexCoordinateLinearMap]

/-- The sum of barycentric coordinates as a linear map on the ambient simplex space. -/
noncomputable def simplexAmbientSumLinearMap (k : ℕ) :
    SimplexAmbient k →ₗ[ℝ] ℝ :=
  ∑ j : Fin (k + 1), LinearMap.proj j

/-- The tangent hyperplane to the affine simplex, cut out by zero total coordinate sum. -/
noncomputable def simplexTangentSubmodule (k : ℕ) :
    Submodule ℝ (SimplexAmbient k) :=
  LinearMap.ker (simplexAmbientSumLinearMap k)

theorem simplexAmbientSumLinearMap_apply (k : ℕ) (y : SimplexAmbient k) :
    simplexAmbientSumLinearMap k y = ∑ j : Fin (k + 1), y j := by
  simp [simplexAmbientSumLinearMap]

theorem simplexCoordinateLinearMap_mem_tangent
    (k : ℕ) (x : Fin k → ℝ) :
    simplexCoordinateLinearMap k x ∈ simplexTangentSubmodule k := by
  change simplexAmbientSumLinearMap k (simplexCoordinateLinearMap k x) = 0
  rw [simplexAmbientSumLinearMap_apply, Fin.sum_univ_castSucc]
  simp

/-- Affine coordinates identify `ℝ^k` with the zero-sum hyperplane in barycentric space. -/
noncomputable def simplexCoordinateLinearEquivTangent (k : ℕ) :
    (Fin k → ℝ) ≃ₗ[ℝ] simplexTangentSubmodule k where
  toFun x := ⟨simplexCoordinateLinearMap k x,
    simplexCoordinateLinearMap_mem_tangent k x⟩
  invFun y := simplexCoordinateOfBarycentric k y
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp
  left_inv x := by
    ext i
    simp [simplexCoordinateOfBarycentric]
  right_inv y := by
    ext j
    cases j using Fin.lastCases
    · have hy0 : simplexAmbientSumLinearMap k (y : SimplexAmbient k) = 0 := y.2
      have hy :
          ∑ i : Fin k, (y : SimplexAmbient k) i.castSucc +
              (y : SimplexAmbient k) (Fin.last k) = 0 := by
        rw [simplexAmbientSumLinearMap_apply, Fin.sum_univ_castSucc] at hy0
        exact hy0
      simp [simplexCoordinateOfBarycentric]
      linarith
    · simp [simplexCoordinateOfBarycentric]

/-- The affine barycentric coordinate map has this linear part and a constant last vertex. -/
theorem simplexCoordinateMap_eq_linear_add_const
    (k : ℕ) (x : Fin k → ℝ) :
    simplexCoordinateMap k x =
      simplexCoordinateLinearMap k x + Pi.single (Fin.last k) (1 : ℝ) := by
  ext j
  cases j using Fin.lastCases
  · simp [simplexCoordinateMap]
    ring
  · simp [simplexCoordinateMap]

/-- The affine coordinate map to barycentric coordinates is smooth. -/
theorem contDiff_simplexCoordinateMap (k : ℕ) {r : WithTop ℕ∞} :
    ContDiff ℝ r (simplexCoordinateMap k) := by
  classical
  have h :
      ContDiff ℝ r
        (fun x : Fin k → ℝ =>
          simplexCoordinateLinearMap k x + Pi.single (Fin.last k) (1 : ℝ)) :=
    (simplexCoordinateLinearMap k).contDiff.add contDiff_const
  convert h using 1
  ext x j
  cases j using Fin.lastCases
  · simp [simplexCoordinateMap]
    ring
  · simp [simplexCoordinateMap]

/-- The ambient linear map inducing a map between standard simplices. -/
noncomputable def simplexAmbientMap {k l : ℕ}
    (f : Fin (k + 1) → Fin (l + 1)) :
    SimplexAmbient k →L[ℝ] SimplexAmbient l :=
  ⟨FunOnFinite.linearMap ℝ ℝ f, FunOnFinite.continuous_linearMap ℝ ℝ f⟩

@[simp]
theorem simplexAmbientMap_succAbove_apply_omitted
    {k : ℕ} (i : Fin (k + 2)) (y : SimplexAmbient k) :
    simplexAmbientMap i.succAbove y i = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ i.succAbove y i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun a : Fin (k + 1) => i.succAbove a = i) = ∅ := by
    ext a
    simp [Fin.succAbove_ne]
  rw [hfilter]
  simp

@[simp]
theorem simplexAmbientMap_succAbove_apply_succAbove
    {k : ℕ} (i : Fin (k + 2)) (y : SimplexAmbient k) (j : Fin (k + 1)) :
    simplexAmbientMap i.succAbove y (i.succAbove j) = y j := by
  classical
  change FunOnFinite.linearMap ℝ ℝ i.succAbove y (i.succAbove j) = y j
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter
          (fun a : Fin (k + 1) => i.succAbove a = i.succAbove j) = {j} := by
    ext a
    simp
  rw [hfilter]
  simp

/-- The lower endpoint of the last-coordinate slicing is the face where the
penultimate barycentric coordinate is zero. -/
theorem simplexCoordinateMap_slice_zero_eq_face
    (k : ℕ) (x : Fin k → ℝ) :
    simplexCoordinateMap (k + 1) (simplexCoordinateSliceMap k x 0) =
      simplexAmbientMap (Fin.castSucc (Fin.last k)).succAbove
        (simplexCoordinateMap k x) := by
  classical
  ext j
  cases j using Fin.lastCases with
  | last =>
      simpa [simplexCoordinateMap, simplexCoordinateSliceMap] using
        (simplexAmbientMap_succAbove_apply_succAbove
          (i := (Fin.castSucc (Fin.last k))) (y := simplexCoordinateMap k x)
          (j := Fin.last k)).symm
  | cast j =>
      cases j using Fin.lastCases with
      | last =>
          simp [simplexCoordinateMap, simplexCoordinateSliceMap]
      | cast j =>
          simpa [simplexCoordinateMap, simplexCoordinateSliceMap] using
            (simplexAmbientMap_succAbove_apply_succAbove
              (i := (Fin.castSucc (Fin.last k))) (y := simplexCoordinateMap k x)
              (j := Fin.castSucc j)).symm

/-- The upper endpoint of the last-coordinate slicing is the final face of the
standard simplex. -/
theorem simplexCoordinateMap_slice_upper_eq_face
    (k : ℕ) (x : Fin k → ℝ) :
    simplexCoordinateMap (k + 1)
        (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i)) =
      simplexAmbientMap (Fin.last (k + 1)).succAbove
        (simplexCoordinateMap k x) := by
  classical
  ext j
  cases j using Fin.lastCases with
  | last =>
      simpa [simplexCoordinateMap, simplexCoordinateSliceMap, Fin.sum_univ_castSucc] using
        (simplexAmbientMap_succAbove_apply_omitted
          (i := Fin.last (k + 1)) (y := simplexCoordinateMap k x)).symm
  | cast j =>
      cases j using Fin.lastCases with
      | last =>
          simpa [simplexCoordinateMap, simplexCoordinateSliceMap] using
            (simplexAmbientMap_succAbove_apply_succAbove
              (i := Fin.last (k + 1)) (y := simplexCoordinateMap k x)
              (j := Fin.last k)).symm
      | cast j =>
          simpa [simplexCoordinateMap, simplexCoordinateSliceMap] using
            (simplexAmbientMap_succAbove_apply_succAbove
              (i := Fin.last (k + 1)) (y := simplexCoordinateMap k x)
              (j := Fin.castSucc j)).symm

/-- The affine coordinate map on the domain of the `i`-th face, written in the
coordinates of the ambient simplex. -/
noncomputable def simplexFaceCoordinateMap {k : ℕ} (i : Fin (k + 2))
    (x : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  simplexCoordinateOfBarycentric (k + 1)
    (simplexAmbientMap i.succAbove (simplexCoordinateMap k x))

/-- The linear part of the affine coordinate map of a face. -/
noncomputable def simplexFaceCoordinateLinearMap {k : ℕ} (i : Fin (k + 2)) :
    (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
  (simplexCoordinateProjectionLinearMap (k + 1)).comp
    ((simplexAmbientMap i.succAbove).comp (simplexCoordinateLinearMap k))

theorem simplexCoordinateMap_simplexFaceCoordinateMap
    {k : ℕ} (i : Fin (k + 2)) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexCoordinateMap (k + 1) (simplexFaceCoordinateMap i x) =
      simplexAmbientMap i.succAbove (simplexCoordinateMap k x) := by
  apply simplexCoordinateMap_simplexCoordinateOfBarycentric
  exact stdSimplex.image_linearMap i.succAbove
    ⟨simplexCoordinateMap k x, simplexCoordinateMap_mem_stdSimplex hx, rfl⟩

theorem simplexFaceCoordinateMap_mem
    {k : ℕ} (i : Fin (k + 2)) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexFaceCoordinateMap i x ∈ simplexCoordinateDomain (k + 1) := by
  apply simplexCoordinateOfBarycentric_mem
  exact stdSimplex.image_linearMap i.succAbove
    ⟨simplexCoordinateMap k x, simplexCoordinateMap_mem_stdSimplex hx, rfl⟩

theorem simplexFaceCoordinateMap_eq_linear_add_const
    {k : ℕ} (i : Fin (k + 2)) (x : Fin k → ℝ) :
    simplexFaceCoordinateMap i x =
      simplexFaceCoordinateLinearMap i x +
        simplexCoordinateOfBarycentric (k + 1)
          (simplexAmbientMap i.succAbove (Pi.single (Fin.last k) (1 : ℝ))) := by
  ext j
  simp [simplexFaceCoordinateMap, simplexFaceCoordinateLinearMap,
    simplexCoordinateOfBarycentric, simplexCoordinateMap_eq_linear_add_const, map_add]

theorem fderivWithin_simplexFaceCoordinateMap
    {k : ℕ} (i : Fin (k + 2)) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    fderivWithin ℝ (simplexFaceCoordinateMap i)
      (simplexCoordinateDomain k) x =
      simplexFaceCoordinateLinearMap i := by
  let c : Fin (k + 1) → ℝ :=
    simplexCoordinateOfBarycentric (k + 1)
      (simplexAmbientMap i.succAbove (Pi.single (Fin.last k) (1 : ℝ)))
  have hfun :
      simplexFaceCoordinateMap i =
        fun y : Fin k → ℝ => simplexFaceCoordinateLinearMap i y + c := by
    funext y
    exact simplexFaceCoordinateMap_eq_linear_add_const i y
  rw [hfun]
  simpa using
    (ContinuousLinearMap.fderivWithin
      (simplexFaceCoordinateLinearMap i)
      ((uniqueDiffOn_simplexCoordinateDomain k) x hx))

theorem hasFDerivWithinAt_simplexFaceCoordinateMap
    {k : ℕ} (i : Fin (k + 2)) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    HasFDerivWithinAt (simplexFaceCoordinateMap i)
      (simplexFaceCoordinateLinearMap i)
      (simplexCoordinateDomain k) x := by
  rw [← fderivWithin_simplexFaceCoordinateMap i hx]
  have hdiff : Differentiable ℝ (simplexFaceCoordinateMap i) := by
    have hfun :
        simplexFaceCoordinateMap i =
          fun y : Fin k → ℝ =>
            simplexFaceCoordinateLinearMap i y +
              simplexCoordinateOfBarycentric (k + 1)
                (simplexAmbientMap i.succAbove (Pi.single (Fin.last k) (1 : ℝ))) := by
      funext y
      exact simplexFaceCoordinateMap_eq_linear_add_const i y
    rw [hfun]
    exact (simplexFaceCoordinateLinearMap i).differentiable.add_const _
  exact (hdiff x).differentiableWithinAt.hasFDerivWithinAt

/-- The face omitting the penultimate barycentric coordinate is the lower
endpoint of the last-coordinate slice. -/
@[simp]
theorem simplexFaceCoordinateMap_castSucc_last
    (k : ℕ) (x : Fin k → ℝ) :
    simplexFaceCoordinateMap (Fin.castSucc (Fin.last k)) x =
      simplexCoordinateSliceMap k x 0 := by
  rw [simplexFaceCoordinateMap]
  rw [← simplexCoordinateMap_slice_zero_eq_face k x]
  exact simplexCoordinateOfBarycentric_simplexCoordinateMap (k + 1)
    (simplexCoordinateSliceMap k x 0)

/-- The final face is the upper endpoint of the last-coordinate slice. -/
@[simp]
theorem simplexFaceCoordinateMap_last
    (k : ℕ) (x : Fin k → ℝ) :
    simplexFaceCoordinateMap (Fin.last (k + 1)) x =
      simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i) := by
  rw [simplexFaceCoordinateMap]
  rw [← simplexCoordinateMap_slice_upper_eq_face k x]
  exact simplexCoordinateOfBarycentric_simplexCoordinateMap (k + 1)
    (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i))

/-- Setting an arbitrary affine coordinate to zero gives the corresponding
coordinate face. -/
theorem simplexFaceCoordinateMap_castSucc_eq_insert_zero
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ) :
    simplexFaceCoordinateMap i.castSucc x =
      simplexCoordinateInsertMap i x 0 := by
  rw [simplexFaceCoordinateMap]
  have hmap :
      simplexAmbientMap i.castSucc.succAbove (simplexCoordinateMap k x) =
        simplexCoordinateMap (k + 1) (simplexCoordinateInsertMap i x 0) := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i.castSucc j with rfl | ⟨a, rfl⟩
    · simp [simplexCoordinateMap, simplexCoordinateInsertMap]
    · cases a using Fin.lastCases with
      | last =>
          calc
            (simplexAmbientMap i.castSucc.succAbove)
                (simplexCoordinateMap k x) (i.castSucc.succAbove (Fin.last k)) =
                1 - ∑ a : Fin k, x a := by
                  simpa [simplexCoordinateMap] using
                    (simplexAmbientMap_succAbove_apply_succAbove
                      (i := i.castSucc) (y := simplexCoordinateMap k x)
                      (j := Fin.last k))
            _ = simplexCoordinateMap (k + 1)
                (simplexCoordinateInsertMap i x 0)
                (i.castSucc.succAbove (Fin.last k)) := by
                  have hidx :
                      i.castSucc.succAbove (Fin.last k) = Fin.last (k + 1) := by
                    have hnot : ¬ Fin.last k < i := not_lt.mpr (Fin.le_last i)
                    ext
                    simp [Fin.succAbove, hnot]
                  rw [hidx]
                  simp [simplexCoordinateMap, simplexCoordinateInsertMap_sum]
      | cast a =>
          simpa [simplexCoordinateMap] using
            (simplexAmbientMap_succAbove_apply_succAbove
              (i := i.castSucc) (y := simplexCoordinateMap k x)
              (j := Fin.castSucc a))
  rw [hmap]
  exact simplexCoordinateOfBarycentric_simplexCoordinateMap (k + 1)
    (simplexCoordinateInsertMap i x 0)

theorem castSucc_succAbove_castSucc
    {k : ℕ} (i : Fin (k + 1)) (j : Fin k) :
    i.castSucc.succAbove j.castSucc = (i.succAbove j).castSucc := by
  ext
  by_cases h : j.castSucc < i
  · have hcast : j.castSucc.castSucc < i.castSucc := by
      exact h
    simp [Fin.succAbove, h, hcast]
  · have h' : ¬ j.castSucc < i := by
      exact h
    have hcast : ¬ j.castSucc.castSucc < i.castSucc := by
      intro hj
      exact h (by exact hj)
    simp [Fin.succAbove, h', hcast]

/-- The linear part of the face omitting affine coordinate `i` inserts a zero
in the omitted coordinate. -/
theorem simplexFaceCoordinateLinearMap_castSucc_apply_succAbove
    {k : ℕ} (i : Fin (k + 1)) (v : Fin k → ℝ) (j : Fin k) :
    simplexFaceCoordinateLinearMap i.castSucc v (i.succAbove j) = v j := by
  have hcoord :
      i.castSucc.succAbove j.castSucc = (i.succAbove j).castSucc :=
    castSucc_succAbove_castSucc i j
  simpa [simplexFaceCoordinateLinearMap, simplexCoordinateOfBarycentric, hcoord] using
    (simplexAmbientMap_succAbove_apply_succAbove
      (i := i.castSucc) (y := simplexCoordinateLinearMap k v)
      (j := j.castSucc))

/-- The linear part of the face omitting affine coordinate `i` vanishes in the
omitted coordinate. -/
theorem simplexFaceCoordinateLinearMap_castSucc_apply_self
    {k : ℕ} (i : Fin (k + 1)) (v : Fin k → ℝ) :
    simplexFaceCoordinateLinearMap i.castSucc v i = 0 := by
  simp [simplexFaceCoordinateLinearMap, simplexCoordinateOfBarycentric]

/-- On basis vectors, the linear part of the face omitting affine coordinate
`i` is the corresponding ambient coordinate basis vector. -/
theorem simplexFaceCoordinateLinearMap_castSucc_basis
    {k : ℕ} (i : Fin (k + 1)) (j : Fin k) :
    simplexFaceCoordinateLinearMap i.castSucc (Pi.single j (1 : ℝ)) =
      Pi.single (i.succAbove j) (1 : ℝ) := by
  ext m
  rcases Fin.eq_self_or_eq_succAbove i m with rfl | ⟨a, rfl⟩
  · simp [simplexFaceCoordinateLinearMap_castSucc_apply_self]
  · by_cases ha : a = j
    · subst ha
      simp [simplexFaceCoordinateLinearMap_castSucc_apply_succAbove]
    · simp [simplexFaceCoordinateLinearMap_castSucc_apply_succAbove, ha]

/-- The linear part of the final face has the usual tangent basis
`e_j - e_last`. -/
theorem simplexFaceCoordinateLinearMap_last_basis
    {k : ℕ} (j : Fin k) :
    simplexFaceCoordinateLinearMap (Fin.last (k + 1)) (Pi.single j (1 : ℝ)) =
      Pi.single j.castSucc (1 : ℝ) - Pi.single (Fin.last k) (1 : ℝ) := by
  ext m
  cases m using Fin.lastCases with
  | last =>
      have h :=
        simplexAmbientMap_succAbove_apply_succAbove
          (i := Fin.last (k + 1))
          (y := simplexCoordinateLinearMap k (Pi.single j (1 : ℝ)))
          (j := Fin.last k)
      simpa [simplexFaceCoordinateLinearMap, simplexCoordinateOfBarycentric] using h
  | cast m =>
      have h :=
        simplexAmbientMap_succAbove_apply_succAbove
          (i := Fin.last (k + 1))
          (y := simplexCoordinateLinearMap k (Pi.single j (1 : ℝ)))
          (j := Fin.castSucc m)
      by_cases hm : m = j
      · subst hm
        simpa [simplexFaceCoordinateLinearMap, simplexCoordinateOfBarycentric] using h
      · simpa [simplexFaceCoordinateLinearMap, simplexCoordinateOfBarycentric, hm] using h

@[simp]
theorem simplexAmbientMap_perm_apply
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) (y : SimplexAmbient k)
    (j : Fin (k + 1)) :
    simplexAmbientMap p y j = y (p.symm j) := by
  classical
  change FunOnFinite.linearMap ℝ ℝ p y j = y (p.symm j)
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter :
      (Finset.univ.filter fun x : Fin (k + 1) ↦ p x = j) = {p.symm j} := by
    ext x
    simp [Equiv.apply_eq_iff_eq_symm_apply]
  rw [hfilter]
  simp

theorem simplexAmbientSumLinearMap_simplexAmbientMap
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) (y : SimplexAmbient k) :
    simplexAmbientSumLinearMap k (simplexAmbientMap p y) =
      simplexAmbientSumLinearMap k y := by
  classical
  rw [simplexAmbientSumLinearMap_apply, simplexAmbientSumLinearMap_apply]
  calc
    ∑ j : Fin (k + 1), (simplexAmbientMap p) y j =
        ∑ j : Fin (k + 1), y (p.symm j) := by
          simp
    _ = ∑ j : Fin (k + 1), y j := by
          simpa using (Equiv.sum_comp p.symm fun j : Fin (k + 1) ↦ y j)

theorem simplexAmbientMap_preserves_tangent
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) :
    simplexTangentSubmodule k ≤
      (simplexTangentSubmodule k).comap
        (simplexAmbientMap p : SimplexAmbient k →ₗ[ℝ] SimplexAmbient k) := by
  intro y hy
  change simplexAmbientSumLinearMap k (simplexAmbientMap p y) = 0
  rw [simplexAmbientSumLinearMap_simplexAmbientMap p y]
  exact hy

theorem simplexAmbientMap_det
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) :
    LinearMap.det (simplexAmbientMap p : SimplexAmbient k →ₗ[ℝ] SimplexAmbient k) =
      ((Equiv.Perm.sign p : ℤˣ) : ℝ) := by
  classical
  let e : Module.Basis (Fin (k + 1)) ℝ (SimplexAmbient k) :=
    Pi.basisFun ℝ (Fin (k + 1))
  have hcomp :
      e.det ((simplexAmbientMap p : SimplexAmbient k →ₗ[ℝ] SimplexAmbient k) ∘
          fun i : Fin (k + 1) ↦ e i) =
        LinearMap.det (simplexAmbientMap p :
          SimplexAmbient k →ₗ[ℝ] SimplexAmbient k) := by
    simpa [Function.comp_def, Module.Basis.det_self] using
      (Module.Basis.det_comp e
        (simplexAmbientMap p : SimplexAmbient k →ₗ[ℝ] SimplexAmbient k)
        (fun i : Fin (k + 1) ↦ e i))
  have hfamily :
      ((simplexAmbientMap p : SimplexAmbient k →ₗ[ℝ] SimplexAmbient k) ∘
          fun i : Fin (k + 1) ↦ e i) =
        e ∘ p := by
    funext i
    ext j
    simp [simplexAmbientMap, e, Pi.basisFun_apply]
  rw [← hcomp, hfamily]
  simpa [Module.Basis.det_self, Units.smul_def] using
    (e.det.map_perm (fun i : Fin (k + 1) ↦ e i) p)

variable (I : ModelWithCorners ℝ E H)

/--
%%handwave
name:
  Smoothness of a singular simplex
statement:
  A parameterized singular simplex is \(C^r\) when it is the restriction to
  the standard simplex of a \(C^r\) map defined on the ambient affine space.
-/
def HasContMDiffExtensionOnSimplex (k : ℕ) (r : WithTop ℕ∞)
    (f : StandardSimplex k → M) : Prop :=
  ∃ F : SimplexAmbient k → M,
    ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r F (stdSimplex ℝ (Fin (k + 1))) ∧
      ∀ x : StandardSimplex k, F (x : SimplexAmbient k) = f x

/--
%%handwave
name:
  \(C^r\) singular simplex
statement:
  A \(C^r\) singular \(k\)-simplex in a manifold is a continuous map from the
  standard \(k\)-simplex to the manifold which has a \(C^r\) extension from the
  ambient affine space.
-/
structure ContMDiffSingularSimplex (k : ℕ) (r : WithTop ℕ∞) where
  /-- The underlying continuous singular simplex. -/
  toContinuousMap : C(StandardSimplex k, M)
  /-- The simplex is `C^r` in the extension sense. -/
  contMDiff :
    HasContMDiffExtensionOnSimplex (I := I) k r toContinuousMap

namespace ContMDiffSingularSimplex

variable {I}
variable {k : ℕ} {r : WithTop ℕ∞}

instance : CoeFun (ContMDiffSingularSimplex (I := I) (M := M) k r)
    (fun _ ↦ StandardSimplex k → M) where
  coe σ := σ.toContinuousMap

/-- A chosen ambient extension of a smooth singular simplex. -/
noncomputable def extension
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) : SimplexAmbient k → M :=
  Classical.choose σ.contMDiff

theorem extension_contMDiffOn
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) :
    ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r σ.extension
      (stdSimplex ℝ (Fin (k + 1))) :=
  (Classical.choose_spec σ.contMDiff).1

theorem extension_eq
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (x : StandardSimplex k) :
    σ.extension (x : SimplexAmbient k) = σ.toContinuousMap x :=
  (Classical.choose_spec σ.contMDiff).2 x

/--
The underlying Mathlib singular simplex.  This is the bridge from smooth
singular chains to Mathlib's singular set and singular homology.
-/
noncomputable def toSSetSimplex
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) :
    (TopCat.toSSet.obj (TopCat.of M)).obj (Opposite.op (SimplexCategory.mk k)) :=
  (TopCat.toSSetObjEquiv (TopCat.of M) (Opposite.op (SimplexCategory.mk k))).symm
    σ.toContinuousMap

end ContMDiffSingularSimplex

/-- Smooth singular simplices are \(C^\infty\) singular simplices. -/
abbrev SmoothSingularSimplex (k : ℕ) :=
  ContMDiffSingularSimplex (I := I) (M := M) k ∞

/-- \(C^1\) singular simplices are enough for integrating continuous forms. -/
abbrev C1SingularSimplex (k : ℕ) :=
  ContMDiffSingularSimplex (I := I) (M := M) k (1 : WithTop ℕ∞)

/-- A \(C^2\) simplex is in particular \(C^1\), which is enough for integration. -/
theorem one_le_of_two_le_smoothness {r : WithTop ℕ∞}
    (h : (2 : WithTop ℕ∞) ≤ r) : (1 : WithTop ℕ∞) ≤ r := by
  exact (by norm_num : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞)).trans h

/-- A vertex permutation acts on the standard simplex by permuting barycentric coordinates. -/
noncomputable def simplexVertexPermutationMap {k : ℕ}
    (p : Equiv.Perm (Fin (k + 1))) :
    C(StandardSimplex k, StandardSimplex k) :=
  ⟨stdSimplex.map p, stdSimplex.continuous_map p⟩

/-- The affine-coordinate self-map induced by a permutation of the simplex vertices. -/
noncomputable def simplexCoordinateVertexPermutationMap {k : ℕ}
    (p : Equiv.Perm (Fin (k + 1))) (x : Fin k → ℝ) : Fin k → ℝ :=
  simplexCoordinateOfBarycentric k
    (FunOnFinite.linearMap ℝ ℝ p (simplexCoordinateMap k x))

/-- The upper endpoint obtained by inserting the residual barycentric
coordinate in slot `i` is the standard final-face parametrization after the
corresponding cyclic vertex permutation of the face coordinates. -/
theorem simplexCoordinateOfBarycentric_insert_upper_eq_vertexPermutation
    {k : ℕ} (i : Fin (k + 1)) (x : Fin k → ℝ) :
    simplexCoordinateOfBarycentric k
        (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j)) =
      simplexCoordinateVertexPermutationMap
        (i.cycleRange.symm * (Fin.last k).cycleRange) x := by
  classical
  let r : ℝ := 1 - ∑ j : Fin k, x j
  let b : Fin (k + 1) → ℝ := simplexCoordinateMap k x
  let p : Equiv.Perm (Fin (k + 1)) :=
    i.cycleRange.symm * (Fin.last k).cycleRange
  have hlin : FunOnFinite.linearMap ℝ ℝ p b = b ∘ p.symm := by
    ext a
    change simplexAmbientMap p b a = (b ∘ p.symm) a
    simp
  have hcons : (Fin.cons r x : Fin (k + 1) → ℝ) =
      b ∘ (Fin.last k).cycleRange.symm := by
    ext a
    cases a using Fin.cases with
    | zero =>
        change r = b ((Fin.last k).cycleRange.symm 0)
        rw [Fin.cycleRange_symm_zero]
        simp [b, r, simplexCoordinateMap]
    | succ a =>
        change x a = b ((Fin.last k).cycleRange.symm a.succ)
        rw [Fin.cycleRange_symm_succ]
        simp [b, simplexCoordinateMap]
  have hinsert :
      simplexCoordinateInsertMap i x r =
        ((Fin.cons r x : Fin (k + 1) → ℝ) ∘ i.cycleRange) := by
    simp [simplexCoordinateInsertMap, Fin.cons_comp_cycleRange]
  ext a
  change simplexCoordinateInsertMap i x r a.castSucc =
    simplexCoordinateOfBarycentric k
      (FunOnFinite.linearMap ℝ ℝ p (simplexCoordinateMap k x)) a
  simp only [simplexCoordinateOfBarycentric]
  rw [hlin]
  change simplexCoordinateInsertMap i x r a.castSucc = b (p.symm a.castSucc)
  rw [hinsert]
  change
    (Fin.cons r x : Fin (k + 1) → ℝ) (i.cycleRange a.castSucc) =
      b (p.symm a.castSucc)
  rw [hcons]
  change
    b ((Fin.last k).cycleRange.symm (i.cycleRange a.castSucc)) =
      b (p.symm a.castSucc)
  congr 1

/-- The cyclic vertex permutation used by the upper-endpoint parametrization
has the expected orientation sign. -/
theorem upperEndpointVertexPermutation_sign_int
    {k : ℕ} (i : Fin (k + 1)) :
    (((Equiv.Perm.sign
        (i.cycleRange.symm * (Fin.last k).cycleRange) : ℤˣ) : ℤ)) =
      ((-1 : ℤ) ^ (i : ℕ)) * ((-1 : ℤ) ^ k) := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm]
  rw [Fin.sign_cycleRange, Fin.sign_cycleRange, Fin.val_last]
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  rfl

/-- The linear part of the affine coordinate self-map induced by a vertex permutation. -/
noncomputable def simplexCoordinateVertexPermutationLinearMap {k : ℕ}
    (p : Equiv.Perm (Fin (k + 1))) :
    (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  (simplexCoordinateProjectionLinearMap k).comp
    ((simplexAmbientMap p).comp (simplexCoordinateLinearMap k))

@[simp]
theorem simplexCoordinateVertexPermutationLinearMap_apply
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) (x : Fin k → ℝ) :
    simplexCoordinateVertexPermutationLinearMap p x =
      simplexCoordinateOfBarycentric k
        (FunOnFinite.linearMap ℝ ℝ p (simplexCoordinateLinearMap k x)) := by
  rfl

theorem simplexCoordinateVertexPermutationLinearMap_conj_tangent
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) :
    ((simplexCoordinateLinearEquivTangent k).symm :
        simplexTangentSubmodule k ≃ₗ[ℝ] (Fin k → ℝ)).toLinearMap.comp
        (((simplexAmbientMap p : SimplexAmbient k →ₗ[ℝ] SimplexAmbient k).restrict
          (simplexAmbientMap_preserves_tangent p)).comp
          (simplexCoordinateLinearEquivTangent k).toLinearMap) =
      (simplexCoordinateVertexPermutationLinearMap p :
        (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) := by
  ext x i
  rfl

theorem simplexCoordinateVertexPermutationLinearMap_det
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) :
    LinearMap.det
        (simplexCoordinateVertexPermutationLinearMap p :
          (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) =
      ((Equiv.Perm.sign p : ℤˣ) : ℝ) := by
  classical
  let W : Submodule ℝ (SimplexAmbient k) := simplexTangentSubmodule k
  let P : SimplexAmbient k →ₗ[ℝ] SimplexAmbient k :=
    (simplexAmbientMap p : SimplexAmbient k →ₗ[ℝ] SimplexAmbient k)
  let hpres : W ≤ W.comap P := simplexAmbientMap_preserves_tangent p
  have hquot :
      LinearMap.det (W.mapQ W P hpres) = (1 : ℝ) := by
    have hmapQ : W.mapQ W P hpres = LinearMap.id := by
      apply LinearMap.ext
      intro q
      refine Submodule.Quotient.induction_on W q ?_
      intro y
      rw [Submodule.mapQ_apply]
      change Submodule.Quotient.mk (P y) = Submodule.Quotient.mk y
      rw [Submodule.Quotient.eq]
      change P y - y ∈ W
      change simplexAmbientSumLinearMap k (P y - y) = 0
      simp [P, simplexAmbientSumLinearMap_simplexAmbientMap p y]
    rw [hmapQ, LinearMap.det_id]
  have hrestrict :
      LinearMap.det (P.restrict hpres) =
        ((Equiv.Perm.sign p : ℤˣ) : ℝ) := by
    have h := LinearMap.det_eq_det_mul_det W P hpres
    rw [show LinearMap.det P = ((Equiv.Perm.sign p : ℤˣ) : ℝ) by
      simpa [P] using simplexAmbientMap_det p, hquot, mul_one] at h
    exact h.symm
  have hconj :=
    LinearMap.det_conj (P.restrict hpres)
      ((simplexCoordinateLinearEquivTangent k).symm :
        simplexTangentSubmodule k ≃ₗ[ℝ] (Fin k → ℝ))
  have hconjmap :
      (((simplexCoordinateLinearEquivTangent k).symm :
          simplexTangentSubmodule k ≃ₗ[ℝ] (Fin k → ℝ)).toLinearMap.comp
          ((P.restrict hpres).comp
            ((simplexCoordinateLinearEquivTangent k).symm.symm).toLinearMap)) =
        (simplexCoordinateVertexPermutationLinearMap p :
          (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) := by
    ext x i
    rfl
  rw [hconjmap] at hconj
  exact hconj.trans hrestrict

/-- The coordinate self-map induced by a vertex permutation is affine. -/
theorem simplexCoordinateVertexPermutationMap_eq_linear_add_const
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) (x : Fin k → ℝ) :
    simplexCoordinateVertexPermutationMap p x =
      simplexCoordinateVertexPermutationLinearMap p x +
        simplexCoordinateOfBarycentric k
          (FunOnFinite.linearMap ℝ ℝ p (Pi.single (Fin.last k) (1 : ℝ))) := by
  ext i
  simp [simplexCoordinateVertexPermutationMap, simplexCoordinateVertexPermutationLinearMap,
    simplexAmbientMap, simplexCoordinateOfBarycentric, simplexCoordinateMap_eq_linear_add_const,
    map_add]

theorem simplexCoordinateVertexPermutationMap_mem
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexCoordinateVertexPermutationMap p x ∈ simplexCoordinateDomain k := by
  apply simplexCoordinateOfBarycentric_mem
  exact stdSimplex.image_linearMap p
    ⟨simplexCoordinateMap k x, simplexCoordinateMap_mem_stdSimplex hx, rfl⟩

theorem simplexCoordinateMap_vertexPermutation
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexCoordinateMap k (simplexCoordinateVertexPermutationMap p x) =
      FunOnFinite.linearMap ℝ ℝ p (simplexCoordinateMap k x) := by
  apply simplexCoordinateMap_simplexCoordinateOfBarycentric
  exact stdSimplex.image_linearMap p
    ⟨simplexCoordinateMap k x, simplexCoordinateMap_mem_stdSimplex hx, rfl⟩

@[simp]
theorem simplexCoordinateVertexPermutationMap_symm_apply
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexCoordinateVertexPermutationMap p.symm
      (simplexCoordinateVertexPermutationMap p x) = x := by
  have hmap :
      simplexCoordinateMap k
          (simplexCoordinateVertexPermutationMap p.symm
            (simplexCoordinateVertexPermutationMap p x)) =
        simplexCoordinateMap k x := by
    calc
      simplexCoordinateMap k
          (simplexCoordinateVertexPermutationMap p.symm
            (simplexCoordinateVertexPermutationMap p x)) =
          FunOnFinite.linearMap ℝ ℝ p.symm
            (simplexCoordinateMap k (simplexCoordinateVertexPermutationMap p x)) := by
            exact simplexCoordinateMap_vertexPermutation p.symm
              (simplexCoordinateVertexPermutationMap_mem p hx)
      _ = FunOnFinite.linearMap ℝ ℝ p.symm
            (FunOnFinite.linearMap ℝ ℝ p (simplexCoordinateMap k x)) := by
            rw [simplexCoordinateMap_vertexPermutation p hx]
      _ = simplexCoordinateMap k x := by
            ext j
            simp [FunOnFinite.linearMap]
  simpa [simplexCoordinateVertexPermutationMap] using
    congr_arg (simplexCoordinateOfBarycentric k) hmap

theorem contDiff_simplexCoordinateVertexPermutationMap
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) {r : WithTop ℕ∞} :
    ContDiff ℝ r (simplexCoordinateVertexPermutationMap p) := by
  simpa [simplexCoordinateVertexPermutationMap] using
    (simplexCoordinateProjectionLinearMap k).contDiff.comp
      ((simplexAmbientMap p).contDiff.comp (contDiff_simplexCoordinateMap k))

/-- The coordinate self-map induced by a vertex permutation has the expected derivative. -/
theorem fderivWithin_simplexCoordinateVertexPermutationMap
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    fderivWithin ℝ (simplexCoordinateVertexPermutationMap p)
      (simplexCoordinateDomain k) x =
      simplexCoordinateVertexPermutationLinearMap p := by
  let c : Fin k → ℝ :=
    simplexCoordinateOfBarycentric k
      (FunOnFinite.linearMap ℝ ℝ p (Pi.single (Fin.last k) (1 : ℝ)))
  have hfun :
      simplexCoordinateVertexPermutationMap p =
        fun y : Fin k → ℝ => simplexCoordinateVertexPermutationLinearMap p y + c := by
    funext y
    exact simplexCoordinateVertexPermutationMap_eq_linear_add_const p y
  rw [hfun]
  simpa using
    (ContinuousLinearMap.fderivWithin
      (simplexCoordinateVertexPermutationLinearMap p)
      ((uniqueDiffOn_simplexCoordinateDomain k) x hx))

theorem hasFDerivWithinAt_simplexCoordinateVertexPermutationMap
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    HasFDerivWithinAt (simplexCoordinateVertexPermutationMap p)
      (simplexCoordinateVertexPermutationLinearMap p)
      (simplexCoordinateDomain k) x := by
  rw [← fderivWithin_simplexCoordinateVertexPermutationMap p hx]
  have hdiff : Differentiable ℝ (simplexCoordinateVertexPermutationMap p) :=
    (contDiff_simplexCoordinateVertexPermutationMap (r := (1 : WithTop ℕ∞)) p).differentiable
      one_ne_zero
  exact (hdiff x).differentiableWithinAt.hasFDerivWithinAt

theorem simplexCoordinateVertexPermutationMap_injOn
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) :
    InjOn (simplexCoordinateVertexPermutationMap p) (simplexCoordinateDomain k) := by
  intro x hx y hy hxy
  have h := congrArg (simplexCoordinateVertexPermutationMap p.symm) hxy
  simpa [simplexCoordinateVertexPermutationMap_symm_apply p hx,
    simplexCoordinateVertexPermutationMap_symm_apply p hy] using h

theorem simplexCoordinateVertexPermutationMap_image_domain
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) :
    simplexCoordinateVertexPermutationMap p '' simplexCoordinateDomain k =
      simplexCoordinateDomain k := by
  apply subset_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact simplexCoordinateVertexPermutationMap_mem p hx
  · intro y hy
    refine ⟨simplexCoordinateVertexPermutationMap p.symm y,
      simplexCoordinateVertexPermutationMap_mem p.symm hy, ?_⟩
    simpa using simplexCoordinateVertexPermutationMap_symm_apply p.symm hy

/-- Vertex permutations preserve integration over the affine coordinate
simplex. -/
theorem integral_comp_simplexCoordinateVertexPermutationMap
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ} (p : Equiv.Perm (Fin (k + 1)))
    (g : (Fin k → ℝ) → G) :
    (∫ x in simplexCoordinateDomain k,
        g (simplexCoordinateVertexPermutationMap p x)) =
      ∫ x in simplexCoordinateDomain k, g x := by
  classical
  let D : Set (Fin k → ℝ) := simplexCoordinateDomain k
  let q : (Fin k → ℝ) → (Fin k → ℝ) :=
    simplexCoordinateVertexPermutationMap p
  let L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    simplexCoordinateVertexPermutationLinearMap p
  have hdetL :
      LinearMap.det (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) =
        ((Equiv.Perm.sign p : ℤˣ) : ℝ) := by
    simpa [L] using simplexCoordinateVertexPermutationLinearMap_det p
  have habsL :
      |LinearMap.det (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))| = (1 : ℝ) := by
    rw [hdetL]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hsign | hsign <;>
      simp [hsign]
  have hcov :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (s := D) (f := q)
      (by simpa [D] using measurableSet_simplexCoordinateDomain k)
      (fun x hx ↦ by
        show HasFDerivWithinAt q L D x
        simpa [D, q, L] using
          hasFDerivWithinAt_simplexCoordinateVertexPermutationMap p hx)
      (by simpa [D, q] using simplexCoordinateVertexPermutationMap_injOn p)
      g
  rw [show Set.image q D = D by
    simpa [D, q] using simplexCoordinateVertexPermutationMap_image_domain p] at hcov
  simpa [D, q, habsL] using hcov.symm

theorem hasContMDiffExtensionOnSimplex_comp_vertexPermutation
    {k : ℕ} {r : WithTop ℕ∞}
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (p : Equiv.Perm (Fin (k + 1))) :
    HasContMDiffExtensionOnSimplex (I := I) k r
      (fun x ↦ σ.toContinuousMap (simplexVertexPermutationMap p x)) := by
  rcases σ.contMDiff with ⟨F, hF, hF_eq⟩
  refine ⟨F ∘ simplexAmbientMap p, ?_, ?_⟩
  · exact hF.comp (simplexAmbientMap p).contMDiffOn fun x hx ↦ by
      change FunOnFinite.linearMap ℝ ℝ p x ∈ stdSimplex ℝ (Fin (k + 1))
      exact stdSimplex.image_linearMap p ⟨x, hx, rfl⟩
  · intro x
    simpa [simplexAmbientMap, simplexVertexPermutationMap] using
      hF_eq (simplexVertexPermutationMap p x)

namespace ContMDiffSingularSimplex

variable {I}

/-- Reparameterize a singular simplex by permuting the vertices of the source simplex. -/
noncomputable def reparametrizeVertexPermutation
    {k : ℕ} {r : WithTop ℕ∞}
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (p : Equiv.Perm (Fin (k + 1))) :
    ContMDiffSingularSimplex (I := I) (M := M) k r where
  toContinuousMap := σ.toContinuousMap.comp (simplexVertexPermutationMap p)
  contMDiff :=
    hasContMDiffExtensionOnSimplex_comp_vertexPermutation (I := I) σ p

end ContMDiffSingularSimplex

/-- The inclusion of the `i`-th face of the standard simplex. -/
noncomputable def simplexFaceMap {k : ℕ} (i : Fin (k + 2)) :
    C(StandardSimplex k, StandardSimplex (k + 1)) :=
  ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩

theorem hasContMDiffExtensionOnSimplex_comp_face
    {k : ℕ} {r : WithTop ℕ∞}
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (i : Fin (k + 2)) :
    HasContMDiffExtensionOnSimplex (I := I) k r
      (fun x ↦ σ.toContinuousMap (simplexFaceMap i x)) := by
  rcases σ.contMDiff with ⟨F, hF, hF_eq⟩
  refine ⟨F ∘ simplexAmbientMap i.succAbove, ?_, ?_⟩
  · exact hF.comp (simplexAmbientMap i.succAbove).contMDiffOn fun x hx ↦ by
      change FunOnFinite.linearMap ℝ ℝ i.succAbove x ∈ stdSimplex ℝ (Fin (k + 2))
      exact stdSimplex.image_linearMap i.succAbove ⟨x, hx, rfl⟩
  · intro x
    simpa [simplexAmbientMap, simplexFaceMap] using hF_eq (simplexFaceMap i x)

namespace ContMDiffSingularSimplex

variable {I}

/-- Restrict a singular simplex to its `i`-th face. -/
noncomputable def face
    {k : ℕ} {r : WithTop ℕ∞}
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (i : Fin (k + 2)) :
    ContMDiffSingularSimplex (I := I) (M := M) k r where
  toContinuousMap := σ.toContinuousMap.comp (simplexFaceMap i)
  contMDiff := hasContMDiffExtensionOnSimplex_comp_face (I := I) σ i

end ContMDiffSingularSimplex

/--
%%handwave
name:
  Smooth singular chain
statement:
  A singular \(k\)-chain with \(C^r\) cells is a finite integer linear
  combination of \(C^r\) singular \(k\)-simplices.
-/
abbrev SingularChain (k : ℕ) (r : WithTop ℕ∞) : Type _ :=
  ContMDiffSingularSimplex (I := I) (M := M) k r →₀ ℤ

/--
%%handwave
name:
  Boundary of a singular chain
statement:
  The boundary of a parameterized simplex is the alternating sum of its
  codimension-one faces, and the boundary of a chain is obtained by linearity.
-/
noncomputable def boundary {k : ℕ} {r : WithTop ℕ∞} :
    SingularChain (I := I) (M := M) (k + 1) r →ₗ[ℤ]
      SingularChain (I := I) (M := M) k r :=
  Finsupp.linearCombination ℤ fun σ ↦
    ∑ i : Fin (k + 2),
      ((-1 : ℤ) ^ (i : ℕ)) •
        Finsupp.single (ContMDiffSingularSimplex.face (I := I) σ i) (1 : ℤ)

variable {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A vector-valued top-degree alternating map is the determinant form multiplied by its
value on an oriented basis. -/
theorem alternatingMap_eq_smulRight_basis_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V]
    {W : Type*} [AddCommGroup W] [Module R W]
    (e : Module.Basis ι R V) (form : V [⋀^ι]→ₗ[R] W) :
    form = e.det.smulRight (form fun i ↦ e i) := by
  classical
  refine Module.Basis.ext_alternating e fun i h ↦ ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change form (e ∘ σ) = (e.det.smulRight (form fun i ↦ e i)) (e ∘ σ)
  simp [AlternatingMap.map_perm, Module.Basis.det_self]

/-- Pulling a top-degree continuous alternating map back by a linear endomorphism scales
its coefficient by the determinant. -/
theorem continuousAlternatingMap_compContinuousLinearMap_apply_basisFun_det
    {k : ℕ} (form : (Fin k → ℝ) [⋀^Fin k]→L[ℝ] F)
    (L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) :
    form.compContinuousLinearMap L (fun i : Fin k ↦ Pi.single i (1 : ℝ)) =
      LinearMap.det (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) •
        form (fun i : Fin k ↦ Pi.single i (1 : ℝ)) := by
  classical
  let e : Module.Basis (Fin k) ℝ (Fin k → ℝ) := Pi.basisFun ℝ (Fin k)
  have h :=
    congrFun (congrArg DFunLike.coe
      (alternatingMap_eq_smulRight_basis_det e
        form.toAlternatingMap)) (fun i ↦ L (e i))
  have hdet :
      e.det (fun i : Fin k ↦ L (e i)) =
        LinearMap.det (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) := by
    simpa [Function.comp_def, Module.Basis.det_self] using
      (Module.Basis.det_comp e (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))
        (fun i : Fin k ↦ e i))
  simp [AlternatingMap.smulRight_apply, hdet] at h
  simpa [e, Pi.basisFun_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def] using h

theorem intUnit_real_smul_eq_int_smul (u : ℤˣ) (x : F) :
    ((u : ℝ) • x) = ((u : ℤ) • x) := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

theorem abs_intUnit_cast_real (u : ℤˣ) :
    |((u : ℤ) : ℝ)| = (1 : ℝ) := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

theorem integral_negOnePow_zsmul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (n : ℕ) (f : α → F) :
    (∫ x, ((-1 : ℤ) ^ n) • f x ∂μ) =
      ((-1 : ℤ) ^ n) • ∫ x, f x ∂μ := by
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ n) with h | h
  · have hInt : ((-1 : ℤ) ^ n) = 1 := by
      change ((((-1 : ℤˣ) : ℤ) ^ n) = 1)
      exact congrArg (fun u : ℤˣ => (u : ℤ)) h
    simp [hInt]
  · have hInt : ((-1 : ℤ) ^ n) = -1 := by
      change ((((-1 : ℤˣ) : ℤ) ^ n) = -1)
      exact congrArg (fun u : ℤˣ => (u : ℤ)) h
    simp [hInt, integral_neg]

omit [NormedSpace ℝ F] in
theorem integrable_negOnePow_zsmul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (n : ℕ) {f : α → F} (hf : Integrable f μ) :
    Integrable (fun x => ((-1 : ℤ) ^ n) • f x) μ := by
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ n) with h | h
  · have hInt : ((-1 : ℤ) ^ n) = 1 := by
      change ((((-1 : ℤˣ) : ℤ) ^ n) = 1)
      exact congrArg (fun u : ℤˣ => (u : ℤ)) h
    simpa [hInt] using hf
  · have hInt : ((-1 : ℤ) ^ n) = -1 := by
      change ((((-1 : ℤˣ) : ℤ) ^ n) = -1)
      exact congrArg (fun u : ℤˣ => (u : ℤ)) h
    simpa [hInt] using hf.neg

/-- Continuous differential forms are \(C^0\) forms. -/
abbrev ContinuousDifferentialForm (n : ℕ) :=
  DifferentialForm (I := I) (M := M) (F := F) (n := n) (r := (0 : WithTop ℕ∞))

/-- \(C^1\) differential forms are the regularity needed for Stokes' theorem. -/
abbrev C1DifferentialForm (n : ℕ) :=
  DifferentialForm (I := I) (M := M) (F := F) (n := n) (r := (1 : WithTop ℕ∞))

/-- The map from affine simplex coordinates to the manifold induced by an ambient extension. -/
noncomputable def simplexParametrizationUsingExtension
    {k : ℕ} (G : SimplexAmbient k → M) (x : Fin k → ℝ) : M :=
  G (simplexCoordinateMap k x)

/-- A \(C^r\) ambient extension restricts to a \(C^r\) map on affine simplex coordinates. -/
theorem contMDiffOn_simplexParametrizationUsingExtension
    {k : ℕ} {r : WithTop ℕ∞} {G : SimplexAmbient k → M}
    (hG : ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r G
      (stdSimplex ℝ (Fin (k + 1)))) :
    ContMDiffOn 𝓘(ℝ, Fin k → ℝ) I r
      (simplexParametrizationUsingExtension G) (simplexCoordinateDomain k) := by
  exact hG.comp (contDiff_simplexCoordinateMap k).contMDiff.contMDiffOn
    fun x hx ↦ simplexCoordinateMap_mem_stdSimplex hx

/-- The coordinate parametrization of a \(C^r\) singular simplex is \(C^r\). -/
theorem ContMDiffSingularSimplex.contMDiffOn_simplexParametrization
    {k : ℕ} {r : WithTop ℕ∞}
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) :
    ContMDiffOn 𝓘(ℝ, Fin k → ℝ) I r
      (simplexParametrizationUsingExtension σ.extension) (simplexCoordinateDomain k) :=
  contMDiffOn_simplexParametrizationUsingExtension (I := I)
    σ.extension_contMDiffOn

theorem ContMDiffSingularSimplex.contMDiffWithinAt_simplexParametrization
    {k : ℕ} {r : WithTop ℕ∞}
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    {x : Fin k → ℝ} (hx : x ∈ simplexCoordinateDomain k) :
    ContMDiffWithinAt 𝓘(ℝ, Fin k → ℝ) I r
      (simplexParametrizationUsingExtension σ.extension)
      (simplexCoordinateDomain k) x :=
  (ContMDiffSingularSimplex.contMDiffOn_simplexParametrization
    (I := I) (M := M) σ) x hx

theorem ContMDiffSingularSimplex.mdifferentiableWithinAt_simplexParametrization
    {k : ℕ} {r : WithTop ℕ∞}
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (hr : r ≠ 0) {x : Fin k → ℝ} (hx : x ∈ simplexCoordinateDomain k) :
    MDifferentiableWithinAt 𝓘(ℝ, Fin k → ℝ) I
      (simplexParametrizationUsingExtension σ.extension)
      (simplexCoordinateDomain k) x :=
  (ContMDiffSingularSimplex.contMDiffWithinAt_simplexParametrization
    (I := I) (M := M) σ hx).mdifferentiableWithinAt hr

theorem mfderivWithin_simplexParametrization_eq_fderivWithin_extChartAt
    [IsManifold I 1 M]
    {k : ℕ} {r : WithTop ℕ∞}
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (hr : r ≠ 0) {x : Fin k → ℝ} (hx : x ∈ simplexCoordinateDomain k) :
    mfderivWithin 𝓘(ℝ, Fin k → ℝ) I
        (simplexParametrizationUsingExtension σ.extension)
        (simplexCoordinateDomain k) x =
      fderivWithin ℝ
        (fun y : Fin k → ℝ =>
          (extChartAt I (simplexParametrizationUsingExtension σ.extension x))
            (simplexParametrizationUsingExtension σ.extension y))
        (simplexCoordinateDomain k) x := by
  rw [mfderivWithin]
  simp [ContMDiffSingularSimplex.mdifferentiableWithinAt_simplexParametrization
    (I := I) (M := M) σ hr hx, writtenInExtChartAt]
  rfl

/-- The pullback of a top-degree form along an explicit ambient extension of a simplex,
written in the standard affine coordinates on the source simplex. -/
noncomputable def simplexPullbackFormUsingExtension
    {k : ℕ}
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (G : SimplexAmbient k → M) (x : Fin k → ℝ) :
    (Fin k → ℝ) [⋀^Fin k]→L[ℝ] F :=
  (form.toFun (simplexParametrizationUsingExtension G x)).compContinuousLinearMap
    (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I
      (simplexParametrizationUsingExtension G) (simplexCoordinateDomain k) x)

/-- The pullback of a degree `k` form along an `m`-simplex, before taking a top-degree
coefficient.  The Stokes proof uses this when `m = k + 1`. -/
noncomputable def simplexPullbackFormAlongUsingExtension
    {m k : ℕ}
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (G : SimplexAmbient m → M) (x : Fin m → ℝ) :
    (Fin m → ℝ) [⋀^Fin k]→L[ℝ] F :=
  (form.toFun (simplexParametrizationUsingExtension G x)).compContinuousLinearMap
    (mfderivWithin 𝓘(ℝ, Fin m → ℝ) I
      (simplexParametrizationUsingExtension G) (simplexCoordinateDomain m) x)

/-- In a fixed chart around the image point, the pulled-back form along a simplex is the
ordinary model-space pullback of the coordinate representative. -/
theorem simplexPullbackFormAlongUsingExtension_eq_coordinateExpression_of_mem_source
    [IsManifold I ∞ M]
    {m k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) m r)
    {x y : Fin m → ℝ} (hy : y ∈ simplexCoordinateDomain m)
    (hsource :
      simplexParametrizationUsingExtension σ.extension y ∈
        (chartAt H (simplexParametrizationUsingExtension σ.extension x)).source) :
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
        (m := m) (k := k) form σ.extension y =
      (coordinateExpression (I := I) (F := F) (n := k) form.toFun
        (chartAt H (simplexParametrizationUsingExtension σ.extension x))
        ((extChartAt I (simplexParametrizationUsingExtension σ.extension x))
          (simplexParametrizationUsingExtension σ.extension y))).compContinuousLinearMap
        (fderivWithin ℝ
          (fun z : Fin m → ℝ =>
            (extChartAt I (simplexParametrizationUsingExtension σ.extension x))
              (simplexParametrizationUsingExtension σ.extension z))
          (simplexCoordinateDomain m) y) := by
  classical
  let D : Set (Fin m → ℝ) := simplexCoordinateDomain m
  let φ : (Fin m → ℝ) → M := simplexParametrizationUsingExtension σ.extension
  let e : OpenPartialHomeomorph M H := chartAt H (φ x)
  let ψ : (Fin m → ℝ) → E := fun z ↦ (extChartAt I (φ x)) (φ z)
  have he : e ∈ atlas H M := by
    simp [e]
  have hsource_ext : φ y ∈ (e.extend I).source := by
    simpa [e.extend_source (I := I), e, φ] using hsource
  have htarget : ψ y ∈ (e.extend I).target := by
    change (e.extend I) (φ y) ∈ (e.extend I).target
    exact (e.extend I).map_source hsource_ext
  have hleft : (e.extend I).symm (ψ y) = φ y := by
    change (e.extend I).symm ((e.extend I) (φ y)) = φ y
    exact (e.extend I).left_inv hsource_ext
  have hφ_contdiff :
      ContMDiffWithinAt 𝓘(ℝ, Fin m → ℝ) I r φ D y := by
    simpa [D, φ] using
      ContMDiffSingularSimplex.contMDiffWithinAt_simplexParametrization
        (I := I) (M := M) σ hy
  have hφ_contdiff_one :
      ContMDiffWithinAt 𝓘(ℝ, Fin m → ℝ) I (1 : WithTop ℕ∞) φ D y :=
    hφ_contdiff.of_le hcell
  have hψ_contdiff :
      ContMDiffWithinAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, E) (1 : WithTop ℕ∞) ψ D y := by
    have htarget_form :=
      (contMDiffWithinAt_iff_target_of_mem_source
        (I := 𝓘(ℝ, Fin m → ℝ)) (I' := I) (n := (1 : WithTop ℕ∞))
        (f := φ) (s := D) (x := y) (y := φ x) hsource).1 hφ_contdiff_one
    simpa [ψ, φ, e] using htarget_form.2
  have hψ_diff :
      MDifferentiableWithinAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, E) ψ D y :=
    hψ_contdiff.mdifferentiableWithinAt one_ne_zero
  have hsymm_diff :
      MDifferentiableWithinAt 𝓘(ℝ, E) I (e.extend I).symm
        (e.extend I).target (ψ y) :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas
      (I := I) he (by simpa [e, ψ, φ] using htarget)
  have hpre_source : φ ⁻¹' e.source ∈ 𝓝[D] y := by
    exact hφ_contdiff_one.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_source.mem_nhds (by simpa [e, φ] using hsource))
  have hpre_target : ψ ⁻¹' (e.extend I).target ∈ 𝓝[D] y := by
    refine Filter.mem_of_superset hpre_source ?_
    intro z hz
    have hzsource_ext : φ z ∈ (e.extend I).source := by
      simpa [e.extend_source (I := I)] using hz
    change (e.extend I) (φ z) ∈ (e.extend I).target
    exact (e.extend I).map_source hzsource_ext
  have hcomp_deriv :
      mfderivWithin 𝓘(ℝ, Fin m → ℝ) I ((e.extend I).symm ∘ ψ) D y =
        (mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm
          (e.extend I).target (ψ y)).comp
          (mfderivWithin 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, E) ψ D y) :=
    mfderivWithin_comp_of_preimage_mem_nhdsWithin (x := y)
      (I := 𝓘(ℝ, Fin m → ℝ)) (I' := 𝓘(ℝ, E)) (I'' := I)
      (g := (e.extend I).symm) (f := ψ)
      (s := D) (u := (e.extend I).target) hsymm_diff hψ_diff
      hpre_target (((uniqueDiffOn_simplexCoordinateDomain m) y
        (by simpa [D] using hy)).uniqueMDiffWithinAt)
  have hevent :
      ((e.extend I).symm ∘ ψ) =ᶠ[𝓝[D] y] φ := by
    filter_upwards [hpre_source] with z hz
    have hzsource_ext : φ z ∈ (e.extend I).source := by
      simpa [e.extend_source (I := I)] using hz
    change (e.extend I).symm ((e.extend I) (φ z)) = φ z
    exact (e.extend I).left_inv hzsource_ext
  have hcomp_eq :
      mfderivWithin 𝓘(ℝ, Fin m → ℝ) I ((e.extend I).symm ∘ ψ) D y =
        mfderivWithin 𝓘(ℝ, Fin m → ℝ) I φ D y :=
    hevent.mfderivWithin_eq (by simpa [ψ, φ] using hleft)
  have hderiv :
      mfderivWithin 𝓘(ℝ, Fin m → ℝ) I φ D y =
        (mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm
          (e.extend I).target (ψ y)).comp
          (fderivWithin ℝ ψ D y) := by
    rw [← hcomp_eq, hcomp_deriv]
    simp [mfderivWithin_eq_fderivWithin]
    rfl
  change
    (form.toFun (φ y)).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, Fin m → ℝ) I φ D y) =
      ((form.toFun ((e.extend I).symm (ψ y))).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm
          (e.extend I).target (ψ y))).compContinuousLinearMap
        (fderivWithin ℝ ψ D y)
  rw [hleft, hderiv]
  rfl

/-- Near a simplex point, the pulled-back form is represented by pulling back the fixed-chart
coordinate expression around the image of that point. -/
theorem simplexPullbackFormAlongUsingExtension_eventuallyEq_coordinateExpression
    [IsManifold I ∞ M]
    {m k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) m r)
    {x : Fin m → ℝ} (hx : x ∈ simplexCoordinateDomain m) :
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
        (m := m) (k := k) form σ.extension
      =ᶠ[𝓝[simplexCoordinateDomain m] x]
      fun y : Fin m → ℝ =>
        (coordinateExpression (I := I) (F := F) (n := k) form.toFun
          (chartAt H (simplexParametrizationUsingExtension σ.extension x))
          ((extChartAt I (simplexParametrizationUsingExtension σ.extension x))
            (simplexParametrizationUsingExtension σ.extension y))).compContinuousLinearMap
          (fderivWithin ℝ
            (fun z : Fin m → ℝ =>
              (extChartAt I (simplexParametrizationUsingExtension σ.extension x))
                (simplexParametrizationUsingExtension σ.extension z))
            (simplexCoordinateDomain m) y) := by
  classical
  let D : Set (Fin m → ℝ) := simplexCoordinateDomain m
  let φ : (Fin m → ℝ) → M := simplexParametrizationUsingExtension σ.extension
  let e : OpenPartialHomeomorph M H := chartAt H (φ x)
  have hφ_contdiff :
      ContMDiffWithinAt 𝓘(ℝ, Fin m → ℝ) I (1 : WithTop ℕ∞) φ D x := by
    exact (ContMDiffSingularSimplex.contMDiffWithinAt_simplexParametrization
      (I := I) (M := M) σ (by simpa [D] using hx)).of_le hcell
  have hpre_source : φ ⁻¹' e.source ∈ 𝓝[D] x := by
    exact hφ_contdiff.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_source.mem_nhds (by simp [e, φ]))
  filter_upwards [self_mem_nhdsWithin, hpre_source] with y hyD hy_source
  exact
    simplexPullbackFormAlongUsingExtension_eq_coordinateExpression_of_mem_source
      (I := I) (F := F) (m := m) (k := k) hcell form σ
      (by simpa [D] using hyD)
      (by simpa [e, φ] using hy_source)

/-- The scalar coefficient of the pulled-back top-degree form in the standard orientation. -/
noncomputable def simplexPullbackCoefficientUsingExtension
    {k : ℕ}
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (G : SimplexAmbient k → M) (x : Fin k → ℝ) : F :=
  simplexPullbackFormUsingExtension (I := I) (F := F) form G x
    (fun i : Fin k ↦ Pi.single i (1 : ℝ))

/--
%%handwave
name:
  Pullback integrand on a simplex
statement:
  Pulling a degree \(k\) form back along a \(C^1\) singular \(k\)-simplex gives
  a top-degree form on the standard simplex, hence a scalar coefficient in the
  standard affine coordinates.
-/
noncomputable def simplexPullbackCoefficient
    {k : ℕ} {r : WithTop ℕ∞}
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) (x : Fin k → ℝ) : F :=
  simplexPullbackCoefficientUsingExtension (I := I) (F := F) form σ.extension x

/--
%%handwave
name:
  Integral over a simplex by pullback
statement:
  The integral of a degree \(k\) form over a \(C^1\) singular \(k\)-simplex is
  the Bochner integral of the scalar coefficient of the pulled-back form over
  the standard affine simplex.
-/
noncomputable def integrateSimplexByPullback
    {k : ℕ} {r : WithTop ℕ∞} (_hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) : F :=
  ((-1 : ℤ) ^ k) •
    ∫ x in simplexCoordinateDomain k,
      simplexPullbackCoefficient (I := I) (F := F) form σ x

/--
%%handwave
name:
  Pullback coefficients are independent of the ambient extension
statement:
  Let \(\sigma:\Delta^k\to M\) be a parameterized simplex, and let
  \(G,G':\mathbb R^{k+1}\to M\) be \(C^r\) extensions that agree with
  \(\sigma\) on \(\Delta^k\).  For every affine coordinate
  \(x\in\{x_i\geq0,\ \sum_i x_i\leq1\}\), the coefficients obtained by
  evaluating \(G^*\omega\) and \((G')^*\omega\) on the standard frame are
  equal.
proof:
  The two affine parameterizations agree on the coordinate simplex.  Their
  derivatives tangent to that simplex therefore agree at \(x\), so the two
  pullbacks have the same value and the same tangent arguments there.
-/
theorem simplexPullbackCoefficientUsingExtension_eq_of_eqOn
    {k : ℕ} {r : WithTop ℕ∞}
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    {G G' : SimplexAmbient k → M}
    (_hGdiff : ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r G
      (stdSimplex ℝ (Fin (k + 1))))
    (_hG'diff : ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r G'
      (stdSimplex ℝ (Fin (k + 1))))
    (hG : ∀ x : StandardSimplex k, G (x : SimplexAmbient k) = σ.toContinuousMap x)
    (hG' : ∀ x : StandardSimplex k, G' (x : SimplexAmbient k) = σ.toContinuousMap x)
    {x : Fin k → ℝ} (hx : x ∈ simplexCoordinateDomain k) :
    simplexPullbackCoefficientUsingExtension (I := I) (F := F) form G x =
      simplexPullbackCoefficientUsingExtension (I := I) (F := F) form G' x := by
  have hEq :
      EqOn (simplexParametrizationUsingExtension G)
        (simplexParametrizationUsingExtension G') (simplexCoordinateDomain k) := by
    intro z hz
    exact
      (hG ⟨simplexCoordinateMap k z, simplexCoordinateMap_mem_stdSimplex hz⟩).trans
        (hG' ⟨simplexCoordinateMap k z, simplexCoordinateMap_mem_stdSimplex hz⟩).symm
  have hpoint :
      simplexParametrizationUsingExtension G x =
        simplexParametrizationUsingExtension G' x :=
    hEq hx
  have hderiv :
      mfderivWithin 𝓘(ℝ, Fin k → ℝ) I
          (simplexParametrizationUsingExtension G) (simplexCoordinateDomain k) x =
        mfderivWithin 𝓘(ℝ, Fin k → ℝ) I
          (simplexParametrizationUsingExtension G') (simplexCoordinateDomain k) x :=
    mfderivWithin_congr hEq hpoint
  dsimp [simplexPullbackCoefficientUsingExtension, simplexPullbackFormUsingExtension]
  rw [← hpoint, ← hderiv]

/--
%%handwave
name:
  Simplex pullback integrals are independent of the ambient extension
statement:
  If two \(C^r\) ambient extensions \(G,G':\mathbb R^{k+1}\to M\) represent
  the same parameterized simplex \(\sigma:\Delta^k\to M\), then
  \[
    \int_{\Delta^k} G^*\omega=\int_{\Delta^k}(G')^*\omega
  \]
  when both pullbacks are written in the standard affine coordinates.
proof:
  [The two pullback coefficients agree at every point of the affine simplex](lean:JJMath.Manifold.simplexPullbackCoefficientUsingExtension_eq_of_eqOn), and equality of their Bochner integrals follows by pointwise congruence on that measurable domain.
-/
theorem integral_simplexPullbackCoefficientUsingExtension_eq_of_eqOn
    {k : ℕ} {r : WithTop ℕ∞}
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    {G G' : SimplexAmbient k → M}
    (hGdiff : ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r G
      (stdSimplex ℝ (Fin (k + 1))))
    (hG'diff : ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r G'
      (stdSimplex ℝ (Fin (k + 1))))
    (hG : ∀ x : StandardSimplex k, G (x : SimplexAmbient k) = σ.toContinuousMap x)
    (hG' : ∀ x : StandardSimplex k, G' (x : SimplexAmbient k) = σ.toContinuousMap x) :
    (∫ x in simplexCoordinateDomain k,
      simplexPullbackCoefficientUsingExtension (I := I) (F := F) form G x) =
    (∫ x in simplexCoordinateDomain k,
      simplexPullbackCoefficientUsingExtension (I := I) (F := F) form G' x) := by
  refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
  intro x hx
  exact simplexPullbackCoefficientUsingExtension_eq_of_eqOn
    (I := I) (F := F) form σ hGdiff hG'diff hG hG' hx

/-- The integral over a face may be computed using the ambient extension obtained
by composing the simplex extension with the affine face inclusion. -/
theorem integrateSimplexByPullback_face_eq_integral_usingExtension
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (i : Fin (k + 2)) :
    integrateSimplexByPullback (I := I) (F := F) hcell form
        (ContMDiffSingularSimplex.face (I := I) σ i) =
      ((-1 : ℤ) ^ k) •
        ∫ x in simplexCoordinateDomain k,
          simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
            (σ.extension ∘ simplexAmbientMap i.succAbove) x := by
  classical
  let τ : ContMDiffSingularSimplex (I := I) (M := M) k r :=
    ContMDiffSingularSimplex.face (I := I) σ i
  let Gface : SimplexAmbient k → M := σ.extension ∘ simplexAmbientMap i.succAbove
  have hGfaceDiff :
      ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r Gface
        (stdSimplex ℝ (Fin (k + 1))) := by
    exact σ.extension_contMDiffOn.comp
      (simplexAmbientMap i.succAbove).contMDiffOn fun x hx ↦ by
        change FunOnFinite.linearMap ℝ ℝ i.succAbove x ∈ stdSimplex ℝ (Fin (k + 2))
        exact stdSimplex.image_linearMap i.succAbove ⟨x, hx, rfl⟩
  have hGfaceEq : ∀ x : StandardSimplex k, Gface (x : SimplexAmbient k) = τ.toContinuousMap x := by
    intro x
    simpa [τ, Gface, simplexAmbientMap, simplexFaceMap] using
      σ.extension_eq (simplexFaceMap i x)
  have hchosen :
      (∫ x in simplexCoordinateDomain k,
        simplexPullbackCoefficientUsingExtension (I := I) (F := F) form τ.extension x) =
      (∫ x in simplexCoordinateDomain k,
        simplexPullbackCoefficientUsingExtension (I := I) (F := F) form Gface x) :=
    integral_simplexPullbackCoefficientUsingExtension_eq_of_eqOn
      (I := I) (F := F) form τ τ.extension_contMDiffOn hGfaceDiff
      τ.extension_eq hGfaceEq
  calc
    integrateSimplexByPullback (I := I) (F := F) hcell form
        (ContMDiffSingularSimplex.face (I := I) σ i)
        = ((-1 : ℤ) ^ k) •
            ∫ x in simplexCoordinateDomain k,
              simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
                τ.extension x := by
          simp [integrateSimplexByPullback, simplexPullbackCoefficient, τ]
    _ = ((-1 : ℤ) ^ k) •
        ∫ x in simplexCoordinateDomain k,
          simplexPullbackCoefficientUsingExtension (I := I) (F := F) form Gface x := by
          rw [hchosen]
    _ = ((-1 : ℤ) ^ k) •
        ∫ x in simplexCoordinateDomain k,
          simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
            (σ.extension ∘ simplexAmbientMap i.succAbove) x := by
          rfl

/-- Pointwise, the coefficient of the pullback to a face is obtained by
pulling the ambient simplex pullback form along the affine face-coordinate map. -/
theorem simplexPullbackCoefficientUsingExtension_comp_face_eq_pullbackAlong
    [IsManifold I 1 M]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (i : Fin (k + 2)) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
        (σ.extension ∘ simplexAmbientMap i.succAbove) x =
      simplexPullbackFormAlongUsingExtension (I := I) (F := F)
        (m := k + 1) (k := k) form σ.extension
        (simplexFaceCoordinateMap i x)
        (fun j : Fin k =>
          simplexFaceCoordinateLinearMap i (Pi.single j (1 : ℝ))) := by
  classical
  let Dk : Set (Fin k → ℝ) := simplexCoordinateDomain k
  let Dn : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
  let q : (Fin k → ℝ) → (Fin (k + 1) → ℝ) :=
    simplexFaceCoordinateMap i
  let L : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
    simplexFaceCoordinateLinearMap i
  let φ : (Fin (k + 1) → ℝ) → M :=
    simplexParametrizationUsingExtension σ.extension
  let φface : (Fin k → ℝ) → M :=
    simplexParametrizationUsingExtension (σ.extension ∘ simplexAmbientMap i.succAbove)
  let base : Fin k → (Fin k → ℝ) := fun j ↦ Pi.single j (1 : ℝ)
  have hEqParam : EqOn φface (φ ∘ q) Dk := by
    intro y hy
    simp [φface, φ, q, simplexParametrizationUsingExtension,
      simplexCoordinateMap_simplexFaceCoordinateMap i (by simpa [Dk] using hy)]
  have hparam_x : φface x = φ (q x) := hEqParam (by simpa [Dk] using hx)
  have hderiv_congr :
      mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φface Dk x =
        mfderivWithin 𝓘(ℝ, Fin k → ℝ) I (φ ∘ q) Dk x :=
    mfderivWithin_congr hEqParam hparam_x
  have hr_ne : r ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (zero_lt_one : (0 : WithTop ℕ∞) < 1) hcell)
  have hφ_contdiff :
      ContMDiffOn 𝓘(ℝ, Fin (k + 1) → ℝ) I r φ Dn := by
    simpa [φ, Dn] using
      contMDiffOn_simplexParametrizationUsingExtension (I := I)
        σ.extension_contMDiffOn
  have hφ_mdifferentiable :
      MDifferentiableWithinAt 𝓘(ℝ, Fin (k + 1) → ℝ) I φ Dn (q x) :=
    (hφ_contdiff.mdifferentiableOn hr_ne) (q x)
      (by simpa [Dn, q] using simplexFaceCoordinateMap_mem i hx)
  have hq_mdifferentiable :
      MDifferentiableWithinAt 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin (k + 1) → ℝ) q Dk x := by
    exact
      (hasFDerivWithinAt_simplexFaceCoordinateMap i (by simpa [Dk] using hx)).differentiableWithinAt
        |>.mdifferentiableWithinAt
  have hmaps : Dk ⊆ q ⁻¹' Dn := by
    intro y hy
    simpa [Dn, q] using simplexFaceCoordinateMap_mem i (by simpa [Dk] using hy)
  have hchain :
      mfderivWithin 𝓘(ℝ, Fin k → ℝ) I (φ ∘ q) Dk x =
        (mfderivWithin 𝓘(ℝ, Fin (k + 1) → ℝ) I φ Dn (q x)).comp
          (mfderivWithin 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin (k + 1) → ℝ) q Dk x) := by
    exact mfderivWithin_comp (x := x) hφ_mdifferentiable hq_mdifferentiable hmaps
      (((uniqueDiffOn_simplexCoordinateDomain k) x
        (by simpa [Dk] using hx)).uniqueMDiffWithinAt)
  have hqmf :
      mfderivWithin 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin (k + 1) → ℝ) q Dk x = L := by
    simpa [Dk, q, L] using
      fderivWithin_simplexFaceCoordinateMap i (by simpa [Dk] using hx)
  dsimp [simplexPullbackCoefficientUsingExtension, simplexPullbackFormUsingExtension,
    simplexPullbackFormAlongUsingExtension]
  change
    (form.toFun (φface x)).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φface Dk x) base =
      (form.toFun (φ (q x))).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, Fin (k + 1) → ℝ) I φ Dn (q x))
        (fun j : Fin k => L (Pi.single j (1 : ℝ)))
  rw [hparam_x, hderiv_congr, hchain, hqmf]
  rfl

/-- The integral over a face may be written as the ambient pulled-back form
evaluated on the affine face-coordinate tangent vectors. -/
theorem integrateSimplexByPullback_face_eq_integral_pullbackAlong
    [IsManifold I 1 M]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (i : Fin (k + 2)) :
    integrateSimplexByPullback (I := I) (F := F) hcell form
        (ContMDiffSingularSimplex.face (I := I) σ i) =
      ((-1 : ℤ) ^ k) •
        ∫ x in simplexCoordinateDomain k,
          simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k) form σ.extension
            (simplexFaceCoordinateMap i x)
            (fun j : Fin k =>
              simplexFaceCoordinateLinearMap i (Pi.single j (1 : ℝ))) := by
  classical
  rw [integrateSimplexByPullback_face_eq_integral_usingExtension
    (I := I) (F := F) hcell form σ i]
  congr 1
  refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
  intro x hx
  exact simplexPullbackCoefficientUsingExtension_comp_face_eq_pullbackAlong
    (I := I) (F := F) hcell form σ i hx

/-- The lower endpoint obtained by setting affine coordinate `i` to zero is
the coefficient of the face omitting that coordinate. -/
theorem simplexPullbackFormAlongUsingExtension_insert_zero_eq_faceCoefficient
    [IsManifold I 1 M]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (i : Fin (k + 1)) {x : Fin k → ℝ}
    (hx : x ∈ simplexCoordinateDomain k) :
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
        (m := k + 1) (k := k) form σ.extension
        (simplexCoordinateInsertMap i x 0)
        (i.removeNth fun j : Fin (k + 1) ↦
          (Pi.single j (1 : ℝ) : Fin (k + 1) → ℝ)) =
      simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
        (σ.extension ∘ simplexAmbientMap i.castSucc.succAbove) x := by
  classical
  have hface :=
    simplexPullbackCoefficientUsingExtension_comp_face_eq_pullbackAlong
      (I := I) (F := F) hcell form σ i.castSucc hx
  rw [hface]
  congr 2
  · exact (simplexFaceCoordinateMap_castSucc_eq_insert_zero i x).symm
  · funext j
    simp [Fin.removeNth_apply, simplexFaceCoordinateLinearMap_castSucc_basis]

/-- The integral over a non-final coordinate face is the integral of the
corresponding lower-endpoint coefficient in the ambient pulled-back form. -/
theorem integrateSimplexByPullback_castSucc_face_eq_insert_zero_integral
    [IsManifold I 1 M]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (i : Fin (k + 1)) :
    integrateSimplexByPullback (I := I) (F := F) hcell form
        (ContMDiffSingularSimplex.face (I := I) σ i.castSucc) =
      ((-1 : ℤ) ^ k) •
        ∫ x in simplexCoordinateDomain k,
          simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k) form σ.extension
            (simplexCoordinateInsertMap i x 0)
            (i.removeNth fun j : Fin (k + 1) ↦
              (Pi.single j (1 : ℝ) : Fin (k + 1) → ℝ)) := by
  classical
  rw [integrateSimplexByPullback_face_eq_integral_pullbackAlong
    (I := I) (F := F) hcell form σ i.castSucc]
  congr 1
  refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
  intro x hx
  change
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
        (m := k + 1) (k := k) form σ.extension
        (simplexFaceCoordinateMap i.castSucc x)
        (fun j : Fin k =>
          simplexFaceCoordinateLinearMap i.castSucc (Pi.single j (1 : ℝ))) =
      simplexPullbackFormAlongUsingExtension (I := I) (F := F)
        (m := k + 1) (k := k) form σ.extension
        (simplexCoordinateInsertMap i x 0)
        (i.removeNth fun j : Fin (k + 1) ↦
          (Pi.single j (1 : ℝ) : Fin (k + 1) → ℝ))
  rw [← simplexPullbackCoefficientUsingExtension_comp_face_eq_pullbackAlong
    (I := I) (F := F) hcell form σ i.castSucc hx]
  exact
    (simplexPullbackFormAlongUsingExtension_insert_zero_eq_faceCoefficient
      (I := I) (F := F) hcell form σ i hx).symm

/-- The final face integral is the upper endpoint of the last-coordinate
slicing, evaluated on the final-face tangent basis `e_j - e_last`. -/
theorem integrateSimplexByPullback_last_face_eq_slice_upper_integral
    [IsManifold I 1 M]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
    integrateSimplexByPullback (I := I) (F := F) hcell form
        (ContMDiffSingularSimplex.face (I := I) σ (Fin.last (k + 1))) =
      ((-1 : ℤ) ^ k) •
        ∫ x in simplexCoordinateDomain k,
          simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k) form σ.extension
            (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i))
            (fun j : Fin k =>
              Pi.single j.castSucc (1 : ℝ) - Pi.single (Fin.last k) (1 : ℝ)) := by
  classical
  rw [integrateSimplexByPullback_face_eq_integral_pullbackAlong
    (I := I) (F := F) hcell form σ (Fin.last (k + 1))]
  congr 1
  refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
  intro x hx
  simp [simplexFaceCoordinateLinearMap_last_basis]

/--
%%handwave
name:
  Continuity of a simplex pullback coefficient
statement:
  If \(\sigma:\Delta^k\to M\) is \(C^r\) with \(r\geq1\) and \(\omega\) is
  a continuous \(k\)-form, then the coefficient of \(\sigma^*\omega\) in the
  standard affine frame is continuous on
  \(\{x_i\geq0,\ \sum_i x_i\leq1\}\).
proof:
  The affine parameterization is \(C^1\), hence its derivative varies
  continuously on the simplex.  Evaluating the continuous coefficient field
  of \(\omega\) on these continuously varying tangent vectors is continuous.
-/
theorem continuousOn_simplexPullbackCoefficient
    [IsManifold I 1 M]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) :
    ContinuousOn (simplexPullbackCoefficient (I := I) (F := F) form σ)
      (simplexCoordinateDomain k) := by
  simpa [simplexPullbackCoefficient, simplexPullbackCoefficientUsingExtension,
    simplexPullbackFormUsingExtension] using
    DifferentialForm.continuousOn_eval_comp_mfderivWithin
      (I := I) (F := F) (n := k) (rφ := r)
      form σ.contMDiffOn_simplexParametrization hcell
      (uniqueDiffOn_simplexCoordinateDomain k)
      (fun i : Fin k ↦ Pi.single i (1 : ℝ))

/--
%%handwave
name:
  Integrability of a simplex pullback coefficient
statement:
  If the coefficient space is complete, the coefficient of the pullback of a
  continuous \(k\)-form along a \(C^1\) parameterized \(k\)-simplex is
  Bochner integrable over the standard affine simplex.
proof:
  [The pullback coefficient is continuous on the affine simplex](lean:JJMath.Manifold.continuousOn_simplexPullbackCoefficient), and that simplex is compact, so the coefficient is integrable there.
-/
theorem integrableOn_simplexPullbackCoefficient
    [IsManifold I 1 M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) :
    IntegrableOn (simplexPullbackCoefficient (I := I) (F := F) form σ)
      (simplexCoordinateDomain k) := by
  exact (continuousOn_simplexPullbackCoefficient
    (I := I) (F := F) hcell form σ).integrableOn_compact
      (isCompact_simplexCoordinateDomain k)

/-- The pulled-back form along an `m`-simplex, evaluated on fixed tangent
vectors in affine coordinates, is continuous on the affine simplex. -/
theorem continuousOn_simplexPullbackFormAlongUsingExtension_eval
    [IsManifold I 1 M]
    {m k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) m r)
    (v : Fin k → (Fin m → ℝ)) :
    ContinuousOn
      (fun x : Fin m → ℝ =>
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := m) (k := k) form σ.extension x v)
      (simplexCoordinateDomain m) := by
  simpa [simplexPullbackFormAlongUsingExtension] using
    DifferentialForm.continuousOn_eval_comp_mfderivWithin
      (I := I) (F := F) (n := k) (rφ := r)
      form σ.contMDiffOn_simplexParametrization hcell
      (uniqueDiffOn_simplexCoordinateDomain m) v

/-- The pulled-back form along an `m`-simplex, evaluated on fixed tangent
vectors in affine coordinates, is integrable on the affine simplex. -/
theorem integrableOn_simplexPullbackFormAlongUsingExtension_eval
    [IsManifold I 1 M] [CompleteSpace F]
    {m k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) m r)
    (v : Fin k → (Fin m → ℝ)) :
    IntegrableOn
      (fun x : Fin m → ℝ =>
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := m) (k := k) form σ.extension x v)
      (simplexCoordinateDomain m) := by
  exact (continuousOn_simplexPullbackFormAlongUsingExtension_eval
    (I := I) (F := F) hcell form σ v).integrableOn_compact
      (isCompact_simplexCoordinateDomain m)

/--
The analytic change-of-variables statement for a pulled-back top-degree form
under the affine coordinate self-map induced by a permutation of the vertices.

This is the remaining measure-theoretic and linear-algebraic core: the chain
rule for the pullback form, the determinant/sign calculation for the affine
self-map of the coordinate simplex, and Bochner change of variables on that
compact simplex.
-/
theorem integral_simplexPullbackCoefficientUsingExtension_comp_vertexPermutation
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    {G : SimplexAmbient k → M}
    (hGdiff : ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r G
      (stdSimplex ℝ (Fin (k + 1))))
    (p : Equiv.Perm (Fin (k + 1))) :
    (∫ x in simplexCoordinateDomain k,
      simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
        (G ∘ simplexAmbientMap p) x) =
      (((Equiv.Perm.sign p : ℤˣ) : ℤ) •
        ∫ x in simplexCoordinateDomain k,
          simplexPullbackCoefficientUsingExtension (I := I) (F := F) form G x) := by
  classical
  let D : Set (Fin k → ℝ) := simplexCoordinateDomain k
  let q : (Fin k → ℝ) → (Fin k → ℝ) :=
    simplexCoordinateVertexPermutationMap p
  let L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    simplexCoordinateVertexPermutationLinearMap p
  let g : (Fin k → ℝ) → F :=
    fun x ↦ simplexPullbackCoefficientUsingExtension (I := I) (F := F) form G x
  have hdetL :
      LinearMap.det (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) =
        ((Equiv.Perm.sign p : ℤˣ) : ℝ) := by
    simpa [L] using simplexCoordinateVertexPermutationLinearMap_det p
  have habsL :
      |LinearMap.det (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))| = (1 : ℝ) := by
    rw [hdetL]
    exact abs_intUnit_cast_real (Equiv.Perm.sign p)
  have hcov :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (s := D) (f := q) (f' := fun _ ↦ L) (g := g)
      (by simpa [D] using measurableSet_simplexCoordinateDomain k)
      (fun x hx ↦ by
        simpa [D, q, L] using
          hasFDerivWithinAt_simplexCoordinateVertexPermutationMap p hx)
      (by simpa [D, q] using simplexCoordinateVertexPermutationMap_injOn p)
  have hintegral_reparam :
      (∫ x in D, g x) = ∫ x in D, g (q x) := by
    rw [show q '' D = D by
      simpa [D, q] using simplexCoordinateVertexPermutationMap_image_domain p] at hcov
    simpa [habsL] using hcov
  have hr_ne : r ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (zero_lt_one : (0 : WithTop ℕ∞) < 1) hcell)
  have hpoint :
      ∀ x ∈ D,
        simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
            (G ∘ simplexAmbientMap p) x =
          (((Equiv.Perm.sign p : ℤˣ) : ℤ) • g (q x)) := by
    intro x hx
    let φ : (Fin k → ℝ) → M := simplexParametrizationUsingExtension G
    let φp : (Fin k → ℝ) → M :=
      simplexParametrizationUsingExtension (G ∘ simplexAmbientMap p)
    let base : Fin k → (Fin k → ℝ) := fun i ↦ Pi.single i (1 : ℝ)
    have hEqParam : EqOn φp (φ ∘ q) D := by
      intro y hy
      simp [φp, φ, q, simplexParametrizationUsingExtension,
        simplexAmbientMap, simplexCoordinateMap_vertexPermutation p hy]
    have hparam_x : φp x = φ (q x) := hEqParam hx
    have hderiv_congr :
        mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φp D x =
          mfderivWithin 𝓘(ℝ, Fin k → ℝ) I (φ ∘ q) D x :=
      mfderivWithin_congr hEqParam hparam_x
    have hGparam :
        ContMDiffOn 𝓘(ℝ, Fin k → ℝ) I r φ D :=
      contMDiffOn_simplexParametrizationUsingExtension (I := I) hGdiff
    have hGmdiff :
        MDifferentiableWithinAt 𝓘(ℝ, Fin k → ℝ) I φ D (q x) :=
      (hGparam.mdifferentiableOn hr_ne) (q x)
        (by simpa [D, q] using simplexCoordinateVertexPermutationMap_mem p hx)
    have hqmdiff :
        MDifferentiableWithinAt 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin k → ℝ) q D x := by
      have hdiff : Differentiable ℝ q := by
        simpa [q] using
          (contDiff_simplexCoordinateVertexPermutationMap
            (r := (1 : WithTop ℕ∞)) p).differentiable one_ne_zero
      exact (hdiff x).differentiableWithinAt.mdifferentiableWithinAt
    have hmaps : D ⊆ q ⁻¹' D := by
      intro y hy
      simpa [D, q] using simplexCoordinateVertexPermutationMap_mem p hy
    have hchain :
        mfderivWithin 𝓘(ℝ, Fin k → ℝ) I (φ ∘ q) D x =
          (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φ D (q x)).comp
            (mfderivWithin 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin k → ℝ) q D x) := by
      exact mfderivWithin_comp (x := x) hGmdiff hqmdiff hmaps
        (((uniqueDiffOn_simplexCoordinateDomain k) x (by simpa [D] using hx)).uniqueMDiffWithinAt)
    have hqmf :
        mfderivWithin 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin k → ℝ) q D x = L := by
      simpa [D, q, L] using
        fderivWithin_simplexCoordinateVertexPermutationMap p (by simpa [D] using hx)
    have htop :=
      continuousAlternatingMap_compContinuousLinearMap_apply_basisFun_det
        (F := F)
        ((form.toFun (φ (q x))).compContinuousLinearMap
          (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φ D (q x)))
        L
    dsimp [simplexPullbackCoefficientUsingExtension, simplexPullbackFormUsingExtension, g]
    change
      (form.toFun (φp x)).compContinuousLinearMap
          (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φp D x) base =
        (((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          ((form.toFun (φ (q x))).compContinuousLinearMap
            (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φ D (q x)) base))
    rw [hparam_x, hderiv_congr, hchain, hqmf]
    calc
      (form.toFun (φ (q x))).compContinuousLinearMap
          ((mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φ D (q x)).comp L) base =
          (((form.toFun (φ (q x))).compContinuousLinearMap
              (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φ D (q x))).compContinuousLinearMap L) base := by
            rfl
      _ = LinearMap.det (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) •
            ((form.toFun (φ (q x))).compContinuousLinearMap
              (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φ D (q x)) base) := htop
      _ = ((Equiv.Perm.sign p : ℤˣ) : ℝ) •
            ((form.toFun (φ (q x))).compContinuousLinearMap
              (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φ D (q x)) base) := by
            rw [hdetL]
      _ = (((Equiv.Perm.sign p : ℤˣ) : ℤ) •
            ((form.toFun (φ (q x))).compContinuousLinearMap
              (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I φ D (q x)) base)) := by
            exact intUnit_real_smul_eq_int_smul (F := F) (Equiv.Perm.sign p) _
  have hcongr :
      (∫ x in D,
        simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
          (G ∘ simplexAmbientMap p) x) =
        ∫ x in D, (((Equiv.Perm.sign p : ℤˣ) : ℤ) • g (q x)) := by
    refine setIntegral_congr_fun (by simpa [D] using measurableSet_simplexCoordinateDomain k) ?_
    intro x hx
    exact hpoint x hx
  rw [show simplexCoordinateDomain k = D by rfl]
  rw [hcongr]
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hsign | hsign
  · simp [g, D, q, hsign, hintegral_reparam]
  · simp [g, D, q, hsign, hintegral_reparam, integral_neg]

/--
%%handwave
name:
  Change of variables for a pulled-back simplex integral
statement:
  Permuting the vertices of the standard simplex changes the pulled-back
  integral by the sign of the permutation.
proof:
  Represent the reparameterized simplex by composing an ambient extension
  with the affine vertex permutation.  Independence of the chosen extension
  reduces the claim to the affine change-of-variables formula, whose
  determinant is the sign of the permutation.
-/
theorem integrateSimplexByPullback_reparametrizeVertexPermutation
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (p : Equiv.Perm (Fin (k + 1))) :
    integrateSimplexByPullback (I := I) (F := F) hcell form
        (σ.reparametrizeVertexPermutation p) =
      (((Equiv.Perm.sign p : ℤˣ) : ℤ) •
        integrateSimplexByPullback (I := I) (F := F) hcell form σ) := by
  let τ : ContMDiffSingularSimplex (I := I) (M := M) k r :=
    σ.reparametrizeVertexPermutation p
  let Gp : SimplexAmbient k → M := σ.extension ∘ simplexAmbientMap p
  have hGpDiff :
      ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I r Gp
        (stdSimplex ℝ (Fin (k + 1))) := by
    exact σ.extension_contMDiffOn.comp (simplexAmbientMap p).contMDiffOn fun x hx ↦ by
      change FunOnFinite.linearMap ℝ ℝ p x ∈ stdSimplex ℝ (Fin (k + 1))
      exact stdSimplex.image_linearMap p ⟨x, hx, rfl⟩
  have hGpEq : ∀ x : StandardSimplex k, Gp (x : SimplexAmbient k) = τ.toContinuousMap x := by
    intro x
    simpa [τ, Gp, simplexAmbientMap, simplexVertexPermutationMap] using
      σ.extension_eq (simplexVertexPermutationMap p x)
  have hchosen :
      (∫ x in simplexCoordinateDomain k,
        simplexPullbackCoefficientUsingExtension (I := I) (F := F) form τ.extension x) =
      (∫ x in simplexCoordinateDomain k,
        simplexPullbackCoefficientUsingExtension (I := I) (F := F) form Gp x) :=
    integral_simplexPullbackCoefficientUsingExtension_eq_of_eqOn
      (I := I) (F := F) form τ τ.extension_contMDiffOn hGpDiff
      τ.extension_eq hGpEq
  calc
    integrateSimplexByPullback (I := I) (F := F) hcell form
        (σ.reparametrizeVertexPermutation p)
        = ((-1 : ℤ) ^ k) •
            (∫ x in simplexCoordinateDomain k,
            simplexPullbackCoefficientUsingExtension (I := I) (F := F) form
              τ.extension x) := by
          simp [integrateSimplexByPullback, simplexPullbackCoefficient, τ]
    _ = ((-1 : ℤ) ^ k) •
          (∫ x in simplexCoordinateDomain k,
            simplexPullbackCoefficientUsingExtension (I := I) (F := F) form Gp x) := by
          rw [hchosen]
    _ = ((-1 : ℤ) ^ k) • (((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          ∫ x in simplexCoordinateDomain k,
            simplexPullbackCoefficientUsingExtension (I := I) (F := F) form σ.extension x) := by
          simpa [Gp] using
            congrArg (fun y : F => ((-1 : ℤ) ^ k) • y)
              (integral_simplexPullbackCoefficientUsingExtension_comp_vertexPermutation
              (I := I) (F := F) hcell form σ.extension_contMDiffOn p
              )
    _ = (((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          (((-1 : ℤ) ^ k) •
            ∫ x in simplexCoordinateDomain k,
              simplexPullbackCoefficientUsingExtension (I := I) (F := F) form σ.extension x)) := by
          rw [smul_smul, smul_smul, mul_comm]
    _ = (((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          integrateSimplexByPullback (I := I) (F := F) hcell form σ) := by
          simp [integrateSimplexByPullback, simplexPullbackCoefficient]

/-- A pulled-back exterior derivative, written in the target chart at the point. -/
theorem simplexPullbackCoefficient_exteriorDerivative_eq_coordinateExpression
    [IsManifold I ∞ M]
    {k : ℕ} {r : WithTop ℕ∞}
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (x : Fin (k + 1) → ℝ) :
    simplexPullbackCoefficient (I := I) (F := F)
        (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ x =
      ((extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := k) omega.toFun
            (chartAt H (simplexParametrizationUsingExtension σ.extension x)))
          (extChartAt I (simplexParametrizationUsingExtension σ.extension x)).target
          ((extChartAt I (simplexParametrizationUsingExtension σ.extension x))
            (simplexParametrizationUsingExtension σ.extension x))).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, Fin (k + 1) → ℝ) I
          (simplexParametrizationUsingExtension σ.extension)
          (simplexCoordinateDomain (k + 1)) x))
        (fun j : Fin (k + 1) ↦ Pi.single j (1 : ℝ)) := by
  let φ : (Fin (k + 1) → ℝ) → M :=
    simplexParametrizationUsingExtension σ.extension
  let e : OpenPartialHomeomorph M H := chartAt H (φ x)
  have he : e ∈ atlas H M := by
    simp [e]
  have hy : (extChartAt I (φ x)) (φ x) ∈ (e.extend I).target := by
    simp [e]
  have hcoord :=
    coordinateExpression_exteriorDerivativePoint (I := I) (F := F)
      (n := k) (r := (0 : WithTop ℕ∞)) omega he hy
  have hcoord' :
      coordinateExpression (I := I) (F := F) (n := k + 1)
          (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega).toFun e
          ((extChartAt I (φ x)) (φ x)) =
        extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := k) omega.toFun e)
          (e.extend I).target ((extChartAt I (φ x)) (φ x)) := by
    simpa [exteriorDerivative] using hcoord
  have hself :
      coordinateExpression (I := I) (F := F) (n := k + 1)
          (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega).toFun e
          ((extChartAt I (φ x)) (φ x)) =
        (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega).toFun (φ x) := by
    simpa [e, φ] using
      coordinateExpression_chartAt_self (I := I) (F := F) (n := k + 1)
        (form := (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega).toFun)
        (x := φ x)
  dsimp [simplexPullbackCoefficient, simplexPullbackCoefficientUsingExtension,
    simplexPullbackFormUsingExtension, φ]
  rw [← hself]
  rw [hcoord']
  simp [e, φ]
  rfl

/--
The model-space exterior derivative of the pulled-back form agrees pointwise with the
chart-coordinate pullback of the model-space exterior derivative.

This is the local form of the statement that exterior derivative commutes with pullback.
-/
theorem extDerivWithin_simplexPullbackFormAlong_eq_coordinateExpression
    [IsManifold I ∞ M]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
    EqOn
      (fun x : Fin (k + 1) → ℝ =>
        extDerivWithin
          (simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            σ.extension)
          (simplexCoordinateDomain (k + 1)) x
          (fun j : Fin (k + 1) ↦ Pi.single j (1 : ℝ)))
      (fun x : Fin (k + 1) → ℝ =>
        ((extDerivWithin
            (coordinateExpression (I := I) (F := F) (n := k) omega.toFun
              (chartAt H (simplexParametrizationUsingExtension σ.extension x)))
            (extChartAt I (simplexParametrizationUsingExtension σ.extension x)).target
            ((extChartAt I (simplexParametrizationUsingExtension σ.extension x))
              (simplexParametrizationUsingExtension σ.extension x))).compContinuousLinearMap
          (mfderivWithin 𝓘(ℝ, Fin (k + 1) → ℝ) I
            (simplexParametrizationUsingExtension σ.extension)
            (simplexCoordinateDomain (k + 1)) x))
          (fun j : Fin (k + 1) ↦ Pi.single j (1 : ℝ)))
      (simplexCoordinateDomain (k + 1)) := by
  intro x hx
  classical
  let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
  let φ : (Fin (k + 1) → ℝ) → M :=
    simplexParametrizationUsingExtension σ.extension
  let e : OpenPartialHomeomorph M H := chartAt H (φ x)
  let ψ : (Fin (k + 1) → ℝ) → E := fun y ↦ (extChartAt I (φ x)) (φ y)
  let η : E → (E [⋀^Fin k]→L[ℝ] F) :=
    coordinateExpression (I := I) (F := F) (n := k) omega.toFun e
  let form0 : ContinuousDifferentialForm (I := I) (M := M) (F := F) k :=
    DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega
  let pulled : (Fin (k + 1) → ℝ) →
      (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := k + 1) (k := k) form0 σ.extension
  let localPullback : (Fin (k + 1) → ℝ) →
      (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    fun y ↦ (η (ψ y)).compContinuousLinearMap (fderivWithin ℝ ψ D y)
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  have hcell_one : (1 : WithTop ℕ∞) ≤ r :=
    one_le_of_two_le_smoothness hcell
  have he : e ∈ atlas H M := by
    simp [e]
  have hφ_contdiff :
      ContMDiffWithinAt 𝓘(ℝ, Fin (k + 1) → ℝ) I r φ D x := by
    simpa [D, φ] using
      ContMDiffSingularSimplex.contMDiffWithinAt_simplexParametrization
        (I := I) (M := M) σ (by simpa [D] using hx)
  have hφ_contdiff_two :
      ContMDiffWithinAt 𝓘(ℝ, Fin (k + 1) → ℝ) I (2 : WithTop ℕ∞) φ D x :=
    hφ_contdiff.of_le hcell
  have hψ_contdiff_mfld :
      ContMDiffWithinAt 𝓘(ℝ, Fin (k + 1) → ℝ) 𝓘(ℝ, E)
        (2 : WithTop ℕ∞) ψ D x := by
    have htarget_form :=
      (contMDiffWithinAt_iff_target_of_mem_source
        (I := 𝓘(ℝ, Fin (k + 1) → ℝ)) (I' := I) (n := (2 : WithTop ℕ∞))
        (f := φ) (s := D) (x := x) (y := φ x) (by simp [φ])).1 hφ_contdiff_two
    simpa [ψ, φ, e] using htarget_form.2
  have hψ_contdiff :
      ContDiffWithinAt ℝ (2 : WithTop ℕ∞) ψ D x :=
    hψ_contdiff_mfld.contDiffWithinAt
  have hψ_maps : MapsTo ψ D (range I) := by
    intro y hy
    change (extChartAt I (φ x)) (φ y) ∈ range I
    simp [extChartAt]
  have hψx_target : ψ x ∈ (e.extend I).target := by
    simp [ψ, e, φ]
  have hηdiff_target :
      DifferentiableWithinAt ℝ η (e.extend I).target (ψ x) := by
    exact ((omega.isContMDiff e he (ψ x) hψx_target).differentiableWithinAt one_ne_zero)
  have htarget_mem : (e.extend I).target ∈ 𝓝[range I] (ψ x) := by
    simpa [e, ψ, φ] using
      extChartAt_target_mem_nhdsWithin (I := I) (x := φ x)
  have hηdiff_range : DifferentiableWithinAt ℝ η (range I) (ψ x) :=
    hηdiff_target.mono_of_mem_nhdsWithin htarget_mem
  have hmin : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞) := by
    simp
  have hclosure : x ∈ closure (interior D) := by
    exact simplexCoordinateDomain_subset_closure_interior (k + 1) (by simpa [D] using hx)
  have hpullback :
      extDerivWithin localPullback D x =
        (extDerivWithin η (range I) (ψ x)).compContinuousLinearMap
          (fderivWithin ℝ ψ D x) := by
    simpa [localPullback] using
      extDerivWithin_pullback (x := x) (f := ψ)
        (s := D) (t := range I) hηdiff_range hψ_contdiff hmin
        (uniqueDiffOn_simplexCoordinateDomain (k + 1))
        hclosure (by simpa [D] using hx) hψ_maps
  have hηderiv_set :
      fderivWithin ℝ η (range I) (ψ x) =
        fderivWithin ℝ η (e.extend I).target (ψ x) :=
    fderivWithin_of_mem_nhdsWithin htarget_mem
      (I.uniqueDiffOn (ψ x) (hψ_maps (by simpa [D] using hx))) hηdiff_target
  have hset :
      extDerivWithin η (range I) (ψ x) =
        extDerivWithin η (e.extend I).target (ψ x) := by
    rw [extDerivWithin, extDerivWithin, hηderiv_set]
  have hevent : pulled =ᶠ[𝓝[D] x] localPullback := by
    simpa [pulled, localPullback, form0, η, ψ, e, φ, D] using
      simplexPullbackFormAlongUsingExtension_eventuallyEq_coordinateExpression
        (I := I) (F := F) (m := k + 1) (k := k)
        hcell_one form0 σ (by simpa [D] using hx)
  have hleft :
      extDerivWithin pulled D x = extDerivWithin localPullback D x :=
    hevent.extDerivWithin_eq_of_mem (by simpa [D] using hx)
  have hr_ne : r ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (zero_lt_one : (0 : WithTop ℕ∞) < 1) hcell_one)
  have hmf :
      mfderivWithin 𝓘(ℝ, Fin (k + 1) → ℝ) I φ D x =
        fderivWithin ℝ ψ D x := by
    simpa [D, φ, ψ] using
      mfderivWithin_simplexParametrization_eq_fderivWithin_extChartAt
        (I := I) (M := M) σ hr_ne (by simpa [D] using hx)
  change extDerivWithin pulled D x base =
    ((extDerivWithin η (e.extend I).target (ψ x)).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, Fin (k + 1) → ℝ) I φ D x)) base
  rw [hleft, hpullback, hset, hmf]
  rfl

/--
The pullback of the exterior derivative to a singular simplex agrees with the exterior derivative
of the pulled-back form on the affine coordinate simplex.

This follows from the chartwise computation of the manifold exterior derivative and the local
pullback formula for the model-space exterior derivative.
-/
theorem simplexPullbackCoefficient_exteriorDerivative_eq_extDerivWithin_pullbackForm
    [IsManifold I ∞ M]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
    EqOn
      (fun x : Fin (k + 1) → ℝ =>
        simplexPullbackCoefficient (I := I) (F := F)
          (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ x)
      (fun x : Fin (k + 1) → ℝ =>
        extDerivWithin
          (simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            σ.extension)
          (simplexCoordinateDomain (k + 1)) x
          (fun j : Fin (k + 1) ↦ Pi.single j (1 : ℝ)))
      (simplexCoordinateDomain (k + 1)) := by
  intro x hx
  change
    simplexPullbackCoefficient (I := I) (F := F)
        (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ x =
      extDerivWithin
        (simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension)
        (simplexCoordinateDomain (k + 1)) x
        (fun j : Fin (k + 1) ↦ Pi.single j (1 : ℝ))
  rw [simplexPullbackCoefficient_exteriorDerivative_eq_coordinateExpression
    (I := I) (F := F) omega σ x]
  exact
    (extDerivWithin_simplexPullbackFormAlong_eq_coordinateExpression
      (I := I) (F := F) hcell omega σ hx).symm

/-- Fundamental theorem of calculus for a set integral over a closed interval. -/
theorem integral_Icc_eq_endpoint_sub_of_derivWithin
    [CompleteSpace F] {a b : ℝ} {f g : ℝ → F}
    (hcont : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b)
    (hg : EqOn g (fun t ↦ derivWithin f (Icc a b) t) (Icc a b)) :
    (∫ t in Icc a b, g t) = f b - f a := by
  calc
    (∫ t in Icc a b, g t)
        = ∫ t in Icc a b, derivWithin f (Icc a b) t := by
          exact setIntegral_congr_fun measurableSet_Icc hg
    _ = ∫ t in Ioc a b, derivWithin f (Icc a b) t := by
          exact integral_Icc_eq_integral_Ioc
    _ = ∫ t in a..b, derivWithin f (Icc a b) t := by
          exact (intervalIntegral.integral_of_le (μ := volume)
            (f := fun t ↦ derivWithin f (Icc a b) t) hab).symm
    _ = f b - f a :=
          intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hcont hab

/-- Fundamental theorem of calculus for a set integral over a closed interval,
where the displayed integrand is only required to agree with the within
derivative on the open interval.  The endpoints do not affect the Bochner
integral. -/
theorem integral_Icc_eq_endpoint_sub_of_eqOn_Ioo_derivWithin
    [CompleteSpace F] {a b : ℝ} {f g : ℝ → F}
    (hcont : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b)
    (hg : EqOn g (fun t ↦ derivWithin f (Icc a b) t) (Ioo a b)) :
    (∫ t in Icc a b, g t) = f b - f a := by
  calc
    (∫ t in Icc a b, g t)
        = ∫ t in Ioo a b, g t := by
          exact MeasureTheory.integral_Icc_eq_integral_Ioo
    _ = ∫ t in Ioo a b, derivWithin f (Icc a b) t := by
          exact setIntegral_congr_fun measurableSet_Ioo hg
    _ = ∫ t in Icc a b, derivWithin f (Icc a b) t := by
          exact MeasureTheory.integral_Icc_eq_integral_Ioo.symm
    _ = f b - f a :=
          integral_Icc_eq_endpoint_sub_of_derivWithin
            (F := F) hcont hab (fun _ _ => rfl)

/-- The standard affine basis on a sliced simplex, with the last coordinate
direction removed. -/
def simplexCoordinateSliceBasisWithoutLast (k : ℕ) :
    Fin k → (Fin (k + 1) → ℝ) :=
  (Fin.last k).removeNth
    (fun j : Fin (k + 1) =>
      (Pi.single j (1 : ℝ) : Fin (k + 1) → ℝ))

@[simp]
theorem simplexCoordinateSliceBasisWithoutLast_apply
    (k : ℕ) (i : Fin k) :
    simplexCoordinateSliceBasisWithoutLast k i =
      Pi.single i.castSucc (1 : ℝ) := by
  ext j
  simp [simplexCoordinateSliceBasisWithoutLast, Fin.init]

/-- Each upper inserted-coordinate parametrization of the final face gives the
same integral as the standard final-face parametrization, before doing the
alternating tangent-basis algebra. -/
theorem integral_upperEndpoint_insert_eq_finalFace_reparametrized
    {k : ℕ}
    (pulled :
      (Fin (k + 1) → ℝ) →
        (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F)
    (i : Fin (k + 1)) :
    (let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
      fun j ↦ Pi.single j (1 : ℝ)
     ∫ x in simplexCoordinateDomain k,
      pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
        (i.removeNth base)) =
    (let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
      fun j ↦ Pi.single j (1 : ℝ)
     ∫ x in simplexCoordinateDomain k,
      pulled (simplexCoordinateSliceMap k x (1 - ∑ j : Fin k, x j))
        (i.removeNth base)) := by
  classical
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  let p : Equiv.Perm (Fin (k + 1)) :=
    i.cycleRange.symm * (Fin.last k).cycleRange
  let g : (Fin k → ℝ) → F := fun x =>
    pulled (simplexCoordinateSliceMap k x (1 - ∑ j : Fin k, x j))
      (i.removeNth base)
  have hcov := integral_comp_simplexCoordinateVertexPermutationMap (G := F) p g
  rw [← hcov]
  refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
  intro x hx
  dsimp [g, base]
  rw [← simplexCoordinateOfBarycentric_insert_upper_eq_vertexPermutation i x]
  rw [simplexCoordinateInsertMap_upper_eq_slice_of_barycentric i x]

/-- If an alternating form is curried at `x`, translating all remaining
arguments by `-x` does not change its value. -/
theorem continuousAlternatingMap_curryLeft_sub_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {k : ℕ} (B : V [⋀^Fin (k + 1)]→L[ℝ] F) (x : V)
    (v : Fin k → V) :
    B.curryLeft x (fun j : Fin k => v j - x) = B.curryLeft x v := by
  classical
  let G : V [⋀^Fin k]→L[ℝ] F := B.curryLeft x
  have hsum' :
      (∑ s : Finset (Fin k), G (s.piecewise v (fun _ : Fin k => -x))) =
        G ((Finset.univ : Finset (Fin k)).piecewise v (fun _ : Fin k => -x)) := by
    refine Finset.sum_eq_single
      (s := (Finset.univ : Finset (Finset (Fin k))))
      (f := fun s : Finset (Fin k) => G (s.piecewise v (fun _ : Fin k => -x)))
      (a := (Finset.univ : Finset (Fin k))) ?_ ?_
    · intro s hs hne
      have hproper : ∃ j : Fin k, j ∉ s := by
        by_contra h
        push Not at h
        apply hne
        ext j
        simp [h j]
      rcases hproper with ⟨j, hjs⟩
      let w : Fin k → V := s.piecewise v (fun _ : Fin k => -x)
      have hwj : w j = -x := by
        simpa [w] using s.piecewise_eq_of_notMem v (fun _ : Fin k => -x) hjs
      have hwupdate : w = Function.update w j (-x) := by
        funext a
        by_cases haj : a = j
        · subst a
          simp [hwj]
        · simp [Function.update, haj]
      calc
        G (s.piecewise v (fun _ : Fin k => -x)) = G w := by rfl
        _ = G (Function.update w j ((-1 : ℝ) • x)) := by
          rw [hwupdate]
          simp
        _ = (-1 : ℝ) • G (Function.update w j x) := by
          exact G.map_update_smul w j (-1 : ℝ) x
        _ = 0 := by
          have hz : G (Function.update w j x) = 0 := by
            change B (Matrix.vecCons x (Function.update w j x)) = 0
            exact B.map_eq_zero_of_eq
              (Matrix.vecCons x (Function.update w j x))
              (i := (0 : Fin (k + 1))) (j := j.succ)
              (by simp) (by exact (Fin.succ_ne_zero j).symm)
          simp [hz]
    · intro hnot
      simp at hnot
  have hsum :
      (∑ s : Finset (Fin k), G (s.piecewise v (fun _ : Fin k => -x))) = G v := by
    simpa using hsum'
  have hmap := G.map_add_univ v (fun _ : Fin k => -x)
  simpa [G, sub_eq_add_neg, Pi.add_apply] using hmap.trans hsum

/-- The alternating sum of the coordinate hyperface tangent bases is the
standard oriented final-face tangent basis. -/
theorem continuousAlternatingMap_boundaryBasis_eq_finalFaceBasis
    {k : ℕ}
    (A : (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F) :
    (let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
      fun j ↦ Pi.single j (1 : ℝ)
     ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • A (i.removeNth base)) =
      ((-1 : ℤ) ^ k) •
        A (fun j : Fin k =>
          Pi.single j.castSucc (1 : ℝ) -
            Pi.single (Fin.last k) (1 : ℝ)) := by
  classical
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  let sumCoord : (Fin (k + 1) → ℝ) →L[ℝ] ℝ :=
    ∑ j : Fin (k + 1), ContinuousLinearMap.proj j
  let B : (Fin (k + 1) → ℝ) [⋀^Fin (k + 1)]→L[ℝ] F :=
    ContinuousAlternatingMap.alternatizeUncurryFin
      (sumCoord.smulRight A)
  let lastVec : Fin (k + 1) → ℝ := Pi.single (Fin.last k) (1 : ℝ)
  let tail : Fin k → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j.castSucc (1 : ℝ)
  let finalBasis : Fin k → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j.castSucc (1 : ℝ) -
      Pi.single (Fin.last k) (1 : ℝ)
  have hB_base :
      B base =
        ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • A (i.removeNth base) := by
    simpa [B, sumCoord, base] using
      ContinuousAlternatingMap.alternatizeUncurryFin_apply
        (sumCoord.smulRight A) base
  have hbase_insert :
      base = (Fin.last k).insertNth lastVec tail := by
    funext a
    cases a using Fin.lastCases with
    | last =>
        simp [base, lastVec, tail]
    | cast a =>
        simp [base, lastVec, tail]
  have hB_insert :
      B base =
        ((-1 : ℤ) ^ k) • B (Matrix.vecCons lastVec tail) := by
    rw [hbase_insert]
    simpa [lastVec, tail] using
      ContinuousAlternatingMap.map_insertNth B (Fin.last k) lastVec tail
  have htail_final :
      B (Matrix.vecCons lastVec finalBasis) =
        B (Matrix.vecCons lastVec tail) := by
    change B.curryLeft lastVec finalBasis = B.curryLeft lastVec tail
    simpa [finalBasis, tail, lastVec] using
      continuousAlternatingMap_curryLeft_sub_const
        (F := F) B lastVec tail
  have hB_final :
      B (Matrix.vecCons lastVec finalBasis) = A finalBasis := by
    change (ContinuousAlternatingMap.alternatizeUncurryFin
      (sumCoord.smulRight A)) (Matrix.vecCons lastVec finalBasis) = A finalBasis
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    rw [Fin.sum_univ_succ]
    simp [sumCoord, lastVec, finalBasis]
  calc
    (let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
      fun j ↦ Pi.single j (1 : ℝ)
     ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • A (i.removeNth base))
        = B base := by
          simpa [base] using hB_base.symm
    _ = ((-1 : ℤ) ^ k) • B (Matrix.vecCons lastVec tail) := hB_insert
    _ = ((-1 : ℤ) ^ k) • B (Matrix.vecCons lastVec finalBasis) := by
          rw [htail_final]
    _ = ((-1 : ℤ) ^ k) • A finalBasis := by
          rw [hB_final]
    _ = ((-1 : ℤ) ^ k) •
        A (fun j : Fin k =>
          Pi.single j.castSucc (1 : ℝ) -
            Pi.single (Fin.last k) (1 : ℝ)) := by
          rfl

/-- The defining alternating-sum expansion of the model-space exterior derivative,
written directly in terms of the Fréchet derivative of the form-valued map. -/
theorem extDerivWithin_apply_fderivWithin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (eta : V → V [⋀^Fin n]→L[ℝ] W) (s : Set V) (x : V)
    (v : Fin (n + 1) → V) :
    extDerivWithin eta s x v =
      ∑ i : Fin (n + 1),
        (-1 : ℤ) ^ (i : ℕ) •
          (fderivWithin ℝ eta s x (v i)) (i.removeNth v) := by
  simpa [extDerivWithin] using
    ContinuousAlternatingMap.alternatizeUncurryFin_apply
      (fderivWithin ℝ eta s x) v

/-- Evaluating a differentiable family of alternating maps on a fixed tuple
commutes with taking the within Fréchet derivative. -/
theorem fderivWithin_continuousAlternatingMap_apply_const_apply_symm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} {eta : V → V [⋀^Fin n]→L[ℝ] W} {s : Set V} {x : V}
    (hxs : UniqueDiffWithinAt ℝ s x)
    (heta : DifferentiableWithinAt ℝ eta s x)
    (u : Fin n → V) (v : V) :
    (fderivWithin ℝ eta s x v) u =
      fderivWithin ℝ (fun y => eta y u) s x v := by
  exact
    (fderivWithin_continuousAlternatingMap_apply_const_apply
      hxs heta u v).symm

/-- The exterior derivative of a family of `k`-forms in affine coordinates is
the alternating sum of the coordinate derivatives of its scalar coefficients. -/
theorem extDerivWithin_apply_basis_eq_sum_directional_coefficients
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} (eta : V → V [⋀^Fin k]→L[ℝ] W)
    (s : Set V) {x : V}
    (base : Fin (k + 1) → V)
    (hxs : UniqueDiffWithinAt ℝ s x)
    (heta : DifferentiableWithinAt ℝ eta s x) :
    extDerivWithin eta s x base =
      ∑ i : Fin (k + 1),
        (-1 : ℤ) ^ (i : ℕ) •
          fderivWithin ℝ
            (fun y => eta y (i.removeNth base)) s x (base i) := by
  rw [extDerivWithin_apply_fderivWithin]
  refine Finset.sum_congr rfl ?_
  intro i hi
  congr 1
  exact fderivWithin_continuousAlternatingMap_apply_const_apply_symm
    hxs heta (i.removeNth base) (base i)

/--
The one-dimensional FTC contribution obtained by integrating in an arbitrary
affine coordinate of a simplex.
-/
theorem integral_simplexInsertedCoordinateDerivative_eq_endpoint_sub
    [CompleteSpace F]
    {k : ℕ} (i : Fin (k + 1))
    (coeff : (Fin (k + 1) → ℝ) → F)
    (x : Fin k → ℝ) (u : ℝ)
    (hu : 0 ≤ u)
    (hcont :
      ContDiffOn ℝ 1
        (fun t : ℝ => coeff (simplexCoordinateInsertMap i x t))
        (Icc (0 : ℝ) u))
    (hderiv :
      EqOn
        (fun t : ℝ =>
          fderivWithin ℝ coeff
            (simplexCoordinateDomain (k + 1))
            (simplexCoordinateInsertMap i x t)
            (Pi.single i (1 : ℝ)))
        (fun t : ℝ =>
          derivWithin
            (fun s : ℝ => coeff (simplexCoordinateInsertMap i x s))
            (Icc (0 : ℝ) u) t)
        (Icc (0 : ℝ) u)) :
    (∫ t in Icc (0 : ℝ) u,
      fderivWithin ℝ coeff
        (simplexCoordinateDomain (k + 1))
        (simplexCoordinateInsertMap i x t)
        (Pi.single i (1 : ℝ))) =
      coeff (simplexCoordinateInsertMap i x u) -
        coeff (simplexCoordinateInsertMap i x 0) := by
  exact
    integral_Icc_eq_endpoint_sub_of_derivWithin
      (F := F) (a := (0 : ℝ)) (b := u)
      (f := fun t : ℝ => coeff (simplexCoordinateInsertMap i x t))
      (g := fun t : ℝ =>
        fderivWithin ℝ coeff
          (simplexCoordinateDomain (k + 1))
          (simplexCoordinateInsertMap i x t)
          (Pi.single i (1 : ℝ)))
      hcont hu hderiv

/-- Integrating one coordinate derivative over the affine simplex gives the
difference of the corresponding coefficient on the two opposite coordinate
faces. -/
theorem integral_simplexCoordinateDomain_directionalDerivative_eq_faceDifference
    [CompleteSpace F]
    {k : ℕ} (i : Fin (k + 1))
    (coeff : (Fin (k + 1) → ℝ) → F)
    (hInt :
      IntegrableOn
        (fun y : Fin (k + 1) → ℝ =>
          fderivWithin ℝ coeff (simplexCoordinateDomain (k + 1)) y
            (Pi.single i (1 : ℝ)))
        (simplexCoordinateDomain (k + 1)))
    (hcont :
      ∀ x ∈ simplexCoordinateDomain k,
        ContDiffOn ℝ 1
          (fun t : ℝ => coeff
            (simplexCoordinateInsertMap i x t))
          (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)))
    (hderiv :
      ∀ x ∈ simplexCoordinateDomain k,
        EqOn
          (fun t : ℝ =>
            fderivWithin ℝ coeff
              (simplexCoordinateDomain (k + 1))
              (simplexCoordinateInsertMap i x t)
              (Pi.single i (1 : ℝ)))
          (fun t : ℝ =>
            derivWithin
              (fun s : ℝ => coeff (simplexCoordinateInsertMap i x s))
              (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)) t)
          (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j))) :
    (∫ y in simplexCoordinateDomain (k + 1),
      fderivWithin ℝ coeff (simplexCoordinateDomain (k + 1)) y
        (Pi.single i (1 : ℝ))) =
      ∫ x in simplexCoordinateDomain k,
        coeff (simplexCoordinateInsertMap i x
          (1 - ∑ j : Fin k, x j)) -
          coeff (simplexCoordinateInsertMap i x 0) := by
  classical
  rw [integral_simplexCoordinateDomain_eq_insertIterated
    (k := k) i
    (f := fun y : Fin (k + 1) → ℝ =>
      fderivWithin ℝ coeff (simplexCoordinateDomain (k + 1)) y
        (Pi.single i (1 : ℝ)))
    hInt]
  refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
  intro x hx
  have hu : 0 ≤ 1 - ∑ j : Fin k, x j := sub_nonneg.mpr hx.2
  exact
    integral_simplexInsertedCoordinateDerivative_eq_endpoint_sub
      (F := F) i coeff x (1 - ∑ j : Fin k, x j) hu
      (hcont x hx) (hderiv x hx)

/-- Integrating one coordinate derivative over the affine simplex gives the
difference of the two coordinate-face integrals. -/
theorem integral_simplexCoordinateDomain_directionalDerivative_eq_integral_faceDifference
    [CompleteSpace F]
    {k : ℕ} (i : Fin (k + 1))
    (coeff : (Fin (k + 1) → ℝ) → F)
    (hInt :
      IntegrableOn
        (fun y : Fin (k + 1) → ℝ =>
          fderivWithin ℝ coeff (simplexCoordinateDomain (k + 1)) y
            (Pi.single i (1 : ℝ)))
        (simplexCoordinateDomain (k + 1)))
    (hUpperInt :
      IntegrableOn
        (fun x : Fin k → ℝ =>
          coeff (simplexCoordinateInsertMap i x
            (1 - ∑ j : Fin k, x j)))
        (simplexCoordinateDomain k))
    (hLowerInt :
      IntegrableOn
        (fun x : Fin k → ℝ =>
          coeff (simplexCoordinateInsertMap i x 0))
        (simplexCoordinateDomain k))
    (hcont :
      ∀ x ∈ simplexCoordinateDomain k,
        ContDiffOn ℝ 1
          (fun t : ℝ => coeff
            (simplexCoordinateInsertMap i x t))
          (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)))
    (hderiv :
      ∀ x ∈ simplexCoordinateDomain k,
        EqOn
          (fun t : ℝ =>
            fderivWithin ℝ coeff
              (simplexCoordinateDomain (k + 1))
              (simplexCoordinateInsertMap i x t)
              (Pi.single i (1 : ℝ)))
          (fun t : ℝ =>
            derivWithin
              (fun s : ℝ => coeff (simplexCoordinateInsertMap i x s))
              (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)) t)
          (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j))) :
    (∫ y in simplexCoordinateDomain (k + 1),
      fderivWithin ℝ coeff (simplexCoordinateDomain (k + 1)) y
        (Pi.single i (1 : ℝ))) =
      (∫ x in simplexCoordinateDomain k,
        coeff (simplexCoordinateInsertMap i x
          (1 - ∑ j : Fin k, x j))) -
        ∫ x in simplexCoordinateDomain k,
          coeff (simplexCoordinateInsertMap i x 0) := by
  rw [integral_simplexCoordinateDomain_directionalDerivative_eq_faceDifference
    (F := F) i coeff hInt hcont hderiv]
  rw [integral_sub hUpperInt hLowerInt]

/-- A coordinate-line derivative integrates to the difference of the two
coordinate-face integrals.  Unlike
`integral_simplexCoordinateDomain_directionalDerivative_eq_integral_faceDifference`,
the derivative integrand is supplied separately; the hypotheses only require
that it agrees with the one-dimensional derivative on every inserted coordinate
line. -/
theorem integral_simplexCoordinateDomain_lineDerivative_eq_integral_faceDifference
    [CompleteSpace F]
    {k : ℕ} (i : Fin (k + 1))
    (coeff g : (Fin (k + 1) → ℝ) → F)
    (hInt : IntegrableOn g (simplexCoordinateDomain (k + 1)))
    (hUpperInt :
      IntegrableOn
        (fun x : Fin k → ℝ =>
          coeff (simplexCoordinateInsertMap i x
            (1 - ∑ j : Fin k, x j)))
        (simplexCoordinateDomain k))
    (hLowerInt :
      IntegrableOn
        (fun x : Fin k → ℝ =>
          coeff (simplexCoordinateInsertMap i x 0))
        (simplexCoordinateDomain k))
    (hcont :
      ∀ x ∈ simplexCoordinateDomain k,
        ContDiffOn ℝ 1
          (fun t : ℝ => coeff
            (simplexCoordinateInsertMap i x t))
          (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)))
    (hderiv :
      ∀ x ∈ simplexCoordinateDomain k,
        EqOn
          (fun t : ℝ => g (simplexCoordinateInsertMap i x t))
          (fun t : ℝ =>
            derivWithin
              (fun s : ℝ => coeff (simplexCoordinateInsertMap i x s))
              (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)) t)
          (Ioo (0 : ℝ) (1 - ∑ j : Fin k, x j))) :
    (∫ y in simplexCoordinateDomain (k + 1), g y) =
      (∫ x in simplexCoordinateDomain k,
        coeff (simplexCoordinateInsertMap i x
          (1 - ∑ j : Fin k, x j))) -
        ∫ x in simplexCoordinateDomain k,
          coeff (simplexCoordinateInsertMap i x 0) := by
  rw [integral_simplexCoordinateDomain_eq_insertIterated
    (k := k) i g hInt]
  have hpoint :
      EqOn
        (fun x : Fin k → ℝ =>
          ∫ t in Icc (0 : ℝ) (1 - ∑ j : Fin k, x j),
            g (simplexCoordinateInsertMap i x t))
        (fun x : Fin k → ℝ =>
          coeff (simplexCoordinateInsertMap i x
            (1 - ∑ j : Fin k, x j)) -
          coeff (simplexCoordinateInsertMap i x 0))
        (simplexCoordinateDomain k) := by
    intro x hx
    have hu : 0 ≤ 1 - ∑ j : Fin k, x j := sub_nonneg.mpr hx.2
    exact integral_Icc_eq_endpoint_sub_of_eqOn_Ioo_derivWithin
      (F := F) (a := (0 : ℝ)) (b := 1 - ∑ j : Fin k, x j)
      (f := fun t : ℝ => coeff (simplexCoordinateInsertMap i x t))
      (g := fun t : ℝ => g (simplexCoordinateInsertMap i x t))
      (hcont x hx) hu (hderiv x hx)
  rw [setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) hpoint]
  rw [integral_sub hUpperInt hLowerInt]

/--
The one-dimensional FTC contribution on a last-coordinate slice of a simplex.

The hypotheses isolate the analytic leaf: the primitive along the slice is `C^1`,
and the displayed ambient directional derivative is its within-interval derivative.
-/
theorem integral_simplexSlice_lastCoordinateDerivative_eq_endpoint_sub
    [CompleteSpace F]
    {k : ℕ}
    (pulled :
      (Fin (k + 1) → ℝ) →
        (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F)
    (x : Fin k → ℝ) (u : ℝ)
    (hu : 0 ≤ u)
    (hcont :
      ContDiffOn ℝ 1
        (fun t : ℝ =>
          pulled (simplexCoordinateSliceMap k x t)
            (simplexCoordinateSliceBasisWithoutLast k))
        (Icc (0 : ℝ) u))
    (hderiv :
      EqOn
        (fun t : ℝ =>
          fderivWithin ℝ
            (fun y : Fin (k + 1) → ℝ =>
              pulled y (simplexCoordinateSliceBasisWithoutLast k))
            (simplexCoordinateDomain (k + 1))
            (simplexCoordinateSliceMap k x t)
            (Pi.single (Fin.last k) (1 : ℝ)))
        (fun t : ℝ =>
          derivWithin
            (fun s : ℝ =>
              pulled (simplexCoordinateSliceMap k x s)
                (simplexCoordinateSliceBasisWithoutLast k))
            (Icc (0 : ℝ) u) t)
        (Icc (0 : ℝ) u)) :
    (∫ t in Icc (0 : ℝ) u,
      fderivWithin ℝ
        (fun y : Fin (k + 1) → ℝ =>
          pulled y (simplexCoordinateSliceBasisWithoutLast k))
        (simplexCoordinateDomain (k + 1))
        (simplexCoordinateSliceMap k x t)
        (Pi.single (Fin.last k) (1 : ℝ))) =
      pulled (simplexCoordinateSliceMap k x u)
          (simplexCoordinateSliceBasisWithoutLast k) -
        pulled (simplexCoordinateSliceMap k x 0)
          (simplexCoordinateSliceBasisWithoutLast k) := by
  exact
    integral_Icc_eq_endpoint_sub_of_derivWithin
      (F := F) (a := (0 : ℝ)) (b := u)
      (f := fun t : ℝ =>
        pulled (simplexCoordinateSliceMap k x t)
          (simplexCoordinateSliceBasisWithoutLast k))
      (g := fun t : ℝ =>
        fderivWithin ℝ
          (fun y : Fin (k + 1) → ℝ =>
            pulled y (simplexCoordinateSliceBasisWithoutLast k))
          (simplexCoordinateDomain (k + 1))
          (simplexCoordinateSliceMap k x t)
          (Pi.single (Fin.last k) (1 : ℝ)))
      hcont hu hderiv

/--
The endpoint algebra for the simplex Stokes calculation.

If the alternating sum of all upper-coordinate endpoints is the oriented final-face
term, then the signed endpoint sum obtained from the coordinatewise FTC is exactly
the boundary formula used below.
-/
theorem simplexEndpointAlternatingSum_with_upperCollapse
    {A : Type*} [AddCommGroup A]
    {k : ℕ} (U L : Fin (k + 1) → A) (Final : A)
    (hUpper :
      (∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • U i) =
        ((-1 : ℤ) ^ k) • Final) :
    ((-1 : ℤ) ^ (k + 1)) •
        (∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • (U i - L i)) =
      (∑ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i.castSucc : ℕ)) • (((-1 : ℤ) ^ k) • L i)) +
      ((-1 : ℤ) ^ (k + 1)) • (((-1 : ℤ) ^ k) • Final) := by
  have hdistrib :
      ((-1 : ℤ) ^ (k + 1)) •
          (∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • (U i - L i)) =
        ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (k + 1)) •
          (((-1 : ℤ) ^ (i : ℕ)) • (U i - L i)) := by
    exact (Finset.smul_sum (s := Finset.univ)
      (r := ((-1 : ℤ) ^ (k + 1)))
      (f := fun i : Fin (k + 1) => ((-1 : ℤ) ^ (i : ℕ)) • (U i - L i)))
  rw [hdistrib]
  simp_rw [smul_smul, zsmul_sub]
  rw [Finset.sum_sub_distrib]
  have hupper' :
      (∑ i : Fin (k + 1), (((-1 : ℤ) ^ (k + 1)) * ((-1 : ℤ) ^ (i : ℕ))) • U i) =
        ((-1 : ℤ) ^ (k + 1)) • (((-1 : ℤ) ^ k) • Final) := by
    rw [← hUpper]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [smul_smul]
  rw [hupper']
  rw [sub_eq_add_neg]
  rw [smul_smul]
  rw [(show (∑ i : Fin (k + 1), (((-1 : ℤ) ^ (i.castSucc : ℕ)) * ((-1 : ℤ) ^ k)) • L i) +
      (((-1 : ℤ) ^ (k + 1) * ((-1 : ℤ) ^ k)) • Final) =
      (((-1 : ℤ) ^ (k + 1) * ((-1 : ℤ) ^ k)) • Final) +
      (∑ i : Fin (k + 1), (((-1 : ℤ) ^ (i.castSucc : ℕ)) * ((-1 : ℤ) ^ k)) • L i) by
        rw [add_comm])]
  rw [add_left_cancel_iff]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [← neg_zsmul]
  congr 1
  simp [pow_succ, mul_comm]

/-- Pulling a \(C^1\) degree \(k\) form back along a \(C^2\) simplex gives a
\(C^1\) family of alternating \(k\)-forms on affine simplex coordinates. -/
theorem simplexPullbackFormAlongUsingExtension_contDiffOn
    [IsManifold I ∞ M]
    {m k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) m r) :
    ContDiffOn ℝ 1
      (simplexPullbackFormAlongUsingExtension (I := I) (F := F)
        (m := m) (k := k)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
        σ.extension)
      (simplexCoordinateDomain m) := by
  classical
  let D : Set (Fin m → ℝ) := simplexCoordinateDomain m
  let φ : (Fin m → ℝ) → M := simplexParametrizationUsingExtension σ.extension
  let form0 : ContinuousDifferentialForm (I := I) (M := M) (F := F) k :=
    DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega
  let pulled : (Fin m → ℝ) →
      (Fin m → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := m) (k := k) form0 σ.extension
  have hcell_one : (1 : WithTop ℕ∞) ≤ r :=
    one_le_of_two_le_smoothness hcell
  refine contDiffOn_of_locally_contDiffOn ?_
  intro x hx
  let e : OpenPartialHomeomorph M H := chartAt H (φ x)
  let ψ : (Fin m → ℝ) → E := fun y ↦ (extChartAt I (φ x)) (φ y)
  let η : E → E [⋀^Fin k]→L[ℝ] F :=
    coordinateExpression (I := I) (F := F) (n := k) omega.toFun e
  let localPullback : (Fin m → ℝ) →
      (Fin m → ℝ) [⋀^Fin k]→L[ℝ] F :=
    fun y ↦ (η (ψ y)).compContinuousLinearMap (fderivWithin ℝ ψ D y)
  have he : e ∈ atlas H M := by
    simp [e]
  have hφ_contdiff_one :
      ContMDiffWithinAt 𝓘(ℝ, Fin m → ℝ) I (1 : WithTop ℕ∞) φ D x := by
    exact (ContMDiffSingularSimplex.contMDiffWithinAt_simplexParametrization
      (I := I) (M := M) σ (by simpa [D] using hx)).of_le hcell_one
  have hpre_source : φ ⁻¹' e.source ∈ 𝓝[D] x := by
    exact hφ_contdiff_one.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_source.mem_nhds (by simp [e, φ]))
  rcases mem_nhdsWithin.1 hpre_source with ⟨u, hu_open, hxu, hu_subset⟩
  refine ⟨u, hu_open, hxu, ?_⟩
  have hφ_contdiff_two_on :
      ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I (2 : WithTop ℕ∞) φ D := by
    exact (ContMDiffSingularSimplex.contMDiffOn_simplexParametrization
      (I := I) (M := M) σ).of_le hcell
  have hψ_contdiff_mfld :
      ContMDiffOn 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, E)
        (2 : WithTop ℕ∞) ψ (D ∩ φ ⁻¹' e.source) := by
    have htarget_form :=
      (contMDiffOn_iff_target
        (I := 𝓘(ℝ, Fin m → ℝ)) (I' := I)
        (n := (2 : WithTop ℕ∞))
        (f := φ) (s := D)).1 hφ_contdiff_two_on
    simpa [ψ, φ, e] using (htarget_form.2 (φ x))
  have hDu_subset_source : D ∩ u ⊆ D ∩ φ ⁻¹' e.source := by
    intro y hy
    exact ⟨hy.1, hu_subset ⟨hy.2, hy.1⟩⟩
  have hψ_two : ContDiffOn ℝ (2 : WithTop ℕ∞) ψ (D ∩ u) := by
    exact (hψ_contdiff_mfld.contDiffOn).mono hDu_subset_source
  have hψ_one : ContDiffOn ℝ 1 ψ (D ∩ u) :=
    hψ_two.of_le (by norm_num)
  have hψ_maps_target : MapsTo ψ (D ∩ u) (e.extend I).target := by
    intro y hy
    have hsource : φ y ∈ (e.extend I).source := by
      simpa [e.extend_source (I := I)] using
        (hu_subset ⟨hy.2, hy.1⟩ : φ y ∈ e.source)
    change (e.extend I) (φ y) ∈ (e.extend I).target
    exact (e.extend I).map_source hsource
  have hη : ContDiffOn ℝ 1 η (e.extend I).target := by
    simpa [η] using omega.isContMDiff e he
  have hηψ : ContDiffOn ℝ 1 (fun y ↦ η (ψ y)) (D ∩ u) := by
    exact hη.comp hψ_one hψ_maps_target
  have hDψ_local :
      ContDiffOn ℝ 1 (fderivWithin ℝ ψ (D ∩ u)) (D ∩ u) := by
    exact hψ_two.fderivWithin
      ((uniqueDiffOn_simplexCoordinateDomain m).inter hu_open)
      (by norm_num)
  have hDψ :
      ContDiffOn ℝ 1 (fderivWithin ℝ ψ D) (D ∩ u) := by
    refine hDψ_local.congr ?_
    intro y hy
    exact (fderivWithin_inter (hu_open.mem_nhds hy.2)).symm
  have hlocal :
      ContDiffOn ℝ 1 localPullback (D ∩ u) := by
    simpa [localPullback] using
      contDiffOn_continuousAlternatingMap_compContinuousLinearMap_one
        (𝕜 := ℝ) (s := D ∩ u)
        ((uniqueDiffOn_simplexCoordinateDomain m).inter hu_open)
        hηψ hDψ
  have hpulled_local : ContDiffOn ℝ 1 pulled (D ∩ u) := by
    refine hlocal.congr ?_
    intro y hy
    have hsource : φ y ∈ e.source :=
      hu_subset ⟨hy.2, hy.1⟩
    simpa [pulled, localPullback, form0, η, ψ, φ, e, D] using
      simplexPullbackFormAlongUsingExtension_eq_coordinateExpression_of_mem_source
        (I := I) (F := F) (m := m) (k := k)
        hcell_one form0 σ (by simpa [D] using hy.1) hsource
  simpa [pulled, form0, D] using hpulled_local

/--
Regularity of the pulled-back coefficient functions along the coordinate
lines of the affine simplex.

This is the analytic input for the coordinatewise FTC step: the displayed
coordinate derivatives are integrable over the simplex, each coefficient
restricted to an inserted coordinate line is \(C^1\), and the displayed
integrand agrees with the derivative of that one-dimensional restriction.
-/
theorem simplexPullbackFormAlongUsingExtension_coordinateLineFTCData
    [IsManifold I ∞ M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
      (let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
       let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension
       let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
       (∀ i : Fin (k + 1),
          IntegrableOn
            (fun y : Fin (k + 1) → ℝ =>
              (fderivWithin ℝ pulled D y (base i)) (i.removeNth base))
            D) ∧
       (∀ (i : Fin (k + 1)) (x : Fin k → ℝ),
          x ∈ simplexCoordinateDomain k →
            ContDiffOn ℝ 1
              (fun t : ℝ =>
                pulled (simplexCoordinateInsertMap i x t)
                  (i.removeNth base))
              (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j))) ∧
       (∀ (i : Fin (k + 1)) (x : Fin k → ℝ),
          x ∈ simplexCoordinateDomain k →
            EqOn
              (fun t : ℝ =>
                (fderivWithin ℝ pulled D
                  (simplexCoordinateInsertMap i x t) (base i))
                  (i.removeNth base))
              (fun t : ℝ =>
                derivWithin
                  (fun s : ℝ =>
                    pulled (simplexCoordinateInsertMap i x s)
                      (i.removeNth base))
                  (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)) t)
              (Ioo (0 : ℝ) (1 - ∑ j : Fin k, x j)))) := by
  classical
  let form0 : ContinuousDifferentialForm (I := I) (M := M) (F := F) k :=
    DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega
  let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
  let pulled :
      (Fin (k + 1) → ℝ) →
        (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := k + 1) (k := k) form0 σ.extension
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  have hpull : ContDiffOn ℝ 1 pulled D := by
    simpa [pulled, form0, D] using
      simplexPullbackFormAlongUsingExtension_contDiffOn
        (I := I) (F := F) (m := k + 1) (k := k) hcell omega σ
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hfd :
        ContinuousOn (fun y : Fin (k + 1) → ℝ =>
          fderivWithin ℝ pulled D y) D :=
      hpull.continuousOn_fderivWithin
        (by simpa [D] using uniqueDiffOn_simplexCoordinateDomain (k + 1))
        (by simp)
    have hfd_apply :
        ContinuousOn
          (fun y : Fin (k + 1) → ℝ =>
            (fderivWithin ℝ pulled D y) (base i)) D :=
      hfd.clm_apply continuousOn_const
    have hterm :
        ContinuousOn
          (fun y : Fin (k + 1) → ℝ =>
            (fderivWithin ℝ pulled D y (base i)) (i.removeNth base)) D :=
      (ContinuousLinearMap.continuous
        (ContinuousAlternatingMap.apply ℝ (Fin (k + 1) → ℝ) F
          (i.removeNth base))).comp_continuousOn hfd_apply
    exact hterm.integrableOn_compact (by simpa [D] using isCompact_simplexCoordinateDomain (k + 1))
  · intro i x hx
    let interval : Set ℝ := Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)
    let line : ℝ → (Fin (k + 1) → ℝ) :=
      fun t ↦ simplexCoordinateInsertMap i x t
    have hline : ContDiffOn ℝ 1 line interval := by
      simpa [line] using
        (contDiffOn_simplexCoordinateInsertMap_line (k := k) i x
          (r := (1 : WithTop ℕ∞)) (s := interval))
    have hmaps : MapsTo line interval D := by
      intro t ht
      change simplexCoordinateInsertMap i x t ∈ simplexCoordinateDomain (k + 1)
      rw [simplexCoordinateInsertMap_mem_domain_iff]
      exact ⟨hx, ht⟩
    have hpull_line :
        ContDiffOn ℝ 1 (pulled ∘ line) interval :=
      hpull.comp hline hmaps
    have hcoeff :
        ContDiffOn ℝ 1
          ((ContinuousAlternatingMap.apply ℝ (Fin (k + 1) → ℝ) F
            (i.removeNth base)) ∘ (pulled ∘ line)) interval :=
      (ContinuousAlternatingMap.apply ℝ (Fin (k + 1) → ℝ) F
        (i.removeNth base)).contDiff.comp_contDiffOn hpull_line
    simpa [line, Function.comp_def, interval] using hcoeff
  · intro i x hx
    let interval : Set ℝ := Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)
    let line : ℝ → (Fin (k + 1) → ℝ) :=
      fun t ↦ simplexCoordinateInsertMap i x t
    let coeff : (Fin (k + 1) → ℝ) → F :=
      fun y ↦ pulled y (i.removeNth base)
    intro t ht
    have ht_interval : t ∈ interval := ⟨ht.1.le, ht.2.le⟩
    have hu_pos : 0 < 1 - ∑ j : Fin k, x j := lt_trans ht.1 ht.2
    have hmaps : MapsTo line interval D := by
      intro s hs
      change simplexCoordinateInsertMap i x s ∈ simplexCoordinateDomain (k + 1)
      rw [simplexCoordinateInsertMap_mem_domain_iff]
      exact ⟨hx, hs⟩
    have hy : line t ∈ D := hmaps ht_interval
    have hdiff_pulled : DifferentiableWithinAt ℝ pulled D (line t) :=
      (hpull.differentiableOn one_ne_zero) (line t) hy
    let evalCLM :
        ((Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F) →L[ℝ] F :=
      ContinuousAlternatingMap.apply ℝ (Fin (k + 1) → ℝ) F
        (i.removeNth base)
    have hcoeff_deriv :
        HasFDerivWithinAt coeff
          (evalCLM.comp (fderivWithin ℝ pulled D (line t))) D (line t) := by
      change HasFDerivWithinAt (evalCLM ∘ pulled)
        (evalCLM.comp (fderivWithin ℝ pulled D (line t))) D (line t)
      exact (ContinuousLinearMap.hasFDerivAt evalCLM).comp_hasFDerivWithinAt
        (line t) hdiff_pulled.hasFDerivWithinAt
    have hline_deriv : HasDerivWithinAt line (base i) interval t := by
      simpa [line, base] using
        (hasDerivWithinAt_simplexCoordinateInsertMap_line (k := k) i x
          (s := interval) (t := t))
    have hcomp :
        HasDerivWithinAt (coeff ∘ line)
          ((evalCLM.comp (fderivWithin ℝ pulled D (line t))) (base i))
          interval t :=
      hcoeff_deriv.comp_hasDerivWithinAt t hline_deriv hmaps
    have hunique : UniqueDiffWithinAt ℝ interval t :=
      (uniqueDiffOn_Icc hu_pos).uniqueDiffWithinAt ht_interval
    have hderiv := hcomp.derivWithin hunique
    simpa [coeff, line, interval, evalCLM, ContinuousLinearMap.comp_apply] using hderiv.symm

/--
The coordinatewise FTC/Fubini step for the pulled-back `k`-form on the affine
`(k+1)`-simplex.

Each coordinate derivative integrates to the difference between the corresponding
upper coordinate endpoint and lower coordinate endpoint.  This is the analytic
leaf: it packages the `C^1` regularity of the pulled-back coefficient functions,
their integrability, Fubini for the sliced simplex, and the one-dimensional FTC.
-/
theorem integral_simplexPullbackFormAlong_expandedInterior_eq_endpointAlternatingSum
    [IsManifold I ∞ M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
      (let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
       let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension
       let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
       ∫ x in simplexCoordinateDomain k,
        ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
          (∑ i : Fin k,
            ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
              (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                (base i.castSucc))
                (i.castSucc.removeNth base)) +
            ((-1 : ℤ) ^ k) •
              (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                (Pi.single (Fin.last k) (1 : ℝ)))
                (simplexCoordinateSliceBasisWithoutLast k)) =
      (let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension
       let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
       ∑ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) •
          ((∫ x in simplexCoordinateDomain k,
              pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
                (i.removeNth base)) -
            ∫ x in simplexCoordinateDomain k,
              pulled (simplexCoordinateInsertMap i x 0)
                (i.removeNth base))) := by
  classical
  let form0 : ContinuousDifferentialForm (I := I) (M := M) (F := F) k :=
    DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega
  let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
  let pulled :
      (Fin (k + 1) → ℝ) →
        (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := k + 1) (k := k) form0 σ.extension
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  let derivTerm : Fin (k + 1) → (Fin (k + 1) → ℝ) → F :=
    fun i y => (fderivWithin ℝ pulled D y (base i)) (i.removeNth base)
  let fullIntegrand : (Fin (k + 1) → ℝ) → F :=
    fun y => ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • derivTerm i y
  have hreg :
      (∀ i : Fin (k + 1), IntegrableOn (derivTerm i) D) ∧
      (∀ (i : Fin (k + 1)) (x : Fin k → ℝ),
        x ∈ simplexCoordinateDomain k →
          ContDiffOn ℝ 1
            (fun t : ℝ =>
              pulled (simplexCoordinateInsertMap i x t)
                (i.removeNth base))
            (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j))) ∧
      (∀ (i : Fin (k + 1)) (x : Fin k → ℝ),
        x ∈ simplexCoordinateDomain k →
          EqOn
            (fun t : ℝ =>
              derivTerm i (simplexCoordinateInsertMap i x t))
            (fun t : ℝ =>
              derivWithin
                (fun s : ℝ =>
                  pulled (simplexCoordinateInsertMap i x s)
                    (i.removeNth base))
                (Icc (0 : ℝ) (1 - ∑ j : Fin k, x j)) t)
            (Ioo (0 : ℝ) (1 - ∑ j : Fin k, x j))) := by
    simpa [form0, pulled, D, base, derivTerm] using
      simplexPullbackFormAlongUsingExtension_coordinateLineFTCData
        (I := I) (F := F) hcell omega σ
  rcases hreg with ⟨hInt, hcont, hderiv⟩
  have hsignedInt :
      ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
        Integrable (fun y : Fin (k + 1) → ℝ =>
          ((-1 : ℤ) ^ (i : ℕ)) • derivTerm i y) (volume.restrict D) := by
    intro i hi
    exact integrable_negOnePow_zsmul (F := F)
      (μ := volume.restrict D) (n := (i : ℕ)) (hInt i)
  have hfullInt : IntegrableOn fullIntegrand D := by
    simpa [fullIntegrand] using
      integrable_finsetSum
        (s := (Finset.univ : Finset (Fin (k + 1))))
        (μ := volume.restrict D) hsignedInt
  have hcell_one : (1 : WithTop ℕ∞) ≤ r :=
    one_le_of_two_le_smoothness hcell
  have hUpperInt :
      ∀ i : Fin (k + 1),
        IntegrableOn
          (fun x : Fin k → ℝ =>
            pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
              (i.removeNth base))
          (simplexCoordinateDomain k) := by
    intro i
    have hmaps :
        MapsTo
          (fun x : Fin k → ℝ =>
            simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
          (simplexCoordinateDomain k) D := by
      intro x hx
      change simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j) ∈
        simplexCoordinateDomain (k + 1)
      rw [simplexCoordinateInsertMap_mem_domain_iff]
      exact ⟨hx, ⟨sub_nonneg.mpr hx.2, le_rfl⟩⟩
    have hcont_ambient :
        ContinuousOn
          (fun y : Fin (k + 1) → ℝ =>
            pulled y (i.removeNth base)) D := by
      simpa [pulled, form0, D] using
        continuousOn_simplexPullbackFormAlongUsingExtension_eval
          (I := I) (F := F) (m := k + 1) (k := k)
          hcell_one form0 σ (i.removeNth base)
    have hcont_map :
        ContinuousOn
          (fun x : Fin k → ℝ =>
            simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
          (simplexCoordinateDomain k) :=
      (continuous_simplexCoordinateInsertMap_upper i).continuousOn
    exact (hcont_ambient.comp hcont_map hmaps).integrableOn_compact
      (isCompact_simplexCoordinateDomain k)
  have hLowerInt :
      ∀ i : Fin (k + 1),
        IntegrableOn
          (fun x : Fin k → ℝ =>
            pulled (simplexCoordinateInsertMap i x 0)
              (i.removeNth base))
          (simplexCoordinateDomain k) := by
    intro i
    have hmaps :
        MapsTo
          (fun x : Fin k → ℝ => simplexCoordinateInsertMap i x 0)
          (simplexCoordinateDomain k) D := by
      intro x hx
      change simplexCoordinateInsertMap i x 0 ∈ simplexCoordinateDomain (k + 1)
      rw [simplexCoordinateInsertMap_mem_domain_iff]
      exact ⟨hx, ⟨le_rfl, sub_nonneg.mpr hx.2⟩⟩
    have hcont_ambient :
        ContinuousOn
          (fun y : Fin (k + 1) → ℝ =>
            pulled y (i.removeNth base)) D := by
      simpa [pulled, form0, D] using
        continuousOn_simplexPullbackFormAlongUsingExtension_eval
          (I := I) (F := F) (m := k + 1) (k := k)
          hcell_one form0 σ (i.removeNth base)
    have hcont_map :
        ContinuousOn
          (fun x : Fin k → ℝ => simplexCoordinateInsertMap i x 0)
          (simplexCoordinateDomain k) :=
      (continuous_simplexCoordinateInsertMap_zero i).continuousOn
    exact (hcont_ambient.comp hcont_map hmaps).integrableOn_compact
      (isCompact_simplexCoordinateDomain k)
  have hsplit :
      (∫ x in simplexCoordinateDomain k,
        ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
          (∑ i : Fin k,
            ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
              (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                (base i.castSucc))
                (i.castSucc.removeNth base)) +
            ((-1 : ℤ) ^ k) •
              (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                (Pi.single (Fin.last k) (1 : ℝ)))
                (simplexCoordinateSliceBasisWithoutLast k)) =
        (∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            fullIntegrand (simplexCoordinateSliceMap k x t)) := by
    refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
    intro x hx
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    simp [fullIntegrand, derivTerm, D, base, Fin.sum_univ_castSucc,
      simplexCoordinateSliceBasisWithoutLast]
  have hfull_to_endpoint :
      (∫ y in D, fullIntegrand y) =
        ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) •
          ((∫ x in simplexCoordinateDomain k,
              pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
                (i.removeNth base)) -
            ∫ x in simplexCoordinateDomain k,
              pulled (simplexCoordinateInsertMap i x 0)
                (i.removeNth base)) := by
    have hsum_integral :
        (∫ y in D, fullIntegrand y) =
          ∑ i : Fin (k + 1),
            ∫ y in D, ((-1 : ℤ) ^ (i : ℕ)) • derivTerm i y := by
      simpa [fullIntegrand] using
        MeasureTheory.integral_finsetSum
          (μ := volume.restrict D)
          (s := (Finset.univ : Finset (Fin (k + 1))))
          (f := fun i y => ((-1 : ℤ) ^ (i : ℕ)) • derivTerm i y)
          hsignedInt
    rw [hsum_integral]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [integral_negOnePow_zsmul
      (μ := volume.restrict D) (n := (i : ℕ))
      (f := derivTerm i)]
    congr 1
    have hcoord :=
      integral_simplexCoordinateDomain_lineDerivative_eq_integral_faceDifference
        (F := F) (k := k) i
        (fun y : Fin (k + 1) → ℝ => pulled y (i.removeNth base))
        (derivTerm i)
        (hInt i) (hUpperInt i) (hLowerInt i) (hcont i) (hderiv i)
    simpa [derivTerm, D, base] using hcoord
  calc
    (let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
     let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension
     let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
     ∫ x in simplexCoordinateDomain k,
      ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
        (∑ i : Fin k,
          ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
            (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
              (base i.castSucc))
              (i.castSucc.removeNth base)) +
          ((-1 : ℤ) ^ k) •
            (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
              (Pi.single (Fin.last k) (1 : ℝ)))
              (simplexCoordinateSliceBasisWithoutLast k)) =
      ∫ x in simplexCoordinateDomain k,
        ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
          fullIntegrand (simplexCoordinateSliceMap k x t) := by
        simpa [form0, pulled, D, base] using hsplit
    _ = ∫ y in D, fullIntegrand y := by
        exact (integral_simplexCoordinateDomain_succ_eq_iterated
          (k := k) fullIntegrand hfullInt).symm
    _ =
      (let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension
       let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
       ∑ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) •
          ((∫ x in simplexCoordinateDomain k,
              pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
                (i.removeNth base)) -
            ∫ x in simplexCoordinateDomain k,
              pulled (simplexCoordinateInsertMap i x 0)
                (i.removeNth base))) := by
        simpa [form0, pulled, base] using hfull_to_endpoint

/--
The upper-coordinate endpoints of the coordinatewise FTC collapse to the oriented
final face.

This is the geometric leaf: it is the affine change-of-variables and orientation
calculation identifying the `k+1` upper-coordinate parametrizations of the
residual barycentric face with the standard final-face parametrization.
-/
theorem simplexPullbackFormAlong_upperEndpointAlternatingIntegral_eq_finalFace
    [IsManifold I ∞ M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
      (let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension
       let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
       ∑ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) •
          ∫ x in simplexCoordinateDomain k,
            pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
              (i.removeNth base)) =
      (let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension
       ((-1 : ℤ) ^ k) •
          ∫ x in simplexCoordinateDomain k,
            pulled
              (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i))
              (fun j : Fin k =>
                Pi.single j.castSucc (1 : ℝ) -
                  Pi.single (Fin.last k) (1 : ℝ))) := by
  classical
  let form0 : ContinuousDifferentialForm (I := I) (M := M) (F := F) k :=
    DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega
  let pulled :
      (Fin (k + 1) → ℝ) →
        (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := k + 1) (k := k) form0 σ.extension
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  let finalPoint : (Fin k → ℝ) → (Fin (k + 1) → ℝ) :=
    fun x ↦ simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i)
  let finalBasis : Fin k → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j.castSucc (1 : ℝ) -
      Pi.single (Fin.last k) (1 : ℝ)
  change
    (∑ i : Fin (k + 1),
      ((-1 : ℤ) ^ (i : ℕ)) •
        ∫ x in simplexCoordinateDomain k,
          pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
            (i.removeNth base)) =
      ((-1 : ℤ) ^ k) •
        ∫ x in simplexCoordinateDomain k,
          pulled (finalPoint x) finalBasis
  have hreparam :
      ∀ i : Fin (k + 1),
        (∫ x in simplexCoordinateDomain k,
          pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
            (i.removeNth base)) =
        ∫ x in simplexCoordinateDomain k,
          pulled (finalPoint x) (i.removeNth base) := by
    intro i
    simpa [pulled, base, finalPoint] using
      integral_upperEndpoint_insert_eq_finalFace_reparametrized
        (F := F) (k := k) pulled i
  have hleft_reparam :
      (∑ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) •
          ∫ x in simplexCoordinateDomain k,
            pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
              (i.removeNth base)) =
      ∑ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) •
          ∫ x in simplexCoordinateDomain k,
            pulled (finalPoint x) (i.removeNth base) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hreparam i]
  rw [hleft_reparam]
  have hcell_one : (1 : WithTop ℕ∞) ≤ r :=
    one_le_of_two_le_smoothness hcell
  have hfinal_eq_face :
      finalPoint = simplexFaceCoordinateMap (Fin.last (k + 1)) := by
    funext x
    simp [finalPoint]
  have hfinal_cont : ContinuousOn finalPoint (simplexCoordinateDomain k) := by
    rw [hfinal_eq_face]
    have hfun :
        simplexFaceCoordinateMap (Fin.last (k + 1)) =
          fun y : Fin k → ℝ =>
            simplexFaceCoordinateLinearMap (Fin.last (k + 1)) y +
              simplexCoordinateOfBarycentric (k + 1)
                (simplexAmbientMap (Fin.last (k + 1)).succAbove
                  (Pi.single (Fin.last k) (1 : ℝ))) := by
      funext y
      exact simplexFaceCoordinateMap_eq_linear_add_const (Fin.last (k + 1)) y
    rw [hfun]
    exact ((simplexFaceCoordinateLinearMap (Fin.last (k + 1))).continuous.add
      continuous_const).continuousOn
  have hfinal_maps :
      MapsTo finalPoint (simplexCoordinateDomain k)
        (simplexCoordinateDomain (k + 1)) := by
    intro x hx
    rw [hfinal_eq_face]
    exact simplexFaceCoordinateMap_mem (Fin.last (k + 1)) hx
  have hintegrable_final :
      ∀ v : Fin k → (Fin (k + 1) → ℝ),
        IntegrableOn (fun x : Fin k → ℝ => pulled (finalPoint x) v)
          (simplexCoordinateDomain k) := by
    intro v
    have hcont_ambient :
        ContinuousOn
          (fun y : Fin (k + 1) → ℝ => pulled y v)
          (simplexCoordinateDomain (k + 1)) := by
      simpa [pulled, form0] using
        continuousOn_simplexPullbackFormAlongUsingExtension_eval
          (I := I) (F := F) (m := k + 1) (k := k)
          hcell_one form0 σ v
    have hcont :
        ContinuousOn (fun x : Fin k → ℝ => pulled (finalPoint x) v)
          (simplexCoordinateDomain k) :=
      hcont_ambient.comp hfinal_cont hfinal_maps
    exact hcont.integrableOn_compact (isCompact_simplexCoordinateDomain k)
  let signedFaceTerm : Fin (k + 1) → (Fin k → ℝ) → F :=
    fun i x ↦ ((-1 : ℤ) ^ (i : ℕ)) •
      pulled (finalPoint x) (i.removeNth base)
  have hintegrable_signed :
      ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
        Integrable (signedFaceTerm i) (volume.restrict (simplexCoordinateDomain k)) := by
    intro i hi
    have hbase :
        Integrable (fun x : Fin k → ℝ =>
          pulled (finalPoint x) (i.removeNth base))
          (volume.restrict (simplexCoordinateDomain k)) :=
      hintegrable_final (i.removeNth base)
    rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ (i : ℕ)) with h | h
    · have hInt : ((-1 : ℤ) ^ (i : ℕ)) = 1 := by
        change ((((-1 : ℤˣ) : ℤ) ^ (i : ℕ)) = 1)
        exact congrArg (fun u : ℤˣ => (u : ℤ)) h
      simpa [signedFaceTerm, hInt] using hbase
    · have hInt : ((-1 : ℤ) ^ (i : ℕ)) = -1 := by
        change ((((-1 : ℤˣ) : ℤ) ^ (i : ℕ)) = -1)
        exact congrArg (fun u : ℤˣ => (u : ℤ)) h
      simpa [signedFaceTerm, hInt] using hbase.neg
  have hsum_integral :
      (∑ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) •
          ∫ x in simplexCoordinateDomain k,
            pulled (finalPoint x) (i.removeNth base)) =
        ∫ x in simplexCoordinateDomain k,
          ∑ i : Fin (k + 1),
            ((-1 : ℤ) ^ (i : ℕ)) •
              pulled (finalPoint x) (i.removeNth base) := by
    rw [show (∫ x in simplexCoordinateDomain k,
          ∑ i : Fin (k + 1),
            ((-1 : ℤ) ^ (i : ℕ)) •
              pulled (finalPoint x) (i.removeNth base)) =
        ∑ i : Fin (k + 1),
          ∫ x in simplexCoordinateDomain k,
            ((-1 : ℤ) ^ (i : ℕ)) •
              pulled (finalPoint x) (i.removeNth base) by
      simpa [signedFaceTerm] using
        MeasureTheory.integral_finsetSum
          (μ := volume.restrict (simplexCoordinateDomain k))
          (s := (Finset.univ : Finset (Fin (k + 1))))
          (f := signedFaceTerm) hintegrable_signed]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [integral_negOnePow_zsmul
      (μ := volume.restrict (simplexCoordinateDomain k))
      (n := (i : ℕ))
      (f := fun x : Fin k → ℝ =>
        pulled (finalPoint x) (i.removeNth base))]
  rw [hsum_integral]
  have hpoint :
      EqOn
        (fun x : Fin k → ℝ =>
          ∑ i : Fin (k + 1),
            ((-1 : ℤ) ^ (i : ℕ)) •
              pulled (finalPoint x) (i.removeNth base))
        (fun x : Fin k → ℝ =>
          ((-1 : ℤ) ^ k) • pulled (finalPoint x) finalBasis)
        (simplexCoordinateDomain k) := by
    intro x hx
    simpa [base, finalBasis] using
      continuousAlternatingMap_boundaryBasis_eq_finalFaceBasis
        (F := F) (k := k) (pulled (finalPoint x))
  rw [setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) hpoint]
  rw [integral_negOnePow_zsmul
    (μ := volume.restrict (simplexCoordinateDomain k))
    (n := k)
    (f := fun x : Fin k → ℝ => pulled (finalPoint x) finalBasis)]

/--
The affine-simplex FTC and endpoint-collapse calculation needed for Stokes.

This is the remaining analytic/geometric leaf: integrate the displayed coordinate
derivatives over the simplex, use one-dimensional FTC in each coordinate, identify
the lower endpoints with the non-final coordinate faces, and collapse the upper
endpoints to the final face using alternation.
-/
theorem integral_simplexPullbackFormAlong_expandedInterior_eq_boundaryEndpointFormula
    [IsManifold I ∞ M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
      (((-1 : ℤ) ^ (k + 1)) •
        (let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
         let pulled :
            (Fin (k + 1) → ℝ) →
              (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
          simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            σ.extension
         let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
          fun j ↦ Pi.single j (1 : ℝ)
         ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            (∑ i : Fin k,
              ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
                (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                  (base i.castSucc))
                  (i.castSucc.removeNth base)) +
              ((-1 : ℤ) ^ k) •
                (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                  (Pi.single (Fin.last k) (1 : ℝ)))
                  (simplexCoordinateSliceBasisWithoutLast k))) =
        (let pulled :
            (Fin (k + 1) → ℝ) →
              (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
          simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            σ.extension
        let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
          fun j ↦ Pi.single j (1 : ℝ)
        (∑ i : Fin (k + 1),
          ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
            (((-1 : ℤ) ^ k) •
              ∫ x in simplexCoordinateDomain k,
                pulled (simplexCoordinateInsertMap i x 0)
                  (i.removeNth base))) +
          ((-1 : ℤ) ^ (k + 1)) •
            (((-1 : ℤ) ^ k) •
              ∫ x in simplexCoordinateDomain k,
                pulled
                  (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i))
                  (fun j : Fin k =>
                    Pi.single j.castSucc (1 : ℝ) -
                      Pi.single (Fin.last k) (1 : ℝ)))) := by
  classical
  let form0 : ContinuousDifferentialForm (I := I) (M := M) (F := F) k :=
    DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega
  let pulled :
      (Fin (k + 1) → ℝ) →
        (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := k + 1) (k := k) form0 σ.extension
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  let U : Fin (k + 1) → F := fun i =>
    ∫ x in simplexCoordinateDomain k,
      pulled (simplexCoordinateInsertMap i x (1 - ∑ j : Fin k, x j))
        (i.removeNth base)
  let L : Fin (k + 1) → F := fun i =>
    ∫ x in simplexCoordinateDomain k,
      pulled (simplexCoordinateInsertMap i x 0)
        (i.removeNth base)
  let Final : F :=
    ∫ x in simplexCoordinateDomain k,
      pulled
        (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i))
        (fun j : Fin k =>
          Pi.single j.castSucc (1 : ℝ) - Pi.single (Fin.last k) (1 : ℝ))
  have hendpoint :
      (let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
       let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k) form0 σ.extension
       let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
       ∫ x in simplexCoordinateDomain k,
        ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
          (∑ i : Fin k,
            ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
              (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                (base i.castSucc))
                (i.castSucc.removeNth base)) +
            ((-1 : ℤ) ^ k) •
              (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                (Pi.single (Fin.last k) (1 : ℝ)))
                (simplexCoordinateSliceBasisWithoutLast k)) =
        ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • (U i - L i) := by
    simpa [form0, pulled, base, U, L] using
      integral_simplexPullbackFormAlong_expandedInterior_eq_endpointAlternatingSum
        (I := I) (F := F) hcell omega σ
  have hupper : (∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • U i) =
      ((-1 : ℤ) ^ k) • Final := by
    simpa [form0, pulled, base, U, Final] using
      simplexPullbackFormAlong_upperEndpointAlternatingIntegral_eq_finalFace
        (I := I) (F := F) hcell omega σ
  have halg :=
    simplexEndpointAlternatingSum_with_upperCollapse
      (k := k) (U := U) (L := L) (Final := Final) hupper
  calc
    (((-1 : ℤ) ^ (k + 1)) •
        (let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
         let pulled :
            (Fin (k + 1) → ℝ) →
              (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
          simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k) form0 σ.extension
         let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
          fun j ↦ Pi.single j (1 : ℝ)
         ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            (∑ i : Fin k,
              ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
                (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                  (base i.castSucc))
                  (i.castSucc.removeNth base)) +
              ((-1 : ℤ) ^ k) •
                (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                  (Pi.single (Fin.last k) (1 : ℝ)))
                  (simplexCoordinateSliceBasisWithoutLast k))) =
      ((-1 : ℤ) ^ (k + 1)) •
        (∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) • (U i - L i)) := by
        rw [hendpoint]
    _ =
        (∑ i : Fin (k + 1),
          ((-1 : ℤ) ^ (i.castSucc : ℕ)) • (((-1 : ℤ) ^ k) • L i)) +
        ((-1 : ℤ) ^ (k + 1)) • (((-1 : ℤ) ^ k) • Final) := halg
    _ =
      (let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k) form0 σ.extension
       let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
       (∑ i : Fin (k + 1),
          ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
            (((-1 : ℤ) ^ k) •
              ∫ x in simplexCoordinateDomain k,
                pulled (simplexCoordinateInsertMap i x 0)
                  (i.removeNth base))) +
          ((-1 : ℤ) ^ (k + 1)) •
            (((-1 : ℤ) ^ k) •
              ∫ x in simplexCoordinateDomain k,
                pulled
                  (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i))
                  (fun j : Fin k =>
                    Pi.single j.castSucc (1 : ℝ) -
                      Pi.single (Fin.last k) (1 : ℝ)))) := by
        rfl

/--
The remaining affine-simplex calculus identity after Fubini and expansion of the exterior
derivative.  The lateral terms are the integration-by-parts contributions from the first `k`
coordinates, while the final displayed term is the last-coordinate FTC contribution.
-/
theorem integral_simplexPullbackFormAlong_expandedBoundary_eq_expandedInterior
    [IsManifold I ∞ M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
    (∑ i : Fin (k + 2),
        ((-1 : ℤ) ^ (i : ℕ)) •
          integrateSimplexByPullback (I := I) (F := F)
            (one_le_of_two_le_smoothness hcell)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            (ContMDiffSingularSimplex.face (I := I) σ i)) =
      ((-1 : ℤ) ^ (k + 1)) •
      let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
      let pulled :
          (Fin (k + 1) → ℝ) →
            (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
        simplexPullbackFormAlongUsingExtension (I := I) (F := F)
          (m := k + 1) (k := k)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
          σ.extension
      let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
        fun j ↦ Pi.single j (1 : ℝ)
      ∫ x in simplexCoordinateDomain k,
        ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
          (∑ i : Fin k,
            ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
              (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                (base i.castSucc))
                (i.castSucc.removeNth base)) +
            ((-1 : ℤ) ^ k) •
              (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                (Pi.single (Fin.last k) (1 : ℝ)))
                (simplexCoordinateSliceBasisWithoutLast k) := by
  classical
  let form0 : ContinuousDifferentialForm (I := I) (M := M) (F := F) k :=
    DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega
  let pulled :
      (Fin (k + 1) → ℝ) →
        (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := k + 1) (k := k) form0 σ.extension
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  have hcast :
      (∑ i : Fin (k + 1),
          ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
            integrateSimplexByPullback (I := I) (F := F)
              (one_le_of_two_le_smoothness hcell) form0
              (ContMDiffSingularSimplex.face (I := I) σ i.castSucc)) =
        ∑ i : Fin (k + 1),
          ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
            (((-1 : ℤ) ^ k) •
              ∫ x in simplexCoordinateDomain k,
                pulled (simplexCoordinateInsertMap i x 0)
                  (i.removeNth base)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [integrateSimplexByPullback_castSucc_face_eq_insert_zero_integral
      (I := I) (F := F)
      (hcell := one_le_of_two_le_smoothness hcell)
      (form := form0) (σ := σ) i]
  have hlast :
      ((-1 : ℤ) ^ (Fin.last (k + 1) : ℕ)) •
          integrateSimplexByPullback (I := I) (F := F)
            (one_le_of_two_le_smoothness hcell) form0
            (ContMDiffSingularSimplex.face (I := I) σ (Fin.last (k + 1))) =
        ((-1 : ℤ) ^ (k + 1)) •
          (((-1 : ℤ) ^ k) •
            ∫ x in simplexCoordinateDomain k,
              pulled
                (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i))
                (fun j : Fin k =>
                  Pi.single j.castSucc (1 : ℝ) -
                    Pi.single (Fin.last k) (1 : ℝ))) := by
    rw [integrateSimplexByPullback_last_face_eq_slice_upper_integral
      (I := I) (F := F)
      (hcell := one_le_of_two_le_smoothness hcell)
      (form := form0) (σ := σ)]
    simp [pulled]
  have hboundary :
      (∑ i : Fin (k + 2),
          ((-1 : ℤ) ^ (i : ℕ)) •
            integrateSimplexByPullback (I := I) (F := F)
              (one_le_of_two_le_smoothness hcell) form0
              (ContMDiffSingularSimplex.face (I := I) σ i)) =
        (∑ i : Fin (k + 1),
          ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
            (((-1 : ℤ) ^ k) •
              ∫ x in simplexCoordinateDomain k,
                pulled (simplexCoordinateInsertMap i x 0)
                  (i.removeNth base))) +
          ((-1 : ℤ) ^ (k + 1)) •
            (((-1 : ℤ) ^ k) •
              ∫ x in simplexCoordinateDomain k,
                pulled
                  (simplexCoordinateSliceMap k x (1 - ∑ i : Fin k, x i))
                  (fun j : Fin k =>
                    Pi.single j.castSucc (1 : ℝ) -
                      Pi.single (Fin.last k) (1 : ℝ))) := by
    rw [Fin.sum_univ_castSucc]
    rw [hcast, hlast]
  have hinterior :=
    integral_simplexPullbackFormAlong_expandedInterior_eq_boundaryEndpointFormula
      (I := I) (F := F) hcell omega σ
  rw [hboundary]
  simpa [form0, pulled, base] using hinterior.symm

/--
Model-space Stokes theorem for the pullback of a degree `k` form to the affine
`(k+1)`-simplex.

The proof is the Fubini/FTC argument on simplex coordinates: slice the simplex by the last
coordinate, reduce to an iterated integral, and apply the fundamental theorem of calculus in the
inner integral.  The other faces are obtained by the usual alternating orientation bookkeeping.
-/
theorem integral_extDerivWithin_simplexPullbackFormAlong_eq_boundary
    [IsManifold I ∞ M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
    (∑ i : Fin (k + 2),
        ((-1 : ℤ) ^ (i : ℕ)) •
          integrateSimplexByPullback (I := I) (F := F)
            (one_le_of_two_le_smoothness hcell)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            (ContMDiffSingularSimplex.face (I := I) σ i)) =
      ((-1 : ℤ) ^ (k + 1)) •
      ∫ x in simplexCoordinateDomain (k + 1),
        extDerivWithin
          (simplexPullbackFormAlongUsingExtension (I := I) (F := F)
            (m := k + 1) (k := k)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            σ.extension)
          (simplexCoordinateDomain (k + 1)) x
          (fun j : Fin (k + 1) ↦ Pi.single j (1 : ℝ)) := by
  classical
  let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
  let pulled : (Fin (k + 1) → ℝ) →
      (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := k + 1) (k := k)
      (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
      σ.extension
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  let sliceTerm : Fin (k + 1) → (Fin k → ℝ) → ℝ → F :=
    fun i x t ↦
      ((-1 : ℤ) ^ (i : ℕ)) •
        (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t) (base i))
          (i.removeNth base)
  let lateralSliceTerms : (Fin k → ℝ) → ℝ → F :=
    fun x t ↦ ∑ i : Fin k, sliceTerm i.castSucc x t
  let verticalSliceTerm : (Fin k → ℝ) → ℝ → F :=
    fun x t ↦ sliceTerm (Fin.last k) x t
  have hverticalSliceTerm :
      ∀ (x : Fin k → ℝ) (t : ℝ),
        verticalSliceTerm x t =
          ((-1 : ℤ) ^ k) •
            (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
              (Pi.single (Fin.last k) (1 : ℝ)))
              (simplexCoordinateSliceBasisWithoutLast k) := by
    intro x t
    simp [verticalSliceTerm, sliceTerm, base, simplexCoordinateSliceBasisWithoutLast]
  have hcoeff_eq :
      EqOn
        (fun x : Fin (k + 1) → ℝ =>
          simplexPullbackCoefficient (I := I) (F := F)
            (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ x)
        (fun x : Fin (k + 1) → ℝ => extDerivWithin pulled D x base) D := by
    simpa [D, pulled, base] using
      simplexPullbackCoefficient_exteriorDerivative_eq_extDerivWithin_pullbackForm
        (I := I) (F := F) hcell omega σ
  have hcoeff_integrable :
      IntegrableOn
        (fun x : Fin (k + 1) → ℝ =>
          simplexPullbackCoefficient (I := I) (F := F)
            (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ x)
        D := by
    simpa [D] using
      integrableOn_simplexPullbackCoefficient
        (I := I) (F := F) (k := k + 1)
        (one_le_of_two_le_smoothness hcell)
        (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ
  have hrhs_integrable :
      IntegrableOn (fun x : Fin (k + 1) → ℝ => extDerivWithin pulled D x base) D := by
    exact hcoeff_integrable.congr_fun hcoeff_eq
      (by simpa [D] using measurableSet_simplexCoordinateDomain (k + 1))
  have hRHS_fubini :
      (∫ x in D, extDerivWithin pulled D x base) =
        ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            extDerivWithin pulled D (simplexCoordinateSliceMap k x t) base := by
    simpa [D] using
      integral_simplexCoordinateDomain_succ_eq_iterated
        (k := k)
        (f := fun x : Fin (k + 1) → ℝ => extDerivWithin pulled D x base)
        hrhs_integrable
  change
    (∑ i : Fin (k + 2),
        ((-1 : ℤ) ^ (i : ℕ)) •
          integrateSimplexByPullback (I := I) (F := F)
            (one_le_of_two_le_smoothness hcell)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            (ContMDiffSingularSimplex.face (I := I) σ i)) =
      ((-1 : ℤ) ^ (k + 1)) •
      ∫ x in D, extDerivWithin pulled D x base
  rw [hRHS_fubini]
  have hRHS_expand :
      (∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            extDerivWithin pulled D (simplexCoordinateSliceMap k x t) base) =
        ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            ∑ i : Fin (k + 1), sliceTerm i x t := by
    refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
    intro x hx
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    simpa [sliceTerm] using
      extDerivWithin_apply_fderivWithin
        (eta := pulled) (s := D) (x := simplexCoordinateSliceMap k x t)
        (v := base)
  rw [hRHS_expand]
  have hRHS_splitLast :
      (∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            ∑ i : Fin (k + 1), sliceTerm i x t) =
        ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            lateralSliceTerms x t + verticalSliceTerm x t := by
    refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
    intro x hx
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    simp [lateralSliceTerms, verticalSliceTerm, Fin.sum_univ_castSucc]
  rw [hRHS_splitLast]
  have hRHS_verticalFormula :
      (∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            lateralSliceTerms x t + verticalSliceTerm x t) =
        ∫ x in simplexCoordinateDomain k,
          ∫ t in Icc (0 : ℝ) (1 - ∑ i : Fin k, x i),
            lateralSliceTerms x t +
              ((-1 : ℤ) ^ k) •
                (fderivWithin ℝ pulled D (simplexCoordinateSliceMap k x t)
                  (Pi.single (Fin.last k) (1 : ℝ)))
                  (simplexCoordinateSliceBasisWithoutLast k) := by
    refine setIntegral_congr_fun (measurableSet_simplexCoordinateDomain k) ?_
    intro x hx
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    simpa using congrArg (fun y : F => lateralSliceTerms x t + y)
      (hverticalSliceTerm x t)
  rw [hRHS_verticalFormula]
  simpa [D, pulled, base, sliceTerm, lateralSliceTerms, verticalSliceTerm] using
    integral_simplexPullbackFormAlong_expandedBoundary_eq_expandedInterior
      (I := I) (F := F) hcell omega σ

/--
%%handwave
name:
  Stokes theorem on a simplex
statement:
  For a \(C^1\) degree \(k\) form and a \(C^2\) singular \((k+1)\)-simplex,
  the alternating sum of the integrals over the codimension-one faces is equal
  to the integral of the exterior derivative over the simplex.
proof:
  In affine coordinates, the model-space Stokes formula identifies the
  alternating face integral with the integral of the exterior derivative of
  the pulled-back form.  Naturality of exterior differentiation identifies
  that integrand with the pullback of \(d\omega\), and the orientation factors
  on the two coordinate integrals agree.
-/
theorem integrateSimplexByPullback_boundary_eq_exteriorDerivative
    [IsManifold I ∞ M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r) :
    (∑ i : Fin (k + 2),
        ((-1 : ℤ) ^ (i : ℕ)) •
          integrateSimplexByPullback (I := I) (F := F)
            (one_le_of_two_le_smoothness hcell)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            (ContMDiffSingularSimplex.face (I := I) σ i)) =
      integrateSimplexByPullback (I := I) (F := F)
        (one_le_of_two_le_smoothness hcell)
        (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ := by
  classical
  let D : Set (Fin (k + 1) → ℝ) := simplexCoordinateDomain (k + 1)
  let pulled :
      (Fin (k + 1) → ℝ) →
        (Fin (k + 1) → ℝ) [⋀^Fin k]→L[ℝ] F :=
    simplexPullbackFormAlongUsingExtension (I := I) (F := F)
      (m := k + 1) (k := k)
      (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
      σ.extension
  let base : Fin (k + 1) → (Fin (k + 1) → ℝ) :=
    fun j ↦ Pi.single j (1 : ℝ)
  have hmodel :
      (∑ i : Fin (k + 2),
          ((-1 : ℤ) ^ (i : ℕ)) •
            integrateSimplexByPullback (I := I) (F := F)
              (one_le_of_two_le_smoothness hcell)
              (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
              (ContMDiffSingularSimplex.face (I := I) σ i)) =
        ((-1 : ℤ) ^ (k + 1)) •
        ∫ x in D, extDerivWithin pulled D x base := by
    simpa [D, pulled, base] using
      integral_extDerivWithin_simplexPullbackFormAlong_eq_boundary
        (I := I) (F := F) hcell omega σ
  have hcoeff :
      (∫ x in D,
        simplexPullbackCoefficient (I := I) (F := F)
          (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ x) =
        ∫ x in D, extDerivWithin pulled D x base := by
    refine setIntegral_congr_fun (by simpa [D] using measurableSet_simplexCoordinateDomain (k + 1)) ?_
    intro x hx
    exact
      simplexPullbackCoefficient_exteriorDerivative_eq_extDerivWithin_pullbackForm
        (I := I) (F := F) hcell omega σ (by simpa [D] using hx)
  calc
    (∑ i : Fin (k + 2),
        ((-1 : ℤ) ^ (i : ℕ)) •
          integrateSimplexByPullback (I := I) (F := F)
            (one_le_of_two_le_smoothness hcell)
            (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
            (ContMDiffSingularSimplex.face (I := I) σ i))
        = ((-1 : ℤ) ^ (k + 1)) •
            ∫ x in D, extDerivWithin pulled D x base := hmodel
    _ = ((-1 : ℤ) ^ (k + 1)) •
          ∫ x in D,
          simplexPullbackCoefficient (I := I) (F := F)
            (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ x := by
          exact congrArg (fun y : F => ((-1 : ℤ) ^ (k + 1)) • y) hcoeff.symm
    _ = integrateSimplexByPullback (I := I) (F := F)
          (one_le_of_two_le_smoothness hcell)
          (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) σ := by
          simp [D, integrateSimplexByPullback, simplexPullbackCoefficient]

/--
%%handwave
name:
  Simplex integration theory
statement:
  A simplex integration theory assigns an integral to every continuous degree
  \(k\) form over every \(C^1\) singular \(k\)-simplex, and records the
  oriented change-of-variables rule for vertex permutations.
-/
structure SimplexIntegrationTheory where
  /-- The integral of a continuous form over a singular simplex. -/
  simplexIntegral :
    {k : ℕ} → {r : WithTop ℕ∞} → (1 : WithTop ℕ∞) ≤ r →
      ContinuousDifferentialForm (I := I) (M := M) (F := F) k →
      ContMDiffSingularSimplex (I := I) (M := M) k r → F
  /-- Oriented invariance under permutation of the vertices of the source simplex. -/
  map_reparametrizeVertexPermutation :
    ∀ {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
      (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
      (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
      (p : Equiv.Perm (Fin (k + 1))),
      simplexIntegral hcell form (σ.reparametrizeVertexPermutation p) =
        (((Equiv.Perm.sign p : ℤˣ) : ℤ) • simplexIntegral hcell form σ)

/--
%%handwave
name:
  Pullback simplex integration theory
statement:
  Pulling a form back to the standard simplex and integrating its scalar
  coefficient gives a simplex integration theory.
-/
noncomputable def pullbackSimplexIntegrationTheory :
    SimplexIntegrationTheory (I := I) (M := M) (F := F) where
  simplexIntegral := fun {k} {r} hcell form σ ↦
    integrateSimplexByPullback (I := I) (F := F) hcell form σ
  map_reparametrizeVertexPermutation := by
    intro k r hcell form σ p
    exact integrateSimplexByPullback_reparametrizeVertexPermutation
      (I := I) (F := F) hcell form σ p

/--
%%handwave
name:
  Integral over a simplex
statement:
  Given a simplex integration theory, the integral over a simplex is its
  assigned value on that form and parameterized simplex.
-/
noncomputable def integrateSimplex
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) : F :=
  theory.simplexIntegral hcell form σ

/--
%%handwave
name:
  Change of vertices in a simplex integral
statement:
  Permuting the vertices of the parameter simplex changes the integral of a
  differential form by the sign of the permutation.
-/
theorem integrateSimplex_reparametrizeVertexPermutation
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (p : Equiv.Perm (Fin (k + 1))) :
    integrateSimplex (I := I) (F := F) theory hcell form
        (σ.reparametrizeVertexPermutation p) =
      (((Equiv.Perm.sign p : ℤˣ) : ℤ) •
        integrateSimplex (I := I) (F := F) theory hcell form σ) :=
  theory.map_reparametrizeVertexPermutation hcell form σ p

/--
%%handwave
name:
  Integral over a singular chain
statement:
  The integral of a form over a chain is the finite signed sum of its
  integrals over the parameterized simplices appearing in the chain.
-/
noncomputable def integrateChainHom
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k) :
    SingularChain (I := I) (M := M) k r →ₗ[ℤ] F :=
  Finsupp.linearCombination ℤ fun σ ↦
    integrateSimplex (I := I) (F := F) theory hcell form σ

/-- The value of the chain integral. -/
noncomputable def integrateChain
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (c : SingularChain (I := I) (M := M) k r) : F :=
  integrateChainHom (I := I) (F := F) theory hcell form c

@[simp]
theorem integrateChain_single
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (σ : ContMDiffSingularSimplex (I := I) (M := M) k r) (n : ℤ) :
    integrateChain (I := I) (F := F) theory hcell form (Finsupp.single σ n) =
      n • integrateSimplex (I := I) (F := F) theory hcell form σ := by
  simp [integrateChain, integrateChainHom, Finsupp.linearCombination_single]

/--
%%handwave
name:
  Stokes theorem for singular chains
statement:
  For a \(C^1\) degree \(k\) form and a \(C^2\) singular \((k+1)\)-chain, the
  integral over the boundary is equal to the integral of the exterior
  derivative over the chain.
proof:
  The assertion is linear in the chain, so it suffices to check a single simplex.  On a generator, the boundary expands as the alternating sum of faces, and the result is exactly [the alternating sum of the integrals over the faces is equal to the integral of the exterior derivative over the simplex](lean:JJMath.Manifold.integrateSimplexByPullback_boundary_eq_exteriorDerivative).
-/
theorem integrateChain_boundary_eq_integrateChain_exteriorDerivative
    [IsManifold I ∞ M] [CompleteSpace F]
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (2 : WithTop ℕ∞) ≤ r)
    (omega : C1DifferentialForm (I := I) (M := M) (F := F) k)
    (c : SingularChain (I := I) (M := M) (k + 1) r) :
    integrateChain (I := I) (F := F) (pullbackSimplexIntegrationTheory (I := I) (F := F))
        (one_le_of_two_le_smoothness hcell)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)
        (boundary (I := I) c) =
      integrateChain (I := I) (F := F) (pullbackSimplexIntegrationTheory (I := I) (F := F))
        (one_le_of_two_le_smoothness hcell)
        (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) c := by
  classical
  change
    ((integrateChainHom (I := I) (F := F)
        (pullbackSimplexIntegrationTheory (I := I) (F := F))
        (one_le_of_two_le_smoothness hcell)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := F) (n := k) omega)).comp
      (boundary (I := I))) c =
    integrateChainHom (I := I) (F := F)
      (pullbackSimplexIntegrationTheory (I := I) (F := F))
      (one_le_of_two_le_smoothness hcell)
      (exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) omega) c
  induction c using Finsupp.induction_linear with
  | zero =>
      simp
  | add c d hc hd =>
      simp [map_add, hc, hd]
  | single σ n =>
      have hstokes :=
        integrateSimplexByPullback_boundary_eq_exteriorDerivative
          (I := I) (F := F) hcell omega σ
      simpa [integrateChainHom, boundary, integrateSimplex, pullbackSimplexIntegrationTheory,
        Finsupp.linearCombination_single] using congrArg (fun x : F => n • x) hstokes

/--
%%handwave
name:
  Oriented reparameterization relation
statement:
  Chains are identified when a simplex is reparameterized by a permutation of
  the vertices, with the sign of the permutation recording the induced change
  of orientation.
-/
def reparametrizationGenerators
    {k : ℕ} {r : WithTop ℕ∞} :
    Set (SingularChain (I := I) (M := M) k r) :=
  {g | ∃ (σ : ContMDiffSingularSimplex (I := I) (M := M) k r)
      (p : Equiv.Perm (Fin (k + 1))),
      g =
        Finsupp.single (σ.reparametrizeVertexPermutation p) (1 : ℤ) -
          Finsupp.single σ (((Equiv.Perm.sign p : ℤˣ) : ℤ))}

/-- The subgroup of chains generated by oriented vertex reparameterizations. -/
def reparametrizationSubmodule
    {k : ℕ} {r : WithTop ℕ∞} :
    Submodule ℤ (SingularChain (I := I) (M := M) k r) :=
  Submodule.span ℤ (reparametrizationGenerators (I := I) (M := M) (k := k) (r := r))

/--
%%handwave
name:
  Equivalent singular chains
statement:
  Two chains are equivalent when their difference is generated by oriented
  changes of the simplex parameters.
-/
def ChainEquivalent
    {k : ℕ} {r : WithTop ℕ∞}
    (c d : SingularChain (I := I) (M := M) k r) : Prop :=
  c - d ∈ reparametrizationSubmodule (I := I) (M := M) (k := k) (r := r)

theorem chainEquivalent_refl
    {k : ℕ} {r : WithTop ℕ∞}
    (c : SingularChain (I := I) (M := M) k r) :
    ChainEquivalent (I := I) c c := by
  simp [ChainEquivalent]

theorem chainEquivalent_symm
    {k : ℕ} {r : WithTop ℕ∞}
    {c d : SingularChain (I := I) (M := M) k r}
    (h : ChainEquivalent (I := I) c d) :
    ChainEquivalent (I := I) d c := by
  simpa [ChainEquivalent, neg_sub] using
    (reparametrizationSubmodule (I := I) (M := M) (k := k) (r := r)).neg_mem h

theorem chainEquivalent_trans
    {k : ℕ} {r : WithTop ℕ∞}
    {c d e : SingularChain (I := I) (M := M) k r}
    (hcd : ChainEquivalent (I := I) c d)
    (hde : ChainEquivalent (I := I) d e) :
    ChainEquivalent (I := I) c e := by
  let S := reparametrizationSubmodule (I := I) (M := M) (k := k) (r := r)
  have hsum : (c - d) + (d - e) ∈ S := S.add_mem hcd hde
  simpa [ChainEquivalent, S, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

instance chainEquivalentSetoid
    {k : ℕ} {r : WithTop ℕ∞} :
    Setoid (SingularChain (I := I) (M := M) k r) where
  r := ChainEquivalent (I := I)
  iseqv :=
    ⟨fun c ↦ chainEquivalent_refl (I := I) c,
      fun {c d} h ↦ chainEquivalent_symm (I := I) (c := c) (d := d) h,
      fun {c d e} hcd hde ↦
        chainEquivalent_trans (I := I) (c := c) (d := d) (e := e) hcd hde⟩

/-- Geometric chains are chains modulo oriented vertex reparameterization. -/
abbrev GeometricChain (k : ℕ) (r : WithTop ℕ∞) :=
  SingularChain (I := I) (M := M) k r ⧸
    reparametrizationSubmodule (I := I) (M := M) (k := k) (r := r)

theorem integrateChainHom_mem_ker_of_mem_reparametrizationSubmodule
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    {c : SingularChain (I := I) (M := M) k r}
    (hc : c ∈ reparametrizationSubmodule (I := I) (M := M) (k := k) (r := r)) :
    c ∈ LinearMap.ker (integrateChainHom (I := I) (F := F) theory hcell form) := by
  refine
    (Submodule.span_le.mpr ?_) hc
  intro g hg
  rcases hg with ⟨σ, p, rfl⟩
  change
    integrateChainHom (I := I) (F := F) theory hcell form
        (Finsupp.single (σ.reparametrizeVertexPermutation p) (1 : ℤ) -
          Finsupp.single σ (((Equiv.Perm.sign p : ℤˣ) : ℤ))) = 0
  rw [map_sub]
  simp [integrateChainHom, Finsupp.linearCombination_single,
    integrateSimplex_reparametrizeVertexPermutation]

/--
%%handwave
name:
  Chain integration is independent of representative
statement:
  If two chains differ only by oriented changes of the simplex parameters,
  then every continuous form has the same integral over both chains.
proof:
  The difference of the two chains lies in the span of the oriented reparameterization relations.  Each generator has integral zero by [permuting the vertices of the parameter simplex changes the integral by the sign of the permutation](lean:JJMath.Manifold.integrateSimplex_reparametrizeVertexPermutation), and linearity gives the result.
-/
theorem integrateChain_eq_of_chainEquivalent
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    {c d : SingularChain (I := I) (M := M) k r}
    (h : ChainEquivalent (I := I) c d) :
    integrateChain (I := I) (F := F) theory hcell form c =
      integrateChain (I := I) (F := F) theory hcell form d := by
  have hker :=
    integrateChainHom_mem_ker_of_mem_reparametrizationSubmodule
      (I := I) (F := F) theory hcell form h
  rw [LinearMap.mem_ker] at hker
  have hsub :
      integrateChainHom (I := I) (F := F) theory hcell form c -
          integrateChainHom (I := I) (F := F) theory hcell form d = 0 := by
    simpa [map_sub] using hker
  exact sub_eq_zero.mp hsub

/-- The chain integral descends to geometric chains. -/
noncomputable def integrateGeometricChain
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k) :
    GeometricChain (I := I) (M := M) k r →ₗ[ℤ] F :=
  (reparametrizationSubmodule (I := I) (M := M) (k := k) (r := r)).liftQ
    (integrateChainHom (I := I) (F := F) theory hcell form) <| by
      intro c hc
      exact
        integrateChainHom_mem_ker_of_mem_reparametrizationSubmodule
          (I := I) (F := F) theory hcell form hc

@[simp]
theorem integrateGeometricChain_mk
    (theory : SimplexIntegrationTheory (I := I) (M := M) (F := F))
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (form : ContinuousDifferentialForm (I := I) (M := M) (F := F) k)
    (c : SingularChain (I := I) (M := M) k r) :
    integrateGeometricChain (I := I) (F := F) theory hcell form
        (Submodule.Quotient.mk c : GeometricChain (I := I) (M := M) k r) =
      integrateChain (I := I) (F := F) theory hcell form c := by
  simpa [integrateGeometricChain, integrateChain] using
    (Submodule.liftQ_apply
      (p := reparametrizationSubmodule (I := I) (M := M) (k := k) (r := r))
      (f := integrateChainHom (I := I) (F := F) theory hcell form)
      (x := c))

end

end Manifold
end JJMath
