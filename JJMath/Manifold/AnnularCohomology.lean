import JJMath.Manifold.AnnularPeriod
import JJMath.Manifold.DeRhamComparison.Base

/-!
# Cohomology of punctured annular charts

This file realizes the standard cylinder with one vertical line removed as a
convex model open.  In particular, the punctured cylinder has vanishing first
de Rham cohomology.  These charts are the local input for the two-chart
Mayer--Vietoris computation of annular cohomology.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

/-- The product of stereographic projection away from `v` with the real identity chart. -/
def annularPunctureChart (v : Circle) :
    OpenPartialHomeomorph (Circle × ℝ)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) :=
  (stereographic' 1 v).prod (OpenPartialHomeomorph.refl ℝ)

/-- The standard cylinder with the vertical line through `v` removed. -/
def annularPunctureOpen (v : Circle) :
    TopologicalSpace.Opens (Circle × ℝ) :=
  ⟨(annularPunctureChart v).source, (annularPunctureChart v).open_source⟩

theorem annularPunctureChart_mem_atlas (v : Circle) :
    annularPunctureChart v ∈
      atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) (Circle × ℝ) := by
  change (stereographic' 1 v).prod (OpenPartialHomeomorph.refl ℝ) ∈
    Set.image2 OpenPartialHomeomorph.prod
      (atlas (EuclideanSpace ℝ (Fin 1)) Circle) (atlas ℝ ℝ)
  exact ⟨stereographic' 1 v, ⟨v, rfl⟩,
    OpenPartialHomeomorph.refl ℝ, by simp, rfl⟩

/-- A once-punctured cylinder is diffeomorphic to a nonempty convex open plane. -/
theorem annularPuncture_diffeomorphic_convex (v : Circle) :
    ∃ V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1) × ℝ),
      Convex ℝ (V : Set (EuclideanSpace ℝ (Fin 1) × ℝ)) ∧
      (V : Set (EuclideanSpace ℝ (Fin 1) × ℝ)).Nonempty ∧
      Nonempty
        (annularPunctureOpen v ≃ₘ⟮AnnularCylinderModel,
          𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ)⟯ V) := by
  let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1) × ℝ) := ⊤
  refine ⟨V, convex_univ, Set.univ_nonempty, ?_⟩
  apply deRham_boundarylessExtendedChart_restriction_diffeomorph
    AnnularCylinderModel
    (e := annularPunctureChart v)
    (annularPunctureChart_mem_atlas v)
  · simpa [annularPunctureOpen, V, deRham_boundarylessExtendedChart] using
      ((annularPunctureChart v).extend_source (I := AnnularCylinderModel)).symm
  · intro y hy
    change y ∈ ((annularPunctureChart v).extend AnnularCylinderModel).target
    rw [OpenPartialHomeomorph.extend_target]
    simp [annularPunctureChart, AnnularCylinderModel]
    exact Set.mem_univ y

/-- The first de Rham cohomology of a once-punctured cylinder vanishes. -/
theorem annularPuncture_deRhamH1_subsingleton (v : Circle) :
    Subsingleton
      (DeRhamCohomology (I := AnnularCylinderModel)
        (M := annularPunctureOpen v) (A := ℝ) 1) := by
  rcases annularPuncture_diffeomorphic_convex v with ⟨V, hconvex, hne, ⟨phi⟩⟩
  exact deRhamCohomology_subsingleton_of_diffeomorphic
    AnnularCylinderModel
    (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ)) phi 1
    (deRham_poincareLemma_convex_open V hconvex hne 0)

end

end Manifold
end JJMath
