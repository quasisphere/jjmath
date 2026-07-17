import JJMath.Manifold.AnnularPeriod
import JJMath.Uniformization.SmoothChainConnectivity

/-!
# The annular-period obstruction on a smooth surface

This file combines the compactly supported annular one-form with smooth-chain
connectivity.  If the exterior of the compact transition band is connected,
its two transverse endpoints can be joined by a smooth return chain.  The
resulting cycle has period one, so first de Rham cohomology is nontrivial.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

open JJMath.Uniformization

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/-- A point in the exterior of an annular transition core, specified in collar
coordinates. -/
noncomputable def annularCollarExteriorPoint
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) (t : ℝ) (ht : t ∉ Set.Icc (-1 : ℝ) 1) :
    annularCollarExteriorOpen SurfaceRealModel U phi := by
  refine ⟨((phi.symm (z, t) : U) : X), ?_⟩
  change ((phi.symm (z, t) : U) : X) ∉
    annularCollarCore SurfaceRealModel U phi
  rintro ⟨p, hp, hp_eq⟩
  have hsub : phi.symm p = phi.symm (z, t) := by
    apply Subtype.ext
    exact hp_eq
  have : p = (z, t) := phi.symm.injective hsub
  subst p
  exact ht hp

@[simp]
theorem annularCollarExteriorPoint_val
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) (t : ℝ) (ht : t ∉ Set.Icc (-1 : ℝ) 1) :
    ((annularCollarExteriorPoint U phi z t ht :
      annularCollarExteriorOpen SurfaceRealModel U phi) : X) =
      ((phi.symm (z, t) : U) : X) :=
  rfl

theorem point_openInclusion_annularCollarExteriorPoint
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) (t : ℝ) (ht : t ∉ Set.Icc (-1 : ℝ) 1) :
    (ContMDiffSingularSimplex.point (I := SurfaceRealModel)
        (r := ∞) (annularCollarExteriorPoint U phi z t ht)).openInclusion
      (I := SurfaceRealModel)
      (annularCollarExteriorOpen SurfaceRealModel U phi) =
    ContMDiffSingularSimplex.point (I := SurfaceRealModel)
      (r := ∞) (((phi.symm (z, t) : U) : X)) := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  rfl

/-- The boundary of a transverse collar crossing is its positive-side
endpoint minus its negative-side endpoint. -/
theorem boundary_annularCollarTransverseSimplex_single
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) (a b : ℝ) :
    boundary (I := SurfaceRealModel)
      (Finsupp.single
        ((annularCollarTransverseSimplex SurfaceRealModel U phi z a b).openInclusion
          (I := SurfaceRealModel) U) (1 : ℤ)) =
      Finsupp.single
        (ContMDiffSingularSimplex.point (I := SurfaceRealModel)
          (((phi.symm (z, b) : U) : X))) (1 : ℤ) -
      Finsupp.single
        (ContMDiffSingularSimplex.point (I := SurfaceRealModel)
          (((phi.symm (z, a) : U) : X))) (1 : ℤ) := by
  have hface_zero :
      ((annularCollarTransverseSimplex SurfaceRealModel U phi z a b).openInclusion
        (I := SurfaceRealModel) U).face 0 =
      ContMDiffSingularSimplex.point (I := SurfaceRealModel)
        (((phi.symm (z, b) : U) : X)) := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    rw [ContMDiffSingularSimplex.openInclusion_face]
    change (((annularCollarTransverseSimplex SurfaceRealModel U phi z a b).face 0 q : U) : X) = _
    simp
  have hface_one :
      ((annularCollarTransverseSimplex SurfaceRealModel U phi z a b).openInclusion
        (I := SurfaceRealModel) U).face 1 =
      ContMDiffSingularSimplex.point (I := SurfaceRealModel)
        (((phi.symm (z, a) : U) : X)) := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    rw [ContMDiffSingularSimplex.openInclusion_face]
    change (((annularCollarTransverseSimplex SurfaceRealModel U phi z a b).face 1 q : U) : X) = _
    simp
  simp [boundary, Finsupp.linearCombination_single, Fin.sum_univ_two,
    hface_zero, hface_one, sub_eq_add_neg]

/-- If the exterior of the compact middle of an annular collar is connected,
the annular period form detects nontrivial first de Rham cohomology. -/
theorem not_subsingleton_deRhamH1_of_annularCollar_exterior_connected
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) {a b : ℝ} (ha : a < -1) (hb : 1 < b)
    [ConnectedSpace (annularCollarExteriorOpen SurfaceRealModel U phi)] :
    ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1) := by
  have ha_out : a ∉ Set.Icc (-1 : ℝ) 1 := by
    intro ha_mem
    linarith [ha_mem.1]
  have hb_out : b ∉ Set.Icc (-1 : ℝ) 1 := by
    intro hb_mem
    linarith [hb_mem.2]
  let xminus := annularCollarExteriorPoint U phi z a ha_out
  let xplus := annularCollarExteriorPoint U phi z b hb_out
  rcases SmoothChainConnectivity.smoothChainJoined_all xplus xminus with
    ⟨returning, hreturning⟩
  apply not_subsingleton_deRhamH1_of_annularCollar_return_chain_boundary
    SurfaceRealModel U phi z ha.le hb.le returning
  rw [hreturning, sub_eq_add_neg, SingularChain.openInclusion_add]
  rw [show -Finsupp.single
      (ContMDiffSingularSimplex.point (I := SurfaceRealModel) xplus) (1 : ℤ) =
        (-1 : ℤ) • Finsupp.single
          (ContMDiffSingularSimplex.point (I := SurfaceRealModel) xplus) (1 : ℤ) by
      simp]
  rw [SingularChain.openInclusion_zsmul]
  simp only [SingularChain.openInclusion_single]
  rw [point_openInclusion_annularCollarExteriorPoint U phi z a ha_out]
  rw [point_openInclusion_annularCollarExteriorPoint U phi z b hb_out]
  rw [boundary_annularCollarTransverseSimplex_single U phi z a b]
  abel

/-- Vanishing first de Rham cohomology forces the exterior of the compact
middle of every annular collar to be disconnected. -/
theorem annularCollar_exterior_not_connected_of_deRhamH1_subsingleton
    (hH1 : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1))
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) :
    ¬ ConnectedSpace
      (annularCollarExteriorOpen SurfaceRealModel U phi) := by
  intro hconnected
  letI : ConnectedSpace
      (annularCollarExteriorOpen SurfaceRealModel U phi) := hconnected
  exact not_subsingleton_deRhamH1_of_annularCollar_exterior_connected
    U phi z (a := -2) (b := 2) (by norm_num) (by norm_num) hH1

end
end Manifold
end JJMath
