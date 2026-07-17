import JJMath.Manifold.ProperLineThom
import JJMath.Uniformization.SmoothChainConnectivity

/-!
# Proper-line period obstructions on smooth surfaces

This file combines the transverse Thom form of a proper line tube with
smooth-chain connectivity.  If deleting the closed middle strip leaves a
connected surface, its two transverse endpoints can be joined outside the
strip.  Closing the transverse crossing by that return chain gives a cycle
of period one.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

open JJMath.Uniformization

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/-- A point in the exterior of a proper-line transition core, specified in
tube coordinates. -/
noncomputable def properLineTubeExteriorPoint
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore SurfaceRealModel U phi))
    (s t : ℝ) (ht : t ∉ Set.Icc (-1 : ℝ) 1) :
    properLineTubeExteriorOpen SurfaceRealModel U phi hcore := by
  refine ⟨((phi.symm (s, t) : U) : X), ?_⟩
  change ((phi.symm (s, t) : U) : X) ∉
    properLineTubeCore SurfaceRealModel U phi
  rintro ⟨p, hp, hp_eq⟩
  have hsub : phi.symm p = phi.symm (s, t) := by
    apply Subtype.ext
    exact hp_eq
  have : p = (s, t) := phi.symm.injective hsub
  subst p
  exact ht hp

@[simp]
theorem properLineTubeExteriorPoint_val
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore SurfaceRealModel U phi))
    (s t : ℝ) (ht : t ∉ Set.Icc (-1 : ℝ) 1) :
    ((properLineTubeExteriorPoint U phi hcore s t ht :
      properLineTubeExteriorOpen SurfaceRealModel U phi hcore) : X) =
      ((phi.symm (s, t) : U) : X) :=
  rfl

theorem point_openInclusion_properLineTubeExteriorPoint
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore SurfaceRealModel U phi))
    (s t : ℝ) (ht : t ∉ Set.Icc (-1 : ℝ) 1) :
    (ContMDiffSingularSimplex.point (I := SurfaceRealModel)
        (r := ∞) (properLineTubeExteriorPoint U phi hcore s t ht)).openInclusion
      (I := SurfaceRealModel)
      (properLineTubeExteriorOpen SurfaceRealModel U phi hcore) =
    ContMDiffSingularSimplex.point (I := SurfaceRealModel)
      (r := ∞) (((phi.symm (s, t) : U) : X)) := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  rfl

/-- The boundary of a transverse proper-line-tube crossing is its
positive-side endpoint minus its negative-side endpoint. -/
theorem boundary_properLineTubeTransverseSimplex_single
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, ProperLineTubeModel⟯ ℝ × ℝ)
    (s a b : ℝ) :
    boundary (I := SurfaceRealModel)
      (Finsupp.single
        ((properLineTubeTransverseSimplex SurfaceRealModel U phi s a b).openInclusion
          (I := SurfaceRealModel) U) (1 : ℤ)) =
      Finsupp.single
        (ContMDiffSingularSimplex.point (I := SurfaceRealModel)
          (((phi.symm (s, b) : U) : X))) (1 : ℤ) -
      Finsupp.single
        (ContMDiffSingularSimplex.point (I := SurfaceRealModel)
          (((phi.symm (s, a) : U) : X))) (1 : ℤ) := by
  have hface_zero :
      ((properLineTubeTransverseSimplex SurfaceRealModel U phi s a b).openInclusion
        (I := SurfaceRealModel) U).face 0 =
      ContMDiffSingularSimplex.point (I := SurfaceRealModel)
        (((phi.symm (s, b) : U) : X)) := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    rw [ContMDiffSingularSimplex.openInclusion_face]
    change (((properLineTubeTransverseSimplex SurfaceRealModel U phi s a b).face 0 q : U) : X) = _
    simp
  have hface_one :
      ((properLineTubeTransverseSimplex SurfaceRealModel U phi s a b).openInclusion
        (I := SurfaceRealModel) U).face 1 =
      ContMDiffSingularSimplex.point (I := SurfaceRealModel)
        (((phi.symm (s, a) : U) : X)) := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    rw [ContMDiffSingularSimplex.openInclusion_face]
    change (((properLineTubeTransverseSimplex SurfaceRealModel U phi s a b).face 1 q : U) : X) = _
    simp
  simp [boundary, Finsupp.linearCombination_single, Fin.sum_univ_two,
    hface_zero, hface_one, sub_eq_add_neg]

/-- If deleting the closed middle strip of a proper line tube leaves a
connected surface, the tube's transverse Thom form detects nontrivial first
de Rham cohomology. -/
theorem not_subsingleton_deRhamH1_of_properLineTube_exterior_connected
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore SurfaceRealModel U phi))
    (s : ℝ) {a b : ℝ} (ha : a < -1) (hb : 1 < b)
    [ConnectedSpace
      (properLineTubeExteriorOpen SurfaceRealModel U phi hcore)] :
    ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1) := by
  have ha_out : a ∉ Set.Icc (-1 : ℝ) 1 := by
    intro ha_mem
    linarith [ha_mem.1]
  have hb_out : b ∉ Set.Icc (-1 : ℝ) 1 := by
    intro hb_mem
    linarith [hb_mem.2]
  let xminus := properLineTubeExteriorPoint U phi hcore s a ha_out
  let xplus := properLineTubeExteriorPoint U phi hcore s b hb_out
  rcases SmoothChainConnectivity.smoothChainJoined_all xplus xminus with
    ⟨returning, hreturning⟩
  apply not_subsingleton_deRhamH1_of_properLineTube_return_chain_boundary
    SurfaceRealModel U phi hcore s ha.le hb.le returning
  rw [hreturning, sub_eq_add_neg, SingularChain.openInclusion_add]
  rw [show -Finsupp.single
      (ContMDiffSingularSimplex.point (I := SurfaceRealModel) xplus) (1 : ℤ) =
        (-1 : ℤ) • Finsupp.single
          (ContMDiffSingularSimplex.point (I := SurfaceRealModel) xplus) (1 : ℤ) by
      simp]
  rw [SingularChain.openInclusion_zsmul]
  simp only [SingularChain.openInclusion_single]
  rw [point_openInclusion_properLineTubeExteriorPoint U phi hcore s a ha_out]
  rw [point_openInclusion_properLineTubeExteriorPoint U phi hcore s b hb_out]
  rw [boundary_properLineTubeTransverseSimplex_single U phi s a b]
  abel

/-- Vanishing first de Rham cohomology forces the exterior of every proper
line tube's closed transition strip to be disconnected. -/
theorem properLineTube_exterior_not_connected_of_deRhamH1_subsingleton
    (hH1 : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1))
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore SurfaceRealModel U phi))
    (s : ℝ) :
    ¬ ConnectedSpace
      (properLineTubeExteriorOpen SurfaceRealModel U phi hcore) := by
  intro hconnected
  letI : ConnectedSpace
      (properLineTubeExteriorOpen SurfaceRealModel U phi hcore) := hconnected
  exact not_subsingleton_deRhamH1_of_properLineTube_exterior_connected
    U phi hcore s (a := -2) (b := 2) (by norm_num) (by norm_num) hH1

end
end Manifold
end JJMath
