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

/--
%%handwave
name:
  Underlying point of a proper-line tube exterior point
statement:
  If \(t\notin[-1,1]\), the exterior point specified by tube coordinates
  \((s,t)\) has underlying surface point \(\varphi^{-1}(s,t)\).
proof:
  This is the defining value of the exterior point; its additional data only
  certifies that it lies outside the transition core.
-/
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

/--
%%handwave
name:
  Inclusion of an exterior point simplex
statement:
  The singular zero-simplex at the exterior point with tube coordinates
  \((s,t)\), after inclusion into the surface, is the point simplex at
  \(\varphi^{-1}(s,t)\).
proof:
  Both zero-simplices are constant maps with the same underlying surface
  value.
-/
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

/--
%%handwave
name:
  Boundary of a transverse crossing of a proper-line tube
statement:
  The oriented boundary of the transverse one-simplex
  \(q\mapsto\varphi^{-1}(s,(1-q)a+qb)\) is the point at
  \(\varphi^{-1}(s,b)\) minus the point at \(\varphi^{-1}(s,a)\).
proof:
  The two faces of a one-simplex are its endpoint at \(b\) and its endpoint
  at \(a\), with alternating signs \(+1\) and \(-1\).
-/
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

/--
%%handwave
name:
  Connected proper-line exterior forces nontrivial first cohomology
statement:
  Suppose the complement of the closed transition core of a proper-line tube
  is connected.  Then \(H^1_{\mathrm{dR}}(X)\) is nontrivial.
proof:
  Choose transverse endpoints below and above the core and join them by a
  smooth chain in the connected exterior.  Adding this return chain to the
  transverse crossing gives a cycle.  The tube Thom form integrates to one
  on the crossing and to zero on the exterior return, so its cohomology class
  is nonzero.
-/
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

/--
%%handwave
name:
  Vanishing first cohomology disconnects every proper-line exterior
statement:
  If \(H^1_{\mathrm{dR}}(X)=0\), then the complement of the closed transition
  core of every proper-line tube is disconnected.
proof:
  If such an exterior were connected, the transverse crossing and an
  exterior return chain would produce a cycle of Thom-form period one,
  contradicting the assumed vanishing of first de Rham cohomology.
-/
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
