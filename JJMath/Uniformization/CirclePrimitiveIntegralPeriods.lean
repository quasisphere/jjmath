import JJMath.Manifold.CirclePrimitive
import JJMath.Uniformization.CompactSupportTransfer
import JJMath.Uniformization.SmoothChainConnectivity

/-!
# Circle primitives from integral smooth periods

On a connected smooth surface, a closed one-form whose smooth singular
periods are integer multiples of two pi has a smooth circle-valued primitive.
The phase is defined by exponentiating the integral along a chosen smooth
chain from a base point.  Local Poincare primitives show that this apparently
choice-dependent definition is smooth.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-- A closed one-form on a smooth complex surface has a real primitive on a
full-plane coordinate neighborhood.  The neighborhood also comes with smooth
chains from its marked point to all of its points.

%%handwave
name: Coordinate primitive with smooth chain connectivity
statement:
  Let $\omega$ be a closed smooth real one-form on a Riemann surface and let $x$ be a point. There is a full-plane coordinate neighborhood $U\ni x$ and a smooth real function $\theta$ on $U$ such that $\omega|_U=d\theta$, and every point of $U$ can be joined to $x$ by a smooth singular one-chain with the expected boundary.
proof:
  Choose a full-plane coordinate chart around $x$. Pull $\omega$ to the convex plane, apply the Poincaré lemma, and pull the primitive back. The chart domain is connected, so smooth-chain connectivity supplies the required chains.
-/
theorem exists_coordinateOpen_realPrimitive_and_smoothChains
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x : X) :
    ∃ (U : TopologicalSpace.Opens X) (hxU : x ∈ U)
        (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯),
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega.1 =
          deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta) ∧
      ∀ y : U,
        SmoothChainConnectivity.SmoothChainJoined
          ⟨x, hxU⟩ y := by
  rcases exists_complexPlanarChart_subordinate
      (⊤ : TopologicalSpace.Opens X) x trivial with
    ⟨U, hxU, _hUtop, hphi⟩
  let phi := Classical.choice hphi
  let omegaU : DeRhamClosedForms
      (I := SurfaceRealModel) (M := U) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionToOpen
      (I := SurfaceRealModel) (A := ℝ) U 1 omega
  let omegaPlane : DeRhamClosedForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph
      SurfaceRealModel SurfaceRealModel phi.symm 1 omegaU
  have hconvex : Convex ℝ (complexPlanarModelOpen : Set ℂ) := by
    simpa [complexPlanarModelOpen] using (convex_univ : Convex ℝ (univ : Set ℂ))
  rcases deRham_convex_open_closed_succ_form_has_primitive
      complexPlanarModelOpen hconvex (phi ⟨x, hxU⟩) 0 omegaPlane with
    ⟨thetaPlane, hthetaPlane⟩
  let thetaU : SmoothForms (I := SurfaceRealModel) (M := U) ℝ 0 :=
    smoothFormsPullbackDiffeomorph
      SurfaceRealModel SurfaceRealModel phi 0 thetaPlane
  let theta : C^∞⟮SurfaceRealModel, U; ℝ⟯ :=
    smoothRealFunctionOfZeroForm SurfaceRealModel thetaU
  have htheta :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega.1 =
        deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta) := by
    rw [smoothRealFunctionToZeroForm_smoothRealFunctionOfZeroForm]
    change omegaU.1 = deRhamDifferential
      (I := SurfaceRealModel) (M := U) (A := ℝ) 0 thetaU
    dsimp only [thetaU]
    rw [deRhamDifferential_smoothFormsPullbackDiffeomorph,
      hthetaPlane]
    exact (smoothFormsPullbackDiffeomorph_symm_comp
      SurfaceRealModel SurfaceRealModel phi.symm omegaU.1).symm
  let planeToOpen : ℂ → complexPlanarModelOpen := fun z => ⟨z, trivial⟩
  have hplaneToOpen : Function.Surjective planeToOpen := by
    intro z
    exact ⟨z, Subtype.ext (by rfl)⟩
  letI : ConnectedSpace complexPlanarModelOpen :=
    hplaneToOpen.connectedSpace (continuous_id.subtype_mk (fun _ => trivial))
  letI : ConnectedSpace U :=
    phi.symm.surjective.connectedSpace phi.symm.continuous
  refine ⟨U, hxU, theta, htheta, ?_⟩
  intro y
  exact SmoothChainConnectivity.smoothChainJoined_all ⟨x, hxU⟩ y

end

end JJMath.Uniformization
