import JJMath.Uniformization.ExteriorAngularExtension

/-!
# Exhaustions with vanishing first de Rham cohomology

The bounded filling of each pointed exhaustion member has no bounded
complementary component.  Removing its finitely many exterior complementary
components from the ambient surface, one at a time, gives annular
Mayer--Vietoris covers and preserves vanishing first cohomology.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold
open JJMath.Manifold.SmoothChainConnectivity

noncomputable section

/--
%%handwave
name:
  Zero-cohomology bounded-filling exhaustion
statement:
  Let a connected noncompact Riemann surface have vanishing first real de
  Rham cohomology.  From every smooth relatively compact exhaustion and every
  base point one can construct a pointed smooth relatively compact exhaustion
  by path-connected domains whose first real de Rham cohomology vanishes.
proof:
  Take the component containing the base point and fill its relatively compact
  complementary components.  The remaining complementary components are
  exterior.  Delete them one at a time through annular Mayer--Vietoris covers;
  the nonzero angular period supplied from the exterior side makes exactness
  preserve vanishing first cohomology at every deletion.
tags:
  milestone
-/
theorem
    smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_ambientDeRhamH1Zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X) (p : X) :
    Nonempty (PointedH1ZeroSmoothRelativelyCompactExhaustion X p) := by
  refine smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_domainwise
    (fun D q hq Dhat hDhat => ?_) E p
  letI : PathConnectedSpace Dhat.carrier := by
    rw [hDhat]
    exact smoothBoundaryDomain_boundedFilling_pathConnected D hq
  have hpre : IsPreconnected Dhat.carrier :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  apply Dhat.deRhamH1Zero_of_all_complementComponents_exterior
    hnoncompact E hpre
  intro V hV
  exact (hV.isExteriorComponent_iff_not_closure_compact
    Dhat.compact_closure).2
      (smoothBoundaryDomain_boundedFilling_complement_components_unbounded
        D hq Dhat hDhat V hV)

/--
%%handwave
name:
  Filling a smooth exhaustion gives vanishing first cohomology
statement:
  Every smooth relatively compact exhaustion of a noncompact simply connected
  Riemann surface can be replaced, after fixing a base point, by a pointed
  smooth relatively compact exhaustion whose members have vanishing first real
  de Rham cohomology.
proof:
  First integrate closed one-forms from a basepoint on the ambient simply
  connected surface; a finite-grid homotopy argument makes the integral
  path-independent and proves that every closed one-form is exact.  Fill the
  bounded holes of each pointed exhaustion member.  Every remaining
  complementary component is exterior, and deleting these finitely many
  components one at a time gives annular Mayer--Vietoris covers.  The angular
  period class on each collar makes the restriction from the exterior side
  nonzero, so exactness preserves vanishing first cohomology at every deletion.
-/
theorem smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X) (p : X) :
    Nonempty (PointedH1ZeroSmoothRelativelyCompactExhaustion X p) := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  letI : Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1) :=
    simplyConnected_surface_deRhamH1_zero (X := X)
  exact
    smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_ambientDeRhamH1Zero
      hnoncompact E p


end

end JJMath.Uniformization
