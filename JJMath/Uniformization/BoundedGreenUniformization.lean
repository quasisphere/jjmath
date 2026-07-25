import JJMath.Uniformization.BoundedGreenDomain
import JJMath.Uniformization.GreenConjugateVortex
import JJMath.Uniformization.GreenFunction

/-!
# Uniformizing a bounded Green domain

This file closes the analytic bounded-domain pipeline.  Once the open surface
carried by a smooth boundary domain has no monodromy, Hubbard's Perron Green
potential exponentiates to a proper degree-one disk map and hence gives a
biholomorphism with the unit disk.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

/--
%%handwave
name: Biholomorphism associated with a bijective pointed disk map
statement:
  If a pointed holomorphic map $F:X\to\mathbb D$ is bijective, bundle $F$
  and its inverse as a biholomorphism whose forward map is exactly $F$.
-/
noncomputable def PointedHolomorphicMap.biholomorphicOfBijective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hbij : Function.Bijective F.toFun) :
    Biholomorphic X Complex.UnitDisc := by
  have hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx
        (fun y ↦ (F.toFun y : ℂ)) ≠ 0 := by
    intro x χx
    apply injective_holomorphicMap_surfaceComplexDerivative_ne_zero
      χx F.holomorphic_coe_unitDisc
    intro y z hyz
    exact hbij.1 (Subtype.ext hyz)
  let hloc : IsLocalHomeomorph F.toFun :=
    unbranched_pointedDiskMap_isLocalHomeomorph X F hunbranched
  let e : X ≃ₜ Complex.UnitDisc :=
    hloc.toHomeomorphOfBijective hbij
  exact
    { toHomeomorph := e
      holomorphic_toFun := by
        simpa [e, hloc] using F.holomorphic
      holomorphic_invFun := by
        simpa [e, hloc] using
          bijective_unbranched_pointedDiskMap_inverse_holomorphic
            X F hunbranched hbij.1 hbij.2 }

/--
%%handwave
name: Underlying map of the biholomorphism induced by a bijective disk map
statement:
  If a pointed holomorphic map $F:X\to\mathbb D$ is bijective, then the biholomorphism constructed from $F$ has underlying map $x\mapsto F(x)$.
proof:
  This is the underlying map specified in the construction.
-/
@[simp]
theorem PointedHolomorphicMap.biholomorphicOfBijective_apply
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hbij : Function.Bijective F.toFun) (x : X) :
    (F.biholomorphicOfBijective hbij).toHomeomorph x = F.toFun x := by
  rfl

/--
%%handwave
name: Base point of the induced disk biholomorphism
statement:
  If a bijective pointed holomorphic map $F:X\to\mathbb D$ sends $p$ to $0$, then the induced biholomorphism also sends $p$ to $0$.
proof:
  Its underlying map is $F$, so the assertion is the pointed normalization $F(p)=0$.
-/
@[simp]
theorem PointedHolomorphicMap.biholomorphicOfBijective_base
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hbij : Function.Bijective F.toFun) :
    (F.biholomorphicOfBijective hbij).toHomeomorph p = 0 := by
  simpa using F.base_eq

/-- The zero-cohomology Green construction produces an actual bijective
pointed disk map, not merely the proposition that a biholomorphism exists.
Keeping the normalized map is essential in the exhaustion argument.

%%handwave
name: Bijective disk map from a compact-superlevel Green function
statement:
  Let $X$ be a noncompact Riemann surface with $H^1_{\mathrm{dR}}(X;\mathbb R)=0$, let $p\in X$, and let $G$ be a Green function with pole at $p$ and compact positive superlevel sets. Then there is a pointed holomorphic map $F:X\to\mathbb D$ with $F(p)=0$ that is bijective.
proof:
  The vortex construction exponentiates the Green function and its global conjugate to a pointed disk map. Its modulus identity gives properness, while the logarithmic pole gives one simple zero at $p$. The proper-map degree theorem therefore makes every fiber a singleton.
-/
theorem compactSuperlevelGreenFunction_exists_bijective_pointedDiskMap_of_deRhamH1Zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    ∃ F : PointedHolomorphicMap X Complex.UnitDisc p 0,
      Function.Bijective F.toFun := by
  have hnoncompact : ¬ CompactSpace X :=
    not_compactSpace_iff.mpr inferInstance
  rcases connected_noncompact_has_smoothRelativelyCompactExhaustion
      X hnoncompact with ⟨E⟩
  rcases compactSuperlevelGreenFunction_planeMap_of_vortex E G with ⟨P⟩
  rcases compactSuperlevelGreenFunctionPlaneMap_to_pointedDiskMap
      X G P with ⟨F, hF⟩
  have hproper : IsProperMap F.toFun :=
    compactSuperlevelGreenFunction_pointedDiskMap_isProper X G F hF
  have hdegree : ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z :=
    proper_pointedDiskMap_degree_one_of_simple_single_zero
      X F hproper hF.2.1 hF.2.2
  refine ⟨F, ?_, ?_⟩
  · intro x y hxy
    exact (hdegree (F.toFun x)).unique
      rfl (by simp [hxy])
  · intro z
    exact (hdegree z).exists

/-- The Green maps on all exhaustion members can be chosen simultaneously,
with the common exhaustion base point sent to the center of the disk.

%%handwave
name: Simultaneous pointed disk maps along a zero-cohomology exhaustion
statement:
  Let $(\Omega_n)$ be a pointed smooth relatively compact exhaustion of a noncompact Riemann surface, with each $\Omega_n$ path connected and satisfying $H^1_{\mathrm{dR}}(\Omega_n;\mathbb R)=0$. Then one can choose for every $n$ a bijective holomorphic map $F_n:\Omega_n\to\mathbb D$ sending the common base point to $0$.
proof:
  Choose compact-superlevel Green functions on all exhaustion members. On each open carrier, install its induced Riemann-surface and vanishing-cohomology structures and apply the bijective Green disk-map construction.
-/
theorem PointedH1ZeroSmoothRelativelyCompactExhaustion.has_bijective_pointedDiskMaps
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (hX : ¬ CompactSpace X)
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p) :
    Nonempty ((n : ℕ) →
      {F : PointedHolomorphicMap (E.domain n).openCarrier
          Complex.UnitDisc ⟨p, E.domain_base_mem n⟩ 0 //
        Function.Bijective F.toFun}) := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  rcases E.has_compactSuperlevelGreenFunctions hX with ⟨G⟩
  refine ⟨fun n ↦ ?_⟩
  letI : PathConnectedSpace (E.domain n).carrier := E.pathConnected n
  letI : Nonempty (E.domain n).carrier :=
    ⟨⟨p, E.domain_base_mem n⟩⟩
  let U : TopologicalSpace.Opens X := (E.domain n).openCarrier
  letI : RiemannSurface U :=
    (E.domain n).openCarrier_riemannSurface
  letI : IsManifold SurfaceRealModel ∞ U :=
    complexOneManifold_has_real_smooth_structure U
  letI : NoncompactSpace U :=
    not_compactSpace_iff.mp
      ((E.domain n).not_compactSpace_openCarrier hX)
  letI : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := U) (A := ℝ) 1) :=
    E.domain_deRhamH1Zero n
  change {F : PointedHolomorphicMap U Complex.UnitDisc
      ⟨p, E.domain_base_mem n⟩ 0 // Function.Bijective F.toFun}
  have hne : Nonempty {F : PointedHolomorphicMap U Complex.UnitDisc
      ⟨p, E.domain_base_mem n⟩ 0 // Function.Bijective F.toFun} := by
    rcases
        compactSuperlevelGreenFunction_exists_bijective_pointedDiskMap_of_deRhamH1Zero
          U (G n) with ⟨F, hF⟩
    exact ⟨⟨F, hF⟩⟩
  exact Classical.choice hne

end

end JJMath.Uniformization
