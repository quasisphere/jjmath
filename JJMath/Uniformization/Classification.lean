import JJMath.Uniformization.Classification.StandardModels
import JJMath.Uniformization.Classification.PlanarDeck
import JJMath.Uniformization.Classification.Spherical
import JJMath.Uniformization.Classification.UniversalCoverComparison
import JJMath.Uniformization.Classification.Quotient
import JJMath.Uniformization.CompactH1Uniformization
import JJMath.Uniformization.GreenFunction

/-!
# Universal-cover classification of Riemann surfaces

This file exposes the basepoint-independent disk predicate and assembles the
existing simply connected uniformization theorem into the universal-cover
trichotomy.  The standard parabolic models and the holomorphic covering
infrastructure live in the support modules under `Classification/`.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

open JJMath.PathHomotopyUniversalCover

/--
%%handwave
name: Unit-disc universal-cover property
statement:
  A Riemann surface $X$ has the unit-disc universal-cover property when, for
  every basepoint $x_0\in X$, its path-homotopy universal cover based at
  $x_0$ is biholomorphic to $\mathbb D$.
-/
def HasUnitDiscUniversalCover (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  ∀ x₀ : X,
    @BiholomorphicSurfaces (PathHomotopyUniversalCover X x₀) Complex.UnitDisc
      inferInstance inferInstance inferInstance inferInstance

/--
%%handwave
name:
  A spherical universal cover is independent of the base point
statement:
  If the path-class universal cover of a Riemann surface $X$ based at one
  point $x_0$ is biholomorphic to the Riemann sphere, then the path-class
  cover based at every $x_1\in X$ is biholomorphic to the sphere.
proof:
  Compose the given spherical biholomorphism with the biholomorphic
  basepoint-change map from the cover based at $x_1$ to the cover based at
  $x_0$.
-/
theorem hasSphericalUniversalCover_of_one_basepoint
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ : X)
    (h : BiholomorphicSurfaces (PathHomotopyUniversalCover X x₀) RiemannSphere) :
    HasSphericalUniversalCover X := by
  intro x₁
  exact BiholomorphicSurfaces.trans
    (pathHomotopyUniversalCover_basepoint_biholomorphicSurfaces x₁ x₀) h

/--
%%handwave
name:
  A planar universal cover is independent of the base point
statement:
  If the path-class universal cover of a Riemann surface $X$ based at one
  point $x_0$ is biholomorphic to $\mathbb C$, then the path-class cover based
  at every $x_1\in X$ is biholomorphic to $\mathbb C$.
proof:
  Compose the given planar biholomorphism with the biholomorphic
  basepoint-change map from the cover based at $x_1$ to the cover based at
  $x_0$.
-/
theorem hasParabolicUniversalCover_of_one_basepoint
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ : X)
    (h : BiholomorphicSurfaces (PathHomotopyUniversalCover X x₀) ℂ) :
    HasParabolicUniversalCover X := by
  intro x₁
  simpa [BiholomorphicToComplexPlane] using
    BiholomorphicSurfaces.trans
      (pathHomotopyUniversalCover_basepoint_biholomorphicSurfaces x₁ x₀) h

/--
%%handwave
name:
  A planar universal cover gives the plane, cylinder, or a torus
statement:
  If a Riemann surface $X$ has universal cover biholomorphic to
  $\mathbb C$, then $X$ is biholomorphic to $\mathbb C$, to
  $\mathbb C^\times$, or to a complex torus $\mathbb C/\Lambda$.
proof:
  Transport the deck group to the plane. Its elements are translations and
  its translation subgroup is discrete, hence has integral rank $0$, $1$, or
  $2$. The three rank cases identify the quotient respectively with the
  plane, the punctured plane, or the quotient by a full complex lattice.
-/
theorem isPlaneCylinderOrTorus_of_hasParabolicUniversalCover
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (h : HasParabolicUniversalCover X) :
    IsPlaneCylinderOrTorus X := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  have hE : BiholomorphicSurfaces
      (PathHomotopyUniversalCover X x₀) ℂ := by
    simpa [BiholomorphicToComplexPlane] using h x₀
  rcases hE with ⟨E⟩
  rcases planarDeckSubmodule_finrank_cases E with hzero | hone | htwo
  · exact Or.inl
      (biholomorphicSurfaces_complexPlane_of_planarDeckSubmodule_finrank_zero
        E hzero)
  · exact Or.inr (Or.inl
      (biholomorphicSurfaces_complexCylinder_of_planarDeckSubmodule_finrank_one
        E hone))
  · exact Or.inr (Or.inr
      (biholomorphicSurfaces_complexTorus_of_planarDeckSubmodule_finrank_two
        E htwo))

/--
%%handwave
name:
  A holomorphic plane covering makes the universal cover planar
statement:
  Let $X$ be a Riemann surface. If there is a surjective holomorphic covering
  map $p:\mathbb C\to X$, then every based path-class universal cover of $X$
  is biholomorphic to $\mathbb C$.
proof:
  Covering-space uniqueness gives a homeomorphism from $\mathbb C$ to one
  based path-class cover over $X$, and endpoint preservation makes this map
  holomorphic. Uniformize that path-class cover. The sphere is excluded by
  noncompactness. The disk is excluded because composing the plane map with a
  disk uniformization would give a bounded nonconstant entire function.
  Thus the cover is planar, and basepoint change gives the conclusion at
  every base point.
-/
theorem hasParabolicUniversalCover_of_holomorphic_complexPlane_cover
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (p : ℂ → X) (hp_cover : IsCoveringMap p)
    (hp_holomorphic : HolomorphicMap ℂ X p)
    (hp_surjective : Function.Surjective p) :
    HasParabolicUniversalCover X := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  rcases hp_surjective x₀ with ⟨z₀, hz₀⟩
  let pC : C(ℂ, X) := ⟨p, hp_cover.continuous⟩
  let C₀ := PathHomotopyUniversalCover X x₀
  let H : ℂ ≃ₜ C₀ :=
    simplyConnectedCoverHomeomorph x₀ pC hp_cover z₀ hz₀
  have hH_endpoint (z : ℂ) : endpoint (H z) = p z := by
    exact simplyConnectedCoverHomeomorph_endpoint
      x₀ pC hp_cover z₀ hz₀ z
  have hH_holomorphic : HolomorphicMap ℂ C₀ H :=
    holomorphicMap_to_pathHomotopyUniversalCover_of_endpoint_eq
      H.continuous hp_holomorphic hH_endpoint
  letI : RiemannSurface C₀ :=
    pathHomotopyUniversalCover_riemannSurface (Y := X) x₀
  letI : SimplyConnectedSpace C₀ :=
    pathHomotopyUniversalCover_simplyConnected (Y := X) x₀
  rcases simplyConnected_riemannSurface_uniformization C₀ with
      hsphere | hplane | hdisk
  · rcases hsphere with ⟨B⟩
    letI : CompactSpace C₀ :=
      Homeomorph.compactSpace B.toHomeomorph.symm
    letI : CompactSpace ℂ := Homeomorph.compactSpace H.symm
    exact ((not_compactSpace_iff.mpr
      (inferInstance : NoncompactSpace ℂ)) inferInstance).elim
  · exact hasParabolicUniversalCover_of_one_basepoint X x₀ hplane
  · rcases hdisk with ⟨B⟩
    exfalso
    apply complexPlane_has_no_bounded_nonconstant_holomorphicFunction
    let f : ℂ → ℂ := fun z ↦ (B.toHomeomorph (H z) : ℂ)
    have hf_holomorphic : HolomorphicMap ℂ ℂ f := by
      change HolomorphicMap ℂ ℂ
        (((↑) : Complex.UnitDisc → ℂ) ∘ B.toHomeomorph ∘ H)
      exact holomorphicMap_unitDisc_coe.comp
        (B.holomorphic_toFun.comp hH_holomorphic)
    have hf_injective : Function.Injective f := by
      intro z w hzw
      apply H.injective
      apply B.toHomeomorph.injective
      exact Subtype.ext hzw
    refine ⟨f, hf_holomorphic, ?_, ?_⟩
    · exact isBounded_iff_forall_norm_le.mpr
        ⟨1, by
          rintro _ ⟨z, rfl⟩
          exact le_of_lt (Complex.UnitDisc.norm_lt_one (B.toHomeomorph (H z)))⟩
    · exact Set.nontrivial_of_mem_mem_ne
        (show f 0 ∈ Set.range f from ⟨0, rfl⟩)
        (show f 1 ∈ Set.range f from ⟨1, rfl⟩)
        (by
          intro h01
          exact zero_ne_one (hf_injective h01))

/--
%%handwave
name:
  The plane, cylinder, and complex tori have planar universal cover
statement:
  If a Riemann surface $X$ is biholomorphic to $\mathbb C$, to
  $\mathbb C^\times$, or to a complex torus $\mathbb C/\Lambda$, then every
  based universal cover of $X$ is biholomorphic to $\mathbb C$.
proof:
  In the three cases, compose the model biholomorphism with respectively the
  identity map, the exponential covering, or the lattice quotient covering.
  This gives a surjective holomorphic covering from $\mathbb C$ to $X$, whose
  path-class universal cover is planar.
-/
theorem hasParabolicUniversalCover_of_isPlaneCylinderOrTorus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (h : IsPlaneCylinderOrTorus X) :
    HasParabolicUniversalCover X := by
  rcases h with hplane | hcylinder | htorus
  · rcases hplane with ⟨B⟩
    exact hasParabolicUniversalCover_of_holomorphic_complexPlane_cover
      X B.toHomeomorph.symm
      (homeomorph_isCoveringMap B.toHomeomorph.symm)
      B.holomorphic_invFun B.toHomeomorph.symm.surjective
  · rcases hcylinder with ⟨B⟩
    let p : ℂ → X := B.toHomeomorph.symm ∘ complexExponentialCover
    have hp_cover : IsCoveringMap p := by
      simpa [p] using complexExponentialCover_isCoveringMap.homeomorph_comp
        B.toHomeomorph.symm
    have hp_holomorphic : HolomorphicMap ℂ X p := by
      exact B.holomorphic_invFun.comp complexExponentialCover_holomorphic
    have hp_surjective : Function.Surjective p :=
      B.toHomeomorph.symm.surjective.comp
        Complex.isAddQuotientCoveringMap_exp.surjective
    exact hasParabolicUniversalCover_of_holomorphic_complexPlane_cover
      X p hp_cover hp_holomorphic hp_surjective
  · rcases htorus with ⟨Lambda, ⟨B⟩⟩
    let p : ℂ → X :=
      B.toHomeomorph.symm ∘ complexTorusQuotientMk Lambda
    have hp_cover : IsCoveringMap p := by
      simpa [p] using (complexTorusQuotientMk_isCoveringMap Lambda).homeomorph_comp
        B.toHomeomorph.symm
    have hp_holomorphic : HolomorphicMap ℂ X p := by
      exact B.holomorphic_invFun.comp
        (complexTorusQuotientMk_holomorphic Lambda)
    have hp_surjective : Function.Surjective p :=
      B.toHomeomorph.symm.surjective.comp
        (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).surjective
    exact hasParabolicUniversalCover_of_holomorphic_complexPlane_cover
      X p hp_cover hp_holomorphic hp_surjective

/--
%%handwave
name:
  Classification of Riemann surfaces with planar universal cover
statement:
  For every Riemann surface $X$, its universal cover is biholomorphic to
  $\mathbb C$ if and only if $X$ is biholomorphic to $\mathbb C$, to
  $\mathbb C^\times$, or to a complex torus $\mathbb C/\Lambda$.
proof:
  In the forward direction, classify the discrete translation group of deck
  transformations by its integral rank $0$, $1$, or $2$. In the reverse
  direction, use the identity, exponential, and lattice quotient coverings
  of the three respective models.
tags:
  milestone
-/
theorem hasParabolicUniversalCover_iff_isPlaneCylinderOrTorus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] :
    HasParabolicUniversalCover X ↔ IsPlaneCylinderOrTorus X :=
  ⟨isPlaneCylinderOrTorus_of_hasParabolicUniversalCover X,
    hasParabolicUniversalCover_of_isPlaneCylinderOrTorus X⟩

/--
%%handwave
name:
  A disk universal cover is independent of the base point
statement:
  If the path-class universal cover of a Riemann surface $X$ based at one
  point $x_0$ is biholomorphic to the unit disk, then the path-class cover
  based at every $x_1\in X$ is biholomorphic to the unit disk.
proof:
  Compose the given disk biholomorphism with the biholomorphic
  basepoint-change map from the cover based at $x_1$ to the cover based at
  $x_0$.
-/
theorem hasUnitDiscUniversalCover_of_one_basepoint
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ : X)
    (h : BiholomorphicSurfaces
      (PathHomotopyUniversalCover X x₀) Complex.UnitDisc) :
    HasUnitDiscUniversalCover X := by
  intro x₁
  exact BiholomorphicSurfaces.trans
    (pathHomotopyUniversalCover_basepoint_biholomorphicSurfaces x₁ x₀) h

/--
%%handwave
name:
  Disk and half-plane universal covers are equivalent
statement:
  A Riemann surface has universal cover biholomorphic to the unit disk if and
  only if it has universal cover biholomorphic to the upper half-plane.
proof:
  At every base point, compose with the Cayley biholomorphism between the unit
  disk and the upper half-plane, in either direction.
-/
theorem hasUnitDiscUniversalCover_iff_hasUpperHalfPlaneUniformizingCover
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallySimplyConnectedSpace X] :
    HasUnitDiscUniversalCover X ↔ HasUpperHalfPlaneUniformizingCover X := by
  constructor
  · intro hdisk x₀
    exact biholomorphicToUpperHalfPlane_of_biholomorphicSurfaces_unitDisc
      (PathHomotopyUniversalCover X x₀) (hdisk x₀)
  · intro hupper x₀
    have h : BiholomorphicSurfaces
        (PathHomotopyUniversalCover X x₀) UpperHalfPlane := by
      simpa [BiholomorphicToUpperHalfPlane] using hupper x₀
    exact BiholomorphicSurfaces.trans h
      (BiholomorphicSurfaces.symm
        unitDisc_biholomorphicSurfaces_upperHalfPlane)

/--
%%handwave
name:
  Universal-cover trichotomy for Riemann surfaces
statement:
  For every Riemann surface $X$, its universal cover is biholomorphic to the
  Riemann sphere, the complex plane, or the unit disk.
proof:
  Apply simply connected uniformization to one based path-class cover, then
  use biholomorphic basepoint change to propagate the resulting alternative
  to every base point.
-/
theorem riemannSurface_hasUniversalCoverTrichotomy
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] :
    HasSphericalUniversalCover X ∨
      HasParabolicUniversalCover X ∨ HasUnitDiscUniversalCover X := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let C := PathHomotopyUniversalCover X x₀
  letI : RiemannSurface C :=
    pathHomotopyUniversalCover_riemannSurface (Y := X) x₀
  letI : SimplyConnectedSpace C :=
    pathHomotopyUniversalCover_simplyConnected (Y := X) x₀
  rcases simplyConnected_riemannSurface_uniformization C with hsphere | hplane | hdisk
  · exact Or.inl (hasSphericalUniversalCover_of_one_basepoint X x₀ hsphere)
  · exact Or.inr (Or.inl
      (hasParabolicUniversalCover_of_one_basepoint X x₀ hplane))
  · exact Or.inr (Or.inr
      (hasUnitDiscUniversalCover_of_one_basepoint X x₀ hdisk))

/--
%%handwave
name:
  The disk is exactly the nonspherical nonplanar universal-cover case
statement:
  For every Riemann surface $X$, the universal cover is biholomorphic to the
  unit disk if and only if it is neither biholomorphic to the Riemann sphere
  nor biholomorphic to the complex plane.
proof:
  The three simply connected uniformization models are pairwise exclusive.
  Thus the disk alternative excludes the spherical and planar alternatives;
  conversely, the universal-cover trichotomy leaves only the disk when those
  two alternatives fail.
-/
theorem hasUnitDiscUniversalCover_iff_not_hasSpherical_and_not_hasParabolic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] :
    HasUnitDiscUniversalCover X ↔
      ¬ HasSphericalUniversalCover X ∧ ¬ HasParabolicUniversalCover X := by
  constructor
  · intro hdisk
    have hupper :=
      (hasUnitDiscUniversalCover_iff_hasUpperHalfPlaneUniformizingCover X).mp
        hdisk
    exact (uniformizing_universal_cover_models_mutually_exclusive X).2.2 hupper
  · rintro ⟨hnotSphere, hnotPlane⟩
    rcases riemannSurface_hasUniversalCoverTrichotomy X with
        hsphere | hplane | hdisk
    · exact (hnotSphere hsphere).elim
    · exact (hnotPlane hplane).elim
    · exact hdisk

/--
%%handwave
name:
  The disk is the nonspherical case outside the parabolic quotients
statement:
  For every Riemann surface $X$, the universal cover is biholomorphic to the
  unit disk if and only if the universal cover is not spherical and $X$ is
  biholomorphic to none of $\mathbb C$, $\mathbb C^\times$, and the complex
  tori $\mathbb C/\Lambda$.
proof:
  Use the universal-cover trichotomy and replace the planar universal-cover
  alternative by its classification as the plane, cylinder, or a complex
  torus.
-/
theorem hasUnitDiscUniversalCover_iff_not_hasSpherical_and_not_isPlaneCylinderOrTorus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] :
    HasUnitDiscUniversalCover X ↔
      ¬ HasSphericalUniversalCover X ∧ ¬ IsPlaneCylinderOrTorus X := by
  rw [hasUnitDiscUniversalCover_iff_not_hasSpherical_and_not_hasParabolic,
    hasParabolicUniversalCover_iff_isPlaneCylinderOrTorus]

/--
%%handwave
name:
  Classification of Riemann surfaces with disk universal cover
statement:
  For every Riemann surface $X$, its universal cover is biholomorphic to the
  unit disk if and only if $X$ is not biholomorphic to
  $\widehat{\mathbb C}$ and is biholomorphic to none of $\mathbb C$,
  $\mathbb C^\times$, and the complex tori $\mathbb C/\Lambda$.
proof:
  In the [disk remainder of the universal-cover trichotomy](lean:JJMath.Uniformization.hasUnitDiscUniversalCover_iff_not_hasSpherical_and_not_isPlaneCylinderOrTorus), replace the spherical alternative by [being the Riemann sphere](lean:JJMath.Uniformization.hasSphericalUniversalCover_iff_biholomorphicSurfaces_riemannSphere).
tags:
  milestone
-/
theorem hasUnitDiscUniversalCover_iff_not_biholomorphicSphere_and_not_isPlaneCylinderOrTorus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] :
    HasUnitDiscUniversalCover X ↔
      ¬ BiholomorphicSurfaces X RiemannSphere ∧
        ¬ IsPlaneCylinderOrTorus X := by
  rw [hasUnitDiscUniversalCover_iff_not_hasSpherical_and_not_isPlaneCylinderOrTorus,
    hasSphericalUniversalCover_iff_biholomorphicSurfaces_riemannSphere]

/--
%%handwave
name:
  Surfaces outside the spherical and parabolic models have disk universal cover
statement:
  If a Riemann surface $X$ is not biholomorphic to the Riemann sphere and is
  biholomorphic to none of $\mathbb C$, $\mathbb C^\times$, and the complex
  tori, then its universal cover is biholomorphic to the unit disk.
proof:
  A spherical universal cover would force $X$ itself to be the sphere, and a
  planar universal cover would force $X$ to be the plane, cylinder, or a
  complex torus. Excluding those two alternatives in the universal-cover
  trichotomy leaves the disk.
-/
theorem hasUnitDiscUniversalCover_of_not_biholomorphicSphere_and_not_isPlaneCylinderOrTorus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (h : ¬ BiholomorphicSurfaces X RiemannSphere ∧
      ¬ IsPlaneCylinderOrTorus X) :
    HasUnitDiscUniversalCover X := by
  exact
    (hasUnitDiscUniversalCover_iff_not_biholomorphicSphere_and_not_isPlaneCylinderOrTorus
      X).mpr h

/--
%%handwave
name:
  Biholomorphic classification by universal cover
statement:
  For every Riemann surface $X$, the following three equivalences hold:
  the universal cover is $\widehat{\mathbb C}$ exactly when
  $X\simeq\widehat{\mathbb C}$; it is $\mathbb C$ exactly when $X$ is the
  plane, cylinder, or a complex torus; and it is the unit disk exactly when
  $X$ belongs to neither preceding class.
proof:
  Combine the [spherical classification](lean:JJMath.Uniformization.hasSphericalUniversalCover_iff_biholomorphicSurfaces_riemannSphere), the [planar classification](lean:JJMath.Uniformization.hasParabolicUniversalCover_iff_isPlaneCylinderOrTorus), and the [disk remainder](lean:JJMath.Uniformization.hasUnitDiscUniversalCover_iff_not_biholomorphicSphere_and_not_isPlaneCylinderOrTorus).
tags:
  milestone
-/
theorem riemannSurface_universalCover_classification
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] :
    (HasSphericalUniversalCover X ↔
      BiholomorphicSurfaces X RiemannSphere) ∧
    (HasParabolicUniversalCover X ↔ IsPlaneCylinderOrTorus X) ∧
    (HasUnitDiscUniversalCover X ↔
      ¬ BiholomorphicSurfaces X RiemannSphere ∧
        ¬ IsPlaneCylinderOrTorus X) := by
  exact ⟨hasSphericalUniversalCover_iff_biholomorphicSurfaces_riemannSphere X,
    hasParabolicUniversalCover_iff_isPlaneCylinderOrTorus X,
    hasUnitDiscUniversalCover_iff_not_biholomorphicSphere_and_not_isPlaneCylinderOrTorus
      X⟩

/--
%%handwave
name:
  Quotient uniformization trichotomy for Riemann surfaces
statement:
  Let $X$ be a Riemann surface and $x_0\in X$. For one of
  $U=\widehat{\mathbb C}$, $U=\mathbb C$, or $U=\mathbb D$, there is a
  biholomorphism $E:\widetilde X_{x_0}\to U$ such that
  $X$ is biholomorphic to
  $U/\pi_1(X,x_0)$ for the action
  $\gamma\cdot_Eu=E(\gamma\cdot E^{-1}(u))$.
proof:
  Apply the [universal cover is one of the three standard simply connected surfaces](lean:JJMath.Uniformization.riemannSurface_hasUniversalCoverTrichotomy) at $x_0$. In each case, use [a Riemann surface is biholomorphic to the deck-orbit quotient of its chosen uniformizing model](lean:JJMath.Uniformization.PathHomotopyUniversalCover.biholomorphicSurfaces_uniformizingDeckQuotient).
tags:
  milestone
-/
theorem riemannSurface_hasQuotientUniformizationTrichotomy
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ : X) :
    (∃ E : Biholomorphic
        (PathHomotopyUniversalCover X x₀) RiemannSphere,
      BiholomorphicSurfaces X
        (PathHomotopyUniversalCover.UniformizingDeckQuotient E)) ∨
    (∃ E : Biholomorphic
        (PathHomotopyUniversalCover X x₀) ℂ,
      BiholomorphicSurfaces X
        (PathHomotopyUniversalCover.UniformizingDeckQuotient E)) ∨
    (∃ E : Biholomorphic
        (PathHomotopyUniversalCover X x₀) Complex.UnitDisc,
      BiholomorphicSurfaces X
        (PathHomotopyUniversalCover.UniformizingDeckQuotient E)) := by
  rcases riemannSurface_hasUniversalCoverTrichotomy X with
      hsphere | hplane | hdisk
  · rcases hsphere x₀ with ⟨E⟩
    exact Or.inl
      ⟨E, PathHomotopyUniversalCover.biholomorphicSurfaces_uniformizingDeckQuotient E⟩
  · have hE : BiholomorphicSurfaces
        (PathHomotopyUniversalCover X x₀) ℂ := by
      simpa [BiholomorphicToComplexPlane] using hplane x₀
    rcases hE with ⟨E⟩
    exact Or.inr (Or.inl
      ⟨E, PathHomotopyUniversalCover.biholomorphicSurfaces_uniformizingDeckQuotient E⟩)
  · rcases hdisk x₀ with ⟨E⟩
    exact Or.inr (Or.inr
      ⟨E, PathHomotopyUniversalCover.biholomorphicSurfaces_uniformizingDeckQuotient E⟩)

end Uniformization

end JJMath
