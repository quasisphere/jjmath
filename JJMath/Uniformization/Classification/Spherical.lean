import JJMath.Uniformization.Classification.Automorphisms
import JJMath.Uniformization.Classification.HolomorphicCover
import JJMath.Uniformization.Classification.SphereSimplyConnected
import JJMath.Uniformization.GreenFunction

/-!
# The spherical universal-cover case

The fixed-point theorem for automorphisms of the Riemann sphere forces every
deck transformation of a spherical path-class cover to be trivial.  Hence the
endpoint projection itself is a biholomorphism.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

open JJMath.PathHomotopyUniversalCover

noncomputable section

/--
%%handwave
name:
  A spherical universal cover has spherical base
statement:
  Let $X$ be a Riemann surface. If its path-class universal cover is
  biholomorphic to $\widehat{\mathbb C}$ at every base point, then $X$ is
  biholomorphic to $\widehat{\mathbb C}$.
proof:
  Fix one base point and conjugate every deck transformation through a
  biholomorphism from the universal cover to the sphere. The resulting sphere
  automorphism has a fixed point, while the deck action is free, so every deck
  transformation is the identity. Transitivity of the deck action on each
  endpoint fiber then makes the endpoint projection injective. It is already
  a surjective holomorphic covering, hence is biholomorphic, and composing its
  inverse with the chosen spherical biholomorphism identifies $X$ with the
  sphere.
-/
theorem biholomorphicSurfaces_riemannSphere_of_hasSphericalUniversalCover
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (hspherical : HasSphericalUniversalCover X) :
    BiholomorphicSurfaces X RiemannSphere := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let C := PathHomotopyUniversalCover X x₀
  letI : RiemannSurface C :=
    pathHomotopyUniversalCover_riemannSurface (Y := X) x₀
  rcases hspherical x₀ with ⟨E⟩
  have hdeck_trivial : ∀ gamma : FundamentalGroup X x₀, gamma = 1 := by
    intro gamma
    let D : Biholomorphic C C :=
      JJMath.Uniformization.PathHomotopyUniversalCover.deckBiholomorphic gamma
    let S : Biholomorphic RiemannSphere RiemannSphere :=
      E.symm.trans D |>.trans E
    rcases biholomorphic_riemannSphere_has_fixedPoint S with ⟨p, hp⟩
    let y : C := E.toHomeomorph.symm p
    apply deckAction_fiber_free gamma y
    apply E.toHomeomorph.injective
    have hp' :
        E.toHomeomorph
            (deckHomeomorphism gamma (E.toHomeomorph.symm p)) =
          E.toHomeomorph (E.toHomeomorph.symm p) := by
      simpa [S, D, Biholomorphic.trans] using hp
    simpa [y] using hp'
  have hendpoint_injective : Function.Injective (endpoint : C → X) := by
    intro y z hyz
    rcases deckHomeomorphism_same_fiber_transitive y z hyz with
      ⟨gamma, hgamma⟩
    rw [hdeck_trivial gamma] at hgamma
    simpa [deckHomeomorphism] using hgamma
  let P : Biholomorphic C X :=
    JJMath.Uniformization.PathHomotopyUniversalCover.biholomorphicEndpointOfInjective
      hendpoint_injective
  exact ⟨P.symm.trans E⟩

/--
%%handwave
name:
  The Riemann sphere has spherical universal cover
statement:
  Let $X$ be a Riemann surface. If $X$ is biholomorphic to
  $\widehat{\mathbb C}$, then every based path-class universal cover of $X$
  is biholomorphic to $\widehat{\mathbb C}$.
proof:
  The [Riemann sphere is simply connected](lean:JJMath.riemannSphere_simplyConnectedSpace), so a biholomorphism $X\simeq\widehat{\mathbb C}$ transports simple connectedness to $X$. Consequently [the endpoint projection has one path class over each endpoint](lean:JJMath.Uniformization.PathHomotopyUniversalCover.endpoint_injective_of_simplyConnected), and the holomorphic covering projection is a biholomorphism. Compose it with the given biholomorphism from $X$ to the sphere.
-/
theorem hasSphericalUniversalCover_of_biholomorphicSurfaces_riemannSphere
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (hsphere : BiholomorphicSurfaces X RiemannSphere) :
    HasSphericalUniversalCover X := by
  rcases hsphere with ⟨B⟩
  letI : SimplyConnectedSpace RiemannSphere :=
    riemannSphere_simplyConnectedSpace
  letI : SimplyConnectedSpace X :=
    B.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  intro x₀
  let P : Biholomorphic (PathHomotopyUniversalCover X x₀) X :=
    JJMath.Uniformization.PathHomotopyUniversalCover.biholomorphicEndpointOfInjective
      JJMath.Uniformization.PathHomotopyUniversalCover.endpoint_injective_of_simplyConnected
  exact ⟨P.trans B⟩

/--
%%handwave
name:
  Classification of Riemann surfaces with spherical universal cover
statement:
  For every Riemann surface $X$, its universal cover is biholomorphic to
  $\widehat{\mathbb C}$ if and only if $X$ itself is biholomorphic to
  $\widehat{\mathbb C}$.
proof:
  A spherical universal cover has trivial deck group because every spherical
  automorphism has a fixed point and the deck action is free. Conversely, the
  sphere is simply connected, and simple connectedness is preserved by
  biholomorphism.
tags:
  milestone
-/
theorem hasSphericalUniversalCover_iff_biholomorphicSurfaces_riemannSphere
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] :
    HasSphericalUniversalCover X ↔
      BiholomorphicSurfaces X RiemannSphere :=
  ⟨biholomorphicSurfaces_riemannSphere_of_hasSphericalUniversalCover X,
    hasSphericalUniversalCover_of_biholomorphicSurfaces_riemannSphere X⟩

end

end Uniformization

end JJMath
