import JJMath.Uniformization.Classification.Automorphisms
import JJMath.Uniformization.Classification.HolomorphicCover
import JJMath.Uniformization.Classification.StandardModels

/-!
# Deck translations in the planar case

After identifying a path-class universal cover with the complex plane, every
nonidentity deck transformation is fixed-point-free and hence a translation.
This file packages its translation vector, proves additivity, and identifies
the fibers of the uniformizing projection with the resulting translation
orbits.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

open JJMath.PathHomotopyUniversalCover

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [RiemannSurface X] {x₀ : X}

/--
%%handwave
name: Planar conjugate of a deck transformation
statement:
  Given a biholomorphism $E:\widetilde X\to\mathbb C$, transport a deck
  transformation $\delta_\gamma$ to the plane as
  $E\circ\delta_\gamma\circ E^{-1}$.
-/
def conjugatedPlanarDeckBiholomorphic
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ)
    (gamma : FundamentalGroup X x₀) : Biholomorphic ℂ ℂ :=
  E.symm.trans
      (JJMath.Uniformization.PathHomotopyUniversalCover.deckBiholomorphic gamma)
    |>.trans E

/--
%%handwave
name: Translation vector of a planar deck transformation
statement:
  In a planar universal-cover coordinate $E$, define the translation vector
  of $\gamma\in\pi_1(X,x_0)$ to be
  $t_E(\gamma)=(E\circ\delta_\gamma\circ E^{-1})(0)$.
-/
def planarDeckTranslation
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ)
    (gamma : FundamentalGroup X x₀) : ℂ :=
  (conjugatedPlanarDeckBiholomorphic E gamma).toHomeomorph 0

/--
%%handwave
name:
  Planar deck transformations act by translations
statement:
  Let $E:\widetilde X_{x_0}\to\mathbb C$ be biholomorphic. For every
  $\gamma\in\pi_1(X,x_0)$ and $z\in\mathbb C$, the transported deck action
  has the form $E\gamma E^{-1}(z)=z+\tau(\gamma)$, where
  $\tau(\gamma)=E\gamma E^{-1}(0)$.
proof:
  If $\gamma=1$, the deck action is the identity. Otherwise a fixed point of
  the transported action would pull back to a fixed point of the free deck
  action, forcing $\gamma=1$. Thus the transported automorphism is
  fixed-point-free, and every fixed-point-free automorphism of the complex
  plane is a nontrivial translation. Evaluating at zero identifies its
  translation vector with $\tau(\gamma)$.
-/
theorem conjugatedPlanarDeckBiholomorphic_apply
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ)
    (gamma : FundamentalGroup X x₀) (z : ℂ) :
    (conjugatedPlanarDeckBiholomorphic E gamma).toHomeomorph z =
      z + planarDeckTranslation E gamma := by
  by_cases hgamma : gamma = 1
  · subst gamma
    simp [conjugatedPlanarDeckBiholomorphic, planarDeckTranslation,
      Biholomorphic.trans, Biholomorphic.symm,
      JJMath.Uniformization.PathHomotopyUniversalCover.deckBiholomorphic,
      deckHomeomorphism]
  · have hfree : ∀ w : ℂ,
        (conjugatedPlanarDeckBiholomorphic E gamma).toHomeomorph w ≠ w := by
      intro w hw
      apply hgamma
      let y : PathHomotopyUniversalCover X x₀ := E.toHomeomorph.symm w
      apply deckAction_fiber_free gamma y
      apply E.toHomeomorph.injective
      have hw' := hw
      change E.toHomeomorph
          (deckHomeomorphism gamma (E.toHomeomorph.symm w)) = w at hw'
      simpa [y] using hw'
    rcases biholomorphic_complexPlane_eq_translation_of_fixedPointFree
        (conjugatedPlanarDeckBiholomorphic E gamma) hfree with
      ⟨b, _hb, htranslation⟩
    have hb : b = planarDeckTranslation E gamma := by
      have hzero := htranslation 0
      simpa [planarDeckTranslation] using hzero.symm
    simpa [hb] using htranslation z

/--
%%handwave
name: Additive translation representation of the deck group
statement:
  Bundle $\gamma\mapsto t_E(\gamma)$ as an additive homomorphism from the
  fundamental group, written additively, to $(\mathbb C,+)$.
-/
def planarDeckTranslationHom
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ) :
    Additive (FundamentalGroup X x₀) →+ ℂ where
  toFun gamma := planarDeckTranslation E gamma.toMul
  map_zero' := by
    simp [conjugatedPlanarDeckBiholomorphic, planarDeckTranslation,
      Biholomorphic.trans, Biholomorphic.symm,
      JJMath.Uniformization.PathHomotopyUniversalCover.deckBiholomorphic,
      deckHomeomorphism]
  map_add' gamma delta := by
    let w : ℂ :=
      E.toHomeomorph
        (deckHomeomorphism delta.toMul (E.toHomeomorph.symm 0))
    have hgamma :=
      conjugatedPlanarDeckBiholomorphic_apply E gamma.toMul w
    have hdelta :=
      conjugatedPlanarDeckBiholomorphic_apply E delta.toMul 0
    change planarDeckTranslation E (gamma.toMul * delta.toMul) =
      planarDeckTranslation E gamma.toMul + planarDeckTranslation E delta.toMul
    have hmul :=
      conjugatedPlanarDeckBiholomorphic_apply E
        (gamma.toMul * delta.toMul) 0
    change E.toHomeomorph
        (deckHomeomorphism (gamma.toMul * delta.toMul)
          (E.toHomeomorph.symm 0)) =
      0 + planarDeckTranslation E (gamma.toMul * delta.toMul) at hmul
    change E.toHomeomorph
        (deckHomeomorphism gamma.toMul (E.toHomeomorph.symm w)) =
      w + planarDeckTranslation E gamma.toMul at hgamma
    change E.toHomeomorph
        (deckHomeomorphism delta.toMul (E.toHomeomorph.symm 0)) =
      0 + planarDeckTranslation E delta.toMul at hdelta
    change E.toHomeomorph
        (deckAction (gamma.toMul * delta.toMul)
          (E.toHomeomorph.symm 0)) =
      0 + planarDeckTranslation E (gamma.toMul * delta.toMul) at hmul
    rw [deckAction_mul] at hmul
    have hw : w = planarDeckTranslation E delta.toMul := by
      simpa [w] using hdelta
    have hinv_w : E.toHomeomorph.symm w =
        deckHomeomorphism delta.toMul (E.toHomeomorph.symm 0) := by
      apply E.toHomeomorph.injective
      simp [w]
    rw [hinv_w] at hgamma
    calc
      planarDeckTranslation E (gamma.toMul * delta.toMul) =
          0 + planarDeckTranslation E (gamma.toMul * delta.toMul) := by simp
      _ = E.toHomeomorph
          (deckAction gamma.toMul
            (deckAction delta.toMul (E.toHomeomorph.symm 0))) := hmul.symm
      _ = w + planarDeckTranslation E gamma.toMul := by
        simpa using hgamma
      _ = planarDeckTranslation E gamma.toMul +
          planarDeckTranslation E delta.toMul := by
        rw [hw]
        ac_rfl

/--
%%handwave
name: Translation lattice of the planar deck action
statement:
  Define the integral submodule
  $\Lambda_E=\{t_E(\gamma):\gamma\in\pi_1(X,x_0)\}\subseteq\mathbb C$.
-/
def planarDeckSubmodule
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ) :
    Submodule ℤ ℂ :=
  (planarDeckTranslationHom E).range.toIntSubmodule

/--
%%handwave
name: Uniformizing projection in a planar coordinate
statement:
  Given $E:\widetilde X\to\mathbb C$, define
  $p_E(z)=\operatorname{endpoint}(E^{-1}(z)):\mathbb C\to X$.
-/
def planarUniformizingProjection
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ) : ℂ → X :=
  fun z ↦ endpoint (E.toHomeomorph.symm z)

/--
%%handwave
name:
  Fibers of a planar uniformizing projection are translation orbits
statement:
  Let $p:\mathbb C\to X$ be the endpoint projection expressed through a
  planar biholomorphism, and let $L\subset\mathbb C$ be the subgroup of deck
  translation vectors. For $z,w\in\mathbb C$, one has $p(z)=p(w)$ if and
  only if $z=\ell+w$ for some $\ell\in L$.
proof:
  Equal endpoints put the corresponding lifts in one fiber. Transitivity of
  the deck action supplies a deck transformation carrying the lift of $w$ to
  the lift of $z$, and its transported action is translation by its vector in
  $L$. Conversely, translation by a deck vector is a deck transformation and
  therefore preserves endpoints.
-/
theorem planarUniformizingProjection_eq_iff_mem_orbit
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ)
    {z w : ℂ} :
    planarUniformizingProjection E z = planarUniformizingProjection E w ↔
      z ∈ AddAction.orbit (planarDeckSubmodule E) w := by
  constructor
  · intro hzw
    have hfiber : endpoint (E.toHomeomorph.symm w) =
        endpoint (E.toHomeomorph.symm z) := by
      simpa [planarUniformizingProjection] using hzw.symm
    rcases deckHomeomorphism_same_fiber_transitive
        (E.toHomeomorph.symm w) (E.toHomeomorph.symm z) hfiber with
      ⟨gamma, hgamma⟩
    apply AddAction.mem_orbit_iff.mpr
    let ell : planarDeckSubmodule E :=
      ⟨planarDeckTranslation E gamma, ⟨Additive.ofMul gamma, rfl⟩⟩
    refine ⟨ell, ?_⟩
    change (planarDeckTranslation E gamma : ℂ) + w = z
    have h := conjugatedPlanarDeckBiholomorphic_apply E gamma w
    change E.toHomeomorph
        (deckHomeomorphism gamma (E.toHomeomorph.symm w)) =
      w + planarDeckTranslation E gamma at h
    rw [hgamma] at h
    simpa [add_comm] using h.symm
  · intro horbit
    rcases AddAction.mem_orbit_iff.mp horbit with ⟨ell, hell⟩
    rcases ell.2 with ⟨gamma, hgamma⟩
    change planarDeckTranslation E gamma.toMul = (ell : ℂ) at hgamma
    have h := conjugatedPlanarDeckBiholomorphic_apply E gamma.toMul w
    change E.toHomeomorph
        (deckHomeomorphism gamma.toMul (E.toHomeomorph.symm w)) =
      w + planarDeckTranslation E gamma.toMul at h
    have hz : z = w + planarDeckTranslation E gamma.toMul := by
      calc
        z = (ell : ℂ) + w := hell.symm
        _ = w + planarDeckTranslation E gamma.toMul := by
          rw [← hgamma]
          ac_rfl
    change endpoint (E.toHomeomorph.symm z) =
      endpoint (E.toHomeomorph.symm w)
    rw [hz, ← h]
    simp

/--
%%handwave
name:
  The planar deck-translation subgroup is discrete
statement:
  For a planar uniformizing coordinate
  $E:\widetilde X_{x_0}\to\mathbb C$, the subgroup
  $L=\tau(\pi_1(X,x_0))\subset\mathbb C$ of deck-translation vectors is
  discrete.
proof:
  The uniformizing projection is a covering map, so it is injective on some
  neighborhood $U$ of zero. A deck vector $\ell\in L\cap U$ lies in the same
  projection fiber as zero. Since both points lie in $U$, local injectivity
  gives $\ell=0$. Thus zero is isolated in $L$, and translations isolate every
  other subgroup element.
-/
theorem planarDeckSubmodule_discreteTopology
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ) :
    DiscreteTopology (planarDeckSubmodule E) := by
  let p : ℂ → X := planarUniformizingProjection E
  have hp_cover : IsCoveringMap p := by
    have h := (isCoveringMap_endpoint_of_riemannSurface X x₀).comp_homeomorph
      E.toHomeomorph.symm
    simpa [p, planarUniformizingProjection, Function.comp_def] using h
  rcases hp_cover.isLocalHomeomorph.isLocallyInjective 0 with
    ⟨U, hU_open, hzero_U, hU_injective⟩
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨U, hU_open, ?_⟩
  ext ell
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hell_U
    apply Subtype.ext
    apply hU_injective hell_U hzero_U
    exact (planarUniformizingProjection_eq_iff_mem_orbit E).mpr
      (AddAction.mem_orbit_iff.mpr ⟨ell, by
        change (ell : ℂ) + 0 = (ell : ℂ)
        simp⟩)
  · rintro rfl
    exact hzero_U

/--
%%handwave
name:
  The planar deck subgroup has rank zero, one, or two
statement:
  The integral rank of the planar deck-translation subgroup
  $L\subset\mathbb C$ is $0$, $1$, or $2$.
proof:
  The subgroup is discrete, and every discrete integral submodule of the
  two-dimensional real vector space $\mathbb C$ has integral rank at most
  two.
-/
theorem planarDeckSubmodule_finrank_cases
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ) :
    Module.finrank ℤ (planarDeckSubmodule E) = 0 ∨
      Module.finrank ℤ (planarDeckSubmodule E) = 1 ∨
        Module.finrank ℤ (planarDeckSubmodule E) = 2 := by
  letI : DiscreteTopology (planarDeckSubmodule E) :=
    planarDeckSubmodule_discreteTopology E
  exact discreteComplexSubmodule_finrank_cases (planarDeckSubmodule E)

/--
%%handwave
name:
  Rank-zero planar deck group gives the plane
statement:
  Let $E:\widetilde X_{x_0}\to\mathbb C$ be a planar uniformizing
  coordinate. If its deck-translation subgroup has integral rank zero, then
  $X$ is biholomorphic to $\mathbb C$.
proof:
  A torsion-free integral module of rank zero is trivial. Hence every orbit of
  the deck-translation subgroup is a singleton, so the planar uniformizing
  projection is injective. Equivalently, the endpoint projection of the
  path-class cover is injective. It is therefore biholomorphic, and composing
  its inverse with $E$ identifies $X$ with the plane.
-/
theorem biholomorphicSurfaces_complexPlane_of_planarDeckSubmodule_finrank_zero
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ)
    (hrank : Module.finrank ℤ (planarDeckSubmodule E) = 0) :
    BiholomorphicSurfaces X ℂ := by
  letI : DiscreteTopology (planarDeckSubmodule E) :=
    planarDeckSubmodule_discreteTopology E
  have hL_bot : planarDeckSubmodule E = ⊥ :=
    discreteComplexSubmodule_eq_bot_of_finrank_zero
      (planarDeckSubmodule E) hrank
  have hp_injective : Function.Injective (planarUniformizingProjection E) := by
    intro z w hzw
    have horbit :=
      (planarUniformizingProjection_eq_iff_mem_orbit E).mp hzw
    rcases AddAction.mem_orbit_iff.mp horbit with ⟨ell, hell⟩
    have hell_zero : (ell : ℂ) = 0 := by
      have : (ell : ℂ) ∈ (⊥ : Submodule ℤ ℂ) := by
        rw [← hL_bot]
        exact ell.property
      simpa using this
    change (ell : ℂ) + w = z at hell
    rw [hell_zero] at hell
    simpa using hell.symm
  have hendpoint_injective : Function.Injective
      (endpoint : PathHomotopyUniversalCover X x₀ → X) := by
    intro y z hyz
    apply E.toHomeomorph.injective
    apply hp_injective
    simpa [planarUniformizingProjection] using hyz
  let P : Biholomorphic (PathHomotopyUniversalCover X x₀) X :=
    JJMath.Uniformization.PathHomotopyUniversalCover.biholomorphicEndpointOfInjective
      hendpoint_injective
  exact ⟨P.symm.trans E⟩

/--
%%handwave
name:
  Rank-one planar deck group gives the cylinder
statement:
  Let $E:\widetilde X_{x_0}\to\mathbb C$ be a planar uniformizing
  coordinate. If its deck-translation subgroup has integral rank one, then
  $X$ is biholomorphic to the punctured plane $\mathbb C^\times$.
proof:
  A discrete rank-one subgroup is $\mathbb Z\omega$ for some nonzero
  $\omega$. The planar uniformizing projection and the rescaled exponential
  $z\mapsto\exp(2\pi i z/\omega)$ have exactly the same fibers. Their
  quotient-map universal properties give inverse homeomorphisms between $X$
  and $\mathbb C^\times$. The forward homeomorphism is holomorphic after
  pullback to the plane, hence is biholomorphic by the complex inverse
  function theorem.
-/
theorem biholomorphicSurfaces_complexCylinder_of_planarDeckSubmodule_finrank_one
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ)
    (hrank : Module.finrank ℤ (planarDeckSubmodule E) = 1) :
    BiholomorphicSurfaces X ComplexCylinder := by
  letI : DiscreteTopology (planarDeckSubmodule E) :=
    planarDeckSubmodule_discreteTopology E
  rcases discreteComplexSubmodule_eq_zmultiples_of_finrank_one
      (planarDeckSubmodule E) hrank with ⟨omega, homega, hL⟩
  let p : ℂ → X := planarUniformizingProjection E
  let q : ℂ → ComplexCylinder := scaledComplexExponentialCover omega
  have hp_cover : IsCoveringMap p := by
    have h := (isCoveringMap_endpoint_of_riemannSurface X x₀).comp_homeomorph
      E.toHomeomorph.symm
    simpa [p, planarUniformizingProjection, Function.comp_def] using h
  have hp_surjective : Function.Surjective p := by
    intro x
    rcases endpoint_surjective_of_riemannSurface X x₀ x with ⟨y, hy⟩
    refine ⟨E.toHomeomorph y, ?_⟩
    simpa [p, planarUniformizingProjection] using hy
  have hq_cover : IsCoveringMap q := by
    simpa [q] using scaledComplexExponentialCover_isCoveringMap omega homega
  have hq_surjective : Function.Surjective q := by
    simpa [q] using scaledComplexExponentialCover_surjective omega homega
  let pC : C(ℂ, X) := ⟨p, hp_cover.continuous⟩
  let qC : C(ℂ, ComplexCylinder) := ⟨q, hq_cover.continuous⟩
  have hp_quotient : Topology.IsQuotientMap pC :=
    hp_cover.isQuotientMap hp_surjective
  have hq_quotient : Topology.IsQuotientMap qC :=
    hq_cover.isQuotientMap hq_surjective
  have hq_factors : Function.FactorsThrough qC pC := by
    intro z w hzw
    apply (scaledComplexExponentialCover_eq_iff_mem_orbit omega homega).mpr
    have horbit :=
      (planarUniformizingProjection_eq_iff_mem_orbit E).mp hzw
    change z ∈ AddAction.orbit (planarDeckSubmodule E).toAddSubgroup w at horbit
    rw [hL] at horbit
    exact horbit
  have hp_factors : Function.FactorsThrough pC qC := by
    intro z w hzw
    apply (planarUniformizingProjection_eq_iff_mem_orbit E).mpr
    have horbit :=
      (scaledComplexExponentialCover_eq_iff_mem_orbit omega homega).mp hzw
    change z ∈ AddAction.orbit (planarDeckSubmodule E).toAddSubgroup w
    rw [hL]
    exact horbit
  let phi : C(X, ComplexCylinder) :=
    hp_quotient.lift qC hq_factors
  let psi : C(ComplexCylinder, X) :=
    hq_quotient.lift pC hp_factors
  have hphi_p (z : ℂ) : phi (p z) = q z := by
    change (hp_quotient.lift qC hq_factors) (pC z) = qC z
    exact congrArg (fun F : C(ℂ, ComplexCylinder) ↦ F z)
      (hp_quotient.lift_comp qC hq_factors)
  have hpsi_q (z : ℂ) : psi (q z) = p z := by
    change (hq_quotient.lift pC hp_factors) (qC z) = pC z
    exact congrArg (fun F : C(ℂ, X) ↦ F z)
      (hq_quotient.lift_comp pC hp_factors)
  let H : X ≃ₜ ComplexCylinder :=
    { toFun := phi
      invFun := psi
      left_inv := by
        intro x
        rcases hp_surjective x with ⟨z, rfl⟩
        rw [hphi_p, hpsi_q]
      right_inv := by
        intro t
        rcases hq_surjective t with ⟨z, rfl⟩
        rw [hpsi_q, hphi_p]
      continuous_toFun := phi.continuous
      continuous_invFun := psi.continuous }
  have hphi_holomorphic : HolomorphicMap X ComplexCylinder phi := by
    apply JJMath.Uniformization.PathHomotopyUniversalCover.holomorphicMap_of_comp_endpoint
      (x₀ := x₀)
    have heq :
        (fun y : PathHomotopyUniversalCover X x₀ ↦ phi (endpoint y)) =
          fun y ↦ q (E.toHomeomorph y) := by
      funext y
      rw [← hphi_p (E.toHomeomorph y)]
      simp [p, planarUniformizingProjection]
    change HolomorphicMap (PathHomotopyUniversalCover X x₀)
      ComplexCylinder (fun y ↦ phi (endpoint y))
    rw [heq]
    exact (scaledComplexExponentialCover_holomorphic omega).comp
      E.holomorphic_toFun
  exact biholomorphicSurfaces_complexCylinder_of_homeomorph_holomorphic
    H hphi_holomorphic

/--
%%handwave
name:
  Rank-two planar deck group gives a complex torus
statement:
  Let $E:\widetilde X_{x_0}\to\mathbb C$ be a planar uniformizing
  coordinate. If its deck-translation subgroup $L$ has integral rank two,
  then $L$ is a full complex lattice and $X$ is biholomorphic to
  $\mathbb C/L$.
proof:
  Discreteness and rank two make $L$ a full lattice. The planar uniformizing
  projection and the lattice quotient projection have exactly the same
  fibers, namely the $L$-orbits. Their quotient-map universal properties give
  inverse homeomorphisms between $X$ and $\mathbb C/L$. Holomorphicity in
  both directions descends through the path-class endpoint charts and the
  preferred lattice-quotient charts.
-/
theorem biholomorphicSurfaces_complexTorus_of_planarDeckSubmodule_finrank_two
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) ℂ)
    (hrank : Module.finrank ℤ (planarDeckSubmodule E) = 2) :
    ∃ Lambda : ComplexLattice, BiholomorphicSurfaces X (ComplexTorus Lambda) := by
  letI : DiscreteTopology (planarDeckSubmodule E) :=
    planarDeckSubmodule_discreteTopology E
  let Lambda : ComplexLattice :=
    complexLatticeOfDiscreteFinrankTwo (planarDeckSubmodule E) hrank
  let p : ℂ → X := planarUniformizingProjection E
  let q : ℂ → ComplexTorus Lambda := complexTorusQuotientMk Lambda
  have hp_cover : IsCoveringMap p := by
    have h := (isCoveringMap_endpoint_of_riemannSurface X x₀).comp_homeomorph
      E.toHomeomorph.symm
    simpa [p, planarUniformizingProjection, Function.comp_def] using h
  have hp_surjective : Function.Surjective p := by
    intro x
    rcases endpoint_surjective_of_riemannSurface X x₀ x with ⟨y, hy⟩
    refine ⟨E.toHomeomorph y, ?_⟩
    simpa [p, planarUniformizingProjection] using hy
  have hq_surjective : Function.Surjective q :=
    (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).surjective
  let pC : C(ℂ, X) := ⟨p, hp_cover.continuous⟩
  let qC : C(ℂ, ComplexTorus Lambda) :=
    ⟨q, (complexTorusQuotientMk_isCoveringMap Lambda).continuous⟩
  have hp_quotient : Topology.IsQuotientMap pC :=
    hp_cover.isQuotientMap hp_surjective
  have hq_quotient : Topology.IsQuotientMap qC :=
    (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).toIsQuotientMap
  have hq_factors : Function.FactorsThrough qC pC := by
    intro z w hzw
    apply (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).apply_eq_iff_mem_orbit.mpr
    change z ∈ AddAction.orbit (planarDeckSubmodule E) w
    exact (planarUniformizingProjection_eq_iff_mem_orbit E).mp hzw
  have hp_factors : Function.FactorsThrough pC qC := by
    intro z w hzw
    apply (planarUniformizingProjection_eq_iff_mem_orbit E).mpr
    change z ∈ AddAction.orbit Lambda.carrier w
    exact (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).apply_eq_iff_mem_orbit.mp hzw
  let phi : C(X, ComplexTorus Lambda) :=
    hp_quotient.lift qC hq_factors
  let psi : C(ComplexTorus Lambda, X) :=
    hq_quotient.lift pC hp_factors
  have hphi_p (z : ℂ) : phi (p z) = q z := by
    change (hp_quotient.lift qC hq_factors) (pC z) = qC z
    exact congrArg (fun F : C(ℂ, ComplexTorus Lambda) ↦ F z)
      (hp_quotient.lift_comp qC hq_factors)
  have hpsi_q (z : ℂ) : psi (q z) = p z := by
    change (hq_quotient.lift pC hp_factors) (qC z) = pC z
    exact congrArg (fun F : C(ℂ, X) ↦ F z)
      (hq_quotient.lift_comp pC hp_factors)
  let H : X ≃ₜ ComplexTorus Lambda :=
    { toFun := phi
      invFun := psi
      left_inv := by
        intro x
        rcases hp_surjective x with ⟨z, rfl⟩
        rw [hphi_p, hpsi_q]
      right_inv := by
        intro t
        rcases hq_surjective t with ⟨z, rfl⟩
        rw [hpsi_q, hphi_p]
      continuous_toFun := phi.continuous
      continuous_invFun := psi.continuous }
  have hp_holomorphic : HolomorphicMap ℂ X p := by
    change HolomorphicMap ℂ X (endpoint ∘ E.toHomeomorph.symm)
    exact
      (JJMath.Uniformization.PathHomotopyUniversalCover.holomorphicMap_endpoint
        (X := X) (x₀ := x₀)).comp E.holomorphic_invFun
  have hphi_holomorphic : HolomorphicMap X (ComplexTorus Lambda) phi := by
    apply JJMath.Uniformization.PathHomotopyUniversalCover.holomorphicMap_of_comp_endpoint
      (x₀ := x₀)
    have heq : (fun y : PathHomotopyUniversalCover X x₀ ↦ phi (endpoint y)) =
        fun y ↦ q (E.toHomeomorph y) := by
      funext y
      rw [← hphi_p (E.toHomeomorph y)]
      simp [p, planarUniformizingProjection]
    change HolomorphicMap (PathHomotopyUniversalCover X x₀)
      (ComplexTorus Lambda) (fun y ↦ phi (endpoint y))
    rw [heq]
    exact (complexTorusQuotientMk_holomorphic Lambda).comp E.holomorphic_toFun
  have hpsi_holomorphic : HolomorphicMap (ComplexTorus Lambda) X psi := by
    apply holomorphicMap_of_comp_complexTorusQuotientMk Lambda
    have heq : (psi ∘ complexTorusQuotientMk Lambda) = p := by
      funext z
      exact hpsi_q z
    rw [heq]
    exact hp_holomorphic
  refine ⟨Lambda, ⟨?_⟩⟩
  exact
    { toHomeomorph := H
      holomorphic_toFun := hphi_holomorphic
      holomorphic_invFun := hpsi_holomorphic }

end

end Uniformization

end JJMath
