import JJMath.Uniformization.Biholomorphic
import JJMath.Uniformization.RadoSecondCountable

/-!
# Holomorphic covering maps

This file supplies the holomorphic part of the path-homotopy universal-cover
infrastructure.  The underlying covering map, its local sheets, and its deck
homeomorphisms are constructed in `JJMath.Hyperbolic.Cover`; here we record
that the pulled-back complex charts make the endpoint projection and every
deck transformation holomorphic.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

universe u v

open JJMath.PathHomotopyUniversalCover

/-- A holomorphic covering map between complex manifolds. -/
structure IsHolomorphicCoveringMap
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) : Prop where
  /-- The underlying map is a topological covering map. -/
  isCoveringMap : IsCoveringMap f
  /-- The map is holomorphic. -/
  holomorphic : HolomorphicMap X Y f

namespace PathHomotopyUniversalCover

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {x₀ : X}

/--
%%handwave
name:
  The endpoint projection is holomorphic
statement:
  For a Riemann surface $X$ and $x_0\in X$, the endpoint projection
  $\pi:\widetilde X_{x_0}\to X$ is holomorphic for the pulled-back complex
  structure on $\widetilde X_{x_0}$.
proof:
  A pulled-back cover chart is the endpoint projection followed by a complex
  chart on $X$, so the coordinate expression of $\pi$ is the identity.
-/
theorem holomorphicMap_endpoint [RiemannSurface X] :
    HolomorphicMap (PathHomotopyUniversalCover X x₀) X endpoint := by
  letI : IsManifold 𝓘(ℂ) ⊤ (PathHomotopyUniversalCover X x₀) :=
    pathHomotopyUniversalCover_isManifold (Y := X) x₀
  intro y
  let e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ :=
    chartAt ℂ y
  have he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀) :=
    chart_mem_atlas ℂ y
  let b : OpenPartialHomeomorph X ℂ :=
    baseChartOfCoverChart (x₀ := x₀) e he
  have hb : b ∈ atlas ℂ X :=
    baseChartOfCoverChart_mem_atlas (x₀ := x₀) e he
  have hy : y ∈ e.source := mem_chart_source ℂ y
  have hendpoint_source : endpoint y ∈ b.source :=
    coverChart_source_projection_mem_baseChart_source (x₀ := x₀) e he hy
  have hey : e y = b (endpoint y) :=
    coverChart_apply_eq_baseChart_apply_endpoint (x₀ := x₀) e he hy
  have hey_target : e y ∈ b.target := by
    rw [hey]
    exact b.map_source hendpoint_source
  have he_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e y :=
    mdifferentiableAt_atlas he hy
  have hb_symm_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) b.symm (e y) :=
    mdifferentiableAt_atlas_symm hb hey_target
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (b.symm ∘ e) y :=
    hb_symm_mdiff.comp y he_mdiff
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hy] with y' hy'
  change endpoint y' = b.symm (e y')
  rw [coverChart_apply_eq_baseChart_apply_endpoint (x₀ := x₀) e he hy']
  exact (b.left_inv
    (coverChart_source_projection_mem_baseChart_source (x₀ := x₀) e he hy')).symm

/--
%%handwave
name:
  A simply connected base has one path class over each endpoint
statement:
  If $X$ is simply connected and $x_0\in X$, then the endpoint projection
  $\pi:\widetilde X_{x_0}\to X$ is injective.
proof:
  Two points over the same endpoint are represented by two paths from $x_0$
  to that endpoint. Simple connectedness makes those paths endpoint-fixed
  homotopic, so their path classes, and hence the two points of the cover,
  are equal.
-/
theorem endpoint_injective_of_simplyConnected
    [SimplyConnectedSpace X] :
    Function.Injective
      (endpoint : PathHomotopyUniversalCover X x₀ → X) := by
  rintro ⟨x, gamma⟩ ⟨y, eta⟩ hxy
  change x = y at hxy
  subst y
  congr
  exact Subsingleton.elim gamma eta

/--
%%handwave
name:
  An injective path-class endpoint map is biholomorphic
statement:
  Let $X$ be a Riemann surface and $x_0\in X$. If the endpoint projection
  $\pi:\widetilde X_{x_0}\to X$ is injective, then it is a biholomorphic
  equivalence.
proof:
  The endpoint projection is already a surjective holomorphic covering map,
  hence an injective one is a homeomorphism. In every pulled-back cover chart,
  its inverse is the inverse cover chart composed with the corresponding
  chart of $X$, so the inverse is holomorphic.
-/
noncomputable def biholomorphicEndpointOfInjective [RiemannSurface X]
    (hinjective : Function.Injective
      (endpoint : PathHomotopyUniversalCover X x₀ → X)) :
    Biholomorphic (PathHomotopyUniversalCover X x₀) X := by
  let C := PathHomotopyUniversalCover X x₀
  letI : IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ C :=
    pathHomotopyUniversalCover_isManifold (Y := X) x₀
  have hbijective : Function.Bijective (endpoint : C → X) :=
    ⟨hinjective, endpoint_surjective_of_riemannSurface X x₀⟩
  let E : C ≃ₜ X :=
    (isCoveringMap_endpoint_of_riemannSurface X x₀).isLocalHomeomorph
      |>.toHomeomorphOfBijective hbijective
  have hE_apply (y : C) : E y = endpoint y := rfl
  refine
    { toHomeomorph := E
      holomorphic_toFun := ?_
      holomorphic_invFun := ?_ }
  · simpa [hE_apply] using
      (holomorphicMap_endpoint (X := X) (x₀ := x₀))
  · intro x
    let y : C := E.symm x
    let e : OpenPartialHomeomorph C ℂ := chartAt ℂ y
    have he : e ∈ atlas ℂ C := chart_mem_atlas ℂ y
    have hy : y ∈ e.source := mem_chart_source ℂ y
    let b : OpenPartialHomeomorph X ℂ :=
      baseChartOfCoverChart (x₀ := x₀) e he
    have hb : b ∈ atlas ℂ X :=
      baseChartOfCoverChart_mem_atlas (x₀ := x₀) e he
    have hy_endpoint : endpoint y = x := by
      change E y = x
      exact E.apply_symm_apply x
    have hx_source : x ∈ b.source := by
      rw [← hy_endpoint]
      exact coverChart_source_projection_mem_baseChart_source
        (x₀ := x₀) e he hy
    have hey : e y = b x := by
      rw [← hy_endpoint]
      exact coverChart_apply_eq_baseChart_apply_endpoint
        (x₀ := x₀) e he hy
    have hbx_target : b x ∈ e.target := by
      rw [← hey]
      exact e.map_source hy
    have hb_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) b x :=
      mdifferentiableAt_atlas hb hx_source
    have he_symm_mdiff :
        MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
          (modelWithCornersSelf ℂ ℂ) e.symm (b x) :=
      mdifferentiableAt_atlas_symm he hbx_target
    have hcomp : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) (e.symm ∘ b) x :=
      he_symm_mdiff.comp x hb_mdiff
    apply hcomp.congr_of_eventuallyEq
    have hb_source : b.source ∈ nhds x := b.open_source.mem_nhds hx_source
    have he_source : (fun x' ↦ E.symm x') ⁻¹' e.source ∈ nhds x :=
      E.symm.continuous.continuousAt.preimage_mem_nhds
        (e.open_source.mem_nhds hy)
    filter_upwards [hb_source, he_source] with x' hx'b hx'e
    change E.symm x' = e.symm (b x')
    calc
      E.symm x' = e.symm (e (E.symm x')) := (e.left_inv hx'e).symm
      _ = e.symm (b (endpoint (E.symm x'))) := by
        rw [coverChart_apply_eq_baseChart_apply_endpoint
          (x₀ := x₀) e he hx'e]
      _ = e.symm (b x') := by
        have : endpoint (E.symm x') = x' := by
          change E (E.symm x') = x'
          exact E.apply_symm_apply x'
        rw [this]

/--
%%handwave
name:
  Holomorphicity descends through the path-class endpoint cover
statement:
  Let $X$ be a Riemann surface, let $Y$ be a complex one-manifold, and let
  $F:X\to Y$. If
  $F\circ\pi:\widetilde X_{x_0}\to Y$ is holomorphic, then $F$ is
  holomorphic.
proof:
  Around any lift $y$ of $x\in X$, a pulled-back cover chart gives a local
  inverse branch of the endpoint projection. This branch is the inverse cover
  chart composed with its associated chart on $X$, hence is holomorphic.
  Locally, $F$ is the composite of this branch with the holomorphic map
  $F\circ\pi$.
-/
theorem holomorphicMap_of_comp_endpoint [RiemannSurface X]
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [ComplexOneManifold Y] {F : X → Y}
    (hF : HolomorphicMap (PathHomotopyUniversalCover X x₀) Y
      (F ∘ endpoint)) :
    HolomorphicMap X Y F := by
  let C := PathHomotopyUniversalCover X x₀
  letI : IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ C :=
    pathHomotopyUniversalCover_isManifold (Y := X) x₀
  intro x
  let y : C := liftOfPoint x₀ x
  have hy_endpoint : endpoint y = x := endpoint_liftOfPoint x₀ x
  let e : OpenPartialHomeomorph C ℂ := chartAt ℂ y
  have he : e ∈ atlas ℂ C := chart_mem_atlas ℂ y
  have hy : y ∈ e.source := mem_chart_source ℂ y
  let b : OpenPartialHomeomorph X ℂ :=
    baseChartOfCoverChart (x₀ := x₀) e he
  have hb : b ∈ atlas ℂ X :=
    baseChartOfCoverChart_mem_atlas (x₀ := x₀) e he
  have hx_source : x ∈ b.source := by
    rw [← hy_endpoint]
    exact coverChart_source_projection_mem_baseChart_source
      (x₀ := x₀) e he hy
  have hey : e y = b x := by
    rw [← hy_endpoint]
    exact coverChart_apply_eq_baseChart_apply_endpoint
      (x₀ := x₀) e he hy
  have hbx_target : b x ∈ e.target := by
    rw [← hey]
    exact e.map_source hy
  have hb_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) b x :=
    mdifferentiableAt_atlas hb hx_source
  have he_symm_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) e.symm (b x) :=
    mdifferentiableAt_atlas_symm he hbx_target
  have hbranch : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) (e.symm ∘ b) x :=
    he_symm_mdiff.comp x hb_mdiff
  have hbranch_x : e.symm (b x) = y := by
    rw [← hey]
    exact e.left_inv hy
  have hcomp : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ)
      ((F ∘ endpoint) ∘ (e.symm ∘ b)) x := by
    have hout := hF y
    rw [← hbranch_x] at hout
    exact hout.comp x hbranch
  apply hcomp.congr_of_eventuallyEq
  have he_target_nhds : b ⁻¹' e.target ∈ nhds x :=
    (b.continuousAt hx_source).preimage_mem_nhds
      (e.open_target.mem_nhds hbx_target)
  filter_upwards [b.open_source.mem_nhds hx_source, he_target_nhds]
    with x' hx' hbx'
  change F x' = F (endpoint (e.symm (b x')))
  congr 1
  have heinv : e.symm (b x') ∈ e.source := e.map_target hbx'
  calc
    x' = b.symm (b x') := (b.left_inv hx').symm
    _ = b.symm (e (e.symm (b x'))) := by rw [e.right_inv hbx']
    _ = endpoint (e.symm (b x')) := by
      rw [coverChart_apply_eq_baseChart_apply_endpoint
        (x₀ := x₀) e he heinv]
      exact b.left_inv
        (coverChart_source_projection_mem_baseChart_source
          (x₀ := x₀) e he heinv)

/--
%%handwave
name:
  Endpoint-preserving maps between path-class covers are holomorphic
statement:
  Let $F:\widetilde X_{x_0}\to\widetilde X_{x_1}$ be continuous. If
  $\pi_{x_1}(F(y))=\pi_{x_0}(y)$ for every $y$, then $F$ is holomorphic.
proof:
  In pulled-back charts centered at $y$ and $F(y)$, endpoint preservation
  makes the coordinate expression of $F$ the identity near $y$.
-/
theorem holomorphicMap_of_continuous_endpoint_eq
    [RiemannSurface X] {x₁ : X}
    {F : PathHomotopyUniversalCover X x₀ → PathHomotopyUniversalCover X x₁}
    (hF : Continuous F)
    (hendpoint : ∀ y, endpoint (F y) = endpoint y) :
    HolomorphicMap (PathHomotopyUniversalCover X x₀)
      (PathHomotopyUniversalCover X x₁) F := by
  letI : IsManifold 𝓘(ℂ) ⊤ (PathHomotopyUniversalCover X x₀) :=
    pathHomotopyUniversalCover_isManifold (Y := X) x₀
  letI : IsManifold 𝓘(ℂ) ⊤ (PathHomotopyUniversalCover X x₁) :=
    pathHomotopyUniversalCover_isManifold (Y := X) x₁
  intro y
  let e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ :=
    chartAt ℂ y
  let e' : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₁) ℂ :=
    chartAt ℂ (F y)
  have he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀) :=
    chart_mem_atlas ℂ y
  have he' : e' ∈ atlas ℂ (PathHomotopyUniversalCover X x₁) :=
    chart_mem_atlas ℂ (F y)
  have hy : y ∈ e.source := mem_chart_source ℂ y
  have hFy : F y ∈ e'.source := mem_chart_source ℂ (F y)
  have hcoord_y : e' (F y) = e y := by
    rw [chartAt_apply_eq_chartAt_endpoint_apply (x₀ := x₁) (F y) (F y) hFy]
    rw [chartAt_apply_eq_chartAt_endpoint_apply (x₀ := x₀) y y hy]
    rw [hendpoint]
  have hey_target : e y ∈ e'.target := by
    rw [← hcoord_y]
    exact e'.map_source hFy
  have he_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e y :=
    mdifferentiableAt_atlas he hy
  have he'_symm_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e'.symm (e y) :=
    mdifferentiableAt_atlas_symm he' hey_target
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (e'.symm ∘ e) y :=
    he'_symm_mdiff.comp y he_mdiff
  apply hcomp.congr_of_eventuallyEq
  have hsource : e.source ∈ nhds y := e.open_source.mem_nhds hy
  have htarget : F ⁻¹' e'.source ∈ nhds y :=
    hF.continuousAt.preimage_mem_nhds (e'.open_source.mem_nhds hFy)
  filter_upwards [hsource, htarget] with y' hy' hFy'
  change F y' = e'.symm (e y')
  have hcoord : e' (F y') = e y' := by
    change (chartAt ℂ (F y)) (F y') = (chartAt ℂ y) y'
    rw [chartAt_apply_eq_chartAt_endpoint_apply (x₀ := x₁) (F y) (F y') hFy']
    rw [chartAt_apply_eq_chartAt_endpoint_apply (x₀ := x₀) y y' hy']
    rw [hendpoint y]
    exact congrArg (chartAt ℂ (endpoint y)) (hendpoint y')
  calc
    F y' = e'.symm (e' (F y')) := (e'.left_inv hFy').symm
    _ = e'.symm (e y') := congrArg e'.symm hcoord

/--
%%handwave
name:
  Deck transformations are holomorphic
statement:
  For $\gamma\in\pi_1(X,x_0)$, the associated deck transformation of
  $\widetilde X_{x_0}$ is holomorphic.
proof:
  Deck transformations preserve the endpoint projection. In any two
  corresponding pulled-back charts, the deck transformation therefore has
  the identity as its local coordinate expression.
-/
theorem holomorphicMap_deckHomeomorphism [RiemannSurface X]
    (gamma : FundamentalGroup X x₀) :
    HolomorphicMap (PathHomotopyUniversalCover X x₀)
      (PathHomotopyUniversalCover X x₀) (deckHomeomorphism gamma) := by
  letI : IsManifold 𝓘(ℂ) ⊤ (PathHomotopyUniversalCover X x₀) :=
    pathHomotopyUniversalCover_isManifold (Y := X) x₀
  intro y
  let e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ :=
    chartAt ℂ y
  let e' : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ :=
    chartAt ℂ (deckHomeomorphism gamma y)
  have he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀) :=
    chart_mem_atlas ℂ y
  have he' : e' ∈ atlas ℂ (PathHomotopyUniversalCover X x₀) :=
    chart_mem_atlas ℂ (deckHomeomorphism gamma y)
  have hy : y ∈ e.source := mem_chart_source ℂ y
  have hgamma_y : deckHomeomorphism gamma y ∈ e'.source :=
    mem_chart_source ℂ (deckHomeomorphism gamma y)
  have hcoord_y : e' (deckHomeomorphism gamma y) = e y := by
    rw [chartAt_apply_eq_chartAt_endpoint_apply
      (x₀ := x₀) (deckHomeomorphism gamma y) (deckHomeomorphism gamma y) hgamma_y]
    rw [chartAt_apply_eq_chartAt_endpoint_apply (x₀ := x₀) y y hy]
    rw [endpoint_deckHomeomorphism]
  have hey_target : e y ∈ e'.target := by
    rw [← hcoord_y]
    exact e'.map_source hgamma_y
  have he_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e y :=
    mdifferentiableAt_atlas he hy
  have he'_symm_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e'.symm (e y) :=
    mdifferentiableAt_atlas_symm he' hey_target
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (e'.symm ∘ e) y :=
    he'_symm_mdiff.comp y he_mdiff
  apply hcomp.congr_of_eventuallyEq
  have hsource : e.source ∈ nhds y := e.open_source.mem_nhds hy
  have htarget : (deckHomeomorphism gamma) ⁻¹' e'.source ∈ nhds y :=
    (deckHomeomorphism gamma).continuous.continuousAt.preimage_mem_nhds
      (e'.open_source.mem_nhds hgamma_y)
  filter_upwards [hsource, htarget] with y' hy' hgamma_y'
  change deckHomeomorphism gamma y' = e'.symm (e y')
  have hcoord : e' (deckHomeomorphism gamma y') = e y' := by
    change
      (chartAt ℂ (deckHomeomorphism gamma y)) (deckHomeomorphism gamma y') =
        (chartAt ℂ y) y'
    rw [chartAt_apply_eq_chartAt_endpoint_apply
      (x₀ := x₀) (deckHomeomorphism gamma y) (deckHomeomorphism gamma y') hgamma_y']
    rw [chartAt_apply_eq_chartAt_endpoint_apply (x₀ := x₀) y y' hy']
    exact congrArg (chartAt ℂ (endpoint y)) (endpoint_deckHomeomorphism gamma y')
  calc
    deckHomeomorphism gamma y' = e'.symm (e' (deckHomeomorphism gamma y')) :=
      (e'.left_inv hgamma_y').symm
    _ = e'.symm (e y') := congrArg e'.symm hcoord

/--
%%handwave
name: Biholomorphic deck transformation of the universal cover
statement:
  For $\gamma\in\pi_1(X,x_0)$, bundle the deck transformation of the
  path-homotopy universal cover as a biholomorphic self-map.
-/
noncomputable def deckBiholomorphic [RiemannSurface X]
    (gamma : FundamentalGroup X x₀) :
    Biholomorphic (PathHomotopyUniversalCover X x₀)
      (PathHomotopyUniversalCover X x₀) where
  toHomeomorph := deckHomeomorphism gamma
  holomorphic_toFun := holomorphicMap_deckHomeomorphism gamma
  holomorphic_invFun := by
    simpa using holomorphicMap_deckHomeomorphism (X := X) (x₀ := x₀) gamma⁻¹

end PathHomotopyUniversalCover

end Uniformization

end JJMath
