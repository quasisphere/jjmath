import JJMath.Uniformization.Classification.HolomorphicCover

/-!
# Comparing based universal covers

The path-homotopy universal cover is based, while the classification
predicates quantify over every base point.  This file constructs the canonical
kind of comparison needed between two choices of base point, using uniqueness
of lifts through covering maps.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

open JJMath.PathHomotopyUniversalCover

noncomputable section

/--
%%handwave
name:
  A homeomorphism is a covering map
statement:
  Every homeomorphism $H:Y\to X$, regarded as a continuous map, is a
  one-sheeted covering map.
proof:
  Take the whole base as an evenly covered neighborhood. The preimage is the
  whole source, and $H$ identifies it with the base times a one-point fiber.
-/
theorem homeomorph_isCoveringMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (H : Y ≃ₜ X) : IsCoveringMap H := by
  intro x
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Unit)
  refine ⟨inferInstance, Set.univ, Set.mem_univ x, isOpen_univ, ?_, ?_⟩
  · simp
  · let K : {y : Y // y ∈ H ⁻¹' (Set.univ : Set X)} ≃ₜ
        ({x : X // x ∈ (Set.univ : Set X)} × Unit) :=
      { toFun := fun y ↦ (⟨H y, Set.mem_univ _⟩, Unit.unit)
        invFun := fun xu ↦ ⟨H.symm xu.1, Set.mem_univ _⟩
        left_inv := by
          intro y
          apply Subtype.ext
          exact H.symm_apply_apply y
        right_inv := by
          intro xu
          apply Prod.ext
          · apply Subtype.ext
            exact H.apply_symm_apply xu.1
          · exact Subsingleton.elim _ _
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact ⟨K, fun _ ↦ rfl⟩

/--
%%handwave
name:
  A holomorphic map lifts holomorphically to the path-class cover
statement:
  Let $p:Y\to X$ be holomorphic between complex one-manifolds and let
  $F:Y\to\widetilde X_{x_0}$ be continuous. If
  $\pi(F(y))=p(y)$ for every $y\in Y$, then $F$ is holomorphic.
proof:
  In a pulled-back cover chart around $F(y)$, the lift is locally the inverse
  cover chart composed with the associated chart of $X$ and with $p$. This is
  a composite of holomorphic maps, and covering-map uniqueness identifies it
  locally with $F$.
-/
theorem holomorphicMap_to_pathHomotopyUniversalCover_of_endpoint_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X}
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [ComplexOneManifold Y]
    {p : Y → X} {F : Y → PathHomotopyUniversalCover X x₀}
    (hF : Continuous F) (hp : HolomorphicMap Y X p)
    (hendpoint : ∀ y, endpoint (F y) = p y) :
    HolomorphicMap Y (PathHomotopyUniversalCover X x₀) F := by
  let C := PathHomotopyUniversalCover X x₀
  letI : IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ C :=
    pathHomotopyUniversalCover_isManifold (Y := X) x₀
  intro y
  let e : OpenPartialHomeomorph C ℂ := chartAt ℂ (F y)
  have he : e ∈ atlas ℂ C := chart_mem_atlas ℂ (F y)
  have hFy : F y ∈ e.source := mem_chart_source ℂ (F y)
  let b : OpenPartialHomeomorph X ℂ :=
    baseChartOfCoverChart (x₀ := x₀) e he
  have hb : b ∈ atlas ℂ X :=
    baseChartOfCoverChart_mem_atlas (x₀ := x₀) e he
  have hpy_source : p y ∈ b.source := by
    rw [← hendpoint y]
    exact coverChart_source_projection_mem_baseChart_source
      (x₀ := x₀) e he hFy
  have hcoord_y : e (F y) = b (p y) := by
    rw [← hendpoint y]
    exact coverChart_apply_eq_baseChart_apply_endpoint
      (x₀ := x₀) e he hFy
  have hbpy_target : b (p y) ∈ e.target := by
    rw [← hcoord_y]
    exact e.map_source hFy
  have hp_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) p y := hp y
  have hb_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) b (p y) :=
    mdifferentiableAt_atlas hb hpy_source
  have he_symm_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) e.symm (b (p y)) :=
    mdifferentiableAt_atlas_symm he hbpy_target
  have hbranch : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) (e.symm ∘ b ∘ p) y :=
    he_symm_mdiff.comp y (hb_mdiff.comp y hp_mdiff)
  apply hbranch.congr_of_eventuallyEq
  have hF_source : F ⁻¹' e.source ∈ nhds y :=
    hF.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hFy)
  filter_upwards [hF_source] with y' hFy'
  change F y' = e.symm (b (p y'))
  calc
    F y' = e.symm (e (F y')) := (e.left_inv hFy').symm
    _ = e.symm (b (endpoint (F y'))) := by
      rw [coverChart_apply_eq_baseChart_apply_endpoint
        (x₀ := x₀) e he hFy']
    _ = e.symm (b (p y')) := by rw [hendpoint y']

/--
%%handwave
name: Comparison homeomorphism for a simply connected cover
statement:
  Given a simply connected covering $p:Y\to X$, a point $y_0\in Y$, and
  $p(y_0)=x_0$, define the homeomorphism
  $Y\cong\widetilde X_{x_0}$ over $X$ that sends $y_0$ to the constant path
  class.
-/
def simplyConnectedCoverHomeomorph
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ : X)
    {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    [LocPathConnectedSpace Y]
    (p : C(Y, X)) (hp : IsCoveringMap p) (y₀ : Y)
    (hy₀ : p y₀ = x₀) :
    Y ≃ₜ PathHomotopyUniversalCover X x₀ := by
  let C₀ := PathHomotopyUniversalCover X x₀
  letI : SimplyConnectedSpace C₀ :=
    pathHomotopyUniversalCover_simplyConnected (Y := X) x₀
  letI : LocPathConnectedSpace C₀ :=
    pathHomotopyUniversalCover_locPathConnected (Y := X) x₀
  let q : C(C₀, X) :=
    ⟨endpoint, continuous_endpoint_of_riemannSurface X x₀⟩
  let c₀ : C₀ := baseLift x₀
  let hF_exists :=
    (isCoveringMap_endpoint_of_riemannSurface X x₀).existsUnique_continuousMap_lifts
      p y₀ c₀ hy₀.symm
  let F : C(Y, C₀) := Classical.choose hF_exists
  have hF := (Classical.choose_spec hF_exists).1
  let hG_exists := hp.existsUnique_continuousMap_lifts q c₀ y₀ hy₀
  let G : C(C₀, Y) := Classical.choose hG_exists
  have hG := (Classical.choose_spec hG_exists).1
  let hYY_exists := hp.existsUnique_continuousMap_lifts p y₀ y₀ rfl
  have hYY_unique := (Classical.choose_spec hYY_exists).2
  let hCC_exists :=
    (isCoveringMap_endpoint_of_riemannSurface X x₀).existsUnique_continuousMap_lifts
      q c₀ c₀ rfl
  have hCC_unique := (Classical.choose_spec hCC_exists).2
  have hGF_data : (G.comp F) y₀ = y₀ ∧ p ∘ (G.comp F) = p := by
    constructor
    · exact (congrArg G hF.1).trans hG.1
    · funext y
      exact (congrFun hG.2 (F y)).trans (congrFun hF.2 y)
  have hidY_data : (ContinuousMap.id Y) y₀ = y₀ ∧
      p ∘ (ContinuousMap.id Y) = p := by simp
  have hGF : G.comp F = ContinuousMap.id Y :=
    (hYY_unique (G.comp F) hGF_data).trans
      (hYY_unique (ContinuousMap.id Y) hidY_data).symm
  have hFG_data : (F.comp G) c₀ = c₀ ∧ q ∘ (F.comp G) = q := by
    constructor
    · exact (congrArg F hG.1).trans hF.1
    · funext y
      exact (congrFun hF.2 (G y)).trans (congrFun hG.2 y)
  have hidC_data : (ContinuousMap.id C₀) c₀ = c₀ ∧
      q ∘ (ContinuousMap.id C₀) = q := by simp
  have hFG : F.comp G = ContinuousMap.id C₀ :=
    (hCC_unique (F.comp G) hFG_data).trans
      (hCC_unique (ContinuousMap.id C₀) hidC_data).symm
  exact
    { toFun := F
      invFun := G
      left_inv := fun y ↦ congrArg (fun K : C(Y, Y) ↦ K y) hGF
      right_inv := fun y ↦ congrArg (fun K : C(C₀, C₀) ↦ K y) hFG
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }

/--
%%handwave
name:
  A simply connected cover is homeomorphic to the path-class cover over the base
statement:
  Let $p:Y\to X$ be a covering map with simply connected, locally path
  connected total space, and choose $y_0\in Y$ over $x_0\in X$. Then there is
  a homeomorphism $H:Y\to\widetilde X_{x_0}$ satisfying
  $\pi(H(y))=p(y)$ for every $y\in Y$.
proof:
  Lift $p$ through the path-class cover and lift the endpoint projection
  through $p$, matching the chosen base points. Uniqueness of lifts over the
  two simply connected domains shows that the resulting maps are inverse.
-/
theorem simplyConnectedCoverHomeomorph_endpoint
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ : X)
    {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    [LocPathConnectedSpace Y]
    (p : C(Y, X)) (hp : IsCoveringMap p) (y₀ : Y)
    (hy₀ : p y₀ = x₀) (y : Y) :
    endpoint (simplyConnectedCoverHomeomorph x₀ p hp y₀ hy₀ y) = p y := by
  let C₀ := PathHomotopyUniversalCover X x₀
  letI : SimplyConnectedSpace C₀ :=
    pathHomotopyUniversalCover_simplyConnected (Y := X) x₀
  letI : LocPathConnectedSpace C₀ :=
    pathHomotopyUniversalCover_locPathConnected (Y := X) x₀
  let q : C(C₀, X) :=
    ⟨endpoint, continuous_endpoint_of_riemannSurface X x₀⟩
  let c₀ : C₀ := baseLift x₀
  let hF_exists :=
    (isCoveringMap_endpoint_of_riemannSurface X x₀).existsUnique_continuousMap_lifts
      p y₀ c₀ hy₀.symm
  let F : C(Y, C₀) := Classical.choose hF_exists
  have hF := (Classical.choose_spec hF_exists).1
  change q (F y) = p y
  exact congrFun hF.2 y

/-- A basepoint-change homeomorphism between path-homotopy universal covers,
together with the fact that it preserves the endpoint projection in both
directions. -/
structure PathHomotopyUniversalCoverBasepointChange
    {X : Type} [TopologicalSpace X] (x₀ x₁ : X) where
  /-- The comparison homeomorphism. -/
  toHomeomorph :
    PathHomotopyUniversalCover X x₀ ≃ₜ PathHomotopyUniversalCover X x₁
  /-- The forward comparison preserves endpoints. -/
  endpoint_to : ∀ y, endpoint (toHomeomorph y) = endpoint y
  /-- The inverse comparison preserves endpoints. -/
  endpoint_inv : ∀ y, endpoint (toHomeomorph.symm y) = endpoint y

/--
%%handwave
name: Basepoint-change data for path-homotopy universal covers
statement:
  For $x_0,x_1\in X$, choose a homeomorphism
  $\widetilde X_{x_0}\cong\widetilde X_{x_1}$ that commutes with both endpoint
  projections to $X$.
-/
def pathHomotopyUniversalCoverBasepointChange
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ x₁ : X) : PathHomotopyUniversalCoverBasepointChange x₀ x₁ := by
  let C₀ := PathHomotopyUniversalCover X x₀
  let C₁ := PathHomotopyUniversalCover X x₁
  letI : SimplyConnectedSpace C₀ :=
    pathHomotopyUniversalCover_simplyConnected (Y := X) x₀
  letI : LocPathConnectedSpace C₀ :=
    pathHomotopyUniversalCover_locPathConnected (Y := X) x₀
  letI : SimplyConnectedSpace C₁ :=
    pathHomotopyUniversalCover_simplyConnected (Y := X) x₁
  letI : LocPathConnectedSpace C₁ :=
    pathHomotopyUniversalCover_locPathConnected (Y := X) x₁
  let p₀ : C(C₀, X) :=
    ⟨endpoint, continuous_endpoint_of_riemannSurface X x₀⟩
  let p₁ : C(C₁, X) :=
    ⟨endpoint, continuous_endpoint_of_riemannSurface X x₁⟩
  let a₀ : C₀ := baseLift x₀
  let b₀ : C₁ := liftOfPoint x₁ x₀
  have hb₀ : p₁ b₀ = p₀ a₀ := rfl
  let cov₀ := isCoveringMap_endpoint_of_riemannSurface X x₀
  let cov₁ := isCoveringMap_endpoint_of_riemannSurface X x₁
  let hF_exists := cov₁.existsUnique_continuousMap_lifts p₀ a₀ b₀ hb₀
  let F : C(C₀, C₁) := Classical.choose hF_exists
  have hF := (Classical.choose_spec hF_exists).1
  let hG_exists := cov₀.existsUnique_continuousMap_lifts p₁ b₀ a₀ hb₀.symm
  let G : C(C₁, C₀) := Classical.choose hG_exists
  have hG := (Classical.choose_spec hG_exists).1
  let hH₀_exists := cov₀.existsUnique_continuousMap_lifts p₀ a₀ a₀ rfl
  let H₀ : C(C₀, C₀) := Classical.choose hH₀_exists
  have hH₀_unique := (Classical.choose_spec hH₀_exists).2
  let hH₁_exists := cov₁.existsUnique_continuousMap_lifts p₁ b₀ b₀ rfl
  let H₁ : C(C₁, C₁) := Classical.choose hH₁_exists
  have hH₁_unique := (Classical.choose_spec hH₁_exists).2
  have hGF_data : (G.comp F) a₀ = a₀ ∧ p₀ ∘ (G.comp F) = p₀ := by
    constructor
    · exact (congrArg G hF.1).trans hG.1
    · funext y
      exact (congrFun hG.2 (F y)).trans (congrFun hF.2 y)
  have hid₀_data : (ContinuousMap.id C₀) a₀ = a₀ ∧
      p₀ ∘ (ContinuousMap.id C₀) = p₀ := by simp
  have hGF : G.comp F = ContinuousMap.id C₀ :=
    (hH₀_unique (G.comp F) hGF_data).trans
      (hH₀_unique (ContinuousMap.id C₀) hid₀_data).symm
  have hFG_data : (F.comp G) b₀ = b₀ ∧ p₁ ∘ (F.comp G) = p₁ := by
    constructor
    · exact (congrArg F hG.1).trans hF.1
    · funext y
      exact (congrFun hF.2 (G y)).trans (congrFun hG.2 y)
  have hid₁_data : (ContinuousMap.id C₁) b₀ = b₀ ∧
      p₁ ∘ (ContinuousMap.id C₁) = p₁ := by simp
  have hFG : F.comp G = ContinuousMap.id C₁ :=
    (hH₁_unique (F.comp G) hFG_data).trans
      (hH₁_unique (ContinuousMap.id C₁) hid₁_data).symm
  let homeomorph : C₀ ≃ₜ C₁ :=
    { toFun := F
      invFun := G
      left_inv := fun y ↦ congrArg (fun K : C(C₀, C₀) ↦ K y) hGF
      right_inv := fun y ↦ congrArg (fun K : C(C₁, C₁) ↦ K y) hFG
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  refine
    { toHomeomorph := homeomorph
      endpoint_to := ?_
      endpoint_inv := ?_ }
  · intro y
    exact congrFun hF.2 y
  · intro y
    exact congrFun hG.2 y

/--
%%handwave
name: Biholomorphic basepoint change for universal covers
statement:
  For $x_0,x_1\in X$, bundle the basepoint-change homeomorphism
  $\widetilde X_{x_0}\to\widetilde X_{x_1}$ as a biholomorphism over $X$.
-/
def pathHomotopyUniversalCover_basepoint_biholomorphic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ x₁ : X) :
    Biholomorphic (PathHomotopyUniversalCover X x₀)
      (PathHomotopyUniversalCover X x₁) := by
  let D := pathHomotopyUniversalCoverBasepointChange x₀ x₁
  exact
    { toHomeomorph := D.toHomeomorph
      holomorphic_toFun :=
        PathHomotopyUniversalCover.holomorphicMap_of_continuous_endpoint_eq
          D.toHomeomorph.continuous D.endpoint_to
      holomorphic_invFun :=
        PathHomotopyUniversalCover.holomorphicMap_of_continuous_endpoint_eq
          D.toHomeomorph.symm.continuous D.endpoint_inv }

/--
%%handwave
name:
  Universal covers based at two points are biholomorphic
statement:
  If $X$ is a Riemann surface and $x_0,x_1\in X$, then the path-class
  universal covers $\widetilde X_{x_0}$ and $\widetilde X_{x_1}$ are
  biholomorphic.
proof:
  Lift each endpoint projection through the other cover with compatible
  chosen lifts.  Uniqueness of covering lifts makes the maps inverse, and
  endpoint preservation makes both maps holomorphic in pulled-back charts.
-/
theorem pathHomotopyUniversalCover_basepoint_biholomorphicSurfaces
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (x₀ x₁ : X) :
    BiholomorphicSurfaces (PathHomotopyUniversalCover X x₀)
      (PathHomotopyUniversalCover X x₁) :=
  ⟨pathHomotopyUniversalCover_basepoint_biholomorphic x₀ x₁⟩

end

end Uniformization

end JJMath
