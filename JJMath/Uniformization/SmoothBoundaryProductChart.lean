import JJMath.Manifold.SmoothImplicitLevel
import JJMath.Uniformization.LiouvilleExistence

/-!
# Smooth product charts at a surface boundary

The local defining function of a smooth boundary can be completed to a
smooth coordinate system.  After restricting the source, the domain is the
negative half of the first coordinate and its frontier is the zero level.
-/

open Set
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold 𝓘(ℝ, ℂ) ∞ X]

/-- A smooth coordinate chart in which a smooth domain boundary is the
vertical axis and the domain lies on its negative side. -/
structure SmoothBoundaryProductChart
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) where
  coordinate : PartialDiffeomorph
    𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) X (ℝ × ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
  point_mem : (p : X) ∈ coordinate.source
  point_coord : coordinate p = (0, 0)
  domain_iff_negative : ∀ x ∈ coordinate.source,
    x ∈ D.carrier ↔ (coordinate x).1 < 0
  frontier_iff_zero : ∀ x ∈ coordinate.source,
    x ∈ frontier D.carrier ↔ (coordinate x).1 = 0

/--
%%handwave
name:
  Boundary product coordinates for a smooth surface domain
statement:
  Let \(D\) be a smoothly bounded domain in a complex surface and let
  \(p\in\partial D\).  There is a smooth local coordinate map
  \(\Phi\) about \(p\), with \(\Phi(p)=(0,0)\), such that for every
  \(x\) in its source,
  \[
    x\in D\iff (\Phi(x))_1<0,
    \qquad
    x\in\partial D\iff (\Phi(x))_1=0.
  \]
proof:
  A local defining function for \(D\) has nonzero differential along the
  boundary.  The regular-level coordinate theorem makes that function the
  first coordinate; restricting the resulting chart to the defining
  neighborhood gives the asserted sign and zero-set descriptions.
-/
theorem exists_smoothBoundaryProductChart
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    Nonempty (SmoothBoundaryProductChart D p) := by
  rcases D.smooth_boundary p p.2 with
    ⟨e, he, hpe, r, hrsmooth, dr, hrderiv, hdr, hlocal⟩
  have hlocal_p := hlocal.self_of_nhds
  have hrzero : r (e (p : X)) = 0 := hlocal_p.2.2.mp p.2
  rcases JJMath.Manifold.exists_smoothRegularLevelPartialDiffeomorph_of_contDiffOnNhd
      hrsmooth hrderiv hdr with
    ⟨Psi, hpPsi, hPsiPoint, hPsiFirst⟩
  let eSmooth : PartialDiffeomorph
      𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    JJMath.Manifold.partialDiffeomorphOfMemMaximalAtlas e
      (IsManifold.subset_maximalAtlas he)
  let coord0 : PartialDiffeomorph
      𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) X (ℝ × ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    JJMath.Manifold.PartialDiffeomorph.trans eSmooth Psi
  have hpcoord0 : (p : X) ∈ coord0.source := by
    rw [show coord0.source =
        eSmooth.source ∩ eSmooth ⁻¹' Psi.source from
      PartialEquiv.trans_source eSmooth.toPartialEquiv Psi.toPartialEquiv]
    exact ⟨hpe, hpPsi⟩
  rcases mem_nhds_iff.mp hlocal with ⟨W, hWsub, hWopen, hpW⟩
  let coord : PartialDiffeomorph
      𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) X (ℝ × ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    JJMath.Manifold.PartialDiffeomorph.restrOpen coord0 W hWopen
  have hpcoord : (p : X) ∈ coord.source := by
    rw [show coord.source = coord0.source ∩ W from
      PartialEquiv.restr_source coord0.toPartialEquiv W]
    exact ⟨hpcoord0, hpW⟩
  refine ⟨{
    coordinate := coord
    point_mem := hpcoord
    point_coord := ?_
    domain_iff_negative := ?_
    frontier_iff_zero := ?_ }⟩
  · change Psi (e (p : X)) = (0, 0)
    simpa [hrzero] using hPsiPoint
  · intro x hx
    have hx' : x ∈ coord0.source ∧ x ∈ W := by
      simpa [coord] using hx
    have hxPsi : e x ∈ Psi.source := by
      have htrans : x ∈ eSmooth.source ∧ eSmooth x ∈ Psi.source := by
        simpa [coord0] using hx'.1
      exact htrans.2
    have hfirst : (coord x).1 = r (e x) := by
      change (Psi (e x)).1 = r (e x)
      exact hPsiFirst (e x) hxPsi
    rw [hfirst]
    exact (hWsub hx'.2).2.1
  · intro x hx
    have hx' : x ∈ coord0.source ∧ x ∈ W := by
      simpa [coord] using hx
    have hxPsi : e x ∈ Psi.source := by
      have htrans : x ∈ eSmooth.source ∧ eSmooth x ∈ Psi.source := by
        simpa [coord0] using hx'.1
      exact htrans.2
    have hfirst : (coord x).1 = r (e x) := by
      change (Psi (e x)).1 = r (e x)
      exact hPsiFirst (e x) hxPsi
    rw [hfirst]
    exact (hWsub hx'.2).2.2

/--
%%handwave
name: A fixed choice of product chart at each boundary point
statement:
  For every $p\in\partial\Omega$, choose a centered smooth product chart in
  which $\Omega$ is the negative first-coordinate side and the frontier is
  the zero slice.
-/
noncomputable def smoothBoundaryProductChartAt
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    SmoothBoundaryProductChart D p :=
  Classical.choice (exists_smoothBoundaryProductChart D p)

/--
%%handwave
name:
  The center belongs to its chosen boundary chart
statement:
  If \(p\in\partial D\), then \(p\) lies in the source of the chosen
  boundary product coordinate map \(\Phi_p\).
proof:
  This is one of the defining properties of the chosen product chart.
-/
theorem smoothBoundaryProductChartAt_point_mem
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    (p : X) ∈ (smoothBoundaryProductChartAt D p).coordinate.source :=
  (smoothBoundaryProductChartAt D p).point_mem

omit [IsManifold 𝓘(ℝ, ℂ) ∞ X] in
/--
%%handwave
name:
  A boundary product chart contains a centered ball
statement:
  Let \(\Phi\) be a boundary product chart centered at
  \(p\in\partial D\).  There is an \(\varepsilon>0\) such that
  \[
    B_{\mathbb R^2}(0,\varepsilon)\subseteq\operatorname{target}(\Phi).
  \]
proof:
  The chart sends \(p\) to the origin, so the origin belongs to its open
  target.  An open neighborhood of the origin in Euclidean space contains
  a positive-radius metric ball.
-/
theorem SmoothBoundaryProductChart.exists_target_ball
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (C : SmoothBoundaryProductChart D p) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      Metric.ball (0 : ℝ × ℝ) epsilon ⊆ C.coordinate.target := by
  have hzero_target : (0 : ℝ × ℝ) ∈ C.coordinate.target := by
    simpa only [C.point_coord] using C.coordinate.map_source C.point_mem
  exact Metric.isOpen_iff.mp C.coordinate.open_target 0 hzero_target

/--
%%handwave
name: A fixed positive radius whose target ball lies in the chosen product chart
statement:
  For each chosen centered boundary product chart, choose
  $r_p>0$ such that the Euclidean ball $B(0,r_p)$ lies in its target.
-/
noncomputable def smoothBoundaryProductChartRadius
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) : ℝ :=
  Classical.choose (smoothBoundaryProductChartAt D p).exists_target_ball

/--
%%handwave
name:
  Positivity of the chosen boundary-chart radius
statement:
  For every \(p\in\partial D\), the chosen radius \(r_p\) of the centered
  target ball is strictly positive.
proof:
  The radius is chosen from a pair consisting of a positive number and the
  proof that its centered ball lies in the chart target.
-/
theorem smoothBoundaryProductChartRadius_pos
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    0 < smoothBoundaryProductChartRadius D p :=
  (Classical.choose_spec
    (smoothBoundaryProductChartAt D p).exists_target_ball).1

/--
%%handwave
name:
  The chosen centered ball lies in the chart target
statement:
  For every \(p\in\partial D\), the chosen radius \(r_p\) satisfies
  \[
    B_{\mathbb R^2}(0,r_p)\subseteq\operatorname{target}(\Phi_p).
  \]
proof:
  This is the containment property of the chosen target-ball radius.
-/
theorem smoothBoundaryProductChart_ball_subset_target
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    Metric.ball (0 : ℝ × ℝ) (smoothBoundaryProductChartRadius D p) ⊆
      (smoothBoundaryProductChartAt D p).coordinate.target :=
  (Classical.choose_spec
    (smoothBoundaryProductChartAt D p).exists_target_ball).2

/--
%%handwave
name: The part of a chosen boundary chart mapping into its centered target ball
statement:
  Define
  $U_p=\operatorname{source}(\Phi_p)\cap\Phi_p^{-1}(B(0,r_p))$, the
  centered product-ball neighborhood of $p$.
-/
def smoothBoundaryProductBallSource
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) : Set X :=
  (smoothBoundaryProductChartAt D p).coordinate.source ∩
    (smoothBoundaryProductChartAt D p).coordinate ⁻¹'
      Metric.ball (0 : ℝ × ℝ) (smoothBoundaryProductChartRadius D p)

/--
%%handwave
name:
  Openness of a boundary product-ball neighborhood
statement:
  For \(p\in\partial D\), the set
  \[
    U_p=\{x\in\operatorname{source}(\Phi_p):
      \Phi_p(x)\in B_{\mathbb R^2}(0,r_p)\}
  \]
  is open in the surface.
proof:
  The chart source and the Euclidean ball are open, and a partial
  homeomorphism pulls back open subsets of its target to open subsets of its
  source.
-/
theorem smoothBoundaryProductBallSource_isOpen
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    IsOpen (smoothBoundaryProductBallSource D p) := by
  exact (smoothBoundaryProductChartAt D p).coordinate.toOpenPartialHomeomorph
    |>.isOpen_inter_preimage Metric.isOpen_ball

/--
%%handwave
name:
  The center belongs to its boundary product-ball neighborhood
statement:
  For every \(p\in\partial D\), one has \(p\in U_p\), where
  \(U_p=\Phi_p^{-1}(B_{\mathbb R^2}(0,r_p))\) inside the chart source.
proof:
  The point \(p\) lies in the chart source and satisfies
  \(\Phi_p(p)=0\); the origin lies in the ball because \(r_p>0\).
-/
theorem smoothBoundaryProductBallSource_point_mem
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    (p : X) ∈ smoothBoundaryProductBallSource D p := by
  refine ⟨smoothBoundaryProductChartAt_point_mem D p, ?_⟩
  change (smoothBoundaryProductChartAt D p).coordinate p ∈
    Metric.ball (0 : ℝ × ℝ) (smoothBoundaryProductChartRadius D p)
  rw [(smoothBoundaryProductChartAt D p).point_coord]
  exact Metric.mem_ball_self (smoothBoundaryProductChartRadius_pos D p)

/--
%%handwave
name: A centered product-ball arc of a smooth frontier is explicitly an open real interval
statement:
  The second product coordinate gives a homeomorphism
  $\partial\Omega\cap U_p\to(-r_p,r_p)$ for every centered boundary
  product-ball neighborhood.
-/
noncomputable def smoothBoundaryProductBall_frontierHomeomorph
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ↑(frontier D.carrier ∩ smoothBoundaryProductBallSource D p) ≃ₜ
      Metric.ball (0 : ℝ) (smoothBoundaryProductChartRadius D p) := by
  let C := smoothBoundaryProductChartAt D p
  let radius := smoothBoundaryProductChartRadius D p
  let S : Set X := frontier D.carrier ∩ smoothBoundaryProductBallSource D p
  let J : Set ℝ := Metric.ball 0 radius
  have hzeroBall : (0 : ℝ) ∈ J := by
    exact Metric.mem_ball_self (smoothBoundaryProductChartRadius_pos D p)
  let toFun : S → J := fun x => ⟨(C.coordinate (x : X)).2, by
    have hxball := x.2.2.2
    rw [← ball_prod_same] at hxball
    exact hxball.2⟩
  let invFun : J → S := fun t => by
    have hqball : (0, (t : ℝ)) ∈ Metric.ball (0 : ℝ × ℝ) radius := by
      rw [← ball_prod_same]
      exact ⟨hzeroBall, t.2⟩
    have hqtarget : (0, (t : ℝ)) ∈ C.coordinate.target :=
      smoothBoundaryProductChart_ball_subset_target D p hqball
    let x : X := C.coordinate.symm (0, (t : ℝ))
    have hxsource : x ∈ C.coordinate.source :=
      C.coordinate.symm.map_source hqtarget
    have hcoordx : C.coordinate x = (0, (t : ℝ)) :=
      C.coordinate.right_inv hqtarget
    have hxfrontier : x ∈ frontier D.carrier :=
      (C.frontier_iff_zero x hxsource).mpr (by simp only [hcoordx])
    have hxballSource : x ∈ smoothBoundaryProductBallSource D p := by
      refine ⟨hxsource, ?_⟩
      change C.coordinate x ∈
        Metric.ball (0 : ℝ × ℝ) (smoothBoundaryProductChartRadius D p)
      simpa only [hcoordx, radius] using hqball
    exact ⟨x, hxfrontier, hxballSource⟩
  refine
    { toEquiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := ?_
          right_inv := ?_ }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    change C.coordinate.symm (0, (C.coordinate (x : X)).2) = (x : X)
    have hfirst : (C.coordinate (x : X)).1 = 0 :=
      (C.frontier_iff_zero (x : X) x.2.2.1).mp x.2.1
    rw [show (0, (C.coordinate (x : X)).2) = C.coordinate (x : X) by
      exact Prod.ext hfirst.symm rfl]
    exact C.coordinate.left_inv x.2.2.1
  · intro t
    apply Subtype.ext
    dsimp only [toFun, invFun]
    have hqball : (0, (t : ℝ)) ∈ Metric.ball (0 : ℝ × ℝ) radius := by
      rw [← ball_prod_same]
      exact ⟨hzeroBall, t.2⟩
    have hqtarget : (0, (t : ℝ)) ∈ C.coordinate.target :=
      smoothBoundaryProductChart_ball_subset_target D p hqball
    exact congrArg Prod.snd (C.coordinate.right_inv hqtarget)
  · apply Continuous.subtype_mk
    have hcoord : Continuous (fun x : S => C.coordinate (x : X)) := by
      exact C.coordinate.toOpenPartialHomeomorph.continuousOn.comp_continuous
        continuous_subtype_val (fun x => x.2.2.1)
    exact continuous_snd.comp hcoord
  · apply Continuous.subtype_mk
    have hsymm : Continuous (fun t : J => C.coordinate.symm (0, (t : ℝ))) := by
      have hinclusion : Continuous (fun t : J => ((0 : ℝ), (t : ℝ))) :=
        (continuous_const : Continuous (fun _ : J => (0 : ℝ))).prodMk
          continuous_subtype_val
      apply C.coordinate.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        hinclusion
      intro t
      apply smoothBoundaryProductChart_ball_subset_target D p
      rw [← ball_prod_same]
      exact ⟨hzeroBall, t.2⟩
    exact hsymm

omit [IsManifold 𝓘(ℝ, ℂ) ∞ X] in
/--
%%handwave
name:
  Compactness of each smooth frontier component
statement:
  Let \(D\) be a relatively compact smoothly bounded domain and
  \(p\in\partial D\).  The connected component
  \(\operatorname{Comp}_{\partial D}(p)\) is compact in the ambient
  surface.
proof:
  The frontier is closed in the compact closure of \(D\), hence compact.
  A connected component is closed in the frontier, so it is compact there;
  the inclusion of the frontier into the surface preserves compactness.
-/
theorem smoothBoundaryDomain_frontier_connectedComponentIn_isCompact
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    IsCompact (connectedComponentIn (frontier D.carrier) (p : X)) := by
  letI : CompactSpace (frontier D.carrier) :=
    isCompact_iff_compactSpace.mp
      (D.compact_closure.of_isClosed_subset
        isClosed_frontier frontier_subset_closure)
  have hcompact : IsCompact (connectedComponent p) :=
    isClosed_connectedComponent.isCompact
  rw [connectedComponentIn_eq_image p.2]
  exact hcompact.image continuous_subtype_val

end

end JJMath.Uniformization
