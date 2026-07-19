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

/-- A fixed choice of product chart at each boundary point. -/
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

/--
%%handwave
name:
  Openness of a chosen boundary coordinate neighborhood
statement:
  For \(p\in\partial D\), the source of the chosen boundary product
  coordinate map \(\Phi_p\) is open in the surface.
proof:
  The source of every partial diffeomorphism is open.
-/
theorem smoothBoundaryProductChartAt_source_isOpen
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    IsOpen (smoothBoundaryProductChartAt D p).coordinate.source :=
  (smoothBoundaryProductChartAt D p).coordinate.open_source

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

/-- A fixed positive radius whose target ball lies in the chosen product
chart. -/
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

/-- The part of a chosen boundary chart mapping into its centered target
ball. -/
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

/-- The upper half of the frontier diameter in a centered product-ball chart. -/
def smoothBoundaryProductBallUpperFrontierArc
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) : Set X :=
  {x | x ∈ frontier D.carrier ∩ smoothBoundaryProductBallSource D p ∧
    0 < ((smoothBoundaryProductChartAt D p).coordinate x).2}

/-- The lower half of the frontier diameter in a centered product-ball chart. -/
def smoothBoundaryProductBallLowerFrontierArc
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) : Set X :=
  {x | x ∈ frontier D.carrier ∩ smoothBoundaryProductBallSource D p ∧
    ((smoothBoundaryProductChartAt D p).coordinate x).2 < 0}

/--
%%handwave
name:
  A smooth domain is a negative half-ball in boundary coordinates
statement:
  Let \(p\in\partial D\), let \(\Phi_p\) be a centered boundary product
  chart, and choose \(r_p>0\) with \(B(0,r_p)\) in its target.  Then
  \[
    \Phi_p\bigl(D\cap\Phi_p^{-1}(B(0,r_p))\bigr)
      =B(0,r_p)\cap\{(s,t):s<0\}.
  \]
proof:
  The boundary-chart sign condition identifies membership in \(D\) with
  negativity of the first coordinate.  The chart and inverse-chart identities
  give the two set inclusions inside the chosen target ball.
-/
theorem smoothBoundaryProductChart_image_domain_inter_ballSource
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    (smoothBoundaryProductChartAt D p).coordinate ''
        (D.carrier ∩ smoothBoundaryProductBallSource D p) =
      Metric.ball (0 : ℝ × ℝ) (smoothBoundaryProductChartRadius D p) ∩
        {q | q.1 < 0} := by
  let C := smoothBoundaryProductChartAt D p
  let radius := smoothBoundaryProductChartRadius D p
  apply Set.Subset.antisymm
  · rintro q ⟨x, ⟨hxD, hxsource, hxball⟩, rfl⟩
    exact ⟨hxball, (C.domain_iff_negative x hxsource).mp hxD⟩
  · rintro q ⟨hqball, hqneg⟩
    have hqtarget : q ∈ C.coordinate.target :=
      smoothBoundaryProductChart_ball_subset_target D p hqball
    let x : X := C.coordinate.symm q
    have hxsource : x ∈ C.coordinate.source :=
      C.coordinate.symm.map_source hqtarget
    have hcoordx : C.coordinate x = q := C.coordinate.right_inv hqtarget
    refine ⟨x, ⟨?_, hxsource, ?_⟩, hcoordx⟩
    · exact (C.domain_iff_negative x hxsource).mpr (hcoordx.symm ▸ hqneg)
    · change C.coordinate x ∈ Metric.ball (0 : ℝ × ℝ) radius
      rw [hcoordx]
      exact hqball

/--
%%handwave
name:
  The frontier is the central diameter in boundary coordinates
statement:
  With the same centered chart and radius,
  \[
    \Phi_p\bigl(\partial D\cap\Phi_p^{-1}(B(0,r_p))\bigr)
      =B(0,r_p)\cap\{(s,t):s=0\}.
  \]
proof:
  The boundary-chart equation identifies frontier points with the zero set of
  the first coordinate.  Applying the chart inverse to every point of the
  central diameter proves the reverse inclusion.
-/
theorem smoothBoundaryProductChart_image_frontier_inter_ballSource
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    (smoothBoundaryProductChartAt D p).coordinate ''
        (frontier D.carrier ∩ smoothBoundaryProductBallSource D p) =
      Metric.ball (0 : ℝ × ℝ) (smoothBoundaryProductChartRadius D p) ∩
        {q | q.1 = 0} := by
  let C := smoothBoundaryProductChartAt D p
  let radius := smoothBoundaryProductChartRadius D p
  apply Set.Subset.antisymm
  · rintro q ⟨x, ⟨hxfrontier, hxsource, hxball⟩, rfl⟩
    exact ⟨hxball, (C.frontier_iff_zero x hxsource).mp hxfrontier⟩
  · rintro q ⟨hqball, hqzero⟩
    have hqtarget : q ∈ C.coordinate.target :=
      smoothBoundaryProductChart_ball_subset_target D p hqball
    let x : X := C.coordinate.symm q
    have hxsource : x ∈ C.coordinate.source :=
      C.coordinate.symm.map_source hqtarget
    have hcoordx : C.coordinate x = q := C.coordinate.right_inv hqtarget
    refine ⟨x, ⟨?_, hxsource, ?_⟩, hcoordx⟩
    · exact (C.frontier_iff_zero x hxsource).mpr (hcoordx.symm ▸ hqzero)
    · change C.coordinate x ∈ Metric.ball (0 : ℝ × ℝ) radius
      rw [hcoordx]
      exact hqball

/-- A centered product-ball arc of a smooth frontier is explicitly an open
real interval. -/
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

/--
%%handwave
name:
  Connectedness of a boundary product-ball arc
statement:
  For every \(p\in\partial D\), the local frontier arc
  \[
    \partial D\cap\Phi_p^{-1}(B(0,r_p))
  \]
  is nonempty and connected.
proof:
  The chart identifies this set with the vertical diameter
  \(\{0\}\times(-r_p,r_p)\), which is the continuous image of a real
  interval and is therefore connected.  It contains the center \(p\).
-/
theorem smoothBoundaryProductBall_frontier_isConnected
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    IsConnected (frontier D.carrier ∩ smoothBoundaryProductBallSource D p) := by
  let C := smoothBoundaryProductChartAt D p
  let radius := smoothBoundaryProductChartRadius D p
  let S : Set X := frontier D.carrier ∩ smoothBoundaryProductBallSource D p
  let T : Set (ℝ × ℝ) :=
    Metric.ball (0 : ℝ × ℝ) radius ∩ {q | q.1 = 0}
  let J : Set ℝ := Metric.ball 0 radius
  have hT_image : (fun t : ℝ => (0, t)) '' J = T := by
    apply Set.Subset.antisymm
    · rintro q ⟨t, ht, rfl⟩
      refine ⟨?_, rfl⟩
      rw [← ball_prod_same]
      exact ⟨Metric.mem_ball_self (smoothBoundaryProductChartRadius_pos D p), ht⟩
    · rintro q ⟨hqball, hqzero⟩
      refine ⟨q.2, ?_, ?_⟩
      · rw [← ball_prod_same] at hqball
        exact hqball.2
      · exact Prod.ext hqzero.symm rfl
  have hTpre : IsPreconnected T := by
    rw [← hT_image]
    exact (convex_ball (0 : ℝ) radius).isPreconnected.image _
      (continuous_const.prodMk continuous_id).continuousOn
  have hsymm_image : C.coordinate.symm '' T = S := by
    apply Set.Subset.antisymm
    · rintro x ⟨q, ⟨hqball, hqzero⟩, rfl⟩
      have hqtarget : q ∈ C.coordinate.target :=
        smoothBoundaryProductChart_ball_subset_target D p hqball
      have hxsource : C.coordinate.symm q ∈ C.coordinate.source :=
        C.coordinate.symm.map_source hqtarget
      have hcoordx : C.coordinate (C.coordinate.symm q) = q :=
        C.coordinate.right_inv hqtarget
      refine ⟨(C.frontier_iff_zero _ hxsource).mpr ?_, hxsource, ?_⟩
      · simpa only [hcoordx] using hqzero
      · change C.coordinate (C.coordinate.symm q) ∈
          Metric.ball (0 : ℝ × ℝ) radius
        rw [hcoordx]
        exact hqball
    · rintro x ⟨hxfrontier, hxsource, hxball⟩
      have hcoord_target : C.coordinate x ∈ C.coordinate.target :=
        C.coordinate.map_source hxsource
      refine ⟨C.coordinate x, ⟨hxball,
        (C.frontier_iff_zero x hxsource).mp hxfrontier⟩, ?_⟩
      exact C.coordinate.left_inv hxsource
  have hTtarget : T ⊆ C.coordinate.target := by
    intro q hq
    exact smoothBoundaryProductChart_ball_subset_target D p hq.1
  have hSpre : IsPreconnected S := by
    rw [← hsymm_image]
    exact hTpre.image C.coordinate.symm
      (C.coordinate.toOpenPartialHomeomorph.continuousOn_symm.mono hTtarget)
  have hpS : (p : X) ∈ S :=
    ⟨p.2, smoothBoundaryProductBallSource_point_mem D p⟩
  exact ⟨⟨p, hpS⟩, hSpre⟩

/--
%%handwave
name:
  Connected vertical intervals pull back to connected frontier arcs
statement:
  Let \(p\in\partial D\), and let \(J\subseteq(-r_p,r_p)\) be nonempty
  and connected.  Then
  \[
    \{x\in\partial D\cap U_p:(\Phi_p(x))_2\in J\}
  \]
  is nonempty and connected.
proof:
  The set is the image of the connected vertical segment
  \(\{0\}\times J\) under the inverse chart.  The ball containment makes
  the inverse chart defined there, and continuity preserves connectedness.
-/
theorem smoothBoundaryProductBall_verticalInterval_isConnected
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    (J : Set ℝ) (hJ : IsConnected J)
    (hJball : J ⊆
      Metric.ball (0 : ℝ) (smoothBoundaryProductChartRadius D p)) :
    IsConnected {x | x ∈
        frontier D.carrier ∩ smoothBoundaryProductBallSource D p ∧
      ((smoothBoundaryProductChartAt D p).coordinate x).2 ∈ J} := by
  let C := smoothBoundaryProductChartAt D p
  let radius := smoothBoundaryProductChartRadius D p
  let A : Set X := {x | x ∈
      frontier D.carrier ∩ smoothBoundaryProductBallSource D p ∧
    (C.coordinate x).2 ∈ J}
  let T : Set (ℝ × ℝ) := (fun t : ℝ => (0, t)) '' J
  have hTconnected : IsConnected T := by
    exact hJ.image _ (continuous_const.prodMk continuous_id).continuousOn
  have hTtarget : T ⊆ C.coordinate.target := by
    rintro q ⟨t, htJ, rfl⟩
    apply smoothBoundaryProductChart_ball_subset_target D p
    rw [← ball_prod_same]
    exact ⟨Metric.mem_ball_self (smoothBoundaryProductChartRadius_pos D p),
      hJball htJ⟩
  have hsymm_image : C.coordinate.symm '' T = A := by
    apply Set.Subset.antisymm
    · rintro x ⟨q, ⟨t, htJ, rfl⟩, rfl⟩
      have hqtarget : (0, t) ∈ C.coordinate.target :=
        hTtarget ⟨t, htJ, rfl⟩
      have hxsource : C.coordinate.symm (0, t) ∈ C.coordinate.source :=
        C.coordinate.symm.map_source hqtarget
      have hcoordx : C.coordinate (C.coordinate.symm (0, t)) = (0, t) :=
        C.coordinate.right_inv hqtarget
      refine ⟨⟨(C.frontier_iff_zero _ hxsource).mpr ?_, hxsource, ?_⟩, ?_⟩
      · simp only [hcoordx]
      · change C.coordinate (C.coordinate.symm (0, t)) ∈
          Metric.ball (0 : ℝ × ℝ) radius
        rw [hcoordx, ← ball_prod_same]
        exact ⟨Metric.mem_ball_self
          (smoothBoundaryProductChartRadius_pos D p), hJball htJ⟩
      · simpa only [hcoordx] using htJ
    · rintro x ⟨⟨hxfrontier, hxsource, hxball⟩, hxJ⟩
      have hcoord_zero : (C.coordinate x).1 = 0 :=
        (C.frontier_iff_zero x hxsource).mp hxfrontier
      refine ⟨C.coordinate x, ⟨(C.coordinate x).2, hxJ, ?_⟩, ?_⟩
      · exact Prod.ext hcoord_zero.symm rfl
      · exact C.coordinate.left_inv hxsource
  change IsConnected A
  rw [← hsymm_image]
  exact hTconnected.image C.coordinate.symm
    (C.coordinate.toOpenPartialHomeomorph.continuousOn_symm.mono hTtarget)

/--
%%handwave
name:
  Connectedness of the upper half of a boundary arc
statement:
  For \(p\in\partial D\), the set
  \[
    \{x\in\partial D\cap U_p:0<(\Phi_p(x))_2\}
  \]
  is nonempty and connected.
proof:
  This is the inverse-chart image of the nonempty connected interval
  \((0,r_p)\) on the vertical coordinate axis.
-/
theorem smoothBoundaryProductBall_upperFrontierArc_isConnected
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    IsConnected (smoothBoundaryProductBallUpperFrontierArc D p) := by
  let radius := smoothBoundaryProductChartRadius D p
  have hinterval : IsConnected (Set.Ioo (0 : ℝ) radius) :=
    isConnected_Ioo (smoothBoundaryProductChartRadius_pos D p)
  have hinterval_ball : Set.Ioo (0 : ℝ) radius ⊆
      Metric.ball (0 : ℝ) (smoothBoundaryProductChartRadius D p) := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2
  have hset : smoothBoundaryProductBallUpperFrontierArc D p =
      {x | x ∈ frontier D.carrier ∩ smoothBoundaryProductBallSource D p ∧
        ((smoothBoundaryProductChartAt D p).coordinate x).2 ∈
          Set.Ioo (0 : ℝ) radius} := by
    ext x
    constructor
    · rintro ⟨hx, hpos⟩
      have hxball := hx.2.2
      rw [← ball_prod_same] at hxball
      have habs :
          |((smoothBoundaryProductChartAt D p).coordinate x).2| < radius := by
        simpa [Metric.mem_ball, Real.dist_eq] using hxball.2
      exact ⟨hx, hpos, (abs_lt.mp habs).2⟩
    · rintro ⟨hx, hpos, _hlt⟩
      exact ⟨hx, hpos⟩
  rw [hset]
  exact smoothBoundaryProductBall_verticalInterval_isConnected
    D p (Set.Ioo (0 : ℝ) radius) hinterval hinterval_ball

/--
%%handwave
name:
  Connectedness of the lower half of a boundary arc
statement:
  For \(p\in\partial D\), the set
  \[
    \{x\in\partial D\cap U_p:(\Phi_p(x))_2<0\}
  \]
  is nonempty and connected.
proof:
  This is the inverse-chart image of the nonempty connected interval
  \((-r_p,0)\) on the vertical coordinate axis.
-/
theorem smoothBoundaryProductBall_lowerFrontierArc_isConnected
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    IsConnected (smoothBoundaryProductBallLowerFrontierArc D p) := by
  let radius := smoothBoundaryProductChartRadius D p
  have hneg : -radius < (0 : ℝ) := neg_lt_zero.mpr
    (smoothBoundaryProductChartRadius_pos D p)
  have hinterval : IsConnected (Set.Ioo (-radius) (0 : ℝ)) :=
    isConnected_Ioo hneg
  have hinterval_ball : Set.Ioo (-radius) (0 : ℝ) ⊆
      Metric.ball (0 : ℝ) (smoothBoundaryProductChartRadius D p) := by
    intro t ht
    dsimp [radius] at ht
    have htleft := ht.1
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonpos ht.2.le]
    linarith only [htleft]
  have hset : smoothBoundaryProductBallLowerFrontierArc D p =
      {x | x ∈ frontier D.carrier ∩ smoothBoundaryProductBallSource D p ∧
        ((smoothBoundaryProductChartAt D p).coordinate x).2 ∈
          Set.Ioo (-radius) (0 : ℝ)} := by
    ext x
    constructor
    · rintro ⟨hx, hnegx⟩
      have hxball := hx.2.2
      rw [← ball_prod_same] at hxball
      have habs :
          |((smoothBoundaryProductChartAt D p).coordinate x).2| < radius := by
        simpa [Metric.mem_ball, Real.dist_eq] using hxball.2
      exact ⟨hx, (abs_lt.mp habs).1, hnegx⟩
    · rintro ⟨hx, _hlt, hnegx⟩
      exact ⟨hx, hnegx⟩
  rw [hset]
  exact smoothBoundaryProductBall_verticalInterval_isConnected
    D p (Set.Ioo (-radius) (0 : ℝ)) hinterval hinterval_ball

/--
%%handwave
name:
  A punctured boundary arc has two coordinate halves
statement:
  If \(A_p=\partial D\cap\Phi_p^{-1}(B(0,r_p))\), then
  \[
    A_p\setminus\{p\}
      =\{x\in A_p:(\Phi_p x)_2>0\}
       \cup\{x\in A_p:(\Phi_p x)_2<0\}.
  \]
proof:
  Every point of \(A_p\) has first coordinate zero, and the center has both
  coordinates zero.  Injectivity of the chart shows that a noncentral point
  has nonzero second coordinate, which is either positive or negative.
-/
theorem smoothBoundaryProductBall_frontier_diff_center
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    (frontier D.carrier ∩ smoothBoundaryProductBallSource D p) \ {(p : X)} =
      smoothBoundaryProductBallUpperFrontierArc D p ∪
        smoothBoundaryProductBallLowerFrontierArc D p := by
  let C := smoothBoundaryProductChartAt D p
  ext x
  constructor
  · rintro ⟨hx, hxp⟩
    have hxsource : x ∈ C.coordinate.source := hx.2.1
    have hfirst : (C.coordinate x).1 = 0 :=
      (C.frontier_iff_zero x hxsource).mp hx.1
    have hsecond : (C.coordinate x).2 ≠ 0 := by
      intro hzero
      have hcoord : C.coordinate x = C.coordinate p := by
        rw [C.point_coord]
        exact Prod.ext hfirst hzero
      have hxeq : x = (p : X) := by
        calc
          x = C.coordinate.symm (C.coordinate x) :=
            (C.coordinate.left_inv hxsource).symm
          _ = C.coordinate.symm (C.coordinate p) := congrArg _ hcoord
          _ = (p : X) := C.coordinate.left_inv C.point_mem
      apply hxp
      rw [hxeq]
      simp
    rcases lt_or_gt_of_ne hsecond with hnegative | hpositive
    · exact Or.inr ⟨hx, hnegative⟩
    · exact Or.inl ⟨hx, hpositive⟩
  · intro hx
    rcases hx with hupper | hlower
    · refine ⟨hupper.1, ?_⟩
      intro hxp
      have hxeq : x = (p : X) := by simpa using hxp
      subst x
      have hpositive := hupper.2
      rw [(smoothBoundaryProductChartAt D p).point_coord] at hpositive
      exact (lt_irrefl 0) hpositive
    · refine ⟨hlower.1, ?_⟩
      intro hxp
      have hxeq : x = (p : X) := by simpa using hxp
      subst x
      have hnegative := hlower.2
      rw [(smoothBoundaryProductChartAt D p).point_coord] at hnegative
      exact (lt_irrefl 0) hnegative

/--
%%handwave
name:
  Disjointness of the two halves of a punctured boundary arc
statement:
  The subsets of a boundary product-ball arc on which the second coordinate
  is respectively positive and negative are disjoint.
proof:
  No real number can be both strictly positive and strictly negative.
-/
theorem smoothBoundaryProductBall_frontier_halves_disjoint
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    Disjoint (smoothBoundaryProductBallUpperFrontierArc D p)
      (smoothBoundaryProductBallLowerFrontierArc D p) := by
  rw [Set.disjoint_left]
  intro x hupper hlower
  exact (not_lt_of_ge hupper.2.le) hlower.2

/--
%%handwave
name:
  A boundary product-ball arc lies in one frontier component
statement:
  If \(p\in\partial D\), then
  \[
    \partial D\cap U_p
      \subseteq \operatorname{Comp}_{\partial D}(p),
  \]
  where the right-hand side is the connected component of \(p\) in
  \(\partial D\).
proof:
  The local frontier arc is connected, contains \(p\), and is contained in
  \(\partial D\).  Hence it lies in the maximal connected subset of
  \(\partial D\) containing \(p\).
-/
theorem smoothBoundaryProductBall_frontier_subset_connectedComponentIn
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    frontier D.carrier ∩ smoothBoundaryProductBallSource D p ⊆
      connectedComponentIn (frontier D.carrier) (p : X) := by
  exact
    (smoothBoundaryProductBall_frontier_isConnected D p).isPreconnected
      |>.subset_connectedComponentIn
        ⟨p.2, smoothBoundaryProductBallSource_point_mem D p⟩
        inter_subset_left

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

/--
%%handwave
name:
  Finite product-ball cover of one frontier component
statement:
  Every connected component \(C\) of the frontier of a smooth relatively
  compact domain admits points \(p_1,\ldots,p_N\in C\) such that
  \[
    C\subseteq\bigcup_{j=1}^N\Phi_{p_j}^{-1}(B(0,r_{p_j})).
  \]
proof:
  The frontier component is compact, and the product-ball sources centered at
  its points form an open cover.  Extract a finite subcover.
-/
theorem exists_finite_smoothBoundaryProductBall_cover_frontierComponent
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ centers : Finset
        {x // x ∈ connectedComponentIn (frontier D.carrier) (p : X)},
      connectedComponentIn (frontier D.carrier) (p : X) ⊆
        ⋃ q ∈ centers,
          smoothBoundaryProductBallSource D
            ⟨(q : X), connectedComponentIn_subset
              (frontier D.carrier) (p : X) q.2⟩ := by
  classical
  let C : Set X := connectedComponentIn (frontier D.carrier) (p : X)
  let pointOf (q : C) : frontier D.carrier :=
    ⟨(q : X), connectedComponentIn_subset
      (frontier D.carrier) (p : X) q.2⟩
  let U : C → Set X := fun q =>
    smoothBoundaryProductBallSource D (pointOf q)
  have hCcompact : IsCompact C :=
    smoothBoundaryDomain_frontier_connectedComponentIn_isCompact D p
  have hUopen : ∀ q, IsOpen (U q) := fun q =>
    smoothBoundaryProductBallSource_isOpen D (pointOf q)
  have hcover : C ⊆ ⋃ q, U q := by
    intro x hx
    let q : C := ⟨x, hx⟩
    exact mem_iUnion.mpr
      ⟨q, smoothBoundaryProductBallSource_point_mem D (pointOf q)⟩
  rcases hCcompact.elim_finite_subcover U hUopen hcover with
    ⟨centers, hcenters⟩
  exact ⟨centers, by simpa [C, U, pointOf] using hcenters⟩

/--
%%handwave
name:
  Finite boundary product-chart cover of the frontier
statement:
  If \(D\) is a relatively compact smoothly bounded domain, there are
  finitely many points \(p_1,\ldots,p_N\in\partial D\) such that
  \[
    \partial D\subseteq
      \bigcup_{j=1}^{N}\operatorname{source}(\Phi_{p_j}).
  \]
proof:
  The frontier is compact, and the open sources of the product charts
  centered at its points cover it.  Compactness supplies a finite subcover.
-/
theorem exists_finite_smoothBoundaryProductChart_cover_frontier
    (D : SmoothBoundaryDomain X) :
    ∃ centers : Finset (frontier D.carrier),
      frontier D.carrier ⊆
        ⋃ p ∈ centers, (smoothBoundaryProductChartAt D p).coordinate.source := by
  classical
  let U : frontier D.carrier → Set X := fun p =>
    (smoothBoundaryProductChartAt D p).coordinate.source
  have hfrontier_compact : IsCompact (frontier D.carrier) :=
    D.compact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hUopen : ∀ p, IsOpen (U p) := fun p =>
    smoothBoundaryProductChartAt_source_isOpen D p
  have hcover : frontier D.carrier ⊆ ⋃ p, U p := by
    intro x hx
    let p : frontier D.carrier := ⟨x, hx⟩
    exact mem_iUnion.mpr
      ⟨p, smoothBoundaryProductChartAt_point_mem D p⟩
  rcases hfrontier_compact.elim_finite_subcover U hUopen hcover with
    ⟨centers, hcenters⟩
  exact ⟨centers, by simpa [U] using hcenters⟩

/--
%%handwave
name:
  Finite product-ball cover of the frontier
statement:
  For a smooth relatively compact domain \(D\), there are finitely many
  \(p_1,\ldots,p_N\in\partial D\) such that
  \[
    \partial D\subseteq\bigcup_{j=1}^N
      \Phi_{p_j}^{-1}(B(0,r_{p_j})).
  \]
proof:
  The frontier is a closed subset of the compact closure of \(D\), hence is
  compact.  The centered product-ball sources form an open cover, so a finite
  subcover exists.
-/
theorem exists_finite_smoothBoundaryProductBall_cover_frontier
    (D : SmoothBoundaryDomain X) :
    ∃ centers : Finset (frontier D.carrier),
      frontier D.carrier ⊆
        ⋃ p ∈ centers, smoothBoundaryProductBallSource D p := by
  classical
  let U : frontier D.carrier → Set X := fun p =>
    smoothBoundaryProductBallSource D p
  have hfrontier_compact : IsCompact (frontier D.carrier) :=
    D.compact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hUopen : ∀ p, IsOpen (U p) := fun p =>
    smoothBoundaryProductBallSource_isOpen D p
  have hcover : frontier D.carrier ⊆ ⋃ p, U p := by
    intro x hx
    let p : frontier D.carrier := ⟨x, hx⟩
    exact mem_iUnion.mpr
      ⟨p, smoothBoundaryProductBallSource_point_mem D p⟩
  rcases hfrontier_compact.elim_finite_subcover U hUopen hcover with
    ⟨centers, hcenters⟩
  exact ⟨centers, by simpa [U] using hcenters⟩

/--
%%handwave
name:
  Finite cover of the frontier by connected open arcs
statement:
  The frontier of a smooth relatively compact domain has a finite cover by
  product-ball sources \(U_{p_j}\) such that every
  \(\partial D\cap U_{p_j}\) is connected and relatively open in
  \(\partial D\).
proof:
  Take a finite product-ball cover.  Each intersection with the frontier is a
  connected central-diameter arc, and relative openness follows because each
  product-ball source is open in the ambient surface.
-/
theorem exists_finite_connected_smoothBoundaryProductBall_cover_frontier
    (D : SmoothBoundaryDomain X) :
    ∃ centers : Finset (frontier D.carrier),
      frontier D.carrier ⊆
          ⋃ p ∈ centers, smoothBoundaryProductBallSource D p ∧
        ∀ p ∈ centers,
          IsConnected
              (frontier D.carrier ∩ smoothBoundaryProductBallSource D p) ∧
            IsOpen ((fun x : frontier D.carrier => (x : X)) ⁻¹'
              smoothBoundaryProductBallSource D p) := by
  rcases exists_finite_smoothBoundaryProductBall_cover_frontier D with
    ⟨centers, hcover⟩
  refine ⟨centers, hcover, ?_⟩
  intro p _hp
  exact ⟨smoothBoundaryProductBall_frontier_isConnected D p,
    (smoothBoundaryProductBallSource_isOpen D p).preimage
      continuous_subtype_val⟩

end

end JJMath.Uniformization
