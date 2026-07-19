import JJMath.Uniformization.AtlasVortexTransport

/-!
# Locally finite subdivision by compact atlas vortices

The geometric input to the vortex telescope is a controlled coordinate
neighborhood: inside a sufficiently small neighborhood of a point, every
ordered pair of distinct points supports an atlas vortex pair, and the
compact core of that pair remains in any prescribed ambient neighborhood.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/--
%%handwave
name:
  A coordinate neighborhood supporting pairwise compact vortices
statement:
  Let \(a\) lie in an open set \(W\) of a complex surface.  There is an open
  neighborhood \(V\) of \(a\), contained in \(W\), such that every ordered
  pair of distinct points \(b,c\in V\) supports an atlas vortex from \(b\) to
  \(c\) whose compact core is contained in \(W\).
proof:
  Choose a surface chart at \(a\) and a coordinate ball whose inverse image
  lies in \(W\).  Take a much smaller concentric ball for \(V\).  Points of
  this smaller ball are close enough for the standard affine planar vortex
  construction, and the quantitative bound on its core keeps that core in
  the original larger coordinate ball and hence in \(W\).
-/
theorem exists_pairwise_atlasVortexNeighborhood
    (W : TopologicalSpace.Opens X) {a : X} (haW : a ∈ W) :
    ∃ V : TopologicalSpace.Opens X, a ∈ V ∧ V ≤ W ∧
      ∀ b ∈ V, ∀ c ∈ V, b ≠ c →
        ∃ D : AtlasVortexPairData X b c, D.ambientCore ⊆ W := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ a
  let S : Set X := (W : Set X) ∩ e.source
  have hSopen : IsOpen S := W.isOpen.inter e.open_source
  have hSsource : S ⊆ e.source := inter_subset_right
  have haS : a ∈ S := ⟨haW, mem_chart_source ℂ a⟩
  have himageOpen : IsOpen (e '' S) :=
    e.isOpen_image_of_subset_source hSopen hSsource
  have heaImage : e a ∈ e '' S := ⟨a, haS, rfl⟩
  rcases Metric.isOpen_iff.mp himageOpen (e a) heaImage with
    ⟨r, hr, hballImage⟩
  have himageTarget : e '' S ⊆ e.target := by
    rintro z ⟨x, hxS, rfl⟩
    exact e.map_source hxS.2
  have hbigTarget : Metric.ball (e a) r ⊆ e.target :=
    hballImage.trans himageTarget
  let B : Set ℂ := Metric.ball (e a) (r / 10)
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBTarget : B ⊆ e.target := by
    intro z hz
    apply hbigTarget
    rw [Metric.mem_ball] at hz ⊢
    linarith
  let Vset : Set X := e.symm '' B
  have hVopen : IsOpen Vset :=
    e.isOpen_image_symm_of_subset_target hBopen hBTarget
  let V : TopologicalSpace.Opens X := ⟨Vset, hVopen⟩
  have haV : a ∈ V := by
    refine ⟨e a, ?_, ?_⟩
    · exact Metric.mem_ball_self (by linarith)
    · exact e.left_inv (mem_chart_source ℂ a)
  have hVW : V ≤ W := by
    intro x hxV
    rcases hxV with ⟨z, hzB, rfl⟩
    have hzbig : z ∈ Metric.ball (e a) r := by
      rw [Metric.mem_ball] at hzB ⊢
      linarith
    rcases hballImage hzbig with ⟨y, hyS, hyz⟩
    have hzTarget : z ∈ e.target := hbigTarget hzbig
    have heq : e.symm z = y := by
      rw [← hyz]
      exact e.left_inv hyS.2
    rw [heq]
    exact hyS.1
  refine ⟨V, haV, hVW, ?_⟩
  intro b hbV c hcV hbc
  rcases hbV with ⟨zb, hzbB, rfl⟩
  rcases hcV with ⟨zc, hzcB, rfl⟩
  have hzbTarget : zb ∈ e.target := hBTarget hzbB
  have hzcTarget : zc ∈ e.target := hBTarget hzcB
  have hbSource : e.symm zb ∈ e.source := e.map_target hzbTarget
  have hcSource : e.symm zc ∈ e.source := e.map_target hzcTarget
  have heb : e (e.symm zb) = zb := e.right_inv hzbTarget
  have hec : e (e.symm zc) = zc := e.right_inv hzcTarget
  have hzbNorm : ‖zb - e a‖ < r / 10 := by
    simpa [B, Metric.mem_ball, dist_eq_norm] using hzbB
  have hzcNorm : ‖zc - e a‖ < r / 10 := by
    simpa [B, Metric.mem_ball, dist_eq_norm] using hzcB
  have hdist : ‖zc - zb‖ < r / 5 := by
    calc
      ‖zc - zb‖ = ‖(zc - e a) + (e a - zb)‖ := by congr 1 <;> ring
      _ ≤ ‖zc - e a‖ + ‖e a - zb‖ := norm_add_le _ _
      _ = ‖zc - e a‖ + ‖zb - e a‖ := by
        rw [show ‖e a - zb‖ = ‖zb - e a‖ by exact norm_sub_rev _ _]
      _ < r / 5 := by linarith
  have hballLeft : Metric.ball (e (e.symm zb)) (4 * r / 5) ⊆
      e.target := by
    rw [heb]
    intro z hz
    apply hbigTarget
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    calc
      ‖z - e a‖ = ‖(z - zb) + (zb - e a)‖ := by congr 1 <;> ring
      _ ≤ ‖z - zb‖ + ‖zb - e a‖ := norm_add_le _ _
      _ < 4 * r / 5 + r / 10 := add_lt_add hz hzbNorm
      _ < r := by linarith
  have hclose : 2 * ‖e (e.symm zc) - e (e.symm zb)‖ < 4 * r / 5 := by
    rw [heb, hec]
    linarith
  let D : AtlasVortexPairData X (e.symm zb) (e.symm zc) :=
    AtlasVortexPairData.ofChartBall e (chart_mem_atlas ℂ a)
      hbSource hcSource hbc hballLeft hclose
  refine ⟨D, ?_⟩
  intro x hxcore
  rcases hxcore with ⟨xU, hxUcore, rfl⟩
  have hcoordCore : e (xU : X) ∈
      planarVortexAffineCore D.chart_values_ne := hxUcore
  have hcoreClose :
      2 * ‖D.chart (e.symm zc) - D.chart (e.symm zb)‖ < 2 * r / 5 := by
    change 2 * ‖e (e.symm zc) - e (e.symm zb)‖ < 2 * r / 5
    rw [heb, hec]
    linarith
  have hcoreBallD :=
    (planarVortexAffineCore_subset_ball_left D.chart_values_ne hcoreClose)
      hcoordCore
  have hcoreBall : e (xU : X) ∈ Metric.ball zb (2 * r / 5) := by
    change e (xU : X) ∈ Metric.ball (D.chart (e.symm zb)) (2 * r / 5) at hcoreBallD
    change e (xU : X) ∈ Metric.ball zb (2 * r / 5)
    simpa [D, AtlasVortexPairData.ofChartBall, heb] using hcoreBallD
  have hcoordBig : e (xU : X) ∈ Metric.ball (e a) r := by
    rw [Metric.mem_ball, dist_eq_norm] at hcoreBall ⊢
    calc
      ‖e (xU : X) - e a‖ =
          ‖(e (xU : X) - zb) + (zb - e a)‖ := by congr 1 <;> ring
      _ ≤ ‖e (xU : X) - zb‖ + ‖zb - e a‖ := norm_add_le _ _
      _ < 2 * r / 5 + r / 10 := add_lt_add hcoreBall hzbNorm
      _ < r := by linarith
  rcases hballImage hcoordBig with ⟨y, hyS, hycoord⟩
  have hyx : y = (xU : X) := by
    apply e.injOn hyS.2 xU.2
    exact hycoord
  change (xU : X) ∈ W
  rw [← hyx]
  exact hyS.1

/-- A controlled vortex edge lies in an ambient open set together with its
compact core. -/
def ControlledAtlasVortexEdge
    (W : TopologicalSpace.Opens X) (a b : X) : Prop :=
  a ∈ W ∧ b ∈ W ∧
    ∃ D : AtlasVortexPairData X a b, D.ambientCore ⊆ W

/-- Two points are joined in an open set by a finite chain of controlled
atlas vortex pairs. -/
def AtlasVortexChainJoinedIn
    (W : TopologicalSpace.Opens X) (a b : X) : Prop :=
  Relation.ReflTransGen (ControlledAtlasVortexEdge W) a b

/--
%%handwave
name:
  Reflexivity of controlled vortex-chain reachability
statement:
  Every point is joined to itself by a finite controlled atlas-vortex chain
  in any open set.
proof:
  Use the chain of length zero.
-/
theorem atlasVortexChainJoinedIn_refl
    (W : TopologicalSpace.Opens X) (a : X) :
    AtlasVortexChainJoinedIn W a a :=
  Relation.ReflTransGen.refl

/--
%%handwave
name:
  Transitivity of controlled vortex-chain reachability
statement:
  A controlled atlas-vortex chain from \(a\) to \(b\), followed by one from
  \(b\) to \(c\), gives a controlled chain from \(a\) to \(c\) in the same
  open set.
proof:
  Concatenate the two finite chains.
-/
theorem atlasVortexChainJoinedIn_trans
    (W : TopologicalSpace.Opens X) {a b c : X}
    (hab : AtlasVortexChainJoinedIn W a b)
    (hbc : AtlasVortexChainJoinedIn W b c) :
    AtlasVortexChainJoinedIn W a c :=
  hab.trans hbc

/--
%%handwave
name:
  Local two-way controlled vortex-chain reachability
statement:
  If \(a\in W\), there is an open neighborhood \(V\subseteq W\) of \(a\)
  such that every \(b\in V\) is joined to \(a\), and \(a\) to \(b\), by
  finite atlas-vortex chains whose cores lie in \(W\).
proof:
  Choose the pairwise vortex neighborhood inside \(W\).  If \(b=a\), use the
  empty chain.  Otherwise construct one vortex for the ordered pair \((a,b)\)
  and another for \((b,a)\); each gives a one-edge controlled chain.
-/
theorem exists_open_atlasVortexChainJoinedIn_both
    (W : TopologicalSpace.Opens X) {a : X} (haW : a ∈ W) :
    ∃ V : TopologicalSpace.Opens X, a ∈ V ∧ V ≤ W ∧
      ∀ b ∈ V,
        AtlasVortexChainJoinedIn W a b ∧
          AtlasVortexChainJoinedIn W b a := by
  rcases exists_pairwise_atlasVortexNeighborhood W haW with
    ⟨V, haV, hVW, hpairs⟩
  refine ⟨V, haV, hVW, ?_⟩
  intro b hbV
  by_cases hab : a = b
  · subst b
    exact ⟨atlasVortexChainJoinedIn_refl W a,
      atlasVortexChainJoinedIn_refl W a⟩
  · have hba : b ≠ a := fun h ↦ hab h.symm
    rcases hpairs a haV b hbV hab with ⟨Dab, hDab⟩
    rcases hpairs b hbV a haV hba with ⟨Dba, hDba⟩
    exact ⟨Relation.ReflTransGen.single
        ⟨haW, hVW hbV, ⟨Dab, hDab⟩⟩,
      Relation.ReflTransGen.single
        ⟨hVW hbV, haW, ⟨Dba, hDba⟩⟩⟩

/--
%%handwave
name:
  Controlled vortex-chain connectivity of a connected open surface
statement:
  Any two points of a connected open subset \(W\) of a complex surface can be
  joined by a finite chain of atlas vortices whose vertices and compact cores
  all remain in \(W\).
proof:
  Fix one endpoint and consider the points reachable from it.  Local two-way
  reachability makes this set open and also makes its complement open.  It is
  nonempty, so connectedness of \(W\) makes every point reachable.
-/
theorem atlasVortexChainJoinedIn_all
    (W : TopologicalSpace.Opens X) [ConnectedSpace W] (a b : W) :
    AtlasVortexChainJoinedIn W (a : X) (b : X) := by
  let S : Set W := {z | AtlasVortexChainJoinedIn W (a : X) (z : X)}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases exists_open_atlasVortexChainJoinedIn_both W z.2 with
      ⟨V, hzV, _hVW, hlocal⟩
    let O : TopologicalSpace.Opens W :=
      ⟨{w | (w : X) ∈ V}, V.isOpen.preimage
        (continuous_subtype_val : Continuous (fun w : W ↦ (w : X)))⟩
    refine Filter.mem_of_superset (O.isOpen.mem_nhds hzV) ?_
    intro w hw
    exact atlasVortexChainJoinedIn_trans W hz (hlocal (w : X) hw).1
  have hScomplOpen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases exists_open_atlasVortexChainJoinedIn_both W z.2 with
      ⟨V, hzV, _hVW, hlocal⟩
    let O : TopologicalSpace.Opens W :=
      ⟨{w | (w : X) ∈ V}, V.isOpen.preimage
        (continuous_subtype_val : Continuous (fun w : W ↦ (w : X)))⟩
    refine Filter.mem_of_superset (O.isOpen.mem_nhds hzV) ?_
    intro w hw hwS
    exact hz (atlasVortexChainJoinedIn_trans W hwS (hlocal (w : X) hw).2)
  have hSclopen : IsClopen S :=
    ⟨isOpen_compl_iff.mp hScomplOpen, hSopen⟩
  have hSnonempty : S.Nonempty :=
    ⟨a, atlasVortexChainJoinedIn_refl W (a : X)⟩
  have hSuniv : S = Set.univ := hSclopen.eq_univ hSnonempty
  change b ∈ S
  rw [hSuniv]
  exact Set.mem_univ b

/-! ## Type-valued controlled paths

The reachability predicate above is convenient for the connectedness
argument, but the countable telescope must retain the actual vortex data in
each finite block.  The following type-valued refinement does exactly that.
-/

/-- A finite path of atlas vortex pairs whose vertices and compact cores all
remain in a prescribed open set. -/
inductive ControlledAtlasVortexPath
    (W : TopologicalSpace.Opens X) : X → X → Type
  | nil (a : X) (ha : a ∈ W) : ControlledAtlasVortexPath W a a
  | tail {a q b : X} (path : ControlledAtlasVortexPath W a q)
      (hb : b ∈ W) (data : AtlasVortexPairData X q b)
      (core_subset : data.ambientCore ⊆ W) :
      ControlledAtlasVortexPath W a b

namespace ControlledAtlasVortexPath

/-- The initial vertex of a controlled path lies in its control set. -/
def start_mem {W : TopologicalSpace.Opens X} {a b : X}
    (path : ControlledAtlasVortexPath W a b) : a ∈ W := by
  induction path with
  | nil ha => exact ha
  | tail path _ _ _ ih => exact ih

/-- The terminal vertex of a controlled path lies in its control set. -/
def end_mem {W : TopologicalSpace.Opens X} {a b : X}
    (path : ControlledAtlasVortexPath W a b) : b ∈ W := by
  cases path with
  | nil ha => exact ha
  | tail _ hb _ _ => exact hb

/--
%%handwave
name:
  An explicit controlled path from finite vortex-chain reachability
statement:
  If \(a\in W\) and a finite controlled atlas-vortex chain joins \(a\) to
  \(b\), then there exists explicit finite path data recording every vertex,
  vortex pair, and core-containment condition along the chain.
proof:
  Induct over the reflexive-transitive chain.  The reflexive case is the
  empty path at \(a\); at each tail step, append the recorded vortex edge to
  the previously constructed path.
-/
theorem nonempty_of_joined {W : TopologicalSpace.Opens X} {a b : X}
    (ha : a ∈ W) (h : AtlasVortexChainJoinedIn W a b) :
    Nonempty (ControlledAtlasVortexPath W a b) := by
  induction h with
  | refl => exact ⟨.nil a ha⟩
  | tail h edge ih =>
      rcases ih with ⟨path⟩
      rcases edge with ⟨_hq, hb, data, hcore⟩
      exact ⟨.tail path hb data hcore⟩

/--
%%handwave
name:
  Appending a controlled vortex path while preserving the exterior phase
statement:
  Let a controlled vortex path inside \(W\) run from \(a\) to \(b\), let
  \(p\notin W\), and let \(T\) be a transport from \(p\) to \(a\).  Then the
  whole path can be appended to obtain a transport from \(p\) to \(b\), and
  outside \(W\) its phase is exactly the phase of \(T\).
proof:
  Induct over the controlled path.  At each edge, append its atlas vortex to
  the current transport.  Outside \(W\), the edge's compact core is absent,
  so its global phase equals one; the append product formula therefore leaves
  the previous phase unchanged.
-/
theorem exists_append_transport {W : TopologicalSpace.Opens X}
    {p a b : X} (path : ControlledAtlasVortexPath W a b)
    (T : AtlasVortexTransportData X p a) (hpW : p ∉ W) :
    ∃ T' : AtlasVortexTransportData X p b,
      ∀ (x : coordinateVortexPairOpen p b) (_hxW : (x : X) ∉ W),
        T'.phase x = T.phase
          ⟨(x : X), ⟨x.2.1,
            fun hxa ↦ _hxW (hxa ▸ path.start_mem)⟩⟩ := by
  induction path generalizing T with
  | nil ha =>
      exact ⟨T, fun _ _ ↦ rfl⟩
  | @tail q b path hb data hcore ih =>
      have hpq : p ≠ q := by
        intro hpq
        exact hpW (hpq ▸ path.end_mem)
      have hpb : p ≠ b := by
        intro hpb
        exact hpW (hpb ▸ hb)
      rcases ih T with ⟨Tq, hTq⟩
      rcases Tq.exists_append data hpb with ⟨Tb, hTb⟩
      refine ⟨Tb, ?_⟩
      intro x hxW
      have hxq : (x : X) ≠ q := by
        intro hxq
        exact hxW (hxq ▸ path.end_mem)
      have hxa : (x : X) ≠ a := by
        intro hxa
        exact hxW (hxa ▸ path.start_mem)
      have hxcore : (x : X) ∉ data.ambientCore := by
        intro hx
        exact hxW (hcore hx)
      rw [hTb x hxq]
      have hphaseOne : data.globalPhase
          (⟨(x : X), ⟨hxq, x.2.2⟩⟩ :
            coordinateVortexPairOpen q b) = 1 :=
        data.globalPhaseFun_eq_one_of_mem_exterior hxcore
      rw [hphaseOne, mul_one]
      exact hTq ⟨(x : X), ⟨x.2.1, hxq⟩⟩ hxW

/--
%%handwave
name:
  A nontrivial controlled vortex path yields a finite transport
statement:
  If a controlled atlas-vortex path runs from \(a\) to \(b\) with \(a\ne b\),
  then there exists a finite atlas-vortex transport from \(a\) to \(b\).
proof:
  Induct over the path.  An empty path contradicts \(a\ne b\).  For a final
  edge, either its initial point is \(a\), in which case that single vortex is
  the transport, or append the edge to the transport supplied by induction.
-/
theorem nonempty_transport {W : TopologicalSpace.Opens X} {a b : X}
    (path : ControlledAtlasVortexPath W a b) (hab : a ≠ b) :
    Nonempty (AtlasVortexTransportData X a b) := by
  induction path with
  | nil _ => exact (hab rfl).elim
  | @tail q b path _hb data _hcore ih =>
      by_cases haq : a = q
      · subst q
        exact ⟨AtlasVortexTransportData.single data⟩
      · rcases ih haq with ⟨Tq⟩
        rcases Tq.exists_append data hab with ⟨Tb, _⟩
        exact ⟨Tb⟩

end ControlledAtlasVortexPath

end

end JJMath.Uniformization
