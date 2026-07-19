import JJMath.Uniformization.LiouvilleExistence
import JJMath.Uniformization.RadoSecondCountable
import JJMath.Uniformization.SimplyConnectedOneForm
import JJMath.Uniformization.SurfaceDiskSurgery
import JJMath.RiemannianGeometry.SurfaceAnalysis
import JJMath.Manifold.DeRhamTheorem
import JJMath.Uniformization.AnnularPeriodObstruction
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Defs.Filter

/-!
# Simply connected smooth exhaustions

This file isolates the surface-topological input behind the hole-filling
construction for noncompact simply connected Riemann surfaces.  The intended
application is to replace an arbitrary smooth relatively compact exhaustion by
one whose members are obtained from the base-point component by filling all
bounded complementary components.
-/

namespace JJMath

open Set
open scoped _root_.Manifold _root_.Topology ContDiff

namespace Uniformization

/--
%%handwave
name:
  Locally path connected spaces are locally connected
statement:
  A locally path connected space is locally connected.
proof:
  Path-connected neighborhoods form a connected neighborhood basis.
-/
theorem locPathConnectedSpace_locallyConnectedSpace
    {X : Type} [TopologicalSpace X] [LocPathConnectedSpace X] :
    LocallyConnectedSpace X :=
  locallyConnectedSpace_of_connected_bases
    (fun (_ : X) (U : Set X) => U)
    (fun (x : X) (U : Set X) => U ∈ 𝓝 x ∧ IsPathConnected U)
    (fun x => path_connected_basis x)
    (fun _ _ hU => hU.2.isConnected.isPreconnected)

/--
%%handwave
name:
  Locally path connectedness from local open pieces
statement:
  If every point of a topological space has an open neighborhood which is
  locally path connected in the subspace topology, then the whole space is
  locally path connected.
proof:
  Given an open neighborhood \(U\) of a point \(x\), choose a locally path
  connected open patch \(S\) around \(x\).  In \(S\), the path component of
  \(x\) inside \(U\cap S\) is a neighborhood of \(x\).  Its image in the
  ambient space is still a neighborhood of \(x\) and lies in the path
  component of \(x\) inside \(U\).
-/
theorem locPathConnectedSpace_of_openCover
    {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ s : Set X, IsOpen s ∧ x ∈ s ∧ LocPathConnectedSpace s) :
    LocPathConnectedSpace X := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  rcases h x with ⟨s, hs_open, hxs, hs_lpc⟩
  let xs : s := ⟨x, hxs⟩
  let us : Set s := {y : s | (y : X) ∈ u}
  haveI : LocPathConnectedSpace s := hs_lpc
  have hus_open : IsOpen us := by
    exact hu.preimage continuous_subtype_val
  have hxs_us : xs ∈ us := hxu
  have hpc_nhds_s : pathComponentIn us xs ∈ 𝓝 xs :=
    pathComponentIn_mem_nhds (hus_open.mem_nhds hxs_us)
  have hmap : Filter.map ((↑) : s → X) (𝓝 xs) = 𝓝 x := by
    exact map_nhds_subtype_coe_eq_nhds hxs (hs_open.mem_nhds hxs)
  have himage_nhds : ((↑) : s → X) '' pathComponentIn us xs ∈ 𝓝 x := by
    rw [← hmap]
    exact Filter.image_mem_map hpc_nhds_s
  refine Filter.mem_of_superset himage_nhds ?_
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  exact
    ((isPathConnected_pathComponentIn hxs_us).image
        continuous_subtype_val).subset_pathComponentIn
      ⟨xs, mem_pathComponentIn_self hxs_us, rfl⟩
      (by
        intro w hw
        rcases hw with ⟨q, hq, rfl⟩
        exact (pathComponentIn_subset (F := us) (x := xs) hq))
      ⟨z, hz, rfl⟩

/--
%%handwave
name:
  Nested subspace cut by an ambient set
statement:
  If \(A\) and \(B\) are subsets of a topological space, then the subspace of
  \(A\) cut out by \(B\) is homeomorphic to the subspace \(A\cap B\) of the
  ambient space.
proof:
  Both spaces have the same points; the homeomorphism only reassociates the
  two membership conditions.
-/
noncomputable def subtypePreimageHomeomorph
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    {x : A | (x : X) ∈ B} ≃ₜ (B ∩ A : Set X) where
  toFun x := ⟨x.1, ⟨x.2, x.1.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun x => ⟨x.2, x.1.2⟩)
  continuous_invFun := by
    exact (Continuous.subtype_mk continuous_subtype_val (fun x => x.2.2)).subtype_mk
      (fun x => x.2.1)

/--
%%handwave
name:
  Component of a set
statement:
  A subset \(U\) is a component of a set \(S\) when it is a nonempty
  preconnected subset of \(S\), maximal among preconnected subsets of \(S\)
  that meet it.
-/
def IsComponentOf {X : Type} [TopologicalSpace X] (U S : Set X) : Prop :=
  U ⊆ S ∧ U.Nonempty ∧ IsPreconnected U ∧
    ∀ V : Set X, V ⊆ S → IsPreconnected V → (U ∩ V).Nonempty → V ⊆ U

/--
%%handwave
name:
  Components lie in the ambient set
statement:
  A component of \(S\) is contained in \(S\).
proof:
  This containment is the first condition in the definition of a component.
-/
theorem IsComponentOf.subset
    {X : Type} [TopologicalSpace X] {U S : Set X}
    (hU : IsComponentOf U S) :
    U ⊆ S :=
  hU.1

/--
%%handwave
name:
  Components are nonempty
statement:
  A component is nonempty.
proof:
  Nonemptiness is one of the defining conditions for a component.
-/
theorem IsComponentOf.nonempty
    {X : Type} [TopologicalSpace X] {U S : Set X}
    (hU : IsComponentOf U S) :
    U.Nonempty :=
  hU.2.1

/--
%%handwave
name:
  Components are preconnected
statement:
  A component is preconnected.
proof:
  Preconnectedness is one of the defining conditions for a component.
-/
theorem IsComponentOf.isPreconnected
    {X : Type} [TopologicalSpace X] {U S : Set X}
    (hU : IsComponentOf U S) :
    IsPreconnected U :=
  hU.2.2.1

/--
%%handwave
name:
  Connected components are components
statement:
  If \(x\in S\), then the connected component of \(x\) inside \(S\) is a
  component of \(S\).
proof:
  The connected component is contained in \(S\), is nonempty, and is
  preconnected.  Any preconnected subset of \(S\) that meets it lies in the
  same connected component.
-/
theorem isComponentOf_connectedComponentIn
    {X : Type} [TopologicalSpace X] {S : Set X} {x : X} (hx : x ∈ S) :
    IsComponentOf (connectedComponentIn S x) S := by
  refine ⟨connectedComponentIn_subset S x, ⟨x, mem_connectedComponentIn hx⟩,
    isPreconnected_connectedComponentIn, ?_⟩
  intro V hVS hVpre hmeet
  rcases hmeet with ⟨y, hyC, hyV⟩
  have hVy : V ⊆ connectedComponentIn S y :=
    hVpre.subset_connectedComponentIn hyV hVS
  have hCy : connectedComponentIn S x = connectedComponentIn S y :=
    connectedComponentIn_eq hyC
  simpa [hCy] using hVy

/--
%%handwave
name:
  Components are connected components
statement:
  A component of \(S\) that contains \(x\) is exactly the connected component
  of \(x\) inside \(S\).
proof:
  Maximality gives one inclusion, while preconnectedness of the component
  gives the other.
-/
theorem IsComponentOf.eq_connectedComponentIn_of_mem
    {X : Type} [TopologicalSpace X] {U S : Set X}
    (hU : IsComponentOf U S) {x : X} (hxU : x ∈ U) :
    U = connectedComponentIn S x := by
  apply Subset.antisymm
  · exact hU.2.2.1.subset_connectedComponentIn hxU hU.1
  · exact hU.2.2.2 (connectedComponentIn S x) (connectedComponentIn_subset S x)
      isPreconnected_connectedComponentIn
      ⟨x, hxU, mem_connectedComponentIn (hU.1 hxU)⟩

/--
%%handwave
name:
  Components are unique when they meet
statement:
  Two components of the same set that intersect are equal.
proof:
  Each component is maximal among preconnected subsets meeting it, so each
  contains the other.
-/
theorem IsComponentOf.eq_of_inter_nonempty
    {X : Type} [TopologicalSpace X] {U V S : Set X}
    (hU : IsComponentOf U S) (hV : IsComponentOf V S)
    (hUV : (U ∩ V).Nonempty) :
    U = V := by
  rcases hUV with ⟨x, hxU, hxV⟩
  apply Subset.antisymm
  · exact hV.2.2.2 U hU.1 hU.2.2.1 ⟨x, hxV, hxU⟩
  · exact hU.2.2.2 V hV.1 hV.2.2.1 ⟨x, hxU, hxV⟩

/--
%%handwave
name:
  Distinct components are disjoint
statement:
  Two distinct components of the same set have empty intersection.
proof:
  If they met, component uniqueness would make them equal.
-/
theorem IsComponentOf.inter_eq_empty_of_ne
    {X : Type} [TopologicalSpace X] {U V S : Set X}
    (hU : IsComponentOf U S) (hV : IsComponentOf V S)
    (hUV : U ≠ V) :
    U ∩ V = ∅ := by
  by_contra hne
  have hnonempty : (U ∩ V).Nonempty :=
    nonempty_iff_ne_empty.mpr hne
  exact hUV (hU.eq_of_inter_nonempty hV hnonempty)

/--
%%handwave
name:
  Component characterization
statement:
  The components of \(S\) are exactly the connected components of its points.
proof:
  One direction uses a point of the nonempty component; the converse is the
  connected-component construction.
-/
theorem isComponentOf_iff_exists_connectedComponentIn
    {X : Type} [TopologicalSpace X] {U S : Set X} :
    IsComponentOf U S ↔ ∃ x ∈ S, U = connectedComponentIn S x := by
  constructor
  · intro hU
    rcases hU.2.1 with ⟨x, hxU⟩
    exact ⟨x, hU.1 hxU, hU.eq_connectedComponentIn_of_mem hxU⟩
  · rintro ⟨x, hxS, rfl⟩
    exact isComponentOf_connectedComponentIn hxS

/--
%%handwave
name:
  Connected components are closed inside a set
statement:
  If a point of \(S\) lies in the closure of the component of \(x\) inside
  \(S\), then it lies in that component.
proof:
  In the subtype topology on \(S\), connected components are closed.  Pull the
  ambient closure statement back through the subtype embedding.
-/
theorem connectedComponentIn_mem_of_mem_closure_of_mem
    {X : Type} [TopologicalSpace X] {S : Set X} {x y : X}
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hy_closure : y ∈ closure (connectedComponentIn S x)) :
    y ∈ connectedComponentIn S x := by
  let xS : S := ⟨x, hxS⟩
  let yS : S := ⟨y, hyS⟩
  have hcomponent_eq :
      connectedComponentIn S x =
        ((↑) : S → X) '' connectedComponent xS :=
    connectedComponentIn_eq_image hxS
  have hy_sub_closure : yS ∈ closure (connectedComponent xS) := by
    have hy_preimage :
        yS ∈ ((↑) : S → X) ⁻¹'
          closure (((↑) : S → X) '' connectedComponent xS) := by
      simpa [yS, hcomponent_eq] using hy_closure
    simpa [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      using hy_preimage
  have hy_sub_component : yS ∈ connectedComponent xS := by
    have hclosed : IsClosed (connectedComponent xS) := isClosed_connectedComponent
    rwa [hclosed.closure_eq] at hy_sub_closure
  rw [hcomponent_eq]
  exact ⟨yS, hy_sub_component, rfl⟩

/--
%%handwave
name:
  Component frontiers lie in the ambient frontier
statement:
  In a locally connected space, the frontier of a component of an open set lies
  in the frontier of that open set.
proof:
  Components of open sets are open in locally connected spaces.  A frontier
  point of the component cannot lie in the open set without lying back in the
  component, because components are closed inside the open set.
-/
theorem frontier_connectedComponentIn_subset_frontier_of_isOpen
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {S : Set X} {x : X} (hS_open : IsOpen S) (hxS : x ∈ S) :
    frontier (connectedComponentIn S x) ⊆ frontier S := by
  let C : Set X := connectedComponentIn S x
  have hC_subsetS : C ⊆ S := by
    dsimp [C]
    exact connectedComponentIn_subset S x
  have hC_open : IsOpen C := by
    dsimp [C]
    exact hS_open.connectedComponentIn
  intro y hy
  have hy_closureS : y ∈ closure S :=
    closure_mono hC_subsetS (frontier_subset_closure hy)
  have hy_notS : y ∉ S := by
    intro hyS
    have hyC : y ∈ C := by
      dsimp [C]
      exact connectedComponentIn_mem_of_mem_closure_of_mem hxS hyS
        (frontier_subset_closure hy)
    have hy_inter : y ∈ C ∩ frontier C := ⟨hyC, hy⟩
    rw [hC_open.inter_frontier_eq] at hy_inter
    exact hy_inter
  rw [frontier, hS_open.interior_eq]
  exact ⟨hy_closureS, hy_notS⟩

/--
%%handwave
name:
  Components of open sets are open
statement:
  In a locally connected space, every component of an open set is open.
proof:
  A component containing \(x\) is the connected component of \(x\) inside the
  open set, and such connected components are open in locally connected
  spaces.
-/
theorem IsComponentOf.isOpen_of_isOpen
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {U S : Set X} (hU : IsComponentOf U S) (hS_open : IsOpen S) :
    IsOpen U := by
  rcases hU.nonempty with ⟨x, hxU⟩
  rw [hU.eq_connectedComponentIn_of_mem hxU]
  exact hS_open.connectedComponentIn

/--
%%handwave
name:
  Components are connected sets
statement:
  Every component of a set is connected.
proof:
  By definition, a component is nonempty and preconnected.
-/
theorem IsComponentOf.isConnected
    {X : Type} [TopologicalSpace X]
    {U S : Set X} (hU : IsComponentOf U S) :
    IsConnected U :=
  ⟨hU.nonempty, hU.isPreconnected⟩

/--
%%handwave
name:
  Component closures are connected
statement:
  The closure of a component is connected.
proof:
  The closure of a preconnected set is preconnected, and the component is
  nonempty.
-/
theorem IsComponentOf.closure_isConnected
    {X : Type} [TopologicalSpace X]
    {U S : Set X} (hU : IsComponentOf U S) :
    IsConnected (closure U) :=
  ⟨hU.nonempty.mono subset_closure, hU.isPreconnected.closure⟩

/--
%%handwave
name:
  Open components are path connected
statement:
  In a locally path-connected space, every component of an open set is path
  connected.
proof:
  Components of open sets are open.  In a locally path-connected space, an
  open connected set is path connected.
-/
theorem IsComponentOf.isPathConnected_of_isOpen
    {X : Type} [TopologicalSpace X] [LocPathConnectedSpace X]
    {U S : Set X} (hU : IsComponentOf U S) (hS_open : IsOpen S) :
    IsPathConnected U := by
  exact ((hU.isOpen_of_isOpen hS_open).isConnected_iff_isPathConnected).mp
    hU.isConnected

/--
%%handwave
name:
  Complementary components of closed sets are path connected
statement:
  In a locally path-connected space, every complementary component of a closed
  set is path connected.
proof:
  The complement of a closed set is open, so the open-component
  path-connectedness theorem applies.
-/
theorem IsComponentOf.isPathConnected_of_compl_isClosed
    {X : Type} [TopologicalSpace X] [LocPathConnectedSpace X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ) (hK_closed : IsClosed K) :
    IsPathConnected U :=
  hU.isPathConnected_of_isOpen hK_closed.isOpen_compl

/--
%%handwave
name:
  Joining every point to one base point gives connectedness
statement:
  If every point of a set can be joined inside the set to one fixed base
  point, then the set is connected.
proof:
  Join any two points by concatenating the reverse of the first path to the
  base point with the second path from the base point.
-/
theorem isPreconnected_of_forall_joinedIn_base
    {X : Type} [TopologicalSpace X] {s : Set X} {p : X}
    (hjoin : ∀ x ∈ s, JoinedIn s p x) :
    IsPreconnected s := by
  refine isPreconnected_of_forall_joinedIn ?_
  intro x hx y hy
  exact (hjoin x hx).symm.trans (hjoin y hy)

/--
%%handwave
name:
  Joining every point to one base point gives path connectedness
statement:
  If one point of a set can be joined inside the set to every other point,
  then the set is path connected.
proof:
  This is exactly the definition of path connectedness for a set.
-/
theorem isPathConnected_of_forall_joinedIn_base
    {X : Type} [TopologicalSpace X] {s : Set X} {p : X}
    (hp : p ∈ s) (hjoin : ∀ x ∈ s, JoinedIn s p x) :
    IsPathConnected s :=
  ⟨p, hp, fun {_x} hx => hjoin _ hx⟩

/--
%%handwave
name:
  Component frontiers lie in the ambient frontier
statement:
  In a locally connected space, the frontier of a component of an open set
  lies in the frontier of the open set.
proof:
  Identify the component with the connected component of any one of its
  points, then apply the connected-component frontier lemma.
-/
theorem IsComponentOf.frontier_subset_frontier_of_isOpen
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {U S : Set X} (hU : IsComponentOf U S) (hS_open : IsOpen S) :
    frontier U ⊆ frontier S := by
  rcases hU.nonempty with ⟨x, hxU⟩
  rw [hU.eq_connectedComponentIn_of_mem hxU]
  exact frontier_connectedComponentIn_subset_frontier_of_isOpen hS_open
    (hU.subset hxU)

/--
%%handwave
name:
  Component closures add only ambient frontier points
statement:
  In a locally connected space, the closure of a component of an open set is
  contained in the component together with the frontier of the open set.
proof:
  The closure of any set is the set together with its frontier, and the
  frontier of the component lies in the ambient frontier.
-/
theorem IsComponentOf.closure_subset_union_frontier_of_isOpen
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {U S : Set X} (hU : IsComponentOf U S) (hS_open : IsOpen S) :
    closure U ⊆ U ∪ frontier S := by
  rw [closure_eq_self_union_frontier U]
  exact union_subset_union subset_rfl
    (hU.frontier_subset_frontier_of_isOpen hS_open)

/--
%%handwave
name:
  Component frontiers in a closed complement
statement:
  If \(K\) is closed, then the frontier of any component of \(X\setminus K\)
  lies in \(K\).
proof:
  The frontier lies in the frontier of \(X\setminus K\), which is the same as
  the frontier of \(K\), and the frontier of a closed set lies in the set.
-/
theorem IsComponentOf.frontier_subset_of_compl_isClosed
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ) (hK_closed : IsClosed K) :
    frontier U ⊆ K := by
  have hfrontier : frontier U ⊆ frontier Kᶜ :=
    hU.frontier_subset_frontier_of_isOpen hK_closed.isOpen_compl
  have hfrontierK : frontier Kᶜ ⊆ K := by
    rw [frontier_compl]
    exact hK_closed.frontier_subset
  exact hfrontier.trans hfrontierK

/--
%%handwave
name:
  Component closures in a closed complement
statement:
  If \(K\) is closed, then the closure of a component of \(X\setminus K\) is
  contained in that component together with \(K\).
proof:
  The only new points added by closing the component are frontier points, and
  those frontier points lie in \(K\).
-/
theorem IsComponentOf.closure_subset_union_of_compl_isClosed
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ) (hK_closed : IsClosed K) :
    closure U ⊆ U ∪ K := by
  exact (hU.closure_subset_union_frontier_of_isOpen hK_closed.isOpen_compl).trans
    (union_subset_union_right U
      (by
        rw [frontier_compl]
        exact hK_closed.frontier_subset))

/--
%%handwave
name:
  Complementary components touch the obstacle
statement:
  Let \(K\) be a nonempty closed subset of a connected locally connected
  space.  Every component of \(X\setminus K\) has a frontier point on \(K\).
proof:
  If such a component had no frontier point on \(K\), then its closure would
  stay in \(X\setminus K\).  Components of the open complement are closed
  inside the complement, so the component would be closed in \(X\).  It is
  also open; by connectedness it would be all of \(X\), contradicting
  \(K\ne\emptyset\).
-/
theorem IsComponentOf.frontier_inter_nonempty_of_compl_isClosed
    {X : Type} [TopologicalSpace X] [PreconnectedSpace X]
    [LocallyConnectedSpace X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ)
    (hK_closed : IsClosed K) (hK_nonempty : K.Nonempty) :
    (frontier U ∩ K).Nonempty := by
  by_contra hfrontier_empty
  have hfrontier_inter_empty : frontier U ∩ K = ∅ :=
    not_nonempty_iff_eq_empty.mp hfrontier_empty
  have hU_open : IsOpen U :=
    hU.isOpen_of_isOpen hK_closed.isOpen_compl
  have hclosure_subset_U : closure U ⊆ U := by
    intro x hx_closure
    have hxKc : x ∈ Kᶜ := by
      by_contra hxK
      have hxK_mem : x ∈ K := by
        simpa using hxK
      have hx_frontier : x ∈ frontier U := by
        rw [hU_open.frontier_eq]
        exact ⟨hx_closure, fun hxU => hU.subset hxU hxK_mem⟩
      have hx_empty : x ∈ frontier U ∩ K := ⟨hx_frontier, hxK_mem⟩
      rw [hfrontier_inter_empty] at hx_empty
      exact hx_empty
    rcases hU.nonempty with ⟨y, hyU⟩
    have hyKc : y ∈ Kᶜ := hU.subset hyU
    have hU_eq : U = connectedComponentIn Kᶜ y :=
      hU.eq_connectedComponentIn_of_mem hyU
    rw [hU_eq] at hx_closure ⊢
    exact connectedComponentIn_mem_of_mem_closure_of_mem
      hyKc hxKc hx_closure
  have hU_closed : IsClosed U :=
    isClosed_of_closure_subset hclosure_subset_U
  have hU_univ : U = univ :=
    IsClopen.eq_univ ⟨hU_closed, hU_open⟩ hU.nonempty
  rcases hK_nonempty with ⟨x, hxK⟩
  have hxU : x ∈ U := by
    rw [hU_univ]
    exact mem_univ x
  exact hU.subset hxU hxK

/--
%%handwave
name:
  Complementary components touch the boundary
statement:
  Let \(K\) be a nonempty closed subset of a connected locally connected
  space.  Every component of \(X\setminus K\) has a frontier point on the
  frontier of \(K\).
proof:
  A complementary component has a frontier point on \(K\).  Since the
  component lies in \(X\setminus K\), that point is also in the closure of
  \(X\setminus K\), hence lies on the frontier of \(K\).
-/
theorem IsComponentOf.frontier_inter_frontier_nonempty_of_compl_isClosed
    {X : Type} [TopologicalSpace X] [PreconnectedSpace X]
    [LocallyConnectedSpace X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ)
    (hK_closed : IsClosed K) (hK_nonempty : K.Nonempty) :
    (frontier U ∩ frontier K).Nonempty := by
  rcases hU.frontier_inter_nonempty_of_compl_isClosed
      hK_closed hK_nonempty with
    ⟨x, hx_frontierU, hxK⟩
  have hx_closureKc : x ∈ closure Kᶜ :=
    closure_mono hU.subset (frontier_subset_closure hx_frontierU)
  have hx_notKc : x ∉ Kᶜ := by
    simpa using hxK
  have hx_frontierKc : x ∈ frontier Kᶜ := by
    rw [frontier, hK_closed.isOpen_compl.interior_eq]
    exact ⟨hx_closureKc, hx_notKc⟩
  have hx_frontierK : x ∈ frontier K := by
    simpa [frontier_compl] using hx_frontierKc
  exact ⟨x, hx_frontierU, hx_frontierK⟩

/--
%%handwave
name:
  Finite incidence gives finitely many complementary components
statement:
  Let \(K\) be a nonempty closed subset of a connected locally connected
  space.  If the frontier of \(K\) has finitely many connected components and
  only finitely many complementary components are incident to each boundary
  component, then \(X\setminus K\) has finitely many components.
proof:
  Every complementary component touches the frontier of \(K\), so it is
  incident to one connected component of that frontier.  The complementary
  components are therefore covered by a finite union of finite incident
  families.
-/
theorem finite_complement_components_of_finite_boundary_components_and_finite_incidence
    {X : Type} [TopologicalSpace X] [PreconnectedSpace X]
    [LocallyConnectedSpace X]
    {K : Set X} (hK_closed : IsClosed K) (hK_nonempty : K.Nonempty)
    (hfinite_boundary : Finite (ConnectedComponents (frontier K)))
    (hfinite_incidence :
      ∀ B : ConnectedComponents (frontier K),
        {V : Set X |
          IsComponentOf V Kᶜ ∧
            ∃ x : frontier K,
              (x : X) ∈ frontier V ∧
                ConnectedComponents.mk x = B}.Finite) :
    {V : Set X | IsComponentOf V Kᶜ}.Finite := by
  classical
  letI : Finite (ConnectedComponents (frontier K)) := hfinite_boundary
  let incidence : ConnectedComponents (frontier K) → Set (Set X) :=
    fun B ↦
      {V : Set X |
        IsComponentOf V Kᶜ ∧
          ∃ x : frontier K,
            (x : X) ∈ frontier V ∧
              ConnectedComponents.mk x = B}
  have hcover :
      {V : Set X | IsComponentOf V Kᶜ} ⊆ ⋃ B, incidence B := by
    intro V hV
    rcases IsComponentOf.frontier_inter_frontier_nonempty_of_compl_isClosed
        hV hK_closed hK_nonempty with
      ⟨x, hx_frontierV, hx_frontierK⟩
    refine mem_iUnion.mpr
      ⟨ConnectedComponents.mk (⟨x, hx_frontierK⟩ : frontier K), ?_⟩
    exact ⟨hV, ⟨⟨x, hx_frontierK⟩, hx_frontierV, rfl⟩⟩
  have hfinite_union : (⋃ B, incidence B).Finite := by
    refine Set.finite_iUnion ?_
    intro B
    exact hfinite_incidence B
  exact hfinite_union.subset hcover

/--
%%handwave
name:
  Finite incidence along a larger boundary gives finitely many complementary components
statement:
  Let \(K\) be a nonempty closed subset of a connected locally connected
  space, and suppose the frontier of \(K\) is contained in a set \(A\).
  If \(A\) has finitely many connected components and only finitely many
  complementary components of \(X\setminus K\) are incident to each component
  of \(A\), then \(X\setminus K\) has finitely many components.
proof:
  Every complementary component touches the frontier of \(K\), hence touches
  \(A\).  Assign it to the connected component of \(A\) containing such a
  touching point.  The complementary components are covered by a finite union
  of finite incident families.
-/
theorem finite_complement_components_of_frontier_subset_finite_boundary_components_and_finite_incidence
    {X : Type} [TopologicalSpace X] [PreconnectedSpace X]
    [LocallyConnectedSpace X]
    {K A : Set X} (hK_closed : IsClosed K) (hK_nonempty : K.Nonempty)
    (hfrontier_subset : frontier K ⊆ A)
    (hfinite_boundary : Finite (ConnectedComponents A))
    (hfinite_incidence :
      ∀ B : ConnectedComponents A,
        {V : Set X |
          IsComponentOf V Kᶜ ∧
            ∃ x : A,
              (x : X) ∈ frontier V ∧
                ConnectedComponents.mk x = B}.Finite) :
    {V : Set X | IsComponentOf V Kᶜ}.Finite := by
  classical
  letI : Finite (ConnectedComponents A) := hfinite_boundary
  let incidence : ConnectedComponents A → Set (Set X) :=
    fun B ↦
      {V : Set X |
        IsComponentOf V Kᶜ ∧
          ∃ x : A,
            (x : X) ∈ frontier V ∧
              ConnectedComponents.mk x = B}
  have hcover :
      {V : Set X | IsComponentOf V Kᶜ} ⊆ ⋃ B, incidence B := by
    intro V hV
    rcases IsComponentOf.frontier_inter_frontier_nonempty_of_compl_isClosed
        hV hK_closed hK_nonempty with
      ⟨x, hx_frontierV, hx_frontierK⟩
    let xA : A := ⟨x, hfrontier_subset hx_frontierK⟩
    refine mem_iUnion.mpr ⟨ConnectedComponents.mk xA, ?_⟩
    exact ⟨hV, ⟨xA, hx_frontierV, rfl⟩⟩
  have hfinite_union : (⋃ B, incidence B).Finite := by
    refine Set.finite_iUnion ?_
    intro B
    exact hfinite_incidence B
  exact hfinite_union.subset hcover

/--
%%handwave
name:
  Compact sets in noncompact spaces have exterior points
statement:
  A compact subset of a noncompact space is not the whole space.
proof:
  Otherwise the compact subset would equal the entire space, making the space
  compact and contradicting noncompactness.
-/
theorem noncompact_exists_not_mem_compact
    {X : Type} [TopologicalSpace X] [NoncompactSpace X]
    {K : Set X} (hK : IsCompact K) :
    ∃ x : X, x ∉ K := by
  by_contra h
  have hK_univ : K = univ := by
    ext x
    constructor
    · intro _hx
      exact mem_univ x
    · intro _hx
      by_contra hxK
      exact h ⟨x, hxK⟩
  exact hK.ne_univ hK_univ

/--
%%handwave
name:
  Compact complements are nonempty in noncompact spaces
statement:
  The complement of a compact set in a noncompact space is nonempty.
proof:
  A compact set cannot be the entire noncompact space, so some point lies
  outside it.
-/
theorem noncompact_compl_nonempty_of_isCompact
    {X : Type} [TopologicalSpace X]
    (hnoncompact : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) :
    Kᶜ.Nonempty := by
  haveI : NoncompactSpace X := not_compactSpace_iff.mp hnoncompact
  rcases noncompact_exists_not_mem_compact hK with ⟨x, hxK⟩
  exact ⟨x, hxK⟩

/--
%%handwave
name:
  Compact complements have components in noncompact spaces
statement:
  The complement of a compact set in a noncompact space has at least one
  connected component.
proof:
  Choose a point outside the compact set and take its connected component
  within the complement.
-/
theorem noncompact_compact_complement_has_component
    {X : Type} [TopologicalSpace X]
    (hnoncompact : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) :
    ∃ U : Set X, IsComponentOf U Kᶜ := by
  rcases noncompact_compl_nonempty_of_isCompact hnoncompact hK with ⟨x, hxK⟩
  exact ⟨connectedComponentIn Kᶜ x, isComponentOf_connectedComponentIn hxK⟩

/--
%%handwave
name:
  Compact-exhaustion stages are proper in noncompact spaces
statement:
  No member of a compact exhaustion of a noncompact space is the whole space.
proof:
  If one compact member were all of \(X\), then \(X\) itself would be compact.
-/
theorem CompactExhaustion.ne_univ_of_noncompact
    {X : Type} [TopologicalSpace X]
    (hnoncompact : ¬ CompactSpace X) (E : CompactExhaustion X) (n : ℕ) :
    E n ≠ (univ : Set X) := by
  intro hE
  have hcompact_univ : IsCompact (univ : Set X) := by
    simpa [hE] using E.isCompact n
  exact hnoncompact ⟨hcompact_univ⟩

/--
%%handwave
name:
  Compact-exhaustion stages miss points in noncompact spaces
statement:
  Every member of a compact exhaustion of a noncompact space misses some point.
proof:
  Otherwise that member would be the whole space, contradicting
  noncompactness.
-/
theorem CompactExhaustion.exists_not_mem_of_noncompact
    {X : Type} [TopologicalSpace X]
    (hnoncompact : ¬ CompactSpace X) (E : CompactExhaustion X) (n : ℕ) :
    ∃ x : X, x ∉ E n := by
  by_contra hmissing
  have hE_univ : E n = (univ : Set X) := by
    rw [eq_univ_iff_forall]
    intro x
    by_contra hx
    exact hmissing ⟨x, hx⟩
  exact CompactExhaustion.ne_univ_of_noncompact hnoncompact E n hE_univ

/--
%%handwave
name:
  Far complementary components outside a compact-exhaustion stage
statement:
  If \(K\) is contained in a compact-exhaustion member \(E_n\), then some
  component of \(X\setminus K\) is not contained in \(E_n\).
proof:
  Choose a point outside \(E_n\).  Since \(K\subset E_n\), the point lies in
  \(X\setminus K\); its complementary component contains that point and hence
  is not contained in \(E_n\).
-/
theorem compactExhaustion_complement_has_component_not_subset_stage
    {X : Type} [TopologicalSpace X]
    (hnoncompact : ¬ CompactSpace X) (E : CompactExhaustion X)
    {K : Set X} {n : ℕ} (hK_subset : K ⊆ E n) :
    ∃ U : Set X, IsComponentOf U Kᶜ ∧ ¬ U ⊆ E n := by
  rcases CompactExhaustion.exists_not_mem_of_noncompact
      hnoncompact E n with
    ⟨x, hxE⟩
  have hxK : x ∈ Kᶜ := by
    intro hxK
    exact hxE (hK_subset hxK)
  refine ⟨connectedComponentIn Kᶜ x,
    isComponentOf_connectedComponentIn hxK, ?_⟩
  intro hsubset
  exact hxE (hsubset (mem_connectedComponentIn hxK))

/--
%%handwave
name:
  Far complementary components eventually exist at every stage
statement:
  If \(K\) is compact in a noncompact space with a compact exhaustion, then
  after some index every exhaustion member has a complementary component of
  \(X\setminus K\) that is not contained in that member.
proof:
  First put \(K\) inside one exhaustion member.  Monotonicity keeps it inside
  all later members, and the previous result supplies a component reaching
  outside each such member.
-/
theorem compactExhaustion_complement_has_component_not_subset_eventually
    {X : Type} [TopologicalSpace X]
    (hnoncompact : ¬ CompactSpace X) (E : CompactExhaustion X)
    {K : Set X} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ U : Set X, IsComponentOf U Kᶜ ∧ ¬ U ⊆ E n := by
  rcases E.exists_superset_of_isCompact hK with ⟨N, hKN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact compactExhaustion_complement_has_component_not_subset_stage
    hnoncompact E (hKN.trans (E.subset hn))

/--
%%handwave
name:
  Exterior component
statement:
  An exterior component of the complement of a compact set is a complementary
  component that eventually leaves every compact subset of the surface.
-/
def IsExteriorComponent {X : Type} [TopologicalSpace X] (K U : Set X) : Prop :=
  IsComponentOf U Kᶜ ∧ ∀ L : Set X, IsCompact L → ∃ x ∈ U, x ∉ L

/--
%%handwave
name:
  Escaping complementary components are exterior components
statement:
  A component of \(X\setminus K\) that leaves every compact set is an exterior
  component.
proof:
  These are exactly the two clauses in the definition of an exterior
  component.
-/
theorem IsComponentOf.isExteriorComponent_of_escapes
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsComponentOf U Kᶜ)
    (hesc : ∀ L : Set X, IsCompact L → ∃ x ∈ U, x ∉ L) :
    IsExteriorComponent K U :=
  ⟨hU, hesc⟩

/--
%%handwave
name:
  Exterior components are complementary components
statement:
  An exterior component is, in particular, a component of the complement of
  the compact set.
proof:
  This is the first clause in the definition of an exterior component.
-/
theorem IsExteriorComponent.isComponentOf
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsExteriorComponent K U) :
    IsComponentOf U Kᶜ :=
  hU.1

/--
%%handwave
name:
  Exterior components lie outside the compact set
statement:
  An exterior component of \(X\setminus K\) is contained in \(X\setminus K\).
proof:
  An exterior component is a complementary component, and every component is
  contained in its ambient set.
-/
theorem IsExteriorComponent.subset_compl
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsExteriorComponent K U) :
    U ⊆ Kᶜ :=
  hU.1.1

/--
%%handwave
name:
  Intersecting exterior components are equal
statement:
  Two exterior components of the same complement that intersect are equal.
proof:
  This is the uniqueness of connected components before using any
  simple-connectedness input.
-/
theorem IsExteriorComponent.eq_of_inter_nonempty
    {X : Type} [TopologicalSpace X] {K U V : Set X}
    (hU : IsExteriorComponent K U) (hV : IsExteriorComponent K V)
    (hUV : (U ∩ V).Nonempty) :
    U = V :=
  hU.isComponentOf.eq_of_inter_nonempty hV.isComponentOf hUV

/--
%%handwave
name:
  Exterior components are connected components
statement:
  An exterior component containing \(x\) is the connected component of \(x\)
  in the compact complement.
proof:
  A component is maximal among preconnected subsets of the complement, so the
  component containing \(x\) coincides with the connected component of \(x\)
  there.
-/
theorem IsExteriorComponent.eq_connectedComponentIn_of_mem
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsExteriorComponent K U) {x : X} (hxU : x ∈ U) :
    U = connectedComponentIn Kᶜ x :=
  hU.isComponentOf.eq_connectedComponentIn_of_mem hxU

/--
%%handwave
name:
  Distinct exterior components are disjoint
statement:
  Two distinct exterior components of the same compact complement have empty
  intersection.
proof:
  Intersecting components of the same set coincide by maximality.  Thus two
  distinct exterior components cannot meet.
-/
theorem IsExteriorComponent.inter_eq_empty_of_ne
    {X : Type} [TopologicalSpace X] {K U V : Set X}
    (hU : IsExteriorComponent K U) (hV : IsExteriorComponent K V)
    (hUV : U ≠ V) :
    U ∩ V = ∅ :=
  hU.isComponentOf.inter_eq_empty_of_ne hV.isComponentOf hUV

/--
%%handwave
name:
  Exterior components escape compact supports
statement:
  If \(U\) is an exterior component, then it contains points outside every
  prescribed compact set.
proof:
  This is the escaping clause in the definition of an exterior component.
-/
theorem IsExteriorComponent.exists_not_mem_compact
    {X : Type} [TopologicalSpace X] {K U L : Set X}
    (hU : IsExteriorComponent K U) (hL : IsCompact L) :
    ∃ x ∈ U, x ∉ L :=
  hU.2 L hL

/--
%%handwave
name:
  Exterior components are not compactly contained
statement:
  An exterior component is not contained in any compact subset of the surface.
proof:
  If it were contained in a compact set, the defining escaping property for
  that compact set would give a point both inside and outside it.
-/
theorem IsExteriorComponent.not_subset_compact
    {X : Type} [TopologicalSpace X] {K U L : Set X}
    (hU : IsExteriorComponent K U) (hL : IsCompact L) :
    ¬ U ⊆ L := by
  intro hUL
  rcases hU.exists_not_mem_compact hL with ⟨x, hxU, hxL⟩
  exact hxL (hUL hxU)

/--
%%handwave
name:
  Exterior criterion by compact containment
statement:
  A complementary component is exterior exactly when it is not contained in
  any compact subset of the surface.
proof:
  The forward direction is immediate from the escaping definition.  Conversely,
  if no compact contains the component, then each compact misses some point of
  it.
-/
theorem IsComponentOf.isExteriorComponent_iff_not_subset_compact
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsComponentOf U Kᶜ) :
    IsExteriorComponent K U ↔
      ∀ L : Set X, IsCompact L → ¬ U ⊆ L := by
  constructor
  · intro hExt L hL
    exact hExt.not_subset_compact hL
  · intro hnot
    refine ⟨hU, ?_⟩
    intro L hL
    by_contra hmissing
    have hUL : U ⊆ L := by
      intro x hxU
      by_contra hxL
      exact hmissing ⟨x, hxU, hxL⟩
    exact hnot L hL hUL

/--
%%handwave
name:
  Non-exterior components are compactly contained
statement:
  A complementary component that is not exterior is contained in some compact
  subset of the surface.
proof:
  This is the contrapositive of the compact-containment criterion.
-/
theorem IsComponentOf.not_isExteriorComponent_iff_subset_compact
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsComponentOf U Kᶜ) :
    ¬ IsExteriorComponent K U ↔
      ∃ L : Set X, IsCompact L ∧ U ⊆ L := by
  classical
  constructor
  · intro hnot
    by_contra hno
    apply hnot
    refine hU.isExteriorComponent_iff_not_subset_compact.mpr ?_
    intro L hL hUL
    exact hno ⟨L, hL, hUL⟩
  · rintro ⟨L, hL, hUL⟩ hExt
    exact (hU.isExteriorComponent_iff_not_subset_compact.mp hExt L hL) hUL

/--
%%handwave
name:
  Compactly contained complementary components have compact closure
statement:
  If \(K\) is compact and \(U\) is a component of \(X\setminus K\) contained
  in another compact set, then the closure of \(U\) is compact.
proof:
  The closure of \(U\) is contained in \(U\cup K\), hence in the union of the
  two compact sets.
-/
theorem IsComponentOf.closure_compact_of_subset_compact_compl
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K U L : Set X} (hU : IsComponentOf U Kᶜ)
    (hK : IsCompact K) (hL : IsCompact L) (hUL : U ⊆ L) :
    IsCompact (closure U) := by
  have hsub : closure U ⊆ L ∪ K :=
    (hU.closure_subset_union_of_compl_isClosed hK.isClosed).trans
      (union_subset_union hUL subset_rfl)
  exact (hL.union hK).of_isClosed_subset isClosed_closure hsub

/--
%%handwave
name:
  Non-exterior complementary components have compact closure
statement:
  If \(K\) is compact, every non-exterior component of \(X\setminus K\) has
  compact closure.
proof:
  A non-exterior component is contained in some compact set, and closing it
  only adds points from \(K\).
-/
theorem IsComponentOf.closure_compact_of_not_isExteriorComponent
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ) (hK : IsCompact K)
    (hnot : ¬ IsExteriorComponent K U) :
    IsCompact (closure U) := by
  rcases hU.not_isExteriorComponent_iff_subset_compact.mp hnot with
    ⟨L, hL, hUL⟩
  exact hU.closure_compact_of_subset_compact_compl hK hL hUL

/--
%%handwave
name:
  Non-exterior holes are compact under exterior uniqueness
statement:
  If \(U\) is the unique exterior component of \(X\setminus K\), then every
  complementary component different from \(U\) has compact closure.
proof:
  A different component cannot be exterior by uniqueness, and every
  non-exterior complementary component has compact closure.
-/
theorem IsComponentOf.closure_compact_of_ne_unique_exterior
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K U V : Set X} (hV : IsComponentOf V Kᶜ) (hK : IsCompact K)
    (hunique : ∀ W : Set X, IsExteriorComponent K W → W = U)
    (hne : V ≠ U) :
    IsCompact (closure V) := by
  refine hV.closure_compact_of_not_isExteriorComponent hK ?_
  intro hVext
  exact hne (hunique V hVext)

/--
%%handwave
name:
  Compact-closure components are not exterior
statement:
  A complementary component whose closure is compact is not exterior.
proof:
  The compact closure contains the component, contradicting the defining
  escape property of an exterior component.
-/
theorem IsComponentOf.not_isExteriorComponent_of_closure_compact
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (_hU : IsComponentOf U Kᶜ) (hclosure : IsCompact (closure U)) :
    ¬ IsExteriorComponent K U := by
  intro hExt
  exact hExt.not_subset_compact hclosure subset_closure

/--
%%handwave
name:
  Bounded-hole criterion by compact closure
statement:
  For the complement of a compact set in a locally connected Hausdorff space,
  a component is non-exterior exactly when its closure is compact.
proof:
  Non-exterior components are compactly contained, and closing such a
  component only adds points from the compact set.  Conversely, compact
  closure itself prevents escape.
-/
theorem IsComponentOf.not_isExteriorComponent_iff_closure_compact
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ) (hK : IsCompact K) :
    ¬ IsExteriorComponent K U ↔ IsCompact (closure U) := by
  constructor
  · exact hU.closure_compact_of_not_isExteriorComponent hK
  · exact hU.not_isExteriorComponent_of_closure_compact

/--
%%handwave
name:
  Exterior criterion by noncompact closure
statement:
  For the complement of a compact set in a locally connected Hausdorff space,
  a component is exterior exactly when its closure is not compact.
proof:
  This is the negation of the bounded-hole compact-closure criterion.
-/
theorem IsComponentOf.isExteriorComponent_iff_not_closure_compact
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ) (hK : IsCompact K) :
    IsExteriorComponent K U ↔ ¬ IsCompact (closure U) := by
  constructor
  · intro hExt hclosure
    exact hExt.not_subset_compact hclosure subset_closure
  · intro hnotCompact
    by_contra hnotExt
    exact hnotCompact
      (hU.closure_compact_of_not_isExteriorComponent hK hnotExt)

/--
%%handwave
name:
  Exterior components are nonempty
statement:
  Every exterior component is nonempty.
proof:
  Exterior components are complementary components, and components are
  nonempty by definition.
-/
theorem IsExteriorComponent.nonempty
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsExteriorComponent K U) : U.Nonempty :=
  hU.1.2.1

/--
%%handwave
name:
  Connected-component exterior criterion
statement:
  The component of a point outside \(K\) is an exterior component exactly when
  it leaves every compact subset of the surface.
proof:
  The connected component is already a component of \(X\setminus K\); hence the
  only additional condition for being exterior is precisely the stated
  escaping property.
-/
theorem connectedComponentIn_isExteriorComponent_iff
    {X : Type} [TopologicalSpace X] {K : Set X} {x : X} (hxK : x ∈ Kᶜ) :
    IsExteriorComponent K (connectedComponentIn Kᶜ x) ↔
      ∀ L : Set X, IsCompact L →
        ∃ y ∈ connectedComponentIn Kᶜ x, y ∉ L := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact (isComponentOf_connectedComponentIn hxK).isExteriorComponent_of_escapes h

/--
%%handwave
name:
  Bounded filling of a compact complement
statement:
  The bounded filling of a closed set is the interior of the union of the set
  with all complementary components whose closures are compact.
-/
def boundedFillingOfComplement
    {X : Type} [TopologicalSpace X] (K : Set X) : Set X :=
  interior
    (K ∪
      {x : X |
        ∃ V : Set X, IsComponentOf V Kᶜ ∧ IsCompact (closure V) ∧ x ∈ V})

/-- The inclusion of a bounded filling into the ambient space. -/
def boundedFillingInclusion
    {X : Type} [TopologicalSpace X] (K : Set X) :
    C(boundedFillingOfComplement K, X) where
  toFun x := x
  continuous_toFun := continuous_subtype_val

/--
%%handwave
name:
  Bounded fillings are open
statement:
  The bounded filling of a complement is open.
proof:
  By definition, the bounded filling is the interior of the obstacle together
  with all complementary components having compact closure, and every
  interior is open.
-/
theorem boundedFillingOfComplement_isOpen
    {X : Type} [TopologicalSpace X] (K : Set X) :
    IsOpen (boundedFillingOfComplement K) :=
  isOpen_interior

/--
%%handwave
name:
  Open subsets of the obstacle lie in the bounded filling
statement:
  Every open subset of the filled obstacle lies in its bounded filling.
proof:
  The bounded filling is the interior of a set containing the obstacle.
-/
theorem open_subset_boundedFillingOfComplement_of_subset_obstacle
    {X : Type} [TopologicalSpace X] {C K : Set X}
    (hC_open : IsOpen C) (hCK : C ⊆ K) :
    C ⊆ boundedFillingOfComplement K :=
  hC_open.subset_interior_iff.mpr
    (fun _ hx => Or.inl (hCK hx))

/--
%%handwave
name:
  Bounded complementary components lie in the bounded filling
statement:
  If a component of the complement has compact closure, then it lies in the
  bounded filling.
proof:
  The component is open and is one of the bounded complementary pieces
  adjoined before taking the interior.
-/
theorem IsComponentOf.subset_boundedFillingOfComplement_of_closure_compact
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K V : Set X} (hV : IsComponentOf V Kᶜ) (hK_closed : IsClosed K)
    (hV_compact : IsCompact (closure V)) :
    V ⊆ boundedFillingOfComplement K := by
  have hV_open : IsOpen V :=
    hV.isOpen_of_isOpen hK_closed.isOpen_compl
  refine hV_open.subset_interior_iff.mpr ?_
  intro x hxV
  exact Or.inr ⟨V, hV, hV_compact, hxV⟩

/--
%%handwave
name:
  Bounded fillings lie in the obstacle and bounded components
statement:
  A point of the bounded filling lies either in the original closed set or in
  a complementary component with compact closure.
proof:
  The bounded filling is the interior of the union of exactly those sets, and
  every interior point belongs to the union itself.
-/
theorem boundedFillingOfComplement_subset_obstacle_union_bounded_components
    {X : Type} [TopologicalSpace X] (K : Set X) :
    boundedFillingOfComplement K ⊆
      K ∪
        {x : X |
          ∃ V : Set X, IsComponentOf V Kᶜ ∧
            IsCompact (closure V) ∧ x ∈ V} :=
  interior_subset

/--
%%handwave
name:
  Bounded fillings are monotone
statement:
  If \(K_1\subset K_2\), then the bounded filling of \(K_1\) is contained in
  the bounded filling of \(K_2\).
proof:
  A point in \(K_1\) lies in \(K_2\).  A point in a bounded complementary
  component of \(X\setminus K_1\) either lies in \(K_2\), or lies in a
  component of \(X\setminus K_2\) contained in the original bounded component;
  its closure is therefore still compact.
-/
theorem boundedFillingOfComplement_mono
    {X : Type} [TopologicalSpace X] {K₁ K₂ : Set X}
    (hK : K₁ ⊆ K₂) :
    boundedFillingOfComplement K₁ ⊆ boundedFillingOfComplement K₂ := by
  refine interior_mono ?_
  intro x hx
  rcases hx with hxK₁ | hxhole
  · exact Or.inl (hK hxK₁)
  · rcases hxhole with ⟨V, hV, hV_compact, hxV⟩
    by_cases hxK₂ : x ∈ K₂
    · exact Or.inl hxK₂
    · have hxK₂c : x ∈ K₂ᶜ := hxK₂
      let W : Set X := connectedComponentIn K₂ᶜ x
      have hxW : x ∈ W := by
        dsimp [W]
        exact mem_connectedComponentIn hxK₂c
      have hWcomp : IsComponentOf W K₂ᶜ := by
        dsimp [W]
        exact isComponentOf_connectedComponentIn hxK₂c
      have hW_subset_K₁c : W ⊆ K₁ᶜ := by
        intro y hyW hyK₁
        exact hWcomp.subset hyW (hK hyK₁)
      have hW_subset_V : W ⊆ V :=
        hV.2.2.2 W hW_subset_K₁c hWcomp.isPreconnected
          ⟨x, hxV, hxW⟩
      have hW_compact : IsCompact (closure W) :=
        hV_compact.of_isClosed_subset isClosed_closure
          (closure_mono hW_subset_V)
      exact Or.inr ⟨W, hWcomp, hW_compact, hxW⟩

/--
%%handwave
name:
  Bounded-filling frontiers lie on the obstacle
statement:
  If \(K\) is closed in a locally connected space, then the frontier of its
  bounded filling is contained in \(K\).
proof:
  Away from \(K\), a point lies in a single open complementary component.  If
  that component has compact closure, it is entirely inside the bounded
  filling; otherwise it is entirely outside the bounded filling.  In either
  case the point is not on the frontier.
-/
theorem boundedFillingOfComplement_frontier_subset_obstacle
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K : Set X} (hK_closed : IsClosed K) :
    frontier (boundedFillingOfComplement K) ⊆ K := by
  classical
  intro x hx_frontier
  by_contra hxK
  have hxKc : x ∈ Kᶜ := hxK
  let V : Set X := connectedComponentIn Kᶜ x
  have hxV : x ∈ V := by
    dsimp [V]
    exact mem_connectedComponentIn hxKc
  have hVcomp : IsComponentOf V Kᶜ := by
    dsimp [V]
    exact isComponentOf_connectedComponentIn hxKc
  have hV_open : IsOpen V :=
    hVcomp.isOpen_of_isOpen hK_closed.isOpen_compl
  by_cases hV_compact : IsCompact (closure V)
  · have hV_subset :
        V ⊆ boundedFillingOfComplement K :=
      hVcomp.subset_boundedFillingOfComplement_of_closure_compact
        hK_closed hV_compact
    have hx_fill : x ∈ boundedFillingOfComplement K := hV_subset hxV
    have hx_empty :
        x ∈ boundedFillingOfComplement K ∩
          frontier (boundedFillingOfComplement K) :=
      ⟨hx_fill, hx_frontier⟩
    rw [(boundedFillingOfComplement_isOpen K).inter_frontier_eq] at hx_empty
    exact hx_empty
  · have hV_disjoint :
        Disjoint V (boundedFillingOfComplement K) := by
      refine disjoint_left.mpr ?_
      intro y hyV hyF
      have hy_union :
          y ∈
            K ∪
              {z : X |
                ∃ W : Set X, IsComponentOf W Kᶜ ∧
                  IsCompact (closure W) ∧ z ∈ W} :=
        boundedFillingOfComplement_subset_obstacle_union_bounded_components
          K hyF
      rcases hy_union with hyK | hyHole
      · exact hVcomp.subset hyV hyK
      · rcases hyHole with ⟨W, hW, hW_compact, hyW⟩
        have hVW : V = W :=
          hVcomp.eq_of_inter_nonempty hW ⟨y, hyV, hyW⟩
        exact hV_compact (by simpa [hVW] using hW_compact)
    have hV_nhds : V ∈ 𝓝 x := hV_open.mem_nhds hxV
    rcases mem_closure_iff_nhds.mp
        (frontier_subset_closure hx_frontier) V hV_nhds with
      ⟨y, hyV, hyF⟩
    exact Set.disjoint_left.mp hV_disjoint hyV hyF

/--
%%handwave
name:
  Bounded fillings are compact in the finite-component case
statement:
  If \(K\) is compact and \(X\setminus K\) has only finitely many components,
  then the bounded filling of \(K\) has compact closure.
proof:
  The closure of the bounded filling lies in \(K\) together with the finite
  union of closures of the bounded complementary components.
-/
theorem boundedFillingOfComplement_compact_closure_of_finite_components
    {X : Type} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K)
    (hfinite : {V : Set X | IsComponentOf V Kᶜ}.Finite) :
    IsCompact (closure (boundedFillingOfComplement K)) := by
  classical
  let components : Set (Set X) := {V : Set X | IsComponentOf V Kᶜ}
  let boundedComponents : Finset (Set X) :=
    hfinite.toFinset.filter (fun V : Set X => IsCompact (closure V))
  let B : Set X := ⋃ V ∈ boundedComponents, closure V
  have hB_compact : IsCompact B := by
    dsimp [B, boundedComponents]
    refine (hfinite.toFinset.filter
      (fun V : Set X => IsCompact (closure V))).isCompact_biUnion ?_
    intro V hVmem
    exact (Finset.mem_filter.mp hVmem).2
  have hsub :
      boundedFillingOfComplement K ⊆ K ∪ B := by
    intro x hx
    have hx_union :=
      boundedFillingOfComplement_subset_obstacle_union_bounded_components
        K hx
    rcases hx_union with hxK | hxhole
    · exact Or.inl hxK
    · rcases hxhole with ⟨V, hVcomp, hV_compact, hxV⟩
      have hVmem_components : V ∈ components := by
        dsimp [components]
        exact hVcomp
      have hVfin : V ∈ hfinite.toFinset :=
        hfinite.mem_toFinset.mpr hVmem_components
      have hVbounded : V ∈ boundedComponents := by
        dsimp [boundedComponents]
        exact Finset.mem_filter.mpr ⟨hVfin, hV_compact⟩
      exact Or.inr (by
        dsimp [B]
        exact mem_iUnion₂.mpr ⟨V, hVbounded, subset_closure hxV⟩)
  have hclosed : IsClosed (K ∪ B) :=
    (hK.union hB_compact).isClosed
  have hclosure_subset : closure (boundedFillingOfComplement K) ⊆ K ∪ B :=
    closure_minimal hsub hclosed
  exact (hK.union hB_compact).of_isClosed_subset
    isClosed_closure hclosure_subset

/--
%%handwave
name:
  Filled side of an exterior component
statement:
  The filled side determined by an exterior component is the open side
  obtained by taking the interior of its complement.
-/
def filledSideOfExteriorComponent
    {X : Type} [TopologicalSpace X] (U : Set X) : Set X :=
  interior Uᶜ

/--
%%handwave
name:
  Filled sides are open
statement:
  The filled side of an exterior component is open.
proof:
  It is defined as the interior of the complement, and interiors are open.
-/
theorem filledSideOfExteriorComponent_isOpen
    {X : Type} [TopologicalSpace X] (U : Set X) :
    IsOpen (filledSideOfExteriorComponent U) :=
  isOpen_interior

/--
%%handwave
name:
  Filled sides avoid the exterior component
statement:
  The filled side is contained in the complement of the exterior component.
proof:
  Every interior of a set is contained in that set.
-/
theorem filledSideOfExteriorComponent_subset_compl
    {X : Type} [TopologicalSpace X] (U : Set X) :
    filledSideOfExteriorComponent U ⊆ Uᶜ :=
  interior_subset

/--
%%handwave
name:
  Filled sides are disjoint from the exterior component
statement:
  The filled side and the exterior component are disjoint.
proof:
  The filled side lies in the complement of the exterior component.
-/
theorem filledSideOfExteriorComponent_disjoint
    {X : Type} [TopologicalSpace X] (U : Set X) :
    Disjoint (filledSideOfExteriorComponent U) U := by
  exact disjoint_left.mpr fun _ hx hU =>
    filledSideOfExteriorComponent_subset_compl U hx hU

/--
%%handwave
name:
  Open subsets of the closed side lie in the filled side
statement:
  If an open set is contained in the complement of the exterior component,
  then it is contained in the filled side.
proof:
  The filled side is the interior of that complement.
-/
theorem subset_filledSideOfExteriorComponent_of_isOpen_subset_compl
    {X : Type} [TopologicalSpace X] {C U : Set X}
    (hC_open : IsOpen C) (hCU : C ⊆ Uᶜ) :
    C ⊆ filledSideOfExteriorComponent U :=
  hC_open.subset_interior_iff.mpr hCU

/--
%%handwave
name:
  Sets whose closure avoids the exterior lie in the filled side
statement:
  If an open set has closure disjoint from the exterior component, then it is
  contained in the filled side.
proof:
  The set lies in its closure, and its closure avoids the exterior component;
  hence the set lies in the complement of the exterior component.  Since the
  set is open, it lies in the interior of that complement.
-/
theorem subset_filledSideOfExteriorComponent_of_isOpen_closure_subset_compl
    {X : Type} [TopologicalSpace X] {C U : Set X}
    (hC_open : IsOpen C) (hCU : closure C ⊆ Uᶜ) :
    C ⊆ filledSideOfExteriorComponent U :=
  subset_filledSideOfExteriorComponent_of_isOpen_subset_compl hC_open
    (subset_closure.trans hCU)

/--
%%handwave
name:
  Filled-side closure avoids open exterior components
statement:
  If the exterior component is open, then the closure of the filled side is
  still disjoint from that exterior component.
proof:
  The complement of an open set is closed, and the filled side is contained in
  that closed complement.
-/
theorem closure_filledSideOfExteriorComponent_subset_compl_of_isOpen
    {X : Type} [TopologicalSpace X] {U : Set X} (hU_open : IsOpen U) :
    closure (filledSideOfExteriorComponent U) ⊆ Uᶜ :=
  closure_minimal (filledSideOfExteriorComponent_subset_compl U)
    hU_open.isClosed_compl

/--
%%handwave
name:
  Filled-side frontiers lie on exterior frontiers
statement:
  The frontier of the filled side is contained in the frontier of the exterior
  component.
proof:
  The filled side is the interior of the exterior complement.  The frontier of
  an interior lies in the original frontier, and frontiers are unchanged by
  taking complements.
-/
theorem frontier_filledSideOfExteriorComponent_subset_frontier
    {X : Type} [TopologicalSpace X] (U : Set X) :
    frontier (filledSideOfExteriorComponent U) ⊆ frontier U := by
  dsimp [filledSideOfExteriorComponent]
  simpa [frontier_compl] using
    (frontier_interior_subset (s := Uᶜ))

/--
%%handwave
name:
  Filled-side frontiers lie on the compact obstacle
statement:
  If \(U\) is an exterior component of \(X\setminus K\) and \(K\) is closed,
  then the frontier of the filled side determined by \(U\) lies in \(K\).
proof:
  The filled-side frontier lies on the frontier of \(U\), and the frontier of
  a component of \(X\setminus K\) lies in \(K\).
-/
theorem IsExteriorComponent.frontier_filledSide_subset_of_isClosed
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K U : Set X} (hU : IsExteriorComponent K U) (hK_closed : IsClosed K) :
    frontier (filledSideOfExteriorComponent U) ⊆ K :=
  (frontier_filledSideOfExteriorComponent_subset_frontier U).trans
    (hU.isComponentOf.frontier_subset_of_compl_isClosed hK_closed)

/--
%%handwave
name:
  Local set equality gives local frontier equality
statement:
  If two sets agree after intersecting with an open neighborhood of a point,
  then their frontiers agree near that point.
proof:
  Inside the open neighborhood, the frontier of an intersection with that
  neighborhood is the original frontier restricted to the neighborhood.
-/
theorem eventually_frontier_congr_of_local_inter_eq
    {X : Type} [TopologicalSpace X] {s t N : Set X} {x : X}
    (hN_open : IsOpen N) (hxN : x ∈ N) (hst : s ∩ N = t ∩ N) :
    ∀ᶠ y in 𝓝 x, (y ∈ frontier s ↔ y ∈ frontier t) := by
  filter_upwards [hN_open.mem_nhds hxN] with y hyN
  have hs :
      y ∈ frontier (s ∩ N) ↔ y ∈ frontier s := by
    have h :=
      congrArg (fun A : Set X => y ∈ A)
        (frontier_inter_open_inter (s := s) (t := N) hN_open)
    simpa [hyN] using h
  have ht :
      y ∈ frontier (t ∩ N) ↔ y ∈ frontier t := by
    have h :=
      congrArg (fun A : Set X => y ∈ A)
        (frontier_inter_open_inter (s := t) (t := N) hN_open)
    simpa [hyN] using h
  rw [← hs, hst, ht]

/--
%%handwave
name:
  Local membership equality gives local frontier equality
statement:
  If two sets have the same membership germ at a point, then their frontiers
  have the same membership germ at that point.
proof:
  Choose an open neighborhood on which membership in the two sets is
  equivalent, then apply local frontier equality for intersections with that
  neighborhood.
-/
theorem eventually_frontier_congr_of_eventually_mem_iff
    {X : Type} [TopologicalSpace X] {s t : Set X} {x : X}
    (hst : ∀ᶠ y in 𝓝 x, (y ∈ s ↔ y ∈ t)) :
    ∀ᶠ y in 𝓝 x, (y ∈ frontier s ↔ y ∈ frontier t) := by
  rcases mem_nhds_iff.mp hst with ⟨N, hN_subset, hN_open, hxN⟩
  have hinter : s ∩ N = t ∩ N := by
    ext y
    constructor
    · rintro ⟨hys, hyN⟩
      exact ⟨(hN_subset hyN).mp hys, hyN⟩
    · rintro ⟨hyt, hyN⟩
      exact ⟨(hN_subset hyN).mpr hyt, hyN⟩
  exact eventually_frontier_congr_of_local_inter_eq hN_open hxN hinter

/--
%%handwave
name:
  Smooth boundary data transfers across equal local germs
statement:
  If \(V\) has smooth boundary and, near a point, \(U\) has the same points
  and the same frontier as \(V\), then the smooth defining function for \(V\)
  is also smooth boundary data for \(U\) at that point.
proof:
  Reuse the same chart and defining function, replacing membership and
  frontier membership by the local equivalences.
-/
theorem hasSmoothBoundary_localData_of_eventually_mem_and_frontier_iff
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U V : Set X} {x : X}
    (hV : HasSmoothBoundary V) (hxV : x ∈ frontier V)
    (hmem : ∀ᶠ y in 𝓝 x, (y ∈ U ↔ y ∈ V))
    (hfrontier : ∀ᶠ y in 𝓝 x, (y ∈ frontier U ↔ y ∈ frontier V)) :
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧ x ∈ e.source ∧
      ∃ r : ℂ → ℝ, ContDiffOnNhdAt r (e x) ∧
        ∃ dr : ℂ →L[ℝ] ℝ,
          HasFDerivAt r dr (e x) ∧ dr ≠ 0 ∧
            ∀ᶠ y in 𝓝 x,
              y ∈ e.source ∧
                (y ∈ U ↔ r (e y) < 0) ∧
                  (y ∈ frontier U ↔ r (e y) = 0) := by
  rcases hV x hxV with
    ⟨e, he, hx_source, r, hr_smooth, dr, hr_deriv, hdr_ne, hlocal⟩
  refine ⟨e, he, hx_source, r, hr_smooth, dr, hr_deriv, hdr_ne, ?_⟩
  filter_upwards [hlocal, hmem, hfrontier] with y hy_local hy_mem hy_frontier
  rcases hy_local with ⟨hy_source, hyV_mem, hyV_frontier⟩
  exact ⟨hy_source, hy_mem.trans hyV_mem,
    hy_frontier.trans hyV_frontier⟩

/--
%%handwave
name:
  Components lie in the filled side of their exterior
statement:
  If \(U\) is an exterior component of the complement of \(\overline C\) and
  \(C\) is open, then \(C\) is contained in the filled side determined by
  \(U\).
proof:
  The exterior component is disjoint from \(\overline C\).  Therefore \(C\)
  lies in the complement of \(U\), and openness puts it inside the interior of
  that complement.
-/
theorem IsExteriorComponent.open_subset_filledSide_of_closure_complement
    {X : Type} [TopologicalSpace X] {C U : Set X}
    (hU : IsExteriorComponent (closure C) U) (hC_open : IsOpen C) :
    C ⊆ filledSideOfExteriorComponent U :=
  subset_filledSideOfExteriorComponent_of_isOpen_closure_subset_compl hC_open
    (by
      intro x hxC hxU
      exact hU.subset_compl hxU hxC)

/--
%%handwave
name:
  Other complementary components lie in the filled side
statement:
  If \(U\) is a complementary component and \(V\) is a distinct component of
  the same closed complement, then \(V\) lies in the filled side determined by
  \(U\).
proof:
  The component \(V\) is open and disjoint from \(U\).  Hence it is an open
  subset of the complement of \(U\), and so lies in the interior of that
  complement.
-/
theorem IsComponentOf.subset_filledSide_of_ne_exterior
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K U V : Set X} (hU : IsExteriorComponent K U)
    (hV : IsComponentOf V Kᶜ) (hK_closed : IsClosed K)
    (hne : V ≠ U) :
    V ⊆ filledSideOfExteriorComponent U := by
  have hV_open : IsOpen V :=
    hV.isOpen_of_isOpen hK_closed.isOpen_compl
  refine subset_filledSideOfExteriorComponent_of_isOpen_subset_compl hV_open ?_
  intro x hxV hxU
  have hVU : (V ∩ U).Nonempty := ⟨x, hxV, hxU⟩
  exact hne (hV.eq_of_inter_nonempty hU.isComponentOf hVU)

/--
%%handwave
name:
  Filled-side points lie on the obstacle or in a bounded complementary region
statement:
  If \(U\) is an exterior component of \(X\setminus K\), then every point of
  the filled side determined by \(U\) either lies in \(K\), or lies in a
  complementary component different from \(U\).
proof:
  A point of the filled side is not in \(U\).  If it is not in \(K\), take the
  component of \(X\setminus K\) containing it.  That component cannot be
  \(U\), since the point avoids \(U\).
-/
theorem IsExteriorComponent.filledSide_subset_union_nonExterior_components
    {X : Type} [TopologicalSpace X]
    {K U : Set X} (_hU : IsExteriorComponent K U) :
    filledSideOfExteriorComponent U ⊆
      K ∪ {x : X | ∃ V : Set X, IsComponentOf V Kᶜ ∧ V ≠ U ∧ x ∈ V} := by
  intro x hx
  by_cases hxK : x ∈ K
  · exact Or.inl hxK
  · have hxKc : x ∈ Kᶜ := hxK
    have hxUc : x ∈ Uᶜ :=
      filledSideOfExteriorComponent_subset_compl U hx
    let C : Set X := connectedComponentIn Kᶜ x
    have hxC : x ∈ C := by
      dsimp [C]
      exact mem_connectedComponentIn hxKc
    have hCcomp : IsComponentOf C Kᶜ := by
      dsimp [C]
      exact isComponentOf_connectedComponentIn hxKc
    have hC_ne : C ≠ U := by
      intro hCU
      have hxU : x ∈ U := by
        simpa [hCU] using hxC
      exact hxUc hxU
    exact Or.inr ⟨C, hCcomp, hC_ne, hxC⟩

/--
%%handwave
name:
  Points in the same filled hole are joined inside the filled side
statement:
  Let \(V\) be a complementary component of \(X\setminus K\) distinct from
  the exterior component \(U\).  Then any two points of \(V\) can be joined by
  a path lying in the filled side determined by \(U\).
proof:
  The complement of the closed set \(K\) is open.  In a locally path-connected
  space, its components are path connected.  Since \(V\ne U\), the whole
  component \(V\) lies in the filled side.
-/
theorem IsComponentOf.joinedIn_filledSide_of_ne_exterior
    {X : Type} [TopologicalSpace X] [LocPathConnectedSpace X]
    {K U V : Set X} (hU : IsExteriorComponent K U)
    (hV : IsComponentOf V Kᶜ) (hK_closed : IsClosed K)
    (hne : V ≠ U) :
    ∀ x ∈ V, ∀ y ∈ V, JoinedIn (filledSideOfExteriorComponent U) x y := by
  haveI : LocallyConnectedSpace X := locPathConnectedSpace_locallyConnectedSpace
  have hpath : IsPathConnected V :=
    hV.isPathConnected_of_compl_isClosed hK_closed
  have hV_subset_filled : V ⊆ filledSideOfExteriorComponent U :=
    IsComponentOf.subset_filledSide_of_ne_exterior hU hV hK_closed hne
  intro x hx y hy
  exact (hpath.joinedIn x hx y hy).mono hV_subset_filled

/--
%%handwave
name:
  The filled-side closure lies on the obstacle or on a hole
statement:
  If \(U\) is an exterior component of \(X\setminus K\) and \(K\) is closed,
  then every point in the closure of the filled side determined by \(U\) lies
  either on \(K\) or in the closure of a complementary component different
  from \(U\).
proof:
  The closure of the filled side is disjoint from the open exterior component.
  A point outside \(K\) lies in a unique complementary component.  Since it is
  not in \(U\), that component is one of the holes.
-/
theorem IsExteriorComponent.closure_filledSide_subset_union_nonExterior_component_closures
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K U : Set X} (hK_closed : IsClosed K)
    (hU : IsExteriorComponent K U) :
    closure (filledSideOfExteriorComponent U) ⊆
      K ∪ {x : X | ∃ V : Set X, IsComponentOf V Kᶜ ∧ V ≠ U ∧ x ∈ closure V} := by
  have hU_open : IsOpen U :=
    hU.isComponentOf.isOpen_of_isOpen hK_closed.isOpen_compl
  have hclosure_subset_Uc :
      closure (filledSideOfExteriorComponent U) ⊆ Uᶜ :=
    closure_filledSideOfExteriorComponent_subset_compl_of_isOpen hU_open
  intro x hx
  by_cases hxK : x ∈ K
  · exact Or.inl hxK
  · have hxKc : x ∈ Kᶜ := hxK
    have hxUc : x ∈ Uᶜ := hclosure_subset_Uc hx
    let C : Set X := connectedComponentIn Kᶜ x
    have hxC : x ∈ C := by
      dsimp [C]
      exact mem_connectedComponentIn hxKc
    have hCcomp : IsComponentOf C Kᶜ := by
      dsimp [C]
      exact isComponentOf_connectedComponentIn hxKc
    have hC_ne : C ≠ U := by
      intro hCU
      have hxU : x ∈ U := by
        simpa [hCU] using hxC
      exact hxUc hxU
    exact Or.inr ⟨C, hCcomp, hC_ne, subset_closure hxC⟩

/--
%%handwave
name:
  Filled sides are compact in the finite-component case
statement:
  If \(K\) is compact, \(X\setminus K\) has only finitely many components,
  and \(U\) is the unique exterior component, then the filled side determined
  by \(U\) has compact closure.
proof:
  The frontier of the filled side lies in \(K\).  Any point of the filled-side
  closure outside \(K\) lies in a complementary component different from
  \(U\).  By uniqueness, that component is not exterior, hence has compact
  closure.  Since there are only finitely many such components, the closure of
  the filled side lies in a finite union of compact sets.
-/
theorem IsExteriorComponent.filledSide_closure_compact_of_finite_components
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsExteriorComponent K U)
    (hunique : ∀ V : Set X, IsExteriorComponent K V → V = U)
    (hfinite : {V : Set X | IsComponentOf V Kᶜ}.Finite) :
    IsCompact (closure (filledSideOfExteriorComponent U)) := by
  classical
  let components : Set (Set X) := {V : Set X | IsComponentOf V Kᶜ}
  let boundedComponents : Finset (Set X) :=
    hfinite.toFinset.filter (fun V : Set X => V ≠ U)
  let B : Set X := ⋃ V ∈ boundedComponents, closure V
  have hB_compact : IsCompact B := by
    dsimp [B, boundedComponents]
    refine (hfinite.toFinset.filter (fun V : Set X => V ≠ U)).isCompact_biUnion ?_
    intro V hVmem
    rcases Finset.mem_filter.mp hVmem with ⟨hVfin, hV_ne⟩
    have hVcomp : IsComponentOf V Kᶜ :=
      hfinite.mem_toFinset.mp hVfin
    exact hVcomp.closure_compact_of_ne_unique_exterior hK hunique hV_ne
  have hU_open : IsOpen U :=
    hU.isComponentOf.isOpen_of_isOpen hK.isClosed.isOpen_compl
  have hclosure_subset_Uc :
      closure (filledSideOfExteriorComponent U) ⊆ Uᶜ :=
    closure_filledSideOfExteriorComponent_subset_compl_of_isOpen hU_open
  have hsub :
      closure (filledSideOfExteriorComponent U) ⊆ K ∪ B := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · have hxKc : x ∈ Kᶜ := hxK
      have hxUc : x ∈ Uᶜ := hclosure_subset_Uc hx
      let C : Set X := connectedComponentIn Kᶜ x
      have hxC : x ∈ C := by
        dsimp [C]
        exact mem_connectedComponentIn hxKc
      have hCcomp : IsComponentOf C Kᶜ := by
        dsimp [C]
        exact isComponentOf_connectedComponentIn hxKc
      have hC_ne : C ≠ U := by
        intro hCU
        have hxU : x ∈ U := by
          simpa [hCU] using hxC
        exact hxUc hxU
      have hCfin : C ∈ hfinite.toFinset :=
        hfinite.mem_toFinset.mpr hCcomp
      have hCbounded : C ∈ boundedComponents := by
        dsimp [boundedComponents]
        exact Finset.mem_filter.mpr ⟨hCfin, hC_ne⟩
      exact Or.inr (by
        dsimp [B]
        exact mem_iUnion₂.mpr ⟨C, hCbounded, subset_closure hxC⟩)
  exact (hK.union hB_compact).of_isClosed_subset isClosed_closure hsub

/--
%%handwave
name:
  Filled sides are compact when all holes are trapped
statement:
  If \(K\) is compact, \(U\) is an exterior component of \(X\setminus K\),
  and the closures of all complementary components different from \(U\) lie in
  one compact set \(B\), then the filled side determined by \(U\) has compact
  closure.
proof:
  The closure of the filled side is disjoint from the open exterior component.
  A point of that closure is either on \(K\), or else it belongs to the closure
  of the complementary component containing it.  If that component were
  \(U\), the point would lie in the exterior component, a contradiction.  Thus
  the point lies in the prescribed compact set.
-/
theorem IsExteriorComponent.filledSide_closure_compact_of_nonExterior_components_subset_compact
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K U B : Set X} (hK : IsCompact K) (hU : IsExteriorComponent K U)
    (hB : IsCompact B)
    (hcomponents :
      ∀ V : Set X, IsComponentOf V Kᶜ → V ≠ U → closure V ⊆ B) :
    IsCompact (closure (filledSideOfExteriorComponent U)) := by
  have hcover :=
    hU.closure_filledSide_subset_union_nonExterior_component_closures
      hK.isClosed
  have hsub :
      closure (filledSideOfExteriorComponent U) ⊆ K ∪ B := by
    intro x hx
    rcases hcover hx with hxK | hxHole
    · exact Or.inl hxK
    · rcases hxHole with ⟨V, hVcomp, hV_ne, hxVclosure⟩
      exact Or.inr (hcomponents V hVcomp hV_ne hxVclosure)
  exact (hK.union hB).of_isClosed_subset isClosed_closure hsub

/--
%%handwave
name:
  Exterior components shrink as the compact obstacle grows
statement:
  If \(K_1\subset K_2\), \(U_i\) is an exterior component of
  \(X\setminus K_i\), and \(U_1\) is the unique exterior component for
  \(K_1\), then \(U_2\subset U_1\).
proof:
  The set \(U_2\) is a preconnected subset of \(X\setminus K_1\), so it lies
  in one component of \(X\setminus K_1\).  Since \(U_2\) escapes every compact
  set, that larger component is exterior.  Uniqueness for \(K_1\) identifies
  it with \(U_1\).
-/
theorem IsExteriorComponent.subset_of_subset_left_of_unique
    {X : Type} [TopologicalSpace X]
    {K₁ K₂ U₁ U₂ : Set X} (hK : K₁ ⊆ K₂)
    (hU₁ : IsExteriorComponent K₁ U₁)
    (hU₂ : IsExteriorComponent K₂ U₂)
    (hunique₁ :
      ∀ V : Set X, IsExteriorComponent K₁ V → V = U₁) :
    U₂ ⊆ U₁ := by
  have _hU₁_nonempty : U₁.Nonempty := hU₁.nonempty
  rcases hU₂.nonempty with ⟨x, hxU₂⟩
  have hU₂_subset_K₁c : U₂ ⊆ K₁ᶜ := by
    intro y hyU₂ hyK₁
    exact hU₂.subset_compl hyU₂ (hK hyK₁)
  have hxK₁c : x ∈ K₁ᶜ := hU₂_subset_K₁c hxU₂
  let C : Set X := connectedComponentIn K₁ᶜ x
  have hC_component : IsComponentOf C K₁ᶜ := by
    dsimp [C]
    exact isComponentOf_connectedComponentIn hxK₁c
  have hU₂_subset_C : U₂ ⊆ C := by
    dsimp [C]
    exact hU₂.isComponentOf.isPreconnected.subset_connectedComponentIn
      hxU₂ hU₂_subset_K₁c
  have hC_ext : IsExteriorComponent K₁ C := by
    refine hC_component.isExteriorComponent_of_escapes ?_
    intro L hL
    rcases hU₂.exists_not_mem_compact hL with ⟨y, hyU₂, hyL⟩
    exact ⟨y, hU₂_subset_C hyU₂, hyL⟩
  have hC_eq : C = U₁ := hunique₁ C hC_ext
  intro y hyU₂
  exact hC_eq ▸ hU₂_subset_C hyU₂

/--
%%handwave
name:
  A nested exterior component after enlarging a compact obstacle
statement:
  Let \(K_1\subseteq K_2\), with \(K_2\) compact, in a Hausdorff locally
  connected space.  If \(U_1\) is an exterior component of \(X\setminus K_1\)
  and \(X\setminus K_2\) has only finitely many components, then some exterior
  component \(U_2\) of \(X\setminus K_2\) satisfies \(U_2\subseteq U_1\).
proof:
  Suppose every component of \(X\setminus K_2\) contained in \(U_1\) were
  non-exterior.  Each such component then has compact closure, and there are
  only finitely many of them.  Their closures together with \(K_2\) form a
  compact set containing all of \(U_1\), contradicting that an exterior
  component escapes every compact set.
-/
theorem IsExteriorComponent.exists_nested_of_subset_left_of_finite_components
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K₁ K₂ U₁ : Set X} (hK : K₁ ⊆ K₂)
    (hK₂compact : IsCompact K₂)
    (hU₁ : IsExteriorComponent K₁ U₁)
    (hfinite : {V : Set X | IsComponentOf V K₂ᶜ}.Finite) :
    ∃ U₂ : Set X, IsExteriorComponent K₂ U₂ ∧ U₂ ⊆ U₁ := by
  classical
  let components : Set (Set X) :=
    {V : Set X | IsComponentOf V K₂ᶜ}
  let children : Finset (Set X) :=
    hfinite.toFinset.filter (fun V : Set X => V ⊆ U₁)
  by_contra hnone
  have hchildren_nonExterior :
      ∀ V ∈ children, ¬ IsExteriorComponent K₂ V := by
    intro V hVchildren hVexterior
    apply hnone
    exact ⟨V, hVexterior, (Finset.mem_filter.mp hVchildren).2⟩
  let B : Set X := ⋃ V ∈ children, closure V
  have hBcompact : IsCompact B := by
    dsimp [B]
    refine children.isCompact_biUnion ?_
    intro V hVchildren
    have hVcomponent : IsComponentOf V K₂ᶜ := by
      have hVfin : V ∈ hfinite.toFinset :=
        (Finset.mem_filter.mp hVchildren).1
      exact hfinite.mem_toFinset.mp hVfin
    exact hVcomponent.closure_compact_of_not_isExteriorComponent
      hK₂compact (hchildren_nonExterior V hVchildren)
  let L : Set X := K₂ ∪ B
  have hLcompact : IsCompact L := hK₂compact.union hBcompact
  have hU₁L : U₁ ⊆ L := by
    intro x hxU₁
    by_cases hxK₂ : x ∈ K₂
    · exact Or.inl hxK₂
    · have hxK₂c : x ∈ K₂ᶜ := hxK₂
      let C : Set X := connectedComponentIn K₂ᶜ x
      have hCcomponent : IsComponentOf C K₂ᶜ :=
        isComponentOf_connectedComponentIn hxK₂c
      have hCsubsetK₁c : C ⊆ K₁ᶜ := by
        intro y hyC hyK₁
        exact hCcomponent.subset hyC (hK hyK₁)
      have hCsubsetU₁ : C ⊆ U₁ := by
        have hCsubsetComponent :
            C ⊆ connectedComponentIn K₁ᶜ x :=
          hCcomponent.isPreconnected.subset_connectedComponentIn
            (mem_connectedComponentIn hxK₂c) hCsubsetK₁c
        rw [← hU₁.eq_connectedComponentIn_of_mem hxU₁] at hCsubsetComponent
        exact hCsubsetComponent
      have hCchildren : C ∈ children := by
        apply Finset.mem_filter.mpr
        exact ⟨hfinite.mem_toFinset.mpr hCcomponent, hCsubsetU₁⟩
      refine Or.inr ?_
      exact Set.mem_iUnion_of_mem C
        (Set.mem_iUnion_of_mem hCchildren
          (subset_closure (mem_connectedComponentIn hxK₂c)))
  exact hU₁.not_subset_compact hLcompact hU₁L

/--
%%handwave
name:
  Filled sides grow as exterior components shrink
statement:
  If one exterior component is contained in another, then the filled side of
  the larger exterior component is contained in the filled side of the smaller
  one.
proof:
  Taking complements reverses inclusions, and taking interiors preserves them.
-/
theorem filledSideOfExteriorComponent_mono_of_subset
    {X : Type} [TopologicalSpace X] {U₁ U₂ : Set X}
    (hU : U₂ ⊆ U₁) :
    filledSideOfExteriorComponent U₁ ⊆
      filledSideOfExteriorComponent U₂ :=
  interior_mono (compl_subset_compl.mpr hU)

/--
%%handwave
name:
  Filled sides grow with the compact obstacle
statement:
  If \(K_1\subset K_2\), \(U_i\) is an exterior component of
  \(X\setminus K_i\), and \(U_1\) is the unique exterior component for
  \(K_1\), then the filled side for \(U_1\) is contained in the filled side
  for \(U_2\).
proof:
  The exterior component for the larger obstacle lies inside the exterior
  component for the smaller obstacle, so the filled sides are ordered in the
  opposite direction.
-/
theorem IsExteriorComponent.filledSide_subset_of_subset_left_of_unique
    {X : Type} [TopologicalSpace X]
    {K₁ K₂ U₁ U₂ : Set X} (hK : K₁ ⊆ K₂)
    (hU₁ : IsExteriorComponent K₁ U₁)
    (hU₂ : IsExteriorComponent K₂ U₂)
    (hunique₁ :
      ∀ V : Set X, IsExteriorComponent K₁ V → V = U₁) :
    filledSideOfExteriorComponent U₁ ⊆
      filledSideOfExteriorComponent U₂ :=
  filledSideOfExteriorComponent_mono_of_subset
    (hU₁.subset_of_subset_left_of_unique hK hU₂ hunique₁)

/--
%%handwave
name:
  Pointed simply connected smooth exhaustion
statement:
  A pointed simply connected smooth exhaustion is a smooth relatively compact
  exhaustion whose members all contain the base point and are simply connected.
-/
structure PointedSimplyConnectedSmoothRelativelyCompactExhaustion
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (p : X) where
  /-- The underlying smooth relatively compact exhaustion. -/
  toSmoothRelativelyCompactExhaustion : SmoothRelativelyCompactExhaustion X
  /-- Every member contains the base point. -/
  base_mem :
    ∀ n : ℕ, p ∈ (toSmoothRelativelyCompactExhaustion.domain n).carrier
  /-- Every member is simply connected. -/
  simplyConnected :
    ∀ n : ℕ,
      SimplyConnectedSpace
        (toSmoothRelativelyCompactExhaustion.domain n).carrier

namespace PointedSimplyConnectedSmoothRelativelyCompactExhaustion

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}

/-- The domain at index \(n\). -/
def domain
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) : SmoothBoundaryDomain X :=
  E.toSmoothRelativelyCompactExhaustion.domain n

/--
%%handwave
name:
  Pointed exhaustion domains are open
statement:
  Every domain in a pointed smooth simply connected exhaustion is open.
proof:
  Each member is a smooth boundary domain, whose carrier is open by definition.
-/
theorem domain_isOpen
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    IsOpen (E.domain n).carrier :=
  (E.domain n).isOpen

/--
%%handwave
name:
  Pointed exhaustion domains are nonempty
statement:
  Every domain in a pointed smooth simply connected exhaustion is nonempty.
proof:
  Nonemptiness is part of the smooth boundary domain data.
-/
theorem domain_nonempty
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    (E.domain n).carrier.Nonempty :=
  (E.domain n).nonempty

/--
%%handwave
name:
  Pointed exhaustion domains have compact closure
statement:
  Every domain in a pointed smooth simply connected exhaustion has compact
  closure.
proof:
  Compactness of the closure is part of the smooth relatively compact
  exhaustion data.
-/
theorem domain_compact_closure
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    IsCompact (closure (E.domain n).carrier) :=
  (E.domain n).compact_closure

/--
%%handwave
name:
  Pointed exhaustion domains have smooth boundary
statement:
  Every domain in a pointed smooth simply connected exhaustion has smooth
  boundary.
proof:
  Each exhaustion member is, by construction, a smooth boundary domain.
-/
theorem domain_smooth_boundary
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    HasSmoothBoundary (E.domain n).carrier :=
  (E.domain n).smooth_boundary

/--
%%handwave
name:
  Pointed exhaustion domains contain the base point
statement:
  Every domain in a pointed smooth simply connected exhaustion contains the
  base point.
proof:
  Containment of the base point in every member is part of the pointed
  exhaustion data.
-/
theorem domain_base_mem
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    p ∈ (E.domain n).carrier :=
  E.base_mem n

/--
%%handwave
name:
  Pointed exhaustion domains are simply connected
statement:
  Every domain in a pointed smooth simply connected exhaustion is simply
  connected.
proof:
  Simple connectedness of every member is part of the defining exhaustion
  data.
-/
theorem domain_simplyConnected
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    SimplyConnectedSpace (E.domain n).carrier :=
  E.simplyConnected n

/--
%%handwave
name:
  Pointed exhaustion domains are monotone
statement:
  The domains of a pointed smooth simply connected exhaustion are monotone.
proof:
  Iterate the one-step inclusions of the underlying smooth exhaustion from the
  earlier index to the later one.
-/
theorem domain_carrier_mono
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    {m n : ℕ} (hmn : m ≤ n) :
    (E.domain m).carrier ⊆ (E.domain n).carrier := by
  refine Nat.le_induction ?base ?step n hmn
  · exact subset_rfl
  · intro k _hmk ih
    exact ih.trans (E.toSmoothRelativelyCompactExhaustion.monotone k)

/--
%%handwave
name:
  Pointed exhaustion closures enter the next domain
statement:
  The closure of each domain in a pointed smooth simply connected exhaustion
  lies in the next domain.
proof:
  This is the successive compact-containment condition of the underlying
  smooth exhaustion.
-/
theorem domain_closure_subset_next
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    closure (E.domain n).carrier ⊆ (E.domain (n + 1)).carrier :=
  E.toSmoothRelativelyCompactExhaustion.closure_subset_next n

/--
%%handwave
name:
  Pointed exhaustion closures enter later domains
statement:
  If \(m<n\), then the closure of the \(m\)-th domain lies in the \(n\)-th
  domain.
proof:
  The closure of the \(m\)-th domain lies in the next domain, and monotonicity
  carries it through all later domains.
-/
theorem domain_closure_subset_of_lt
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    {m n : ℕ} (hmn : m < n) :
    closure (E.domain m).carrier ⊆ (E.domain n).carrier :=
  (E.domain_closure_subset_next m).trans
    (E.domain_carrier_mono (Nat.succ_le_iff.mpr hmn))

/--
%%handwave
name:
  Pointed exhaustions exhaust the surface
statement:
  Every point lies in some domain of a pointed smooth simply connected
  exhaustion.
proof:
  The underlying smooth exhaustion covers the entire surface.
-/
theorem domain_exhausts
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (x : X) :
    ∃ n : ℕ, x ∈ (E.domain n).carrier :=
  E.toSmoothRelativelyCompactExhaustion.exhausts x

/--
%%handwave
name:
  Points eventually lie in pointed exhaustion domains
statement:
  Every point lies in all sufficiently late domains of a pointed smooth simply
  connected exhaustion.
proof:
  Choose one domain containing the point.  Monotonicity places the point in
  every member with a larger index.
-/
theorem domain_eventually_mem
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    (x : X) :
    ∀ᶠ n : ℕ in Filter.atTop, x ∈ (E.domain n).carrier := by
  rcases E.domain_exhausts x with ⟨N, hxN⟩
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact E.domain_carrier_mono hn hxN

/--
%%handwave
name:
  Pointed exhaustion domains cover the surface
statement:
  The union of the domains of a pointed smooth simply connected exhaustion is
  the whole surface.
proof:
  Every domain is contained in the surface, while the exhaustion property puts
  every surface point in at least one domain.
-/
theorem iUnion_domain_carrier_eq_univ
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p) :
    (⋃ n : ℕ, (E.domain n).carrier) = (univ : Set X) := by
  ext x
  constructor
  · intro _hx
    exact mem_univ x
  · intro _hx
    exact mem_iUnion.mpr (E.domain_exhausts x)

end PointedSimplyConnectedSmoothRelativelyCompactExhaustion

namespace SmoothBoundaryDomain

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]

/--
%%handwave
name:
  First real de Rham cohomology of a smooth boundary domain
statement:
  The first real de Rham cohomology of a smooth boundary domain is the degree
  one de Rham cohomology of the corresponding open submanifold.
-/
abbrev deRhamH1 (D : SmoothBoundaryDomain X) : Type _ :=
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  let U : TopologicalSpace.Opens X := ⟨D.carrier, D.isOpen⟩
  Manifold.DeRhamCohomology (I := SurfaceRealModel) (M := U) (A := ℝ) 1

/--
%%handwave
name:
  Vanishing first real de Rham cohomology
statement:
  A smooth boundary domain has vanishing first real de Rham cohomology when
  its degree one de Rham cohomology group is trivial.
-/
abbrev deRhamH1Zero (D : SmoothBoundaryDomain X) : Prop :=
  Subsingleton D.deRhamH1

end SmoothBoundaryDomain

/--
%%handwave
name:
  Pointed H-one-zero smooth exhaustion
statement:
  A pointed H-one-zero smooth exhaustion is a smooth relatively compact
  exhaustion whose members all contain the base point and have vanishing first
  real de Rham cohomology.
-/
structure PointedH1ZeroSmoothRelativelyCompactExhaustion
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (p : X) where
  /-- The underlying smooth relatively compact exhaustion. -/
  toSmoothRelativelyCompactExhaustion : SmoothRelativelyCompactExhaustion X
  /-- Every member contains the base point. -/
  base_mem :
    ∀ n : ℕ, p ∈ (toSmoothRelativelyCompactExhaustion.domain n).carrier
  /-- Every member is path connected. -/
  pathConnected :
    ∀ n : ℕ,
      PathConnectedSpace
        (toSmoothRelativelyCompactExhaustion.domain n).carrier
  /-- Every member has vanishing first real de Rham cohomology. -/
  deRhamH1Zero :
    ∀ n : ℕ,
      (toSmoothRelativelyCompactExhaustion.domain n).deRhamH1Zero

namespace PointedH1ZeroSmoothRelativelyCompactExhaustion

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {p : X}

/-- The domain at index \(n\). -/
def domain
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) : SmoothBoundaryDomain X :=
  E.toSmoothRelativelyCompactExhaustion.domain n

/--
%%handwave
name:
  Pointed H-one-zero exhaustion domains contain the base point
statement:
  Every domain in a pointed H-one-zero smooth exhaustion contains the base
  point.
proof:
  Containment of the base point in every member is part of the pointed
  exhaustion data.
-/
theorem domain_base_mem
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    p ∈ (E.domain n).carrier :=
  E.base_mem n

/--
%%handwave
name:
  Pointed H-one-zero exhaustion domains are path connected
statement:
  Every domain in a pointed smooth exhaustion with vanishing first real de
  Rham cohomology is path connected.
proof:
  Path connectedness is part of the pointed exhaustion data.  In the
  bounded-filling construction it follows because one starts with the
  component containing the base point and fills complementary components.
-/
theorem domain_pathConnected
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    PathConnectedSpace (E.domain n).carrier :=
  E.pathConnected n

/--
%%handwave
name:
  Pointed exhaustion domains have vanishing first cohomology
statement:
  Every domain in a pointed H-one-zero smooth exhaustion has vanishing first
  real de Rham cohomology.
proof:
  Vanishing of first de Rham cohomology for each member is part of the defining
  exhaustion data.
-/
theorem domain_deRhamH1Zero
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    (n : ℕ) :
    (E.domain n).deRhamH1Zero :=
  E.deRhamH1Zero n

/--
%%handwave
name:
  Monotonicity of pointed cohomologically trivial exhaustion domains
statement:
  For a pointed smooth exhaustion by domains with vanishing first real de
  Rham cohomology, if \(m\le n\), then the \(m\)-th domain is contained in the
  \(n\)-th domain.
proof:
  Induct from \(m\) to \(n\), composing the one-step inclusions supplied by
  the underlying smooth exhaustion.
-/
theorem domain_carrier_mono
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    {m n : ℕ} (hmn : m ≤ n) :
    (E.domain m).carrier ⊆ (E.domain n).carrier := by
  refine Nat.le_induction ?_ ?_ n hmn
  · exact subset_rfl
  · intro k _hmk ih
    exact ih.trans (E.toSmoothRelativelyCompactExhaustion.monotone k)

/--
%%handwave
name:
  Pointed H-one-zero exhaustions exhaust the surface
statement:
  Every point of the surface lies in some domain of a pointed H-one-zero
  smooth exhaustion.
proof:
  The underlying smooth relatively compact exhaustion covers the surface.
-/
theorem domain_exhausts
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    (x : X) :
    ∃ n : ℕ, x ∈ (E.domain n).carrier :=
  E.toSmoothRelativelyCompactExhaustion.exhausts x

/--
%%handwave
name:
  Pointed H-one-zero exhaustion domains cover the surface
statement:
  The union of the domains of a pointed H-one-zero smooth exhaustion is the
  whole surface.
proof:
  Every surface point lies in some exhaustion member, and every member is a
  subset of the surface.
-/
theorem iUnion_domain_carrier_eq_univ
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p) :
    (⋃ n : ℕ, (E.domain n).carrier) = (univ : Set X) := by
  ext x
  constructor
  · intro _hx
    exact mem_univ x
  · intro _hx
    exact mem_iUnion.mpr (E.domain_exhausts x)

end PointedH1ZeroSmoothRelativelyCompactExhaustion

/--
%%handwave
name:
  Exterior criterion along a compact exhaustion
statement:
  A complementary component is exterior exactly when it is not contained in
  any member of a compact exhaustion.
proof:
  If the component were contained in one compact exhaustion member, it would
  fail to escape that compact set.  Conversely, every compact subset is
  contained in some member of the compact exhaustion.
-/
theorem IsComponentOf.isExteriorComponent_iff_not_subset_compactExhaustion
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsComponentOf U Kᶜ) (E : CompactExhaustion X) :
    IsExteriorComponent K U ↔
      ∀ n : ℕ, ¬ U ⊆ E n := by
  constructor
  · intro hExt n hUn
    exact hExt.not_subset_compact (E.isCompact n) hUn
  · intro hnot
    refine hU.isExteriorComponent_iff_not_subset_compact.mpr ?_
    intro L hL hUL
    rcases E.exists_superset_of_isCompact hL with ⟨n, hLn⟩
    exact hnot n (hUL.trans hLn)

/--
%%handwave
name:
  Recurrently far components are exterior
statement:
  If the same complementary component is not contained in arbitrarily late
  compact-exhaustion stages, then it is exterior.
proof:
  Were it contained in one exhaustion member, monotonicity would keep it
  contained in every later member, contradicting recurrent escape.
-/
theorem IsComponentOf.isExteriorComponent_of_frequently_not_subset_compactExhaustion
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsComponentOf U Kᶜ) (E : CompactExhaustion X)
    (hfreq : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ¬ U ⊆ E m) :
    IsExteriorComponent K U := by
  refine (hU.isExteriorComponent_iff_not_subset_compactExhaustion E).mpr ?_
  intro n hUn
  rcases hfreq n with ⟨m, hnm, hm⟩
  exact hm (hUn.trans (E.subset hnm))

/--
%%handwave
name:
  Exterior components leave every compact-exhaustion member
statement:
  An exterior component has a point outside each member of any compact
  exhaustion.
proof:
  Each member of a compact exhaustion is compact, so the escaping property
  gives a point of the exterior component outside it.
-/
theorem IsExteriorComponent.exists_not_mem_compactExhaustion
    {X : Type} [TopologicalSpace X] {K U : Set X}
    (hU : IsExteriorComponent K U) (E : CompactExhaustion X) (n : ℕ) :
    ∃ x ∈ U, x ∉ E n :=
  hU.exists_not_mem_compact (E.isCompact n)

/--
%%handwave
name:
  Finitely many non-exterior holes are trapped in a compact exhaustion
statement:
  If \(U\) is the unique exterior component of \(X\setminus K\) and
  \(X\setminus K\) has only finitely many components, then along any compact
  exhaustion there is one exhaustion member containing the closures of all
  complementary components different from \(U\).
proof:
  Each component different from the unique exterior component is non-exterior,
  hence has compact closure.  A compact exhaustion captures each of these
  finitely many compact closures, and taking the maximum of the corresponding
  indices captures them all.
-/
theorem IsExteriorComponent.nonExterior_component_closures_subset_compactExhaustion_of_finite_components
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {K U : Set X} (_hU : IsExteriorComponent K U)
    (E : CompactExhaustion X) (hK : IsCompact K)
    (hunique : ∀ V : Set X, IsExteriorComponent K V → V = U)
    (hfinite : {V : Set X | IsComponentOf V Kᶜ}.Finite) :
    ∃ N : ℕ, ∀ V : Set X, IsComponentOf V Kᶜ → V ≠ U →
      closure V ⊆ E N := by
  classical
  let components : Set (Set X) := {V : Set X | IsComponentOf V Kᶜ}
  have hbounded :
      ∀ V : Set X, V ∈ components → V ≠ U →
        ∃ n : ℕ, closure V ⊆ E n := by
    intro V hV hV_ne
    have hVcomp : IsComponentOf V Kᶜ := hV
    exact E.exists_superset_of_isCompact
      (hVcomp.closure_compact_of_ne_unique_exterior hK hunique hV_ne)
  let nOf : {V : Set X // V ∈ components ∧ V ≠ U} → ℕ :=
    fun V ↦ Classical.choose (hbounded V.1 V.2.1 V.2.2)
  let N : ℕ :=
    hfinite.toFinset.sup
      (fun V ↦ if hV : V ∈ components ∧ V ≠ U then nOf ⟨V, hV⟩ else 0)
  refine ⟨N, ?_⟩
  intro V hVcomp hV_ne
  have hVmem_components : V ∈ components := hVcomp
  have hVmem : V ∈ hfinite.toFinset :=
    hfinite.mem_toFinset.mpr hVcomp
  have hle :
      (if hV : V ∈ components ∧ V ≠ U then nOf ⟨V, hV⟩ else 0) ≤ N :=
    Finset.le_sup (f := fun V ↦
      if hV : V ∈ components ∧ V ≠ U then nOf ⟨V, hV⟩ else 0) hVmem
  have hle_n :
      nOf ⟨V, hVmem_components, hV_ne⟩ ≤ N := by
    simpa [N, hVmem_components, hV_ne] using hle
  have hclosure :
      closure V ⊆ E (nOf ⟨V, hVmem_components, hV_ne⟩) :=
    Classical.choose_spec (hbounded V hVmem_components hV_ne)
  exact hclosure.trans (E.subset hle_n)

/--
%%handwave
name:
  Finite stage-escaping components force an exterior component
statement:
  Suppose \(X\setminus K\) has only finitely many components.  If, at every
  sufficiently late compact-exhaustion stage, some complementary component is
  not contained in that stage, then one complementary component is exterior.
proof:
  If no component were exterior, then every component would be contained in
  some exhaustion member.  Finiteness lets one take a single later member
  containing all components, contradicting the existence of a component
  escaping that member.
-/
theorem finite_complement_components_exteriorComponent_exists_of_compactExhaustion_stage_escape
    {X : Type} [TopologicalSpace X] (E : CompactExhaustion X)
    {K : Set X}
    (hfinite : {U : Set X | IsComponentOf U Kᶜ}.Finite)
    (hstage :
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∃ U : Set X, IsComponentOf U Kᶜ ∧ ¬ U ⊆ E n) :
    ∃ U : Set X, IsExteriorComponent K U := by
  classical
  by_contra hno
  let components : Set (Set X) := {U : Set X | IsComponentOf U Kᶜ}
  have hbounded :
      ∀ U : Set X, U ∈ components →
        ∃ n : ℕ, U ⊆ E n := by
    intro U hU
    have hUcomp : IsComponentOf U Kᶜ := hU
    have hnotExt : ¬ IsExteriorComponent K U := by
      intro hExt
      exact hno ⟨U, hExt⟩
    by_contra hnone
    apply hnotExt
    exact (hUcomp.isExteriorComponent_iff_not_subset_compactExhaustion E).mpr
      (by
        intro n hUn
        exact hnone ⟨n, hUn⟩)
  let nOf : components → ℕ :=
    fun U ↦ Classical.choose (hbounded U.1 U.2)
  let Ncomponents : ℕ :=
    hfinite.toFinset.sup
      (fun U ↦ if hU : U ∈ components then nOf ⟨U, hU⟩ else 0)
  have hle_component :
      ∀ {U : Set X} (hU : U ∈ components),
        nOf ⟨U, hU⟩ ≤ Ncomponents := by
    intro U hU
    have hmem : U ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr hU
    have hle :
        (if hU' : U ∈ components then nOf ⟨U, hU'⟩ else 0) ≤
          Ncomponents :=
      Finset.le_sup (f := fun U ↦
        if hU : U ∈ components then nOf ⟨U, hU⟩ else 0) hmem
    simpa [Ncomponents, hU] using hle
  have hcomponent_subset :
      ∀ {U : Set X} (hU : U ∈ components),
        U ⊆ E (nOf ⟨U, hU⟩) := by
    intro U hU
    exact Classical.choose_spec (hbounded U hU)
  rcases hstage with ⟨N₀, hstage⟩
  let N : ℕ := max N₀ Ncomponents
  rcases hstage N (le_max_left N₀ Ncomponents) with
    ⟨U, hUcomp, hUnot⟩
  have hUmem : U ∈ components := hUcomp
  have hU_subset : U ⊆ E N := by
    exact (hcomponent_subset hUmem).trans
      (E.subset ((hle_component hUmem).trans
        (le_max_right N₀ Ncomponents)))
  exact hUnot hU_subset

/--
%%handwave
name:
  Finite complementary components force an exterior component
statement:
  If a compact complement has only finitely many components in a noncompact
  space with a compact exhaustion, then one of those components is exterior.
proof:
  If no component were exterior, each component would lie in some compact
  exhaustion member.  Finiteness gives a single member containing all
  complementary components, while compactness puts the compact set itself in
  another member.  A later member would then contain the whole space,
  contradicting noncompactness.
-/
theorem finite_complement_components_exteriorComponent_exists_of_compactExhaustion
    {X : Type} [TopologicalSpace X]
    (hnoncompact : ¬ CompactSpace X) (E : CompactExhaustion X)
    {K : Set X} (hK : IsCompact K)
    (hfinite : {U : Set X | IsComponentOf U Kᶜ}.Finite) :
    ∃ U : Set X, IsExteriorComponent K U := by
  exact
    finite_complement_components_exteriorComponent_exists_of_compactExhaustion_stage_escape
      E hfinite
      (compactExhaustion_complement_has_component_not_subset_eventually
        hnoncompact E hK)

/--
%%handwave
name:
  The pointed component contains the point
statement:
  If \(p\) lies in a smooth domain \(D\), then \(p\) lies in the component of
  \(D\) that contains \(p\).
proof:
  The constant path at \(p\) lies in \(D\), so \(p\) belongs to its connected
  component relative to \(D\).
-/
theorem smoothBoundaryDomain_pointedComponent_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    p ∈ connectedComponentIn D.carrier p :=
  mem_connectedComponentIn hp

/--
%%handwave
name:
  The pointed component is a component
statement:
  If \(p\in D\), then the component of \(D\) containing \(p\) is a component
  of \(D\).
proof:
  A connected component relative to a set, based at a point of that set, is
  by definition a maximal connected subset of the set.
-/
theorem smoothBoundaryDomain_pointedComponent_isComponentOf
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    IsComponentOf (connectedComponentIn D.carrier p) D.carrier :=
  isComponentOf_connectedComponentIn hp

/--
%%handwave
name:
  The pointed component has compact closure
statement:
  The closure of the component of a smooth relatively compact domain is
  compact.
proof:
  The component is contained in the domain, so its closure is contained in the
  compact closure of the domain.
-/
theorem smoothBoundaryDomain_pointedComponent_closure_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) (p : X) :
    IsCompact (closure (connectedComponentIn D.carrier p)) := by
  exact D.compact_closure.of_isClosed_subset isClosed_closure
    (closure_mono (connectedComponentIn_subset D.carrier p))

/--
%%handwave
name:
  The closed pointed component is connected
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  Then \(\overline C\) is connected.
proof:
  The component \(C\) is connected, and the closure of a connected set is
  connected.
-/
theorem smoothBoundaryDomain_pointedComponent_closure_isConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    IsConnected (closure (connectedComponentIn D.carrier p)) :=
  (smoothBoundaryDomain_pointedComponent_isComponentOf D hp).closure_isConnected

/--
%%handwave
name:
  The boundary of a smooth domain is compact
statement:
  The frontier of a smooth relatively compact domain is compact.
proof:
  The frontier is closed and is contained in the compact closure of the
  domain.
-/
theorem smoothBoundaryDomain_frontier_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) :
    IsCompact (frontier D.carrier) :=
  D.compact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure

/--
%%handwave
name:
  The pointed-component frontier is compact
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  Then the frontier of \(C\) is compact.
proof:
  The frontier of \(C\) lies in the frontier of \(D\), and the latter is
  compact.
-/
theorem smoothBoundaryDomain_pointedComponent_frontier_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    IsCompact (frontier (connectedComponentIn D.carrier p)) := by
  have hcomponent :
      IsComponentOf (connectedComponentIn D.carrier p) D.carrier :=
    smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  exact (smoothBoundaryDomain_frontier_compact D).of_isClosed_subset
    isClosed_frontier
    (hcomponent.frontier_subset_frontier_of_isOpen D.isOpen)

/--
%%handwave
name:
  The closed pointed-component boundary is compact
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  Then the frontier of \(\overline C\)
  is compact.
proof:
  The set \(\overline C\) is compact and closed, and its frontier is a closed
  subset of it.
-/
theorem smoothBoundaryDomain_pointedComponent_closure_frontier_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) (p : X) :
    IsCompact (frontier (closure (connectedComponentIn D.carrier p))) := by
  have hK :
      IsCompact (closure (connectedComponentIn D.carrier p)) :=
    smoothBoundaryDomain_pointedComponent_closure_compact D p
  have hfrontier_subset :
      frontier (closure (connectedComponentIn D.carrier p)) ⊆
        closure (connectedComponentIn D.carrier p) := by
    simpa [isClosed_closure.closure_eq] using
      (frontier_subset_closure
        (s := closure (connectedComponentIn D.carrier p)))
  exact hK.of_isClosed_subset isClosed_frontier hfrontier_subset

/--
%%handwave
name:
  The closed pointed-component boundary lies on the original boundary
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  Then the frontier of \(\overline C\)
  is contained in the frontier of \(D\).
proof:
  The frontier of \(\overline C\) is contained in the frontier of \(C\), and
  component frontiers of open sets lie on the frontier of the ambient open
  set.
-/
theorem smoothBoundaryDomain_pointedComponent_closure_frontier_subset_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    frontier (closure (connectedComponentIn D.carrier p)) ⊆
      frontier D.carrier := by
  have hcomponent :
      IsComponentOf (connectedComponentIn D.carrier p) D.carrier :=
    smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  exact (frontier_closure_subset
      (s := connectedComponentIn D.carrier p)).trans
    (hcomponent.frontier_subset_frontier_of_isOpen D.isOpen)

/--
%%handwave
name:
  A nonzero real differential is onto the line
statement:
  A nonzero real linear functional on the complex plane has full range in the
  real line.
proof:
  Choose a vector on which the functional is nonzero and rescale it to hit any
  prescribed real number.
-/
theorem complexRealLinearFunctional_range_eq_top_of_nonzero
    (dr : ℂ →L[ℝ] ℝ) (hdr_nonzero : dr ≠ 0) :
    dr.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  have hz_exists : ∃ z : ℂ, dr z ≠ 0 := by
    by_contra h
    apply hdr_nonzero
    ext z
    exact not_not.mp (not_exists.mp h z)
  rcases hz_exists with ⟨z, hz⟩
  intro y
  refine ⟨(y / dr z : ℝ) • z, ?_⟩
  calc
    dr ((y / dr z : ℝ) • z) = (y / dr z : ℝ) • dr z := by
      exact map_smul dr (y / dr z : ℝ) z
    _ = (y / dr z) * dr z := by
      simp
    _ = y := by
      field_simp [hz]

/--
%%handwave
name:
  A vertical line is homeomorphic to its transverse coordinate
statement:
  For any topological space \(E\) and real number \(a\), the vertical line
  \(\{(a,t):t\in E\}\subset \mathbb R\times E\) is homeomorphic to \(E\).
proof:
  The homeomorphism sends \(t\) to \((a,t)\), with inverse given by
  projection to the second coordinate.
-/
def verticalLineHomeomorph (E : Type*) [TopologicalSpace E] (a : ℝ) :
    E ≃ₜ {p : ℝ × E | p.1 = a} where
  toFun t := ⟨(a, t), rfl⟩
  invFun p := p.1.2
  left_inv t := rfl
  right_inv p := by
    cases p with
    | mk q hq =>
      cases q with
      | mk x y =>
        simp at hq ⊢
        exact hq.symm
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/--
%%handwave
name:
  Vertical lines are locally path connected
statement:
  If \(E\) is locally path connected, then every vertical line in
  \(\mathbb R\times E\) is locally path connected.
proof:
  Use the homeomorphism from \(E\) to the vertical line.
-/
theorem verticalLine_locPathConnectedSpace
    (E : Type*) [TopologicalSpace E] [LocPathConnectedSpace E] (a : ℝ) :
    LocPathConnectedSpace {p : ℝ × E | p.1 = a} := by
  exact (verticalLineHomeomorph E a).symm.isOpenEmbedding.locPathConnectedSpace

/--
%%handwave
name:
  Regular plane levels are vertical lines in implicit coordinates
statement:
  Let \(r\) be a smooth real-valued function on the complex plane, and suppose
  that \(dr\ne0\) is its differential at \(z_0\).  Then the implicit-function
  coordinates near \(z_0\) send the level \(r=r(z_0)\) to a vertical line.
proof:
  Mathlib's implicit-function theorem gives local coordinates whose first
  coordinate is \(r\).  Therefore the level set is exactly the inverse image
  of the vertical line with first coordinate \(r(z_0)\).
-/
theorem smoothPlaneRegularLevel_implicitCoord_isImage_level
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph ℂ (ℝ × dr.ker),
      z₀ ∈ Φ.source ∧
        Φ.IsImage {z : ℂ | r z = r z₀}
          {p : ℝ × dr.ker | p.1 = r z₀} := by
  have hr_strict : HasStrictFDerivAt r dr z₀ :=
    hr_smooth.hasStrictFDerivAt' hr_deriv (by simp)
  have hdr_range : dr.range = ⊤ :=
    complexRealLinearFunctional_range_eq_top_of_nonzero dr hdr_nonzero
  let Φ : OpenPartialHomeomorph ℂ (ℝ × dr.ker) :=
    hr_strict.implicitToOpenPartialHomeomorph r dr hdr_range
  refine ⟨Φ, ?_, ?_⟩
  · exact hr_strict.mem_implicitToOpenPartialHomeomorph_source hdr_range
  · intro z _hz_source
    have hfst : (Φ z).1 = r z := by
      simp [Φ, hr_strict.implicitToOpenPartialHomeomorph_fst hdr_range z]
    simp [hfst]

/--
%%handwave
name:
  Regular plane zero sets are vertical lines in implicit coordinates
statement:
  Let \(r\) be a smooth real-valued function on the complex plane, let
  \(r(z_0)=0\), and suppose that \(dr\ne0\) is its differential at \(z_0\).
  Then the implicit-function coordinates near \(z_0\) send the zero set of
  \(r\) to the vertical line with first coordinate zero.
proof:
  This is the preceding level-set statement applied to the zero level.
-/
theorem smoothPlaneRegularZeroSet_implicitCoord_isImage_zero
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0)
    (hr_zero : r z₀ = 0) :
    ∃ Φ : OpenPartialHomeomorph ℂ (ℝ × dr.ker),
      z₀ ∈ Φ.source ∧
        Φ.IsImage {z : ℂ | r z = 0}
          {p : ℝ × dr.ker | p.1 = 0} := by
  simpa [hr_zero] using
    smoothPlaneRegularLevel_implicitCoord_isImage_level
      hr_smooth hr_deriv hdr_nonzero

/--
%%handwave
name:
  Regular plane zero-set coordinates remember the defining function
statement:
  Let \(r\) be a smooth real-valued function on the complex plane, let
  \(r(z_0)=0\), and suppose that \(dr\ne0\) is its differential at \(z_0\).
  Then the implicit-function coordinates near \(z_0\) have first coordinate
  equal to \(r\), and carry the zero set of \(r\) to the vertical line.
proof:
  Mathlib's implicit-function chart is built with \(r\) as its transverse
  coordinate.  The zero-set conclusion follows by reading off this first
  coordinate.
-/
theorem smoothPlaneRegularZeroSet_implicitCoord_fst_eq
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0)
    (_hr_zero : r z₀ = 0) :
    ∃ Φ : OpenPartialHomeomorph ℂ (ℝ × dr.ker),
      z₀ ∈ Φ.source ∧
        (∀ z ∈ Φ.source, (Φ z).1 = r z) ∧
          Φ.IsImage {z : ℂ | r z = 0}
            {p : ℝ × dr.ker | p.1 = 0} := by
  have hr_strict : HasStrictFDerivAt r dr z₀ :=
    hr_smooth.hasStrictFDerivAt' hr_deriv (by simp)
  have hdr_range : dr.range = ⊤ :=
    complexRealLinearFunctional_range_eq_top_of_nonzero dr hdr_nonzero
  let Φ : OpenPartialHomeomorph ℂ (ℝ × dr.ker) :=
    hr_strict.implicitToOpenPartialHomeomorph r dr hdr_range
  refine ⟨Φ, ?_, ?_, ?_⟩
  · exact hr_strict.mem_implicitToOpenPartialHomeomorph_source hdr_range
  · intro z _hz
    simp [Φ, hr_strict.implicitToOpenPartialHomeomorph_fst hdr_range z]
  · intro z hz
    have hfst : (Φ z).1 = r z := by
      simp [Φ, hr_strict.implicitToOpenPartialHomeomorph_fst hdr_range z]
    simp [hfst]

/--
%%handwave
name:
  Regular plane zero-set neighborhoods map to line neighborhoods
statement:
  In the same situation, the implicit-function coordinates identify the
  neighborhood filter of \(z_0\) within the zero set of \(r\) with the
  neighborhood filter of the corresponding point within the vertical line.
proof:
  Apply the neighborhood-within mapping theorem for the local homeomorphism
  from the implicit-function theorem and the zero-set image statement.
-/
theorem smoothPlaneRegularZeroSet_implicitCoord_map_nhdsWithin_zero
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0)
    (hr_zero : r z₀ = 0) :
    ∃ Φ : OpenPartialHomeomorph ℂ (ℝ × dr.ker),
      z₀ ∈ Φ.source ∧
        Filter.map Φ (𝓝[{z : ℂ | r z = 0}] z₀) =
          𝓝[{p : ℝ × dr.ker | p.1 = 0}] Φ z₀ := by
  rcases smoothPlaneRegularZeroSet_implicitCoord_isImage_zero
      hr_smooth hr_deriv hdr_nonzero hr_zero with
    ⟨Φ, hz_source, hΦ⟩
  exact ⟨Φ, hz_source, hΦ.map_nhdsWithin_eq hz_source⟩

/--
%%handwave
name:
  Smooth frontiers have path-connected neighborhood bases
statement:
  Near every point of a smooth frontier, there is a basis of path-connected
  neighborhoods inside the frontier.
proof:
  In a smooth boundary chart, the frontier is the zero set of a submersion
  from the plane to the line.  The implicit function theorem gives local
  coordinates in which the frontier is an interval, and intervals have
  path-connected neighborhood bases.
-/
theorem hasSmoothBoundary_frontier_pathConnected_nhds_basis
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} (hU : HasSmoothBoundary U) :
    ∀ x : frontier U,
      (𝓝 x).HasBasis
        (fun s : Set (frontier U) => s ∈ 𝓝 x ∧ IsPathConnected s) id := by
  haveI : LocPathConnectedSpace (frontier U) := by
    refine locPathConnectedSpace_of_openCover ?_
    intro x
    rcases x with ⟨x, hxfront⟩
    rcases hU x hxfront with
      ⟨e, _he, hxsource, r, hrsmooth, dr, hrderiv, hdrnz, hlocal⟩
    rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, hxN⟩
    have hprops_x := hNsub hxN
    have hxzero : r (e x) = 0 := (hprops_x.2.2).mp hxfront
    rcases smoothPlaneRegularZeroSet_implicitCoord_isImage_zero
        hrsmooth.contDiffAt hrderiv hdrnz hxzero with
      ⟨Φ, hxΦ, hΦ⟩
    let eN : OpenPartialHomeomorph X ℂ := e.restrOpen N hNopen
    let E : OpenPartialHomeomorph X (ℝ × dr.ker) := eN.trans Φ
    let line : Set (ℝ × dr.ker) := {p | p.1 = (0 : ℝ)}
    let s : Set (frontier U) := {y | (y : X) ∈ E.source}
    refine ⟨s, ?_, ?_, ?_⟩
    · exact E.open_source.preimage continuous_subtype_val
    · have hxE : x ∈ E.source := by
        change x ∈ (eN.trans Φ).source
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨by simpa [eN] using ⟨hxsource, hxN⟩, by simpa [eN] using hxΦ⟩
      exact hxE
    · have hEimage : E.IsImage (frontier U) line := by
        intro y hy
        have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
          change y ∈ (eN.trans Φ).source at hy
          simpa [OpenPartialHomeomorph.trans_source] using hy
        have hy_eN_source : y ∈ e.source ∩ N := by
          simpa [eN] using hy'.1
        have hyN : y ∈ N := hy_eN_source.2
        have hyΦ : e y ∈ Φ.source := by
          simpa [eN] using hy'.2
        have hzero_iff : y ∈ frontier U ↔ r (e y) = 0 :=
          (hNsub hyN).2.2
        have hΦiff : Φ (e y) ∈ line ↔ r (e y) = 0 := by
          simpa [line] using (hΦ hyΦ)
        simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
          hΦiff.trans hzero_iff.symm
      have hline_lpc : LocPathConnectedSpace line := by
        exact verticalLine_locPathConnectedSpace dr.ker 0
      haveI : LocPathConnectedSpace line := hline_lpc
      have hopenLinePatch :
          IsOpen {p : line | (p : ℝ × dr.ker) ∈ E.target} := by
        exact E.open_target.preimage continuous_subtype_val
      have hlinePatch_lpc :
          LocPathConnectedSpace {p : line | (p : ℝ × dr.ker) ∈ E.target} := by
        exact hopenLinePatch.locPathConnectedSpace
      have htarget_lpc :
          LocPathConnectedSpace (E.target ∩ line : Set (ℝ × dr.ker)) := by
        haveI : LocPathConnectedSpace
            {p : line | (p : ℝ × dr.ker) ∈ E.target} :=
          hlinePatch_lpc
        exact
          (subtypePreimageHomeomorph line E.target).symm.isOpenEmbedding.locPathConnectedSpace
      have hA_lpc : LocPathConnectedSpace (E.source ∩ frontier U : Set X) := by
        let A : Set X := E.source ∩ frontier U
        let B : Set (ℝ × dr.ker) := E '' A
        have hA_subset : A ⊆ E.source := inter_subset_left
        have hB_eq : B = E.target ∩ line := by
          dsimp [B, A]
          exact hEimage.image_eq
        haveI : LocPathConnectedSpace (E.target ∩ line : Set (ℝ × dr.ker)) :=
          htarget_lpc
        have hB_lpc : LocPathConnectedSpace B := by
          exact (Homeomorph.setCongr hB_eq).isOpenEmbedding.locPathConnectedSpace
        haveI : LocPathConnectedSpace B := hB_lpc
        let hAB : A ≃ₜ B :=
          E.homeomorphOfImageSubsetSource (s := A) (t := B) hA_subset rfl
        exact
          hAB.isOpenEmbedding.locPathConnectedSpace
      haveI : LocPathConnectedSpace (E.source ∩ frontier U : Set X) := hA_lpc
      change LocPathConnectedSpace {y : frontier U | (y : X) ∈ E.source}
      exact
        (subtypePreimageHomeomorph (frontier U) E.source).isOpenEmbedding.locPathConnectedSpace
  exact path_connected_basis

/--
%%handwave
name:
  Smooth frontiers are locally path connected
statement:
  The frontier of a set with smooth boundary is locally path connected.
proof:
  In a smooth boundary chart, the frontier is the zero set of a submersion
  from the plane to the line.  The implicit function theorem identifies it
  locally with an interval.
-/
theorem hasSmoothBoundary_frontier_locPathConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} (hU : HasSmoothBoundary U) :
    LocPathConnectedSpace (frontier U) := by
  exact ⟨hasSmoothBoundary_frontier_pathConnected_nhds_basis hU⟩

/--
%%handwave
name:
  Smooth frontiers are locally connected
statement:
  The frontier of a set with smooth boundary is locally connected.
proof:
  Smooth frontiers are locally path connected, hence locally connected.
-/
theorem hasSmoothBoundary_frontier_locallyConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} (hU : HasSmoothBoundary U) :
    LocallyConnectedSpace (frontier U) := by
  haveI : LocPathConnectedSpace (frontier U) :=
    hasSmoothBoundary_frontier_locPathConnected hU
  exact locPathConnectedSpace_locallyConnectedSpace

/--
%%handwave
name:
  Smooth-domain frontiers are locally connected
statement:
  The frontier of a smooth boundary domain is locally connected.
proof:
  This is the local connectedness of smooth frontiers applied to the smooth
  boundary structure of the domain.
-/
theorem smoothBoundaryDomain_frontier_locallyConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) :
    LocallyConnectedSpace (frontier D.carrier) :=
  hasSmoothBoundary_frontier_locallyConnected D.smooth_boundary

/--
%%handwave
name:
  Smooth-domain frontiers have finitely many components
statement:
  The frontier of a smooth relatively compact domain has only finitely many
  connected components.
proof:
  The frontier is compact and locally connected.  A compact locally connected
  space has finitely many connected components.
-/
theorem smoothBoundaryDomain_frontier_finite_connectedComponents
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) :
    Finite (ConnectedComponents (frontier D.carrier)) := by
  letI : CompactSpace (frontier D.carrier) :=
    isCompact_iff_compactSpace.mp
      (smoothBoundaryDomain_frontier_compact D)
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    smoothBoundaryDomain_frontier_locallyConnected D
  infer_instance

/--
%%handwave
name:
  The pointed component is open
statement:
  In a locally connected surface, the component of a smooth domain containing
  a point is open.
proof:
  Components of open sets are open in locally connected spaces.
-/
theorem smoothBoundaryDomain_pointedComponent_isOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) (p : X) :
    IsOpen (connectedComponentIn D.carrier p) :=
  D.isOpen.connectedComponentIn

/--
%%handwave
name:
  The pointed component is path connected
statement:
  On a Riemann surface, the component of a smooth domain containing a chosen
  interior point is path connected.
proof:
  It is a component of an open set.  Components of open sets are path
  connected in locally path-connected spaces.
-/
theorem smoothBoundaryDomain_pointedComponent_isPathConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (D : SmoothBoundaryDomain X) {p : X}
    (hp : p ∈ D.carrier) :
    IsPathConnected (connectedComponentIn D.carrier p) :=
  (smoothBoundaryDomain_pointedComponent_isComponentOf D hp).isPathConnected_of_isOpen
    D.isOpen

/--
%%handwave
name:
  The pointed component lies in its filled side
statement:
  If \(U\) is the exterior component of the complement of the closure of the
  pointed component, then the pointed component lies in the filled side
  determined by \(U\).
proof:
  The exterior component is disjoint from the closure of the pointed
  component, while the pointed component is open.
-/
theorem smoothBoundaryDomain_pointedComponent_subset_filledSide_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) (p : X)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U) :
    connectedComponentIn D.carrier p ⊆ filledSideOfExteriorComponent U :=
  hU.open_subset_filledSide_of_closure_complement
    (smoothBoundaryDomain_pointedComponent_isOpen D p)

/--
%%handwave
name:
  Pointed-component points join to the base inside the filled side
statement:
  If \(x\) lies in the pointed component of \(D\), then \(p\) and \(x\) can
  be joined by a path lying in the filled side determined by the exterior
  component.
proof:
  The pointed component is path connected and lies in the filled side.
-/
theorem smoothBoundaryDomain_pointedComponent_joinedIn_filledSide_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (D : SmoothBoundaryDomain X) {p x : X}
    (hp : p ∈ D.carrier) {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hx : x ∈ connectedComponentIn D.carrier p) :
    JoinedIn (filledSideOfExteriorComponent U) p x := by
  have hpath :
      IsPathConnected (connectedComponentIn D.carrier p) :=
    smoothBoundaryDomain_pointedComponent_isPathConnected D hp
  have hp_component : p ∈ connectedComponentIn D.carrier p :=
    smoothBoundaryDomain_pointedComponent_mem D hp
  exact (hpath.joinedIn p hp_component x hx).mono
    (smoothBoundaryDomain_pointedComponent_subset_filledSide_of_exteriorComponent_closure
      D p hU)

/--
%%handwave
name:
  The base point lies in the filled side
statement:
  If \(p\in D\) and \(U\) is the exterior component of the complement of the
  closure of the \(p\)-component, then \(p\) lies in the filled side
  determined by \(U\).
proof:
  The point lies in its component, and that component lies in the filled side.
-/
theorem smoothBoundaryDomain_base_mem_filledSide_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) {p : X}
    (hp : p ∈ D.carrier) {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U) :
    p ∈ filledSideOfExteriorComponent U :=
  smoothBoundaryDomain_pointedComponent_subset_filledSide_of_exteriorComponent_closure
    D p hU (smoothBoundaryDomain_pointedComponent_mem D hp)

/--
%%handwave
name:
  Filled-side points lie in the pointed closure or in a filled hole
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the exterior component of
  \(X\setminus\overline C\), then every point of the filled side either lies
  in \(\overline C\) or lies in a complementary component different from
  \(U\).
proof:
  This is the general filled-side decomposition applied to the compact set
  \(\overline C\).
-/
theorem smoothBoundaryDomain_filledSide_subset_pointedComponent_closure_union_holes
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) (p : X) {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U) :
    filledSideOfExteriorComponent U ⊆
      closure (connectedComponentIn D.carrier p) ∪
        {x : X |
          ∃ V : Set X,
            IsComponentOf V
              (closure (connectedComponentIn D.carrier p))ᶜ ∧
              V ≠ U ∧ x ∈ V} :=
  hU.filledSide_subset_union_nonExterior_components

/--
%%handwave
name:
  Points in one filled hole join inside the filled side
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(V\) is a component of
  \(X\setminus\overline C\) different from the exterior component \(U\), then
  any two points of \(V\) can be joined by a path lying in the filled side.
proof:
  Complementary components of the closed set \(\overline C\) are path
  connected in the locally path-connected surface, and components different
  from \(U\) lie in the filled side.
-/
theorem smoothBoundaryDomain_nonExterior_component_joinedIn_filledSide
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) (p : X) {U V : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hV :
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ)
    (hne : V ≠ U) :
    ∀ x ∈ V, ∀ y ∈ V, JoinedIn (filledSideOfExteriorComponent U) x y :=
  hV.joinedIn_filledSide_of_ne_exterior hU isClosed_closure hne

/--
%%handwave
name:
  Filled holes touch the closed pointed component
statement:
  Let \(V\) be a component of \(X\setminus\overline C\), where \(C\) is the
  component of \(D\) containing \(p\).  Then the frontier of \(V\) meets
  \(\overline C\).
proof:
  The closed set \(\overline C\) is nonempty.  In a connected locally
  connected space, every component of the complement of a nonempty closed set
  has a frontier point on that closed set.
-/
theorem smoothBoundaryDomain_nonExterior_component_frontier_meets_pointedComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {V : Set X}
    (hV :
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ) :
    ∃ a : X,
      a ∈ frontier V ∧
        a ∈ closure (connectedComponentIn D.carrier p) := by
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hK_nonempty :
      (closure (connectedComponentIn D.carrier p)).Nonempty :=
    ⟨p, subset_closure (smoothBoundaryDomain_pointedComponent_mem D hp)⟩
  rcases hV.frontier_inter_nonempty_of_compl_isClosed
      isClosed_closure hK_nonempty with
    ⟨a, ha_frontier, ha_closure⟩
  exact ⟨a, ha_frontier, ha_closure⟩

/--
%%handwave
name:
  Pointed-component frontier points are reached from the inside
statement:
  Let \(x\) be a frontier point of the pointed component \(C\) that lies in
  the filled side.  Then \(x\) can be reached inside the filled side from
  some point of \(C\).
proof:
  The filled side is open and locally path connected.  The path component of
  the filled side containing \(x\) is therefore an open neighborhood of
  \(x\).  Since \(x\in\overline C\), this neighborhood contains a point of
  \(C\), and by construction that point is joined to \(x\) inside the filled
  side.
-/
theorem smoothBoundaryDomain_pointedComponent_frontier_has_interior_collar_in_filledSide
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p x : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hx_frontier : x ∈ frontier (connectedComponentIn D.carrier p))
    (hx_filled : x ∈ filledSideOfExteriorComponent U) :
    ∃ y : X,
      y ∈ connectedComponentIn D.carrier p ∧
        JoinedIn (filledSideOfExteriorComponent U) y x := by
  let F : Set X := filledSideOfExteriorComponent U
  let C : Set X := connectedComponentIn D.carrier p
  have _hp_mem : p ∈ D.carrier := hp
  have _hU_component : IsComponentOf U (closure C)ᶜ := by
    simpa [C] using hU.isComponentOf
  haveI : LocPathConnectedSpace X :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
  have hx_closure : x ∈ closure C := frontier_subset_closure hx_frontier
  have hF_nhds : F ∈ 𝓝 x :=
    (filledSideOfExteriorComponent_isOpen U).mem_nhds hx_filled
  have hP_nhds : pathComponentIn F x ∈ 𝓝 x :=
    pathComponentIn_mem_nhds hF_nhds
  rcases mem_closure_iff_nhds.mp hx_closure
      (pathComponentIn F x) hP_nhds with
    ⟨y, hyP, hyC⟩
  exact ⟨y, hyC, hyP.symm⟩

/--
%%handwave
name:
  Pointed-component frontier points join to the base in the filled side
statement:
  Let \(x\) be a frontier point of the pointed component \(C\) that lies in
  the filled side.  Then \(p\) and \(x\) can be joined by a path lying in the
  filled side.
proof:
  A smooth one-sided collar of \(C\) at \(x\) connects \(x\) to nearby
  interior points of \(C\), and the pointed component is path connected.
-/
theorem smoothBoundaryDomain_pointedComponent_frontier_joinedIn_filledSide_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p x : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hx_frontier : x ∈ frontier (connectedComponentIn D.carrier p))
    (hx_filled : x ∈ filledSideOfExteriorComponent U) :
    JoinedIn (filledSideOfExteriorComponent U) p x := by
  rcases
      smoothBoundaryDomain_pointedComponent_frontier_has_interior_collar_in_filledSide
        D hp hU hx_frontier hx_filled with
    ⟨y, hy_component, hyx⟩
  have hpy :
      JoinedIn (filledSideOfExteriorComponent U) p y :=
    smoothBoundaryDomain_pointedComponent_joinedIn_filledSide_of_exteriorComponent_closure
      D hp hU hy_component
  exact hpy.trans hyx

/--
%%handwave
name:
  Closed pointed-component points join to the base in the filled side
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(x\in\overline C\) also lies in
  the filled side determined by the exterior component, then \(p\) and \(x\)
  can be joined by a path lying in the filled side.
proof:
  Interior points of \(C\) are joined to \(p\) inside \(C\).  Boundary points
  are reached from nearby points of \(C\) through a smooth one-sided collar
  that stays in the filled side.
-/
theorem smoothBoundaryDomain_pointedComponent_closure_joinedIn_filledSide_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p x : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hx_closure : x ∈ closure (connectedComponentIn D.carrier p))
    (hx_filled : x ∈ filledSideOfExteriorComponent U) :
    JoinedIn (filledSideOfExteriorComponent U) p x := by
  by_cases hx_component : x ∈ connectedComponentIn D.carrier p
  · exact
      smoothBoundaryDomain_pointedComponent_joinedIn_filledSide_of_exteriorComponent_closure
        D hp hU hx_component
  · haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
    have hcomponent_open :
        IsOpen (connectedComponentIn D.carrier p) :=
      smoothBoundaryDomain_pointedComponent_isOpen D p
    have hx_frontier : x ∈ frontier (connectedComponentIn D.carrier p) := by
      rw [frontier, hcomponent_open.interior_eq]
      exact ⟨hx_closure, hx_component⟩
    exact
      smoothBoundaryDomain_pointedComponent_frontier_joinedIn_filledSide_of_exteriorComponent_closure
        D hp hU hx_frontier hx_filled

/--
%%handwave
name:
  Non-exterior attachments lie on the filled side in signed coordinates
statement:
  In a signed smooth-boundary chart, suppose the negative side belongs to the
  chosen component and a complementary component \(V\ne U\) accumulates at the
  boundary point.  Then the boundary point lies in the filled side determined
  by \(U\).
proof:
  Shrink to a product square.  The negative half-square lies in the chosen
  component, so the complement of its closure inside the square is exactly
  the positive half-square.  Since \(V\) accumulates at the boundary point,
  this positive half-square lies in \(V\), and therefore the whole square is
  disjoint from \(U\).
-/
theorem signedBoundaryChart_nonExterior_attachment_mem_filledSide
    {X F : Type} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D C K U V : Set X} (hC : IsComponentOf C D)
    (hK : K = closure C) (hUcomp : IsComponentOf U Kᶜ)
    (hVcomp : IsComponentOf V Kᶜ) (hne : V ≠ U)
    (x : frontier D) (hxK : (x : X) ∈ K) (hxVcl : (x : X) ∈ closure V)
    (E : OpenPartialHomeomorph X (ℝ × F))
    (hxE : (x : X) ∈ E.source)
    (hD_side : ∀ y ∈ E.source, y ∈ D ↔ (E y).1 < 0)
    (hfront_side : ∀ y ∈ E.source, y ∈ frontier D ↔ (E y).1 = 0) :
    (x : X) ∈ filledSideOfExteriorComponent U := by
  classical
  let z₀ : ℝ × F := E (x : X)
  have hz₀_target : z₀ ∈ E.target := by
    simpa [z₀] using E.map_source hxE
  have hz₀_fst : z₀.1 = 0 := by
    simpa [z₀] using (hfront_side (x : X) hxE).mp x.2
  rcases mem_nhds_prod_iff.mp (E.open_target.mem_nhds hz₀_target) with
    ⟨U₀, hU₀, V₀, hV₀, hU₀V₀⟩
  have hz₀_fst' : (E (x : X)).1 = 0 := by
    simpa [z₀] using hz₀_fst
  have hU₀_zero : U₀ ∈ 𝓝 (0 : ℝ) := by
    simpa [hz₀_fst'] using hU₀
  rcases mem_nhds_iff_exists_Ioo_subset.mp hU₀_zero with
    ⟨a, b, h0ab, hIooU₀⟩
  rcases Metric.nhds_basis_ball.mem_iff.mp hV₀ with
    ⟨ρ, hρpos, hρV₀⟩
  have ha0 : a < 0 := h0ab.1
  have h0b : 0 < b := h0ab.2
  let S : Set (ℝ × F) := Ioo a b ×ˢ Metric.ball z₀.2 ρ
  let Sneg : Set (ℝ × F) := Ioo a 0 ×ˢ Metric.ball z₀.2 ρ
  let Spos : Set (ℝ × F) := Ioo 0 b ×ˢ Metric.ball z₀.2 ρ
  let O : Set X := E.symm '' S
  let Pneg : Set X := E.symm '' Sneg
  let Ppos : Set X := E.symm '' Spos
  have hS_target : S ⊆ E.target := by
    intro q hq
    exact hU₀V₀ ⟨hIooU₀ hq.1, hρV₀ hq.2⟩
  have hSneg_subset_S : Sneg ⊆ S := by
    intro q hq
    exact ⟨⟨hq.1.1, hq.1.2.trans h0b⟩, hq.2⟩
  have hSpos_subset_S : Spos ⊆ S := by
    intro q hq
    exact ⟨⟨ha0.trans hq.1.1, hq.1.2⟩, hq.2⟩
  have hSneg_target : Sneg ⊆ E.target := hSneg_subset_S.trans hS_target
  have hSpos_target : Spos ⊆ E.target := hSpos_subset_S.trans hS_target
  have hS_open : IsOpen S := by
    exact isOpen_Ioo.prod Metric.isOpen_ball
  have hO_open : IsOpen O := by
    exact E.isOpen_image_symm_of_subset_target hS_open hS_target
  have hz₀S : z₀ ∈ S := by
    exact ⟨by simpa [hz₀_fst] using h0ab,
      Metric.mem_ball_self hρpos⟩
  have hxO : (x : X) ∈ O := by
    refine ⟨z₀, hz₀S, ?_⟩
    simpa [z₀] using E.left_inv hxE
  have hO_nhds_x : O ∈ 𝓝 (x : X) := hO_open.mem_nhds hxO
  have hx_closureC : (x : X) ∈ closure C := by
    simpa [hK] using hxK
  have hO_meets_C : (O ∩ C).Nonempty :=
    mem_closure_iff_nhds.mp hx_closureC O hO_nhds_x
  have hSneg_pre : IsPreconnected Sneg := by
    exact ((convex_Ioo a (0 : ℝ)).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hSpos_pre : IsPreconnected Spos := by
    exact ((convex_Ioo (0 : ℝ) b).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hPneg_pre : IsPreconnected Pneg := by
    exact hSneg_pre.image E.symm (E.continuousOn_symm.mono hSneg_target)
  have hPpos_pre : IsPreconnected Ppos := by
    exact hSpos_pre.image E.symm (E.continuousOn_symm.mono hSpos_target)
  have hPneg_subset_D : Pneg ⊆ D := by
    rintro y ⟨q, hq, rfl⟩
    have hq_target : q ∈ E.target := hSneg_target hq
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    exact (hD_side (E.symm q) hy_source).2 (by
      simpa [hEq] using hq.1.2)
  have hPneg_meets_C : (C ∩ Pneg).Nonempty := by
    rcases hO_meets_C with ⟨c, hcO, hcC⟩
    rcases hcO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hc_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hcD : E.symm q ∈ D := hC.subset hcC
    have hq_neg : q.1 < 0 := by
      simpa [hEq] using (hD_side (E.symm q) hc_source).1 hcD
    refine ⟨E.symm q, hcC, ⟨q, ?_, rfl⟩⟩
    exact ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩
  have hPneg_subset_C : Pneg ⊆ C :=
    hC.2.2.2 Pneg hPneg_subset_D hPneg_pre hPneg_meets_C
  have hPpos_subset_compl : Ppos ⊆ O ∩ Kᶜ := by
    rintro y ⟨q, hqpos, rfl⟩
    have hqS : q ∈ S := hSpos_subset_S hqpos
    have hq_target : q ∈ E.target := hSpos_target hqpos
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hq_pos : 0 < q.1 := hqpos.1.1
    refine ⟨⟨q, hqS, rfl⟩, ?_⟩
    intro hyK
    have hy_notD : E.symm q ∉ D := by
      intro hyD
      have hlt : q.1 < 0 := by
        simpa [hEq] using (hD_side (E.symm q) hy_source).1 hyD
      linarith
    have hy_not_frontier : E.symm q ∉ frontier D := by
      intro hyfront
      have hzero : q.1 = 0 := by
        simpa [hEq] using (hfront_side (E.symm q) hy_source).1 hyfront
      linarith
    have hy_not_closureD : E.symm q ∉ closure D := by
      rw [closure_eq_self_union_frontier]
      exact fun hy => hy.elim hy_notD hy_not_frontier
    exact hy_not_closureD (closure_mono hC.subset (by simpa [hK] using hyK))
  have hcompl_subset_Ppos : O ∩ Kᶜ ⊆ Ppos := by
    rintro y ⟨hyO, hyKc⟩
    rcases hyO with ⟨q, hqS, rfl⟩
    rcases lt_trichotomy q.1 0 with hq_neg | hq_zero | hq_pos
    · exact False.elim (hyKc (by
        rw [hK]
        exact subset_closure (hPneg_subset_C ⟨q, ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩, rfl⟩)))
    · have hq_target : q ∈ E.target := hS_target hqS
      have hq_closure_neg : q ∈ closure Sneg := by
        change q ∈ closure (Ioo a 0 ×ˢ Metric.ball z₀.2 ρ)
        rw [closure_prod_eq, closure_Ioo ha0.ne]
        exact ⟨⟨le_of_lt (by simpa [hq_zero] using hqS.1.1),
            by simp [hq_zero]⟩,
          subset_closure hqS.2⟩
      have hcont : ContinuousWithinAt E.symm Sneg q :=
        (E.continuousOn_symm q hq_target).mono hSneg_target
      have hy_closure_Pneg : E.symm q ∈ closure Pneg :=
        hcont.mem_closure hq_closure_neg (mapsTo_image E.symm Sneg)
      exact False.elim (hyKc (by
        rw [hK]
        exact closure_mono hPneg_subset_C hy_closure_Pneg))
    · refine ⟨q, ?_, rfl⟩
      exact ⟨⟨hq_pos, hqS.1.2⟩, hqS.2⟩
  have hpatch_eq : O ∩ Kᶜ = Ppos :=
    Subset.antisymm hcompl_subset_Ppos hPpos_subset_compl
  have hPpos_subset_Kc : Ppos ⊆ Kᶜ :=
    fun y hy => (hPpos_subset_compl hy).2
  have hV_meets_Ppos : (V ∩ Ppos).Nonempty := by
    rcases mem_closure_iff_nhds.mp hxVcl O hO_nhds_x with
      ⟨z, hzO, hzV⟩
    have hzKc : z ∈ Kᶜ := hVcomp.subset hzV
    have hzPpos : z ∈ Ppos := by
      simpa [hpatch_eq] using (show z ∈ O ∩ Kᶜ from ⟨hzO, hzKc⟩)
    exact ⟨z, hzV, hzPpos⟩
  have hPpos_subset_V : Ppos ⊆ V :=
    hVcomp.2.2.2 Ppos hPpos_subset_Kc hPpos_pre hV_meets_Ppos
  have hO_subset_Uc : O ⊆ Uᶜ := by
    intro y hyO hyU
    have hyKc : y ∈ Kᶜ := hUcomp.subset hyU
    have hyPpos : y ∈ Ppos := by
      simpa [hpatch_eq] using (show y ∈ O ∩ Kᶜ from ⟨hyO, hyKc⟩)
    have hyV : y ∈ V := hPpos_subset_V hyPpos
    exact hne (hVcomp.eq_of_inter_nonempty hUcomp ⟨y, hyV, hyU⟩)
  simpa [filledSideOfExteriorComponent] using
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hO_nhds_x hO_subset_Uc)

/--
%%handwave
name:
  Filled-hole attachments have collar bridges
statement:
  Suppose a non-exterior complementary component touches \(\overline C\) at
  a frontier point.  Then some point of the component can be joined inside the
  filled side to a point of \(\overline C\).
proof:
  In a smooth boundary chart at the attachment point, the component and the
  pointed side occupy adjacent local sides.  A short collar path crosses from
  the component to the pointed closure without entering the exterior side.
-/
theorem smoothBoundaryDomain_nonExterior_component_frontier_attachment_has_collar_bridge
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) {U V : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hV :
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ)
    (hne : V ≠ U) {a : X}
    (ha_frontier : a ∈ frontier V)
    (ha_closure : a ∈ closure (connectedComponentIn D.carrier p)) :
    ∃ y : X,
      y ∈ V ∧
        ∃ b : X,
          b ∈ closure (connectedComponentIn D.carrier p) ∧
            b ∈ filledSideOfExteriorComponent U ∧
              JoinedIn (filledSideOfExteriorComponent U) y b := by
  classical
  let C : Set X := connectedComponentIn D.carrier p
  let K : Set X := closure C
  haveI : LocPathConnectedSpace X :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
  haveI : LocallyConnectedSpace X := locPathConnectedSpace_locallyConnectedSpace
  have ha_closureKc : a ∈ closure Kᶜ := by
    exact closure_mono (by simpa [K] using hV.subset)
      (frontier_subset_closure ha_frontier)
  have ha_frontierK : a ∈ frontier K := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure (by simpa [K, C] using ha_closure), ha_closureKc⟩
  have ha_boundary : a ∈ frontier D.carrier := by
    simpa [C, K] using
      smoothBoundaryDomain_pointedComponent_closure_frontier_subset_boundary
        D hp ha_frontierK
  rcases D.smooth_boundary a ha_boundary with
    ⟨e, _he, hasource, r, hrsmooth, dr, hrderiv, hdrnz, hlocal⟩
  rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, haN⟩
  have hprops_a := hNsub haN
  have hazero : r (e a) = 0 := (hprops_a.2.2).mp ha_boundary
  rcases smoothPlaneRegularZeroSet_implicitCoord_fst_eq
      hrsmooth.contDiffAt hrderiv hdrnz hazero with
    ⟨Φ, haΦ, hΦfst, _hΦzero⟩
  let eN : OpenPartialHomeomorph X ℂ := e.restrOpen N hNopen
  let E : OpenPartialHomeomorph X (ℝ × dr.ker) := eN.trans Φ
  have haE : a ∈ E.source := by
    change a ∈ (eN.trans Φ).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by simpa [eN] using ⟨hasource, haN⟩, by simpa [eN] using haΦ⟩
  have hD_side :
      ∀ y ∈ E.source, y ∈ D.carrier ↔ (E y).1 < 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.1
  have hfront_side :
      ∀ y ∈ E.source, y ∈ frontier D.carrier ↔ (E y).1 = 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.2
  have hC : IsComponentOf C D.carrier :=
    smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  have hUcomp : IsComponentOf U Kᶜ := by
    simpa [C, K] using hU.isComponentOf
  have hVcomp : IsComponentOf V Kᶜ := by
    simpa [C, K] using hV
  have ha_filled : a ∈ filledSideOfExteriorComponent U := by
    simpa [C, K] using
      signedBoundaryChart_nonExterior_attachment_mem_filledSide
        (D := D.carrier) (C := C) (K := K) (U := U) (V := V)
        hC rfl hUcomp hVcomp hne ⟨a, ha_boundary⟩
        (by simpa [C, K] using ha_closure)
        (frontier_subset_closure ha_frontier)
        E haE hD_side hfront_side
  let Fset : Set X := filledSideOfExteriorComponent U
  have hF_nhds : Fset ∈ 𝓝 a :=
    (filledSideOfExteriorComponent_isOpen U).mem_nhds (by simpa [Fset] using ha_filled)
  have hpathComponent_nhds : pathComponentIn Fset a ∈ 𝓝 a :=
    pathComponentIn_mem_nhds hF_nhds
  rcases mem_closure_iff_nhds.mp (frontier_subset_closure ha_frontier)
      (pathComponentIn Fset a) hpathComponent_nhds with
    ⟨y, hy_path, hyV⟩
  exact ⟨y, hyV, a, ha_closure, ha_filled, by simpa [Fset] using hy_path.symm⟩

/--
%%handwave
name:
  Filled holes attach through a chosen frontier point
statement:
  Let \(V\) be a complementary component different from the exterior
  component, and let \(a\in\partial V\cap\overline C\).  Then every point of
  \(V\) can be joined inside the filled side to some point of \(\overline C\).
proof:
  In a smooth boundary chart at the attachment point, the component \(V\) and
  the closed pointed component meet along the two sides of a smooth arc.  The
  collar supplies a path from \(V\) to a filled-side point of \(\overline C\).
-/
theorem smoothBoundaryDomain_nonExterior_component_joinedIn_pointedComponent_closure_in_filledSide_of_frontier_attachment
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) {U V : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hV :
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ)
    (hne : V ≠ U) {a : X}
    (ha_frontier : a ∈ frontier V)
    (ha_closure : a ∈ closure (connectedComponentIn D.carrier p)) :
    ∀ x ∈ V,
      ∃ b : X,
        b ∈ closure (connectedComponentIn D.carrier p) ∧
          b ∈ filledSideOfExteriorComponent U ∧
            JoinedIn (filledSideOfExteriorComponent U) x b := by
  rcases
      smoothBoundaryDomain_nonExterior_component_frontier_attachment_has_collar_bridge
        D hp hU hV hne ha_frontier ha_closure with
    ⟨y, hyV, b, hb_closure, hb_filled, hyb⟩
  intro x hxV
  have hxy :
      JoinedIn (filledSideOfExteriorComponent U) x y :=
    smoothBoundaryDomain_nonExterior_component_joinedIn_filledSide
      D p hU hV hne x hxV y hyV
  exact ⟨b, hb_closure, hb_filled, hxy.trans hyb⟩

/--
%%handwave
name:
  Filled holes attach to the closed pointed component
statement:
  Let \(V\) be a complementary component of
  \(X\setminus\overline C\) different from the exterior component.  Every
  point of \(V\) can be joined inside the filled side to a point of
  \(\overline C\).
proof:
  The component \(V\) touches the smooth boundary of \(\overline C\).  A
  two-sided smooth-boundary chart gives an attachment point on
  \(\overline C\) that lies in the filled side, and local path connectedness
  joins the given point of \(V\) to that attachment through \(V\) together
  with the collar.
-/
theorem smoothBoundaryDomain_nonExterior_component_joinedIn_pointedComponent_closure_in_filledSide
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) {U V : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hV :
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ)
    (hne : V ≠ U) :
    ∀ x ∈ V,
      ∃ a : X,
        a ∈ closure (connectedComponentIn D.carrier p) ∧
          a ∈ filledSideOfExteriorComponent U ∧
            JoinedIn (filledSideOfExteriorComponent U) x a := by
  rcases
      smoothBoundaryDomain_nonExterior_component_frontier_meets_pointedComponent_closure
        D hp hV with
    ⟨a, ha_frontier, ha_closure⟩
  exact
    smoothBoundaryDomain_nonExterior_component_joinedIn_pointedComponent_closure_in_filledSide_of_frontier_attachment
      D hp hU hV hne ha_frontier ha_closure

/--
%%handwave
name:
  The filled side has frontier on the pointed-component closure
statement:
  If \(U\) is the exterior component of the complement of the closure of the
  pointed component, then the frontier of the filled side determined by \(U\)
  lies in that closure.
proof:
  Filled-side frontiers lie on exterior frontiers, and exterior frontiers for
  the complement of a closed set lie on that closed set.
-/
theorem smoothBoundaryDomain_frontier_filledSide_subset_pointedComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) (p : X)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U) :
    frontier (filledSideOfExteriorComponent U) ⊆
      closure (connectedComponentIn D.carrier p) :=
  hU.frontier_filledSide_subset_of_isClosed isClosed_closure

/--
%%handwave
name:
  The filled-side frontier lies on the original boundary
statement:
  If \(U\) is the exterior component of the complement of the closure of the
  pointed component of \(D\), then the frontier of the filled side determined
  by \(U\) lies on the frontier of \(D\).
proof:
  The filled-side frontier lies in the closure of the pointed component.  It
  cannot lie in the pointed component itself, because that component is open
  and contained in the filled side.  Therefore it lies on the frontier of the
  pointed component, and component frontiers of open sets lie on the frontier
  of the ambient open set.
-/
theorem smoothBoundaryDomain_frontier_filledSide_subset_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) {p : X}
    (hp : p ∈ D.carrier) {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U) :
    frontier (filledSideOfExteriorComponent U) ⊆ frontier D.carrier := by
  have hfrontier_subset_closure :
      frontier (filledSideOfExteriorComponent U) ⊆
        closure (connectedComponentIn D.carrier p) :=
    smoothBoundaryDomain_frontier_filledSide_subset_pointedComponent_closure
      D p hU
  have hcomponent_subset_filled :
      connectedComponentIn D.carrier p ⊆ filledSideOfExteriorComponent U :=
    smoothBoundaryDomain_pointedComponent_subset_filledSide_of_exteriorComponent_closure
      D p hU
  have hcomponent_open :
      IsOpen (connectedComponentIn D.carrier p) :=
    smoothBoundaryDomain_pointedComponent_isOpen D p
  have hcomponent :
      IsComponentOf (connectedComponentIn D.carrier p) D.carrier :=
    smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  have hfrontier_component_subset :
      frontier (connectedComponentIn D.carrier p) ⊆ frontier D.carrier :=
    hcomponent.frontier_subset_frontier_of_isOpen D.isOpen
  intro x hx
  have hx_closure : x ∈ closure (connectedComponentIn D.carrier p) :=
    hfrontier_subset_closure hx
  have hx_not_component : x ∉ connectedComponentIn D.carrier p := by
    intro hx_component
    have hx_filled : x ∈ filledSideOfExteriorComponent U :=
      hcomponent_subset_filled hx_component
    have hfilled_open : IsOpen (filledSideOfExteriorComponent U) :=
      filledSideOfExteriorComponent_isOpen U
    have hx_empty :
        x ∈ filledSideOfExteriorComponent U ∩
          frontier (filledSideOfExteriorComponent U) :=
      ⟨hx_filled, hx⟩
    rw [hfilled_open.inter_frontier_eq] at hx_empty
    exact hx_empty
  have hx_component_frontier :
      x ∈ frontier (connectedComponentIn D.carrier p) := by
    rw [frontier, hcomponent_open.interior_eq]
    exact ⟨hx_closure, hx_not_component⟩
  exact hfrontier_component_subset hx_component_frontier

/--
%%handwave
name:
  The filled side remains away from the exterior component
statement:
  If \(U\) is the exterior component of the complement of the closure of the
  pointed component, then the closure of the filled side determined by \(U\)
  is disjoint from \(U\).
proof:
  In a locally connected surface the exterior component is open, and the
  closure of the filled side remains in its complement.
-/
theorem smoothBoundaryDomain_closure_filledSide_subset_compl_exteriorComponent
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) (p : X)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U) :
    closure (filledSideOfExteriorComponent U) ⊆ Uᶜ := by
  have hU_open : IsOpen U :=
    hU.isComponentOf.isOpen_of_isOpen isClosed_closure.isOpen_compl
  exact closure_filledSideOfExteriorComponent_subset_compl_of_isOpen hU_open

/--
%%handwave
name:
  The filled side is nonempty
statement:
  If \(p\in D\), then the filled side determined by the exterior component of
  the complement of the pointed-component closure is nonempty.
proof:
  The base point belongs to the filled side.
-/
theorem smoothBoundaryDomain_filledSide_nonempty_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) {p : X}
    (hp : p ∈ D.carrier) {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U) :
    (filledSideOfExteriorComponent U).Nonempty :=
  ⟨p, smoothBoundaryDomain_base_mem_filledSide_of_exteriorComponent_closure
    D hp hU⟩

/--
%%handwave
name:
  Non-exterior holes of a pointed component are compact
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then every other complementary
  component has compact closure.
proof:
  The closure \(\overline C\) is compact.  A complementary component different
  from the unique exterior component is non-exterior, hence has compact
  closure.
-/
theorem smoothBoundaryDomain_nonExterior_component_closure_compact_of_unique_exterior
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (_hp : p ∈ D.carrier)
    {U V : Set X}
    (_hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hunique :
      ∀ W : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) W →
          W = U)
    (hV :
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ)
    (hne : V ≠ U) :
    IsCompact (closure V) :=
  hV.closure_compact_of_ne_unique_exterior
    (smoothBoundaryDomain_pointedComponent_closure_compact D p)
    hunique hne

/--
%%handwave
name:
  A local complement patch determines incident components
statement:
  Let \(K\) be closed, and let \(V_0\) be a component of \(X\setminus K\).
  Suppose an ambient neighborhood \(O\) of each point of a boundary interval
  has the property that \(O\cap (X\setminus K)\subset V_0\).  Then every
  complementary component whose frontier meets that interval is \(V_0\).
proof:
  If the frontier of a component \(V\) meets the interval at \(y\), then every
  neighborhood of \(y\) meets \(V\).  In particular \(O\) meets \(V\), and
  this point of \(O\cap (X\setminus K)\) lies in \(V_0\).  Thus \(V\) and
  \(V_0\) intersect, so component uniqueness gives \(V=V_0\).
-/
theorem complement_component_frontiers_subset_singleton_of_local_complement_subset
    {X A : Type} [TopologicalSpace X] {K O : Set X}
    {V₀ : {V : Set X // IsComponentOf V Kᶜ}}
    {frontierTrace : {V : Set X // IsComponentOf V Kᶜ} → Set A}
    {val : A → X} {t : Set A}
    (hO_nhds : ∀ y : A, y ∈ t → O ∈ 𝓝 (val y))
    (htrace : ∀ V : {V : Set X // IsComponentOf V Kᶜ},
      frontierTrace V ⊆ {y : A | val y ∈ frontier (V : Set X)})
    (hO_subset : O ∩ Kᶜ ⊆ (V₀ : Set X)) :
    {V : {V : Set X // IsComponentOf V Kᶜ} |
      ((frontierTrace V) ∩ t).Nonempty} ⊆ {V₀} := by
  intro V hV
  rcases hV with ⟨y, hy_trace, hyt⟩
  have hy_frontier : val y ∈ frontier (V : Set X) :=
    htrace V hy_trace
  have hO_meets : (O ∩ (V : Set X)).Nonempty :=
    mem_closure_iff_nhds.mp (frontier_subset_closure hy_frontier)
      O (hO_nhds y hyt)
  rcases hO_meets with ⟨z, hzO, hzV⟩
  have hzKc : z ∈ Kᶜ := V.2.subset hzV
  have hzV₀ : z ∈ (V₀ : Set X) := hO_subset ⟨hzO, hzKc⟩
  have hEq : (V : Set X) = (V₀ : Set X) :=
    V.2.eq_of_inter_nonempty V₀.2 ⟨z, hzV, hzV₀⟩
  exact Set.mem_singleton_iff.mpr (Subtype.ext hEq)

/--
%%handwave
name:
  A connected complement patch lies in one component
statement:
  If a nonempty preconnected set \(P\) is contained in \(X\setminus K\), then
  \(P\) is contained in one component of \(X\setminus K\).
proof:
  Choose a point of \(P\).  The connected component of this point in
  \(X\setminus K\) contains every preconnected subset of the complement that
  meets it, hence contains \(P\).
-/
theorem preconnected_subset_compl_subset_component
    {X : Type} [TopologicalSpace X] {K P : Set X}
    (hP_pre : IsPreconnected P) (hP_nonempty : P.Nonempty)
    (hP_subset : P ⊆ Kᶜ) :
    ∃ V₀ : {V : Set X // IsComponentOf V Kᶜ}, P ⊆ (V₀ : Set X) := by
  rcases hP_nonempty with ⟨z, hzP⟩
  refine ⟨⟨connectedComponentIn Kᶜ z,
    isComponentOf_connectedComponentIn (hP_subset hzP)⟩, ?_⟩
  exact hP_pre.subset_connectedComponentIn hzP hP_subset

/--
%%handwave
name:
  Signed boundary charts give connected local complement patches
statement:
  Suppose a neighborhood of a boundary point is identified with a neighborhood
  in a product \(\mathbb R\times F\), with the domain given by the negative
  transverse coordinate and the boundary by the zero transverse coordinate.
  If the boundary point lies in the closure of the chosen component, then a
  sufficiently small square around it has a nonempty connected positive-side
  complement patch.
proof:
  Choose a small product square inside the chart.  The negative half-square is
  connected and meets the chosen component, so it lies in that component.  The
  zero side is in its closure.  Thus, inside the square, the complement of the
  closed component is exactly the positive half-square, which is nonempty and
  connected.
-/
theorem signedBoundaryChart_preconnected_local_complement_patch
    {X F : Type} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D C K : Set X} (_hD_open : IsOpen D) (hC : IsComponentOf C D)
    (hK : K = closure C)
    (x : frontier D) (hxK : (x : X) ∈ K)
    (E : OpenPartialHomeomorph X (ℝ × F))
    (hxE : (x : X) ∈ E.source)
    (hD_side : ∀ y ∈ E.source, y ∈ D ↔ (E y).1 < 0)
    (hfront_side : ∀ y ∈ E.source, y ∈ frontier D ↔ (E y).1 = 0) :
    ∃ t ∈ 𝓝 x,
      ∃ O : Set X,
        (∀ y : frontier D, y ∈ t → O ∈ 𝓝 (y : X)) ∧
          (O ∩ Kᶜ).Nonempty ∧ IsPreconnected (O ∩ Kᶜ) := by
  classical
  let z₀ : ℝ × F := E (x : X)
  have hz₀_target : z₀ ∈ E.target := by
    simpa [z₀] using E.map_source hxE
  have hz₀_fst : z₀.1 = 0 := by
    simpa [z₀] using (hfront_side (x : X) hxE).mp x.2
  rcases mem_nhds_prod_iff.mp (E.open_target.mem_nhds hz₀_target) with
    ⟨U, hU, V, hV, hUV⟩
  have hz₀_fst' : (E (x : X)).1 = 0 := by
    simpa [z₀] using hz₀_fst
  have hU₀ : U ∈ 𝓝 (0 : ℝ) := by
    simpa [hz₀_fst'] using hU
  rcases mem_nhds_iff_exists_Ioo_subset.mp hU₀ with
    ⟨a, b, h0ab, hIooU⟩
  rcases Metric.nhds_basis_ball.mem_iff.mp hV with
    ⟨ρ, hρpos, hρV⟩
  have ha0 : a < 0 := h0ab.1
  have h0b : 0 < b := h0ab.2
  let S : Set (ℝ × F) := Ioo a b ×ˢ Metric.ball z₀.2 ρ
  let Sneg : Set (ℝ × F) := Ioo a 0 ×ˢ Metric.ball z₀.2 ρ
  let Spos : Set (ℝ × F) := Ioo 0 b ×ˢ Metric.ball z₀.2 ρ
  let O : Set X := E.symm '' S
  let Pneg : Set X := E.symm '' Sneg
  let Ppos : Set X := E.symm '' Spos
  have hS_target : S ⊆ E.target := by
    intro q hq
    exact hUV ⟨hIooU hq.1, hρV hq.2⟩
  have hSneg_subset_S : Sneg ⊆ S := by
    intro q hq
    exact ⟨⟨hq.1.1, hq.1.2.trans h0b⟩, hq.2⟩
  have hSpos_subset_S : Spos ⊆ S := by
    intro q hq
    exact ⟨⟨ha0.trans hq.1.1, hq.1.2⟩, hq.2⟩
  have hSneg_target : Sneg ⊆ E.target := hSneg_subset_S.trans hS_target
  have hSpos_target : Spos ⊆ E.target := hSpos_subset_S.trans hS_target
  have hS_open : IsOpen S := by
    exact isOpen_Ioo.prod Metric.isOpen_ball
  have hO_open : IsOpen O := by
    exact E.isOpen_image_symm_of_subset_target hS_open hS_target
  have hz₀S : z₀ ∈ S := by
    exact ⟨by simpa [hz₀_fst] using h0ab,
      Metric.mem_ball_self hρpos⟩
  have hxO : (x : X) ∈ O := by
    refine ⟨z₀, hz₀S, ?_⟩
    simpa [z₀] using E.left_inv hxE
  have hO_nhds_x : O ∈ 𝓝 (x : X) := hO_open.mem_nhds hxO
  have hx_closureC : (x : X) ∈ closure C := by
    simpa [hK] using hxK
  have hO_meets_C : (O ∩ C).Nonempty :=
    mem_closure_iff_nhds.mp hx_closureC O hO_nhds_x
  have hSneg_pre : IsPreconnected Sneg := by
    exact ((convex_Ioo a (0 : ℝ)).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hSpos_pre : IsPreconnected Spos := by
    exact ((convex_Ioo (0 : ℝ) b).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hPneg_pre : IsPreconnected Pneg := by
    exact hSneg_pre.image E.symm (E.continuousOn_symm.mono hSneg_target)
  have hPpos_pre : IsPreconnected Ppos := by
    exact hSpos_pre.image E.symm (E.continuousOn_symm.mono hSpos_target)
  have hPneg_subset_D : Pneg ⊆ D := by
    rintro y ⟨q, hq, rfl⟩
    have hq_target : q ∈ E.target := hSneg_target hq
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    exact (hD_side (E.symm q) hy_source).2 (by
      simpa [hEq] using hq.1.2)
  have hPneg_meets_C : (C ∩ Pneg).Nonempty := by
    rcases hO_meets_C with ⟨c, hcO, hcC⟩
    rcases hcO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hc_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hcD : E.symm q ∈ D := hC.subset hcC
    have hq_neg : q.1 < 0 := by
      simpa [hEq] using (hD_side (E.symm q) hc_source).1 hcD
    refine ⟨E.symm q, hcC, ⟨q, ?_, rfl⟩⟩
    exact ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩
  have hPneg_subset_C : Pneg ⊆ C :=
    hC.2.2.2 Pneg hPneg_subset_D hPneg_pre hPneg_meets_C
  have zero_slice_mem_K :
      ∀ q ∈ S, q.1 = 0 → E.symm q ∈ K := by
    intro q hqS hq_zero
    have hq_target : q ∈ E.target := hS_target hqS
    have hq_closure_neg : q ∈ closure Sneg := by
      change q ∈ closure (Ioo a 0 ×ˢ Metric.ball z₀.2 ρ)
      rw [closure_prod_eq, closure_Ioo ha0.ne]
      exact ⟨⟨le_of_lt (by simpa [hq_zero] using hqS.1.1),
          by simp [hq_zero]⟩,
        subset_closure hqS.2⟩
    have hcont : ContinuousWithinAt E.symm Sneg q :=
      (E.continuousOn_symm q hq_target).mono hSneg_target
    have hy_closure_Pneg : E.symm q ∈ closure Pneg :=
      hcont.mem_closure hq_closure_neg (mapsTo_image E.symm Sneg)
    rw [hK]
    exact closure_mono hPneg_subset_C hy_closure_Pneg
  have hPpos_subset_compl : Ppos ⊆ O ∩ Kᶜ := by
    rintro y ⟨q, hqpos, rfl⟩
    have hqS : q ∈ S := hSpos_subset_S hqpos
    have hq_target : q ∈ E.target := hSpos_target hqpos
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hq_pos : 0 < q.1 := hqpos.1.1
    refine ⟨⟨q, hqS, rfl⟩, ?_⟩
    intro hyK
    have hy_notD : E.symm q ∉ D := by
      intro hyD
      have hlt : q.1 < 0 := by
        simpa [hEq] using (hD_side (E.symm q) hy_source).1 hyD
      linarith
    have hy_not_frontier : E.symm q ∉ frontier D := by
      intro hyfront
      have hzero : q.1 = 0 := by
        simpa [hEq] using (hfront_side (E.symm q) hy_source).1 hyfront
      linarith
    have hy_not_closureD : E.symm q ∉ closure D := by
      rw [closure_eq_self_union_frontier]
      exact fun hy => hy.elim hy_notD hy_not_frontier
    exact hy_not_closureD (closure_mono hC.subset (by simpa [hK] using hyK))
  have hcompl_subset_Ppos : O ∩ Kᶜ ⊆ Ppos := by
    rintro y ⟨hyO, hyKc⟩
    rcases hyO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    rcases lt_trichotomy q.1 0 with hq_neg | hq_zero | hq_pos
    · exact False.elim (hyKc (by
        rw [hK]
        exact subset_closure (hPneg_subset_C ⟨q, ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩, rfl⟩)))
    · exact False.elim (hyKc (zero_slice_mem_K q hqS hq_zero))
    · refine ⟨q, ?_, rfl⟩
      exact ⟨⟨hq_pos, hqS.1.2⟩, hqS.2⟩
  have hpatch_eq : O ∩ Kᶜ = Ppos :=
    Subset.antisymm hcompl_subset_Ppos hPpos_subset_compl
  have hPpos_nonempty : Ppos.Nonempty := by
    refine ⟨E.symm (b / 2, z₀.2), ⟨(b / 2, z₀.2), ?_, rfl⟩⟩
    exact ⟨by constructor <;> linarith, Metric.mem_ball_self hρpos⟩
  let t : Set (frontier D) := {y | (y : X) ∈ O}
  refine ⟨t, ?_, O, ?_, ?_, ?_⟩
  · exact (hO_open.preimage continuous_subtype_val).mem_nhds hxO
  · intro y hy
    exact hO_open.mem_nhds hy
  · rwa [hpatch_eq]
  · rwa [hpatch_eq]

/--
%%handwave
name:
  Signed boundary charts identify the filled side near an exterior boundary point
statement:
  Suppose a neighborhood of a boundary point is identified with a neighborhood
  in a product \(\mathbb R\times F\), with the domain given by the negative
  transverse coordinate and the boundary by the zero transverse coordinate.
  If the boundary point lies in the closures of the chosen domain component
  and of a complementary component \(U\), then near that point the filled side
  determined by \(U\) is exactly the domain side.
proof:
  Choose a product square inside the chart.  The negative half-square lies in
  the chosen domain component, the positive half-square is a connected subset
  of the complement of its closure, and the zero diameter is in the closures
  of both half-squares.  Since \(U\) accumulates at the boundary point, the
  positive half-square meets \(U\), hence lies in \(U\).  Thus the interior of
  the complement of \(U\) inside the square is precisely the negative
  half-square.
-/
theorem signedBoundaryChart_filledSide_eventually_eq_domain_of_component_closure
    {X F : Type} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D C K U : Set X} (hD_open : IsOpen D) (hC : IsComponentOf C D)
    (hK : K = closure C) (hUcomp : IsComponentOf U Kᶜ)
    (x : frontier D) (hxK : (x : X) ∈ K) (hxUcl : (x : X) ∈ closure U)
    (E : OpenPartialHomeomorph X (ℝ × F))
    (hxE : (x : X) ∈ E.source)
    (hD_side : ∀ y ∈ E.source, y ∈ D ↔ (E y).1 < 0)
    (hfront_side : ∀ y ∈ E.source, y ∈ frontier D ↔ (E y).1 = 0) :
    ∀ᶠ y in 𝓝 (x : X),
      (y ∈ filledSideOfExteriorComponent U ↔ y ∈ D) := by
  classical
  let z₀ : ℝ × F := E (x : X)
  have hz₀_target : z₀ ∈ E.target := by
    simpa [z₀] using E.map_source hxE
  have hz₀_fst : z₀.1 = 0 := by
    simpa [z₀] using (hfront_side (x : X) hxE).mp x.2
  rcases mem_nhds_prod_iff.mp (E.open_target.mem_nhds hz₀_target) with
    ⟨U₀, hU₀, V₀, hV₀, hU₀V₀⟩
  have hz₀_fst' : (E (x : X)).1 = 0 := by
    simpa [z₀] using hz₀_fst
  have hU₀_zero : U₀ ∈ 𝓝 (0 : ℝ) := by
    simpa [hz₀_fst'] using hU₀
  rcases mem_nhds_iff_exists_Ioo_subset.mp hU₀_zero with
    ⟨a, b, h0ab, hIooU₀⟩
  rcases Metric.nhds_basis_ball.mem_iff.mp hV₀ with
    ⟨ρ, hρpos, hρV₀⟩
  have ha0 : a < 0 := h0ab.1
  have h0b : 0 < b := h0ab.2
  let S : Set (ℝ × F) := Ioo a b ×ˢ Metric.ball z₀.2 ρ
  let Sneg : Set (ℝ × F) := Ioo a 0 ×ˢ Metric.ball z₀.2 ρ
  let Spos : Set (ℝ × F) := Ioo 0 b ×ˢ Metric.ball z₀.2 ρ
  let O : Set X := E.symm '' S
  let Pneg : Set X := E.symm '' Sneg
  let Ppos : Set X := E.symm '' Spos
  have hS_target : S ⊆ E.target := by
    intro q hq
    exact hU₀V₀ ⟨hIooU₀ hq.1, hρV₀ hq.2⟩
  have hSneg_subset_S : Sneg ⊆ S := by
    intro q hq
    exact ⟨⟨hq.1.1, hq.1.2.trans h0b⟩, hq.2⟩
  have hSpos_subset_S : Spos ⊆ S := by
    intro q hq
    exact ⟨⟨ha0.trans hq.1.1, hq.1.2⟩, hq.2⟩
  have hSneg_target : Sneg ⊆ E.target := hSneg_subset_S.trans hS_target
  have hSpos_target : Spos ⊆ E.target := hSpos_subset_S.trans hS_target
  have hS_open : IsOpen S := by
    exact isOpen_Ioo.prod Metric.isOpen_ball
  have hO_open : IsOpen O := by
    exact E.isOpen_image_symm_of_subset_target hS_open hS_target
  have hz₀S : z₀ ∈ S := by
    exact ⟨by simpa [hz₀_fst] using h0ab,
      Metric.mem_ball_self hρpos⟩
  have hxO : (x : X) ∈ O := by
    refine ⟨z₀, hz₀S, ?_⟩
    simpa [z₀] using E.left_inv hxE
  have hO_nhds_x : O ∈ 𝓝 (x : X) := hO_open.mem_nhds hxO
  have hx_closureC : (x : X) ∈ closure C := by
    simpa [hK] using hxK
  have hO_meets_C : (O ∩ C).Nonempty :=
    mem_closure_iff_nhds.mp hx_closureC O hO_nhds_x
  have hSneg_pre : IsPreconnected Sneg := by
    exact ((convex_Ioo a (0 : ℝ)).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hSpos_pre : IsPreconnected Spos := by
    exact ((convex_Ioo (0 : ℝ) b).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hPneg_pre : IsPreconnected Pneg := by
    exact hSneg_pre.image E.symm (E.continuousOn_symm.mono hSneg_target)
  have hPpos_pre : IsPreconnected Ppos := by
    exact hSpos_pre.image E.symm (E.continuousOn_symm.mono hSpos_target)
  have hPneg_subset_D : Pneg ⊆ D := by
    rintro y ⟨q, hq, rfl⟩
    have hq_target : q ∈ E.target := hSneg_target hq
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    exact (hD_side (E.symm q) hy_source).2 (by
      simpa [hEq] using hq.1.2)
  have hPneg_meets_C : (C ∩ Pneg).Nonempty := by
    rcases hO_meets_C with ⟨c, hcO, hcC⟩
    rcases hcO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hc_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hcD : E.symm q ∈ D := hC.subset hcC
    have hq_neg : q.1 < 0 := by
      simpa [hEq] using (hD_side (E.symm q) hc_source).1 hcD
    refine ⟨E.symm q, hcC, ⟨q, ?_, rfl⟩⟩
    exact ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩
  have hPneg_subset_C : Pneg ⊆ C :=
    hC.2.2.2 Pneg hPneg_subset_D hPneg_pre hPneg_meets_C
  have hPpos_subset_compl : Ppos ⊆ O ∩ Kᶜ := by
    rintro y ⟨q, hqpos, rfl⟩
    have hqS : q ∈ S := hSpos_subset_S hqpos
    have hq_target : q ∈ E.target := hSpos_target hqpos
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hq_pos : 0 < q.1 := hqpos.1.1
    refine ⟨⟨q, hqS, rfl⟩, ?_⟩
    intro hyK
    have hy_notD : E.symm q ∉ D := by
      intro hyD
      have hlt : q.1 < 0 := by
        simpa [hEq] using (hD_side (E.symm q) hy_source).1 hyD
      linarith
    have hy_not_frontier : E.symm q ∉ frontier D := by
      intro hyfront
      have hzero : q.1 = 0 := by
        simpa [hEq] using (hfront_side (E.symm q) hy_source).1 hyfront
      linarith
    have hy_not_closureD : E.symm q ∉ closure D := by
      rw [closure_eq_self_union_frontier]
      exact fun hy => hy.elim hy_notD hy_not_frontier
    exact hy_not_closureD (closure_mono hC.subset (by simpa [hK] using hyK))
  have hcompl_subset_Ppos : O ∩ Kᶜ ⊆ Ppos := by
    rintro y ⟨hyO, hyKc⟩
    rcases hyO with ⟨q, hqS, rfl⟩
    rcases lt_trichotomy q.1 0 with hq_neg | hq_zero | hq_pos
    · exact False.elim (hyKc (by
        rw [hK]
        exact subset_closure (hPneg_subset_C ⟨q, ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩, rfl⟩)))
    · have hq_target : q ∈ E.target := hS_target hqS
      have hq_closure_neg : q ∈ closure Sneg := by
        change q ∈ closure (Ioo a 0 ×ˢ Metric.ball z₀.2 ρ)
        rw [closure_prod_eq, closure_Ioo ha0.ne]
        exact ⟨⟨le_of_lt (by simpa [hq_zero] using hqS.1.1),
            by simp [hq_zero]⟩,
          subset_closure hqS.2⟩
      have hcont : ContinuousWithinAt E.symm Sneg q :=
        (E.continuousOn_symm q hq_target).mono hSneg_target
      have hy_closure_Pneg : E.symm q ∈ closure Pneg :=
        hcont.mem_closure hq_closure_neg (mapsTo_image E.symm Sneg)
      exact False.elim (hyKc (by
        rw [hK]
        exact closure_mono hPneg_subset_C hy_closure_Pneg))
    · refine ⟨q, ?_, rfl⟩
      exact ⟨⟨hq_pos, hqS.1.2⟩, hqS.2⟩
  have hpatch_eq : O ∩ Kᶜ = Ppos :=
    Subset.antisymm hcompl_subset_Ppos hPpos_subset_compl
  have hPpos_subset_Kc : Ppos ⊆ Kᶜ :=
    fun y hy => (hPpos_subset_compl hy).2
  have hU_meets_Ppos : (U ∩ Ppos).Nonempty := by
    rcases mem_closure_iff_nhds.mp hxUcl O hO_nhds_x with
      ⟨z, hzO, hzU⟩
    have hzKc : z ∈ Kᶜ := hUcomp.subset hzU
    have hzPpos : z ∈ Ppos := by
      simpa [hpatch_eq] using (show z ∈ O ∩ Kᶜ from ⟨hzO, hzKc⟩)
    exact ⟨z, hzU, hzPpos⟩
  have hPpos_subset_U : Ppos ⊆ U :=
    hUcomp.2.2.2 Ppos hPpos_subset_Kc hPpos_pre hU_meets_Ppos
  have zero_slice_mem_closure_U :
      ∀ q ∈ S, q.1 = 0 → E.symm q ∈ closure U := by
    intro q hqS hq_zero
    have hq_target : q ∈ E.target := hS_target hqS
    have hq_closure_pos : q ∈ closure Spos := by
      change q ∈ closure (Ioo 0 b ×ˢ Metric.ball z₀.2 ρ)
      rw [closure_prod_eq, closure_Ioo h0b.ne]
      exact ⟨⟨by simp [hq_zero],
          le_of_lt (by simpa [hq_zero] using hqS.1.2)⟩,
        subset_closure hqS.2⟩
    have hcont : ContinuousWithinAt E.symm Spos q :=
      (E.continuousOn_symm q hq_target).mono hSpos_target
    have hy_closure_Ppos : E.symm q ∈ closure Ppos :=
      hcont.mem_closure hq_closure_pos (mapsTo_image E.symm Spos)
    exact closure_mono hPpos_subset_U hy_closure_Ppos
  have hOD_subset_Uc : O ∩ D ⊆ Uᶜ := by
    rintro y ⟨hyO, hyD⟩ hyU
    have hyKc : y ∈ Kᶜ := hUcomp.subset hyU
    have hyPpos : y ∈ Ppos := by
      simpa [hpatch_eq] using (show y ∈ O ∩ Kᶜ from ⟨hyO, hyKc⟩)
    rcases hyPpos with ⟨q, hqpos, rfl⟩
    have hq_target : q ∈ E.target := hSpos_target hqpos
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hlt : q.1 < 0 := by
      simpa [hEq] using (hD_side (E.symm q) hy_source).1 hyD
    have hpos : 0 < q.1 := hqpos.1.1
    linarith
  filter_upwards [hO_open.mem_nhds hxO] with y hyO
  constructor
  · intro hyF
    rcases hyO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hy_not_closureU : E.symm q ∉ closure U := by
      simpa [filledSideOfExteriorComponent, interior_compl] using hyF
    rcases lt_trichotomy q.1 0 with hq_neg | hq_zero | hq_pos
    · exact (hD_side (E.symm q) hy_source).2 (by
        simpa [hEq] using hq_neg)
    · exact False.elim
        (hy_not_closureU (zero_slice_mem_closure_U q hqS hq_zero))
    · have hyPpos : E.symm q ∈ Ppos :=
        ⟨q, ⟨⟨hq_pos, hqS.1.2⟩, hqS.2⟩, rfl⟩
      exact False.elim
        (hy_not_closureU (subset_closure (hPpos_subset_U hyPpos)))
  · intro hyD
    have hOD_nhds : O ∩ D ∈ 𝓝 y :=
      (hO_open.inter hD_open).mem_nhds ⟨hyO, hyD⟩
    have hUc_nhds : Uᶜ ∈ 𝓝 y :=
      Filter.mem_of_superset hOD_nhds hOD_subset_Uc
    exact mem_interior_iff_mem_nhds.mpr hUc_nhds

/--
%%handwave
name:
  Boundary intervals have connected local complement patches
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  At any smooth boundary point lying in
  \(\overline C\), there is a small boundary interval and an ambient
  neighborhood of that interval whose part outside \(\overline C\) is
  nonempty and preconnected.
proof:
  Use a smooth boundary chart and shrink to a disk whose boundary diameter is
  the chosen interval.  The domain half-disk is connected and meets \(C\), so
  it lies in \(C\).  The local complement of \(\overline C\) in the disk is
  therefore the opposite half-disk, which is nonempty and connected.
-/
theorem smoothBoundaryDomain_pointedComponent_boundary_interval_preconnected_local_complement_patch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    (x : frontier D.carrier)
    (hxK : (x : X) ∈ closure (connectedComponentIn D.carrier p)) :
    ∃ t ∈ 𝓝 x,
      ∃ O : Set X,
        (∀ y : frontier D.carrier, y ∈ t → O ∈ 𝓝 (y : X)) ∧
          (O ∩ (closure (connectedComponentIn D.carrier p))ᶜ).Nonempty ∧
            IsPreconnected (O ∩ (closure (connectedComponentIn D.carrier p))ᶜ) := by
  classical
  let C : Set X := connectedComponentIn D.carrier p
  let K : Set X := closure C
  rcases D.smooth_boundary (x : X) x.2 with
    ⟨e, _he, hxsource, r, hrsmooth, dr, hrderiv, hdrnz, hlocal⟩
  rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, hxN⟩
  have hprops_x := hNsub hxN
  have hxzero : r (e (x : X)) = 0 := (hprops_x.2.2).mp x.2
  rcases smoothPlaneRegularZeroSet_implicitCoord_fst_eq
      hrsmooth.contDiffAt hrderiv hdrnz hxzero with
    ⟨Φ, hxΦ, hΦfst, _hΦzero⟩
  let eN : OpenPartialHomeomorph X ℂ := e.restrOpen N hNopen
  let E : OpenPartialHomeomorph X (ℝ × dr.ker) := eN.trans Φ
  have hxE : (x : X) ∈ E.source := by
    change (x : X) ∈ (eN.trans Φ).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by simpa [eN] using ⟨hxsource, hxN⟩, by simpa [eN] using hxΦ⟩
  have hD_side :
      ∀ y ∈ E.source, y ∈ D.carrier ↔ (E y).1 < 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.1
  have hfront_side :
      ∀ y ∈ E.source, y ∈ frontier D.carrier ↔ (E y).1 = 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.2
  have hC : IsComponentOf C D.carrier :=
    smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  simpa [C, K] using
    signedBoundaryChart_preconnected_local_complement_patch
      (D := D.carrier) (C := C) (K := K)
      D.isOpen hC rfl x hxK E hxE hD_side hfront_side

/--
%%handwave
name:
  Boundary intervals have a single complement side
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  At any smooth boundary point lying in
  \(\overline C\), there is a small boundary interval and an ambient
  neighborhood of that interval whose points outside \(\overline C\) all lie
  in one component of \(X\setminus\overline C\).
proof:
  Use a smooth boundary chart and shrink to a disk whose boundary diameter is
  the chosen interval.  The domain half-disk is connected and meets \(C\),
  so it lies in \(C\).  The opposite half-disk is connected and lies outside
  \(\overline C\), hence lies in a single complementary component.  Boundary
  points of the diameter are closure points of the domain half-disk, so no
  other local complement side remains.
-/
theorem smoothBoundaryDomain_pointedComponent_boundary_interval_local_complement_subset_component
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    (x : frontier D.carrier)
    (hxK : (x : X) ∈ closure (connectedComponentIn D.carrier p)) :
    ∃ t ∈ 𝓝 x,
      ∃ O : Set X,
        (∀ y : frontier D.carrier, y ∈ t → O ∈ 𝓝 (y : X)) ∧
          ∃ V₀ : {V : Set X //
              IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ},
            O ∩ (closure (connectedComponentIn D.carrier p))ᶜ ⊆ (V₀ : Set X) := by
  rcases
      smoothBoundaryDomain_pointedComponent_boundary_interval_preconnected_local_complement_patch
        D hp x hxK with
    ⟨t, ht, O, hO_nhds, hpatch_nonempty, hpatch_pre⟩
  rcases preconnected_subset_compl_subset_component
      (K := closure (connectedComponentIn D.carrier p))
      (P := O ∩ (closure (connectedComponentIn D.carrier p))ᶜ)
      hpatch_pre hpatch_nonempty inter_subset_right with
    ⟨V₀, hV₀_subset⟩
  exact ⟨t, ht, O, hO_nhds, V₀, hV₀_subset⟩

/--
%%handwave
name:
  Boundary intervals have one local exterior component
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  At any smooth boundary point lying in
  \(\overline C\), there is a boundary interval and a single component of
  \(X\setminus\overline C\) such that every complementary frontier meeting
  that interval is the frontier of this component.
proof:
  In a smooth boundary chart, shrink to a disk whose diameter is the boundary
  interval.  Since the chosen boundary point lies in \(\overline C\), the
  domain half-disk meets \(C\); by connectedness of the half-disk it lies in
  \(C\).  The other half-disk lies in \(X\setminus\overline D\), hence in
  \(X\setminus\overline C\), and is connected, so it lies in one global
  complementary component.  Any complementary frontier on the smaller
  boundary interval must be incident to that exterior half-disk.
-/
theorem smoothBoundaryDomain_pointedComponent_boundary_interval_frontiers_subset_singleton
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    (x : frontier D.carrier)
    (hxK : (x : X) ∈ closure (connectedComponentIn D.carrier p)) :
    ∃ t ∈ 𝓝 x,
      ∃ V₀ : {V : Set X //
          IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ},
        {V : {V : Set X //
            IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ} |
          (({y : frontier D.carrier | (y : X) ∈ frontier (V : Set X)} ∩ t).Nonempty)}
            ⊆ {V₀} := by
  rcases
      smoothBoundaryDomain_pointedComponent_boundary_interval_local_complement_subset_component
        D hp x hxK with
    ⟨t, ht, O, hO_nhds, V₀, hO_subset⟩
  refine ⟨t, ht, V₀, ?_⟩
  exact
    complement_component_frontiers_subset_singleton_of_local_complement_subset
      (A := frontier D.carrier)
      (K := closure (connectedComponentIn D.carrier p))
      (O := O)
      (V₀ := V₀)
      (frontierTrace :=
        fun V : {V : Set X //
            IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ} =>
          {y : frontier D.carrier | (y : X) ∈ frontier (V : Set X)})
      (val := fun y : frontier D.carrier => (y : X))
      (t := t)
      hO_nhds
      (by
        intro V y hy
        exact hy)
      hO_subset

/--
%%handwave
name:
  Boundary intervals meet finitely many complementary frontiers
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  At any smooth boundary point lying in
  \(\overline C\), there is a boundary interval that meets the frontiers of
  only finitely many components of \(X\setminus\overline C\).
proof:
  Choose a smooth boundary chart and shrink it so that the boundary becomes a
  diameter of a small disk.  The disk is cut into two half-disks: the domain
  side, which lies in the pointed component near the chosen point, and the
  exterior side.  Hence only the complementary regions occupying these local
  sides can have frontier on the smaller boundary interval.
-/
theorem smoothBoundaryDomain_pointedComponent_boundary_interval_meets_finitely_many_complement_frontiers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    (x : frontier D.carrier)
    (hxK : (x : X) ∈ closure (connectedComponentIn D.carrier p)) :
    ∃ t ∈ 𝓝 x,
      {V : {V : Set X //
          IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ} |
        (({y : frontier D.carrier | (y : X) ∈ frontier (V : Set X)} ∩ t).Nonempty)}.Finite := by
  rcases
      smoothBoundaryDomain_pointedComponent_boundary_interval_frontiers_subset_singleton
        D hp x hxK with
    ⟨t, ht, V₀, hsubset⟩
  exact ⟨t, ht, (Set.finite_singleton V₀).subset hsubset⟩

/--
%%handwave
name:
  Complementary frontiers are locally finite along a smooth boundary
statement:
  Let \(D\) be a smooth relatively compact domain, let \(C\) be the component
  of \(D\) containing \(p\), and let the complementary components be the
  components of \(X\setminus\overline C\).  The traces of their frontiers on
  the original smooth boundary of \(D\) form a locally finite family.
proof:
  In a smooth boundary chart, the boundary is an interval and the two sides
  of the interval are the domain side and the exterior side.  If a boundary
  point lies in \(\overline C\), then the nearby domain side belongs to the
  pointed component, so locally the complement of \(\overline C\) has only the
  exterior side.  If the boundary point is not in \(\overline C\), no
  complementary frontier can meet it in a sufficiently small neighborhood.
  Thus a small boundary interval meets only finitely many complementary
  frontiers.
-/
theorem smoothBoundaryDomain_pointedComponent_complement_component_frontiers_locallyFinite_on_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    LocallyFinite
      (fun V : {V : Set X //
          IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ} =>
        {x : frontier D.carrier | (x : X) ∈ frontier (V : Set X)}) := by
  classical
  intro x
  let K : Set X := closure (connectedComponentIn D.carrier p)
  by_cases hxK : (x : X) ∈ K
  · simpa [K] using
      smoothBoundaryDomain_pointedComponent_boundary_interval_meets_finitely_many_complement_frontiers
        D hp x hxK
  · let t : Set (frontier D.carrier) := {y | (y : X) ∈ Kᶜ}
    have ht_nhds : t ∈ 𝓝 x := by
      have hxKc : (x : X) ∈ Kᶜ := by
        simpa using hxK
      simpa [t] using
        ((isClosed_closure.isOpen_compl).preimage continuous_subtype_val).mem_nhds hxKc
    refine ⟨t, ht_nhds, ?_⟩
    have hset_empty :
        {V : {V : Set X // IsComponentOf V Kᶜ} |
          (({y : frontier D.carrier | (y : X) ∈ frontier (V : Set X)} ∩ t).Nonempty)} =
            ∅ := by
      ext V
      constructor
      · intro hV
        rcases hV with ⟨y, hy_frontier, hyt⟩
        have hyK : (y : X) ∈ K :=
          V.2.frontier_subset_of_compl_isClosed isClosed_closure hy_frontier
        exact False.elim (hyt hyK)
      · intro hV
        exact False.elim hV
    simp [K, hset_empty]

/--
%%handwave
name:
  Smooth boundary components have finite local incidence
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  Along each connected component of the
  original smooth boundary of \(D\), only finitely many components of
  \(X\setminus\overline C\) are incident.
proof:
  Smooth boundary charts identify the boundary locally with an interval and
  the complement locally with the two sides of that interval.  Compactness of
  the boundary component gives a finite subcover by such two-sided charts.
-/
theorem smoothBoundaryDomain_pointedComponent_boundaryComponent_incident_complement_components_finite
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    (B : ConnectedComponents (frontier D.carrier)) :
    {V : Set X |
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ ∧
        ∃ x : frontier D.carrier,
          (x : X) ∈ frontier V ∧
            ConnectedComponents.mk x = B}.Finite := by
  classical
  let K : Set X := closure (connectedComponentIn D.carrier p)
  let I : Type :=
    {V : Set X //
      IsComponentOf V Kᶜ ∧
        ∃ x : frontier D.carrier,
          (x : X) ∈ frontier V ∧
            ConnectedComponents.mk x = B}
  let J : Type := {V : Set X // IsComponentOf V Kᶜ}
  let fJ : J → Set (frontier D.carrier) :=
    fun V ↦ {x : frontier D.carrier | (x : X) ∈ frontier (V : Set X)}
  let g : I → J := fun V ↦ ⟨(V : Set X), V.2.1⟩
  have hg_inj : Function.Injective g := by
    intro V W hVW
    apply Subtype.ext
    exact congrArg (fun Z : J => (Z : Set X)) hVW
  have hLFJ : LocallyFinite fJ := by
    simpa [K, J, fJ] using
      smoothBoundaryDomain_pointedComponent_complement_component_frontiers_locallyFinite_on_boundary
        D hp
  have hLFI : LocallyFinite (fJ ∘ g) :=
    hLFJ.comp_injective hg_inj
  haveI : CompactSpace (frontier D.carrier) :=
    isCompact_iff_compactSpace.mp (smoothBoundaryDomain_frontier_compact D)
  have hnonempty : ∀ V : I, ((fJ ∘ g) V).Nonempty := by
    intro V
    rcases V.2.2 with ⟨x, hx_frontier, _hxB⟩
    exact ⟨x, hx_frontier⟩
  have hIfinite_univ : (univ : Set I).Finite :=
    hLFI.finite_of_compact hnonempty
  have himage_finite :
      ((fun V : I => (V : Set X)) '' (univ : Set I)).Finite :=
    hIfinite_univ.image _
  convert himage_finite using 1
  ext V
  constructor
  · intro hV
    exact ⟨⟨V, by simpa [K] using hV⟩, mem_univ _, rfl⟩
  · rintro ⟨W, _hW, rfl⟩
    simpa [K] using W.2

/--
%%handwave
name:
  Finite smooth boundary components give finitely many complementary regions
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If the original frontier of \(D\)
  has only finitely many connected components, then
  \(X\setminus\overline C\) has only finitely many complementary components.
proof:
  Every complementary component touches the frontier of \(\overline C\), and
  that frontier is contained in the original frontier of \(D\).  Smooth
  boundary charts have exactly two local sides, so only finitely many
  complementary components can be incident to each original boundary
  component.
-/
theorem smoothBoundaryDomain_pointedComponent_complement_components_finite_of_finite_boundary_components
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    (hfinite_boundary : Finite (ConnectedComponents (frontier D.carrier))) :
    {V : Set X |
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ}.Finite := by
  have hK_nonempty :
      (closure (connectedComponentIn D.carrier p)).Nonempty :=
    ⟨p, subset_closure (smoothBoundaryDomain_pointedComponent_mem D hp)⟩
  haveI : LocallyConnectedSpace X :=
    ChartedSpace.locallyConnectedSpace (H := ℂ) (M := X)
  exact
    finite_complement_components_of_frontier_subset_finite_boundary_components_and_finite_incidence
      (K := closure (connectedComponentIn D.carrier p))
      (A := frontier D.carrier)
      isClosed_closure hK_nonempty
      (smoothBoundaryDomain_pointedComponent_closure_frontier_subset_boundary
        D hp)
      hfinite_boundary
      (fun B =>
        smoothBoundaryDomain_pointedComponent_boundaryComponent_incident_complement_components_finite
          D hp B)

/--
%%handwave
name:
  Smooth filled obstacles have finitely many complementary components
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  Then
  \(X\setminus\overline C\) has only finitely many complementary components.
proof:
  The original frontier of \(D\) is compact and locally connected, hence has
  finitely many connected components.  The frontier of \(\overline C\) lies
  in that original frontier, and smooth boundary charts have finitely many
  local sides along each original boundary component.
-/
theorem smoothBoundaryDomain_pointedComponent_complement_components_finite
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    {V : Set X |
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ}.Finite := by
  exact
    smoothBoundaryDomain_pointedComponent_complement_components_finite_of_finite_boundary_components
      D hp
      (smoothBoundaryDomain_frontier_finite_connectedComponents D)

/--
%%handwave
name:
  The pointed component lies in the bounded filling
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component containing \(p\).  Then \(C\) lies in the bounded filling of
  \(\overline C\).
proof:
  The component \(C\) is open and contained in its closure.
-/
theorem smoothBoundaryDomain_pointedComponent_subset_boundedFilling
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) (p : X) :
    connectedComponentIn D.carrier p ⊆
      boundedFillingOfComplement
        (closure (connectedComponentIn D.carrier p)) :=
  open_subset_boundedFillingOfComplement_of_subset_obstacle
    (smoothBoundaryDomain_pointedComponent_isOpen D p)
    subset_closure

/--
%%handwave
name:
  The base point lies in the bounded filling
statement:
  If \(p\in D\), then \(p\) lies in the bounded filling of the closed
  component of \(D\) containing \(p\).
proof:
  The pointed component is open and is contained in its closure, hence it lies
  in the interior defining the bounded filling.  In particular, it contains
  \(p\).
-/
theorem smoothBoundaryDomain_base_mem_boundedFilling
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallyConnectedSpace X] (D : SmoothBoundaryDomain X) {p : X}
    (hp : p ∈ D.carrier) :
    p ∈ boundedFillingOfComplement
      (closure (connectedComponentIn D.carrier p)) :=
  smoothBoundaryDomain_pointedComponent_subset_boundedFilling D p
    (smoothBoundaryDomain_pointedComponent_mem D hp)

/--
%%handwave
name:
  The bounded filling is relatively compact
statement:
  The bounded filling of the closed pointed component of a smooth relatively
  compact domain has compact closure.
proof:
  The complement of the closed pointed component has finitely many components.
  The bounded filling is contained in the compact closure of the pointed
  component together with the finite union of the compact closures of the
  bounded complementary components.
-/
theorem smoothBoundaryDomain_boundedFilling_compact_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    IsCompact
      (closure
        (boundedFillingOfComplement
          (closure (connectedComponentIn D.carrier p)))) := by
  exact
    boundedFillingOfComplement_compact_closure_of_finite_components
      (smoothBoundaryDomain_pointedComponent_closure_compact D p)
      (smoothBoundaryDomain_pointedComponent_complement_components_finite
        D hp)

/--
%%handwave
name:
  The bounded-filling frontier lies on the original boundary
statement:
  The frontier of the bounded filling of the closed pointed component lies on
  the original smooth boundary of \(D\).
proof:
  The frontier of a bounded filling lies on the closed pointed component.
  It cannot lie in the open pointed component itself, since that component is
  contained in the bounded filling.  Hence it lies on the frontier of the
  pointed component, and this frontier is contained in the original boundary
  of \(D\).
-/
theorem smoothBoundaryDomain_frontier_boundedFilling_subset_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    frontier
        (boundedFillingOfComplement
          (closure (connectedComponentIn D.carrier p))) ⊆
      frontier D.carrier := by
  let C : Set X := connectedComponentIn D.carrier p
  let K : Set X := closure C
  have hfrontier_subset_K :
      frontier (boundedFillingOfComplement K) ⊆ K :=
    boundedFillingOfComplement_frontier_subset_obstacle isClosed_closure
  have hC_subset_fill :
      C ⊆ boundedFillingOfComplement K := by
    simpa [C, K] using
      smoothBoundaryDomain_pointedComponent_subset_boundedFilling D p
  have hC_open : IsOpen C := by
    simpa [C] using smoothBoundaryDomain_pointedComponent_isOpen D p
  have hcomponent :
      IsComponentOf C D.carrier := by
    simpa [C] using smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  have hfrontier_component_subset :
      frontier C ⊆ frontier D.carrier :=
    hcomponent.frontier_subset_frontier_of_isOpen D.isOpen
  intro x hx
  have hxK : x ∈ K := hfrontier_subset_K (by simpa [C, K] using hx)
  have hx_not_C : x ∉ C := by
    intro hxC
    have hx_fill : x ∈ boundedFillingOfComplement K :=
      hC_subset_fill hxC
    have hx_empty :
        x ∈ boundedFillingOfComplement K ∩
          frontier (boundedFillingOfComplement K) :=
      ⟨hx_fill, by simpa [C, K] using hx⟩
    rw [(boundedFillingOfComplement_isOpen K).inter_frontier_eq] at hx_empty
    exact hx_empty
  have hx_frontier_C : x ∈ frontier C := by
    rw [frontier, hC_open.interior_eq]
    exact ⟨hxK, hx_not_C⟩
  exact hfrontier_component_subset hx_frontier_C

/--
%%handwave
name:
  Signed boundary charts identify bounded fillings at retained boundary points
statement:
  In a smooth boundary chart, suppose the marked boundary point belongs to the
  closed chosen component but not to its bounded filling.  Then, near that
  point, the bounded filling occupies exactly the original domain side.
proof:
  Shrink to a product square.  The negative half-square lies in the chosen
  component, while the positive half-square lies in a single complementary
  component.  If that component had compact closure, the whole square would
  lie in the filled obstacle near the marked point, contrary to the point not
  being in the bounded filling.  Thus the positive side is unfilled; openness
  also excludes the zero side.
-/
theorem signedBoundaryChart_boundedFilling_eventually_eq_domain_of_not_mem
    {X F : Type} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D C K : Set X} (hC_open : IsOpen C) (hC : IsComponentOf C D)
    (hK : K = closure C)
    (x : frontier D) (hxK : (x : X) ∈ K)
    (hx_notFill : (x : X) ∉ boundedFillingOfComplement K)
    (E : OpenPartialHomeomorph X (ℝ × F))
    (hxE : (x : X) ∈ E.source)
    (hD_side : ∀ y ∈ E.source, y ∈ D ↔ (E y).1 < 0)
    (hfront_side : ∀ y ∈ E.source, y ∈ frontier D ↔ (E y).1 = 0) :
    ∀ᶠ y in 𝓝 (x : X),
      (y ∈ boundedFillingOfComplement K ↔ y ∈ D) := by
  classical
  let z₀ : ℝ × F := E (x : X)
  have hz₀_target : z₀ ∈ E.target := by
    simpa [z₀] using E.map_source hxE
  have hz₀_fst : z₀.1 = 0 := by
    simpa [z₀] using (hfront_side (x : X) hxE).mp x.2
  rcases mem_nhds_prod_iff.mp (E.open_target.mem_nhds hz₀_target) with
    ⟨U₀, hU₀, V₀, hV₀, hU₀V₀⟩
  have hz₀_fst' : (E (x : X)).1 = 0 := by
    simpa [z₀] using hz₀_fst
  have hU₀_zero : U₀ ∈ 𝓝 (0 : ℝ) := by
    simpa [hz₀_fst'] using hU₀
  rcases mem_nhds_iff_exists_Ioo_subset.mp hU₀_zero with
    ⟨a, b, h0ab, hIooU₀⟩
  rcases Metric.nhds_basis_ball.mem_iff.mp hV₀ with
    ⟨ρ, hρpos, hρV₀⟩
  have ha0 : a < 0 := h0ab.1
  have h0b : 0 < b := h0ab.2
  let S : Set (ℝ × F) := Ioo a b ×ˢ Metric.ball z₀.2 ρ
  let Sneg : Set (ℝ × F) := Ioo a 0 ×ˢ Metric.ball z₀.2 ρ
  let Spos : Set (ℝ × F) := Ioo 0 b ×ˢ Metric.ball z₀.2 ρ
  let O : Set X := E.symm '' S
  let Pneg : Set X := E.symm '' Sneg
  let Ppos : Set X := E.symm '' Spos
  have hS_target : S ⊆ E.target := by
    intro q hq
    exact hU₀V₀ ⟨hIooU₀ hq.1, hρV₀ hq.2⟩
  have hSneg_subset_S : Sneg ⊆ S := by
    intro q hq
    exact ⟨⟨hq.1.1, hq.1.2.trans h0b⟩, hq.2⟩
  have hSpos_subset_S : Spos ⊆ S := by
    intro q hq
    exact ⟨⟨ha0.trans hq.1.1, hq.1.2⟩, hq.2⟩
  have hSneg_target : Sneg ⊆ E.target := hSneg_subset_S.trans hS_target
  have hSpos_target : Spos ⊆ E.target := hSpos_subset_S.trans hS_target
  have hS_open : IsOpen S := by
    exact isOpen_Ioo.prod Metric.isOpen_ball
  have hO_open : IsOpen O := by
    exact E.isOpen_image_symm_of_subset_target hS_open hS_target
  have hz₀S : z₀ ∈ S := by
    exact ⟨by simpa [hz₀_fst] using h0ab,
      Metric.mem_ball_self hρpos⟩
  have hxO : (x : X) ∈ O := by
    refine ⟨z₀, hz₀S, ?_⟩
    simpa [z₀] using E.left_inv hxE
  have hO_nhds_x : O ∈ 𝓝 (x : X) := hO_open.mem_nhds hxO
  have hx_closureC : (x : X) ∈ closure C := by
    simpa [hK] using hxK
  have hO_meets_C : (O ∩ C).Nonempty :=
    mem_closure_iff_nhds.mp hx_closureC O hO_nhds_x
  have hSneg_pre : IsPreconnected Sneg := by
    exact ((convex_Ioo a (0 : ℝ)).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hSpos_pre : IsPreconnected Spos := by
    exact ((convex_Ioo (0 : ℝ) b).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hPneg_pre : IsPreconnected Pneg := by
    exact hSneg_pre.image E.symm (E.continuousOn_symm.mono hSneg_target)
  have hPpos_pre : IsPreconnected Ppos := by
    exact hSpos_pre.image E.symm (E.continuousOn_symm.mono hSpos_target)
  have hPneg_subset_D : Pneg ⊆ D := by
    rintro y ⟨q, hq, rfl⟩
    have hq_target : q ∈ E.target := hSneg_target hq
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    exact (hD_side (E.symm q) hy_source).2 (by
      simpa [hEq] using hq.1.2)
  have hPneg_meets_C : (C ∩ Pneg).Nonempty := by
    rcases hO_meets_C with ⟨c, hcO, hcC⟩
    rcases hcO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hc_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hcD : E.symm q ∈ D := hC.subset hcC
    have hq_neg : q.1 < 0 := by
      simpa [hEq] using (hD_side (E.symm q) hc_source).1 hcD
    refine ⟨E.symm q, hcC, ⟨q, ?_, rfl⟩⟩
    exact ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩
  have hPneg_subset_C : Pneg ⊆ C :=
    hC.2.2.2 Pneg hPneg_subset_D hPneg_pre hPneg_meets_C
  have zero_slice_mem_K :
      ∀ q ∈ S, q.1 = 0 → E.symm q ∈ K := by
    intro q hqS hq_zero
    have hq_target : q ∈ E.target := hS_target hqS
    have hq_closure_neg : q ∈ closure Sneg := by
      change q ∈ closure (Ioo a 0 ×ˢ Metric.ball z₀.2 ρ)
      rw [closure_prod_eq, closure_Ioo ha0.ne]
      exact ⟨⟨le_of_lt (by simpa [hq_zero] using hqS.1.1),
          by simp [hq_zero]⟩,
        subset_closure hqS.2⟩
    have hcont : ContinuousWithinAt E.symm Sneg q :=
      (E.continuousOn_symm q hq_target).mono hSneg_target
    have hy_closure_Pneg : E.symm q ∈ closure Pneg :=
      hcont.mem_closure hq_closure_neg (mapsTo_image E.symm Sneg)
    rw [hK]
    exact closure_mono hPneg_subset_C hy_closure_Pneg
  have hPpos_subset_compl : Ppos ⊆ O ∩ Kᶜ := by
    rintro y ⟨q, hqpos, rfl⟩
    have hqS : q ∈ S := hSpos_subset_S hqpos
    have hq_target : q ∈ E.target := hSpos_target hqpos
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hq_pos : 0 < q.1 := hqpos.1.1
    refine ⟨⟨q, hqS, rfl⟩, ?_⟩
    intro hyK
    have hy_notD : E.symm q ∉ D := by
      intro hyD
      have hlt : q.1 < 0 := by
        simpa [hEq] using (hD_side (E.symm q) hy_source).1 hyD
      linarith
    have hy_not_frontier : E.symm q ∉ frontier D := by
      intro hyfront
      have hzero : q.1 = 0 := by
        simpa [hEq] using (hfront_side (E.symm q) hy_source).1 hyfront
      linarith
    have hy_not_closureD : E.symm q ∉ closure D := by
      rw [closure_eq_self_union_frontier]
      exact fun hy => hy.elim hy_notD hy_not_frontier
    exact hy_not_closureD (closure_mono hC.subset (by simpa [hK] using hyK))
  have hcompl_subset_Ppos : O ∩ Kᶜ ⊆ Ppos := by
    rintro y ⟨hyO, hyKc⟩
    rcases hyO with ⟨q, hqS, rfl⟩
    rcases lt_trichotomy q.1 0 with hq_neg | hq_zero | hq_pos
    · exact False.elim (hyKc (by
        rw [hK]
        exact subset_closure (hPneg_subset_C ⟨q, ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩, rfl⟩)))
    · exact False.elim (hyKc (zero_slice_mem_K q hqS hq_zero))
    · refine ⟨q, ?_, rfl⟩
      exact ⟨⟨hq_pos, hqS.1.2⟩, hqS.2⟩
  have hpatch_eq : O ∩ Kᶜ = Ppos :=
    Subset.antisymm hcompl_subset_Ppos hPpos_subset_compl
  have hPpos_subset_Kc : Ppos ⊆ Kᶜ :=
    fun y hy => (hPpos_subset_compl hy).2
  have hPpos_nonempty : Ppos.Nonempty := by
    refine ⟨E.symm (b / 2, z₀.2), ⟨(b / 2, z₀.2), ?_, rfl⟩⟩
    exact ⟨by constructor <;> linarith, Metric.mem_ball_self hρpos⟩
  rcases preconnected_subset_compl_subset_component
      (K := K) (P := Ppos)
      hPpos_pre hPpos_nonempty hPpos_subset_Kc with
    ⟨V₀, hPpos_subset_V₀⟩
  have hV₀_not_compact : ¬ IsCompact (closure (V₀ : Set X)) := by
    intro hV₀_compact
    have hO_subset :
        O ⊆
          K ∪
            {y : X |
              ∃ W : Set X, IsComponentOf W Kᶜ ∧
                IsCompact (closure W) ∧ y ∈ W} := by
      intro y hyO
      by_cases hyK : y ∈ K
      · exact Or.inl hyK
      · have hyPpos : y ∈ Ppos := by
          simpa [hpatch_eq] using (show y ∈ O ∩ Kᶜ from ⟨hyO, hyK⟩)
        exact Or.inr
          ⟨(V₀ : Set X), V₀.property, hV₀_compact,
            hPpos_subset_V₀ hyPpos⟩
    exact hx_notFill
      (mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset hO_nhds_x hO_subset))
  have hF_subset_V₀c :
      boundedFillingOfComplement K ⊆ (V₀ : Set X)ᶜ := by
    intro y hyF hyV₀
    have hy_decomp :=
      boundedFillingOfComplement_subset_obstacle_union_bounded_components
        K hyF
    rcases hy_decomp with hyK | hy_component
    · exact V₀.property.subset hyV₀ hyK
    · rcases hy_component with ⟨W, hW, hWcompact, hyW⟩
      have hWV₀ : W = (V₀ : Set X) :=
        hW.eq_of_inter_nonempty V₀.property ⟨y, hyW, hyV₀⟩
      exact hV₀_not_compact (by simpa [hWV₀] using hWcompact)
  have hOD_subset_C : O ∩ D ⊆ C := by
    rintro y ⟨hyO, hyD⟩
    rcases hyO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hq_neg : q.1 < 0 := by
      simpa [hEq] using (hD_side (E.symm q) hy_source).1 hyD
    exact hPneg_subset_C ⟨q, ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩, rfl⟩
  have zero_slice_mem_closure_Ppos :
      ∀ q ∈ S, q.1 = 0 → E.symm q ∈ closure Ppos := by
    intro q hqS hq_zero
    have hq_target : q ∈ E.target := hS_target hqS
    have hq_closure_pos : q ∈ closure Spos := by
      change q ∈ closure (Ioo 0 b ×ˢ Metric.ball z₀.2 ρ)
      rw [closure_prod_eq, closure_Ioo h0b.ne]
      exact ⟨⟨by simp [hq_zero],
          le_of_lt (by simpa [hq_zero] using hqS.1.2)⟩,
        subset_closure hqS.2⟩
    have hcont : ContinuousWithinAt E.symm Spos q :=
      (E.continuousOn_symm q hq_target).mono hSpos_target
    exact hcont.mem_closure hq_closure_pos (mapsTo_image E.symm Spos)
  have zero_slice_not_mem_fill :
      ∀ q ∈ S, q.1 = 0 →
        E.symm q ∉ boundedFillingOfComplement K := by
    intro q hqS hq_zero hqF
    have hF_nhds : boundedFillingOfComplement K ∈ 𝓝 (E.symm q) :=
      (boundedFillingOfComplement_isOpen K).mem_nhds hqF
    rcases mem_closure_iff_nhds.mp
        (zero_slice_mem_closure_Ppos q hqS hq_zero)
        (boundedFillingOfComplement K) hF_nhds with
      ⟨z, hzF, hzPpos⟩
    exact hF_subset_V₀c hzF (hPpos_subset_V₀ hzPpos)
  have hC_subset_fill : C ⊆ boundedFillingOfComplement K := by
    exact open_subset_boundedFillingOfComplement_of_subset_obstacle
      hC_open (by
        intro y hyC
        rw [hK]
        exact subset_closure hyC)
  filter_upwards [hO_open.mem_nhds hxO] with y hyO
  constructor
  · intro hyF
    rcases hyO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    rcases lt_trichotomy q.1 0 with hq_neg | hq_zero | hq_pos
    · exact (hD_side (E.symm q) hy_source).2 (by
        simpa [hEq] using hq_neg)
    · exact False.elim (zero_slice_not_mem_fill q hqS hq_zero hyF)
    · have hyPpos : E.symm q ∈ Ppos :=
        ⟨q, ⟨⟨hq_pos, hqS.1.2⟩, hqS.2⟩, rfl⟩
      exact False.elim (hF_subset_V₀c hyF (hPpos_subset_V₀ hyPpos))
  · intro hyD
    exact hC_subset_fill (hOD_subset_C ⟨hyO, hyD⟩)

/--
%%handwave
name:
  The bounded filling agrees locally with the original domain on its boundary
statement:
  Near every frontier point of the bounded filling of the closed pointed
  component, membership in the bounded filling is equivalent to membership in
  the original smooth domain.
proof:
  At a retained boundary point, the local complement side belongs to an
  unbounded complementary component.  The bounded filling therefore keeps
  exactly the original domain side in a small smooth-boundary chart.
-/
theorem smoothBoundaryDomain_boundedFilling_eventually_eq_carrier_near_frontier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    ∀ x ∈ frontier
        (boundedFillingOfComplement
          (closure (connectedComponentIn D.carrier p))),
      ∀ᶠ y in 𝓝 x,
        (y ∈
            boundedFillingOfComplement
              (closure (connectedComponentIn D.carrier p)) ↔
          y ∈ D.carrier) := by
  classical
  intro x hx_frontier
  let C : Set X := connectedComponentIn D.carrier p
  let K : Set X := closure C
  have hxK : x ∈ K := by
    simpa [C, K] using
      boundedFillingOfComplement_frontier_subset_obstacle
        (K := K) isClosed_closure hx_frontier
  have hx_notFill :
      x ∉ boundedFillingOfComplement K := by
    exact
      Set.disjoint_left.mp
        ((disjoint_frontier_iff_isOpen).2
          (boundedFillingOfComplement_isOpen K))
        (by simpa [C, K] using hx_frontier)
  have hx_boundary : x ∈ frontier D.carrier :=
    smoothBoundaryDomain_frontier_boundedFilling_subset_boundary
      D hp hx_frontier
  rcases D.smooth_boundary x hx_boundary with
    ⟨e, _he, hxsource, r, hrsmooth, dr, hrderiv, hdrnz, hlocal⟩
  rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, hxN⟩
  have hprops_x := hNsub hxN
  have hxzero : r (e x) = 0 := (hprops_x.2.2).mp hx_boundary
  rcases smoothPlaneRegularZeroSet_implicitCoord_fst_eq
      hrsmooth.contDiffAt hrderiv hdrnz hxzero with
    ⟨Φ, hxΦ, hΦfst, _hΦzero⟩
  let eN : OpenPartialHomeomorph X ℂ := e.restrOpen N hNopen
  let E : OpenPartialHomeomorph X (ℝ × dr.ker) := eN.trans Φ
  have hxE : x ∈ E.source := by
    change x ∈ (eN.trans Φ).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by simpa [eN] using ⟨hxsource, hxN⟩, by simpa [eN] using hxΦ⟩
  have hD_side :
      ∀ y ∈ E.source, y ∈ D.carrier ↔ (E y).1 < 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.1
  have hfront_side :
      ∀ y ∈ E.source, y ∈ frontier D.carrier ↔ (E y).1 = 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.2
  have hC : IsComponentOf C D.carrier :=
    smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  have hC_open : IsOpen C := by
    simpa [C] using smoothBoundaryDomain_pointedComponent_isOpen D p
  simpa [C, K] using
    signedBoundaryChart_boundedFilling_eventually_eq_domain_of_not_mem
      (D := D.carrier) (C := C) (K := K)
      hC_open hC rfl ⟨x, hx_boundary⟩ hxK hx_notFill
      E hxE hD_side hfront_side

/--
%%handwave
name:
  The bounded filling has smooth boundary
statement:
  The bounded filling of the closed pointed component of a smooth relatively
  compact domain has smooth boundary.
proof:
  Along its frontier the bounded filling agrees locally with the original
  smooth domain, so the original smooth boundary charts apply.
-/
theorem smoothBoundaryDomain_boundedFilling_hasSmoothBoundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    HasSmoothBoundary
      (boundedFillingOfComplement
        (closure (connectedComponentIn D.carrier p))) := by
  intro x hx_frontier
  have hx_boundary : x ∈ frontier D.carrier :=
    smoothBoundaryDomain_frontier_boundedFilling_subset_boundary
      D hp hx_frontier
  have hmem :
      ∀ᶠ y in 𝓝 x,
        (y ∈
            boundedFillingOfComplement
              (closure (connectedComponentIn D.carrier p)) ↔
          y ∈ D.carrier) :=
    smoothBoundaryDomain_boundedFilling_eventually_eq_carrier_near_frontier
      D hp x hx_frontier
  have hfrontier :
      ∀ᶠ y in 𝓝 x,
        (y ∈ frontier
            (boundedFillingOfComplement
              (closure (connectedComponentIn D.carrier p))) ↔
          y ∈ frontier D.carrier) :=
    eventually_frontier_congr_of_eventually_mem_iff hmem
  exact hasSmoothBoundary_localData_of_eventually_mem_and_frontier_iff
    D.smooth_boundary hx_boundary hmem hfrontier

/--
%%handwave
name:
  The bounded filling is a smooth relatively compact domain
statement:
  The bounded filling of the closed pointed component is the carrier of a
  smooth relatively compact domain.
proof:
  Use the bounded filling as the carrier.  It is open, contains the base
  point, has compact closure, and has smooth boundary by the preceding
  bounded-filling results, so these data define the required domain.
-/
theorem smoothBoundaryDomain_exists_domain_with_boundedFilling_carrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    ∃ Dhat : SmoothBoundaryDomain X,
      Dhat.carrier =
        boundedFillingOfComplement
          (closure (connectedComponentIn D.carrier p)) := by
  refine ⟨
    { carrier :=
        boundedFillingOfComplement
          (closure (connectedComponentIn D.carrier p))
      isOpen :=
        boundedFillingOfComplement_isOpen
          (closure (connectedComponentIn D.carrier p))
      nonempty :=
        ⟨p, smoothBoundaryDomain_base_mem_boundedFilling D hp⟩
      compact_closure :=
        smoothBoundaryDomain_boundedFilling_compact_closure D hp
      smooth_boundary :=
        smoothBoundaryDomain_boundedFilling_hasSmoothBoundary D hp },
    rfl⟩

/--
%%handwave
name:
  Closed pointed-component points join inside the bounded filling
statement:
  Every point of the closed pointed component that lies in the bounded filling
  can be joined to the base point by a path contained in the bounded filling.
proof:
  Interior points are joined inside the pointed component.  Boundary points
  are reached from nearby interior points because the bounded filling is open
  and the surface is locally path connected.
-/
theorem smoothBoundaryDomain_pointedComponent_closure_joinedIn_boundedFilling
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p x : X} (hp : p ∈ D.carrier)
    (hx_closure : x ∈ closure (connectedComponentIn D.carrier p))
    (hx_fill :
      x ∈ boundedFillingOfComplement
        (closure (connectedComponentIn D.carrier p))) :
    JoinedIn
      (boundedFillingOfComplement
        (closure (connectedComponentIn D.carrier p))) p x := by
  let C : Set X := connectedComponentIn D.carrier p
  let F : Set X := boundedFillingOfComplement (closure C)
  have hC_subset_F : C ⊆ F := by
    simpa [C, F] using
      smoothBoundaryDomain_pointedComponent_subset_boundedFilling D p
  have hpC : p ∈ C := by
    simpa [C] using smoothBoundaryDomain_pointedComponent_mem D hp
  have hpathC : IsPathConnected C := by
    simpa [C] using smoothBoundaryDomain_pointedComponent_isPathConnected D hp
  by_cases hxC : x ∈ C
  · exact (hpathC.joinedIn p hpC x hxC).mono hC_subset_F
  · have hC_open : IsOpen C := by
      simpa [C] using smoothBoundaryDomain_pointedComponent_isOpen D p
    have hx_frontier : x ∈ frontier C := by
      rw [frontier, hC_open.interior_eq]
      exact ⟨by simpa [C] using hx_closure, hxC⟩
    haveI : LocPathConnectedSpace X :=
      ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
    have hF_open : IsOpen F := by
      simpa [F] using
        boundedFillingOfComplement_isOpen (closure C)
    have hF_nhds : F ∈ 𝓝 x :=
      hF_open.mem_nhds (by simpa [C, F] using hx_fill)
    have hpathComponent_nhds : pathComponentIn F x ∈ 𝓝 x :=
      pathComponentIn_mem_nhds hF_nhds
    rcases mem_closure_iff_nhds.mp
        (frontier_subset_closure hx_frontier)
        (pathComponentIn F x) hpathComponent_nhds with
      ⟨y, hy_path, hyC⟩
    have hpy : JoinedIn F p y :=
      (hpathC.joinedIn p hpC y hyC).mono hC_subset_F
    exact hpy.trans hy_path.symm

/--
%%handwave
name:
  Bounded complementary attachments lie in the bounded filling
statement:
  In a smooth-boundary chart, if a complementary component with compact
  closure accumulates at a point of the closed pointed component, then that
  attachment point belongs to the bounded filling.
proof:
  A small product chart splits into the pointed side and the complementary
  side.  The complementary side is contained in the given compact-closure
  component, so the whole small chart lies in the obstacle together with that
  bounded component.
-/
theorem signedBoundaryChart_bounded_attachment_mem_boundedFilling
    {X F : Type} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D C K V : Set X} (hC : IsComponentOf C D)
    (hK : K = closure C)
    (hVcomp : IsComponentOf V Kᶜ) (hVcompact : IsCompact (closure V))
    (x : frontier D) (hxK : (x : X) ∈ K) (hxVcl : (x : X) ∈ closure V)
    (E : OpenPartialHomeomorph X (ℝ × F))
    (hxE : (x : X) ∈ E.source)
    (hD_side : ∀ y ∈ E.source, y ∈ D ↔ (E y).1 < 0)
    (hfront_side : ∀ y ∈ E.source, y ∈ frontier D ↔ (E y).1 = 0) :
    (x : X) ∈ boundedFillingOfComplement K := by
  classical
  let z₀ : ℝ × F := E (x : X)
  have hz₀_target : z₀ ∈ E.target := by
    simpa [z₀] using E.map_source hxE
  have hz₀_fst : z₀.1 = 0 := by
    simpa [z₀] using (hfront_side (x : X) hxE).mp x.2
  rcases mem_nhds_prod_iff.mp (E.open_target.mem_nhds hz₀_target) with
    ⟨U₀, hU₀, V₀, hV₀, hU₀V₀⟩
  have hz₀_fst' : (E (x : X)).1 = 0 := by
    simpa [z₀] using hz₀_fst
  have hU₀_zero : U₀ ∈ 𝓝 (0 : ℝ) := by
    simpa [hz₀_fst'] using hU₀
  rcases mem_nhds_iff_exists_Ioo_subset.mp hU₀_zero with
    ⟨a, b, h0ab, hIooU₀⟩
  rcases Metric.nhds_basis_ball.mem_iff.mp hV₀ with
    ⟨ρ, hρpos, hρV₀⟩
  have ha0 : a < 0 := h0ab.1
  have h0b : 0 < b := h0ab.2
  let S : Set (ℝ × F) := Ioo a b ×ˢ Metric.ball z₀.2 ρ
  let Sneg : Set (ℝ × F) := Ioo a 0 ×ˢ Metric.ball z₀.2 ρ
  let Spos : Set (ℝ × F) := Ioo 0 b ×ˢ Metric.ball z₀.2 ρ
  let O : Set X := E.symm '' S
  let Pneg : Set X := E.symm '' Sneg
  let Ppos : Set X := E.symm '' Spos
  have hS_target : S ⊆ E.target := by
    intro q hq
    exact hU₀V₀ ⟨hIooU₀ hq.1, hρV₀ hq.2⟩
  have hSneg_subset_S : Sneg ⊆ S := by
    intro q hq
    exact ⟨⟨hq.1.1, hq.1.2.trans h0b⟩, hq.2⟩
  have hSpos_subset_S : Spos ⊆ S := by
    intro q hq
    exact ⟨⟨ha0.trans hq.1.1, hq.1.2⟩, hq.2⟩
  have hSneg_target : Sneg ⊆ E.target := hSneg_subset_S.trans hS_target
  have hSpos_target : Spos ⊆ E.target := hSpos_subset_S.trans hS_target
  have hS_open : IsOpen S := by
    exact isOpen_Ioo.prod Metric.isOpen_ball
  have hO_open : IsOpen O := by
    exact E.isOpen_image_symm_of_subset_target hS_open hS_target
  have hz₀S : z₀ ∈ S := by
    exact ⟨by simpa [hz₀_fst] using h0ab,
      Metric.mem_ball_self hρpos⟩
  have hxO : (x : X) ∈ O := by
    refine ⟨z₀, hz₀S, ?_⟩
    simpa [z₀] using E.left_inv hxE
  have hO_nhds_x : O ∈ 𝓝 (x : X) := hO_open.mem_nhds hxO
  have hx_closureC : (x : X) ∈ closure C := by
    simpa [hK] using hxK
  have hO_meets_C : (O ∩ C).Nonempty :=
    mem_closure_iff_nhds.mp hx_closureC O hO_nhds_x
  have hSneg_pre : IsPreconnected Sneg := by
    exact ((convex_Ioo a (0 : ℝ)).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hSpos_pre : IsPreconnected Spos := by
    exact ((convex_Ioo (0 : ℝ) b).prod (convex_ball z₀.2 ρ)).isPreconnected
  have hPneg_pre : IsPreconnected Pneg := by
    exact hSneg_pre.image E.symm (E.continuousOn_symm.mono hSneg_target)
  have hPpos_pre : IsPreconnected Ppos := by
    exact hSpos_pre.image E.symm (E.continuousOn_symm.mono hSpos_target)
  have hPneg_subset_D : Pneg ⊆ D := by
    rintro y ⟨q, hq, rfl⟩
    have hq_target : q ∈ E.target := hSneg_target hq
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    exact (hD_side (E.symm q) hy_source).2 (by
      simpa [hEq] using hq.1.2)
  have hPneg_meets_C : (C ∩ Pneg).Nonempty := by
    rcases hO_meets_C with ⟨c, hcO, hcC⟩
    rcases hcO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hc_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hcD : E.symm q ∈ D := hC.subset hcC
    have hq_neg : q.1 < 0 := by
      simpa [hEq] using (hD_side (E.symm q) hc_source).1 hcD
    refine ⟨E.symm q, hcC, ⟨q, ?_, rfl⟩⟩
    exact ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩
  have hPneg_subset_C : Pneg ⊆ C :=
    hC.2.2.2 Pneg hPneg_subset_D hPneg_pre hPneg_meets_C
  have hPpos_subset_compl : Ppos ⊆ O ∩ Kᶜ := by
    rintro y ⟨q, hqpos, rfl⟩
    have hqS : q ∈ S := hSpos_subset_S hqpos
    have hq_target : q ∈ E.target := hSpos_target hqpos
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    have hq_pos : 0 < q.1 := hqpos.1.1
    refine ⟨⟨q, hqS, rfl⟩, ?_⟩
    intro hyK
    have hy_notD : E.symm q ∉ D := by
      intro hyD
      have hlt : q.1 < 0 := by
        simpa [hEq] using (hD_side (E.symm q) hy_source).1 hyD
      linarith
    have hy_not_frontier : E.symm q ∉ frontier D := by
      intro hyfront
      have hzero : q.1 = 0 := by
        simpa [hEq] using (hfront_side (E.symm q) hy_source).1 hyfront
      linarith
    have hy_not_closureD : E.symm q ∉ closure D := by
      rw [closure_eq_self_union_frontier]
      exact fun hy => hy.elim hy_notD hy_not_frontier
    exact hy_not_closureD (closure_mono hC.subset (by simpa [hK] using hyK))
  have hcompl_subset_Ppos : O ∩ Kᶜ ⊆ Ppos := by
    rintro y ⟨hyO, hyKc⟩
    rcases hyO with ⟨q, hqS, rfl⟩
    rcases lt_trichotomy q.1 0 with hq_neg | hq_zero | hq_pos
    · exact False.elim (hyKc (by
        rw [hK]
        exact subset_closure (hPneg_subset_C ⟨q, ⟨⟨hqS.1.1, hq_neg⟩, hqS.2⟩, rfl⟩)))
    · have hq_target : q ∈ E.target := hS_target hqS
      have hq_closure_neg : q ∈ closure Sneg := by
        change q ∈ closure (Ioo a 0 ×ˢ Metric.ball z₀.2 ρ)
        rw [closure_prod_eq, closure_Ioo ha0.ne]
        exact ⟨⟨le_of_lt (by simpa [hq_zero] using hqS.1.1),
            by simp [hq_zero]⟩,
          subset_closure hqS.2⟩
      have hcont : ContinuousWithinAt E.symm Sneg q :=
        (E.continuousOn_symm q hq_target).mono hSneg_target
      have hy_closure_Pneg : E.symm q ∈ closure Pneg :=
        hcont.mem_closure hq_closure_neg (mapsTo_image E.symm Sneg)
      exact False.elim (hyKc (by
        rw [hK]
        exact closure_mono hPneg_subset_C hy_closure_Pneg))
    · refine ⟨q, ?_, rfl⟩
      exact ⟨⟨hq_pos, hqS.1.2⟩, hqS.2⟩
  have hpatch_eq : O ∩ Kᶜ = Ppos :=
    Subset.antisymm hcompl_subset_Ppos hPpos_subset_compl
  have hPpos_subset_Kc : Ppos ⊆ Kᶜ :=
    fun y hy => (hPpos_subset_compl hy).2
  have hV_meets_Ppos : (V ∩ Ppos).Nonempty := by
    rcases mem_closure_iff_nhds.mp hxVcl O hO_nhds_x with
      ⟨z, hzO, hzV⟩
    have hzKc : z ∈ Kᶜ := hVcomp.subset hzV
    have hzPpos : z ∈ Ppos := by
      simpa [hpatch_eq] using (show z ∈ O ∩ Kᶜ from ⟨hzO, hzKc⟩)
    exact ⟨z, hzV, hzPpos⟩
  have hPpos_subset_V : Ppos ⊆ V :=
    hVcomp.2.2.2 Ppos hPpos_subset_Kc hPpos_pre hV_meets_Ppos
  have hO_subset_fill_base :
      O ⊆
        K ∪
          {y : X |
            ∃ W : Set X, IsComponentOf W Kᶜ ∧
              IsCompact (closure W) ∧ y ∈ W} := by
    intro y hyO
    by_cases hyK : y ∈ K
    · exact Or.inl hyK
    · have hyPpos : y ∈ Ppos := by
        simpa [hpatch_eq] using (show y ∈ O ∩ Kᶜ from ⟨hyO, hyK⟩)
      exact Or.inr ⟨V, hVcomp, hVcompact, hPpos_subset_V hyPpos⟩
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset hO_nhds_x hO_subset_fill_base)

/--
%%handwave
name:
  Bounded component frontier attachments lie in the bounded filling
statement:
  If a compact-closure complementary component touches the closed pointed
  component, then the touching point lies in the bounded filling.
proof:
  The touching point lies on the boundary of the closed pointed component and
  hence on the smooth boundary of the original domain.  A regular boundary
  chart splits a small neighborhood into the domain side and its complement.
  Maximality of the two relevant complementary components places the two
  half-neighborhoods in the pointed component and the bounded component,
  respectively.  Thus the whole neighborhood lies in their union, so the
  touching point belongs to the interior defining the bounded filling.
-/
theorem smoothBoundaryDomain_bounded_component_frontier_attachment_mem_boundedFilling
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) {V : Set X}
    (hV :
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ)
    (hVcompact : IsCompact (closure V)) {a : X}
    (ha_frontier : a ∈ frontier V)
    (ha_closure : a ∈ closure (connectedComponentIn D.carrier p)) :
    a ∈ boundedFillingOfComplement
      (closure (connectedComponentIn D.carrier p)) := by
  classical
  let C : Set X := connectedComponentIn D.carrier p
  let K : Set X := closure C
  haveI : LocPathConnectedSpace X :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
  haveI : LocallyConnectedSpace X := locPathConnectedSpace_locallyConnectedSpace
  have ha_closureKc : a ∈ closure Kᶜ := by
    exact closure_mono (by simpa [K, C] using hV.subset)
      (frontier_subset_closure ha_frontier)
  have ha_frontierK : a ∈ frontier K := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure (by simpa [K, C] using ha_closure), ha_closureKc⟩
  have ha_boundary : a ∈ frontier D.carrier := by
    simpa [C, K] using
      smoothBoundaryDomain_pointedComponent_closure_frontier_subset_boundary
        D hp ha_frontierK
  rcases D.smooth_boundary a ha_boundary with
    ⟨e, _he, hasource, r, hrsmooth, dr, hrderiv, hdrnz, hlocal⟩
  rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, haN⟩
  have hprops_a := hNsub haN
  have hazero : r (e a) = 0 := (hprops_a.2.2).mp ha_boundary
  rcases smoothPlaneRegularZeroSet_implicitCoord_fst_eq
      hrsmooth.contDiffAt hrderiv hdrnz hazero with
    ⟨Φ, haΦ, hΦfst, _hΦzero⟩
  let eN : OpenPartialHomeomorph X ℂ := e.restrOpen N hNopen
  let E : OpenPartialHomeomorph X (ℝ × dr.ker) := eN.trans Φ
  have haE : a ∈ E.source := by
    change a ∈ (eN.trans Φ).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by simpa [eN] using ⟨hasource, haN⟩, by simpa [eN] using haΦ⟩
  have hD_side :
      ∀ y ∈ E.source, y ∈ D.carrier ↔ (E y).1 < 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.1
  have hfront_side :
      ∀ y ∈ E.source, y ∈ frontier D.carrier ↔ (E y).1 = 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.2
  have hC : IsComponentOf C D.carrier :=
    smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  have hVcomp : IsComponentOf V Kᶜ := by
    simpa [C, K] using hV
  simpa [C, K] using
    signedBoundaryChart_bounded_attachment_mem_boundedFilling
      (D := D.carrier) (C := C) (K := K) (V := V)
      hC rfl hVcomp (by simpa [C, K] using hVcompact)
      ⟨a, ha_boundary⟩
      (by simpa [C, K] using ha_closure)
      (frontier_subset_closure ha_frontier)
      E haE hD_side hfront_side

/--
%%handwave
name:
  Bounded complementary components join to the pointed closure
statement:
  Every point in a compact-closure complementary component can be joined
  inside the bounded filling to a point of the closed pointed component.
proof:
  Choose a frontier point of the bounded complementary component that lies in
  the closed pointed component.  The preceding attachment result puts this
  point in the open bounded filling, while the whole complementary component
  also lies in the filling and is path connected.  A small path component of
  the filling near the attachment meets the complementary component; joining
  inside the component and then inside that path component gives the required
  path.
-/
theorem smoothBoundaryDomain_bounded_component_joinedIn_pointedComponent_closure_in_boundedFilling
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) {V : Set X}
    (hV :
      IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ)
    (hVcompact : IsCompact (closure V)) :
    ∀ x ∈ V,
      ∃ a : X,
        a ∈ closure (connectedComponentIn D.carrier p) ∧
          a ∈ boundedFillingOfComplement
            (closure (connectedComponentIn D.carrier p)) ∧
            JoinedIn
              (boundedFillingOfComplement
                (closure (connectedComponentIn D.carrier p))) x a := by
  intro x hxV
  let K : Set X := closure (connectedComponentIn D.carrier p)
  let F : Set X := boundedFillingOfComplement K
  haveI : LocPathConnectedSpace X :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
  haveI : LocallyConnectedSpace X := locPathConnectedSpace_locallyConnectedSpace
  rcases
      smoothBoundaryDomain_nonExterior_component_frontier_meets_pointedComponent_closure
        D hp hV with
    ⟨a, ha_frontier, ha_closure⟩
  have ha_fill : a ∈ F := by
    simpa [K, F] using
      smoothBoundaryDomain_bounded_component_frontier_attachment_mem_boundedFilling
        D hp hV hVcompact ha_frontier ha_closure
  have hV_subset_F : V ⊆ F := by
    simpa [K, F] using
      hV.subset_boundedFillingOfComplement_of_closure_compact
        isClosed_closure hVcompact
  have hV_path : IsPathConnected V :=
    hV.isPathConnected_of_compl_isClosed isClosed_closure
  have hF_open : IsOpen F := by
    simpa [F] using boundedFillingOfComplement_isOpen K
  have hF_nhds : F ∈ 𝓝 a :=
    hF_open.mem_nhds ha_fill
  have hpathComponent_nhds : pathComponentIn F a ∈ 𝓝 a :=
    pathComponentIn_mem_nhds hF_nhds
  rcases mem_closure_iff_nhds.mp
      (frontier_subset_closure ha_frontier)
      (pathComponentIn F a) hpathComponent_nhds with
    ⟨y, hy_path, hyV⟩
  have hxy : JoinedIn F x y :=
    (hV_path.joinedIn x hxV y hyV).mono hV_subset_F
  exact ⟨a, ha_closure, by simpa [K, F] using ha_fill,
    by simpa [K, F] using hxy.trans hy_path.symm⟩

/--
%%handwave
name:
  Bounded fillings are path connected
statement:
  The bounded filling of the closed pointed component is path connected.
proof:
  The pointed component is path connected.  Each bounded complementary
  component attaches to the pointed closure through a smooth collar, so
  adjoining all bounded components preserves one path component.
-/
theorem smoothBoundaryDomain_boundedFilling_pathConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier) :
    PathConnectedSpace
      (boundedFillingOfComplement
        (closure (connectedComponentIn D.carrier p))) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  let K : Set X := closure (connectedComponentIn D.carrier p)
  let F : Set X := boundedFillingOfComplement K
  refine isPathConnected_of_forall_joinedIn_base
    (by
      simpa [K, F] using smoothBoundaryDomain_base_mem_boundedFilling D hp)
    ?_
  intro x hxF
  have hx_decomp :
      x ∈ K ∪
        {y : X |
          ∃ V : Set X, IsComponentOf V Kᶜ ∧
            IsCompact (closure V) ∧ y ∈ V} := by
    exact boundedFillingOfComplement_subset_obstacle_union_bounded_components
      K (by simpa [F] using hxF)
  rcases hx_decomp with hxK | hx_component
  · simpa [K, F] using
      smoothBoundaryDomain_pointedComponent_closure_joinedIn_boundedFilling
        D hp (by simpa [K] using hxK) (by simpa [K, F] using hxF)
  · rcases hx_component with ⟨V, hV, hVcompact, hxV⟩
    rcases
        smoothBoundaryDomain_bounded_component_joinedIn_pointedComponent_closure_in_boundedFilling
          D hp (by simpa [K] using hV) hVcompact x hxV with
      ⟨a, haK, haF, hxa⟩
    have hpa :
        JoinedIn F p a := by
      simpa [K, F] using
        smoothBoundaryDomain_pointedComponent_closure_joinedIn_boundedFilling
          D hp (by simpa [K] using haK) (by simpa [K, F] using haF)
    exact hpa.trans hxa.symm

/--
%%handwave
name:
  Bounded fillings have no compact complementary components
statement:
  Every component of the complement of the closure of the bounded filling has
  noncompact closure.
proof:
  Let \(F\) be the bounded filling of \(\overline C\), where \(C\) is the
  pointed component.  Since \(C\subset F\), the set \(\overline C\) lies in
  \(\overline F\).  A component \(V\) of \(X\setminus\overline F\) therefore
  lies in \(X\setminus\overline C\).  If \(W\) is the component of
  \(X\setminus\overline C\) containing \(V\), then \(W\) cannot meet
  \(\overline F\): any such meeting would force \(W\) to meet \(F\), hence to
  be one of the compact complementary components already filled into \(F\).
  Thus \(W\) is itself contained in \(X\setminus\overline F\), and maximality
  gives \(W=V\).  A compact closure for \(V\) would then put \(W\) inside the
  bounded filling, contradicting \(V\subset X\setminus\overline F\).
-/
theorem smoothBoundaryDomain_boundedFilling_complement_components_noCompactClosure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (_hp : p ∈ D.carrier) :
    ∀ V : Set X,
      IsComponentOf V
        (closure
          (boundedFillingOfComplement
            (closure (connectedComponentIn D.carrier p))))ᶜ →
        ¬ IsCompact (closure V) := by
  classical
  intro V hV hVcompact
  let C : Set X := connectedComponentIn D.carrier p
  let K : Set X := closure C
  let F : Set X := boundedFillingOfComplement K
  haveI : LocPathConnectedSpace X :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
  haveI : LocallyConnectedSpace X := locPathConnectedSpace_locallyConnectedSpace
  have hC_subset_F : C ⊆ F := by
    simpa [C, K, F] using
      smoothBoundaryDomain_pointedComponent_subset_boundedFilling D p
  have hK_subset_closureF : K ⊆ closure F := by
    simpa [K] using closure_mono hC_subset_F
  rcases hV.2.1 with ⟨x₀, hx₀V⟩
  have hx₀_not_closureF : x₀ ∉ closure F := by
    exact hV.1 (by simpa [F] using hx₀V)
  have hx₀Kc : x₀ ∈ Kᶜ := by
    intro hx₀K
    exact hx₀_not_closureF (hK_subset_closureF hx₀K)
  let W : Set X := connectedComponentIn Kᶜ x₀
  have hx₀W : x₀ ∈ W := by
    dsimp [W]
    exact mem_connectedComponentIn hx₀Kc
  have hWcomp : IsComponentOf W Kᶜ := by
    dsimp [W]
    exact isComponentOf_connectedComponentIn hx₀Kc
  have hV_subset_Kc : V ⊆ Kᶜ := by
    intro y hyV hyK
    exact hV.1 (by simpa [F] using hyV) (hK_subset_closureF hyK)
  have hV_subset_W : V ⊆ W :=
    hV.2.2.1.subset_connectedComponentIn hx₀V hV_subset_Kc
  have hW_open : IsOpen W :=
    hWcomp.isOpen_of_isOpen isClosed_closure.isOpen_compl
  have hW_disjoint_closureF : Disjoint W (closure F) := by
    refine disjoint_left.mpr ?_
    intro y hyW hy_closureF
    have hW_nhds : W ∈ 𝓝 y := hW_open.mem_nhds hyW
    rcases mem_closure_iff_nhds.mp hy_closureF W hW_nhds with
      ⟨z, hzW, hzF⟩
    have hz_union :
        z ∈
          K ∪
            {u : X |
              ∃ U : Set X, IsComponentOf U Kᶜ ∧
                IsCompact (closure U) ∧ u ∈ U} := by
      exact boundedFillingOfComplement_subset_obstacle_union_bounded_components
        K (by simpa [F] using hzF)
    rcases hz_union with hzK | hz_component
    · exact hWcomp.subset hzW hzK
    · rcases hz_component with ⟨U, hUcomp, hUcompact, hzU⟩
      have hUW : U = W :=
        hUcomp.eq_of_inter_nonempty hWcomp ⟨z, hzU, hzW⟩
      have hWcompact : IsCompact (closure W) := by
        simpa [hUW] using hUcompact
      have hW_subset_F : W ⊆ F := by
        simpa [F] using
          hWcomp.subset_boundedFillingOfComplement_of_closure_compact
            isClosed_closure hWcompact
      exact hx₀_not_closureF (subset_closure (hW_subset_F hx₀W))
  have hW_subset_closureFc : W ⊆ (closure F)ᶜ := by
    intro y hyW hy_closureF
    exact Set.disjoint_left.mp hW_disjoint_closureF hyW hy_closureF
  have hW_subset_V : W ⊆ V := by
    exact hV.2.2.2 W
      (by
        intro y hyW
        simpa [F] using hW_subset_closureFc hyW)
      hWcomp.isPreconnected
      ⟨x₀, hx₀V, hx₀W⟩
  have hVW : V = W := Subset.antisymm hV_subset_W hW_subset_V
  have hWcompact : IsCompact (closure W) := by
    simpa [hVW] using hVcompact
  have hW_subset_F : W ⊆ F := by
    simpa [F] using
      hWcomp.subset_boundedFillingOfComplement_of_closure_compact
        isClosed_closure hWcompact
  exact hx₀_not_closureF (subset_closure (hW_subset_F hx₀W))









/--
%%handwave
name:
  Continuous retraction onto a subset
statement:
  A subset \(A\) is a continuous retract of an ambient space when there is a
  continuous map from the ambient space to \(A\) whose restriction to \(A\) is
  the identity.
-/
def HasContinuousRetractionOntoSet
    {X : Type} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ ρ : C(X, A), ∀ x : A, ρ x = x

/-- The inclusion of one subset into another as a morphism of topological spaces. -/
def subsetInclusionTopCat
    {X : Type} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom
    ⟨fun x : A => ⟨(x : X), hAB x.2⟩,
      Continuous.subtype_mk continuous_subtype_val (fun x => hAB x.2)⟩

/--
%%handwave
name:
  Vanishing real singular cohomology passes to continuous retracts
statement:
  If \(A\) is a continuous retract of \(X\) and \(H^n(X;\mathbb R)=0\), then
  \(H^n(A;\mathbb R)=0\).
proof:
  Write \(i:A\to X\) for the inclusion and \(r:X\to A\) for the retraction.
  Since \(r\circ i=\mathrm{id}_A\), contravariant functoriality makes the
  identity of \(H^n(A;\mathbb R)\) factor through \(H^n(X;\mathbb R)\).
-/
theorem realSingularCohomology_isZero_of_continuous_retract
    {X : Type} [TopologicalSpace X] (A : Set X)
    (hretract : HasContinuousRetractionOntoSet A) (n : ℕ)
    (hX :
      CategoryTheory.Limits.IsZero
        (JJMath.Cohomology.RealSingularCohomology (TopCat.of X) n)) :
    CategoryTheory.Limits.IsZero
      (JJMath.Cohomology.RealSingularCohomology (TopCat.of A) n) := by
  rcases hretract with ⟨ρ, hρ⟩
  let i : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨fun x : A => (x : X), continuous_subtype_val⟩
  let r : TopCat.of X ⟶ TopCat.of A :=
    TopCat.ofHom ρ
  refine
    JJMath.Cohomology.singularCohomology_isZero_of_retract
      ℝ i r ?_ n hX
  ext x
  simpa [i, r] using congrArg Subtype.val (hρ x)

/--
%%handwave
name:
  Continuous retraction from a component closure to its boundary
statement:
  The closure of a complementary component retracts continuously to its
  boundary if there is a continuous map from the closure to the frontier which
  fixes every frontier point.
-/
def HasContinuousRetractionFromClosureOntoFrontier
    {X : Type} [TopologicalSpace X] (V : Set X) : Prop :=
  ∃ ρ : C(closure V, frontier V),
    ∀ x : frontier V, ρ ⟨x.1, frontier_subset_closure x.2⟩ = x

/-- The open subset underlying a smooth boundary domain. -/
abbrev smoothBoundaryDomainOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (Dhat : SmoothBoundaryDomain X) :
    TopologicalSpace.Opens X :=
  ⟨Dhat.carrier, Dhat.isOpen⟩

/-- The inclusion of a smooth boundary domain into its closure. -/
def smoothBoundaryDomainOpenToClosure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (Dhat : SmoothBoundaryDomain X) :
    TopCat.of (smoothBoundaryDomainOpen Dhat) ⟶
      TopCat.of (closure Dhat.carrier) :=
  subsetInclusionTopCat
    (show (smoothBoundaryDomainOpen Dhat : Set X) ⊆ closure Dhat.carrier by
      exact subset_closure)

/--
%%handwave
name:
  The closure collar pushes back into the open domain up to homotopy
statement:
  The closure of a smooth boundary domain admits a continuous map back to the
  open domain such that inclusion followed by this map is homotopic to the
  identity of the open domain.
proof:
  Use a smooth collar of the boundary and push boundary-collar coordinates
  slightly inward, leaving the deeper interior fixed up to homotopy.
-/
def HasHomotopyRetractionFromClosureOntoOpenCarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (Dhat : SmoothBoundaryDomain X) : Prop :=
  ∃ ρ : C(closure Dhat.carrier, smoothBoundaryDomainOpen Dhat),
    (ρ.comp (smoothBoundaryDomainOpenToClosure Dhat).hom).Homotopic
      (ContinuousMap.id (smoothBoundaryDomainOpen Dhat))

/--
%%handwave
name:
  Empty boundary needs no collar push
statement:
  If a smooth boundary domain has empty frontier, its closure is already its
  open carrier, so the identity gives the required closure-to-interior
  homotopy retraction.
proof:
  The closure is the union of the carrier and its frontier.  With empty
  frontier this is the carrier itself, and the resulting map is the identity.
-/
theorem smoothBoundaryDomain_closure_homotopy_retracts_to_open_carrier_of_frontier_eq_empty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (hfrontier : frontier Dhat.carrier = ∅) :
    HasHomotopyRetractionFromClosureOntoOpenCarrier Dhat := by
  have hclosure : closure Dhat.carrier = Dhat.carrier := by
    rw [closure_eq_self_union_frontier, hfrontier, union_empty]
  let ρ : C(closure Dhat.carrier, smoothBoundaryDomainOpen Dhat) :=
    ⟨fun x => ⟨(x : X), by simpa [hclosure] using x.2⟩,
      Continuous.subtype_mk continuous_subtype_val
        (fun x => by simpa [hclosure] using x.2)⟩
  refine ⟨ρ, ?_⟩
  convert ContinuousMap.Homotopic.refl
    (ContinuousMap.id (smoothBoundaryDomainOpen Dhat)) using 1

/--
%%handwave
name:
  Annular crossing cycles cannot occur on a simply connected surface
statement:
  On a simply connected Riemann surface, a transverse crossing of an annular
  collar cannot be closed by a smooth chain outside the compact middle of the
  collar.
proof:
  The compactly supported annular one-form has period one on the crossing and
  zero on the return chain.  Their sum would therefore be a cycle with
  nonzero period, contradicting the vanishing of first de Rham cohomology.
-/
theorem simplyConnected_surface_no_annularCollar_return_chain_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    [IsManifold SurfaceRealModel ∞ X]
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (returning : JJMath.Manifold.SingularChain
      (I := SurfaceRealModel)
      (M := JJMath.Manifold.annularCollarExteriorOpen
        SurfaceRealModel U phi) 1 ∞)
    (hboundary : JJMath.Manifold.SingularChain.openInclusion
        (I := SurfaceRealModel)
        (JJMath.Manifold.annularCollarExteriorOpen
          SurfaceRealModel U phi)
        (JJMath.Manifold.boundary (I := SurfaceRealModel) returning) =
      -JJMath.Manifold.boundary (I := SurfaceRealModel)
        (Finsupp.single
          ((JJMath.Manifold.annularCollarTransverseSimplex
              SurfaceRealModel U phi z a b).openInclusion
            (I := SurfaceRealModel) U) (1 : ℤ))) :
    False := by
  have hnot :=
    JJMath.Manifold.not_subsingleton_deRhamH1_of_annularCollar_return_chain_boundary
      SurfaceRealModel U phi z ha hb returning hboundary
  exact hnot (simplyConnected_surface_deRhamH1_zero (X := X))

/--
%%handwave
name:
  Simply connected smooth domains have vanishing first de Rham cohomology
statement:
  A simply connected smooth boundary domain in a Riemann surface has
  trivial first real de Rham cohomology.
proof:
  Regard the domain as an open Riemann surface.  Integrating a closed one-form
  from a basepoint is independent of the chosen smooth path by a finite-grid
  homotopy argument, and therefore gives a global primitive.
-/
theorem SmoothBoundaryDomain.deRhamH1Zero_of_simplyConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    [SimplyConnectedSpace Dhat.carrier] :
    Dhat.deRhamH1Zero := by
  let U : TopologicalSpace.Opens X := ⟨Dhat.carrier, Dhat.isOpen⟩
  letI : SimplyConnectedSpace U := by infer_instance
  have hne : (U : Set X).Nonempty := by
    simpa [U] using Dhat.nonempty
  have hpre : IsPreconnected (U : Set X) :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  letI : RiemannSurface U :=
    riemannSurface_openSubset U hne hpre
  simpa [SmoothBoundaryDomain.deRhamH1, U] using
    (simplyConnected_surface_deRhamH1_zero (X := U))

/--
%%handwave
name:
  A simply connected pointed exhaustion has vanishing first cohomology
statement:
  Forgetting simple connectedness and applying the path-integral primitive
  construction on each member turns a pointed simply connected smooth
  exhaustion into a pointed smooth exhaustion with vanishing first real de
  Rham cohomology.
proof:
  Keep the same domains and base point.  Each domain has trivial first de Rham
  cohomology because every closed one-form has a path-integral primitive.
-/
noncomputable def
    PointedSimplyConnectedSmoothRelativelyCompactExhaustion.toPointedH1Zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p) :
    PointedH1ZeroSmoothRelativelyCompactExhaustion X p where
  toSmoothRelativelyCompactExhaustion :=
    E.toSmoothRelativelyCompactExhaustion
  base_mem := E.base_mem
  pathConnected := by
    intro n
    exact @SimplyConnectedSpace.instPathConnectedSpace
      (E.domain n).carrier inferInstance (E.simplyConnected n)
  deRhamH1Zero := by
    intro n
    letI : SimplyConnectedSpace (E.domain n).carrier := E.simplyConnected n
    exact (E.domain n).deRhamH1Zero_of_simplyConnected

/--
%%handwave
name:
  Filled domains have no bounded complementary components
statement:
  After filling all complementary components with compact closure, every
  component of the complement of the filled domain has noncompact closure.
proof:
  A component with compact closure would have been one of the bounded holes
  added to the filling.
-/
theorem smoothBoundaryDomain_boundedFilling_complement_components_unbounded
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    (Dhat : SmoothBoundaryDomain X)
    (hDhat_carrier :
      Dhat.carrier =
        boundedFillingOfComplement
          (closure (connectedComponentIn D.carrier p))) :
    ∀ V : Set X,
      IsComponentOf V (closure Dhat.carrier)ᶜ →
        ¬ IsCompact (closure V) := by
  intro V hV
  exact
    smoothBoundaryDomain_boundedFilling_complement_components_noCompactClosure
      D hp V (by simpa [hDhat_carrier] using hV)

/--
%%handwave
name:
  Boundary intervals have connected exterior patches for closure complements
statement:
  At every boundary point of a smooth relatively compact domain, there is a
  boundary interval and an ambient neighborhood whose intersection with the
  complement of the domain closure is nonempty and preconnected.
proof:
  In a smooth boundary chart, shrink to a product box in which the domain is
  the negative side and the boundary is the zero slice.  The complement of the
  closure in the box is the positive side, which is nonempty and connected.
-/
theorem smoothBoundaryDomain_boundary_interval_closure_complement_preconnected_patch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (x : frontier Dhat.carrier) :
    ∃ t ∈ 𝓝 x,
      ∃ O : Set X,
        (∀ y : frontier Dhat.carrier, y ∈ t → O ∈ 𝓝 (y : X)) ∧
          (∀ y : frontier Dhat.carrier, y ∈ t →
            (y : X) ∈ closure (O ∩ (closure Dhat.carrier)ᶜ)) ∧
          (O ∩ (closure Dhat.carrier)ᶜ).Nonempty ∧
            IsPreconnected (O ∩ (closure Dhat.carrier)ᶜ) := by
  classical
  rcases Dhat.smooth_boundary (x : X) x.2 with
    ⟨e, _he, hxsource, r, hrsmooth, dr, hrderiv, hdrnz, hlocal⟩
  rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, hxN⟩
  have hprops_x := hNsub hxN
  have hxzero : r (e (x : X)) = 0 := (hprops_x.2.2).mp x.2
  rcases smoothPlaneRegularZeroSet_implicitCoord_fst_eq
      hrsmooth.contDiffAt hrderiv hdrnz hxzero with
    ⟨Φ, hxΦ, hΦfst, _hΦzero⟩
  let eN : OpenPartialHomeomorph X ℂ := e.restrOpen N hNopen
  let E : OpenPartialHomeomorph X (ℝ × dr.ker) := eN.trans Φ
  have hxE : (x : X) ∈ E.source := by
    change (x : X) ∈ (eN.trans Φ).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by simpa [eN] using ⟨hxsource, hxN⟩, by simpa [eN] using hxΦ⟩
  have hD_side :
      ∀ y ∈ E.source, y ∈ Dhat.carrier ↔ (E y).1 < 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.1
  have hfront_side :
      ∀ y ∈ E.source, y ∈ frontier Dhat.carrier ↔ (E y).1 = 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.2
  let z₀ : ℝ × dr.ker := E (x : X)
  have hz₀_target : z₀ ∈ E.target := by
    simpa [z₀] using E.map_source hxE
  have hz₀_fst : z₀.1 = 0 := by
    simpa [z₀] using (hfront_side (x : X) hxE).mp x.2
  rcases mem_nhds_prod_iff.mp (E.open_target.mem_nhds hz₀_target) with
    ⟨U₀, hU₀, V₀, hV₀, hU₀V₀⟩
  have hz₀_fst' : (E (x : X)).1 = 0 := by
    simpa [z₀] using hz₀_fst
  have hU₀_zero : U₀ ∈ 𝓝 (0 : ℝ) := by
    rw [← hz₀_fst']
    simpa [E, eN, OpenPartialHomeomorph.trans_apply] using hU₀
  rcases mem_nhds_iff_exists_Ioo_subset.mp hU₀_zero with
    ⟨a, b, h0ab, hIooU₀⟩
  rcases Metric.nhds_basis_ball.mem_iff.mp hV₀ with
    ⟨ρ, hρpos, hρV₀⟩
  have ha0 : a < 0 := h0ab.1
  have h0b : 0 < b := h0ab.2
  let S : Set (ℝ × dr.ker) := Ioo a b ×ˢ Metric.ball z₀.2 ρ
  let Spos : Set (ℝ × dr.ker) := Ioo 0 b ×ˢ Metric.ball z₀.2 ρ
  let O : Set X := E.symm '' S
  let Ppos : Set X := E.symm '' Spos
  have hS_target : S ⊆ E.target := by
    intro q hq
    exact hU₀V₀ ⟨hIooU₀ hq.1, hρV₀ hq.2⟩
  have hSpos_subset_S : Spos ⊆ S := by
    intro q hq
    exact ⟨⟨ha0.trans hq.1.1, hq.1.2⟩, hq.2⟩
  have hSpos_target : Spos ⊆ E.target := hSpos_subset_S.trans hS_target
  have hS_open : IsOpen S := by
    exact isOpen_Ioo.prod Metric.isOpen_ball
  have hO_open : IsOpen O := by
    exact E.isOpen_image_symm_of_subset_target hS_open hS_target
  have hz₀S : z₀ ∈ S := by
    exact ⟨by simpa [hz₀_fst] using h0ab,
      Metric.mem_ball_self hρpos⟩
  have hxO : (x : X) ∈ O := by
    refine ⟨z₀, hz₀S, ?_⟩
    simpa [z₀] using E.left_inv hxE
  have hPpos_pre : IsPreconnected Ppos := by
    have hSpos_pre : IsPreconnected Spos := by
      exact ((convex_Ioo (0 : ℝ) b).prod (convex_ball z₀.2 ρ)).isPreconnected
    exact hSpos_pre.image E.symm (E.continuousOn_symm.mono hSpos_target)
  have hPpos_subset_compl : Ppos ⊆ O ∩ (closure Dhat.carrier)ᶜ := by
    rintro y ⟨q, hqpos, rfl⟩
    have hqS : q ∈ S := hSpos_subset_S hqpos
    have hq_target : q ∈ E.target := hSpos_target hqpos
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    refine ⟨⟨q, hqS, rfl⟩, ?_⟩
    intro hy_closure
    have hy_union : E.symm q ∈ Dhat.carrier ∪ frontier Dhat.carrier := by
      rwa [closure_eq_self_union_frontier] at hy_closure
    rcases hy_union with hyD | hyfront
    · have hlt : q.1 < 0 := by
        simpa [hEq] using (hD_side (E.symm q) hy_source).1 hyD
      linarith [hqpos.1.1]
    · have hzero : q.1 = 0 := by
        simpa [hEq] using (hfront_side (E.symm q) hy_source).1 hyfront
      linarith [hqpos.1.1]
  have hcompl_subset_Ppos : O ∩ (closure Dhat.carrier)ᶜ ⊆ Ppos := by
    rintro y ⟨hyO, hy_closure_compl⟩
    rcases hyO with ⟨q, hqS, rfl⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hEq : E (E.symm q) = q := E.right_inv hq_target
    rcases lt_trichotomy q.1 0 with hq_neg | hq_zero | hq_pos
    · have hyD : E.symm q ∈ Dhat.carrier := by
        exact (hD_side (E.symm q) hy_source).2 (by simpa [hEq] using hq_neg)
      exact False.elim (hy_closure_compl (subset_closure hyD))
    · have hyfront : E.symm q ∈ frontier Dhat.carrier := by
        exact (hfront_side (E.symm q) hy_source).2 (by simpa [hEq] using hq_zero)
      exact False.elim (hy_closure_compl (frontier_subset_closure hyfront))
    · refine ⟨q, ?_, rfl⟩
      exact ⟨⟨hq_pos, hqS.1.2⟩, hqS.2⟩
  have hpatch_eq : O ∩ (closure Dhat.carrier)ᶜ = Ppos :=
    Subset.antisymm hcompl_subset_Ppos hPpos_subset_compl
  have zero_slice_mem_closure_Ppos :
      ∀ q ∈ S, q.1 = 0 → E.symm q ∈ closure Ppos := by
    intro q hqS hq_zero
    have hq_target : q ∈ E.target := hS_target hqS
    have hq_closure_pos : q ∈ closure Spos := by
      change q ∈ closure (Ioo 0 b ×ˢ Metric.ball z₀.2 ρ)
      rw [closure_prod_eq, closure_Ioo h0b.ne]
      exact ⟨⟨by simp [hq_zero],
          le_of_lt (by simpa [hq_zero] using hqS.1.2)⟩,
        subset_closure hqS.2⟩
    have hcont : ContinuousWithinAt E.symm Spos q :=
      (E.continuousOn_symm q hq_target).mono hSpos_target
    exact hcont.mem_closure hq_closure_pos (mapsTo_image E.symm Spos)
  have hPpos_nonempty : Ppos.Nonempty := by
    refine ⟨E.symm (b / 2, z₀.2), ⟨(b / 2, z₀.2), ?_, rfl⟩⟩
    exact ⟨by constructor <;> linarith, Metric.mem_ball_self hρpos⟩
  let t : Set (frontier Dhat.carrier) := {y | (y : X) ∈ O}
  refine ⟨t, ?_, O, ?_, ?_, ?_, ?_⟩
  · exact (hO_open.preimage continuous_subtype_val).mem_nhds hxO
  · intro y hy
    exact hO_open.mem_nhds hy
  · intro y hy
    change (y : X) ∈ O at hy
    rcases hy with ⟨q, hqS, hqy⟩
    have hq_target : q ∈ E.target := hS_target hqS
    have hy_source : E.symm q ∈ E.source := E.map_target hq_target
    have hq_zero : q.1 = 0 := by
      have hy_frontier : E.symm q ∈ frontier Dhat.carrier := by
        simpa [hqy] using y.2
      simpa [E.right_inv hq_target] using
        (hfront_side (E.symm q) hy_source).mp hy_frontier
    rw [hpatch_eq]
    simpa [hqy] using zero_slice_mem_closure_Ppos q hqS hq_zero
  · rwa [hpatch_eq]
  · rwa [hpatch_eq]

/--
%%handwave
name:
  Boundary intervals have one local exterior component for closure complements
statement:
  At every boundary point of a smooth relatively compact domain, there is a
  boundary interval and a single component of the complement of the domain
  closure containing the local exterior patch.
proof:
  The local exterior patch is nonempty, preconnected, and contained in the
  complement of the closure, hence lies in one connected component of that
  complement.
-/
theorem smoothBoundaryDomain_boundary_interval_local_closure_complement_subset_component
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (x : frontier Dhat.carrier) :
    ∃ t ∈ 𝓝 x,
      ∃ O : Set X,
        (∀ y : frontier Dhat.carrier, y ∈ t → O ∈ 𝓝 (y : X)) ∧
          ∃ V₀ : {V : Set X // IsComponentOf V (closure Dhat.carrier)ᶜ},
            O ∩ (closure Dhat.carrier)ᶜ ⊆ (V₀ : Set X) := by
  rcases
      smoothBoundaryDomain_boundary_interval_closure_complement_preconnected_patch
        Dhat x with
    ⟨t, ht, O, hO_nhds, _hpatch_closure, hpatch_nonempty, hpatch_pre⟩
  rcases preconnected_subset_compl_subset_component
      (K := closure Dhat.carrier)
      (P := O ∩ (closure Dhat.carrier)ᶜ)
      hpatch_pre hpatch_nonempty inter_subset_right with
    ⟨V₀, hV₀_subset⟩
  exact ⟨t, ht, O, hO_nhds, V₀, hV₀_subset⟩

/--
%%handwave
name:
  Unique complementary component incident along a boundary interval
statement:
  Let \(D\) be a smooth relatively compact domain and \(x\in\partial D\).
  There is a neighborhood \(t\) of \(x\) within \(\partial D\) and a component
  \(V_0\) of \(X\setminus\overline D\) such that every point of \(t\) lies in
  \(\partial V_0\), and every component of \(X\setminus\overline D\) whose
  frontier trace meets \(t\) is \(V_0\).
proof:
  A signed boundary chart supplies a nonempty preconnected local exterior
  patch whose closure contains the boundary interval.  Put that patch in its
  complementary component \(V_0\).  Openness of \(V_0\) makes every point of
  the interval a frontier point, while local component uniqueness forces any
  other component with frontier meeting the interval to equal \(V_0\).
-/
theorem smoothBoundaryDomain_boundary_interval_unique_incident_closure_complement_component
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (x : frontier Dhat.carrier) :
    ∃ t ∈ 𝓝 x,
      ∃ V₀ : {V : Set X // IsComponentOf V (closure Dhat.carrier)ᶜ},
        (∀ y : frontier Dhat.carrier, y ∈ t →
          (y : X) ∈ frontier (V₀ : Set X)) ∧
        {V : {V : Set X // IsComponentOf V (closure Dhat.carrier)ᶜ} |
          (({y : frontier Dhat.carrier |
              (y : X) ∈ frontier (V : Set X)} ∩ t).Nonempty)} ⊆ {V₀} := by
  rcases
      smoothBoundaryDomain_boundary_interval_closure_complement_preconnected_patch
        Dhat x with
    ⟨t, ht, O, hO_nhds, hpatch_closure, hpatch_nonempty, hpatch_pre⟩
  rcases preconnected_subset_compl_subset_component
      (K := closure Dhat.carrier)
      (P := O ∩ (closure Dhat.carrier)ᶜ)
      hpatch_pre hpatch_nonempty inter_subset_right with
    ⟨V₀, hpatch_subset⟩
  have hV₀_open : IsOpen (V₀ : Set X) :=
    V₀.2.isOpen_of_isOpen isClosed_closure.isOpen_compl
  have hinterval_frontier :
      ∀ y : frontier Dhat.carrier, y ∈ t →
        (y : X) ∈ frontier (V₀ : Set X) := by
    intro y hy
    have hy_closure : (y : X) ∈ closure (V₀ : Set X) :=
      closure_mono hpatch_subset (hpatch_closure y hy)
    have hy_not_mem : (y : X) ∉ (V₀ : Set X) := by
      intro hyV₀
      exact V₀.2.subset hyV₀ (frontier_subset_closure y.2)
    rw [frontier, hV₀_open.interior_eq]
    exact ⟨hy_closure, hy_not_mem⟩
  refine ⟨t, ht, V₀, hinterval_frontier, ?_⟩
  exact
    complement_component_frontiers_subset_singleton_of_local_complement_subset
      (A := frontier Dhat.carrier)
      (K := closure Dhat.carrier)
      (O := O)
      (V₀ := V₀)
      (frontierTrace :=
        fun V : {V : Set X //
            IsComponentOf V (closure Dhat.carrier)ᶜ} =>
          {y : frontier Dhat.carrier | (y : X) ∈ frontier (V : Set X)})
      (val := fun y : frontier Dhat.carrier => (y : X))
      (t := t)
      hO_nhds
      (by
        intro V y hy
        exact hy)
      hpatch_subset

/--
%%handwave
name:
  A connected boundary component has one exterior side
statement:
  Every connected component of the boundary of a smooth relatively compact
  domain is contained in the frontier of a single connected component of the
  complement of the domain closure.
proof:
  The exterior component incident to a boundary point is locally constant by
  the signed boundary chart.  The trace of any fixed exterior frontier is
  therefore both open and closed in the boundary.  It contains the entire
  connected boundary component through the original point.
-/
theorem smoothBoundaryDomain_connected_boundary_component_incident_component
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (p : frontier Dhat.carrier) :
    ∃ V₀ : {V : Set X // IsComponentOf V (closure Dhat.carrier)ᶜ},
      ∀ y ∈ connectedComponent p, (y : X) ∈ frontier (V₀ : Set X) := by
  classical
  rcases
      smoothBoundaryDomain_boundary_interval_unique_incident_closure_complement_component
        Dhat p with
    ⟨t₀, ht₀, V₀, hfrontier₀, _hunique₀⟩
  let S : Set (frontier Dhat.carrier) :=
    {y | (y : X) ∈ frontier (V₀ : Set X)}
  have hS_closed : IsClosed S := by
    exact isClosed_frontier.preimage continuous_subtype_val
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hyS
    rcases
        smoothBoundaryDomain_boundary_interval_unique_incident_closure_complement_component
          Dhat y with
      ⟨t, ht, V, hfrontier, hunique⟩
    have hyt : y ∈ t := mem_of_mem_nhds ht
    have hV₀_mem :
        V₀ ∈ {W : {W : Set X //
            IsComponentOf W (closure Dhat.carrier)ᶜ} |
          (({z : frontier Dhat.carrier |
              (z : X) ∈ frontier (W : Set X)} ∩ t).Nonempty)} := by
      exact ⟨y, hyS, hyt⟩
    have hV₀_eq_V : V₀ = V :=
      Set.mem_singleton_iff.mp (hunique hV₀_mem)
    refine Filter.mem_of_superset ht ?_
    intro z hzt
    change (z : X) ∈ frontier (V₀ : Set X)
    simpa [hV₀_eq_V] using hfrontier z hzt
  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  have hpS : p ∈ S := hfrontier₀ p (mem_of_mem_nhds ht₀)
  refine ⟨V₀, ?_⟩
  intro y hy
  exact hS_clopen.connectedComponent_subset hpS hy

/--
%%handwave
name:
  Incidence propagates along a connected smooth boundary component
statement:
  Let \(D\) be a smooth relatively compact domain, let
  \(p\in\partial D\), and let \(V\) be a component of
  \(X\setminus\overline D\).  If \(p\in\partial V\), then every point in the
  connected component of \(p\) within \(\partial D\) also lies in
  \(\partial V\).
proof:
  The preceding local uniqueness theorem provides a complementary component
  incident along the whole connected boundary component.  At a small boundary
  interval through \(p\), both this component and \(V\) occur in the singleton
  family of incident components, so they agree.  Substitute this equality in
  the global incidence conclusion.
-/
theorem smoothBoundaryDomain_connected_boundary_component_subset_frontier_of_incident
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (p : frontier Dhat.carrier)
    (V : Set X) (hV : IsComponentOf V (closure Dhat.carrier)ᶜ)
    (hpV : (p : X) ∈ frontier V) :
    ∀ y ∈ connectedComponent p, (y : X) ∈ frontier V := by
  classical
  rcases smoothBoundaryDomain_connected_boundary_component_incident_component
      Dhat p with ⟨V₀, hV₀frontier⟩
  rcases
      smoothBoundaryDomain_boundary_interval_unique_incident_closure_complement_component
        Dhat p with
    ⟨t, ht, W, _hWfrontier, hunique⟩
  have hpt : p ∈ t := mem_of_mem_nhds ht
  have hV_mem :
      ⟨V, hV⟩ ∈ {Z : {Z : Set X //
          IsComponentOf Z (closure Dhat.carrier)ᶜ} |
        (({z : frontier Dhat.carrier |
            (z : X) ∈ frontier (Z : Set X)} ∩ t).Nonempty)} :=
    ⟨p, hpV, hpt⟩
  have hV₀_mem :
      V₀ ∈ {Z : {Z : Set X //
          IsComponentOf Z (closure Dhat.carrier)ᶜ} |
        (({z : frontier Dhat.carrier |
            (z : X) ∈ frontier (Z : Set X)} ∩ t).Nonempty)} :=
    ⟨p, hV₀frontier p mem_connectedComponent, hpt⟩
  have hVW : (⟨V, hV⟩ : {Z : Set X //
      IsComponentOf Z (closure Dhat.carrier)ᶜ}) = W :=
    Set.mem_singleton_iff.mp (hunique hV_mem)
  have hV₀W : V₀ = W :=
    Set.mem_singleton_iff.mp (hunique hV₀_mem)
  have hVV₀ : V = (V₀ : Set X) := by
    exact congrArg Subtype.val (hVW.trans hV₀W.symm)
  intro y hy
  simpa [hVV₀] using hV₀frontier y hy

/--
%%handwave
name:
  Boundary intervals meet one exterior frontier for closure complements
statement:
  At every boundary point of a smooth relatively compact domain, there is a
  boundary interval such that every complementary component whose frontier
  meets that interval is the same component.
proof:
  Use the local exterior component from the boundary chart.  Any component
  whose frontier touches the interval must meet the local exterior patch, so
  component uniqueness identifies it with that component.
-/
theorem smoothBoundaryDomain_boundary_interval_closure_complement_frontiers_subset_singleton
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (x : frontier Dhat.carrier) :
    ∃ t ∈ 𝓝 x,
      ∃ V₀ : {V : Set X //
          IsComponentOf V (closure Dhat.carrier)ᶜ},
        {V : {V : Set X //
            IsComponentOf V (closure Dhat.carrier)ᶜ} |
          (({y : frontier Dhat.carrier | (y : X) ∈ frontier (V : Set X)} ∩ t).Nonempty)}
            ⊆ {V₀} := by
  rcases
      smoothBoundaryDomain_boundary_interval_local_closure_complement_subset_component
        Dhat x with
    ⟨t, ht, O, hO_nhds, V₀, hO_subset⟩
  refine ⟨t, ht, V₀, ?_⟩
  exact
    complement_component_frontiers_subset_singleton_of_local_complement_subset
      (A := frontier Dhat.carrier)
      (K := closure Dhat.carrier)
      (O := O)
      (V₀ := V₀)
      (frontierTrace :=
        fun V : {V : Set X //
            IsComponentOf V (closure Dhat.carrier)ᶜ} =>
          {y : frontier Dhat.carrier | (y : X) ∈ frontier (V : Set X)})
      (val := fun y : frontier Dhat.carrier => (y : X))
      (t := t)
      hO_nhds
      (by
        intro V y hy
        exact hy)
      hO_subset

/--
%%handwave
name:
  Boundary intervals meet finitely many exterior frontiers for closure complements
statement:
  At every boundary point of a smooth relatively compact domain, there is a
  boundary interval that meets the frontiers of only finitely many components
  of the complement of the domain closure.
proof:
  The interval from the local exterior-component theorem meets frontiers
  belonging to at most one complementary component.
-/
theorem smoothBoundaryDomain_boundary_interval_meets_finitely_many_closure_complement_frontiers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (x : frontier Dhat.carrier) :
    ∃ t ∈ 𝓝 x,
      {V : {V : Set X //
          IsComponentOf V (closure Dhat.carrier)ᶜ} |
        (({y : frontier Dhat.carrier | (y : X) ∈ frontier (V : Set X)} ∩ t).Nonempty)}.Finite := by
  rcases
      smoothBoundaryDomain_boundary_interval_closure_complement_frontiers_subset_singleton
        Dhat x with
    ⟨t, ht, V₀, hsubset⟩
  exact ⟨t, ht, (Set.finite_singleton V₀).subset hsubset⟩

/--
%%handwave
name:
  Exterior frontiers are locally finite along a smooth boundary
statement:
  For a smooth relatively compact domain, the traces on the smooth boundary
  of the frontiers of the components of the complement of the domain closure
  form a locally finite family.
proof:
  Around every boundary point, the local exterior-side theorem gives a
  boundary interval meeting only finitely many complementary frontiers.
-/
theorem smoothBoundaryDomain_closure_complement_component_frontiers_locallyFinite_on_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X) :
    LocallyFinite
      (fun V : {V : Set X //
          IsComponentOf V (closure Dhat.carrier)ᶜ} =>
        {x : frontier Dhat.carrier | (x : X) ∈ frontier (V : Set X)}) := by
  intro x
  simpa using
    smoothBoundaryDomain_boundary_interval_meets_finitely_many_closure_complement_frontiers
      Dhat x

/--
%%handwave
name:
  Smooth boundary components have finite incidence for closure complements
statement:
  Along each connected component of the boundary of a smooth relatively
  compact domain, only finitely many components of the complement of the
  domain closure are incident.
proof:
  Smooth boundary charts identify the boundary locally with an interval and
  the complement locally with the exterior side of that interval.  Compactness
  of each boundary component gives a finite subcover by such charts.
-/
theorem smoothBoundaryDomain_boundaryComponent_incident_closure_complement_components_finite
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (B : ConnectedComponents (frontier Dhat.carrier)) :
    {V : Set X |
      IsComponentOf V (closure Dhat.carrier)ᶜ ∧
        ∃ x : frontier Dhat.carrier,
          (x : X) ∈ frontier V ∧
            ConnectedComponents.mk x = B}.Finite := by
  classical
  let K : Set X := closure Dhat.carrier
  let I : Type :=
    {V : Set X //
      IsComponentOf V Kᶜ ∧
        ∃ x : frontier Dhat.carrier,
          (x : X) ∈ frontier V ∧
            ConnectedComponents.mk x = B}
  let J : Type := {V : Set X // IsComponentOf V Kᶜ}
  let fJ : J → Set (frontier Dhat.carrier) :=
    fun V ↦ {x : frontier Dhat.carrier | (x : X) ∈ frontier (V : Set X)}
  let g : I → J := fun V ↦ ⟨(V : Set X), V.2.1⟩
  have hg_inj : Function.Injective g := by
    intro V W hVW
    apply Subtype.ext
    exact congrArg (fun Z : J => (Z : Set X)) hVW
  have hLFJ : LocallyFinite fJ := by
    simpa [K, J, fJ] using
      smoothBoundaryDomain_closure_complement_component_frontiers_locallyFinite_on_boundary
        Dhat
  have hLFI : LocallyFinite (fJ ∘ g) :=
    hLFJ.comp_injective hg_inj
  haveI : CompactSpace (frontier Dhat.carrier) :=
    isCompact_iff_compactSpace.mp (smoothBoundaryDomain_frontier_compact Dhat)
  have hnonempty : ∀ V : I, ((fJ ∘ g) V).Nonempty := by
    intro V
    rcases V.2.2 with ⟨x, hx_frontier, _hxB⟩
    exact ⟨x, hx_frontier⟩
  have hIfinite_univ : (univ : Set I).Finite :=
    hLFI.finite_of_compact hnonempty
  have himage_finite :
      ((fun V : I => (V : Set X)) '' (univ : Set I)).Finite :=
    hIfinite_univ.image _
  convert himage_finite using 1
  ext V
  constructor
  · intro hV
    exact ⟨⟨V, by simpa [K] using hV⟩, mem_univ _, rfl⟩
  · rintro ⟨W, _hW, rfl⟩
    simpa [K] using W.2

/--
%%handwave
name:
  Smooth compact-boundary domains have finitely many complementary components
statement:
  The complement of the closure of a smooth relatively compact domain in a
  connected surface has only finitely many connected components.
proof:
  The boundary is compact and locally connected, hence has finitely many
  connected components.  Smooth boundary charts have two local sides, so only
  finitely many complementary components can be incident to each boundary
  component; finite incidence gives the result.
-/
theorem smoothBoundaryDomain_complement_components_finite
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X) :
    {V : Set X | IsComponentOf V (closure Dhat.carrier)ᶜ}.Finite := by
  rcases Dhat.nonempty with ⟨x, hx⟩
  have hK_nonempty : (closure Dhat.carrier).Nonempty :=
    ⟨x, subset_closure hx⟩
  haveI : LocallyConnectedSpace X :=
    ChartedSpace.locallyConnectedSpace (H := ℂ) (M := X)
  exact
    finite_complement_components_of_frontier_subset_finite_boundary_components_and_finite_incidence
      (K := closure Dhat.carrier)
      (A := frontier Dhat.carrier)
      isClosed_closure hK_nonempty
      frontier_closure_subset
      (smoothBoundaryDomain_frontier_finite_connectedComponents Dhat)
      (fun B =>
        smoothBoundaryDomain_boundaryComponent_incident_closure_complement_components_finite
          Dhat B)

/--
%%handwave
name:
  Component retractions glue to a retraction onto the closure
statement:
  If a smooth relatively compact domain has finitely many complementary
  components and every complementary component closure retracts to its
  boundary, then the ambient surface retracts continuously onto the domain
  closure.
proof:
  Paste the identity on the domain closure with the component retractions.
  The domain closure and the finitely many component closures form a finite
  closed cover, and the maps agree on their overlaps because each component
  retraction fixes its boundary.
-/
theorem smoothBoundaryDomain_closure_retract_of_finite_component_retractions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (hfinite_components :
      {V : Set X | IsComponentOf V (closure Dhat.carrier)ᶜ}.Finite)
    (hcomponent_retractions :
      ∀ V : Set X,
        IsComponentOf V (closure Dhat.carrier)ᶜ →
          HasContinuousRetractionFromClosureOntoFrontier V) :
    HasContinuousRetractionOntoSet (closure Dhat.carrier) := by
  classical
  let K : Set X := closure Dhat.carrier
  let I := {V : Set X // IsComponentOf V Kᶜ}
  have hfiniteI : Set.Finite {V : Set X | IsComponentOf V Kᶜ} := by
    simpa [K] using hfinite_components
  letI : Fintype I := hfiniteI.fintype
  let componentRetraction (V : I) : C(closure (V : Set X), frontier (V : Set X)) :=
    Classical.choose (hcomponent_retractions V (by simpa [K] using V.property))
  have componentRetraction_fixed (V : I) :
      ∀ x : frontier (V : Set X),
        componentRetraction V ⟨x.1, frontier_subset_closure x.2⟩ = x :=
    Classical.choose_spec (hcomponent_retractions V (by simpa [K] using V.property))
  have frontier_component_subset (V : I) : frontier (V : Set X) ⊆ K :=
    V.property.frontier_subset_of_compl_isClosed isClosed_closure
  let componentMap (V : I) : C(closure (V : Set X), K) :=
    (ContinuousMap.mk
      (fun x : frontier (V : Set X) =>
        ⟨(x : X), frontier_component_subset V x.2⟩)
      (Continuous.subtype_mk continuous_subtype_val
        (fun x => frontier_component_subset V x.2))).comp
      (componentRetraction V)
  have componentMap_eq_of_eq (A B : I) (hAB : A = B)
      (xA : closure (A : Set X)) (xB : closure (B : Set X))
      (hx : (xA : X) = xB) : componentMap A xA = componentMap B xB := by
    subst B
    have hxx : xA = xB := Subtype.ext hx
    subst xB
    rfl
  let componentAt (x : X) (hx : x ∉ K) : I :=
    ⟨connectedComponentIn Kᶜ x,
      isComponentOf_connectedComponentIn (by simpa using hx)⟩
  let ρ : X → K := fun x =>
    if hx : x ∈ K then ⟨x, hx⟩
    else
      componentMap (componentAt x hx)
        ⟨x, subset_closure (mem_connectedComponentIn (by simpa using hx))⟩
  have ρ_eq_on_K : ∀ x : K, ρ x = x := by
    intro x
    simp [ρ, x.2]
  have componentAt_eq (V : I) {x : X} (hxV : x ∈ (V : Set X))
      (hxK : x ∉ K) : componentAt x hxK = V := by
    apply Subtype.ext
    exact (V.property.eq_connectedComponentIn_of_mem hxV).symm
  have ρ_eq_componentMap (V : I) :
      ∀ x : closure (V : Set X), ρ x = componentMap V x := by
    rcases V with ⟨V, hV⟩
    intro x
    by_cases hxK : (x : X) ∈ K
    · have hxfrontier : (x : X) ∈ frontier (V : Set X) := by
        rw [frontier, (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl).interior_eq]
        exact ⟨x.2, fun hxV => (hV.subset hxV) hxK⟩
      have hfixed := componentRetraction_fixed ⟨V, hV⟩ ⟨x, hxfrontier⟩
      apply Subtype.ext
      simpa [ρ, hxK, componentMap] using congrArg Subtype.val hfixed.symm
    · have hx_union : (x : X) ∈ (V : Set X) ∪ K :=
        hV.closure_subset_union_of_compl_isClosed isClosed_closure x.2
      have hxV : (x : X) ∈ (V : Set X) := hx_union.resolve_right hxK
      have hcomponent : componentAt (x : X) hxK = ⟨V, hV⟩ :=
        componentAt_eq ⟨V, hV⟩ hxV hxK
      have hset : connectedComponentIn Kᶜ (x : X) = V :=
        congrArg Subtype.val hcomponent
      simp only [ρ, hxK, ↓reduceDIte]
      exact componentMap_eq_of_eq
        (componentAt (x : X) hxK) ⟨V, hV⟩ hcomponent _ x rfl
  have hρ_continuousOn_K : ContinuousOn ρ K := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : K.restrict ρ = ContinuousMap.id K := by
      funext x
      exact ρ_eq_on_K x
    rw [heq]
    exact (ContinuousMap.id K).continuous
  have hρ_continuousOn_component (V : I) :
      ContinuousOn ρ (closure (V : Set X)) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (closure (V : Set X)).restrict ρ = componentMap V := by
      funext x
      exact ρ_eq_componentMap V x
    rw [heq]
    exact (componentMap V).continuous
  let pieces : Option I → Set X
    | none => K
    | some V => closure (V : Set X)
  have hpieces_closed : ∀ i, IsClosed (pieces i) := by
    intro i
    cases i with
    | none => exact isClosed_closure
    | some V => exact isClosed_closure
  have hpieces_cover : ⋃ i, pieces i = (univ : Set X) := by
    apply eq_univ_of_forall
    intro x
    by_cases hxK : x ∈ K
    · exact mem_iUnion.mpr ⟨none, hxK⟩
    · let V : I := componentAt x hxK
      have hxV : x ∈ (V : Set X) := by
        exact mem_connectedComponentIn (by simpa using hxK)
      exact mem_iUnion.mpr ⟨some V, subset_closure hxV⟩
  have hρ_continuousOn_pieces : ∀ i, ContinuousOn ρ (pieces i) := by
    intro i
    cases i with
    | none => exact hρ_continuousOn_K
    | some V => exact hρ_continuousOn_component V
  have hρ_continuous : Continuous ρ :=
    (locallyFinite_of_finite pieces).continuous
      hpieces_cover hpieces_closed hρ_continuousOn_pieces
  exact ⟨⟨ρ, hρ_continuous⟩, ρ_eq_on_K⟩

/--
%%handwave
name:
  A retract inherits vanishing first singular cohomology
statement:
  If the ambient surface has vanishing first real singular cohomology and the
  closure of a smooth domain is a continuous retract of the surface, then the
  closure also has vanishing first real singular cohomology.
proof:
  Contravariant functoriality makes the identity on the cohomology of the
  closure factor through the zero ambient cohomology group.
-/
theorem smoothBoundaryDomain_closure_realSingularH1_zero_of_retract
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (hambient :
      CategoryTheory.Limits.IsZero
        (JJMath.Cohomology.RealSingularCohomology (TopCat.of X) 1))
    (hretract : HasContinuousRetractionOntoSet (closure Dhat.carrier)) :
    CategoryTheory.Limits.IsZero
      (JJMath.Cohomology.RealSingularCohomology
        (TopCat.of (closure Dhat.carrier)) 1) := by
  exact realSingularCohomology_isZero_of_continuous_retract
    (closure Dhat.carrier) hretract 1 hambient

/--
%%handwave
name:
  A collar transfers vanishing cohomology to the interior
statement:
  Suppose a smooth domain closure admits an inward collar push whose
  restriction to the interior is homotopic to the identity.  If the closure
  has vanishing first real singular cohomology, then so does the interior.
proof:
  The inclusion and collar push give a one-sided homotopy inverse, so the
  identity on interior cohomology factors through the zero cohomology of the
  closure.
-/
theorem smoothBoundaryDomain_open_realSingularH1_zero_of_closure_retract
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Dhat : SmoothBoundaryDomain X)
    (hclosure :
      CategoryTheory.Limits.IsZero
        (JJMath.Cohomology.RealSingularCohomology
          (TopCat.of (closure Dhat.carrier)) 1))
    (hretract : HasHomotopyRetractionFromClosureOntoOpenCarrier Dhat) :
    let U : TopologicalSpace.Opens X := ⟨Dhat.carrier, Dhat.isOpen⟩
    CategoryTheory.Limits.IsZero
      (JJMath.Cohomology.RealSingularCohomology (TopCat.of U) 1) := by
  let U : TopologicalSpace.Opens X := ⟨Dhat.carrier, Dhat.isOpen⟩
  rcases hretract with ⟨ρ, ⟨hρ⟩⟩
  let i : TopCat.of U ⟶ TopCat.of (closure Dhat.carrier) :=
    smoothBoundaryDomainOpenToClosure Dhat
  let r : TopCat.of (closure Dhat.carrier) ⟶ TopCat.of U := TopCat.ofHom ρ
  exact
    JJMath.Cohomology.singularCohomology_isZero_of_left_homotopy_inverse
      ℝ i r (by simpa [U, i, r] using hρ) 1
      (by simpa [U] using hclosure)




/--
%%handwave
name:
  The filled side is relatively compact when there are finitely many holes
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(X\setminus\overline C\) has
  finitely many components and \(U\) is the unique exterior component, then
  the filled side determined by \(U\) has compact closure.
proof:
  Apply the finite-component compactness theorem for filled sides to the
  compact set \(\overline C\).
-/
theorem smoothBoundaryDomain_filledSide_compact_closure_of_finite_complement_components
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (_hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U)
    (hfinite :
      {V : Set X |
        IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ}.Finite) :
    IsCompact (closure (filledSideOfExteriorComponent U)) :=
  hU.filledSide_closure_compact_of_finite_components
    (smoothBoundaryDomain_pointedComponent_closure_compact D p)
    hunique hfinite

/--
%%handwave
name:
  The filled side is relatively compact when all holes are trapped
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If the closures of all complementary
  components of \(X\setminus\overline C\) except the exterior component lie in
  one compact set, then the filled side determined by the exterior component
  has compact closure.
proof:
  Apply the compactness theorem for filled sides to the compact set
  \(\overline C\).
-/
theorem smoothBoundaryDomain_filledSide_compact_closure_of_nonExterior_components_subset_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (_hp : p ∈ D.carrier)
    {U B : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hB : IsCompact B)
    (hcomponents :
      ∀ V : Set X,
        IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ →
        V ≠ U → closure V ⊆ B) :
    IsCompact (closure (filledSideOfExteriorComponent U)) :=
  hU.filledSide_closure_compact_of_nonExterior_components_subset_compact
    (smoothBoundaryDomain_pointedComponent_closure_compact D p) hB
    hcomponents

/--
%%handwave
name:
  The bounded holes are trapped in one compact set
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then the closures of all other
  complementary components lie in one compact subset of the surface.
proof:
  If no such compact set existed, choose non-exterior complementary components
  with points escaping a compact exhaustion.  Their closures are individually
  compact, but the escaping choice forces an additional exterior component in
  the limit, contradicting uniqueness of the exterior component.
-/
theorem smoothBoundaryDomain_nonExterior_components_subset_common_compact_of_unique_exterior
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (_hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U) :
    ∃ B : Set X, IsCompact B ∧
      ∀ V : Set X,
        IsComponentOf V (closure (connectedComponentIn D.carrier p))ᶜ →
        V ≠ U → closure V ⊆ B := by
  classical
  let K : Set X := closure (connectedComponentIn D.carrier p)
  let components : Set (Set X) := {V : Set X | IsComponentOf V Kᶜ}
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact smoothBoundaryDomain_pointedComponent_closure_compact D p
  have hfinite : components.Finite := by
    dsimp [components, K]
    exact smoothBoundaryDomain_pointedComponent_complement_components_finite
      D hp
  let boundedComponents : Finset (Set X) :=
    hfinite.toFinset.filter (fun V : Set X => V ≠ U)
  let B : Set X := ⋃ V ∈ boundedComponents, closure V
  have hB_compact : IsCompact B := by
    dsimp [B, boundedComponents]
    refine (hfinite.toFinset.filter (fun V : Set X => V ≠ U)).isCompact_biUnion ?_
    intro V hVmem
    rcases Finset.mem_filter.mp hVmem with ⟨hVfin, hV_ne⟩
    have hVcomp : IsComponentOf V Kᶜ :=
      hfinite.mem_toFinset.mp hVfin
    exact hVcomp.closure_compact_of_ne_unique_exterior
      hK_compact
      (by
        intro W hW
        exact hunique W hW)
      hV_ne
  refine ⟨B, hB_compact, ?_⟩
  intro V hVcomp hV_ne
  have hVmem_components : V ∈ components := by
    dsimp [components, K]
    exact hVcomp
  have hVfin : V ∈ hfinite.toFinset :=
    hfinite.mem_toFinset.mpr hVmem_components
  have hVbounded : V ∈ boundedComponents := by
    dsimp [boundedComponents]
    exact Finset.mem_filter.mpr ⟨hVfin, hV_ne⟩
  intro x hx
  dsimp [B]
  exact mem_iUnion₂.mpr ⟨V, hVbounded, hx⟩

/--
%%handwave
name:
  The filled side is relatively compact
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then the closure of the filled side
  determined by \(U\) is compact.
proof:
  The filled side consists of \(\overline C\) together with the non-exterior
  complementary components.  Uniqueness of the exterior component rules out an
  escaping sequence in that union, so the filled side has compact closure.
-/
theorem smoothBoundaryDomain_filledSide_compact_closure_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U) :
    IsCompact (closure (filledSideOfExteriorComponent U)) := by
  rcases smoothBoundaryDomain_nonExterior_components_subset_common_compact_of_unique_exterior
      D hp hU hunique with ⟨B, hB_compact, hB_components⟩
  exact
    smoothBoundaryDomain_filledSide_compact_closure_of_nonExterior_components_subset_compact
      D hp hU hB_compact hB_components

/--
%%handwave
name:
  The filled side agrees locally with the original domain along its frontier
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then near every point of the
  frontier of the filled side determined by \(U\), membership in the filled
  side is the same as membership in \(D\).
proof:
  Such a frontier point lies on the exterior boundary of the pointed
  component.  Filling only adds complementary components on the bounded side,
  so in a sufficiently small smooth-boundary chart around this exterior
  boundary point the filled side and the original domain occupy the same side
  of the boundary.
-/
theorem smoothBoundaryDomain_filledSide_eventually_eq_carrier_near_frontier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (_hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U) :
    ∀ x ∈ frontier (filledSideOfExteriorComponent U),
      ∀ᶠ y in 𝓝 x,
        (y ∈ filledSideOfExteriorComponent U ↔ y ∈ D.carrier) := by
  classical
  intro x hx_frontier
  let C : Set X := connectedComponentIn D.carrier p
  let K : Set X := closure C
  have hxK : x ∈ K := by
    simpa [C, K] using
      smoothBoundaryDomain_frontier_filledSide_subset_pointedComponent_closure
        D p hU hx_frontier
  have hx_boundary : x ∈ frontier D.carrier :=
    smoothBoundaryDomain_frontier_filledSide_subset_boundary D hp hU
      hx_frontier
  have hxUcl : x ∈ closure U := by
    have hx_not_filled : x ∉ filledSideOfExteriorComponent U := by
      exact
        Set.disjoint_left.mp
          ((disjoint_frontier_iff_isOpen).2
            (filledSideOfExteriorComponent_isOpen U))
          hx_frontier
    simpa [filledSideOfExteriorComponent, interior_compl] using hx_not_filled
  rcases D.smooth_boundary x hx_boundary with
    ⟨e, _he, hxsource, r, hrsmooth, dr, hrderiv, hdrnz, hlocal⟩
  rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, hxN⟩
  have hprops_x := hNsub hxN
  have hxzero : r (e x) = 0 := (hprops_x.2.2).mp hx_boundary
  rcases smoothPlaneRegularZeroSet_implicitCoord_fst_eq
      hrsmooth.contDiffAt hrderiv hdrnz hxzero with
    ⟨Φ, hxΦ, hΦfst, _hΦzero⟩
  let eN : OpenPartialHomeomorph X ℂ := e.restrOpen N hNopen
  let E : OpenPartialHomeomorph X (ℝ × dr.ker) := eN.trans Φ
  have hxE : x ∈ E.source := by
    change x ∈ (eN.trans Φ).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by simpa [eN] using ⟨hxsource, hxN⟩, by simpa [eN] using hxΦ⟩
  have hD_side :
      ∀ y ∈ E.source, y ∈ D.carrier ↔ (E y).1 < 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.1
  have hfront_side :
      ∀ y ∈ E.source, y ∈ frontier D.carrier ↔ (E y).1 = 0 := by
    intro y hy
    have hy' : y ∈ eN.source ∩ eN ⁻¹' Φ.source := by
      change y ∈ (eN.trans Φ).source at hy
      simpa [OpenPartialHomeomorph.trans_source] using hy
    have hy_eN_source : y ∈ e.source ∩ N := by
      simpa [eN] using hy'.1
    have hyN : y ∈ N := hy_eN_source.2
    have hyΦ : e y ∈ Φ.source := by
      simpa [eN] using hy'.2
    have hfst : (E y).1 = r (e y) := by
      simpa [E, eN, OpenPartialHomeomorph.trans_apply] using
        hΦfst (e y) hyΦ
    simpa [hfst] using (hNsub hyN).2.2
  have hC : IsComponentOf C D.carrier :=
    smoothBoundaryDomain_pointedComponent_isComponentOf D hp
  have hUcomp : IsComponentOf U Kᶜ := by
    simpa [C, K] using hU.isComponentOf
  simpa [C, K] using
    signedBoundaryChart_filledSide_eventually_eq_domain_of_component_closure
      (D := D.carrier) (C := C) (K := K) (U := U)
      D.isOpen hC rfl hUcomp ⟨x, hx_boundary⟩ hxK hxUcl
      E hxE hD_side hfront_side

/--
%%handwave
name:
  The filled side has smooth boundary
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then the filled side determined by
  \(U\) has smooth boundary.
proof:
  Filling holes deletes whole boundary components of the original smooth
  domain and keeps the exterior boundary components.  It therefore introduces
  no new nonsmooth boundary points.
-/
theorem smoothBoundaryDomain_filledSide_hasSmoothBoundary_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U) :
    HasSmoothBoundary (filledSideOfExteriorComponent U) := by
  intro x hx_frontier
  have hx_boundary : x ∈ frontier D.carrier :=
    smoothBoundaryDomain_frontier_filledSide_subset_boundary D hp hU
      hx_frontier
  have hmem :
      ∀ᶠ y in 𝓝 x,
        (y ∈ filledSideOfExteriorComponent U ↔ y ∈ D.carrier) :=
    smoothBoundaryDomain_filledSide_eventually_eq_carrier_near_frontier
      D hp hU hunique x hx_frontier
  have hfrontier :
      ∀ᶠ y in 𝓝 x,
        (y ∈ frontier (filledSideOfExteriorComponent U) ↔
          y ∈ frontier D.carrier) :=
    eventually_frontier_congr_of_eventually_mem_iff hmem
  exact hasSmoothBoundary_localData_of_eventually_mem_and_frontier_iff
    D.smooth_boundary hx_boundary hmem hfrontier

/--
%%handwave
name:
  The filled side is a smooth relatively compact domain
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then the filled side determined by
  \(U\) is the carrier of a smooth relatively compact domain.
proof:
  The filled side is open and nonempty.  Uniqueness of the exterior component
  makes the complementary side relatively compact, while smoothness follows
  because the operation deletes boundary components rather than creating new
  ones.
-/
theorem smoothBoundaryDomain_exists_domain_with_filledSide_carrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U) :
    ∃ Dhat : SmoothBoundaryDomain X,
      Dhat.carrier = filledSideOfExteriorComponent U := by
  refine ⟨
    { carrier := filledSideOfExteriorComponent U
      isOpen := filledSideOfExteriorComponent_isOpen U
      nonempty :=
        smoothBoundaryDomain_filledSide_nonempty_of_exteriorComponent_closure
          D hp hU
      compact_closure :=
        smoothBoundaryDomain_filledSide_compact_closure_of_exteriorComponent_closure
          D hp hU hunique
      smooth_boundary :=
        smoothBoundaryDomain_filledSide_hasSmoothBoundary_of_exteriorComponent_closure
          D hp hU hunique },
    rfl⟩

/--
%%handwave
name:
  Filled-side points join to the base
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then every point of the filled side
  can be joined to \(p\) by a path lying in the filled side.
proof:
  Points of \(C\) are joined to \(p\) inside \(C\).  Points in a bounded
  complementary hole are joined to a boundary point of \(\overline C\) through
  the local smooth-boundary collar, then to \(p\) through \(C\).
-/
theorem smoothBoundaryDomain_filledSide_joinedIn_base_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (_hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U) :
    ∀ x ∈ filledSideOfExteriorComponent U,
      JoinedIn (filledSideOfExteriorComponent U) p x := by
  intro x hx
  have hdecomp :
      filledSideOfExteriorComponent U ⊆
        closure (connectedComponentIn D.carrier p) ∪
          {x : X |
            ∃ V : Set X,
              IsComponentOf V
                (closure (connectedComponentIn D.carrier p))ᶜ ∧
                V ≠ U ∧ x ∈ V} :=
    smoothBoundaryDomain_filledSide_subset_pointedComponent_closure_union_holes
      D p hU
  rcases hdecomp hx with hx_closure | hx_hole
  · exact
      smoothBoundaryDomain_pointedComponent_closure_joinedIn_filledSide_of_exteriorComponent_closure
        D hp hU hx_closure hx
  · rcases hx_hole with ⟨V, hV, hV_ne, hxV⟩
    rcases
      smoothBoundaryDomain_nonExterior_component_joinedIn_pointedComponent_closure_in_filledSide
        D hp hU hV hV_ne x hxV with
      ⟨a, ha_closure, ha_filled, hxa⟩
    have hpa :
        JoinedIn (filledSideOfExteriorComponent U) p a :=
      smoothBoundaryDomain_pointedComponent_closure_joinedIn_filledSide_of_exteriorComponent_closure
        D hp hU ha_closure ha_filled
    exact hpa.trans hxa.symm

/--
%%handwave
name:
  The filled side is connected
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then the filled side determined by
  \(U\) is connected.
proof:
  The pointed component is connected and every bounded complementary component
  that is filled touches it through the retained side of a smooth boundary
  chart.  Thus adjoining all bounded holes does not create a new connected
  component.
-/
theorem smoothBoundaryDomain_filledSide_isPreconnected_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U) :
    IsPreconnected (filledSideOfExteriorComponent U) := by
  exact isPreconnected_of_forall_joinedIn_base
    (smoothBoundaryDomain_filledSide_joinedIn_base_of_exteriorComponent_closure
      D hp hU hunique)

/--
%%handwave
name:
  The filled side is path connected
statement:
  Let \(D\) be a smooth relatively compact domain and let \(C\) be the
  component of \(D\) containing \(p\).  If \(U\) is the unique exterior
  component of \(X\setminus\overline C\), then the filled side determined by
  \(U\) is path connected.
proof:
  The pointed component is connected and every bounded complementary component
  that is filled touches its boundary.  Paths in the smooth surface can be
  joined through small boundary charts, so adjoining all bounded holes keeps a
  single path component.
-/
theorem smoothBoundaryDomain_filledSide_pathConnected_of_exteriorComponent_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) {p : X} (hp : p ∈ D.carrier)
    {U : Set X}
    (hU : IsExteriorComponent
      (closure (connectedComponentIn D.carrier p)) U)
    (hunique :
      ∀ V : Set X,
        IsExteriorComponent (closure (connectedComponentIn D.carrier p)) V →
          V = U) :
    PathConnectedSpace (filledSideOfExteriorComponent U) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  exact isPathConnected_of_forall_joinedIn_base
    (smoothBoundaryDomain_base_mem_filledSide_of_exteriorComponent_closure
      D hp hU)
    (smoothBoundaryDomain_filledSide_joinedIn_base_of_exteriorComponent_closure
      D hp hU hunique)

/--
%%handwave
name:
  Ambient loops in simply connected spaces contract
statement:
  If \(X\) is simply connected, then the image in \(X\) of any loop in a
  subset is homotopic to the constant loop.
proof:
  In a simply connected space any two paths with the same endpoints are
  homotopic.
-/
theorem simplyConnected_subtype_loop_ambient_nullhomotopic
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    {s : Set X} (x : s) (γ : Path x x) :
    Path.Homotopic (γ.map continuous_subtype_val) (Path.refl (x : X)) :=
  SimplyConnectedSpace.paths_homotopic _ _

/--
%%handwave
name:
  Monotonicity of exhaustion domains
statement:
  In a smooth relatively compact exhaustion, an earlier domain is contained in
  every later domain.
proof:
  Iterate the successive containment in the definition of the exhaustion.
-/
theorem smoothRelativelyCompactExhaustion_carrier_mono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m ≤ n) :
    (E.domain m).carrier ⊆ (E.domain n).carrier := by
  refine Nat.le_induction ?base ?step n hmn
  · exact subset_rfl
  · intro k _hmk ih
    exact ih.trans (E.monotone k)

/--
%%handwave
name:
  Compact sets enter a smooth exhaustion
statement:
  Every compact subset of a surface is contained in one member of a smooth
  relatively compact exhaustion.
proof:
  The exhaustion domains are open and cover the surface.  A finite subcover
  of the compact set is contained in one later exhaustion domain by
  monotonicity.
-/
theorem smoothRelativelyCompactExhaustion_compact_subset_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {K : Set X}
    (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ (E.domain n).carrier := by
  classical
  let nOf : X → ℕ := fun x ↦ Classical.choose (E.exhausts x)
  have hnOf : ∀ x : X, x ∈ (E.domain (nOf x)).carrier := by
    intro x
    exact Classical.choose_spec (E.exhausts x)
  let U : X → Set X := fun x ↦ (E.domain (nOf x)).carrier
  have hU_open : ∀ x : X, IsOpen (U x) := by
    intro x
    exact (E.domain (nOf x)).isOpen
  have hcover : K ⊆ ⋃ x : X, U x := by
    intro x _hx
    exact mem_iUnion.mpr ⟨x, hnOf x⟩
  rcases hK.elim_finite_subcover U hU_open hcover with ⟨t, ht⟩
  let N : ℕ := t.sup nOf
  refine ⟨N, ?_⟩
  intro x hxK
  have hxUnion : x ∈ ⋃ y ∈ t, U y := ht hxK
  rcases mem_iUnion.mp hxUnion with ⟨y, hyUnion⟩
  rcases mem_iUnion.mp hyUnion with ⟨hyt, hxy⟩
  exact smoothRelativelyCompactExhaustion_carrier_mono E (Finset.le_sup hyt) hxy

/--
%%handwave
name:
  Compact sets eventually stay inside a smooth exhaustion
statement:
  Every compact subset of a surface is contained in all sufficiently late
  members of a smooth relatively compact exhaustion.
proof:
  Once the compact set lies in one member, monotonicity keeps it in every
  later member.
-/
theorem smoothRelativelyCompactExhaustion_eventually_compact_subset_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {K : Set X}
    (hK : IsCompact K) :
    ∀ᶠ n : ℕ in Filter.atTop, K ⊆ (E.domain n).carrier := by
  rcases smoothRelativelyCompactExhaustion_compact_subset_domain E hK with
    ⟨N, hN⟩
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact hN.trans (smoothRelativelyCompactExhaustion_carrier_mono E hn)

/--
%%handwave
name:
  Compact sets enter a pointed smooth simply connected exhaustion
statement:
  Every compact subset of the surface is contained in one domain of a pointed
  smooth simply connected exhaustion.
proof:
  Apply the compact-containment theorem for the underlying smooth relatively
  compact exhaustion.
-/
theorem PointedSimplyConnectedSmoothRelativelyCompactExhaustion.compact_subset_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    {K : Set X} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ (E.domain n).carrier :=
  smoothRelativelyCompactExhaustion_compact_subset_domain
    E.toSmoothRelativelyCompactExhaustion hK

/--
%%handwave
name:
  Compact sets eventually stay in a pointed smooth simply connected exhaustion
statement:
  Every compact subset of the surface is contained in all sufficiently late
  domains of a pointed smooth simply connected exhaustion.
proof:
  Apply the eventual compact-containment theorem for the underlying smooth
  relatively compact exhaustion.
-/
theorem PointedSimplyConnectedSmoothRelativelyCompactExhaustion.eventually_compact_subset_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (E : PointedSimplyConnectedSmoothRelativelyCompactExhaustion X p)
    {K : Set X} (hK : IsCompact K) :
    ∀ᶠ n : ℕ in Filter.atTop, K ⊆ (E.domain n).carrier :=
  smoothRelativelyCompactExhaustion_eventually_compact_subset_domain
    E.toSmoothRelativelyCompactExhaustion hK

/--
%%handwave
name:
  Compact sets enter a pointed H-one-zero smooth exhaustion
statement:
  Every compact subset of the surface is contained in one domain of a pointed
  smooth exhaustion whose domains have vanishing first real de Rham
  cohomology.
proof:
  Apply the compact-containment theorem for the underlying smooth relatively
  compact exhaustion.
-/
theorem PointedH1ZeroSmoothRelativelyCompactExhaustion.compact_subset_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {p : X}
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    {K : Set X} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ (E.domain n).carrier :=
  smoothRelativelyCompactExhaustion_compact_subset_domain
    E.toSmoothRelativelyCompactExhaustion hK

/--
%%handwave
name:
  Compact sets eventually stay in a pointed H-one-zero smooth exhaustion
statement:
  Every compact subset of the surface is contained in all sufficiently late
  domains of a pointed smooth exhaustion whose domains have vanishing first
  real de Rham cohomology.
proof:
  Apply the eventual compact-containment theorem for the underlying smooth
  relatively compact exhaustion.
-/
theorem PointedH1ZeroSmoothRelativelyCompactExhaustion.eventually_compact_subset_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {p : X}
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    {K : Set X} (hK : IsCompact K) :
    ∀ᶠ n : ℕ in Filter.atTop, K ⊆ (E.domain n).carrier :=
  smoothRelativelyCompactExhaustion_eventually_compact_subset_domain
    E.toSmoothRelativelyCompactExhaustion hK

/--
%%handwave
name:
  Exterior criterion along a smooth exhaustion
statement:
  A complementary component is exterior exactly when it is not contained in
  any member of a smooth relatively compact exhaustion.
proof:
  If the component were contained in one exhaustion member, it would be
  contained in the compact closure of that member.  Conversely, every compact
  set is contained in some exhaustion member.
-/
theorem IsComponentOf.isExteriorComponent_iff_not_subset_exhaustion_domains
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ)
    (E : SmoothRelativelyCompactExhaustion X) :
    IsExteriorComponent K U ↔
      ∀ n : ℕ, ¬ U ⊆ (E.domain n).carrier := by
  constructor
  · intro hExt n hUn
    exact hExt.not_subset_compact (E.domain n).compact_closure
      (hUn.trans subset_closure)
  · intro hnot
    refine hU.isExteriorComponent_iff_not_subset_compact.mpr ?_
    intro L hL hUL
    rcases smoothRelativelyCompactExhaustion_compact_subset_domain E hL with
      ⟨n, hLn⟩
    exact hnot n (hUL.trans hLn)

/--
%%handwave
name:
  Non-exterior criterion along a smooth exhaustion
statement:
  A complementary component is not exterior exactly when it is contained in
  some member of a smooth relatively compact exhaustion.
proof:
  This is the negation of the exhaustion-domain exterior criterion.
-/
theorem IsComponentOf.not_isExteriorComponent_iff_subset_exhaustion_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {K U : Set X} (hU : IsComponentOf U Kᶜ)
    (E : SmoothRelativelyCompactExhaustion X) :
    ¬ IsExteriorComponent K U ↔
      ∃ n : ℕ, U ⊆ (E.domain n).carrier := by
  classical
  constructor
  · intro hnot
    by_contra hno
    apply hnot
    exact hU.isExteriorComponent_iff_not_subset_exhaustion_domains E |>.mpr
      (by
        intro n hUn
        exact hno ⟨n, hUn⟩)
  · rintro ⟨n, hUn⟩ hExt
    exact hExt.not_subset_compact (E.domain n).compact_closure
      (hUn.trans subset_closure)

/--
%%handwave
name:
  Exterior components leave every exhaustion member
statement:
  An exterior component has a point outside each member of any smooth
  relatively compact exhaustion.
proof:
  Otherwise it would be contained in that exhaustion member, contradicting the
  exhaustion-domain exterior criterion.
-/
theorem IsExteriorComponent.exists_not_mem_exhaustion_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {K U : Set X} (hU : IsExteriorComponent K U)
    (E : SmoothRelativelyCompactExhaustion X) (n : ℕ) :
    ∃ x ∈ U, x ∉ (E.domain n).carrier := by
  rcases hU.exists_not_mem_compact (E.domain n).compact_closure with
    ⟨x, hxU, hx_closure⟩
  exact ⟨x, hxU, fun hx_domain => hx_closure (subset_closure hx_domain)⟩

/--
%%handwave
name:
  Finite complementary components force an exterior component
statement:
  If the complement of a compact set has only finitely many components in a
  noncompact surface with a smooth relatively compact exhaustion, then one of
  those components is exterior.
proof:
  If no component were exterior, each component would be contained in some
  exhaustion member.  Finiteness lets one choose a single later member
  containing all complementary components, while compactness puts the compact
  set itself into another exhaustion member.  Hence the whole surface would be
  contained in one relatively compact exhaustion member, contradicting
  noncompactness.
-/
theorem finite_complement_components_exteriorComponent_exists_of_smoothExhaustion
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X)
    {K : Set X} (hK : IsCompact K)
    (hfinite : {U : Set X | IsComponentOf U Kᶜ}.Finite) :
    ∃ U : Set X, IsExteriorComponent K U := by
  classical
  by_contra hno
  let components : Set (Set X) := {U : Set X | IsComponentOf U Kᶜ}
  have hbounded :
      ∀ U : Set X, U ∈ components →
        ∃ n : ℕ, U ⊆ (E.domain n).carrier := by
    intro U hU
    have hUcomp : IsComponentOf U Kᶜ := hU
    have hnotExt : ¬ IsExteriorComponent K U := by
      intro hExt
      exact hno ⟨U, hExt⟩
    exact (hUcomp.not_isExteriorComponent_iff_subset_exhaustion_domain E).mp
      hnotExt
  let nOf : components → ℕ :=
    fun U ↦ Classical.choose (hbounded U.1 U.2)
  let Ncomponents : ℕ :=
    hfinite.toFinset.sup
      (fun U ↦ if hU : U ∈ components then nOf ⟨U, hU⟩ else 0)
  have hle_component :
      ∀ {U : Set X} (hU : U ∈ components),
        nOf ⟨U, hU⟩ ≤ Ncomponents := by
    intro U hU
    have hmem : U ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr hU
    have hle :
        (if hU' : U ∈ components then nOf ⟨U, hU'⟩ else 0) ≤
          Ncomponents :=
      Finset.le_sup (f := fun U ↦
        if hU : U ∈ components then nOf ⟨U, hU⟩ else 0) hmem
    simpa [Ncomponents, hU] using hle
  have hcomponent_subset :
      ∀ {U : Set X} (hU : U ∈ components),
        U ⊆ (E.domain (nOf ⟨U, hU⟩)).carrier := by
    intro U hU
    exact Classical.choose_spec (hbounded U hU)
  rcases smoothRelativelyCompactExhaustion_compact_subset_domain E hK with
    ⟨NK, hK_subset⟩
  let N : ℕ := max NK Ncomponents
  have huniv_subset : (univ : Set X) ⊆ (E.domain N).carrier := by
    intro x _hx
    by_cases hxK : x ∈ K
    · exact smoothRelativelyCompactExhaustion_carrier_mono E
        (le_max_left NK Ncomponents) (hK_subset hxK)
    · have hxKc : x ∈ Kᶜ := hxK
      let C : Set X := connectedComponentIn Kᶜ x
      have hxC : x ∈ C := mem_connectedComponentIn hxKc
      have hCcomp : IsComponentOf C Kᶜ :=
        isComponentOf_connectedComponentIn hxKc
      have hCmem : C ∈ components := hCcomp
      have hxC_domain :
          x ∈ (E.domain (nOf ⟨C, hCmem⟩)).carrier :=
        hcomponent_subset hCmem hxC
      exact smoothRelativelyCompactExhaustion_carrier_mono E
        ((hle_component hCmem).trans (le_max_right NK Ncomponents))
        hxC_domain
  have hdomain_univ : (E.domain N).carrier = (univ : Set X) :=
    eq_univ_iff_forall.mpr fun x ↦ huniv_subset (mem_univ x)
  have hcompact_univ : IsCompact (univ : Set X) := by
    simpa [hdomain_univ] using (E.domain N).compact_closure
  exact hnoncompact ⟨hcompact_univ⟩

/--
%%handwave
name:
  Monotonicity of pointed components
statement:
  The component containing the base point in an earlier exhaustion member is
  contained in the corresponding component in every later member.
proof:
  Monotonicity of the exhaustion domains induces monotonicity of connected
  components inside those domains.
-/
theorem smoothRelativelyCompactExhaustion_pointed_components_mono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X} {m n : ℕ}
    (hmn : m ≤ n) :
    connectedComponentIn (E.domain m).carrier p ⊆
      connectedComponentIn (E.domain n).carrier p :=
  connectedComponentIn_mono p
    (smoothRelativelyCompactExhaustion_carrier_mono E hmn)

/--
%%handwave
name:
  Monotonicity of pointed-component closures
statement:
  The closure of an earlier pointed component is contained in the closure of
  every later pointed component.
proof:
  Pointed components are nested, and taking closure preserves inclusions.
-/
theorem smoothRelativelyCompactExhaustion_pointed_component_closure_mono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X} {m n : ℕ}
    (hmn : m ≤ n) :
    closure (connectedComponentIn (E.domain m).carrier p) ⊆
      closure (connectedComponentIn (E.domain n).carrier p) :=
  closure_mono (smoothRelativelyCompactExhaustion_pointed_components_mono E hmn)

/--
%%handwave
name:
  The base point lies in each pointed component
statement:
  If every exhaustion member contains \(p\), then \(p\) lies in the
  \(p\)-component of every member.
proof:
  A point of a set belongs to its own connected component within that set.
-/
theorem smoothRelativelyCompactExhaustion_pointed_component_base_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) (n : ℕ) :
    p ∈ connectedComponentIn (E.domain n).carrier p :=
  mem_connectedComponentIn (hp n)

/--
%%handwave
name:
  Pointed-component closures enter the next pointed component
statement:
  If every exhaustion member contains \(p\), then the closure of the
  \(p\)-component of one member lies in the \(p\)-component of the next member.
proof:
  The closure of the earlier pointed component lies in the next exhaustion
  member by the compact-containment condition.  It is preconnected, contains
  \(p\), and therefore lies in the next pointed component.
-/
theorem smoothRelativelyCompactExhaustion_pointed_component_closure_subset_next
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) (n : ℕ) :
    closure (connectedComponentIn (E.domain n).carrier p) ⊆
      connectedComponentIn (E.domain (n + 1)).carrier p := by
  have hclosure_subset_next :
      closure (connectedComponentIn (E.domain n).carrier p) ⊆
        (E.domain (n + 1)).carrier :=
    (closure_mono (connectedComponentIn_subset (E.domain n).carrier p)).trans
      (E.closure_subset_next n)
  have hp_closure :
      p ∈ closure (connectedComponentIn (E.domain n).carrier p) :=
    subset_closure (smoothRelativelyCompactExhaustion_pointed_component_base_mem
      E hp n)
  exact (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
    hp_closure hclosure_subset_next

/--
%%handwave
name:
  Pointed components are components
statement:
  If every exhaustion member contains \(p\), then the \(p\)-component of each
  member is a component of that member.
proof:
  Since \(p\) belongs to the member, its connected component within that member
  is nonempty, preconnected, contained there, and maximal.
-/
theorem smoothRelativelyCompactExhaustion_pointed_component_isComponentOf
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) (n : ℕ) :
    IsComponentOf (connectedComponentIn (E.domain n).carrier p)
      (E.domain n).carrier :=
  isComponentOf_connectedComponentIn (hp n)

/--
%%handwave
name:
  Pointed components are preconnected
statement:
  The \(p\)-component of an exhaustion member is preconnected.
proof:
  Connected components within a set are preconnected by construction.
-/
theorem smoothRelativelyCompactExhaustion_pointed_component_isPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) (p : X) (n : ℕ) :
    IsPreconnected (connectedComponentIn (E.domain n).carrier p) :=
  isPreconnected_connectedComponentIn

/--
%%handwave
name:
  Pointed components have compact closure
statement:
  The closure of each pointed component of a smooth relatively compact
  exhaustion member is compact.
proof:
  The pointed component lies in the exhaustion domain, so its closure is a
  closed subset of the compact closure of that domain.
-/
theorem smoothRelativelyCompactExhaustion_pointed_component_closure_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) (p : X) (n : ℕ) :
    IsCompact (closure (connectedComponentIn (E.domain n).carrier p)) :=
  smoothBoundaryDomain_pointedComponent_closure_compact (E.domain n) p

/--
%%handwave
name:
  Bounded-fillings of pointed exhaustion components are monotone
statement:
  If \(m\le n\), then the bounded filling of the \(m\)-th pointed component
  is contained in the bounded filling of the \(n\)-th pointed component.
proof:
  Pointed-component closures are monotone, and bounded filling is monotone
  with respect to inclusion of the closed obstacle.
-/
theorem smoothRelativelyCompactExhaustion_boundedFilling_mono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X} {m n : ℕ}
    (hmn : m ≤ n) :
    boundedFillingOfComplement
        (closure (connectedComponentIn (E.domain m).carrier p)) ⊆
      boundedFillingOfComplement
        (closure (connectedComponentIn (E.domain n).carrier p)) :=
  boundedFillingOfComplement_mono
    (smoothRelativelyCompactExhaustion_pointed_component_closure_mono E hmn)

/--
%%handwave
name:
  Closures of bounded fillings enter the next bounded filling
statement:
  If every exhaustion member contains \(p\), then the closure of the bounded
  filling attached to one pointed component lies in the next bounded filling.
proof:
  The bounded fillings are monotone.  The frontier of the earlier bounded
  filling lies on the earlier pointed-component closure, which is contained in
  the next pointed component, and the next pointed component lies in the next
  bounded filling.
-/
theorem smoothRelativelyCompactExhaustion_closure_boundedFilling_subset_next_boundedFilling
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) (n : ℕ) :
    closure
        (boundedFillingOfComplement
          (closure (connectedComponentIn (E.domain n).carrier p))) ⊆
      boundedFillingOfComplement
        (closure (connectedComponentIn (E.domain (n + 1)).carrier p)) := by
  let Kₙ : Set X := closure (connectedComponentIn (E.domain n).carrier p)
  let Knext : Set X :=
    closure (connectedComponentIn (E.domain (n + 1)).carrier p)
  have hfilled_subset :
      boundedFillingOfComplement Kₙ ⊆
        boundedFillingOfComplement Knext := by
    simpa [Kₙ, Knext] using
      smoothRelativelyCompactExhaustion_boundedFilling_mono
        E (Nat.le_succ n)
  have hfrontier_subset_K :
      frontier (boundedFillingOfComplement Kₙ) ⊆ Kₙ :=
    boundedFillingOfComplement_frontier_subset_obstacle isClosed_closure
  have hK_subset_next_component :
      Kₙ ⊆ connectedComponentIn (E.domain (n + 1)).carrier p := by
    simpa [Kₙ] using
      smoothRelativelyCompactExhaustion_pointed_component_closure_subset_next
        E hp n
  have hnext_component_subset_filled :
      connectedComponentIn (E.domain (n + 1)).carrier p ⊆
        boundedFillingOfComplement Knext := by
    simpa [Knext] using
      smoothBoundaryDomain_pointedComponent_subset_boundedFilling
        (E.domain (n + 1)) p
  have hfrontier_subset_filled :
      frontier (boundedFillingOfComplement Kₙ) ⊆
        boundedFillingOfComplement Knext :=
    hfrontier_subset_K.trans
      (hK_subset_next_component.trans hnext_component_subset_filled)
  intro x hx
  rw [closure_eq_self_union_frontier] at hx
  exact hx.elim
    (fun hx_fill => hfilled_subset hx_fill)
    (fun hx_frontier => hfrontier_subset_filled hx_frontier)

/--
%%handwave
name:
  Filled sides of pointed components are monotone
statement:
  Suppose \(m\le n\).  If \(U_m\) and \(U_n\) are the exterior components of
  the complements of the closures of the corresponding pointed components,
  and the exterior component at \(m\) is unique, then the filled side at \(m\)
  is contained in the filled side at \(n\).
proof:
  The pointed-component closures are nested.  Hence the exterior component for
  the larger closure lies inside the earlier exterior component, and filled
  sides are ordered in the opposite direction.
-/
theorem smoothRelativelyCompactExhaustion_filledSide_mono_of_unique_exteriorComponents
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X} {m n : ℕ}
    (hmn : m ≤ n) {U_m U_n : Set X}
    (hU_m : IsExteriorComponent
      (closure (connectedComponentIn (E.domain m).carrier p)) U_m)
    (hU_n : IsExteriorComponent
      (closure (connectedComponentIn (E.domain n).carrier p)) U_n)
    (hunique_m :
      ∀ V : Set X,
        IsExteriorComponent
          (closure (connectedComponentIn (E.domain m).carrier p)) V →
          V = U_m) :
    filledSideOfExteriorComponent U_m ⊆
      filledSideOfExteriorComponent U_n :=
  hU_m.filledSide_subset_of_subset_left_of_unique
    (smoothRelativelyCompactExhaustion_pointed_component_closure_mono E hmn)
    hU_n hunique_m

/--
%%handwave
name:
  Closures of filled sides enter the next filled side
statement:
  If every exhaustion member contains \(p\), then the closure of the filled
  side attached to one pointed component lies in the next filled side, provided
  the earlier exterior component is unique.
proof:
  The filled sides themselves are nested.  Their frontiers lie on the earlier
  pointed-component closure, and that closure lies inside the next pointed
  component.  Since the next pointed component lies in the next filled side,
  the closure of the earlier filled side is contained in the next filled side.
-/
theorem smoothRelativelyCompactExhaustion_closure_filledSide_subset_next_filledSide_of_unique_exteriorComponents
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) (n : ℕ)
    {U_n U_next : Set X}
    (hU_n : IsExteriorComponent
      (closure (connectedComponentIn (E.domain n).carrier p)) U_n)
    (hU_next : IsExteriorComponent
      (closure (connectedComponentIn (E.domain (n + 1)).carrier p)) U_next)
    (hunique_n :
      ∀ V : Set X,
        IsExteriorComponent
          (closure (connectedComponentIn (E.domain n).carrier p)) V →
          V = U_n) :
    closure (filledSideOfExteriorComponent U_n) ⊆
      filledSideOfExteriorComponent U_next := by
  have hfilled_subset :
      filledSideOfExteriorComponent U_n ⊆
        filledSideOfExteriorComponent U_next :=
    smoothRelativelyCompactExhaustion_filledSide_mono_of_unique_exteriorComponents
      E (Nat.le_succ n) hU_n hU_next hunique_n
  have hfrontier_subset_K :
      frontier (filledSideOfExteriorComponent U_n) ⊆
        closure (connectedComponentIn (E.domain n).carrier p) :=
    hU_n.frontier_filledSide_subset_of_isClosed isClosed_closure
  have hK_subset_next_component :
      closure (connectedComponentIn (E.domain n).carrier p) ⊆
        connectedComponentIn (E.domain (n + 1)).carrier p :=
    smoothRelativelyCompactExhaustion_pointed_component_closure_subset_next
      E hp n
  have hnext_component_subset_filled :
      connectedComponentIn (E.domain (n + 1)).carrier p ⊆
        filledSideOfExteriorComponent U_next :=
    smoothBoundaryDomain_pointedComponent_subset_filledSide_of_exteriorComponent_closure
      (E.domain (n + 1)) p hU_next
  have hfrontier_subset_filled :
      frontier (filledSideOfExteriorComponent U_n) ⊆
        filledSideOfExteriorComponent U_next :=
    hfrontier_subset_K.trans
      (hK_subset_next_component.trans hnext_component_subset_filled)
  intro x hx
  rw [closure_eq_self_union_frontier] at hx
  exact hx.elim (fun hx_filled => hfilled_subset hx_filled)
    (fun hx_frontier => hfrontier_subset_filled hx_frontier)

/--
%%handwave
name:
  Pointed components of an exhaustion exhaust
statement:
  If a smooth exhaustion of a simply connected surface contains a fixed point
  \(p\) in every member, then the components containing \(p\) still exhaust
  the surface.
proof:
  Given \(x\), choose a path from \(p\) to \(x\).  The path image is compact,
  so it is contained in a sufficiently late member of the exhaustion.  Thus
  \(p\) and \(x\) lie in the same component of that member.
-/
theorem smoothRelativelyCompactExhaustion_pointed_components_exhaust
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (_hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) :
    ∀ x : X, ∃ n : ℕ, x ∈ connectedComponentIn (E.domain n).carrier p := by
  classical
  intro x
  let γ : Path p x := PathConnectedSpace.somePath p x
  have hγ_compact : IsCompact (range γ) :=
    isCompact_range γ.continuous
  have hγ_subset : ∃ n : ℕ, range γ ⊆ (E.domain n).carrier :=
    smoothRelativelyCompactExhaustion_compact_subset_domain E hγ_compact
  rcases hγ_subset with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hpre : IsPreconnected (range γ) :=
    (isConnected_range γ.continuous).isPreconnected
  have hrange_component : range γ ⊆ connectedComponentIn (E.domain n).carrier p :=
    hpre.subset_connectedComponentIn (Path.source_mem_range γ) hn
  exact hrange_component (Path.target_mem_range γ)

/--
%%handwave
name:
  Points eventually stay in pointed components
statement:
  If all exhaustion members contain \(p\), then every point lies in the
  \(p\)-component of every sufficiently late member.
proof:
  Once the point lies in one pointed component, monotonicity of pointed
  components keeps it there for all later indices.
-/
theorem smoothRelativelyCompactExhaustion_pointed_components_eventually_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) :
    ∀ x : X, ∀ᶠ n : ℕ in Filter.atTop,
      x ∈ connectedComponentIn (E.domain n).carrier p := by
  intro x
  rcases smoothRelativelyCompactExhaustion_pointed_components_exhaust
      (E := E) hp x with ⟨N, hxN⟩
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact smoothRelativelyCompactExhaustion_pointed_components_mono E hn hxN

/--
%%handwave
name:
  Points eventually lie in filled sides
statement:
  If \(U_n\) is an exterior component of the complement of the closure of the
  \(p\)-component of the \(n\)-th exhaustion member, then every point lies in
  the corresponding filled side for all sufficiently large \(n\).
proof:
  Every point eventually lies in the pointed component itself, and each
  pointed component lies in the filled side determined by its exterior
  component.
-/
theorem smoothRelativelyCompactExhaustion_eventually_mem_filledSide_of_exteriorComponents
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (U : ℕ → Set X)
    (hU : ∀ n : ℕ,
      IsExteriorComponent
        (closure (connectedComponentIn (E.domain n).carrier p)) (U n)) :
    ∀ x : X, ∀ᶠ n : ℕ in Filter.atTop,
      x ∈ filledSideOfExteriorComponent (U n) := by
  intro x
  filter_upwards
    [smoothRelativelyCompactExhaustion_pointed_components_eventually_mem
      E hp x] with n hxn
  exact smoothBoundaryDomain_pointedComponent_subset_filledSide_of_exteriorComponent_closure
    (E.domain n) p (hU n) hxn

/--
%%handwave
name:
  Pointed components cover the surface
statement:
  If all exhaustion members contain \(p\), then the union of the pointed
  components is the whole surface.
proof:
  For any point \(x\), choose a path from \(p\) to \(x\).  Its compact image is
  contained in some exhaustion member, so \(x\) and \(p\) lie in the same
  component of that member.
-/
theorem smoothRelativelyCompactExhaustion_iUnion_pointed_components_eq_univ
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) :
    (⋃ n : ℕ, connectedComponentIn (E.domain n).carrier p) = (univ : Set X) := by
  ext x
  constructor
  · intro _hx
    exact mem_univ x
  · intro _hx
    exact mem_iUnion.mpr
      (smoothRelativelyCompactExhaustion_pointed_components_exhaust (E := E) hp x)

/--
%%handwave
name:
  Domainwise cohomology vanishing gives a filled cohomology exhaustion
statement:
  Suppose the bounded filling of every pointed component of every smooth
  relatively compact domain has vanishing first real de Rham cohomology.
  Then any smooth exhaustion can be replaced by a pointed bounded-filling
  exhaustion with vanishing first cohomology.
proof:
  Discard finitely many initial members so the base point lies in every
  remaining domain.  Take the bounded filling of each pointed component.
  Monotonicity, compact containment in the next member, and coverage follow
  from the corresponding bounded-filling lemmas, while the assumed
  one-domain result supplies cohomology vanishing member by member.
-/
theorem smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_domainwise
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hzero :
      ∀ (D : SmoothBoundaryDomain X) {q : X}, q ∈ D.carrier →
        ∀ Dhat : SmoothBoundaryDomain X,
          Dhat.carrier =
            boundedFillingOfComplement
              (closure (connectedComponentIn D.carrier q)) →
          Dhat.deRhamH1Zero)
    (E : SmoothRelativelyCompactExhaustion X) (p : X) :
    Nonempty (PointedH1ZeroSmoothRelativelyCompactExhaustion X p) := by
  classical
  rcases E.exhausts p with ⟨N₀, hpN₀⟩
  let E₀ : SmoothRelativelyCompactExhaustion X :=
    { domain := fun n => E.domain (N₀ + n)
      monotone := by
        intro n
        exact smoothRelativelyCompactExhaustion_carrier_mono E
          (Nat.add_le_add_left (Nat.le_succ n) N₀)
      closure_subset_next := by
        intro n
        simpa [Nat.add_assoc] using E.closure_subset_next (N₀ + n)
      exhausts := by
        intro x
        rcases E.exhausts x with ⟨m, hxm⟩
        refine ⟨m, ?_⟩
        exact smoothRelativelyCompactExhaustion_carrier_mono E
          (Nat.le_add_left m N₀) hxm }
  have hp₀ : ∀ n : ℕ, p ∈ (E₀.domain n).carrier := by
    intro n
    exact smoothRelativelyCompactExhaustion_carrier_mono E
      (Nat.le_add_right N₀ n) hpN₀
  let filledDomainExists :
      (n : ℕ) →
        ∃ Dhat : SmoothBoundaryDomain X,
          Dhat.carrier =
            boundedFillingOfComplement
              (closure (connectedComponentIn (E₀.domain n).carrier p)) :=
    fun n =>
      smoothBoundaryDomain_exists_domain_with_boundedFilling_carrier
        (D := E₀.domain n) (hp₀ n)
  let Dhat : ℕ → SmoothBoundaryDomain X :=
    fun n => Classical.choose (filledDomainExists n)
  have hDhat_carrier : ∀ n : ℕ,
      (Dhat n).carrier =
        boundedFillingOfComplement
          (closure (connectedComponentIn (E₀.domain n).carrier p)) := by
    intro n
    exact Classical.choose_spec (filledDomainExists n)
  let Ehat : SmoothRelativelyCompactExhaustion X :=
    { domain := Dhat
      monotone := by
        intro n
        rw [hDhat_carrier n, hDhat_carrier (n + 1)]
        exact smoothRelativelyCompactExhaustion_boundedFilling_mono
          E₀ (Nat.le_succ n)
      closure_subset_next := by
        intro n
        rw [hDhat_carrier n, hDhat_carrier (n + 1)]
        exact
          smoothRelativelyCompactExhaustion_closure_boundedFilling_subset_next_boundedFilling
            E₀ hp₀ n
      exhausts := by
        intro x
        rcases smoothRelativelyCompactExhaustion_pointed_components_exhaust
            (E := E₀) hp₀ x with ⟨n, hxn⟩
        refine ⟨n, ?_⟩
        rw [hDhat_carrier n]
        exact smoothBoundaryDomain_pointedComponent_subset_boundedFilling
          (E₀.domain n) p hxn }
  exact ⟨
    { toSmoothRelativelyCompactExhaustion := Ehat
      base_mem := by
        intro n
        change p ∈ (Dhat n).carrier
        rw [hDhat_carrier n]
        exact smoothBoundaryDomain_base_mem_boundedFilling
          (E₀.domain n) (hp₀ n)
      pathConnected := by
        intro n
        change PathConnectedSpace (Dhat n).carrier
        rw [hDhat_carrier n]
        exact smoothBoundaryDomain_boundedFilling_pathConnected
          (E₀.domain n) (hp₀ n)
      deRhamH1Zero := by
        intro n
        exact hzero (E₀.domain n) (hp₀ n) (Dhat n)
          (hDhat_carrier n) }⟩





end Uniformization

end JJMath
