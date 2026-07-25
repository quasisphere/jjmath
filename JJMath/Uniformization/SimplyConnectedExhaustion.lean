import JJMath.Uniformization.LiouvilleExistence
import JJMath.Uniformization.RadoSecondCountable
import JJMath.Uniformization.SimplyConnectedOneForm
import Mathlib.Topology.UrysohnsLemma
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

/--
%%handwave
name: Domain at an exhaustion index
statement:
  For $n\in\mathbb N$, take the $n$-th smooth relatively compact domain in
  the pointed exhaustion.
-/
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

end PointedH1ZeroSmoothRelativelyCompactExhaustion

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
