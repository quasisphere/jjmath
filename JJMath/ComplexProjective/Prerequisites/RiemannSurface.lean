import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected

/-!
# Riemann surfaces

This file fixes the typeclass assumptions used by the project.  A complex
one-manifold is a Hausdorff manifold modelled on `ℂ`, and a Riemann surface is
a connected complex one-manifold.

Local path-connectedness and local simple connectedness are consequences of
the complex charts.  Path-connectedness then follows from connectedness, so
none of these properties is stored independently in the Riemann-surface class.
-/

namespace JJMath

open scoped Manifold

/--
A locally simply connected space, stated in the neighborhood-refinement form
needed by the path-homotopy universal-cover construction.

At every point and inside every open neighborhood, there is an open, path
connected, simply connected smaller neighborhood.
-/
class LocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  exists_isOpen_simplyConnected_subset :
    ∀ x (N : Set X), x ∈ N → IsOpen N →
      ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ N ∧
        Nonempty (PathConnectedSpace U) ∧ Nonempty (SimplyConnectedSpace U)

namespace LocallySimplyConnectedSpace

variable {X : Type*} [TopologicalSpace X] [LocallySimplyConnectedSpace X]

/-- A convenience wrapper for the local simply connected refinement property. -/
theorem exists_subset (x : X) {N : Set X} (hxN : x ∈ N) (hN : IsOpen N) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ N ∧
      Nonempty (PathConnectedSpace U) ∧ Nonempty (SimplyConnectedSpace U) :=
  LocallySimplyConnectedSpace.exists_isOpen_simplyConnected_subset x N hxN hN

end LocallySimplyConnectedSpace

/--
A chosen simply connected open neighborhood inside a prescribed open
neighborhood.
-/
structure SimplyConnectedOpenNeighborhood {X : Type*} [TopologicalSpace X]
    (x : X) (N : Set X) where
  /-- The selected neighborhood. -/
  carrier : Set X
  /-- The point lies in the selected neighborhood. -/
  mem_carrier : x ∈ carrier
  /-- The selected neighborhood is open. -/
  carrier_open : IsOpen carrier
  /-- The selected neighborhood lies in the prescribed set. -/
  carrier_subset : carrier ⊆ N
  /-- The selected neighborhood is path connected. -/
  [carrier_pathConnected : PathConnectedSpace carrier]
  /-- The selected neighborhood is simply connected. -/
  [carrier_simplyConnected : SimplyConnectedSpace carrier]

attribute [instance] SimplyConnectedOpenNeighborhood.carrier_pathConnected
attribute [instance] SimplyConnectedOpenNeighborhood.carrier_simplyConnected

namespace SimplyConnectedOpenNeighborhood

variable {X : Type*} [TopologicalSpace X] [LocallySimplyConnectedSpace X]

/-- Choose a simply connected open refinement of an open neighborhood. -/
noncomputable def choose {x : X} {N : Set X} (hxN : x ∈ N) (hN : IsOpen N) :
    SimplyConnectedOpenNeighborhood x N :=
  let h := LocallySimplyConnectedSpace.exists_subset x hxN hN
  let U := Classical.choose h
  have hU := Classical.choose_spec h
  { carrier := U
    mem_carrier := hU.1
    carrier_open := hU.2.1
    carrier_subset := hU.2.2.1
    carrier_pathConnected := hU.2.2.2.1.some
    carrier_simplyConnected := hU.2.2.2.2.some }

end SimplyConnectedOpenNeighborhood

/-- A Hausdorff complex one-manifold, with no connectedness assumption. -/
class ComplexOneManifold (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop
    extends T2Space X, IsManifold 𝓘(ℂ) ⊤ X

/-- The complex plane has its standard complex one-manifold structure. -/
instance ComplexOneManifold.complex : ComplexOneManifold ℂ where
  toT2Space := inferInstance
  toIsManifold := inferInstance

/-- Complex one-manifolds are locally compact. -/
instance ComplexOneManifold.locallyCompactSpace
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] :
    LocallyCompactSpace X :=
  Manifold.locallyCompact_of_finiteDimensional 𝓘(ℂ)

/-- Complex one-manifolds are locally path connected, as this property is
transported through their charts from `ℂ`. -/
instance ComplexOneManifold.locPathConnectedSpace
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] :
    LocPathConnectedSpace X :=
  ChartedSpace.locPathConnectedSpace ℂ X

/-- Complex one-manifolds are locally simply connected.  Inside any prescribed
open neighborhood, pull a sufficiently small complex ball back through a
chart. -/
noncomputable instance ComplexOneManifold.locallySimplyConnectedSpace
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] :
    LocallySimplyConnectedSpace X where
  exists_isOpen_simplyConnected_subset := by
    intro x N hxN hN
    let e := chartAt ℂ x
    have hxsource : x ∈ e.source := mem_chart_source ℂ x
    have hopen : IsOpen (e '' (e.source ∩ N)) :=
      e.isOpen_image_of_subset_source (e.open_source.inter hN) Set.inter_subset_left
    have hximage : e x ∈ e '' (e.source ∩ N) :=
      ⟨x, ⟨hxsource, hxN⟩, rfl⟩
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen (e x) hximage
    let V : Set ℂ := Metric.ball (e x) r
    let U : Set X := e.symm '' V
    have hVtarget : V ⊆ e.target := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hrsub hz
      exact e.mapsTo hw.1
    have hxU : x ∈ U := by
      refine ⟨e x, Metric.mem_ball_self hr, ?_⟩
      exact e.left_inv hxsource
    have hUopen : IsOpen U :=
      e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hVtarget
    have hUN : U ⊆ N := by
      rintro y ⟨z, hzV, rfl⟩
      obtain ⟨w, hw, hwz⟩ := hrsub hzV
      rw [← hwz, e.left_inv hw.1]
      exact hw.2
    have hVsourceSymm : V ⊆ e.symm.source := by
      simpa using hVtarget
    let hVU : V ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hVsourceSymm rfl
    haveI : ContractibleSpace V := Metric.contractibleSpace_ball hr
    haveI : ContractibleSpace U := hVU.symm.contractibleSpace
    exact ⟨U, hxU, hUopen, hUN, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- A Riemann surface is a connected complex one-manifold. -/
class RiemannSurface (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop
    extends ComplexOneManifold X, ConnectedSpace X

/-- The complex plane is a Riemann surface. -/
instance RiemannSurface.complex : RiemannSurface ℂ where
  toComplexOneManifold := inferInstance
  toConnectedSpace := inferInstance

/-- A Riemann surface is path connected because it is connected and locally
path connected. -/
instance (priority := 100) RiemannSurface.pathConnectedSpace
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] :
    PathConnectedSpace X :=
  PathConnectedSpace.of_locPathConnectedSpace

end JJMath
