import Mathlib

/-!
# Simply connected uniformization: comparator challenge

This file deliberately imports only Mathlib.  The declarations below reproduce
the statement-level interface used by the project theorem, so Comparator can
check the project proof without trusting any project module on the challenge
side.
-/

namespace JJMath

open Filter Set
open scoped Manifold MatrixGroups Topology

noncomputable section

section StatementInterface

attribute [local instance 2000] NormedField.toNormedCommRing
attribute [local instance 2000] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance 2000] InnerProductSpace.toNormedSpace
attribute [local instance 2000] TopologicalSpace.PseudoMetrizableSpace.regularSpace
attribute [local instance 2000] T2Space.t1Space

/-- The Riemann sphere, represented as the one-point compactification of `ℂ`. -/
abbrev RiemannSphere : Type :=
  OnePoint ℂ

/-- A Hausdorff complex one-manifold, with no connectedness assumption. -/
class ComplexOneManifold (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop
    extends T2Space X, IsManifold 𝓘(ℂ) ⊤ X

/-- A Riemann surface is a connected complex one-manifold. -/
class RiemannSurface (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop
    extends ComplexOneManifold X, ConnectedSpace X

section RiemannSphereInversion

local instance instDecidableEqComplex_jJMath : DecidableEq ℂ := Classical.decEq ℂ

/-- Inversion on the finite part of the Riemann sphere, with `0` sent to infinity. -/
def riemannSphereInvFinite (z : ℂ) : RiemannSphere :=
  if z = 0 then OnePoint.infty else ((z⁻¹ : ℂ) : RiemannSphere)

/-- Inversion on the Riemann sphere, exchanging `0` and infinity. -/
def riemannSphereInv (z : RiemannSphere) : RiemannSphere :=
  z.elim ((0 : ℂ) : RiemannSphere) riemannSphereInvFinite

@[simp]
theorem riemannSphereInv_infty :
    riemannSphereInv OnePoint.infty = ((0 : ℂ) : RiemannSphere) :=
  rfl

@[simp]
theorem riemannSphereInv_zero :
    riemannSphereInv ((0 : ℂ) : RiemannSphere) = OnePoint.infty := by
  simp [riemannSphereInv, riemannSphereInvFinite]

@[simp]
theorem riemannSphereInv_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    riemannSphereInv (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := by
  simp [riemannSphereInv, riemannSphereInvFinite, hz]

/-- The finite-part inversion map into the Riemann sphere is continuous. -/
theorem riemannSphereInvFinite_continuous :
    Continuous riemannSphereInvFinite := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    rw [ContinuousAt, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
    constructor
    · have hinv : Tendsto Inv.inv (𝓝[≠] (0 : ℂ)) (Filter.coclosedCompact ℂ) := by
        simpa [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
          (tendsto_inv₀_nhdsNE_zero (α := ℂ))
      have hpunct :
          Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere))
            (𝓝[≠] (0 : ℂ)) (𝓝 (OnePoint.infty : RiemannSphere)) :=
        OnePoint.tendsto_coe_infty.comp hinv
      simpa [riemannSphereInvFinite] using hpunct.congr' (by
        filter_upwards [eventually_mem_nhdsWithin] with w hw
        have hne : w ≠ 0 := by simpa using hw
        simp [riemannSphereInvFinite, hne])
    · exact tendsto_pure_nhds (f := riemannSphereInvFinite) (a := (0 : ℂ))
  · have hlocal :
        riemannSphereInvFinite =ᶠ[𝓝 z] fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp [riemannSphereInvFinite, hw]
    have hinv :
        Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere)) (𝓝 z)
          (𝓝 (((z⁻¹ : ℂ) : RiemannSphere))) :=
      OnePoint.continuous_coe.continuousAt.comp (tendsto_inv₀ hz)
    change Tendsto riemannSphereInvFinite (𝓝 z) (𝓝 (riemannSphereInvFinite z))
    simpa [riemannSphereInvFinite, hz] using hinv.congr' hlocal.symm

/-- Inversion is continuous on the Riemann sphere. -/
theorem riemannSphereInv_continuous :
    Continuous riemannSphereInv := by
  rw [OnePoint.continuous_iff]
  constructor
  · have hinv : Tendsto Inv.inv (Filter.coclosedCompact ℂ) (𝓝 (0 : ℂ)) := by
      simpa [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded (α := ℂ))
    have hcoe :
        Tendsto (fun z : ℂ ↦ ((z⁻¹ : ℂ) : RiemannSphere))
          (Filter.coclosedCompact ℂ) (𝓝 (((0 : ℂ) : RiemannSphere))) :=
      (OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hinv
    have hzeroCompl : ({(0 : ℂ)} : Set ℂ)ᶜ ∈ Filter.coclosedCompact ℂ :=
      (isCompact_singleton (x := (0 : ℂ))).compl_mem_coclosedCompact_of_isClosed
        isClosed_singleton
    refine hcoe.congr' ?_
    filter_upwards [hzeroCompl] with z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp [riemannSphereInv, riemannSphereInvFinite, hz]
  · simpa [riemannSphereInv] using riemannSphereInvFinite_continuous

end RiemannSphereInversion

section RiemannSphereCharts

local instance : DecidableEq RiemannSphere := Classical.decEq RiemannSphere

/-- Inversion on the Riemann sphere is an involution. -/
theorem riemannSphereInv_involutive : Function.Involutive riemannSphereInv := by
  intro z
  induction z using OnePoint.rec with
  | infty => simp
  | coe z =>
      by_cases hz : z = 0
      · subst z
        simp
      · rw [riemannSphereInv_coe_of_ne_zero hz]
        rw [riemannSphereInv_coe_of_ne_zero (inv_ne_zero hz)]
        simp

@[simp]
theorem riemannSphereInv_inv (z : RiemannSphere) :
    riemannSphereInv (riemannSphereInv z) = z :=
  riemannSphereInv_involutive z

/-- Inversion as a self-homeomorphism of the Riemann sphere. -/
def riemannSphereInvHomeomorph : RiemannSphere ≃ₜ RiemannSphere where
  toFun := riemannSphereInv
  invFun := riemannSphereInv
  left_inv := riemannSphereInv_involutive
  right_inv := riemannSphereInv_involutive
  continuous_toFun := riemannSphereInv_continuous
  continuous_invFun := riemannSphereInv_continuous

@[simp]
theorem riemannSphereInvHomeomorph_apply (z : RiemannSphere) :
    riemannSphereInvHomeomorph z = riemannSphereInv z :=
  rfl

/-- The affine coordinate on the finite part of the Riemann sphere. -/
def riemannSphereFiniteChart : OpenPartialHomeomorph RiemannSphere ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph
    ((↑) : ℂ → RiemannSphere)).symm

@[simp]
theorem riemannSphereFiniteChart_source :
    riemannSphereFiniteChart.source = ({OnePoint.infty} : Set RiemannSphere)ᶜ := by
  simp [riemannSphereFiniteChart, OnePoint.compl_infty]

@[simp]
theorem riemannSphereFiniteChart_target :
    riemannSphereFiniteChart.target = Set.univ := by
  simp [riemannSphereFiniteChart]

@[simp]
theorem riemannSphereFiniteChart_coe (z : ℂ) :
    riemannSphereFiniteChart (z : RiemannSphere) = z := by
  simpa [riemannSphereFiniteChart] using
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      ((↑) : ℂ → RiemannSphere) OnePoint.isOpenEmbedding_coe (x := z))

@[simp]
theorem riemannSphereFiniteChart_symm_apply (z : ℂ) :
    riemannSphereFiniteChart.symm z = (z : RiemannSphere) :=
  rfl

/-- The reciprocal coordinate near infinity. -/
def riemannSphereInfinityChart : OpenPartialHomeomorph RiemannSphere ℂ :=
  riemannSphereInvHomeomorph.toOpenPartialHomeomorph.trans riemannSphereFiniteChart

@[simp]
theorem riemannSphereInfinityChart_source :
    riemannSphereInfinityChart.source = ({((0 : ℂ) : RiemannSphere)} : Set RiemannSphere)ᶜ := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [riemannSphereInfinityChart]
  | coe z =>
      by_cases hz : z = 0
      · subst z
        simp [riemannSphereInfinityChart]
      · simp [riemannSphereInfinityChart, hz, riemannSphereInv_coe_of_ne_zero]

@[simp]
theorem riemannSphereInfinityChart_target :
    riemannSphereInfinityChart.target = Set.univ := by
  simp [riemannSphereInfinityChart]

@[simp]
theorem riemannSphereInfinityChart_symm_apply (z : ℂ) :
    riemannSphereInfinityChart.symm z = riemannSphereInv (z : RiemannSphere) :=
  rfl

@[simp]
theorem riemannSphereInfinityChart_infty :
    riemannSphereInfinityChart OnePoint.infty = 0 := by
  simp [riemannSphereInfinityChart]

@[simp]
theorem riemannSphereInfinityChart_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    riemannSphereInfinityChart (z : RiemannSphere) = z⁻¹ := by
  simp [riemannSphereInfinityChart, riemannSphereInv_coe_of_ne_zero hz]

@[simp]
theorem riemannSphereInfinityChart_inv_coe (z : ℂ) :
    riemannSphereInfinityChart (riemannSphereInv (z : RiemannSphere)) = z := by
  by_cases hz : z = 0
  · subst z
    simp
  · simp [riemannSphereInv_coe_of_ne_zero hz, inv_ne_zero hz]

/-- The standard two-chart complex atlas on the Riemann sphere. -/
noncomputable instance instChartedSpaceComplexRiemannSphere :
    ChartedSpace ℂ RiemannSphere where
  atlas := {riemannSphereFiniteChart, riemannSphereInfinityChart}
  chartAt z := if z = OnePoint.infty then
      riemannSphereInfinityChart
    else
      riemannSphereFiniteChart
  mem_chart_source z := by
    by_cases hz : z = OnePoint.infty
    · subst z
      simp
    · simp [hz]
  chart_mem_atlas z := by
    by_cases hz : z = OnePoint.infty <;> simp [hz]

end RiemannSphereCharts

namespace Uniformization

universe u v

/-- The unit disk inherits its complex chart from its open embedding in `ℂ`. -/
noncomputable instance instChartedSpaceComplexUnitDisc :
    ChartedSpace ℂ Complex.UnitDisc :=
  Topology.IsOpenEmbedding.singletonChartedSpace
    (show Topology.IsOpenEmbedding ((↑) : Complex.UnitDisc → ℂ) from
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal)

/-- A holomorphic map between complex manifolds. -/
def HolomorphicMap (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f

/-- A biholomorphic equivalence. -/
structure Biholomorphic (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] where
  toHomeomorph : X ≃ₜ Y
  holomorphic_toFun : HolomorphicMap X Y toHomeomorph
  holomorphic_invFun : HolomorphicMap Y X toHomeomorph.symm

/-- The proposition that two complex manifolds are biholomorphic. -/
def BiholomorphicSurfaces (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] : Prop :=
  Nonempty (@Biholomorphic X Y inferInstance inferInstance inferInstance inferInstance)

end Uniformization

end StatementInterface

namespace Uniformization

/-- Every simply connected Riemann surface has one of the three standard models. -/
theorem simplyConnected_riemannSurface_uniformization
    (X : Type) [t : TopologicalSpace X] [c : ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X] :
    BiholomorphicSurfaces X RiemannSphere ∨
      @BiholomorphicSurfaces X ℂ t c
        (@UniformSpace.toTopologicalSpace ℂ
          (@PseudoMetricSpace.toUniformSpace ℂ
            (@SeminormedRing.toPseudoMetricSpace ℂ
              (@SeminormedCommRing.toSeminormedRing ℂ
                (@NormedCommRing.toSeminormedCommRing ℂ
                  (@CommCStarAlgebra.toNormedCommRing ℂ instCommCStarAlgebraComplex))))))
        (@chartedSpaceSelf ℂ
          (@UniformSpace.toTopologicalSpace ℂ
            (@PseudoMetricSpace.toUniformSpace ℂ
              (@SeminormedRing.toPseudoMetricSpace ℂ
                (@SeminormedCommRing.toSeminormedRing ℂ
                  (@NormedCommRing.toSeminormedCommRing ℂ
                    (@NormedField.toNormedCommRing ℂ Complex.instNormedField))))))) ∨
        BiholomorphicSurfaces X Complex.UnitDisc := by
  sorry

end Uniformization

end

end JJMath
