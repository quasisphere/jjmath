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

/--
%%handwave
name:
  Inversion sends infinity to zero
statement:
  On the Riemann sphere, inversion satisfies \(I(\infty)=0\).
proof:
  This is the defining value of inversion at the point at infinity.
-/
@[simp]
theorem riemannSphereInv_infty :
    riemannSphereInv OnePoint.infty = ((0 : ℂ) : RiemannSphere) :=
  rfl

/--
%%handwave
name:
  Inversion sends zero to infinity
statement:
  On the Riemann sphere, inversion satisfies \(I(0)=\infty\).
proof:
  Substitute zero into the piecewise definition of finite inversion.
-/
@[simp]
theorem riemannSphereInv_zero :
    riemannSphereInv ((0 : ℂ) : RiemannSphere) = OnePoint.infty := by
  simp [riemannSphereInv, riemannSphereInvFinite]

/--
%%handwave
name:
  Inversion at a nonzero finite point
statement:
  For every \(z\in\mathbb C\) with \(z\ne0\), inversion on the Riemann sphere
  satisfies \(I(z)=z^{-1}\).
proof:
  The nonzero branch of the piecewise definition is the ordinary reciprocal.
-/
@[simp]
theorem riemannSphereInv_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    riemannSphereInv (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := by
  simp [riemannSphereInv, riemannSphereInvFinite, hz]

/--
%%handwave
name:
  Continuity of finite inversion into the Riemann sphere
statement:
  The map \(z\mapsto \infty\) at \(z=0\) and \(z\mapsto z^{-1}\) otherwise,
  regarded as a map from \(\mathbb C\) to \(\widehat{\mathbb C}\), is continuous.
proof:
  Away from zero this is continuity of reciprocal followed by the finite-part embedding. At zero, reciprocal tends to infinity along punctured neighborhoods, while the assigned value handles the remaining pure neighborhood.
-/
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

/--
%%handwave
name:
  Continuity of inversion on the Riemann sphere
statement:
  The map \(I:\widehat{\mathbb C}\to\widehat{\mathbb C}\) that exchanges
  \(0\) and \(\infty\) and sends every other finite point \(z\) to \(z^{-1}\)
  is continuous.
proof:
  On the finite part use continuity of finite inversion. At infinity, reciprocal tends to zero along the cocompact filter, so the one-point compactification continuity criterion applies.
-/
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

/--
%%handwave
name:
  Riemann-sphere inversion is involutive
statement:
  Every \(z\in\widehat{\mathbb C}\) satisfies \(I(I(z))=z\).
proof:
  Split into the point at infinity and finite points. Zero and infinity are exchanged; for \(z\ne0\), applying reciprocal twice returns \(z\).
-/
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

/--
%%handwave
name:
  Double inversion on the Riemann sphere
statement:
  For every \(z\in\widehat{\mathbb C}\), one has \(I(I(z))=z\).
proof:
  Apply the involutivity of Riemann-sphere inversion.
-/
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

/--
%%handwave
name:
  Underlying map of the inversion homeomorphism
statement:
  The self-homeomorphism of \(\widehat{\mathbb C}\) defined by inversion sends
  each \(z\) to \(I(z)\).
proof:
  This is the defining forward map of the homeomorphism.
-/
@[simp]
theorem riemannSphereInvHomeomorph_apply (z : RiemannSphere) :
    riemannSphereInvHomeomorph z = riemannSphereInv z :=
  rfl

/-- The affine coordinate on the finite part of the Riemann sphere. -/
def riemannSphereFiniteChart : OpenPartialHomeomorph RiemannSphere ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph
    ((↑) : ℂ → RiemannSphere)).symm

/--
%%handwave
name:
  Domain of the finite Riemann-sphere chart
statement:
  The source of the affine chart on \(\widehat{\mathbb C}\) is
  \(\widehat{\mathbb C}\setminus\{\infty\}\).
proof:
  The affine chart is the inverse of the open embedding of \(\mathbb C\) into its one-point compactification, whose image is precisely the complement of infinity.
-/
@[simp]
theorem riemannSphereFiniteChart_source :
    riemannSphereFiniteChart.source = ({OnePoint.infty} : Set RiemannSphere)ᶜ := by
  simp [riemannSphereFiniteChart, OnePoint.compl_infty]

/--
%%handwave
name:
  Range of the finite Riemann-sphere chart
statement:
  The affine chart on \(\widehat{\mathbb C}\) has target all of \(\mathbb C\).
proof:
  It is the inverse chart of the finite-part embedding \(\mathbb C\hookrightarrow\widehat{\mathbb C}\).
-/
@[simp]
theorem riemannSphereFiniteChart_target :
    riemannSphereFiniteChart.target = Set.univ := by
  simp [riemannSphereFiniteChart]

/--
%%handwave
name:
  Finite chart coordinate
statement:
  For every \(z\in\mathbb C\), the affine Riemann-sphere chart sends the finite
  point represented by \(z\) to \(z\).
proof:
  This is the left-inverse identity for the finite-part open embedding.
-/
@[simp]
theorem riemannSphereFiniteChart_coe (z : ℂ) :
    riemannSphereFiniteChart (z : RiemannSphere) = z := by
  simpa [riemannSphereFiniteChart] using
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      ((↑) : ℂ → RiemannSphere) OnePoint.isOpenEmbedding_coe (x := z))

/--
%%handwave
name:
  Inverse finite chart coordinate
statement:
  For every \(z\in\mathbb C\), the inverse affine chart sends \(z\) to the
  corresponding finite point of \(\widehat{\mathbb C}\).
proof:
  This is the defining inverse map of the affine chart.
-/
@[simp]
theorem riemannSphereFiniteChart_symm_apply (z : ℂ) :
    riemannSphereFiniteChart.symm z = (z : RiemannSphere) :=
  rfl

/-- The reciprocal coordinate near infinity. -/
def riemannSphereInfinityChart : OpenPartialHomeomorph RiemannSphere ℂ :=
  riemannSphereInvHomeomorph.toOpenPartialHomeomorph.trans riemannSphereFiniteChart

/--
%%handwave
name:
  Domain of the chart at infinity
statement:
  The reciprocal chart at infinity has source
  \(\widehat{\mathbb C}\setminus\{0\}\).
proof:
  A point lies in this source exactly when its image under inversion is finite. Splitting into infinity and finite points reduces the claim to the formulas for reciprocal inversion.
-/
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

/--
%%handwave
name:
  Range of the chart at infinity
statement:
  The reciprocal chart at infinity has target all of \(\mathbb C\).
proof:
  Inversion is a self-homeomorphism, and the finite chart following it has target \(\mathbb C\).
-/
@[simp]
theorem riemannSphereInfinityChart_target :
    riemannSphereInfinityChart.target = Set.univ := by
  simp [riemannSphereInfinityChart]

/--
%%handwave
name:
  Inverse coordinate in the chart at infinity
statement:
  For every \(z\in\mathbb C\), the inverse chart at infinity represents the
  Riemann-sphere point \(I(z)\).
proof:
  The chart at infinity is inversion followed by the affine chart, and inversion is its own inverse.
-/
@[simp]
theorem riemannSphereInfinityChart_symm_apply (z : ℂ) :
    riemannSphereInfinityChart.symm z = riemannSphereInv (z : RiemannSphere) :=
  rfl

/--
%%handwave
name:
  Coordinate of infinity
statement:
  The reciprocal chart at infinity sends \(\infty\) to \(0\).
proof:
  Inversion sends infinity to zero, and the affine chart fixes finite coordinates.
-/
@[simp]
theorem riemannSphereInfinityChart_infty :
    riemannSphereInfinityChart OnePoint.infty = 0 := by
  simp [riemannSphereInfinityChart]

/--
%%handwave
name:
  Reciprocal coordinate of a finite point
statement:
  If \(z\in\mathbb C\) is nonzero, then the chart at infinity sends the finite
  point \(z\) to \(z^{-1}\).
proof:
  Apply the nonzero formula for inversion and then the affine-coordinate identity.
-/
@[simp]
theorem riemannSphereInfinityChart_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    riemannSphereInfinityChart (z : RiemannSphere) = z⁻¹ := by
  simp [riemannSphereInfinityChart, riemannSphereInv_coe_of_ne_zero hz]

/--
%%handwave
name:
  Infinity chart cancels inversion
statement:
  For every \(z\in\mathbb C\), the chart at infinity sends \(I(z)\) to \(z\).
proof:
  If \(z=0\), inversion gives infinity, whose reciprocal coordinate is zero. Otherwise the claim is the identity \((z^{-1})^{-1}=z\).
-/
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

/--
%%handwave
name:
  Uniformization of simply connected Riemann surfaces
statement:
  Every simply connected Riemann surface \(X\) is biholomorphic to one of the
  standard simply connected surfaces \(\widehat{\mathbb C}\), \(\mathbb C\),
  or the unit disk \(\mathbb D\).
proof:
  Integrate closed real one-forms from a base point. A finite-grid homotopy argument makes the integral path-independent, so first real de Rham cohomology vanishes. Compactness then gives the sphere; in the noncompact case, open-surface uniformization gives the plane or disk.
tags:
  shadow
-/
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
