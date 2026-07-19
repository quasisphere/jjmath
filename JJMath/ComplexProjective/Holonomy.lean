import JJMath.ComplexProjective.Structure
import JJMath.Hyperbolic.Cover
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Holonomy representations

The holonomy of a complex projective structure is represented as a group
homomorphism from the fundamental group of the surface to `PGL(2, ℂ)`.

This file packages holonomy together with the developing-map/equivariance data
from which it is read.  Analytic continuation remains a theorem input elsewhere,
but the construction data is no longer an unrelated monoid homomorphism.
-/

namespace JJMath

open scoped MatrixGroups

noncomputable section

/-- A holonomy representation for a based topological space. -/
structure HolonomyRepresentation (X : Type*) [TopologicalSpace X] (x₀ : X) where
  /-- The monodromy action of loops based at `x₀` on projective coordinates. -/
  toMonoidHom : FundamentalGroup X x₀ →* MobiusGroup

namespace HolonomyRepresentation

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

noncomputable instance : CoeFun (HolonomyRepresentation X x₀)
    (fun _ ↦ FundamentalGroup X x₀ → MobiusGroup) where
  coe ρ := ρ.toMonoidHom

/--
%%handwave
name:
  Holonomy preserves the identity loop
statement:
  For every holonomy representation \(\rho:\pi_1(X,x_0)\to
  \operatorname{PGL}_2(\mathbb C)\), one has \(\rho(1)=1\).
proof:
  This is the identity-preservation law for the homomorphism underlying \(\rho\).
-/
@[simp]
theorem map_one (ρ : HolonomyRepresentation X x₀) :
    ρ (1 : FundamentalGroup X x₀) = 1 :=
  ρ.toMonoidHom.map_one

/--
%%handwave
name:
  Holonomy preserves loop multiplication
statement:
  For every holonomy representation \(\rho\) and loops
  \(\gamma,\delta\in\pi_1(X,x_0)\), one has
  \(\rho(\gamma\delta)=\rho(\gamma)\rho(\delta)\).
proof:
  This is the multiplication-preservation law for the homomorphism underlying \(\rho\).
-/
@[simp]
theorem map_mul (ρ : HolonomyRepresentation X x₀) (γ δ : FundamentalGroup X x₀) :
    ρ (γ * δ) = ρ γ * ρ δ :=
  ρ.toMonoidHom.map_mul γ δ

end HolonomyRepresentation

/--
Developing-map data certifying that a holonomy representation is the monodromy
seen by a projective developing map on a simply connected cover.
-/
structure ProjectiveHolonomyDevelopingData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (basepoint : X) (ρ : HolonomyRepresentation X basepoint) where
  /-- The simply connected cover on which the developing map is single-valued. -/
  cover : SimplyConnectedCover X basepoint
  /-- The projective developing map on the cover. -/
  developingMap : cover.total → RiemannSphere
  /--
  Equivariance with explicit Mobius representatives of the stored holonomy.
  This is the certificate tying `ρ` to the developing map.
  -/
  equivariant_representatives :
    ∀ γ, ∃ A : MobiusRepresentative,
      Matrix.ProjGenLinGroup.mk A = ρ γ ∧
        ∀ y, developingMap (cover.deckAction γ y) = A • developingMap y

/--
Local chart/developing-map agreement on the actual sheet of the developing
cover.

For a point `y` in the cover, the local section is required to pass through
`y` itself.  The projective chart may differ from the developing map along
that section by one fixed Mobius normalization; this is the natural ambiguity
when the atlas chart was selected using a different local cover sheet.
-/
structure ProjectiveHolonomyLocalChartAgreementData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {basepoint : X} {ρ : HolonomyRepresentation X basepoint}
    (P : ComplexProjectiveStructure X)
    (developingData : ProjectiveHolonomyDevelopingData X basepoint ρ)
    (y : developingData.cover.total) where
  /-- A projective chart from the structure near the projected point. -/
  chart : ProjectiveChart X
  /-- The chart belongs to the projective atlas whose holonomy is being certified. -/
  chart_mem : chart ∈ P.atlasSet
  /-- The projected cover point lies in the chart source. -/
  projected_mem : developingData.cover.projection y ∈ chart.source
  /-- A local section of the covering projection over the chart source. -/
  lift : chart.source → developingData.cover.total
  /-- The local section projects back to the base point. -/
  lift_projects :
    ∀ x : chart.source, developingData.cover.projection (lift x) = (x : X)
  /-- The local section is the actual sheet through `y`. -/
  lift_through_y :
    lift ⟨developingData.cover.projection y, projected_mem⟩ = y
  /-- The local section is continuous on the chart source. -/
  lift_continuous : Continuous lift
  /-- The single Mobius post-normalization relating the chart to the developing map. -/
  normalization : MobiusRepresentative
  /-- Along this actual local section, the developing map is the normalized chart. -/
  developing_eq_normalized_chart :
    ∀ x : chart.source, developingData.developingMap (lift x) = normalization • chart (x : X)

/--
Concrete chart/developing data certifying that a based projective surface is
equipped with the projective atlas and developing-map monodromy from which
holonomy is to be read.

This is a checkable atlas/developing certificate, not a free representation:
the basepoint lies in a named projective chart, all stored projective-chart
transitions are Mobius transformations, and the representation is tied to a
projective developing map on a simply connected cover by local agreement with
the actual projective atlas.
-/
structure ProjectiveHolonomyConstructionData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (basepoint : X) (P : ComplexProjectiveStructure X)
    (ρ : HolonomyRepresentation X basepoint) where
  /-- Developing-map/equivariance data producing the stored holonomy representation. -/
  developingData : ProjectiveHolonomyDevelopingData X basepoint ρ
  /-- A projective chart based at the chosen basepoint. -/
  baseChart : ProjectiveChart X
  /-- The base chart belongs to the projective structure. -/
  baseChart_mem : baseChart ∈ P.atlasSet
  /-- The basepoint lies in the source of the base chart. -/
  basepoint_mem_baseChart : basepoint ∈ baseChart.source
  /--
  Around every point of the developing cover there is a projective chart of
  `P` obtained from the stored developing map by a local lift through that
  actual cover point, up to one Mobius normalization.
  -/
  developingMap_locally_agrees_with_projective_charts :
    ∀ y : developingData.cover.total,
      Nonempty (ProjectiveHolonomyLocalChartAgreementData X P developingData y)
  /-- All coordinate changes in the projective atlas are locally Mobius transformations. -/
  transition_mobius :
    ∀ e ∈ P.atlasSet, ∀ e' ∈ P.atlasSet, HasLocalMobiusTransition e e'

/--
A based Riemann surface equipped with a complex projective structure
and its holonomy representation.
-/
structure BasedProjectiveSurface (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] where
  /-- The basepoint used to identify the fundamental group. -/
  basepoint : X
  /-- The projective structure. -/
  projectiveStructure : ComplexProjectiveStructure X
  /-- The associated holonomy representation. -/
  holonomy : HolonomyRepresentation X basepoint
  /-- Concrete atlas data supporting the holonomy construction. -/
  holonomy_constructed_from_projective_charts :
    ProjectiveHolonomyConstructionData X basepoint projectiveStructure holonomy

end

end JJMath
