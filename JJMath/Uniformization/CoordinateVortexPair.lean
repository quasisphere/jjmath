import JJMath.Uniformization.PlanarVortexPair
import JJMath.Uniformization.CompactSupportTransfer
import JJMath.Uniformization.SmoothUnitPhaseCirclePrimitive

/-!
# Compactly supported vortex pairs in a surface coordinate chart

The planar zero--pole phase is transported through a full-plane surface
chart.  Its nonconstant locus has compact closure in that chart, so extending
the phase by one gives a smooth unit phase on the ambient surface with only
the two marked points removed.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/--
%%handwave
name: The surface with two marked points removed
statement:
  The surface with two marked points removed.
-/
def coordinateVortexPairOpen (a b : X) : TopologicalSpace.Opens X :=
  ⟨{x : X | x ≠ a ∧ x ≠ b}, isOpen_ne.inter isOpen_ne⟩

/--
%%handwave
name: The part of a twice-punctured surface lying in a chosen coordinate chart
statement:
  The part of a twice-punctured surface lying in a chosen coordinate
  chart.
-/
def coordinateVortexChartPatch
    (U : TopologicalSpace.Opens X) (a b : U) :
    TopologicalSpace.Opens (coordinateVortexPairOpen (a : X) (b : X)) :=
  ⟨{x | (x : X) ∈ U}, U.isOpen.preimage
    (continuous_subtype_val : Continuous
      (fun x : coordinateVortexPairOpen (a : X) (b : X) ↦ (x : X)))⟩

/--
%%handwave
name: A chart-patch point, regarded as a point of the original chart
statement:
  A chart-patch point, regarded as a point of the original chart.
-/
def coordinateVortexChartPatchToChart
    (U : TopologicalSpace.Opens X) (a b : U)
    (x : coordinateVortexChartPatch U a b) : U :=
  ⟨((x : coordinateVortexPairOpen (a : X) (b : X)) : X), x.2⟩

end

end JJMath.Uniformization
