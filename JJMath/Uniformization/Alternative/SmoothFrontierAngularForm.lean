import JJMath.Uniformization.SmoothFrontierLocalCollar
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# An alternative angular-form construction on a smooth frontier collar

This file isolates the intrinsic obstruction behind the horizontal form on a
frontier collar.  A real function on a compact frontier component has a
critical point.  Consequently, a covector which is everywhere positive in
the oriented frontier direction cannot be the differential of a globally
defined real function.
-/

open Set Filter
open JJMath.Manifold
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/--
%%handwave
name: Rotate the differential of the global signed boundary coordinate by a quarter turn in the complex tangent line
statement:
  Rotate the differential of the global signed boundary coordinate by a
  quarter turn in the complex tangent line.  Along the frontier this is the
  intrinsic horizontal covector complementary to the normal differential.
-/
noncomputable def smoothBoundaryAngularCovector
    (D : SmoothBoundaryDomain X) (x : X) : ℂ →L[ℝ] ℝ :=
  surfaceQuarterTurnCovector
    (mfderiv SurfaceRealModel (modelWithCornersSelf ℝ ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x)

end

end JJMath.Uniformization
