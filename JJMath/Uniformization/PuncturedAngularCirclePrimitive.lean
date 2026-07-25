import JJMath.Uniformization.CirclePrimitiveIntegralPeriods
import JJMath.Uniformization.PuncturedAngularForm

/-!
# Circle primitives from the local puncture class

On a surface with vanishing first de Rham cohomology, restriction from the
punctured surface to a punctured coordinate disk is injective.  Consequently,
a global angular form has a circle primitive as soon as its local class agrees
with the class of any global form whose circle primitive is already known.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

/--
%%handwave
name: The class obtained by restricting a closed form on a punctured surface to the punctured part of a coordinate disk
statement:
  The class obtained by restricting a closed form on a punctured surface to
  the punctured part of a coordinate disk.
-/
noncomputable def puncturedCoordinateDiskDeRhamH1Class
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (p : X) (D : ClosedCoordinateDisk X)
    (eta : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1) :
    DeRhamCohomology (I := SurfaceRealModel)
      (M := (puncturedSurfaceOpen p ⊓
        ⟨D.expandedOpenDisk D.closedRadius,
          D.expandedOpenDisk_isOpen D.closedRadius⟩ :
            TopologicalSpace.Opens X)) (A := ℝ) 1 :=
  deRhamCohomologyRestrictionOfLE
    (I := SurfaceRealModel) (A := ℝ)
    (W := (puncturedSurfaceOpen p ⊓
      ⟨D.expandedOpenDisk D.closedRadius,
        D.expandedOpenDisk_isOpen D.closedRadius⟩ :
          TopologicalSpace.Opens X))
    (V := puncturedSurfaceOpen p) inf_le_left 1
    ((DeRhamExactClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ eta)

/--
%%handwave
name: A circle primitive of one global puncture class transfers to every closed one-form with the same class on a punctured coordinate disk
statement:
  A circle primitive of one global puncture class transfers to every closed
  one-form with the same class on a punctured coordinate disk.
-/
noncomputable def puncturedAngularCirclePrimitive_of_local_class
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (p : X) (D : ClosedCoordinateDisk X)
    (hp : p ∈ D.expandedOpenDisk D.closedRadius)
    (eta tau : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1)
    (hlocal :
      puncturedCoordinateDiskDeRhamH1Class p D eta =
        puncturedCoordinateDiskDeRhamH1Class p D tau)
    (Ptau : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • tau.1)) :
    SmoothCirclePrimitive SurfaceRealModel ((2 * Real.pi) • eta.1) := by
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  let V : TopologicalSpace.Opens X :=
    ⟨D.expandedOpenDisk D.closedRadius,
      D.expandedOpenDisk_isOpen D.closedRadius⟩
  have hinj := puncturedSurfaceOpen_coordinateDisk_restriction_injective p D hp
  have hclass :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := U) (A := ℝ) 1).mkQ eta =
        (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := U) (A := ℝ) 1).mkQ tau := by
    apply hinj
    simpa [puncturedCoordinateDiskDeRhamH1Class, U, V] using hlocal
  let etaScaled : DeRhamClosedForms (I := SurfaceRealModel)
      (M := U) (A := ℝ) 1 := (2 * Real.pi) • eta
  let tauScaled : DeRhamClosedForms (I := SurfaceRealModel)
      (M := U) (A := ℝ) 1 := (2 * Real.pi) • tau
  have hscaled :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := U) (A := ℝ) 1).mkQ etaScaled =
        (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := U) (A := ℝ) 1).mkQ tauScaled := by
    simpa [etaScaled, tauScaled] using congrArg ((2 * Real.pi) • ·) hclass
  let PtauScaled : SmoothCirclePrimitive SurfaceRealModel tauScaled.1 :=
    SmoothCirclePrimitive.congr SurfaceRealModel Ptau rfl
  exact SmoothCirclePrimitive.of_cohomologous SurfaceRealModel
    PtauScaled hscaled

set_option synthInstance.maxHeartbeats 100000 in
/--
%%handwave
name: Reversing the orientation of the known puncture phase is harmless: local classes that agree up to sign still transfer a circle primitive
statement:
  Reversing the orientation of the known puncture phase is harmless: local
  classes that agree up to sign still transfer a circle primitive.
-/
noncomputable def puncturedAngularCirclePrimitive_of_local_class_eq_or_neg
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (p : X) (D : ClosedCoordinateDisk X)
    (hp : p ∈ D.expandedOpenDisk D.closedRadius)
    (eta tau : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1)
    (hlocal :
      puncturedCoordinateDiskDeRhamH1Class p D eta =
          puncturedCoordinateDiskDeRhamH1Class p D tau ∨
        puncturedCoordinateDiskDeRhamH1Class p D eta =
          -puncturedCoordinateDiskDeRhamH1Class p D tau)
    (Ptau : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • tau.1)) :
    SmoothCirclePrimitive SurfaceRealModel ((2 * Real.pi) • eta.1) := by
  classical
  by_cases hsame :
      puncturedCoordinateDiskDeRhamH1Class p D eta =
        puncturedCoordinateDiskDeRhamH1Class p D tau
  · exact puncturedAngularCirclePrimitive_of_local_class
      p D hp eta tau hsame Ptau
  · have hneg := hlocal.resolve_left hsame
    let tauNeg : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1 := -tau
    have hlocalNeg :
        puncturedCoordinateDiskDeRhamH1Class p D eta =
          puncturedCoordinateDiskDeRhamH1Class p D tauNeg := by
      simpa [tauNeg, puncturedCoordinateDiskDeRhamH1Class] using hneg
    let PtauNeg : SmoothCirclePrimitive SurfaceRealModel
        ((2 * Real.pi) • tauNeg.1) :=
      SmoothCirclePrimitive.congr SurfaceRealModel
        (SmoothCirclePrimitive.neg SurfaceRealModel Ptau) (by
          dsimp [tauNeg]
          module)
    exact puncturedAngularCirclePrimitive_of_local_class
      p D hp eta tauNeg hlocalNeg PtauNeg

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
end

end JJMath.Uniformization
