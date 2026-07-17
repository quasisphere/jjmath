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

/-- The class obtained by restricting a closed form on a punctured surface to
the punctured part of a coordinate disk. -/
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

/-- A circle primitive of one global puncture class transfers to every closed
one-form with the same class on a punctured coordinate disk. -/
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
/-- Reversing the orientation of the known puncture phase is harmless: local
classes that agree up to sign still transfer a circle primitive. -/
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
/-- A single normalized period on the punctured coordinate annulus suffices
to transfer a global circle primitive to the angular form. -/
noncomputable def puncturedAngularCirclePrimitive_of_local_period_eq_or_neg
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (p : X) (D : ClosedCoordinateDisk X)
    (hp : p ∈ D.expandedOpenDisk D.closedRadius)
    (eta tau : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1)
    (phi : (puncturedSurfaceOpen p ⊓
        ⟨D.expandedOpenDisk D.closedRadius,
          D.expandedOpenDisk_isOpen D.closedRadius⟩ :
          TopologicalSpace.Opens X) ≃ₘ⟮SurfaceRealModel,
            AnnularCylinderModel⟯ Circle × ℝ)
    (v : Circle)
    (c : SingularChain (I := SurfaceRealModel)
      (M := (puncturedSurfaceOpen p ⊓
        ⟨D.expandedOpenDisk D.closedRadius,
          D.expandedOpenDisk_isOpen D.closedRadius⟩ :
            TopologicalSpace.Opens X)) 1 ∞)
    (hcycle : boundary (I := SurfaceRealModel) c = 0)
    (hperiod :
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1 c =
          integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c ∨
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1 c =
          -integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c)
    (htauPeriod :
      integrateSmoothChain (I := SurfaceRealModel)
        (deRhamClosedFormsRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c ≠ 0)
    (Ptau : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • tau.1)) :
    SmoothCirclePrimitive SurfaceRealModel ((2 * Real.pi) • eta.1) := by
  let W : TopologicalSpace.Opens X := puncturedSurfaceOpen p ⊓
    ⟨D.expandedOpenDisk D.closedRadius,
      D.expandedOpenDisk_isOpen D.closedRadius⟩
  let etaW : DeRhamClosedForms (I := SurfaceRealModel)
      (M := W) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE
      (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta
  let tauW : DeRhamClosedForms (I := SurfaceRealModel)
      (M := W) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE
      (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau
  have hclassW := deRhamH1_class_eq_or_neg_of_annular_period_eq_or_neg
    SurfaceRealModel phi v etaW tauW c hcycle hperiod htauPeriod
  have hlocal :
      puncturedCoordinateDiskDeRhamH1Class p D eta =
          puncturedCoordinateDiskDeRhamH1Class p D tau ∨
        puncturedCoordinateDiskDeRhamH1Class p D eta =
          -puncturedCoordinateDiskDeRhamH1Class p D tau := by
    simpa [puncturedCoordinateDiskDeRhamH1Class, W, etaW, tauW,
      deRhamCohomologyRestrictionOfLE, Submodule.mapQ_apply] using hclassW
  exact puncturedAngularCirclePrimitive_of_local_class_eq_or_neg
    p D hp eta tau hlocal Ptau

/-- The coordinate-disk angular construction supplies a normalized smooth
cycle in the punctured surface.  If that cycle generates all smooth
one-cycles modulo smooth boundaries, the angular form has a circle-valued
primitive. -/
theorem ClosedCoordinateDisk.exists_closed_puncturedAngularForm_circlePrimitive_of_cycleGenerator
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ D.openDisk.chart.source)
    (hcenter : D.openDisk.chart p = D.openDisk.center)
    (hdouble : 2 * D.closedRadius ≤ D.openDisk.radius)
    (v : Circle) (x₀ : puncturedSurfaceOpen p) :
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      ∃ gamma : SingularChain (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) 1 ∞,
        boundary (I := SurfaceRealModel) gamma = 0 ∧
          integrateSmoothChain (I := SurfaceRealModel)
              ((2 * Real.pi) • eta.1) gamma = 2 * Real.pi ∧
            ((∀ c : SingularChain (I := SurfaceRealModel)
                  (M := puncturedSurfaceOpen p) 1 ∞,
                boundary (I := SurfaceRealModel) c = 0 →
                  ∃ (k : ℤ) (b : SingularChain (I := SurfaceRealModel)
                      (M := puncturedSurfaceOpen p) 2 ∞),
                    c = k • gamma + boundary (I := SurfaceRealModel) b) →
              Nonempty (SmoothCirclePrimitive SurfaceRealModel
                ((2 * Real.pi) • eta.1))) := by
  let D₀ : SmoothBoundaryDomain X := D.toSmoothBoundaryDomain
  let W := D.puncturedExpandedOpenDisk p (2 * D.closedRadius)
  let Q : TopologicalSpace.Opens X :=
    W ⊓ ⟨D₀.carrier, D₀.isOpen⟩
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  have hQU : Q ≤ U := inf_le_left.trans inf_le_left
  rcases D.exists_closed_puncturedAngularForm_normalized
      E p hp_source hcenter hdouble v with ⟨eta, c, hcycle, hperiod⟩
  let cU : SingularChain (I := SurfaceRealModel) (M := U) 1 ∞ :=
    SingularChain.nestedOpenInclusion (I := SurfaceRealModel) hQU c
  let gamma : SingularChain (I := SurfaceRealModel) (M := U) 1 ∞ := -cU
  have hcUcycle : boundary (I := SurfaceRealModel) cU = 0 := by
    rw [← SingularChain.nestedOpenInclusion_boundary, hcycle]
    simp
  have hgammaCycle : boundary (I := SurfaceRealModel) gamma = 0 := by
    change boundary (I := SurfaceRealModel) (-cU) = 0
    rw [map_neg, hcUcycle, neg_zero]
  have hcUperiod :
      integrateSmoothChain (I := SurfaceRealModel) eta.1 cU = -1 := by
    calc
      integrateSmoothChain (I := SurfaceRealModel) eta.1 cU =
          integrateSmoothChain (I := SurfaceRealModel)
            (restrictSmoothFormsOfLE
              (I := SurfaceRealModel) (A := ℝ) hQU 1 eta.1) c :=
        integrateSmoothChain_nestedOpenInclusion
          (I := SurfaceRealModel) hQU eta.1 c
      _ = -1 := by
        simpa [D₀, W, Q, U, hQU] using hperiod
  have hgammaPeriod :
      integrateSmoothChain (I := SurfaceRealModel)
          ((2 * Real.pi) • eta.1) gamma = 2 * Real.pi := by
    change integrateSmoothChain (I := SurfaceRealModel)
        ((2 * Real.pi) • eta.1) (-cU) = 2 * Real.pi
    rw [integrateSmoothChain_neg_one, integrateSmoothChain_smul_form,
      hcUperiod]
    ring
  refine ⟨eta, gamma, hgammaCycle, hgammaPeriod, ?_⟩
  intro hgenerate
  let etaScaled : DeRhamClosedForms (I := SurfaceRealModel)
      (M := U) (A := ℝ) 1 := (2 * Real.pi) • eta
  let P : SmoothCirclePrimitive SurfaceRealModel etaScaled.1 :=
    smoothCirclePrimitiveOfNormalizedCycleGenerator
      etaScaled x₀ gamma (by simpa [etaScaled] using hgammaPeriod) hgenerate
  exact ⟨SmoothCirclePrimitive.congr SurfaceRealModel P rfl⟩

end

end JJMath.Uniformization
