import JJMath.Uniformization.GreenConjugateCirclePrimitive
import JJMath.Uniformization.PuncturedVortexAngularClass

/-!
# Direct vortex exponentiation of the Green conjugate

A transported unit vortex supplies the integral puncture class directly.  By
shrinking the Green pole coordinate into the stationary radial germ, the
Green angular representative and the vortex are compared in the same
annular coordinate.  This avoids any comparison with singular cohomology.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Direct vortex exponentiation of a Green function
statement:
  Let (X) be a connected noncompact Riemann surface with vanishing first
  real de Rham cohomology, equipped with a smooth relatively compact
  exhaustion.  Every positive Green function on (X) whose positive
  superlevel sets are compact determines a holomorphic plane map with
  logarithmic modulus equal to the negative Green function, one simple zero
  at the pole, and no other zeros.
proof:
  Transport a compact coordinate vortex from the pole to infinity to obtain
  a global circle phase.  Shrink the pole coordinate into its stationary
  radial germ.  There the normalized vortex class and the Green angular class
  agree up to orientation by the annular de Rham Mayer--Vietoris calculation.
  Injectivity of restriction from the punctured surface transfers the circle
  primitive to the Green conjugate differential.  Exponentiation gives the
  punctured holomorphic map, and the logarithmic pole gives its removable
  extension with one simple zero.
-/
theorem compactSuperlevelGreenFunction_planeMap_of_vortex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G) := by
  rcases compactSuperlevelGreenFunction_poleExponentialBranch X G with ⟨P⟩
  rcases compactSuperlevelGreenFunction_poleCoordinateLogData_nonempty
      X G P with ⟨D⟩
  rcases exists_puncturedAtlasVortexCirclePrimitiveData_from_chart
      E D.coordinate.chart D.coordinate.chart_mem_atlas p
        D.coordinate.base_mem_source with ⟨A, hAchart⟩
  rcases D.exists_shrink_closedDisk_openDisk_subset_open
      A.localRadialNeighborhood A.pole_mem_localRadialNeighborhood with
    ⟨D', hcoordinate, _hlogFactor, hstationary⟩
  rcases compactSuperlevelGreenFunction_puncturedConjugateDifferentialData_nonempty
      X G with ⟨C⟩
  let v : Circle := circleAntipode 1
  let K : ClosedCoordinateDisk X := D'.closedDisk
  let W : TopologicalSpace.Opens X := D'.puncturedPoleDisk
  let Q : TopologicalSpace.Opens X := W ⊓
    ⟨K.toSmoothBoundaryDomain.carrier,
      K.toSmoothBoundaryDomain.isOpen⟩
  let phi := D'.radialDiffeomorph
  have hchart : K.openDisk.chart = A.vortex.chart := by
    rw [show K.openDisk.chart = D'.coordinate.chart by
      exact D'.closedDisk_openDisk_chart]
    rw [hcoordinate, hAchart]
  have hcenter : K.openDisk.center = A.vortex.chart p := by
    rw [show K.openDisk.center = D'.coordinate.chart p by
      exact D'.closedDisk_openDisk_center]
    rw [hcoordinate, hAchart]
  have hdouble : 2 * K.closedRadius ≤ K.openDisk.radius := by
    exact D'.closedDisk_double_closedRadius.le
  have hside : ∀ y : W,
      ((y : X) ∈ K.toSmoothBoundaryDomain.carrier ↔
        (phi y).2 < 0) := by
    intro y
    exact (K.radialPuncturedCollarDiffeomorph_second_lt_zero_iff p
      D'.pole_mem_closedDisk_chart_source
      D'.closedDisk_chart_p_eq_center hdouble y).symm
  let psi := sidePreservingAnnularCollarDomainRestriction
    K.toSmoothBoundaryDomain W phi hside
  rcases D'.exists_puncturedAngularForm_greenConjugate_class_with_local
      E C v with ⟨eta, hGreenClass, hetaLocal, _hcycle⟩
  let tau : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1 :=
    A.puncturedNormalizedClosedOneForm
  let etaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      (inf_le_left.trans D'.puncturedPoleDisk_le_puncturedSurfaceOpen)
      1 eta
  let tauQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      (inf_le_left.trans D'.puncturedPoleDisk_le_puncturedSurfaceOpen)
      1 tau
  let betaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
      AnnularCylinderModel psi 1
      (deRhamClosedFormsRestrictionToOpen
        (I := AnnularCylinderModel) (A := ℝ)
        negativeAnnularCylinderOpen 1 (annularAngularClosedForm v))
  have hetaQ : etaQ = betaQ := by
    apply Subtype.ext
    calc
      etaQ.1 = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ)
          (W := Q) (V := puncturedSurfaceOpen p)
          (inf_le_left.trans D'.puncturedPoleDisk_le_puncturedSurfaceOpen)
          1 eta.1 := rfl
      _ = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q) (V := W) inf_le_left 1
          (exteriorCutoffAngularCollarOneForm W phi v) := by
            simpa [K, W, Q, phi] using hetaLocal
      _ = betaQ.1 := by
        exact restrict_exteriorCutoffAngularCollarOneForm_domain_eq_pullback_negative
          K.toSmoothBoundaryDomain W phi hside v
  have htauQ :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ tauQ =
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1).mkQ betaQ ∨
        (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ tauQ =
          -(DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1).mkQ betaQ := by
    simpa [K, W, Q, phi, psi, hside, tau, tauQ, betaQ, v] using
      A.puncturedInnerDiskGlobalNormalizedClass_eq_or_neg_angular
        K hchart hcenter hdouble hstationary
  have hlocalQ :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ etaQ =
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1).mkQ tauQ ∨
        (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ etaQ =
          -(DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1).mkQ tauQ := by
    rcases htauQ with htauQ | htauQ
    · left
      rw [hetaQ]
      exact htauQ.symm
    · right
      rw [hetaQ, htauQ]
      simp
  have hQ : Q = puncturedSurfaceOpen p ⊓
      ⟨K.expandedOpenDisk K.closedRadius,
        K.expandedOpenDisk_isOpen K.closedRadius⟩ := by
    simpa [K, W, Q] using D'.puncturedPoleDisk_inf_innerDomain_eq
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  let Qsmall : TopologicalSpace.Opens X := puncturedSurfaceOpen p ⊓
    ⟨K.expandedOpenDisk K.closedRadius,
      K.expandedOpenDisk_isOpen K.closedRadius⟩
  have hQsmallQ : Qsmall ≤ Q := by
    exact hQ.ge
  have hQU : Q ≤ U := by
    exact inf_le_left.trans D'.puncturedPoleDisk_le_puncturedSurfaceOpen
  let restrictQsmall := deRhamCohomologyRestrictionOfLE
    (I := SurfaceRealModel) (A := ℝ)
    (W := Qsmall) (V := Q) hQsmallQ 1
  have hetaTrans :
      puncturedCoordinateDiskDeRhamH1Class p K eta =
        restrictQsmall
          ((DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1).mkQ etaQ) := by
    simpa [puncturedCoordinateDiskDeRhamH1Class, U, Qsmall,
      restrictQsmall, etaQ, deRhamCohomologyRestrictionOfLE,
      Submodule.mapQ_apply] using
        deRhamCohomologyRestrictionOfLE_trans
          Qsmall Q U hQsmallQ hQU 1
          ((DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := U) (A := ℝ) 1).mkQ eta)
  have htauTrans :
      puncturedCoordinateDiskDeRhamH1Class p K tau =
        restrictQsmall
          ((DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1).mkQ tauQ) := by
    simpa [puncturedCoordinateDiskDeRhamH1Class, U, Qsmall,
      restrictQsmall, tauQ, deRhamCohomologyRestrictionOfLE,
      Submodule.mapQ_apply] using
        deRhamCohomologyRestrictionOfLE_trans
          Qsmall Q U hQsmallQ hQU 1
          ((DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := U) (A := ℝ) 1).mkQ tau)
  have hlocal :
      puncturedCoordinateDiskDeRhamH1Class p K eta =
          puncturedCoordinateDiskDeRhamH1Class p K tau ∨
        puncturedCoordinateDiskDeRhamH1Class p K eta =
          -puncturedCoordinateDiskDeRhamH1Class p K tau := by
    rcases hlocalQ with hlocalQ | hlocalQ
    · left
      calc
        puncturedCoordinateDiskDeRhamH1Class p K eta =
            restrictQsmall
              ((DeRhamExactClosedForms (I := SurfaceRealModel)
                (M := Q) (A := ℝ) 1).mkQ etaQ) := hetaTrans
        _ = restrictQsmall
              ((DeRhamExactClosedForms (I := SurfaceRealModel)
                (M := Q) (A := ℝ) 1).mkQ tauQ) := congrArg _ hlocalQ
        _ = puncturedCoordinateDiskDeRhamH1Class p K tau := htauTrans.symm
    · right
      calc
        puncturedCoordinateDiskDeRhamH1Class p K eta =
            restrictQsmall
              ((DeRhamExactClosedForms (I := SurfaceRealModel)
                (M := Q) (A := ℝ) 1).mkQ etaQ) := hetaTrans
        _ = restrictQsmall
              (-((DeRhamExactClosedForms (I := SurfaceRealModel)
                (M := Q) (A := ℝ) 1).mkQ tauQ)) := congrArg _ hlocalQ
        _ = -restrictQsmall
              ((DeRhamExactClosedForms (I := SurfaceRealModel)
                (M := Q) (A := ℝ) 1).mkQ tauQ) := by simp
        _ = -puncturedCoordinateDiskDeRhamH1Class p K tau :=
          congrArg Neg.neg htauTrans.symm
  have hexact :
      (C.toClosedForm - annularAngleTransitionCoefficient v • eta :
          DeRhamClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1) ∈
        DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) (A := ℝ) 1 := by
    have hclass' :
        (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ
            C.toClosedForm =
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ
            (annularAngleTransitionCoefficient v • eta) := by
      simpa using hGreenClass
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq] at hclass'
    exact hclass'
  change
    (C.conjugate.omega - annularAngleTransitionCoefficient v • eta.1) ∈
      DeRhamExactForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1 at hexact
  rw [DeRhamExactForms] at hexact
  rcases hexact with ⟨theta, htheta⟩
  have hdecomposition :
      C.conjugate.omega =
        annularAngleTransitionCoefficient v • eta.1 +
          deRhamDifferential (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta := by
    rw [htheta]
    module
  have hp : p ∈ K.expandedOpenDisk K.closedRadius := by
    refine ⟨D'.pole_mem_closedDisk_chart_source, ?_⟩
    change dist (K.openDisk.chart p) K.openDisk.center < K.closedRadius
    rw [hchart, hcenter]
    simpa using K.closedRadius_pos
  exact greenConjugate_planeMap_of_local_angular_circlePrimitive
    C P v K hp eta tau theta hdecomposition hlocal
      A.puncturedNormalizedCirclePrimitive

end

end JJMath.Uniformization
