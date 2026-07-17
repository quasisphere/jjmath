import JJMath.Manifold.DeRham

/-!
# Linearity of the de Rham Mayer--Vietoris connecting map

The connecting map chosen from partition-of-unity lifts is additive and
commutes with real scalar multiplication.  These properties follow directly by
adding or scaling the lift-and-glue data used in its defining formula.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The partition-of-unity Mayer--Vietoris connecting map is additive. -/
theorem deRhamMayerVietorisConnectingOfPartitionOfUnity_add
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (alpha beta :
      DeRhamCohomology (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := ℝ) n) :
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ) I U V hcover n
        (alpha + beta) =
      deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ) I U V hcover n alpha +
        deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ) I U V hcover n beta := by
  induction alpha using Submodule.Quotient.induction_on with
  | _ omega =>
      induction beta using Submodule.Quotient.induction_on with
      | _ eta =>
          let omegaData :
              DeRhamMayerVietorisConnectingData
                (I := I) (A := ℝ) U V hcover n omega :=
            Classical.choice
              (deRham_mayerVietoris_connectingData_nonempty_of_partitionOfUnity
                (A := ℝ) I U V hcover n omega)
          let etaData :
              DeRhamMayerVietorisConnectingData
                (I := I) (A := ℝ) U V hcover n eta :=
            Classical.choice
              (deRham_mayerVietoris_connectingData_nonempty_of_partitionOfUnity
                (A := ℝ) I U V hcover n eta)
          let sumData :
              DeRhamMayerVietorisConnectingData
                (I := I) (A := ℝ) U V hcover n (omega + eta) :=
            { lift :=
                (omegaData.lift.1 + etaData.lift.1,
                  omegaData.lift.2 + etaData.lift.2)
              lift_difference := by
                change
                  deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ) U V n
                      (omegaData.lift.1 + etaData.lift.1,
                        omegaData.lift.2 + etaData.lift.2) =
                    (omega + eta).1
                have homega := omegaData.lift_difference
                have heta := etaData.lift_difference
                change
                  restrictSmoothFormsOfLE (I := I) (A := ℝ)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                      inf_le_left n omegaData.lift.1 -
                    restrictSmoothFormsOfLE (I := I) (A := ℝ)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                      inf_le_right n omegaData.lift.2 = omega.1 at homega
                change
                  restrictSmoothFormsOfLE (I := I) (A := ℝ)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                      inf_le_left n etaData.lift.1 -
                    restrictSmoothFormsOfLE (I := I) (A := ℝ)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                      inf_le_right n etaData.lift.2 = eta.1 at heta
                simp only [deRhamMayerVietorisSmoothDifference]
                rw [map_add, map_add]
                calc
                  _ =
                      (restrictSmoothFormsOfLE (I := I) (A := ℝ)
                          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                          inf_le_left n omegaData.lift.1 -
                        restrictSmoothFormsOfLE (I := I) (A := ℝ)
                          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                          inf_le_right n omegaData.lift.2) +
                      (restrictSmoothFormsOfLE (I := I) (A := ℝ)
                          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                          inf_le_left n etaData.lift.1 -
                        restrictSmoothFormsOfLE (I := I) (A := ℝ)
                          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                          inf_le_right n etaData.lift.2) := by abel
                  _ = omega.1 + eta.1 := by rw [homega, heta]
                  _ = (omega + eta).1 := rfl
              glued := omegaData.glued + etaData.glued
              glued_restriction := by
                change
                  deRhamMayerVietorisSmoothRestriction (I := I) (A := ℝ) U V (n + 1)
                      (omegaData.glued + etaData.glued).1 =
                    (deRhamDifferential (I := I) (M := U) (A := ℝ) n
                        (omegaData.lift.1 + etaData.lift.1),
                      deRhamDifferential (I := I) (M := V) (A := ℝ) n
                        (omegaData.lift.2 + etaData.lift.2))
                have homega := omegaData.glued_restriction
                have heta := etaData.glued_restriction
                apply Prod.ext
                · change
                    restrictSmoothFormsToOpen (I := I) (A := ℝ) U (n + 1)
                        (omegaData.glued.1 + etaData.glued.1) = _
                  rw [map_add, map_add]
                  rw [show
                    restrictSmoothFormsToOpen (I := I) (A := ℝ) U (n + 1)
                        omegaData.glued.1 =
                      deRhamDifferential (I := I) (M := U) (A := ℝ) n
                        omegaData.lift.1 by
                      simpa [deRhamMayerVietorisSmoothRestriction] using
                        congrArg Prod.fst homega]
                  rw [show
                    restrictSmoothFormsToOpen (I := I) (A := ℝ) U (n + 1)
                        etaData.glued.1 =
                      deRhamDifferential (I := I) (M := U) (A := ℝ) n
                        etaData.lift.1 by
                      simpa [deRhamMayerVietorisSmoothRestriction] using
                        congrArg Prod.fst heta]
                · change
                    restrictSmoothFormsToOpen (I := I) (A := ℝ) V (n + 1)
                        (omegaData.glued.1 + etaData.glued.1) = _
                  rw [map_add, map_add]
                  rw [show
                    restrictSmoothFormsToOpen (I := I) (A := ℝ) V (n + 1)
                        omegaData.glued.1 =
                      deRhamDifferential (I := I) (M := V) (A := ℝ) n
                        omegaData.lift.2 by
                      simpa [deRhamMayerVietorisSmoothRestriction] using
                        congrArg Prod.snd homega]
                  rw [show
                    restrictSmoothFormsToOpen (I := I) (A := ℝ) V (n + 1)
                        etaData.glued.1 =
                      deRhamDifferential (I := I) (M := V) (A := ℝ) n
                        etaData.lift.2 by
                      simpa [deRhamMayerVietorisSmoothRestriction] using
                        congrArg Prod.snd heta]
                  simp only [map_add] }
          change
            deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ) I U V hcover n
                ((DeRhamExactClosedForms (I := I)
                  (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := ℝ) n).mkQ omega +
                  (DeRhamExactClosedForms (I := I)
                    (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := ℝ) n).mkQ eta) = _
          rw [← map_add]
          rw [deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
            (A := ℝ) I U V hcover n (omega + eta) sumData]
          have homega :=
            deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
              (A := ℝ) I U V hcover n omega omegaData
          have heta :=
            deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
              (A := ℝ) I U V hcover n eta etaData
          calc
            (DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) (n + 1)).mkQ
                sumData.glued =
              (DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) (n + 1)).mkQ
                  omegaData.glued +
                (DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) (n + 1)).mkQ
                  etaData.glued := by
                    exact map_add _ _ _
            _ = _ := congrArg₂ (· + ·) homega.symm heta.symm

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The partition-of-unity Mayer--Vietoris connecting map commutes with real scalars. -/
theorem deRhamMayerVietorisConnectingOfPartitionOfUnity_smul
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (c : ℝ)
    (alpha :
      DeRhamCohomology (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := ℝ) n) :
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ) I U V hcover n
        (c • alpha) =
      c • deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ) I U V hcover n alpha := by
  induction alpha using Submodule.Quotient.induction_on with
  | _ omega =>
      let omegaData :
          DeRhamMayerVietorisConnectingData
            (I := I) (A := ℝ) U V hcover n omega :=
        Classical.choice
          (deRham_mayerVietoris_connectingData_nonempty_of_partitionOfUnity
            (A := ℝ) I U V hcover n omega)
      let smulData :
          DeRhamMayerVietorisConnectingData
            (I := I) (A := ℝ) U V hcover n (c • omega) :=
        { lift := (c • omegaData.lift.1, c • omegaData.lift.2)
          lift_difference := by
            change
              deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ) U V n
                  (c • omegaData.lift.1, c • omegaData.lift.2) =
                (c • omega).1
            have homega := omegaData.lift_difference
            change
              restrictSmoothFormsOfLE (I := I) (A := ℝ)
                    (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                    inf_le_left n omegaData.lift.1 -
                  restrictSmoothFormsOfLE (I := I) (A := ℝ)
                    (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                    inf_le_right n omegaData.lift.2 = omega.1 at homega
            simp only [deRhamMayerVietorisSmoothDifference]
            rw [map_smul, map_smul]
            calc
              c • restrictSmoothFormsOfLE (I := I) (A := ℝ)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                      inf_le_left n omegaData.lift.1 -
                    c • restrictSmoothFormsOfLE (I := I) (A := ℝ)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                      inf_le_right n omegaData.lift.2 =
                  c • (restrictSmoothFormsOfLE (I := I) (A := ℝ)
                        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                        inf_le_left n omegaData.lift.1 -
                      restrictSmoothFormsOfLE (I := I) (A := ℝ)
                        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                        inf_le_right n omegaData.lift.2) := by
                    rw [smul_sub]
              _ = c • omega.1 := by rw [homega]
              _ = (c • omega).1 := rfl
          glued := c • omegaData.glued
          glued_restriction := by
            have homega := omegaData.glued_restriction
            apply Prod.ext
            · change
                restrictSmoothFormsToOpen (I := I) (A := ℝ) U (n + 1)
                    (c • omegaData.glued.1) = _
              rw [map_smul, map_smul]
              rw [show
                restrictSmoothFormsToOpen (I := I) (A := ℝ) U (n + 1)
                    omegaData.glued.1 =
                  deRhamDifferential (I := I) (M := U) (A := ℝ) n
                    omegaData.lift.1 by
                  simpa [deRhamMayerVietorisSmoothRestriction] using
                    congrArg Prod.fst homega]
            · change
                restrictSmoothFormsToOpen (I := I) (A := ℝ) V (n + 1)
                    (c • omegaData.glued.1) = _
              rw [map_smul, map_smul]
              rw [show
                restrictSmoothFormsToOpen (I := I) (A := ℝ) V (n + 1)
                    omegaData.glued.1 =
                  deRhamDifferential (I := I) (M := V) (A := ℝ) n
                    omegaData.lift.2 by
                  simpa [deRhamMayerVietorisSmoothRestriction] using
                    congrArg Prod.snd homega]
              simp only [map_smul] }
      change
        deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ) I U V hcover n
            (c • (DeRhamExactClosedForms (I := I)
              (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := ℝ) n).mkQ omega) = _
      rw [← map_smul]
      rw [deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
        (A := ℝ) I U V hcover n (c • omega) smulData]
      have homega :=
        deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
          (A := ℝ) I U V hcover n omega omegaData
      calc
        (DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) (n + 1)).mkQ
            smulData.glued =
          c • (DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) (n + 1)).mkQ
            omegaData.glued := by
              exact map_smul _ _ _
        _ = _ := congrArg (c • ·) homega.symm

end

end JJMath.Manifold
