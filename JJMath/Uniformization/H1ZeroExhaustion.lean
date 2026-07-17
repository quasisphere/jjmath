import JJMath.Uniformization.ExteriorAngularExtension

/-!
# Exhaustions with vanishing first de Rham cohomology

The bounded filling of each pointed exhaustion member has no bounded
complementary component.  Removing its finitely many exterior complementary
components from the ambient surface, one at a time, gives annular
Mayer--Vietoris covers and preserves vanishing first cohomology.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold
open JJMath.Manifold.SmoothChainConnectivity

noncomputable section

/--
%%handwave
name:
  Vanishing first cohomology passes from a connected exhaustion to the surface
statement:
  If a Riemann surface has a pointed increasing smooth exhaustion
  by path-connected domains with vanishing first real de Rham cohomology, then
  the surface itself has vanishing first real de Rham cohomology.
proof:
  Restrict a closed one-form to each exhaustion domain and choose a primitive.
  Subtract its value at the common base point.  Two such normalized primitives
  agree on every nested overlap because their difference has zero differential
  on a connected domain.  The compatible primitives glue over the exhaustion,
  which covers the surface, and their differential is the original one-form.
-/
theorem PointedH1ZeroSmoothRelativelyCompactExhaustion.ambientDeRhamH1Zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X}
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p) :
    Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1) := by
  classical
  let U : ℕ → TopologicalSpace.Opens X :=
    fun n => ⟨(E.domain n).carrier, (E.domain n).isOpen⟩
  have hU_mono {m n : ℕ} (hmn : m ≤ n) : U m ≤ U n := by
    exact E.domain_carrier_mono hmn
  have hpU (n : ℕ) : p ∈ U n := E.domain_base_mem n
  have hU_iSup : iSup U = ⊤ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rcases E.domain_exhausts x with ⟨n, hxn⟩
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨n, hxn⟩
  have htop :
      Subsingleton
        (DeRhamCohomology
          (I := SurfaceRealModel)
          (M := (⊤ : TopologicalSpace.Opens X)) (A := ℝ) 1) := by
    apply
      deRhamCohomology_subsingleton_of_closedForms_succ_le_exactForms
        (I := SurfaceRealModel)
        (M := (⊤ : TopologicalSpace.Opens X)) (A := ℝ) (n := 0)
    intro omega
    let omegaU (n : ℕ) :
        DeRhamClosedForms
          (I := SurfaceRealModel) (M := U n) (A := ℝ) 1 :=
      deRhamClosedFormsRestrictionOfLE
        (I := SurfaceRealModel) (A := ℝ)
        (show U n ≤ (⊤ : TopologicalSpace.Opens X) from le_top) 1 omega
    have hprimitive (n : ℕ) :
        ∃ theta : SmoothForms
            (I := SurfaceRealModel) (M := U n) ℝ 0,
          deRhamDifferential
              (I := SurfaceRealModel) (M := U n) (A := ℝ) 0 theta =
            (omegaU n : SmoothForms
              (I := SurfaceRealModel) (M := U n) ℝ 1) := by
      letI : Subsingleton
          (DeRhamCohomology
            (I := SurfaceRealModel) (M := U n) (A := ℝ) 1) :=
        E.domain_deRhamH1Zero n
      exact
        deRhamClosedSuccForm_has_primitive_of_cohomology_subsingleton
          (I := SurfaceRealModel) (M := U n) (A := ℝ) (n := 0)
          (omegaU n)
    let thetaRaw (n : ℕ) :
        SmoothForms (I := SurfaceRealModel) (M := U n) ℝ 0 :=
      Classical.choose (hprimitive n)
    let pU (n : ℕ) : U n := ⟨p, hpU n⟩
    let c (n : ℕ) : ℝ :=
      (thetaRaw n).toFun (pU n) (fun i : Fin 0 => nomatch i)
    let theta (n : ℕ) :
        SmoothForms (I := SurfaceRealModel) (M := U n) ℝ 0 :=
      thetaRaw n -
        smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
          (smoothRealConstantFunction (I0 := SurfaceRealModel) (c n))
    have htheta_d (n : ℕ) :
        deRhamDifferential
            (I := SurfaceRealModel) (M := U n) (A := ℝ) 0 (theta n) =
          (omegaU n : SmoothForms
            (I := SurfaceRealModel) (M := U n) ℝ 1) := by
      change
        (deRhamDifferential
          (I := SurfaceRealModel) (M := U n) (A := ℝ) 0)
            (thetaRaw n -
              smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
                (smoothRealConstantFunction
                  (I0 := SurfaceRealModel) (c n))) = _
      rw [map_sub, Classical.choose_spec (hprimitive n),
        deRhamDifferential_smoothRealFunctionToZeroForm_const, sub_zero]
    have htheta_base (n : ℕ) :
        (theta n).toFun (pU n) (fun i : Fin 0 => nomatch i) = 0 := by
      change c n - c n = 0
      ring
    have htheta_restrict {m n : ℕ} (hmn : m ≤ n) :
        restrictSmoothFormsOfLE
            (I := SurfaceRealModel) (M := X) (A := ℝ)
            (hU_mono hmn) 0 (theta n) =
          theta m := by
      letI : PathConnectedSpace (U m) := E.domain_pathConnected m
      letI : ConnectedSpace (U m) := inferInstance
      apply smoothZeroForm_eq_of_differential_eq_of_eq_at
        (x₀ := pU m)
      · rw [deRhamDifferential_restrictSmoothFormsOfLE,
          htheta_d n, htheta_d m]
        simpa [omegaU] using
          restrictSmoothFormsOfLE_comp
            (I := SurfaceRealModel) (M := X) (A := ℝ)
            (show U n ≤ (⊤ : TopologicalSpace.Opens X) from le_top)
            (hU_mono hmn) 1 (omega : SmoothForms
              (I := SurfaceRealModel)
              (M := (⊤ : TopologicalSpace.Opens X)) ℝ 1)
      · have hzero := htheta_base n
        have hzero' := htheta_base m
        change
          (theta n).toFun (pU n)
              ((mfderiv SurfaceRealModel SurfaceRealModel
                  (TopologicalSpace.Opens.inclusion (hU_mono hmn)) (pU m)) ∘
                (fun i : Fin 0 => nomatch i)) =
            (theta m).toFun (pU m) (fun i : Fin 0 => nomatch i)
        rw [show
          (mfderiv SurfaceRealModel SurfaceRealModel
              (TopologicalSpace.Opens.inclusion (hU_mono hmn)) (pU m)) ∘
              (fun i : Fin 0 => nomatch i) =
            (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
        rw [hzero, hzero']
    have hcompat :
        ∀ i j : ℕ,
          restrictSmoothFormsOfLE
              (I := SurfaceRealModel) (M := X) (A := ℝ)
              (V := U i) (W := U i ⊓ U j) inf_le_left 0 (theta i) =
            restrictSmoothFormsOfLE
              (I := SurfaceRealModel) (M := X) (A := ℝ)
              (V := U j) (W := U i ⊓ U j) inf_le_right 0 (theta j) := by
      intro i j
      rcases le_total i j with hij | hji
      · rw [← htheta_restrict hij]
        simpa using
          restrictSmoothFormsOfLE_comp
            (I := SurfaceRealModel) (M := X) (A := ℝ)
            (hU_mono hij) inf_le_left 0 (theta j)
      · rw [← htheta_restrict hji]
        symm
        simpa using
          restrictSmoothFormsOfLE_comp
            (I := SurfaceRealModel) (M := X) (A := ℝ)
            (hU_mono hji) inf_le_right 0 (theta i)
    rcases exists_smoothForms_iSup_gluing
        (M := X) SurfaceRealModel 0 U theta hcompat with
      ⟨thetaSup, hthetaSup⟩
    let omegaSup : SmoothForms
        (I := SurfaceRealModel) (M := (iSup U : TopologicalSpace.Opens X))
        ℝ 1 :=
      restrictSmoothFormsOfLE
        (I := SurfaceRealModel) (M := X) (A := ℝ)
        (show iSup U ≤ (⊤ : TopologicalSpace.Opens X) from le_top) 1 omega
    have hthetaSup_d :
        deRhamDifferential
            (I := SurfaceRealModel)
            (M := (iSup U : TopologicalSpace.Opens X)) (A := ℝ) 0 thetaSup =
          omegaSup := by
      apply smoothForms_iSup_eq_of_forall_restrict_eq
        (M := X) SurfaceRealModel 1 U
      intro n
      rw [← deRhamDifferential_restrictSmoothFormsOfLE, hthetaSup n,
        htheta_d n]
      simpa [omegaSup, omegaU] using
        (restrictSmoothFormsOfLE_comp
          (I := SurfaceRealModel) (M := X) (A := ℝ)
          (show iSup U ≤ (⊤ : TopologicalSpace.Opens X) from le_top)
          (le_iSup U n) 1 (omega : SmoothForms
            (I := SurfaceRealModel)
            (M := (⊤ : TopologicalSpace.Opens X)) ℝ 1)).symm
    have hexact :
        ∃ thetaTop : SmoothForms
            (I := SurfaceRealModel)
            (M := (⊤ : TopologicalSpace.Opens X)) ℝ 0,
          deRhamDifferential
              (I := SurfaceRealModel)
              (M := (⊤ : TopologicalSpace.Opens X)) (A := ℝ) 0 thetaTop =
            (omega : SmoothForms
              (I := SurfaceRealModel)
              (M := (⊤ : TopologicalSpace.Opens X)) ℝ 1) := by
      have hTopSup :
          (⊤ : TopologicalSpace.Opens X) ≤ iSup U := by
        rw [hU_iSup]
      have hSupTop :
          iSup U ≤ (⊤ : TopologicalSpace.Opens X) := le_top
      let phi :
          (⊤ : TopologicalSpace.Opens X) ≃ₘ⟮SurfaceRealModel,
            SurfaceRealModel⟯ (iSup U : TopologicalSpace.Opens X) :=
        { toEquiv :=
            { toFun := TopologicalSpace.Opens.inclusion hTopSup
              invFun := TopologicalSpace.Opens.inclusion hSupTop
              left_inv := fun _ => Subtype.ext rfl
              right_inv := fun _ => Subtype.ext rfl }
          contMDiff_toFun := contMDiff_inclusion hTopSup
          contMDiff_invFun := contMDiff_inclusion hSupTop }
      have homegaSup :
          omegaSup =
            smoothFormsPullbackDiffeomorph
              SurfaceRealModel SurfaceRealModel phi.symm 1 omega := by
        apply DifferentialForm.ext
        intro x
        ext v
        rfl
      let thetaTop : SmoothForms
          (I := SurfaceRealModel)
          (M := (⊤ : TopologicalSpace.Opens X)) ℝ 0 :=
        smoothFormsPullbackDiffeomorph
          SurfaceRealModel SurfaceRealModel phi 0 thetaSup
      refine ⟨thetaTop, ?_⟩
      rw [show
        deRhamDifferential
            (I := SurfaceRealModel)
            (M := (⊤ : TopologicalSpace.Opens X)) (A := ℝ) 0 thetaTop =
          smoothFormsPullbackDiffeomorph
            SurfaceRealModel SurfaceRealModel phi 1
              (deRhamDifferential
                (I := SurfaceRealModel)
                (M := (iSup U : TopologicalSpace.Opens X))
                (A := ℝ) 0 thetaSup) by
          exact deRhamDifferential_smoothFormsPullbackDiffeomorph
            SurfaceRealModel SurfaceRealModel phi thetaSup]
      rw [hthetaSup_d, homegaSup]
      exact smoothFormsPullbackDiffeomorph_comp_symm
        SurfaceRealModel SurfaceRealModel phi
          (omega : SmoothForms
            (I := SurfaceRealModel)
            (M := (⊤ : TopologicalSpace.Opens X)) ℝ 1)
    rcases hexact with ⟨thetaTop, hthetaTop⟩
    simpa [DeRhamExactForms] using ⟨thetaTop, hthetaTop⟩
  rcases deRhamCohomology_addEquiv_topOpenDeRhamCohomology
      (M := X) SurfaceRealModel 1 with ⟨e⟩
  exact
    ⟨fun a b => e.injective (@Subsingleton.elim _ htop (e a) (e b))⟩

/--
%%handwave
name:
  Zero-cohomology bounded-filling exhaustion
statement:
  Let a connected noncompact Riemann surface have vanishing first real de
  Rham cohomology.  From every smooth relatively compact exhaustion and every
  base point one can construct a pointed smooth relatively compact exhaustion
  by path-connected domains whose first real de Rham cohomology vanishes.
proof:
  Take the component containing the base point and fill its relatively compact
  complementary components.  The remaining complementary components are
  exterior.  Delete them one at a time through annular Mayer--Vietoris covers;
  the nonzero angular period supplied from the exterior side makes exactness
  preserve vanishing first cohomology at every deletion.
-/
theorem
    smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_ambientDeRhamH1Zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X) (p : X) :
    Nonempty (PointedH1ZeroSmoothRelativelyCompactExhaustion X p) := by
  refine smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_domainwise
    (fun D q hq Dhat hDhat => ?_) E p
  letI : PathConnectedSpace Dhat.carrier := by
    rw [hDhat]
    exact smoothBoundaryDomain_boundedFilling_pathConnected D hq
  have hpre : IsPreconnected Dhat.carrier :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  apply Dhat.deRhamH1Zero_of_all_complementComponents_exterior
    hnoncompact E hpre
  intro V hV
  exact (hV.isExteriorComponent_iff_not_closure_compact
    Dhat.compact_closure).2
      (smoothBoundaryDomain_boundedFilling_complement_components_unbounded
        D hq Dhat hDhat V hV)

/--
%%handwave
name:
  Filling a smooth exhaustion gives vanishing first cohomology
statement:
  Every smooth relatively compact exhaustion of a noncompact simply connected
  Riemann surface can be replaced, after fixing a base point, by a pointed
  smooth relatively compact exhaustion whose members have vanishing first real
  de Rham cohomology.
proof:
  First integrate closed one-forms from a basepoint on the ambient simply
  connected surface; a finite-grid homotopy argument makes the integral
  path-independent and proves that every closed one-form is exact.  Fill the
  bounded holes of each pointed exhaustion member.  Every remaining
  complementary component is exterior, and deleting these finitely many
  components one at a time gives annular Mayer--Vietoris covers.  The angular
  period class on each collar makes the restriction from the exterior side
  nonzero, so exactness preserves vanishing first cohomology at every deletion.
-/
theorem smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X) (p : X) :
    Nonempty (PointedH1ZeroSmoothRelativelyCompactExhaustion X p) := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  letI : Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1) :=
    simplyConnected_surface_deRhamH1_zero (X := X)
  exact
    smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_ambientDeRhamH1Zero
      hnoncompact E p


end

end JJMath.Uniformization
