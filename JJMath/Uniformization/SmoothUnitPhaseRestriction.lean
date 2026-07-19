import JJMath.Manifold.CirclePrimitiveUniqueness
import JJMath.Manifold.DeRhamPoincare
import JJMath.Uniformization.SmoothUnitPhaseCirclePrimitive

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

/--
%%handwave
name:
  Smooth corestriction to an open submanifold
statement:
  Let \(f:M\to N\) be a smooth map whose image is contained in an open set
  \(U\subseteq N\).  Then the same map, regarded as a map \(M\to U\), is
  smooth.
proof:
  Near each image point, the local retraction from \(N\) to \(U\) is the
  identity.  Compose \(f\) with that local retraction and use local agreement
  with the corestricted map.
-/
private theorem contMDiffCodRestrictOpen
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G M N : Type*}
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F G}
    [ChartedSpace H M] [ChartedSpace G N]
    {n : WithTop ℕ∞} {f : M → N}
    (hf : ContMDiff I J n f) (U : TopologicalSpace.Opens N)
    (hmem : ∀ x, f x ∈ U) :
    ContMDiff I J n (fun x => (⟨f x, hmem x⟩ : U)) := by
  classical
  intro x
  let qU : U := ⟨f x, hmem x⟩
  let retract : N → U := fun y =>
    if hy : y ∈ U then ⟨y, hy⟩ else qU
  have hretract : ContMDiffAt J J n retract (f x) := by
    rw [← contMDiffAt_subtype_iff (U := U) (x := qU)]
    have heq : (fun y : U => retract y) = id := by
      funext y
      simp [retract]
    rw [heq]
    exact contMDiffAt_id
  have hcomp := hretract.comp x (hf x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [retract, hmem]

/-- The nested open subset `V` inside `U` is diffeomorphic to `U ∩ V`. -/
noncomputable def openInOpenDiffeomorph
    (U V : TopologicalSpace.Opens M) :
    openInOpen U V ≃ₘ⟮I, I⟯ (U ⊓ V : TopologicalSpace.Opens M) := by
  let toFun : openInOpen U V → (U ⊓ V : TopologicalSpace.Opens M) :=
    fun x => ⟨((x : U) : M), ⟨(x : U).2, x.2⟩⟩
  have hto : ContMDiff I I ∞ toFun := by
    exact contMDiffCodRestrictOpen
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).comp
        (contMDiff_subtype_val (I := I) (n := ∞) (U := openInOpen U V)))
      (U ⊓ V : TopologicalSpace.Opens M) (fun x => ⟨(x : U).2, x.2⟩)
  let invFun : (U ⊓ V : TopologicalSpace.Opens M) → openInOpen U V :=
    fun x => ⟨⟨(x : M), x.2.1⟩, x.2.2⟩
  have hinv : ContMDiff I I ∞ invFun := by
    have htoU : ContMDiff I I ∞
        (fun x : (U ⊓ V : TopologicalSpace.Opens M) =>
          (⟨(x : M), x.2.1⟩ : U)) :=
      contMDiffCodRestrictOpen
        (contMDiff_subtype_val (I := I) (n := ∞)
          (U := (U ⊓ V : TopologicalSpace.Opens M))) U (fun x => x.2.1)
    exact contMDiffCodRestrictOpen htoU (openInOpen U V) (fun x => x.2.2)
  exact
    { toEquiv := openInOpenEquivInf U V
      contMDiff_toFun := hto
      contMDiff_invFun := hinv }

/--
%%handwave
name:
  Nested restriction of a differential form
statement:
  For open sets \(U,V\subseteq M\) and a smooth \(n\)-form \(\omega\) on
  \(M\), restricting \(\omega\) first to \(U\) and then to the part of \(V\)
  inside \(U\) equals pulling back \(\omega|_{U\cap V}\) through the canonical
  diffeomorphism between these two presentations of \(U\cap V\).
proof:
  Evaluate both forms at a point and tangent vectors.  The underlying points
  coincide, and the chain rule identifies the two composites of tangent maps
  with the derivative of the same inclusion into \(M\).
-/
theorem nested_restriction_eq_pullback_intersection
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ n) :
    restrictSmoothFormsToOpen (I := I) (M := U) (A := ℝ)
        (openInOpen U V) n
        (restrictSmoothFormsToOpen (I := I) (M := M) (A := ℝ) U n omega) =
      smoothFormsPullbackDiffeomorph I I (openInOpenDiffeomorph I U V) n
        (restrictSmoothFormsToOpen (I := I) (M := M) (A := ℝ)
          (U ⊓ V : TopologicalSpace.Opens M) n omega) := by
  apply DifferentialForm.ext
  intro x
  let A : TopologicalSpace.Opens U := openInOpen U V
  let B : TopologicalSpace.Opens M := U ⊓ V
  let e : A ≃ₘ⟮I, I⟯ B := openInOpenDiffeomorph I U V
  let xU : U := (x : A)
  let xB : B := e x
  let LAU : TangentSpace I x →L[ℝ] TangentSpace I xU :=
    mfderiv I I (fun y : A => (y : U)) x
  let LUM : TangentSpace I xU →L[ℝ] TangentSpace I (xU : M) :=
    mfderiv I I (fun y : U => (y : M)) xU
  let LAB : TangentSpace I x →L[ℝ] TangentSpace I xB := mfderiv I I e x
  let LBM : TangentSpace I xB →L[ℝ] TangentSpace I (xB : M) :=
    mfderiv I I (fun y : B => (y : M)) xB
  have hpoint : (xB : M) = (xU : M) := rfl
  have hleft : LUM.comp LAU =
      mfderiv I I (fun y : A => ((y : U) : M)) x := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) (x := x)
      (g := fun y : U => (y : M)) (f := fun y : A => (y : U))
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).contMDiffAt.mdifferentiableAt
        (by simp))
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := A)).contMDiffAt.mdifferentiableAt
        (by simp))
    exact h.symm
  have hright : LBM.comp LAB =
      mfderiv I I (fun y : A => ((y : U) : M)) x := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) (x := x)
      (g := fun y : B => (y : M)) (f := e)
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := B)).contMDiffAt.mdifferentiableAt
        (by simp))
      (e.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv I I (fun y : A => ((y : U) : M)) x = LBM.comp LAB at h
    exact h.symm
  change
    ((omega.toFun (xU : M)).compContinuousLinearMap LUM).compContinuousLinearMap LAU =
      ((omega.toFun (xB : M)).compContinuousLinearMap LBM).compContinuousLinearMap LAB
  rw [hpoint]
  ext q
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (omega.toFun (xU : M))
  funext i
  exact congrArg (fun L => L (q i)) (hleft.trans hright.symm)

/-- Restrict a smooth circle primitive to an open submanifold. -/
noncomputable def SmoothCirclePrimitive.restrictToOpen
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega)
    (U : TopologicalSpace.Opens M) :
    SmoothCirclePrimitive I
      (restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1 omega) where
  phase :=
    { val := fun x => P.phase (x : M)
      property := P.phase.contMDiff.comp
        (contMDiff_subtype_val (I := I) (n := ∞) (U := U)) }
  locally_has_argument := by
    intro x
    rcases P.locally_has_argument (x : M) with
      ⟨V, hxV, theta, hphase, homega⟩
    let A : TopologicalSpace.Opens U := openInOpen U V
    let B : TopologicalSpace.Opens M := U ⊓ V
    let e : A ≃ₘ⟮I, I⟯ B := openInOpenDiffeomorph I U V
    let thetaB : SmoothForms (I := I) (M := B) ℝ 0 :=
      restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_right 0
        (smoothRealFunctionToZeroForm (I0 := I) theta)
    let thetaAZero : SmoothForms (I := I) (M := A) ℝ 0 :=
      smoothFormsPullbackDiffeomorph I I e 0 thetaB
    let thetaA : C^∞⟮I, A; ℝ⟯ := smoothRealFunctionOfZeroForm I thetaAZero
    refine ⟨A, hxV, thetaA, ?_, ?_⟩
    · intro y
      let yV : V := ⟨((y : A) : U), y.2⟩
      have hp := hphase yV
      change P.phase ((y : A) : M) =
        Complex.exp (((thetaA y : ℝ) : ℂ) * Complex.I)
      convert hp using 1
    · calc
        restrictSmoothFormsToOpen (I := I) (M := U) (A := ℝ) A 1
            (restrictSmoothFormsToOpen (I := I) (M := M) (A := ℝ) U 1 omega) =
          smoothFormsPullbackDiffeomorph I I e 1
            (restrictSmoothFormsToOpen (I := I) (M := M) (A := ℝ) B 1 omega) := by
              simpa [A, B, e] using
                nested_restriction_eq_pullback_intersection I U V omega
        _ = smoothFormsPullbackDiffeomorph I I e 1
            (restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_right 1
              (restrictSmoothFormsToOpen (I := I) (M := M) (A := ℝ) V 1 omega)) := by
              rw [restrictSmoothFormsOfLE_restrictSmoothFormsToOpen_eq]
        _ = smoothFormsPullbackDiffeomorph I I e 1
            (restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_right 1
              (deRhamDifferential (I := I) (M := V) (A := ℝ) 0
                (smoothRealFunctionToZeroForm (I0 := I) theta))) := by rw [homega]
        _ = smoothFormsPullbackDiffeomorph I I e 1
            (deRhamDifferential (I := I) (M := B) (A := ℝ) 0 thetaB) := by
              rw [deRhamDifferential_restrictSmoothFormsOfLE]
        _ = deRhamDifferential (I := I) (M := A) (A := ℝ) 0 thetaAZero := by
              exact (deRhamDifferential_smoothFormsPullbackDiffeomorph
                I I e thetaB).symm
        _ = deRhamDifferential (I := I) (M := A) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := I) thetaA) := by
              rw [smoothRealFunctionToZeroForm_smoothRealFunctionOfZeroForm]

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H']
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
variable (J : ModelWithCorners ℝ E' H') [IsManifold J ∞ N]

/-- The inverse image of an open set under a diffeomorphism. -/
def diffeomorphPreimageOpen
    (phi : N ≃ₘ⟮J, I⟯ M) (U : TopologicalSpace.Opens M) :
    TopologicalSpace.Opens N :=
  ⟨phi ⁻¹' U, U.isOpen.preimage phi.continuous⟩

/-- A diffeomorphism restricts to a diffeomorphism over an open set. -/
noncomputable def diffeomorphRestrictPreimageOpen
    (phi : N ≃ₘ⟮J, I⟯ M) (U : TopologicalSpace.Opens M) :
    diffeomorphPreimageOpen I J phi U ≃ₘ⟮J, I⟯ U := by
  let toFun : diffeomorphPreimageOpen I J phi U → U := fun x => ⟨phi x, x.2⟩
  have hto : ContMDiff J I ∞ toFun :=
    contMDiffCodRestrictOpen
      (phi.contMDiff.comp
        (contMDiff_subtype_val (I := J) (n := ∞)
          (U := diffeomorphPreimageOpen I J phi U)))
      U (fun x => x.2)
  let invFun : U → diffeomorphPreimageOpen I J phi U :=
    fun x => ⟨phi.symm x, by simp [diffeomorphPreimageOpen]⟩
  have hinv : ContMDiff I J ∞ invFun :=
    contMDiffCodRestrictOpen
      (phi.symm.contMDiff.comp
        (contMDiff_subtype_val (I := I) (n := ∞) (U := U)))
      (diffeomorphPreimageOpen I J phi U)
      (fun x => by simp [diffeomorphPreimageOpen])
  let e : diffeomorphPreimageOpen I J phi U ≃ U :=
    { toFun := toFun
      invFun := invFun
      left_inv := by intro x; apply Subtype.ext; simp [toFun, invFun]
      right_inv := by intro x; apply Subtype.ext; simp [toFun, invFun] }
  exact { toEquiv := e, contMDiff_toFun := hto, contMDiff_invFun := hinv }

/--
%%handwave
name:
  Restriction commutes with pullback by a diffeomorphism
statement:
  Let \(\phi:N\to M\) be a diffeomorphism, let \(U\subseteq M\) be open, and
  let \(\omega\) be a smooth \(n\)-form on \(M\).  Restricting
  \(\phi^*\omega\) to \(\phi^{-1}(U)\) equals pulling back \(\omega|_U\) by
  the restricted diffeomorphism \(\phi^{-1}(U)\to U\).
proof:
  Evaluate at a point of \(\phi^{-1}(U)\).  Both sides evaluate \(\omega\) at
  the same point, and the chain rule shows that their tangent maps are the
  derivative of the same composite into \(M\).
-/
theorem restrict_pullbackDiffeomorph_eq_pullback_restrict
    (phi : N ≃ₘ⟮J, I⟯ M) (U : TopologicalSpace.Opens M) {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ n) :
    restrictSmoothFormsToOpen (I := J) (M := N) (A := ℝ)
        (diffeomorphPreimageOpen I J phi U) n
        (smoothFormsPullbackDiffeomorph J I phi n omega) =
      smoothFormsPullbackDiffeomorph J I
        (diffeomorphRestrictPreimageOpen I J phi U) n
        (restrictSmoothFormsToOpen (I := I) (M := M) (A := ℝ) U n omega) := by
  apply DifferentialForm.ext
  intro x
  let A : TopologicalSpace.Opens N := diffeomorphPreimageOpen I J phi U
  let e : A ≃ₘ⟮J, I⟯ U := diffeomorphRestrictPreimageOpen I J phi U
  let xN : N := (x : A)
  let xM : M := phi xN
  let xU : U := e x
  let LAN : TangentSpace J x →L[ℝ] TangentSpace J xN :=
    mfderiv J J (fun y : A => (y : N)) x
  let LNM : TangentSpace J xN →L[ℝ] TangentSpace I xM := mfderiv J I phi xN
  let LAU : TangentSpace J x →L[ℝ] TangentSpace I xU := mfderiv J I e x
  let LUM : TangentSpace I xU →L[ℝ] TangentSpace I (xU : M) :=
    mfderiv I I (fun y : U => (y : M)) xU
  have hpoint : (xU : M) = xM := rfl
  have hleft : LNM.comp LAN = mfderiv J I (fun y : A => phi (y : N)) x := by
    have h := mfderiv_comp (I := J) (I' := J) (I'' := I) (x := x)
      (g := phi) (f := fun y : A => (y : N))
      (phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := J) (n := ∞) (U := A)).contMDiffAt.mdifferentiableAt
        (by simp))
    exact h.symm
  have hright : LUM.comp LAU = mfderiv J I (fun y : A => phi (y : N)) x := by
    have h := mfderiv_comp (I := J) (I' := I) (I'' := I) (x := x)
      (g := fun y : U => (y : M)) (f := e)
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).contMDiffAt.mdifferentiableAt
        (by simp))
      (e.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv J I (fun y : A => phi (y : N)) x = LUM.comp LAU at h
    exact h.symm
  change
    ((omega.toFun xM).compContinuousLinearMap LNM).compContinuousLinearMap LAN =
      ((omega.toFun (xU : M)).compContinuousLinearMap LUM).compContinuousLinearMap LAU
  rw [hpoint]
  ext q
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (omega.toFun xM)
  funext i
  exact congrArg (fun L => L (q i)) (hleft.trans hright.symm)

/-- Pull a smooth circle primitive back along a diffeomorphism. -/
noncomputable def SmoothCirclePrimitive.pullbackDiffeomorph
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega)
    (phi : N ≃ₘ⟮J, I⟯ M) :
    SmoothCirclePrimitive J (smoothFormsPullbackDiffeomorph J I phi 1 omega) where
  phase :=
    { val := fun x => P.phase (phi x)
      property := P.phase.contMDiff.comp phi.contMDiff }
  locally_has_argument := by
    intro x
    rcases P.locally_has_argument (phi x) with
      ⟨U, hxU, theta, hphase, homega⟩
    let A : TopologicalSpace.Opens N := diffeomorphPreimageOpen I J phi U
    let e : A ≃ₘ⟮J, I⟯ U := diffeomorphRestrictPreimageOpen I J phi U
    let thetaAZero : SmoothForms (I := J) (M := A) ℝ 0 :=
      smoothFormsPullbackDiffeomorph J I e 0
        (smoothRealFunctionToZeroForm (I0 := I) theta)
    let thetaA : C^∞⟮J, A; ℝ⟯ := smoothRealFunctionOfZeroForm J thetaAZero
    refine ⟨A, hxU, thetaA, ?_, ?_⟩
    · intro y
      have hp := hphase (e y)
      change P.phase (phi (y : N)) =
        Complex.exp (((thetaA y : ℝ) : ℂ) * Complex.I)
      convert hp using 1
    · calc
        restrictSmoothFormsToOpen (I := J) (M := N) (A := ℝ) A 1
            (smoothFormsPullbackDiffeomorph J I phi 1 omega) =
          smoothFormsPullbackDiffeomorph J I e 1
            (restrictSmoothFormsToOpen (I := I) (M := M) (A := ℝ) U 1 omega) := by
              simpa [A, e] using restrict_pullbackDiffeomorph_eq_pullback_restrict
                I J phi U omega
        _ = smoothFormsPullbackDiffeomorph J I e 1
            (deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) theta)) := by rw [homega]
        _ = deRhamDifferential (I := J) (M := A) (A := ℝ) 0 thetaAZero := by
              exact (deRhamDifferential_smoothFormsPullbackDiffeomorph
                J I e (smoothRealFunctionToZeroForm (I0 := I) theta)).symm
        _ = deRhamDifferential (I := J) (M := A) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := J) thetaA) := by
              rw [smoothRealFunctionToZeroForm_smoothRealFunctionOfZeroForm]

end Pullback

section NestedOpen

variable {U W : TopologicalSpace.Opens M}

/-- If `W ⊆ U`, the copy of `W` inside `U` is diffeomorphic to `W`. -/
noncomputable def openInOpenOfLEDiffeomorph
    (hWU : W ≤ U) : openInOpen U W ≃ₘ⟮I, I⟯ W := by
  let toFun : openInOpen U W → W := fun x => ⟨((x : U) : M), x.2⟩
  have hto : ContMDiff I I ∞ toFun :=
    contMDiffCodRestrictOpen
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).comp
        (contMDiff_subtype_val (I := I) (n := ∞) (U := openInOpen U W)))
      W (fun x => x.2)
  let invFun : W → openInOpen U W := fun x =>
    ⟨TopologicalSpace.Opens.inclusion hWU x, x.2⟩
  have hinv : ContMDiff I I ∞ invFun :=
    contMDiffCodRestrictOpen
      (contMDiff_inclusion (I := I) (n := ∞) hWU)
      (openInOpen U W) (fun x => x.2)
  let e : openInOpen U W ≃ W :=
    { toFun := toFun
      invFun := invFun
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  exact { toEquiv := e, contMDiff_toFun := hto, contMDiff_invFun := hinv }

/--
%%handwave
name:
  Compatibility of restriction along nested open sets
statement:
  If \(W\subseteq U\) are open subsets of \(M\) and \(\omega\) is a smooth
  \(n\)-form on \(U\), then restricting \(\omega\) to the copy of \(W\) inside
  \(U\) and transporting it through the canonical diffeomorphism to \(W\)
  equals the direct restriction of \(\omega\) along \(W\hookrightarrow U\).
proof:
  At each point of \(W\), the two underlying points of \(U\) coincide.  The
  chain rule identifies the composite tangent map through the nested subtype
  with the derivative of the direct inclusion.
-/
theorem pullback_nested_open_restriction_eq_restrictOfLE
    (hWU : W ≤ U) {n : ℕ}
    (omega : SmoothForms (I := I) (M := U) ℝ n) :
    smoothFormsPullbackDiffeomorph I I
        (openInOpenOfLEDiffeomorph I hWU).symm n
        (restrictSmoothFormsToOpen (I := I) (M := U) (A := ℝ)
          (openInOpen U W) n omega) =
      restrictSmoothFormsOfLE (I := I) (M := M) (A := ℝ) hWU n omega := by
  apply DifferentialForm.ext
  intro x
  let A : TopologicalSpace.Opens U := openInOpen U W
  let e : A ≃ₘ⟮I, I⟯ W := openInOpenOfLEDiffeomorph I hWU
  let xA : A := e.symm x
  let xU : U := (xA : A)
  let LAW : TangentSpace I xA →L[ℝ] TangentSpace I x := mfderiv I I e xA
  let LWA : TangentSpace I x →L[ℝ] TangentSpace I xA := mfderiv I I e.symm x
  let LAU : TangentSpace I xA →L[ℝ] TangentSpace I xU :=
    mfderiv I I (fun y : A => (y : U)) xA
  let LWU : TangentSpace I x →L[ℝ]
      TangentSpace I (TopologicalSpace.Opens.inclusion hWU x) :=
    mfderiv I I (TopologicalSpace.Opens.inclusion hWU) x
  have hpoint : xU = TopologicalSpace.Opens.inclusion hWU x := by
    apply Subtype.ext
    rfl
  have hcomp : LAU.comp LWA = LWU := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) (x := x)
      (g := fun y : A => (y : U)) (f := e.symm)
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := A)).contMDiffAt.mdifferentiableAt
        (by simp))
      (e.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv I I (TopologicalSpace.Opens.inclusion hWU) x = LAU.comp LWA at h
    exact h.symm
  change
    ((omega.toFun xU).compContinuousLinearMap LAU).compContinuousLinearMap LWA =
      (omega.toFun (TopologicalSpace.Opens.inclusion hWU x)).compContinuousLinearMap LWU
  rw [hpoint]
  ext q
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (omega.toFun (TopologicalSpace.Opens.inclusion hWU x))
  funext i
  exact congrArg (fun L => L (q i)) hcomp

/-- Restrict a smooth circle primitive along an inclusion of ambient open sets. -/
noncomputable def SmoothCirclePrimitive.restrictOfLE
    (hWU : W ≤ U)
    {omega : SmoothForms (I := I) (M := U) ℝ 1}
    (P : SmoothCirclePrimitive I omega) :
    SmoothCirclePrimitive I
      (restrictSmoothFormsOfLE (I := I) (M := M) (A := ℝ) hWU 1 omega) := by
  let A : TopologicalSpace.Opens U := openInOpen U W
  let e : A ≃ₘ⟮I, I⟯ W := openInOpenOfLEDiffeomorph I hWU
  let PA : SmoothCirclePrimitive I
      (restrictSmoothFormsToOpen (I := I) (M := U) (A := ℝ) A 1 omega) :=
    P.restrictToOpen I A
  let PW := PA.pullbackDiffeomorph I I e.symm
  exact SmoothCirclePrimitive.congr I PW
    (pullback_nested_open_restriction_eq_restrictOfLE I hWU omega)

/--
%%handwave
name:
  Transporting a circle primitive preserves its phase
statement:
  If two smooth one-forms are equal, transporting a circle primitive of the
  first form across that equality leaves its circle-valued phase unchanged at
  every point.
proof:
  Substitute the equality of the one-forms; the transported primitive is then
  definitionally the original one.
-/
theorem SmoothCirclePrimitive.congr_phase
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M']
    {omega eta : SmoothForms (I := I) (M := M') ℝ 1}
    (P : SmoothCirclePrimitive I omega) (h : omega = eta) (x : M') :
    (SmoothCirclePrimitive.congr I P h).phase x = P.phase x := by
  subst eta
  rfl

/--
%%handwave
name:
  Phase of a circle primitive restricted to a smaller open set
statement:
  If \(W\subseteq U\) are open and a circle primitive on \(U\) is restricted
  to \(W\), then its phase at \(x\in W\) is the original phase evaluated at
  the image of \(x\) under \(W\hookrightarrow U\).
proof:
  Expand the restriction construction and use that transport across equality
  does not alter the phase.
-/
theorem SmoothCirclePrimitive.restrictOfLE_phase
    (hWU : W ≤ U)
    {omega : SmoothForms (I := I) (M := U) ℝ 1}
    (P : SmoothCirclePrimitive I omega) (x : W) :
    (P.restrictOfLE I hWU).phase x =
      P.phase (TopologicalSpace.Opens.inclusion hWU x) := by
  unfold SmoothCirclePrimitive.restrictOfLE
  rw [SmoothCirclePrimitive.congr_phase]
  rfl

end NestedOpen

/-- The exponential of a global smooth real argument is a circle primitive
of its differential. -/
noncomputable def smoothCirclePrimitiveOfGlobalArgument
    (theta : C^∞⟮I, M; ℝ⟯) :
    SmoothCirclePrimitive I
      (deRhamDifferential (I := I) (M := M) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I) theta)) where
  phase :=
    { val := fun x ↦ Complex.exp ((((theta x : ℝ) : ℂ) * Complex.I))
      property := by
        have harg : ContMDiff I (modelWithCornersSelf ℝ ℂ) ∞
            (fun x : M ↦ ((theta x : ℝ) : ℂ)) :=
          Complex.ofRealCLM.contDiff.contMDiff.comp theta.contMDiff
        have hmul : ContMDiff (modelWithCornersSelf ℝ ℂ)
            (modelWithCornersSelf ℝ ℂ) ∞
            (fun z : ℂ ↦ z * Complex.I) := by
          rw [contMDiff_iff_contDiff]
          fun_prop
        have hexp : ContMDiff (modelWithCornersSelf ℝ ℂ)
            (modelWithCornersSelf ℝ ℂ) ∞ Complex.exp := by
          rw [contMDiff_iff_contDiff]
          exact Complex.contDiff_exp
        exact hexp.comp (hmul.comp harg) }
  locally_has_argument := by
    intro x
    let U : TopologicalSpace.Opens M := ⊤
    let thetaU : C^∞⟮I, U; ℝ⟯ :=
      smoothFunctionRestrictToOpen (I := I) U theta
    refine ⟨U, Set.mem_univ x, thetaU, ?_, ?_⟩
    · intro y
      rfl
    · have hzero :
          restrictSmoothFormsToOpen (I := I) (A := ℝ) U 0
              (smoothRealFunctionToZeroForm (I0 := I) theta) =
            smoothRealFunctionToZeroForm (I0 := I) thetaU := by
          apply DifferentialForm.ext
          intro y
          ext q
          rw [show q = (fun i : Fin 0 ↦ nomatch i) from Subsingleton.elim _ _]
          rfl
      calc
        restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1
            (deRhamDifferential (I := I) (M := M) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) theta)) =
          deRhamDifferential (I := I) (M := U) (A := ℝ) 0
            (restrictSmoothFormsToOpen (I := I) (A := ℝ) U 0
              (smoothRealFunctionToZeroForm (I0 := I) theta)) := by
                rw [deRhamDifferential_restrictSmoothFormsToOpen]
        _ = deRhamDifferential (I := I) (M := U) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := I) thetaU) := by
              rw [hzero]

end

end JJMath.Manifold

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

/--
%%handwave
name:
  Restriction of the logarithmic one-form of a unit phase
statement:
  Let \(W\subseteq U\) be open subsets of a manifold.  Suppose
  \(P:U\to S^1\) and \(Q:W\to S^1\) are smooth unit phases and
  \(Q=P|_W\).  Then the canonical logarithmic one-form of \(P\), restricted
  to \(W\), equals the canonical logarithmic one-form of \(Q\).
proof:
  Restrict the circle primitive associated with \(P\) to \(W\).  Its phase is
  \(P|_W=Q\), so uniqueness of the one-form determined by a circle phase
  identifies it with the circle primitive associated with \(Q\).
-/
theorem smoothUnitPhaseOneForm_restrictOfLE
    {U W : TopologicalSpace.Opens M} (hWU : W ≤ U)
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) U ℂ ∞)
    (hP : ∀ x : U, ‖P x‖ = 1)
    (Q : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) W ℂ ∞)
    (hQ : ∀ x : W, ‖Q x‖ = 1)
    (hphase : ∀ x : W,
      Q x = P (TopologicalSpace.Opens.inclusion hWU x)) :
    restrictSmoothFormsOfLE (I := I) (M := M) (A := ℝ) hWU 1
        (smoothUnitPhaseOneForm I P hP) =
      smoothUnitPhaseOneForm I Q hQ := by
  apply SmoothCirclePrimitive.oneForm_eq_of_phase_eq I
    ((smoothUnitPhaseCirclePrimitive I P hP).restrictOfLE I hWU)
    (smoothUnitPhaseCirclePrimitive I Q hQ)
  intro x
  rw [SmoothCirclePrimitive.restrictOfLE_phase]
  exact (hphase x).symm

end


end JJMath.Uniformization
