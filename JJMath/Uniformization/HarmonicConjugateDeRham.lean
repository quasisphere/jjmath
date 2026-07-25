import JJMath.Uniformization.RadoSecondCountable
import JJMath.Manifold.OneFormPeriod
import JJMath.Uniformization.SmoothChainConnectivity
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Harmonic conjugates from first de Rham cohomology

Local holomorphic functions with a fixed real part have imaginary parts that
differ by constants.  Their differentials therefore glue to a global closed
one-form.  When first de Rham cohomology vanishes, a global primitive supplies
a harmonic conjugate and hence a global holomorphic function with the given
real part.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

open JJMath.Manifold

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/--
%%handwave
name: Imaginary part of a local holomorphic real-part branch
statement:
  For a local holomorphic function $f$ with prescribed real part on an open
  subset $U$ of a Riemann surface, bundle $\operatorname{Im}f:U\to\mathbb R$
  as a smooth function.
-/
def SurfaceHolomorphicRealPartBranch.imaginarySmoothFunction
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    {u : Z → ℝ} (B : SurfaceHolomorphicRealPartBranch Z u) :
    C^∞⟮𝓘(ℝ, ℂ), (⟨B.source, B.source_open⟩ : TopologicalSpace.Opens Z); ℝ⟯ := by
  let U : TopologicalSpace.Opens Z := ⟨B.source, B.source_open⟩
  let f : U → ℝ := fun x => (B.toSurfaceTotalFunction (x : Z)).im
  have hchart :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ B.chart B.source := by
    exact (contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, ℂ)) (n := ∞)
        B.chart_mem_atlas)).mono (by
          intro x hx
          exact B.mem_chart_source_of_mem_source hx)
  have hpotC : ContDiffOn ℂ ∞ B.potential B.coordinateSource :=
    B.potential_holomorphic.contDiffOn B.coordinateSource_open.uniqueDiffOn
  have hpotR : ContDiffOn ℝ ∞ B.potential B.coordinateSource :=
    hpotC.restrict_scalars ℝ
  have hpotM :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        B.potential B.coordinateSource := by
    exact contMDiffOn_iff_contDiffOn.mpr hpotR
  have htotal :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        B.toSurfaceTotalFunction B.source := by
    simpa [SurfaceHolomorphicRealPartBranch.toSurfaceTotalFunction,
      Function.comp_def] using
      hpotM.comp hchart (by
        intro x hx
        exact B.chart_mem_coordinateSource_of_mem_source hx)
  have htotalU :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (fun x : U => B.toSurfaceTotalFunction (x : Z)) := by
    rw [← contMDiffOn_univ]
    exact htotal.comp
      (contMDiff_subtype_val (I := 𝓘(ℝ, ℂ)) (n := ∞)).contMDiffOn
      (by intro x _hx; exact x.2)
  have him :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun z : ℂ => z.im) := by
    exact contMDiff_iff_contDiff.mpr Complex.imCLM.contDiff
  exact ⟨f, by
    simpa [f, Function.comp_def] using him.comp htotalU⟩

/--
%%handwave
name: Differential of a local harmonic conjugate
statement:
  For a local holomorphic function $f$ with prescribed real part, define the
  smooth one-form $d(\operatorname{Im}f)$ on its source.
-/
noncomputable def SurfaceHolomorphicRealPartBranch.imaginaryDifferential
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    {u : Z → ℝ} (B : SurfaceHolomorphicRealPartBranch Z u) :
    SmoothForms (I := 𝓘(ℝ, ℂ))
      (M := (⟨B.source, B.source_open⟩ : TopologicalSpace.Opens Z)) ℝ 1 :=
  deRhamDifferential (I := 𝓘(ℝ, ℂ)) (A := ℝ) 0
    (smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ))
      B.imaginarySmoothFunction)

/--
%%handwave
name: Agreement of conjugate differentials under an imaginary translation
statement:
  Suppose two holomorphic functions with the same real part are defined on overlapping surface charts and differ on an open subset by the constant $ic$, with $c\in\mathbb R$. Then the differentials of their imaginary parts agree on that subset.
proof:
  Their imaginary parts differ by the constant $c$. Differentiate this equality; the differential of a constant is zero, and restriction commutes with the de Rham differential.
-/
theorem SurfaceHolomorphicRealPartBranch.imaginaryDifferential_restrict_eq
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    {u : Z → ℝ} (B C : SurfaceHolomorphicRealPartBranch Z u)
    (W : TopologicalSpace.Opens Z)
    (hWB : W ≤ (⟨B.source, B.source_open⟩ : TopologicalSpace.Opens Z))
    (hWC : W ≤ (⟨C.source, C.source_open⟩ : TopologicalSpace.Opens Z))
    (c : ℝ)
    (htransition : ∀ x : W,
      B.toSurfaceTotalFunction (x : Z) =
        C.toSurfaceTotalFunction (x : Z) + (c : ℂ) * Complex.I) :
    restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWB 1
        B.imaginaryDifferential =
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWC 1
        C.imaginaryDifferential := by
  let thetaB : SmoothForms (I := 𝓘(ℝ, ℂ))
      (M := (⟨B.source, B.source_open⟩ : TopologicalSpace.Opens Z)) ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ))
      B.imaginarySmoothFunction
  let thetaC : SmoothForms (I := 𝓘(ℝ, ℂ))
      (M := (⟨C.source, C.source_open⟩ : TopologicalSpace.Opens Z)) ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ))
      C.imaginarySmoothFunction
  let constC : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := W) ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ))
      (smoothRealConstantFunction (I0 := 𝓘(ℝ, ℂ)) c)
  have htheta :
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWB 0 thetaB =
        restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWC 0 thetaC + constC := by
    apply DifferentialForm.ext
    intro x
    ext v
    have him := congrArg Complex.im (htransition x)
    simp [thetaB, thetaC, constC,
      restrictSmoothFormsOfLE, restrictSmoothFormOfLE,
      SurfaceHolomorphicRealPartBranch.imaginarySmoothFunction] at him ⊢
    exact him
  change
    restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWB 1
        (deRhamDifferential (I := 𝓘(ℝ, ℂ)) (A := ℝ) 0 thetaB) =
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWC 1
        (deRhamDifferential (I := 𝓘(ℝ, ℂ)) (A := ℝ) 0 thetaC)
  rw [← deRhamDifferential_restrictSmoothFormsOfLE,
    ← deRhamDifferential_restrictSmoothFormsOfLE]
  change deRhamDifferential (I := 𝓘(ℝ, ℂ)) (M := W) (A := ℝ) 0
      (restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWB 0 thetaB) =
    deRhamDifferential (I := 𝓘(ℝ, ℂ)) (M := W) (A := ℝ) 0
      (restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWC 0 thetaC)
  rw [htheta, map_add,
    deRhamDifferential_smoothRealFunctionToZeroForm_const, add_zero]

/--
%%handwave
name: Pointwise agreement of compatible open-set forms
statement:
  Let $W\subseteq U\cap V$. If smooth $n$-forms on $U$ and $V$ have equal restrictions to $W$, then their ambiently interpreted values agree at every $x\in W$.
proof:
  Precompose both ambient form values with the surjective tangent map of $W\hookrightarrow Z$. The resulting alternating maps are the pointwise values of the two restricted forms, hence equal; surjectivity permits cancellation.
-/
theorem smoothFormOpenExtensionValue_eq_of_restrict_eq
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    (W U V : TopologicalSpace.Opens Z) (hWU : W ≤ U) (hWV : W ≤ V)
    {n : ℕ}
    (alpha : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := U) ℝ n)
    (beta : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := V) ℝ n)
    (heq :
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWU n alpha =
        restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWV n beta)
    (x : W) :
    smoothFormOpenExtensionValue (I := 𝓘(ℝ, ℂ)) (A := ℝ)
        U alpha (x : Z) (hWU x.2) =
      smoothFormOpenExtensionValue (I := 𝓘(ℝ, ℂ)) (A := ℝ)
        V beta (x : Z) (hWV x.2) := by
  let L : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (x : Z) :=
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : W => (y : Z)) x
  apply continuousAlternatingMap_compContinuousLinearMap_injective L
    (mfderiv_subtypeVal_surjective (I := 𝓘(ℝ, ℂ)) W x)
  dsimp [L]
  rw [smoothFormOpenExtensionValue_restrictOfLE
        (I := 𝓘(ℝ, ℂ)) (A := ℝ) W U hWU alpha x,
      smoothFormOpenExtensionValue_restrictOfLE
        (I := 𝓘(ℝ, ℂ)) (A := ℝ) W V hWV beta x]
  exact congrArg (fun omega : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := W) ℝ n =>
    omega.toFun x) heq

/--
%%handwave
name: Transitivity of restriction for smooth forms
statement:
  Let $W\subseteq U\subseteq Z$. If an ambient smooth form $\omega$ restricts to $\alpha$ on $U$, then $\omega|_W$ equals the restriction of $\alpha$ from $U$ to $W$.
proof:
  Evaluate at a point of $W$ and factor the tangent map $W\hookrightarrow Z$ through $U$. The assumed equality on $U$ then gives equality after composition with the inclusion differential.
-/
theorem restrictSmoothFormsToOpen_eq_restrictSmoothFormsOfLE_of_restrict_eq
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    (W U : TopologicalSpace.Opens Z) (hWU : W ≤ U) {n : ℕ}
    (omega : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := Z) ℝ n)
    (alpha : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := U) ℝ n)
    (heq : restrictSmoothFormsToOpen (I := 𝓘(ℝ, ℂ)) (A := ℝ) U n omega = alpha) :
    restrictSmoothFormsToOpen (I := 𝓘(ℝ, ℂ)) (A := ℝ) W n omega =
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWU n alpha := by
  apply DifferentialForm.ext
  intro x
  let xU : U := TopologicalSpace.Opens.inclusion hWU x
  let LU : TangentSpace 𝓘(ℝ, ℂ) xU →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (x : Z) :=
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : U => (y : Z)) xU
  let LWU : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) xU :=
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (TopologicalSpace.Opens.inclusion hWU) x
  let LW : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (x : Z) :=
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : W => (y : Z)) x
  have hpoint := congrArg
    (fun eta : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := U) ℝ n => eta.toFun xU) heq
  have hfactor : LU.comp LWU = LW := by
    simpa [LU, LWU, LW, xU] using
      mfderiv_subtypeVal_comp_inclusion_eq
        (I := 𝓘(ℝ, ℂ)) W U hWU x
  change (omega.toFun (x : Z)).compContinuousLinearMap LW =
    (alpha.toFun xU).compContinuousLinearMap LWU
  rw [← hfactor]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hpoint' :
      (omega.toFun (x : Z)).compContinuousLinearMap LU = alpha.toFun xU := by
    simpa [restrictSmoothFormsToOpen, restrictSmoothFormToOpen, LU, xU] using hpoint
  exact congrArg
    (fun eta : FormAt (I := 𝓘(ℝ, ℂ)) (M := U) ℝ n xU =>
      eta (LWU ∘ v)) hpoint'

structure HarmonicConjugateDifferentialData
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    {u : Z → ℝ}
    (_hbranches : ∀ p : Z,
      ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source) where
  omega : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := Z) ℝ 1
  restrict_eq : ∀ B : SurfaceHolomorphicRealPartBranch Z u,
    restrictSmoothFormsToOpen (I := 𝓘(ℝ, ℂ)) (A := ℝ)
        (⟨B.source, B.source_open⟩ : TopologicalSpace.Opens Z) 1 omega =
      B.imaginaryDifferential

/--
%%handwave
name: Global conjugate differential from local holomorphic real parts
statement:
  Suppose a real function $u$ on a complex one-manifold is locally the real part of a holomorphic function around every point. Then the differentials of the local imaginary parts glue to a global smooth real one-form $\omega$.
proof:
  Choose one local branch at each point and define $\omega_x$ from its imaginary differential. On overlaps, two branches with the same real part differ locally by a purely imaginary constant, so their imaginary differentials agree. This independence makes the pointwise form smooth and gives the required restriction identity for every branch.
-/
theorem exists_harmonicConjugateDifferentialData
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    {u : Z → ℝ}
    (hbranches : ∀ p : Z,
      ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source) :
    Nonempty (HarmonicConjugateDifferentialData hbranches) := by
  classical
  let chosen : Z → SurfaceHolomorphicRealPartBranch Z u :=
    fun x => Classical.choose (hbranches x)
  have hchosen (x : Z) : x ∈ (chosen x).source :=
    Classical.choose_spec (hbranches x)
  let U : SurfaceHolomorphicRealPartBranch Z u → TopologicalSpace.Opens Z :=
    fun B => ⟨B.source, B.source_open⟩
  let alpha : ∀ B : SurfaceHolomorphicRealPartBranch Z u,
      SmoothForms (I := 𝓘(ℝ, ℂ)) (M := U B) ℝ 1 :=
    fun B => B.imaginaryDifferential
  let form : (x : Z) → FormAt (I := 𝓘(ℝ, ℂ)) ℝ 1 x := fun x =>
    smoothFormOpenExtensionValue (I := 𝓘(ℝ, ℂ)) (A := ℝ)
      (U (chosen x)) (alpha (chosen x)) x (hchosen x)
  have hcover : iSup U = ⊤ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rcases hbranches x with ⟨B, hxB⟩
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨B, hxB⟩
  have hlocal :
      ∀ B : SurfaceHolomorphicRealPartBranch Z u, ∀ ⦃x : Z⦄ (hx : x ∈ U B),
        form x = smoothFormOpenExtensionValue (I := 𝓘(ℝ, ℂ)) (A := ℝ)
          (U B) (alpha B) x hx := by
    intro B x hx
    let C := chosen x
    have hxC : x ∈ C.source := hchosen x
    let S := holomorphicRealPartBranchSystem hbranches
    rcases holomorphicRealPartBranchSystem_hasLocalTransitions hbranches C B x
        ⟨hxC, hx⟩ with ⟨T⟩
    let W : TopologicalSpace.Opens Z := ⟨T.neighborhood, T.neighborhood_open⟩
    have hWB : W ≤ U B := fun _ hy => (T.subset_overlap hy).2
    have hWC : W ≤ U C := fun _ hy => (T.subset_overlap hy).1
    have htrans : ∀ y : W,
        B.toSurfaceTotalFunction (y : Z) =
          C.toSurfaceTotalFunction (y : Z) +
            ((T.transition.toAdd : ℝ) : ℂ) * Complex.I := by
      intro y
      simpa [S, holomorphicRealPartBranchSystem] using
        T.transition_eq (y : Z) y.2
    have hrestr :
        restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWB 1 (alpha B) =
          restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWC 1 (alpha C) := by
      exact B.imaginaryDifferential_restrict_eq C W hWB hWC
        T.transition.toAdd htrans
    have hxW : x ∈ W := T.mem_neighborhood
    change smoothFormOpenExtensionValue (I := 𝓘(ℝ, ℂ)) (A := ℝ)
        (U C) (alpha C) x hxC =
      smoothFormOpenExtensionValue (I := 𝓘(ℝ, ℂ)) (A := ℝ)
        (U B) (alpha B) x hx
    exact (smoothFormOpenExtensionValue_eq_of_restrict_eq
      W (U B) (U C) hWB hWC (alpha B) (alpha C) hrestr
      ⟨x, hxW⟩).symm
  let omega : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := Z) ℝ 1 :=
    { toFun := form
      isContMDiff :=
        isContMDiffForm_of_eqOn_iSup_open_cover
          (I := 𝓘(ℝ, ℂ)) (A := ℝ) U hcover form alpha hlocal }
  refine ⟨{ omega := omega, restrict_eq := ?_ }⟩
  intro B
  apply DifferentialForm.ext
  intro x
  have hxlocal := hlocal B x.2
  change (form (x : Z)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (fun y : U B => (y : Z)) x) = (alpha B).toFun x
  rw [hxlocal]
  exact smoothFormOpenExtensionValue_restrict
    (I := 𝓘(ℝ, ℂ)) (A := ℝ) (U B) (alpha B) x

/--
%%handwave
name: Closedness of the global conjugate differential
statement:
  The global one-form obtained by gluing differentials of local harmonic conjugates is closed.
proof:
  Near any point, restrict to a local holomorphic real-part branch. There the form is $d\theta$ for the branch's imaginary part, so its differential is $d^2\theta=0$. Surjectivity of the tangent map from the open chart transfers this local vanishing to the ambient two-form.
-/
theorem HarmonicConjugateDifferentialData.closed
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    {u : Z → ℝ}
    {hbranches : ∀ p : Z,
      ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source}
    (D : HarmonicConjugateDifferentialData hbranches) :
    deRhamDifferential (I := 𝓘(ℝ, ℂ)) (M := Z) (A := ℝ) 1 D.omega = 0 := by
  apply DifferentialForm.ext
  intro x
  rcases hbranches x with ⟨B, hxB⟩
  let U : TopologicalSpace.Opens Z := ⟨B.source, B.source_open⟩
  let xU : U := ⟨x, hxB⟩
  let L : TangentSpace 𝓘(ℝ, ℂ) xU →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x :=
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : U => (y : Z)) xU
  apply continuousAlternatingMap_compContinuousLinearMap_injective L
    (mfderiv_subtypeVal_surjective (I := 𝓘(ℝ, ℂ)) U xU)
  have hrestrict :
      restrictSmoothFormsToOpen (I := 𝓘(ℝ, ℂ)) (A := ℝ) U 2
          (deRhamDifferential (I := 𝓘(ℝ, ℂ)) (M := Z) (A := ℝ) 1 D.omega) = 0 := by
    rw [← deRhamDifferential_restrictSmoothFormsToOpen, D.restrict_eq B]
    exact deRhamDifferential_comp_eq_zero (I := 𝓘(ℝ, ℂ))
      (M := U) (A := ℝ)
      (smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ))
        B.imaginarySmoothFunction)
  have hpoint := congrArg
    (fun eta : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := U) ℝ 2 => eta.toFun xU)
    hrestrict
  simpa [restrictSmoothFormsToOpen, restrictSmoothFormToOpen, U, xU, L] using hpoint

/--
%%handwave
name: Closed form represented by the harmonic-conjugate differential
statement:
  Bundle the global one-form obtained by gluing the local differentials
  $d(\operatorname{Im}f)$ together with the proof that it is closed.
-/
noncomputable def HarmonicConjugateDifferentialData.toClosedForm
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    {u : Z → ℝ}
    {hbranches : ∀ p : Z,
      ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source}
    (D : HarmonicConjugateDifferentialData hbranches) :
    DeRhamClosedForms (I := 𝓘(ℝ, ℂ)) (M := Z) (A := ℝ) 1 :=
  ⟨D.omega, D.closed⟩

set_option maxHeartbeats 1500000 in
end
end Uniformization
end JJMath
