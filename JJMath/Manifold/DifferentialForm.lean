import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Differential forms on manifolds

This file introduces a chartwise definition of differential forms on a
manifold, following mathlib's existing model-space differential forms.

The underlying degree-`n` form at a point is a continuous alternating map on
the tangent space at that point.  Regularity is imposed by passing to every
extended chart and asking the coordinate representative to be `C^r` as a map
from the model vector space to the model-space alternating maps.  Here `r`
uses mathlib's calculus convention: finite differentiability levels, `∞` for
smoothness, and `ω` for analyticity.

This is intended as a foundation for a future de Rham complex and comparison
with sheaf and singular cohomology.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

section AlternatingPullbackCalculus

/--
%%handwave
name:
  Continuous variation of the derivative of multilinear pullback
statement:
  For normed spaces \(A,B,C\) over a nontrivially normed field and a finite
  index set \(I\), the map
  \[
    (\alpha,(L_i)_{i\in I})\longmapsto
    D_L\bigl(\alpha\circ(L_i)_{i\in I}\bigr)
  \]
  from a continuous multilinear form and a family of continuous linear maps
  to the derivative with respect to that family is continuous.
proof:
  Multilinear pullback is a polynomial map of \((\alpha,(L_i))\), hence is
  \(C^1\).  Its derivative is continuous; restricting that derivative to the
  linear-map variables gives the asserted map.
-/
theorem continuous_continuousMultilinearMap_fderivCompContinuousLinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {A B C ι : Type*}
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    [Fintype ι] [DecidableEq ι] :
    Continuous (fun p :
        (ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C) ×
          (ι → A →L[𝕜] B) =>
      p.1.fderivCompContinuousLinearMap p.2) := by
  let H :
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C) ×
        (ι → A →L[𝕜] B) →
      ContinuousMultilinearMap 𝕜 (fun _ : ι => A) C :=
    fun p => p.1.compContinuousLinearMap p.2
  have hH : ContDiff 𝕜 1 H := by
    let K :
        ((ι → A →L[𝕜] B) ×
          ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C) →
        ContinuousMultilinearMap 𝕜 (fun _ : ι => A) C :=
      fun p => p.2.compContinuousLinearMap p.1
    have hKpoly : CPolynomialOn 𝕜 K Set.univ := by
      simpa [K] using
        (ContinuousMultilinearMap.cpolynomialOn_uncurry_compContinuousLinearMap
          (𝕜 := 𝕜) (ι := ι) (Fm := fun _ : ι => A) (Em := fun _ : ι => B)
          (G := C) (t := Set.univ))
    have hK : ContDiff 𝕜 1 K := by
      rw [← contDiffOn_univ]
      exact hKpoly.contDiffOn
    let swap :
        (ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C) ×
          (ι → A →L[𝕜] B) →
        (ι → A →L[𝕜] B) ×
          ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C :=
      fun p => (p.2, p.1)
    have hswap : ContDiff 𝕜 1 swap := by
      exact contDiff_snd.prodMk contDiff_fst
    simpa [H, K, swap, Function.comp_def] using hK.comp hswap
  have hDf : Continuous (fderiv 𝕜 H) :=
    hH.continuous_fderiv (by norm_num)
  let linr :
      (ι → A →L[𝕜] B) →L[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C) ×
          (ι → A →L[𝕜] B) :=
    ContinuousLinearMap.inr 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C)
      (ι → A →L[𝕜] B)
  have hproj : Continuous (fun p => (fderiv 𝕜 H p).comp linr) := by
    exact (ContinuousLinearMap.precomp
      (G := ContinuousMultilinearMap 𝕜 (fun _ : ι => A) C) linr).continuous.comp hDf
  refine hproj.congr ?_
  intro p
  have hderiv :=
    (ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
      (𝕜 := 𝕜) (ι := ι) (F := fun _ : ι => A) (G := fun _ : ι => B)
      (H := C) p).hasFDerivAt.fderiv
  change fderiv 𝕜 H p = _ at hderiv
  rw [hderiv, ContinuousLinearMap.add_comp]
  have hzero :
      ((ContinuousMultilinearMap.compContinuousLinearMapL p.2).comp
        (ContinuousLinearMap.fst 𝕜
          (ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C)
          (ι → A →L[𝕜] B))).comp linr = 0 := by
    ext dg v
    simp [linr, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hzero, zero_add]
  ext dg v
  simp [linr]
/--
%%handwave
name:
  Continuity of the derivative of alternating pullback
statement:
  Let \(f:X\to\operatorname{Alt}^I(B,C)\) and
  \(g:X\to\mathcal L(A,B)\) be continuous on \(S\subseteq X\).  Then
  \[
    x\longmapsto D_g\bigl(f(x)\circ g(x)^{\times I}\bigr)
  \]
  is continuous on \(S\).
proof:
  Regard alternating maps as multilinear maps, insert \(g(x)\) diagonally in
  every argument, and apply continuity of the derivative of multilinear
  pullback.  The embedding of alternating maps into multilinear maps detects
  the resulting continuity.
-/
theorem continuousOn_continuousAlternatingMap_fderivCompContinuousLinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X A B C ι : Type*}
    [TopologicalSpace X]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    [Fintype ι] [DecidableEq ι]
    {s : Set X} {f : X → B [⋀^ι]→L[𝕜] C}
    {g : X → A →L[𝕜] B}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x : X => (f x).fderivCompContinuousLinearMap (g x)) s := by
  let diag : (A →L[𝕜] B) →L[𝕜] (ι → A →L[𝕜] B) :=
    ContinuousLinearMap.pi fun _ : ι =>
      ContinuousLinearMap.id 𝕜 (A →L[𝕜] B)
  have hML :=
    continuous_continuousMultilinearMap_fderivCompContinuousLinearMap
      (𝕜 := 𝕜) (ι := ι) (A := A) (B := B) (C := C)
  intro x hx
  have hleft : ContinuousWithinAt
      (fun y : X => ContinuousAlternatingMap.toContinuousMultilinearMap (f y)) s x :=
    ContinuousAlternatingMap.continuous_toContinuousMultilinearMap.continuousAt
      |>.comp_continuousWithinAt (hf x hx)
  have hright : ContinuousWithinAt (fun y : X => diag (g y)) s x :=
    diag.continuous.continuousAt.comp_continuousWithinAt (hg x hx)
  have hpair : ContinuousWithinAt
      (fun y : X =>
        (ContinuousAlternatingMap.toContinuousMultilinearMap (f y), diag (g y))) s x :=
    hleft.prodMk hright
  have hopen : ContinuousWithinAt
      (fun y : X =>
        (ContinuousAlternatingMap.toContinuousMultilinearMap (f y)).fderivCompContinuousLinearMap
          (diag (g y))) s x := by
    simpa [Function.comp_def] using hML.continuousAt.comp_continuousWithinAt hpair
  have hpre : ContinuousWithinAt
      (fun y : X =>
        ((ContinuousAlternatingMap.toContinuousMultilinearMap (f y)).fderivCompContinuousLinearMap
          (diag (g y))).comp diag) s x := by
    exact (ContinuousLinearMap.precomp
      (G := ContinuousMultilinearMap 𝕜 (fun _ : ι => A) C) diag).continuous.continuousAt
      |>.comp_continuousWithinAt hopen
  refine (Topology.IsInducing.continuousWithinAt_iff
    (f := fun y : X => (f y).fderivCompContinuousLinearMap (g y))
    (g := (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜 :
        (A [⋀^ι]→L[𝕜] C) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => A) C).comp)
    (ContinuousLinearMap.isEmbedding_postcomp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜 :
        (A [⋀^ι]→L[𝕜] C) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => A) C)
      ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap).isInducing).2 ?_
  refine hpre.congr (fun y hy => ?_) ?_
  · change (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜).comp
        ((f y).fderivCompContinuousLinearMap (g y)) =
      ((ContinuousAlternatingMap.toContinuousMultilinearMap (f y)).fderivCompContinuousLinearMap
        (diag (g y))).comp diag
    simp [diag]
  · change (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜).comp
        ((f x).fderivCompContinuousLinearMap (g x)) =
      ((ContinuousAlternatingMap.toContinuousMultilinearMap (f x)).fderivCompContinuousLinearMap
        (diag (g x))).comp diag
    simp [diag]

/--
%%handwave
name:
  A \(C^1\) family of pullbacks is \(C^1\)
statement:
  Let \(S\) be a set with unique derivatives.  If
  \(f:S\to\operatorname{Alt}^I(B,C)\) and
  \(g:S\to\mathcal L(A,B)\) are \(C^1\), then
  \[
    x\longmapsto f(x)\circ g(x)^{\times I}
  \]
  is \(C^1\) on \(S\).
proof:
  The chain rule gives two derivative terms, one from differentiating \(f\)
  and one from differentiating \(g\).  Each varies continuously: the first by
  continuity of composition and the second by continuity of the derivative of
  alternating pullback.  The derivative characterization of \(C^1\) maps then
  applies.
-/
theorem contDiffOn_continuousAlternatingMap_compContinuousLinearMap_one
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X A B C ι : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    [Fintype ι] [DecidableEq ι]
    {s : Set X} {f : X → B [⋀^ι]→L[𝕜] C}
    {g : X → A →L[𝕜] B}
    (hs : UniqueDiffOn 𝕜 s)
    (hf : ContDiffOn 𝕜 1 f s) (hg : ContDiffOn 𝕜 1 g s) :
    ContDiffOn 𝕜 1 (fun x ↦ (f x).compContinuousLinearMap (g x)) s := by
  classical
  have hdiff :
      DifferentiableOn 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s := by
    intro x hx
    exact (hf.differentiableOn_one x hx)
      |>.continuousAlternatingMapCompContinuousLinearMap
        (hg.differentiableOn_one x hx)
  have hf0 : ContDiffOn 𝕜 0 f s := hf.of_le (by norm_num)
  have hg0 : ContDiffOn 𝕜 0 g s := hg.of_le (by norm_num)
  have hDf0 : ContDiffOn 𝕜 0 (fderivWithin 𝕜 f s) s :=
    hf.fderivWithin hs (by norm_num)
  have hDg0 : ContDiffOn 𝕜 0 (fderivWithin 𝕜 g s) s :=
    hg.fderivWithin hs (by norm_num)
  have hcompCLM :
      ContinuousOn
        (fun x : X =>
          ContinuousAlternatingMap.compContinuousLinearMapCLM
            (𝕜 := 𝕜) (ι := ι) (E := A) (F := C) (E' := B) (g x))
        s := by
    exact ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn
      hg0.continuousOn
  have hterm₁ :
      ContinuousOn
        (fun x : X =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM
            (𝕜 := 𝕜) (ι := ι) (E := A) (F := C) (E' := B) (g x)).comp
            (fderivWithin 𝕜 f s x))
        s :=
    hcompCLM.clm_comp hDf0.continuousOn
  have hfderivComp :
      ContinuousOn
        (fun x : X => (f x).fderivCompContinuousLinearMap (g x))
        s := by
    exact continuousOn_continuousAlternatingMap_fderivCompContinuousLinearMap
      hf0.continuousOn hg0.continuousOn
  have hterm₂ :
      ContinuousOn
        (fun x : X =>
          ((f x).fderivCompContinuousLinearMap (g x)).comp
            (fderivWithin 𝕜 g s x))
        s :=
    hfderivComp.clm_comp hDg0.continuousOn
  have hderiv_cont :
      ContinuousOn
        (fun x : X =>
          fderivWithin 𝕜
            (fun x ↦ (f x).compContinuousLinearMap (g x)) s x)
        s := by
    refine (hterm₁.add hterm₂).congr ?_
    intro x hx
    exact fderivWithin_continuousAlternatingMapCompContinuousLinearMap
      (hf.differentiableOn_one x hx) (hg.differentiableOn_one x hx)
      (hs x hx)
  have hderiv0 :
      ContDiffOn 𝕜 0
        (fun x : X =>
          fderivWithin 𝕜
            (fun x ↦ (f x).compContinuousLinearMap (g x)) s x)
        s := by
    rw [contDiffOn_zero]
    exact hderiv_cont
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by norm_num]
  exact contDiffOn_succ_of_fderivWithin hdiff (by simp) hderiv0

end AlternatingPullbackCalculus

section ContinuousAlternatingMapLemmas

variable {R : Type*} [Semiring R]
variable {M₁ M₂ N : Type*}
variable [AddCommMonoid M₁] [Module R M₁] [TopologicalSpace M₁]
variable [AddCommMonoid M₂] [Module R M₂] [TopologicalSpace M₂]
variable [AddCommMonoid N] [Module R N] [TopologicalSpace N]
variable {ι : Type*}

/--
%%handwave
name:
  Pullback by a surjective linear map is injective
statement:
  If a continuous linear map is surjective, then precomposing alternating
  forms with it is injective.
proof:
  Pass to the underlying alternating maps and use the corresponding algebraic
  injectivity for precomposition by a surjective linear map.
-/
theorem continuousAlternatingMap_compContinuousLinearMap_injective
    (f : M₂ →L[R] M₁) (hf : Function.Surjective f) :
    Function.Injective
      (fun omega : M₁ [⋀^ι]→L[R] N => omega.compContinuousLinearMap f) := by
  intro omega eta h
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply AlternatingMap.compLinearMap_injective (f : M₂ →ₗ[R] M₁) hf
  change (omega.compContinuousLinearMap f).toAlternatingMap =
    (eta.compContinuousLinearMap f).toAlternatingMap
  exact congrArg ContinuousAlternatingMap.toAlternatingMap h

/--
%%handwave
name:
  Pullback along an inverse linear map cancels
statement:
  If a continuous linear map is invertible, pulling an alternating form back by
  its inverse and then by the map itself recovers the original form.
proof:
  Evaluate on an arbitrary tuple of vectors and use that the inverse really is
  an inverse on each vector.
-/
theorem continuousAlternatingMap_compContinuousLinearMap_inverse_comp
    (omega : M₂ [⋀^ι]→L[R] N) (f : M₂ →L[R] M₁)
  (hf : f.IsInvertible) :
    (omega.compContinuousLinearMap f.inverse).compContinuousLinearMap f = omega := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr
  funext i
  exact hf.inverse_apply_self (v i)

end ContinuousAlternatingMapLemmas

section ContinuousAlternatingMapContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X B C D ι : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup B] [NormedSpace 𝕜 B]
variable [NormedAddCommGroup C] [NormedSpace 𝕜 C]
variable [NormedAddCommGroup D] [NormedSpace 𝕜 D]
variable [Fintype ι]

/--
%%handwave
name:
  Differentiability of alternating pullback
statement:
  If a family of alternating forms and a family of continuous linear maps are
  differentiable on a set, then the family obtained by precomposition is
  differentiable on that set.
proof:
  Apply the differentiability rule for precomposition of continuous alternating
  maps with continuous linear maps.
-/
theorem differentiableOn_continuousAlternatingMap_compContinuousLinearMap
    {s : Set X}
    {f : X → B [⋀^ι]→L[𝕜] C} {g : X → D →L[𝕜] B}
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s := by
  intro x hx
  exact (hf x hx).continuousAlternatingMapCompContinuousLinearMap (hg x hx)

noncomputable def continuousMultilinearMapAlternatizationCLM
    [DecidableEq ι] :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => D) C →L[𝕜] D [⋀^ι]→L[𝕜] C where
  toLinearMap :=
    { toFun := fun f => ContinuousMultilinearMap.alternatization f
      map_add' := by
        intro f g
        ext v
        simp [ContinuousMultilinearMap.alternatization_apply_apply]
      map_smul' := by
        intro c f
        ext v
        rw [ContinuousMultilinearMap.alternatization_apply_apply,
          ContinuousAlternatingMap.smul_apply,
          ContinuousMultilinearMap.alternatization_apply_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [ContinuousMultilinearMap.smul_apply]
        simpa using smul_comm (Equiv.Perm.sign σ) c (f (v ∘ σ)) }
  cont := by
    rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
    change Continuous
      (fun f : ContinuousMultilinearMap 𝕜 (fun _ : ι => D) C =>
        (ContinuousMultilinearMap.alternatization f).toContinuousMultilinearMap)
    simp only [ContinuousMultilinearMap.alternatization_apply_toContinuousMultilinearMap]
    exact continuous_finsetSum _ fun σ _ =>
      ((ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 D C σ).toContinuousLinearEquiv.continuous).const_smul _

/--
%%handwave
name:
  Alternatization as a continuous linear map
statement:
  The continuous linear map built from alternatization evaluates to ordinary
  alternatization.
proof:
  This is the defining evaluation rule for the constructed continuous linear
  map.
-/
theorem continuousMultilinearMapAlternatizationCLM_apply
    [DecidableEq ι]
    (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => D) C) :
    continuousMultilinearMapAlternatizationCLM (𝕜 := 𝕜) (D := D) (C := C) (ι := ι) f =
      ContinuousMultilinearMap.alternatization f :=
  rfl

/--
%%handwave
name:
  Alternatization after diagonal precomposition
statement:
  Alternatizing an alternating form after precomposing every variable by the
  same linear map gives the factorial multiple of the pulled-back alternating
  form.
proof:
  Compare the underlying alternating maps and use the standard formula for
  alternatization of an alternating map.
-/
theorem continuousMultilinearMap_alternatization_compContinuousLinearMap_diagonal
    [DecidableEq ι]
    (omega : B [⋀^ι]→L[𝕜] C) (g : D →L[𝕜] B) :
    ContinuousMultilinearMap.alternatization
        (omega.toContinuousMultilinearMap.compContinuousLinearMap (fun _ : ι => g)) =
      (Nat.factorial (Fintype.card ι) : 𝕜) • omega.compContinuousLinearMap g := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap,
    ContinuousAlternatingMap.toAlternatingMap_smul]
  change MultilinearMap.alternatization
      ((omega.compContinuousLinearMap g).toAlternatingMap :
        MultilinearMap 𝕜 (fun _ : ι => D) C) =
    (Nat.factorial (Fintype.card ι) : 𝕜) • (omega.compContinuousLinearMap g).toAlternatingMap
  simpa [Nat.cast_smul_eq_nsmul 𝕜] using
    AlternatingMap.coe_alternatization (R := 𝕜) (M := D) (N' := C)
      (ι := ι) (omega.compContinuousLinearMap g).toAlternatingMap

/--
%%handwave
name:
  Smoothness of alternating pullback
statement:
  The operation sending a linear map and an alternating form to the pullback of
  the form by the map is \(C^r\).
proof:
  Express pullback through multilinear composition and alternatization; these
  operations are smooth, and the factorial factor is invertible in
  characteristic zero.
-/
theorem contDiff_continuousAlternatingMap_compContinuousLinearMap
    [DecidableEq ι] [CharZero 𝕜] {r : WithTop ℕ∞} :
    ContDiff 𝕜 r
      (fun p : (D →L[𝕜] B) × (B [⋀^ι]→L[𝕜] C) =>
        p.2.compContinuousLinearMap p.1) := by
  let diag : (D →L[𝕜] B) →L[𝕜] (ι → D →L[𝕜] B) :=
    ContinuousLinearMap.pi fun _ : ι =>
      ContinuousLinearMap.id 𝕜 (D →L[𝕜] B)
  let alt : ContinuousMultilinearMap 𝕜 (fun _ : ι => D) C →L[𝕜] D [⋀^ι]→L[𝕜] C :=
    continuousMultilinearMapAlternatizationCLM (𝕜 := 𝕜) (D := D) (C := C) (ι := ι)
  let incl : B [⋀^ι]→L[𝕜] C →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM (𝕜 := 𝕜)
      (E := B) (F := C) (ι := ι) 𝕜
  let scale : D [⋀^ι]→L[𝕜] C →L[𝕜] D [⋀^ι]→L[𝕜] C :=
    (1 / (Nat.factorial (Fintype.card ι) : 𝕜)) •
      ContinuousLinearMap.id 𝕜 (D [⋀^ι]→L[𝕜] C)
  have hpoly :
      ContDiff 𝕜 r
        (fun p : (ι → D →L[𝕜] B) × ContinuousMultilinearMap 𝕜 (fun _ : ι => B) C =>
          p.2.compContinuousLinearMap p.1) := by
    rw [← contDiffOn_univ]
    exact (ContinuousMultilinearMap.cpolynomialOn_uncurry_compContinuousLinearMap
      (𝕜 := 𝕜) (ι := ι) (Fm := fun _ : ι => D) (Em := fun _ : ι => B)
      (G := C) (t := Set.univ)).contDiffOn
  have hpairs :
      ContDiff 𝕜 r
        (fun p : (D →L[𝕜] B) × (B [⋀^ι]→L[𝕜] C) =>
          (diag p.1, incl p.2)) := by
    exact (diag.contDiff.comp contDiff_fst).prodMk
      (incl.contDiff.comp contDiff_snd)
  have hmain :
      ContDiff 𝕜 r
        (fun p : (D →L[𝕜] B) × (B [⋀^ι]→L[𝕜] C) =>
          scale (alt ((incl p.2).compContinuousLinearMap (diag p.1)))) := by
    exact scale.contDiff.comp (alt.contDiff.comp (hpoly.comp hpairs))
  rw [← contDiffOn_univ] at hmain ⊢
  refine hmain.congr ?_
  intro p _hp
  symm
  dsimp [diag, alt, incl, scale]
  rw [continuousMultilinearMapAlternatizationCLM_apply]
  rw [continuousMultilinearMap_alternatization_compContinuousLinearMap_diagonal
    (omega := p.2) (g := p.1)]
  rw [smul_smul]
  have hfact : (Nat.factorial (Fintype.card ι) : 𝕜) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (Fintype.card ι))
  have hscalar :
      (1 / (Nat.factorial (Fintype.card ι) : 𝕜)) *
          (Nat.factorial (Fintype.card ι) : 𝕜) = 1 := by
    field_simp [hfact]
  rw [hscalar, one_smul]

/--
%%handwave
name:
  Chartwise smoothness of alternating pullback
statement:
  If a family of alternating forms and a family of linear maps are \(C^r\) on
  a set, then their pointwise pullback is \(C^r\) on that set.
proof:
  Compose the globally smooth pullback operation with the two \(C^r\) input
  families.
-/
theorem contDiffOn_continuousAlternatingMap_compContinuousLinearMap
    [DecidableEq ι] [CharZero 𝕜]
    {s : Set X} {r : WithTop ℕ∞}
    {f : X → B [⋀^ι]→L[𝕜] C} {g : X → D →L[𝕜] B}
    (hf : ContDiffOn 𝕜 r f s) (hg : ContDiffOn 𝕜 r g s) :
    ContDiffOn 𝕜 r (fun x ↦ (f x).compContinuousLinearMap (g x)) s := by
  simpa [Function.comp_def] using
    (contDiff_continuousAlternatingMap_compContinuousLinearMap
      (𝕜 := 𝕜) (D := D) (B := B) (C := C) (ι := ι) (r := r)).comp₂_contDiffOn hg hf

end ContinuousAlternatingMapContDiff

section ModelProductCartan

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
%%handwave
name:
  Time-slice derivative as a product derivative
statement:
  If a family of product-space forms is differentiable at \((x,t)\), then the
  derivative in the interval variable of its evaluation on fixed base vectors
  is the product-space Fréchet derivative evaluated on the time vector.
proof:
  Evaluate the form on the fixed tuple of base vectors and compose the
  resulting differentiable scalar-valued map on \(s\times[0,1]\) with the
  curve \(\tau\mapsto (x,\tau)\).  The derivative of this curve is the time
  vector.
-/
theorem hasDerivWithinAt_modelForm_product_time_eval
    {s : Set E}
    {n : ℕ}
    (eta : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F)
    {x : E} (hx : x ∈ s) {t : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heta :
      DifferentiableWithinAt ℝ eta (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t))
    (v : Fin (n + 1) → E) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        ((eta (x, τ)).compContinuousLinearMap
          (ContinuousLinearMap.inl ℝ E ℝ)) v)
      (fderivWithin ℝ
        (fun p : E × ℝ ↦ eta p (fun i : Fin (n + 1) ↦ ((v i), (0 : ℝ))))
        (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t) ((0 : E), (1 : ℝ)))
      (Set.Icc (0 : ℝ) 1) t := by
  let u : Fin (n + 1) → E × ℝ := fun i ↦ ((v i), (0 : ℝ))
  have hscalar :
      DifferentiableWithinAt ℝ
        (fun p : E × ℝ ↦ eta p u)
        (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t) :=
    heta.continuousAlternatingMap_apply_const u
  have hcurve :
      HasDerivWithinAt
        (fun τ : ℝ ↦ (x, τ))
        ((0 : E), (1 : ℝ))
        (Set.Icc (0 : ℝ) 1) t := by
    exact (hasDerivWithinAt_const (c := x) (x := t)
      (s := Set.Icc (0 : ℝ) 1)).prodMk (hasDerivWithinAt_id t (Set.Icc (0 : ℝ) 1))
  have hmaps :
      MapsTo (fun τ : ℝ ↦ (x, τ)) (Set.Icc (0 : ℝ) 1)
        (s ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    exact ⟨hx, hτ⟩
  have hcomp :
      HasDerivWithinAt
        ((fun p : E × ℝ ↦ eta p u) ∘ fun τ : ℝ ↦ (x, τ))
        (fderivWithin ℝ
          (fun p : E × ℝ ↦ eta p u)
          (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t) ((0 : E), (1 : ℝ)))
        (Set.Icc (0 : ℝ) 1) t :=
    hscalar.hasFDerivWithinAt.comp_hasDerivWithinAt t hcurve hmaps
  simpa [u, Function.comp_def, ContinuousAlternatingMap.compContinuousLinearMap_apply] using hcomp

/--
%%handwave
name:
  Base-slice derivative as a product derivative
statement:
  For a differentiable map on \(s\times[0,1]\), the derivative of the slice
  \(y\mapsto f(y,t)\) in a base direction \(w\) is the product derivative of
  \(f\) in the direction \((w,0)\).
proof:
  Compose \(f\) with the affine inclusion \(y\mapsto (y,t)\).  The derivative
  of this inclusion is the inclusion of the base tangent space into the
  product tangent space.
-/
theorem fderivWithin_product_base_slice_apply
    {s : Set E} (hsUnique : UniqueDiffOn ℝ s)
    {f : E × ℝ → F}
    {x : E} (hx : x ∈ s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hf :
      DifferentiableWithinAt ℝ f (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t))
    (w : E) :
    fderivWithin ℝ (fun y : E ↦ f (y, t)) s x w =
      fderivWithin ℝ f (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t) (w, (0 : ℝ)) := by
  let slice : E → E × ℝ := fun y ↦ (y, t)
  have hslice :
      HasFDerivWithinAt slice (ContinuousLinearMap.inl ℝ E ℝ) s x := by
    simpa [slice, ContinuousLinearMap.inl] using
      (hasFDerivWithinAt_id (𝕜 := ℝ) x s).prodMk
        (hasFDerivWithinAt_const (𝕜 := ℝ) (c := t) (x := x) (s := s))
  have hmaps :
      MapsTo slice s (s ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro y hy
    exact ⟨hy, ht⟩
  have hcomp :
      fderivWithin ℝ (f ∘ slice) s x =
        (fderivWithin ℝ f (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t)).comp
          (ContinuousLinearMap.inl ℝ E ℝ) :=
    (hf.hasFDerivWithinAt.comp x hslice hmaps).fderivWithin
      (hsUnique.uniqueDiffWithinAt hx)
  exact congrFun (congrArg DFunLike.coe hcomp) w

/--
%%handwave
name:
  Removing the first coordinate from a vector with an adjoined head
statement:
  For \(a\in\alpha\) and \(b:\operatorname{Fin}(n)\to\alpha\), deleting
  coordinate \(0\) from the vector \((a,b_0,\ldots,b_{n-1})\) gives \(b\).
proof:
  Evaluate both sides at each coordinate; the index shift defining deletion
  cancels the shift used to adjoin the head.
-/
@[simp]
theorem Fin.removeNth_zero_vecCons {α : Type*} {n : ℕ}
    (a : α) (b : Fin n → α) :
    (0 : Fin (n + 1)).removeNth (Matrix.vecCons a b) = b := by
  funext i
  simp [Fin.removeNth]

/--
%%handwave
name:
  Removing a noninitial coordinate from a vector with an adjoined head
statement:
  For \(a\in\alpha\), \(b:\operatorname{Fin}(n+1)\to\alpha\), and
  \(i\in\operatorname{Fin}(n+1)\), deleting coordinate \(i+1\) from
  \((a,b)\) gives \((a,b\text{ with coordinate }i\text{ deleted})\).
proof:
  Split the remaining coordinate into the initial coordinate and a successor;
  both identities then follow from the definitions of adjoining and deleting
  coordinates.
-/
@[simp]
theorem Fin.removeNth_succ_vecCons {α : Type*} {n : ℕ}
    (a : α) (b : Fin (n + 1) → α) (i : Fin (n + 1)) :
    i.succ.removeNth (Matrix.vecCons a b) =
      Matrix.vecCons a (i.removeNth b) := by
  funext j
  cases j using Fin.cases with
  | zero =>
      simp [Fin.removeNth]
  | succ j =>
      simp [Fin.removeNth]

/--
%%handwave
name:
  Cancellation of consecutive alternating sign sums
statement:
  For \(a_0,\ldots,a_n\) in an additive commutative group,
  \(\sum_{i=0}^n(-1)^i a_i+\sum_{i=0}^n(-1)^{i+1}a_i=0\).
proof:
  Combine the two sums term by term.  Each summand is
  \((-1)^i a_i-(-1)^i a_i=0\).
-/
theorem alternating_zsmul_sum_add_succ_eq_zero
    {A : Type*} [AddCommGroup A] {n : ℕ} (a : Fin (n + 1) → A) :
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • a i) +
        (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.succ : ℕ) • a i) =
      0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero ?_
  intro i _hi
  simp [pow_succ]

/--
%%handwave
name:
  Splitting the product exterior derivative into time and base terms
statement:
  For a differentiable family of forms on \(s\times[0,1]\), evaluating the
  exterior derivative on \(\partial_t,v_0,\ldots,v_n\) gives the time
  derivative of the base restriction minus the exterior derivative, in the
  base variables, of the contraction by \(\partial_t\).
proof:
  Expand both exterior derivatives as alternating sums of directional
  derivatives.  The zero-th summand of the product expansion is the time
  derivative, while the remaining summands agree with the base expansion after
  moving the time vector past one omitted base vector, contributing the
  opposite sign.
-/
theorem modelForm_product_extDerivWithin_time_split
    {s : Set E} (_hsOpen : IsOpen s) (hsUnique : UniqueDiffOn ℝ s)
    {n : ℕ}
    (eta : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F)
    {x : E} (hx : x ∈ s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heta :
      DifferentiableWithinAt ℝ eta (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t))
    (v : Fin (n + 1) → E) :
    fderivWithin ℝ
        (fun p : E × ℝ ↦ eta p (fun i : Fin (n + 1) ↦ ((v i), (0 : ℝ))))
        (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t) ((0 : E), (1 : ℝ)) =
      ((extDerivWithin
          (fun y : E ↦
            ((eta (y, t)).curryLeft ((0 : E), (1 : ℝ))).compContinuousLinearMap
              (ContinuousLinearMap.inl ℝ E ℝ))
          s x) v) +
        (extDerivWithin eta (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t)
          (Matrix.vecCons ((0 : E), (1 : ℝ))
            (fun i : Fin (n + 1) ↦ ((v i), (0 : ℝ))))) := by
  classical
  let S : Set (E × ℝ) := s ×ˢ Set.Icc (0 : ℝ) 1
  let time : E × ℝ := ((0 : E), (1 : ℝ))
  let base : Fin (n + 1) → E × ℝ := fun i ↦ ((v i), (0 : ℝ))
  let full : Fin (n + 2) → E × ℝ := Matrix.vecCons time base
  let contraction : E → E [⋀^Fin n]→L[ℝ] F :=
    fun y ↦
      ((eta (y, t)).curryLeft time).compContinuousLinearMap
        (ContinuousLinearMap.inl ℝ E ℝ)
  have hSUnique : UniqueDiffWithinAt ℝ S (x, t) := by
    exact (hsUnique.prod uniqueDiffOn_Icc_zero_one).uniqueDiffWithinAt ⟨hx, ht⟩
  have hslice :
      DifferentiableWithinAt ℝ (fun y : E ↦ eta (y, t)) s x := by
    let slice : E → E × ℝ := fun y ↦ (y, t)
    have hslice_deriv :
        HasFDerivWithinAt slice (ContinuousLinearMap.inl ℝ E ℝ) s x := by
      simpa [slice, ContinuousLinearMap.inl] using
        (hasFDerivWithinAt_id (𝕜 := ℝ) x s).prodMk
          (hasFDerivWithinAt_const (𝕜 := ℝ) (c := t) (x := x) (s := s))
    have hmaps : MapsTo slice s S := by
      intro y hy
      exact ⟨hy, ht⟩
    exact (heta.comp x hslice_deriv.differentiableWithinAt hmaps)
  have hcontraction :
      DifferentiableWithinAt ℝ contraction s x := by
    let curryOp :
        ((E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ]
          (E × ℝ) →L[ℝ] (E × ℝ) [⋀^Fin n]→L[ℝ] F :=
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := E × ℝ) (F := F) (n := n)).toContinuousLinearMap
    let evalTime :
        ((E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ]
          (E × ℝ) [⋀^Fin n]→L[ℝ] F :=
      (ContinuousLinearMap.apply ℝ ((E × ℝ) [⋀^Fin n]→L[ℝ] F) time).comp curryOp
    let compBase :
        ((E × ℝ) [⋀^Fin n]→L[ℝ] F) →L[ℝ] E [⋀^Fin n]→L[ℝ] F :=
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (𝕜 := ℝ) (ι := Fin n) (E := E) (E' := E × ℝ) (F := F)
        (ContinuousLinearMap.inl ℝ E ℝ)
    let contractOp :
        ((E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ]
          E [⋀^Fin n]→L[ℝ] F :=
      compBase.comp evalTime
    have hcontract :
        DifferentiableWithinAt ℝ
          (contractOp ∘ fun y : E ↦ eta (y, t)) s x :=
      contractOp.differentiableAt.comp_differentiableWithinAt x hslice
    simpa [contraction, contractOp, compBase, evalTime, curryOp, Function.comp_def,
      ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      ContinuousAlternatingMap.curryLeftLI_apply] using hcontract
  have htotal_expand :
      extDerivWithin eta S (x, t) full =
        ∑ i : Fin (n + 2),
          (-1 : ℤ) ^ (i : ℕ) •
            fderivWithin ℝ (fun p : E × ℝ ↦ eta p (i.removeNth full))
              S (x, t) (full i) := by
    simpa [S, full] using extDerivWithin_apply heta hSUnique full
  have hbase_expand :
      extDerivWithin contraction s x v =
        ∑ i : Fin (n + 1),
          (-1 : ℤ) ^ (i : ℕ) •
            fderivWithin ℝ (fun y : E ↦ contraction y (i.removeNth v))
              s x (v i) := by
    simpa [contraction] using
      extDerivWithin_apply hcontraction (hsUnique.uniqueDiffWithinAt hx) v
  have hbase_term :
      ∀ i : Fin (n + 1),
        fderivWithin ℝ (fun y : E ↦ contraction y (i.removeNth v))
            s x (v i) =
          fderivWithin ℝ (fun p : E × ℝ ↦ eta p (i.succ.removeNth full))
            S (x, t) (full i.succ) := by
    intro i
    have hscalar :
        DifferentiableWithinAt ℝ
          (fun p : E × ℝ ↦ eta p (i.succ.removeNth full))
          S (x, t) :=
      heta.continuousAlternatingMap_apply_const (i.succ.removeNth full)
    have hslice_eval :=
      fderivWithin_product_base_slice_apply
        (E := E) (F := F) (s := s) hsUnique hx ht hscalar (v i)
    simpa [S, full, base, time, contraction,
      ContinuousAlternatingMap.compContinuousLinearMap_apply] using hslice_eval
  let T : F :=
    fderivWithin ℝ (fun p : E × ℝ ↦ eta p base) S (x, t) time
  let A : Fin (n + 1) → F :=
    fun i ↦
      fderivWithin ℝ (fun p : E × ℝ ↦ eta p (i.succ.removeNth full))
        S (x, t) (full i.succ)
  have htotal_succ :
      extDerivWithin eta S (x, t) full =
        T + ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.succ : ℕ) • A i := by
    rw [htotal_expand]
    simp [Fin.sum_univ_succ, T, A, full, base, time]
  have hbase_A :
      extDerivWithin contraction s x v =
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A i := by
    rw [hbase_expand]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [hbase_term i]
  have hcancel :
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A i) +
          (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.succ : ℕ) • A i) =
        0 :=
    alternating_zsmul_sum_add_succ_eq_zero A
  have hsum :
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A i) +
          (T + ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.succ : ℕ) • A i) =
        T := by
    calc
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A i) +
          (T + ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.succ : ℕ) • A i)
          = T + ((∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A i) +
              (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.succ : ℕ) • A i)) := by
            abel
      _ = T := by
            rw [hcancel, add_zero]
  change T = extDerivWithin contraction s x v + extDerivWithin eta S (x, t) full
  rw [hbase_A, htotal_succ]
  exact hsum.symm

/--
%%handwave
name:
  Product Cartan formula for the time coordinate
statement:
  Let \(\eta\) be a \(C^1\) family of forms on \(U\times[0,1]\).  The
  derivative in the interval coordinate of the restriction of \(\eta\) to
  base tangent vectors is the sum of the base exterior derivative of the
  contraction by \(\partial_t\) and the total exterior derivative of \(\eta\),
  evaluated on \(\partial_t\) followed by the chosen base tangent vectors.
proof:
  Expand both exterior derivatives as alternating sums of directional
  derivatives.  The total alternating sum has one term in the time direction
  and the remaining terms are the negative of the base exterior derivative of
  the contraction; rearranging gives the stated identity.
-/
theorem hasDerivWithinAt_modelForm_product_time_cartan
    {s : Set E} (hsOpen : IsOpen s) (hsUnique : UniqueDiffOn ℝ s)
    {n : ℕ}
    (eta : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F)
    (heta : ContDiffOn ℝ 1 eta (s ×ˢ Set.Icc (0 : ℝ) 1))
    (x : E) (hx : x ∈ s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (v : Fin (n + 1) → E) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        ((eta (x, τ)).compContinuousLinearMap
          (ContinuousLinearMap.inl ℝ E ℝ)) v)
      (((extDerivWithin
          (fun y : E ↦
            ((eta (y, t)).curryLeft ((0 : E), (1 : ℝ))).compContinuousLinearMap
              (ContinuousLinearMap.inl ℝ E ℝ))
          s x) v) +
        (extDerivWithin eta (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t)
          (Matrix.vecCons ((0 : E), (1 : ℝ))
            (fun i : Fin (n + 1) ↦ ((v i), (0 : ℝ))))))
      (Set.Icc (0 : ℝ) 1) t := by
  have hdiff :
      DifferentiableWithinAt ℝ eta (s ×ˢ Set.Icc (0 : ℝ) 1) (x, t) :=
    (heta (x, t) ⟨hx, ht⟩).differentiableWithinAt (by norm_num)
  have htime :=
    hasDerivWithinAt_modelForm_product_time_eval
      (E := E) (F := F) (s := s) eta hx ht hdiff v
  have hsplit :=
    modelForm_product_extDerivWithin_time_split
      (E := E) (F := F) (s := s) hsOpen hsUnique eta hx ht hdiff v
  simpa [hsplit] using htime

end ModelProductCartan

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H)

section Coefficients

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable (n : ℕ)

/--
%%handwave
name:
  Model-space differential form
statement:
  A degree \(n\) differential form on a model vector space, with values in a
  normed coefficient space, is a continuous alternating \(n\)-linear map.
-/
abbrev ModelForm : Type _ :=
  E [⋀^Fin n]→L[𝕜] F

/--
%%handwave
name:
  Pointwise differential form
statement:
  A degree \(n\) differential form at a point of a manifold is a continuous
  alternating \(n\)-linear map on the tangent space at that point.
-/
abbrev FormAt (x : M) : Type _ :=
  TangentSpace I x [⋀^Fin n]→L[𝕜] F

variable {I F n}

/--
The coordinate representative of a possibly dependent pointwise form in a
chart.  It is obtained by pulling the form back along the inverse extended
chart.
-/
def coordinateExpression
    (form : (x : M) → FormAt (I := I) F n x)
    (e : OpenPartialHomeomorph M H) :
    E → ModelForm (𝕜 := 𝕜) (E := E) F n :=
  fun y ↦
    (form ((e.extend I).symm y)).compContinuousLinearMap
      (mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y)

/--
%%handwave
name:
  Chartwise regularity of a differential form
statement:
  A pointwise form is \(C^r\) when every coordinate representative on an
  extended chart is \(C^r\) on the chart image; the analytic case is obtained
  by taking \(r=\omega\).
-/
def IsContMDiffForm
    (r : WithTop ℕ∞) (form : (x : M) → FormAt (I := I) F n x) : Prop :=
  ∀ e ∈ atlas H M,
    ContDiffOn 𝕜 r (coordinateExpression (I := I) (F := F) (n := n) form e)
      (e.extend I).target

/--
%%handwave
name:
  Differentiability of an extended inverse chart
statement:
  If \(e\) is a chart in a \(C^1\) atlas and \(y\) belongs to the target of
  its extension, then the extended inverse chart is differentiable at \(y\)
  relative to that target.
proof:
  The extended inverse is the chart inverse after the inverse model-with-corners
  map.  Both factors are differentiable at the relevant points, so the claim
  follows by composition.
-/
theorem mdifferentiableWithinAt_extend_symm_of_mem_atlas
    [IsManifold I 1 M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    {y : E} (hy : y ∈ (e.extend I).target) :
    MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y := by
  rw [e.extend_coe_symm (I := I)]
  have hy_range : y ∈ range I := e.extend_target_subset_range hy
  have hy_target : I.symm y ∈ e.target := by
    simpa [e.extend_target (I := I)] using hy.2
  have hI : MDifferentiableWithinAt 𝓘(𝕜, E) I I.symm (range I) y :=
    I.mdifferentiableWithinAt_symm hy_range
  have he_symm : MDifferentiableAt I I e.symm (I.symm y) :=
    mdifferentiableAt_atlas_symm (I := I) he hy_target
  exact he_symm.comp_mdifferentiableWithinAt y (hI.mono (e.extend_target_subset_range))

/--
%%handwave
name:
  Derivatives of an extended chart and its inverse
statement:
  If \(e\) is a chart in a \(C^1\) atlas and \(x\) lies in its source, then
  \(D(e^{-1})_{e(x)}\circ De_x=\operatorname{id}_{T_xM}\), with the inverse
  derivative taken relative to the extended chart target.
proof:
  Differentiate the local identity \(e^{-1}\circ e=\operatorname{id}\) on
  the open extended chart source and apply the chain rule.
-/
theorem mfderivWithin_extend_symm_comp_mfderiv_extend_of_mem_atlas
    [IsManifold I 1 M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    {x : M} (hx : x ∈ e.source) :
    (mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target ((e.extend I) x)).comp
        (mfderiv I 𝓘(𝕜, E) (e.extend I) x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have hx_ext : x ∈ (e.extend I).source := by
    simpa [e.extend_source (I := I)] using hx
  have htarget : (e.extend I) x ∈ (e.extend I).target :=
    (e.extend I).map_source hx_ext
  have hunique : UniqueMDiffWithinAt I (e.extend I).source x :=
    (e.isOpen_extend_source (I := I)).uniqueMDiffWithinAt hx_ext
  have hemax : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.subset_maximalAtlas (I := I) (n := 1) he
  have h_extend_at :
      MDifferentiableAt I 𝓘(𝕜, E) (e.extend I) x :=
    (contMDiffAt_extend (I := I) (e := e) hemax hx).mdifferentiableAt one_ne_zero
  have h_extend_within :
      MDifferentiableWithinAt I 𝓘(𝕜, E) (e.extend I) (e.extend I).source x :=
    h_extend_at.mdifferentiableWithinAt
  have h_symm_within :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target
        ((e.extend I) x) :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) he htarget
  have hmaps :
      (e.extend I).source ⊆ (e.extend I) ⁻¹' (e.extend I).target := by
    intro z hz
    exact (e.extend I).map_source hz
  have h_extend_deriv :
      mfderiv I 𝓘(𝕜, E) (e.extend I) x =
        mfderivWithin I 𝓘(𝕜, E) (e.extend I) (e.extend I).source x := by
    rw [mfderivWithin_eq_mfderiv hunique h_extend_at]
  rw [h_extend_deriv]
  rw [← mfderivWithin_comp_of_eq
    (x := x) (y := (e.extend I) x)
    (g := (e.extend I).symm) (f := e.extend I)
    (s := (e.extend I).source) (u := (e.extend I).target)
    h_symm_within h_extend_within hmaps hunique rfl]
  rw [← mfderivWithin_id hunique]
  apply Filter.EventuallyEq.mfderivWithin_eq
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (e.extend I).left_inv hz
  · exact (e.extend I).left_inv hx_ext

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Unique differentiability of an extended chart target
statement:
  The target of every extended chart is a unique-differentiability set in the
  model vector space.
proof:
  The target is the inverse image under the model-with-corners equivalence of
  the open chart target, so unique differentiability follows from that of the
  model range.
-/
theorem uniqueDiffOn_extend_target
    (e : OpenPartialHomeomorph M H) :
    UniqueDiffOn 𝕜 (e.extend I).target := by
  rw [e.extend_target (I := I)]
  exact I.uniqueDiffOn_preimage e.open_target

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Relative neighborhoods in an extended chart target
statement:
  If \(y\) lies in the target of an extended chart, then the neighborhood
  filters of \(y\) relative to the extended target and relative to the full
  model range coincide.
proof:
  Write \(y\) as the image of its inverse-chart point and use that the ordinary
  chart target is open around this point.
-/
theorem nhdsWithin_extend_target_eq_of_mem
    {e : OpenPartialHomeomorph M H} {y : E}
    (hy : y ∈ (e.extend I).target) :
    𝓝[(e.extend I).target] y = 𝓝[range I] y := by
  rw [← (e.extend I).right_inv hy]
  have hx_extend : (e.extend I).symm y ∈ (e.extend I).source :=
    (e.extend I).map_target hy
  have hx : (e.extend I).symm y ∈ e.source := by
    simpa [e.extend_source (I := I)] using hx_extend
  exact e.nhdsWithin_extend_target_eq (I := I) hx

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Density of the interior of a coordinate-change domain
statement:
  For any two charts, the domain \(S\) of their extended coordinate change
  satisfies \(S\subseteq\overline{\operatorname{int}S}\).
proof:
  Intersect an arbitrary neighborhood with the coordinate-change domain and
  with the dense interior of the model range.  At the resulting interior point
  the relative coordinate-change domain is an ordinary neighborhood.
-/
theorem extendCoordChange_source_subset_closure_interior
    (e e' : OpenPartialHomeomorph M H) :
    (I.extendCoordChange e e').source ⊆
      closure (interior (I.extendCoordChange e e').source) := by
  intro y hy
  rw [mem_closure_iff_nhds]
  intro t ht
  have hsource_mem :
      (I.extendCoordChange e e').source ∈ 𝓝[range I] y :=
    I.extendCoordChange_source_mem_nhdsWithin hy
  have hsource_union_mem :
      (I.extendCoordChange e e').source ∪ (range I)ᶜ ∈ 𝓝 y := by
    rw [← nhdsWithin_univ, ← union_compl_self (range I), nhdsWithin_union]
    exact Filter.union_mem_sup hsource_mem self_mem_nhdsWithin
  have hy_range : y ∈ range I := by
    rw [I.extendCoordChange_source] at hy
    rcases hy with ⟨z, _hz, rfl⟩
    exact mem_range_self z
  have hy_closure : y ∈ closure (interior (range I)) :=
    I.range_subset_closure_interior hy_range
  obtain ⟨z, ⟨⟨hzt, hz_source_or_compl⟩, hz_range_int⟩⟩ :
      (t ∩ ((I.extendCoordChange e e').source ∪ (range I)ᶜ) ∩
          interior (range I)).Nonempty :=
    mem_closure_iff_nhds.1 hy_closure _
      (Filter.inter_mem ht hsource_union_mem)
  have hz_source : z ∈ (I.extendCoordChange e e').source := by
    rcases hz_source_or_compl with hz_source | hz_compl
    · exact hz_source
    · exact False.elim (hz_compl (interior_subset hz_range_int))
  have hz_source_nhds :
      (I.extendCoordChange e e').source ∈ 𝓝 z := by
    have hsource_nhdsWithin :
        (I.extendCoordChange e e').source ∈ 𝓝[range I] z :=
      I.extendCoordChange_source_mem_nhdsWithin hz_source
    have hrange_nhds : range I ∈ 𝓝 z :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hz_range_int) interior_subset
    have h_eq : 𝓝[range I] z = 𝓝 z := nhdsWithin_eq_nhds.2 hrange_nhds
    simpa [h_eq] using hsource_nhdsWithin
  exact ⟨z, hzt, mem_interior_iff_mem_nhds.mpr hz_source_nhds⟩

omit [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [ChartedSpace H M] in
/--
%%handwave
name:
  Intersecting a locally dense set with an open set
statement:
  If \(x\in\overline{\operatorname{int}s}\), \(u\) is open, and \(x\in u\),
  then \(x\in\overline{\operatorname{int}(s\cap u)}\).
proof:
  Every neighborhood of \(x\) remains a neighborhood after intersection with
  \(u\), and hence meets \(\operatorname{int}s\cap u\), which is contained in
  \(\operatorname{int}(s\cap u)\).
-/
theorem mem_closure_interior_inter_of_mem_open
    {X : Type*} [TopologicalSpace X] {s u : Set X} {x : X}
    (hs : x ∈ closure (interior s)) (hu : IsOpen u) (hxu : x ∈ u) :
    x ∈ closure (interior (s ∩ u)) := by
  rw [mem_closure_iff_nhds] at hs ⊢
  intro t ht
  rcases hs (t ∩ u) (Filter.inter_mem ht (hu.mem_nhds hxu)) with
    ⟨z, hz_tu, hz_ints⟩
  refine ⟨z, hz_tu.1, ?_⟩
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset
      (Filter.inter_mem (isOpen_interior.mem_nhds hz_ints) (hu.mem_nhds hz_tu.2))
      (by
        intro w hw
        exact ⟨interior_subset hw.1, hw.2⟩))

/--
%%handwave
name:
  Regularity of the coordinate exterior derivative
statement:
  Let \(s\) be a unique-differentiability set.  If an \(n\)-form-valued map
  \(\eta\) is \(C^{r+1}\) on \(s\), then its exterior derivative computed
  relative to \(s\) is \(C^r\) on \(s\).
proof:
  The exterior derivative is the continuous alternation of the first derivative
  of \(\eta\).  Differentiation lowers regularity by one, while the fixed
  continuous linear alternation map preserves \(C^r\) regularity.
-/
theorem contDiffOn_extDerivWithin
    {eta : E → ModelForm (𝕜 := 𝕜) (E := E) F n} {s : Set E}
    {r : WithTop ℕ∞}
    (heta : ContDiffOn 𝕜 (r + 1) eta s) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 r (extDerivWithin eta s) s := by
  change ContDiffOn 𝕜 r
    (fun x => (ContinuousAlternatingMap.alternatizeUncurryFinCLM (𝕜 := 𝕜) E F)
      (fderivWithin 𝕜 eta s x)) s
  exact
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM (𝕜 := 𝕜) E F).contDiff.comp_contDiffOn
      (heta.fderivWithin hs (show r + 1 ≤ r + 1 from le_rfl))

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Compatibility of inverse charts with a coordinate change
statement:
  If \(y\) belongs to the domain of the coordinate change
  \(\phi=e'\circ e^{-1}\), then \(e'^{-1}(\phi(y))=e^{-1}(y)\), where the
  charts are understood as their extensions to the model space.
proof:
  The point \(e^{-1}(y)\) lies in the source of \(e'\), so the left-inverse
  identity for \(e'\) applies directly.
-/
theorem extendCoordChange_symm_apply
    {e e' : OpenPartialHomeomorph M H} {y : E}
    (hy : y ∈ (I.extendCoordChange e e').source) :
    (e'.extend I).symm ((I.extendCoordChange e e') y) = (e.extend I).symm y := by
  set φ := I.extendCoordChange e e'
  have hy_source' : (e.extend I).symm y ∈ (e'.extend I).source := by
    have hy_source'_raw : (e.extend I).symm y ∈ e'.source := by
      simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hy.2
    simpa [e'.extend_source (I := I)] using hy_source'_raw
  change (e'.extend I).symm (φ y) = (e.extend I).symm y
  rw [show φ y = e'.extend I ((e.extend I).symm y) from rfl]
  exact (e'.extend I).left_inv hy_source'

/--
%%handwave
name:
  Chain rule for inverse charts under a coordinate change
statement:
  For \(C^1\) charts \(e,e'\), a point \(y\) in the domain of
  \(\phi=e'\circ e^{-1}\) satisfies
  \[
    D(e^{-1})_y=D(e'^{-1})_{\phi(y)}\circ D\phi_y,
  \]
  with derivatives taken relative to the corresponding chart domains.
proof:
  The inverse-chart maps agree on the coordinate-change domain as
  \(e^{-1}=e'^{-1}\circ\phi\).  Differentiate this identity and apply the
  within-set chain rule.
-/
theorem mfderivWithin_extend_symm_coordChange
    [IsManifold I 1 M]
    {e e' : OpenPartialHomeomorph M H} {y : E}
    (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    (hy : y ∈ (I.extendCoordChange e e').source) :
    mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y =
      (mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target
        ((I.extendCoordChange e e') y)).comp
        (fderivWithin 𝕜 (I.extendCoordChange e e') (I.extendCoordChange e e').source y) := by
  set φ := I.extendCoordChange e e'
  have hy_target : y ∈ (e.extend I).target := by
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hy.1
  have hφ_target_subset_target' : φ.target ⊆ (e'.extend I).target := by
    intro z hz
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_target] using hz.1
  have hφ_maps : MapsTo φ φ.source (e'.extend I).target := by
    intro z hz
    exact hφ_target_subset_target' (φ.mapsTo hz)
  have hφ_source_subset_target : φ.source ⊆ (e.extend I).target := by
    intro z hz
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hz.1
  have htarget_mem : (e.extend I).target ∈ 𝓝[φ.source] y :=
    Filter.mem_of_superset self_mem_nhdsWithin hφ_source_subset_target
  have hunique_φ : UniqueMDiffWithinAt 𝓘(𝕜, E) φ.source y :=
    (I.uniqueDiffOn_extendCoordChange_source (e := e) (e' := e') y hy).uniqueMDiffWithinAt
  have he_symm_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) he hy_target
  have hwithin :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm φ.source y =
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y :=
    he_symm_diff.mfderivWithin_mono_of_mem_nhdsWithin hunique_φ htarget_mem
  have hcomp_eq : EqOn ((e'.extend I).symm ∘ φ) (e.extend I).symm φ.source := by
    intro z hz
    exact extendCoordChange_symm_apply (I := I) hz
  have hcomp_deriv :
      mfderivWithin 𝓘(𝕜, E) I ((e'.extend I).symm ∘ φ) φ.source y =
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm φ.source y :=
    mfderivWithin_congr hcomp_eq (hcomp_eq hy)
  have hφ_diff : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) φ φ.source y := by
    have hφ_contdiff :
        ContDiffOn 𝕜 1 φ φ.source :=
      I.contDiffOn_extendCoordChange
        (IsManifold.subset_maximalAtlas (I := I) (n := 1) he)
        (IsManifold.subset_maximalAtlas (I := I) (n := 1) he')
    exact (hφ_contdiff y hy).differentiableWithinAt one_ne_zero |>.mdifferentiableWithinAt
  have hφy_target : φ y ∈ (e'.extend I).target :=
    hφ_target_subset_target' (φ.map_source hy)
  have he'_symm_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y) :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) he' hφy_target
  have hchain :
      mfderivWithin 𝓘(𝕜, E) I ((e'.extend I).symm ∘ φ) φ.source y =
        (mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y)).comp
          (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) φ φ.source y) :=
    mfderivWithin_comp y he'_symm_diff hφ_diff hφ_maps hunique_φ
  have h_to_chain :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y =
        mfderivWithin 𝓘(𝕜, E) I ((e'.extend I).symm ∘ φ) φ.source y :=
    hwithin.symm.trans hcomp_deriv.symm
  have h_to_model :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y =
        (mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y)).comp
          (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) φ φ.source y) :=
    h_to_chain.trans hchain
  exact h_to_model.trans (by
    congr 1
    exact mfderivWithin_eq_fderivWithin)

/--
%%handwave
name:
  Transformation law for coordinate expressions of differential forms
statement:
  Let \(\omega\) be a pointwise \(n\)-form and let
  \(\phi=e'\circ e^{-1}\) be the transition between two \(C^1\) charts.  On
  the transition domain,
  \[
    \omega_e(y)=\omega_{e'}(\phi(y))\circ (D\phi_y)^{\times n}.
  \]
proof:
  Expand both coordinate expressions as pullbacks by inverse-chart
  derivatives, then use
  \(D(e^{-1})_y=D(e'^{-1})_{\phi(y)}\circ D\phi_y\).
-/
theorem coordinateExpression_coordChange
    [IsManifold I 1 M]
    (form : (x : M) → FormAt (I := I) F n x)
    {e e' : OpenPartialHomeomorph M H} {y : E}
    (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    (hy : y ∈ (I.extendCoordChange e e').source) :
    coordinateExpression (I := I) (F := F) (n := n) form e y =
      (coordinateExpression (I := I) (F := F) (n := n) form e'
        ((I.extendCoordChange e e') y)).compContinuousLinearMap
        (fderivWithin 𝕜 (I.extendCoordChange e e') (I.extendCoordChange e e').source y) := by
  set φ := I.extendCoordChange e e'
  have hy_target : y ∈ (e.extend I).target := by
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hy.1
  have hxy_extend_source : (e.extend I).symm y ∈ (e.extend I).source :=
    (e.extend I).map_target hy_target
  have hxy_source' : (e.extend I).symm y ∈ e'.source := by
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hy.2
  have hφ_target_subset_target' : φ.target ⊆ (e'.extend I).target := by
    intro z hz
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_target] using hz.1
  have hφ_maps : MapsTo φ φ.source (e'.extend I).target := by
    intro z hz
    exact hφ_target_subset_target' (φ.mapsTo hz)
  have hφ_source_subset_target : φ.source ⊆ (e.extend I).target := by
    intro z hz
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hz.1
  have htarget_mem : (e.extend I).target ∈ 𝓝[φ.source] y :=
    Filter.mem_of_superset self_mem_nhdsWithin hφ_source_subset_target
  have hunique_φ : UniqueMDiffWithinAt 𝓘(𝕜, E) φ.source y :=
    (I.uniqueDiffOn_extendCoordChange_source (e := e) (e' := e') y hy).uniqueMDiffWithinAt
  have he_symm_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) he hy_target
  have hwithin :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm φ.source y =
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y :=
    he_symm_diff.mfderivWithin_mono_of_mem_nhdsWithin hunique_φ htarget_mem
  have hcomp_eq : EqOn ((e'.extend I).symm ∘ φ) (e.extend I).symm φ.source := by
    intro z hz
    have hz_source' : (e.extend I).symm z ∈ e'.source := by
      simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hz.2
    have hz_extend_source' : (e.extend I).symm z ∈ (e'.extend I).source := by
      simpa [e'.extend_source (I := I)] using hz_source'
    change (e'.extend I).symm (φ z) = (e.extend I).symm z
    rw [show φ z = e'.extend I ((e.extend I).symm z) from rfl]
    exact (e'.extend I).left_inv hz_extend_source'
  have hcomp_deriv :
      mfderivWithin 𝓘(𝕜, E) I ((e'.extend I).symm ∘ φ) φ.source y =
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm φ.source y :=
    mfderivWithin_congr hcomp_eq (hcomp_eq hy)
  have hφ_diff : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) φ φ.source y := by
    have hφ_contdiff :
        ContDiffOn 𝕜 1 φ φ.source :=
      I.contDiffOn_extendCoordChange
        (IsManifold.subset_maximalAtlas (I := I) (n := 1) he)
        (IsManifold.subset_maximalAtlas (I := I) (n := 1) he')
    exact (hφ_contdiff y hy).differentiableWithinAt one_ne_zero |>.mdifferentiableWithinAt
  have hφy_target : φ y ∈ (e'.extend I).target :=
    hφ_target_subset_target' (φ.map_source hy)
  have he'_symm_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y) :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) he' hφy_target
  have hchain :
      mfderivWithin 𝓘(𝕜, E) I ((e'.extend I).symm ∘ φ) φ.source y =
        (mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y)).comp
          (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) φ φ.source y) :=
    mfderivWithin_comp y he'_symm_diff hφ_diff hφ_maps hunique_φ
  have hderiv :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y =
        (mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y)).comp
          (fderivWithin 𝕜 φ φ.source y) := by
    have h_to_chain :
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y =
          mfderivWithin 𝓘(𝕜, E) I ((e'.extend I).symm ∘ φ) φ.source y :=
      hwithin.symm.trans hcomp_deriv.symm
    have h_to_model :
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y =
          (mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y)).comp
            (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) φ φ.source y) :=
      h_to_chain.trans hchain
    exact h_to_model.trans (by
      congr 1
      exact mfderivWithin_eq_fderivWithin)
  have hpoint : (e'.extend I).symm (φ y) = (e.extend I).symm y := hcomp_eq hy
  rw [coordinateExpression, coordinateExpression]
  rw [hderiv]
  rw [hpoint]
  ext v
  rfl

/--
%%handwave
name:
  \(C^r\) differential form
statement:
  A \(C^r\) differential form is a pointwise alternating covector field whose
  coordinate representatives are \(C^r\).
-/
structure DifferentialForm (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n : ℕ) (r : WithTop ℕ∞) where
  /-- The value of the form at each point. -/
  toFun : (x : M) → FormAt (I := I) F n x
  /-- The form is `C^r` in every chart. -/
  isContMDiff : IsContMDiffForm (I := I) (F := F) (n := n) r toFun

namespace DifferentialForm

variable {r : WithTop ℕ∞}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

instance : Zero (DifferentialForm (I := I) (M := M) F n r) where
  zero :=
    { toFun := fun _ ↦ 0
      isContMDiff := by
        intro e _he
        simpa [coordinateExpression] using
          (contDiff_const (𝕜 := 𝕜) (n := r) (E := E)
            (c := (0 : ModelForm (𝕜 := 𝕜) (E := E) F n))).contDiffOn }

instance : CoeFun (DifferentialForm (I := I) (M := M) F n r)
    (fun _ ↦ (x : M) → FormAt (I := I) (M := M) F n x) where
  coe form := form.toFun

/--
%%handwave
name:
  Extensionality of differential forms
statement:
  Two \(C^r\) differential forms are equal if their alternating covectors agree
  at every point of the manifold.
proof:
  A bundled differential form is determined by its pointwise covector field;
  its regularity proof carries no additional data.
-/
@[ext]
theorem ext {omegaForm eta : DifferentialForm (I := I) (M := M) F n r}
    (h : ∀ x, omegaForm.toFun x = eta.toFun x) : omegaForm = eta := by
  cases omegaForm
  cases eta
  congr
  funext x
  exact h x

/-- Lower the recorded regularity of a differential form. -/
def of_le {r r' : WithTop ℕ∞} (hrr' : r ≤ r')
    (form : DifferentialForm (I := I) (M := M) F n r') :
    DifferentialForm (I := I) (M := M) F n r where
  toFun := form.toFun
  isContMDiff := by
    intro e he
    exact (form.isContMDiff e he).of_le hrr'

/-- Regard a differential form of any regularity as a continuous form. -/
def toContinuous (form : DifferentialForm (I := I) (M := M) F n r) :
    DifferentialForm (I := I) (M := M) F n (0 : WithTop ℕ∞) :=
  of_le (I := I) (M := M) (F := F) (n := n) zero_le form

/--
%%handwave
name:
  Underlying form after lowering regularity
statement:
  Regarding a \(C^{r'}\) differential form as \(C^r\), for \(r\le r'\), does
  not change its pointwise alternating covectors.
proof:
  Lowering the asserted regularity leaves the underlying pointwise form
  unchanged by definition.
-/
@[simp]
theorem of_le_toFun {r r' : WithTop ℕ∞} (hrr' : r ≤ r')
    (form : DifferentialForm (I := I) (M := M) F n r') :
    (of_le (I := I) (M := M) (F := F) (n := n) hrr' form).toFun = form.toFun :=
  rfl

/--
%%handwave
name:
  Underlying form after forgetting to continuity
statement:
  Regarding a differential form of arbitrary regularity as merely continuous
  does not change its pointwise alternating covectors.
proof:
  Passing to continuity leaves the underlying pointwise form unchanged by
  definition.
-/
@[simp]
theorem toContinuous_toFun
    (form : DifferentialForm (I := I) (M := M) F n r) :
    (form.toContinuous (I := I) (M := M) (F := F) (n := n)).toFun = form.toFun :=
  rfl

/--
%%handwave
name:
  Continuity of evaluating a continuous alternating form field
statement:
  Let \(\omega_x\) be a continuous field of \(n\)-linear alternating forms on
  a set \(s\), and let \(v_0,\ldots,v_{n-1}\) be continuous vector fields on
  \(s\).  Then \(x\mapsto\omega_x(v_0(x),\ldots,v_{n-1}(x))\) is continuous
  on \(s\).
proof:
  Assemble the vector fields into a continuous map to the finite product and
  compose with the continuous evaluation map.
-/
theorem continuousOn_modelForm_eval
    {α : Type*} [TopologicalSpace α] {s : Set α}
    {omega : α → ModelForm (𝕜 := 𝕜) (E := E) F n}
    {v : Fin n → α → E}
    (homega : ContinuousOn omega s)
    (hv : ∀ i, ContinuousOn (v i) s) :
    ContinuousOn (fun x ↦ omega x (fun i ↦ v i x)) s := by
  have hv' : ContinuousOn (fun x ↦ fun i ↦ v i x) s :=
    continuousOn_pi.2 hv
  simpa using (continuous_eval.comp_continuousOn (homega.prodMk hv'))

/--
%%handwave
name:
  Evaluation of a differential form in tangent-bundle coordinates
statement:
  If \(z\) lies in a chart centered at \(x_0\), then for tangent vectors
  \(v_0,\ldots,v_{n-1}\in T_zM\),
  \[
    \omega_z(v_0,\ldots,v_{n-1})
    =\omega_e(e(z))\bigl([v_0]_e,\ldots,[v_{n-1}]_e\bigr),
  \]
  where \([v_i]_e\) are their coordinates in the induced tangent
  trivialization.
proof:
  The inverse of the tangent trivialization converts each coordinate vector
  back to \(v_i\); substituting this identity in the definition of the
  coordinate representative gives the formula.
-/
theorem eval_eq_coordinateExpression_chartAt
    [IsManifold I 1 M]
    (form : (x : M) → FormAt (I := I) F n x)
    {x₀ z : M} (hz : z ∈ (chartAt H x₀).source)
    (v : Fin n → TangentSpace I z) :
    form z v =
      coordinateExpression (I := I) (F := F) (n := n) form (chartAt H x₀)
        ((extChartAt I x₀) z)
        (fun i ↦
          (trivializationAt E (TangentSpace I) x₀
            (⟨z, v i⟩ : TangentBundle I M)).2) := by
  have hsource : z ∈ (extChartAt I x₀).source := by
    simpa [extChartAt_source] using hz
  have hbase :
      z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet] using hz
  have hpoint :
      ((chartAt H x₀).extend I).symm ((extChartAt I x₀) z) = z := by
    change (extChartAt I x₀).symm ((extChartAt I x₀) z) = z
    exact (extChartAt I x₀).left_inv hsource
  have htarget_range :
      mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (extChartAt I x₀).target ((extChartAt I x₀) z) =
        mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (range I) ((extChartAt I x₀) z) :=
    mfderivWithin_congr_set (I := 𝓘(𝕜, E)) (I' := I)
      (f := (extChartAt I x₀).symm) (x := (extChartAt I x₀) z)
      (extChartAt_target_eventuallyEq' (I := I) hsource)
  have hsymm :
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 z =
        mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (range I) ((extChartAt I x₀) z) :=
    TangentBundle.symmL_trivializationAt (I := I) hz
  rw [coordinateExpression, hpoint]
  change form z v =
    ((form z).compContinuousLinearMap
      (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (extChartAt I x₀).target ((extChartAt I x₀) z)))
      (fun i ↦
        (trivializationAt E (TangentSpace I) x₀
          (⟨z, v i⟩ : TangentBundle I M)).2)
  rw [htarget_range, ← hsymm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr
  funext i
  let T := trivializationAt E (TangentSpace I) x₀
  symm
  change T.symmL 𝕜 z ((T (⟨z, v i⟩ : TangentBundle I M)).2) = v i
  have hcoord :
      T.linearMapAt 𝕜 z (v i) =
        (T (⟨z, v i⟩ : TangentBundle I M)).2 :=
    congrFun (T.coe_linearMapAt_of_mem (R := 𝕜) hbase) (v i)
  rw [← hcoord]
  exact T.symmₗ_linearMapAt (R := 𝕜) hbase (v i)

/--
%%handwave
name:
  Continuity of a differential form evaluated on tangent fields
statement:
  Let \(\omega\) be a continuous differential \(n\)-form, let
  \(\phi:s\to M\) be continuous, and let \(V_i(x)\in T_{\phi(x)}M\) be
  continuous tangent-vector fields along \(\phi\).  Then
  \[
    x\longmapsto\omega_{\phi(x)}(V_0(x),\ldots,V_{n-1}(x))
  \]
  is continuous on \(s\).
proof:
  Work locally in a chart around each \(\phi(x)\).  The coordinate
  representative of \(\omega\) and the tangent coordinates of all \(V_i\)
  are continuous, so continuity follows from continuous evaluation and then
  glues over the domain.
-/
theorem continuousOn_eval_continuous_tangentFields
    [IsManifold I 1 M]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    {n : ℕ}
    (form : DifferentialForm (I := I) (M := M) F n (0 : WithTop ℕ∞))
    {φ : E₀ → M} {s : Set E₀}
    (_hφ : ContinuousOn φ s)
    (V : (i : Fin n) → (x : E₀) → TangentSpace I (φ x))
    (_hV : ∀ i,
      ContinuousOn (fun x ↦ (⟨φ x, V i x⟩ : TangentBundle I M)) s) :
    ContinuousOn (fun x ↦ form.toFun (φ x) (fun i ↦ V i x)) s := by
  intro a ha
  let e : OpenPartialHomeomorph M H := chartAt H (φ a)
  let T := trivializationAt E (TangentSpace I) (φ a)
  let U : Set E₀ := φ ⁻¹' e.source
  have haU : a ∈ U := by
    simp [U, e]
  have hU_mem : U ∈ 𝓝[s] a :=
    (_hφ a ha).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds (by simp [e]))
  have hlocal :
      ContinuousWithinAt
        (fun x ↦ form.toFun (φ x) (fun i ↦ V i x)) (s ∩ U) a := by
    have hae : a ∈ s ∩ U := ⟨ha, haU⟩
    have hcoord :
        ContinuousOn (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          (e.extend I).target :=
      (form.isContMDiff e (by simp [e])).continuousOn
    have hchart :
        ContinuousOn (fun x ↦ (e.extend I) (φ x)) (s ∩ U) := by
      exact (e.continuousOn_extend (I := I)).comp (_hφ.mono inter_subset_left) (by
        intro x hx
        simpa [U, e.extend_source (I := I)] using hx.2)
    have hcoord_comp :
        ContinuousOn
          (fun x ↦ coordinateExpression (I := I) (F := F) (n := n) form.toFun e
            ((e.extend I) (φ x))) (s ∩ U) := by
      exact hcoord.comp hchart (by
        intro x hx
        exact (e.extend I).map_source (by
          simpa [U, e.extend_source (I := I)] using hx.2))
    have hvec :
        ∀ i, ContinuousOn
          (fun x ↦ (T (⟨φ x, V i x⟩ : TangentBundle I M)).2) (s ∩ U) := by
      intro i
      have hT :
          ContinuousOn (fun x ↦ T (⟨φ x, V i x⟩ : TangentBundle I M)) (s ∩ U) := by
        exact T.continuousOn.comp ((_hV i).mono inter_subset_left) (by
          intro x hx
          exact T.mem_source.mpr (by
            simpa [T, U, e, TangentBundle.trivializationAt_baseSet] using hx.2))
      exact hT.snd
    have hmodel :
        ContinuousOn
          (fun x ↦
            coordinateExpression (I := I) (F := F) (n := n) form.toFun e
              ((e.extend I) (φ x))
              (fun i ↦ (T (⟨φ x, V i x⟩ : TangentBundle I M)).2))
          (s ∩ U) :=
      continuousOn_modelForm_eval (𝕜 := 𝕜) (E := E) (F := F) (n := n)
        hcoord_comp hvec
    have heq : EqOn
        (fun x ↦ form.toFun (φ x) (fun i ↦ V i x))
        (fun x ↦
          coordinateExpression (I := I) (F := F) (n := n) form.toFun e
            ((e.extend I) (φ x))
            (fun i ↦ (T (⟨φ x, V i x⟩ : TangentBundle I M)).2))
        (s ∩ U) := by
      intro x hx
      simpa [e, T, U] using
        eval_eq_coordinateExpression_chartAt (I := I) (F := F) (n := n)
          (form := form.toFun) (x₀ := φ a) (z := φ x) hx.2 (fun i ↦ V i x)
    exact (hmodel.congr heq).continuousWithinAt hae
  exact hlocal.mono_of_mem_nhdsWithin
    (Filter.inter_mem self_mem_nhdsWithin hU_mem)

/--
%%handwave
name:
  Continuity of a constant tangent vector field on a vector space
statement:
  For a normed vector space \(E\) and fixed \(v\in E\), the tangent-bundle
  section \(x\mapsto(x,v)\in TE\) is continuous on every subset of \(E\).
proof:
  Under the canonical trivialization \(TE\cong E\times E\), this is the product
  of the identity map with the constant map \(v\).
-/
theorem continuousOn_constTangentVector_modelSpace
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    {s : Set E₀} (v : E₀) :
    ContinuousOn
      (fun x : E₀ ↦
        (⟨x, (v : TangentSpace 𝓘(𝕜, E₀) x)⟩ :
          TangentBundle 𝓘(𝕜, E₀) E₀)) s := by
  rw [← (tangentBundleModelSpaceHomeomorph (𝓘(𝕜, E₀))).comp_continuousOn_iff]
  simpa using (continuous_id.continuousOn.prodMk continuousOn_const :
    ContinuousOn (fun x : E₀ ↦ (x, v)) s)

/--
%%handwave
name:
  Continuity of a differential form evaluated on a derivative
statement:
  Let \(\omega\) be a continuous differential \(n\)-form, let
  \(\phi:s\to M\) be \(C^1\), and assume \(s\) is a
  unique-differentiability set.  For fixed \(v_0,\ldots,v_{n-1}\) in the
  parameter space, the function
  \[
    x\longmapsto
    \omega_{\phi(x)}(D\phi_xv_0,\ldots,D\phi_xv_{n-1})
  \]
  is continuous on \(s\).
proof:
  The tangent map of \(\phi\) sends each constant tangent field \(v_i\) to a
  continuous tangent field along \(\phi\).  Apply continuity of evaluating a
  continuous form on continuous tangent fields.
-/
theorem continuousOn_eval_comp_mfderivWithin
    [IsManifold I 1 M]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    {n : ℕ} {rφ : WithTop ℕ∞}
    (form : DifferentialForm (I := I) (M := M) F n (0 : WithTop ℕ∞))
    {φ : E₀ → M} {s : Set E₀}
    (_hφ : ContMDiffOn 𝓘(𝕜, E₀) I rφ φ s)
    (_hrφ : (1 : WithTop ℕ∞) ≤ rφ)
    (_hs : UniqueDiffOn 𝕜 s)
    (v : Fin n → E₀) :
    ContinuousOn
      (fun x ↦
        ((form.toFun (φ x)).compContinuousLinearMap
          (mfderivWithin 𝓘(𝕜, E₀) I φ s x)) v) s := by
  let V : (i : Fin n) → (x : E₀) → TangentSpace I (φ x) :=
    fun i x ↦ (mfderivWithin 𝓘(𝕜, E₀) I φ s x) (v i)
  have hV : ∀ i,
      ContinuousOn (fun x ↦ (⟨φ x, V i x⟩ : TangentBundle I M)) s := by
    intro i
    have htangent :=
      _hφ.continuousOn_tangentMapWithin _hrφ _hs.uniqueMDiffOn
    have hconst :=
      continuousOn_constTangentVector_modelSpace (𝕜 := 𝕜) (s := s) (v := v i)
    have hcomp := htangent.comp hconst (by
      intro x hx
      simpa using hx)
    simpa [V] using hcomp
  simpa [V] using
    continuousOn_eval_continuous_tangentFields
      (I := I) (M := M) (F := F) (form := form)
      _hφ.continuousOn V hV

end DifferentialForm

/-- Smooth differential forms are `C^∞` forms. -/
abbrev SmoothDifferentialForm
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) :=
  DifferentialForm (I := I) (M := M) (F := F) (n := n) (r := ∞)

/--
%%handwave
name:
  Analytic differential form
statement:
  An analytic differential form is a pointwise alternating covector field whose
  coordinate representatives are analytic.
-/
abbrev AnalyticDifferentialForm
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) :=
  DifferentialForm (I := I) (M := M) (F := F) (n := n) (r := ω)

def exteriorDerivativePoint
    [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ} {r : WithTop ℕ∞}
    (form : DifferentialForm (I := I) (M := M) F n (r + 1)) (x : M) :
    FormAt (I := I) (M := M) F (n + 1) x :=
  (extDerivWithin
      (coordinateExpression (I := I) (F := F) (n := n) form.toFun (chartAt H x))
      (extChartAt I x).target ((extChartAt I x) x)).compContinuousLinearMap
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x)

/--
%%handwave
name:
  Coordinate expression of the pointwise exterior derivative
statement:
  Let \(\omega\) be a \(C^{r+1}\) differential \(n\)-form on a smooth
  manifold.  In every chart \(e\) and at every point \(y\) of its extended
  target,
  \[
    (d\omega)_e(y)=d\bigl(\omega_e\bigr)(y),
  \]
  where the derivative on the right is computed relative to the chart target.
proof:
  Compare the chart \(e\) with the chart centered at the underlying point.
  Use the coordinate transformation law for \(\omega\), naturality of the
  exterior derivative under the transition map, and the chain rule for the
  inverse-chart derivatives.
-/
theorem coordinateExpression_exteriorDerivativePoint
    [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ} {r : WithTop ℕ∞}
    (form : DifferentialForm (I := I) (M := M) F n (r + 1))
    {e : OpenPartialHomeomorph M H} {y : E}
    (he : e ∈ atlas H M) (hy : y ∈ (e.extend I).target) :
    coordinateExpression (I := I) (F := F) (n := n + 1)
      (exteriorDerivativePoint (I := I) form) e y =
      extDerivWithin
        (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
        (e.extend I).target y := by
  set x : M := (e.extend I).symm y
  set e' : OpenPartialHomeomorph M H := chartAt H x
  set φ := I.extendCoordChange e e'
  have hx_source : x ∈ (e.extend I).source := by
    simpa [x] using (e.extend I).map_target hy
  have hx_e_source : x ∈ e.source := by
    simpa [e.extend_source (I := I)] using hx_source
  have hy_eq : e.extend I x = y := by
    simpa [x] using (e.extend I).right_inv hy
  have hx_chart_source : x ∈ e'.source := by
    simp [e']
  have hyφ : y ∈ φ.source := by
    change y ∈ (e.extend I).target ∧ (e.extend I).symm y ∈ (e'.extend I).source
    refine ⟨hy, ?_⟩
    simp [e', x]
  have he' : e' ∈ atlas H M := by
    simp [e']
  have hφy_target : φ y ∈ (e'.extend I).target := by
    have htarget : φ.target ⊆ (e'.extend I).target := by
      intro z hz
      simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_target] using hz.1
    exact htarget (φ.map_source hyφ)
  have hpoint : (e'.extend I).symm (φ y) = x := by
    change (e'.extend I).symm (φ y) = (e.extend I).symm y
    exact extendCoordChange_symm_apply (I := I) (e := e) (e' := e') hyφ
  have hφy_eq : (extChartAt I x) x = φ y := by
    change (e'.extend I) x = φ y
    rw [show φ y = e'.extend I ((e.extend I).symm y) from rfl]
  have hderiv :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y =
        (mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y)).comp
          (fderivWithin 𝕜 φ φ.source y) := by
    simpa [φ] using
      mfderivWithin_extend_symm_coordChange (I := I) (e := e) (e' := e') he he' hyφ
  have hleft_deriv :
      (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x).comp
          (mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y) =
        fderivWithin 𝕜 φ φ.source y := by
    have hφy_ext_target : φ y ∈ (extChartAt I x).target := by
      simpa [e', extChartAt] using hφy_target
    have hpoint_ext : (extChartAt I x).symm (φ y) = x := by
      simpa [e', extChartAt] using hpoint
    have hB_range :
        mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y) =
          mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (φ y) := by
      simpa [e', extChartAt] using
        (mfderivWithin_congr_set (I := 𝓘(𝕜, E)) (I' := I)
          (f := (extChartAt I x).symm) (x := φ y)
          (extChartAt_target_eventuallyEq_of_mem (I := I) hφy_ext_target))
    have hcomp_id :
        (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x).comp
          (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (φ y)) =
            ContinuousLinearMap.id 𝕜 E := by
      have hraw :=
        mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I)
          (x := x) hφy_ext_target
      rw [hpoint_ext] at hraw
      simpa using hraw
    rw [hderiv, hB_range]
    ext v
    simpa using congrArg
      (fun L : E →L[𝕜] E => L ((fderivWithin 𝕜 φ φ.source y) v)) hcomp_id
  have hφ_source_subset_target : φ.source ⊆ (e.extend I).target := by
    intro z hz
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hz.1
  have hφ_source_mem_target : φ.source ∈ 𝓝[(e.extend I).target] y := by
    have hsource_range : φ.source ∈ 𝓝[range I] y :=
      I.extendCoordChange_source_mem_nhdsWithin (e := e) (e' := e') hyφ
    have h_eq : 𝓝[(e.extend I).target] y = 𝓝[range I] y :=
      nhdsWithin_extend_target_eq_of_mem (I := I) hy
    exact h_eq.symm ▸ hsource_range
  have hCE_diff_source :
      DifferentiableWithinAt 𝕜
        (coordinateExpression (I := I) (F := F) (n := n) form.toFun e) φ.source y := by
    exact ((form.isContMDiff e he y hy).differentiableWithinAt (by simp)).mono
      hφ_source_subset_target
  have hderiv_set :
      fderivWithin 𝕜
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          (e.extend I).target y =
        fderivWithin 𝕜
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          φ.source y :=
    fderivWithin_of_mem_nhdsWithin hφ_source_mem_target
      ((uniqueDiffOn_extend_target (I := I) e) y hy) hCE_diff_source
  have hset :
      extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          (e.extend I).target y =
        extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          φ.source y := by
    rw [extDerivWithin, extDerivWithin, hderiv_set]
  have hCE_eq :
      EqOn
        (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
        (fun z =>
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e' (φ z)).compContinuousLinearMap
            (fderivWithin 𝕜 φ φ.source z))
        φ.source := by
    intro z hz
    simpa [φ] using
      coordinateExpression_coordChange (I := I) (F := F) (n := n) form.toFun he he' hz
  have hcongr :
      extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          φ.source y =
        extDerivWithin
          (fun z =>
            (coordinateExpression (I := I) (F := F) (n := n) form.toFun e' (φ z)).compContinuousLinearMap
              (fderivWithin 𝕜 φ φ.source z))
          φ.source y :=
    extDerivWithin_congr' hCE_eq hyφ
  have hωdiff :
      DifferentiableWithinAt 𝕜
        (coordinateExpression (I := I) (F := F) (n := n) form.toFun e')
        (e'.extend I).target (φ y) :=
    (form.isContMDiff e' he' (φ y) hφy_target).differentiableWithinAt (by simp)
  have hφ_contdiff :
      ContDiffWithinAt 𝕜 ∞ φ φ.source y := by
    have hφ_contdiff_on : ContDiffOn 𝕜 ∞ φ φ.source :=
      I.contDiffOn_extendCoordChange
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) he)
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) he')
    exact hφ_contdiff_on y hyφ
  have hmin : minSmoothness 𝕜 2 ≤ (∞ : WithTop ℕ∞) := by
    simpa [minSmoothness] using
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from by
        exact_mod_cast (show (2 : ℕ) ≤ (⊤ : ℕ∞) from le_top))
  have hmaps : MapsTo φ φ.source (e'.extend I).target := by
    intro z hz
    have htarget : φ.target ⊆ (e'.extend I).target := by
      intro w hw
      simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_target] using hw.1
    exact htarget (φ.mapsTo hz)
  have hpullback :
      extDerivWithin
          (fun z =>
            (coordinateExpression (I := I) (F := F) (n := n) form.toFun e' (φ z)).compContinuousLinearMap
              (fderivWithin 𝕜 φ φ.source z))
          φ.source y =
        (extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e')
          (e'.extend I).target (φ y)).compContinuousLinearMap
            (fderivWithin 𝕜 φ φ.source y) :=
    extDerivWithin_pullback (x := y) (f := φ) (t := (e'.extend I).target)
      hωdiff hφ_contdiff hmin
      (I.uniqueDiffOn_extendCoordChange_source (e := e) (e' := e'))
      (extendCoordChange_source_subset_closure_interior (I := I) e e' hyφ) hyφ hmaps
  calc
    coordinateExpression (I := I) (F := F) (n := n + 1)
        (exteriorDerivativePoint (I := I) form) e y =
      (extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e')
          (e'.extend I).target (φ y)).compContinuousLinearMap
            (fderivWithin 𝕜 φ φ.source y) := by
        rw [coordinateExpression, exteriorDerivativePoint]
        change
          ((extDerivWithin
              (coordinateExpression (I := I) (F := F) (n := n) form.toFun e')
              (e'.extend I).target (φ y)).compContinuousLinearMap
              (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x)).compContinuousLinearMap
            (mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y) =
          (extDerivWithin
              (coordinateExpression (I := I) (F := F) (n := n) form.toFun e')
              (e'.extend I).target (φ y)).compContinuousLinearMap
            (fderivWithin 𝕜 φ φ.source y)
        ext v
        simpa using congrArg
          (fun L : E →L[𝕜] E =>
            (extDerivWithin
              (coordinateExpression (I := I) (F := F) (n := n) form.toFun e')
              (e'.extend I).target (φ y)).compContinuousLinearMap L v)
          hleft_deriv
    _ =
      extDerivWithin
        (fun z =>
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e' (φ z)).compContinuousLinearMap
            (fderivWithin 𝕜 φ φ.source z))
        φ.source y := hpullback.symm
    _ =
      extDerivWithin
        (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
        φ.source y := hcongr.symm
    _ =
      extDerivWithin
        (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
        (e.extend I).target y := hset.symm

/--
%%handwave
name:
  Coordinate expression in a chart at its center
statement:
  For a pointwise \(n\)-form \(\omega\) and \(x\in M\), the coordinate
  representative in the chart centered at \(x\), evaluated at the coordinate
  point of \(x\), is exactly \(\omega_x\).
proof:
  The derivative of the inverse extended chart at the coordinate point of
  \(x\) is the inverse of the chart derivative, so their composition is the
  identity on \(T_xM\).
-/
theorem coordinateExpression_chartAt_self
    [IsManifold I 1 M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (form : (x : M) → FormAt (I := I) (M := M) F n x) (x : M) :
    coordinateExpression (I := I) (F := F) (n := n) form (chartAt H x)
      ((extChartAt I x) x) = form x := by
  rw [coordinateExpression]
  have hset :
      mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (extChartAt I x).target
          ((extChartAt I x) x) =
        mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I)
          ((extChartAt I x) x) := by
    exact mfderivWithin_congr_set
      (extChartAt_target_eventuallyEq (I := I) (x := x))
  rw [show (chartAt H x).extend I = extChartAt I x from rfl]
  rw [hset, mfderivWithin_range_extChartAt_symm (I := I), extChartAt_to_inv]
  ext v
  rfl

/--
%%handwave
name:
  Exterior derivative
statement:
  The exterior derivative sends a \(C^{r+1}\) degree \(n\) differential form
  to a \(C^r\) degree \(n+1\) differential form and is computed in coordinates
  by the usual alternating derivative.
-/
def exteriorDerivative
    [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ} {r : WithTop ℕ∞}
    (form : DifferentialForm (I := I) (M := M) F n (r + 1)) :
    DifferentialForm (I := I) (M := M) F (n + 1) r where
  toFun := exteriorDerivativePoint (I := I) form
  isContMDiff := by
    intro e he
    exact
      (contDiffOn_extDerivWithin (F := F) (n := n)
        (form.isContMDiff e he) (uniqueDiffOn_extend_target (I := I) e)).congr
        fun y hy => coordinateExpression_exteriorDerivativePoint (I := I) (r := r) form he hy

/--
%%handwave
name:
  The second exterior derivative vanishes
statement:
  On a real or complex smooth manifold, applying the exterior derivative twice
  to a smooth differential form gives the zero form, \(d(d\omega)=0\).
proof:
  In every coordinate chart, this is the [identity that the second exterior derivative of a sufficiently smooth model-space form is zero](lean:extDeriv_extDeriv).  The pullback compatibility of the model-space exterior derivative transports the identity between charts.
tags:
  milestone
-/
theorem exteriorDerivative_exteriorDerivative_eq_zero
    [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (form : SmoothDifferentialForm (I := I) (M := M) F n) :
    (exteriorDerivative (I := I) (r := ∞)
      (exteriorDerivative (I := I) (r := ∞) form) :
        SmoothDifferentialForm (I := I) (M := M) F (n + 2)) = 0 := by
  apply DifferentialForm.ext
  intro x
  let e : OpenPartialHomeomorph M H := chartAt H x
  let y : E := (extChartAt I x) x
  have he : e ∈ atlas H M := by
    simp [e]
  have hy : y ∈ (e.extend I).target := by
    simp [e, y, extChartAt]
  have hη_eq_on :
      EqOn
        (coordinateExpression (I := I) (F := F) (n := n + 1)
          (exteriorDerivative (I := I) (r := ∞) form).toFun e)
        (extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          (e.extend I).target)
        (e.extend I).target := by
    intro z hz
    exact coordinateExpression_exteriorDerivativePoint (I := I) (r := ∞) form he hz
  have houter :
      coordinateExpression (I := I) (F := F) (n := n + 2)
        (exteriorDerivative (I := I) (r := ∞)
          (exteriorDerivative (I := I) (r := ∞) form)).toFun e y =
      extDerivWithin
        (coordinateExpression (I := I) (F := F) (n := n + 1)
          (exteriorDerivative (I := I) (r := ∞) form).toFun e)
        (e.extend I).target y :=
    coordinateExpression_exteriorDerivativePoint (I := I)
      (r := ∞) (exteriorDerivative (I := I) (r := ∞) form) he hy
  have hcongr :
      extDerivWithin
        (coordinateExpression (I := I) (F := F) (n := n + 1)
          (exteriorDerivative (I := I) (r := ∞) form).toFun e)
        (e.extend I).target y =
      extDerivWithin
        (extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          (e.extend I).target)
        (e.extend I).target y :=
    extDerivWithin_congr' hη_eq_on hy
  have hmin : minSmoothness 𝕜 2 ≤ (∞ : WithTop ℕ∞) := by
    simpa [minSmoothness] using
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from by
        exact_mod_cast (show (2 : ℕ) ≤ (⊤ : ℕ∞) from le_top))
  have hclosure : y ∈ closure (interior (e.extend I).target) := by
    simpa [e, y, extChartAt] using
      extChartAt_target_subset_closure_interior (I := I) (x := x)
        (mem_extChartAt_target (I := I) x)
  have hd2_model :
      extDerivWithin
        (extDerivWithin
          (coordinateExpression (I := I) (F := F) (n := n) form.toFun e)
          (e.extend I).target)
        (e.extend I).target y = 0 := by
    have hd2_eqOn :=
      extDerivWithin_extDerivWithin_eqOn
        (form.isContMDiff e he) hmin (uniqueDiffOn_extend_target (I := I) e)
    exact hd2_eqOn ⟨hy, hclosure⟩
  have hcoord_zero :
      coordinateExpression (I := I) (F := F) (n := n + 2)
        (exteriorDerivative (I := I) (r := ∞)
          (exteriorDerivative (I := I) (r := ∞) form)).toFun e y = 0 := by
    rw [houter, hcongr, hd2_model]
  have hself :=
    coordinateExpression_chartAt_self (I := I)
      (F := F) (n := n + 2)
      (exteriorDerivative (I := I) (r := ∞)
        (exteriorDerivative (I := I) (r := ∞) form)).toFun x
  simpa [e, y] using hself.symm.trans hcoord_zero

section DiffeomorphismPullback

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H₁ : Type*} [TopologicalSpace H₁]
variable {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable {H₂ : Type*} [TopologicalSpace H₂]
variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]

/--
%%handwave
name:
  Smoothness of a diffeomorphism in two fixed charts
statement:
  On any part of a source coordinate chart whose image lies in a target
  chart, the coordinate expression of a smooth diffeomorphism is smooth.
proof:
  The inverse source chart, the diffeomorphism, and the target chart are smooth,
  and smoothness is preserved under composition.
-/
theorem contDiffOn_diffeomorphChartMap_local
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂)
    (e₁ : OpenPartialHomeomorph M₁ H₁) (he₁ : e₁ ∈ atlas H₁ M₁)
    (e₂ : OpenPartialHomeomorph M₂ H₂) (he₂ : e₂ ∈ atlas H₂ M₂)
    {u : Set E₁}
    (hmaps :
      MapsTo
        (fun y ↦ φ ((e₁.extend I₁).symm y))
        ((e₁.extend I₁).target ∩ u)
        e₂.source) :
    ContDiffOn ℝ ∞
      (fun y ↦ (e₂.extend I₂) (φ ((e₁.extend I₁).symm y)))
      ((e₁.extend I₁).target ∩ u) := by
  have he₁max : e₁ ∈ IsManifold.maximalAtlas I₁ ∞ M₁ :=
    IsManifold.subset_maximalAtlas (I := I₁) (n := ∞) he₁
  have he₂max : e₂ ∈ IsManifold.maximalAtlas I₂ ∞ M₂ :=
    IsManifold.subset_maximalAtlas (I := I₂) (n := ∞) he₂
  have hsymm :
      ContMDiffOn 𝓘(ℝ, E₁) I₁ ∞
        (e₁.extend I₁).symm (e₁.extend I₁).target := by
    rw [OpenPartialHomeomorph.extend_target']
    exact contMDiffOn_extend_symm (I := I₁) (e := e₁) he₁max
  have hφ :
      ContMDiffOn I₁ I₂ ∞ (φ : M₁ → M₂) Set.univ :=
    φ.contMDiff.contMDiffOn
  have hφ_chart :
      ContMDiffOn 𝓘(ℝ, E₁) I₂ ∞
        (fun y ↦ φ ((e₁.extend I₁).symm y))
        ((e₁.extend I₁).target ∩ u) := by
    simpa [Function.comp_def] using
      hφ.comp (hsymm.mono inter_subset_left)
        (by
          intro y _hy
          simp)
  have hext :
      ContMDiffOn I₂ 𝓘(ℝ, E₂) ∞ (e₂.extend I₂) e₂.source :=
    contMDiffOn_extend (I := I₂) (e := e₂) he₂max
  have hcomp :
      ContMDiffOn 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞
        ((e₂.extend I₂) ∘ fun y ↦ φ ((e₁.extend I₁).symm y))
        ((e₁.extend I₁).target ∩ u) :=
    hext.comp hφ_chart hmaps
  exact (contMDiffOn_iff_contDiffOn.mp hcomp).congr (fun _ _ ↦ rfl)

/--
%%handwave
name:
  Target chart source is a source-chart neighborhood
statement:
  The preimage of the target chart around the image point is a neighborhood in
  the source coordinate chart.
proof:
  The source chart inverse followed by the diffeomorphism is continuous, and
  the target chart source is an open neighborhood of the image point.
-/
theorem diffeomorph_targetChart_source_mem_nhdsWithin
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂)
    (e₁ : OpenPartialHomeomorph M₁ H₁) (he₁ : e₁ ∈ atlas H₁ M₁)
    {y : E₁} (hy : y ∈ (e₁.extend I₁).target) :
    (fun z ↦ φ ((e₁.extend I₁).symm z)) ⁻¹'
        (chartAt H₂ (φ ((e₁.extend I₁).symm y))).source ∈
      𝓝[(e₁.extend I₁).target] y := by
  have he₁max : e₁ ∈ IsManifold.maximalAtlas I₁ ∞ M₁ :=
    IsManifold.subset_maximalAtlas (I := I₁) (n := ∞) he₁
  have hsymm :
      ContMDiffOn 𝓘(ℝ, E₁) I₁ ∞
        (e₁.extend I₁).symm (e₁.extend I₁).target := by
    rw [OpenPartialHomeomorph.extend_target']
    exact contMDiffOn_extend_symm (I := I₁) (e := e₁) he₁max
  have hφ :
      ContMDiffOn I₁ I₂ ∞ (φ : M₁ → M₂) Set.univ :=
    φ.contMDiff.contMDiffOn
  have hφ_chart :
      ContMDiffOn 𝓘(ℝ, E₁) I₂ ∞
        (fun z ↦ φ ((e₁.extend I₁).symm z))
        (e₁.extend I₁).target := by
    simpa [Function.comp_def] using
      hφ.comp hsymm
        (by
          intro z _hz
          simp)
  have hcont :
      ContinuousWithinAt
        (fun z ↦ φ ((e₁.extend I₁).symm z))
        (e₁.extend I₁).target y :=
    (hφ_chart y hy).continuousWithinAt
  exact hcont.preimage_mem_nhdsWithin
    ((chartAt H₂ (φ ((e₁.extend I₁).symm y))).open_source.mem_nhds (by simp))

/--
%%handwave
name:
  Coordinate formula for pullback by a diffeomorphism
statement:
  In a localized pair of source and target charts, the coordinate
  representative of the pullback form is the target coordinate representative
  pulled back by the derivative of the coordinate expression of the
  diffeomorphism.
proof:
  Expand both coordinate representatives.  The derivative of the coordinate
  expression of the diffeomorphism is the derivative of the target chart,
  followed by the manifold derivative of the diffeomorphism, followed by the
  derivative of the inverse source chart; the target-chart inverse derivative
  cancels the target-chart derivative.
-/
theorem coordinateExpression_smoothDifferentialFormPullbackDiffeomorph_eqOn_local
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothDifferentialForm (I := I₂) (M := M₂) ℝ n)
    (e₁ : OpenPartialHomeomorph M₁ H₁) (he₁ : e₁ ∈ atlas H₁ M₁)
    (e₂ : OpenPartialHomeomorph M₂ H₂) (he₂ : e₂ ∈ atlas H₂ M₂)
    {u : Set E₁}
    (hu : IsOpen u)
    (hmaps :
      MapsTo
        (fun y ↦ φ ((e₁.extend I₁).symm y))
        ((e₁.extend I₁).target ∩ u)
        e₂.source) :
    EqOn
      (coordinateExpression (I := I₁) (F := ℝ) (n := n)
        (fun x ↦
          (omega.toFun (φ x)).compContinuousLinearMap
            (mfderiv I₁ I₂ φ x)) e₁)
      (fun y ↦
        (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂
          ((e₂.extend I₂) (φ ((e₁.extend I₁).symm y)))).compContinuousLinearMap
          (fderivWithin ℝ
            (fun z ↦ (e₂.extend I₂) (φ ((e₁.extend I₁).symm z)))
            ((e₁.extend I₁).target ∩ u) y))
      ((e₁.extend I₁).target ∩ u) := by
  intro y hy
  let s : Set E₁ := (e₁.extend I₁).target ∩ u
  let x : M₁ := (e₁.extend I₁).symm y
  let q : M₂ := φ x
  let f : E₁ → M₂ := fun z ↦ φ ((e₁.extend I₁).symm z)
  let ψ : E₁ → E₂ := fun z ↦ (e₂.extend I₂) (f z)
  have hy_target : y ∈ (e₁.extend I₁).target := hy.1
  have hx_ext_source : x ∈ (e₁.extend I₁).source :=
    (e₁.extend I₁).map_target hy_target
  have hx_source : x ∈ e₁.source := by
    simpa [x, e₁.extend_source (I := I₁)] using hx_ext_source
  have hq_source : q ∈ e₂.source := by
    simpa [q, f, x, s] using hmaps hy
  have hq_ext_source : q ∈ (e₂.extend I₂).source := by
    simpa [e₂.extend_source (I := I₂)] using hq_source
  have hpoint :
      (e₂.extend I₂).symm ((e₂.extend I₂) q) = q :=
    (e₂.extend I₂).left_inv hq_ext_source
  have hs_unique : UniqueMDiffWithinAt 𝓘(ℝ, E₁) s y :=
    (((uniqueDiffOn_extend_target (I := I₁) e₁).inter hu) y hy).uniqueMDiffWithinAt
  have htarget_mem : (e₁.extend I₁).target ∈ 𝓝[s] y :=
    Filter.mem_of_superset self_mem_nhdsWithin inter_subset_left
  have hsymm_target :
      MDifferentiableWithinAt 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
        (e₁.extend I₁).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I₁) he₁ hy_target
  have hsymm_s :
      MDifferentiableWithinAt 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm s y :=
    hsymm_target.mono inter_subset_left
  have hsymm_deriv_s :
      mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm s y =
        mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
          (e₁.extend I₁).target y :=
    hsymm_target.mfderivWithin_mono_of_mem_nhdsWithin hs_unique htarget_mem
  have hφ_at : MDifferentiableAt I₁ I₂ (φ : M₁ → M₂) x :=
    φ.mdifferentiable (by simp) x
  have hf_diff :
      MDifferentiableWithinAt 𝓘(ℝ, E₁) I₂ f s y := by
    simpa [f, x, Function.comp_def] using
      hφ_at.comp_mdifferentiableWithinAt y hsymm_s
  have hf_deriv :
      mfderivWithin 𝓘(ℝ, E₁) I₂ f s y =
        (mfderiv I₁ I₂ (φ : M₁ → M₂) x).comp
          (mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
            (e₁.extend I₁).target y) := by
    have hchain :
        mfderivWithin 𝓘(ℝ, E₁) I₂ ((φ : M₁ → M₂) ∘ (e₁.extend I₁).symm) s y =
          (mfderiv I₁ I₂ (φ : M₁ → M₂) x).comp
            (mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm s y) := by
      simpa [x] using
        mfderiv_comp_mfderivWithin
          (x := y) (g := (φ : M₁ → M₂)) (f := (e₁.extend I₁).symm)
          hφ_at hsymm_s hs_unique
    have hchain' :
        mfderivWithin 𝓘(ℝ, E₁) I₂ f s y =
          (mfderiv I₁ I₂ (φ : M₁ → M₂) x).comp
            (mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm s y) := by
      simpa [f, x, Function.comp_def] using hchain
    exact hchain'.trans (by rw [hsymm_deriv_s])
  have he₂max : e₂ ∈ IsManifold.maximalAtlas I₂ 1 M₂ :=
    IsManifold.subset_maximalAtlas (I := I₂) (n := 1) he₂
  have hext_at :
      MDifferentiableAt I₂ 𝓘(ℝ, E₂) (e₂.extend I₂) q :=
    (contMDiffAt_extend (I := I₂) (e := e₂) he₂max hq_source).mdifferentiableAt
      one_ne_zero
  have hfy : f y = q := by
    rfl
  have hψ_deriv_model :
      mfderivWithin 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ψ s y =
        (mfderiv I₂ 𝓘(ℝ, E₂) (e₂.extend I₂) q).comp
          ((mfderiv I₁ I₂ (φ : M₁ → M₂) x).comp
            (mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
              (e₁.extend I₁).target y)) := by
    have hchain :
        mfderivWithin 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ((e₂.extend I₂) ∘ f) s y =
          (mfderiv I₂ 𝓘(ℝ, E₂) (e₂.extend I₂) q).comp
            (mfderivWithin 𝓘(ℝ, E₁) I₂ f s y) := by
      simpa [hfy] using
        mfderiv_comp_mfderivWithin_of_eq
          (x := y) (y := q) (g := e₂.extend I₂) (f := f)
          hext_at hf_diff hs_unique hfy
    simpa [ψ, hf_deriv, ContinuousLinearMap.comp_assoc] using hchain
  have hψ_deriv :
      fderivWithin ℝ ψ s y =
        (mfderiv I₂ 𝓘(ℝ, E₂) (e₂.extend I₂) q).comp
          ((mfderiv I₁ I₂ (φ : M₁ → M₂) x).comp
            (mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
              (e₁.extend I₁).target y)) := by
    simpa [mfderivWithin_eq_fderivWithin] using hψ_deriv_model
  have hcancel :
      (mfderivWithin 𝓘(ℝ, E₂) I₂ (e₂.extend I₂).symm
          (e₂.extend I₂).target ((e₂.extend I₂) q)).comp
        (mfderiv I₂ 𝓘(ℝ, E₂) (e₂.extend I₂) q) =
      ContinuousLinearMap.id ℝ (TangentSpace I₂ q) :=
    mfderivWithin_extend_symm_comp_mfderiv_extend_of_mem_atlas
      (I := I₂) he₂ hq_source
  have hderiv :
      (mfderivWithin 𝓘(ℝ, E₂) I₂ (e₂.extend I₂).symm
          (e₂.extend I₂).target ((e₂.extend I₂) q)).comp
        (fderivWithin ℝ ψ s y) =
      (mfderiv I₁ I₂ (φ : M₁ → M₂) x).comp
        (mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
          (e₁.extend I₁).target y) := by
    let B :=
      mfderivWithin 𝓘(ℝ, E₂) I₂ (e₂.extend I₂).symm
        (e₂.extend I₂).target ((e₂.extend I₂) q)
    let C := mfderiv I₂ 𝓘(ℝ, E₂) (e₂.extend I₂) q
    let T :=
      (mfderiv I₁ I₂ (φ : M₁ → M₂) x).comp
        (mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
          (e₁.extend I₁).target y)
    change B.comp (fderivWithin ℝ ψ s y) = T
    have hψ_deriv' : fderivWithin ℝ ψ s y = C.comp T := by
      simpa [C, T] using hψ_deriv
    have hcancel' : B.comp C = ContinuousLinearMap.id ℝ (TangentSpace I₂ q) := by
      simpa [B, C] using hcancel
    have h1 : B.comp (fderivWithin ℝ ψ s y) = B.comp (C.comp T) :=
      congrArg (fun L ↦ B.comp L) hψ_deriv'
    have h2 : B.comp (C.comp T) = (B.comp C).comp T :=
      (ContinuousLinearMap.comp_assoc B C T).symm
    have h3 :
        (B.comp C).comp T =
          (ContinuousLinearMap.id ℝ (TangentSpace I₂ q)).comp T :=
      congrArg (fun L ↦ L.comp T) hcancel'
    have h4 : (ContinuousLinearMap.id ℝ (TangentSpace I₂ q)).comp T = T :=
      ContinuousLinearMap.id_comp T
    exact h1.trans (h2.trans (h3.trans h4))
  change
    ((omega.toFun q).compContinuousLinearMap
        (mfderiv I₁ I₂ (φ : M₁ → M₂) x)).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
        (e₁.extend I₁).target y)
    =
    ((omega.toFun ((e₂.extend I₂).symm ((e₂.extend I₂) q))).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E₂) I₂ (e₂.extend I₂).symm
          (e₂.extend I₂).target ((e₂.extend I₂) q))).compContinuousLinearMap
      (fderivWithin ℝ ψ s y)
  rw [hpoint]
  let A :=
    mfderivWithin 𝓘(ℝ, E₁) I₁ (e₁.extend I₁).symm
      (e₁.extend I₁).target y
  let L := mfderiv I₁ I₂ (φ : M₁ → M₂) x
  let B :=
    mfderivWithin 𝓘(ℝ, E₂) I₂ (e₂.extend I₂).symm
      (e₂.extend I₂).target ((e₂.extend I₂) q)
  let D := fderivWithin ℝ ψ s y
  change
    ((omega.toFun q).compContinuousLinearMap L).compContinuousLinearMap A =
    ((omega.toFun q).compContinuousLinearMap B).compContinuousLinearMap D
  have hleft :
      ((omega.toFun q).compContinuousLinearMap L).compContinuousLinearMap A =
        (omega.toFun q).compContinuousLinearMap (L.comp A) := by
    ext v
    rfl
  have hright :
      ((omega.toFun q).compContinuousLinearMap B).compContinuousLinearMap D =
        (omega.toFun q).compContinuousLinearMap (B.comp D) := by
    ext v
    rfl
  have hderiv' : B.comp D = L.comp A := by
    simpa [A, L, B, D] using hderiv
  rw [hleft, hright, hderiv']
  rfl

/--
%%handwave
name:
  Coordinate smoothness of smooth-form pullback along a diffeomorphism
statement:
  In every source chart, the coordinate representative of the pullback of a
  smooth real differential form along a smooth diffeomorphism is smooth.
proof:
  Near a source coordinate point, choose a target chart around its image.  The
  coordinate representative is the target coordinate representative composed
  with the coordinate expression of the diffeomorphism, and pulled back by the
  derivative of that coordinate expression.
-/
theorem contDiffOn_coordinateExpression_smoothDifferentialFormPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothDifferentialForm (I := I₂) (M := M₂) ℝ n)
    (e : OpenPartialHomeomorph M₁ H₁) (he : e ∈ atlas H₁ M₁) :
    ContDiffOn ℝ ∞
      (coordinateExpression (I := I₁) (F := ℝ) (n := n)
        (fun x ↦
          (omega.toFun (φ x)).compContinuousLinearMap
            (mfderiv I₁ I₂ φ x)) e)
      (e.extend I₁).target := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro y hy
  let x : M₁ := (e.extend I₁).symm y
  let e₂ : OpenPartialHomeomorph M₂ H₂ := chartAt H₂ (φ x)
  let u₀ : Set E₁ :=
    (fun z ↦ φ ((e.extend I₁).symm z)) ⁻¹' e₂.source
  have he₂ : e₂ ∈ atlas H₂ M₂ := by
    simp [e₂]
  have hu₀_mem : u₀ ∈ 𝓝[(e.extend I₁).target] y := by
    simpa [u₀, e₂, x] using
      diffeomorph_targetChart_source_mem_nhdsWithin
        (I₁ := I₁) (I₂ := I₂) φ e he hy
  rcases mem_nhdsWithin.mp hu₀_mem with ⟨u, hu_open, hyu, hu_sub⟩
  refine ⟨u, hu_open, hyu, ?_⟩
  let s : Set E₁ := (e.extend I₁).target ∩ u
  let ψ : E₁ → E₂ :=
    fun z ↦ (e₂.extend I₂) (φ ((e.extend I₁).symm z))
  have hmaps_source :
      MapsTo
        (fun z ↦ φ ((e.extend I₁).symm z))
        s e₂.source := by
    intro z hz
    exact hu_sub ⟨hz.2, hz.1⟩
  have hψ :
      ContDiffOn ℝ ∞ ψ s := by
    simpa [ψ, s] using
      contDiffOn_diffeomorphChartMap_local
        (I₁ := I₁) (I₂ := I₂) φ e he e₂ he₂
        (u := u) hmaps_source
  have hs : UniqueDiffOn ℝ s := by
    simpa [s] using
      (uniqueDiffOn_extend_target (I := I₁) e).inter hu_open
  have hDψ :
      ContDiffOn ℝ ∞
        (fderivWithin ℝ ψ s) s :=
    hψ.fderivWithin hs (by simp)
  have hη :
      ContDiffOn ℝ ∞
        (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂)
        (e₂.extend I₂).target :=
    omega.isContMDiff e₂ he₂
  have hψ_maps :
      MapsTo ψ s (e₂.extend I₂).target := by
    intro z hz
    have hz_source : φ ((e.extend I₁).symm z) ∈ (e₂.extend I₂).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hmaps_source hz
    simpa [ψ] using (e₂.extend I₂).map_source hz_source
  have hηψ :
      ContDiffOn ℝ ∞
        (fun z ↦
          coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂
            (ψ z)) s :=
    hη.comp hψ hψ_maps
  have hpullback :
      ContDiffOn ℝ ∞
        (fun z ↦
          (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂
            (ψ z)).compContinuousLinearMap
            (fderivWithin ℝ ψ s z)) s :=
    contDiffOn_continuousAlternatingMap_compContinuousLinearMap hηψ hDψ
  have hcoord_eq :
      EqOn
        (coordinateExpression (I := I₁) (F := ℝ) (n := n)
          (fun x ↦
            (omega.toFun (φ x)).compContinuousLinearMap
              (mfderiv I₁ I₂ φ x)) e)
        (fun z ↦
          (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂
            (ψ z)).compContinuousLinearMap
            (fderivWithin ℝ ψ s z))
        s := by
    simpa [ψ, s] using
      coordinateExpression_smoothDifferentialFormPullbackDiffeomorph_eqOn_local
        (I₁ := I₁) (I₂ := I₂) φ omega e he e₂ he₂
        (u := u) hu_open hmaps_source
  exact hpullback.congr hcoord_eq

/--
%%handwave
name:
  Smooth-form pullback along a diffeomorphism is smooth
statement:
  Pulling a smooth real differential form back along a smooth diffeomorphism
  gives a smooth real differential form.
proof:
  This follows from [the chartwise smoothness of smooth-form pullback along a diffeomorphism](lean:JJMath.Manifold.contDiffOn_coordinateExpression_smoothDifferentialFormPullbackDiffeomorph).
-/
theorem isContMDiffForm_smoothDifferentialFormPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothDifferentialForm (I := I₂) (M := M₂) ℝ n) :
    IsContMDiffForm (I := I₁) (M := M₁) (F := ℝ) (n := n) ∞
      (fun x ↦
        (omega.toFun (φ x)).compContinuousLinearMap
          (mfderiv I₁ I₂ φ x)) := by
  intro e he
  exact
    contDiffOn_coordinateExpression_smoothDifferentialFormPullbackDiffeomorph
      I₁ I₂ φ omega e he

/--
%%handwave
name:
  Pullback of a smooth real differential form along a diffeomorphism
statement:
  A smooth diffeomorphism pulls smooth real differential forms on the target
  back to smooth real differential forms on the source.
proof:
  At each point, pull back the alternating covector by the differential of the
  diffeomorphism.  Smoothness is [the smoothness of this chartwise pullback](lean:JJMath.Manifold.isContMDiffForm_smoothDifferentialFormPullbackDiffeomorph).
-/
def smoothDifferentialFormPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothDifferentialForm (I := I₂) (M := M₂) ℝ n) :
    SmoothDifferentialForm (I := I₁) (M := M₁) ℝ n where
  toFun := fun x ↦
    (omega.toFun (φ x)).compContinuousLinearMap
      (mfderiv I₁ I₂ φ x)
  isContMDiff :=
    isContMDiffForm_smoothDifferentialFormPullbackDiffeomorph
      (I₁ := I₁) (I₂ := I₂) φ omega

/--
%%handwave
name:
  Exterior derivative is natural for smooth-form pullback on tangent tuples
statement:
  At each point and on each tangent tuple,
  \(d(\varphi^\*\omega)=\varphi^\*(d\omega)\) for pullback of smooth real
  differential forms along a smooth diffeomorphism.
proof:
  In local coordinates this is the model-space pullback identity for the
  exterior derivative, applied to the coordinate expression of the
  diffeomorphism.
-/
theorem exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph_apply
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothDifferentialForm (I := I₂) (M := M₂) ℝ n)
    (x : M₁) (v : Fin (n + 1) → TangentSpace I₁ x) :
    ((exteriorDerivative (I := I₁) (r := ∞)
        (smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ omega)).toFun x :
      TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
    ((smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ
        (exteriorDerivative (I := I₂) (r := ∞) omega)).toFun x :
      TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) v := by
  let α : SmoothDifferentialForm (I := I₁) (M := M₁) ℝ n :=
    smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ omega
  let β : SmoothDifferentialForm (I := I₁) (M := M₁) ℝ (n + 1) :=
    smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ
      (exteriorDerivative (I := I₂) (r := ∞) omega)
  let e₁ : OpenPartialHomeomorph M₁ H₁ := chartAt H₁ x
  let y : E₁ := (extChartAt I₁ x) x
  have he₁ : e₁ ∈ atlas H₁ M₁ := by
    simp [e₁]
  have hy : y ∈ (e₁.extend I₁).target := by
    simp [e₁, y, extChartAt]
  have hsymm_y : (e₁.extend I₁).symm y = x := by
    simp [e₁, y, extChartAt]
  let q : M₂ := φ ((e₁.extend I₁).symm y)
  have hq_eq : q = φ x := by
    exact congrArg φ hsymm_y
  let e₂ : OpenPartialHomeomorph M₂ H₂ := chartAt H₂ q
  let u₀ : Set E₁ :=
    (fun z ↦ φ ((e₁.extend I₁).symm z)) ⁻¹' e₂.source
  have he₂ : e₂ ∈ atlas H₂ M₂ := by
    simp [e₂]
  have hu₀_mem : u₀ ∈ 𝓝[(e₁.extend I₁).target] y := by
    simpa [u₀, e₂, q] using
      diffeomorph_targetChart_source_mem_nhdsWithin
        (I₁ := I₁) (I₂ := I₂) φ e₁ he₁ hy
  rcases mem_nhdsWithin.mp hu₀_mem with ⟨u, hu_open, hyu, hu_sub⟩
  let s : Set E₁ := (e₁.extend I₁).target ∩ u
  let ψ : E₁ → E₂ :=
    fun z ↦ (e₂.extend I₂) (φ ((e₁.extend I₁).symm z))
  have hy_s : y ∈ s := ⟨hy, hyu⟩
  have hmaps_source :
      MapsTo
        (fun z ↦ φ ((e₁.extend I₁).symm z))
        s e₂.source := by
    intro z hz
    exact hu_sub ⟨hz.2, hz.1⟩
  have hψ :
      ContDiffOn ℝ ∞ ψ s := by
    simpa [ψ, s] using
      contDiffOn_diffeomorphChartMap_local
        (I₁ := I₁) (I₂ := I₂) φ e₁ he₁ e₂ he₂
        (u := u) hmaps_source
  have hψ_at : ContDiffWithinAt ℝ ∞ ψ s y :=
    hψ y hy_s
  have hs_unique : UniqueDiffOn ℝ s := by
    simpa [s] using
      (uniqueDiffOn_extend_target (I := I₁) e₁).inter hu_open
  have hs_mem_target : s ∈ 𝓝[(e₁.extend I₁).target] y := by
    change (e₁.extend I₁).target ∩ u ∈ 𝓝[(e₁.extend I₁).target] y
    exact
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (hu_open.mem_nhds hyu))
  have hy_closure_target : y ∈ closure (interior (e₁.extend I₁).target) := by
    simpa [e₁, y, extChartAt] using
      extChartAt_target_subset_closure_interior (I := I₁) (x := x)
        (mem_extChartAt_target (I := I₁) x)
  have hy_closure_s : y ∈ closure (interior s) := by
    simpa [s] using
      mem_closure_interior_inter_of_mem_open
        (s := (e₁.extend I₁).target) (u := u)
        hy_closure_target hu_open hyu
  have hψ_maps :
      MapsTo ψ s (e₂.extend I₂).target := by
    intro z hz
    have hz_source : φ ((e₁.extend I₁).symm z) ∈ (e₂.extend I₂).source := by
      simpa [e₂.extend_source (I := I₂)] using hmaps_source hz
    simpa [ψ] using (e₂.extend I₂).map_source hz_source
  have hψy_target : ψ y ∈ (e₂.extend I₂).target :=
    hψ_maps hy_s
  have hmin : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    simpa [minSmoothness] using
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from by
        exact_mod_cast (show (2 : ℕ) ≤ (⊤ : ℕ∞) from le_top))
  have hα_set :
      extDerivWithin
          (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁)
          (e₁.extend I₁).target y =
        extDerivWithin
          (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁)
          s y := by
    have hdiff_s :
        DifferentiableWithinAt ℝ
          (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁) s y :=
      ((α.isContMDiff e₁ he₁ y hy).differentiableWithinAt (by simp)).mono
        inter_subset_left
    have hderiv_set :
        fderivWithin ℝ
            (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁)
            (e₁.extend I₁).target y =
          fderivWithin ℝ
            (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁)
            s y :=
      fderivWithin_of_mem_nhdsWithin hs_mem_target
        ((uniqueDiffOn_extend_target (I := I₁) e₁) y hy) hdiff_s
    rw [extDerivWithin, extDerivWithin, hderiv_set]
  have hα_coord_eq :
      EqOn
        (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁)
        (fun z ↦
          (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂
            (ψ z)).compContinuousLinearMap
            (fderivWithin ℝ ψ s z))
        s := by
    simpa [α, ψ, s] using
      coordinateExpression_smoothDifferentialFormPullbackDiffeomorph_eqOn_local
        (I₁ := I₁) (I₂ := I₂) φ omega e₁ he₁ e₂ he₂
        (u := u) hu_open hmaps_source
  have hα_congr :
      extDerivWithin
          (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁)
          s y =
        extDerivWithin
          (fun z ↦
            (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂
              (ψ z)).compContinuousLinearMap
              (fderivWithin ℝ ψ s z))
          s y :=
    extDerivWithin_congr' hα_coord_eq hy_s
  have hωdiff :
      DifferentiableWithinAt ℝ
        (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂)
        (e₂.extend I₂).target (ψ y) :=
    (omega.isContMDiff e₂ he₂ (ψ y) hψy_target).differentiableWithinAt (by simp)
  have hpullback :
      extDerivWithin
          (fun z ↦
            (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂
              (ψ z)).compContinuousLinearMap
              (fderivWithin ℝ ψ s z))
          s y =
        (extDerivWithin
          (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂)
          (e₂.extend I₂).target (ψ y)).compContinuousLinearMap
            (fderivWithin ℝ ψ s y) :=
    extDerivWithin_pullback (x := y) (f := ψ) (t := (e₂.extend I₂).target)
      hωdiff hψ_at hmin hs_unique hy_closure_s hy_s hψ_maps
  have hβ_coord_eq :
      EqOn
        (coordinateExpression (I := I₁) (F := ℝ) (n := n + 1) β.toFun e₁)
        (fun z ↦
          (coordinateExpression (I := I₂) (F := ℝ) (n := n + 1)
            (exteriorDerivative (I := I₂) (r := ∞) omega).toFun e₂
            (ψ z)).compContinuousLinearMap
            (fderivWithin ℝ ψ s z))
        s := by
    simpa [β, ψ, s] using
      coordinateExpression_smoothDifferentialFormPullbackDiffeomorph_eqOn_local
        (I₁ := I₁) (I₂ := I₂) φ
        (exteriorDerivative (I := I₂) (r := ∞) omega) e₁ he₁ e₂ he₂
        (u := u) hu_open hmaps_source
  have htarget_d :
      coordinateExpression (I := I₂) (F := ℝ) (n := n + 1)
          (exteriorDerivative (I := I₂) (r := ∞) omega).toFun e₂ (ψ y) =
        extDerivWithin
          (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂)
          (e₂.extend I₂).target (ψ y) :=
    coordinateExpression_exteriorDerivativePoint (I := I₂) (r := ∞) omega he₂ hψy_target
  have hcoord :
      coordinateExpression (I := I₁) (F := ℝ) (n := n + 1)
          (exteriorDerivative (I := I₁) (r := ∞) α).toFun e₁ y =
        coordinateExpression (I := I₁) (F := ℝ) (n := n + 1) β.toFun e₁ y := by
    calc
      coordinateExpression (I := I₁) (F := ℝ) (n := n + 1)
          (exteriorDerivative (I := I₁) (r := ∞) α).toFun e₁ y =
        extDerivWithin
          (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁)
          (e₁.extend I₁).target y := by
          exact coordinateExpression_exteriorDerivativePoint
            (I := I₁) (r := ∞) α he₁ hy
      _ =
        extDerivWithin
          (coordinateExpression (I := I₁) (F := ℝ) (n := n) α.toFun e₁)
          s y := hα_set
      _ =
        extDerivWithin
          (fun z ↦
            (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂
              (ψ z)).compContinuousLinearMap
              (fderivWithin ℝ ψ s z))
          s y := hα_congr
      _ =
        (extDerivWithin
          (coordinateExpression (I := I₂) (F := ℝ) (n := n) omega.toFun e₂)
          (e₂.extend I₂).target (ψ y)).compContinuousLinearMap
            (fderivWithin ℝ ψ s y) := hpullback
      _ =
        (coordinateExpression (I := I₂) (F := ℝ) (n := n + 1)
          (exteriorDerivative (I := I₂) (r := ∞) omega).toFun e₂
          (ψ y)).compContinuousLinearMap
            (fderivWithin ℝ ψ s y) := by
          rw [htarget_d]
      _ =
        coordinateExpression (I := I₁) (F := ℝ) (n := n + 1) β.toFun e₁ y :=
          (hβ_coord_eq hy_s).symm
  have hleft_self :=
    coordinateExpression_chartAt_self (I := I₁)
      (F := ℝ) (n := n + 1)
      (exteriorDerivative (I := I₁) (r := ∞) α).toFun x
  have hright_self :=
    coordinateExpression_chartAt_self (I := I₁)
      (F := ℝ) (n := n + 1) β.toFun x
  have hpoint_eq :
      ((exteriorDerivative (I := I₁) (r := ∞) α).toFun x :
        TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) =
      (β.toFun x :
        TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) := by
    simpa [e₁, y] using hleft_self.symm.trans (hcoord.trans hright_self)
  simpa [α, β] using congrArg (fun eta ↦ eta v) hpoint_eq

/--
%%handwave
name:
  Exterior derivative is natural for smooth-form pullback
statement:
  As pointwise forms, \(d(\varphi^\*\omega)=\varphi^\*(d\omega)\) for
  smooth real differential forms and smooth diffeomorphisms.
proof:
  Extensionality reduces this to [naturality on tangent tuples](lean:JJMath.Manifold.exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph_apply).
-/
theorem exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph_toFun
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothDifferentialForm (I := I₂) (M := M₂) ℝ n)
    (x : M₁) :
    ((exteriorDerivative (I := I₁) (r := ∞)
        (smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ omega)).toFun x :
      TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) =
    ((smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ
        (exteriorDerivative (I := I₂) (r := ∞) omega)).toFun x :
      TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) := by
  ext v
  exact exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph_apply
    I₁ I₂ φ omega x v

/--
%%handwave
name:
  Exterior derivative commutes with smooth-form pullback
statement:
  The exterior derivative of the pullback of a smooth real differential form
  along a smooth diffeomorphism is the pullback of its exterior derivative.
proof:
  Extensionality reduces this to [the pointwise naturality statement](lean:JJMath.Manifold.exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph_toFun).
-/
theorem exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothDifferentialForm (I := I₂) (M := M₂) ℝ n) :
    exteriorDerivative (I := I₁) (r := ∞)
        (smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ omega) =
      smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ
        (exteriorDerivative (I := I₂) (r := ∞) omega) := by
  ext x v
  exact exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph_apply
    I₁ I₂ φ omega x v

end DiffeomorphismPullback

end Coefficients

section RealManifoldAliases

variable {Eℝ : Type*} [NormedAddCommGroup Eℝ] [NormedSpace ℝ Eℝ]
variable {Hℝ : Type*} [TopologicalSpace Hℝ]
variable {Mℝ : Type*} [TopologicalSpace Mℝ] [ChartedSpace Hℝ Mℝ]
variable (Iℝ : ModelWithCorners ℝ Eℝ Hℝ)

/-- Real-valued `C^r` differential forms on a real manifold. -/
abbrev RealDifferentialForm (n : ℕ) (r : WithTop ℕ∞) :=
  DifferentialForm (I := Iℝ) (M := Mℝ) (F := ℝ) (n := n) (r := r)

/-- Complex-valued `C^r` differential forms on a real manifold. -/
abbrev ComplexDifferentialForm (n : ℕ) (r : WithTop ℕ∞) :=
  DifferentialForm (I := Iℝ) (M := Mℝ) (F := ℂ) (n := n) (r := r)

/-- Real-valued smooth differential forms on a real manifold. -/
abbrev SmoothRealDifferentialForm (n : ℕ) :=
  DifferentialForm (I := Iℝ) (M := Mℝ) (F := ℝ) (n := n) (r := ∞)

/-- Complex-valued smooth differential forms on a real manifold. -/
abbrev SmoothComplexDifferentialForm (n : ℕ) :=
  DifferentialForm (I := Iℝ) (M := Mℝ) (F := ℂ) (n := n) (r := ∞)

/-- Real-valued analytic differential forms on a real manifold. -/
abbrev AnalyticRealDifferentialForm (n : ℕ) :=
  DifferentialForm (I := Iℝ) (M := Mℝ) (F := ℝ) (n := n) (r := ω)

/-- Complex-valued analytic differential forms on a real manifold. -/
abbrev AnalyticComplexDifferentialForm (n : ℕ) :=
  DifferentialForm (I := Iℝ) (M := Mℝ) (F := ℂ) (n := n) (r := ω)

end RealManifoldAliases

end
end Manifold
end JJMath
