import JJMath.Manifold.DifferentialForm
import Mathlib.Algebra.Exact
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# De Rham cohomology

This file packages smooth differential forms into the beginning of the de Rham
complex.  The core quotient is the usual one: closed forms modulo exact forms.

The Mayer-Vietoris theorem is recorded as the next target theorem.  Its proof
will require the restriction maps, the difference map on the overlap, the
connecting morphism, and the short exact sequence of de Rham complexes for an
open cover.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

universe v w m a

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H)

namespace DifferentialForm

variable {I}
variable {A : Type a} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
variable {n : ℕ} {r : WithTop ℕ∞}

/--
%%handwave
name:
  Addition preserves form regularity
statement:
  The pointwise sum of two \(C^r\) differential forms is again a \(C^r\)
  differential form.
proof:
  In each chart, add the two coordinate representatives and use pointwise
  equality of the resulting alternating maps.
-/
theorem isContMDiffForm_add
    (omega eta : DifferentialForm (I := I) (M := M) A n r) :
    IsContMDiffForm (I := I) (M := M) (F := A) (n := n) r
      (fun x ↦ omega.toFun x + eta.toFun x) := by
  intro e he
  refine ((omega.isContMDiff e he).add (eta.isContMDiff e he)).congr ?_
  intro y hy
  ext v
  rfl

/--
%%handwave
name:
  Negation preserves form regularity
statement:
  The pointwise negative of a \(C^r\) differential form is again a \(C^r\)
  differential form.
proof:
  In each chart, negate the coordinate representative and identify the result
  pointwise.
-/
theorem isContMDiffForm_neg
    (omega : DifferentialForm (I := I) (M := M) A n r) :
    IsContMDiffForm (I := I) (M := M) (F := A) (n := n) r
      (fun x ↦ -omega.toFun x) := by
  intro e he
  refine (omega.isContMDiff e he).neg.congr ?_
  intro y hy
  ext v
  rfl

/--
%%handwave
name:
  Scalar multiplication preserves form regularity
statement:
  Multiplying a \(C^r\) differential form by a scalar gives another \(C^r\)
  differential form.
proof:
  In every chart, multiply the coordinate representative by the same scalar and
  compare the alternating maps pointwise.
-/
theorem isContMDiffForm_smul
    (c : 𝕜) (omega : DifferentialForm (I := I) (M := M) A n r) :
    IsContMDiffForm (I := I) (M := M) (F := A) (n := n) r
      (fun x ↦ c • omega.toFun x) := by
  intro e he
  refine ((omega.isContMDiff e he).const_smul c).congr ?_
  intro y hy
  ext v
  rfl

instance instAdd : Add (DifferentialForm (I := I) (M := M) A n r) where
  add omega eta :=
    { toFun := fun x ↦ omega.toFun x + eta.toFun x
      isContMDiff := isContMDiffForm_add (I := I) omega eta }

instance instNeg : Neg (DifferentialForm (I := I) (M := M) A n r) where
  neg omega :=
    { toFun := fun x ↦ -omega.toFun x
      isContMDiff := isContMDiffForm_neg (I := I) omega }

instance instSub : Sub (DifferentialForm (I := I) (M := M) A n r) where
  sub omega eta := omega + -eta

instance instAddCommGroup : AddCommGroup (DifferentialForm (I := I) (M := M) A n r) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  sub := fun omega eta ↦ omega + -eta
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro omega eta theta
    ext x v
    exact add_assoc (omega.toFun x v) (eta.toFun x v) (theta.toFun x v)
  zero_add := by
    intro omega
    ext x v
    exact zero_add (omega.toFun x v)
  add_zero := by
    intro omega
    ext x v
    exact add_zero (omega.toFun x v)
  neg_add_cancel := by
    intro omega
    ext x v
    exact neg_add_cancel (omega.toFun x v)
  add_comm := by
    intro omega eta
    ext x v
    exact add_comm (omega.toFun x v) (eta.toFun x v)

instance instSMul : SMul 𝕜 (DifferentialForm (I := I) (M := M) A n r) where
  smul c omega :=
    { toFun := fun x ↦ c • omega.toFun x
      isContMDiff := isContMDiffForm_smul (I := I) c omega }

instance instModule : Module 𝕜 (DifferentialForm (I := I) (M := M) A n r) where
  one_smul := by
    intro omega
    ext x v
    exact one_smul 𝕜 (omega.toFun x v)
  mul_smul := by
    intro c d omega
    ext x v
    exact mul_smul c d (omega.toFun x v)
  smul_zero := by
    intro c
    ext x v
    exact smul_zero c
  smul_add := by
    intro c omega eta
    ext x v
    exact smul_add c (omega.toFun x v) (eta.toFun x v)
  add_smul := by
    intro c d omega
    ext x v
    exact add_smul c d (omega.toFun x v)
  zero_smul := by
    intro omega
    ext x v
    exact zero_smul 𝕜 (omega.toFun x v)

end DifferentialForm

section OpenSubtypeCharts

variable {I}

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Restricted chart target lies in the ambient chart target
statement:
  A point in the extended target of a chart restricted to an open subset also
  lies in the extended target of the ambient chart.
proof:
  Expand the extended target of the restricted chart and keep the ambient
  target membership.
-/
theorem subtypeRestr_extend_target_subset
    (e : OpenPartialHomeomorph M H) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) {y : E}
    (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    y ∈ (e.extend I).target := by
  rw [OpenPartialHomeomorph.extend_target] at hy ⊢
  exact ⟨e.subtypeRestr_target_subset hU hy.1, hy.2⟩

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Ambient chart points in an open subset lie in the restricted target
statement:
  If a point of an ambient extended chart maps back into an open subset, then
  it belongs to the extended target of the restricted chart.
proof:
  Expand the target conditions and use the image description of a restricted
  chart.
-/
theorem subtypeRestr_extend_target_of_mem
    (e : OpenPartialHomeomorph M H) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) {y : E}
    (hy : y ∈ (e.extend I).target)
    (hyU : (e.extend I).symm y ∈ U) :
    y ∈ ((e.subtypeRestr hU).extend I).target := by
  rw [OpenPartialHomeomorph.extend_target] at hy ⊢
  refine ⟨?_, hy.2⟩
  let x : M := e.symm (I.symm y)
  have hx_source : x ∈ e.source := by
    exact e.map_target hy.1
  have hxU : x ∈ U := by
    simpa [x, OpenPartialHomeomorph.extend_coe_symm] using hyU
  have hmap : e x ∈ (e.subtypeRestr hU).target :=
    e.map_subtype_source (hs := hU) (x := ⟨x, hxU⟩) hx_source
  have hx_map : e x = I.symm y := by
    exact e.right_inv hy.1
  simpa [x, hx_map] using hmap

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Restricted chart target is a neighborhood in the ambient target
statement:
  At a point of a restricted chart target, that restricted target is a
  neighborhood relative to the ambient chart target.
proof:
  Identify both relative neighborhood filters with the model range and use the
  basic self-neighborhood property.
-/
theorem subtypeRestr_extend_target_mem_nhdsWithin
    (e : OpenPartialHomeomorph M H) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) {y : E}
    (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    ((e.subtypeRestr hU).extend I).target ∈ 𝓝[(e.extend I).target] y := by
  have hsmall :
      𝓝[((e.subtypeRestr hU).extend I).target] y = 𝓝[range I] y :=
    nhdsWithin_extend_target_eq_of_mem (I := I) hy
  have hamb : 𝓝[(e.extend I).target] y = 𝓝[range I] y :=
    nhdsWithin_extend_target_eq_of_mem (I := I)
      (subtypeRestr_extend_target_subset (I := I) e U hU hy)
  have hs : ((e.subtypeRestr hU).extend I).target ∈ 𝓝[range I] y := by
    simpa [← hsmall] using
      (self_mem_nhdsWithin : ((e.subtypeRestr hU).extend I).target ∈
        𝓝[((e.subtypeRestr hU).extend I).target] y)
  simpa [← hamb] using hs

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Restricted inverse chart agrees with the ambient inverse
statement:
  The inverse extended chart of a restricted chart, viewed in the ambient
  manifold, agrees with the inverse extended chart of the original chart.
proof:
  Expand the extended inverse charts and apply the inverse formula for
  restricted charts.
-/
theorem subtypeRestr_extend_symm_coe
    (e : OpenPartialHomeomorph M H) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) {y : E}
    (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    (((e.subtypeRestr hU).extend I).symm y : U) = (e.extend I).symm y := by
  rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe_symm]
  have hy' : I.symm y ∈ (e.subtypeRestr hU).target := by
    rw [OpenPartialHomeomorph.extend_target] at hy
    exact hy.1
  simpa using e.subtypeRestr_symm_apply hU hy'

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Restricted chart targets are monotone
statement:
  If one open subset is contained in another, the target of the chart
  restricted to the smaller subset is contained in the target of the chart
  restricted to the larger subset.
proof:
  Write both targets as images of sources and regard a point of the smaller
  open subset as a point of the larger one.
-/
theorem subtypeRestr_target_mono
    (e : OpenPartialHomeomorph M H) {U V : TopologicalSpace.Opens M}
    (hU : Nonempty U) (hV : Nonempty V) (hUV : U ≤ V) :
    (e.subtypeRestr hU).target ⊆ (e.subtypeRestr hV).target := by
  rw [← OpenPartialHomeomorph.image_source_eq_target,
      ← OpenPartialHomeomorph.image_source_eq_target]
  rintro y ⟨x, hx, rfl⟩
  refine ⟨⟨x, hUV x.prop⟩, ?_, rfl⟩
  simpa [OpenPartialHomeomorph.subtypeRestr_source] using hx

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Extended restricted chart targets are monotone
statement:
  If one open subset is contained in another, membership in the extended
  target of the smaller restricted chart implies membership in the extended
  target of the larger restricted chart.
proof:
  Expand the extended target and use monotonicity of the ordinary restricted
  chart targets.
-/
theorem subtypeRestr_extend_target_mono
    (e : OpenPartialHomeomorph M H) {U V : TopologicalSpace.Opens M}
    (hU : Nonempty U) (hV : Nonempty V) (hUV : U ≤ V) {y : E}
    (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    y ∈ ((e.subtypeRestr hV).extend I).target := by
  rw [OpenPartialHomeomorph.extend_target] at hy ⊢
  exact ⟨subtypeRestr_target_mono e hU hV hUV hy.1, hy.2⟩

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Smaller restricted chart target is a relative neighborhood
statement:
  If one open subset is contained in another, then at a point of the smaller
  restricted target, that smaller target is a neighborhood inside the larger
  restricted target.
proof:
  Identify the relative neighborhood filters of both extended targets with the
  model range.
-/
theorem subtypeRestr_extend_target_mem_nhdsWithin_of_le
    (e : OpenPartialHomeomorph M H) {U V : TopologicalSpace.Opens M}
    (hU : Nonempty U) (hV : Nonempty V) (hUV : U ≤ V) {y : E}
    (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    ((e.subtypeRestr hU).extend I).target ∈
      𝓝[((e.subtypeRestr hV).extend I).target] y := by
  have hsmall :
      𝓝[((e.subtypeRestr hU).extend I).target] y = 𝓝[range I] y :=
    nhdsWithin_extend_target_eq_of_mem (I := I) hy
  have hlarge :
      𝓝[((e.subtypeRestr hV).extend I).target] y = 𝓝[range I] y :=
    nhdsWithin_extend_target_eq_of_mem (I := I)
      (subtypeRestr_extend_target_mono (I := I) e hU hV hUV hy)
  have hs : ((e.subtypeRestr hU).extend I).target ∈ 𝓝[range I] y := by
    simpa [← hsmall] using
      (self_mem_nhdsWithin : ((e.subtypeRestr hU).extend I).target ∈
        𝓝[((e.subtypeRestr hU).extend I).target] y)
  simpa [← hlarge] using hs

omit [ChartedSpace H M] in
/--
%%handwave
name:
  Inverse charts are compatible with open inclusions
statement:
  For nested open subsets, the inverse chart for the larger restricted chart is
  the inclusion of the inverse chart for the smaller restricted chart.
proof:
  Expand the extended inverse charts and use compatibility of restricted chart
  inverses under inclusion.
-/
theorem subtypeRestr_extend_symm_of_le
    (e : OpenPartialHomeomorph M H) {U V : TopologicalSpace.Opens M}
    (hU : Nonempty U) (hV : Nonempty V) (hUV : U ≤ V) {y : E}
    (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    ((e.subtypeRestr hV).extend I).symm y =
      TopologicalSpace.Opens.inclusion hUV (((e.subtypeRestr hU).extend I).symm y) := by
  rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe_symm]
  have hy' : I.symm y ∈ (e.subtypeRestr hU).target := by
    rw [OpenPartialHomeomorph.extend_target] at hy
    exact hy.1
  exact e.subtypeRestr_symm_eqOn_of_le hU hV hUV hy'

end OpenSubtypeCharts

section OpenSubtypeDerivative

variable {I}

/--
%%handwave
name:
  Derivative of an open-subset chart inclusion
statement:
  In a restricted chart, the derivative of the inclusion of an open subset
  composed with the inverse restricted chart is the derivative of the inverse
  ambient chart.
proof:
  Apply the chain rule to the inverse restricted chart followed by the
  inclusion, then replace the resulting map by the ambient inverse chart on the
  relevant target.
-/
theorem mfderiv_subtypeVal_comp_subtypeRestr_extend_symm
    [IsManifold I 1 M]
    (e : OpenPartialHomeomorph M H) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) (he : e ∈ atlas H M)
    (heU : e.subtypeRestr hU ∈ atlas H U)
    {y : E} (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    (mfderiv I I (fun z : U => (z : M)) (((e.subtypeRestr hU).extend I).symm y)).comp
        (mfderivWithin 𝓘(𝕜, E) I ((e.subtypeRestr hU).extend I).symm
          ((e.subtypeRestr hU).extend I).target y) =
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y := by
  let eU : OpenPartialHomeomorph U H := e.subtypeRestr hU
  have hf : MDifferentiableWithinAt 𝓘(𝕜, E) I (eU.extend I).symm
      (eU.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) heU hy
  have hg : MDifferentiableWithinAt I I (fun z : U => (z : M)) univ
      ((eU.extend I).symm y) := by
    simpa [mdifferentiableWithinAt_univ] using
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).contMDiffAt.mdifferentiableAt
        (by simp))
  have hxs : UniqueMDiffWithinAt 𝓘(𝕜, E) (eU.extend I).target y := by
    exact ((uniqueDiffOn_extend_target (I := I) eU) y hy).uniqueMDiffWithinAt
  have hchain :=
    mfderivWithin_comp (I := 𝓘(𝕜, E)) (I' := I) (I'' := I) (x := y)
      (g := fun z : U => (z : M)) (f := (eU.extend I).symm)
      (s := (eU.extend I).target) (u := univ) hg hf (by intro z _hz; trivial) hxs
  change mfderivWithin 𝓘(𝕜, E) I
      ((fun z : U => (z : M)) ∘ (eU.extend I).symm)
      (eU.extend I).target y = _ at hchain
  rw [mfderivWithin_univ] at hchain
  have hcomp_eq :
      EqOn ((fun z : U => (z : M)) ∘ (eU.extend I).symm)
        (e.extend I).symm (eU.extend I).target := by
    intro z hz
    exact subtypeRestr_extend_symm_coe (I := I) e U hU hz
  have hleft_eq :
      mfderivWithin 𝓘(𝕜, E) I
          ((fun z : U => (z : M)) ∘ (eU.extend I).symm)
          (eU.extend I).target y =
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm
          (eU.extend I).target y :=
    mfderivWithin_congr hcomp_eq (hcomp_eq hy)
  have hamb_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y := by
    exact mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) he
      (subtypeRestr_extend_target_subset (I := I) e U hU hy)
  have htarget_mem : (e.extend I).target ∈ 𝓝[(eU.extend I).target] y := by
    exact Filter.mem_of_superset self_mem_nhdsWithin (by
      intro z hz
      exact subtypeRestr_extend_target_subset (I := I) e U hU hz)
  have hright_eq :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (eU.extend I).target y =
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y := by
    exact hamb_diff.mfderivWithin_mono_of_mem_nhdsWithin hxs htarget_mem
  rw [hleft_eq, hright_eq] at hchain
  exact hchain.symm

/--
%%handwave
name:
  Differentiability of inverse charts in the maximal atlas
statement:
  The inverse of an extended chart from the maximal \(C^1\) atlas is
  differentiable within its target.
proof:
  Write the inverse extended chart as the model inverse followed by the chart
  inverse, and compose their differentiability statements.
-/
theorem mdifferentiableWithinAt_extend_symm_of_mem_maximalAtlas
    [IsManifold I 1 M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    {y : E} (hy : y ∈ (e.extend I).target) :
    MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y := by
  rw [e.extend_coe_symm (I := I)]
  have hy_range : y ∈ range I := e.extend_target_subset_range hy
  have hy_target : I.symm y ∈ e.target := by
    simpa [e.extend_target (I := I)] using hy.2
  have hI : MDifferentiableWithinAt 𝓘(𝕜, E) I I.symm (range I) y :=
    I.mdifferentiableWithinAt_symm hy_range
  have he_symm : MDifferentiableAt I I e.symm (I.symm y) :=
    (contMDiffAt_symm_of_mem_maximalAtlas (I := I) (n := 1) he hy_target).mdifferentiableAt
      one_ne_zero
  exact he_symm.comp_mdifferentiableWithinAt y (hI.mono (e.extend_target_subset_range))

/--
%%handwave
name:
  Smooth open-subset chart inclusion derivative
statement:
  For smooth maximal-atlas charts, the derivative formula for the inclusion of
  an open subset agrees with the ambient inverse chart derivative.
proof:
  Reduce the smooth maximal-atlas hypotheses to \(C^1\), apply the chain rule,
  and identify the relative derivatives using neighborhood containment.
-/
theorem mfderiv_subtypeVal_comp_subtypeRestr_extend_symm_maximal
    [IsManifold I ∞ M]
    (e : OpenPartialHomeomorph M H) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (heU : e.subtypeRestr hU ∈ IsManifold.maximalAtlas I ∞ U)
    {y : E} (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    (mfderiv I I (fun z : U => (z : M)) (((e.subtypeRestr hU).extend I).symm y)).comp
        (mfderivWithin 𝓘(𝕜, E) I ((e.subtypeRestr hU).extend I).symm
          ((e.subtypeRestr hU).extend I).target y) =
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y := by
  let eU : OpenPartialHomeomorph U H := e.subtypeRestr hU
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp) he
  have heU1 : eU ∈ IsManifold.maximalAtlas I 1 U :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := U)
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp) heU
  have hf : MDifferentiableWithinAt 𝓘(𝕜, E) I (eU.extend I).symm
      (eU.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_maximalAtlas (I := I) heU1 hy
  have hg : MDifferentiableWithinAt I I (fun z : U => (z : M)) univ
      ((eU.extend I).symm y) := by
    simpa [mdifferentiableWithinAt_univ] using
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).contMDiffAt.mdifferentiableAt
        (by simp))
  have hxs : UniqueMDiffWithinAt 𝓘(𝕜, E) (eU.extend I).target y := by
    exact ((uniqueDiffOn_extend_target (I := I) eU) y hy).uniqueMDiffWithinAt
  have hchain :=
    mfderivWithin_comp (I := 𝓘(𝕜, E)) (I' := I) (I'' := I) (x := y)
      (g := fun z : U => (z : M)) (f := (eU.extend I).symm)
      (s := (eU.extend I).target) (u := univ) hg hf (by intro z _hz; trivial) hxs
  change mfderivWithin 𝓘(𝕜, E) I
      ((fun z : U => (z : M)) ∘ (eU.extend I).symm)
      (eU.extend I).target y = _ at hchain
  rw [mfderivWithin_univ] at hchain
  have hcomp_eq :
      EqOn ((fun z : U => (z : M)) ∘ (eU.extend I).symm)
        (e.extend I).symm (eU.extend I).target := by
    intro z hz
    exact subtypeRestr_extend_symm_coe (I := I) e U hU hz
  have hleft_eq :
      mfderivWithin 𝓘(𝕜, E) I
          ((fun z : U => (z : M)) ∘ (eU.extend I).symm)
          (eU.extend I).target y =
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm
          (eU.extend I).target y :=
    mfderivWithin_congr hcomp_eq (hcomp_eq hy)
  have hamb_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_maximalAtlas (I := I) he1
      (subtypeRestr_extend_target_subset (I := I) e U hU hy)
  have htarget_mem : (e.extend I).target ∈ 𝓝[(eU.extend I).target] y := by
    exact Filter.mem_of_superset self_mem_nhdsWithin (by
      intro z hz
      exact subtypeRestr_extend_target_subset (I := I) e U hU hz)
  have hright_eq :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (eU.extend I).target y =
        mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y := by
    exact hamb_diff.mfderivWithin_mono_of_mem_nhdsWithin hxs htarget_mem
  rw [hleft_eq, hright_eq] at hchain
  exact hchain.symm

/--
%%handwave
name:
  Derivative of inverse charts under coordinate change
statement:
  The derivative of an inverse chart equals the derivative of another inverse
  chart after coordinate change, composed with the derivative of the coordinate
  change.
proof:
  Apply the chain rule to the identity between inverse charts and coordinate
  changes, replacing derivatives over smaller target sets by derivatives over
  the chart targets.
-/
theorem mfderivWithin_extend_symm_coordChange_maximal
    [IsManifold I 1 M]
    {e e' : OpenPartialHomeomorph M H} {y : E}
    (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
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
    exact hφ_target_subset_target' (φ.map_source hz)
  have hφ_source_subset_target : φ.source ⊆ (e.extend I).target := by
    intro z hz
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using hz.1
  have htarget_mem : (e.extend I).target ∈ 𝓝[φ.source] y :=
    Filter.mem_of_superset self_mem_nhdsWithin hφ_source_subset_target
  have hunique_φ : UniqueMDiffWithinAt 𝓘(𝕜, E) φ.source y :=
    (I.uniqueDiffOn_extendCoordChange_source (e := e) (e' := e') y hy).uniqueMDiffWithinAt
  have he_symm_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_maximalAtlas (I := I) he hy_target
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
    have hφ_contdiff : ContDiffOn 𝕜 1 φ φ.source :=
      I.contDiffOn_extendCoordChange he he'
    exact (hφ_contdiff y hy).differentiableWithinAt one_ne_zero |>.mdifferentiableWithinAt
  have hφy_target : φ y ∈ (e'.extend I).target :=
    hφ_target_subset_target' (φ.map_source hy)
  have he'_symm_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y) :=
    mdifferentiableWithinAt_extend_symm_of_mem_maximalAtlas (I := I) he' hφy_target
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
  Coordinate expressions transform by pullback
statement:
  The coordinate representative of a form in one chart is obtained from its
  representative in another chart by precomposing with the derivative of the
  coordinate change.
proof:
  Use the point equality of inverse charts under coordinate change and the
  derivative formula for inverse charts.
-/
theorem coordinateExpression_coordChange_maximal
    [IsManifold I 1 M]
    {A : Type a} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    {n : ℕ} (form : (x : M) → FormAt (I := I) (M := M) A n x)
    {e e' : OpenPartialHomeomorph M H} {y : E}
    (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    (hy : y ∈ (I.extendCoordChange e e').source) :
    coordinateExpression (I := I) (F := A) (n := n) form e y =
      (coordinateExpression (I := I) (F := A) (n := n) form e'
        ((I.extendCoordChange e e') y)).compContinuousLinearMap
        (fderivWithin 𝕜 (I.extendCoordChange e e') (I.extendCoordChange e e').source y) := by
  set φ := I.extendCoordChange e e'
  have hpoint :
      (e'.extend I).symm (φ y) = (e.extend I).symm y :=
    extendCoordChange_symm_apply (I := I) (e := e) (e' := e') hy
  have hderiv :
      mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y =
        (mfderivWithin 𝓘(𝕜, E) I (e'.extend I).symm (e'.extend I).target (φ y)).comp
          (fderivWithin 𝕜 φ φ.source y) := by
    simpa [φ] using
      mfderivWithin_extend_symm_coordChange_maximal
        (I := I) (e := e) (e' := e') he he' hy
  rw [coordinateExpression, coordinateExpression, hpoint, hderiv]
  ext v
  rfl

/--
%%handwave
name:
  Coordinate expression of restriction to an open subset
statement:
  In a restricted chart, the coordinate representative of a restricted form is
  the same as the ambient coordinate representative.
proof:
  Expand the two coordinate representatives and use compatibility of inverse
  restricted charts and their derivatives with the ambient chart.
-/
theorem coordinateExpression_restrictSmoothFormToOpen_subtypeRestr
    [IsManifold I ∞ M]
    (e : OpenPartialHomeomorph M H) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) (he : e ∈ atlas H M)
    (heU : e.subtypeRestr hU ∈ atlas H U)
    {A : Type a} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    {n : ℕ} (form : (x : M) → FormAt (I := I) (M := M) A n x)
    {y : E} (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    coordinateExpression (I := I) (F := A) (n := n)
      (fun x : U =>
        (form (x : M)).compContinuousLinearMap
          (mfderiv I I (fun z : U => (z : M)) x))
      (e.subtypeRestr hU) y =
    coordinateExpression (I := I) (F := A) (n := n) form e y := by
  rw [coordinateExpression, coordinateExpression]
  have hpoint : (((e.subtypeRestr hU).extend I).symm y : U) = (e.extend I).symm y :=
    subtypeRestr_extend_symm_coe (I := I) e U hU hy
  have hderiv :=
    mfderiv_subtypeVal_comp_subtypeRestr_extend_symm (I := I) e U hU he heU hy
  rw [hpoint]
  ext v
  change form ((e.extend I).symm y)
      (((mfderiv I I (fun z : U => (z : M)) (((e.subtypeRestr hU).extend I).symm y)).comp
        (mfderivWithin 𝓘(𝕜, E) I ((e.subtypeRestr hU).extend I).symm
          ((e.subtypeRestr hU).extend I).target y)) ∘ v) =
    form ((e.extend I).symm y)
      ((mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y) ∘ v)
  rw [hderiv]
  rfl

/--
%%handwave
name:
  Derivative of an inclusion between open subsets
statement:
  In compatible restricted charts for nested open subsets, the derivative of
  the inclusion composed with the smaller inverse chart equals the larger
  inverse chart derivative.
proof:
  Apply the chain rule to the inclusion after the smaller inverse chart and use
  the equality with the larger inverse chart on the smaller target.
-/
theorem mfderiv_inclusion_comp_subtypeRestr_extend_symm
    [IsManifold I 1 M]
    (e : OpenPartialHomeomorph M H) {U V : TopologicalSpace.Opens M}
    (hU : Nonempty U) (hV : Nonempty V) (hUV : U ≤ V)
    (heU : e.subtypeRestr hU ∈ atlas H U)
    (heV : e.subtypeRestr hV ∈ atlas H V)
    {y : E} (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    (mfderiv I I (TopologicalSpace.Opens.inclusion hUV)
        (((e.subtypeRestr hU).extend I).symm y)).comp
        (mfderivWithin 𝓘(𝕜, E) I ((e.subtypeRestr hU).extend I).symm
          ((e.subtypeRestr hU).extend I).target y) =
      mfderivWithin 𝓘(𝕜, E) I ((e.subtypeRestr hV).extend I).symm
        ((e.subtypeRestr hV).extend I).target y := by
  let eU : OpenPartialHomeomorph U H := e.subtypeRestr hU
  let eV : OpenPartialHomeomorph V H := e.subtypeRestr hV
  have hf : MDifferentiableWithinAt 𝓘(𝕜, E) I (eU.extend I).symm
      (eU.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) heU hy
  have hg : MDifferentiableWithinAt I I (TopologicalSpace.Opens.inclusion hUV) univ
      ((eU.extend I).symm y) := by
    simpa [mdifferentiableWithinAt_univ] using
      ((contMDiff_inclusion (I := I) (n := ∞) hUV).contMDiffAt.mdifferentiableAt
        (by simp))
  have hxs : UniqueMDiffWithinAt 𝓘(𝕜, E) (eU.extend I).target y := by
    exact ((uniqueDiffOn_extend_target (I := I) eU) y hy).uniqueMDiffWithinAt
  have hchain :=
    mfderivWithin_comp (I := 𝓘(𝕜, E)) (I' := I) (I'' := I) (x := y)
      (g := TopologicalSpace.Opens.inclusion hUV) (f := (eU.extend I).symm)
      (s := (eU.extend I).target) (u := univ) hg hf (by intro z _hz; trivial) hxs
  change mfderivWithin 𝓘(𝕜, E) I
      ((TopologicalSpace.Opens.inclusion hUV) ∘ (eU.extend I).symm)
      (eU.extend I).target y = _ at hchain
  rw [mfderivWithin_univ] at hchain
  have hcomp_eq :
      EqOn ((TopologicalSpace.Opens.inclusion hUV) ∘ (eU.extend I).symm)
        (eV.extend I).symm (eU.extend I).target := by
    intro z hz
    exact (subtypeRestr_extend_symm_of_le (I := I) e hU hV hUV hz).symm
  have hleft_eq :
      mfderivWithin 𝓘(𝕜, E) I
          ((TopologicalSpace.Opens.inclusion hUV) ∘ (eU.extend I).symm)
          (eU.extend I).target y =
        mfderivWithin 𝓘(𝕜, E) I (eV.extend I).symm
          (eU.extend I).target y :=
    mfderivWithin_congr hcomp_eq (hcomp_eq hy)
  have hVdiff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (eV.extend I).symm (eV.extend I).target y := by
    exact mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) heV
      (subtypeRestr_extend_target_mono (I := I) e hU hV hUV hy)
  have htarget_mem : (eV.extend I).target ∈ 𝓝[(eU.extend I).target] y := by
    exact Filter.mem_of_superset self_mem_nhdsWithin (by
      intro z hz
      exact subtypeRestr_extend_target_mono (I := I) e hU hV hUV hz)
  have hright_eq :
      mfderivWithin 𝓘(𝕜, E) I (eV.extend I).symm (eU.extend I).target y =
        mfderivWithin 𝓘(𝕜, E) I (eV.extend I).symm (eV.extend I).target y := by
    exact hVdiff.mfderivWithin_mono_of_mem_nhdsWithin hxs htarget_mem
  rw [hleft_eq, hright_eq] at hchain
  exact hchain.symm

/--
%%handwave
name:
  Tangent map of an open inclusion is surjective
statement:
  The derivative of the inclusion of an open subset into the ambient manifold
  is surjective on tangent spaces.
proof:
  Work in a chart around the point and factor the ambient chart derivative
  through the restricted chart derivative, whose model derivative is
  invertible.
-/
theorem mfderiv_subtypeVal_surjective
    [IsManifold I 1 M]
    (U : TopologicalSpace.Opens M) (x : U) :
    Function.Surjective (mfderiv I I (fun y : U => (y : M)) x) := by
  intro v
  let eM : OpenPartialHomeomorph M H := chartAt H (x : M)
  let hU : Nonempty U := ⟨x⟩
  let eU : OpenPartialHomeomorph U H := eM.subtypeRestr hU
  let y : E := (eU.extend I) x
  have heM : eM ∈ atlas H M := by
    simp [eM]
  have heU : eU ∈ atlas H U := by
    change (chartAt H (x : M)).subtypeRestr (⟨x⟩ : Nonempty U) ∈ atlas H U
    exact chart_mem_atlas H x
  have hxU_source : x ∈ (eU.extend I).source := by
    simp [eU, eM]
  have hyU : y ∈ (eU.extend I).target := by
    exact (eU.extend I).map_source hxU_source
  have hyM : y ∈ (eM.extend I).target :=
    subtypeRestr_extend_target_subset (I := I) eM U hU hyU
  have hsymmU : (eU.extend I).symm y = x := by
    exact (eU.extend I).left_inv hxU_source
  have hfactor :=
    mfderiv_subtypeVal_comp_subtypeRestr_extend_symm
      (I := I) eM U hU heM heU hyU
  rw [hsymmU] at hfactor
  have hamb_diff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) heM hyM
  have htarget_mem_range : (eM.extend I).target ∈ 𝓝[range I] y := by
    have htarget_mem_target :
        (eM.extend I).target ∈ 𝓝[(eM.extend I).target] y :=
      self_mem_nhdsWithin
    rw [nhdsWithin_extend_target_eq_of_mem (I := I) hyM] at htarget_mem_target
    exact htarget_mem_target
  have hunique_range : UniqueMDiffWithinAt 𝓘(𝕜, E) (range I) y := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn y (eM.extend_target_subset_range (I := I) hyM)
  have hamb_range_eq :
      mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (range I) y =
        mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y :=
    hamb_diff.mfderivWithin_mono_of_mem_nhdsWithin hunique_range htarget_mem_range
  have hinv :
      (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (range I) y).IsInvertible := by
    simpa [eM, extChartAt] using
      (isInvertible_mfderivWithin_extChartAt_symm
        (I := I) (x := (x : M)) (y := y) (by simpa [eM, extChartAt] using hyM))
  rcases hinv.surjective v with ⟨w, hw⟩
  refine ⟨mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y w, ?_⟩
  have hfirst :
      mfderiv I I (fun y : U => (y : M)) x
          (mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y w) =
        (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y) w :=
    congrArg (fun L : E →L[𝕜] TangentSpace I (x : M) => L w) hfactor
  have hsecond :
      (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y) w =
        (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (range I) y) w := by
    rw [← hamb_range_eq]
  exact hfirst.trans (hsecond.trans hw)

/--
%%handwave
name:
  Tangent map of an open inclusion is injective
statement:
  The derivative of the inclusion of an open subset into the ambient manifold
  is injective on tangent spaces.
proof:
  Factor the derivative through restricted and ambient chart derivatives and
  use invertibility of the model chart derivatives to force a zero tangent
  vector.
-/
theorem mfderiv_subtypeVal_injective
    [IsManifold I 1 M]
    (U : TopologicalSpace.Opens M) (x : U) :
    Function.Injective (mfderiv I I (fun y : U => (y : M)) x) := by
  let L : TangentSpace I x →L[𝕜] TangentSpace I (x : M) :=
    mfderiv I I (fun y : U => (y : M)) x
  suffices hzero : ∀ z, L z = 0 → z = 0 by
    intro z z' hz
    rw [← sub_eq_zero]
    exact hzero (z - z') (by simpa [L, map_sub] using sub_eq_zero.mpr hz)
  intro z hz
  let eM : OpenPartialHomeomorph M H := chartAt H (x : M)
  let hU : Nonempty U := ⟨x⟩
  let eU : OpenPartialHomeomorph U H := eM.subtypeRestr hU
  let y : E := (eU.extend I) x
  have heM : eM ∈ atlas H M := by
    simp [eM]
  have heU : eU ∈ atlas H U := by
    change (chartAt H (x : M)).subtypeRestr (⟨x⟩ : Nonempty U) ∈ atlas H U
    exact chart_mem_atlas H x
  have hxU_source : x ∈ (eU.extend I).source := by
    simp [eU, eM]
  have hyU : y ∈ (eU.extend I).target :=
    (eU.extend I).map_source hxU_source
  have hyM : y ∈ (eM.extend I).target :=
    subtypeRestr_extend_target_subset (I := I) eM U hU hyU
  have hsymmU : (eU.extend I).symm y = x :=
    (eU.extend I).left_inv hxU_source
  have hfactor :=
    mfderiv_subtypeVal_comp_subtypeRestr_extend_symm
      (I := I) eM U hU heM heU hyU
  rw [hsymmU] at hfactor
  have hUdiff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) heU hyU
  have hUtarget_mem_range : (eU.extend I).target ∈ 𝓝[range I] y := by
    have htarget_mem_target :
        (eU.extend I).target ∈ 𝓝[(eU.extend I).target] y :=
      self_mem_nhdsWithin
    rw [nhdsWithin_extend_target_eq_of_mem (I := I) hyU] at htarget_mem_target
    exact htarget_mem_target
  have hUunique_range : UniqueMDiffWithinAt 𝓘(𝕜, E) (range I) y := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn y (eU.extend_target_subset_range (I := I) hyU)
  have hUrange_eq :
      mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (range I) y =
        mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y :=
    hUdiff.mfderivWithin_mono_of_mem_nhdsWithin hUunique_range hUtarget_mem_range
  have hUinv_range :
      (mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (range I) y).IsInvertible := by
    simpa [eU, eM, extChartAt] using
      (isInvertible_mfderivWithin_extChartAt_symm
        (I := I) (x := x) (y := y) (by simpa [eU, eM, extChartAt] using hyU))
  have hUsurj :
      Function.Surjective
        (mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y) := by
    intro u
    rcases hUinv_range.surjective u with ⟨w, hw⟩
    rw [hUrange_eq] at hw
    exact ⟨w, hw⟩
  have hMdiff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) heM hyM
  have hMtarget_mem_range : (eM.extend I).target ∈ 𝓝[range I] y := by
    have htarget_mem_target :
        (eM.extend I).target ∈ 𝓝[(eM.extend I).target] y :=
      self_mem_nhdsWithin
    rw [nhdsWithin_extend_target_eq_of_mem (I := I) hyM] at htarget_mem_target
    exact htarget_mem_target
  have hMunique_range : UniqueMDiffWithinAt 𝓘(𝕜, E) (range I) y := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn y (eM.extend_target_subset_range (I := I) hyM)
  have hMrange_eq :
      mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (range I) y =
        mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y :=
    hMdiff.mfderivWithin_mono_of_mem_nhdsWithin hMunique_range hMtarget_mem_range
  have hMinv_range :
      (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (range I) y).IsInvertible := by
    simpa [eM, extChartAt] using
      (isInvertible_mfderivWithin_extChartAt_symm
        (I := I) (x := (x : M)) (y := y) (by simpa [eM, extChartAt] using hyM))
  have hMinj :
      Function.Injective
        (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y) := by
    intro w w' hww'
    apply hMinv_range.injective
    rw [hMrange_eq]
    exact hww'
  rcases hUsurj z with ⟨w, hw⟩
  have hMw_zero :
      (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y) w = 0 := by
    calc
      (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y) w =
          L ((mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm
            (eU.extend I).target y) w) := by
            simpa [L] using congrArg (fun T : E →L[𝕜] TangentSpace I (x : M) => T w)
              hfactor.symm
      _ = L z := by rw [hw]
      _ = 0 := hz
  have hw_zero : w = 0 := by
    apply hMinj
    rw [map_zero]
    exact hMw_zero
  rw [← hw, hw_zero, map_zero]
  rfl

/--
%%handwave
name:
  Tangent map of an open inclusion is bijective
statement:
  The derivative of the inclusion of an open subset into the ambient manifold
  is a bijection on tangent spaces.
proof:
  Combine injectivity and surjectivity of the tangent map of an open inclusion.
-/
theorem mfderiv_subtypeVal_bijective
    [IsManifold I 1 M]
    (U : TopologicalSpace.Opens M) (x : U) :
    Function.Bijective (mfderiv I I (fun y : U => (y : M)) x) :=
  ⟨mfderiv_subtypeVal_injective (I := I) U x,
    mfderiv_subtypeVal_surjective (I := I) U x⟩

/--
%%handwave
name:
  Tangent map of an open inclusion is invertible
statement:
  The derivative of the inclusion of an open subset into the ambient manifold
  is an invertible continuous linear map.
proof:
  Express the inclusion derivative as a composite of an ambient chart
  derivative with the inverse of the restricted chart derivative.
-/
theorem mfderiv_subtypeVal_isInvertible
    [IsManifold I 1 M]
    (U : TopologicalSpace.Opens M) (x : U) :
    (mfderiv I I (fun y : U => (y : M)) x).IsInvertible := by
  let L : TangentSpace I x →L[𝕜] TangentSpace I (x : M) :=
    mfderiv I I (fun y : U => (y : M)) x
  let eM : OpenPartialHomeomorph M H := chartAt H (x : M)
  let hU : Nonempty U := ⟨x⟩
  let eU : OpenPartialHomeomorph U H := eM.subtypeRestr hU
  let y : E := (eU.extend I) x
  let DU : E →L[𝕜] TangentSpace I x :=
    mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y
  let DM : E →L[𝕜] TangentSpace I (x : M) :=
    mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y
  have heM : eM ∈ atlas H M := by
    simp [eM]
  have heU : eU ∈ atlas H U := by
    change (chartAt H (x : M)).subtypeRestr (⟨x⟩ : Nonempty U) ∈ atlas H U
    exact chart_mem_atlas H x
  have hxU_source : x ∈ (eU.extend I).source := by
    simp [eU, eM]
  have hyU : y ∈ (eU.extend I).target :=
    (eU.extend I).map_source hxU_source
  have hyM : y ∈ (eM.extend I).target :=
    subtypeRestr_extend_target_subset (I := I) eM U hU hyU
  have hsymmU : (eU.extend I).symm y = x :=
    (eU.extend I).left_inv hxU_source
  have hfactor :=
    mfderiv_subtypeVal_comp_subtypeRestr_extend_symm
      (I := I) eM U hU heM heU hyU
  rw [hsymmU] at hfactor
  have hfactor' : L.comp DU = DM := by
    simpa [L, DU, DM, eU] using hfactor
  have hUdiff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) heU hyU
  have hUtarget_mem_range : (eU.extend I).target ∈ 𝓝[range I] y := by
    have htarget_mem_target :
        (eU.extend I).target ∈ 𝓝[(eU.extend I).target] y :=
      self_mem_nhdsWithin
    rw [nhdsWithin_extend_target_eq_of_mem (I := I) hyU] at htarget_mem_target
    exact htarget_mem_target
  have hUunique_range : UniqueMDiffWithinAt 𝓘(𝕜, E) (range I) y := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn y (eU.extend_target_subset_range (I := I) hyU)
  have hUrange_eq :
      mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (range I) y =
        mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y :=
    hUdiff.mfderivWithin_mono_of_mem_nhdsWithin hUunique_range hUtarget_mem_range
  have hUinv_range :
      (mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (range I) y).IsInvertible := by
    simpa [eU, eM, extChartAt] using
      (isInvertible_mfderivWithin_extChartAt_symm
        (I := I) (x := x) (y := y) (by simpa [eU, eM, extChartAt] using hyU))
  have hUinv : DU.IsInvertible := by
    change
      (mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y).IsInvertible
    rw [← hUrange_eq]
    exact hUinv_range
  have hMdiff :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y :=
    mdifferentiableWithinAt_extend_symm_of_mem_atlas (I := I) heM hyM
  have hMtarget_mem_range : (eM.extend I).target ∈ 𝓝[range I] y := by
    have htarget_mem_target :
        (eM.extend I).target ∈ 𝓝[(eM.extend I).target] y :=
      self_mem_nhdsWithin
    rw [nhdsWithin_extend_target_eq_of_mem (I := I) hyM] at htarget_mem_target
    exact htarget_mem_target
  have hMunique_range : UniqueMDiffWithinAt 𝓘(𝕜, E) (range I) y := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn y (eM.extend_target_subset_range (I := I) hyM)
  have hMrange_eq :
      mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (range I) y =
        mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y :=
    hMdiff.mfderivWithin_mono_of_mem_nhdsWithin hMunique_range hMtarget_mem_range
  have hMinv_range :
      (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (range I) y).IsInvertible := by
    simpa [eM, extChartAt] using
      (isInvertible_mfderivWithin_extChartAt_symm
        (I := I) (x := (x : M)) (y := y) (by simpa [eM, extChartAt] using hyM))
  have hMinv : DM.IsInvertible := by
    change
      (mfderivWithin 𝓘(𝕜, E) I (eM.extend I).symm (eM.extend I).target y).IsInvertible
    rw [← hMrange_eq]
    exact hMinv_range
  have hL_eq : L = DM.comp DU.inverse := by
    apply ContinuousLinearMap.ext
    intro z
    rcases hUinv.surjective z with ⟨w, hw⟩
    rw [← hw]
    calc
      L (DU w) = (L.comp DU) w := rfl
      _ = DM w := by rw [hfactor']
      _ = DM (DU.inverse (DU w)) := by rw [hUinv.inverse_apply_self]
      _ = (DM.comp DU.inverse) (DU w) := rfl
  change L.IsInvertible
  rw [hL_eq]
  exact hMinv.comp hUinv.inverse

/--
%%handwave
name:
  Coordinate expression of restriction along an open inclusion
statement:
  For nested open subsets, the coordinate representative of a form restricted
  from the larger open set to the smaller one agrees with the representative in
  the larger restricted chart.
proof:
  Expand coordinate representatives and use compatibility of inverse restricted
  charts and derivatives under inclusion.
-/
theorem coordinateExpression_restrictSmoothFormOfLE_subtypeRestr
    [IsManifold I ∞ M]
    (e : OpenPartialHomeomorph M H) {U V : TopologicalSpace.Opens M}
    (hU : Nonempty U) (hV : Nonempty V) (hUV : U ≤ V)
    (heU : e.subtypeRestr hU ∈ atlas H U)
    (heV : e.subtypeRestr hV ∈ atlas H V)
    {A : Type a} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    {n : ℕ} (form : (x : V) → FormAt (I := I) (M := V) A n x)
    {y : E} (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    coordinateExpression (I := I) (F := A) (n := n)
      (fun x : U =>
        (form (TopologicalSpace.Opens.inclusion hUV x)).compContinuousLinearMap
          (mfderiv I I (TopologicalSpace.Opens.inclusion hUV) x))
      (e.subtypeRestr hU) y =
    coordinateExpression (I := I) (F := A) (n := n) form (e.subtypeRestr hV) y := by
  rw [coordinateExpression, coordinateExpression]
  have hpoint :
      ((e.subtypeRestr hV).extend I).symm y =
        TopologicalSpace.Opens.inclusion hUV (((e.subtypeRestr hU).extend I).symm y) :=
    subtypeRestr_extend_symm_of_le (I := I) e hU hV hUV hy
  have hderiv :=
    mfderiv_inclusion_comp_subtypeRestr_extend_symm (I := I) e hU hV hUV heU heV hy
  rw [← hpoint]
  ext v
  change form (((e.subtypeRestr hV).extend I).symm y)
      (((mfderiv I I (TopologicalSpace.Opens.inclusion hUV)
        (((e.subtypeRestr hU).extend I).symm y)).comp
        (mfderivWithin 𝓘(𝕜, E) I ((e.subtypeRestr hU).extend I).symm
          ((e.subtypeRestr hU).extend I).target y)) ∘ v) =
    form (((e.subtypeRestr hV).extend I).symm y)
      ((mfderivWithin 𝓘(𝕜, E) I ((e.subtypeRestr hV).extend I).symm
        ((e.subtypeRestr hV).extend I).target y) ∘ v)
  rw [hderiv]
  rfl

end OpenSubtypeDerivative

section DeRhamComplex

variable [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M]
variable (A : Type a) [NormedAddCommGroup A] [NormedSpace 𝕜 A]

/--
Smooth differential \(n\)-forms, regarded as the \(n\)-th term of the de Rham
cochain complex.
-/
abbrev SmoothForms (n : ℕ) : Type _ :=
  SmoothDifferentialForm (I := I) (M := M) A n

variable {I A}

section SmoothRealFunctionToZeroForm

variable {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
variable {H0 : Type w} [TopologicalSpace H0]
variable {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
variable {I0 : ModelWithCorners ℝ E0 H0}

/--
%%handwave
name:
  Constant real functions are smooth
statement:
  A constant real-valued function on a smooth real manifold is smooth.
proof:
  This is the standard smoothness of constant maps.
-/
noncomputable def smoothRealConstantFunction (c : ℝ) : C^∞⟮I0, M0; ℝ⟯ where
  val := fun _ ↦ c
  property := contMDiff_const

/--
%%handwave
name:
  Constant smooth real functions evaluate constantly
statement:
  The smooth function associated to a real constant has that value at every
  point.
proof:
  This is the defining formula for the constant smooth function.
-/
@[simp]
theorem smoothRealConstantFunction_apply (c : ℝ) (x : M0) :
    smoothRealConstantFunction (I0 := I0) c x = c :=
  rfl

variable [IsManifold I0 ∞ M0]

/--
%%handwave
name:
  Smooth functions are smooth zero-forms
statement:
  A smooth real-valued function on a smooth real manifold determines a smooth
  real zero-form by viewing each value as the unique alternating map on the
  empty list of tangent vectors.
proof:
  In a chart, the coordinate representative is obtained from the chart
  representative of the function by the continuous linear identification
  between real numbers and alternating maps on no arguments.
-/
noncomputable def smoothRealFunctionToZeroForm
    (f : C^∞⟮I0, M0; ℝ⟯) : SmoothForms (I := I0) (M := M0) ℝ 0 where
  toFun := fun x ↦
    ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace I0 x) (Fin 0) (f x)
  isContMDiff := by
    intro e he
    have hemax : e ∈ IsManifold.maximalAtlas I0 ∞ M0 :=
      IsManifold.subset_maximalAtlas (I := I0) (n := ∞) he
    have hsymm :
        ContMDiffOn 𝓘(ℝ, E0) I0 ∞ (e.extend I0).symm (e.extend I0).target := by
      rw [e.extend_target' (I := I0)]
      exact contMDiffOn_extend_symm (I := I0) (n := ∞) hemax
    have hf_on :
        ContMDiffOn I0 (modelWithCornersSelf ℝ ℝ) ∞ f univ :=
      f.contMDiff.contMDiffOn
    have hscalar_m :
        ContMDiffOn 𝓘(ℝ, E0) 𝓘(ℝ, ℝ) ∞
          (fun y ↦ f ((e.extend I0).symm y)) (e.extend I0).target := by
      change
        ContMDiffOn 𝓘(ℝ, E0) (modelWithCornersSelf ℝ ℝ) ∞
          (fun y ↦ f ((e.extend I0).symm y)) (e.extend I0).target
      exact hf_on.comp hsymm (by intro y _hy; simp)
    have hscalar :
        ContDiffOn ℝ ∞
          (fun y ↦ f ((e.extend I0).symm y)) (e.extend I0).target :=
      hscalar_m.contDiffOn
    let L : ℝ →L[ℝ] ModelForm (𝕜 := ℝ) (E := E0) ℝ 0 :=
      (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E0 ℝ (Fin 0)).toContinuousLinearMap
    have hconst :
        ContDiffOn ℝ ∞
          (fun y ↦ L (f ((e.extend I0).symm y))) (e.extend I0).target := by
      simpa [L, Function.comp_def] using hscalar.continuousLinearMap_comp L
    have hCE :
        coordinateExpression (I := I0) (F := ℝ) (n := 0)
            (fun x ↦
              ContinuousAlternatingMap.constOfIsEmpty ℝ
                (TangentSpace I0 x) (Fin 0) (f x)) e =
          fun y ↦ L (f ((e.extend I0).symm y)) := by
      funext y
      ext v
      simpa [coordinateExpression, L,
        ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.constOfIsEmptyLIE_apply] using
        (ContinuousAlternatingMap.constOfIsEmpty_apply ℝ
          (TangentSpace I0 ((e.extend I0).symm y)) (Fin 0)
          (f ((e.extend I0).symm y))
          ((mfderivWithin 𝓘(ℝ, E0) I0 (e.extend I0).symm
              (e.extend I0).target y) ∘ v))
    simpa [hCE] using hconst

/--
%%handwave
name:
  The zero-form attached to a smooth function evaluates by that function
statement:
  The zero-form associated to a smooth real-valued function has, at each point,
  the constant alternating map with value equal to the value of the function.
proof:
  This is the defining formula for the associated zero-form.
-/
@[simp]
theorem smoothRealFunctionToZeroForm_toFun
    (f : C^∞⟮I0, M0; ℝ⟯) (x : M0) :
    (smoothRealFunctionToZeroForm (I0 := I0) f).toFun x =
      ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace I0 x) (Fin 0) (f x) :=
  rfl

end SmoothRealFunctionToZeroForm

omit [IsRCLikeNormedField 𝕜] in
def smoothFormsPointwiseSMul {n : ℕ}
    (f : C^∞⟮I, M; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := M) A n) :
    SmoothForms (I := I) (M := M) A n where
  toFun := fun x ↦ f x • omega.toFun x
  isContMDiff := by
    intro e he
    have hemax : e ∈ IsManifold.maximalAtlas I ∞ M :=
      IsManifold.subset_maximalAtlas (I := I) (n := ∞) he
    have hsymm :
        ContMDiffOn 𝓘(𝕜, E) I ∞ (e.extend I).symm (e.extend I).target := by
      rw [e.extend_target' (I := I)]
      exact contMDiffOn_extend_symm (I := I) (n := ∞) hemax
    have hf_on :
        ContMDiffOn I (modelWithCornersSelf 𝕜 𝕜) ∞ f univ :=
      f.contMDiff.contMDiffOn
    have hscalar_m :
        ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, 𝕜) ∞
          (fun y ↦ f ((e.extend I).symm y)) (e.extend I).target := by
      change
        ContMDiffOn 𝓘(𝕜, E) (modelWithCornersSelf 𝕜 𝕜) ∞
          (fun y ↦ f ((e.extend I).symm y)) (e.extend I).target
      exact hf_on.comp hsymm (by intro y _hy; simp)
    have hscalar :
        ContDiffOn 𝕜 ∞
          (fun y ↦ f ((e.extend I).symm y)) (e.extend I).target :=
      hscalar_m.contDiffOn
    have hCE :
        coordinateExpression (I := I) (F := A) (n := n)
            (fun x ↦ f x • omega.toFun x) e =
          fun y ↦ f ((e.extend I).symm y) •
            coordinateExpression (I := I) (F := A) (n := n) omega.toFun e y := by
      funext y
      ext v
      rfl
    simpa [hCE] using hscalar.smul (omega.isContMDiff e he)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Pointwise scalar multiplication evaluates pointwise
statement:
  Multiplying a form by a smooth function evaluates at a point as scalar
  multiplication by the value of that function.
proof:
  This is immediate from the definition of pointwise multiplication of smooth
  forms.
-/
@[simp]
theorem smoothFormsPointwiseSMul_toFun {n : ℕ}
    (f : C^∞⟮I, M; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := M) A n) (x : M) :
    (smoothFormsPointwiseSMul (I := I) (A := A) f omega).toFun x =
      f x • omega.toFun x :=
  by
    simp [smoothFormsPointwiseSMul]

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  A finite partition of unity acts as the identity on forms
statement:
  If finitely many smooth functions sum to \(1\) at every point, then the
  finite sum of the corresponding pointwise multiplication operators sends any
  smooth form to itself.
proof:
  Evaluate at a point and on tangent vectors.  The finite sum of scalar
  multiples is multiplication by the finite scalar sum, which is \(1\).
-/
theorem smoothFormsPointwiseSMul_finset_sum_eq_self_of_sum_eq_one
    {ι : Type*} {n : ℕ} (s : Finset ι)
    (χ : ι → C^∞⟮I, M; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := M) A n)
    (hsum : ∀ x : M, ∑ i ∈ s, χ i x = 1) :
    (∑ i ∈ s,
      smoothFormsPointwiseSMul (I := I) (M := M) (A := A) (χ i) omega) =
      omega := by
  apply DifferentialForm.ext
  intro x
  ext v
  have hsum_eval :
      ((∑ i ∈ s,
          smoothFormsPointwiseSMul (I := I) (M := M) (A := A) (χ i) omega).toFun x) v =
        ∑ i ∈ s, (χ i x) • omega.toFun x v := by
    classical
    clear hsum
    induction s using Finset.induction with
    | empty =>
        rfl
    | insert i s his ih =>
        rw [Finset.sum_insert his, Finset.sum_insert his]
        change
          (((smoothFormsPointwiseSMul (I := I) (M := M) (A := A) (χ i) omega).toFun x +
              (∑ j ∈ s,
                smoothFormsPointwiseSMul (I := I) (M := M) (A := A) (χ j) omega).toFun x) v) =
            (χ i x) • omega.toFun x v + ∑ j ∈ s, (χ j x) • omega.toFun x v
        rw [ContinuousAlternatingMap.add_apply, ih]
        simp [smoothFormsPointwiseSMul]
  calc
    ((∑ i ∈ s,
        smoothFormsPointwiseSMul (I := I) (M := M) (A := A) (χ i) omega).toFun x) v =
        ∑ i ∈ s, (χ i x) • omega.toFun x v := hsum_eval
    _ = ((∑ i ∈ s, χ i x) : 𝕜) • omega.toFun x v := by
      rw [Finset.sum_smul]
    _ = omega.toFun x v := by
      rw [hsum x, one_smul]

omit [IsRCLikeNormedField 𝕜] in
def smoothFunctionRestrictToOpen
    (U : TopologicalSpace.Opens M) (f : C^∞⟮I, M; 𝕜⟯) :
    C^∞⟮I, U; 𝕜⟯ where
  val := fun x ↦ f (x : M)
  property := f.contMDiff.comp (contMDiff_subtype_val (I := I) (n := ∞) (U := U))

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  Restricting a smooth function evaluates by inclusion
statement:
  The restriction of a smooth function to an open subset evaluates at a point
  as the original function evaluated at the underlying point.
proof:
  The equality is part of the definition of the restricted smooth function.
-/
@[simp]
theorem smoothFunctionRestrictToOpen_apply
    (U : TopologicalSpace.Opens M) (f : C^∞⟮I, M; 𝕜⟯) (x : U) :
    smoothFunctionRestrictToOpen (I := I) U f x = f (x : M) :=
  rfl

/-- A locally constant real function is smooth on a smooth manifold. -/
noncomputable def smoothRealFunctionOfIsLocallyConstant
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (f : M → ℝ) (hf : IsLocallyConstant f) : C^∞⟮I, M; ℝ⟯ where
  val := f
  property := by
    intro x
    exact contMDiffAt_const.congr_of_eventuallyEq (hf.eventually_eq x)

/--
%%handwave
name:
  Exterior derivative is additive
statement:
  The exterior derivative of the sum of two smooth forms is the sum of their
  exterior derivatives.
proof:
  Check the equality at each point in a chart, use the model-space additivity
  of the exterior derivative, and translate back from coordinate
  representatives.
-/
theorem exteriorDerivative_add {n : ℕ}
    (omega eta : SmoothForms (I := I) (M := M) A n) :
    exteriorDerivative (I := I) (r := ∞) (omega + eta) =
      exteriorDerivative (I := I) (r := ∞) omega +
        exteriorDerivative (I := I) (r := ∞) eta := by
  apply DifferentialForm.ext
  intro x
  let e : OpenPartialHomeomorph M H := chartAt H x
  let y : E := (extChartAt I x) x
  have he : e ∈ atlas H M := by
    simp [e]
  have hy : y ∈ (e.extend I).target := by
    simp [e, y, extChartAt]
  have hCE_add :
      coordinateExpression (I := I) (F := A) (n := n)
          (omega + eta).toFun e =
        fun z ↦
          coordinateExpression (I := I) (F := A) (n := n) omega.toFun e z +
            coordinateExpression (I := I) (F := A) (n := n) eta.toFun e z := by
    funext z
    ext v
    rfl
  have hdiff_omega :
      DifferentiableWithinAt 𝕜
        (coordinateExpression (I := I) (F := A) (n := n) omega.toFun e)
        (e.extend I).target y :=
    (omega.isContMDiff e he y hy).differentiableWithinAt (by simp)
  have hdiff_eta :
      DifferentiableWithinAt 𝕜
        (coordinateExpression (I := I) (F := A) (n := n) eta.toFun e)
        (e.extend I).target y :=
    (eta.isContMDiff e he y hy).differentiableWithinAt (by simp)
  have hleft :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (exteriorDerivative (I := I) (r := ∞) (omega + eta)).toFun e y =
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) (omega + eta).toFun e)
        (e.extend I).target y :=
    coordinateExpression_exteriorDerivativePoint (I := I)
      (r := ∞) (omega + eta) he hy
  have homega :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (exteriorDerivative (I := I) (r := ∞) omega).toFun e y =
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) omega.toFun e)
        (e.extend I).target y :=
    coordinateExpression_exteriorDerivativePoint (I := I)
      (r := ∞) omega he hy
  have heta :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (exteriorDerivative (I := I) (r := ∞) eta).toFun e y =
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) eta.toFun e)
        (e.extend I).target y :=
    coordinateExpression_exteriorDerivativePoint (I := I)
      (r := ∞) eta he hy
  have hmodel :
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) (omega + eta).toFun e)
        (e.extend I).target y =
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) omega.toFun e)
        (e.extend I).target y +
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) eta.toFun e)
        (e.extend I).target y := by
    rw [hCE_add]
    exact extDerivWithin_fun_add
      ((uniqueDiffOn_extend_target (I := I) e) y hy) hdiff_omega hdiff_eta
  have hself_left :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (exteriorDerivative (I := I) (r := ∞) (omega + eta)).toFun x
  have hself_omega :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (exteriorDerivative (I := I) (r := ∞) omega).toFun x
  have hself_eta :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (exteriorDerivative (I := I) (r := ∞) eta).toFun x
  rw [← hself_left]
  change _ =
    (exteriorDerivative (I := I) (r := ∞) omega).toFun x +
      (exteriorDerivative (I := I) (r := ∞) eta).toFun x
  rw [← hself_omega, ← hself_eta]
  simp only [e, y] at hleft homega heta hmodel ⊢
  rw [hleft, homega, heta]
  exact hmodel

/--
%%handwave
name:
  Exterior derivative commutes with scalar multiplication
statement:
  The exterior derivative of a scalar multiple of a smooth form is the same
  scalar multiple of the exterior derivative.
proof:
  Work pointwise in a chart and use the corresponding model-space homogeneity
  of the exterior derivative.
-/
theorem exteriorDerivative_smul {n : ℕ}
    (c : 𝕜) (omega : SmoothForms (I := I) (M := M) A n) :
    exteriorDerivative (I := I) (r := ∞) (c • omega) =
      c • exteriorDerivative (I := I) (r := ∞) omega := by
  apply DifferentialForm.ext
  intro x
  let e : OpenPartialHomeomorph M H := chartAt H x
  let y : E := (extChartAt I x) x
  have he : e ∈ atlas H M := by
    simp [e]
  have hy : y ∈ (e.extend I).target := by
    simp [e, y, extChartAt]
  have hCE_smul :
      coordinateExpression (I := I) (F := A) (n := n)
          (c • omega).toFun e =
        fun z ↦
          c • coordinateExpression (I := I) (F := A) (n := n) omega.toFun e z := by
    funext z
    ext v
    rfl
  have hleft :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (exteriorDerivative (I := I) (r := ∞) (c • omega)).toFun e y =
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) (c • omega).toFun e)
        (e.extend I).target y :=
    coordinateExpression_exteriorDerivativePoint (I := I)
      (r := ∞) (c • omega) he hy
  have homega :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (exteriorDerivative (I := I) (r := ∞) omega).toFun e y =
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) omega.toFun e)
        (e.extend I).target y :=
    coordinateExpression_exteriorDerivativePoint (I := I)
      (r := ∞) omega he hy
  have hmodel :
      extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) (c • omega).toFun e)
        (e.extend I).target y =
      c • extDerivWithin
        (coordinateExpression (I := I) (F := A) (n := n) omega.toFun e)
        (e.extend I).target y := by
    rw [hCE_smul]
    exact extDerivWithin_fun_smul c
      (coordinateExpression (I := I) (F := A) (n := n) omega.toFun e)
      ((uniqueDiffOn_extend_target (I := I) e) y hy)
  have hself_left :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (exteriorDerivative (I := I) (r := ∞) (c • omega)).toFun x
  have hself_omega :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (exteriorDerivative (I := I) (r := ∞) omega).toFun x
  rw [← hself_left]
  change _ = c • (exteriorDerivative (I := I) (r := ∞) omega).toFun x
  rw [← hself_omega]
  simp only [e, y] at hleft homega hmodel ⊢
  rw [hleft, homega]
  exact hmodel

/--
%%handwave
name:
  De Rham differential
statement:
  The exterior derivative is a linear map from smooth \(n\)-forms to smooth
  \((n+1)\)-forms.
-/
def deRhamDifferential (n : ℕ) :
    SmoothForms (I := I) (M := M) A n →ₗ[𝕜]
      SmoothForms (I := I) (M := M) A (n + 1) where
  toFun := fun omega ↦ exteriorDerivative (I := I) (r := ∞) omega
  map_add' := by
    intro omega eta
    exact exteriorDerivative_add (I := I) (A := A) omega eta
  map_smul' := by
    intro c omega
    exact exteriorDerivative_smul (I := I) (A := A) c omega

/--
%%handwave
name:
  Evaluation of the de Rham differential
statement:
  Applying the de Rham differential to a smooth form is applying the exterior
  derivative.
proof:
  This is the defining action of the de Rham differential.
-/
@[simp]
theorem deRhamDifferential_apply {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) A n) :
    deRhamDifferential (I := I) (A := A) n omega =
      exteriorDerivative (I := I) (r := ∞) omega :=
  rfl

/--
%%handwave
name:
  The de Rham differential squares to zero
statement:
  For every smooth \(n\)-form \(\omega\), one has \(d(d\omega)=0\).
proof:
  This is [the identity that applying the exterior derivative twice gives zero](lean:JJMath.Manifold.exteriorDerivative_exteriorDerivative_eq_zero).
tags:
  milestone
-/
theorem deRhamDifferential_comp_eq_zero {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) A n) :
    deRhamDifferential (I := I) (A := A) (n + 1)
      (deRhamDifferential (I := I) (A := A) n omega) = 0 := by
  simpa [deRhamDifferential] using
      exteriorDerivative_exteriorDerivative_eq_zero (I := I) (F := A) (n := n) omega

section SmoothRealFunctionToZeroFormDifferential

variable {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
variable {H0 : Type w} [TopologicalSpace H0]
variable {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
variable {I0 : ModelWithCorners ℝ E0 H0} [IsManifold I0 ∞ M0]

/--
%%handwave
name:
  Constant zero-forms are closed
statement:
  The exterior derivative of the zero-form associated to a constant real
  function is zero.
proof:
  In every coordinate chart the zero-form is the constant model-space function,
  whose derivative, and hence exterior derivative, is zero.
-/
@[simp]
theorem deRhamDifferential_smoothRealFunctionToZeroForm_const
    (c : ℝ) :
    deRhamDifferential (I := I0) (M := M0) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I0)
          (smoothRealConstantFunction (I0 := I0) c)) =
      0 := by
  apply DifferentialForm.ext
  intro x
  ext v
  let e : OpenPartialHomeomorph M0 H0 := chartAt H0 x
  let y : E0 := (extChartAt I0 x) x
  have hy : y ∈ (e.extend I0).target := by
    simp [e, y, extChartAt]
  have hCE :
      coordinateExpression (I := I0) (F := ℝ) (n := 0)
          (fun x : M0 =>
            ContinuousAlternatingMap.constOfIsEmpty ℝ
              (TangentSpace I0 x) (Fin 0) c) e =
        fun _ : E0 => ContinuousAlternatingMap.constOfIsEmpty ℝ E0 (Fin 0) c := by
    funext z
    ext w
    exact ContinuousAlternatingMap.constOfIsEmpty_apply ℝ
      (TangentSpace I0 (e.symm (I0.symm z))) (Fin 0) c
      ((mfderivWithin 𝓘(ℝ, E0) I0 (e.symm ∘ I0.symm)
        (range I0 ∩ I0.symm ⁻¹' e.target) z) ∘ w)
  have hconst :=
    extDerivWithin_constOfIsEmpty (𝕜 := ℝ) (E := E0) (F := ℝ)
      (f := fun _ : E0 => c) (s := (e.extend I0).target) (x := y)
      ((uniqueDiffOn_extend_target (I := I0) e) y hy)
  have hconst_apply :
      (extDerivWithin
          (fun _ : E0 => ContinuousAlternatingMap.constOfIsEmpty ℝ E0 (Fin 0) c)
          (e.extend I0).target y)
        ((mfderiv I0 𝓘(ℝ, E0) (extChartAt I0 x) x) ∘ v) = 0 := by
    simpa using congrArg
      (fun eta : E0 [⋀^Fin 1]→L[ℝ] ℝ =>
        eta ((mfderiv I0 𝓘(ℝ, E0) (extChartAt I0 x) x) ∘ v))
      hconst
  simpa [deRhamDifferential, exteriorDerivative, exteriorDerivativePoint,
    smoothRealFunctionToZeroForm, smoothRealConstantFunction, e, y, hCE] using hconst_apply

/--
%%handwave
name:
  Exterior differentiation depends only on the germ
statement:
  If smooth \(n\)-forms \(\omega\) and \(\eta\) agree on a neighborhood of
  \(x\), then \(d\omega(x)=d\eta(x)\).
proof:
  Pull both forms into a chart at \(x\).  Their coordinate expressions agree
  near the chart point, so their within-set exterior derivatives agree there;
  composing with the chart tangent map preserves the equality.
-/
theorem deRhamDifferential_toFun_eq_of_eventuallyEq
    {I : ModelWithCorners ℝ E0 H0} [IsManifold I ∞ M0]
    {n : ℕ} (omega eta : SmoothForms (I := I) (M := M0) ℝ n) {x : M0}
    (hlocal : ∀ᶠ y in nhds x, omega.toFun y = eta.toFun y) :
    (deRhamDifferential (I := I) (M := M0) (A := ℝ) n omega).toFun x =
      (deRhamDifferential (I := I) (M := M0) (A := ℝ) n eta).toFun x := by
  let e : OpenPartialHomeomorph M0 H0 := chartAt H0 x
  let y : E0 := (extChartAt I x) x
  have hy : y ∈ (e.extend I).target := by
    simp [e, y, extChartAt]
  have hsymm_y : (e.extend I).symm y = x := by
    simp [e, y, extChartAt]
  have hsymm :
      Filter.Tendsto (e.extend I).symm
        (nhdsWithin y (e.extend I).target) (nhds x) := by
    have hcontinuous :
        ContinuousWithinAt (e.extend I).symm (e.extend I).target y :=
      e.continuousOn_extend_symm (I := I) y hy
    rw [← hsymm_y]
    exact hcontinuous.tendsto
  have hcoordinate :
      coordinateExpression (I := I) (F := ℝ) (n := n) omega.toFun e =ᶠ[
        nhdsWithin y (e.extend I).target]
      coordinateExpression (I := I) (F := ℝ) (n := n) eta.toFun e := by
    filter_upwards [hsymm hlocal] with z hz
    simp only [coordinateExpression]
    rw [hz]
  change
    (extDerivWithin
      (coordinateExpression (I := I) (F := ℝ) (n := n) omega.toFun e)
      (e.extend I).target y).compContinuousLinearMap
        (mfderiv I (modelWithCornersSelf ℝ E0) (extChartAt I x) x) =
      (extDerivWithin
        (coordinateExpression (I := I) (F := ℝ) (n := n) eta.toFun e)
        (e.extend I).target y).compContinuousLinearMap
          (mfderiv I (modelWithCornersSelf ℝ E0) (extChartAt I x) x)
  rw [hcoordinate.extDerivWithin_eq_of_mem hy]

/--
%%handwave
name:
  A locally constant zero-form has zero exterior derivative
statement:
  If \(f:M\to\mathbb R\) is locally constant, then the smooth zero-form
  associated to \(f\) satisfies \(df=0\).
proof:
  Near each point \(x\), the function equals the constant \(f(x)\).
  Exterior differentiation depends only on this germ, and the differential of
  a constant zero-form is zero.
-/
theorem deRhamDifferential_locallyConstant_zeroForm_eq_zero
    (f : M0 → ℝ) (hf : IsLocallyConstant f) :
    deRhamDifferential (I := I0) (M := M0) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I0)
          (smoothRealFunctionOfIsLocallyConstant I0 f hf)) = 0 := by
  apply DifferentialForm.ext
  intro x
  have heq : ∀ᶠ y in nhds x,
      (smoothRealFunctionToZeroForm (I0 := I0)
        (smoothRealFunctionOfIsLocallyConstant I0 f hf)).toFun y =
      (smoothRealFunctionToZeroForm (I0 := I0)
        (smoothRealConstantFunction (I0 := I0) (f x))).toFun y := by
    filter_upwards [hf.eventually_eq x] with y hy
    simp [smoothRealFunctionOfIsLocallyConstant, hy]
  rw [deRhamDifferential_toFun_eq_of_eventuallyEq
    (I := I0)
    (smoothRealFunctionToZeroForm (I0 := I0)
      (smoothRealFunctionOfIsLocallyConstant I0 f hf))
    (smoothRealFunctionToZeroForm (I0 := I0)
      (smoothRealConstantFunction (I0 := I0) (f x))) heq]
  rw [deRhamDifferential_smoothRealFunctionToZeroForm_const]

end SmoothRealFunctionToZeroFormDifferential

/--
Closed smooth \(n\)-forms.
-/
def DeRhamClosedForms (n : ℕ) :
    Submodule 𝕜 (SmoothForms (I := I) (M := M) A n) :=
  LinearMap.ker (deRhamDifferential (I := I) (A := A) n)

section ConstantDegreeZeroClass

variable {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
variable {H0 : Type w} [TopologicalSpace H0]
variable {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
variable {I0 : ModelWithCorners ℝ E0 H0} [IsManifold I0 ∞ M0]

/-- A real constant, regarded as a closed smooth zero-form. -/
noncomputable def deRhamConstantZeroClosedForm (c : ℝ) :
    DeRhamClosedForms (I := I0) (M := M0) (A := ℝ) 0 :=
  ⟨smoothRealFunctionToZeroForm (I0 := I0)
      (smoothRealConstantFunction (I0 := I0) c),
    deRhamDifferential_smoothRealFunctionToZeroForm_const (I0 := I0) c⟩

end ConstantDegreeZeroClass

/--
Exact smooth \(n\)-forms.  In degree zero this is the zero submodule.
-/
def DeRhamExactForms : (n : ℕ) →
    Submodule 𝕜 (SmoothForms (I := I) (M := M) A n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (deRhamDifferential (I := I) (A := A) n)

/--
%%handwave
name:
  Exact forms are closed
statement:
  Every exact smooth form is closed.
proof:
  In degree zero, exactness means the form is zero.  In positive degree, write
  the form as \(d\eta\) and use \(d^2=0\).
-/
theorem deRhamExactForms_le_closedForms (n : ℕ) :
    DeRhamExactForms (I := I) (M := M) (A := A) n ≤
      DeRhamClosedForms (I := I) (M := M) (A := A) n := by
  cases n with
  | zero =>
      intro omega homega
      simp [DeRhamExactForms] at homega
      rw [homega]
      simp [DeRhamClosedForms]
  | succ n =>
      rw [DeRhamExactForms, DeRhamClosedForms]
      intro omega homega
      rcases homega with ⟨eta, rfl⟩
      exact deRhamDifferential_comp_eq_zero (I := I) (A := A) eta

/--
Exact forms considered as a submodule of the closed forms.
-/
def DeRhamExactClosedForms (n : ℕ) :
    Submodule 𝕜 (DeRhamClosedForms (I := I) (M := M) (A := A) n) :=
  (DeRhamExactForms (I := I) (M := M) (A := A) n).comap
    (Submodule.subtype (DeRhamClosedForms (I := I) (M := M) (A := A) n))

/--
%%handwave
name:
  De Rham cohomology
statement:
  The degree \(n\) de Rham cohomology of a smooth manifold is the quotient
  of closed \(n\)-forms by exact \(n\)-forms.
-/
abbrev DeRhamCohomology (n : ℕ) : Type _ :=
  DeRhamClosedForms (I := I) (M := M) (A := A) n ⧸
    DeRhamExactClosedForms (I := I) (M := M) (A := A) n

section ConstantDegreeZeroClass

variable {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
variable {H0 : Type w} [TopologicalSpace H0]
variable {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
variable {I0 : ModelWithCorners ℝ E0 H0} [IsManifold I0 ∞ M0]

/-- The degree-zero de Rham cohomology class represented by a real constant. -/
noncomputable def deRhamConstantH0Class (c : ℝ) :
    DeRhamCohomology (I := I0) (M := M0) (A := ℝ) 0 :=
  (DeRhamExactClosedForms (I := I0) (M := M0) (A := ℝ) 0).mkQ
    (deRhamConstantZeroClosedForm (I0 := I0) (M0 := M0) c)

/--
%%handwave
name:
  Distinct constants give distinct degree-zero classes
statement:
  On a nonempty smooth real manifold, the map from real constants to
  degree-zero de Rham cohomology is injective.
proof:
  Exact zero-forms vanish.  Thus equality of two constant cohomology classes
  makes the constant zero-forms equal; evaluation at any point recovers the
  two real constants.
-/
theorem deRhamConstantH0Class_injective [Nonempty M0] :
    Function.Injective (deRhamConstantH0Class (I0 := I0) (M0 := M0)) := by
  intro c d h
  simp only [deRhamConstantH0Class, Submodule.mkQ_apply] at h
  rw [Submodule.Quotient.eq] at h
  have hzero :
      deRhamConstantZeroClosedForm (I0 := I0) (M0 := M0) c -
          deRhamConstantZeroClosedForm (I0 := I0) (M0 := M0) d = 0 := by
    simpa [DeRhamExactClosedForms, DeRhamExactForms] using h
  have heq :
      deRhamConstantZeroClosedForm (I0 := I0) (M0 := M0) c =
        deRhamConstantZeroClosedForm (I0 := I0) (M0 := M0) d :=
    sub_eq_zero.mp hzero
  let x : M0 := Classical.choice (inferInstance : Nonempty M0)
  have hx := congrArg
    (fun omega : DeRhamClosedForms (I := I0) (M := M0) (A := ℝ) 0 =>
      omega.1.toFun x (fun i : Fin 0 => nomatch i)) heq
  simpa [deRhamConstantZeroClosedForm] using hx

end ConstantDegreeZeroClass

instance deRhamCohomologyAddCommGroup (n : ℕ) :
    AddCommGroup (DeRhamCohomology (I := I) (M := M) (A := A) n) :=
  inferInstance

instance deRhamCohomologyModule (n : ℕ) :
    Module 𝕜 (DeRhamCohomology (I := I) (M := M) (A := A) n) :=
  inferInstance

section Restriction

variable (U : TopologicalSpace.Opens M)

/-
Pulling a smooth differential form back along the inclusion of an open
submanifold gives a smooth differential form.
-/
omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Restriction to an open subset is smooth
statement:
  Pulling a smooth form back along the inclusion of an open subset gives a
  smooth form on that open subset.
proof:
  In a restricted chart, identify the coordinate representative with the
  ambient coordinate representative restricted to a smaller target.
-/
theorem isContMDiffForm_restrictSmoothFormToOpen {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) A n) :
    IsContMDiffForm (I := I) (M := U) (F := A) (n := n) ∞
      (fun x ↦
        (omega.toFun (x : M)).compContinuousLinearMap
          (mfderiv I I (fun y : U ↦ (y : M)) x)) := by
  intro e he
  have hU : Nonempty U := by
    change e ∈
      (⋃ x : U, ({(chartAt H (x : M)).subtypeRestr ⟨x⟩} :
        Set (OpenPartialHomeomorph U H))) at he
    rw [Set.mem_iUnion] at he
    rcases he with ⟨x, _hx⟩
    exact ⟨x⟩
  rcases TopologicalSpace.Opens.chart_eq hU he with ⟨x, rfl⟩
  let eM : OpenPartialHomeomorph M H := chartAt H (x : M)
  have heM : eM ∈ atlas H M := by
    simp [eM]
  have heU : eM.subtypeRestr hU ∈ atlas H U := by
    simpa [eM] using he
  have hsubset :
      ((eM.subtypeRestr hU).extend I).target ⊆ (eM.extend I).target := by
    intro y hy
    exact subtypeRestr_extend_target_subset (I := I) eM U hU hy
  refine ((omega.isContMDiff eM heM).mono hsubset).congr ?_
  intro y hy
  simpa [eM] using
    coordinateExpression_restrictSmoothFormToOpen_subtypeRestr
      (I := I) eM U hU heM heU omega.toFun hy

/-- Restriction of a smooth form on a manifold to an open subset. -/
def restrictSmoothFormToOpen {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) A n) :
    SmoothForms (I := I) (M := U) A n where
  toFun := fun x ↦
    (omega.toFun (x : M)).compContinuousLinearMap
      (mfderiv I I (fun y : U ↦ (y : M)) x)
  isContMDiff :=
    isContMDiffForm_restrictSmoothFormToOpen (I := I) (A := A) U omega

/-- Restriction of smooth forms to an open subset, as a linear map. -/
def restrictSmoothFormsToOpen (n : ℕ) :
    SmoothForms (I := I) (M := M) A n →ₗ[𝕜]
      SmoothForms (I := I) (M := U) A n where
  toFun := restrictSmoothFormToOpen (I := I) (A := A) U
  map_add' := by
    intro omega eta
    ext x v
    rfl
  map_smul' := by
    intro c omega
    ext x v
    rfl

/--
%%handwave
name:
  Exterior derivative commutes with open restriction
statement:
  Restricting a smooth form to an open subset and then applying \(d\) gives the
  same result as applying \(d\) first and then restricting.
proof:
  Compare both forms pointwise in a restricted chart; the coordinate
  representatives agree near the point, so their model exterior derivatives
  agree.
-/
theorem deRhamDifferential_restrictSmoothFormsToOpen {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) A n) :
    deRhamDifferential (I := I) (M := U) (A := A) n
        (restrictSmoothFormsToOpen (I := I) (A := A) U n omega) =
      restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1)
        (deRhamDifferential (I := I) (M := M) (A := A) n omega) := by
  apply DifferentialForm.ext
  intro x
  let hU : Nonempty U := ⟨x⟩
  let eM : OpenPartialHomeomorph M H := chartAt H (x : M)
  let eU : OpenPartialHomeomorph U H := eM.subtypeRestr hU
  let y : E := (eU.extend I) x
  have heM : eM ∈ atlas H M := by
    simp [eM]
  have heU : eU ∈ atlas H U := by
    change chartAt H x ∈ atlas H U
    exact chart_mem_atlas H x
  have hx_source : x ∈ (eU.extend I).source := by
    simp [eU, eM]
  have hyU : y ∈ (eU.extend I).target := by
    exact (eU.extend I).map_source hx_source
  have hyM : y ∈ (eM.extend I).target :=
    subtypeRestr_extend_target_subset (I := I) eM U hU hyU
  let CEU : E → ModelForm (𝕜 := 𝕜) (E := E) A n :=
    coordinateExpression (I := I) (F := A) (n := n)
      (restrictSmoothFormsToOpen (I := I) (A := A) U n omega).toFun eU
  let CEM : E → ModelForm (𝕜 := 𝕜) (E := E) A n :=
    coordinateExpression (I := I) (F := A) (n := n) omega.toFun eM
  have hleft :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (deRhamDifferential (I := I) (M := U) (A := A) n
          (restrictSmoothFormsToOpen (I := I) (A := A) U n omega)).toFun eU y =
      extDerivWithin CEU (eU.extend I).target y := by
    simpa [deRhamDifferential, CEU] using
      coordinateExpression_exteriorDerivativePoint (I := I) (r := ∞)
        (restrictSmoothFormsToOpen (I := I) (A := A) U n omega) heU hyU
  have hCE_eq : EqOn CEU CEM (eU.extend I).target := by
    intro z hz
    simpa [CEU, CEM, restrictSmoothFormsToOpen, restrictSmoothFormToOpen, eU] using
      coordinateExpression_restrictSmoothFormToOpen_subtypeRestr
        (I := I) eM U hU heM heU omega.toFun hz
  have hcongr :
      extDerivWithin CEU (eU.extend I).target y =
        extDerivWithin CEM (eU.extend I).target y :=
    extDerivWithin_congr' hCE_eq hyU
  have hdiff_small : DifferentiableWithinAt 𝕜 CEM (eU.extend I).target y := by
    exact ((omega.isContMDiff eM heM y hyM).differentiableWithinAt (by simp)).mono
      (by intro z hz; exact subtypeRestr_extend_target_subset (I := I) eM U hU hz)
  have hset :
      extDerivWithin CEM (eM.extend I).target y =
        extDerivWithin CEM (eU.extend I).target y := by
    have hderiv_set :
        fderivWithin 𝕜 CEM (eM.extend I).target y =
          fderivWithin 𝕜 CEM (eU.extend I).target y :=
      fderivWithin_of_mem_nhdsWithin
        (subtypeRestr_extend_target_mem_nhdsWithin (I := I) eM U hU hyU)
        ((uniqueDiffOn_extend_target (I := I) eM) y hyM) hdiff_small
    rw [extDerivWithin, extDerivWithin, hderiv_set]
  have hright_ambient :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (deRhamDifferential (I := I) (M := M) (A := A) n omega).toFun eM y =
      extDerivWithin CEM (eM.extend I).target y := by
    simpa [deRhamDifferential, CEM] using
      coordinateExpression_exteriorDerivativePoint (I := I) (r := ∞) omega heM hyM
  have hright :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1)
          (deRhamDifferential (I := I) (M := M) (A := A) n omega)).toFun eU y =
      extDerivWithin CEM (eM.extend I).target y := by
    change coordinateExpression (I := I) (F := A) (n := n + 1)
      (fun x : U =>
        ((deRhamDifferential (I := I) (M := M) (A := A) n omega).toFun (x : M)).compContinuousLinearMap
          (mfderiv I I (fun z : U => (z : M)) x)) eU y = _
    rw [coordinateExpression_restrictSmoothFormToOpen_subtypeRestr
        (I := I) eM U hU heM heU
        (deRhamDifferential (I := I) (M := M) (A := A) n omega).toFun hyU]
    exact hright_ambient
  have hcoords :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (deRhamDifferential (I := I) (M := U) (A := A) n
          (restrictSmoothFormsToOpen (I := I) (A := A) U n omega)).toFun eU y =
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1)
          (deRhamDifferential (I := I) (M := M) (A := A) n omega)).toFun eU y := by
    rw [hleft, hright, hcongr]
    exact hset.symm
  have hself_left :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (deRhamDifferential (I := I) (M := U) (A := A) n
        (restrictSmoothFormsToOpen (I := I) (A := A) U n omega)).toFun x
  have hself_right :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1)
        (deRhamDifferential (I := I) (M := M) (A := A) n omega)).toFun x
  rw [← hself_left, ← hself_right]
  simpa [eU, eM, y, extChartAt] using hcoords

/-- Restriction sends closed forms on a manifold to closed forms on an open subset. -/
def deRhamClosedFormsRestrictionToOpen (n : ℕ) :
    DeRhamClosedForms (I := I) (M := M) (A := A) n →ₗ[𝕜]
      DeRhamClosedForms (I := I) (M := U) (A := A) n where
  toFun := fun omega ↦
    ⟨restrictSmoothFormsToOpen (I := I) (A := A) U n omega.1, by
      change
        deRhamDifferential (I := I) (M := U) (A := A) n
            (restrictSmoothFormsToOpen (I := I) (A := A) U n omega.1) = 0
      rw [deRhamDifferential_restrictSmoothFormsToOpen (I := I) (A := A) U]
      rw [omega.2]
      simp⟩
  map_add' := by
    intro omega eta
    apply Subtype.ext
    exact (restrictSmoothFormsToOpen (I := I) (A := A) U n).map_add omega.1 eta.1
  map_smul' := by
    intro c omega
    apply Subtype.ext
    exact (restrictSmoothFormsToOpen (I := I) (A := A) U n).map_smul c omega.1

/--
%%handwave
name:
  Open restriction preserves exact closed forms
statement:
  Restricting a closed exact form to an open subset gives an exact closed form
  on that open subset.
proof:
  In degree zero this follows from the zero definition of exact forms.  In
  positive degree, restrict a primitive and use compatibility of \(d\) with
  restriction.
-/
theorem deRhamClosedFormsRestrictionToOpen_exact (n : ℕ) :
    DeRhamExactClosedForms (I := I) (M := M) (A := A) n ≤
      (DeRhamExactClosedForms (I := I) (M := U) (A := A) n).comap
        (deRhamClosedFormsRestrictionToOpen (I := I) (A := A) U n) := by
  intro omega homega
  change
    (deRhamClosedFormsRestrictionToOpen (I := I) (A := A) U n omega).1 ∈
      DeRhamExactForms (I := I) (M := U) (A := A) n
  change omega.1 ∈ DeRhamExactForms (I := I) (M := M) (A := A) n at homega
  cases n with
  | zero =>
      simp [DeRhamExactForms] at homega ⊢
      rw [homega]
      rfl
  | succ n =>
      rw [DeRhamExactForms] at homega ⊢
      rcases homega with ⟨eta, heta⟩
      refine ⟨restrictSmoothFormsToOpen (I := I) (A := A) U n eta, ?_⟩
      rw [deRhamDifferential_restrictSmoothFormsToOpen (I := I) (A := A) U]
      rw [heta]
      rfl

/-- The induced restriction map on de Rham cohomology. -/
def deRhamCohomologyRestrictionToOpen (n : ℕ) :
    DeRhamCohomology (I := I) (M := M) (A := A) n →ₗ[𝕜]
      DeRhamCohomology (I := I) (M := U) (A := A) n :=
  (DeRhamExactClosedForms (I := I) (M := M) (A := A) n).mapQ
    (DeRhamExactClosedForms (I := I) (M := U) (A := A) n)
    (deRhamClosedFormsRestrictionToOpen (I := I) (A := A) U n)
    (deRhamClosedFormsRestrictionToOpen_exact (I := I) (A := A) U n)

variable {U}
variable {V W : TopologicalSpace.Opens M}

/-
Pulling a smooth differential form back along an inclusion of open
submanifolds gives a smooth differential form.
-/
omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Restriction along an open inclusion is smooth
statement:
  Pulling a smooth form back along an inclusion of open subsets gives a smooth
  form on the smaller open subset.
proof:
  In compatible restricted charts, identify the coordinate representative on
  the smaller open subset with the representative on the larger one.
-/
theorem isContMDiffForm_restrictSmoothFormOfLE (hWV : W ≤ V) {n : ℕ}
    (omega : SmoothForms (I := I) (M := V) A n) :
    IsContMDiffForm (I := I) (M := W) (F := A) (n := n) ∞
      (fun x ↦
        (omega.toFun (TopologicalSpace.Opens.inclusion hWV x)).compContinuousLinearMap
          (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x)) := by
  intro e he
  have hW : Nonempty W := by
    change e ∈
      (⋃ x : W, ({(chartAt H (x : M)).subtypeRestr ⟨x⟩} :
        Set (OpenPartialHomeomorph W H))) at he
    rw [Set.mem_iUnion] at he
    rcases he with ⟨x, _hx⟩
    exact ⟨x⟩
  rcases TopologicalSpace.Opens.chart_eq hW he with ⟨x, rfl⟩
  let hV : Nonempty V := ⟨TopologicalSpace.Opens.inclusion hWV x⟩
  let eM : OpenPartialHomeomorph M H := chartAt H (x : M)
  have heW : eM.subtypeRestr hW ∈ atlas H W := by
    simpa [eM] using he
  have heV : eM.subtypeRestr hV ∈ atlas H V := by
    dsimp [eM, hV]
    change chartAt H (TopologicalSpace.Opens.inclusion hWV x) ∈ atlas H V
    exact chart_mem_atlas H (TopologicalSpace.Opens.inclusion hWV x)
  have hsubset :
      ((eM.subtypeRestr hW).extend I).target ⊆ ((eM.subtypeRestr hV).extend I).target := by
    intro y hy
    exact subtypeRestr_extend_target_mono (I := I) eM hW hV hWV hy
  refine ((omega.isContMDiff (eM.subtypeRestr hV) heV).mono hsubset).congr ?_
  intro y hy
  simpa [eM] using
    coordinateExpression_restrictSmoothFormOfLE_subtypeRestr
      (I := I) eM hW hV hWV heW heV omega.toFun hy

/-- Restriction of smooth forms along an inclusion of open subsets. -/
def restrictSmoothFormOfLE (hWV : W ≤ V) {n : ℕ}
    (omega : SmoothForms (I := I) (M := V) A n) :
    SmoothForms (I := I) (M := W) A n where
  toFun := fun x ↦
    (omega.toFun (TopologicalSpace.Opens.inclusion hWV x)).compContinuousLinearMap
      (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x)
  isContMDiff :=
    isContMDiffForm_restrictSmoothFormOfLE (I := I) (A := A) hWV omega

/-- Restriction of smooth forms along an inclusion of open subsets, as a linear map. -/
def restrictSmoothFormsOfLE (hWV : W ≤ V) (n : ℕ) :
    SmoothForms (I := I) (M := V) A n →ₗ[𝕜]
      SmoothForms (I := I) (M := W) A n where
  toFun := restrictSmoothFormOfLE (I := I) (A := A) hWV
  map_add' := by
    intro omega eta
    ext x v
    rfl
  map_smul' := by
    intro c omega
    ext x v
    rfl

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Transitivity of restriction for smooth forms
statement:
  If \(W\subseteq V\subseteq U\) are open subsets and
  \(\omega\in\Omega^n(U;A)\), then
  \[
    (\omega|_V)|_W=\omega|_W.
  \]
proof:
  Evaluate both forms at \(x\in W\).  The inclusions have the same composite,
  and the manifold chain rule identifies the composite of their derivatives
  with the derivative of the direct inclusion, so the two pullbacks agree.
-/
theorem restrictSmoothFormsOfLE_comp
    {U V W : TopologicalSpace.Opens M} (hVU : V ≤ U) (hWV : W ≤ V)
    (n : ℕ) (omega : SmoothForms (I := I) (M := U) A n) :
    restrictSmoothFormsOfLE (I := I) (A := A) hWV n
        (restrictSmoothFormsOfLE (I := I) (A := A) hVU n omega) =
      restrictSmoothFormsOfLE (I := I) (A := A) (hWV.trans hVU) n omega := by
  apply DifferentialForm.ext
  intro x
  ext v
  change
    ((omega.toFun (TopologicalSpace.Opens.inclusion hVU
        (TopologicalSpace.Opens.inclusion hWV x))).compContinuousLinearMap
        (mfderiv I I (TopologicalSpace.Opens.inclusion hVU)
          (TopologicalSpace.Opens.inclusion hWV x))).compContinuousLinearMap
        (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x) v =
      (omega.toFun
        (TopologicalSpace.Opens.inclusion (hWV.trans hVU) x)).compContinuousLinearMap
        (mfderiv I I
          (TopologicalSpace.Opens.inclusion (hWV.trans hVU)) x) v
  have hpoint :
      TopologicalSpace.Opens.inclusion hVU
          (TopologicalSpace.Opens.inclusion hWV x) =
        TopologicalSpace.Opens.inclusion (hWV.trans hVU) x := rfl
  rw [hpoint]
  have hderiv :
      (mfderiv I I (TopologicalSpace.Opens.inclusion hVU)
          (TopologicalSpace.Opens.inclusion hWV x)).comp
        (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x) =
      mfderiv I I
        (TopologicalSpace.Opens.inclusion (hWV.trans hVU)) x := by
    have h :=
      mfderiv_comp (I := I) (I' := I) (I'' := I) (x := x)
        (g := TopologicalSpace.Opens.inclusion hVU)
        (f := TopologicalSpace.Opens.inclusion hWV)
        (((contMDiff_inclusion (I := I) (n := ∞) hVU)).contMDiffAt.mdifferentiableAt
          (by simp))
        (((contMDiff_inclusion (I := I) (n := ∞) hWV)).contMDiffAt.mdifferentiableAt
          (by simp))
    change mfderiv I I
        (TopologicalSpace.Opens.inclusion (hWV.trans hVU)) x = _ at h
    exact h.symm
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [← hderiv]
  rfl

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Restriction commutes with pointwise scalar multiplication
statement:
  If \(W\subset V\) are open subsets, restricting the product of a form on
  \(V\) with a smooth scalar function restricted from the ambient manifold is
  the same as multiplying the restricted form on \(W\) by the scalar function
  restricted directly to \(W\).
proof:
  Both forms have the same pointwise value: the scalar is evaluated at the
  underlying ambient point and the form is pulled back along the inclusion.
-/
theorem restrictSmoothFormsOfLE_smoothFormsPointwiseSMul
    {W V : TopologicalSpace.Opens M} (hWV : W ≤ V) {n : ℕ}
    (χ : C^∞⟮I, M; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := V) A n) :
    restrictSmoothFormsOfLE (I := I) (A := A) hWV n
        (smoothFormsPointwiseSMul (I := I) (M := V) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := M) V χ) omega) =
      smoothFormsPointwiseSMul (I := I) (M := W) (A := A)
        (smoothFunctionRestrictToOpen (I := I) (M := M) W χ)
        (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega) := by
  apply DifferentialForm.ext
  intro x
  ext v
  simp [restrictSmoothFormsOfLE, restrictSmoothFormOfLE, smoothFormsPointwiseSMul,
    smoothFunctionRestrictToOpen, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply]

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  A finite cutoff sum restricts to the identity when the scalars sum to one
statement:
  If \(W\subset V\) are open subsets and finitely many global smooth functions
  sum to \(1\) on \(W\), then the sum of the restrictions to \(W\) of their
  products with a form on \(V\) is the restriction of the form.
proof:
  Restriction commutes with pointwise scalar multiplication, so the left side is
  the finite sum of pointwise products on \(W\).  The finite scalar sum is \(1\)
  on \(W\), hence [the finite sum acts as the identity](lean:JJMath.Manifold.smoothFormsPointwiseSMul_finset_sum_eq_self_of_sum_eq_one).
-/
theorem restrictSmoothFormsOfLE_smoothFormsPointwiseSMul_finset_sum_eq_self_of_sum_eq_one
    {W V : TopologicalSpace.Opens M} (hWV : W ≤ V) {n : ℕ}
    {ι : Type*} (s : Finset ι)
    (χ : ι → C^∞⟮I, M; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := V) A n)
    (hsum : ∀ x : W, ∑ i ∈ s, χ i (x : M) = 1) :
    (∑ i ∈ s,
      restrictSmoothFormsOfLE (I := I) (A := A) hWV n
        (smoothFormsPointwiseSMul (I := I) (M := V) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := M) V (χ i)) omega)) =
      restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega := by
  have hsum' :
      ∀ x : W,
        ∑ i ∈ s,
          smoothFunctionRestrictToOpen (I := I) (M := M) W (χ i) x = 1 := by
    intro x
    simpa using hsum x
  calc
    (∑ i ∈ s,
      restrictSmoothFormsOfLE (I := I) (A := A) hWV n
        (smoothFormsPointwiseSMul (I := I) (M := V) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := M) V (χ i)) omega)) =
        ∑ i ∈ s,
          smoothFormsPointwiseSMul (I := I) (M := W) (A := A)
            (smoothFunctionRestrictToOpen (I := I) (M := M) W (χ i))
            (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact restrictSmoothFormsOfLE_smoothFormsPointwiseSMul
        (I := I) (M := M) (A := A) hWV (χ i) omega
    _ = restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega := by
      exact smoothFormsPointwiseSMul_finset_sum_eq_self_of_sum_eq_one
        (I := I) (M := W) (A := A) s
        (fun i => smoothFunctionRestrictToOpen (I := I) (M := M) W (χ i))
        (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega) hsum'

/--
%%handwave
name:
  Exterior derivative commutes with restriction along open inclusions
statement:
  Restricting a smooth form along an inclusion of open subsets and then
  applying \(d\) gives the same form as applying \(d\) first and then
  restricting.
proof:
  Compare coordinate representatives in compatible restricted charts and use
  that the exterior derivative only depends on the germ near the point.
-/
theorem deRhamDifferential_restrictSmoothFormsOfLE (hWV : W ≤ V) {n : ℕ}
    (omega : SmoothForms (I := I) (M := V) A n) :
    deRhamDifferential (I := I) (M := W) (A := A) n
        (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega) =
      restrictSmoothFormsOfLE (I := I) (A := A) hWV (n + 1)
        (deRhamDifferential (I := I) (M := V) (A := A) n omega) := by
  apply DifferentialForm.ext
  intro x
  let hW : Nonempty W := ⟨x⟩
  let hV : Nonempty V := ⟨TopologicalSpace.Opens.inclusion hWV x⟩
  let eM : OpenPartialHomeomorph M H := chartAt H (x : M)
  let eW : OpenPartialHomeomorph W H := eM.subtypeRestr hW
  let eV : OpenPartialHomeomorph V H := eM.subtypeRestr hV
  let y : E := (eW.extend I) x
  have heW : eW ∈ atlas H W := by
    change chartAt H x ∈ atlas H W
    exact chart_mem_atlas H x
  have heV : eV ∈ atlas H V := by
    dsimp [eV, eM, hV]
    change chartAt H (TopologicalSpace.Opens.inclusion hWV x) ∈ atlas H V
    exact chart_mem_atlas H (TopologicalSpace.Opens.inclusion hWV x)
  have hx_source : x ∈ (eW.extend I).source := by
    simp [eW, eM]
  have hyW : y ∈ (eW.extend I).target := by
    exact (eW.extend I).map_source hx_source
  have hyV : y ∈ (eV.extend I).target :=
    subtypeRestr_extend_target_mono (I := I) eM hW hV hWV hyW
  let CEW : E → ModelForm (𝕜 := 𝕜) (E := E) A n :=
    coordinateExpression (I := I) (F := A) (n := n)
      (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega).toFun eW
  let CEV : E → ModelForm (𝕜 := 𝕜) (E := E) A n :=
    coordinateExpression (I := I) (F := A) (n := n) omega.toFun eV
  have hleft :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (deRhamDifferential (I := I) (M := W) (A := A) n
          (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega)).toFun eW y =
      extDerivWithin CEW (eW.extend I).target y := by
    simpa [deRhamDifferential, CEW] using
      coordinateExpression_exteriorDerivativePoint (I := I) (r := ∞)
        (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega) heW hyW
  have hCE_eq : EqOn CEW CEV (eW.extend I).target := by
    intro z hz
    simpa [CEW, CEV, restrictSmoothFormsOfLE, restrictSmoothFormOfLE, eW, eV] using
      coordinateExpression_restrictSmoothFormOfLE_subtypeRestr
        (I := I) eM hW hV hWV heW heV omega.toFun hz
  have hcongr :
      extDerivWithin CEW (eW.extend I).target y =
        extDerivWithin CEV (eW.extend I).target y :=
    extDerivWithin_congr' hCE_eq hyW
  have hdiff_small : DifferentiableWithinAt 𝕜 CEV (eW.extend I).target y := by
    exact ((omega.isContMDiff eV heV y hyV).differentiableWithinAt (by simp)).mono
      (by intro z hz; exact subtypeRestr_extend_target_mono (I := I) eM hW hV hWV hz)
  have hset :
      extDerivWithin CEV (eV.extend I).target y =
        extDerivWithin CEV (eW.extend I).target y := by
    have hderiv_set :
        fderivWithin 𝕜 CEV (eV.extend I).target y =
          fderivWithin 𝕜 CEV (eW.extend I).target y :=
      fderivWithin_of_mem_nhdsWithin
        (subtypeRestr_extend_target_mem_nhdsWithin_of_le (I := I) eM hW hV hWV hyW)
        ((uniqueDiffOn_extend_target (I := I) eV) y hyV) hdiff_small
    rw [extDerivWithin, extDerivWithin, hderiv_set]
  have hright_ambient :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (deRhamDifferential (I := I) (M := V) (A := A) n omega).toFun eV y =
      extDerivWithin CEV (eV.extend I).target y := by
    simpa [deRhamDifferential, CEV] using
      coordinateExpression_exteriorDerivativePoint (I := I) (r := ∞) omega heV hyV
  have hright :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (restrictSmoothFormsOfLE (I := I) (A := A) hWV (n + 1)
          (deRhamDifferential (I := I) (M := V) (A := A) n omega)).toFun eW y =
      extDerivWithin CEV (eV.extend I).target y := by
    change coordinateExpression (I := I) (F := A) (n := n + 1)
      (fun x : W =>
        ((deRhamDifferential (I := I) (M := V) (A := A) n omega).toFun
          (TopologicalSpace.Opens.inclusion hWV x)).compContinuousLinearMap
          (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x)) eW y = _
    rw [coordinateExpression_restrictSmoothFormOfLE_subtypeRestr
        (I := I) eM hW hV hWV heW heV
        (deRhamDifferential (I := I) (M := V) (A := A) n omega).toFun hyW]
    exact hright_ambient
  have hcoords :
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (deRhamDifferential (I := I) (M := W) (A := A) n
          (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega)).toFun eW y =
      coordinateExpression (I := I) (F := A) (n := n + 1)
        (restrictSmoothFormsOfLE (I := I) (A := A) hWV (n + 1)
          (deRhamDifferential (I := I) (M := V) (A := A) n omega)).toFun eW y := by
    rw [hleft, hright, hcongr]
    exact hset.symm
  have hself_left :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (deRhamDifferential (I := I) (M := W) (A := A) n
        (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega)).toFun x
  have hself_right :=
    coordinateExpression_chartAt_self (I := I) (F := A) (n := n + 1)
      (restrictSmoothFormsOfLE (I := I) (A := A) hWV (n + 1)
        (deRhamDifferential (I := I) (M := V) (A := A) n omega)).toFun x
  rw [← hself_left, ← hself_right]
  simpa [eW, eM, y, extChartAt] using hcoords

/-- Restriction along an inclusion of open subsets sends closed forms to closed forms. -/
def deRhamClosedFormsRestrictionOfLE (hWV : W ≤ V) (n : ℕ) :
    DeRhamClosedForms (I := I) (M := V) (A := A) n →ₗ[𝕜]
      DeRhamClosedForms (I := I) (M := W) (A := A) n where
  toFun := fun omega ↦
    ⟨restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega.1, by
      change
        deRhamDifferential (I := I) (M := W) (A := A) n
            (restrictSmoothFormsOfLE (I := I) (A := A) hWV n omega.1) = 0
      rw [deRhamDifferential_restrictSmoothFormsOfLE (I := I) (A := A) hWV]
      rw [omega.2]
      simp⟩
  map_add' := by
    intro omega eta
    apply Subtype.ext
    exact (restrictSmoothFormsOfLE (I := I) (A := A) hWV n).map_add omega.1 eta.1
  map_smul' := by
    intro c omega
    apply Subtype.ext
    exact (restrictSmoothFormsOfLE (I := I) (A := A) hWV n).map_smul c omega.1

/--
%%handwave
name:
  Open-inclusion restriction preserves exact closed forms
statement:
  Restricting an exact closed form along an inclusion of open subsets gives an
  exact closed form on the smaller open subset.
proof:
  In degree zero exact forms are zero; in positive degree, restrict a primitive
  and use compatibility of \(d\) with restriction along the inclusion.
-/
theorem deRhamClosedFormsRestrictionOfLE_exact (hWV : W ≤ V) (n : ℕ) :
    DeRhamExactClosedForms (I := I) (M := V) (A := A) n ≤
      (DeRhamExactClosedForms (I := I) (M := W) (A := A) n).comap
        (deRhamClosedFormsRestrictionOfLE (I := I) (A := A) hWV n) := by
  intro omega homega
  change
    (deRhamClosedFormsRestrictionOfLE (I := I) (A := A) hWV n omega).1 ∈
      DeRhamExactForms (I := I) (M := W) (A := A) n
  change omega.1 ∈ DeRhamExactForms (I := I) (M := V) (A := A) n at homega
  cases n with
  | zero =>
      simp [DeRhamExactForms] at homega ⊢
      rw [homega]
      rfl
  | succ n =>
      rw [DeRhamExactForms] at homega ⊢
      rcases homega with ⟨eta, heta⟩
      refine ⟨restrictSmoothFormsOfLE (I := I) (A := A) hWV n eta, ?_⟩
      rw [deRhamDifferential_restrictSmoothFormsOfLE (I := I) (A := A) hWV]
      rw [heta]
      rfl

/-- The induced restriction map on de Rham cohomology for an inclusion of opens. -/
def deRhamCohomologyRestrictionOfLE (hWV : W ≤ V) (n : ℕ) :
    DeRhamCohomology (I := I) (M := V) (A := A) n →ₗ[𝕜]
      DeRhamCohomology (I := I) (M := W) (A := A) n :=
  (DeRhamExactClosedForms (I := I) (M := V) (A := A) n).mapQ
    (DeRhamExactClosedForms (I := I) (M := W) (A := A) n)
    (deRhamClosedFormsRestrictionOfLE (I := I) (A := A) hWV n)
    (deRhamClosedFormsRestrictionOfLE_exact (I := I) (A := A) hWV n)

/--
%%handwave
name:
  Restriction preserves constant degree-zero classes
statement:
  Restricting a real constant degree-zero de Rham class along an inclusion of
  open subsets gives the class represented by the same constant.
proof:
  The pullback of a constant zero-form along the open inclusion is the same
  constant zero-form; pass this equality to cohomology.
-/
theorem deRhamCohomologyRestrictionOfLE_constant
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    {I0 : ModelWithCorners ℝ E0 H0} [IsManifold I0 ∞ M0]
    {W V : TopologicalSpace.Opens M0} (hWV : W ≤ V) (c : ℝ) :
    deRhamCohomologyRestrictionOfLE (I := I0) (A := ℝ) hWV 0
        (deRhamConstantH0Class (I0 := I0) (M0 := V) c) =
      deRhamConstantH0Class (I0 := I0) (M0 := W) c := by
  simp only [deRhamConstantH0Class, deRhamCohomologyRestrictionOfLE]
  apply congrArg
    (DeRhamExactClosedForms (I := I0) (M := W) (A := ℝ) 0).mkQ
  apply Subtype.ext
  apply DifferentialForm.ext
  intro x
  ext v
  rfl

end Restriction

end DeRhamComplex

section MayerVietoris

variable [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M]
variable (A : Type a) [NormedAddCommGroup A] [NormedSpace 𝕜 A]

/--
%%handwave
name:
  Mayer-Vietoris restriction map
statement:
  The map \(\rho_n:H^n(M)\to H^n(U)\oplus H^n(V)\) sends a cohomology class to the pair of its restrictions to \(U\) and \(V\).
-/
def deRhamMayerVietorisRestriction
    (U V : TopologicalSpace.Opens M) (n : ℕ) :
    DeRhamCohomology (I := I) (M := M) (A := A) n →
      DeRhamCohomology (I := I) (M := U) (A := A) n ×
        DeRhamCohomology (I := I) (M := V) (A := A) n :=
  fun omega ↦
    (deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) U n omega,
      deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) V n omega)

/--
%%handwave
name:
  Mayer-Vietoris difference map
statement:
  The map \(\Delta_n:H^n(U)\oplus H^n(V)\to H^n(U\cap V)\) sends \(([\alpha],[\beta])\) to the difference of the two restricted classes on the overlap.
-/
def deRhamMayerVietorisDifference
    (U V : TopologicalSpace.Opens M) (n : ℕ) :
    DeRhamCohomology (I := I) (M := U) (A := A) n ×
        DeRhamCohomology (I := I) (M := V) (A := A) n →
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n :=
  fun omega ↦
    deRhamCohomologyRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n omega.1 -
      deRhamCohomologyRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n omega.2

/--
%%handwave
name:
  Chain-level Mayer-Vietoris restriction
statement:
  On differential forms, the restriction map sends \(\omega\) to \((\omega|_U,\omega|_V)\).
-/
def deRhamMayerVietorisSmoothRestriction
    (U V : TopologicalSpace.Opens M) (n : ℕ) :
    SmoothForms (I := I) (M := M) A n →
      SmoothForms (I := I) (M := U) A n ×
        SmoothForms (I := I) (M := V) A n :=
  fun omega ↦
    (restrictSmoothFormsToOpen (I := I) (A := A) U n omega,
      restrictSmoothFormsToOpen (I := I) (A := A) V n omega)

/--
%%handwave
name:
  Chain-level Mayer-Vietoris difference
statement:
  On differential forms, the overlap map sends \((\alpha,\beta)\) to \(\alpha|_{U\cap V}-\beta|_{U\cap V}\).
-/
def deRhamMayerVietorisSmoothDifference
    (U V : TopologicalSpace.Opens M) (n : ℕ) :
    SmoothForms (I := I) (M := U) A n ×
        SmoothForms (I := I) (M := V) A n →
      SmoothForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n :=
  fun omega ↦
    restrictSmoothFormsOfLE (I := I) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n omega.1 -
    restrictSmoothFormsOfLE (I := I) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n omega.2

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  Tangent maps factor through nested open inclusions
statement:
  For nested open subsets, the tangent map of the smaller inclusion into the
  manifold is the composite of the tangent map into the larger open subset and
  the tangent map from the larger open subset into the manifold.
proof:
  Apply the chain rule to the composite of the two open inclusions.
-/
theorem mfderiv_subtypeVal_comp_inclusion_eq
    (W V : TopologicalSpace.Opens M) (hWV : W ≤ V) (x : W) :
    (mfderiv I I (fun y : V => (y : M))
        (TopologicalSpace.Opens.inclusion hWV x)).comp
        (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x) =
      mfderiv I I (fun y : W => (y : M)) x := by
  have h :=
    mfderiv_comp (I := I) (I' := I) (I'' := I) (x := x)
      (g := fun y : V => (y : M))
      (f := TopologicalSpace.Opens.inclusion hWV)
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := V)).contMDiffAt.mdifferentiableAt
        (by simp))
      (((contMDiff_inclusion (I := I) (n := ∞) hWV)).contMDiffAt.mdifferentiableAt
        (by simp))
  change mfderiv I I (fun y : W => (y : M)) x = _ at h
  exact h.symm

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Transitivity of restriction for smooth differential forms
statement:
  For open subsets \(W\subseteq V\subseteq M\), restricting a smooth form
  first from \(M\) to \(V\) and then from \(V\) to \(W\) equals direct
  restriction from \(M\) to \(W\).
proof:
  At each point of \(W\), the chain rule identifies the composite of the two
  inclusion tangent maps with the tangent map of the direct inclusion.
  Evaluating the ambient form on these maps gives the same value.
-/
theorem restrictSmoothFormsOfLE_restrictSmoothFormsToOpen_eq
    {W V : TopologicalSpace.Opens M} (hWV : W ≤ V) {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) A n) :
    restrictSmoothFormsOfLE (I := I) (A := A) hWV n
        (restrictSmoothFormsToOpen (I := I) (A := A) V n omega) =
      restrictSmoothFormsToOpen (I := I) (A := A) W n omega := by
  apply DifferentialForm.ext
  intro x
  ext v
  have hfactor :=
    mfderiv_subtypeVal_comp_inclusion_eq (I := I) W V hWV x
  simp only [restrictSmoothFormsOfLE]
  change omega.toFun (x : M)
      (((mfderiv I I (fun y : V ↦ (y : M))
          (TopologicalSpace.Opens.inclusion hWV x)).comp
        (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x)) ∘ v) =
    omega.toFun (x : M)
      ((mfderiv I I (fun y : W ↦ (y : M)) x) ∘ v)
  rw [hfactor]

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  Tangent map of a nested open inclusion is invertible
statement:
  For nested open subsets \(W\subset V\), the derivative of the inclusion
  \(W\hookrightarrow V\) is an invertible continuous linear map on tangent
  spaces.
proof:
  Factor the tangent map of \(W\hookrightarrow M\) through \(V\hookrightarrow M\)
  and \(W\hookrightarrow V\).  The two tangent maps into \(M\) are invertible,
  so the intermediate tangent map is their composite.
-/
theorem mfderiv_opens_inclusion_isInvertible
    [IsManifold I 1 M]
    (W V : TopologicalSpace.Opens M) (hWV : W ≤ V) (x : W) :
    (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x).IsInvertible := by
  let xV : V := TopologicalSpace.Opens.inclusion hWV x
  let LV : TangentSpace I xV →L[𝕜] TangentSpace I (x : M) :=
    mfderiv I I (fun y : V => (y : M)) xV
  let LW : TangentSpace I x →L[𝕜] TangentSpace I (x : M) :=
    mfderiv I I (fun y : W => (y : M)) x
  let L : TangentSpace I x →L[𝕜] TangentSpace I xV :=
    mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x
  have hfactor : LV.comp L = LW := by
    simpa [LV, LW, L, xV] using
      mfderiv_subtypeVal_comp_inclusion_eq (I := I) W V hWV x
  have hLV : LV.IsInvertible := by
    simpa [LV, xV] using mfderiv_subtypeVal_isInvertible (I := I) V xV
  have hLW : LW.IsInvertible := by
    simpa [LW] using mfderiv_subtypeVal_isInvertible (I := I) W x
  have hL_eq : L = LV.inverse.comp LW := by
    apply ContinuousLinearMap.ext
    intro z
    calc
      L z = LV.inverse (LV (L z)) := by
        rw [hLV.inverse_apply_self]
      _ = LV.inverse (LW z) := by
        rw [← hfactor]
        rfl
      _ = (LV.inverse.comp LW) z := rfl
  change L.IsInvertible
  rw [hL_eq]
  exact hLV.inverse.comp hLW

def smoothFormOpenExtensionValue
    (U : TopologicalSpace.Opens M) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (x : M) (hx : x ∈ U) : FormAt (I := I) (M := M) A n x :=
  (alpha.toFun ⟨x, hx⟩).compContinuousLinearMap
    (mfderiv I I (fun y : U => (y : M)) ⟨x, hx⟩).inverse

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Extension value restricts back to the original form
statement:
  Extending the value of a form from an open subset to the ambient tangent
  space and then restricting back recovers the original pointwise form.
proof:
  Use that the tangent map of an open inclusion is invertible and that
  precomposition by the inverse cancels.
-/
theorem smoothFormOpenExtensionValue_restrict
    (U : TopologicalSpace.Opens M) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (x : U) :
    (smoothFormOpenExtensionValue (I := I) (A := A) U alpha (x : M) x.2).compContinuousLinearMap
        (mfderiv I I (fun y : U => (y : M)) x) =
      alpha.toFun x := by
  change
    ((alpha.toFun x).compContinuousLinearMap
      (mfderiv I I (fun y : U => (y : M)) x).inverse).compContinuousLinearMap
        (mfderiv I I (fun y : U => (y : M)) x) =
      alpha.toFun x
  exact continuousAlternatingMap_compContinuousLinearMap_inverse_comp
    (alpha.toFun x)
    (mfderiv I I (fun y : U => (y : M)) x)
      (mfderiv_subtypeVal_isInvertible (I := I) U x)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Extension value restricts along smaller open subsets
statement:
  If a form on an open subset is evaluated as an ambient tangent form and then
  restricted to a smaller open subset, the result agrees with ordinary
  restriction to the smaller open subset.
proof:
  Factor the tangent map through the larger open subset and cancel the
  invertible tangent map of the larger inclusion.
-/
theorem smoothFormOpenExtensionValue_restrictOfLE
    (W U : TopologicalSpace.Opens M) (hWU : W ≤ U) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (x : W) :
    (smoothFormOpenExtensionValue (I := I) (A := A) U alpha (x : M) (hWU x.2)).compContinuousLinearMap
        (mfderiv I I (fun y : W => (y : M)) x) =
      (alpha.toFun (TopologicalSpace.Opens.inclusion hWU x)).compContinuousLinearMap
        (mfderiv I I (TopologicalSpace.Opens.inclusion hWU) x) := by
  let xU : U := TopologicalSpace.Opens.inclusion hWU x
  let LU : TangentSpace I xU →L[𝕜] TangentSpace I (x : M) :=
    mfderiv I I (fun y : U => (y : M)) xU
  let LWU : TangentSpace I x →L[𝕜] TangentSpace I xU :=
    mfderiv I I (TopologicalSpace.Opens.inclusion hWU) x
  let LWM : TangentSpace I x →L[𝕜] TangentSpace I (x : M) :=
    mfderiv I I (fun y : W => (y : M)) x
  have hfactor : LU.comp LWU = LWM := by
    simpa [LU, LWU, LWM, xU] using
      mfderiv_subtypeVal_comp_inclusion_eq (I := I) W U hWU x
  have hLU : LU.IsInvertible := by
    simpa [LU, xU] using mfderiv_subtypeVal_isInvertible (I := I) U xU
  change
    ((alpha.toFun xU).compContinuousLinearMap LU.inverse).compContinuousLinearMap LWM =
      (alpha.toFun xU).compContinuousLinearMap LWU
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (alpha.toFun xU)
  funext i
  calc
    LU.inverse (LWM (v i)) = LU.inverse ((LU.comp LWU) (v i)) := by
      rw [hfactor]
    _ = LU.inverse (LU (LWU (v i))) := rfl
    _ = LWU (v i) := hLU.inverse_apply_self (LWU (v i))

/--
%%handwave
name:
  The de Rham differential commutes with the Mayer-Vietoris difference
statement:
  Applying \(d\) to the two components of a pair of forms and then taking the
  overlap difference is the same as first taking the overlap difference and
  then applying \(d\).
proof:
  Expand the overlap difference and use compatibility of \(d\) with restriction
  along the two inclusions into the overlap.
-/
theorem deRhamDifferential_mayerVietorisSmoothDifference
    (U V : TopologicalSpace.Opens M) (n : ℕ)
    (omega :
      SmoothForms (I := I) (M := U) A n ×
        SmoothForms (I := I) (M := V) A n) :
    deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (n + 1)
        (deRhamDifferential (I := I) (M := U) (A := A) n omega.1,
          deRhamDifferential (I := I) (M := V) (A := A) n omega.2) =
      deRhamDifferential (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n
        (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n omega) := by
  rw [deRhamMayerVietorisSmoothDifference]
  change
    restrictSmoothFormsOfLE (I := I) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left (n + 1)
        (deRhamDifferential (I := I) (M := U) (A := A) n omega.1) -
      restrictSmoothFormsOfLE (I := I) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right (n + 1)
        (deRhamDifferential (I := I) (M := V) (A := A) n omega.2) =
    deRhamDifferential (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n
      (restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n omega.1 -
        restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n omega.2)
  rw [map_sub]
  rw [deRhamDifferential_restrictSmoothFormsOfLE (I := I) (A := A) inf_le_left,
    deRhamDifferential_restrictSmoothFormsOfLE (I := I) (A := A) inf_le_right]

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  The two overlap tangent factorizations agree
statement:
  At a point of \(U\cap V\), factoring the ambient tangent map through \(U\)
  or through \(V\) gives the same tangent map into the ambient manifold.
proof:
  Apply the chain rule to both open inclusions from the overlap and identify
  both composites with the same ambient inclusion.
-/
theorem mfderiv_subtypeVal_comp_inclusion_inf_eq
    (U V : TopologicalSpace.Opens M)
    (x : (U ⊓ V : TopologicalSpace.Opens M)) :
    (mfderiv I I (fun y : U => (y : M)) (TopologicalSpace.Opens.inclusion inf_le_left x)).comp
        (mfderiv I I
          (TopologicalSpace.Opens.inclusion
            (U := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left) x) =
      (mfderiv I I (fun y : V => (y : M)) (TopologicalSpace.Opens.inclusion inf_le_right x)).comp
        (mfderiv I I
          (TopologicalSpace.Opens.inclusion
            (U := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right) x) := by
  let W : TopologicalSpace.Opens M := U ⊓ V
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  have hleft :=
    mfderiv_comp (I := I) (I' := I) (I'' := I) (x := x)
      (g := fun y : U => (y : M))
      (f := TopologicalSpace.Opens.inclusion hWU)
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).contMDiffAt.mdifferentiableAt
        (by simp))
      (((contMDiff_inclusion (I := I) (n := ∞) hWU)).contMDiffAt.mdifferentiableAt
        (by simp))
  have hright :=
    mfderiv_comp (I := I) (I' := I) (I'' := I) (x := x)
      (g := fun y : V => (y : M))
      (f := TopologicalSpace.Opens.inclusion hWV)
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := V)).contMDiffAt.mdifferentiableAt
        (by simp))
      (((contMDiff_inclusion (I := I) (n := ∞) hWV)).contMDiffAt.mdifferentiableAt
        (by simp))
  change mfderiv I I (fun y : W => (y : M)) x = _ at hleft
  change mfderiv I I (fun y : W => (y : M)) x = _ at hright
  exact hleft.symm.trans hright

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Zero smooth overlap difference gives equality on the overlap
statement:
  If two forms on \(U\) and \(V\) have zero overlap difference, their
  pointwise restrictions to \(U\cap V\) agree.
proof:
  Evaluate the zero overlap-difference equality at the point and use the
  equality of the two tangent factorizations through the overlap.
-/
theorem smoothForms_overlap_eq_of_smooth_difference_eq_zero
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0)
    (x : (U ⊓ V : TopologicalSpace.Opens M)) :
    (alpha.toFun (TopologicalSpace.Opens.inclusion inf_le_left x)).compContinuousLinearMap
        (mfderiv I I
          (TopologicalSpace.Opens.inclusion
            (U := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left) x) =
      (beta.toFun (TopologicalSpace.Opens.inclusion inf_le_right x)).compContinuousLinearMap
        (mfderiv I I
          (TopologicalSpace.Opens.inclusion
            (U := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right) x) := by
  have hforms :
      restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha =
        restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta := by
    apply sub_eq_zero.mp
    simpa [deRhamMayerVietorisSmoothDifference] using hoverlap
  have hpoint :=
    congrArg
      (fun omega : SmoothForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n =>
        omega.toFun x)
      hforms
  change
    (alpha.toFun (TopologicalSpace.Opens.inclusion inf_le_left x)).compContinuousLinearMap
        (mfderiv I I
          (TopologicalSpace.Opens.inclusion
            (U := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left) x) =
      (beta.toFun (TopologicalSpace.Opens.inclusion inf_le_right x)).compContinuousLinearMap
        (mfderiv I I
          (TopologicalSpace.Opens.inclusion
            (U := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right) x) at hpoint
  exact hpoint

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Extension values agree on the overlap
statement:
  If two forms on \(U\) and \(V\) have zero overlap difference, then their
  ambient extension values agree at every point of \(U\cap V\).
proof:
  Precompose both ambient extension values with the surjective tangent map from
  the overlap and use equality of the two restricted forms there.
-/
theorem smoothFormOpenExtensionValue_eq_on_overlap
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0)
    (x : (U ⊓ V : TopologicalSpace.Opens M)) :
    smoothFormOpenExtensionValue (I := I) (A := A) U alpha (x : M)
        ((inf_le_left : (U ⊓ V : TopologicalSpace.Opens M) ≤ U) x.2) =
      smoothFormOpenExtensionValue (I := I) (A := A) V beta (x : M)
        ((inf_le_right : (U ⊓ V : TopologicalSpace.Opens M) ≤ V) x.2) := by
  let W : TopologicalSpace.Opens M := U ⊓ V
  let hWU : W ≤ U := inf_le_left
  let hWV : W ≤ V := inf_le_right
  let LWM : TangentSpace I x →L[𝕜] TangentSpace I (x : M) :=
    mfderiv I I (fun y : W => (y : M)) x
  apply continuousAlternatingMap_compContinuousLinearMap_injective LWM
    (mfderiv_subtypeVal_surjective (I := I) W x)
  change
    (smoothFormOpenExtensionValue (I := I) (A := A) U alpha (x : M) (hWU x.2)).compContinuousLinearMap
        LWM =
      (smoothFormOpenExtensionValue (I := I) (A := A) V beta (x : M) (hWV x.2)).compContinuousLinearMap
        LWM
  rw [smoothFormOpenExtensionValue_restrictOfLE (I := I) (A := A) W U hWU alpha x,
    smoothFormOpenExtensionValue_restrictOfLE (I := I) (A := A) W V hWV beta x]
  exact smoothForms_overlap_eq_of_smooth_difference_eq_zero
    (I := I) (A := A) U V alpha beta hoverlap x

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  Membership in the other open set of a two-open cover
statement:
  If \(U\cup V=M\) and a point is not in \(U\), then it is in \(V\).
proof:
  Use the cover equality to obtain membership in \(U\) or \(V\), then eliminate
  the \(U\)-case.
-/
theorem mem_right_of_not_mem_left_of_sup_eq_top
    {U V : TopologicalSpace.Opens M} (hcover : U ⊔ V = ⊤)
    {x : M} (hxU : x ∉ U) : x ∈ V := by
  have hx : x ∈ (U ⊔ V : TopologicalSpace.Opens M) := by
    rw [hcover]
    trivial
  have hxUV : x ∈ U ∨ x ∈ V := by
    simpa using hx
  exact hxUV.resolve_left hxU

def smoothFormsTwoOpenGlueFun
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n) :
    (x : M) → FormAt (I := I) (M := M) A n x :=
  fun x => by
    classical
    exact
      if hxU : x ∈ U then
        smoothFormOpenExtensionValue (I := I) (A := A) U alpha x hxU
      else
        smoothFormOpenExtensionValue (I := I) (A := A) V beta x
          (mem_right_of_not_mem_left_of_sup_eq_top hcover hxU)

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  The glued form equals the left form on \(U\)
statement:
  The pointwise glued form for a two-open cover is given by the left form at
  points of \(U\).
proof:
  Unfold the case distinction defining the glued form and choose the \(U\)
  branch.
-/
theorem smoothFormsTwoOpenGlueFun_eq_left
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    {x : M} (hxU : x ∈ U) :
    smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta x =
      smoothFormOpenExtensionValue (I := I) (A := A) U alpha x hxU := by
  simp [smoothFormsTwoOpenGlueFun, hxU]

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  The glued form equals the right form on \(V\)
statement:
  If the two local forms agree on the overlap, the pointwise glued form is
  given by the right form at points of \(V\).
proof:
  If the point also lies in \(U\), use equality of extension values on the
  overlap; otherwise the defining case distinction already chooses the
  \(V\)-branch.
-/
theorem smoothFormsTwoOpenGlueFun_eq_right
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0)
    {x : M} (hxV : x ∈ V) :
    smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta x =
      smoothFormOpenExtensionValue (I := I) (A := A) V beta x hxV := by
  classical
  by_cases hxU : x ∈ U
  · let xW : (U ⊓ V : TopologicalSpace.Opens M) := ⟨x, by exact ⟨hxU, hxV⟩⟩
    have hbranch :=
      smoothFormOpenExtensionValue_eq_on_overlap
        (I := I) (A := A) U V alpha beta hoverlap xW
    simpa [smoothFormsTwoOpenGlueFun, hxU, xW] using hbranch
  · simp [smoothFormsTwoOpenGlueFun, hxU]

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Coordinate expression of the glued form on \(U\)
statement:
  On a chart restricted to \(U\), the coordinate representative of the glued
  form agrees with the coordinate representative of the left local form.
proof:
  Use the left-branch formula for the glued form and cancel the inverse tangent
  map of the open inclusion.
-/
theorem coordinateExpression_smoothFormsTwoOpenGlueFun_left
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (e : OpenPartialHomeomorph M H) (hU : Nonempty U)
    (he : e ∈ atlas H M) (heU : e.subtypeRestr hU ∈ atlas H U)
    {y : E} (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    coordinateExpression (I := I) (F := A) (n := n)
        (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta) e y =
      coordinateExpression (I := I) (F := A) (n := n)
        alpha.toFun (e.subtypeRestr hU) y := by
  let eU : OpenPartialHomeomorph U H := e.subtypeRestr hU
  let xU : U := (eU.extend I).symm y
  let L : TangentSpace I xU →L[𝕜] TangentSpace I (xU : M) :=
    mfderiv I I (fun z : U => (z : M)) xU
  let DU : E →L[𝕜] TangentSpace I xU :=
    mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y
  let DM : E →L[𝕜] TangentSpace I (xU : M) :=
    mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y
  have hpoint : (xU : M) = (e.extend I).symm y := by
    simpa [xU, eU] using subtypeRestr_extend_symm_coe (I := I) e U hU hy
  have hxU : (e.extend I).symm y ∈ U := by
    rw [← hpoint]
    exact xU.2
  have hpointU : (⟨(e.extend I).symm y, hxU⟩ : U) = xU := by
    apply Subtype.ext
    exact hpoint.symm
  have hglue :
      smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta
          ((e.extend I).symm y) =
        smoothFormOpenExtensionValue (I := I) (A := A) U alpha ((e.extend I).symm y) hxU :=
    smoothFormsTwoOpenGlueFun_eq_left (I := I) (A := A) U V hcover alpha beta hxU
  have hfactor : L.comp DU = DM := by
    simpa [L, DU, DM, eU, xU, hpoint] using
      mfderiv_subtypeVal_comp_subtypeRestr_extend_symm (I := I) e U hU he heU hy
  have hL : L.IsInvertible := by
    simpa [L, xU] using mfderiv_subtypeVal_isInvertible (I := I) U xU
  rw [coordinateExpression, coordinateExpression, hglue, smoothFormOpenExtensionValue]
  rw [hpointU]
  change
    ((alpha.toFun xU).compContinuousLinearMap L.inverse).compContinuousLinearMap DM =
      (alpha.toFun xU).compContinuousLinearMap DU
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (alpha.toFun xU)
  funext i
  calc
    L.inverse (DM (v i)) = L.inverse ((L.comp DU) (v i)) := by
      rw [hfactor]
    _ = L.inverse (L (DU (v i))) := rfl
    _ = DU (v i) := hL.inverse_apply_self (DU (v i))

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Smoothness of the glued coordinate expression on \(U\)
statement:
  On the part of a chart lying over \(U\), the coordinate representative of the
  glued form is smooth.
proof:
  Replace it with the coordinate representative of the left local form, which
  is smooth.
-/
theorem contDiffOn_coordinateExpression_smoothFormsTwoOpenGlueFun_left
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (e : OpenPartialHomeomorph M H) (hU : Nonempty U)
    (he : e ∈ atlas H M) (heU : e.subtypeRestr hU ∈ atlas H U) :
    ContDiffOn 𝕜 ∞
      (coordinateExpression (I := I) (F := A) (n := n)
        (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta) e)
      ((e.subtypeRestr hU).extend I).target := by
  exact (alpha.isContMDiff (e.subtypeRestr hU) heU).congr
    (fun y hy =>
      (coordinateExpression_smoothFormsTwoOpenGlueFun_left
        (I := I) (A := A) U V hcover alpha beta e hU he heU hy))

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Coordinate expression of the glued form on \(V\)
statement:
  On a chart restricted to \(V\), the coordinate representative of the glued
  form agrees with the coordinate representative of the right local form.
proof:
  Use the right-branch formula for the glued form and cancel the inverse
  tangent map of the open inclusion.
-/
theorem coordinateExpression_smoothFormsTwoOpenGlueFun_right
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0)
    (e : OpenPartialHomeomorph M H) (hV : Nonempty V)
    (he : e ∈ atlas H M) (heV : e.subtypeRestr hV ∈ atlas H V)
    {y : E} (hy : y ∈ ((e.subtypeRestr hV).extend I).target) :
    coordinateExpression (I := I) (F := A) (n := n)
        (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta) e y =
      coordinateExpression (I := I) (F := A) (n := n)
        beta.toFun (e.subtypeRestr hV) y := by
  let eV : OpenPartialHomeomorph V H := e.subtypeRestr hV
  let xV : V := (eV.extend I).symm y
  let L : TangentSpace I xV →L[𝕜] TangentSpace I (xV : M) :=
    mfderiv I I (fun z : V => (z : M)) xV
  let DV : E →L[𝕜] TangentSpace I xV :=
    mfderivWithin 𝓘(𝕜, E) I (eV.extend I).symm (eV.extend I).target y
  let DM : E →L[𝕜] TangentSpace I (xV : M) :=
    mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y
  have hpoint : (xV : M) = (e.extend I).symm y := by
    simpa [xV, eV] using subtypeRestr_extend_symm_coe (I := I) e V hV hy
  have hxV : (e.extend I).symm y ∈ V := by
    rw [← hpoint]
    exact xV.2
  have hpointV : (⟨(e.extend I).symm y, hxV⟩ : V) = xV := by
    apply Subtype.ext
    exact hpoint.symm
  have hglue :
      smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta
          ((e.extend I).symm y) =
        smoothFormOpenExtensionValue (I := I) (A := A) V beta ((e.extend I).symm y) hxV :=
    smoothFormsTwoOpenGlueFun_eq_right
      (I := I) (A := A) U V hcover alpha beta hoverlap hxV
  have hfactor : L.comp DV = DM := by
    simpa [L, DV, DM, eV, xV, hpoint] using
      mfderiv_subtypeVal_comp_subtypeRestr_extend_symm (I := I) e V hV he heV hy
  have hL : L.IsInvertible := by
    simpa [L, xV] using mfderiv_subtypeVal_isInvertible (I := I) V xV
  rw [coordinateExpression, coordinateExpression, hglue, smoothFormOpenExtensionValue]
  rw [hpointV]
  change
    ((beta.toFun xV).compContinuousLinearMap L.inverse).compContinuousLinearMap DM =
      (beta.toFun xV).compContinuousLinearMap DV
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (beta.toFun xV)
  funext i
  calc
    L.inverse (DM (v i)) = L.inverse ((L.comp DV) (v i)) := by
      rw [hfactor]
    _ = L.inverse (L (DV (v i))) := rfl
    _ = DV (v i) := hL.inverse_apply_self (DV (v i))

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Smoothness of the glued coordinate expression on \(V\)
statement:
  On the part of a chart lying over \(V\), the coordinate representative of the
  glued form is smooth.
proof:
  Replace it with the coordinate representative of the right local form, which
  is smooth.
-/
theorem contDiffOn_coordinateExpression_smoothFormsTwoOpenGlueFun_right
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0)
    (e : OpenPartialHomeomorph M H) (hV : Nonempty V)
    (he : e ∈ atlas H M) (heV : e.subtypeRestr hV ∈ atlas H V) :
    ContDiffOn 𝕜 ∞
      (coordinateExpression (I := I) (F := A) (n := n)
        (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta) e)
      ((e.subtypeRestr hV).extend I).target := by
  exact (beta.isContMDiff (e.subtypeRestr hV) heV).congr
    (fun y hy =>
      (coordinateExpression_smoothFormsTwoOpenGlueFun_right
        (I := I) (A := A) U V hcover alpha beta hoverlap e hV he heV hy))

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Smoothness of glued coordinate expressions from local restrictions
statement:
  If two local forms agree on the overlap, the coordinate representative of
  their glued pointwise form is smooth on every ambient chart.
proof:
  Around each coordinate point, use the cover to choose either the \(U\)-side or
  the \(V\)-side and apply the corresponding local smoothness statement.
-/
theorem contDiffOn_coordinateExpression_smoothFormsTwoOpenGlueFun_of_restrictions
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0)
    (e : OpenPartialHomeomorph M H) (hU : Nonempty U) (hV : Nonempty V)
    (he : e ∈ atlas H M)
    (heU : e.subtypeRestr hU ∈ atlas H U)
    (heV : e.subtypeRestr hV ∈ atlas H V) :
    ContDiffOn 𝕜 ∞
      (coordinateExpression (I := I) (F := A) (n := n)
        (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta) e)
      (e.extend I).target := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro y hy
  let x : M := (e.extend I).symm y
  have hxUV : x ∈ U ∨ x ∈ V := by
    have hx : x ∈ (U ⊔ V : TopologicalSpace.Opens M) := by
      rw [hcover]
      trivial
    simpa [x] using hx
  rcases hxUV with hxU | hxV
  · have hyUtarget : y ∈ ((e.subtypeRestr hU).extend I).target :=
      subtypeRestr_extend_target_of_mem (I := I) e U hU hy (by simpa [x] using hxU)
    rcases mem_nhdsWithin.mp
        (subtypeRestr_extend_target_mem_nhdsWithin (I := I) e U hU hyUtarget) with
      ⟨u, hu_open, hyu, hutarget⟩
    refine ⟨u, hu_open, hyu, ?_⟩
    exact
      (contDiffOn_coordinateExpression_smoothFormsTwoOpenGlueFun_left
        (I := I) (A := A) U V hcover alpha beta e hU he heU).mono
        (by
          intro z hz
          exact hutarget ⟨hz.2, hz.1⟩)
  · have hyVtarget : y ∈ ((e.subtypeRestr hV).extend I).target :=
      subtypeRestr_extend_target_of_mem (I := I) e V hV hy (by simpa [x] using hxV)
    rcases mem_nhdsWithin.mp
        (subtypeRestr_extend_target_mem_nhdsWithin (I := I) e V hV hyVtarget) with
      ⟨u, hu_open, hyu, hutarget⟩
    refine ⟨u, hu_open, hyu, ?_⟩
    exact
      (contDiffOn_coordinateExpression_smoothFormsTwoOpenGlueFun_right
        (I := I) (A := A) U V hcover alpha beta hoverlap e hV he heV).mono
        (by
          intro z hz
          exact hutarget ⟨hz.2, hz.1⟩)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Smoothness can be checked on maximal-atlas charts
statement:
  A chartwise smooth pointwise form has a smooth coordinate representative in
  every chart of the smooth maximal atlas.
proof:
  Near each point of a maximal-atlas chart, compare with an ordinary atlas
  chart by a smooth coordinate change and use smoothness of alternating
  pullback.
-/
theorem contDiffOn_coordinateExpression_of_mem_maximalAtlas
    [CharZero 𝕜]
    {n : ℕ} (form : (x : M) → FormAt (I := I) (M := M) A n x)
    (hform : IsContMDiffForm (I := I) (M := M) (F := A) (n := n) ∞ form)
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn 𝕜 ∞
      (coordinateExpression (I := I) (F := A) (n := n) form e)
      (e.extend I).target := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro y hy
  let x : M := (e.extend I).symm y
  let e' : OpenPartialHomeomorph M H := chartAt H x
  let φ : PartialEquiv E E := I.extendCoordChange e e'
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp) he
  have he'_atlas : e' ∈ atlas H M := by
    simp [e']
  have he'max : e' ∈ IsManifold.maximalAtlas I ∞ M :=
    IsManifold.subset_maximalAtlas (I := I) (n := ∞) he'_atlas
  have he'1 : e' ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp) he'max
  have hx_source : x ∈ e'.source := by
    simp [e', x]
  have hx_extend_source : x ∈ (e'.extend I).source := by
    simpa [e'.extend_source (I := I)] using hx_source
  have hyφ : y ∈ φ.source := by
    change y ∈ (e.extend I).target ∧ (e.extend I).symm y ∈ (e'.extend I).source
    exact ⟨hy, by simpa [x] using hx_extend_source⟩
  have hφ_source_mem_target : φ.source ∈ 𝓝[(e.extend I).target] y := by
    have hsource_range : φ.source ∈ 𝓝[range I] y := by
      simpa [φ] using
        I.extendCoordChange_source_mem_nhdsWithin (e := e) (e' := e') hyφ
    have h_eq : 𝓝[(e.extend I).target] y = 𝓝[range I] y :=
      nhdsWithin_extend_target_eq_of_mem (I := I) hy
    exact h_eq.symm ▸ hsource_range
  have hφ_target_subset_target' : φ.target ⊆ (e'.extend I).target := by
    intro z hz
    simpa [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_target] using hz.1
  have hφ_maps : MapsTo φ φ.source (e'.extend I).target := by
    intro z hz
    exact hφ_target_subset_target' (φ.map_source hz)
  have hη :
      ContDiffOn 𝕜 ∞
        (coordinateExpression (I := I) (F := A) (n := n) form e')
        (e'.extend I).target :=
    hform e' he'_atlas
  have hφ : ContDiffOn 𝕜 ∞ φ φ.source := by
    simpa [φ] using I.contDiffOn_extendCoordChange he he'max
  have hDφ : ContDiffOn 𝕜 ∞ (fderivWithin 𝕜 φ φ.source) φ.source := by
    exact hφ.fderivWithin
      (I.uniqueDiffOn_extendCoordChange_source (e := e) (e' := e'))
      (by simp)
  have hηφ :
      ContDiffOn 𝕜 ∞
        (fun z => coordinateExpression (I := I) (F := A) (n := n) form e' (φ z))
        φ.source :=
    hη.comp hφ hφ_maps
  have hpullback :
      ContDiffOn 𝕜 ∞
        (fun z =>
          (coordinateExpression (I := I) (F := A) (n := n) form e' (φ z)).compContinuousLinearMap
            (fderivWithin 𝕜 φ φ.source z))
        φ.source :=
    contDiffOn_continuousAlternatingMap_compContinuousLinearMap hηφ hDφ
  rcases mem_nhdsWithin.mp hφ_source_mem_target with
    ⟨u, hu_open, hyu, hutarget⟩
  refine ⟨u, hu_open, hyu, ?_⟩
  exact hpullback.mono
    (by
      intro z hz
      exact hutarget ⟨hz.2, hz.1⟩)
    |>.congr
      (fun z hz =>
        coordinateExpression_coordChange_maximal
          (I := I) (A := A) (n := n) form he1 he'1
          (by
            exact hutarget ⟨hz.2, hz.1⟩))

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Coordinate expression from matching extension values
statement:
  If a pointwise form agrees on an open subset with the ambient extension of a
  local form, then in a restricted chart its coordinate representative agrees
  with that of the local form.
proof:
  Substitute the extension-value formula and cancel the inverse tangent map of
  the open inclusion.
-/
theorem coordinateExpression_eq_smoothFormOpenExtensionValue_of_mem
    (U : TopologicalSpace.Opens M) {n : ℕ}
    (form : (x : M) → FormAt (I := I) (M := M) A n x)
    (alpha : SmoothForms (I := I) (M := U) A n)
    (hformU :
      ∀ ⦃x : M⦄ (hx : x ∈ U),
        form x = smoothFormOpenExtensionValue (I := I) (A := A) U alpha x hx)
    (e : OpenPartialHomeomorph M H) (hU : Nonempty U)
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (heU : e.subtypeRestr hU ∈ IsManifold.maximalAtlas I ∞ U)
    {y : E} (hy : y ∈ ((e.subtypeRestr hU).extend I).target) :
    coordinateExpression (I := I) (F := A) (n := n) form e y =
      coordinateExpression (I := I) (F := A) (n := n)
        alpha.toFun (e.subtypeRestr hU) y := by
  let eU : OpenPartialHomeomorph U H := e.subtypeRestr hU
  let xU : U := (eU.extend I).symm y
  let L : TangentSpace I xU →L[𝕜] TangentSpace I (xU : M) :=
    mfderiv I I (fun z : U => (z : M)) xU
  let DU : E →L[𝕜] TangentSpace I xU :=
    mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y
  let DM : E →L[𝕜] TangentSpace I (xU : M) :=
    mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y
  have hpoint : (xU : M) = (e.extend I).symm y := by
    simpa [xU, eU] using subtypeRestr_extend_symm_coe (I := I) e U hU hy
  have hxU : (e.extend I).symm y ∈ U := by
    rw [← hpoint]
    exact xU.2
  have hpointU : (⟨(e.extend I).symm y, hxU⟩ : U) = xU := by
    apply Subtype.ext
    exact hpoint.symm
  have hform :
      form ((e.extend I).symm y) =
        smoothFormOpenExtensionValue (I := I) (A := A) U alpha
          ((e.extend I).symm y) hxU :=
    hformU hxU
  have hfactor : L.comp DU = DM := by
    simpa [L, DU, DM, eU, xU, hpoint] using
      mfderiv_subtypeVal_comp_subtypeRestr_extend_symm_maximal
        (I := I) e U hU he heU hy
  have hL : L.IsInvertible := by
    simpa [L, xU] using mfderiv_subtypeVal_isInvertible (I := I) U xU
  rw [coordinateExpression, coordinateExpression, hform, smoothFormOpenExtensionValue]
  rw [hpointU]
  change
    ((alpha.toFun xU).compContinuousLinearMap L.inverse).compContinuousLinearMap DM =
      (alpha.toFun xU).compContinuousLinearMap DU
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (alpha.toFun xU)
  funext i
  calc
    L.inverse (DM (v i)) = L.inverse ((L.comp DU) (v i)) := by
      rw [hfactor]
    _ = L.inverse (L (DU (v i))) := rfl
    _ = DU (v i) := hL.inverse_apply_self (DU (v i))

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Smoothness from matching extension values on an open subset
statement:
  If a pointwise form agrees on an open subset with the ambient extension of a
  smooth local form, its coordinate representative is smooth on the restricted
  chart target.
proof:
  Replace the coordinate representative by that of the local smooth form on the
  restricted chart.
-/
theorem contDiffOn_coordinateExpression_eq_smoothFormOpenExtensionValue_of_mem
    [CharZero 𝕜]
    (U : TopologicalSpace.Opens M) {n : ℕ}
    (form : (x : M) → FormAt (I := I) (M := M) A n x)
    (alpha : SmoothForms (I := I) (M := U) A n)
    (hformU :
      ∀ ⦃x : M⦄ (hx : x ∈ U),
        form x = smoothFormOpenExtensionValue (I := I) (A := A) U alpha x hx)
    (e : OpenPartialHomeomorph M H) (hU : Nonempty U)
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (heU : e.subtypeRestr hU ∈ IsManifold.maximalAtlas I ∞ U) :
    ContDiffOn 𝕜 ∞
      (coordinateExpression (I := I) (F := A) (n := n) form e)
      ((e.subtypeRestr hU).extend I).target := by
  exact
    (contDiffOn_coordinateExpression_of_mem_maximalAtlas
      (I := I) (A := A) alpha.toFun alpha.isContMDiff
      (e.subtypeRestr hU) heU).congr
      (fun y hy =>
        coordinateExpression_eq_smoothFormOpenExtensionValue_of_mem
          (I := I) (A := A) U form alpha hformU e hU he heU hy)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Smoothness from a two-open local description
statement:
  If a pointwise form is locally given by smooth forms on two opens covering
  the manifold, then each coordinate representative is smooth.
proof:
  Around each coordinate point, choose the open set containing it and use the
  corresponding restricted-chart smoothness statement.
-/
theorem contDiffOn_coordinateExpression_of_eqOn_two_open_cover
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (form : (x : M) → FormAt (I := I) (M := M) A n x)
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hU :
      ∀ ⦃x : M⦄ (hx : x ∈ U),
        form x = smoothFormOpenExtensionValue (I := I) (A := A) U alpha x hx)
    (hV :
      ∀ ⦃x : M⦄ (hx : x ∈ V),
        form x = smoothFormOpenExtensionValue (I := I) (A := A) V beta x hx)
    (e : OpenPartialHomeomorph M H) (he : e ∈ atlas H M) :
    ContDiffOn 𝕜 ∞
      (coordinateExpression (I := I) (F := A) (n := n) form e)
      (e.extend I).target := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro y hy
  let x : M := (e.extend I).symm y
  have hxUV : x ∈ U ∨ x ∈ V := by
    have hx : x ∈ (U ⊔ V : TopologicalSpace.Opens M) := by
      rw [hcover]
      trivial
    simpa [x] using hx
  have hemax : e ∈ IsManifold.maximalAtlas I ∞ M :=
    IsManifold.subset_maximalAtlas (I := I) (n := ∞) he
  rcases hxUV with hxU | hxV
  · let hUnonempty : Nonempty U := ⟨⟨x, hxU⟩⟩
    have hyUtarget : y ∈ ((e.subtypeRestr hUnonempty).extend I).target :=
      subtypeRestr_extend_target_of_mem (I := I) e U hUnonempty hy
        (by simpa [x] using hxU)
    have heUmax :
        e.subtypeRestr hUnonempty ∈ IsManifold.maximalAtlas I ∞ U := by
      simpa [IsManifold.maximalAtlas] using
        (StructureGroupoid.subtypeRestr_mem_maximalAtlas
          (M := M) (H := H) (G := contDiffGroupoid ∞ I)
          (e := e) he (s := U) hUnonempty)
    rcases mem_nhdsWithin.mp
        (subtypeRestr_extend_target_mem_nhdsWithin (I := I) e U hUnonempty hyUtarget) with
      ⟨u, hu_open, hyu, hutarget⟩
    refine ⟨u, hu_open, hyu, ?_⟩
    exact
      (contDiffOn_coordinateExpression_eq_smoothFormOpenExtensionValue_of_mem
        (I := I) (A := A) U form alpha hU e hUnonempty hemax heUmax).mono
        (by
          intro z hz
          exact hutarget ⟨hz.2, hz.1⟩)
  · let hVnonempty : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hyVtarget : y ∈ ((e.subtypeRestr hVnonempty).extend I).target :=
      subtypeRestr_extend_target_of_mem (I := I) e V hVnonempty hy
        (by simpa [x] using hxV)
    have heVmax :
        e.subtypeRestr hVnonempty ∈ IsManifold.maximalAtlas I ∞ V := by
      simpa [IsManifold.maximalAtlas] using
        (StructureGroupoid.subtypeRestr_mem_maximalAtlas
          (M := M) (H := H) (G := contDiffGroupoid ∞ I)
          (e := e) he (s := V) hVnonempty)
    rcases mem_nhdsWithin.mp
        (subtypeRestr_extend_target_mem_nhdsWithin (I := I) e V hVnonempty hyVtarget) with
      ⟨u, hu_open, hyu, hutarget⟩
    refine ⟨u, hu_open, hyu, ?_⟩
    exact
      (contDiffOn_coordinateExpression_eq_smoothFormOpenExtensionValue_of_mem
        (I := I) (A := A) V form beta hV e hVnonempty hemax heVmax).mono
        (by
          intro z hz
          exact hutarget ⟨hz.2, hz.1⟩)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  A two-open local description gives a smooth form
statement:
  If a pointwise form is given by smooth local forms on two opens covering the
  manifold, then it is a smooth differential form.
proof:
  Apply the chartwise smoothness criterion on every chart.
-/
theorem isContMDiffForm_of_eqOn_two_open_cover
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (form : (x : M) → FormAt (I := I) (M := M) A n x)
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hU :
      ∀ ⦃x : M⦄ (hx : x ∈ U),
        form x = smoothFormOpenExtensionValue (I := I) (A := A) U alpha x hx)
    (hV :
      ∀ ⦃x : M⦄ (hx : x ∈ V),
        form x = smoothFormOpenExtensionValue (I := I) (A := A) V beta x hx) :
    IsContMDiffForm (I := I) (M := M) (F := A) (n := n) ∞ form := by
  intro e he
  exact contDiffOn_coordinateExpression_of_eqOn_two_open_cover
    (I := I) (A := A) U V hcover form alpha beta hU hV e he

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Smoothness from an open-cover local description
statement:
  If a pointwise form is locally given by smooth forms on an open cover, then
  each coordinate representative is smooth.
proof:
  At each coordinate point, choose a member of the open cover containing the
  corresponding manifold point.  On a neighborhood in the restricted chart,
  the coordinate representative agrees with that of the chosen local smooth
  form.
-/
theorem contDiffOn_coordinateExpression_of_eqOn_iSup_open_cover
    [CharZero 𝕜] {ι : Type*}
    (U : ι → TopologicalSpace.Opens M) (hcover : iSup U = ⊤) {n : ℕ}
    (form : (x : M) → FormAt (I := I) (M := M) A n x)
    (alpha : ∀ i : ι, SmoothForms (I := I) (M := U i) A n)
    (hU :
      ∀ i : ι, ∀ ⦃x : M⦄ (hx : x ∈ U i),
        form x =
          smoothFormOpenExtensionValue (I := I) (A := A) (U i) (alpha i) x hx)
    (e : OpenPartialHomeomorph M H) (he : e ∈ atlas H M) :
    ContDiffOn 𝕜 ∞
      (coordinateExpression (I := I) (F := A) (n := n) form e)
      (e.extend I).target := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro y hy
  let x : M := (e.extend I).symm y
  have hxSup : x ∈ iSup U := by
    rw [hcover]
    trivial
  rcases TopologicalSpace.Opens.mem_iSup.mp hxSup with ⟨i, hxUi⟩
  let hUnonempty : Nonempty (U i) := ⟨⟨x, hxUi⟩⟩
  have hyUtarget : y ∈ ((e.subtypeRestr hUnonempty).extend I).target :=
    subtypeRestr_extend_target_of_mem (I := I) e (U i) hUnonempty hy
      (by simpa [x] using hxUi)
  have hemax : e ∈ IsManifold.maximalAtlas I ∞ M :=
    IsManifold.subset_maximalAtlas (I := I) (n := ∞) he
  have heUmax :
      e.subtypeRestr hUnonempty ∈ IsManifold.maximalAtlas I ∞ (U i) := by
    simpa [IsManifold.maximalAtlas] using
      (StructureGroupoid.subtypeRestr_mem_maximalAtlas
        (M := M) (H := H) (G := contDiffGroupoid ∞ I)
        (e := e) he (s := U i) hUnonempty)
  rcases mem_nhdsWithin.mp
      (subtypeRestr_extend_target_mem_nhdsWithin
        (I := I) e (U i) hUnonempty hyUtarget) with
    ⟨u, hu_open, hyu, hutarget⟩
  refine ⟨u, hu_open, hyu, ?_⟩
  exact
    (contDiffOn_coordinateExpression_eq_smoothFormOpenExtensionValue_of_mem
      (I := I) (A := A) (U i) form (alpha i) (hU i) e hUnonempty hemax heUmax).mono
      (by
        intro z hz
        exact hutarget ⟨hz.2, hz.1⟩)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  An open-cover local description gives a smooth form
statement:
  If a pointwise form is given by smooth local forms on an open cover, then it
  is a smooth differential form.
proof:
  Apply the chartwise smoothness criterion on every chart, using the local
  smoothness statement for open covers.
-/
theorem isContMDiffForm_of_eqOn_iSup_open_cover
    [CharZero 𝕜] {ι : Type*}
    (U : ι → TopologicalSpace.Opens M) (hcover : iSup U = ⊤) {n : ℕ}
    (form : (x : M) → FormAt (I := I) (M := M) A n x)
    (alpha : ∀ i : ι, SmoothForms (I := I) (M := U i) A n)
    (hU :
      ∀ i : ι, ∀ ⦃x : M⦄ (hx : x ∈ U i),
        form x =
          smoothFormOpenExtensionValue (I := I) (A := A) (U i) (alpha i) x hx) :
    IsContMDiffForm (I := I) (M := M) (F := A) (n := n) ∞ form := by
  intro e he
  exact contDiffOn_coordinateExpression_of_eqOn_iSup_open_cover
    (I := I) (A := A) U hcover form alpha hU e he

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  The glued pointwise form is smooth
statement:
  If two smooth forms on a two-open cover have zero overlap difference, their
  pointwise glued form is smooth.
proof:
  Use the two-open local smoothness criterion with the left and right branch
  formulas for the glued pointwise form.
-/
theorem isContMDiffForm_smoothFormsTwoOpenGlueFun
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0) :
    IsContMDiffForm (I := I) (M := M) (F := A) (n := n) ∞
      (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta) := by
  exact
    isContMDiffForm_of_eqOn_two_open_cover
      (I := I) (A := A) U V hcover
      (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta)
      alpha beta
      (fun {x} hx => smoothFormsTwoOpenGlueFun_eq_left
        (I := I) (A := A) U V hcover alpha beta (x := x) hx)
      (fun {x} hx => smoothFormsTwoOpenGlueFun_eq_right
        (I := I) (A := A) U V hcover alpha beta hoverlap (x := x) hx)

def smoothFormsTwoOpenGlue
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0) :
    SmoothForms (I := I) (M := M) A n where
  toFun := smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta
  isContMDiff :=
    isContMDiffForm_smoothFormsTwoOpenGlueFun
      (I := I) (A := A) U V hcover alpha beta hoverlap

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Restricting the glued form to \(U\)
statement:
  The smooth form obtained by gluing local forms restricts to the original left
  form on \(U\).
proof:
  Evaluate the restricted form pointwise and use the left branch of the glued
  pointwise form.
-/
theorem restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0) :
    restrictSmoothFormsToOpen (I := I) (A := A) U n
        (smoothFormsTwoOpenGlue (I := I) (A := A) U V hcover alpha beta hoverlap) =
      alpha := by
  apply DifferentialForm.ext
  intro x
  change
    (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta (x : M)).compContinuousLinearMap
        (mfderiv I I (fun y : U => (y : M)) x) =
      alpha.toFun x
  rw [smoothFormsTwoOpenGlueFun_eq_left (I := I) (A := A) U V hcover alpha beta x.2]
  exact smoothFormOpenExtensionValue_restrict (I := I) (A := A) U alpha x

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Restricting the glued form to \(V\)
statement:
  The smooth form obtained by gluing local forms restricts to the original
  right form on \(V\).
proof:
  Evaluate the restricted form pointwise and use the right branch of the glued
  pointwise form.
-/
theorem restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) {n : ℕ}
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0) :
    restrictSmoothFormsToOpen (I := I) (A := A) V n
        (smoothFormsTwoOpenGlue (I := I) (A := A) U V hcover alpha beta hoverlap) =
      beta := by
  apply DifferentialForm.ext
  intro x
  change
    (smoothFormsTwoOpenGlueFun (I := I) (A := A) U V hcover alpha beta (x : M)).compContinuousLinearMap
        (mfderiv I I (fun y : V => (y : M)) x) =
      beta.toFun x
  rw [smoothFormsTwoOpenGlueFun_eq_right
    (I := I) (A := A) U V hcover alpha beta hoverlap x.2]
  exact smoothFormOpenExtensionValue_restrict (I := I) (A := A) V beta x

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  The two restrictions of a global form agree on the overlap
statement:
  Restricting a global smooth form to \(U\) and then to \(U\cap V\) agrees with
  restricting it to \(V\) and then to \(U\cap V\).
proof:
  Compare pointwise values and use equality of the two tangent factorizations
  through the overlap.
-/
theorem restrictSmoothForms_overlap_restrictions_eq
    (U V : TopologicalSpace.Opens M) (n : ℕ)
    (omega : SmoothForms (I := I) (M := M) A n) :
    restrictSmoothFormsOfLE (I := I) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
        (restrictSmoothFormsToOpen (I := I) (A := A) U n omega) =
      restrictSmoothFormsOfLE (I := I) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
        (restrictSmoothFormsToOpen (I := I) (A := A) V n omega) := by
  apply DifferentialForm.ext
  intro x
  ext v
  let W : TopologicalSpace.Opens M := U ⊓ V
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  have hderiv :
      (mfderiv I I (fun y : U => (y : M)) (TopologicalSpace.Opens.inclusion hWU x)).comp
          (mfderiv I I (TopologicalSpace.Opens.inclusion hWU) x) =
        (mfderiv I I (fun y : V => (y : M)) (TopologicalSpace.Opens.inclusion hWV x)).comp
          (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x) :=
    mfderiv_subtypeVal_comp_inclusion_inf_eq (I := I) U V x
  simp only [restrictSmoothFormsOfLE, restrictSmoothFormsToOpen]
  change omega.toFun (x : M)
      (((mfderiv I I (fun y : U => (y : M)) (TopologicalSpace.Opens.inclusion hWU x)).comp
          (mfderiv I I (TopologicalSpace.Opens.inclusion hWU) x)) ∘ v) =
    omega.toFun (x : M)
      (((mfderiv I I (fun y : V => (y : M)) (TopologicalSpace.Opens.inclusion hWV x)).comp
          (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x)) ∘ v)
  rw [hderiv]

/--
%%handwave
name:
  Closed-form restrictions agree on the overlap
statement:
  The two restrictions of a closed global form to \(U\cap V\), through \(U\) or
  through \(V\), are equal.
proof:
  This is the corresponding equality for smooth forms, applied to the
  underlying closed form.
-/
theorem deRhamClosedForms_overlap_restrictions_eq
    (U V : TopologicalSpace.Opens M) (n : ℕ)
    (omega : DeRhamClosedForms (I := I) (M := M) (A := A) n) :
    deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
        (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U n omega) =
      deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
        (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V n omega) := by
  apply Subtype.ext
  exact restrictSmoothForms_overlap_restrictions_eq (I := I) (A := A) U V n omega.1

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Equality of zero-forms from equality on an open subset
statement:
  If two global zero-forms have equal restrictions to an open subset, then
  their values agree at every point of that open subset.
proof:
  Evaluate the restricted equality at the corresponding point and use
  surjectivity of the tangent map of the open inclusion.
-/
theorem smoothForms_eq_of_restrictSmoothFormsToOpen_zero_eq_at
    (U : TopologicalSpace.Opens M)
    (omega eta : SmoothForms (I := I) (M := M) A 0)
    (hU :
      restrictSmoothFormsToOpen (I := I) (A := A) U 0 omega =
        restrictSmoothFormsToOpen (I := I) (A := A) U 0 eta)
    {x : M} (hx : x ∈ U) :
    omega.toFun x = eta.toFun x := by
  let xU : U := ⟨x, hx⟩
  have hpoint :=
    congrArg (fun form : SmoothForms (I := I) (M := U) A 0 => form.toFun xU) hU
  change (omega.toFun x).compContinuousLinearMap
      (mfderiv I I (fun y : U => (y : M)) xU) =
    (eta.toFun x).compContinuousLinearMap
      (mfderiv I I (fun y : U => (y : M)) xU) at hpoint
  ext v
  have happ :=
    congrArg
      (fun form : FormAt (I := I) (M := U) A 0 xU =>
        form (fun i : Fin 0 => (0 : TangentSpace I xU)))
      hpoint
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at happ
  convert happ using 2

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Vanishing of a form from vanishing on an open subset
statement:
  If the restriction of a smooth form to an open subset is zero, then the form
  vanishes at every point of that open subset.
proof:
  Apply the preceding pointwise equality statement with the zero form.
-/
theorem smoothForms_eq_zero_of_restrictSmoothFormsToOpen_zero_eq_at
    (U : TopologicalSpace.Opens M)
    {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) A n)
    (hU : restrictSmoothFormsToOpen (I := I) (A := A) U n omega = 0)
    {x : M} (hx : x ∈ U) :
    omega.toFun x = 0 := by
  let xU : U := ⟨x, hx⟩
  have hpoint :=
    congrArg (fun form : SmoothForms (I := I) (M := U) A n => form.toFun xU) hU
  change (omega.toFun x).compContinuousLinearMap
      (mfderiv I I (fun y : U => (y : M)) xU) = 0 at hpoint
  exact
    continuousAlternatingMap_compContinuousLinearMap_injective
      (mfderiv I I (fun y : U => (y : M)) xU)
      (mfderiv_subtypeVal_surjective (I := I) U xU)
      hpoint

/--
%%handwave
name:
  Closed zero-forms are separated by a two-open cover
statement:
  Two closed zero-forms on a two-open cover are equal if their restrictions to
  both opens are equal.
proof:
  For each point, use the cover to choose an open containing it and apply the
  pointwise equality result for restrictions.
-/
theorem deRhamClosedForms_eq_of_equal_restrictions_zero
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤)
    (omega eta : DeRhamClosedForms (I := I) (M := M) (A := A) 0)
    (hU :
      deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U 0 omega =
        deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U 0 eta)
    (hV :
      deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V 0 omega =
        deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V 0 eta) :
    omega = eta := by
  apply Subtype.ext
  apply DifferentialForm.ext
  intro x
  have hxUV : x ∈ U ∨ x ∈ V := by
    have hx : x ∈ (U ⊔ V : TopologicalSpace.Opens M) := by
      rw [hcover]
      trivial
    simpa using hx
  rcases hxUV with hxU | hxV
  · exact smoothForms_eq_of_restrictSmoothFormsToOpen_zero_eq_at
      (I := I) (A := A) U omega.1 eta.1 (congrArg Subtype.val hU) hxU
  · exact smoothForms_eq_of_restrictSmoothFormsToOpen_zero_eq_at
      (I := I) (A := A) V omega.1 eta.1 (congrArg Subtype.val hV) hxV

/--
%%handwave
name:
  Degree-zero cohomology classes are separated by a two-open cover
statement:
  Two degree-zero de Rham cohomology classes are equal if their restrictions to
  both opens of a cover are equal.
proof:
  Choose closed representatives and reduce to equality of closed zero-forms on
  the two-open cover.
-/
theorem deRham_mayerVietoris_eq_of_equal_restrictions_zero
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤)
    (omega eta : DeRhamCohomology (I := I) (M := M) (A := A) 0)
    (hU :
      deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) U 0 omega =
        deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) U 0 eta)
    (hV :
      deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) V 0 omega =
        deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) V 0 eta) :
    omega = eta := by
  induction omega using Submodule.Quotient.induction_on with
  | _ omega =>
      induction eta using Submodule.Quotient.induction_on with
      | _ eta =>
          simp only [deRhamCohomologyRestrictionToOpen, Submodule.mapQ_apply] at hU hV ⊢
          rw [Submodule.Quotient.eq] at hU hV ⊢
          change omega - eta ∈ DeRhamExactClosedForms (I := I) (M := M) (A := A) 0
          have hU' :
              deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U 0 omega =
                deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U 0 eta := by
            rw [← sub_eq_zero]
            exact (Submodule.mem_bot 𝕜).mp
              (show
                (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U 0 omega -
                  deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U 0 eta) ∈
                    (⊥ :
                      Submodule 𝕜
                        (DeRhamClosedForms (I := I) (M := U) (A := A) 0)) by
                  simpa [DeRhamExactClosedForms, DeRhamExactForms] using hU)
          have hV' :
              deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V 0 omega =
                deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V 0 eta := by
            rw [← sub_eq_zero]
            exact (Submodule.mem_bot 𝕜).mp
              (show
                (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V 0 omega -
                  deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V 0 eta) ∈
                    (⊥ :
                      Submodule 𝕜
                        (DeRhamClosedForms (I := I) (M := V) (A := A) 0)) by
                  simpa [DeRhamExactClosedForms, DeRhamExactForms] using hV)
          have homega_eta :
              omega = eta :=
            deRhamClosedForms_eq_of_equal_restrictions_zero
              (I := I) (A := A) U V hcover omega eta hU' hV'
          rw [homega_eta]
          simp [DeRhamExactClosedForms]

/--
%%handwave
name:
  Degree-zero Mayer-Vietoris restriction is injective
statement:
  For a two-open cover, the restriction map on degree-zero de Rham cohomology
  is injective.
proof:
  If two classes have equal pairs of restrictions, apply separatedness of
  degree-zero classes under the cover.
-/
theorem deRham_mayerVietoris_restriction_injective_zero
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) :
    Function.Injective (deRhamMayerVietorisRestriction (I := I) (A := A) U V 0) := by
  intro omega eta homega_eta
  have hU :
      deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) U 0 omega =
        deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) U 0 eta := by
    simpa [deRhamMayerVietorisRestriction] using congrArg Prod.fst homega_eta
  have hV :
      deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) V 0 omega =
        deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) V 0 eta := by
    simpa [deRhamMayerVietorisRestriction] using congrArg Prod.snd homega_eta
  exact deRham_mayerVietoris_eq_of_equal_restrictions_zero
    (I := I) (A := A) U V hcover omega eta hU hV

/--
%%handwave
name:
  Cohomology restrictions agree on the overlap
statement:
  The two ways of restricting a global de Rham cohomology class to
  \(U\cap V\) agree.
proof:
  Descend the equality of closed-form restrictions to the quotient by exact
  forms.
-/
theorem deRham_mayerVietoris_overlap_restrictions_eq
    (U V : TopologicalSpace.Opens M) (n : ℕ)
    (omega : DeRhamCohomology (I := I) (M := M) (A := A) n) :
    deRhamCohomologyRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
        (deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) U n omega) =
      deRhamCohomologyRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
        (deRhamCohomologyRestrictionToOpen (I := I) (M := M) (A := A) V n omega) := by
  induction omega using Submodule.Quotient.induction_on with
  | _ omega =>
      simp only [deRhamCohomologyRestrictionToOpen, deRhamCohomologyRestrictionOfLE,
        Submodule.mapQ_apply]
      exact congrArg
        ((DeRhamExactClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n).mkQ)
        (deRhamClosedForms_overlap_restrictions_eq (I := I) (A := A) U V n omega)

/--
%%handwave
name:
  The Mayer-Vietoris difference vanishes after restriction
statement:
  Restricting a global cohomology class to \(U\) and \(V\), then taking the
  overlap difference, gives zero.
proof:
  The two overlap restrictions of a global class are equal, so their difference
  is zero.
-/
theorem deRham_mayerVietoris_difference_restriction_eq_zero
    (U V : TopologicalSpace.Opens M) (n : ℕ)
    (omega : DeRhamCohomology (I := I) (M := M) (A := A) n) :
    deRhamMayerVietorisDifference (I := I) (A := A) U V n
      (deRhamMayerVietorisRestriction (I := I) (A := A) U V n omega) = 0 := by
  rw [deRhamMayerVietorisDifference, deRhamMayerVietorisRestriction]
  exact sub_eq_zero.mpr
    (deRham_mayerVietoris_overlap_restrictions_eq (I := I) (A := A) U V n omega)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Restriction has zero overlap difference
statement:
  If a smooth form on \(M\) is restricted to \(U\) and \(V\), then the two
  resulting restrictions agree on \(U\cap V\), so their difference there is zero.
proof:
  Expand the smooth restriction and difference maps, then use equality of the two
  iterated restrictions to the overlap.
-/
theorem deRham_mayerVietoris_smooth_difference_restriction_eq_zero
    (U V : TopologicalSpace.Opens M) (n : ℕ)
    (omega : SmoothForms (I := I) (M := M) A n) :
    deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n
      (deRhamMayerVietorisSmoothRestriction (I := I) (A := A) U V n omega) = 0 := by
  rw [deRhamMayerVietorisSmoothDifference, deRhamMayerVietorisSmoothRestriction]
  exact sub_eq_zero.mpr
    (restrictSmoothForms_overlap_restrictions_eq (I := I) (A := A) U V n omega)

def openInOpen (U V : TopologicalSpace.Opens M) : TopologicalSpace.Opens U where
  carrier := {x : U | (x : M) ∈ V}
  is_open' := by
    change IsOpen ((fun x : U => (x : M)) ⁻¹' (V : Set M))
    exact V.2.preimage continuous_subtype_val

/--
%%handwave
name:
  Membership in an open subset inside an open subset
statement:
  A point of \(U\) lies in the open subset cut out by \(V\) exactly when its
  underlying point of \(M\) lies in \(V\).
proof:
  This is the defining membership condition for the induced open subset.
-/
@[simp]
theorem mem_openInOpen
    (U V : TopologicalSpace.Opens M) (x : U) :
    x ∈ openInOpen U V ↔ (x : M) ∈ V :=
  Iff.rfl

def openInOpenEquivInf (U V : TopologicalSpace.Opens M) :
    openInOpen U V ≃ (U ⊓ V : TopologicalSpace.Opens M) where
  toFun x := ⟨((x : U) : M), ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨(x : M), x.2.1⟩, x.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/--
%%handwave
name:
  The overlap equivalence preserves the underlying point
statement:
  The canonical equivalence between \(V\) inside \(U\) and \(U\cap V\) does not
  change the underlying point of \(M\).
proof:
  The equivalence is defined by repackaging the same point with the two
  membership proofs.
-/
@[simp]
theorem openInOpenEquivInf_apply_coe
    (U V : TopologicalSpace.Opens M) (x : openInOpen U V) :
    ((openInOpenEquivInf U V x : (U ⊓ V : TopologicalSpace.Opens M)) : M) =
      ((x : U) : M) :=
  rfl

/--
%%handwave
name:
  The inverse overlap equivalence preserves the underlying point
statement:
  The inverse of the canonical equivalence from \(V\) inside \(U\) to
  \(U\cap V\) does not change the underlying point of \(M\).
proof:
  The inverse equivalence is also only a repackaging of the same point with its
  membership proofs.
-/
@[simp]
theorem openInOpenEquivInf_symm_apply_coe
    (U V : TopologicalSpace.Opens M) (x : (U ⊓ V : TopologicalSpace.Opens M)) :
    (((openInOpenEquivInf U V).symm x : U) : M) = (x : M) :=
  rfl

def openInOpenInfFormFun
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (omega : SmoothForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n) :
    (x : openInOpen U V) → FormAt (I := I) (M := openInOpen U V) A n x :=
  fun x =>
    (smoothFormOpenExtensionValue (I := I) (A := A)
        (U ⊓ V : TopologicalSpace.Opens M) omega
        ((x : U) : M) ⟨(x : U).2, x.2⟩).compContinuousLinearMap
      ((mfderiv I I (fun z : U => (z : M)) (x : U)).comp
        (mfderiv I I (fun y : openInOpen U V => (y : U)) x))

omit [IsRCLikeNormedField 𝕜] [ChartedSpace H M] [IsManifold I ∞ M] in
/--
%%handwave
name:
  A chart for the nested overlap lands in the overlap chart
statement:
  If a coordinate point lies in the target of a chart restricted first to \(U\)
  and then to \(V\), then it lies in the target of the same chart restricted to
  \(U\cap V\).
proof:
  Unpack the chart targets and replace the nested subtype point by the
  corresponding point of the intersection.
-/
theorem openInOpenInfForm_target_subset
    (U V : TopologicalSpace.Opens M)
    (e : OpenPartialHomeomorph M H)
    (hU : Nonempty U)
    (hWU : Nonempty (openInOpen U V))
    (hW : Nonempty (U ⊓ V : TopologicalSpace.Opens M))
    {y : E}
    (hy : ((((e.subtypeRestr hU).subtypeRestr hWU).extend I).target : Set E) y) :
    y ∈ ((e.subtypeRestr hW).extend I).target := by
  rw [OpenPartialHomeomorph.extend_target] at hy ⊢
  constructor
  · rw [← OpenPartialHomeomorph.image_source_eq_target] at hy ⊢
    rcases hy.1 with ⟨x, hx, hxmap⟩
    let xW : (U ⊓ V : TopologicalSpace.Opens M) :=
      ⟨(((x : openInOpen U V) : U) : M),
        ⟨((x : openInOpen U V) : U).2, (x : openInOpen U V).2⟩⟩
    refine ⟨xW, ?_, ?_⟩
    · simpa [xW, OpenPartialHomeomorph.subtypeRestr_source] using hx
    · simpa [xW] using hxmap
  · exact hy.2

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Coordinate expression of the induced overlap form
statement:
  The coordinate representative of the form obtained by viewing a form on
  \(U\cap V\) as a form on \(V\) inside \(U\) agrees with the original coordinate
  representative on the corresponding restricted chart.
proof:
  Rewrite both coordinate expressions, compare the derivatives of the subtype
  inclusions, and cancel the invertible derivative used in the subtype chart.
-/
theorem coordinateExpression_openInOpenInfForm_subtypeRestr
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (omega : SmoothForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n)
    (e : OpenPartialHomeomorph M H)
    (hU : Nonempty U)
    (hWU : Nonempty (openInOpen U V))
    (hW : Nonempty (U ⊓ V : TopologicalSpace.Opens M))
    (he : e ∈ atlas H M)
    (heU : e.subtypeRestr hU ∈ atlas H U)
    (heWU : (e.subtypeRestr hU).subtypeRestr hWU ∈ atlas H (openInOpen U V))
    (heW : e.subtypeRestr hW ∈ atlas H (U ⊓ V : TopologicalSpace.Opens M))
    {y : E} (hy : y ∈ (((e.subtypeRestr hU).subtypeRestr hWU).extend I).target) :
    coordinateExpression (I := I) (F := A) (n := n)
        (openInOpenInfFormFun (I := I) (A := A) U V omega)
        ((e.subtypeRestr hU).subtypeRestr hWU) y =
      coordinateExpression (I := I) (F := A) (n := n)
        omega.toFun (e.subtypeRestr hW) y := by
  let eU : OpenPartialHomeomorph U H := e.subtypeRestr hU
  let eWU : OpenPartialHomeomorph (openInOpen U V) H := eU.subtypeRestr hWU
  let eW : OpenPartialHomeomorph (U ⊓ V : TopologicalSpace.Opens M) H :=
    e.subtypeRestr hW
  have hyU : y ∈ (eU.extend I).target :=
    subtypeRestr_extend_target_subset (I := I) (M := U) eU (openInOpen U V) hWU hy
  have hyW : y ∈ (eW.extend I).target :=
    openInOpenInfForm_target_subset (I := I) U V e hU hWU hW hy
  let xWU : openInOpen U V := (eWU.extend I).symm y
  let xU : U := (eU.extend I).symm y
  let xW : (U ⊓ V : TopologicalSpace.Opens M) := (eW.extend I).symm y
  let xM : M := (e.extend I).symm y
  have hpointWU_U : (xWU : U) = xU := by
    simpa [xWU, xU, eWU, eU] using
      subtypeRestr_extend_symm_coe (I := I) (M := U) eU (openInOpen U V) hWU hy
  have hpointU_M : (xU : M) = xM := by
    simpa [xU, xM, eU] using
      subtypeRestr_extend_symm_coe (I := I) e U hU hyU
  have hpointW_M : (xW : M) = xM := by
    simpa [xW, xM, eW] using
      subtypeRestr_extend_symm_coe (I := I) e
        (U ⊓ V : TopologicalSpace.Opens M) hW hyW
  have hpointWU_W : (((xWU : openInOpen U V) : U) : M) = (xW : M) := by
    exact (congrArg (fun z : U => (z : M)) hpointWU_U).trans
      (hpointU_M.trans hpointW_M.symm)
  let DUW : E →L[𝕜] TangentSpace I xWU :=
    mfderivWithin 𝓘(𝕜, E) I (eWU.extend I).symm (eWU.extend I).target y
  let DU : E →L[𝕜] TangentSpace I xU :=
    mfderivWithin 𝓘(𝕜, E) I (eU.extend I).symm (eU.extend I).target y
  let DW : E →L[𝕜] TangentSpace I xW :=
    mfderivWithin 𝓘(𝕜, E) I (eW.extend I).symm (eW.extend I).target y
  let DM : E →L[𝕜] TangentSpace I xM :=
    mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (e.extend I).target y
  have hWU_U :
      (mfderiv I I (fun z : openInOpen U V => (z : U)) xWU).comp DUW = DU := by
    simpa [xWU, xU, eWU, eU, DUW, DU] using
      mfderiv_subtypeVal_comp_subtypeRestr_extend_symm
        (I := I) (M := U) eU (openInOpen U V) hWU heU heWU hy
  have hU_M :
      (mfderiv I I (fun z : U => (z : M)) xU).comp DU = DM := by
    simpa [xU, xM, eU, DU, DM] using
      mfderiv_subtypeVal_comp_subtypeRestr_extend_symm (I := I) e U hU he heU hyU
  have hW_M :
      (mfderiv I I (fun z : (U ⊓ V : TopologicalSpace.Opens M) => (z : M)) xW).comp DW =
        DM := by
    simpa [xW, xM, eW, DW, DM] using
      mfderiv_subtypeVal_comp_subtypeRestr_extend_symm
        (I := I) e (U ⊓ V : TopologicalSpace.Opens M) hW he heW hyW
  rw [coordinateExpression, coordinateExpression, openInOpenInfFormFun]
  change
    ((smoothFormOpenExtensionValue (I := I) (A := A)
        (U ⊓ V : TopologicalSpace.Opens M) omega (((xWU : openInOpen U V) : U) : M) _).compContinuousLinearMap
        ((mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp
          (mfderiv I I (fun z : openInOpen U V => (z : U)) xWU))).compContinuousLinearMap DUW =
      (omega.toFun xW).compContinuousLinearMap DW
  rw [smoothFormOpenExtensionValue]
  have hxW_eq :
      (⟨(((xWU : openInOpen U V) : U) : M),
        ⟨((xWU : openInOpen U V) : U).2, (xWU : openInOpen U V).2⟩⟩ :
          (U ⊓ V : TopologicalSpace.Opens M)) = xW := by
    apply Subtype.ext
    exact hpointWU_W
  rw [hxW_eq]
  have hnested :
      (((mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp
          (mfderiv I I (fun z : openInOpen U V => (z : U)) xWU)).comp DUW) =
        (mfderiv I I (fun z : (U ⊓ V : TopologicalSpace.Opens M) => (z : M)) xW).comp DW := by
    have hleft :
        (((mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp
            (mfderiv I I (fun z : openInOpen U V => (z : U)) xWU)).comp DUW) =
          (mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp DU := by
      calc
        (((mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp
            (mfderiv I I (fun z : openInOpen U V => (z : U)) xWU)).comp DUW)
            =
          (mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp
            ((mfderiv I I (fun z : openInOpen U V => (z : U)) xWU).comp DUW) := rfl
        _ =
          (mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp DU := by
            rw [hWU_U]
    have hright :
        (mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp DU =
          (mfderiv I I (fun z : (U ⊓ V : TopologicalSpace.Opens M) => (z : M)) xW).comp DW := by
      have hcast :
          (mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp DU =
            (mfderiv I I (fun z : U => (z : M)) xU).comp DU := by
        rw [hpointWU_U]
      exact hcast.trans (hU_M.trans hW_M.symm)
    exact hleft.trans hright
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (omega.toFun xW)
  funext i
  have hL :
      (mfderiv I I (fun z : (U ⊓ V : TopologicalSpace.Opens M) => (z : M)) xW).IsInvertible :=
    mfderiv_subtypeVal_isInvertible (I := I)
      (U ⊓ V : TopologicalSpace.Opens M) xW
  let LW : TangentSpace I xW →L[𝕜] TangentSpace I (xW : M) :=
    mfderiv I I (fun z : (U ⊓ V : TopologicalSpace.Opens M) => (z : M)) xW
  let LN : TangentSpace I xWU →L[𝕜] TangentSpace I (xW : M) :=
    (mfderiv I I (fun z : U => (z : M)) ((xWU : openInOpen U V) : U)).comp
      (mfderiv I I (fun z : openInOpen U V => (z : U)) xWU)
  have hnested_apply :
      LN (DUW (v i)) = LW (DW (v i)) := by
    simpa [LN, LW] using congrArg (fun L : E →L[𝕜] TangentSpace I (xW : M) => L (v i)) hnested
  calc
    LW.inverse (LN (DUW (v i))) =
      LW.inverse (LW (DW (v i))) := by
        rw [hnested_apply]
    _ = DW (v i) :=
      (by
        change LW.IsInvertible at hL
        exact hL.inverse_apply_self (DW (v i)))

def openInOpenInfForm
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (omega : SmoothForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n) :
    SmoothForms (I := I) (M := openInOpen U V) A n where
  toFun := openInOpenInfFormFun (I := I) (A := A) U V omega
  isContMDiff := by
    intro e he
    have hWU : Nonempty (openInOpen U V) := by
      change e ∈
        (⋃ x : openInOpen U V,
          ({(chartAt H (((x : openInOpen U V) : U))).subtypeRestr ⟨x⟩} :
            Set (OpenPartialHomeomorph (openInOpen U V) H))) at he
      rw [Set.mem_iUnion] at he
      rcases he with ⟨x, _hx⟩
      exact ⟨x⟩
    rcases TopologicalSpace.Opens.chart_eq hWU he with ⟨x, rfl⟩
    let xU : U := (x : openInOpen U V)
    let xW : (U ⊓ V : TopologicalSpace.Opens M) :=
      ⟨(xU : M), ⟨xU.2, x.2⟩⟩
    let hU : Nonempty U := ⟨xU⟩
    let hW : Nonempty (U ⊓ V : TopologicalSpace.Opens M) := ⟨xW⟩
    let eM : OpenPartialHomeomorph M H := chartAt H (xU : M)
    have heM : eM ∈ atlas H M := by
      simp [eM]
    have heU : eM.subtypeRestr hU ∈ atlas H U := by
      dsimp [eM, hU]
      change chartAt H xU ∈ atlas H U
      exact chart_mem_atlas H xU
    have heWU : (eM.subtypeRestr hU).subtypeRestr hWU ∈ atlas H (openInOpen U V) := by
      dsimp [eM, hU, hWU]
      change chartAt H x ∈ atlas H (openInOpen U V)
      exact chart_mem_atlas H x
    have heW : eM.subtypeRestr hW ∈ atlas H (U ⊓ V : TopologicalSpace.Opens M) := by
      dsimp [eM, hW, xW]
      change chartAt H ⟨(xU : M), ⟨xU.2, x.2⟩⟩ ∈
        atlas H (U ⊓ V : TopologicalSpace.Opens M)
      exact chart_mem_atlas H
        (⟨(xU : M), ⟨xU.2, x.2⟩⟩ :
          (U ⊓ V : TopologicalSpace.Opens M))
    have hsubset :
        (((eM.subtypeRestr hU).subtypeRestr hWU).extend I).target ⊆
          ((eM.subtypeRestr hW).extend I).target := by
      intro y hy
      exact openInOpenInfForm_target_subset (I := I) U V eM hU hWU hW hy
    refine ((omega.isContMDiff (eM.subtypeRestr hW) heW).mono hsubset).congr ?_
    intro y hy
    simpa [eM] using
      coordinateExpression_openInOpenInfForm_subtypeRestr
        (I := I) (A := A) U V omega eM hU hWU hW heM heU heWU heW hy

def supportComplInOpen
    (U : TopologicalSpace.Opens M) (χ : C^∞⟮I, M; 𝕜⟯) :
    TopologicalSpace.Opens U where
  carrier := {x : U | (x : M) ∉ tsupport χ}
  is_open' := by
    change IsOpen ((fun x : U => (x : M)) ⁻¹' ((tsupport χ)ᶜ : Set M))
    exact (isClosed_tsupport χ).isOpen_compl.preimage continuous_subtype_val

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  Membership in the support-complement open subset
statement:
  A point of \(U\) lies in the open subset complementary to the support of
  \(\chi\) exactly when its underlying point is outside the support of \(\chi\).
proof:
  This is the defining membership condition for the support-complement open
  subset.
-/
@[simp]
theorem mem_supportComplInOpen
    (U : TopologicalSpace.Opens M) (χ : C^∞⟮I, M; 𝕜⟯) (x : U) :
    x ∈ supportComplInOpen (I := I) U χ ↔ (x : M) ∉ tsupport χ :=
  Iff.rfl

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  A smooth function vanishes outside its support
statement:
  If a point is not in the topological support of a smooth function, then the
  function has value zero at that point.
proof:
  Otherwise the point belongs to the support by the basic containment of the
  nonzero locus in the support.
-/
theorem smoothFunction_eq_zero_of_notMem_tsupport
    (χ : C^∞⟮I, M; 𝕜⟯) {x : M} (hx : x ∉ tsupport χ) :
    χ x = 0 := by
  by_contra hχx
  exact hx (subset_tsupport χ hχx)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  A supported scalar multiple vanishes outside the support
statement:
  Multiplying a smooth form by a smooth function gives zero at every point
  outside the support of the function.
proof:
  The scalar is zero outside its support, so the pointwise scalar multiple of the
  form is zero.
-/
theorem smoothFormsPointwiseSMul_eq_zero_of_notMem_tsupport
    {n : ℕ} (χ : C^∞⟮I, M; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := M) A n)
    {x : M} (hx : x ∉ tsupport χ) :
    (smoothFormsPointwiseSMul (I := I) (A := A) χ omega).toFun x = 0 := by
  simp [smoothFormsPointwiseSMul, smoothFunction_eq_zero_of_notMem_tsupport (I := I) χ hx]

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Restricting a zero scalar multiple gives zero
statement:
  If a smooth function vanishes on an open subset \(W\subset V\), then the
  restriction to \(W\) of its pointwise product with a smooth form on \(V\) is
  the zero form.
proof:
  Check equality pointwise and use the assumed vanishing of the scalar on every
  point of \(W\).
-/
theorem restrictSmoothFormsOfLE_smoothFormsPointwiseSMul_eq_zero
    {W V : TopologicalSpace.Opens M} (hWV : W ≤ V) {n : ℕ}
    (f : C^∞⟮I, V; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := V) A n)
    (hzero : ∀ x : W, f (TopologicalSpace.Opens.inclusion hWV x) = 0) :
    restrictSmoothFormsOfLE (I := I) (A := A) hWV n
        (smoothFormsPointwiseSMul (I := I) (M := V) (A := A) f omega) = 0 := by
  apply DifferentialForm.ext
  intro x
  ext v
  change
    ((f (TopologicalSpace.Opens.inclusion hWV x)) •
        omega.toFun (TopologicalSpace.Opens.inclusion hWV x)).compContinuousLinearMap
          (mfderiv I I (TopologicalSpace.Opens.inclusion hWV) x) v =
      0
  rw [hzero x]
  simp

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  The restricted cutoff vanishes on the support-complement overlap
statement:
  On the part of \(V\) inside \(U\) that also lies outside the support of
  \(\chi\), the restriction of \(\chi\) is zero.
proof:
  Apply vanishing outside the support to the underlying point of the nested open
  subset.
-/
theorem smoothFunctionRestrictToOpenInOpen_eq_zero_on_supportCompl
    (U V : TopologicalSpace.Opens M)
    (χ : C^∞⟮I, M; 𝕜⟯)
    (x :
      ((openInOpen U V) ⊓ supportComplInOpen (I := I) U χ :
        TopologicalSpace.Opens U)) :
    smoothFunctionRestrictToOpen (I := I) (M := U) (openInOpen U V)
        (smoothFunctionRestrictToOpen (I := I) (M := M) U χ)
        (TopologicalSpace.Opens.inclusion inf_le_left x) = 0 := by
  exact smoothFunction_eq_zero_of_notMem_tsupport (I := I) χ x.2.2

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  The cutoff multiple vanishes on the support-complement overlap
statement:
  The restriction of the cutoff multiple of a form on \(V\) inside \(U\) to the
  overlap with the complement of the cutoff support is zero.
proof:
  Use the preceding vanishing of the restricted cutoff and the general
  pointwise-vanishing restriction lemma.
-/
theorem restrictSmoothFormsOfLE_smul_openInOpen_supportCompl_eq_zero
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (χ : C^∞⟮I, M; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := openInOpen U V) A n) :
    restrictSmoothFormsOfLE (I := I) (A := A)
        (W := ((openInOpen U V) ⊓ supportComplInOpen (I := I) U χ :
          TopologicalSpace.Opens U))
        (V := openInOpen U V) inf_le_left n
        (smoothFormsPointwiseSMul (I := I) (M := openInOpen U V) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := U) (openInOpen U V)
            (smoothFunctionRestrictToOpen (I := I) (M := M) U χ))
          omega) = 0 := by
  exact
    restrictSmoothFormsOfLE_smoothFormsPointwiseSMul_eq_zero
      (I := I) (A := A)
      (W := ((openInOpen U V) ⊓ supportComplInOpen (I := I) U χ :
        TopologicalSpace.Opens U))
      (V := openInOpen U V) inf_le_left
      (smoothFunctionRestrictToOpen (I := I) (M := U) (openInOpen U V)
        (smoothFunctionRestrictToOpen (I := I) (M := M) U χ))
      omega
      (smoothFunctionRestrictToOpenInOpen_eq_zero_on_supportCompl (I := I) U V χ)

omit [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M] in
/--
%%handwave
name:
  The overlap and support-complement cover \(U\)
statement:
  If the support of \(\chi\) is contained in \(V\), then inside \(U\) the open
  subset cut out by \(V\) together with the complement of the support of
  \(\chi\) covers all of \(U\).
proof:
  At a point of \(U\), either the underlying point lies in \(V\), or it does not;
  in the second case it cannot lie in the support of \(\chi\).
-/
theorem openInOpen_sup_supportComplInOpen_eq_top
    (U V : TopologicalSpace.Opens M) (χ : C^∞⟮I, M; 𝕜⟯)
    (hχ : tsupport χ ⊆ (V : Set M)) :
    openInOpen U V ⊔ supportComplInOpen (I := I) U χ = ⊤ := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    by_cases hxV : (x : M) ∈ V
    · exact Or.inl hxV
    · exact Or.inr (fun hxχ => hxV (hχ hxχ))

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Restriction is compatible with equal open subsets
statement:
  If two open subsets \(W\) and \(W'\) of \(M\) are equal as sets, then
  restricting a form from \(V\) to \(W\) agrees with restricting it to \(W'\)
  after transporting along the equality of opens.
proof:
  Destructure the two open subsets, reduce the equality of opens to reflexivity,
  and compare the resulting restricted forms pointwise.
-/
theorem restrictSmoothFormsOfLE_cast_of_opens_ext
    {W W' V : TopologicalSpace.Opens M} (hWW' : (W : Set M) = W')
    (hWV : W ≤ V) (hW'V : W' ≤ V) {n : ℕ}
    (beta : SmoothForms (I := I) (M := V) A n) :
    (TopologicalSpace.Opens.ext hWW') ▸
        restrictSmoothFormsOfLE (I := I) (A := A)
          (W := W) (V := V) hWV n beta =
      restrictSmoothFormsOfLE (I := I) (A := A)
        (W := W') (V := V) hW'V n beta := by
  cases W with
  | mk W hWopen =>
      cases W' with
      | mk W' hW'open =>
          cases hWW'
          apply DifferentialForm.ext
          intro x
          simp [restrictSmoothFormsOfLE, restrictSmoothFormOfLE]

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Pointwise multiplication is compatible with equal open subsets
statement:
  If two open subsets are equal as sets, then multiplying a transported form by
  the correspondingly restricted function agrees with transporting the product.
proof:
  Reduce the equality of opens to reflexivity and compare the pointwise
  definitions.
-/
theorem smoothFormsPointwiseSMul_cast_of_opens_ext
    {W W' : TopologicalSpace.Opens M} (hWW' : (W : Set M) = W') {n : ℕ}
    (χ : C^∞⟮I, M; 𝕜⟯)
    (omega : SmoothForms (I := I) (M := W) A n) :
    (TopologicalSpace.Opens.ext hWW') ▸
        smoothFormsPointwiseSMul (I := I) (M := W) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := M) W χ) omega =
      smoothFormsPointwiseSMul (I := I) (M := W') (A := A)
        (smoothFunctionRestrictToOpen (I := I) (M := M) W' χ)
        ((TopologicalSpace.Opens.ext hWW') ▸ omega) := by
  cases W with
  | mk W hWopen =>
      cases W' with
      | mk W' hW'open =>
          cases hWW'
          apply DifferentialForm.ext
          intro x
          simp [smoothFormsPointwiseSMul, smoothFunctionRestrictToOpen]

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Extending a cutoff multiple from the left open set
statement:
  If the support of \(\chi\) is contained in \(V\), then the product
  \(\chi\omega\) on \(U\cap V\) is the restriction of a smooth form on \(U\).
proof:
  View \(\omega\) on the overlap inside \(U\), cover \(U\) by the overlap and
  the complement of the support of \(\chi\), glue the cutoff multiple on the
  overlap with the zero form on the complement, and use the vanishing on their
  overlap to prove the gluing condition.
-/
theorem smoothFormsPointwiseSMul_extendByZero_left
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (χ : C^∞⟮I, M; 𝕜⟯)
    (hχ : tsupport χ ⊆ (V : Set M))
    (omega :
      SmoothForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n) :
    ∃ alpha : SmoothForms (I := I) (M := U) A n,
      restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha =
        smoothFormsPointwiseSMul (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A)
      (smoothFunctionRestrictToOpen (I := I) (M := M)
            (U ⊓ V : TopologicalSpace.Opens M) χ)
          omega := by
  let W : TopologicalSpace.Opens M := U ⊓ V
  let WU : TopologicalSpace.Opens U := openInOpen U V
  let ZU : TopologicalSpace.Opens U := supportComplInOpen (I := I) U χ
  let omegaWU : SmoothForms (I := I) (M := WU) A n :=
    openInOpenInfForm (I := I) (A := A) U V omega
  let χU : C^∞⟮I, U; 𝕜⟯ :=
    smoothFunctionRestrictToOpen (I := I) (M := M) U χ
  let χWU : C^∞⟮I, WU; 𝕜⟯ :=
    smoothFunctionRestrictToOpen (I := I) (M := U) WU χU
  let alphaWU : SmoothForms (I := I) (M := WU) A n :=
    smoothFormsPointwiseSMul (I := I) (M := WU) (A := A) χWU omegaWU
  have hcover : WU ⊔ ZU = ⊤ := by
    simpa [WU, ZU] using
      openInOpen_sup_supportComplInOpen_eq_top (I := I) U V χ hχ
  have hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (M := U) (A := A)
          WU ZU n (alphaWU, 0) = 0 := by
    rw [deRhamMayerVietorisSmoothDifference]
    have hleft :
        restrictSmoothFormsOfLE (I := I) (M := U) (A := A)
            (W := (WU ⊓ ZU : TopologicalSpace.Opens U)) (V := WU) inf_le_left n
            alphaWU = 0 := by
      simpa [WU, ZU, alphaWU, omegaWU, χWU, χU] using
        restrictSmoothFormsOfLE_smul_openInOpen_supportCompl_eq_zero
          (I := I) (A := A) U V χ
          (openInOpenInfForm (I := I) (A := A) U V omega)
    rw [hleft]
    simp
  let alpha : SmoothForms (I := I) (M := U) A n :=
    smoothFormsTwoOpenGlue (I := I) (M := U) (A := A)
      WU ZU hcover alphaWU 0 hoverlap
  refine ⟨alpha, ?_⟩
  have hglue :
      restrictSmoothFormsToOpen (I := I) (M := U) (A := A) WU n alpha = alphaWU := by
    simpa [alpha] using
      restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left
        (I := I) (M := U) (A := A) WU ZU hcover alphaWU 0 hoverlap
  apply DifferentialForm.ext
  intro x
  let xWU : WU := (openInOpenEquivInf U V).symm x
  let xU : U := TopologicalSpace.Opens.inclusion (inf_le_left : W ≤ U) x
  let LU : TangentSpace I xU →L[𝕜] TangentSpace I (xU : M) :=
    mfderiv I I (fun y : U => (y : M)) xU
  let LWU : TangentSpace I xWU →L[𝕜] TangentSpace I xU :=
    mfderiv I I (fun y : WU => (y : U)) xWU
  let LW : TangentSpace I x →L[𝕜] TangentSpace I xU :=
    mfderiv I I (TopologicalSpace.Opens.inclusion (inf_le_left : W ≤ U)) x
  let LWM : TangentSpace I x →L[𝕜] TangentSpace I (x : M) :=
    mfderiv I I (fun y : W => (y : M)) x
  let η : FormAt (I := I) (M := M) A n (x : M) :=
    smoothFormOpenExtensionValue (I := I) (A := A) W omega (x : M) x.2
  have hxWU_U : (xWU : U) = xU := by
    apply Subtype.ext
    rfl
  have hpoint :=
    congrArg (fun form : SmoothForms (I := I) (M := WU) A n => form.toFun xWU) hglue
  have hpoint' :
      (alpha.toFun xU).compContinuousLinearMap LWU =
        (χ (x : M)) •
          η.compContinuousLinearMap (LU.comp LWU) := by
    simpa [alphaWU, omegaWU, χWU, χU, openInOpenInfForm, openInOpenInfFormFun,
      smoothFormsPointwiseSMul, smoothFunctionRestrictToOpen, W, WU, xWU, xU,
      LU, LWU, η, hxWU_U] using hpoint
  have halpha :
      alpha.toFun xU = ((χ (x : M)) • η.compContinuousLinearMap LU) := by
    apply continuousAlternatingMap_compContinuousLinearMap_injective LWU
    · simpa [LWU] using mfderiv_subtypeVal_surjective (I := I) (M := U) WU xWU
    · change (alpha.toFun xU).compContinuousLinearMap LWU =
        (((χ (x : M)) • η.compContinuousLinearMap LU).compContinuousLinearMap LWU)
      rw [hpoint']
      ext v
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.smul_apply]
      rfl
  ext v
  change (alpha.toFun xU).compContinuousLinearMap LW v =
      ((χ (x : M)) • omega.toFun x) v
  rw [halpha]
  have hfactor : LU.comp LW = LWM := by
    simpa [W, xU, LU, LW, LWM] using
      mfderiv_subtypeVal_comp_inclusion_eq
        (I := I) W U (inf_le_left : W ≤ U) x
  have hη : η.compContinuousLinearMap LWM = omega.toFun x := by
    simpa [W, η, LWM] using
      smoothFormOpenExtensionValue_restrict (I := I) (A := A) W omega x
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply]
  change (χ (x : M)) • η (fun i => LU (LW (v i))) =
    (χ (x : M)) • omega.toFun x v
  have harg :
      (fun i => LU (LW (v i))) = fun i => LWM (v i) := by
    funext i
    exact congrArg (fun L : TangentSpace I x →L[𝕜] TangentSpace I (x : M) => L (v i))
      hfactor
  rw [harg]
  exact congrArg (fun form : FormAt (I := I) (M := M) A n (x : M) =>
    (χ (x : M)) • form v) hη

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Transporting the right extension across the swapped overlap
statement:
  A cutoff multiple extended from \(V\) over \(V\cap U\) gives the expected
  cutoff multiple on \(U\cap V\) after transporting along the symmetry of
  intersection.
proof:
  Identify \(U\cap V\) and \(V\cap U\) as equal open subsets, transport both the
  restriction and the scalar multiple across this equality, and convert the
  resulting heterogeneous equality back to an equality.
-/
theorem smoothFormsPointwiseSMul_extendByZero_inf_comm_transport
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (χ : C^∞⟮I, M; 𝕜⟯)
    (omega :
      SmoothForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hbeta :
      restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (V ⊓ U : TopologicalSpace.Opens M)) (V := V) inf_le_left n beta =
        smoothFormsPointwiseSMul (I := I)
          (M := (V ⊓ U : TopologicalSpace.Opens M)) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := M)
            (V ⊓ U : TopologicalSpace.Opens M) χ)
          ((inf_comm U V) ▸ omega)) :
    restrictSmoothFormsOfLE (I := I) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta =
      smoothFormsPointwiseSMul (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A)
        (smoothFunctionRestrictToOpen (I := I) (M := M)
          (U ⊓ V : TopologicalSpace.Opens M) χ)
        omega := by
  let hset :
      ((U ⊓ V : TopologicalSpace.Opens M) : Set M) =
        (V ⊓ U : TopologicalSpace.Opens M) :=
    by
      ext x
      constructor
      · intro hx
        exact ⟨hx.2, hx.1⟩
      · intro hx
        exact ⟨hx.2, hx.1⟩
  let hW :
      (U ⊓ V : TopologicalSpace.Opens M) =
        (V ⊓ U : TopologicalSpace.Opens M) :=
    TopologicalSpace.Opens.ext hset
  have hleft :
      HEq
        (restrictSmoothFormsOfLE (I := I) (A := A)
            (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta)
        (restrictSmoothFormsOfLE (I := I) (A := A)
            (W := (V ⊓ U : TopologicalSpace.Opens M)) (V := V) inf_le_left n beta) := by
    let lhs :=
      restrictSmoothFormsOfLE (I := I) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta
    have hcast :
        hW ▸ lhs =
          restrictSmoothFormsOfLE (I := I) (A := A)
            (W := (V ⊓ U : TopologicalSpace.Opens M)) (V := V) inf_le_left n beta := by
      simpa [hW, lhs] using
        restrictSmoothFormsOfLE_cast_of_opens_ext
          (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M))
          (W' := (V ⊓ U : TopologicalSpace.Opens M)) (V := V)
          hset inf_le_right inf_le_left beta
    exact
      (eqRec_heq (φ := fun W : TopologicalSpace.Opens M =>
          SmoothForms (I := I) (M := W) A n) hW lhs).symm.trans
        (heq_of_eq hcast)
  have hright :
      HEq
        (smoothFormsPointwiseSMul (I := I)
          (M := (V ⊓ U : TopologicalSpace.Opens M)) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := M)
            (V ⊓ U : TopologicalSpace.Opens M) χ)
          ((inf_comm U V) ▸ omega))
        (smoothFormsPointwiseSMul (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := M)
            (U ⊓ V : TopologicalSpace.Opens M) χ)
          omega) := by
    let lhs :=
      smoothFormsPointwiseSMul (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A)
        (smoothFunctionRestrictToOpen (I := I) (M := M)
          (U ⊓ V : TopologicalSpace.Opens M) χ)
        omega
    let rhs_hW :=
      smoothFormsPointwiseSMul (I := I)
        (M := (V ⊓ U : TopologicalSpace.Opens M)) (A := A)
        (smoothFunctionRestrictToOpen (I := I) (M := M)
          (V ⊓ U : TopologicalSpace.Opens M) χ)
        (hW ▸ omega)
    have hcast : hW ▸ lhs = rhs_hW := by
      simpa [hW, lhs, rhs_hW] using
        smoothFormsPointwiseSMul_cast_of_opens_ext
          (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M))
          (W' := (V ⊓ U : TopologicalSpace.Opens M))
          hset χ omega
    have hrhs :
        rhs_hW =
          smoothFormsPointwiseSMul (I := I)
            (M := (V ⊓ U : TopologicalSpace.Opens M)) (A := A)
            (smoothFunctionRestrictToOpen (I := I) (M := M)
              (V ⊓ U : TopologicalSpace.Opens M) χ)
            ((inf_comm U V) ▸ omega) := by
      simp [rhs_hW]
    exact
      (heq_of_eq hrhs.symm).trans <|
      (heq_of_eq hcast.symm).trans
        (eqRec_heq (φ := fun W : TopologicalSpace.Opens M =>
          SmoothForms (I := I) (M := W) A n) hW lhs)
  exact eq_of_heq (hleft.trans ((heq_of_eq hbeta).trans hright))

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Extending a cutoff multiple from the right open set
statement:
  If the support of \(\chi\) is contained in \(U\), then the product
  \(\chi\omega\) on \(U\cap V\) is the restriction of a smooth form on \(V\).
proof:
  Apply the left-extension result with \(U\) and \(V\) interchanged, then
  transport the result back across the symmetry of the intersection.
-/
theorem smoothFormsPointwiseSMul_extendByZero_right
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) {n : ℕ}
    (χ : C^∞⟮I, M; 𝕜⟯)
    (hχ : tsupport χ ⊆ (U : Set M))
    (omega :
      SmoothForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n) :
    ∃ beta : SmoothForms (I := I) (M := V) A n,
      restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta =
        smoothFormsPointwiseSMul (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A)
          (smoothFunctionRestrictToOpen (I := I) (M := M)
            (U ⊓ V : TopologicalSpace.Opens M) χ)
          omega := by
  have hW :
      (U ⊓ V : TopologicalSpace.Opens M) =
        (V ⊓ U : TopologicalSpace.Opens M) :=
    inf_comm U V
  let omega' :
      SmoothForms (I := I) (M := (V ⊓ U : TopologicalSpace.Opens M)) A n :=
    hW ▸ omega
  rcases smoothFormsPointwiseSMul_extendByZero_left
      (I := I) (A := A) V U χ hχ omega' with
    ⟨beta, hbeta⟩
  refine ⟨beta, ?_⟩
  exact
    smoothFormsPointwiseSMul_extendByZero_inf_comm_transport
      (I := I) (A := A) U V χ omega beta
      (by simpa [hW] using hbeta)

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Surjectivity of the smooth overlap-difference map from a partition of unity
statement:
  In the standard finite-dimensional real smooth setting with partitions of
  unity, every smooth form on \(U\cap V\) is the overlap difference of a pair of
  smooth forms on \(U\) and \(V\).
proof:
  Choose a two-term smooth partition of unity subordinate to \(U\) and \(V\).
  Extend the two cutoff multiples of the overlap form to \(U\) and \(V\), take
  the pair \((\alpha,-\beta)\), and use that the two partition functions sum to
  one.
-/
theorem deRham_mayerVietoris_smooth_difference_surjective_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (omega :
      SmoothForms (I := Iℝ) (M := (U ⊓ V : TopologicalSpace.Opens M)) A n) :
    ∃ lift :
      SmoothForms (I := Iℝ) (M := U) A n ×
        SmoothForms (I := Iℝ) (M := V) A n,
      deRhamMayerVietorisSmoothDifference (I := Iℝ) (A := A) U V n lift = omega := by
  classical
  rcases
    SmoothPartitionOfUnity.exists_isSubordinate
      (I := Iℝ) (M := M) (ι := Bool) (s := univ)
      isClosed_univ
      (fun b : Bool => if b then (V : Set M) else (U : Set M))
      (by
        intro b
        cases b
        · exact U.2
        · exact V.2)
      (by
        intro x _hx
        have hx : x ∈ (U ⊔ V : TopologicalSpace.Opens M) := by
          rw [hcover]
          trivial
        rcases (show x ∈ U ∨ x ∈ V by simpa using hx) with hxU | hxV
        · exact mem_iUnion_of_mem false hxU
        · exact mem_iUnion_of_mem true hxV) with
    ⟨ρ, hρ⟩
  have htrue :
      tsupport (ρ true) ⊆ (V : Set M) :=
    by simpa using hρ true
  have hfalse :
      tsupport (ρ false) ⊆ (U : Set M) :=
    by simpa using hρ false
  rcases smoothFormsPointwiseSMul_extendByZero_left
      (I := Iℝ) (A := A) U V (ρ true) htrue omega with
    ⟨alpha, halpha⟩
  rcases smoothFormsPointwiseSMul_extendByZero_right
      (I := Iℝ) (A := A) U V (ρ false) hfalse omega with
    ⟨beta, hbeta⟩
  refine ⟨(alpha, -beta), ?_⟩
  rw [deRhamMayerVietorisSmoothDifference]
  rw [halpha]
  rw [map_neg, hbeta]
  apply DifferentialForm.ext
  intro x
  ext v
  have hsum_false_true :
      ρ false (x : M) + ρ true (x : M) = 1 := by
    have hsum := ρ.sum_eq_one (show (x : M) ∈ (univ : Set M) by simp)
    simpa [finsum_eq_sum_of_fintype, add_comm] using hsum
  have hsum_true_false :
      ρ true (x : M) + ρ false (x : M) = 1 := by
    simpa [add_comm] using hsum_false_true
  simp only [smoothFormsPointwiseSMul, smoothFunctionRestrictToOpen, sub_eq_add_neg, neg_neg]
  change
    ((ρ true (x : M)) • omega.toFun x + (ρ false (x : M)) • omega.toFun x) v =
      omega.toFun x v
  rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, ← add_smul, hsum_true_false, one_smul]

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Smooth forms are separated by a two-open cover
statement:
  If a smooth form restricts to zero on both members of a two-open cover, then
  the form is zero.
proof:
  Check pointwise.  Every point lies in \(U\) or \(V\), and on either open the
  corresponding zero restriction forces the value of the form to be zero.
-/
theorem smoothForms_eq_zero_of_restrictions_eq_zero
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (omega : SmoothForms (I := I) (M := M) A n)
    (hU :
      restrictSmoothFormsToOpen (I := I) (A := A) U n omega = 0)
    (hV :
      restrictSmoothFormsToOpen (I := I) (A := A) V n omega = 0) :
    omega = 0 := by
  apply DifferentialForm.ext
  intro x
  have hxUV : x ∈ U ∨ x ∈ V := by
    have hx : x ∈ (U ⊔ V : TopologicalSpace.Opens M) := by
      rw [hcover]
      trivial
    simpa using hx
  rcases hxUV with hxU | hxV
  · exact smoothForms_eq_zero_of_restrictSmoothFormsToOpen_zero_eq_at
      (I := I) (A := A) U omega hU hxU
  · exact smoothForms_eq_zero_of_restrictSmoothFormsToOpen_zero_eq_at
      (I := I) (A := A) V omega hV hxV

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Gluing smooth forms with zero overlap difference
statement:
  If smooth forms on \(U\) and \(V\) have zero difference on \(U\cap V\), then
  they are the two restrictions of a smooth form on \(M\).
proof:
  Use the previously constructed two-open glued form and verify that its
  restrictions are the original local forms.
-/
theorem deRham_mayerVietoris_smooth_glue_of_zero_difference
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0) :
    ∃ eta : SmoothForms (I := I) (M := M) A n,
      deRhamMayerVietorisSmoothRestriction (I := I) (A := A) U V n eta =
        (alpha, beta) := by
  refine ⟨smoothFormsTwoOpenGlue (I := I) (A := A) U V hcover alpha beta hoverlap, ?_⟩
  rw [deRhamMayerVietorisSmoothRestriction]
  exact Prod.ext
    (restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left
      (I := I) (A := A) U V hcover alpha beta hoverlap)
    (restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right
      (I := I) (A := A) U V hcover alpha beta hoverlap)

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  Exactness of the two-open sequence of smooth forms
statement:
  For an open cover \(M=U\cup V\), a pair of smooth forms on \(U\) and \(V\)
  has zero overlap difference exactly when it is the pair of restrictions of a
  smooth form on \(M\).
proof:
  One direction is that restricting a global form twice gives the same form on
  the overlap.  The other direction is smooth gluing for pairs whose overlap
  difference is zero.
-/
theorem deRham_mayerVietoris_smooth_exact_restriction_difference
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    Function.Exact
      (deRhamMayerVietorisSmoothRestriction (I := I) (A := A) U V n)
      (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n) := by
  refine Function.Exact.of_comp_of_mem_range ?_ ?_
  · funext omega
    exact deRham_mayerVietoris_smooth_difference_restriction_eq_zero
      (I := I) (A := A) U V n omega
  · intro omega hzero
    rcases omega with ⟨alpha, beta⟩
    rcases deRham_mayerVietoris_smooth_glue_of_zero_difference
        (I := I) (A := A) U V hcover n alpha beta hzero with
      ⟨eta, heta⟩
    exact ⟨eta, heta⟩

omit [IsRCLikeNormedField 𝕜] in
/--
%%handwave
name:
  The smooth restriction map is injective for a two-open cover
statement:
  A smooth form on \(M\) is determined by its restrictions to \(U\) and \(V\)
  when \(U\cup V=M\).
proof:
  If two forms have the same two restrictions, their difference restricts to
  zero on both opens; separatedness then makes the difference zero.
-/
theorem deRham_mayerVietoris_smooth_restriction_injective
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    Function.Injective
      (deRhamMayerVietorisSmoothRestriction (I := I) (A := A) U V n) := by
  intro omega eta homega_eta
  have hU :
      restrictSmoothFormsToOpen (I := I) (A := A) U n omega =
        restrictSmoothFormsToOpen (I := I) (A := A) U n eta := by
    simpa [deRhamMayerVietorisSmoothRestriction] using congrArg Prod.fst homega_eta
  have hV :
      restrictSmoothFormsToOpen (I := I) (A := A) V n omega =
        restrictSmoothFormsToOpen (I := I) (A := A) V n eta := by
    simpa [deRhamMayerVietorisSmoothRestriction] using congrArg Prod.snd homega_eta
  have hUzero :
      restrictSmoothFormsToOpen (I := I) (A := A) U n (omega - eta) = 0 := by
    rw [map_sub, hU, sub_self]
  have hVzero :
      restrictSmoothFormsToOpen (I := I) (A := A) V n (omega - eta) = 0 := by
    rw [map_sub, hV, sub_self]
  have hzero : omega - eta = 0 :=
    smoothForms_eq_zero_of_restrictions_eq_zero
      (I := I) (A := A) U V hcover n (omega - eta) hUzero hVzero
  exact sub_eq_zero.mp hzero

/--
The short exact sequence of smooth forms attached to a two-open cover.
-/
structure DeRhamMayerVietorisSmoothShortExact
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) where
  injective_restriction :
    Function.Injective
      (deRhamMayerVietorisSmoothRestriction (I := I) (A := A) U V n)
  exact_restriction_difference :
    Function.Exact
      (deRhamMayerVietorisSmoothRestriction (I := I) (A := A) U V n)
      (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n)
  surjective_difference :
    Function.Surjective
      (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n)

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  The short exact sequence of smooth forms from a partition of unity
statement:
  In the standard finite-dimensional real smooth setting, the two-open sequence
  of smooth forms has injective restriction, exact middle term, and surjective
  overlap-difference map.
proof:
  Package the injectivity, exactness, and partition-of-unity surjectivity
  theorems into the short-exact-sequence record.
-/
theorem deRham_mayerVietoris_smooth_shortExact_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    Nonempty (DeRhamMayerVietorisSmoothShortExact (I := Iℝ) (A := A) U V hcover n) := by
  exact ⟨
    { injective_restriction :=
        deRham_mayerVietoris_smooth_restriction_injective
          (I := Iℝ) (A := A) U V hcover n
      exact_restriction_difference :=
        deRham_mayerVietoris_smooth_exact_restriction_difference
          (I := Iℝ) (A := A) U V hcover n
      surjective_difference := by
        intro omega
        exact deRham_mayerVietoris_smooth_difference_surjective_of_partitionOfUnity
          (A := A) Iℝ U V hcover n omega }⟩

/--
%%handwave
name:
  Gluing closed forms with zero smooth overlap difference
statement:
  If closed smooth forms on \(U\) and \(V\) have zero smooth overlap difference,
  then they glue to a closed smooth form on \(M\) whose restrictions are the
  given local forms.
proof:
  First glue the underlying smooth forms.  The exterior derivative of the glued
  form restricts to zero on both opens, so separatedness forces it to be zero.
-/
theorem deRham_mayerVietoris_closed_glue_of_smooth_zero_difference
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (alpha : SmoothForms (I := I) (M := U) A n)
    (beta : SmoothForms (I := I) (M := V) A n)
    (hclosed_alpha :
      deRhamDifferential (I := I) (M := U) (A := A) n alpha = 0)
    (hclosed_beta :
      deRhamDifferential (I := I) (M := V) (A := A) n beta = 0)
    (hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n (alpha, beta) = 0) :
    ∃ eta : DeRhamClosedForms (I := I) (M := M) (A := A) n,
      deRhamMayerVietorisSmoothRestriction (I := I) (A := A) U V n eta.1 =
        (alpha, beta) := by
  rcases deRham_mayerVietoris_smooth_glue_of_zero_difference
      (I := I) (A := A) U V hcover n alpha beta hoverlap with
    ⟨eta, heta⟩
  have hU :
      restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1)
          (deRhamDifferential (I := I) (M := M) (A := A) n eta) = 0 := by
    have hUeta :
        restrictSmoothFormsToOpen (I := I) (A := A) U n eta = alpha := by
      simpa [deRhamMayerVietorisSmoothRestriction] using congrArg Prod.fst heta
    rw [← deRhamDifferential_restrictSmoothFormsToOpen (I := I) (A := A) U eta,
      hUeta, hclosed_alpha]
  have hV :
      restrictSmoothFormsToOpen (I := I) (A := A) V (n + 1)
          (deRhamDifferential (I := I) (M := M) (A := A) n eta) = 0 := by
    have hVeta :
        restrictSmoothFormsToOpen (I := I) (A := A) V n eta = beta := by
      simpa [deRhamMayerVietorisSmoothRestriction] using congrArg Prod.snd heta
    rw [← deRhamDifferential_restrictSmoothFormsToOpen (I := I) (A := A) V eta,
      hVeta, hclosed_beta]
  refine ⟨⟨eta, ?_⟩, heta⟩
  exact smoothForms_eq_zero_of_restrictions_eq_zero
    (I := I) (A := A) U V hcover (n + 1)
    (deRhamDifferential (I := I) (M := M) (A := A) n eta) hU hV

/--
Exact correction data for representatives whose overlap difference is exact.

Mathematically, if
\(\alpha|_{U\cap V}-\beta|_{U\cap V}=d\theta\), a partition of unity writes
the exact overlap term as the difference of restrictions of exact corrections
on \(U\) and \(V\).  Subtracting those corrections makes the representatives
agree exactly on \(U\cap V\).
-/
structure DeRhamMayerVietorisExactOverlapCorrectionData
    (U V : TopologicalSpace.Opens M) (n : ℕ)
    (alpha : DeRhamClosedForms (I := I) (M := U) (A := A) n)
    (beta : DeRhamClosedForms (I := I) (M := V) (A := A) n) where
  left_correction :
    DeRhamClosedForms (I := I) (M := U) (A := A) n
  right_correction :
    DeRhamClosedForms (I := I) (M := V) (A := A) n
  left_correction_exact :
    left_correction ∈ DeRhamExactClosedForms (I := I) (M := U) (A := A) n
  right_correction_exact :
    right_correction ∈ DeRhamExactClosedForms (I := I) (M := V) (A := A) n
  corrected_overlap_eq :
    deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
        (alpha - left_correction) =
      deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
        (beta - right_correction)

/--
%%handwave
name:
  Exact overlap correction data from smooth surjectivity
statement:
  If the smooth overlap-difference map is surjective in all degrees and the
  overlap difference of two closed representatives is exact, then there are
  exact closed corrections on \(U\) and \(V\) after which the corrected
  representatives agree on \(U\cap V\).
proof:
  In degree zero, exactness means the overlap difference is zero.  In positive
  degree, write the exact overlap difference as \(d\theta\), lift \(\theta\) by
  smooth surjectivity, and take the differentials of the two lifted pieces as
  the exact corrections.
-/
theorem deRham_mayerVietoris_exact_overlap_correctionData_exists_of_smooth_difference_surjective
    (U V : TopologicalSpace.Opens M) (n : ℕ)
    (hsurj :
      ∀ m : ℕ,
        Function.Surjective
          (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V m))
    (alpha : DeRhamClosedForms (I := I) (M := U) (A := A) n)
    (beta : DeRhamClosedForms (I := I) (M := V) (A := A) n)
    (hexact :
      deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha -
        deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta ∈
          DeRhamExactClosedForms (I := I)
            (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) :
    Nonempty
      (DeRhamMayerVietorisExactOverlapCorrectionData
        (I := I) (A := A) U V n alpha beta) := by
  cases n with
  | zero =>
      have hdiff_zero :
          deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left 0 alpha -
            deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right 0 beta = 0 := by
        exact (Submodule.mem_bot 𝕜).mp
          (show
            deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
                (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left 0 alpha -
              deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
                (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right 0 beta ∈
                (⊥ :
                  Submodule 𝕜
                    (DeRhamClosedForms (I := I)
                      (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) 0)) by
            simpa [DeRhamExactClosedForms, DeRhamExactForms] using hexact)
      refine ⟨
        { left_correction := 0
          right_correction := 0
          left_correction_exact := ?_
          right_correction_exact := ?_
          corrected_overlap_eq := ?_ }⟩
      · simp [DeRhamExactClosedForms, DeRhamExactForms]
      · simp [DeRhamExactClosedForms, DeRhamExactForms]
      · rw [sub_zero, sub_zero]
        exact sub_eq_zero.mp hdiff_zero
  | succ m =>
      have hexact_smooth :
          (deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left
              (m + 1) alpha -
            deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right
              (m + 1) beta).1 ∈
            DeRhamExactForms (I := I)
              (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) (m + 1) := by
        simpa [DeRhamExactClosedForms] using hexact
      rw [DeRhamExactForms] at hexact_smooth
      rcases hexact_smooth with ⟨theta, htheta⟩
      rcases hsurj m theta with
        ⟨lift, hlift⟩
      let leftCorrection : DeRhamClosedForms (I := I) (M := U) (A := A) (m + 1) :=
        ⟨deRhamDifferential (I := I) (M := U) (A := A) m lift.1,
          deRhamDifferential_comp_eq_zero (I := I) (M := U) (A := A) lift.1⟩
      let rightCorrection : DeRhamClosedForms (I := I) (M := V) (A := A) (m + 1) :=
        ⟨deRhamDifferential (I := I) (M := V) (A := A) m lift.2,
          deRhamDifferential_comp_eq_zero (I := I) (M := V) (A := A) lift.2⟩
      have hcorrections_difference :
          deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left
              (m + 1) leftCorrection -
            deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right
              (m + 1) rightCorrection =
          deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left
              (m + 1) alpha -
            deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right
              (m + 1) beta := by
        apply Subtype.ext
        have hleft :
            deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (m + 1)
                (leftCorrection.1, rightCorrection.1) =
              deRhamDifferential (I := I)
                (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) m theta := by
          change
            deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (m + 1)
                (deRhamDifferential (I := I) (M := U) (A := A) m lift.1,
                  deRhamDifferential (I := I) (M := V) (A := A) m lift.2) =
              deRhamDifferential (I := I)
                (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) m theta
          rw [deRhamDifferential_mayerVietorisSmoothDifference, hlift]
        have hright :
            deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (m + 1)
                (alpha.1, beta.1) =
              deRhamDifferential (I := I)
                (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) m theta := by
          simpa [deRhamMayerVietorisSmoothDifference] using htheta.symm
        exact hleft.trans hright.symm
      refine ⟨
        { left_correction := leftCorrection
          right_correction := rightCorrection
          left_correction_exact := ?_
          right_correction_exact := ?_
          corrected_overlap_eq := ?_ }⟩
      · change deRhamDifferential (I := I) (M := U) (A := A) m lift.1 ∈
          DeRhamExactForms (I := I) (M := U) (A := A) (m + 1)
        rw [DeRhamExactForms]
        exact ⟨lift.1, rfl⟩
      · change deRhamDifferential (I := I) (M := V) (A := A) m lift.2 ∈
          DeRhamExactForms (I := I) (M := V) (A := A) (m + 1)
        rw [DeRhamExactForms]
        exact ⟨lift.2, rfl⟩
      · rw [map_sub, map_sub]
        rw [sub_eq_sub_iff_add_eq_add] at hcorrections_difference ⊢
        rw [← hcorrections_difference]
        exact add_comm _ _

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Exact overlap correction data from a partition of unity
statement:
  In the standard finite-dimensional real smooth setting, exact overlap
  correction data exists whenever the overlap difference of two closed
  representatives is exact.
proof:
  Apply the smooth-surjectivity construction, using the partition-of-unity
  theorem to supply surjectivity of the smooth overlap-difference map in every
  degree.
-/
theorem deRham_mayerVietoris_exact_overlap_correctionData_exists_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (alpha : DeRhamClosedForms (I := Iℝ) (M := U) (A := A) n)
    (beta : DeRhamClosedForms (I := Iℝ) (M := V) (A := A) n)
    (hexact :
      deRhamClosedFormsRestrictionOfLE (I := Iℝ) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha -
        deRhamClosedFormsRestrictionOfLE (I := Iℝ) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta ∈
          DeRhamExactClosedForms (I := Iℝ)
            (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) :
    Nonempty
      (DeRhamMayerVietorisExactOverlapCorrectionData
        (I := Iℝ) (A := A) U V n alpha beta) := by
  exact
    deRham_mayerVietoris_exact_overlap_correctionData_exists_of_smooth_difference_surjective
      (I := Iℝ) (A := A) U V n
      (fun m =>
        fun omega =>
          deRham_mayerVietoris_smooth_difference_surjective_of_partitionOfUnity
            (A := A) Iℝ U V hcover m omega)
      alpha beta hexact

/--
The representative correction supplied by a partition of unity.

Starting from closed representatives on the two opens whose overlap
difference is exact, one can replace both representatives by cohomologous
closed forms whose restrictions agree exactly on the overlap.
-/
structure DeRhamMayerVietorisClosedPairCorrection
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (alpha : DeRhamClosedForms (I := I) (M := U) (A := A) n)
    (beta : DeRhamClosedForms (I := I) (M := V) (A := A) n) where
  left_representative :
    DeRhamClosedForms (I := I) (M := U) (A := A) n
  right_representative :
    DeRhamClosedForms (I := I) (M := V) (A := A) n
  left_cohomologous :
    (DeRhamExactClosedForms (I := I) (M := U) (A := A) n).mkQ
        left_representative =
      (DeRhamExactClosedForms (I := I) (M := U) (A := A) n).mkQ alpha
  right_cohomologous :
    (DeRhamExactClosedForms (I := I) (M := V) (A := A) n).mkQ
        right_representative =
      (DeRhamExactClosedForms (I := I) (M := V) (A := A) n).mkQ beta
  overlap_eq :
    deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
        left_representative =
      deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
        right_representative

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Correcting closed representatives with exact overlap difference
statement:
  In the standard finite-dimensional real smooth setting, closed representatives
  on \(U\) and \(V\) whose overlap difference is exact can be replaced by
  cohomologous closed representatives whose restrictions agree exactly on the
  overlap.
proof:
  Use exact overlap correction data, subtract the exact corrections from the two
  representatives, and observe that subtracting an exact closed form does not
  change a cohomology class.
-/
theorem deRham_mayerVietoris_closed_pair_correction_of_exact_overlap_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (alpha : DeRhamClosedForms (I := Iℝ) (M := U) (A := A) n)
    (beta : DeRhamClosedForms (I := Iℝ) (M := V) (A := A) n)
    (hexact :
      deRhamClosedFormsRestrictionOfLE (I := Iℝ) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha -
        deRhamClosedFormsRestrictionOfLE (I := Iℝ) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta ∈
          DeRhamExactClosedForms (I := Iℝ)
            (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) :
    Nonempty
      (DeRhamMayerVietorisClosedPairCorrection
        (I := Iℝ) (A := A) U V hcover n alpha beta) := by
  rcases deRham_mayerVietoris_exact_overlap_correctionData_exists_of_partitionOfUnity
      (A := A) Iℝ U V hcover n alpha beta hexact with
    ⟨data⟩
  refine ⟨
    { left_representative := alpha - data.left_correction
      right_representative := beta - data.right_correction
      left_cohomologous := ?_
      right_cohomologous := ?_
      overlap_eq := data.corrected_overlap_eq }⟩
  · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    change (alpha - data.left_correction) - alpha ∈
      DeRhamExactClosedForms (I := Iℝ) (M := U) (A := A) n
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (DeRhamExactClosedForms (I := Iℝ) (M := U) (A := A) n).neg_mem
        data.left_correction_exact
  · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    change (beta - data.right_correction) - beta ∈
      DeRhamExactClosedForms (I := Iℝ) (M := V) (A := A) n
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (DeRhamExactClosedForms (I := Iℝ) (M := V) (A := A) n).neg_mem
        data.right_correction_exact

/--
%%handwave
name:
  Gluing closed representatives that agree on the overlap
statement:
  If closed representatives on \(U\) and \(V\) restrict to the same closed form
  on \(U\cap V\), then they are the restrictions of a closed form on \(M\).
proof:
  Convert equality of closed-form restrictions into zero smooth overlap
  difference, glue the underlying smooth forms, and keep the closedness supplied
  by the gluing theorem.
-/
theorem deRham_mayerVietoris_closed_pair_glue_of_equal_overlap
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (alpha : DeRhamClosedForms (I := I) (M := U) (A := A) n)
    (beta : DeRhamClosedForms (I := I) (M := V) (A := A) n)
    (hoverlap :
      deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha =
        deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta) :
    ∃ eta : DeRhamClosedForms (I := I) (M := M) (A := A) n,
      deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U n eta =
        alpha ∧
      deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V n eta =
        beta := by
  have hoverlap_smooth :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n
          (alpha.1, beta.1) = 0 := by
    rw [deRhamMayerVietorisSmoothDifference]
    exact sub_eq_zero.mpr (congrArg Subtype.val hoverlap)
  rcases deRham_mayerVietoris_closed_glue_of_smooth_zero_difference
      (I := I) (A := A) U V hcover n alpha.1 beta.1 alpha.2 beta.2 hoverlap_smooth with
    ⟨eta, heta⟩
  refine ⟨eta, ?_, ?_⟩
  · apply Subtype.ext
    exact congrArg Prod.fst heta
  · apply Subtype.ext
    exact congrArg Prod.snd heta

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Gluing closed representatives with exact overlap difference
statement:
  In the standard finite-dimensional real smooth setting, if the overlap
  difference of closed representatives on \(U\) and \(V\) is exact, then a global
  closed representative exists whose restrictions represent the original two
  cohomology classes.
proof:
  First correct the two representatives to cohomologous representatives agreeing
  exactly on the overlap, then glue those corrected representatives.
-/
theorem deRham_mayerVietoris_closed_pair_glue_of_exact_overlap_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (alpha : DeRhamClosedForms (I := Iℝ) (M := U) (A := A) n)
    (beta : DeRhamClosedForms (I := Iℝ) (M := V) (A := A) n)
    (hexact :
      deRhamClosedFormsRestrictionOfLE (I := Iℝ) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha -
        deRhamClosedFormsRestrictionOfLE (I := Iℝ) (M := M) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta ∈
          DeRhamExactClosedForms (I := Iℝ)
            (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) :
    ∃ eta : DeRhamClosedForms (I := Iℝ) (M := M) (A := A) n,
      (DeRhamExactClosedForms (I := Iℝ) (M := U) (A := A) n).mkQ
          (deRhamClosedFormsRestrictionToOpen (I := Iℝ) (M := M) (A := A) U n eta) =
        (DeRhamExactClosedForms (I := Iℝ) (M := U) (A := A) n).mkQ alpha ∧
      (DeRhamExactClosedForms (I := Iℝ) (M := V) (A := A) n).mkQ
          (deRhamClosedFormsRestrictionToOpen (I := Iℝ) (M := M) (A := A) V n eta) =
        (DeRhamExactClosedForms (I := Iℝ) (M := V) (A := A) n).mkQ beta := by
  rcases deRham_mayerVietoris_closed_pair_correction_of_exact_overlap_of_partitionOfUnity
      (A := A) Iℝ U V hcover n alpha beta hexact with
    ⟨correction⟩
  rcases deRham_mayerVietoris_closed_pair_glue_of_equal_overlap
      (I := Iℝ) (A := A) U V hcover n
      correction.left_representative correction.right_representative
      correction.overlap_eq with
    ⟨eta, hU, hV⟩
  refine ⟨eta, ?_, ?_⟩
  · rw [hU]
    exact correction.left_cohomologous
  · rw [hV]
    exact correction.right_cohomologous

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Gluing cohomology classes with zero Mayer-Vietoris difference
statement:
  In the standard finite-dimensional real smooth setting, every pair of
  cohomology classes on \(U\) and \(V\) with zero overlap difference is the
  restriction of a global cohomology class.
proof:
  Choose closed representatives, interpret the zero quotient-level difference
  as exactness of their representative overlap difference, glue corrected
  representatives, and pass the result back to cohomology.
-/
theorem deRham_mayerVietoris_glue_of_zero_difference_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (omega :
      DeRhamCohomology (I := Iℝ) (M := U) (A := A) n ×
        DeRhamCohomology (I := Iℝ) (M := V) (A := A) n)
    (hzero :
      deRhamMayerVietorisDifference (I := Iℝ) (A := A) U V n omega = 0) :
    ∃ eta : DeRhamCohomology (I := Iℝ) (M := M) (A := A) n,
      deRhamMayerVietorisRestriction (I := Iℝ) (A := A) U V n eta = omega := by
  rcases omega with ⟨omegaU, omegaV⟩
  induction omegaU using Submodule.Quotient.induction_on with
  | _ alpha =>
      induction omegaV using Submodule.Quotient.induction_on with
      | _ beta =>
          simp only [deRhamMayerVietorisDifference, deRhamCohomologyRestrictionOfLE,
            Submodule.mapQ_apply] at hzero
          have hexact :
              deRhamClosedFormsRestrictionOfLE (I := Iℝ) (M := M) (A := A)
                  (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha -
                deRhamClosedFormsRestrictionOfLE (I := Iℝ) (M := M) (A := A)
                  (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta ∈
                  DeRhamExactClosedForms (I := Iℝ)
                    (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n := by
            rw [← Submodule.Quotient.mk_eq_zero]
            simpa using hzero
          rcases deRham_mayerVietoris_closed_pair_glue_of_exact_overlap_of_partitionOfUnity
              (A := A) Iℝ U V hcover n alpha beta hexact with
            ⟨eta, hU, hV⟩
          refine ⟨(DeRhamExactClosedForms (I := Iℝ) (M := M) (A := A) n).mkQ eta, ?_⟩
          simp only [deRhamMayerVietorisRestriction, deRhamCohomologyRestrictionToOpen]
          exact Prod.ext hU hV

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Exactness at the pair term of Mayer-Vietoris
statement:
  In the standard finite-dimensional real smooth setting, the image of
  \(H^n(M)\to H^n(U)\oplus H^n(V)\) is the kernel of the overlap-difference map
  to \(H^n(U\cap V)\).
proof:
  One inclusion is that a global class has equal restrictions on the overlap.
  For the reverse inclusion, use quotient-level gluing for pairs with zero
  overlap difference.
-/
theorem deRham_mayerVietoris_exact_restriction_difference_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    Function.Exact
      (deRhamMayerVietorisRestriction (I := Iℝ) (A := A) U V n)
      (deRhamMayerVietorisDifference (I := Iℝ) (A := A) U V n) := by
  refine Function.Exact.of_comp_of_mem_range ?_ ?_
  · funext omega
    exact deRham_mayerVietoris_difference_restriction_eq_zero
      (I := Iℝ) (A := A) U V n omega
  · intro omega hzero
    exact deRham_mayerVietoris_glue_of_zero_difference_of_partitionOfUnity
      (A := A) Iℝ U V hcover n omega hzero

/--
Data used to compute the connecting map from a closed form on the overlap.

Mathematically, for a closed \(n\)-form \(\gamma\) on \(U\cap V\), choose
\((\alpha,\beta)\in \Omega^n(U)\oplus\Omega^n(V)\) with
\(\alpha|_{U\cap V}-\beta|_{U\cap V}=\gamma\).  Since \(d\gamma=0\), the pair
\((d\alpha,d\beta)\) agrees on the overlap, and therefore glues to a closed
\((n+1)\)-form on \(M\).
-/
structure DeRhamMayerVietorisConnectingData
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (omega :
      DeRhamClosedForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) where
  lift :
    SmoothForms (I := I) (M := U) A n ×
      SmoothForms (I := I) (M := V) A n
  lift_difference :
    deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n lift = omega.1
  glued :
    DeRhamClosedForms (I := I) (M := M) (A := A) (n + 1)
  glued_restriction :
    deRhamMayerVietorisSmoothRestriction (I := I) (A := A) U V (n + 1) glued.1 =
      (deRhamDifferential (I := I) (M := U) (A := A) n lift.1,
        deRhamDifferential (I := I) (M := V) (A := A) n lift.2)

/--
%%handwave
name:
  Connecting-map data from smooth surjectivity
statement:
  If the smooth overlap-difference map is surjective in all degrees, then every
  closed form on \(U\cap V\) admits data computing the Mayer-Vietoris connecting
  class.
proof:
  Lift the closed overlap form to a pair of smooth forms on \(U\) and \(V\).
  Applying \(d\) to the lift gives a pair with zero overlap difference, so the
  closed gluing theorem produces the global closed form used by the connecting
  construction.
-/
theorem deRham_mayerVietoris_connectingData_nonempty_of_smooth_difference_surjective
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (hsurj : ∀ m : ℕ, Function.Surjective
      (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V m))
    (omega :
      DeRhamClosedForms (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) :
    Nonempty (DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega) := by
  rcases hsurj n omega.1 with
    ⟨lift, hlift⟩
  have hoverlap :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (n + 1)
          (deRhamDifferential (I := I) (M := U) (A := A) n lift.1,
            deRhamDifferential (I := I) (M := V) (A := A) n lift.2) = 0 := by
    rw [deRhamDifferential_mayerVietorisSmoothDifference]
    rw [hlift]
    exact omega.2
  have hclosed_left :
      deRhamDifferential (I := I) (M := U) (A := A) (n + 1)
          (deRhamDifferential (I := I) (M := U) (A := A) n lift.1) = 0 :=
    deRhamDifferential_comp_eq_zero (I := I) (M := U) (A := A) lift.1
  have hclosed_right :
      deRhamDifferential (I := I) (M := V) (A := A) (n + 1)
          (deRhamDifferential (I := I) (M := V) (A := A) n lift.2) = 0 :=
    deRhamDifferential_comp_eq_zero (I := I) (M := V) (A := A) lift.2
  rcases deRham_mayerVietoris_closed_glue_of_smooth_zero_difference
      (I := I) (A := A) U V hcover (n + 1)
      (deRhamDifferential (I := I) (M := U) (A := A) n lift.1)
      (deRhamDifferential (I := I) (M := V) (A := A) n lift.2)
      hclosed_left hclosed_right hoverlap with
    ⟨glued, hglued⟩
  exact ⟨
    { lift := lift
      lift_difference := hlift
      glued := glued
      glued_restriction := hglued }⟩

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Connecting-map data from a partition of unity
statement:
  In the standard finite-dimensional real smooth setting, every closed form on
  \(U\cap V\) admits data computing the Mayer-Vietoris connecting class.
proof:
  Apply the smooth-surjectivity construction, using partitions of unity to
  provide the required surjectivity in every degree.
-/
theorem deRham_mayerVietoris_connectingData_nonempty_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (omega :
      DeRhamClosedForms (I := Iℝ)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) :
    Nonempty
      (DeRhamMayerVietorisConnectingData (I := Iℝ) (A := A) U V hcover n omega) := by
  exact deRham_mayerVietoris_connectingData_nonempty_of_smooth_difference_surjective
    (I := Iℝ) (A := A) U V hcover n
    (fun m =>
      deRham_mayerVietoris_smooth_difference_surjective_of_partitionOfUnity
        (A := A) Iℝ U V hcover m)
    omega

/--
Formula characterizing the Mayer-Vietoris connecting map.
-/
def DeRhamMayerVietorisConnectingFormula
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (connecting :
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
        DeRhamCohomology (I := I) (M := M) (A := A) (n + 1)) : Prop :=
    ∀ (omega :
        DeRhamClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n),
      ∀ data :
        DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega,
        connecting
            ((DeRhamExactClosedForms (I := I)
              (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n).mkQ omega) =
          (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ
            data.glued

/--
%%handwave
name:
  Connecting data gives the same global cohomology class
statement:
  Any two choices of connecting data for the same closed overlap form determine
  the same cohomology class on \(M\).
proof:
  The difference of the two chosen lifts has zero overlap difference, so it
  glues to a form whose exterior derivative is exactly the difference of the two
  glued closed forms; hence that difference is exact.
-/
theorem deRham_mayerVietoris_connectingData_same_glued
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (omega :
      DeRhamClosedForms (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n)
    (data data' :
      DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega) :
    (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ data.glued =
      (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ data'.glued := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  change (data.glued - data'.glued).1 ∈
    DeRhamExactForms (I := I) (M := M) (A := A) (n + 1)
  have hdiff_zero :
      deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n
          (data.lift.1 - data'.lift.1, data.lift.2 - data'.lift.2) = 0 := by
    change
      restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
          (data.lift.1 - data'.lift.1) -
        restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
          (data.lift.2 - data'.lift.2) = 0
    rw [map_sub, map_sub]
    have hdata := data.lift_difference
    have hdata' := data'.lift_difference
    change
      restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
          data.lift.1 -
        restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
          data.lift.2 = omega.1 at hdata
    change
      restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
          data'.lift.1 -
        restrictSmoothFormsOfLE (I := I) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
          data'.lift.2 = omega.1 at hdata'
    calc
      (restrictSmoothFormsOfLE (I := I) (A := A)
            (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
            data.lift.1 -
          restrictSmoothFormsOfLE (I := I) (A := A)
            (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
            data'.lift.1) -
        (restrictSmoothFormsOfLE (I := I) (A := A)
            (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
            data.lift.2 -
          restrictSmoothFormsOfLE (I := I) (A := A)
            (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
            data'.lift.2)
          = (restrictSmoothFormsOfLE (I := I) (A := A)
                (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
                data.lift.1 -
              restrictSmoothFormsOfLE (I := I) (A := A)
                (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
                data.lift.2) -
            (restrictSmoothFormsOfLE (I := I) (A := A)
                (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
                data'.lift.1 -
              restrictSmoothFormsOfLE (I := I) (A := A)
                (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
                data'.lift.2) := by
              abel
      _ = omega.1 - omega.1 := by rw [hdata, hdata']
      _ = 0 := sub_self _
  rcases deRham_mayerVietoris_smooth_glue_of_zero_difference
      (I := I) (A := A) U V hcover n
      (data.lift.1 - data'.lift.1) (data.lift.2 - data'.lift.2)
      (by simpa using hdiff_zero) with
    ⟨theta, htheta⟩
  rw [DeRhamExactForms]
  refine ⟨theta, ?_⟩
  symm
  apply sub_eq_zero.mp
  apply smoothForms_eq_zero_of_restrictions_eq_zero
    (I := I) (A := A) U V hcover (n + 1)
    (data.glued.1 - data'.glued.1 -
      deRhamDifferential (I := I) (M := M) (A := A) n theta)
  · have hUglued :
        restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1) data.glued.1 =
          deRhamDifferential (I := I) (M := U) (A := A) n data.lift.1 := by
      simpa [deRhamMayerVietorisSmoothRestriction] using
        congrArg Prod.fst data.glued_restriction
    have hUglued' :
        restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1) data'.glued.1 =
          deRhamDifferential (I := I) (M := U) (A := A) n data'.lift.1 := by
      simpa [deRhamMayerVietorisSmoothRestriction] using
        congrArg Prod.fst data'.glued_restriction
    have hUtheta :
        restrictSmoothFormsToOpen (I := I) (A := A) U n theta =
          data.lift.1 - data'.lift.1 := by
      simpa [deRhamMayerVietorisSmoothRestriction] using
        congrArg Prod.fst htheta
    change
      restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1)
          (data.glued.1 - data'.glued.1 -
            deRhamDifferential (I := I) (M := M) (A := A) n theta) = 0
    rw [map_sub, map_sub, hUglued, hUglued']
    rw [← deRhamDifferential_restrictSmoothFormsToOpen (I := I) (A := A) U theta]
    rw [hUtheta, map_sub]
    abel
  · have hVglued :
        restrictSmoothFormsToOpen (I := I) (A := A) V (n + 1) data.glued.1 =
          deRhamDifferential (I := I) (M := V) (A := A) n data.lift.2 := by
      simpa [deRhamMayerVietorisSmoothRestriction] using
        congrArg Prod.snd data.glued_restriction
    have hVglued' :
        restrictSmoothFormsToOpen (I := I) (A := A) V (n + 1) data'.glued.1 =
          deRhamDifferential (I := I) (M := V) (A := A) n data'.lift.2 := by
      simpa [deRhamMayerVietorisSmoothRestriction] using
        congrArg Prod.snd data'.glued_restriction
    have hVtheta :
        restrictSmoothFormsToOpen (I := I) (A := A) V n theta =
          data.lift.2 - data'.lift.2 := by
      simpa [deRhamMayerVietorisSmoothRestriction] using
        congrArg Prod.snd htheta
    change
      restrictSmoothFormsToOpen (I := I) (A := A) V (n + 1)
          (data.glued.1 - data'.glued.1 -
            deRhamDifferential (I := I) (M := M) (A := A) n theta) = 0
    rw [map_sub, map_sub, hVglued, hVglued']
    rw [← deRhamDifferential_restrictSmoothFormsToOpen (I := I) (A := A) V theta]
    rw [hVtheta, map_sub]
    abel

/--
%%handwave
name:
  Exactly equivalent overlap representatives give the same connecting class
statement:
  If two closed overlap representatives differ by an exact form, then the global
  classes produced from any corresponding connecting data are equal.
proof:
  In degree zero the exact difference is zero.  In positive degree, lift a
  primitive for the exact difference, adjust one set of connecting data by the
  differential of the lift, and then use invariance of the glued class for equal
  overlap data.
-/
theorem deRham_mayerVietoris_connectingData_exact_glued_of_smooth_difference_surjective
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (hsurj : ∀ m : ℕ, Function.Surjective
      (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V m))
    (omega omega' :
      DeRhamClosedForms (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n)
    (data :
      DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega)
    (data' :
      DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega')
    (hexact :
      omega - omega' ∈
        DeRhamExactClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) :
    (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ data.glued =
      (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ data'.glued := by
  cases n with
  | zero =>
      have hzero : omega - omega' = 0 := by
        exact (Submodule.mem_bot 𝕜).mp
          (show
            omega - omega' ∈
              (⊥ :
                Submodule 𝕜
                  (DeRhamClosedForms (I := I)
                    (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) 0)) by
              simpa [DeRhamExactClosedForms, DeRhamExactForms] using hexact)
      have homega : omega = omega' := sub_eq_zero.mp hzero
      subst omega
      exact deRham_mayerVietoris_connectingData_same_glued
        (I := I) (A := A) U V hcover 0 omega' data data'
  | succ m =>
      have hexact_smooth :
          (omega - omega').1 ∈
            DeRhamExactForms (I := I)
              (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) (m + 1) := by
        simpa [DeRhamExactClosedForms] using hexact
      rw [DeRhamExactForms] at hexact_smooth
      rcases hexact_smooth with ⟨theta, htheta⟩
      rcases hsurj m theta with
        ⟨thetaLift, hthetaLift⟩
      let adjusted :
          DeRhamMayerVietorisConnectingData
            (I := I) (A := A) U V hcover (m + 1) omega :=
        { lift :=
            (data'.lift.1 +
              deRhamDifferential (I := I) (M := U) (A := A) m thetaLift.1,
             data'.lift.2 +
              deRhamDifferential (I := I) (M := V) (A := A) m thetaLift.2)
          lift_difference := by
            have hdata' := data'.lift_difference
            change
              deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (m + 1)
                  data'.lift = omega'.1 at hdata'
            have hthetaLift' := hthetaLift
            change
              deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V m
                  thetaLift = theta at hthetaLift'
            calc
              deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (m + 1)
                (data'.lift.1 +
                  deRhamDifferential (I := I) (M := U) (A := A) m thetaLift.1,
                 data'.lift.2 +
                  deRhamDifferential (I := I) (M := V) (A := A) m thetaLift.2)
                  =
                    deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (m + 1)
                      data'.lift +
                    deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V (m + 1)
                      (deRhamDifferential (I := I) (M := U) (A := A) m thetaLift.1,
                       deRhamDifferential (I := I) (M := V) (A := A) m thetaLift.2) := by
                    simp only [deRhamMayerVietorisSmoothDifference]
                    rw [map_add, map_add]
                    abel
              _ = omega'.1 +
                    deRhamDifferential (I := I)
                      (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) m
                      theta := by
                    rw [hdata',
                      deRhamDifferential_mayerVietorisSmoothDifference
                        (I := I) (A := A) U V m thetaLift,
                      hthetaLift']
              _ = omega'.1 + (omega - omega').1 := by rw [htheta]
              _ = omega.1 := by
                    change omega'.1 + (omega.1 - omega'.1) = omega.1
                    abel
          glued := data'.glued
          glued_restriction := by
            apply Prod.ext
            · have hUglued' :
                  restrictSmoothFormsToOpen (I := I) (A := A) U (m + 2) data'.glued.1 =
                    deRhamDifferential (I := I) (M := U) (A := A) (m + 1)
                      data'.lift.1 := by
                simpa [deRhamMayerVietorisSmoothRestriction] using
                  congrArg Prod.fst data'.glued_restriction
              change
                restrictSmoothFormsToOpen (I := I) (A := A) U (m + 2) data'.glued.1 =
                  deRhamDifferential (I := I) (M := U) (A := A) (m + 1)
                    (data'.lift.1 +
                      deRhamDifferential (I := I) (M := U) (A := A) m thetaLift.1)
              rw [map_add, deRhamDifferential_comp_eq_zero, add_zero]
              exact hUglued'
            · have hVglued' :
                  restrictSmoothFormsToOpen (I := I) (A := A) V (m + 2) data'.glued.1 =
                    deRhamDifferential (I := I) (M := V) (A := A) (m + 1)
                      data'.lift.2 := by
                simpa [deRhamMayerVietorisSmoothRestriction] using
                  congrArg Prod.snd data'.glued_restriction
              change
                restrictSmoothFormsToOpen (I := I) (A := A) V (m + 2) data'.glued.1 =
                  deRhamDifferential (I := I) (M := V) (A := A) (m + 1)
                    (data'.lift.2 +
                      deRhamDifferential (I := I) (M := V) (A := A) m thetaLift.2)
              rw [map_add, deRhamDifferential_comp_eq_zero, add_zero]
              exact hVglued' }
      calc
        (DeRhamExactClosedForms (I := I) (M := M) (A := A) (m + 2)).mkQ data.glued =
            (DeRhamExactClosedForms (I := I) (M := M) (A := A) (m + 2)).mkQ
              adjusted.glued := by
              exact deRham_mayerVietoris_connectingData_same_glued
                (I := I) (A := A) U V hcover (m + 1) omega data adjusted
        _ =
            (DeRhamExactClosedForms (I := I) (M := M) (A := A) (m + 2)).mkQ
              data'.glued := rfl

/--
%%handwave
name:
  Existence of a connecting map from smooth surjectivity
statement:
  If the smooth overlap-difference map is surjective in all degrees, then there
  exists a connecting map \(H^n(U\cap V)\to H^{n+1}(M)\) characterized by the
  usual glued-differential formula.
proof:
  Define the connecting map by choosing connecting data for a closed
  representative and taking the class of its glued differential.  The preceding
  exact-representative invariance proves that this descends to the quotient, and
  the same-choice invariance proves the stated formula for arbitrary data.
-/
theorem deRham_mayerVietoris_connecting_formula_exists_from_data_of_smooth_difference_surjective
    [CharZero 𝕜]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    (∀ m : ℕ, Function.Surjective
      (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V m)) →
    ∃ connecting :
        DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
          DeRhamCohomology (I := I) (M := M) (A := A) (n + 1),
      DeRhamMayerVietorisConnectingFormula (I := I) (A := A) U V hcover n
        connecting := by
  intro hsurj
  classical
  let connecting :
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
        DeRhamCohomology (I := I) (M := M) (A := A) (n + 1) :=
    fun q ↦
      Quotient.liftOn q
        (fun omega :
            DeRhamClosedForms (I := I)
              (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n ↦
          (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ
            (Classical.choice
              (deRham_mayerVietoris_connectingData_nonempty_of_smooth_difference_surjective
                (I := I) (A := A) U V hcover n hsurj omega)).glued)
        (by
          intro omega omega' hrel
          let data :
              DeRhamMayerVietorisConnectingData
                (I := I) (A := A) U V hcover n omega :=
            Classical.choice
              (deRham_mayerVietoris_connectingData_nonempty_of_smooth_difference_surjective
                (I := I) (A := A) U V hcover n hsurj omega)
          let data' :
              DeRhamMayerVietorisConnectingData
                (I := I) (A := A) U V hcover n omega' :=
            Classical.choice
              (deRham_mayerVietoris_connectingData_nonempty_of_smooth_difference_surjective
                (I := I) (A := A) U V hcover n hsurj omega')
          change
            (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ data.glued =
              (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ
                data'.glued
          exact deRham_mayerVietoris_connectingData_exact_glued_of_smooth_difference_surjective
            (I := I) (A := A) U V hcover n hsurj omega omega' data data'
            ((Submodule.quotientRel_def
              (p := DeRhamExactClosedForms (I := I)
                (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n)).mp hrel))
  refine ⟨connecting, ?_⟩
  intro omega data
  let chosen :
      DeRhamMayerVietorisConnectingData
        (I := I) (A := A) U V hcover n omega :=
    Classical.choice
      (deRham_mayerVietoris_connectingData_nonempty_of_smooth_difference_surjective
        (I := I) (A := A) U V hcover n hsurj omega)
  change connecting
      ((DeRhamExactClosedForms (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n).mkQ omega) =
    (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ data.glued
  simp only [connecting, Submodule.mkQ_apply]
  change
    (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ chosen.glued =
      (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ data.glued
  exact deRham_mayerVietoris_connectingData_same_glued
    (I := I) (A := A) U V hcover n omega chosen data

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Existence of a connecting map from a partition of unity
statement:
  In the standard finite-dimensional real smooth setting, there exists a
  connecting map \(H^n(U\cap V)\to H^{n+1}(M)\) satisfying the
  glued-differential formula.
proof:
  Apply the abstract construction of the connecting map, using
  partition-of-unity surjectivity of the smooth overlap-difference map.
-/
theorem deRham_mayerVietoris_connecting_formula_exists_from_data_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    ∃ connecting :
        DeRhamCohomology (I := Iℝ) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
          DeRhamCohomology (I := Iℝ) (M := M) (A := A) (n + 1),
      DeRhamMayerVietorisConnectingFormula (I := Iℝ) (A := A) U V hcover n
        connecting := by
  exact deRham_mayerVietoris_connecting_formula_exists_from_data_of_smooth_difference_surjective
    (I := Iℝ) (A := A) U V hcover n
    (fun m omega =>
      deRham_mayerVietoris_smooth_difference_surjective_of_partitionOfUnity
        (A := A) Iℝ U V hcover m omega)

/--
%%handwave
name:
  The connecting map kills overlap differences
statement:
  A connecting map satisfying the glued-differential formula sends every
  Mayer-Vietoris overlap difference to zero.
proof:
  Work with closed representatives.  For an overlap difference, choose the
  evident lift from the two representatives; the glued differential is the zero
  closed form, so its cohomology class is zero.
-/
theorem deRham_mayerVietoris_connecting_difference_eq_zero_of_formula
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (connecting :
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
        DeRhamCohomology (I := I) (M := M) (A := A) (n + 1))
    (hformula :
      DeRhamMayerVietorisConnectingFormula (I := I) (A := A) U V hcover n connecting)
    (omega :
      DeRhamCohomology (I := I) (M := U) (A := A) n ×
        DeRhamCohomology (I := I) (M := V) (A := A) n) :
    connecting (deRhamMayerVietorisDifference (I := I) (A := A) U V n omega) = 0 := by
  rcases omega with ⟨omegaU, omegaV⟩
  induction omegaU using Submodule.Quotient.induction_on with
  | _ alpha =>
      induction omegaV using Submodule.Quotient.induction_on with
      | _ beta =>
          let overlap :
              DeRhamClosedForms (I := I)
                (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n :=
            deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
                (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha -
              deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
                (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta
          let data :
              DeRhamMayerVietorisConnectingData
                (I := I) (A := A) U V hcover n overlap :=
            { lift := (alpha.1, beta.1)
              lift_difference := by
                simp [overlap, deRhamMayerVietorisSmoothDifference,
                  deRhamClosedFormsRestrictionOfLE]
              glued := 0
              glued_restriction := by
                rw [alpha.2, beta.2]
                simp [deRhamMayerVietorisSmoothRestriction] }
          change connecting
              ((DeRhamExactClosedForms (I := I)
                (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n).mkQ overlap) = 0
          rw [hformula overlap data]
          change
            (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ
                (0 : DeRhamClosedForms (I := I) (M := M) (A := A) (n + 1)) = 0
          simp

/--
%%handwave
name:
  Restricting after the connecting map is zero
statement:
  A connecting map satisfying the glued-differential formula has zero composite
  with the restriction map \(H^{n+1}(M)\to H^{n+1}(U)\oplus H^{n+1}(V)\).
proof:
  Choose connecting data for a closed representative.  The glued form restricts
  to the differentials of the two lifted pieces, so both restrictions represent
  exact cohomology classes.
-/
theorem deRham_mayerVietoris_restriction_connecting_eq_zero_of_formula
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (connecting :
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
        DeRhamCohomology (I := I) (M := M) (A := A) (n + 1))
    (hdata :
      ∀ omega :
        DeRhamClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n,
        Nonempty (DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega))
    (hformula :
      DeRhamMayerVietorisConnectingFormula (I := I) (A := A) U V hcover n connecting)
    (omega :
      DeRhamCohomology (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n) :
    deRhamMayerVietorisRestriction (I := I) (A := A) U V (n + 1)
        (connecting omega) = 0 := by
  induction omega using Submodule.Quotient.induction_on with
  | _ omega =>
      let data : DeRhamMayerVietorisConnectingData
          (I := I) (A := A) U V hcover n omega :=
        Classical.choice (hdata omega)
      change
        deRhamMayerVietorisRestriction (I := I) (A := A) U V (n + 1)
          (connecting
            ((DeRhamExactClosedForms (I := I)
              (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n).mkQ omega)) = 0
      rw [hformula omega data]
      rw [deRhamMayerVietorisRestriction]
      apply Prod.ext
      · simp only [deRhamCohomologyRestrictionToOpen, Submodule.mkQ_apply,
          Submodule.mapQ_apply]
        change
          (Submodule.Quotient.mk
            (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) U
              (n + 1) data.glued) :
              DeRhamCohomology (I := I) (M := U) (A := A) (n + 1)) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        change
          restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1) data.glued.1 ∈
            DeRhamExactForms (I := I) (M := U) (A := A) (n + 1)
        have hU :
            restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1) data.glued.1 =
              deRhamDifferential (I := I) (M := U) (A := A) n data.lift.1 := by
          simpa [deRhamMayerVietorisSmoothRestriction] using
            congrArg Prod.fst data.glued_restriction
        rw [DeRhamExactForms]
        exact ⟨data.lift.1, hU.symm⟩
      · simp only [deRhamCohomologyRestrictionToOpen, Submodule.mkQ_apply,
          Submodule.mapQ_apply]
        change
          (Submodule.Quotient.mk
            (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A) V
              (n + 1) data.glued) :
              DeRhamCohomology (I := I) (M := V) (A := A) (n + 1)) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        change
          restrictSmoothFormsToOpen (I := I) (A := A) V (n + 1) data.glued.1 ∈
            DeRhamExactForms (I := I) (M := V) (A := A) (n + 1)
        have hV :
            restrictSmoothFormsToOpen (I := I) (A := A) V (n + 1) data.glued.1 =
              deRhamDifferential (I := I) (M := V) (A := A) n data.lift.2 := by
          simpa [deRhamMayerVietorisSmoothRestriction] using
            congrArg Prod.snd data.glued_restriction
        rw [DeRhamExactForms]
        exact ⟨data.lift.2, hV.symm⟩

/--
%%handwave
name:
  Kernel of the connecting map lies in the range of the difference map
statement:
  If a class on \(U\cap V\) is killed by a connecting map satisfying the
  glued-differential formula, then it is the overlap difference of a pair of
  classes on \(U\) and \(V\).
proof:
  Choose connecting data.  Since the glued class is exact, write it as
  \(d\theta\).  Subtract the restrictions of \(\theta\) from the two lifted
  pieces; the resulting forms are closed and their overlap difference is the
  original representative.
-/
theorem deRham_mayerVietoris_connecting_kernel_mem_range_difference_of_formula
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (connecting :
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
        DeRhamCohomology (I := I) (M := M) (A := A) (n + 1))
    (hdata :
      ∀ omega :
        DeRhamClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n,
        Nonempty (DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega))
    (hformula :
      DeRhamMayerVietorisConnectingFormula (I := I) (A := A) U V hcover n connecting)
    (omega :
      DeRhamCohomology (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n)
    (hzero : connecting omega = 0) :
    ∃ eta :
      DeRhamCohomology (I := I) (M := U) (A := A) n ×
        DeRhamCohomology (I := I) (M := V) (A := A) n,
      deRhamMayerVietorisDifference (I := I) (A := A) U V n eta = omega := by
  induction omega using Submodule.Quotient.induction_on with
  | _ omega =>
      let data : DeRhamMayerVietorisConnectingData
          (I := I) (A := A) U V hcover n omega :=
        Classical.choice (hdata omega)
      have hglued_zero :
          (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ
              data.glued = 0 := by
        rw [← hformula omega data]
        simpa using hzero
      have hglued_exact :
          data.glued ∈ DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        exact hglued_zero
      change data.glued.1 ∈
          DeRhamExactForms (I := I) (M := M) (A := A) (n + 1) at hglued_exact
      rw [DeRhamExactForms] at hglued_exact
      rcases hglued_exact with ⟨theta, htheta⟩
      have hUglued :
          restrictSmoothFormsToOpen (I := I) (A := A) U (n + 1) data.glued.1 =
            deRhamDifferential (I := I) (M := U) (A := A) n data.lift.1 := by
        simpa [deRhamMayerVietorisSmoothRestriction] using
          congrArg Prod.fst data.glued_restriction
      have hVglued :
          restrictSmoothFormsToOpen (I := I) (A := A) V (n + 1) data.glued.1 =
            deRhamDifferential (I := I) (M := V) (A := A) n data.lift.2 := by
        simpa [deRhamMayerVietorisSmoothRestriction] using
          congrArg Prod.snd data.glued_restriction
      let alpha :
          DeRhamClosedForms (I := I) (M := U) (A := A) n :=
        ⟨data.lift.1 - restrictSmoothFormsToOpen (I := I) (A := A) U n theta, by
          change deRhamDifferential (I := I) (M := U) (A := A) n
              (data.lift.1 - restrictSmoothFormsToOpen (I := I) (A := A) U n theta) = 0
          rw [map_sub]
          rw [deRhamDifferential_restrictSmoothFormsToOpen (I := I) (A := A) U theta]
          rw [htheta]
          rw [hUglued]
          exact sub_self _⟩
      let beta :
          DeRhamClosedForms (I := I) (M := V) (A := A) n :=
        ⟨data.lift.2 - restrictSmoothFormsToOpen (I := I) (A := A) V n theta, by
          change deRhamDifferential (I := I) (M := V) (A := A) n
              (data.lift.2 - restrictSmoothFormsToOpen (I := I) (A := A) V n theta) = 0
          rw [map_sub]
          rw [deRhamDifferential_restrictSmoothFormsToOpen (I := I) (A := A) V theta]
          rw [htheta]
          rw [hVglued]
          exact sub_self _⟩
      refine ⟨
        ((DeRhamExactClosedForms (I := I) (M := U) (A := A) n).mkQ alpha,
          (DeRhamExactClosedForms (I := I) (M := V) (A := A) n).mkQ beta), ?_⟩
      have htheta_overlap :
          restrictSmoothFormsOfLE (I := I) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
              (restrictSmoothFormsToOpen (I := I) (A := A) U n theta) =
            restrictSmoothFormsOfLE (I := I) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
              (restrictSmoothFormsToOpen (I := I) (A := A) V n theta) :=
        restrictSmoothForms_overlap_restrictions_eq (I := I) (A := A) U V n theta
      have hoverlap :
          deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n alpha -
            deRhamClosedFormsRestrictionOfLE (I := I) (M := M) (A := A)
              (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n beta =
            omega := by
        apply Subtype.ext
        change
          deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n
              (alpha.1, beta.1) = omega.1
        calc
          deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n
              (alpha.1, beta.1)
              = deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n
                  (data.lift.1, data.lift.2) := by
                change
                  restrictSmoothFormsOfLE (I := I) (A := A)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
                      alpha.1 -
                    restrictSmoothFormsOfLE (I := I) (A := A)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
                      beta.1 =
                    restrictSmoothFormsOfLE (I := I) (A := A)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U) inf_le_left n
                      data.lift.1 -
                    restrictSmoothFormsOfLE (I := I) (A := A)
                      (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V) inf_le_right n
                      data.lift.2
                have hleft :
                    restrictSmoothFormsOfLE (I := I) (A := A)
                        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                        inf_le_left n alpha.1 =
                      restrictSmoothFormsOfLE (I := I) (A := A)
                          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                          inf_le_left n data.lift.1 -
                        restrictSmoothFormsOfLE (I := I) (A := A)
                          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                          inf_le_left n
                          (restrictSmoothFormsToOpen (I := I) (A := A) U n theta) := by
                  change
                    restrictSmoothFormsOfLE (I := I) (A := A)
                        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
                        inf_le_left n
                        (data.lift.1 -
                          restrictSmoothFormsToOpen (I := I) (A := A) U n theta) = _
                  rw [map_sub]
                have hright :
                    restrictSmoothFormsOfLE (I := I) (A := A)
                        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                        inf_le_right n beta.1 =
                      restrictSmoothFormsOfLE (I := I) (A := A)
                          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                          inf_le_right n data.lift.2 -
                        restrictSmoothFormsOfLE (I := I) (A := A)
                          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                          inf_le_right n
                          (restrictSmoothFormsToOpen (I := I) (A := A) V n theta) := by
                  change
                    restrictSmoothFormsOfLE (I := I) (A := A)
                        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
                        inf_le_right n
                        (data.lift.2 -
                          restrictSmoothFormsToOpen (I := I) (A := A) V n theta) = _
                  rw [map_sub]
                rw [hleft, hright, htheta_overlap]
                abel
          _ = omega.1 := data.lift_difference
      exact congrArg
        ((DeRhamExactClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n).mkQ)
        hoverlap

/--
%%handwave
name:
  Exactness at the overlap term from a connecting formula
statement:
  For any connecting map satisfying the glued-differential formula, the image of
  the overlap-difference map is exactly the kernel of the connecting map.
proof:
  Package the two preceding facts: the connecting map kills every overlap
  difference, and every class killed by the connecting map is such a difference.
-/
theorem deRham_mayerVietoris_exact_difference_connecting_of_formula
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (connecting :
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
        DeRhamCohomology (I := I) (M := M) (A := A) (n + 1))
    (hdata :
      ∀ omega :
        DeRhamClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n,
        Nonempty (DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega))
    (hformula :
      DeRhamMayerVietorisConnectingFormula (I := I) (A := A) U V hcover n connecting) :
    Function.Exact
      (deRhamMayerVietorisDifference (I := I) (A := A) U V n)
      connecting := by
  refine Function.Exact.of_comp_of_mem_range ?_ ?_
  · funext omega
    exact deRham_mayerVietoris_connecting_difference_eq_zero_of_formula
      (I := I) (A := A) U V hcover n connecting hformula omega
  · intro omega hzero
    exact deRham_mayerVietoris_connecting_kernel_mem_range_difference_of_formula
      (I := I) (A := A) U V hcover n connecting hdata hformula omega hzero

/--
%%handwave
name:
  Kernel of restriction lies in the range of the connecting map
statement:
  If a class in \(H^{n+1}(M)\) restricts to zero on both \(U\) and \(V\), then it
  is the image of a class on \(U\cap V\) under any connecting map satisfying the
  glued-differential formula.
proof:
  Choose exact primitives for the two zero restrictions.  Their overlap
  difference is a closed form on \(U\cap V\), and the corresponding connecting
  data has the original class as its glued form.
-/
theorem deRham_mayerVietoris_restriction_kernel_mem_range_connecting_of_formula
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (connecting :
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
        DeRhamCohomology (I := I) (M := M) (A := A) (n + 1))
    (hformula :
      DeRhamMayerVietorisConnectingFormula (I := I) (A := A) U V hcover n connecting)
    (eta : DeRhamCohomology (I := I) (M := M) (A := A) (n + 1))
    (hzero :
      deRhamMayerVietorisRestriction (I := I) (A := A) U V (n + 1) eta = 0) :
    ∃ omega :
      DeRhamCohomology (I := I)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n,
      connecting omega = eta := by
  induction eta using Submodule.Quotient.induction_on with
  | _ eta =>
      change
        deRhamMayerVietorisRestriction (I := I) (A := A) U V (n + 1)
          ((DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ eta) = 0
        at hzero
      have hUzero :
          (DeRhamExactClosedForms (I := I) (M := U) (A := A) (n + 1)).mkQ
              (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A)
                U (n + 1) eta) = 0 := by
        have h := congrArg Prod.fst hzero
        simpa [deRhamMayerVietorisRestriction, deRhamCohomologyRestrictionToOpen,
          Submodule.mkQ_apply, Submodule.mapQ_apply] using h
      have hVzero :
          (DeRhamExactClosedForms (I := I) (M := V) (A := A) (n + 1)).mkQ
              (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A)
                V (n + 1) eta) = 0 := by
        have h := congrArg Prod.snd hzero
        simpa [deRhamMayerVietorisRestriction, deRhamCohomologyRestrictionToOpen,
          Submodule.mkQ_apply, Submodule.mapQ_apply] using h
      have hUexact :
          deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A)
              U (n + 1) eta ∈
            DeRhamExactClosedForms (I := I) (M := U) (A := A) (n + 1) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        exact hUzero
      have hVexact :
          deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A)
              V (n + 1) eta ∈
            DeRhamExactClosedForms (I := I) (M := V) (A := A) (n + 1) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        exact hVzero
      change
        (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A)
          U (n + 1) eta).1 ∈
          DeRhamExactForms (I := I) (M := U) (A := A) (n + 1) at hUexact
      change
        (deRhamClosedFormsRestrictionToOpen (I := I) (M := M) (A := A)
          V (n + 1) eta).1 ∈
          DeRhamExactForms (I := I) (M := V) (A := A) (n + 1) at hVexact
      rw [DeRhamExactForms] at hUexact hVexact
      rcases hUexact with ⟨alpha, halpha⟩
      rcases hVexact with ⟨beta, hbeta⟩
      let omega :
          DeRhamClosedForms (I := I)
            (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n :=
        ⟨deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n
            (alpha, beta), by
          change
            deRhamDifferential (I := I)
              (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n
              (deRhamMayerVietorisSmoothDifference (I := I) (A := A) U V n
                (alpha, beta)) = 0
          rw [← deRhamDifferential_mayerVietorisSmoothDifference
            (I := I) (A := A) U V n (alpha, beta)]
          rw [halpha, hbeta]
          rw [deRhamMayerVietorisSmoothDifference]
          exact sub_eq_zero.mpr
            (restrictSmoothForms_overlap_restrictions_eq
              (I := I) (A := A) U V (n + 1) eta.1)⟩
      let data :
          DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega :=
        { lift := (alpha, beta)
          lift_difference := rfl
          glued := eta
          glued_restriction := by
            apply Prod.ext
            · exact halpha.symm
            · exact hbeta.symm }
      refine ⟨
        (DeRhamExactClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n).mkQ omega, ?_⟩
      rw [hformula omega data]
      change
        (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ eta =
          (DeRhamExactClosedForms (I := I) (M := M) (A := A) (n + 1)).mkQ eta
      rfl

/--
%%handwave
name:
  Exactness at the global term from a connecting formula
statement:
  For any connecting map satisfying the glued-differential formula, the image of
  the connecting map is exactly the kernel of the restriction map from
  \(H^{n+1}(M)\) to the two opens.
proof:
  Package the two preceding facts: restriction after the connecting map is zero,
  and every global class with zero restrictions is obtained by the connecting
  construction.
-/
theorem deRham_mayerVietoris_exact_connecting_restriction_of_formula
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (connecting :
      DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
        DeRhamCohomology (I := I) (M := M) (A := A) (n + 1))
    (hdata :
      ∀ omega :
        DeRhamClosedForms (I := I)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n,
        Nonempty (DeRhamMayerVietorisConnectingData (I := I) (A := A) U V hcover n omega))
    (hformula :
      DeRhamMayerVietorisConnectingFormula (I := I) (A := A) U V hcover n connecting) :
    Function.Exact connecting
      (deRhamMayerVietorisRestriction (I := I) (A := A) U V (n + 1)) := by
  refine Function.Exact.of_comp_of_mem_range ?_ ?_
  · funext omega
    exact deRham_mayerVietoris_restriction_connecting_eq_zero_of_formula
      (I := I) (A := A) U V hcover n connecting hdata hformula omega
  · intro eta hzero
    exact deRham_mayerVietoris_restriction_kernel_mem_range_connecting_of_formula
      (I := I) (A := A) U V hcover n connecting hformula eta hzero

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Existence of the Mayer-Vietoris connecting map with exactness
statement:
  In the standard finite-dimensional real smooth setting, there is a connecting
  map \(H^n(U\cap V)\to H^{n+1}(M)\) for which the difference-connecting and
  connecting-restriction pairs are exact, and which satisfies the
  glued-differential formula.
proof:
  Choose the connecting map supplied by the partition-of-unity construction,
  then apply the exactness theorems derived from its formula and the existence of
  connecting data.
-/
theorem deRham_mayerVietoris_connecting_exists_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    ∃ connecting :
        DeRhamCohomology (I := Iℝ) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
          DeRhamCohomology (I := Iℝ) (M := M) (A := A) (n + 1),
      Function.Exact
          (deRhamMayerVietorisDifference (I := Iℝ) (A := A) U V n)
          connecting ∧
        Function.Exact connecting
          (deRhamMayerVietorisRestriction (I := Iℝ) (A := A) U V (n + 1)) ∧
        DeRhamMayerVietorisConnectingFormula (I := Iℝ) (A := A) U V hcover n
          connecting := by
  rcases deRham_mayerVietoris_connecting_formula_exists_from_data_of_partitionOfUnity
      (A := A) Iℝ U V hcover n with
    ⟨connecting, hformula⟩
  have hdata :
      ∀ omega :
        DeRhamClosedForms (I := Iℝ)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n,
        Nonempty
          (DeRhamMayerVietorisConnectingData (I := Iℝ) (A := A)
            U V hcover n omega) :=
    deRham_mayerVietoris_connectingData_nonempty_of_partitionOfUnity
      (A := A) Iℝ U V hcover n
  exact ⟨connecting,
    deRham_mayerVietoris_exact_difference_connecting_of_formula
      (I := Iℝ) (A := A) U V hcover n connecting hdata hformula,
    deRham_mayerVietoris_exact_connecting_restriction_of_formula
      (I := Iℝ) (A := A) U V hcover n connecting hdata hformula,
    hformula⟩

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Mayer-Vietoris connecting map from a partition of unity
statement:
  In the standard smooth real setting, the connecting map \(\partial_n:H^n(U\cap V)\to H^{n+1}(M)\) is chosen from the partition-of-unity lift construction.
-/
noncomputable def deRhamMayerVietorisConnectingOfPartitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    DeRhamCohomology (I := Iℝ) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
      DeRhamCohomology (I := Iℝ) (M := M) (A := A) (n + 1) :=
  Classical.choose
    (deRham_mayerVietoris_connecting_exists_of_partitionOfUnity
      (A := A) Iℝ U V hcover n)

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Formula for the partition-of-unity connecting map
statement:
  If \(\gamma\) is a closed overlap form, \(\alpha|_{U\cap V}-\beta|_{U\cap V}=\gamma\), and \(d\alpha,d\beta\) glue to \(\eta\), then the partition-of-unity connecting map sends \([\gamma]\) to \([\eta]\).
proof:
  Unfold the chosen connecting map and use the formula component stored in the
  existence theorem.
-/
theorem deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ)
    (omega :
      DeRhamClosedForms (I := Iℝ)
        (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n)
    (data :
      DeRhamMayerVietorisConnectingData (I := Iℝ) (A := A) U V hcover n omega) :
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := A) Iℝ U V hcover n
        ((DeRhamExactClosedForms (I := Iℝ)
          (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n).mkQ omega) =
      (DeRhamExactClosedForms (I := Iℝ) (M := M) (A := A) (n + 1)).mkQ
        data.glued := by
  exact
    (Classical.choose_spec
      (deRham_mayerVietoris_connecting_exists_of_partitionOfUnity
        (A := A) Iℝ U V hcover n)).2.2 omega data

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Exactness at the overlap term for the chosen connecting map
statement:
  In the standard finite-dimensional real smooth setting, the image of the
  Mayer-Vietoris difference map is the kernel of the chosen connecting map.
proof:
  Read this exactness assertion from the existence theorem used to choose the
  connecting map.
-/
theorem deRham_mayerVietoris_exact_difference_connecting_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    Function.Exact
      (deRhamMayerVietorisDifference (I := Iℝ) (A := A) U V n)
      (deRhamMayerVietorisConnectingOfPartitionOfUnity (A := A) Iℝ U V hcover n) := by
  exact
    (Classical.choose_spec
      (deRham_mayerVietoris_connecting_exists_of_partitionOfUnity
        (A := A) Iℝ U V hcover n)).1

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Exactness at the global term for the chosen connecting map
statement:
  In the standard finite-dimensional real smooth setting, the image of the
  chosen connecting map is the kernel of the restriction map from
  \(H^{n+1}(M)\) to \(H^{n+1}(U)\oplus H^{n+1}(V)\).
proof:
  Read this exactness assertion from the existence theorem used to choose the
  connecting map.
-/
theorem deRham_mayerVietoris_exact_connecting_restriction_of_partitionOfUnity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    Function.Exact
      (deRhamMayerVietorisConnectingOfPartitionOfUnity (A := A) Iℝ U V hcover n)
      (deRhamMayerVietorisRestriction (I := Iℝ) (A := A) U V (n + 1)) := by
  exact
    (Classical.choose_spec
      (deRham_mayerVietoris_connecting_exists_of_partitionOfUnity
        (A := A) Iℝ U V hcover n)).2.1

/--
Data and exactness assertions for the Mayer-Vietoris long exact sequence
associated to an open cover by two sets.
-/
structure DeRhamMayerVietorisLongExact
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) where
  connecting : (n : ℕ) →
    DeRhamCohomology (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M)) (A := A) n →
      DeRhamCohomology (I := I) (M := M) (A := A) (n + 1)
  injective_restriction_zero :
    Function.Injective (deRhamMayerVietorisRestriction (I := I) (A := A) U V 0)
  exact_restriction_difference :
    ∀ n, Function.Exact
      (deRhamMayerVietorisRestriction (I := I) (A := A) U V n)
      (deRhamMayerVietorisDifference (I := I) (A := A) U V n)
  exact_difference_connecting :
    ∀ n, Function.Exact
      (deRhamMayerVietorisDifference (I := I) (A := A) U V n)
      (connecting n)
  exact_connecting_restriction :
    ∀ n, Function.Exact
      (connecting n)
      (deRhamMayerVietorisRestriction (I := I) (A := A) U V (n + 1))

omit [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsRCLikeNormedField 𝕜]
  [IsManifold I ∞ M] [NormedSpace 𝕜 A] in
/--
%%handwave
name:
  Mayer-Vietoris long exact sequence
statement:
  On a finite-dimensional smooth real manifold with Hausdorff and sigma-compact topology, every two-open cover \(M=U\cup V\) gives the long exact sequence
  \[
    0\to H^0_{\mathrm{dR}}(M)\xrightarrow{\rho_0}H^0_{\mathrm{dR}}(U)\oplus H^0_{\mathrm{dR}}(V)\xrightarrow{\Delta_0}H^0_{\mathrm{dR}}(U\cap V)\xrightarrow{\partial_0}H^1_{\mathrm{dR}}(M)\xrightarrow{\rho_1}H^1_{\mathrm{dR}}(U)\oplus H^1_{\mathrm{dR}}(V)\xrightarrow{\Delta_1}H^1_{\mathrm{dR}}(U\cap V)\xrightarrow{\partial_1}\cdots,
  \]
  where \(\rho_n\) is restriction to \(U\) and \(V\), \(\Delta_n\) is the difference of the two restrictions to \(U\cap V\), and \(\partial_n\) is obtained by lifting overlap forms with a smooth partition of unity.
proof:
  Exactness at \(H^0(M)\) is separatedness of smooth functions, exactness at \(H^n(U)\oplus H^n(V)\) uses the partition-of-unity lift on forms, and the two exactness statements adjacent to the connecting map follow from the glued-differential formula for the connecting map.
tags:
  milestone
-/
theorem deRham_mayerVietoris_longExact
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [NormedSpace ℝ A]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤) :
    Nonempty (DeRhamMayerVietorisLongExact (I := Iℝ) (A := A) U V hcover) := by
  refine ⟨
    { connecting := deRhamMayerVietorisConnectingOfPartitionOfUnity (A := A) Iℝ U V hcover
      injective_restriction_zero :=
        deRham_mayerVietoris_restriction_injective_zero (I := Iℝ) (A := A)
          U V hcover
      exact_restriction_difference := fun n ↦
        deRham_mayerVietoris_exact_restriction_difference_of_partitionOfUnity
          (A := A) Iℝ U V hcover n
      exact_difference_connecting := fun n ↦
        deRham_mayerVietoris_exact_difference_connecting_of_partitionOfUnity
          (A := A) Iℝ U V hcover n
      exact_connecting_restriction := fun n ↦
        deRham_mayerVietoris_exact_connecting_restriction_of_partitionOfUnity
          (A := A) Iℝ U V hcover n }⟩

/--
%%handwave
name:
  Mayer--Vietoris transfer of first-cohomology vanishing
statement:
  Let \(M=U\cup V\) be a two-open cover of a finite-dimensional smooth real
  manifold.  If \(H^1_{\mathrm{dR}}(M;A)=0\) and the restriction
  \(H^1_{\mathrm{dR}}(U;A)\to H^1_{\mathrm{dR}}(U\cap V;A)\) is surjective,
  then \(H^1_{\mathrm{dR}}(V;A)=0\).
proof:
  Given a class on \(V\), lift its overlap restriction to a class on \(U\).
  The resulting pair has zero Mayer--Vietoris difference, so exactness makes
  it the restriction of an ambient class.  The ambient class is zero, hence
  so is the original class on (V).
-/
theorem deRhamH1_subsingleton_of_mayerVietoris_left_restriction_surjective
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] [NormedSpace ℝ A]
    [Subsingleton
      (DeRhamCohomology (I := Iℝ) (M := M) (A := A) 1)]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤)
    (hsurj : Function.Surjective
      (deRhamCohomologyRestrictionOfLE (I := Iℝ) (A := A)
        (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
        inf_le_left 1)) :
    Subsingleton
      (DeRhamCohomology (I := Iℝ) (M := V) (A := A) 1) := by
  rcases deRham_mayerVietoris_longExact (A := A) Iℝ U V hcover with ⟨LES⟩
  constructor
  intro b b'
  have hzero :
      ∀ c : DeRhamCohomology (I := Iℝ) (M := V) (A := A) 1, c = 0 := by
    intro c
    rcases hsurj
        (deRhamCohomologyRestrictionOfLE (I := Iℝ) (A := A)
          (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
          inf_le_right 1 c) with ⟨a, ha⟩
    have hdiff :
        deRhamMayerVietorisDifference (I := Iℝ) (A := A) U V 1
          (a, c) = 0 := by
      rw [deRhamMayerVietorisDifference, ha]
      exact sub_self _
    rcases (LES.exact_restriction_difference 1 (a, c)).mp hdiff with
      ⟨g, hg⟩
    have hg0 : g = 0 := Subsingleton.elim _ _
    have hpair : (a, c) = 0 := by
      rw [← hg, hg0]
      apply Prod.ext
      · exact LinearMap.map_zero
          (deRhamCohomologyRestrictionToOpen
            (I := Iℝ) (M := M) (A := A) U 1)
      · exact LinearMap.map_zero
          (deRhamCohomologyRestrictionToOpen
            (I := Iℝ) (M := M) (A := A) V 1)
    exact congrArg Prod.snd hpair
  rw [hzero b, hzero b']

end MayerVietoris

end

end Manifold
end JJMath
