import JJMath.Manifold.DeRham
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Poincare lemma for the de Rham complex

This file isolates the local analytic input in de Rham's theorem.  The
homotopy-operator construction is stated for convex open subsets of a real
model vector space, and the quotient-level vanishing consequence is proved
from that exactness statement.
-/

open Set
open scoped Manifold ContDiff Topology Interval

namespace JJMath
namespace Manifold

noncomputable section

universe v w m v' w' m' a u

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H)
variable [IsManifold I ∞ M]
variable {A : Type a} [NormedAddCommGroup A] [NormedSpace 𝕜 A]

/--
%%handwave
name:
  Exactness of all closed forms kills de Rham cohomology
statement:
  If every closed \(n\)-form on a smooth manifold is exact, then degree \(n\)
  de Rham cohomology is a singleton.
proof:
  The submodule of exact closed forms is then the whole module of closed forms,
  so the quotient of closed forms by exact closed forms has only one element.
-/
theorem deRhamCohomology_subsingleton_of_closedForms_le_exactForms
    {n : ℕ}
    (h :
      DeRhamClosedForms (I := I) (M := M) (A := A) n ≤
        DeRhamExactForms (I := I) (M := M) (A := A) n) :
    Subsingleton (DeRhamCohomology (I := I) (M := M) (A := A) n) := by
  have htop :
      DeRhamExactClosedForms (I := I) (M := M) (A := A) n = ⊤ := by
    ext omega
    constructor
    · intro _homega
      trivial
    · intro _homega
      change
        (omega : SmoothForms (I := I) (M := M) A n) ∈
          DeRhamExactForms (I := I) (M := M) (A := A) n
      exact h omega.2
  refine ⟨fun alpha beta ↦ ?_⟩
  induction alpha using Submodule.Quotient.induction_on with
  | _ alpha =>
      induction beta using Submodule.Quotient.induction_on with
      | _ beta =>
          rw [Submodule.Quotient.eq]
          rw [htop]
          trivial

/--
%%handwave
name:
  Vanishing de Rham cohomology makes closed forms exact
statement:
  If degree \(n\) de Rham cohomology is a singleton, then every closed
  \(n\)-form is exact.
proof:
  The quotient class of a closed form is equal to the zero class.  By the
  kernel criterion for the quotient map, this means exactly that the closed
  form lies in the exact submodule.
-/
theorem deRhamClosedForm_mem_exactForms_of_cohomology_subsingleton
    {n : ℕ}
    [Subsingleton (DeRhamCohomology (I := I) (M := M) (A := A) n)]
    (omega : DeRhamClosedForms (I := I) (M := M) (A := A) n) :
    (omega : SmoothForms (I := I) (M := M) A n) ∈
      DeRhamExactForms (I := I) (M := M) (A := A) n := by
  have hclass :
      (DeRhamExactClosedForms (I := I) (M := M) (A := A) n).mkQ omega = 0 :=
    Subsingleton.elim _ _
  have hmem :
      omega ∈ DeRhamExactClosedForms (I := I) (M := M) (A := A) n := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [Submodule.mkQ_apply] using hclass
  simpa [DeRhamExactClosedForms] using hmem

/--
%%handwave
name:
  Vanishing positive de Rham cohomology gives primitives
statement:
  If degree \(n+1\) de Rham cohomology is a singleton, then every closed
  \((n+1)\)-form has a smooth primitive.
proof:
  By [vanishing de Rham cohomology makes closed forms exact](lean:JJMath.Manifold.deRhamClosedForm_mem_exactForms_of_cohomology_subsingleton), the closed form lies in the exact submodule.  In positive degree that submodule is the range of the previous exterior derivative.
-/
theorem deRhamClosedSuccForm_has_primitive_of_cohomology_subsingleton
    {n : ℕ}
    [Subsingleton (DeRhamCohomology (I := I) (M := M) (A := A) (n + 1))]
    (omega : DeRhamClosedForms (I := I) (M := M) (A := A) (n + 1)) :
    ∃ theta : SmoothForms (I := I) (M := M) A n,
      deRhamDifferential (I := I) (M := M) (A := A) n theta = omega := by
  have hexact :=
    deRhamClosedForm_mem_exactForms_of_cohomology_subsingleton
      (I := I) (M := M) (A := A) (n := n + 1) omega
  simpa [DeRhamExactForms] using hexact

/--
%%handwave
name:
  Positive-degree exactness kills positive de Rham cohomology
statement:
  If every closed \((n+1)\)-form on a smooth manifold is exact, then degree
  \(n+1\) de Rham cohomology is a singleton.
proof:
  This is [the quotient argument that exactness of all closed forms kills de Rham cohomology](lean:JJMath.Manifold.deRhamCohomology_subsingleton_of_closedForms_le_exactForms).
-/
theorem deRhamCohomology_subsingleton_of_closedForms_succ_le_exactForms
    {n : ℕ}
    (h :
      ∀ omega :
        DeRhamClosedForms (I := I) (M := M) (A := A) (n + 1),
          (omega : SmoothForms (I := I) (M := M) A (n + 1)) ∈
            DeRhamExactForms (I := I) (M := M) (A := A) (n + 1)) :
    Subsingleton (DeRhamCohomology (I := I) (M := M) (A := A) (n + 1)) :=
  deRhamCohomology_subsingleton_of_closedForms_le_exactForms
    (I := I) (M := M) (A := A) (n := n + 1)
    (fun omega hclosed ↦ h ⟨omega, hclosed⟩)

section ConvexModel

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

/--
%%handwave
name:
  Straight segments in convex open sets
statement:
  If \(U\) is convex and \(x_0,x\in U\), then the point
  \((1-t)x_0+tx\) belongs to \(U\) for every \(0\le t\le 1\).
proof:
  This is the defining closure property of a convex set, expressed using the
  affine line segment from \(x_0\) to \(x\).
-/
theorem convexOpen_lineMap_mem
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E))
    (x₀ x : U) (t : Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (x₀ : E) (x : E) (t : ℝ) ∈ (U : Set E) := by
  exact hconvex.lineMap_mem (x := (x₀ : E)) (y := (x : E)) x₀.2 x.2 t.2

/--
%%handwave
name:
  Straight-line contraction of a convex open set
statement:
  A nonempty convex open set \(U\) is contracted to any chosen point \(x_0\in U\)
  by the homotopy \(H_t(x)=(1-t)x_0+tx\), \(0\le t\le 1\).
proof:
  The preceding segment-containment statement shows that \(H_t(x)\) remains in
  \(U\), so the formula defines a map \([0,1]\times U\to U\).
-/
def convexOpenStraightLineHomotopy
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (t : Set.Icc (0 : ℝ) 1) (x : U) : U :=
  ⟨AffineMap.lineMap (x₀ : E) (x : E) (t : ℝ),
    convexOpen_lineMap_mem (E := E) U hconvex x₀ x t⟩

/--
%%handwave
name:
  Straight-line contraction begins at the base point
statement:
  At time \(0\), the straight-line contraction of a convex open set is the
  constant map with value \(x_0\).
proof:
  Evaluate the affine segment formula at \(t=0\).
-/
@[simp]
theorem convexOpenStraightLineHomotopy_zero
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ x : U) :
    convexOpenStraightLineHomotopy (E := E) U hconvex x₀
        ⟨0, by simp⟩ x = x₀ := by
  apply Subtype.ext
  simp [convexOpenStraightLineHomotopy]

/--
%%handwave
name:
  Straight-line contraction ends at the identity
statement:
  At time \(1\), the straight-line contraction of a convex open set is the
  identity map.
proof:
  Evaluate the affine segment formula at \(t=1\).
-/
@[simp]
theorem convexOpenStraightLineHomotopy_one
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ x : U) :
    convexOpenStraightLineHomotopy (E := E) U hconvex x₀
        ⟨1, by simp⟩ x = x := by
  apply Subtype.ext
  simp [convexOpenStraightLineHomotopy]

/--
%%handwave
name:
  Smoothness of the straight-line contraction
statement:
  The straight-line contraction of a convex open subset of a real normed vector
  space is a smooth ambient-valued map of \([0,1]\times U\).
proof:
  The coordinate \(t\mapsto t\) on the interval is smooth, the inclusion
  \(U\hookrightarrow E\) is smooth, and the formula
  \((1-t)x_0+tx\) is built from smooth addition and scalar multiplication.
-/
theorem contMDiff_coe_convexOpenStraightLineHomotopy
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U) :
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : Set.Icc (0 : ℝ) 1 × U =>
        (convexOpenStraightLineHomotopy (E := E) U hconvex x₀ p.1 p.2 : E)) := by
  have ht :
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞
        (fun p : Set.Icc (0 : ℝ) 1 × U => (p.1 : ℝ)) :=
    (contMDiff_subtype_coe_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).comp
      (contMDiff_fst (I := 𝓡∂ 1) (J := 𝓘(ℝ, E)) (n := ∞))
  have hx :
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : Set.Icc (0 : ℝ) 1 × U => (p.2 : E)) :=
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞)).comp
      (contMDiff_snd (I := 𝓡∂ 1) (J := 𝓘(ℝ, E)) (n := ∞))
  have hline :
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : Set.Icc (0 : ℝ) 1 × U =>
          (1 - (p.1 : ℝ)) • (x₀ : E) + (p.1 : ℝ) • (p.2 : E)) :=
    (contMDiff_const.sub ht).smul contMDiff_const |>.add (ht.smul hx)
  simpa [convexOpenStraightLineHomotopy, AffineMap.lineMap_apply_module] using hline

variable [FiniteDimensional ℝ E]

@[instance_reducible]
def normedAddCommGroupTangentSpaceOpenSubtype
    (U : TopologicalSpace.Opens E) (x : U) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

attribute [local instance] normedAddCommGroupTangentSpaceOpenSubtype

@[instance_reducible]
def normedSpaceTangentSpaceOpenSubtype
    (U : TopologicalSpace.Opens E) (x : U) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

attribute [local instance] normedSpaceTangentSpaceOpenSubtype

/-- The model-space coefficient field of a smooth form on an open subset of a vector space. -/
def smoothFormModelCoeff
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n)
    (x : U) :
    E [⋀^Fin n]→L[ℝ] ℝ :=
  omega.toFun x

/-- Extend a coefficient field on an open subset by zero outside the subset. -/
def modelOpenFormCoeffExtension
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (f : U → E [⋀^Fin n]→L[ℝ] ℝ)
    (y : E) :
    E [⋀^Fin n]→L[ℝ] ℝ :=
  letI : Decidable (y ∈ (U : Set E)) := Classical.propDecidable _
  if hy : y ∈ (U : Set E) then f ⟨y, hy⟩ else 0

/--
%%handwave
name:
  Smooth forms on model opens are continuous coefficient fields
statement:
  On an open subset of a finite-dimensional real normed vector space, a smooth
  differential form is a continuous alternating-covector-valued function of the
  base point.
proof:
  In the standard chart of the open subset, the coordinate representative of
  the form is exactly its model-space coefficient field, up to the identity
  tangent map.  The chartwise smoothness condition for a smooth form therefore
  gives continuity of this coefficient field.
-/
theorem continuous_smoothForm_toFun_modelOpen
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n) :
    Continuous
      (fun x : U ↦ smoothFormModelCoeff (E := E) U n omega x) := by
  by_cases hne : Nonempty U
  · let x₀ : U := Classical.choice hne
    let e : OpenPartialHomeomorph U E := chartAt E x₀
    let CE : E → E [⋀^Fin n]→L[ℝ] ℝ :=
      coordinateExpression (I := 𝓘(ℝ, E)) (F := ℝ) (n := n) omega.toFun e
    have he : e ∈ atlas E U := by
      exact chart_mem_atlas E x₀
    have htarget : e.target = (U : Set E) := by
      ext y
      simp [e, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_def]
    have hCE_on : ContinuousOn CE (U : Set E) := by
      simpa [CE, htarget] using (omega.isContMDiff e he).continuousOn
    have hCE_sub : Continuous (fun x : U ↦ CE (x : E)) := by
      rw [← continuousOn_univ]
      exact hCE_on.comp continuous_subtype_val.continuousOn (by
        intro x _hx
        exact x.2)
    have hcoeff_eq : ∀ x : U,
        CE (x : E) = smoothFormModelCoeff (E := E) U n omega x := by
      intro x
      have hself :=
        coordinateExpression_chartAt_self (I := 𝓘(ℝ, E)) (F := ℝ) (n := n)
          omega.toFun x
      simpa [CE, e, smoothFormModelCoeff, TopologicalSpace.Opens.chartAt_eq,
        chartAt_self_eq, extChartAt_model_space_eq_id] using hself
    exact hCE_sub.congr hcoeff_eq
  · rw [continuous_iff_continuousAt]
    intro x
    exact (hne ⟨x⟩).elim

/--
%%handwave
name:
  Smooth forms on model opens have smooth coefficient fields
statement:
  On an open subset of a finite-dimensional real normed vector space, the
  coefficient field of a smooth differential form is smooth in the ambient
  coordinates.
proof:
  In the standard chart of the open subset, the coordinate representative of
  the form is exactly its model-space coefficient field.  The chartwise
  smoothness condition for the form therefore gives smoothness of the
  coefficient field on the open subset.
-/
theorem contDiffOn_smoothFormModelCoeff_modelOpen
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n) :
    ContDiffOn ℝ ∞
      (modelOpenFormCoeffExtension (E := E) U n
        (fun x ↦ smoothFormModelCoeff (E := E) U n omega x))
      (U : Set E) := by
  by_cases hne : Nonempty U
  · let x₀ : U := Classical.choice hne
    let e : OpenPartialHomeomorph U E := chartAt E x₀
    let CE : E → E [⋀^Fin n]→L[ℝ] ℝ :=
      coordinateExpression (I := 𝓘(ℝ, E)) (F := ℝ) (n := n) omega.toFun e
    have he : e ∈ atlas E U := by
      exact chart_mem_atlas E x₀
    have htarget : e.target = (U : Set E) := by
      ext y
      simp [e, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_def]
    have hCE_on : ContDiffOn ℝ ∞ CE (U : Set E) := by
      simpa [CE, htarget] using omega.isContMDiff e he
    have hcoeff_eq : ∀ x : U,
        CE (x : E) = smoothFormModelCoeff (E := E) U n omega x := by
      intro x
      have hself :=
        coordinateExpression_chartAt_self (I := 𝓘(ℝ, E)) (F := ℝ) (n := n)
          omega.toFun x
      simpa [CE, e, smoothFormModelCoeff, TopologicalSpace.Opens.chartAt_eq,
        chartAt_self_eq, extChartAt_model_space_eq_id] using hself
    exact hCE_on.congr (by
      intro y hy
      simp [modelOpenFormCoeffExtension, hy, hcoeff_eq ⟨y, hy⟩])
  · intro y hy
    exact (hne ⟨⟨y, hy⟩⟩).elim

/--
%%handwave
name:
  Exterior derivative on an open set in the model space
statement:
  On an open subset of a finite-dimensional real normed vector space, the
  de Rham differential is computed by the model-space exterior derivative of
  the ambient coefficient field.
proof:
  In the identity chart of the open subset, the coordinate representative of
  a form is its ambient coefficient field.  The coordinate formula for the
  exterior derivative then gives the result.
-/
theorem deRhamDifferential_modelOpen_toFun
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n)
    (x : U) :
    ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n omega).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) =
    extDerivWithin
      (modelOpenFormCoeffExtension (E := E) U n
        (fun y ↦ smoothFormModelCoeff (E := E) U n omega y))
      (U : Set E) (x : E) := by
  let e : OpenPartialHomeomorph U E := chartAt E x
  let y : E := (x : E)
  have he : e ∈ atlas E U := by
    simp [e]
  have hy : y ∈ (e.extend 𝓘(ℝ, E)).target := by
    simp [e, y, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_def]
  have htarget : (e.extend 𝓘(ℝ, E)).target = (U : Set E) := by
    ext z
    simp [e, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_def]
  have htarget_chart : (chartAt E x).target = (U : Set E) := by
    ext z
    simp [TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_def]
  have hcoord :
      EqOn
        (coordinateExpression (I := 𝓘(ℝ, E)) (F := ℝ) (n := n) omega.toFun e)
        (modelOpenFormCoeffExtension (E := E) U n
          (fun z ↦ smoothFormModelCoeff (E := E) U n omega z))
        (U : Set E) := by
    intro z hz
    have hself :=
      coordinateExpression_chartAt_self (I := 𝓘(ℝ, E)) (F := ℝ) (n := n)
        omega.toFun ⟨z, hz⟩
    simpa [e, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
      extChartAt_model_space_eq_id, smoothFormModelCoeff,
      modelOpenFormCoeffExtension, hz] using hself
  have hd_coord :
      coordinateExpression (I := 𝓘(ℝ, E)) (F := ℝ) (n := n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n omega).toFun e y =
        extDerivWithin
          (coordinateExpression (I := 𝓘(ℝ, E)) (F := ℝ) (n := n) omega.toFun e)
          (e.extend 𝓘(ℝ, E)).target y := by
    simpa [deRhamDifferential] using
      coordinateExpression_exteriorDerivativePoint
        (I := 𝓘(ℝ, E)) (r := ∞) omega he hy
  have hd_self :=
    coordinateExpression_chartAt_self (I := 𝓘(ℝ, E)) (F := ℝ) (n := n + 1)
      (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n omega).toFun x
  have hd_ext :
      ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n omega).toFun x :
        E [⋀^Fin (n + 1)]→L[ℝ] ℝ) =
      extDerivWithin
        (coordinateExpression (I := 𝓘(ℝ, E)) (F := ℝ) (n := n) omega.toFun e)
        (U : Set E) (x : E) := by
    simpa [e, y, htarget, htarget_chart] using hd_self.symm.trans hd_coord
  rw [hd_ext]
  exact extDerivWithin_congr' hcoord x.2

/--
%%handwave
name:
  Poincare homotopy integrand
statement:
  For a smooth \((n+1)\)-form \(\omega\), the straight-line homotopy produces
  at each \(x\in U\) and time \(t\) an \(n\)-form by inserting the radial
  vector \(x-x_0\) and pulling the remaining tangent vectors through the
  derivative of \(H_t\).
proof:
  This is the pointwise formula
  \[
    \iota_{x-x_0}(H_t^\*\omega)_x(v_1,\ldots,v_n)
    = \omega_{H_t(x)}(x-x_0,tv_1,\ldots,tv_n).
  \]
-/
def convexOpenPoincareHomotopyIntegrand
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (t : ℝ) :
    E [⋀^Fin n]→L[ℝ] ℝ :=
  let τ : Set.Icc (0 : ℝ) 1 := Set.projIcc (0 : ℝ) 1 zero_le_one t
  let y : U := convexOpenStraightLineHomotopy (E := E) U hconvex x₀ τ x
  let radial : E := (x : E) - (x₀ : E)
  let tangentScale : E →L[ℝ] E :=
    (τ : ℝ) • ContinuousLinearMap.id ℝ E
  (((omega.toFun y : E [⋀^Fin (n + 1)]→L[ℝ] ℝ).curryLeft radial).compContinuousLinearMap
    tangentScale)

/--
%%handwave
name:
  Additivity of the Poincare homotopy integrand
statement:
  At each time and point, the straight-line homotopy integrand is additive in
  the input form.
proof:
  Evaluation of forms, insertion of the radial vector, and precomposition by
  the derivative of the homotopy are all linear operations.
-/
theorem convexOpenPoincareHomotopyIntegrand_add
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega eta : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (t : ℝ) :
    convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n (omega + eta) x t =
      convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t +
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n eta x t := by
  ext v
  simp only [convexOpenPoincareHomotopyIntegrand,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.add_apply]
  rfl

/--
%%handwave
name:
  Homogeneity of the Poincare homotopy integrand
statement:
  At each time and point, the straight-line homotopy integrand is homogeneous
  in the input form.
proof:
  Evaluation of forms, insertion of the radial vector, and precomposition by
  the derivative of the homotopy are all linear operations.
-/
theorem convexOpenPoincareHomotopyIntegrand_smul
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ) (c : ℝ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (t : ℝ) :
    convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n (c • omega) x t =
      c • convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t := by
  ext v
  simp only [convexOpenPoincareHomotopyIntegrand,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.smul_apply]
  rfl

/--
%%handwave
name:
  Pointwise Poincare homotopy operator
statement:
  The pointwise value of the Poincare homotopy operator is the integral from
  \(0\) to \(1\) of the straight-line homotopy integrand.
proof:
  This is the definition \(K\omega=\int_0^1
  \iota_{x-x_0}(H_t^\*\omega)\,dt\).
-/
def convexOpenPoincareHomotopyPoint
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    E [⋀^Fin n]→L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1,
    convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t

/-- Extend the Poincare homotopy integrand by zero outside the open set in the base variable. -/
def convexOpenPoincareHomotopyIntegrandExtension
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (p : E × ℝ) :
    E [⋀^Fin n]→L[ℝ] ℝ :=
  letI : Decidable (p.1 ∈ (U : Set E)) := Classical.propDecidable _
  if hx : p.1 ∈ (U : Set E) then
    convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega
      ⟨p.1, hx⟩ p.2
  else 0

/--
%%handwave
name:
  Continuity of the Poincare homotopy integrand in time
statement:
  For a smooth form, the straight-line homotopy integrand depends continuously
  on the time parameter.
proof:
  The clamped time parameter and the straight-line homotopy are continuous;
  the form is a continuous alternating covector field; and insertion of the
  radial vector together with precomposition by the scaled identity is
  continuous.
-/
theorem continuous_convexOpenPoincareHomotopyIntegrand
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    Continuous
      (fun t : ℝ ↦
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t) := by
  let τ : ℝ → Set.Icc (0 : ℝ) 1 :=
    fun t ↦ Set.projIcc (0 : ℝ) 1 zero_le_one t
  let y : ℝ → U :=
    fun t ↦ convexOpenStraightLineHomotopy (E := E) U hconvex x₀ (τ t) x
  let radial : E := (x : E) - (x₀ : E)
  let tangentScale : ℝ → E →L[ℝ] E :=
    fun t ↦ (τ t : ℝ) • ContinuousLinearMap.id ℝ E
  have hτ : Continuous τ :=
    continuous_projIcc
  have hτ_coe : Continuous (fun t : ℝ ↦ (τ t : ℝ)) :=
    continuous_subtype_val.comp hτ
  have hy : Continuous y := by
    change Continuous
      (fun t : ℝ ↦
        (⟨AffineMap.lineMap (x₀ : E) (x : E) (τ t : ℝ),
          convexOpen_lineMap_mem (E := E) U hconvex x₀ x (τ t)⟩ : U))
    refine Continuous.subtype_mk ?_ ?_
    have hline :
        Continuous
          (fun t : ℝ ↦
            (1 - (τ t : ℝ)) • (x₀ : E) + (τ t : ℝ) • (x : E)) :=
      (continuous_const.sub hτ_coe).smul continuous_const |>.add
        (hτ_coe.smul continuous_const)
    simpa [y, convexOpenStraightLineHomotopy, AffineMap.lineMap_apply_module]
      using hline
  have hform :
      Continuous
        (fun t : ℝ ↦
          smoothFormModelCoeff (E := E) U (n + 1) omega (y t)) :=
    (continuous_smoothForm_toFun_modelOpen (E := E) U (n + 1) omega).comp hy
  let curryOp :
      (E [⋀^Fin (n + 1)]→L[ℝ] ℝ) →L[ℝ]
        E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℝ :=
    (ContinuousAlternatingMap.curryLeftLI
      (𝕜 := ℝ) (E := E) (F := ℝ) (n := n)).toContinuousLinearMap
  have hcurry :
      Continuous
        (fun t : ℝ ↦
          (curryOp (smoothFormModelCoeff (E := E) U (n + 1) omega (y t))) radial) :=
    (curryOp.continuous.comp hform).clm_apply continuous_const
  have hscale : Continuous tangentScale := by
    exact hτ_coe.smul continuous_const
  have hcompCLM :
      Continuous
        (fun t : ℝ ↦
          ContinuousAlternatingMap.compContinuousLinearMapCLM
            (𝕜 := ℝ) (ι := Fin n) (E := E) (E' := E) (F := ℝ)
            (tangentScale t)) :=
    ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp hscale
  have hcomp :
      Continuous
        (fun t : ℝ ↦
          (ContinuousAlternatingMap.compContinuousLinearMapCLM
            (𝕜 := ℝ) (ι := Fin n) (E := E) (E' := E) (F := ℝ)
            (tangentScale t))
            ((curryOp (smoothFormModelCoeff (E := E) U (n + 1) omega (y t))) radial)) :=
    hcompCLM.clm_apply hcurry
  simpa only [convexOpenPoincareHomotopyIntegrand, smoothFormModelCoeff, τ, y, radial,
    tangentScale, curryOp, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.curryLeftLI_apply]
    using hcomp

/--
%%handwave
name:
  Interval integrability of the Poincare homotopy integrand
statement:
  For a smooth form, the straight-line homotopy integrand is integrable in
  time on the compact interval \([0,1]\).
proof:
  The integrand depends continuously on time: the straight-line homotopy is
  smooth, the form is smooth, and insertion/precomposition are continuous
  multilinear operations.  A continuous function on a compact interval is
  interval integrable.
-/
theorem intervalIntegrable_convexOpenPoincareHomotopyIntegrand
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    IntervalIntegrable
      (fun t : ℝ ↦
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  letI : MeasureTheory.IsLocallyFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    Real.locallyFinite_volume
  exact
    (continuous_convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x).intervalIntegrable
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (0 : ℝ) 1

/--
%%handwave
name:
  Interval integrability after evaluating the Poincare integrand
statement:
  After evaluating the straight-line homotopy integrand on a fixed tangent
  tuple, the resulting real-valued function of time is integrable on
  \([0,1]\).
proof:
  The alternating-covector-valued integrand is continuous in time, and
  evaluation on a fixed tangent tuple is continuous linear.
-/
theorem intervalIntegrable_convexOpenPoincareHomotopyIntegrand_apply
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin n → E) :
    IntervalIntegrable
      (fun t : ℝ ↦
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t v)
      MeasureTheory.volume (0 : ℝ) 1 := by
  let eval :
      (E [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousAlternatingMap.apply ℝ E ℝ v
  have hcont :
      Continuous
        (fun t : ℝ ↦
          convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t v) := by
    simpa [eval] using
      eval.continuous.comp
        (continuous_convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x)
  letI : MeasureTheory.IsLocallyFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    Real.locallyFinite_volume
  exact
    hcont.intervalIntegrable
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (0 : ℝ) 1

/--
%%handwave
name:
  Joint smoothness of the Poincare homotopy integrand
statement:
  The straight-line homotopy integrand is smooth as a function of the base
  point and the time parameter on \(U\times[0,1]\), after extending it
  arbitrarily away from \(U\) in the base variable.
proof:
  On \(U\times[0,1]\), the clamped time variable is just \(t\).  The formula is
  built from the smooth coefficient field of \(\omega\), the smooth
  straight-line map \((x,t)\mapsto (1-t)x_0+tx\), the smooth radial vector
  \(x-x_0\), scalar multiplication by \(t\), currying, and smooth pullback of
  alternating forms by linear maps.
-/
theorem contDiffOn_convexOpenPoincareHomotopyIntegrand
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    ContDiffOn ℝ ∞
      (convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega)
      ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1) := by
  let s : Set (E × ℝ) := (U : Set E) ×ˢ Set.Icc (0 : ℝ) 1
  let line : E × ℝ → E :=
    fun p ↦ (1 - p.2) • (x₀ : E) + p.2 • p.1
  let coeff : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E) U (n + 1)
      (fun x ↦ smoothFormModelCoeff (E := E) U (n + 1) omega x)
  let radial : E × ℝ → E := fun p ↦ p.1 - (x₀ : E)
  let tangentScale : E × ℝ → E →L[ℝ] E :=
    fun p ↦ p.2 • ContinuousLinearMap.id ℝ E
  let curryOp :
      (E [⋀^Fin (n + 1)]→L[ℝ] ℝ) →L[ℝ]
        E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℝ :=
    (ContinuousAlternatingMap.curryLeftLI
      (𝕜 := ℝ) (E := E) (F := ℝ) (n := n)).toContinuousLinearMap
  let smoothExpr : E × ℝ → E [⋀^Fin n]→L[ℝ] ℝ :=
    fun p ↦
      ((curryOp (coeff (line p))) (radial p)).compContinuousLinearMap
        (tangentScale p)
  have hline :
      ContDiffOn ℝ ∞ line s := by
    have ht : ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ p.2) s :=
      contDiffOn_snd
    have hx : ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ p.1) s :=
      contDiffOn_fst
    exact
      ((contDiffOn_const.sub ht).smul contDiffOn_const).add
        (ht.smul hx)
  have hline_mem : MapsTo line s (U : Set E) := by
    intro p hp
    simpa [line, AffineMap.lineMap_apply_module] using
      convexOpen_lineMap_mem (E := E) U hconvex x₀ ⟨p.1, hp.1⟩
        ⟨p.2, hp.2⟩
  have hcoeff :
      ContDiffOn ℝ ∞ coeff (U : Set E) :=
    contDiffOn_smoothFormModelCoeff_modelOpen (E := E) U (n + 1) omega
  have hform :
      ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ coeff (line p)) s :=
    hcoeff.comp hline hline_mem
  have hradial :
      ContDiffOn ℝ ∞ radial s :=
    contDiffOn_fst.sub contDiffOn_const
  have hscale :
      ContDiffOn ℝ ∞ tangentScale s := by
    have ht : ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ p.2) s :=
      contDiffOn_snd
    exact ht.smul contDiffOn_const
  have hcurryOp :
      ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ curryOp (coeff (line p))) s := by
    rw [contDiffOn_clm_apply]
    intro v
    let curryEval :
        (E [⋀^Fin (n + 1)]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin n]→L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ (E [⋀^Fin n]→L[ℝ] ℝ) v).comp curryOp
    simpa [curryEval, Function.comp_def] using hform.continuousLinearMap_comp curryEval
  have hcurry :
      ContDiffOn ℝ ∞
        (fun p : E × ℝ ↦ (curryOp (coeff (line p))) (radial p)) s :=
    hcurryOp.clm_apply hradial
  have hsmooth :
      ContDiffOn ℝ ∞ smoothExpr s := by
    simpa [smoothExpr] using
      contDiffOn_continuousAlternatingMap_compContinuousLinearMap
        (𝕜 := ℝ) (ι := Fin n) (B := E) (D := E) (C := ℝ)
        hcurry hscale
  refine hsmooth.congr ?_
  intro p hp
  have hpU : p.1 ∈ (U : Set E) := hp.1
  have hpI : p.2 ∈ Set.Icc (0 : ℝ) 1 := hp.2
  have hline_eq :
      line p =
        (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
          (Set.projIcc (0 : ℝ) 1 zero_le_one p.2) ⟨p.1, hpU⟩ : E) := by
    simp [line, convexOpenStraightLineHomotopy, AffineMap.lineMap_apply_module,
      Set.projIcc_of_mem zero_le_one hpI]
  have hcoeff_eq :
      coeff (line p) =
        smoothFormModelCoeff (E := E) U (n + 1) omega
          (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
            (Set.projIcc (0 : ℝ) 1 zero_le_one p.2) ⟨p.1, hpU⟩) := by
    rw [hline_eq]
    simp [coeff, modelOpenFormCoeffExtension]
  have hτ : ((Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : Set.Icc (0 : ℝ) 1) : ℝ) =
      p.2 := by
    have hproj :
        Set.projIcc (0 : ℝ) 1 zero_le_one p.2 = ⟨p.2, hpI⟩ :=
      Set.projIcc_of_mem zero_le_one hpI
    exact congrArg Subtype.val hproj
  simp only [convexOpenPoincareHomotopyIntegrandExtension, hpU, dite_true,
    convexOpenPoincareHomotopyIntegrand, smoothExpr, hcoeff_eq, radial, tangentScale,
    curryOp, smoothFormModelCoeff, hτ, LinearIsometry.coe_toContinuousLinearMap,
    ContinuousAlternatingMap.curryLeftLI_apply]
  congr 2

/--
%%handwave
name:
  Smoothness from a smooth derivative field
statement:
  On a set with unique derivatives, a function whose within-derivative exists
  everywhere and is a smooth field of continuous linear maps is smooth.
proof:
  Use the recursive characterization of \(C^\infty\) maps by their
  within-derivatives.  The given derivative identifies the canonical
  within-derivative with the smooth field.
-/
theorem contDiffOn_of_hasFDerivWithinAt_of_contDiffOn_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : UniqueDiffOn ℝ s)
    {g : E → F} {g' : E → E →L[ℝ] F}
    (hg' : ContDiffOn ℝ ∞ g' s)
    (hg : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x) :
    ContDiffOn ℝ ∞ g s := by
  rw [contDiffOn_infty_iff_fderivWithin hs]
  refine ⟨fun x hx ↦ (hg x hx).differentiableWithinAt, ?_⟩
  exact hg'.congr fun x hx ↦ (hg x hx).fderivWithin (hs x hx)

/--
%%handwave
name:
  Dominated differentiation gives a within-derivative for interval integrals
statement:
  If a parameter-dependent Banach-valued integrand is differentiable in the
  parameter on a neighborhood of \(x\), the derivative is dominated by an
  integrable bound, and the usual measurability and integrability hypotheses
  hold, then the interval integral has within-derivative equal to the integral
  of the parameter derivative.
proof:
  Apply the standard dominated differentiation theorem for Bochner interval
  integrals, then restrict the resulting derivative to the chosen set.
-/
theorem hasFDerivWithinAt_intervalIntegral_of_dominated_fderiv_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s t : Set E} {a b : ℝ} {f : E → ℝ → F}
    {f' : E → ℝ → E →L[ℝ] F} {bound : ℝ → ℝ} {x : E}
    (ht : t ∈ 𝓝 x)
    (hF_meas :
      ∀ᶠ y in 𝓝 x,
        MeasureTheory.AEStronglyMeasurable (f y) (MeasureTheory.volume.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (f x) MeasureTheory.volume a b)
    (hF'_meas :
      MeasureTheory.AEStronglyMeasurable (f' x) (MeasureTheory.volume.restrict (Ι a b)))
    (h_bound :
      ∀ᵐ r ∂MeasureTheory.volume, r ∈ Ι a b →
        ∀ y ∈ t, ‖f' y r‖ ≤ bound r)
    (h_bound_int : IntervalIntegrable bound MeasureTheory.volume a b)
    (h_diff :
      ∀ᵐ r ∂MeasureTheory.volume, r ∈ Ι a b →
        ∀ y ∈ t, HasFDerivAt (fun z : E ↦ f z r) (f' y r) y) :
    HasFDerivWithinAt
      (fun y : E ↦ ∫ r in a..b, f y r)
      (∫ r in a..b, f' x r)
      s x := by
  exact
    (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := MeasureTheory.volume) (s := t) (x₀ := x)
      (F := f) (F' := f') (bound := bound)
      ht hF_meas hF_int hF'_meas h_bound h_bound_int h_diff).hasFDerivWithinAt

/--
%%handwave
name:
  Continuity of Banach-valued time slices of a product-continuous integrand
statement:
  If a Banach-valued function is continuous on \(s\times[a,b]\), then each
  time slice \(t\mapsto f(y,t)\), with \(y\in s\), is continuous on
  \([a,b]\).
proof:
  Compose the continuous product map with \(t\mapsto (y,t)\).
-/
theorem continuousOn_time_slice_of_contDiffOn_prod_Icc_zero_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (_hs : IsOpen s) {a b : ℝ}
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ 0 f (s ×ˢ Set.Icc a b))
    {y : E} (hy : y ∈ s) :
    ContinuousOn (fun t : ℝ ↦ f (y, t)) (Set.Icc a b) := by
  rw [contDiffOn_zero] at hf
  exact hf.comp (by fun_prop) (fun t ht ↦ ⟨hy, ht⟩)

/--
%%handwave
name:
  Compact-neighborhood uniform bound for product-continuous integrands
statement:
  If a Banach-valued function is continuous on \(s\times[a,b]\), with \(s\)
  open, then each point of \(s\) has a compact neighborhood contained in \(s\)
  on which the integrand is bounded uniformly in \(y\) and \(t\in[a,b]\).
proof:
  Choose a closed ball around the point contained in \(s\).  The product of
  this ball with \([a,b]\) is compact, and the norm of the integrand is
  continuous on it, hence bounded above.
-/
theorem intervalIntegral_uniform_bound_on_nhds_of_contDiffOn_prod_Icc_zero_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ 0 f (s ×ˢ Set.Icc a b)) :
    ∀ x ∈ s,
      ∃ u : Set E,
        u ∈ 𝓝 x ∧ u ⊆ s ∧
          ∃ bound : ℝ → ℝ,
            IntervalIntegrable bound MeasureTheory.volume a b ∧
              (∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι a b →
                ∀ y ∈ u, ‖f (y, t)‖ ≤ bound t) := by
  intro x hx
  obtain ⟨ε, hε_pos, hε_subset⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  let r : ℝ := ε / 2
  have hr_pos : 0 < r := half_pos hε_pos
  have hclosed_subset : Metric.closedBall x r ⊆ s := by
    have hr_lt : r < ε := by
      dsimp [r]
      linarith
    exact (Metric.closedBall_subset_ball hr_lt).trans hε_subset
  have hproper : ProperSpace E := FiniteDimensional.proper_real E
  let K : Set (E × ℝ) := Metric.closedBall x r ×ˢ Set.Icc a b
  have hK_comp : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall x r).prod isCompact_Icc
  have hK_subset : K ⊆ s ×ˢ Set.Icc a b := by
    intro p hp
    exact ⟨hclosed_subset hp.1, hp.2⟩
  have hf_cont : ContinuousOn f K := by
    rw [contDiffOn_zero] at hf
    exact hf.mono hK_subset
  obtain ⟨M, hM⟩ := hK_comp.bddAbove_image hf_cont.norm
  refine
    ⟨Metric.closedBall x r, Metric.closedBall_mem_nhds x hr_pos,
      hclosed_subset, fun _ : ℝ ↦ M, intervalIntegrable_const, ?_⟩
  filter_upwards with t ht
  intro y hy
  have htIcc : t ∈ Set.Icc a b := by
    have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    simpa [Set.uIcc_of_le hab] using ht'
  exact hM (Set.mem_image_of_mem (fun p : E × ℝ ↦ ‖f p‖) ⟨hy, htIcc⟩)

/--
%%handwave
name:
  First-order smoothness gives a continuous parameter-derivative field
statement:
  If a Banach-valued function is \(C^1\) on \(s\times[a,b]\), with \(s\)
  open, then the field of derivatives in the \(s\)-parameter direction is
  continuous on \(s\times[a,b]\).
proof:
  Apply the finite-order within-derivative rule to the curried map
  \(q\mapsto(y\mapsto f(y,q_2))\) and the projection \(q\mapsto q_1\).
-/
theorem contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc_one_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (_hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ 1 f (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ 0
      (fun p : E × ℝ ↦ fderivWithin ℝ (fun y : E ↦ f (y, p.2)) s p.1)
      (s ×ˢ Set.Icc a b) := by
  intro p hp
  have hf_uncurry :
      ContDiffWithinAt ℝ 1
        (Function.uncurry
          (fun q : E × ℝ ↦ fun y : E ↦ f (y, q.2)))
        ((s ×ˢ Set.Icc a b) ×ˢ s) (p, p.1) := by
    have hmap :
        ContDiffWithinAt ℝ 1
          (fun q : (E × ℝ) × E ↦ (q.2, q.1.2))
          ((s ×ˢ Set.Icc a b) ×ˢ s) (p, p.1) := by
      fun_prop
    have hsubset :
        MapsTo (fun q : (E × ℝ) × E ↦ (q.2, q.1.2))
          ((s ×ˢ Set.Icc a b) ×ˢ s) (s ×ˢ Set.Icc a b) := by
      intro q hq
      exact ⟨hq.2, hq.1.2⟩
    simpa [Function.uncurry] using
      (hf.contDiffWithinAt ⟨hp.1, hp.2⟩).comp (p, p.1) hmap hsubset
  have hproj :
      ContDiffWithinAt ℝ 0 (fun q : E × ℝ ↦ q.1)
        (s ×ˢ Set.Icc a b) p := by
    fun_prop
  have hsubset :
      (s ×ˢ Set.Icc a b) ⊆ (fun q : E × ℝ ↦ q.1) ⁻¹' s := by
    intro q hq
    exact hq.1
  simpa [Function.uncurry] using
    hf_uncurry.fderivWithin hproj hs.uniqueDiffOn (by simp)
      hp hsubset

/--
%%handwave
name:
  First-order dominated derivative data from smoothness on a compact interval
statement:
  If a Banach-valued function is \(C^1\) on \(s\times[a,b]\), with \(s\)
  open, then near each point of \(s\) its parameter derivative data satisfy
  the hypotheses needed for differentiating under the interval integral.
proof:
  This is the compact-neighborhood argument: continuity of the integrand and
  the first derivative on the compact product gives measurability,
  integrability, pointwise differentiability, and a uniform derivative bound.
-/
theorem intervalIntegral_dominated_fderiv_data_of_contDiffOn_prod_Icc_one
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ 1 f (s ×ˢ Set.Icc a b)) :
    ∀ x ∈ s,
      ∃ u : Set E,
        u ∈ 𝓝 x ∧ u ⊆ s ∧
          (∀ᶠ y in 𝓝 x,
            MeasureTheory.AEStronglyMeasurable (fun r : ℝ ↦ f (y, r))
              (MeasureTheory.volume.restrict (Ι a b))) ∧
          IntervalIntegrable (fun r : ℝ ↦ f (x, r)) MeasureTheory.volume a b ∧
          MeasureTheory.AEStronglyMeasurable
            (fun r : ℝ ↦ fderivWithin ℝ (fun y : E ↦ f (y, r)) s x)
            (MeasureTheory.volume.restrict (Ι a b)) ∧
          ∃ bound : ℝ → ℝ,
            IntervalIntegrable bound MeasureTheory.volume a b ∧
              (∀ᵐ r ∂MeasureTheory.volume, r ∈ Ι a b →
                ∀ y ∈ u,
                  ‖fderivWithin ℝ (fun z : E ↦ f (z, r)) s y‖ ≤ bound r) ∧
              (∀ᵐ r ∂MeasureTheory.volume, r ∈ Ι a b →
                ∀ y ∈ u,
                  HasFDerivAt (fun z : E ↦ f (z, r))
                    (fderivWithin ℝ (fun z : E ↦ f (z, r)) s y) y) := by
  intro x hx
  have hf0 : ContDiffOn ℝ 0 f (s ×ˢ Set.Icc a b) := hf.of_le (by simp)
  have hdf :
      ContDiffOn ℝ 0
        (fun p : E × ℝ ↦ fderivWithin ℝ (fun y : E ↦ f (y, p.2)) s p.1)
        (s ×ˢ Set.Icc a b) :=
    contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc_one_zero
      (E := E) (F := F) hs hab hf
  rcases intervalIntegral_uniform_bound_on_nhds_of_contDiffOn_prod_Icc_zero_apply
      (E := E) (F := E →L[ℝ] F) hs hab hdf x hx with
    ⟨u, hu_nhds, hu_subset, bound, hbound_int, hbound⟩
  refine ⟨u, hu_nhds, hu_subset, ?_, ?_, ?_, bound, hbound_int, hbound, ?_⟩
  · filter_upwards [hu_nhds] with y hy
    have hy_s : y ∈ s := hu_subset hy
    have hslice :
        ContinuousOn (fun t : ℝ ↦ f (y, t)) (Set.Icc a b) :=
      continuousOn_time_slice_of_contDiffOn_prod_Icc_zero_apply
        (E := E) (F := F) hs hf0 hy_s
    have hsubset : Ι a b ⊆ Set.Icc a b := by
      intro t ht
      have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
      simpa [Set.uIcc_of_le hab] using ht'
    exact
      hslice.aestronglyMeasurable_of_subset_isCompact
        isCompact_Icc measurableSet_uIoc hsubset
  · have hslice :
        ContinuousOn (fun t : ℝ ↦ f (x, t)) (Set.Icc a b) :=
      continuousOn_time_slice_of_contDiffOn_prod_Icc_zero_apply
        (E := E) (F := F) hs hf0 hx
    exact hslice.intervalIntegrable_of_Icc hab
  · have hslice :
        ContinuousOn
          (fun t : ℝ ↦ fderivWithin ℝ (fun y : E ↦ f (y, t)) s x)
          (Set.Icc a b) :=
      continuousOn_time_slice_of_contDiffOn_prod_Icc_zero_apply
        (E := E) (F := E →L[ℝ] F) hs hdf hx
    have hsubset : Ι a b ⊆ Set.Icc a b := by
      intro t ht
      have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
      simpa [Set.uIcc_of_le hab] using ht'
    exact
      hslice.aestronglyMeasurable_of_subset_isCompact
        isCompact_Icc measurableSet_uIoc hsubset
  · filter_upwards with t ht
    intro y hy
    have htIcc : t ∈ Set.Icc a b := by
      have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
      simpa [Set.uIcc_of_le hab] using ht'
    have hy_s : y ∈ s := hu_subset hy
    have hslice :
        ContDiffOn ℝ 1 (fun z : E ↦ f (z, t)) s := by
      exact hf.comp (by fun_prop) (fun z hz ↦ ⟨hz, htIcc⟩)
    exact
      ((hslice.differentiableOn (by simp) y hy_s).hasFDerivWithinAt).hasFDerivAt
        (hs.mem_nhds hy_s)

/--
%%handwave
name:
  Dominated derivative data from smoothness on a compact parameter interval
statement:
  If a Banach-valued function is smooth on \(s\times[a,b]\), with \(s\) open,
  then near each point of \(s\) its parameter derivative data satisfy the
  measurability, integrability, differentiability, and domination hypotheses
  needed for differentiating under the interval integral.
proof:
  Apply the first-order compact-neighborhood statement, since smoothness
  implies \(C^1\) regularity.
-/
theorem intervalIntegral_dominated_fderiv_data_of_contDiffOn_prod_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ Set.Icc a b)) :
    ∀ x ∈ s,
      ∃ u : Set E,
        u ∈ 𝓝 x ∧ u ⊆ s ∧
          (∀ᶠ y in 𝓝 x,
            MeasureTheory.AEStronglyMeasurable (fun r : ℝ ↦ f (y, r))
              (MeasureTheory.volume.restrict (Ι a b))) ∧
          IntervalIntegrable (fun r : ℝ ↦ f (x, r)) MeasureTheory.volume a b ∧
          MeasureTheory.AEStronglyMeasurable
            (fun r : ℝ ↦ fderivWithin ℝ (fun y : E ↦ f (y, r)) s x)
            (MeasureTheory.volume.restrict (Ι a b)) ∧
          ∃ bound : ℝ → ℝ,
            IntervalIntegrable bound MeasureTheory.volume a b ∧
              (∀ᵐ r ∂MeasureTheory.volume, r ∈ Ι a b →
                ∀ y ∈ u,
                  ‖fderivWithin ℝ (fun z : E ↦ f (z, r)) s y‖ ≤ bound r) ∧
              (∀ᵐ r ∂MeasureTheory.volume, r ∈ Ι a b →
                ∀ y ∈ u,
                  HasFDerivAt (fun z : E ↦ f (z, r))
                    (fderivWithin ℝ (fun z : E ↦ f (z, r)) s y) y) := by
  exact
    intervalIntegral_dominated_fderiv_data_of_contDiffOn_prod_Icc_one
      (E := E) (F := F) hs hab (hf.of_le (by simp))

/--
%%handwave
name:
  Derivative of a compact-interval parameter integral
statement:
  If a Banach-valued function is smooth in the parameter and time variables on
  \(s\times[a,b]\), with \(s\) open, then the within-derivative of its
  parameter integral is the integral of the parameter within-derivative.
proof:
  Work near the chosen parameter in a compact neighborhood contained in \(s\).
  The usual dominated differentiation theorem for Bochner integrals applies
  because the derivative field is continuous on the compact product of that
  neighborhood with \([a,b]\), hence is uniformly bounded there.
-/
theorem hasFDerivWithinAt_intervalIntegral_of_contDiffOn_prod_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ Set.Icc a b)) :
    ∀ x ∈ s,
      HasFDerivWithinAt
        (fun y : E ↦ ∫ t in a..b, f (y, t))
        (∫ t in a..b, fderivWithin ℝ (fun y : E ↦ f (y, t)) s x)
        s x := by
  intro x hx
  rcases intervalIntegral_dominated_fderiv_data_of_contDiffOn_prod_Icc
      (E := E) (F := F) hs hab hf x hx with
    ⟨u, hu_nhds, _hu_subset, hF_meas, hF_int, hF'_meas, bound,
      hbound_int, hbound, hdiff⟩
  exact
    hasFDerivWithinAt_intervalIntegral_of_dominated_fderiv_le
      (E := E) (F := F) (s := s) (t := u)
      (f := fun y r ↦ f (y, r))
      (f' := fun y r ↦ fderivWithin ℝ (fun z : E ↦ f (z, r)) s y)
      (bound := bound) (x := x)
      hu_nhds hF_meas hF_int hF'_meas hbound hbound_int hdiff

/--
%%handwave
name:
  First-order derivative of a compact-interval parameter integral
statement:
  If a Banach-valued function is \(C^1\) in the parameter and time variables
  on \(s\times[a,b]\), with \(s\) open, then the within-derivative of its
  parameter integral is the integral of the parameter within-derivative.
proof:
  Apply the dominated differentiation theorem using the first-order compact
  derivative data.
-/
theorem hasFDerivWithinAt_intervalIntegral_of_contDiffOn_prod_Icc_one
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ 1 f (s ×ˢ Set.Icc a b)) :
    ∀ x ∈ s,
      HasFDerivWithinAt
        (fun y : E ↦ ∫ t in a..b, f (y, t))
        (∫ t in a..b, fderivWithin ℝ (fun y : E ↦ f (y, t)) s x)
        s x := by
  intro x hx
  rcases intervalIntegral_dominated_fderiv_data_of_contDiffOn_prod_Icc_one
      (E := E) (F := F) hs hab hf x hx with
    ⟨u, hu_nhds, _hu_subset, hF_meas, hF_int, hF'_meas, bound,
      hbound_int, hbound, hdiff⟩
  exact
    hasFDerivWithinAt_intervalIntegral_of_dominated_fderiv_le
      (E := E) (F := F) (s := s) (t := u)
      (f := fun y r ↦ f (y, r))
      (f' := fun y r ↦ fderivWithin ℝ (fun z : E ↦ f (z, r)) s y)
      (bound := bound) (x := x)
      hu_nhds hF_meas hF_int hF'_meas hbound hbound_int hdiff

/--
%%handwave
name:
  Finite smoothness of the parameter derivative field
statement:
  If a Banach-valued function is \(C^{k+1}\) in the parameter and time
  variables on \(s\times[a,b]\), with \(s\) open, then its derivative in the
  parameter direction is \(C^k\) on \(s\times[a,b]\).
proof:
  This is the finite-order version of the standard rule that differentiating
  once lowers differentiability by one.  Apply the within-derivative API to
  the curried map.
-/
theorem contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc_nat
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (_hab : a ≤ b)
    (k : ℕ) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ (k + 1) f (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ k
      (fun p : E × ℝ ↦ fderivWithin ℝ (fun y : E ↦ f (y, p.2)) s p.1)
      (s ×ˢ Set.Icc a b) := by
  intro p hp
  have hf_uncurry :
      ContDiffWithinAt ℝ (k + 1)
        (Function.uncurry
          (fun q : E × ℝ ↦ fun y : E ↦ f (y, q.2)))
        ((s ×ˢ Set.Icc a b) ×ˢ s) (p, p.1) := by
    have hmap :
        ContDiffWithinAt ℝ (k + 1)
          (fun q : (E × ℝ) × E ↦ (q.2, q.1.2))
          ((s ×ˢ Set.Icc a b) ×ˢ s) (p, p.1) := by
      fun_prop
    have hsubset :
        MapsTo (fun q : (E × ℝ) × E ↦ (q.2, q.1.2))
          ((s ×ˢ Set.Icc a b) ×ˢ s) (s ×ˢ Set.Icc a b) := by
      intro q hq
      exact ⟨hq.2, hq.1.2⟩
    simpa [Function.uncurry] using
      (hf.contDiffWithinAt ⟨hp.1, hp.2⟩).comp (p, p.1) hmap hsubset
  have hproj :
      ContDiffWithinAt ℝ k (fun q : E × ℝ ↦ q.1)
        (s ×ˢ Set.Icc a b) p := by
    fun_prop
  have hsubset :
      (s ×ˢ Set.Icc a b) ⊆ (fun q : E × ℝ ↦ q.1) ⁻¹' s := by
    intro q hq
    exact hq.1
  simpa [Function.uncurry] using
    hf_uncurry.fderivWithin hproj hs.uniqueDiffOn (by simp)
      hp hsubset

/--
%%handwave
name:
  Joint smoothness of the parameter derivative field
statement:
  If a Banach-valued function is smooth in the parameter and time variables on
  \(s\times[a,b]\), with \(s\) open, then its derivative in the parameter
  direction is also smooth on \(s\times[a,b]\).
proof:
  Use the smoothness of \(f\) on the product and the chain rule for the slice
  maps \(y\mapsto f(y,t)\).  Since \(s\) is open, within-derivatives in the
  parameter direction agree with ordinary derivatives on \(s\).
-/
theorem contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (_hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ ∞
      (fun p : E × ℝ ↦ fderivWithin ℝ (fun y : E ↦ f (y, p.2)) s p.1)
      (s ×ˢ Set.Icc a b) := by
  rw [contDiffOn_infty]
  intro k
  exact
    contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc_nat
      (E := E) (F := F) hs _hab k
      (hf.of_le (by exact_mod_cast le_top))

/--
%%handwave
name:
  Continuity of parameter slices of a product-continuous integrand
statement:
  If a continuous-linear-map-valued function is continuous on
  \(s\times[a,b]\), then for each \(t\in[a,b]\) the parameter slice is
  continuous on \(s\).
proof:
  Compose the continuous product map with \(y\mapsto (y,t)\).
-/
theorem continuousOn_parameter_slice_of_contDiffOn_prod_Icc_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (_hs : IsOpen s) {a b t : ℝ}
    {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ 0 g (s ×ˢ Set.Icc a b))
    (ht : t ∈ Set.Icc a b) :
    ContinuousOn (fun y : E ↦ g (y, t)) s := by
  rw [contDiffOn_zero] at hg
  exact hg.comp (by fun_prop) (fun y hy ↦ ⟨hy, ht⟩)

/--
%%handwave
name:
  Continuity of time slices of a product-continuous integrand
statement:
  If a continuous-linear-map-valued function is continuous on
  \(s\times[a,b]\), then for each \(y\in s\) the time slice is continuous on
  \([a,b]\).
proof:
  Compose the continuous product map with \(t\mapsto (y,t)\).
-/
theorem continuousOn_time_slice_of_contDiffOn_prod_Icc_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (_hs : IsOpen s) {a b : ℝ}
    {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ 0 g (s ×ˢ Set.Icc a b))
    {y : E} (hy : y ∈ s) :
    ContinuousOn (fun t : ℝ ↦ g (y, t)) (Set.Icc a b) := by
  rw [contDiffOn_zero] at hg
  exact hg.comp (by fun_prop) (fun t ht ↦ ⟨hy, ht⟩)

/--
%%handwave
name:
  Uniform compact-interval bound for product-continuous integrands
statement:
  If a continuous-linear-map-valued function is continuous on
  \(s\times[a,b]\), with \(s\) open, then near each point of \(s\) its norm is
  bounded on \([a,b]\) by an integrable function independent of the nearby
  parameter.
proof:
  Choose a compact parameter neighborhood contained in \(s\).  Continuity on
  the compact product gives a finite uniform bound; use the corresponding
  constant function on \([a,b]\).
-/
theorem intervalIntegral_uniform_bound_of_contDiffOn_prod_Icc_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ 0 g (s ×ˢ Set.Icc a b)) :
    ∀ x ∈ s,
      ∃ bound : ℝ → ℝ,
        (∀ᶠ y in 𝓝[s] x,
          ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι a b → ‖g (y, t)‖ ≤ bound t) ∧
        IntervalIntegrable bound MeasureTheory.volume a b := by
  intro x hx
  obtain ⟨ε, hε_pos, hε_subset⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  let r : ℝ := ε / 2
  have hr_pos : 0 < r := half_pos hε_pos
  have hclosed_subset : Metric.closedBall x r ⊆ s := by
    have hr_lt : r < ε := by
      dsimp [r]
      linarith
    exact (Metric.closedBall_subset_ball hr_lt).trans hε_subset
  have hproper : ProperSpace E := FiniteDimensional.proper_real E
  let K : Set (E × ℝ) := Metric.closedBall x r ×ˢ Set.Icc a b
  have hK_comp : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall x r).prod isCompact_Icc
  have hK_subset : K ⊆ s ×ˢ Set.Icc a b := by
    intro p hp
    exact ⟨hclosed_subset hp.1, hp.2⟩
  have hg_cont : ContinuousOn g K := by
    rw [contDiffOn_zero] at hg
    exact hg.mono hK_subset
  obtain ⟨M, hM⟩ := hK_comp.bddAbove_image hg_cont.norm
  refine ⟨fun _ : ℝ ↦ M, ?_, intervalIntegrable_const⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x hr_pos)] with y hy
  filter_upwards with t ht
  have htIcc : t ∈ Set.Icc a b := by
    have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    simpa [Set.uIcc_of_le hab] using ht'
  exact hM (Set.mem_image_of_mem (fun p : E × ℝ ↦ ‖g p‖) ⟨hy, htIcc⟩)

/--
%%handwave
name:
  Dominated continuity data from continuity on a compact interval
statement:
  If a continuous-linear-map-valued function is continuous on
  \(s\times[a,b]\), with \(s\) open, then near each point of \(s\) its slices
  are measurable, uniformly dominated by an integrable bound on \([a,b]\), and
  continuous in the parameter for almost every time.
proof:
  Choose a compact parameter neighborhood contained in \(s\).  Continuity on
  the compact product gives a uniform norm bound, while the slice maps are
  continuous and hence measurable.
-/
theorem intervalIntegral_continuity_data_of_contDiffOn_prod_Icc_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ 0 g (s ×ˢ Set.Icc a b)) :
    ∀ x ∈ s,
      ∃ bound : ℝ → ℝ,
        (∀ᶠ y in 𝓝[s] x,
          MeasureTheory.AEStronglyMeasurable (fun t : ℝ ↦ g (y, t))
            (MeasureTheory.volume.restrict (Ι a b))) ∧
        (∀ᶠ y in 𝓝[s] x,
          ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι a b → ‖g (y, t)‖ ≤ bound t) ∧
        IntervalIntegrable bound MeasureTheory.volume a b ∧
        (∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι a b →
          ContinuousWithinAt (fun y : E ↦ g (y, t)) s x) := by
  intro x hx
  rcases intervalIntegral_uniform_bound_of_contDiffOn_prod_Icc_zero
      (E := E) (F := F) hs hab hg x hx with
    ⟨bound, hbound, hbound_int⟩
  refine ⟨bound, ?_, hbound, hbound_int, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hslice :
        ContinuousOn (fun t : ℝ ↦ g (y, t)) (Set.Icc a b) :=
      continuousOn_time_slice_of_contDiffOn_prod_Icc_zero
        (E := E) (F := F) hs hg hy
    have hsubset : Ι a b ⊆ Set.Icc a b := by
      intro t ht
      have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
      simpa [Set.uIcc_of_le hab] using ht'
    exact
      hslice.aestronglyMeasurable_of_subset_isCompact
        isCompact_Icc measurableSet_uIoc hsubset
  · filter_upwards with t ht
    have htIcc : t ∈ Set.Icc a b := by
      have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
      simpa [Set.uIcc_of_le hab] using ht'
    exact
      (continuousOn_parameter_slice_of_contDiffOn_prod_Icc_zero
        (E := E) (F := F) hs hg htIcc) x hx

/--
%%handwave
name:
  Continuity of continuous-linear-map-valued compact-interval integrals
statement:
  If a continuous-linear-map-valued function is continuous in the parameter
  and time variables on \(s\times[a,b]\), with \(s\) open, then its compact
  interval integral is continuous as a function of the parameter.
proof:
  Use dominated convergence on compact parameter neighborhoods.  Continuity on
  the compact product gives a uniform bound for the integrand.
-/
theorem contDiffOn_zero_intervalIntegral_clm_of_contDiffOn_prod_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ 0 g (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ 0 (fun x : E ↦ ∫ t in a..b, g (x, t)) s := by
  rw [contDiffOn_zero]
  intro x hx
  rcases intervalIntegral_continuity_data_of_contDiffOn_prod_Icc_zero
      (E := E) (F := F) hs hab hg x hx with
    ⟨bound, hmeas, hbound, hbound_int, hcont⟩
  exact
    intervalIntegral.continuousWithinAt_of_dominated_interval
      (μ := MeasureTheory.volume) (F := fun y t ↦ g (y, t))
      (x₀ := x) (s := s) (bound := bound)
      hmeas hbound hbound_int hcont

/--
%%handwave
name:
  Successor step for smoothness of continuous-linear-map-valued integrals
statement:
  Suppose a continuous-linear-map-valued function is \(C^{k+1}\) on
  \(s\times[a,b]\), and suppose the integral of its parameter derivative is
  \(C^k\) on \(s\).  Then the compact-interval integral is \(C^{k+1}\) on
  \(s\).
proof:
  Differentiate under the integral sign.  The recursive characterization of
  \(C^{k+1}\) maps then reduces the claim to the assumed \(C^k\) regularity of
  the derivative integral.
-/
theorem contDiffOn_intervalIntegral_clm_of_contDiffOn_prod_Icc_succ
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    (k : ℕ) {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ (k + 1) g (s ×ˢ Set.Icc a b))
    (hderiv :
      ContDiffOn ℝ k
        (fun x : E ↦ ∫ t in a..b,
          fderivWithin ℝ (fun y : E ↦ g (y, t)) s x)
        s) :
    ContDiffOn ℝ (k + 1) (fun x : E ↦ ∫ t in a..b, g (x, t)) s := by
  change
    ContDiffOn ℝ ((k : ℕ∞) + 1) (fun x : E ↦ ∫ t in a..b, g (x, t)) s
  rw [contDiffOn_succ_iff_fderivWithin hs.uniqueDiffOn]
  have hdiff :
      ∀ x ∈ s,
        HasFDerivWithinAt
          (fun y : E ↦ ∫ t in a..b, g (y, t))
          (∫ t in a..b, fderivWithin ℝ (fun y : E ↦ g (y, t)) s x)
          s x :=
    hasFDerivWithinAt_intervalIntegral_of_contDiffOn_prod_Icc_one
      (E := E) (F := E →L[ℝ] F) hs hab
      (hg.of_le (by simp))
  refine ⟨?_, by simp, ?_⟩
  · intro x hx
    exact (hdiff x hx).differentiableWithinAt
  · exact hderiv.congr fun x hx ↦ (hdiff x hx).fderivWithin (hs.uniqueDiffOn x hx)

/--
%%handwave
name:
  Finite smoothness of continuous-linear-map-valued compact-interval integrals in one universe
statement:
  If a continuous-linear-map-valued function is \(C^k\) in the parameter and
  time variables on \(s\times[a,b]\), with \(s\) open, then its compact
  interval integral is \(C^k\) as a function of the parameter, provided the
  codomains stay in a universe closed under taking continuous linear maps out
  of the model space.
proof:
  Induct on \(k\).  The case \(k=0\) is continuity of a parameter integral of
  a continuous integrand over a compact interval.  For the step, differentiate
  under the integral sign; the derivative is the compact-interval integral of
  the parameter derivative, and the induction hypothesis applies to that
  derivative field.
-/
theorem contDiffOn_intervalIntegral_clm_of_contDiffOn_prod_Icc_nat_sameUniverse
    {F : Type (max v u)} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    (k : ℕ) {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ k g (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ k (fun x : E ↦ ∫ t in a..b, g (x, t)) s := by
  induction k generalizing F with
  | zero =>
      exact
        contDiffOn_zero_intervalIntegral_clm_of_contDiffOn_prod_Icc
          (E := E) (F := F) hs hab hg
  | succ k ih =>
      have hderiv :
          ContDiffOn ℝ k
            (fun p : E × ℝ ↦
              fderivWithin ℝ (fun y : E ↦ g (y, p.2)) s p.1)
            (s ×ˢ Set.Icc a b) :=
        contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc_nat
          (E := E) (F := E →L[ℝ] F) hs hab k hg
      exact
        contDiffOn_intervalIntegral_clm_of_contDiffOn_prod_Icc_succ
          (E := E) (F := F) hs hab k hg
          (ih (F := E →L[ℝ] F) hderiv)

/--
%%handwave
name:
  Finite smoothness of continuous-linear-map-valued compact-interval integrals
statement:
  If a continuous-linear-map-valued function is \(C^k\) in the parameter and
  time variables on \(s\times[a,b]\), with \(s\) open, then its compact
  interval integral is \(C^k\) as a function of the parameter.
proof:
  First prove the statement in a universe stable under replacing a codomain
  \(F\) by \(E\to F\).  The remaining reduction transports the integrand
  through universe-lift continuous linear equivalences.
-/
theorem contDiffOn_intervalIntegral_clm_of_contDiffOn_prod_Icc_nat
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    (k : ℕ) {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ k g (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ k (fun x : E ↦ ∫ t in a..b, g (x, t)) s := by
  let isoF : ULift.{v} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  let pushEquiv : (E →L[ℝ] ULift.{v} F) ≃L[ℝ] E →L[ℝ] F :=
    ContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ E) isoF
  let eg : E × ℝ → E →L[ℝ] ULift.{v} F := fun p ↦ pushEquiv.symm (g p)
  have heg : ContDiffOn ℝ k eg (s ×ˢ Set.Icc a b) := by
    have hconst :
        ContDiffOn ℝ k
          (fun _ : E × ℝ ↦ (isoF.symm : F →L[ℝ] ULift.{v} F))
          (s ×ˢ Set.Icc a b) := by
      fun_prop
    simpa [eg, pushEquiv] using hconst.clm_comp hg
  have hI :
      ContDiffOn ℝ k (fun x : E ↦ ∫ t in a..b, eg (x, t)) s :=
    contDiffOn_intervalIntegral_clm_of_contDiffOn_prod_Icc_nat_sameUniverse
      (E := E) (F := ULift.{v} F) hs hab k heg
  have hpush :
      ContDiffOn ℝ k (fun x : E ↦ pushEquiv (∫ t in a..b, eg (x, t))) s :=
    by
      have hconst :
          ContDiffOn ℝ k
            (fun _ : E ↦ (isoF : ULift.{v} F →L[ℝ] F)) s := by
        fun_prop
      simpa [pushEquiv] using hconst.clm_comp hI
  exact hpush.congr fun x hx ↦ by
    symm
    calc
      pushEquiv (∫ t in a..b, eg (x, t)) =
          ∫ t in a..b, pushEquiv (eg (x, t)) := by
        simp only [intervalIntegral, map_sub]
        change
          pushEquiv
              (∫ t, eg (x, t) ∂MeasureTheory.volume.restrict (Set.Ioc a b)) -
              pushEquiv
                (∫ t, eg (x, t) ∂MeasureTheory.volume.restrict (Set.Ioc b a)) =
            (∫ t, pushEquiv (eg (x, t))
                ∂MeasureTheory.volume.restrict (Set.Ioc a b)) -
              (∫ t, pushEquiv (eg (x, t))
                ∂MeasureTheory.volume.restrict (Set.Ioc b a))
        rw [ContinuousLinearEquiv.integral_comp_comm
            (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
            pushEquiv (fun t : ℝ ↦ eg (x, t)),
          ContinuousLinearEquiv.integral_comp_comm
            (μ := MeasureTheory.volume.restrict (Set.Ioc b a))
            pushEquiv (fun t : ℝ ↦ eg (x, t))]
      _ = ∫ t in a..b, g (x, t) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t _ht
        ext y
        simp [eg, pushEquiv]

/--
%%handwave
name:
  Smoothness of continuous-linear-map-valued compact-interval integrals
statement:
  If a continuous-linear-map-valued function is smooth in the parameter and
  time variables on \(s\times[a,b]\), with \(s\) open, then its compact
  interval integral is smooth as a continuous-linear-map-valued function of
  the parameter.
proof:
  This is the all-orders induction for differentiating compact-interval
  parameter integrals, applied to a Banach space of continuous linear maps.
-/
theorem contDiffOn_intervalIntegral_clm_of_contDiffOn_prod_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {g : E × ℝ → E →L[ℝ] F}
    (hg : ContDiffOn ℝ ∞ g (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ ∞ (fun x : E ↦ ∫ t in a..b, g (x, t)) s := by
  rw [contDiffOn_infty]
  intro k
  exact
    contDiffOn_intervalIntegral_clm_of_contDiffOn_prod_Icc_nat
      (E := E) (F := F) hs hab k (hg.of_le (by exact_mod_cast le_top))

/--
%%handwave
name:
  Smooth derivative field of a compact-interval parameter integral
statement:
  If a Banach-valued function is smooth in the parameter and time variables on
  \(s\times[a,b]\), with \(s\) open, then the integrated parameter
  within-derivative is a smooth field of continuous linear maps on \(s\).
proof:
  The parameter within-derivative is smooth in the parameter and time variables
  on the same product.  Apply the compact-interval parameter-integral argument
  recursively to this derivative field.
-/
theorem contDiffOn_intervalIntegral_fderivWithin_of_contDiffOn_prod_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ ∞
      (fun x : E ↦ ∫ t in a..b, fderivWithin ℝ (fun y : E ↦ f (y, t)) s x)
      s := by
  exact
    contDiffOn_intervalIntegral_clm_of_contDiffOn_prod_Icc
      (E := E) (F := F) hs hab
      (contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc
        (E := E) (F := F) hs hab hf)

/--
%%handwave
name:
  Smoothness of compact-interval parameter integrals
statement:
  If a Banach-valued function is smooth in the parameter and time variables on
  \(s\times[a,b]\), with \(s\) open, then its integral over \(a\le t\le b\)
  is a smooth function of the parameter on \(s\).
proof:
  The derivative of the parameter integral is the integral of the parameter
  derivative, and that integrated derivative field is smooth.  The recursive
  characterization of smooth maps by smooth derivative fields then gives the
  result.
-/
theorem contDiffOn_intervalIntegral_of_contDiffOn_prod_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ Set.Icc a b)) :
    ContDiffOn ℝ ∞ (fun x : E ↦ ∫ t in a..b, f (x, t)) s := by
  exact
    contDiffOn_of_hasFDerivWithinAt_of_contDiffOn_derivative
      (E := E) (F := F) hs.uniqueDiffOn
      (contDiffOn_intervalIntegral_fderivWithin_of_contDiffOn_prod_Icc
        (E := E) (F := F) hs hab hf)
      (hasFDerivWithinAt_intervalIntegral_of_contDiffOn_prod_Icc
        (E := E) (F := F) hs hab hf)

/--
%%handwave
name:
  Local smoothness of compact-interval parameter integrals
statement:
  If a Banach-valued function is smooth in the parameter and time variables on
  \(s\times[a,b]\), with \(s\) open, then near each point of \(s\) its integral
  over \(a\le t\le b\) is smooth in the parameter.
proof:
  Use the global smoothness statement and restrict it to the open neighborhood
  \(s\) itself.
-/
theorem contDiffOn_intervalIntegral_of_contDiffOn_prod_Icc_local
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ Set.Icc a b))
    {x₀ : E} (hx₀ : x₀ ∈ s) :
    ∃ u : Set E,
      IsOpen u ∧ x₀ ∈ u ∧
        ContDiffOn ℝ ∞ (fun x : E ↦ ∫ t in a..b, f (x, t)) (s ∩ u) := by
  refine ⟨s, hs, hx₀, ?_⟩
  exact
    (contDiffOn_intervalIntegral_of_contDiffOn_prod_Icc
      (E := E) (F := F) hs hab hf).mono inter_subset_left

/--
%%handwave
name:
  Smooth coefficient field of the Poincare homotopy integral
statement:
  The pointwise interval integral defining the straight-line homotopy operator
  is a smooth alternating-covector-valued function on the convex open set.
proof:
  Apply smoothness of compact-interval parameter integrals to the jointly
  smooth homotopy integrand on \(U\times[0,1]\).
-/
theorem contDiffOn_convexOpenPoincareHomotopyPoint
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    ContDiffOn ℝ ∞
      (modelOpenFormCoeffExtension (E := E) U n
        (fun x ↦ convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega x))
      (U : Set E) := by
  have hf :
      ContDiffOn ℝ ∞
        (convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega)
        ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1) :=
    contDiffOn_convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega
  have hInt :
      ContDiffOn ℝ ∞
        (fun x : E ↦ ∫ t in (0 : ℝ)..1,
          convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega (x, t))
        (U : Set E) :=
    contDiffOn_intervalIntegral_of_contDiffOn_prod_Icc
      (E := E) (F := E [⋀^Fin n]→L[ℝ] ℝ)
      (s := (U : Set E)) U.2 zero_le_one hf
  exact hInt.congr (by
    intro y hy
    simp [modelOpenFormCoeffExtension, convexOpenPoincareHomotopyPoint,
      convexOpenPoincareHomotopyIntegrandExtension, hy])

/--
%%handwave
name:
  Smooth coefficient fields define smooth forms on model opens
statement:
  On an open subset of a finite-dimensional real normed vector space, a
  smooth ambient coefficient field defines a smooth differential form.
proof:
  Every chart of the open subset is the restriction of the identity chart on
  the model vector space, so the chartwise coordinate expression agrees with
  the given coefficient field on the chart image.
-/
theorem isContMDiffForm_modelOpen_of_contDiffOn_coeff
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (f : U → E [⋀^Fin n]→L[ℝ] ℝ)
    (hf :
      ContDiffOn ℝ ∞
        (modelOpenFormCoeffExtension (E := E) U n f)
        (U : Set E)) :
    IsContMDiffForm (I := 𝓘(ℝ, E)) (M := U) (F := ℝ) (n := n) ∞ f := by
  by_cases hne : Nonempty U
  · intro e he
    obtain ⟨x₀, rfl⟩ := TopologicalSpace.Opens.chart_eq (H := E) (M := E) hne he
    have htarget :
        ((chartAt E (x₀ : E)).subtypeRestr hne).target = (U : Set E) := by
      ext y
      simp [OpenPartialHomeomorph.subtypeRestr_def]
    have hexttarget :
        (((chartAt E (x₀ : E)).subtypeRestr hne).extend 𝓘(ℝ, E)).target =
          (U : Set E) := by
      ext y
      simp [OpenPartialHomeomorph.subtypeRestr_def]
    have hcoord : ∀ y ∈ (U : Set E),
        coordinateExpression (I := 𝓘(ℝ, E)) (F := ℝ) (n := n) f
          ((chartAt E (x₀ : E)).subtypeRestr hne) y =
        modelOpenFormCoeffExtension (E := E) U n f y := by
      intro y hy
      have hself :=
        coordinateExpression_chartAt_self (I := 𝓘(ℝ, E)) (F := ℝ) (n := n)
          f ⟨y, hy⟩
      simpa [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
        extChartAt_model_space_eq_id, modelOpenFormCoeffExtension, hy] using hself
    rw [hexttarget]
    exact hf.congr hcoord
  · intro e he
    exfalso
    rcases he with ⟨_s, ⟨x, _hx⟩, _he⟩
    exact hne ⟨x⟩

/--
%%handwave
name:
  Smoothness of the Poincare homotopy integral
statement:
  The pointwise integral defining the straight-line homotopy operator is a
  smooth \(n\)-form on the convex open set.
proof:
  Differentiate under the integral sign.  The integrand is smooth in the base
  point and time parameter, and the time interval is compact, so the integral
  is smooth as a coefficient field; in the model-open chart this is exactly
  smoothness as a differential form.
-/
theorem isContMDiffForm_convexOpenPoincareHomotopyPoint
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    IsContMDiffForm (I := 𝓘(ℝ, E)) (M := U) (F := ℝ) (n := n) ∞
      (fun x : U ↦ convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega x) := by
  exact
    isContMDiffForm_modelOpen_of_contDiffOn_coeff (E := E) U n
      (fun x : U ↦ convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega x)
      (contDiffOn_convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega)

/--
%%handwave
name:
  Smooth form represented by the Poincare homotopy integral
statement:
  The model-space pointwise integral defining the straight-line homotopy
  operator is represented by a smooth \(n\)-form on \(U\).
proof:
  Differentiate under the integral sign, using smooth dependence of
  \(H_t(x)\), \(x-x_0\), and \(t\,v_i\) on \(x\) and \(t\), and compactness of
  the time interval.
-/
theorem exists_convexOpenPoincareHomotopyForm
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    ∃ eta : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n,
      ∀ x : U,
        (eta.toFun x : E [⋀^Fin n]→L[ℝ] ℝ) =
          convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega x := by
  refine ⟨{
    toFun := fun x ↦ convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega x
    isContMDiff :=
      isContMDiffForm_convexOpenPoincareHomotopyPoint
        (E := E) U hconvex x₀ n omega }, ?_⟩
  intro x
  rfl

/--
%%handwave
name:
  Poincare homotopy operator as a smooth form
statement:
  The straight-line homotopy operator sends a smooth \((n+1)\)-form to the
  smooth \(n\)-form obtained by integrating the homotopy integrand.
proof:
  Package the pointwise integral together with its smoothness.
-/
def convexOpenPoincareHomotopyForm
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n :=
  Classical.choose
    (exists_convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega)

/--
%%handwave
name:
  Evaluation of the Poincare homotopy form
statement:
  The chosen smooth form representing the Poincare homotopy operator evaluates
  to the model-space pointwise integral.
proof:
  This is the defining property of the chosen representative.
-/
theorem convexOpenPoincareHomotopyForm_toFun
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    ((convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega).toFun x :
        E [⋀^Fin n]→L[ℝ] ℝ) =
      convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega x :=
  (Classical.choose_spec
    (exists_convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega)) x

/--
%%handwave
name:
  Additivity of the pointwise Poincare integral
statement:
  The model-space pointwise integral defining \(K(\omega+\eta)\) is the sum of
  the pointwise integrals defining \(K\omega\) and \(K\eta\).
proof:
  The integrand is pointwise additive in the form, and Bochner integration is
  additive on the compact interval \([0,1]\).
-/
theorem convexOpenPoincareHomotopyPoint_add
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega eta : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n (omega + eta) x =
      convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega x +
        convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n eta x := by
  rw [convexOpenPoincareHomotopyPoint]
  simp_rw [convexOpenPoincareHomotopyIntegrand_add]
  rw [intervalIntegral.integral_add
    (intervalIntegrable_convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x)
    (intervalIntegrable_convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n eta x)]
  rfl

/--
%%handwave
name:
  Homogeneity of the pointwise Poincare integral
statement:
  The model-space pointwise integral defining \(K(c\omega)\) is \(c\) times
  the pointwise integral defining \(K\omega\).
proof:
  The integrand is pointwise homogeneous in the form, and Bochner integration
  commutes with scalar multiplication on the compact interval \([0,1]\).
-/
theorem convexOpenPoincareHomotopyPoint_smul
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ) (c : ℝ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n (c • omega) x =
      c • convexOpenPoincareHomotopyPoint (E := E) U hconvex x₀ n omega x := by
  rw [convexOpenPoincareHomotopyPoint]
  simp_rw [convexOpenPoincareHomotopyIntegrand_smul]
  rw [intervalIntegral.integral_smul]
  rw [convexOpenPoincareHomotopyPoint]

/--
%%handwave
name:
  Additivity of the Poincare homotopy operator
statement:
  The straight-line homotopy operator is additive in the input form.
proof:
  The integrand is additive in \(\omega\), and Bochner integration is additive.
-/
theorem convexOpenPoincareHomotopyForm_add
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega eta : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n (omega + eta) =
      convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega +
        convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n eta := by
  apply DifferentialForm.ext
  intro x
  change
    ((convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n (omega + eta)).toFun x :
        E [⋀^Fin n]→L[ℝ] ℝ) =
      ((convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega).toFun x :
          E [⋀^Fin n]→L[ℝ] ℝ) +
        ((convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n eta).toFun x :
          E [⋀^Fin n]→L[ℝ] ℝ)
  rw [convexOpenPoincareHomotopyForm_toFun,
    convexOpenPoincareHomotopyForm_toFun,
    convexOpenPoincareHomotopyForm_toFun]
  exact convexOpenPoincareHomotopyPoint_add (E := E) U hconvex x₀ n omega eta x

/--
%%handwave
name:
  Homogeneity of the Poincare homotopy operator
statement:
  The straight-line homotopy operator commutes with scalar multiplication of
  the input form.
proof:
  The integrand is homogeneous in \(\omega\), and Bochner integration commutes
  with scalar multiplication.
-/
theorem convexOpenPoincareHomotopyForm_smul
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ) (c : ℝ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n (c • omega) =
      c • convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega := by
  apply DifferentialForm.ext
  intro x
  change
    ((convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n (c • omega)).toFun x :
        E [⋀^Fin n]→L[ℝ] ℝ) =
      c •
        ((convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega).toFun x :
          E [⋀^Fin n]→L[ℝ] ℝ)
  rw [convexOpenPoincareHomotopyForm_toFun,
    convexOpenPoincareHomotopyForm_toFun]
  exact convexOpenPoincareHomotopyPoint_smul (E := E) U hconvex x₀ n c omega x

/--
%%handwave
name:
  Poincare homotopy operator as a linear map
statement:
  The straight-line homotopy operator is a linear map
  \(K:\Omega^{n+1}(U)\to\Omega^n(U)\).
proof:
  Use the integral formula for \(K\) and the additivity and homogeneity of the
  Bochner integral.
-/
def convexOpenPoincareHomotopyLinearMap
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ) :
    SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1) →ₗ[ℝ]
      SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n where
  toFun := convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n
  map_add' := convexOpenPoincareHomotopyForm_add (E := E) U hconvex x₀ n
  map_smul' := by
    intro c omega
    exact convexOpenPoincareHomotopyForm_smul (E := E) U hconvex x₀ n c omega

/--
%%handwave
name:
  Evaluation commutes with the pointwise Poincare integral
statement:
  Evaluating \(K\omega\) at a tangent tuple is the compact interval integral
  of the evaluated homotopy integrand.
proof:
  The value of \(K\omega\) is the Bochner integral of alternating forms.
  Evaluation at a fixed tangent tuple is a continuous linear map, so it
  commutes with the compact interval integral.
-/
theorem convexOpenPoincareHomotopyLinearMap_apply_eq_integral_apply
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin n → E) :
    ((convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega).toFun x :
        E [⋀^Fin n]→L[ℝ] ℝ) v =
      ∫ t in (0 : ℝ)..1,
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t v := by
  change
    ((convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega).toFun x :
        E [⋀^Fin n]→L[ℝ] ℝ) v =
      ∫ t in (0 : ℝ)..1,
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t v
  rw [convexOpenPoincareHomotopyForm_toFun]
  change
    (∫ t in (0 : ℝ)..1,
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t) v =
      ∫ t in (0 : ℝ)..1,
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t v
  let eval :
      (E [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousAlternatingMap.apply ℝ E ℝ v
  have hInt :
      IntervalIntegrable
        (fun t : ℝ ↦
          convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t)
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_convexOpenPoincareHomotopyIntegrand
      U hconvex x₀ n omega x
  simpa [eval] using
    (ContinuousLinearMap.intervalIntegral_comp_comm
      (μ := MeasureTheory.volume) eval hInt).symm

/--
%%handwave
name:
  The \(K d\omega\) term as an evaluated time integral
statement:
  Evaluating the Poincare homotopy operator applied to \(d\omega\) is the
  integral of the evaluated \(d\omega\)-homotopy integrand.
proof:
  This is [the fact that evaluation commutes with the pointwise Poincare integral](lean:JJMath.Manifold.convexOpenPoincareHomotopyLinearMap_apply_eq_integral_apply), applied to \(d\omega\).
-/
theorem convexOpenPoincareHomotopyLinearMap_deRhamDifferential_apply_eq_integral_apply
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    ((convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
        (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
          omega)).toFun x :
        E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
      ∫ t in (0 : ℝ)..1,
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega) x t v := by
  exact
    convexOpenPoincareHomotopyLinearMap_apply_eq_integral_apply
      (E := E) U hconvex x₀ (n + 1)
      (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1) omega)
      x v

/--
%%handwave
name:
  Straight-line pullback at one time
statement:
  At time \(t\), the straight-line homotopy pulls a positive-degree form
  \(\omega\) back by evaluating \(\omega\) at
  \(H_t(x)=(1-t)x_0+tx\) and applying the tangent map \(v\mapsto tv\) to all
  inputs.
proof:
  This is the pointwise definition of pullback by the time-\(t\) map of the
  straight-line homotopy.
-/
def convexOpenStraightLinePullbackPoint
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (t : ℝ) :
    E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
  let τ : Set.Icc (0 : ℝ) 1 := Set.projIcc (0 : ℝ) 1 zero_le_one t
  let y : U := convexOpenStraightLineHomotopy (E := E) U hconvex x₀ τ x
  let tangentScale : E →L[ℝ] E :=
    (τ : ℝ) • ContinuousLinearMap.id ℝ E
  (omega.toFun y).compContinuousLinearMap tangentScale

/--
%%handwave
name:
  Smoothness of the time-dependent straight-line pullback
statement:
  For fixed \(x\) and fixed tangent inputs, the scalar obtained by evaluating
  the time-\(t\) straight-line pullback of a smooth form is \(C^1\) on
  \([0,1]\).
proof:
  In the interval interior this is the chain rule applied to the smooth
  coefficient field of \(\omega\), the affine homotopy \(H_t\), and the
  linear tangent map \(v\mapsto tv\).  The within-smoothness statement includes
  the two endpoints.
-/
theorem contDiffOn_convexOpenStraightLinePullbackPoint_apply_Icc
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    ContDiffOn ℝ 1
      (fun t : ℝ ↦
        convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x t v)
      (Set.Icc (0 : ℝ) 1) := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t ↦ (1 - t) • (x₀ : E) + t • (x : E)
  let coeff : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E) U (n + 1)
      (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y)
  let tangentScale : ℝ → E →L[ℝ] E :=
    fun t ↦ t • ContinuousLinearMap.id ℝ E
  let pull : ℝ → E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
    fun t ↦ (coeff (line t)).compContinuousLinearMap (tangentScale t)
  have ht : ContDiffOn ℝ ∞ (fun t : ℝ ↦ t) s :=
    contDiffOn_id
  have hline : ContDiffOn ℝ ∞ line s := by
    exact
      ((contDiffOn_const.sub ht).smul contDiffOn_const).add
        (ht.smul contDiffOn_const)
  have hline_mem : MapsTo line s (U : Set E) := by
    intro t htI
    simpa [line, AffineMap.lineMap_apply_module] using
      convexOpen_lineMap_mem (E := E) U hconvex x₀ x ⟨t, htI⟩
  have hcoeff :
      ContDiffOn ℝ ∞ coeff (U : Set E) :=
    contDiffOn_smoothFormModelCoeff_modelOpen (E := E) U (n + 1) omega
  have hform :
      ContDiffOn ℝ ∞ (fun t : ℝ ↦ coeff (line t)) s :=
    hcoeff.comp hline hline_mem
  have hscale : ContDiffOn ℝ ∞ tangentScale s :=
    ht.smul contDiffOn_const
  have hpull :
      ContDiffOn ℝ ∞ pull s := by
    simpa [pull] using
      contDiffOn_continuousAlternatingMap_compContinuousLinearMap
        (𝕜 := ℝ) (ι := Fin (n + 1)) (B := E) (D := E) (C := ℝ)
        hform hscale
  have hvalue :
      ContDiffOn ℝ ∞ (fun t : ℝ ↦ pull t v) s := by
    let eval :
        (E [⋀^Fin (n + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousAlternatingMap.apply ℝ E ℝ v
    simpa [eval, Function.comp_def] using hpull.continuousLinearMap_comp eval
  refine (hvalue.of_le (by simp)).congr ?_
  intro t htI
  have hline_eq :
      line t =
        (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
          (Set.projIcc (0 : ℝ) 1 zero_le_one t) x : E) := by
    simp [line, convexOpenStraightLineHomotopy, AffineMap.lineMap_apply_module,
      Set.projIcc_of_mem zero_le_one htI]
  have hcoeff_eq :
      coeff (line t) =
        smoothFormModelCoeff (E := E) U (n + 1) omega
          (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
            (Set.projIcc (0 : ℝ) 1 zero_le_one t) x) := by
    rw [hline_eq]
    simp [coeff, modelOpenFormCoeffExtension]
  have hτ : ((Set.projIcc (0 : ℝ) 1 zero_le_one t : Set.Icc (0 : ℝ) 1) : ℝ) =
      t := by
    have hproj :
        Set.projIcc (0 : ℝ) 1 zero_le_one t = ⟨t, htI⟩ :=
      Set.projIcc_of_mem zero_le_one htI
    exact congrArg Subtype.val hproj
  simp only [convexOpenStraightLinePullbackPoint, pull, hcoeff_eq, tangentScale,
    smoothFormModelCoeff, hτ]
  congr 4

/--
%%handwave
name:
  Straight-line pullback at time one
statement:
  At time \(1\), the straight-line pullback is the original form.
proof:
  The endpoint \(H_1\) is the identity and its tangent map is the identity.
-/
theorem convexOpenStraightLinePullbackPoint_one
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x 1 =
      omega.toFun x := by
  ext v
  dsimp [convexOpenStraightLinePullbackPoint]
  have hτ :
      Set.projIcc (0 : ℝ) 1 zero_le_one 1 =
        (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
    exact Set.projIcc_right (a := (0 : ℝ)) (b := 1) (h := zero_le_one)
  rw [hτ]
  have hy :
      convexOpenStraightLineHomotopy (E := E) U hconvex x₀
          (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) x = x :=
    convexOpenStraightLineHomotopy_one (E := E) U hconvex x₀ x
  rw [hy]
  have hv :
      (⇑(((⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℝ) •
          ContinuousLinearMap.id ℝ E) ∘ v) = v := by
    funext i
    simp
  exact congrArg (fun w : Fin (n + 1) → E ↦ (omega.toFun x) w) hv

/--
%%handwave
name:
  Straight-line pullback at time zero
statement:
  At time \(0\), the straight-line pullback of a positive-degree form is zero.
proof:
  The endpoint \(H_0\) is constant, so its tangent map is the zero map.  A
  positive-degree alternating multilinear form vanishes when all inputs are
  zero.
-/
theorem convexOpenStraightLinePullbackPoint_zero
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x 0 = 0 := by
  ext v
  dsimp [convexOpenStraightLinePullbackPoint]
  have hτ :
      Set.projIcc (0 : ℝ) 1 zero_le_one 0 =
        (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
    exact Set.projIcc_left (a := (0 : ℝ)) (b := 1) (h := zero_le_one)
  rw [hτ]
  have hv :
      (⇑(((⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℝ) •
          ContinuousLinearMap.id ℝ E) ∘ v) = 0 := by
    funext i
    simp
  calc
    (omega.toFun
          (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
            (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) x))
        (⇑(((⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℝ) •
            ContinuousLinearMap.id ℝ E) ∘ v)
        =
      (omega.toFun
          (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
            (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) x))
        (0 : Fin (n + 1) → E) := by
          exact congrArg
            (fun w : Fin (n + 1) → E ↦
              (omega.toFun
                (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
                  (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) x)) w) hv
    _ = 0 := by
          exact
            (omega.toFun
              (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
                (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) x)).map_zero

/--
%%handwave
name:
  Endpoint contribution for the straight-line pullback
statement:
  The difference between the time-\(1\) and time-\(0\) straight-line pullbacks
  of a positive-degree form is the original form.
proof:
  Use the endpoint identities: \(H_1\) is the identity and \(H_0\) is constant,
  hence has zero pullback in positive degree.
-/
theorem convexOpenStraightLinePullbackPoint_endpoint_sub_apply
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x 1 v -
        convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x 0 v =
      (omega.toFun x : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v := by
  rw [convexOpenStraightLinePullbackPoint_one,
    convexOpenStraightLinePullbackPoint_zero]
  have hzero :
      (0 : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v = 0 := rfl
  rw [hzero, sub_zero]
  rfl

/--
%%handwave
name:
  Cartan density for the straight-line homotopy
statement:
  The pointwise Cartan density at time \(t\) is
  \(d_x(\iota_{\partial_tH}H_t^\*\omega)+
  \iota_{\partial_tH}H_t^\*d\omega\), evaluated at \(x\) and on the tangent
  tuple \(v\).
proof:
  This is the definition of the integrand appearing in the Cartan homotopy
  formula for the straight-line homotopy.
-/
def convexOpenCartanHomotopyDensity
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (t : ℝ) (v : Fin (n + 1) → E) : ℝ :=
  (extDerivWithin
      (fun y : E ↦
        convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
          (y, t))
      (U : Set E) (x : E) v) +
    (convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ (n + 1)
      (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1) omega)
      x t v)

/-- The total straight-line homotopy \((x,t)\mapsto (1-t)x_0+tx\). -/
def convexOpenStraightLineTotalHomotopy
    (x₀ : E) (p : E × ℝ) : E :=
  x₀ + p.2 • (p.1 - x₀)

/--
%%handwave
name:
  The total straight-line homotopy stays in the convex set
statement:
  If \(x\in U\) and \(0\le t\le 1\), then
  \((1-t)x_0+tx\in U\).
proof:
  This is the convexity of \(U\), applied to the segment from \(x_0\) to
  \(x\).
-/
theorem convexOpenStraightLineTotalHomotopy_mapsTo
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U) :
    Set.MapsTo
      (convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E))
      ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1)
      (U : Set E) := by
  intro p hp
  simpa [convexOpenStraightLineTotalHomotopy, AffineMap.lineMap_apply_module', add_comm] using
    convexOpen_lineMap_mem (E := E) U hconvex x₀ ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩

/-- The derivative of the total straight-line homotopy \((x,t)\mapsto (1-t)x_0+tx\). -/
def convexOpenStraightLineTotalFDeriv
    (x₀ : E) (p : E × ℝ) :
    E × ℝ →L[ℝ] E :=
  p.2 • ContinuousLinearMap.fst ℝ E ℝ +
    (ContinuousLinearMap.snd ℝ E ℝ).smulRight (p.1 - x₀)

/--
%%handwave
name:
  Smoothness of the total straight-line homotopy
statement:
  The map \(F(x,t)=(1-t)x_0+tx\) is smooth as a map on the product vector
  space.
proof:
  Rewrite \(F(x,t)=x_0+t(x-x_0)\); this is built from projections, subtraction,
  scalar multiplication, and addition.
-/
theorem contDiff_convexOpenStraightLineTotalHomotopy
    (x₀ : E) :
    ContDiff ℝ ∞ (convexOpenStraightLineTotalHomotopy (E := E) x₀) := by
  have hsnd : ContDiff ℝ ∞ (fun p : E × ℝ ↦ p.2) :=
    contDiff_snd
  have hdiff : ContDiff ℝ ∞ (fun p : E × ℝ ↦ p.1 - x₀) :=
    contDiff_fst.sub contDiff_const
  have hsmul : ContDiff ℝ ∞ (fun p : E × ℝ ↦ p.2 • (p.1 - x₀)) :=
    hsnd.smul hdiff
  simpa [convexOpenStraightLineTotalHomotopy] using contDiff_const.add hsmul

/--
%%handwave
name:
  Derivative of the total straight-line homotopy
statement:
  The derivative of \(F(x,t)=(1-t)x_0+tx\) at \((x,t)\), within any set, is
  \((u,s)\mapsto tu+s(x-x_0)\).
proof:
  Rewrite \(F(x,t)=x_0+t(x-x_0)\) and apply the product rule for scalar
  multiplication.
-/
theorem convexOpenStraightLineTotalHomotopy_hasFDerivWithinAt
    (x₀ : E) (s : Set (E × ℝ)) (p : E × ℝ) :
    HasFDerivWithinAt
      (convexOpenStraightLineTotalHomotopy (E := E) x₀)
      (convexOpenStraightLineTotalFDeriv (E := E) x₀ p)
      s p := by
  have hsnd :
      HasFDerivWithinAt
        (fun q : E × ℝ ↦ q.2)
        (ContinuousLinearMap.snd ℝ E ℝ)
        s p :=
    hasFDerivWithinAt_snd
  have hfst :
      HasFDerivWithinAt
        (fun q : E × ℝ ↦ q.1)
        (ContinuousLinearMap.fst ℝ E ℝ)
        s p :=
    hasFDerivWithinAt_fst
  have hdiff :
      HasFDerivWithinAt
        (fun q : E × ℝ ↦ q.1 - x₀)
        (ContinuousLinearMap.fst ℝ E ℝ)
        s p := by
    simpa using hfst.sub_const x₀
  have hsmul :
      HasFDerivWithinAt
        (fun q : E × ℝ ↦ q.2 • (q.1 - x₀))
        (convexOpenStraightLineTotalFDeriv (E := E) x₀ p)
        s p := by
    simpa [convexOpenStraightLineTotalFDeriv] using hsnd.smul hdiff
  have hconst :
      HasFDerivWithinAt
        (fun _q : E × ℝ ↦ x₀)
        (0 : E × ℝ →L[ℝ] E)
        s p :=
    hasFDerivWithinAt_const x₀ p s
  simpa [convexOpenStraightLineTotalHomotopy] using hconst.add hsmul

/--
%%handwave
name:
  Within-derivative of the total straight-line homotopy
statement:
  On a set with unique tangent directions, the within-derivative of
  \(F(x,t)=(1-t)x_0+tx\) is \((u,s)\mapsto tu+s(x-x_0)\).
proof:
  This is the preceding derivative formula, using uniqueness of within
  derivatives.
-/
theorem convexOpenStraightLineTotalHomotopy_fderivWithin
    (x₀ : E) (s : Set (E × ℝ)) (p : E × ℝ)
    (hs : UniqueDiffWithinAt ℝ s p) :
    fderivWithin ℝ (convexOpenStraightLineTotalHomotopy (E := E) x₀) s p =
      convexOpenStraightLineTotalFDeriv (E := E) x₀ p :=
  (convexOpenStraightLineTotalHomotopy_hasFDerivWithinAt
    (E := E) x₀ s p).fderivWithin hs

/--
%%handwave
name:
  Smooth dependence of the derivative of the total straight-line homotopy
statement:
  The linear map \((u,s)\mapsto tu+s(x-x_0)\), which is the derivative of the
  total straight-line homotopy \(F(x,t)=(1-t)x_0+tx\), depends smoothly on
  \((x,t)\).
proof:
  The term \(tu\) is scalar multiplication of the first projection by the
  smooth coordinate \(t\).  The term \(s(x-x_0)\) is obtained by applying the
  continuous rank-one-operator construction to the smooth map \(x\mapsto
  x-x_0\).  Addition preserves smoothness.
-/
theorem contDiff_convexOpenStraightLineTotalFDeriv
    (x₀ : E) :
    ContDiff ℝ ∞ (convexOpenStraightLineTotalFDeriv (E := E) x₀) := by
  have hsnd : ContDiff ℝ ∞ (fun p : E × ℝ ↦ p.2) :=
    contDiff_snd
  have hfirst :
      ContDiff ℝ ∞
        (fun p : E × ℝ ↦ p.2 • ContinuousLinearMap.fst ℝ E ℝ) :=
    hsnd.smul contDiff_const
  have hdiff : ContDiff ℝ ∞ (fun p : E × ℝ ↦ p.1 - x₀) :=
    contDiff_fst.sub contDiff_const
  let rankOne :
      E →L[ℝ] E × ℝ →L[ℝ] E :=
    ContinuousLinearMap.smulRightL ℝ (E × ℝ) E
      (ContinuousLinearMap.snd ℝ E ℝ)
  have hsecond :
      ContDiff ℝ ∞
        (fun p : E × ℝ ↦
          (ContinuousLinearMap.snd ℝ E ℝ).smulRight (p.1 - x₀)) := by
    simpa [rankOne] using rankOne.contDiff.comp hdiff
  simpa [convexOpenStraightLineTotalFDeriv] using hfirst.add hsecond

/--
The pullback of a form by the total straight-line homotopy
\((x,t)\mapsto (1-t)x_0+tx\), written on the ambient product space.
-/
def convexOpenStraightLineTotalPullbackForm
    (U : TopologicalSpace.Opens E)
    (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (p : E × ℝ) :
    (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
  let coeff : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E) U (n + 1)
      (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y)
  (coeff (convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) p)).compContinuousLinearMap
    (convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) p)

/-- The tangent tuple \(\partial_t,v_0,\ldots,v_n\) on the product \(U\times[0,1]\). -/
def convexOpenStraightLineTimeBaseTangent
    {k : ℕ} (v : Fin k → E) :
    Fin (k + 1) → E × ℝ :=
  Matrix.vecCons ((0 : E), (1 : ℝ)) (fun i : Fin k ↦ (v i, 0))

/--
%%handwave
name:
  Derivative of the total homotopy on the time-base tangent tuple
statement:
  The derivative of \(F(x,t)=(1-t)x_0+tx\) sends
  \(\partial_t,v_0,\ldots,v_n\) to
  \(x-x_0,tv_0,\ldots,tv_n\).
proof:
  The derivative of \(F\) is \((u,s)\mapsto tu+s(x-x_0)\).
-/
theorem convexOpenStraightLineTotalFDeriv_comp_timeBaseTangent
    (x₀ x : E) (t : ℝ) (k : ℕ) (v : Fin k → E) :
    (convexOpenStraightLineTotalFDeriv (E := E) x₀ (x, t)) ∘
        convexOpenStraightLineTimeBaseTangent (E := E) v =
      Matrix.vecCons (x - x₀) (fun i : Fin k ↦ t • v i) := by
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    simp [convexOpenStraightLineTotalFDeriv, convexOpenStraightLineTimeBaseTangent]

/--
%%handwave
name:
  The total pullback on the time-base tangent tuple is the homotopy integrand
statement:
  Evaluating \(F^\*\omega\) on \(\partial_t,v_1,\ldots,v_n\) gives
  \(\omega_{F(x,t)}(x-x_0,tv_1,\ldots,tv_n)\), the integrand of the
  straight-line homotopy operator.
proof:
  The derivative of \(F(x,t)=(1-t)x_0+tx\) sends \(\partial_t\) to
  \(x-x_0\) and sends each base vector \(v_i\) to \(tv_i\).
-/
theorem convexOpenStraightLineTotalPullbackForm_timeBaseTangent
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin n → E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega ((x : E), t)
        (convexOpenStraightLineTimeBaseTangent (E := E) v) =
      convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega x t v := by
  have hτ : ((Set.projIcc (0 : ℝ) 1 zero_le_one t : Set.Icc (0 : ℝ) 1) : ℝ) =
      t := by
    have hproj :
        Set.projIcc (0 : ℝ) 1 zero_le_one t = ⟨t, ht⟩ :=
      Set.projIcc_of_mem zero_le_one ht
    exact congrArg Subtype.val hproj
  have hline :
      convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t) =
        (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
          (Set.projIcc (0 : ℝ) 1 zero_le_one t) x : E) := by
    simp [convexOpenStraightLineTotalHomotopy, convexOpenStraightLineHomotopy,
      AffineMap.lineMap_apply_module', hτ, add_comm]
  have hcoeff :
      modelOpenFormCoeffExtension (E := E) U (n + 1)
          (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y)
          (convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t)) =
        smoothFormModelCoeff (E := E) U (n + 1) omega
          (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
            (Set.projIcc (0 : ℝ) 1 zero_le_one t) x) := by
    rw [hline]
    simp [modelOpenFormCoeffExtension]
  have htangent :
      (convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) ((x : E), t)) ∘
          convexOpenStraightLineTimeBaseTangent (E := E) v =
        Matrix.vecCons ((x : E) - (x₀ : E)) (fun i : Fin n ↦ t • v i) :=
    convexOpenStraightLineTotalFDeriv_comp_timeBaseTangent
      (E := E) (x₀ : E) (x : E) t n v
  dsimp [convexOpenStraightLineTotalPullbackForm, convexOpenPoincareHomotopyIntegrand]
  simp only [hcoeff, hτ]
  rw [htangent]
  rfl

/--
%%handwave
name:
  The total pullback restricted to base tangent vectors is the time pullback
statement:
  Evaluating the total pullback \(F^\*\omega\) on tangent vectors tangent to
  the base \(U\) gives the pullback by the time-\(t\) map \(H_t\).
proof:
  The derivative of \(F(x,t)=(1-t)x_0+tx\) sends a base tangent vector \(v\)
  to \(tv\).  Substituting this into the definition of pullback gives the
  time-\(t\) pullback.
-/
theorem convexOpenStraightLineTotalPullbackForm_baseTangent
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega ((x : E), t)
      ).compContinuousLinearMap (ContinuousLinearMap.inl ℝ E ℝ)) v =
      convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x t v := by
  have hτ : ((Set.projIcc (0 : ℝ) 1 zero_le_one t : Set.Icc (0 : ℝ) 1) : ℝ) =
      t := by
    have hproj :
        Set.projIcc (0 : ℝ) 1 zero_le_one t = ⟨t, ht⟩ :=
      Set.projIcc_of_mem zero_le_one ht
    exact congrArg Subtype.val hproj
  have hline :
      convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t) =
        (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
          (Set.projIcc (0 : ℝ) 1 zero_le_one t) x : E) := by
    simp [convexOpenStraightLineTotalHomotopy, convexOpenStraightLineHomotopy,
      AffineMap.lineMap_apply_module', hτ, add_comm]
  have hcoeff :
      modelOpenFormCoeffExtension (E := E) U (n + 1)
          (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y)
          (convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t)) =
        smoothFormModelCoeff (E := E) U (n + 1) omega
          (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
            (Set.projIcc (0 : ℝ) 1 zero_le_one t) x) := by
    rw [hline]
    simp [modelOpenFormCoeffExtension]
  have htangent :
      (convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) ((x : E), t)).comp
          (ContinuousLinearMap.inl ℝ E ℝ) =
        t • ContinuousLinearMap.id ℝ E := by
    ext z
    simp [convexOpenStraightLineTotalFDeriv]
  dsimp [convexOpenStraightLineTotalPullbackForm, convexOpenStraightLinePullbackPoint]
  rw [hcoeff]
  simp only [hτ, smoothFormModelCoeff]
  change
    (omega.toFun
        (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
          (Set.projIcc (0 : ℝ) 1 zero_le_one t) x))
      (((convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) ((x : E), t)).comp
        (ContinuousLinearMap.inl ℝ E ℝ)) ∘ v) =
    (omega.toFun
        (convexOpenStraightLineHomotopy (E := E) U hconvex x₀
          (Set.projIcc (0 : ℝ) 1 zero_le_one t) x))
      (⇑(t • ContinuousLinearMap.id ℝ E) ∘ v)
  rw [htangent]

/--
%%handwave
name:
  The time contraction of the total pullback is the homotopy integrand
statement:
  On \(U\), contracting the total pullback \(F^\*\omega\) by
  \(\partial_t\) and restricting the remaining inputs to base tangent vectors
  gives the straight-line homotopy integrand.
proof:
  Evaluate both sides on a tangent tuple.  The derivative of \(F\) sends
  \(\partial_t\) to \(x-x_0\) and sends a base vector \(v\) to \(tv\), which
  is exactly the defining formula for the homotopy integrand.
-/
theorem convexOpenStraightLineTotalPullbackForm_timeContraction_eq_integrandExtension
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    EqOn
      (fun y : E ↦
        ((convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega (y, t)
          ).curryLeft ((0 : E), (1 : ℝ))).compContinuousLinearMap
            (ContinuousLinearMap.inl ℝ E ℝ))
      (fun y : E ↦
        convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega (y, t))
      (U : Set E) := by
  intro y hy
  ext v
  have htime :=
    convexOpenStraightLineTotalPullbackForm_timeBaseTangent
      (E := E) U hconvex x₀ n omega ⟨y, hy⟩ v ht
  calc
    (((convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega (y, t)
      ).curryLeft ((0 : E), (1 : ℝ))).compContinuousLinearMap
        (ContinuousLinearMap.inl ℝ E ℝ)) v =
        convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega (y, t)
          (convexOpenStraightLineTimeBaseTangent (E := E) v) := by
          change
            (convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega (y, t)).curryLeft
                ((0 : E), (1 : ℝ))
              (⇑(ContinuousLinearMap.inl ℝ E ℝ) ∘ v) =
            convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega (y, t)
              (convexOpenStraightLineTimeBaseTangent (E := E) v)
          rw [ContinuousAlternatingMap.curryLeft_apply_apply]
          congr 1
    _ =
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega ⟨y, hy⟩ t v :=
          htime
    _ =
        convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega (y, t) v := by
          simp [convexOpenPoincareHomotopyIntegrandExtension, hy]

/--
The exterior derivative of the total pulled-back form, evaluated on
\(\partial_t,v_0,\ldots,v_n\).
-/
def convexOpenStraightLineTotalExteriorDerivativeTerm
    (U : TopologicalSpace.Opens E)
    (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (t : ℝ) (v : Fin (n + 1) → E) : ℝ :=
  extDerivWithin
    (convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega)
    ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1)
    ((x : E), t)
    (convexOpenStraightLineTimeBaseTangent (E := E) v)

/--
%%handwave
name:
  Total exterior derivative as a pulled-back exterior derivative
statement:
  For the total straight-line homotopy \(F(x,t)=(1-t)x_0+tx\), the exterior
  derivative of the ambient pullback \(F^\*\omega\) is the pullback of the
  model exterior derivative of \(\omega\).
proof:
  Apply the naturality of the model-space exterior derivative under smooth
  pullback.  The product \(U\times[0,1]\) has unique tangent directions, the
  straight-line map is smooth and maps this product into \(U\), and its
  within-derivative is the explicit affine derivative.
-/
theorem convexOpenStraightLineTotalExteriorDerivativeTerm_eq_pullback_extDerivWithin
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    convexOpenStraightLineTotalExteriorDerivativeTerm (E := E) U x₀ n omega x t v =
      ((extDerivWithin
          (modelOpenFormCoeffExtension (E := E) U (n + 1)
            (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y))
          (U : Set E)
          (convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t))
        ).compContinuousLinearMap
          (convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) ((x : E), t)))
        (convexOpenStraightLineTimeBaseTangent (E := E) v) := by
  let s : Set (E × ℝ) := (U : Set E) ×ˢ Set.Icc (0 : ℝ) 1
  let p : E × ℝ := ((x : E), t)
  let coeff : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E) U (n + 1)
      (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y)
  let F : E × ℝ → E := convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E)
  have hp : p ∈ s := by
    exact ⟨x.2, ht⟩
  have hsUnique : UniqueDiffOn ℝ s := by
    dsimp [s]
    exact U.2.uniqueDiffOn.prod uniqueDiffOn_Icc_zero_one
  have hFmem : F p ∈ (U : Set E) :=
    convexOpenStraightLineTotalHomotopy_mapsTo (E := E) U hconvex x₀ hp
  have hcoeffDiffOn : DifferentiableOn ℝ coeff (U : Set E) :=
    (contDiffOn_smoothFormModelCoeff_modelOpen (E := E) U (n + 1) omega).differentiableOn
      (by simp)
  have hcoeffDiff : DifferentiableWithinAt ℝ coeff (U : Set E) (F p) :=
    hcoeffDiffOn (F p) hFmem
  have hFContDiff : ContDiffWithinAt ℝ ∞ F s p :=
    (contDiff_convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E)).contDiffAt.contDiffWithinAt
  have hmin : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    simpa [minSmoothness] using
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from by
        exact_mod_cast (show (2 : ℕ) ≤ (⊤ : ℕ∞) from le_top))
  have hpClosure : p ∈ closure (interior s) := by
    dsimp [p, s]
    rw [interior_prod_eq, closure_prod_eq, interior_Icc, closure_Ioo zero_ne_one]
    constructor
    · have hxInterior : (x : E) ∈ interior (U : Set E) := by
        exact mem_interior_iff_mem_nhds.mpr (U.2.mem_nhds x.2)
      exact subset_closure hxInterior
    · exact ht
  have hMaps : Set.MapsTo F s (U : Set E) :=
    convexOpenStraightLineTotalHomotopy_mapsTo (E := E) U hconvex x₀
  have hform_eq :
      EqOn
        (convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega)
        (fun q : E × ℝ ↦
          (coeff (F q)).compContinuousLinearMap (fderivWithin ℝ F s q))
        s := by
    intro q hq
    dsimp [convexOpenStraightLineTotalPullbackForm, coeff, F]
    rw [convexOpenStraightLineTotalHomotopy_fderivWithin
      (E := E) (x₀ : E) s q (hsUnique.uniqueDiffWithinAt hq)]
  have hleft :
      extDerivWithin
          (convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega)
          s p =
        extDerivWithin
          (fun q : E × ℝ ↦
            (coeff (F q)).compContinuousLinearMap (fderivWithin ℝ F s q))
          s p :=
    extDerivWithin_congr' hform_eq hp
  have hpull :
      extDerivWithin
          (fun q : E × ℝ ↦
            (coeff (F q)).compContinuousLinearMap (fderivWithin ℝ F s q))
          s p =
        (extDerivWithin coeff (U : Set E) (F p)).compContinuousLinearMap
          (fderivWithin ℝ F s p) :=
    extDerivWithin_pullback (x := p) (f := F) (t := (U : Set E))
      hcoeffDiff hFContDiff hmin hsUnique hpClosure hp hMaps
  have hFderiv :
      fderivWithin ℝ F s p =
        convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) p :=
    convexOpenStraightLineTotalHomotopy_fderivWithin
      (E := E) (x₀ : E) s p (hsUnique.uniqueDiffWithinAt hp)
  calc
    convexOpenStraightLineTotalExteriorDerivativeTerm (E := E) U x₀ n omega x t v =
        (extDerivWithin
          (convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega)
          s p)
          (convexOpenStraightLineTimeBaseTangent (E := E) v) := by
          rfl
    _ =
        (extDerivWithin
          (fun q : E × ℝ ↦
            (coeff (F q)).compContinuousLinearMap (fderivWithin ℝ F s q))
          s p)
          (convexOpenStraightLineTimeBaseTangent (E := E) v) := by
          rw [hleft]
    _ =
        ((extDerivWithin coeff (U : Set E) (F p)).compContinuousLinearMap
          (fderivWithin ℝ F s p))
          (convexOpenStraightLineTimeBaseTangent (E := E) v) := by
          rw [hpull]
    _ =
        ((extDerivWithin coeff (U : Set E) (F p)).compContinuousLinearMap
          (convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) p))
          (convexOpenStraightLineTimeBaseTangent (E := E) v) := by
          rw [hFderiv]
    _ =
        ((extDerivWithin
          (modelOpenFormCoeffExtension (E := E) U (n + 1)
            (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y))
          (U : Set E)
          (convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t))
        ).compContinuousLinearMap
          (convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) ((x : E), t)))
        (convexOpenStraightLineTimeBaseTangent (E := E) v) := by
          rfl

/--
%%handwave
name:
  Integrability of the exterior-derivative Cartan density
statement:
  The exterior derivative in the base variable of the straight-line homotopy
  integrand, evaluated on a fixed tangent tuple, is integrable in time.
proof:
  This follows from the joint smoothness of the straight-line homotopy
  integrand in the base point and time parameter.
-/
theorem intervalIntegrable_convexOpenPoincareHomotopyExteriorDensity
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    IntervalIntegrable
      (fun t : ℝ ↦
        extDerivWithin
          (fun y : E ↦
            convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
              (y, t))
          (U : Set E) (x : E) v)
      MeasureTheory.volume (0 : ℝ) 1 := by
  let f : E × ℝ → E [⋀^Fin n]→L[ℝ] ℝ :=
    convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
  have hf :
      ContDiffOn ℝ ∞ f ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1) :=
    contDiffOn_convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega
  have hdf :
      ContDiffOn ℝ 0
        (fun p : E × ℝ ↦
          fderivWithin ℝ (fun y : E ↦ f (y, p.2)) (U : Set E) p.1)
        ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1) :=
    (contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc
      (E := E) (F := E [⋀^Fin n]→L[ℝ] ℝ)
      U.2 zero_le_one hf).of_le (by simp)
  have hslice :
      ContinuousOn
        (fun t : ℝ ↦
          fderivWithin ℝ (fun y : E ↦ f (y, t)) (U : Set E) (x : E))
        (Set.Icc (0 : ℝ) 1) :=
    continuousOn_time_slice_of_contDiffOn_prod_Icc_zero
      (E := E) (F := E [⋀^Fin n]→L[ℝ] ℝ)
      U.2 hdf x.2
  let altEval :
      (E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.apply ℝ E ℝ v).comp
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM
        (𝕜 := ℝ) (n := n) E ℝ)
  have hcont :
      ContinuousOn
        (fun t : ℝ ↦
          altEval
            (fderivWithin ℝ (fun y : E ↦ f (y, t)) (U : Set E) (x : E)))
        (Set.Icc (0 : ℝ) 1) := by
    simpa [Function.comp_def] using
      altEval.continuous.continuousOn.comp hslice (fun _ _ ↦ Set.mem_univ _)
  simpa [f, extDerivWithin, altEval] using
    hcont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one

/--
%%handwave
name:
  Continuous linear functionals commute with strong operator time integrals
statement:
  Let \(F\) be complete, and let
  \(g:[0,1]\to\mathcal L(E,F)\) be continuous for the strong operator
  topology.  Applying a continuous linear functional on \(\mathcal L(E,F)\)
  to the compact interval integral of \(g\) is the same as integrating the
  resulting scalar function.
proof:
  Continuity on the compact interval gives interval-integrability of the
  operator-valued path.  The claim is then the Bochner integral functoriality
  statement for continuous linear maps.
-/
theorem continuousLinearMap_intervalIntegral_comp_comm_of_strong_continuousOn_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : (E →L[ℝ] F) →L[ℝ] ℝ)
    (g : ℝ → E →L[ℝ] F)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    L (∫ t in (0 : ℝ)..1, g t) =
      ∫ t in (0 : ℝ)..1, L (g t) := by
  have hgi : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) 1 :=
    hg.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
  simpa using (L.intervalIntegral_comp_comm hgi).symm

/--
%%handwave
name:
  Exterior derivative commutes with a smooth compact time integral
statement:
  If a family of \(n\)-forms on an open subset of a finite-dimensional real
  vector space is smooth jointly in the base point and in
  \(t\in[0,1]\), then the model-space exterior derivative of its compact time
  integral is the compact time integral of its exterior derivatives.
proof:
  Differentiate the Banach-valued integral under the integral sign.  The
  compactness of the time interval and joint smoothness provide the required
  local domination and continuity of the parameter derivative; alternatization
  and evaluation on a fixed tangent tuple are continuous linear operations, so
  they commute with the resulting integral.
-/
theorem extDerivWithin_intervalIntegral_apply_of_contDiffOn_prod_Icc
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (f : E × ℝ → E [⋀^Fin n]→L[ℝ] ℝ)
    (hf : ContDiffOn ℝ ∞ f ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1))
    (x : U) (v : Fin (n + 1) → E) :
    (extDerivWithin
      (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
      (U : Set E) (x : E)) v =
    ∫ t in (0 : ℝ)..1,
      extDerivWithin
        (fun y : E ↦ f (y, t))
        (U : Set E) (x : E) v := by
  let df : E × ℝ → E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℝ :=
    fun p ↦ fderivWithin ℝ (fun y : E ↦ f (y, p.2)) (U : Set E) p.1
  let altEval :
      (E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.apply ℝ E ℝ v).comp
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM
        (𝕜 := ℝ) (n := n) E ℝ)
  have hderiv :
      HasFDerivWithinAt
        (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
        (∫ t in (0 : ℝ)..1,
          fderivWithin ℝ (fun y : E ↦ f (y, t)) (U : Set E) (x : E))
        (U : Set E) (x : E) :=
    hasFDerivWithinAt_intervalIntegral_of_contDiffOn_prod_Icc
      (E := E) (F := E [⋀^Fin n]→L[ℝ] ℝ)
      (s := (U : Set E)) U.2 zero_le_one hf (x : E) x.2
  have hfd :
      fderivWithin ℝ
        (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
        (U : Set E) (x : E) =
      ∫ t in (0 : ℝ)..1,
        fderivWithin ℝ (fun y : E ↦ f (y, t)) (U : Set E) (x : E) :=
    hderiv.fderivWithin (U.2.uniqueDiffOn (x : E) x.2)
  have hdf :
      ContDiffOn ℝ 0 df ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1) := by
    dsimp [df]
    exact
      (contDiffOn_parameter_fderivWithin_of_contDiffOn_prod_Icc
        (E := E) (F := E [⋀^Fin n]→L[ℝ] ℝ)
        U.2 zero_le_one hf).of_le (by simp)
  have hslice :
      ContinuousOn (fun t : ℝ ↦ df ((x : E), t)) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_time_slice_of_contDiffOn_prod_Icc_zero
      (E := E) (F := E [⋀^Fin n]→L[ℝ] ℝ)
      U.2 hdf x.2
  calc
    (extDerivWithin
      (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
      (U : Set E) (x : E)) v
        = altEval
            (fderivWithin ℝ
              (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
              (U : Set E) (x : E)) := by
          rfl
    _ = altEval (∫ t in (0 : ℝ)..1, df ((x : E), t)) := by
          rw [hfd]
    _ = ∫ t in (0 : ℝ)..1, altEval (df ((x : E), t)) := by
          exact
            continuousLinearMap_intervalIntegral_comp_comm_of_strong_continuousOn_Icc
              (E := E) (F := E [⋀^Fin n]→L[ℝ] ℝ)
              altEval (fun t : ℝ ↦ df ((x : E), t)) hslice
    _ =
      ∫ t in (0 : ℝ)..1,
        extDerivWithin
          (fun y : E ↦ f (y, t))
          (U : Set E) (x : E) v := by
        rfl

/--
%%handwave
name:
  Exterior derivative commutes with the Poincare time integral
statement:
  The model-space exterior derivative, evaluated on a fixed tangent tuple,
  commutes with the compact time integral defining the straight-line Poincare
  homotopy.
proof:
  Differentiate the Banach-valued integral under the integral sign, then use
  linearity and continuity of alternatization and evaluation on tangent
  tuples to pass them through the integral.
-/
theorem convexOpenPoincareHomotopy_extDerivWithin_integral_apply
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    (extDerivWithin
      (fun y : E ↦ ∫ t in (0 : ℝ)..1,
        convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
          (y, t))
      (U : Set E) (x : E)) v =
    ∫ t in (0 : ℝ)..1,
      extDerivWithin
        (fun y : E ↦
          convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
            (y, t))
        (U : Set E) (x : E) v := by
  let f : E × ℝ → E [⋀^Fin n]→L[ℝ] ℝ :=
    convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
  have hf : ContDiffOn ℝ ∞ f ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1) :=
    contDiffOn_convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ n omega
  simpa [f] using
    extDerivWithin_intervalIntegral_apply_of_contDiffOn_prod_Icc
      (E := E) U n f hf x v

/--
%%handwave
name:
  The \(dK\omega\) term as an exterior-derivative density integral
statement:
  Evaluating \(dK\omega\) at \(x\) and on a tangent tuple is the time integral
  of the exterior derivative, in the base variable, of the straight-line
  homotopy integrand.
proof:
  Apply the exterior derivative to the smooth coefficient field obtained by
  integrating the homotopy integrand over time, and differentiate under the
  compact interval integral.
-/
theorem deRhamDifferential_convexOpenPoincareHomotopyLinearMap_apply_eq_integral_extDerivWithin
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
        (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
    ∫ t in (0 : ℝ)..1,
      extDerivWithin
        (fun y : E ↦
          convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
            (y, t))
        (U : Set E) (x : E) v := by
  let Komega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n :=
    convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega
  let f : E × ℝ → E [⋀^Fin n]→L[ℝ] ℝ :=
    convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
  have hK_coeff :
      EqOn
        (modelOpenFormCoeffExtension (E := E) U n
        (fun y ↦ smoothFormModelCoeff (E := E) U n Komega y))
        (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
        (U : Set E) := by
    intro y hy
    simp only [modelOpenFormCoeffExtension, hy, dite_true]
    change
      ((Komega.toFun ⟨y, hy⟩ : E [⋀^Fin n]→L[ℝ] ℝ)) =
      ∫ t in (0 : ℝ)..1, f (y, t)
    dsimp [Komega]
    change
      ((convexOpenPoincareHomotopyForm (E := E) U hconvex x₀ n omega).toFun
          ⟨y, hy⟩ :
        E [⋀^Fin n]→L[ℝ] ℝ) =
      ∫ t in (0 : ℝ)..1, f (y, t)
    rw [convexOpenPoincareHomotopyForm_toFun]
    simp [convexOpenPoincareHomotopyPoint, f,
      convexOpenPoincareHomotopyIntegrandExtension, hy]
  have hmodel :
      ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n Komega).toFun x :
        E [⋀^Fin (n + 1)]→L[ℝ] ℝ) =
      extDerivWithin
        (modelOpenFormCoeffExtension (E := E) U n
          (fun y ↦ smoothFormModelCoeff (E := E) U n Komega y))
        (U : Set E) (x : E) :=
    deRhamDifferential_modelOpen_toFun (E := E) U n Komega x
  have hcoeff_ext :
      extDerivWithin
        (modelOpenFormCoeffExtension (E := E) U n
          (fun y ↦ smoothFormModelCoeff (E := E) U n Komega y))
        (U : Set E) (x : E) =
      extDerivWithin
        (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
        (U : Set E) (x : E) :=
    extDerivWithin_congr' hK_coeff x.2
  calc
    ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
        (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v
        = (extDerivWithin
            (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
            (U : Set E) (x : E)) v := by
          change ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n Komega).toFun x :
            E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
              (extDerivWithin
                (fun y : E ↦ ∫ t in (0 : ℝ)..1, f (y, t))
                (U : Set E) (x : E)) v
          rw [hmodel, hcoeff_ext]
          rfl
    _ =
      ∫ t in (0 : ℝ)..1,
        extDerivWithin
          (fun y : E ↦
            convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
              (y, t))
          (U : Set E) (x : E) v := by
        simpa [f] using
          convexOpenPoincareHomotopy_extDerivWithin_integral_apply
            (E := E) U hconvex x₀ n omega x v

/--
%%handwave
name:
  The homotopy formula is the integral of the Cartan density
statement:
  The value of \(dK\omega+Kd\omega\) at \(x\) and on a tangent tuple \(v\) is
  the integral over \(t\in[0,1]\) of the Cartan density.
proof:
  Differentiate the coefficient field of the homotopy integral under the
  compact interval integral, and use the definition of the homotopy operator
  for the \(Kd\omega\) term.
-/
theorem deRham_convex_open_homotopy_linearMap_cartan_add_apply_eq_integral_density
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    ((
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) +
        convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
    ∫ t in (0 : ℝ)..1,
      convexOpenCartanHomotopyDensity (E := E) U hconvex x₀ n omega x t v := by
  have hdK :
      ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega)).toFun x :
        E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
      ∫ t in (0 : ℝ)..1,
        extDerivWithin
          (fun y : E ↦
            convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
              (y, t))
          (U : Set E) (x : E) v :=
    deRhamDifferential_convexOpenPoincareHomotopyLinearMap_apply_eq_integral_extDerivWithin
      (E := E) U hconvex x₀ n omega x v
  have hKd :
      ((convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
          E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
        ∫ t in (0 : ℝ)..1,
          convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ (n + 1)
            (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
              omega) x t v :=
    convexOpenPoincareHomotopyLinearMap_deRhamDifferential_apply_eq_integral_apply
      (E := E) U hconvex x₀ n omega x v
  have hExtInt :
      IntervalIntegrable
        (fun t : ℝ ↦
          extDerivWithin
            (fun y : E ↦
              convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
                (y, t))
            (U : Set E) (x : E) v)
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_convexOpenPoincareHomotopyExteriorDensity
      (E := E) U hconvex x₀ n omega x v
  have hKdInt :
      IntervalIntegrable
        (fun t : ℝ ↦
          convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ (n + 1)
            (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
              omega) x t v)
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_convexOpenPoincareHomotopyIntegrand_apply
      (E := E) U hconvex x₀ (n + 1)
      (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1) omega)
      x v
  calc
    ((
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) +
        convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v
        =
      ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega)).toFun x :
        E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v +
      ((convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
        E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v := by
        rfl
    _ =
      (∫ t in (0 : ℝ)..1,
        extDerivWithin
          (fun y : E ↦
            convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
              (y, t))
          (U : Set E) (x : E) v) +
      (∫ t in (0 : ℝ)..1,
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega) x t v) := by
        rw [hdK, hKd]
    _ =
      ∫ t in (0 : ℝ)..1,
        (extDerivWithin
          (fun y : E ↦
            convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
              (y, t))
          (U : Set E) (x : E) v) +
        convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega) x t v := by
        rw [intervalIntegral.integral_add hExtInt hKdInt]
    _ =
      ∫ t in (0 : ℝ)..1,
        convexOpenCartanHomotopyDensity (E := E) U hconvex x₀ n omega x t v := by
        exact intervalIntegral.integral_congr (by
          intro t _ht
          rfl)

/--
%%handwave
name:
  Smoothness of the total pulled-back form
statement:
  The total pullback \(F^\*\omega\) of a smooth form along
  \(F(x,t)=(1-t)x_0+tx\) is \(C^\infty\) on \(U\times[0,1]\).
proof:
  The coefficient field of \(\omega\) is smooth on \(U\), the total homotopy
  \(F\) is smooth and maps \(U\times[0,1]\) into \(U\), and the derivative
  \(dF\) depends smoothly on \((x,t)\).  Smoothness is preserved by pullback
  of alternating forms along smoothly varying linear maps.
-/
theorem contDiffOn_convexOpenStraightLineTotalPullbackForm
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    ContDiffOn ℝ ∞
      (convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega)
      ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1) := by
  let s : Set (E × ℝ) := (U : Set E) ×ˢ Set.Icc (0 : ℝ) 1
  let coeff : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E) U (n + 1)
      (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y)
  let line : E × ℝ → E :=
    convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E)
  have hcoeff :
      ContDiffOn ℝ ∞ coeff (U : Set E) :=
    contDiffOn_smoothFormModelCoeff_modelOpen (E := E) U (n + 1) omega
  have hline :
      ContDiffOn ℝ ∞ line s :=
    (contDiff_convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E)).contDiffOn
  have hline_mem : MapsTo line s (U : Set E) :=
    convexOpenStraightLineTotalHomotopy_mapsTo (E := E) U hconvex x₀
  have hform :
      ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ coeff (line p)) s :=
    hcoeff.comp hline hline_mem
  have hderiv :
      ContDiffOn ℝ ∞
        (fun p : E × ℝ ↦ convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) p)
        s :=
    (contDiff_convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E)).contDiffOn
  simpa [convexOpenStraightLineTotalPullbackForm, coeff, line, s] using
    contDiffOn_continuousAlternatingMap_compContinuousLinearMap
      (𝕜 := ℝ) (ι := Fin (n + 1)) (B := E) (D := E × ℝ) (C := ℝ)
      hform hderiv

/--
%%handwave
name:
  Product Cartan formula for the straight-line contraction
statement:
  For the total straight-line homotopy \(F(x,t)=(1-t)x_0+tx\), the
  within-derivative of \(H_t^\*\omega(v_0,\ldots,v_n)\) is the sum of
  \(d_x(\iota_{\partial_tF}F^\*\omega)\) and the exterior derivative of the
  total pulled-back form \(F^\*\omega\), both evaluated on
  \(\partial_t,v_0,\ldots,v_n\).
proof:
  Apply the coordinate formula for the exterior derivative of \(F^\*\omega\)
  on the product \(U\times[0,1]\).  The coordinate vector fields
  \(\partial_t,v_0,\ldots,v_n\) commute, so the bracket terms vanish; solving
  the alternating sum for the \(\partial_t\)-derivative gives the formula.
-/
theorem convexOpenStraightLinePullbackPoint_hasDerivWithinAt_productCartan
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt
        (fun τ : ℝ ↦
          convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x τ v)
        ((extDerivWithin
            (fun y : E ↦
              convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
                (y, t))
            (U : Set E) (x : E) v) +
          convexOpenStraightLineTotalExteriorDerivativeTerm (E := E) U x₀ n omega x t v)
        (Set.Icc (0 : ℝ) 1) t := by
  let eta : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
    convexOpenStraightLineTotalPullbackForm (E := E) U x₀ n omega
  have heta : ContDiffOn ℝ 1 eta ((U : Set E) ×ˢ Set.Icc (0 : ℝ) 1) :=
    (contDiffOn_convexOpenStraightLineTotalPullbackForm
      (E := E) U hconvex x₀ n omega).of_le (by simp)
  have hcartan :=
    hasDerivWithinAt_modelForm_product_time_cartan
      (E := E) (F := ℝ)
      (s := (U : Set E)) U.2 U.2.uniqueDiffOn eta heta
      (x : E) x.2 ht v
  have hbase :
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x τ v =
          ((eta ((x : E), τ)).compContinuousLinearMap
            (ContinuousLinearMap.inl ℝ E ℝ)) v := by
    intro τ hτ
    exact
      (convexOpenStraightLineTotalPullbackForm_baseTangent
        (E := E) U hconvex x₀ n omega x v hτ).symm
  have hcontract :
      EqOn
        (fun y : E ↦
          ((eta (y, t)).curryLeft ((0 : E), (1 : ℝ))).compContinuousLinearMap
            (ContinuousLinearMap.inl ℝ E ℝ))
        (fun y : E ↦
          convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega (y, t))
        (U : Set E) :=
    convexOpenStraightLineTotalPullbackForm_timeContraction_eq_integrandExtension
      (E := E) U hconvex x₀ n omega ht
  have hcontract_ext :
      extDerivWithin
          (fun y : E ↦
            ((eta (y, t)).curryLeft ((0 : E), (1 : ℝ))).compContinuousLinearMap
              (ContinuousLinearMap.inl ℝ E ℝ))
          (U : Set E) (x : E) =
        extDerivWithin
          (fun y : E ↦
            convexOpenPoincareHomotopyIntegrandExtension (E := E) U hconvex x₀ n omega
              (y, t))
          (U : Set E) (x : E) :=
    extDerivWithin_congr' hcontract x.2
  exact
    (hcartan.congr_of_mem hbase ht).congr_deriv (by
      dsimp [eta, convexOpenStraightLineTotalExteriorDerivativeTerm] at hcontract_ext ⊢
      rw [hcontract_ext]
      simp [convexOpenStraightLineTimeBaseTangent])

/--
%%handwave
name:
  Naturality of the total exterior derivative
statement:
  For the total straight-line homotopy \(F(x,t)=(1-t)x_0+tx\), the exterior
  derivative of the pulled-back form \(F^\*\omega\), evaluated on
  \(\partial_t,v_0,\ldots,v_n\), equals the insertion term
  \(\iota_{\partial_tF}F^\*(d\omega)(v_0,\ldots,v_n)\).
proof:
  This is the naturality of the exterior derivative under pullback, together
  with the facts that \(dF(\partial_t)=x-x_0\) and \(dF(v_i)=t v_i\).
-/
theorem convexOpenStraightLineTotalExteriorDerivativeTerm_eq_deRhamTerm
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    convexOpenStraightLineTotalExteriorDerivativeTerm (E := E) U x₀ n omega x t v =
      convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ (n + 1)
        (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1) omega)
        x t v := by
  let coeff : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E) U (n + 1)
      (fun y ↦ smoothFormModelCoeff (E := E) U (n + 1) omega y)
  let τ : Set.Icc (0 : ℝ) 1 := Set.projIcc (0 : ℝ) 1 zero_le_one t
  let y : U := convexOpenStraightLineHomotopy (E := E) U hconvex x₀ τ x
  have hτ : (τ : ℝ) = t := by
    have hproj :
        Set.projIcc (0 : ℝ) 1 zero_le_one t = ⟨t, ht⟩ :=
      Set.projIcc_of_mem zero_le_one ht
    exact congrArg Subtype.val hproj
  have hline :
      convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t) =
        (y : E) := by
    simp [y, τ, convexOpenStraightLineTotalHomotopy, convexOpenStraightLineHomotopy,
      AffineMap.lineMap_apply_module', hτ, add_comm]
  have hmodel :
      extDerivWithin coeff (U : Set E)
          (convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t)) =
        ((deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1) omega).toFun y :
          E [⋀^Fin (n + 2)]→L[ℝ] ℝ) := by
    rw [hline]
    exact (deRhamDifferential_modelOpen_toFun (E := E) U (n + 1) omega y).symm
  have htangent :
      (convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) ((x : E), t)) ∘
          convexOpenStraightLineTimeBaseTangent (E := E) v =
        Matrix.vecCons ((x : E) - (x₀ : E)) (fun i : Fin (n + 1) ↦ t • v i) :=
    convexOpenStraightLineTotalFDeriv_comp_timeBaseTangent
      (E := E) (x₀ : E) (x : E) t (n + 1) v
  calc
    convexOpenStraightLineTotalExteriorDerivativeTerm (E := E) U x₀ n omega x t v =
        ((extDerivWithin coeff
          (U : Set E)
          (convexOpenStraightLineTotalHomotopy (E := E) (x₀ : E) ((x : E), t))
        ).compContinuousLinearMap
          (convexOpenStraightLineTotalFDeriv (E := E) (x₀ : E) ((x : E), t)))
        (convexOpenStraightLineTimeBaseTangent (E := E) v) := by
          simpa [coeff] using
            convexOpenStraightLineTotalExteriorDerivativeTerm_eq_pullback_extDerivWithin
              (E := E) U hconvex x₀ n omega x v ht
    _ =
      convexOpenPoincareHomotopyIntegrand (E := E) U hconvex x₀ (n + 1)
        (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1) omega)
        x t v := by
      dsimp [convexOpenPoincareHomotopyIntegrand]
      simp only [τ, hτ]
      rw [hmodel, htangent]
      rfl

/--
%%handwave
name:
  Affine Cartan formula as a within-derivative
statement:
  For the straight-line homotopy \(H_t(x)=(1-t)x_0+tx\) on a convex open set,
  the scalar function \(t\mapsto H_t^\*\omega(v_0,\ldots,v_n)\) has
  within-derivative
  \[
    d_x(\iota_{\partial_tH}H_t^\*\omega)+
    \iota_{\partial_tH}H_t^\*d\omega .
  \]
proof:
  Combine [the product formula that solves the exterior derivative of the total pullback for the time derivative](lean:JJMath.Manifold.convexOpenStraightLinePullbackPoint_hasDerivWithinAt_productCartan) with [the identification of the total exterior derivative with the insertion of \(d\omega\)](lean:JJMath.Manifold.convexOpenStraightLineTotalExteriorDerivativeTerm_eq_deRhamTerm).
-/
theorem convexOpenStraightLinePullbackPoint_hasDerivWithinAt_cartanDensity
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt
        (fun τ : ℝ ↦
          convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x τ v)
        (convexOpenCartanHomotopyDensity (E := E) U hconvex x₀ n omega x t v)
        (Set.Icc (0 : ℝ) 1) t := by
  have hproduct :=
    convexOpenStraightLinePullbackPoint_hasDerivWithinAt_productCartan
      (E := E) U hconvex x₀ n omega x v ht
  have htotal :=
    convexOpenStraightLineTotalExteriorDerivativeTerm_eq_deRhamTerm
      (E := E) U hconvex x₀ n omega x v ht
  rw [htotal] at hproduct
  simpa [convexOpenCartanHomotopyDensity] using hproduct

/--
%%handwave
name:
  Affine Cartan formula for the straight-line contraction
statement:
  For the straight-line homotopy \(H_t(x)=(1-t)x_0+tx\) on a convex open set,
  the within-derivative in \(t\) of the time-\(t\) pullback of a smooth
  positive-degree form is
  \[
    d_x(\iota_{\partial_tH}H_t^\*\omega)+
    \iota_{\partial_tH}H_t^\*d\omega .
  \]
proof:
  This follows from [the statement that the straight-line pullback has within-derivative equal to the Cartan density](lean:JJMath.Manifold.convexOpenStraightLinePullbackPoint_hasDerivWithinAt_cartanDensity), because the interval \([0,1]\) has unique tangent directions at each of its points.
-/
theorem convexOpenStraightLineHomotopy_affine_cartan_formula
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    derivWithin
        (fun τ : ℝ ↦
          convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x τ v)
        (Set.Icc (0 : ℝ) 1) t =
      convexOpenCartanHomotopyDensity (E := E) U hconvex x₀ n omega x t v := by
  exact
    (convexOpenStraightLinePullbackPoint_hasDerivWithinAt_cartanDensity
      (E := E) U hconvex x₀ n omega x v ht).derivWithin
      (uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt ht)

/--
%%handwave
name:
  Cartan density is the time derivative of the pullback
statement:
  For \(t\in[0,1]\), the Cartan density of the straight-line homotopy equals
  the within-derivative in \(t\) of the time-\(t\) pullback \(H_t^\*\omega\).
proof:
  This is Cartan's infinitesimal homotopy formula
  \[
    \partial_t(H_t^\*\omega)
      =d\,\iota_{\partial_tH}H_t^\*\omega+
       \iota_{\partial_tH}H_t^\*d\omega.
  \]
  In the affine straight-line case, the required vector fields commute and the
  identity follows from the coordinate formula for the exterior derivative.
-/
theorem convexOpenCartanHomotopyDensity_eq_time_derivative
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    convexOpenCartanHomotopyDensity (E := E) U hconvex x₀ n omega x t v =
      derivWithin
        (fun τ : ℝ ↦
          convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x τ v)
        (Set.Icc (0 : ℝ) 1) t := by
  exact
    (convexOpenStraightLineHomotopy_affine_cartan_formula
      (E := E) U hconvex x₀ n omega x v ht).symm

/--
%%handwave
name:
  Cartan integrand as the time derivative
statement:
  For the straight-line homotopy, the value of \(dK\omega+Kd\omega\) at
  \(x\) and on a tangent tuple \(v\) is the integral over \(t\in[0,1]\) of the
  within-derivative in \(t\) of the time-\(t\) pullback \(H_t^\*\omega\).
proof:
  This is Cartan's homotopy formula before applying the fundamental theorem of
  calculus: differentiating \(H_t^\*\omega\) in \(t\) gives
  \(d\,\iota_{\partial_tH}H_t^\*\omega+
  \iota_{\partial_tH}H_t^\*d\omega\).
-/
theorem deRham_convex_open_homotopy_linearMap_cartan_add_apply_eq_integral_time_derivative
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    ((
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) +
        convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
    ∫ t in (0 : ℝ)..1,
      derivWithin
        (fun τ : ℝ ↦
          convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x τ v)
        (Set.Icc (0 : ℝ) 1) t := by
  calc
    ((
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) +
        convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v
        = ∫ t in (0 : ℝ)..1,
            convexOpenCartanHomotopyDensity (E := E) U hconvex x₀ n omega x t v := by
          exact
            deRham_convex_open_homotopy_linearMap_cartan_add_apply_eq_integral_density
              (E := E) U hconvex x₀ n omega x v
    _ = ∫ t in (0 : ℝ)..1,
        derivWithin
          (fun τ : ℝ ↦
            convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x τ v)
          (Set.Icc (0 : ℝ) 1) t := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact
            convexOpenCartanHomotopyDensity_eq_time_derivative
              (E := E) U hconvex x₀ n omega x v
              (by simpa [Set.uIcc_of_le zero_le_one] using ht)

/--
%%handwave
name:
  Cartan identity for the straight-line operator on tangent tuples
statement:
  At each point and on each tuple of tangent vectors, the straight-line
  homotopy operator satisfies \(dK\omega+Kd\omega=\omega\).
proof:
  Expand the exterior derivative of the integral formula for \(K\omega\).
  Differentiation in the homotopy parameter gives the endpoint contribution,
  and the remaining terms are exactly canceled by \(K(d\omega)\).
-/
theorem deRham_convex_open_homotopy_linearMap_cartan_add_apply
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) (v : Fin (n + 1) → E) :
    ((
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) +
        convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
    (omega.toFun x : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v := by
  let f : ℝ → ℝ := fun t ↦
    convexOpenStraightLinePullbackPoint (E := E) U hconvex x₀ n omega x t v
  calc
    ((
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) +
        convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v
        = ∫ t in (0 : ℝ)..1, derivWithin f (Set.Icc (0 : ℝ) 1) t := by
          simpa [f] using
            deRham_convex_open_homotopy_linearMap_cartan_add_apply_eq_integral_time_derivative
              (E := E) U hconvex x₀ n omega x v
    _ = f 1 - f 0 := by
          exact intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
            (contDiffOn_convexOpenStraightLinePullbackPoint_apply_Icc
              (E := E) U hconvex x₀ n omega x v)
            zero_le_one
    _ = (omega.toFun x : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) v := by
          exact convexOpenStraightLinePullbackPoint_endpoint_sub_apply
            (E := E) U hconvex x₀ n omega x v

/--
%%handwave
name:
  Pointwise Cartan identity for the straight-line operator
statement:
  At each point of a convex open set, the straight-line homotopy operator
  satisfies the pointwise identity \(dK\omega+Kd\omega=\omega\) on
  positive-degree forms.
proof:
  In model coordinates, differentiate the integral formula for \(K\omega\).
  The \(x\)-derivative terms combine with \(K(d\omega)\), while the
  \(t\)-derivative term integrates to the endpoint contribution
  \(H_1^\*\omega-H_0^\*\omega\).  The first endpoint is \(\omega\), and the
  constant endpoint vanishes in positive degree.
-/
theorem deRham_convex_open_homotopy_linearMap_cartan_add_toFun
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))
    (x : U) :
    ((
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
          (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) +
        convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega)).toFun x :
      E [⋀^Fin (n + 1)]→L[ℝ] ℝ) =
    (omega.toFun x : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) := by
  ext v
  exact deRham_convex_open_homotopy_linearMap_cartan_add_apply
    (E := E) U hconvex x₀ n omega x v

/--
%%handwave
name:
  Cartan homotopy identity for the straight-line operator
statement:
  For the straight-line homotopy operator on a convex open set,
  \(dK\omega+Kd\omega=\omega\) on positive-degree forms.
proof:
  Apply Cartan's homotopy formula to
  \(H_t(x)=(1-t)x_0+tx\).  The endpoint \(H_1\) is the identity, and the
  endpoint \(H_0\) is constant; the pullback by the constant endpoint vanishes
  on positive-degree forms.
-/
theorem deRham_convex_open_homotopy_linearMap_cartan_add
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
        (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) +
      convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
        (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
          omega) =
    omega := by
  apply DifferentialForm.ext
  intro x
  exact deRham_convex_open_homotopy_linearMap_cartan_add_toFun
    (E := E) U hconvex x₀ n omega x

/--
%%handwave
name:
  Cartan formula for the concrete convex homotopy operator
statement:
  The linear map defined by the straight-line integral satisfies
  \(dK\omega=\omega-Kd\omega\) on positive-degree forms.
proof:
  Apply Cartan's homotopy formula to the smooth straight-line homotopy
  \(H_t(x)=(1-t)x_0+tx\).  The endpoint at \(t=1\) is the identity, and the
  endpoint at \(t=0\) is constant, hence has zero pullback on positive-degree
  forms.
-/
theorem deRham_convex_open_homotopy_linearMap_formula
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
        (convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n omega) =
      omega -
        convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega) := by
  rw [eq_sub_iff_add_eq]
  exact deRham_convex_open_homotopy_linearMap_cartan_add (E := E) U hconvex x₀ n omega

/--
%%handwave
name:
  Existence of the convex homotopy operator
statement:
  On a convex open set \(U\) with base point \(x_0\), there is a family of
  linear maps \(K:\Omega^{n+1}(U)\to\Omega^n(U)\) such that
  \(dK\omega=\omega-Kd\omega\) for all positive-degree forms \(\omega\).
proof:
  The operator is
  \(K\omega=\int_0^1 \iota_{\partial_t H_t}H_t^\*\omega\,dt\), where
  \(H_t(x)=(1-t)x_0+tx\).  Cartan's homotopy formula gives
  \(dK+Kd=H_1^\*-H_0^\*\); here \(H_1\) is the identity and the pullback by
  the constant map \(H_0\) vanishes on positive-degree forms.
-/
theorem exists_convexOpenPoincareHomotopyOperator
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U) :
    ∃ K : (n : ℕ) →
        SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1) →ₗ[ℝ]
          SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n,
      ∀ (n : ℕ) (omega :
        SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)),
        deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
            (K n omega) =
          omega -
            K (n + 1)
              (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ)
                (n + 1) omega) := by
  refine ⟨fun n ↦ convexOpenPoincareHomotopyLinearMap (E := E) U hconvex x₀ n, ?_⟩
  intro n omega
  exact deRham_convex_open_homotopy_linearMap_formula (E := E) U hconvex x₀ n omega

/--
%%handwave
name:
  Convex homotopy operator
statement:
  For a convex open set with a chosen base point, choose the standard
  straight-line homotopy operator \(K:\Omega^{n+1}(U)\to\Omega^n(U)\).
proof:
  Choose an operator supplied by the existence theorem for the straight-line
  homotopy operator.
-/
def convexOpenPoincareHomotopyOperator
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ) :
    SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1) →ₗ[ℝ]
      SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n :=
  Classical.choose
    (exists_convexOpenPoincareHomotopyOperator (E := E) U hconvex x₀) n

/--
%%handwave
name:
  Cartan formula for the convex homotopy operator
statement:
  The chosen straight-line homotopy operator satisfies
  \(dK\omega=\omega-Kd\omega\) on positive-degree forms.
proof:
  This is the defining property of the chosen operator, supplied by the
  existence theorem for the homotopy operator.
-/
theorem deRham_convex_open_homotopy_operator_formula
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) :
    deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
        (convexOpenPoincareHomotopyOperator (E := E) U hconvex x₀ n omega) =
      omega -
        convexOpenPoincareHomotopyOperator (E := E) U hconvex x₀ (n + 1)
          (deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)
            omega) := by
  exact
    (Classical.choose_spec
      (exists_convexOpenPoincareHomotopyOperator (E := E) U hconvex x₀)) n omega

/--
%%handwave
name:
  Closed forms are hit by the convex homotopy operator
statement:
  If \(\omega\) is a closed smooth \((n+1)\)-form on a convex open set, then
  \(dK\omega=\omega\).
proof:
  In the homotopy identity \(dK\omega=\omega-Kd\omega\), the last term
  vanishes because \(d\omega=0\).
-/
theorem deRham_convex_open_homotopy_operator_d_eq_of_closed
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega :
      DeRhamClosedForms (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)) :
    deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n
        (convexOpenPoincareHomotopyOperator (E := E) U hconvex x₀ n
          (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1))) =
      (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) := by
  rw [deRham_convex_open_homotopy_operator_formula]
  rw [omega.2]
  simp

/--
%%handwave
name:
  Homotopy operator primitive on a convex open set
statement:
  Let \(U\) be a convex open subset of a finite-dimensional real vector space
  and let \(x_0\in U\).  Every closed smooth \((n+1)\)-form on \(U\) has a
  smooth \(n\)-form primitive obtained from the straight-line homotopy to
  \(x_0\).
proof:
  For the contraction \(H_t(x)=(1-t)x_0+tx\), define
  \(K\omega=\int_0^1 \iota_{\partial_t H_t}H_t^\*\omega\,dt\).  Cartan's
  homotopy formula gives \(dK+Kd=\mathrm{id}-\mathrm{ev}_{x_0}^\*\), and the
  final term is zero in positive degree.
-/
theorem deRham_convex_open_closed_succ_form_has_primitive
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (n : ℕ)
    (omega :
      DeRhamClosedForms (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)) :
    ∃ eta : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ n,
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) n eta =
        (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) := by
  refine ⟨convexOpenPoincareHomotopyOperator (E := E) U hconvex x₀ n
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)), ?_⟩
  exact deRham_convex_open_homotopy_operator_d_eq_of_closed
    (E := E) U hconvex x₀ n omega

/--
%%handwave
name:
  Closed zero-forms on convex opens are constant
statement:
  A closed smooth zero-form on a convex open subset of a finite-dimensional
  real vector space is the constant zero-form determined by its value at any
  chosen point.
proof:
  Identify the zero-form with its scalar coefficient function.  The coordinate
  formula for the exterior derivative says that this function has zero
  Fréchet derivative.  The mean-value theorem on a convex set then makes the
  coefficient constant.
-/
theorem deRham_convex_open_closed_zero_form_eq_constant
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (omega :
      DeRhamClosedForms (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) 0) :
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ 0) =
      smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, E))
        (smoothRealConstantFunction (I0 := 𝓘(ℝ, E))
          ((omega.1.toFun x₀) (fun i : Fin 0 => nomatch i))) := by
  let eta : E → E [⋀^Fin 0]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E) U 0
      (fun x ↦ smoothFormModelCoeff (E := E) U 0 omega.1 x)
  let emptyTuple : Fin 0 → E := fun i => nomatch i
  let f : E → ℝ := fun y =>
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).symm (eta y)
  have heta_smooth : ContDiffOn ℝ ∞ eta (U : Set E) :=
    contDiffOn_smoothFormModelCoeff_modelOpen (E := E) U 0 omega.1
  have hf_smooth : ContDiffOn ℝ ∞ f (U : Set E) := by
    exact
      (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).symm.contDiff.comp_contDiffOn
        (by simpa [eta] using heta_smooth)
  have heta_eq : eta = fun y =>
      ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f y) := by
    funext y
    ext v
    simpa [f] using (congrArg (fun A : E [⋀^Fin 0]→L[ℝ] ℝ => A v)
      ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).apply_symm_apply
        (eta y))).symm
  have hfderiv : ∀ y ∈ (U : Set E), fderivWithin ℝ f (U : Set E) y = 0 := by
    intro y hy
    let yU : U := ⟨y, hy⟩
    have hd := deRhamDifferential_modelOpen_toFun
      (E := E) U 0 omega.1 yU
    rw [omega.2] at hd
    have hext : extDerivWithin eta (U : Set E) y = 0 := by
      simpa [eta, yU] using hd.symm
    rw [heta_eq] at hext
    have hformula :
        extDerivWithin
            (fun z => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f z))
            (U : Set E) y =
          ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
            (fderivWithin ℝ f (U : Set E) y) :=
      extDerivWithin_constOfIsEmpty
        (𝕜 := ℝ) (E := E) (F := ℝ) f (U.2.uniqueDiffOn y hy)
    have hext' :
        ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
            (fderivWithin ℝ f (U : Set E) y) = 0 :=
      hformula.symm.trans hext
    apply ContinuousLinearMap.ext
    intro v
    let q : Fin 1 → E := fun _ => v
    have hv := congrArg (fun A : E [⋀^Fin 1]→L[ℝ] ℝ => A q) hext'
    simpa [q] using hv
  have hf_const : ∀ y ∈ (U : Set E), f y = f (x₀ : E) := by
    intro y hy
    exact hconvex.is_const_of_fderivWithin_eq_zero
      (hf_smooth.differentiableOn (by simp))
      hfderiv hy x₀.2
  apply DifferentialForm.ext
  intro y
  ext v
  have hyf : f (y : E) = f (x₀ : E) := hf_const y y.2
  rw [show v = emptyTuple from Subsingleton.elim _ _]
  change (omega.1.toFun y) emptyTuple = (omega.1.toFun x₀) emptyTuple
  rw [show emptyTuple = 0 from Subsingleton.elim _ _]
  simpa [eta, f, emptyTuple, modelOpenFormCoeffExtension, y.2, x₀.2,
    smoothFormModelCoeff] using hyf

/--
%%handwave
name:
  Degree-zero classes on convex opens are constant classes
statement:
  Every degree-zero real de Rham cohomology class on a nonempty convex open
  subset of a finite-dimensional real vector space is represented by a real
  constant.
proof:
  Choose a closed zero-form representing the class.  By [closed zero-forms on convex opens are constant](lean:JJMath.Manifold.deRham_convex_open_closed_zero_form_eq_constant), it equals the constant zero-form determined by its value at the chosen base point, hence their quotient classes agree.
-/
theorem deRham_convex_open_H0_eq_constant
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (x₀ : U)
    (alpha : DeRhamCohomology (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) 0) :
    ∃ c : ℝ,
      alpha = deRhamConstantH0Class (I0 := 𝓘(ℝ, E)) (M0 := U) c := by
  induction alpha using Submodule.Quotient.induction_on with
  | _ omega =>
      let c : ℝ := (omega.1.toFun x₀) (fun i : Fin 0 => nomatch i)
      refine ⟨c, ?_⟩
      apply congrArg
        (DeRhamExactClosedForms (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) 0).mkQ
      apply Subtype.ext
      exact deRham_convex_open_closed_zero_form_eq_constant
        (E := E) U hconvex x₀ omega

/--
%%handwave
name:
  Poincare lemma on convex model opens
statement:
  On a nonempty convex open subset of a finite-dimensional real vector space,
  every closed positive-degree smooth differential form is exact.
proof:
  Choose a point \(x_0\) in the convex open set and use the straight-line
  contraction \(H_t(x)=x_0+t(x-x_0)\).  The standard homotopy operator
  \(K\omega=\int_0^1 \iota_{\partial_t H_t}H_t^\*\omega\,dt\) satisfies
  \(dK+Kd=\mathrm{id}-\mathrm{ev}_{x_0}^\*\).  In positive degree the
  constant-pullback term vanishes, so a closed form is \(d(K\omega)\).
tags:
  milestone
-/
theorem deRham_poincareLemma_convex_open_exact
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (hne : (U : Set E).Nonempty)
    (n : ℕ)
    (omega :
      DeRhamClosedForms (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)) :
    (omega : SmoothForms (I := 𝓘(ℝ, E)) (M := U) ℝ (n + 1)) ∈
      DeRhamExactForms (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1) := by
  rcases hne with ⟨x₀, hx₀⟩
  rcases deRham_convex_open_closed_succ_form_has_primitive
      (E := E) U hconvex ⟨x₀, hx₀⟩ n omega with
    ⟨eta, heta⟩
  rw [DeRhamExactForms]
  exact ⟨eta, heta⟩

/--
%%handwave
name:
  Poincare vanishing on convex model opens
statement:
  On a nonempty convex open subset of a finite-dimensional real vector space,
  positive-degree real de Rham cohomology is a singleton.
proof:
  Apply [the Poincare lemma that every closed positive-degree form on a convex open set is exact](lean:JJMath.Manifold.deRham_poincareLemma_convex_open_exact), then pass to the quotient by exact forms.
-/
theorem deRham_poincareLemma_convex_open
    (U : TopologicalSpace.Opens E)
    (hconvex : Convex ℝ (U : Set E)) (hne : (U : Set E).Nonempty)
    (n : ℕ) :
    Subsingleton
      (DeRhamCohomology (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n + 1)) :=
  deRhamCohomology_subsingleton_of_closedForms_succ_le_exactForms
    (I := 𝓘(ℝ, E)) (M := U) (A := ℝ) (n := n)
    (fun omega ↦
      deRham_poincareLemma_convex_open_exact
        (E := E) U hconvex hne n omega)

end ConvexModel

section Diffeomorphism

variable {E₁ : Type v} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H₁ : Type w} [TopologicalSpace H₁]
variable {M₁ : Type m} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
variable {E₂ : Type v'} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable {H₂ : Type w'} [TopologicalSpace H₂]
variable {M₂ : Type m'} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]

/--
%%handwave
name:
  Coordinate smoothness of pullback along a diffeomorphism
statement:
  In every source chart, the coordinate representative of the pullback of a
  smooth form along a diffeomorphism is smooth on the chart image.
proof:
  Near a point of the source chart, choose a target chart around its image.
  The coordinate representative is the target coordinate representative of the
  form, composed with the chart expression of the diffeomorphism and pulled
  back by the derivative of that chart expression.
-/
theorem contDiffOn_coordinateExpression_pullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₂) (M := M₂) ℝ n)
    (e : OpenPartialHomeomorph M₁ H₁) (he : e ∈ atlas H₁ M₁) :
    ContDiffOn ℝ ∞
      (coordinateExpression (I := I₁) (F := ℝ) (n := n)
        (fun x ↦
          (omega.toFun (φ x)).compContinuousLinearMap
            (mfderiv I₁ I₂ φ x)) e)
      (e.extend I₁).target := by
  exact
    contDiffOn_coordinateExpression_smoothDifferentialFormPullbackDiffeomorph
      I₁ I₂ φ omega e he

/--
%%handwave
name:
  Pullback of a smooth form along a diffeomorphism
statement:
  Pulling a smooth differential form back along a smooth diffeomorphism gives
  a smooth differential form.
proof:
  In local charts this is the usual smoothness of the coordinate expression of
  \(\varphi^\*\omega\), obtained by composing the coordinate expression of
  \(\omega\) with the chart expression of \(\varphi\) and the derivative of
  that chart expression.
-/
theorem isContMDiffForm_pullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₂) (M := M₂) ℝ n) :
    IsContMDiffForm (I := I₁) (M := M₁) (F := ℝ) (n := n) ∞
      (fun x ↦
        (omega.toFun (φ x)).compContinuousLinearMap
          (mfderiv I₁ I₂ φ x)) := by
  intro e he
  exact contDiffOn_coordinateExpression_pullbackDiffeomorph I₁ I₂ φ omega e he

/-- Pull back a smooth form along a diffeomorphism. -/
abbrev smoothFormPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₂) (M := M₂) ℝ n) :
    SmoothForms (I := I₁) (M := M₁) ℝ n :=
  smoothDifferentialFormPullbackDiffeomorph I₁ I₂ φ omega

/-- Pullback of smooth forms along a diffeomorphism as a linear map. -/
def smoothFormsPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (n : ℕ) :
    SmoothForms (I := I₂) (M := M₂) ℝ n →ₗ[ℝ]
      SmoothForms (I := I₁) (M := M₁) ℝ n where
  toFun := smoothFormPullbackDiffeomorph I₁ I₂ φ
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
  Exterior derivative naturality on tangent tuples
statement:
  At each point and on each tuple of tangent vectors, the exterior derivative
  of the pullback of a form along a diffeomorphism equals the pullback of the
  exterior derivative.
proof:
  Write both sides in local coordinates.  The equality is the standard
  alternating chain-rule formula for the model-space exterior derivative.
-/
theorem exteriorDerivative_smoothFormPullbackDiffeomorph_apply
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₂) (M := M₂) ℝ n)
    (x : M₁) (v : Fin (n + 1) → TangentSpace I₁ x) :
    ((exteriorDerivative (I := I₁) (r := ∞)
        (smoothFormPullbackDiffeomorph I₁ I₂ φ omega)).toFun x :
      TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) v =
    ((smoothFormPullbackDiffeomorph I₁ I₂ φ
        (exteriorDerivative (I := I₂) (r := ∞) omega)).toFun x :
      TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) v := by
  exact
    exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph_apply
      I₁ I₂ φ omega x v

/--
%%handwave
name:
  Pointwise naturality of exterior derivative under diffeomorphism pullback
statement:
  At each point, the exterior derivative of the pullback of a smooth form
  along a diffeomorphism equals the pullback of the exterior derivative.
proof:
  In charts this is the model-space identity
  \(d(\varphi^\*\omega)=\varphi^\*(d\omega)\), obtained from the chain rule
  and alternation.
-/
theorem exteriorDerivative_smoothFormPullbackDiffeomorph_toFun
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₂) (M := M₂) ℝ n) (x : M₁) :
    ((exteriorDerivative (I := I₁) (r := ∞)
        (smoothFormPullbackDiffeomorph I₁ I₂ φ omega)).toFun x :
      TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) =
    ((smoothFormPullbackDiffeomorph I₁ I₂ φ
        (exteriorDerivative (I := I₂) (r := ∞) omega)).toFun x :
      TangentSpace I₁ x [⋀^Fin (n + 1)]→L[ℝ] ℝ) := by
  ext v
  exact exteriorDerivative_smoothFormPullbackDiffeomorph_apply I₁ I₂ φ omega x v

/--
%%handwave
name:
  Exterior derivative is natural for diffeomorphism pullback
statement:
  The exterior derivative of the pullback of a smooth form along a
  diffeomorphism is the pullback of its exterior derivative.
proof:
  In local coordinates this is the standard model-space identity
  \(d(\varphi^\*\omega)=\varphi^\*(d\omega)\), together with the chain rule.
-/
theorem exteriorDerivative_smoothFormPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₂) (M := M₂) ℝ n) :
    exteriorDerivative (I := I₁) (r := ∞)
        (smoothFormPullbackDiffeomorph I₁ I₂ φ omega) =
      smoothFormPullbackDiffeomorph I₁ I₂ φ
        (exteriorDerivative (I := I₂) (r := ∞) omega) := by
  apply DifferentialForm.ext
  intro x
  exact exteriorDerivative_smoothFormPullbackDiffeomorph_toFun I₁ I₂ φ omega x

/--
%%handwave
name:
  Pullback commutes with the exterior derivative
statement:
  Pullback of smooth forms along a diffeomorphism commutes with the de Rham
  differential.
proof:
  This is the standard naturality of exterior derivative under smooth
  pullback, checked in local coordinates.
-/
theorem deRhamDifferential_smoothFormsPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₂) (M := M₂) ℝ n) :
    deRhamDifferential (I := I₁) (M := M₁) (A := ℝ) n
        (smoothFormsPullbackDiffeomorph I₁ I₂ φ n omega) =
      smoothFormsPullbackDiffeomorph I₁ I₂ φ (n + 1)
        (deRhamDifferential (I := I₂) (M := M₂) (A := ℝ) n omega) := by
  simpa [deRhamDifferential] using
    exteriorDerivative_smoothFormPullbackDiffeomorph I₁ I₂ φ omega

/--
%%handwave
name:
  Pullback by inverse diffeomorphisms is the identity on smooth forms
statement:
  Pulling a smooth form first along a diffeomorphism and then along its inverse
  gives the original form.
proof:
  At each point this follows from the chain rule and the identity
  \(\varphi\circ\varphi^{-1}=\mathrm{id}\).
-/
theorem smoothFormsPullbackDiffeomorph_symm_comp
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₂) (M := M₂) ℝ n) :
    smoothFormsPullbackDiffeomorph I₂ I₁ φ.symm n
        (smoothFormsPullbackDiffeomorph I₁ I₂ φ n omega) =
      omega := by
  ext x v
  have hφ :
      MDifferentiableAt I₁ I₂ φ (φ.symm x) :=
    φ.contMDiffAt.mdifferentiableAt (by simp)
  have hφsymm :
      MDifferentiableAt I₂ I₁ φ.symm x :=
    φ.symm.contMDiffAt.mdifferentiableAt (by simp)
  have hderiv :
      mfderiv I₂ I₂ (φ ∘ φ.symm) x =
        (mfderiv I₁ I₂ φ (φ.symm x)).comp
          (mfderiv I₂ I₁ φ.symm x) :=
    mfderiv_comp x hφ hφsymm
  have hid :
      mfderiv I₂ I₂ (φ ∘ φ.symm) x =
        ContinuousLinearMap.id ℝ (TangentSpace I₂ x) := by
    have hfun : φ ∘ φ.symm = (_root_.id : M₂ → M₂) := by
      funext y
      exact φ.apply_symm_apply y
    rw [hfun]
    exact mfderiv_id
  have hcomp :
      (mfderiv I₁ I₂ φ (φ.symm x)).comp
          (mfderiv I₂ I₁ φ.symm x) =
        ContinuousLinearMap.id ℝ (TangentSpace I₂ x) := by
    exact hderiv ▸ hid
  have hcomp_apply :
      ∀ w : TangentSpace I₂ x,
        mfderiv I₁ I₂ φ (φ.symm x) (mfderiv I₂ I₁ φ.symm x w) = w := by
    intro w
    have hw := congrArg (fun L : TangentSpace I₂ x →L[ℝ] TangentSpace I₂ x => L w) hcomp
    simpa using hw
  change
    (((omega.toFun (φ (φ.symm x))).compContinuousLinearMap
          (mfderiv I₁ I₂ φ (φ.symm x))).compContinuousLinearMap
        (mfderiv I₂ I₁ φ.symm x)) v =
      omega.toFun x v
  rw [φ.apply_symm_apply x]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr
  funext i
  exact hcomp_apply (v i)

/--
%%handwave
name:
  Pullback by inverse diffeomorphisms is the identity on smooth forms, reversed
statement:
  Pulling a smooth form first along the inverse diffeomorphism and then along
  the diffeomorphism gives the original form.
proof:
  At each point this follows from the chain rule and the identity
  \(\varphi^{-1}\circ\varphi=\mathrm{id}\).
-/
theorem smoothFormsPullbackDiffeomorph_comp_symm
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : SmoothForms (I := I₁) (M := M₁) ℝ n) :
    smoothFormsPullbackDiffeomorph I₁ I₂ φ n
        (smoothFormsPullbackDiffeomorph I₂ I₁ φ.symm n omega) =
      omega := by
  ext x v
  have hφsymm :
      MDifferentiableAt I₂ I₁ φ.symm (φ x) :=
    φ.symm.contMDiffAt.mdifferentiableAt (by simp)
  have hφ :
      MDifferentiableAt I₁ I₂ φ x :=
    φ.contMDiffAt.mdifferentiableAt (by simp)
  have hderiv :
      mfderiv I₁ I₁ (φ.symm ∘ φ) x =
        (mfderiv I₂ I₁ φ.symm (φ x)).comp
          (mfderiv I₁ I₂ φ x) :=
    mfderiv_comp x hφsymm hφ
  have hid :
      mfderiv I₁ I₁ (φ.symm ∘ φ) x =
        ContinuousLinearMap.id ℝ (TangentSpace I₁ x) := by
    have hfun : φ.symm ∘ φ = (_root_.id : M₁ → M₁) := by
      funext y
      exact φ.symm_apply_apply y
    rw [hfun]
    exact mfderiv_id
  have hcomp :
      (mfderiv I₂ I₁ φ.symm (φ x)).comp
          (mfderiv I₁ I₂ φ x) =
        ContinuousLinearMap.id ℝ (TangentSpace I₁ x) := by
    exact hderiv ▸ hid
  have hcomp_apply :
      ∀ w : TangentSpace I₁ x,
        mfderiv I₂ I₁ φ.symm (φ x) (mfderiv I₁ I₂ φ x w) = w := by
    intro w
    have hw := congrArg (fun L : TangentSpace I₁ x →L[ℝ] TangentSpace I₁ x => L w) hcomp
    simpa using hw
  change
    (((omega.toFun (φ.symm (φ x))).compContinuousLinearMap
          (mfderiv I₂ I₁ φ.symm (φ x))).compContinuousLinearMap
        (mfderiv I₁ I₂ φ x)) v =
      omega.toFun x v
  rw [φ.symm_apply_apply x]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr
  funext i
  exact hcomp_apply (v i)

/-- Pullback along a diffeomorphism sends closed forms to closed forms. -/
def deRhamClosedFormsPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (n : ℕ) :
    DeRhamClosedForms (I := I₂) (M := M₂) (A := ℝ) n →ₗ[ℝ]
      DeRhamClosedForms (I := I₁) (M := M₁) (A := ℝ) n where
  toFun := fun omega ↦
    ⟨smoothFormsPullbackDiffeomorph I₁ I₂ φ n omega.1, by
      change
        deRhamDifferential (I := I₁) (M := M₁) (A := ℝ) n
            (smoothFormsPullbackDiffeomorph I₁ I₂ φ n omega.1) = 0
      rw [deRhamDifferential_smoothFormsPullbackDiffeomorph]
      rw [omega.2]
      simp⟩
  map_add' := by
    intro omega eta
    apply Subtype.ext
    exact (smoothFormsPullbackDiffeomorph I₁ I₂ φ n).map_add omega.1 eta.1
  map_smul' := by
    intro c omega
    apply Subtype.ext
    exact (smoothFormsPullbackDiffeomorph I₁ I₂ φ n).map_smul c omega.1

/--
%%handwave
name:
  Pullback preserves exact closed forms
statement:
  Pullback of closed forms along a diffeomorphism sends exact forms to exact
  forms.
proof:
  In degree zero exactness means vanishing.  In positive degree, pull back a
  primitive and use naturality of the exterior derivative.
-/
theorem deRhamClosedFormsPullbackDiffeomorph_exact
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (n : ℕ) :
    DeRhamExactClosedForms (I := I₂) (M := M₂) (A := ℝ) n ≤
      (DeRhamExactClosedForms (I := I₁) (M := M₁) (A := ℝ) n).comap
        (deRhamClosedFormsPullbackDiffeomorph I₁ I₂ φ n) := by
  intro omega homega
  change
    (deRhamClosedFormsPullbackDiffeomorph I₁ I₂ φ n omega).1 ∈
      DeRhamExactForms (I := I₁) (M := M₁) (A := ℝ) n
  change omega.1 ∈ DeRhamExactForms (I := I₂) (M := M₂) (A := ℝ) n at homega
  cases n with
  | zero =>
      simp [DeRhamExactForms] at homega ⊢
      rw [homega]
      simp [deRhamClosedFormsPullbackDiffeomorph]
  | succ n =>
      rw [DeRhamExactForms] at homega ⊢
      rcases homega with ⟨eta, heta⟩
      refine ⟨smoothFormsPullbackDiffeomorph I₁ I₂ φ n eta, ?_⟩
      change
        deRhamDifferential (I := I₁) (M := M₁) (A := ℝ) n
            (smoothFormsPullbackDiffeomorph I₁ I₂ φ n eta) =
          smoothFormsPullbackDiffeomorph I₁ I₂ φ (n + 1) omega.1
      rw [deRhamDifferential_smoothFormsPullbackDiffeomorph]
      rw [heta]

/-- The induced pullback map on de Rham cohomology. -/
def deRhamCohomologyPullbackDiffeomorph
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (n : ℕ) :
    DeRhamCohomology (I := I₂) (M := M₂) (A := ℝ) n →ₗ[ℝ]
      DeRhamCohomology (I := I₁) (M := M₁) (A := ℝ) n :=
  (DeRhamExactClosedForms (I := I₂) (M := M₂) (A := ℝ) n).mapQ
    (DeRhamExactClosedForms (I := I₁) (M := M₁) (A := ℝ) n)
    (deRhamClosedFormsPullbackDiffeomorph I₁ I₂ φ n)
    (deRhamClosedFormsPullbackDiffeomorph_exact I₁ I₂ φ n)

/-- Pullback by inverse diffeomorphisms is the identity on closed forms. -/
theorem deRhamClosedFormsPullbackDiffeomorph_symm_comp
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : DeRhamClosedForms (I := I₂) (M := M₂) (A := ℝ) n) :
    deRhamClosedFormsPullbackDiffeomorph I₂ I₁ φ.symm n
        (deRhamClosedFormsPullbackDiffeomorph I₁ I₂ φ n omega) =
      omega := by
  apply Subtype.ext
  exact smoothFormsPullbackDiffeomorph_symm_comp I₁ I₂ φ omega.1

/-- Pullback by inverse diffeomorphisms is the identity on closed forms, reversed. -/
theorem deRhamClosedFormsPullbackDiffeomorph_comp_symm
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) {n : ℕ}
    (omega : DeRhamClosedForms (I := I₁) (M := M₁) (A := ℝ) n) :
    deRhamClosedFormsPullbackDiffeomorph I₁ I₂ φ n
        (deRhamClosedFormsPullbackDiffeomorph I₂ I₁ φ.symm n omega) =
      omega := by
  apply Subtype.ext
  exact smoothFormsPullbackDiffeomorph_comp_symm I₁ I₂ φ omega.1

/--
%%handwave
name:
  Pullback by inverse diffeomorphisms composes to the identity
statement:
  Pulling de Rham cohomology first along a diffeomorphism and then along its
  inverse gives the identity.
proof:
  Pullback is functorial, and the composite diffeomorphism is the identity.
-/
theorem deRhamCohomologyPullbackDiffeomorph_symm_comp
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (n : ℕ)
    (alpha : DeRhamCohomology (I := I₂) (M := M₂) (A := ℝ) n) :
    deRhamCohomologyPullbackDiffeomorph I₂ I₁ φ.symm n
        (deRhamCohomologyPullbackDiffeomorph I₁ I₂ φ n alpha) =
      alpha := by
  induction alpha using Submodule.Quotient.induction_on with
  | _ omega =>
      simp only [deRhamCohomologyPullbackDiffeomorph, Submodule.mapQ_apply]
      rw [deRhamClosedFormsPullbackDiffeomorph_symm_comp]

/--
%%handwave
name:
  Pullback by inverse diffeomorphisms composes to the identity, reversed
statement:
  Pulling de Rham cohomology first along the inverse diffeomorphism and then
  along the diffeomorphism gives the identity.
proof:
  Pullback is functorial, and the composite diffeomorphism is the identity.
-/
theorem deRhamCohomologyPullbackDiffeomorph_comp_symm
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (n : ℕ)
    (alpha : DeRhamCohomology (I := I₁) (M := M₁) (A := ℝ) n) :
    deRhamCohomologyPullbackDiffeomorph I₁ I₂ φ n
        (deRhamCohomologyPullbackDiffeomorph I₂ I₁ φ.symm n alpha) =
      alpha := by
  induction alpha using Submodule.Quotient.induction_on with
  | _ omega =>
      simp only [deRhamCohomologyPullbackDiffeomorph, Submodule.mapQ_apply]
      rw [deRhamClosedFormsPullbackDiffeomorph_comp_symm]

/--
%%handwave
name:
  Diffeomorphisms induce isomorphisms on de Rham cohomology
statement:
  A smooth diffeomorphism between smooth real manifolds induces a linear
  isomorphism between their real de Rham cohomology groups in every degree.
proof:
  Pull back forms along the diffeomorphism.  Pullback commutes with exterior
  derivative, so it descends to closed forms modulo exact forms.  The inverse
  diffeomorphism gives the inverse map on cohomology.
tags:
  milestone
-/
theorem deRhamCohomology_linearEquiv_of_diffeomorphic
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (n : ℕ) :
    Nonempty
      (DeRhamCohomology (I := I₁) (M := M₁) (A := ℝ) n ≃ₗ[ℝ]
        DeRhamCohomology (I := I₂) (M := M₂) (A := ℝ) n) := by
  exact ⟨
    LinearEquiv.ofLinear
      (deRhamCohomologyPullbackDiffeomorph I₂ I₁ φ.symm n)
      (deRhamCohomologyPullbackDiffeomorph I₁ I₂ φ n)
      (LinearMap.ext fun alpha ↦
        deRhamCohomologyPullbackDiffeomorph_symm_comp I₁ I₂ φ n alpha)
      (LinearMap.ext fun alpha ↦
        deRhamCohomologyPullbackDiffeomorph_comp_symm I₁ I₂ φ n alpha)⟩

/--
%%handwave
name:
  Diffeomorphic manifolds have the same vanishing de Rham cohomology
statement:
  If two smooth real manifolds are diffeomorphic and degree \(n\) real de Rham
  cohomology of the target is a singleton, then degree \(n\) real de Rham
  cohomology of the source is a singleton.
proof:
  Pullback along the diffeomorphism gives an isomorphism of de Rham complexes,
  with inverse given by pullback along the inverse diffeomorphism.  The induced
  linear equivalence on cohomology transports the singleton property.
tags:
  milestone
-/
theorem deRhamCohomology_subsingleton_of_diffeomorphic
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    (φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (n : ℕ)
    (h₂ : Subsingleton
      (DeRhamCohomology (I := I₂) (M := M₂) (A := ℝ) n)) :
    Subsingleton
      (DeRhamCohomology (I := I₁) (M := M₁) (A := ℝ) n) := by
  rcases deRhamCohomology_linearEquiv_of_diffeomorphic I₁ I₂ φ n with ⟨Φ⟩
  refine ⟨fun alpha beta ↦ ?_⟩
  have hΦ : Φ alpha = Φ beta := @Subsingleton.elim _ h₂ (Φ alpha) (Φ beta)
  calc
    alpha = Φ.symm (Φ alpha) := (Φ.symm_apply_apply alpha).symm
    _ = Φ.symm (Φ beta) := congrArg Φ.symm hΦ
    _ = beta := Φ.symm_apply_apply beta

end Diffeomorphism

end

end Manifold
end JJMath
