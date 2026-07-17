import JJMath.Manifold.Chain
import JJMath.Manifold.DeRhamPoincare

/-!
# Periods of smooth one-forms

This file connects the integration theory for smooth singular chains with
degree-one de Rham cohomology.  Its main point is the Stokes consequence that
exact one-forms integrate to zero over smooth one-cycles.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

universe v w m
universe v' w' m'

/-- The unique vertex of the standard zero-simplex. -/
def standardZeroSimplexVertex : StandardSimplex 0 :=
  ⟨fun _ => 1, by
    constructor
    · intro i
      positivity
    · simp⟩

theorem standardZeroSimplex_eq_vertex (q : StandardSimplex 0) :
    q = standardZeroSimplexVertex := by
  apply Subtype.ext
  funext i
  fin_cases i
  simpa [standardZeroSimplexVertex] using q.2.2

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

/-- Integration of a smooth form over a smooth singular chain. -/
noncomputable def integrateSmoothChain
    {k : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ k)
    (c : SingularChain (I := I) (M := M) k ∞) : ℝ :=
  integrateChain (I := I) (F := ℝ)
    (pullbackSimplexIntegrationTheory (I := I) (M := M) (F := ℝ))
    (r := ∞) (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
    (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
    c

@[simp]
theorem integrateSmoothChain_zero_chain {k : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ k) :
    integrateSmoothChain (I := I) omega 0 = 0 := by
  simp [integrateSmoothChain, integrateChain]

theorem integrateSmoothChain_add {k : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ k)
    (c₁ c₂ : SingularChain (I := I) (M := M) k ∞) :
    integrateSmoothChain (I := I) omega (c₁ + c₂) =
      integrateSmoothChain (I := I) omega c₁ +
        integrateSmoothChain (I := I) omega c₂ := by
  simp [integrateSmoothChain, integrateChain, integrateChainHom]

theorem integrateSmoothChain_zsmul {k : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ k)
    (n : ℤ) (c : SingularChain (I := I) (M := M) k ∞) :
    integrateSmoothChain (I := I) omega (n • c) =
      n • integrateSmoothChain (I := I) omega c := by
  exact map_zsmul
    (integrateChainHom (I := I) (F := ℝ)
      (pullbackSimplexIntegrationTheory (I := I) (M := M) (F := ℝ))
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
      (DifferentialForm.toContinuous
        (I := I) (M := M) (F := ℝ) (n := k) omega)) n c

/-- Integration over a fixed smooth singular chain is additive in the
smooth form. -/
theorem integrateSmoothChain_add_form {k : ℕ}
    (omega eta : SmoothForms (I := I) (M := M) ℝ k)
    (c : SingularChain (I := I) (M := M) k ∞) :
    integrateSmoothChain (I := I) (omega + eta) c =
      integrateSmoothChain (I := I) omega c +
        integrateSmoothChain (I := I) eta c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw [integrateSmoothChain_add, integrateSmoothChain_add,
        integrateSmoothChain_add, hc, hd]
      ring
  | single sigma n =>
      unfold integrateSmoothChain
      rw [integrateChain_single, integrateChain_single, integrateChain_single]
      simp only [integrateSimplex, pullbackSimplexIntegrationTheory]
      unfold integrateSimplexByPullback
      have hcoeff (x : Fin k → ℝ) :
          simplexPullbackCoefficient (I := I) (F := ℝ)
              (DifferentialForm.toContinuous (omega + eta)) sigma x =
            simplexPullbackCoefficient (I := I) (F := ℝ)
                (DifferentialForm.toContinuous omega) sigma x +
              simplexPullbackCoefficient (I := I) (F := ℝ)
                (DifferentialForm.toContinuous eta) sigma x := by
        rfl
      simp_rw [hcoeff]
      rw [MeasureTheory.integral_add
        (integrableOn_simplexPullbackCoefficient (I := I)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous omega) sigma)
        (integrableOn_simplexPullbackCoefficient (I := I)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous eta) sigma)]
      module

/-- Integration over a fixed smooth singular chain commutes with real scalar
multiplication of the smooth form. -/
theorem integrateSmoothChain_smul_form {k : ℕ}
    (a : ℝ) (omega : SmoothForms (I := I) (M := M) ℝ k)
    (c : SingularChain (I := I) (M := M) k ∞) :
    integrateSmoothChain (I := I) (a • omega) c =
      a * integrateSmoothChain (I := I) omega c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw [integrateSmoothChain_add, integrateSmoothChain_add, hc, hd]
      ring
  | single sigma n =>
      unfold integrateSmoothChain
      rw [integrateChain_single, integrateChain_single]
      simp only [integrateSimplex, pullbackSimplexIntegrationTheory]
      unfold integrateSimplexByPullback
      have hcoeff (x : Fin k → ℝ) :
          simplexPullbackCoefficient (I := I) (F := ℝ)
              (DifferentialForm.toContinuous (a • omega)) sigma x =
            a • simplexPullbackCoefficient (I := I) (F := ℝ)
              (DifferentialForm.toContinuous omega) sigma x := by
        rfl
      simp_rw [hcoeff]
      rw [MeasureTheory.integral_smul]
      simp only [smul_eq_mul]
      ring

@[simp]
theorem smoothForms_zero_toFun {n : ℕ} (x : M) :
    (0 : SmoothForms (I := I) (M := M) ℝ n).toFun x = 0 :=
  rfl

/-- Integration of a smooth zero-form over a zero-simplex is evaluation at its vertex. -/
theorem integrateSimplexByPullback_smoothRealFunctionToZeroForm_zero
    (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) 0 ∞) :
    integrateSimplexByPullback (I := I) (F := ℝ)
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := 0)
          (smoothRealFunctionToZeroForm (I0 := I) f)) sigma =
      f (sigma standardZeroSimplexVertex) := by
  classical
  have hdomain : simplexCoordinateDomain 0 = (Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp [simplexCoordinateDomain]
  have hparam (x : Fin 0 → ℝ) :
      simplexParametrizationUsingExtension sigma.extension x =
        sigma standardZeroSimplexVertex := by
    let q : StandardSimplex 0 :=
      ⟨simplexCoordinateMap 0 x,
        simplexCoordinateMap_mem_stdSimplex (by simp [simplexCoordinateDomain])⟩
    calc
      simplexParametrizationUsingExtension sigma.extension x = sigma q :=
        sigma.extension_eq q
      _ = sigma standardZeroSimplexVertex :=
        congrArg sigma (standardZeroSimplex_eq_vertex q)
  have hcoefficient (x : Fin 0 → ℝ) :
      simplexPullbackCoefficient (I := I) (F := ℝ)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := 0)
            (smoothRealFunctionToZeroForm (I0 := I) f)) sigma x =
        f (sigma standardZeroSimplexVertex) := by
    simp [simplexPullbackCoefficient, simplexPullbackCoefficientUsingExtension,
      simplexPullbackFormUsingExtension, hparam,
      smoothRealFunctionToZeroForm,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.constOfIsEmpty_apply]
  unfold integrateSimplexByPullback
  simp_rw [hcoefficient]
  rw [hdomain]
  rw [MeasureTheory.Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  simp

/-- Integration of an arbitrary smooth zero-form over a zero-simplex is
evaluation at its vertex. -/
theorem integrateSimplexByPullback_zeroForm_zero
    (theta : SmoothForms (I := I) (M := M) ℝ 0)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) 0 ∞) :
    integrateSimplexByPullback (I := I) (F := ℝ)
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := 0)
          theta) sigma =
      theta.toFun (sigma standardZeroSimplexVertex)
        (fun i : Fin 0 => nomatch i) := by
  classical
  have hdomain : simplexCoordinateDomain 0 = (Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp [simplexCoordinateDomain]
  have hparam (x : Fin 0 → ℝ) :
      simplexParametrizationUsingExtension sigma.extension x =
        sigma standardZeroSimplexVertex := by
    let q : StandardSimplex 0 :=
      ⟨simplexCoordinateMap 0 x,
        simplexCoordinateMap_mem_stdSimplex (by simp [simplexCoordinateDomain])⟩
    calc
      simplexParametrizationUsingExtension sigma.extension x = sigma q :=
        sigma.extension_eq q
      _ = sigma standardZeroSimplexVertex :=
        congrArg sigma (standardZeroSimplex_eq_vertex q)
  have hcoefficient (x : Fin 0 → ℝ) :
      simplexPullbackCoefficient (I := I) (F := ℝ)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := 0)
            theta) sigma x =
        theta.toFun (sigma standardZeroSimplexVertex)
          (fun i : Fin 0 => nomatch i) := by
    simp only [simplexPullbackCoefficient,
      simplexPullbackCoefficientUsingExtension,
      simplexPullbackFormUsingExtension,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hparam x]
    congr 1
    funext i
    exact Fin.elim0 i
  unfold integrateSimplexByPullback
  simp_rw [hcoefficient]
  rw [hdomain]
  rw [MeasureTheory.Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  simp

/-- Exterior differentiation at a point depends only on the germ of a smooth
form at that point. -/
private theorem legacy_deRhamDifferential_toFun_eq_of_eventuallyEq
    {n : ℕ} (omega eta : SmoothForms (I := I) (M := M) ℝ n) {x : M}
    (hlocal : ∀ᶠ y in 𝓝 x, omega.toFun y = eta.toFun y) :
    (deRhamDifferential (I := I) (M := M) (A := ℝ) n omega).toFun x =
      (deRhamDifferential (I := I) (M := M) (A := ℝ) n eta).toFun x := by
  let e : OpenPartialHomeomorph M H := chartAt H x
  let y : E := (extChartAt I x) x
  have hy : y ∈ (e.extend I).target := by
    simp [e, y, extChartAt]
  have hsymm_y : (e.extend I).symm y = x := by
    simp [e, y, extChartAt]
  have hsymm :
      Filter.Tendsto (e.extend I).symm (𝓝[(e.extend I).target] y) (𝓝 x) := by
    have hcontinuous :
        ContinuousWithinAt (e.extend I).symm (e.extend I).target y :=
      e.continuousOn_extend_symm (I := I) y hy
    rw [← hsymm_y]
    exact hcontinuous.tendsto
  have hcoordinate :
      coordinateExpression (I := I) (F := ℝ) (n := n) omega.toFun e =ᶠ[
        𝓝[(e.extend I).target] y]
      coordinateExpression (I := I) (F := ℝ) (n := n) eta.toFun e := by
    filter_upwards [hsymm hlocal] with z hz
    simp only [coordinateExpression]
    rw [hz]
  change
    (extDerivWithin
      (coordinateExpression (I := I) (F := ℝ) (n := n) omega.toFun e)
      (e.extend I).target y).compContinuousLinearMap
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x) =
      (extDerivWithin
        (coordinateExpression (I := I) (F := ℝ) (n := n) eta.toFun e)
        (e.extend I).target y).compContinuousLinearMap
          (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x)
  rw [hcoordinate.extDerivWithin_eq_of_mem hy]

/-- A pointwise form which is locally equal to a smooth form is smooth. -/
theorem isContMDiffForm_of_locally_eventuallyEq_smoothForms
    {n : ℕ} (form : (x : M) → FormAt (I := I) ℝ n x)
    (hlocal : ∀ x : M, ∃ omega : SmoothForms (I := I) (M := M) ℝ n,
      ∀ᶠ y in 𝓝 x, form y = omega.toFun y) :
    IsContMDiffForm (I := I) (M := M) (F := ℝ) (n := n) ∞ form := by
  intro e he y hy
  let x : M := (e.extend I).symm y
  rcases hlocal x with ⟨omega, homega⟩
  have hsymm :
      Filter.Tendsto (e.extend I).symm (𝓝[(e.extend I).target] y) (𝓝 x) :=
    (e.continuousOn_extend_symm (I := I) y hy).tendsto
  have hcoordinate :
      coordinateExpression (I := I) (F := ℝ) (n := n) form e =ᶠ[
        𝓝[(e.extend I).target] y]
      coordinateExpression (I := I) (F := ℝ) (n := n) omega.toFun e := by
    filter_upwards [hsymm homega] with z hz
    simp only [coordinateExpression]
    rw [hz]
  exact (omega.isContMDiff e he y hy).congr_of_eventuallyEq_of_mem
    hcoordinate hy

/-- Extend a smooth form from one side of a set by zero, assuming the form
already vanishes near every frontier point. -/
noncomputable def smoothFormPiecewiseZero
    {n : ℕ} (omega : SmoothForms (I := I) (M := M) ℝ n) (U : Set M)
    (hzero : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x, omega.toFun y = 0) :
    SmoothForms (I := I) (M := M) ℝ n := by
  classical
  exact
    { toFun := fun x => if x ∈ U then omega.toFun x else 0
      isContMDiff := by
        apply isContMDiffForm_of_locally_eventuallyEq_smoothForms (I := I)
        intro x
        by_cases hxU : x ∈ interior U
        · refine ⟨omega, ?_⟩
          filter_upwards [isOpen_interior.mem_nhds hxU] with y hy
          simp [interior_subset hy]
        by_cases hxclosure : x ∈ closure U
        · have hxfrontier : x ∈ frontier U := ⟨hxclosure, hxU⟩
          refine ⟨0, ?_⟩
          filter_upwards [hzero x hxfrontier] with y hy
          by_cases hyU : y ∈ U <;> simp [hyU, hy]
        · refine ⟨0, ?_⟩
          have hxcompl : x ∈ (closure U)ᶜ := by simpa using hxclosure
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcompl] with y hy
          have hyU : y ∉ U := fun hyU => hy (subset_closure hyU)
          simp [hyU] }

@[simp]
theorem smoothFormPiecewiseZero_toFun_of_mem
    {n : ℕ} (omega : SmoothForms (I := I) (M := M) ℝ n) (U : Set M)
    (hzero : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x, omega.toFun y = 0)
    {x : M} (hx : x ∈ U) :
    (smoothFormPiecewiseZero (I := I) omega U hzero).toFun x = omega.toFun x := by
  classical
  simp [smoothFormPiecewiseZero, hx]

@[simp]
theorem smoothFormPiecewiseZero_toFun_of_not_mem
    {n : ℕ} (omega : SmoothForms (I := I) (M := M) ℝ n) (U : Set M)
    (hzero : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x, omega.toFun y = 0)
    {x : M} (hx : x ∉ U) :
    (smoothFormPiecewiseZero (I := I) omega U hzero).toFun x = 0 := by
  classical
  simp [smoothFormPiecewiseZero, hx]

/-- Extension by zero preserves closedness when the original form vanishes
near the gluing frontier. -/
theorem deRhamDifferential_smoothFormPiecewiseZero_eq_zero
    {n : ℕ} (omega : SmoothForms (I := I) (M := M) ℝ n) (U : Set M)
    (hzero : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x, omega.toFun y = 0)
    (hclosed : deRhamDifferential (I := I) (M := M) (A := ℝ) n omega = 0) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) n
      (smoothFormPiecewiseZero (I := I) omega U hzero) = 0 := by
  classical
  apply DifferentialForm.ext
  intro x
  by_cases hxU : x ∈ interior U
  · have hlocal : ∀ᶠ y in 𝓝 x,
        (smoothFormPiecewiseZero (I := I) omega U hzero).toFun y =
          omega.toFun y := by
      filter_upwards [isOpen_interior.mem_nhds hxU] with y hy
      simp [interior_subset hy]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := I) (smoothFormPiecewiseZero (I := I) omega U hzero) omega hlocal]
    simpa using congrArg (fun theta => theta.toFun x) hclosed
  by_cases hxclosure : x ∈ closure U
  · have hxfrontier : x ∈ frontier U := ⟨hxclosure, hxU⟩
    have hlocal : ∀ᶠ y in 𝓝 x,
        (smoothFormPiecewiseZero (I := I) omega U hzero).toFun y =
          (0 : SmoothForms (I := I) (M := M) ℝ n).toFun y := by
      filter_upwards [hzero x hxfrontier] with y hy
      by_cases hyU : y ∈ U <;> simp [hyU, hy]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := I) (smoothFormPiecewiseZero (I := I) omega U hzero) 0 hlocal]
    have hdzero :
        deRhamDifferential (I := I) (M := M) (A := ℝ) n
          (0 : SmoothForms (I := I) (M := M) ℝ n) = 0 := by
      exact LinearMap.map_zero _
    simpa using congrArg (fun theta => theta.toFun x) hdzero

  · have hxcompl : x ∈ (closure U)ᶜ := by simpa using hxclosure
    have hlocal : ∀ᶠ y in 𝓝 x,
        (smoothFormPiecewiseZero (I := I) omega U hzero).toFun y =
          (0 : SmoothForms (I := I) (M := M) ℝ n).toFun y := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcompl] with y hy
      have hyU : y ∉ U := fun hyU => hy (subset_closure hyU)
      simp [hyU]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := I) (smoothFormPiecewiseZero (I := I) omega U hzero) 0 hlocal]
    have hdzero :
        deRhamDifferential (I := I) (M := M) (A := ℝ) n
          (0 : SmoothForms (I := I) (M := M) ℝ n) = 0 := by
      exact LinearMap.map_zero _
    simpa using congrArg (fun theta => theta.toFun x) hdzero

/-- A locally supported exact form, extended by zero across a region's
frontier, is a global closed one-form. -/
noncomputable def piecewiseExactOneForm
    (theta : SmoothForms (I := I) (M := M) ℝ 0) (U : Set M)
    (hzero : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x,
      (deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta).toFun y = 0) :
    DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1 :=
  ⟨smoothFormPiecewiseZero (I := I)
      (deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta) U hzero,
    deRhamDifferential_smoothFormPiecewiseZero_eq_zero
      (I := I)
      (deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta) U hzero
      (deRhamDifferential_comp_eq_zero (I := I) (M := M) (A := ℝ) theta)⟩

/-- The pullback integral over a simplex only depends on the values of the
form along that simplex. -/
theorem integrateSimplexByPullback_eq_of_toFun_eqOn
    {k : ℕ} {r : WithTop ℕ∞} (hcell : (1 : WithTop ℕ∞) ≤ r)
    (omega eta : ContinuousDifferentialForm (I := I) (M := M) (F := ℝ) k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (hform : ∀ q : StandardSimplex k,
      omega.toFun (sigma q) = eta.toFun (sigma q)) :
    integrateSimplexByPullback (I := I) (F := ℝ) hcell omega sigma =
      integrateSimplexByPullback (I := I) (F := ℝ) hcell eta sigma := by
  classical
  unfold integrateSimplexByPullback
  congr 1
  apply MeasureTheory.setIntegral_congr_fun
    (measurableSet_simplexCoordinateDomain k)
  intro x hx
  let q : StandardSimplex k :=
    ⟨simplexCoordinateMap k x, simplexCoordinateMap_mem_stdSimplex hx⟩
  have hextension : sigma.extension (simplexCoordinateMap k x) = sigma q :=
    sigma.extension_eq q
  simp only [simplexPullbackCoefficient, simplexPullbackCoefficientUsingExtension,
    simplexPullbackFormUsingExtension, simplexParametrizationUsingExtension]
  rw [hextension, hform q]

/-- Two smooth forms with the same values along a smooth simplex have the
same integral over the corresponding singleton chain. -/
theorem integrateSmoothChain_single_eq_of_toFun_eqOn
    {k : ℕ} (omega eta : SmoothForms (I := I) (M := M) ℝ k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) k ∞)
    (hform : ∀ q : StandardSimplex k,
      omega.toFun (sigma q) = eta.toFun (sigma q)) :
    integrateSmoothChain (I := I) omega (Finsupp.single sigma (1 : ℤ)) =
      integrateSmoothChain (I := I) eta (Finsupp.single sigma (1 : ℤ)) := by
  unfold integrateSmoothChain
  rw [integrateChain_single, integrateChain_single]
  simp only [one_zsmul, integrateSimplex, pullbackSimplexIntegrationTheory]
  exact integrateSimplexByPullback_eq_of_toFun_eqOn
    (I := I) (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
    (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
    (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) eta)
    sigma hform

/-- Postcompose a smooth singular simplex with a smooth map. -/
noncomputable def ContMDiffSingularSimplex.postcompose
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) k r) :
    ContMDiffSingularSimplex (I := I') (M := N) k r where
  toContinuousMap :=
    ⟨fun q ↦ f (sigma q),
      f.contMDiff.continuous.comp sigma.toContinuousMap.continuous⟩
  contMDiff := by
    refine ⟨fun q ↦ f (sigma.extension q), ?_, ?_⟩
    · exact f.contMDiff.comp_contMDiffOn sigma.extension_contMDiffOn
    · intro q
      exact congrArg f (sigma.extension_eq q)

@[simp]
theorem ContMDiffSingularSimplex.postcompose_apply
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) k r)
    (q : StandardSimplex k) :
    sigma.postcompose (I := I) f q = f (sigma q) :=
  rfl

@[simp]
theorem ContMDiffSingularSimplex.postcompose_face
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) (k + 1) r)
    (i : Fin (k + 2)) :
    (sigma.postcompose (I := I) f).face i =
      (sigma.face i).postcompose (I := I) f := by
  rfl

/-- Postcompose every simplex in a smooth singular chain with a smooth map. -/
noncomputable def SingularChain.postcompose
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯)
    (c : SingularChain (I := I) (M := M) k r) :
    SingularChain (I := I') (M := N) k r :=
  Finsupp.mapDomain
    (fun sigma => sigma.postcompose (I := I) f) c

@[simp]
theorem SingularChain.postcompose_zero
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯) :
    SingularChain.postcompose (I := I) f
        (0 : SingularChain (I := I) (M := M) k r) = 0 := by
  simp [SingularChain.postcompose]

@[simp]
theorem SingularChain.postcompose_add
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯)
    (c d : SingularChain (I := I) (M := M) k r) :
    SingularChain.postcompose (I := I) f (c + d) =
      SingularChain.postcompose (I := I) f c +
        SingularChain.postcompose (I := I) f d := by
  exact Finsupp.mapDomain_add

@[simp]
theorem SingularChain.postcompose_zsmul
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯) (n : ℤ)
    (c : SingularChain (I := I) (M := M) k r) :
    SingularChain.postcompose (I := I) f (n • c) =
      n • SingularChain.postcompose (I := I) f c := by
  let g : SingularChain (I := I) (M := M) k r →+
      SingularChain (I := I') (M := N) k r :=
    Finsupp.mapDomain.addMonoidHom
      (fun sigma => sigma.postcompose (I := I) f)
  change g (n • c) = n • g c
  exact map_zsmul g n c

@[simp]
theorem SingularChain.postcompose_single
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) k r) (n : ℤ) :
    SingularChain.postcompose (I := I) f (Finsupp.single sigma n) =
      Finsupp.single (sigma.postcompose (I := I) f) n := by
  simp [SingularChain.postcompose]

/-- Taking the boundary of a smooth chain commutes with postcomposition by a
smooth map. -/
theorem SingularChain.postcompose_boundary
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ N]
    {k : ℕ} {r : WithTop ℕ∞}
    (f : C^r⟮I, M; I', N⟯)
    (c : SingularChain (I := I) (M := M) (k + 1) r) :
    SingularChain.postcompose (I := I) f (boundary (I := I) c) =
      boundary (I := I') (SingularChain.postcompose (I := I) f c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single sigma n =>
      simp only [boundary, Finsupp.linearCombination_single,
        SingularChain.postcompose_single]
      rw [SingularChain.postcompose_zsmul]
      congr 1
      change (Finsupp.mapDomain.addMonoidHom
          (fun tau => tau.postcompose (I := I) f))
          (∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
            Finsupp.single (sigma.face i) (1 : ℤ)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_zsmul]
      simp [ContMDiffSingularSimplex.postcompose_face]

/-- Regard a smooth singular simplex in an open subset as a simplex in the
ambient manifold. -/
noncomputable def ContMDiffSingularSimplex.openInclusion
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r) :
    ContMDiffSingularSimplex (I := I) (M := M) k r where
  toContinuousMap :=
    ⟨fun q => (sigma q : M), continuous_subtype_val.comp sigma.toContinuousMap.continuous⟩
  contMDiff := by
    refine ⟨fun q => (sigma.extension q : M), ?_, ?_⟩
    · exact (contMDiff_subtype_val (I := I) (n := r) (U := U)).comp_contMDiffOn
        sigma.extension_contMDiffOn
    · intro q
      exact congrArg Subtype.val (sigma.extension_eq q)

@[simp]
theorem ContMDiffSingularSimplex.openInclusion_apply
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r)
    (q : StandardSimplex k) :
    sigma.openInclusion (I := I) U q = (sigma q : M) :=
  rfl

theorem ContMDiffSingularSimplex.openInclusion_injective
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞} :
    Function.Injective
      (fun sigma : ContMDiffSingularSimplex (I := I) (M := U) k r =>
        sigma.openInclusion (I := I) U) := by
  intro sigma tau h
  rcases sigma with ⟨sigma, hsigma⟩
  rcases tau with ⟨tau, htau⟩
  have hmaps : sigma = tau := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    exact congrArg (fun s => s q) h
  subst tau
  rfl

theorem ContMDiffSingularSimplex.openInclusion_face
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) (k + 1) r)
    (i : Fin (k + 2)) :
    (sigma.openInclusion (I := I) U).face i =
      (sigma.face i).openInclusion (I := I) U := by
  rcases sigma with ⟨sigma, hsigma⟩
  rfl

/-- Regard a smooth singular chain in an open subset as a chain in the
ambient manifold. -/
noncomputable def SingularChain.openInclusion
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (c : SingularChain (I := I) (M := U) k r) :
    SingularChain (I := I) (M := M) k r :=
  Finsupp.mapDomain
    (fun sigma => sigma.openInclusion (I := I) U) c

@[simp]
theorem SingularChain.openInclusion_zero
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞} :
    SingularChain.openInclusion (I := I) U
        (0 : SingularChain (I := I) (M := U) k r) = 0 := by
  simp [SingularChain.openInclusion]

@[simp]
theorem SingularChain.openInclusion_add
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (c d : SingularChain (I := I) (M := U) k r) :
    SingularChain.openInclusion (I := I) U (c + d) =
      SingularChain.openInclusion (I := I) U c +
        SingularChain.openInclusion (I := I) U d := by
  exact Finsupp.mapDomain_add

@[simp]
theorem SingularChain.openInclusion_sub
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (c d : SingularChain (I := I) (M := U) k r) :
    SingularChain.openInclusion (I := I) U (c - d) =
      SingularChain.openInclusion (I := I) U c -
        SingularChain.openInclusion (I := I) U d := by
  let f : SingularChain (I := I) (M := U) k r →+
      SingularChain (I := I) (M := M) k r :=
    Finsupp.mapDomain.addMonoidHom
      (fun sigma => sigma.openInclusion (I := I) U)
  change f (c - d) = f c - f d
  exact map_sub f c d

@[simp]
theorem SingularChain.openInclusion_zsmul
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (n : ℤ) (c : SingularChain (I := I) (M := U) k r) :
    SingularChain.openInclusion (I := I) U (n • c) =
      n • SingularChain.openInclusion (I := I) U c := by
  let f : SingularChain (I := I) (M := U) k r →+
      SingularChain (I := I) (M := M) k r :=
    Finsupp.mapDomain.addMonoidHom
      (fun sigma => sigma.openInclusion (I := I) U)
  change f (n • c) = n • f c
  exact map_zsmul f n c

@[simp]
theorem SingularChain.openInclusion_single
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r) (n : ℤ) :
    SingularChain.openInclusion (I := I) U (Finsupp.single sigma n) =
      Finsupp.single (sigma.openInclusion (I := I) U) n := by
  simp [SingularChain.openInclusion]

/-- Taking the boundary of a smooth chain commutes with inclusion of an open
subset into the ambient manifold. -/
theorem SingularChain.openInclusion_boundary
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (c : SingularChain (I := I) (M := U) (k + 1) r) :
    SingularChain.openInclusion (I := I) U (boundary (I := I) c) =
      boundary (I := I) (SingularChain.openInclusion (I := I) U c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single sigma n =>
      simp only [boundary, Finsupp.linearCombination_single,
        SingularChain.openInclusion_single]
      rw [SingularChain.openInclusion_zsmul]
      congr 1
      change (Finsupp.mapDomain.addMonoidHom
          (fun tau => tau.openInclusion (I := I) U))
          (∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
            Finsupp.single (sigma.face i) (1 : ℤ)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_zsmul]
      simp [ContMDiffSingularSimplex.openInclusion_face]

/-- Include a smooth singular simplex from a smaller open subset into a
larger open subset of the same manifold. -/
noncomputable def ContMDiffSingularSimplex.nestedOpenInclusion
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r) :
    ContMDiffSingularSimplex (I := I) (M := V) k r where
  toContinuousMap :=
    ⟨fun q => TopologicalSpace.Opens.inclusion hUV (sigma q),
      (continuous_inclusion hUV).comp sigma.toContinuousMap.continuous⟩
  contMDiff := by
    refine ⟨fun q => TopologicalSpace.Opens.inclusion hUV (sigma.extension q), ?_, ?_⟩
    · exact (contMDiff_inclusion (I := I) (n := r) hUV).comp_contMDiffOn
        sigma.extension_contMDiffOn
    · intro q
      exact congrArg (TopologicalSpace.Opens.inclusion hUV) (sigma.extension_eq q)

@[simp]
theorem ContMDiffSingularSimplex.nestedOpenInclusion_apply
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r)
    (q : StandardSimplex k) :
    sigma.nestedOpenInclusion (I := I) hUV q =
      TopologicalSpace.Opens.inclusion hUV (sigma q) :=
  rfl

theorem ContMDiffSingularSimplex.nestedOpenInclusion_face
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) (k + 1) r)
    (i : Fin (k + 2)) :
    (sigma.nestedOpenInclusion (I := I) hUV).face i =
      (sigma.face i).nestedOpenInclusion (I := I) hUV := by
  rcases sigma with ⟨sigma, hsigma⟩
  rfl

/-- Include a smooth singular chain from a smaller open subset into a larger
one. -/
noncomputable def SingularChain.nestedOpenInclusion
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (c : SingularChain (I := I) (M := U) k r) :
    SingularChain (I := I) (M := V) k r :=
  Finsupp.mapDomain
    (fun sigma => sigma.nestedOpenInclusion (I := I) hUV) c

@[simp]
theorem SingularChain.nestedOpenInclusion_zero
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞} :
    SingularChain.nestedOpenInclusion (I := I) hUV
        (0 : SingularChain (I := I) (M := U) k r) = 0 := by
  simp [SingularChain.nestedOpenInclusion]

@[simp]
theorem SingularChain.nestedOpenInclusion_single
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r) (n : ℤ) :
    SingularChain.nestedOpenInclusion (I := I) hUV
        (Finsupp.single sigma n) =
      Finsupp.single (sigma.nestedOpenInclusion (I := I) hUV) n := by
  simp [SingularChain.nestedOpenInclusion]

@[simp]
theorem SingularChain.nestedOpenInclusion_add
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (c d : SingularChain (I := I) (M := U) k r) :
    SingularChain.nestedOpenInclusion (I := I) hUV (c + d) =
      SingularChain.nestedOpenInclusion (I := I) hUV c +
        SingularChain.nestedOpenInclusion (I := I) hUV d := by
  exact Finsupp.mapDomain_add

@[simp]
theorem SingularChain.nestedOpenInclusion_sub
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (c d : SingularChain (I := I) (M := U) k r) :
    SingularChain.nestedOpenInclusion (I := I) hUV (c - d) =
      SingularChain.nestedOpenInclusion (I := I) hUV c -
        SingularChain.nestedOpenInclusion (I := I) hUV d := by
  let f : SingularChain (I := I) (M := U) k r →+
      SingularChain (I := I) (M := V) k r :=
    Finsupp.mapDomain.addMonoidHom
      (fun sigma => sigma.nestedOpenInclusion (I := I) hUV)
  change f (c - d) = f c - f d
  exact map_sub f c d

@[simp]
theorem SingularChain.nestedOpenInclusion_zsmul
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (n : ℤ) (c : SingularChain (I := I) (M := U) k r) :
    SingularChain.nestedOpenInclusion (I := I) hUV (n • c) =
      n • SingularChain.nestedOpenInclusion (I := I) hUV c := by
  let f : SingularChain (I := I) (M := U) k r →+
      SingularChain (I := I) (M := V) k r :=
    Finsupp.mapDomain.addMonoidHom
      (fun sigma => sigma.nestedOpenInclusion (I := I) hUV)
  change f (n • c) = n • f c
  exact map_zsmul f n c

/-- Boundary commutes with inclusion between nested open subsets. -/
theorem SingularChain.nestedOpenInclusion_boundary
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (c : SingularChain (I := I) (M := U) (k + 1) r) :
    SingularChain.nestedOpenInclusion (I := I) hUV (boundary (I := I) c) =
      boundary (I := I)
        (SingularChain.nestedOpenInclusion (I := I) hUV c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [SingularChain.nestedOpenInclusion]
  | add c d hc hd => simp [map_add, hc, hd]
  | single sigma n =>
      simp only [boundary, Finsupp.linearCombination_single,
        SingularChain.nestedOpenInclusion_single]
      rw [SingularChain.nestedOpenInclusion_zsmul]
      congr 1
      change (Finsupp.mapDomain.addMonoidHom
          (fun tau => tau.nestedOpenInclusion (I := I) hUV)
          (∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
            Finsupp.single (sigma.face i) (1 : ℤ))) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_zsmul]
      simp [ContMDiffSingularSimplex.nestedOpenInclusion_face]

/-- Pulling a form back along an inclusion of nested open subsets and
integrating over a simplex is the same as integrating over the included
simplex. -/
theorem simplexPullbackCoefficient_nestedOpenInclusion
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} (omega : SmoothForms (I := I) (M := V) ℝ k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k ∞)
    {x : Fin k → ℝ} (hx : x ∈ simplexCoordinateDomain k) :
    simplexPullbackCoefficient (I := I) (F := ℝ)
        (DifferentialForm.toContinuous
          (I := I) (M := V) (F := ℝ) (n := k) omega)
        (sigma.nestedOpenInclusion (I := I) hUV) x =
      simplexPullbackCoefficient (I := I) (F := ℝ)
        (DifferentialForm.toContinuous
          (I := I) (M := U) (F := ℝ) (n := k)
          (restrictSmoothFormsOfLE (I := I) (A := ℝ) hUV k omega))
        sigma x := by
  let sigmaV := sigma.nestedOpenInclusion (I := I) hUV
  let G : SimplexAmbient k → V := fun q =>
    TopologicalSpace.Opens.inclusion hUV (sigma.extension q)
  have hGdiff :
      ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I ∞ G
        (stdSimplex ℝ (Fin (k + 1))) := by
    exact (contMDiff_inclusion (I := I) (n := ∞) hUV).comp_contMDiffOn
      sigma.extension_contMDiffOn
  have hGeq : ∀ q : StandardSimplex k, G q = sigmaV q := by
    intro q
    exact congrArg (TopologicalSpace.Opens.inclusion hUV)
      (sigma.extension_eq q)
  have hextension :
      simplexPullbackCoefficientUsingExtension (I := I) (F := ℝ)
          (DifferentialForm.toContinuous
            (I := I) (M := V) (F := ℝ) (n := k) omega)
          sigmaV.extension x =
        simplexPullbackCoefficientUsingExtension (I := I) (F := ℝ)
          (DifferentialForm.toContinuous
            (I := I) (M := V) (F := ℝ) (n := k) omega)
          G x := by
    exact simplexPullbackCoefficientUsingExtension_eq_of_eqOn
      (I := I) (F := ℝ)
      (DifferentialForm.toContinuous
        (I := I) (M := V) (F := ℝ) (n := k) omega)
      sigmaV sigmaV.extension_contMDiffOn hGdiff sigmaV.extension_eq hGeq hx
  rw [show simplexPullbackCoefficient (I := I) (F := ℝ)
        (DifferentialForm.toContinuous
          (I := I) (M := V) (F := ℝ) (n := k) omega)
        sigmaV x =
      simplexPullbackCoefficientUsingExtension (I := I) (F := ℝ)
        (DifferentialForm.toContinuous
          (I := I) (M := V) (F := ℝ) (n := k) omega)
        sigmaV.extension x by rfl,
    hextension]
  let f : (Fin k → ℝ) → U :=
    simplexParametrizationUsingExtension sigma.extension
  let g : U → V := TopologicalSpace.Opens.inclusion hUV
  have hf : MDifferentiableWithinAt 𝓘(ℝ, Fin k → ℝ) I f
      (simplexCoordinateDomain k) x := by
    exact ContMDiffSingularSimplex.mdifferentiableWithinAt_simplexParametrization
      (I := I) (M := U) sigma (show (∞ : WithTop ℕ∞) ≠ 0 by simp) hx
  have hg : MDifferentiableAt I I g (f x) :=
    (contMDiff_inclusion (I := I) (n := ∞) hUV).contMDiffAt.mdifferentiableAt
      (by simp)
  have hderiv :
      mfderivWithin 𝓘(ℝ, Fin k → ℝ) I (g ∘ f)
          (simplexCoordinateDomain k) x =
        (mfderiv I I g (f x)).comp
          (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I f
            (simplexCoordinateDomain k) x) :=
    mfderiv_comp_mfderivWithin
      (I := 𝓘(ℝ, Fin k → ℝ)) (I' := I) (I'' := I)
      (f := f) (g := g) (s := simplexCoordinateDomain k) (x := x) hg hf
      ((uniqueDiffOn_simplexCoordinateDomain k) x hx).uniqueMDiffWithinAt
  change
    ((omega.toFun (G (simplexCoordinateMap k x))).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I
        (simplexParametrizationUsingExtension G)
        (simplexCoordinateDomain k) x)) (fun i => Pi.single i 1) = _
  change
    ((omega.toFun ((g ∘ f) x)).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I (g ∘ f)
        (simplexCoordinateDomain k) x)) (fun i => Pi.single i 1) = _
  rw [hderiv]
  rfl

/-- Integration over a simplex commutes with inclusion between nested open
subsets. -/
theorem integrateSimplexByPullback_nestedOpenInclusion
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} (omega : SmoothForms (I := I) (M := V) ℝ k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k ∞) :
    integrateSimplexByPullback (I := I) (F := ℝ)
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous
          (I := I) (M := V) (F := ℝ) (n := k) omega)
        (sigma.nestedOpenInclusion (I := I) hUV) =
      integrateSimplexByPullback (I := I) (F := ℝ)
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous
          (I := I) (M := U) (F := ℝ) (n := k)
          (restrictSmoothFormsOfLE (I := I) (A := ℝ) hUV k omega))
        sigma := by
  unfold integrateSimplexByPullback
  congr 1
  apply MeasureTheory.setIntegral_congr_fun
    (measurableSet_simplexCoordinateDomain k)
  intro x hx
  exact simplexPullbackCoefficient_nestedOpenInclusion
    (I := I) hUV omega sigma hx

/-- Integration over a smooth chain commutes with inclusion between nested
open subsets. -/
theorem integrateSmoothChain_nestedOpenInclusion
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} (omega : SmoothForms (I := I) (M := V) ℝ k)
    (c : SingularChain (I := I) (M := U) k ∞) :
    integrateSmoothChain (I := I) omega
        (SingularChain.nestedOpenInclusion (I := I) hUV c) =
      integrateSmoothChain (I := I)
        (restrictSmoothFormsOfLE (I := I) (A := ℝ) hUV k omega) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [integrateSmoothChain_add, hc, hd]
  | single sigma n =>
      simp only [SingularChain.nestedOpenInclusion_single]
      unfold integrateSmoothChain
      rw [integrateChain_single, integrateChain_single]
      change n • integrateSimplexByPullback (I := I) (F := ℝ)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous
            (I := I) (M := V) (F := ℝ) (n := k) omega)
          (sigma.nestedOpenInclusion (I := I) hUV) =
        n • integrateSimplexByPullback (I := I) (F := ℝ)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous
            (I := I) (M := U) (F := ℝ) (n := k)
            (restrictSmoothFormsOfLE (I := I) (A := ℝ) hUV k omega))
          sigma
      rw [integrateSimplexByPullback_nestedOpenInclusion]

/-- Pulling a smooth form back by a diffeomorphism and integrating it over a
simplex is the same as integrating the original form over the transported
simplex. -/
theorem simplexPullbackCoefficient_diffeomorph
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    (I' : ModelWithCorners ℝ E' H') [IsManifold I' ∞ N]
    {k : ℕ} (φ : M ≃ₘ⟮I, I'⟯ N)
    (omega : SmoothForms (I := I') (M := N) ℝ k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) k ∞)
    {x : Fin k → ℝ} (hx : x ∈ simplexCoordinateDomain k) :
    simplexPullbackCoefficient (I := I') (F := ℝ)
        (DifferentialForm.toContinuous
          (I := I') (M := N) (F := ℝ) (n := k) omega)
        (sigma.postcompose (I := I) φ.toContMDiffMap) x =
      simplexPullbackCoefficient (I := I) (F := ℝ)
        (DifferentialForm.toContinuous
          (I := I) (M := M) (F := ℝ) (n := k)
          (smoothFormsPullbackDiffeomorph I I' φ k omega))
        sigma x := by
  let sigmaN := sigma.postcompose (I := I) φ.toContMDiffMap
  let G : SimplexAmbient k → N := fun q => φ (sigma.extension q)
  have hGdiff :
      ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I' ∞ G
        (stdSimplex ℝ (Fin (k + 1))) := by
    exact φ.contMDiff.comp_contMDiffOn sigma.extension_contMDiffOn
  have hGeq : ∀ q : StandardSimplex k, G q = sigmaN q := by
    intro q
    exact congrArg φ (sigma.extension_eq q)
  have hextension :
      simplexPullbackCoefficientUsingExtension (I := I') (F := ℝ)
          (DifferentialForm.toContinuous
            (I := I') (M := N) (F := ℝ) (n := k) omega)
          sigmaN.extension x =
        simplexPullbackCoefficientUsingExtension (I := I') (F := ℝ)
          (DifferentialForm.toContinuous
            (I := I') (M := N) (F := ℝ) (n := k) omega)
          G x := by
    exact simplexPullbackCoefficientUsingExtension_eq_of_eqOn
      (I := I') (F := ℝ)
      (DifferentialForm.toContinuous
        (I := I') (M := N) (F := ℝ) (n := k) omega)
      sigmaN sigmaN.extension_contMDiffOn hGdiff sigmaN.extension_eq hGeq hx
  rw [show simplexPullbackCoefficient (I := I') (F := ℝ)
        (DifferentialForm.toContinuous
          (I := I') (M := N) (F := ℝ) (n := k) omega)
        sigmaN x =
      simplexPullbackCoefficientUsingExtension (I := I') (F := ℝ)
        (DifferentialForm.toContinuous
          (I := I') (M := N) (F := ℝ) (n := k) omega)
        sigmaN.extension x by rfl,
    hextension]
  let f : (Fin k → ℝ) → M :=
    simplexParametrizationUsingExtension sigma.extension
  let g : M → N := fun y => φ y
  have hf : MDifferentiableWithinAt 𝓘(ℝ, Fin k → ℝ) I f
      (simplexCoordinateDomain k) x := by
    exact ContMDiffSingularSimplex.mdifferentiableWithinAt_simplexParametrization
      (I := I) (M := M) sigma (show (∞ : WithTop ℕ∞) ≠ 0 by simp) hx
  have hg : MDifferentiableAt I I' g (f x) :=
    φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hderiv :
      mfderivWithin 𝓘(ℝ, Fin k → ℝ) I' (g ∘ f)
          (simplexCoordinateDomain k) x =
        (mfderiv I I' g (f x)).comp
          (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I f
            (simplexCoordinateDomain k) x) :=
    mfderiv_comp_mfderivWithin
      (I := 𝓘(ℝ, Fin k → ℝ)) (I' := I) (I'' := I')
      (f := f) (g := g) (s := simplexCoordinateDomain k) (x := x) hg hf
      ((uniqueDiffOn_simplexCoordinateDomain k) x hx).uniqueMDiffWithinAt
  change
    ((omega.toFun (G (simplexCoordinateMap k x))).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I'
        (simplexParametrizationUsingExtension G) (simplexCoordinateDomain k) x))
        (fun i => Pi.single i 1) = _
  change
    ((omega.toFun ((g ∘ f) x)).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I' (g ∘ f)
        (simplexCoordinateDomain k) x)) (fun i => Pi.single i 1) = _
  rw [hderiv]
  rfl

/-- Naturality of integration over a simplex under a diffeomorphism. -/
theorem integrateSimplexByPullback_diffeomorph
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    (I' : ModelWithCorners ℝ E' H') [IsManifold I' ∞ N]
    {k : ℕ} (φ : M ≃ₘ⟮I, I'⟯ N)
    (omega : SmoothForms (I := I') (M := N) ℝ k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) k ∞) :
    integrateSimplexByPullback (I := I') (F := ℝ)
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous
          (I := I') (M := N) (F := ℝ) (n := k) omega)
        (sigma.postcompose (I := I) φ.toContMDiffMap) =
      integrateSimplexByPullback (I := I) (F := ℝ)
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous
          (I := I) (M := M) (F := ℝ) (n := k)
          (smoothFormsPullbackDiffeomorph I I' φ k omega)) sigma := by
  unfold integrateSimplexByPullback
  congr 1
  apply MeasureTheory.setIntegral_congr_fun
    (measurableSet_simplexCoordinateDomain k)
  intro x hx
  exact simplexPullbackCoefficient_diffeomorph I I' φ omega sigma hx

/-- Naturality of integration over a smooth singular chain under a
diffeomorphism. -/
theorem integrateSmoothChain_diffeomorph
    {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type w'} [TopologicalSpace H']
    {N : Type m'} [TopologicalSpace N] [ChartedSpace H' N]
    (I' : ModelWithCorners ℝ E' H') [IsManifold I' ∞ N]
    {k : ℕ} (φ : M ≃ₘ⟮I, I'⟯ N)
    (omega : SmoothForms (I := I') (M := N) ℝ k)
    (c : SingularChain (I := I) (M := M) k ∞) :
    integrateSmoothChain (I := I') omega
        (SingularChain.postcompose (I := I) φ.toContMDiffMap c) =
      integrateSmoothChain (I := I)
        (smoothFormsPullbackDiffeomorph I I' φ k omega) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [integrateSmoothChain_add, hc, hd]
  | single sigma n =>
      simp only [SingularChain.postcompose_single]
      unfold integrateSmoothChain
      rw [integrateChain_single, integrateChain_single]
      change n • integrateSimplexByPullback (I := I') (F := ℝ)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous
            (I := I') (M := N) (F := ℝ) (n := k) omega)
          (sigma.postcompose (I := I) φ.toContMDiffMap) =
        n • integrateSimplexByPullback (I := I) (F := ℝ)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous
            (I := I) (M := M) (F := ℝ) (n := k)
            (smoothFormsPullbackDiffeomorph I I' φ k omega)) sigma
      rw [integrateSimplexByPullback_diffeomorph]

/-- Pulling a smooth form back to an open subset and integrating there gives
the same simplex coefficient as integrating the ambient form after inclusion. -/
theorem simplexPullbackCoefficient_openInclusion
    {k : ℕ} (U : TopologicalSpace.Opens M)
    (omega : SmoothForms (I := I) (M := M) ℝ k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k ∞)
    {x : Fin k → ℝ} (hx : x ∈ simplexCoordinateDomain k) :
    simplexPullbackCoefficient (I := I) (F := ℝ)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
        (sigma.openInclusion (I := I) U) x =
      simplexPullbackCoefficient (I := I) (F := ℝ)
        (DifferentialForm.toContinuous (I := I) (M := U) (F := ℝ) (n := k)
          (restrictSmoothFormsToOpen (I := I) (A := ℝ) U k omega))
        sigma x := by
  let sigmaM := sigma.openInclusion (I := I) U
  let G : SimplexAmbient k → M := fun q => (sigma.extension q : M)
  have hGdiff :
      ContMDiffOn 𝓘(ℝ, SimplexAmbient k) I ∞ G
        (stdSimplex ℝ (Fin (k + 1))) := by
    exact (contMDiff_subtype_val (I := I) (n := ∞) (U := U)).comp_contMDiffOn
      sigma.extension_contMDiffOn
  have hGeq : ∀ q : StandardSimplex k, G q = sigmaM q := by
    intro q
    exact congrArg Subtype.val (sigma.extension_eq q)
  have hextension :
      simplexPullbackCoefficientUsingExtension (I := I) (F := ℝ)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
          sigmaM.extension x =
        simplexPullbackCoefficientUsingExtension (I := I) (F := ℝ)
          (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
          G x := by
    exact simplexPullbackCoefficientUsingExtension_eq_of_eqOn
      (I := I) (F := ℝ)
      (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
      sigmaM sigmaM.extension_contMDiffOn hGdiff sigmaM.extension_eq hGeq hx
  rw [show simplexPullbackCoefficient (I := I) (F := ℝ)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
        sigmaM x =
      simplexPullbackCoefficientUsingExtension (I := I) (F := ℝ)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
        sigmaM.extension x by rfl,
    hextension]
  let f : (Fin k → ℝ) → U := simplexParametrizationUsingExtension sigma.extension
  let g : U → M := fun y => (y : M)
  have hf : MDifferentiableWithinAt 𝓘(ℝ, Fin k → ℝ) I f
      (simplexCoordinateDomain k) x := by
    exact ContMDiffSingularSimplex.mdifferentiableWithinAt_simplexParametrization
      (I := I) (M := U) sigma (show (∞ : WithTop ℕ∞) ≠ 0 by simp) hx
  have hg : MDifferentiableAt I I g (f x) :=
    (contMDiff_subtype_val (I := I) (n := ∞) (U := U)).contMDiffAt.mdifferentiableAt
      (by simp)
  have hderiv :
      mfderivWithin 𝓘(ℝ, Fin k → ℝ) I (g ∘ f)
          (simplexCoordinateDomain k) x =
        (mfderiv I I g (f x)).comp
          (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I f
            (simplexCoordinateDomain k) x) :=
    mfderiv_comp_mfderivWithin
      (I := 𝓘(ℝ, Fin k → ℝ)) (I' := I) (I'' := I)
      (f := f) (g := g) (s := simplexCoordinateDomain k) (x := x) hg hf
      ((uniqueDiffOn_simplexCoordinateDomain k) x hx).uniqueMDiffWithinAt
  change
    ((omega.toFun (G (simplexCoordinateMap k x))).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I
        (simplexParametrizationUsingExtension G) (simplexCoordinateDomain k) x))
        (fun i => Pi.single i 1) = _
  change
    ((omega.toFun ((g ∘ f) x)).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, Fin k → ℝ) I (g ∘ f)
        (simplexCoordinateDomain k) x)) (fun i => Pi.single i 1) = _
  rw [hderiv]
  rfl

/-- Integration over a simplex is unchanged when a form and simplex are both
restricted to an open subset containing the simplex. -/
theorem integrateSimplexByPullback_openInclusion
    {k : ℕ} (U : TopologicalSpace.Opens M)
    (omega : SmoothForms (I := I) (M := M) ℝ k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k ∞) :
    integrateSimplexByPullback (I := I) (F := ℝ)
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) omega)
        (sigma.openInclusion (I := I) U) =
      integrateSimplexByPullback (I := I) (F := ℝ)
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous (I := I) (M := U) (F := ℝ) (n := k)
          (restrictSmoothFormsToOpen (I := I) (A := ℝ) U k omega))
        sigma := by
  unfold integrateSimplexByPullback
  congr 1
  apply MeasureTheory.setIntegral_congr_fun
    (measurableSet_simplexCoordinateDomain k)
  intro x hx
  exact simplexPullbackCoefficient_openInclusion (I := I) U omega sigma hx

/-- The integral of a global form over an included singleton simplex equals
the integral of its restriction over the lifted singleton simplex. -/
theorem integrateSmoothChain_openInclusion_single
    {k : ℕ} (U : TopologicalSpace.Opens M)
    (omega : SmoothForms (I := I) (M := M) ℝ k)
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k ∞) :
    integrateSmoothChain (I := I) omega
        (Finsupp.single (sigma.openInclusion (I := I) U) (1 : ℤ)) =
      integrateSmoothChain (I := I)
        (restrictSmoothFormsToOpen (I := I) (A := ℝ) U k omega)
        (Finsupp.single sigma (1 : ℤ)) := by
  unfold integrateSmoothChain
  rw [integrateChain_single, integrateChain_single]
  simp only [one_zsmul, integrateSimplex, pullbackSimplexIntegrationTheory]
  exact integrateSimplexByPullback_openInclusion (I := I) U omega sigma

/-- Integration is unchanged when a form and an arbitrary smooth chain are
both restricted to an open subset containing the chain. -/
theorem integrateSmoothChain_openInclusion
    {k : ℕ} (U : TopologicalSpace.Opens M)
    (omega : SmoothForms (I := I) (M := M) ℝ k)
    (c : SingularChain (I := I) (M := U) k ∞) :
    integrateSmoothChain (I := I) omega
        (SingularChain.openInclusion (I := I) U c) =
      integrateSmoothChain (I := I)
        (restrictSmoothFormsToOpen (I := I) (A := ℝ) U k omega) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [integrateSmoothChain_add, hc, hd]
  | single sigma n =>
      simp only [SingularChain.openInclusion_single]
      unfold integrateSmoothChain
      rw [integrateChain_single, integrateChain_single]
      change n • integrateSimplexByPullback (I := I) (F := ℝ)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous
            (I := I) (M := M) (F := ℝ) (n := k) omega)
          (sigma.openInclusion (I := I) U) =
        n • integrateSimplexByPullback (I := I) (F := ℝ)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous
            (I := I) (M := U) (F := ℝ) (n := k)
              (restrictSmoothFormsToOpen (I := I) (A := ℝ) U k omega))
          sigma
      rw [integrateSimplexByPullback_openInclusion]

/-- The zero smooth form integrates to zero over every smooth singular
chain. -/
theorem integrateSmoothChain_zero_form
    {k : ℕ} (c : SingularChain (I := I) (M := M) k ∞) :
    integrateSmoothChain (I := I)
      (0 : SmoothForms (I := I) (M := M) ℝ k) c = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [integrateSmoothChain_add, hc, hd]
  | single sigma n =>
      unfold integrateSmoothChain
      rw [integrateChain_single]
      suffices integrateSimplexByPullback (I := I) (F := ℝ)
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
          (DifferentialForm.toContinuous
            (I := I) (M := M) (F := ℝ) (n := k)
            (0 : SmoothForms (I := I) (M := M) ℝ k)) sigma = 0 by
        simp [this, integrateSimplex, pullbackSimplexIntegrationTheory]
      simp [integrateSimplexByPullback, simplexPullbackCoefficient,
        simplexPullbackCoefficientUsingExtension,
        simplexPullbackFormUsingExtension]

/--
%%handwave
name:
  Stokes for a smooth differential form
statement:
  The integral of the exterior differential of a smooth degree \(k\) form
  over a smooth singular \((k+1)\)-chain equals the integral of the form over
  the boundary chain.
proof:
  Lower the recorded regularity of the smooth form to (C^1) and apply Stokes'
  theorem for smooth singular chains.
-/
theorem integrateSmoothChain_deRhamDifferential_eq_boundary
    {k : ℕ}
    (theta : SmoothForms (I := I) (M := M) ℝ k)
    (c : SingularChain (I := I) (M := M) (k + 1) ∞) :
    integrateSmoothChain (I := I)
        (deRhamDifferential (I := I) (M := M) (A := ℝ) k theta) c =
      integrateSmoothChain (I := I) theta (boundary (I := I) c) := by
  let thetaC1 : C1DifferentialForm (I := I) (M := M) (F := ℝ) k :=
    DifferentialForm.of_le (I := I) (M := M) (F := ℝ) (n := k)
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp) theta
  have hstokes :=
    integrateChain_boundary_eq_integrateChain_exteriorDerivative
      (I := I) (M := M) (F := ℝ) (k := k) (r := ∞)
        (show (2 : WithTop ℕ∞) ≤ ∞ from
          WithTop.coe_le_coe.2 (OrderTop.le_top (2 : ℕ∞))) thetaC1 c
  have htheta_continuous :
      DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) thetaC1 =
        DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k) theta := by
    apply DifferentialForm.ext
    intro x
    rfl
  have hdtheta_continuous :
      exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) thetaC1 =
        DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := k + 1)
          (deRhamDifferential (I := I) (M := M) (A := ℝ) k theta) := by
    apply DifferentialForm.ext
    intro x
    rfl
  rw [htheta_continuous, hdtheta_continuous] at hstokes
  exact hstokes.symm

/-- A closed smooth form integrates to zero over the boundary of every
smooth singular chain. -/
theorem integrateSmoothChain_boundary_eq_zero_of_closed
    {k : ℕ}
    (omega : DeRhamClosedForms (I := I) (M := M) (A := ℝ) k)
    (c : SingularChain (I := I) (M := M) (k + 1) ∞) :
    integrateSmoothChain (I := I) omega.1 (boundary (I := I) c) = 0 := by
  rw [← integrateSmoothChain_deRhamDifferential_eq_boundary (I := I), omega.2]
  exact integrateSmoothChain_zero_form (I := I) c

/--
%%handwave
name:
  Stokes for a smooth primitive on a one-chain
statement:
  The integral of the differential of a smooth function over a smooth
  one-chain equals the integral of the function over the boundary.
proof:
  Lower the recorded regularity of the smooth function to (C^1) and apply
  Stokes' theorem for smooth singular chains.
-/
theorem integrateSmoothChain_deRhamDifferential_zero_eq_boundary
    (theta : SmoothForms (I := I) (M := M) ℝ 0)
    (c : SingularChain (I := I) (M := M) 1 ∞) :
    integrateSmoothChain (I := I)
        (deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta) c =
      integrateChain (I := I) (F := ℝ)
        (pullbackSimplexIntegrationTheory (I := I) (M := M) (F := ℝ))
        (r := ∞) (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        (DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := 0) theta)
        (boundary (I := I) c) := by
  let thetaC1 : C1DifferentialForm (I := I) (M := M) (F := ℝ) 0 :=
    DifferentialForm.of_le (I := I) (M := M) (F := ℝ) (n := 0)
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp) theta
  have hstokes :=
    integrateChain_boundary_eq_integrateChain_exteriorDerivative
      (I := I) (M := M) (F := ℝ) (k := 0) (r := ∞)
        (show (2 : WithTop ℕ∞) ≤ ∞ from
          WithTop.coe_le_coe.2 (OrderTop.le_top (2 : ℕ∞))) thetaC1 c
  have htheta_continuous :
      DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := 0) thetaC1 =
        DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := 0) theta := by
    apply DifferentialForm.ext
    intro x
    rfl
  have hdtheta_continuous :
      exteriorDerivative (I := I) (r := (0 : WithTop ℕ∞)) thetaC1 =
        DifferentialForm.toContinuous (I := I) (M := M) (F := ℝ) (n := 1)
          (deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta) := by
    apply DifferentialForm.ext
    intro x
    rfl
  rw [htheta_continuous, hdtheta_continuous] at hstokes
  exact hstokes.symm

/--
%%handwave
name:
  Fundamental theorem for a smooth one-simplex
statement:
  For a smooth function \(f:M\to\mathbb R\) and a smooth singular
  one-simplex \(\sigma:[0,1]\to M\),
  \[
    \int_\sigma df=f(\sigma(1))-f(\sigma(0)).
  \]
proof:
  Apply Stokes' theorem to the one-simplex.  Its oriented boundary is the
  terminal vertex minus the initial vertex, and integration of the zero-form
  \(f\) over these vertices is evaluation of \(f\).
-/
theorem integrateSmoothChain_deRhamDifferential_zero_single_eq_endpoint_sub
    (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) 1 ∞) :
    integrateSmoothChain (I := I)
        (deRhamDifferential (I := I) (M := M) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := I) f))
        (Finsupp.single sigma (1 : ℤ)) =
      f (sigma.face 0 standardZeroSimplexVertex) -
        f (sigma.face 1 standardZeroSimplexVertex) := by
  rw [integrateSmoothChain_deRhamDifferential_zero_eq_boundary (I := I)]
  simp [boundary, integrateChain, integrateChainHom, integrateSimplex,
    pullbackSimplexIntegrationTheory,
    integrateSimplexByPullback_smoothRealFunctionToZeroForm_zero,
    sub_eq_add_neg]

/-- The integral of the differential of a smooth zero-form over a smooth
one-simplex is the terminal value of the zero-form minus its initial value. -/
theorem integrateSmoothChain_deRhamDifferential_zeroForm_single_eq_endpoint_sub
    (theta : SmoothForms (I := I) (M := M) ℝ 0)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) 1 ∞) :
    integrateSmoothChain (I := I)
        (deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta)
        (Finsupp.single sigma (1 : ℤ)) =
      theta.toFun (sigma.face 0 standardZeroSimplexVertex)
          (fun i : Fin 0 => nomatch i) -
        theta.toFun (sigma.face 1 standardZeroSimplexVertex)
          (fun i : Fin 0 => nomatch i) := by
  rw [integrateSmoothChain_deRhamDifferential_zero_eq_boundary (I := I)]
  simp [boundary, integrateChain, integrateChainHom, integrateSimplex,
    pullbackSimplexIntegrationTheory, integrateSimplexByPullback_zeroForm_zero,
    sub_eq_add_neg]

/--
%%handwave
name:
  Integration in a region with a primitive
statement:
  Let \(U\subseteq M\) be open and suppose \(\omega|_U=df\).  If a smooth
  one-chain \(c\) in \(U\) has boundary \(b-a\), then
  \[
    \int_c\omega=f(b)-f(a).
  \]
proof:
  Restrict the form and chain to \(U\), replace \(\omega|_U\) by \(df\), and
  apply Stokes.  Evaluating the zero-form \(f\) on the boundary \(b-a\)
  gives the stated difference.
-/
theorem integrateSmoothChain_openInclusion_eq_endpoint_sub_of_restrict_eq_d
    (U : TopologicalSpace.Opens M)
    (omega : SmoothForms (I := I) (M := M) ℝ 1)
    (f : C^∞⟮I, U; ℝ⟯)
    (hexact :
      restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1 omega =
        deRhamDifferential (I := I) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := I) f))
    (c : SingularChain (I := I) (M := U) 1 ∞)
    (a b : ContMDiffSingularSimplex (I := I) (M := U) 0 ∞)
    (hboundary : boundary (I := I) c =
      Finsupp.single b (1 : ℤ) - Finsupp.single a (1 : ℤ)) :
    integrateSmoothChain (I := I) omega
        (SingularChain.openInclusion (I := I) U c) =
      f (b standardZeroSimplexVertex) -
        f (a standardZeroSimplexVertex) := by
  rw [integrateSmoothChain_openInclusion, hexact,
    integrateSmoothChain_deRhamDifferential_zero_eq_boundary, hboundary]
  simp [integrateChain, integrateChainHom, integrateSimplex,
    pullbackSimplexIntegrationTheory,
    integrateSimplexByPullback_smoothRealFunctionToZeroForm_zero,
    sub_eq_add_neg]

/-- On a simplex contained in the retained side, integrating an exact form
extended by zero still gives the change of its primitive at the endpoints. -/
theorem integrate_piecewiseExactOneForm_single_eq_endpoint_sub
    (f : C^∞⟮I, M; ℝ⟯) (U : Set M)
    (hzero : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x,
      (deRhamDifferential (I := I) (M := M) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I) f)).toFun y = 0)
    (sigma : ContMDiffSingularSimplex (I := I) (M := M) 1 ∞)
    (hsigma : ∀ q : StandardSimplex 1, sigma q ∈ U) :
    integrateSmoothChain (I := I)
        ((piecewiseExactOneForm (I := I)
          (smoothRealFunctionToZeroForm (I0 := I) f) U hzero :
            DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1) :
          SmoothForms (I := I) (M := M) ℝ 1)
        (Finsupp.single sigma (1 : ℤ)) =
      f (sigma.face 0 standardZeroSimplexVertex) -
        f (sigma.face 1 standardZeroSimplexVertex) := by
  rw [integrateSmoothChain_single_eq_of_toFun_eqOn
    (I := I)
    ((piecewiseExactOneForm (I := I)
      (smoothRealFunctionToZeroForm (I0 := I) f) U hzero :
        DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1) :
      SmoothForms (I := I) (M := M) ℝ 1)
    (deRhamDifferential (I := I) (M := M) (A := ℝ) 0
      (smoothRealFunctionToZeroForm (I0 := I) f)) sigma]
  · exact integrateSmoothChain_deRhamDifferential_zero_single_eq_endpoint_sub
      (I := I) f sigma
  · intro q
    exact smoothFormPiecewiseZero_toFun_of_mem
      (I := I)
      (deRhamDifferential (I := I) (M := M) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I) f)) U hzero (hsigma q)

/--
%%handwave
name:
  Exact one-forms have zero period
statement:
  The integral of an exact smooth one-form over every smooth singular
  one-cycle is zero.
proof:
  Write the form as the differential of a smooth function and apply Stokes.
  The boundary term vanishes because the chain is a cycle.
-/
theorem integrateSmoothChain_eq_zero_of_mem_deRhamExactForms_one
    (omega : SmoothForms (I := I) (M := M) ℝ 1)
    (homega :
      omega ∈ DeRhamExactForms (I := I) (M := M) (A := ℝ) 1)
    (c : SingularChain (I := I) (M := M) 1 ∞)
    (hcycle : boundary (I := I) c = 0) :
    integrateSmoothChain (I := I) omega c = 0 := by
  rcases homega with ⟨theta, rfl⟩
  rw [integrateSmoothChain_deRhamDifferential_zero_eq_boundary (I := I), hcycle]
  simp [integrateChain]

/--
%%handwave
name:
  Vanishing first de Rham cohomology kills periods
statement:
  If first de Rham cohomology is trivial, then every closed smooth one-form
  has zero integral over every smooth singular one-cycle.
proof:
  Trivial cohomology makes the closed form exact, and exact one-forms have zero
  period by Stokes' theorem.
-/
theorem integrateSmoothChain_eq_zero_of_closed_of_deRhamH1_subsingleton
    [Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1)]
    (omega : DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1)
    (c : SingularChain (I := I) (M := M) 1 ∞)
    (hcycle : boundary (I := I) c = 0) :
    integrateSmoothChain (I := I) (omega : SmoothForms (I := I) (M := M) ℝ 1) c = 0 := by
  have hexact :
      (omega : SmoothForms (I := I) (M := M) ℝ 1) ∈
        DeRhamExactForms (I := I) (M := M) (A := ℝ) 1 :=
    deRhamClosedForm_mem_exactForms_of_cohomology_subsingleton
      (I := I) (M := M) (A := ℝ) omega
  exact integrateSmoothChain_eq_zero_of_mem_deRhamExactForms_one
    (I := I) (omega := (omega : SmoothForms (I := I) (M := M) ℝ 1))
    hexact c hcycle

/-- A nonzero period detects that the de Rham class of the given closed
one-form is nonzero. -/
theorem deRhamCohomologyClass_ne_zero_of_nonzero_period
    (omega : DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1)
    (c : SingularChain (I := I) (M := M) 1 ∞)
    (hcycle : boundary (I := I) c = 0)
    (hperiod :
      integrateSmoothChain (I := I)
        (omega : SmoothForms (I := I) (M := M) ℝ 1) c ≠ 0) :
    (DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) 1).mkQ omega ≠ 0 := by
  intro hclass
  have hmem :
      omega ∈ DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) 1 := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [Submodule.mkQ_apply] using hclass
  have hexact :
      (omega : SmoothForms (I := I) (M := M) ℝ 1) ∈
        DeRhamExactForms (I := I) (M := M) (A := ℝ) 1 := by
    simpa [DeRhamExactClosedForms] using hmem
  exact hperiod
    (integrateSmoothChain_eq_zero_of_mem_deRhamExactForms_one
      (I := I) (omega := (omega : SmoothForms (I := I) (M := M) ℝ 1))
      hexact c hcycle)

/-- A nonzero period after restriction to a smaller open set shows that the
restricted de Rham class is nonzero. -/
theorem deRhamCohomologyRestrictionOfLE_ne_zero_of_nonzero_period
    {W V : TopologicalSpace.Opens M} (hWV : W ≤ V)
    (omega : DeRhamClosedForms (I := I) (M := V) (A := ℝ) 1)
    (c : SingularChain (I := I) (M := W) 1 ∞)
    (hcycle : boundary (I := I) c = 0)
    (hperiod :
      integrateSmoothChain (I := I)
        (restrictSmoothFormsOfLE (I := I) (A := ℝ) hWV 1
          (omega : SmoothForms (I := I) (M := V) ℝ 1)) c ≠ 0) :
    deRhamCohomologyRestrictionOfLE (I := I) (A := ℝ) hWV 1
        ((DeRhamExactClosedForms
          (I := I) (M := V) (A := ℝ) 1).mkQ omega) ≠ 0 := by
  let omegaW := deRhamClosedFormsRestrictionOfLE
    (I := I) (A := ℝ) hWV 1 omega
  have hperiodW :
      integrateSmoothChain (I := I)
        (omegaW : SmoothForms (I := I) (M := W) ℝ 1) c ≠ 0 := by
    simpa [omegaW, deRhamClosedFormsRestrictionOfLE] using hperiod
  have hclassW := deRhamCohomologyClass_ne_zero_of_nonzero_period
    (I := I) omegaW c hcycle hperiodW
  simpa [deRhamCohomologyRestrictionOfLE, omegaW,
    Submodule.mapQ_apply] using hclassW

/--
%%handwave
name:
  A nonzero period detects first de Rham cohomology
statement:
  A closed smooth one-form with nonzero integral over a smooth singular
  one-cycle implies that first de Rham cohomology is nontrivial.
proof:
  If first de Rham cohomology were trivial, the preceding Stokes argument
  would force the asserted nonzero period to vanish.
-/
theorem not_subsingleton_deRhamH1_of_exists_nonzero_period
    (omega : DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1)
    (c : SingularChain (I := I) (M := M) 1 ∞)
    (hcycle : boundary (I := I) c = 0)
    (hperiod :
      integrateSmoothChain (I := I)
        (omega : SmoothForms (I := I) (M := M) ℝ 1) c ≠ 0) :
    ¬ Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := by
  intro hzero
  letI : Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := hzero
  exact hperiod
    (integrateSmoothChain_eq_zero_of_closed_of_deRhamH1_subsingleton
      (I := I) omega c hcycle)

/-- A collar-crossing chain with nonzero period, closed by a return chain on
which the form vanishes, detects nontrivial first de Rham cohomology. -/
theorem not_subsingleton_deRhamH1_of_crossing_and_return
    (omega : DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1)
    (crossing returning : SingularChain (I := I) (M := M) 1 ∞)
    (hcycle : boundary (I := I) (crossing + returning) = 0)
    (hcrossing :
      integrateSmoothChain (I := I)
        (omega : SmoothForms (I := I) (M := M) ℝ 1) crossing = 1)
    (hreturning :
      integrateSmoothChain (I := I)
        (omega : SmoothForms (I := I) (M := M) ℝ 1) returning = 0) :
    ¬ Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := by
  apply not_subsingleton_deRhamH1_of_exists_nonzero_period
    (I := I) omega (crossing + returning) hcycle
  rw [integrateSmoothChain_add, hcrossing, hreturning]
  norm_num

/--
%%handwave
name:
  A cut loop with unit primitive jump has nonzero period
statement:
  Let \(\omega\) be a closed one-form on \(M\).  Suppose a one-cycle is the
  sum of a chain \(c\subseteq U\), with \(\partial c=b-a\), and a bridge
  \(e\subseteq V\).  If \(\omega|_U=df\), \(f(a)=0\), \(f(b)=1\), and
  \(\omega|_V=0\), then
  \[
    \int_{c+e}\omega=1,
  \]
  so \(H^1_{\mathrm{dR}}(M)\neq0\).
proof:
  The primitive formula gives \(\int_c\omega=f(b)-f(a)=1\), while the
  vanishing of \(\omega\) on \(V\) gives \(\int_e\omega=0\).  Thus the cycle
  has nonzero period, which an exact form could not have.
-/
theorem not_subsingleton_deRhamH1_of_cut_primitive_and_zero_bridge
    (omega : DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1)
    (U V : TopologicalSpace.Opens M)
    (f : C^∞⟮I, U; ℝ⟯)
    (hexact :
      restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1
          (omega : SmoothForms (I := I) (M := M) ℝ 1) =
        deRhamDifferential (I := I) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := I) f))
    (hzero :
      restrictSmoothFormsToOpen (I := I) (A := ℝ) V 1
          (omega : SmoothForms (I := I) (M := M) ℝ 1) = 0)
    (long : SingularChain (I := I) (M := U) 1 ∞)
    (a b : ContMDiffSingularSimplex (I := I) (M := U) 0 ∞)
    (hlong_boundary : boundary (I := I) long =
      Finsupp.single b (1 : ℤ) - Finsupp.single a (1 : ℤ))
    (ha : f (a standardZeroSimplexVertex) = 0)
    (hb : f (b standardZeroSimplexVertex) = 1)
    (bridge : SingularChain (I := I) (M := V) 1 ∞)
    (hcycle : boundary (I := I)
      (SingularChain.openInclusion (I := I) U long +
        SingularChain.openInclusion (I := I) V bridge) = 0) :
    ¬ Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := by
  apply not_subsingleton_deRhamH1_of_crossing_and_return
    (I := I) omega
    (SingularChain.openInclusion (I := I) U long)
    (SingularChain.openInclusion (I := I) V bridge) hcycle
  · rw [integrateSmoothChain_openInclusion_eq_endpoint_sub_of_restrict_eq_d
      (I := I) U (omega : SmoothForms (I := I) (M := M) ℝ 1)
      f hexact long a b hlong_boundary, hb, ha]
    norm_num
  · rw [integrateSmoothChain_openInclusion, hzero]
    exact integrateSmoothChain_zero_form I bridge

end

end Manifold
end JJMath
