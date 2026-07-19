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

/--
%%handwave
name:
  Uniqueness of the standard zero-simplex point
statement:
  The standard \(0\)-simplex consists of the single barycentric point
  \((1)\).
proof:
  Its only coordinate must equal the sum of all coordinates, which is \(1\).
-/
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

/--
%%handwave
name:
  Integral over the zero chain
statement:
  For every smooth \(k\)-form \(\omega\), \(\int_0\omega=0\).
proof:
  Integration is an additive homomorphism of singular chains.
-/
@[simp]
theorem integrateSmoothChain_zero_chain {k : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ k) :
    integrateSmoothChain (I := I) omega 0 = 0 := by
  simp [integrateSmoothChain, integrateChain]

/--
%%handwave
name:
  Additivity of integration in the chain
statement:
  For smooth \(k\)-chains \(c_1,c_2\),
  \(\int_{c_1+c_2}\omega=\int_{c_1}\omega+\int_{c_2}\omega\).
proof:
  Integration against a fixed form is defined as an additive homomorphism on
  singular chains.
-/
theorem integrateSmoothChain_add {k : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ k)
    (c₁ c₂ : SingularChain (I := I) (M := M) k ∞) :
    integrateSmoothChain (I := I) omega (c₁ + c₂) =
      integrateSmoothChain (I := I) omega c₁ +
        integrateSmoothChain (I := I) omega c₂ := by
  simp [integrateSmoothChain, integrateChain, integrateChainHom]

/--
%%handwave
name:
  Integer homogeneity of integration in the chain
statement:
  For \(m\in\mathbb Z\) and a smooth \(k\)-chain \(c\),
  \(\int_{m c}\omega=m\int_c\omega\).
proof:
  Every additive homomorphism of abelian groups commutes with integer scalar
  multiplication.
-/
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

/--
%%handwave
name:
  Additivity of integration in the differential form
statement:
  For smooth \(k\)-forms \(\omega,\eta\) and a smooth \(k\)-chain \(c\),
  \(\int_c(\omega+\eta)=\int_c\omega+\int_c\eta\).
proof:
  Reduce by linearity of chains to a single simplex.  There the pullback
  coefficient is pointwise additive, and additivity of the Lebesgue integral
  gives the result.
-/
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

/--
%%handwave
name:
  Real homogeneity of integration in the differential form
statement:
  For \(a\in\mathbb R\), a smooth \(k\)-form \(\omega\), and a smooth
  \(k\)-chain \(c\), \(\int_c a\omega=a\int_c\omega\).
proof:
  Reduce by linearity of chains to a single simplex.  Pullback evaluation is
  pointwise homogeneous, and scalar multiplication commutes with integration.
-/
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

/--
%%handwave
name:
  Pointwise value of the zero differential form
statement:
  At every \(x\in M\), the zero smooth \(n\)-form has value \(0\) in
  \(\Lambda^nT_x^*M\).
proof:
  This is the pointwise definition of the zero form.
-/
@[simp]
theorem smoothForms_zero_toFun {n : ℕ} (x : M) :
    (0 : SmoothForms (I := I) (M := M) ℝ n).toFun x = 0 :=
  rfl

/--
%%handwave
name:
  Integral of a smooth function over a zero-simplex
statement:
  If \(f:M\to\mathbb R\) is smooth and \(\sigma:\Delta^0\to M\), then
  \(\int_\sigma f=f(\sigma(*))\).
proof:
  The coordinate domain of \(\Delta^0\) is the one-point space
  \(\mathbb R^0\), whose volume measure is the Dirac mass at its unique point.
-/
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

/--
%%handwave
name:
  Integral of a smooth zero-form over a zero-simplex
statement:
  For a smooth zero-form \(\theta\) and
  \(\sigma:\Delta^0\to M\), the pullback integral is the value
  \(\theta_{\sigma(*)}\).
proof:
  The simplex coordinate domain is the singleton \(\mathbb R^0\), so the
  integral is evaluation at its unique point.
-/
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

/--
%%handwave
name:
  Smoothness from local equality with smooth forms
statement:
  A pointwise \(n\)-form \(\omega\) is smooth if every \(x\in M\) has a
  neighborhood on which \(\omega\) agrees with some smooth \(n\)-form.
proof:
  In each chart, compose the germ equality with the inverse chart.  The
  coordinate representative is then locally equal to a smooth coordinate
  representative, hence is smooth at every chart point.
-/
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

/--
%%handwave
name:
  Extension by zero on the retained region
statement:
  If a smooth form \(\omega\) is extended by zero outside \(U\), then at every
  \(x\in U\) the extended form equals \(\omega_x\).
proof:
  The piecewise definition selects \(\omega\) at points of \(U\).
-/
@[simp]
theorem smoothFormPiecewiseZero_toFun_of_mem
    {n : ℕ} (omega : SmoothForms (I := I) (M := M) ℝ n) (U : Set M)
    (hzero : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x, omega.toFun y = 0)
    {x : M} (hx : x ∈ U) :
    (smoothFormPiecewiseZero (I := I) omega U hzero).toFun x = omega.toFun x := by
  classical
  simp [smoothFormPiecewiseZero, hx]

/--
%%handwave
name:
  Extension by zero off the retained region
statement:
  If a smooth form \(\omega\) is extended by zero outside \(U\), then at every
  \(x\notin U\) the extended form equals \(0\).
proof:
  The piecewise definition selects the zero form outside \(U\).
-/
@[simp]
theorem smoothFormPiecewiseZero_toFun_of_not_mem
    {n : ℕ} (omega : SmoothForms (I := I) (M := M) ℝ n) (U : Set M)
    (hzero : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x, omega.toFun y = 0)
    {x : M} (hx : x ∉ U) :
    (smoothFormPiecewiseZero (I := I) omega U hzero).toFun x = 0 := by
  classical
  simp [smoothFormPiecewiseZero, hx]

/--
%%handwave
name:
  Closedness of an extension by zero
statement:
  Let \(\omega\) be a closed smooth \(n\)-form and suppose that near every
  point of the frontier of \(U\), \(\omega\) vanishes.  Then the form equal to
  \(\omega\) on \(U\) and \(0\) outside \(U\) is closed.
proof:
  At an interior point it has the same germ as \(\omega\); at a frontier or
  exterior point it has the same germ as zero.  Exterior differentiation
  depends only on the germ, so it vanishes everywhere.
-/
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

/--
%%handwave
name:
  Simplex integrals depend only on values along the simplex
statement:
  If two continuous \(k\)-forms \(\omega,\eta\) have equal values at every
  point of a smooth simplex \(\sigma:\Delta^k\to M\), then
  \(\int_\sigma\omega=\int_\sigma\eta\).
proof:
  On the simplex coordinate domain, both pullback coefficients use the same
  parameterization and derivative; equality of the form values makes the
  integrands pointwise equal.
-/
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

/--
%%handwave
name:
  Equality of singleton-chain integrals from pointwise equality
statement:
  If smooth \(k\)-forms \(\omega,\eta\) agree at every point of a smooth
  simplex \(\sigma\), then their integrals over the singleton chain
  \([\sigma]\) are equal.
proof:
  Integration over a singleton chain is the simplex pullback integral, which
  depends only on the values of the form along \(\sigma\).
-/
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

/--
%%handwave
name:
  Pointwise formula for postcomposing a simplex
statement:
  For a smooth map \(f:M\to N\), a smooth simplex \(\sigma\), and
  \(q\in\Delta^k\), \((f\circ\sigma)(q)=f(\sigma(q))\).
proof:
  This is the definition of postcomposition.
-/
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

/--
%%handwave
name:
  Faces commute with postcomposition
statement:
  For every face \(i\) of a smooth simplex \(\sigma\) and smooth map \(f\),
  \((f\circ\sigma)|_i=f\circ(\sigma|_i)\).
proof:
  Both simplices are the same composition with the \(i\)-th face map.
-/
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

/--
%%handwave
name:
  Postcomposition preserves the zero chain
statement:
  For every smooth map \(f\), the pushforward by postcomposition sends the
  zero singular chain to zero.
proof:
  Postcomposition of chains is induced by mapping the simplex basis.
-/
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

/--
%%handwave
name:
  Postcomposition is additive on chains
statement:
  For smooth singular chains \(c,d\),
  \(f_*(c+d)=f_*c+f_*d\).
proof:
  Mapping the simplex basis defines an additive homomorphism on finitely
  supported chains.
-/
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

/--
%%handwave
name:
  Postcomposition respects integer multiples
statement:
  For \(m\in\mathbb Z\) and a smooth singular chain \(c\),
  \(f_*(m c)=m f_*c\).
proof:
  The map on chains induced by postcomposition is additive and therefore
  commutes with integer scalar multiplication.
-/
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

/--
%%handwave
name:
  Postcomposition of a singleton chain
statement:
  For a smooth simplex \(\sigma\) and \(m\in\mathbb Z\),
  \(f_*(m[\sigma])=m[f\circ\sigma]\).
proof:
  Mapping a finitely supported singleton replaces its simplex by its
  postcomposition and leaves its coefficient unchanged.
-/
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

/--
%%handwave
name:
  Naturality of the boundary under postcomposition
statement:
  For every smooth singular chain \(c\) and smooth map \(f\),
  \(f_*(\partial c)=\partial(f_*c)\).
proof:
  Reduce linearly to a simplex.  Postcomposition commutes with every face map,
  so the two alternating face sums agree term by term.
-/
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

/--
%%handwave
name:
  Pointwise formula for inclusion of an open-subset simplex
statement:
  If \(U\subseteq M\) is open, \(\sigma:\Delta^k\to U\), and
  \(q\in\Delta^k\), then the included simplex takes \(q\) to the underlying
  point of \(\sigma(q)\) in \(M\).
proof:
  This is the definition of inclusion.
-/
@[simp]
theorem ContMDiffSingularSimplex.openInclusion_apply
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r)
    (q : StandardSimplex k) :
    sigma.openInclusion (I := I) U q = (sigma q : M) :=
  rfl

/--
%%handwave
name:
  Injectivity of including simplices from an open subset
statement:
  Inclusion \(U\hookrightarrow M\) induces an injective map from smooth
  simplices in \(U\) to smooth simplices in \(M\).
proof:
  Equality after inclusion gives equality of underlying points because the
  subtype inclusion is injective, hence equality of the original simplices.
-/
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

/--
%%handwave
name:
  Faces commute with open inclusion
statement:
  For a simplex \(\sigma\) in an open subset \(U\), including its \(i\)-th
  face in \(M\) equals the \(i\)-th face of the included simplex.
proof:
  Both are obtained by composing \(\sigma\) first with the face map and then
  with \(U\hookrightarrow M\).
-/
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

/--
%%handwave
name:
  Open inclusion preserves the zero chain
statement:
  The inclusion \(U\hookrightarrow M\) sends the zero singular chain to zero.
proof:
  Inclusion of chains is induced by mapping the simplex basis.
-/
@[simp]
theorem SingularChain.openInclusion_zero
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞} :
    SingularChain.openInclusion (I := I) U
        (0 : SingularChain (I := I) (M := U) k r) = 0 := by
  simp [SingularChain.openInclusion]

/--
%%handwave
name:
  Open inclusion is additive on chains
statement:
  For chains \(c,d\) in \(U\), \(\iota_*(c+d)=\iota_*c+\iota_*d\).
proof:
  Mapping the simplex basis under inclusion defines an additive homomorphism.
-/
@[simp]
theorem SingularChain.openInclusion_add
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (c d : SingularChain (I := I) (M := U) k r) :
    SingularChain.openInclusion (I := I) U (c + d) =
      SingularChain.openInclusion (I := I) U c +
        SingularChain.openInclusion (I := I) U d := by
  exact Finsupp.mapDomain_add

/--
%%handwave
name:
  Open inclusion respects subtraction of chains
statement:
  For chains \(c,d\) in \(U\), \(\iota_*(c-d)=\iota_*c-\iota_*d\).
proof:
  The inclusion-induced map on chains is an additive homomorphism.
-/
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

/--
%%handwave
name:
  Open inclusion respects integer multiples
statement:
  For \(m\in\mathbb Z\) and a chain \(c\) in \(U\),
  \(\iota_*(m c)=m\iota_*c\).
proof:
  The inclusion-induced map on chains is additive.
-/
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

/--
%%handwave
name:
  Open inclusion of a singleton chain
statement:
  For a simplex \(\sigma\) in \(U\) and \(m\in\mathbb Z\),
  \(\iota_*(m[\sigma])=m[\iota\circ\sigma]\).
proof:
  Mapping a finitely supported singleton includes its simplex and preserves
  its coefficient.
-/
@[simp]
theorem SingularChain.openInclusion_single
    (U : TopologicalSpace.Opens M) {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r) (n : ℤ) :
    SingularChain.openInclusion (I := I) U (Finsupp.single sigma n) =
      Finsupp.single (sigma.openInclusion (I := I) U) n := by
  simp [SingularChain.openInclusion]

/--
%%handwave
name:
  Naturality of the boundary under open inclusion
statement:
  For a smooth chain \(c\) in an open subset \(U\subseteq M\),
  \(\iota_*(\partial c)=\partial(\iota_*c)\).
proof:
  Reduce linearly to a simplex.  Inclusion commutes with each face, so the
  alternating boundary sums agree.
-/
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

/--
%%handwave
name:
  Pointwise formula for inclusion between nested open subsets
statement:
  If \(U\subseteq V\) are open and \(\sigma:\Delta^k\to U\), then at every
  \(q\in\Delta^k\) the included simplex is the image of \(\sigma(q)\) under
  \(U\hookrightarrow V\).
proof:
  This is the defining formula for nested inclusion.
-/
@[simp]
theorem ContMDiffSingularSimplex.nestedOpenInclusion_apply
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r)
    (q : StandardSimplex k) :
    sigma.nestedOpenInclusion (I := I) hUV q =
      TopologicalSpace.Opens.inclusion hUV (sigma q) :=
  rfl

/--
%%handwave
name:
  Faces commute with nested open inclusion
statement:
  If \(U\subseteq V\), including the \(i\)-th face of a simplex in \(U\)
  equals taking the \(i\)-th face after inclusion into \(V\).
proof:
  Both maps compose the simplex with the face map and the inclusion
  \(U\hookrightarrow V\).
-/
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

/--
%%handwave
name:
  Nested open inclusion preserves the zero chain
statement:
  For \(U\subseteq V\), the induced map on chains sends \(0\) to \(0\).
proof:
  It is induced by mapping the simplex basis.
-/
@[simp]
theorem SingularChain.nestedOpenInclusion_zero
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞} :
    SingularChain.nestedOpenInclusion (I := I) hUV
        (0 : SingularChain (I := I) (M := U) k r) = 0 := by
  simp [SingularChain.nestedOpenInclusion]

/--
%%handwave
name:
  Nested open inclusion of a singleton chain
statement:
  For \(U\subseteq V\), a simplex \(\sigma\) in \(U\), and \(m\in\mathbb Z\),
  the included chain \(m[\sigma]\) is \(m\) times the included simplex.
proof:
  Mapping a finitely supported singleton preserves its coefficient.
-/
@[simp]
theorem SingularChain.nestedOpenInclusion_single
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (sigma : ContMDiffSingularSimplex (I := I) (M := U) k r) (n : ℤ) :
    SingularChain.nestedOpenInclusion (I := I) hUV
        (Finsupp.single sigma n) =
      Finsupp.single (sigma.nestedOpenInclusion (I := I) hUV) n := by
  simp [SingularChain.nestedOpenInclusion]

/--
%%handwave
name:
  Nested open inclusion is additive on chains
statement:
  For \(U\subseteq V\) and chains \(c,d\) in \(U\),
  \(\iota_*(c+d)=\iota_*c+\iota_*d\).
proof:
  Inclusion acts by an additive map on finitely supported simplex
  coefficients.
-/
@[simp]
theorem SingularChain.nestedOpenInclusion_add
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    {k : ℕ} {r : WithTop ℕ∞}
    (c d : SingularChain (I := I) (M := U) k r) :
    SingularChain.nestedOpenInclusion (I := I) hUV (c + d) =
      SingularChain.nestedOpenInclusion (I := I) hUV c +
        SingularChain.nestedOpenInclusion (I := I) hUV d := by
  exact Finsupp.mapDomain_add

/--
%%handwave
name:
  Nested open inclusion respects subtraction
statement:
  For \(U\subseteq V\) and chains \(c,d\) in \(U\),
  \(\iota_*(c-d)=\iota_*c-\iota_*d\).
proof:
  The inclusion-induced map on chains is additive.
-/
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

/--
%%handwave
name:
  Nested open inclusion respects integer multiples
statement:
  For \(U\subseteq V\), \(m\in\mathbb Z\), and a chain \(c\) in \(U\),
  \(\iota_*(m c)=m\iota_*c\).
proof:
  The inclusion-induced map on chains is additive.
-/
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

/--
%%handwave
name:
  Naturality of the boundary under nested open inclusion
statement:
  If \(U\subseteq V\) and \(c\) is a smooth chain in \(U\), then
  \(\iota_*(\partial c)=\partial(\iota_*c)\).
proof:
  Reduce linearly to a simplex and use that inclusion commutes with every face
  map.
-/
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

/--
%%handwave
name:
  Pullback coefficient under inclusion of nested open subsets
statement:
  Let \(U\subseteq V\), let \(\omega\) be a smooth \(k\)-form on \(V\), and
  let \(\sigma:\Delta^k\to U\).  At every simplex coordinate \(x\), the
  pullback coefficient of \(\omega\) along the included simplex equals that
  of \(\omega|_U\) along \(\sigma\).
proof:
  The included parameterization is the inclusion composed with the original
  one.  The chain rule identifies its derivative, and the definition of
  restriction composes \(\omega\) with exactly that inclusion derivative.
-/
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

/--
%%handwave
name:
  Simplex integration under inclusion of nested open subsets
statement:
  If \(U\subseteq V\), \(\omega\) is a smooth \(k\)-form on \(V\), and
  \(\sigma:\Delta^k\to U\), then
  \[
    \int_{\iota\circ\sigma}\omega=\int_\sigma\omega|_U.
  \]
proof:
  The two pullback coefficients agree pointwise on the common simplex
  coordinate domain, so their integrals agree.
-/
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

/--
%%handwave
name:
  Chain integration under inclusion of nested open subsets
statement:
  If \(U\subseteq V\), \(\omega\) is a smooth \(k\)-form on \(V\), and \(c\)
  is a smooth \(k\)-chain in \(U\), then
  \[
    \int_{\iota_*c}\omega=\int_c\omega|_U.
  \]
proof:
  Reduce linearly to a singleton simplex and apply the corresponding simplex
  integration identity.
-/
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

/--
%%handwave
name:
  Pullback coefficient under a diffeomorphism
statement:
  Let \(\phi:M\to N\) be a diffeomorphism, \(\omega\) a smooth \(k\)-form on
  \(N\), and \(\sigma:\Delta^k\to M\).  At every simplex coordinate \(x\),
  the coefficient of \(\omega\) along \(\phi\circ\sigma\) equals the
  coefficient of \(\phi^*\omega\) along \(\sigma\).
proof:
  The chain rule gives
  \(D(\phi\circ\sigma)=D\phi\circ D\sigma\), exactly matching the definition
  of pullback of a differential form.
-/
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

/--
%%handwave
name:
  Simplex integration under a diffeomorphism
statement:
  For a diffeomorphism \(\phi:M\to N\), smooth \(k\)-form \(\omega\) on
  \(N\), and smooth simplex \(\sigma\) in \(M\),
  \[
    \int_{\phi\circ\sigma}\omega=\int_\sigma\phi^*\omega.
  \]
proof:
  The pullback coefficients agree pointwise by the chain rule, hence their
  simplex integrals agree.
-/
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

/--
%%handwave
name:
  Chain integration under a diffeomorphism
statement:
  For a diffeomorphism \(\phi:M\to N\), a smooth \(k\)-form \(\omega\) on
  \(N\), and a smooth \(k\)-chain \(c\) in \(M\),
  \[
    \int_{\phi_*c}\omega=\int_c\phi^*\omega.
  \]
proof:
  Reduce linearly to a simplex and apply the simplex change-of-variables
  identity.
-/
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

/--
%%handwave
name:
  Pullback coefficient under inclusion of an open subset
statement:
  Let \(U\subseteq M\) be open, \(\omega\) a smooth \(k\)-form on \(M\), and
  \(\sigma:\Delta^k\to U\).  At every simplex coordinate, the coefficient of
  \(\omega\) along the included simplex equals that of \(\omega|_U\) along
  \(\sigma\).
proof:
  Apply the chain rule to the inclusion composed with the simplex
  parameterization; restriction of \(\omega\) inserts the same inclusion
  derivative.
-/
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

/--
%%handwave
name:
  Simplex integration under open inclusion
statement:
  For \(U\subseteq M\) open, a smooth \(k\)-form \(\omega\) on \(M\), and
  \(\sigma:\Delta^k\to U\),
  \[
    \int_{\iota\circ\sigma}\omega=\int_\sigma\omega|_U.
  \]
proof:
  The two simplex pullback coefficients agree pointwise on their common
  coordinate domain.
-/
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

/--
%%handwave
name:
  Integration of one simplex under open inclusion
statement:
  If \(\sigma\) is a smooth \(k\)-simplex in an open subset \(U\subseteq M\),
  then
  \[
    \int_{[\iota\circ\sigma]}\omega=\int_{[\sigma]}\omega|_U.
  \]
proof:
  Integration over a singleton chain is the associated simplex integral, and
  simplex integration commutes with open inclusion.
-/
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

/--
%%handwave
name:
  Chain integration under open inclusion
statement:
  For an open subset \(U\subseteq M\), a smooth \(k\)-form \(\omega\) on
  \(M\), and a smooth \(k\)-chain \(c\) in \(U\),
  \[
    \int_{\iota_*c}\omega=\int_c\omega|_U.
  \]
proof:
  Reduce linearly to singleton chains and apply the corresponding simplex
  identity.
-/
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

/--
%%handwave
name:
  Integral of the zero form
statement:
  For every smooth \(k\)-chain \(c\), \(\int_c0=0\).
proof:
  Reduce linearly to a simplex; its pullback coefficient is identically zero,
  so the simplex integral vanishes.
-/
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

/--
%%handwave
name:
  Closed forms have zero integral over boundaries
statement:
  If \(\omega\) is a closed smooth \(k\)-form and \(c\) is a smooth
  \((k+1)\)-chain, then \(\int_{\partial c}\omega=0\).
proof:
  By Stokes,
  \(\int_{\partial c}\omega=\int_c d\omega\), and \(d\omega=0\).
-/
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

/--
%%handwave
name:
  Fundamental theorem for a smooth zero-form
statement:
  For a smooth zero-form \(\theta\) and smooth singular one-simplex
  \(\sigma:[0,1]\to M\),
  \[
    \int_\sigma d\theta=\theta_{\sigma(1)}-\theta_{\sigma(0)}.
  \]
proof:
  Apply Stokes to \(\sigma\).  Its oriented boundary is the terminal vertex
  minus the initial vertex, and integration of a zero-form over a vertex is
  pointwise evaluation.
-/
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

/--
%%handwave
name:
  Fundamental theorem for an exact form extended by zero
statement:
  Let \(f:M\to\mathbb R\) be smooth and extend \(df\) by zero outside a set
  \(U\), assuming it vanishes near the frontier.  If a smooth one-simplex
  \(\sigma\) lies in \(U\), then
  \[
    \int_\sigma \widetilde{df}
      =f(\sigma(1))-f(\sigma(0)).
  \]
proof:
  Along \(\sigma\), the extension agrees pointwise with \(df\), so the
  simplex integral agrees with that of \(df\).  Apply the fundamental theorem
  for a smooth one-simplex.
-/
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

/--
%%handwave
name:
  A nonzero period detects a nonzero de Rham class
statement:
  If a closed smooth one-form \(\omega\) has nonzero integral over a smooth
  one-cycle \(c\), then \([\omega]\ne0\) in
  \(H_{\mathrm{dR}}^1(M;\mathbb R)\).
proof:
  If \([\omega]=0\), then \(\omega\) is exact.  Stokes forces every exact
  one-form to have zero integral over the cycle \(c\), contradicting the
  nonzero period.
-/
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

/--
%%handwave
name:
  A nonzero local period detects a nonzero restricted class
statement:
  Let \(W\subseteq V\) be open.  If a closed one-form \(\omega\) on \(V\)
  has nonzero period after restriction to a one-cycle \(c\) in \(W\), then
  the restricted class \([\omega]|_W\) is nonzero in
  \(H_{\mathrm{dR}}^1(W;\mathbb R)\).
proof:
  The restricted form is closed and retains the asserted nonzero period.
  Hence its de Rham class is nonzero by the period criterion.
-/
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

/--
%%handwave
name:
  Nontrivial cohomology from a crossing and a zero-period return
statement:
  Let \(\omega\) be a closed one-form.  If a crossing chain \(c\) and return
  chain \(e\) satisfy \(\partial(c+e)=0\),
  \(\int_c\omega=1\), and \(\int_e\omega=0\), then
  \(H_{\mathrm{dR}}^1(M;\mathbb R)\) is not a singleton.
proof:
  Additivity gives \(\int_{c+e}\omega=1\).  Thus the cycle \(c+e\) has a
  nonzero period, which detects a nonzero first de Rham class.
-/
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
