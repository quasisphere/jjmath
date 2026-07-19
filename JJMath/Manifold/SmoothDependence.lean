import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smooth dependence for autonomous ordinary differential equations

For curves on a compact symmetric time interval, the Volterra integral is a
bounded linear operator on the Banach space of continuous curves.  Pointwise
composition with a smooth map is smooth in the supremum norm when the source
is finite-dimensional.  These facts turn the integral equation for an
autonomous ODE into a smooth implicit equation.

The final theorems construct a local flow germ which is smooth jointly in its
initial value and time.  They are formulated independently of manifolds so
that local coordinate vector fields can use them directly.
-/

open Set MeasureTheory Filter
open Asymptotics
open scoped Interval ENat ContDiff Topology

noncomputable section

namespace JJMath.Manifold

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/--
%%handwave
name:
  Local regularity of an implicit function on a common neighborhood
statement:
  Let \(f:E_1\times E_2\to F\) be \(C^n\), with \(n\ne0\), and suppose the
  derivative of \(f\) in the \(E_2\)-direction is invertible at \(u\).
  Then the implicit function obtained at \(u\) is \(C^n\) at every \(x\) in
  some neighborhood of \(u_1\).
proof:
  The implicit-function construction locally identifies
  \((x,y)\mapsto(f(x,y),x)\) with a homeomorphism.  Its derivative remains
  invertible near \(u\), so the inverse function theorem makes the inverse
  \(C^n\) on a common target neighborhood; taking its second component gives
  the implicit function.
-/
theorem ContDiff.eventually_contDiffAt_implicitFunction
    {𝕜 : Type*} [RCLike 𝕜]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u : E₁ × E₂} {f : E₁ × E₂ → F} {n : WithTop ℕ∞}
    (hf : ContDiff 𝕜 n f) (hn : n ≠ 0)
    (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1,
      ContDiffAt 𝕜 n (hf.contDiffAt.implicitFunction hn if₂) x := by
  let cdf : ContDiffAt 𝕜 n f u := hf.contDiffAt
  let φ := (cdf.hasStrictFDerivAt hn).implicitFunctionDataOfProdDomain if₂
  let P := φ.toOpenPartialHomeomorph
  have hprod : ContDiff 𝕜 n φ.prodFun := by
    simpa only [φ, ImplicitFunctionData.prodFun_apply,
      HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
      HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain] using
      hf.prodMk contDiff_fst
  let e₀ : (E₁ × E₂) ≃L[𝕜] (F × E₁) :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
      φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hderiv0 : fderiv 𝕜 φ.prodFun u =
      (e₀ : (E₁ × E₂) →L[𝕜] (F × E₁)) := by
    exact φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have hderivEquiv : ∀ᶠ z : E₁ × E₂ in 𝓝 u,
      fderiv 𝕜 φ.prodFun z ∈
        range ((↑) : ((E₁ × E₂) ≃L[𝕜] (F × E₁)) →
          ((E₁ × E₂) →L[𝕜] (F × E₁))) := by
    apply hprod.continuous_fderiv hn |>.continuousAt.eventually
      (ContinuousLinearEquiv.isOpen.mem_nhds ?_)
    exact ⟨e₀, hderiv0.symm⟩
  have hregular : ∀ᶠ z : E₁ × E₂ in 𝓝 u,
      ∃ L : (E₁ × E₂) ≃L[𝕜] (F × E₁),
        HasFDerivAt φ.prodFun (L : (E₁ × E₂) →L[𝕜] (F × E₁)) z := by
    filter_upwards [hderivEquiv] with z hz
    rcases hz with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    rw [hL]
    exact (hprod.differentiable hn).differentiableAt.hasFDerivAt
  have hu : φ.pt = u := by rfl
  have htarget : φ.prodFun u ∈ P.target := by
    simpa only [P, hu] using φ.map_pt_mem_toOpenPartialHomeomorph_target
  have hsource : u ∈ P.source := by
    simpa only [P, hu] using φ.pt_mem_toOpenPartialHomeomorph_source
  have hsymmcenter : P.symm (φ.prodFun u) = u := by
    rw [← ImplicitFunctionData.toOpenPartialHomeomorph_coe]
    exact P.left_inv hsource
  have hregularTarget : ∀ᶠ q : F × E₁ in 𝓝 (φ.prodFun u),
      ∃ L : (E₁ × E₂) ≃L[𝕜] (F × E₁),
        HasFDerivAt P (L : (E₁ × E₂) →L[𝕜] (F × E₁)) (P.symm q) := by
    have htendsto : Tendsto P.symm (𝓝 (φ.prodFun u)) (𝓝 u) := by
      have h := P.continuousAt_symm htarget
      rw [ContinuousAt, hsymmcenter] at h
      exact h
    have hpre := htendsto.eventually hregular
    filter_upwards [hpre] with q hq
    rcases hq with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    simpa only [P, ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hL
  have hinverseSmooth : ∀ᶠ q : F × E₁ in 𝓝 (φ.prodFun u),
      ContDiffAt 𝕜 n P.symm q := by
    filter_upwards [P.open_target.mem_nhds htarget, hregularTarget] with q hq hregular
    rcases hregular with ⟨L, hL⟩
    apply P.contDiffAt_symm hq hL
    simpa only [P, ImplicitFunctionData.toOpenPartialHomeomorph_coe] using
      hprod.contDiffAt
  have hpair : ContDiffAt 𝕜 n (fun x : E₁ => (f u, x)) u.1 := by
    fun_prop
  have hcenter : (f u, u.1) = φ.prodFun u := by
    simp only [φ, ImplicitFunctionData.prodFun_apply,
      HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
      HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain]
  have hnear : ∀ᶠ x : E₁ in 𝓝 u.1,
      ContDiffAt 𝕜 n P.symm (f u, x) := by
    rw [← hcenter] at hinverseSmooth
    exact hpair.continuousAt.eventually hinverseSmooth
  filter_upwards [hnear] with x hx
  have hpairsmooth : ContDiffAt 𝕜 n (fun y : E₁ => (f u, y)) x := by
    fun_prop
  have hsnd : ContDiffAt 𝕜 n (fun y : E₁ => (P.symm (f u, y)).2) x := by
    exact contDiffAt_snd.comp x (hx.comp x hpairsmooth)
  simpa only [cdf, φ, P, ContDiffAt.implicitFunction_def,
    HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
    ImplicitFunctionData.implicitFunction_apply] using hsnd

abbrev LocalCurve (E : Type*) [TopologicalSpace E] (ε : ℝ) := C(Icc (-ε) ε, E)

def extendLocalCurve (ε : ℝ) (hε : 0 ≤ ε) (f : LocalCurve E ε) : ℝ → E :=
  fun t ↦ f (projIcc (-ε) ε (neg_le_self hε) t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/--
%%handwave
name:
  Continuity of extending a curve by endpoint projection
statement:
  If \(\varepsilon\ge0\) and
  \(u:[-\varepsilon,\varepsilon]\to E\) is continuous, then
  \(t\mapsto u(\operatorname{proj}_{[-\varepsilon,\varepsilon]}t)\) is
  continuous on \(\mathbb R\).
proof:
  The metric projection onto a closed interval is continuous, so the result
  follows by composition.
-/
theorem extendLocalCurve_continuous (ε : ℝ) (hε : 0 ≤ ε) (f : LocalCurve E ε) :
    Continuous (extendLocalCurve ε hε f) :=
  f.continuous.comp continuous_projIcc

def localCurveIntegralFun (ε : ℝ) (hε : 0 ≤ ε) (f : LocalCurve E ε) :
    LocalCurve E ε where
  toFun t := ∫ s : ℝ in 0..(t : ℝ), extendLocalCurve ε hε f s
  continuous_toFun :=
    (intervalIntegral.continuous_primitive
      (fun a b ↦ (extendLocalCurve_continuous ε hε f).intervalIntegrable a b) 0).comp
        continuous_subtype_val

omit [CompleteSpace E] in
/--
%%handwave
name:
  Additivity of the Volterra integral on local curves
statement:
  For continuous curves \(u,v:[-\varepsilon,\varepsilon]\to E\),
  \[
    \int_0^t(u+v)(s)\,ds=\int_0^tu(s)\,ds+\int_0^tv(s)\,ds
  \]
  for every \(t\in[-\varepsilon,\varepsilon]\).
proof:
  This is additivity of the interval integral.
-/
theorem localCurveIntegralFun_add (ε : ℝ) (hε : 0 ≤ ε)
    (f g : LocalCurve E ε) :
    localCurveIntegralFun ε hε (f + g) =
      localCurveIntegralFun ε hε f + localCurveIntegralFun ε hε g := by
  ext t
  change (∫ s : ℝ in 0..(t : ℝ),
      extendLocalCurve ε hε (f + g) s) = _
  simp only [extendLocalCurve, ContinuousMap.add_apply]
  rw [intervalIntegral.integral_add]
  · rfl
  · exact ((extendLocalCurve_continuous ε hε f).intervalIntegrable 0 t)
  · exact ((extendLocalCurve_continuous ε hε g).intervalIntegrable 0 t)

omit [CompleteSpace E] in
/--
%%handwave
name:
  Homogeneity of the Volterra integral on local curves
statement:
  For \(c\in\mathbb R\) and a continuous curve
  \(u:[-\varepsilon,\varepsilon]\to E\),
  \[
    \int_0^t c\,u(s)\,ds=c\int_0^t u(s)\,ds.
  \]
proof:
  This is homogeneity of the interval integral.
-/
theorem localCurveIntegralFun_smul (ε : ℝ) (hε : 0 ≤ ε) (c : ℝ)
    (f : LocalCurve E ε) :
    localCurveIntegralFun ε hε (c • f) = c • localCurveIntegralFun ε hε f := by
  ext t
  change (∫ s : ℝ in 0..(t : ℝ),
      extendLocalCurve ε hε (c • f) s) = _
  simp only [extendLocalCurve, ContinuousMap.smul_apply]
  exact intervalIntegral.integral_smul c _

def localCurveIntegralLinearMap (ε : ℝ) (hε : 0 ≤ ε) :
    LocalCurve E ε →ₗ[ℝ] LocalCurve E ε where
  toFun := localCurveIntegralFun ε hε
  map_add' := localCurveIntegralFun_add ε hε
  map_smul' := localCurveIntegralFun_smul ε hε

omit [CompleteSpace E] in
/--
%%handwave
name:
  Supremum estimate for the Volterra integral
statement:
  If \(\varepsilon\ge0\) and
  \(u:[-\varepsilon,\varepsilon]\to E\) is continuous, then
  \[
    \sup_{|t|\le\varepsilon}\left\|\int_0^tu(s)\,ds\right\|
    \le\varepsilon\|u\|_\infty.
  \]
proof:
  The norm of each interval integral is at most
  \(|t|\|u\|_\infty\), and \(|t|\le\varepsilon\).
-/
theorem localCurveIntegralFun_norm_le (ε : ℝ) (hε : 0 ≤ ε)
    (f : LocalCurve E ε) :
    ‖localCurveIntegralFun ε hε f‖ ≤ ε * ‖f‖ := by
  apply (ContinuousMap.norm_le (localCurveIntegralFun ε hε f)
    (mul_nonneg hε (norm_nonneg f))).2
  intro t
  change ‖∫ s : ℝ in 0..(t : ℝ), extendLocalCurve ε hε f s‖ ≤ _
  calc
    _ ≤ ‖f‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _hs ↦
        ContinuousMap.norm_coe_le_norm f _
    _ ≤ ‖f‖ * ε := by
      gcongr
      simpa only [sub_zero] using (abs_le.mpr t.2)
    _ = ε * ‖f‖ := mul_comm _ _

def localCurveIntegral (ε : ℝ) (hε : 0 ≤ ε) :
    LocalCurve E ε →L[ℝ] LocalCurve E ε :=
  (localCurveIntegralLinearMap ε hε).mkContinuous ε
    (localCurveIntegralFun_norm_le ε hε)

omit [CompleteSpace E] in
/--
%%handwave
name:
  Formula for the Volterra integral operator
statement:
  For \(u:[-\varepsilon,\varepsilon]\to E\) and
  \(t\in[-\varepsilon,\varepsilon]\), the bounded Volterra operator satisfies
  \[
    (Vu)(t)=\int_0^t\widetilde u(s)\,ds,
  \]
  where \(\widetilde u\) is obtained by projecting time to the interval.
proof:
  This is the defining formula of the bounded linear operator.
-/
@[simp]
theorem localCurveIntegral_apply (ε : ℝ) (hε : 0 ≤ ε)
    (f : LocalCurve E ε) (t : Icc (-ε) ε) :
    localCurveIntegral ε hε f t =
      ∫ s : ℝ in 0..(t : ℝ), extendLocalCurve ε hε f s :=
  rfl

omit [CompleteSpace E] in
/--
%%handwave
name:
  Operator norm of the Volterra integral
statement:
  For \(\varepsilon\ge0\), the Volterra operator on continuous curves over
  \([-\varepsilon,\varepsilon]\) has operator norm at most \(\varepsilon\).
proof:
  Apply the supremum estimate
  \(\|Vu\|_\infty\le\varepsilon\|u\|_\infty\).
-/
theorem norm_localCurveIntegral_le (ε : ℝ) (hε : 0 ≤ ε) :
    ‖localCurveIntegral (ε := ε) hε (E := E)‖ ≤ ε :=
  LinearMap.mkContinuous_norm_le _ hε (localCurveIntegralFun_norm_le ε hε)

section PointwiseApply

variable {K : Type*} {F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pointwiseApplyFun (A : C(K, E →L[ℝ] F)) (f : C(K, E)) : C(K, F) where
  toFun x := A x (f x)
  continuous_toFun := A.continuous.clm_apply f.continuous

omit [CompleteSpace E] [CompactSpace K] in
/--
%%handwave
name:
  Additivity of pointwise operator evaluation in the operator field
statement:
  For continuous operator fields \(A,B:K\to\mathcal L(E,F)\) and
  \(u:K\to E\), \((A+B)u=Au+Bu\) pointwise on \(K\).
proof:
  Evaluate at each \(x\in K\) and use additivity of operator evaluation.
-/
theorem pointwiseApplyFun_add_left (A B : C(K, E →L[ℝ] F)) (f : C(K, E)) :
    pointwiseApplyFun (A + B) f = pointwiseApplyFun A f + pointwiseApplyFun B f := by
  ext x
  rfl

omit [CompleteSpace E] [CompactSpace K] in
/--
%%handwave
name:
  Homogeneity of pointwise operator evaluation in the operator field
statement:
  For \(c\in\mathbb R\), \(A:K\to\mathcal L(E,F)\), and \(u:K\to E\),
  \((cA)u=c(Au)\) pointwise.
proof:
  Evaluate at each point and use homogeneity of operator evaluation.
-/
theorem pointwiseApplyFun_smul_left (c : ℝ) (A : C(K, E →L[ℝ] F)) (f : C(K, E)) :
    pointwiseApplyFun (c • A) f = c • pointwiseApplyFun A f := by
  ext x
  rfl

omit [CompleteSpace E] [CompactSpace K] in
/--
%%handwave
name:
  Additivity of pointwise operator evaluation in the vector field
statement:
  For \(A:K\to\mathcal L(E,F)\) and continuous \(u,v:K\to E\),
  \(A(u+v)=Au+Av\) pointwise.
proof:
  Each operator \(A(x)\) is linear.
-/
theorem pointwiseApplyFun_add_right (A : C(K, E →L[ℝ] F)) (f g : C(K, E)) :
    pointwiseApplyFun A (f + g) = pointwiseApplyFun A f + pointwiseApplyFun A g := by
  ext x
  exact map_add (A x) (f x) (g x)

omit [CompleteSpace E] [CompactSpace K] in
/--
%%handwave
name:
  Homogeneity of pointwise operator evaluation in the vector field
statement:
  For \(c\in\mathbb R\), \(A:K\to\mathcal L(E,F)\), and \(u:K\to E\),
  \(A(cu)=c(Au)\) pointwise.
proof:
  Each operator \(A(x)\) is linear.
-/
theorem pointwiseApplyFun_smul_right (c : ℝ) (A : C(K, E →L[ℝ] F)) (f : C(K, E)) :
    pointwiseApplyFun A (c • f) = c • pointwiseApplyFun A f := by
  ext x
  exact map_smul (A x) c (f x)

def pointwiseApplyLinearMap :
    C(K, E →L[ℝ] F) →ₗ[ℝ] C(K, E) →ₗ[ℝ] C(K, F) where
  toFun A :=
    { toFun := pointwiseApplyFun A
      map_add' := pointwiseApplyFun_add_right A
      map_smul' := fun c f ↦ pointwiseApplyFun_smul_right c A f }
  map_add' A B := by
    ext f x
    rfl
  map_smul' c A := by
    ext f x
    rfl

omit [CompleteSpace E] in
/--
%%handwave
name:
  Norm bound for pointwise operator evaluation
statement:
  For continuous \(A:K\to\mathcal L(E,F)\) and \(u:K\to E\),
  \[
    \|x\mapsto A(x)u(x)\|_\infty
      \le\|A\|_\infty\|u\|_\infty.
  \]
proof:
  Pointwise, \(\|A(x)u(x)\|\le\|A(x)\|\|u(x)\|\); take suprema.
-/
theorem pointwiseApplyFun_norm_le (A : C(K, E →L[ℝ] F)) (f : C(K, E)) :
    ‖pointwiseApplyFun A f‖ ≤ ‖A‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le (pointwiseApplyFun A f)
    (mul_nonneg (norm_nonneg A) (norm_nonneg f))).2
  intro x
  exact (ContinuousLinearMap.le_opNorm (A x) (f x)).trans
    (mul_le_mul (ContinuousMap.norm_coe_le_norm A x)
      (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _) (norm_nonneg _))

def pointwiseApplyRight (A : C(K, E →L[ℝ] F)) :
    C(K, E) →L[ℝ] C(K, F) :=
  ((pointwiseApplyLinearMap (E := E) (F := F) (K := K)) A).mkContinuous ‖A‖
    (pointwiseApplyFun_norm_le (E := E) (F := F) (K := K) A)

omit [CompleteSpace E] in
/--
%%handwave
name:
  Operator norm bound for a fixed pointwise operator field
statement:
  For a continuous operator field \(A:K\to\mathcal L(E,F)\), the operator
  \(u\mapsto(x\mapsto A(x)u(x))\) has norm at most \(\|A\|_\infty\).
proof:
  This is the pointwise evaluation norm estimate, viewed as an operator bound.
-/
theorem pointwiseApplyRight_norm_le (A : C(K, E →L[ℝ] F)) :
    ‖pointwiseApplyRight (E := E) (F := F) (K := K) A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A)
    (pointwiseApplyFun_norm_le (E := E) (F := F) (K := K) A)

def pointwiseApplyOuterLinearMap :
    C(K, E →L[ℝ] F) →ₗ[ℝ] C(K, E) →L[ℝ] C(K, F) where
  toFun := pointwiseApplyRight
  map_add' A B := by
    ext f x
    rfl
  map_smul' c A := by
    ext f x
    rfl

def pointwiseApply :
    C(K, E →L[ℝ] F) →L[ℝ] C(K, E) →L[ℝ] C(K, F) where
  toFun := pointwiseApplyRight
  map_add' A B := by
    ext f x
    rfl
  map_smul' c A := by
    ext f x
    rfl
  cont := continuous_of_linear_of_bound (𝕜 := ℝ) (C := 1)
    (fun A B ↦ (pointwiseApplyOuterLinearMap (E := E) (F := F) (K := K)).map_add A B)
    (fun c A ↦ (pointwiseApplyOuterLinearMap (E := E) (F := F) (K := K)).map_smul c A)
    (fun A ↦ by simpa using
      pointwiseApplyRight_norm_le (E := E) (F := F) (K := K) A)

omit [CompleteSpace E] in
/--
%%handwave
name:
  Formula for the bilinear pointwise evaluation map
statement:
  For \(A:K\to\mathcal L(E,F)\), \(u:K\to E\), and \(x\in K\), the
  continuous bilinear evaluation map satisfies
  \[
    \mathcal E(A,u)(x)=A(x)u(x).
  \]
proof:
  This is its defining formula.
-/
@[simp]
theorem pointwiseApply_apply (A : C(K, E →L[ℝ] F)) (f : C(K, E)) (x : K) :
    pointwiseApply (E := E) (F := F) (K := K) A f x = A x (f x) := by
  change pointwiseApplyRight (E := E) (F := F) (K := K) A f x = A x (f x)
  rfl

end PointwiseApply

section Superposition

variable {K : Type*} {F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E]

def superposition (f : E → F) (hf : Continuous f) (u : C(K, E)) : C(K, F) where
  toFun t := f (u t)
  continuous_toFun := hf.comp u.continuous

def fderivAlong (f : E → F) (hf : ContDiff ℝ 1 f) (u : C(K, E)) :
    C(K, E →L[ℝ] F) where
  toFun t := fderiv ℝ f (u t)
  continuous_toFun := (hf.continuous_fderiv (by norm_num)).comp u.continuous

def superpositionFDeriv (f : E → F) (hf : ContDiff ℝ 1 f) (u : C(K, E)) :
    C(K, E) →L[ℝ] C(K, F) :=
  pointwiseApply (E := E) (F := F) (K := K) (fderivAlong f hf u)

omit [NormedSpace ℝ E] [CompleteSpace E] [CompactSpace K]
  [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Formula for a superposition operator
statement:
  For \(f:E\to F\), \(u:K\to E\), and \(t\in K\), the superposition
  operator satisfies \(\mathcal N_f(u)(t)=f(u(t))\).
proof:
  This is the defining formula.
-/
@[simp]
theorem superposition_apply (f : E → F) (hf : Continuous f) (u : C(K, E)) (t : K) :
    superposition f hf u t = f (u t) :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Formula for the derivative candidate of a superposition operator
statement:
  For \(f:E\to F\) of class \(C^1\) and continuous \(u,h:K\to E\),
  \[
    (D\mathcal N_f(u)h)(t)=Df(u(t))h(t).
  \]
proof:
  This is the pointwise evaluation formula for the derivative field
  \(t\mapsto Df(u(t))\).
-/
@[simp]
theorem superpositionFDeriv_apply (f : E → F) (hf : ContDiff ℝ 1 f)
    (u h : C(K, E)) (t : K) :
    superpositionFDeriv f hf u h t = fderiv ℝ f (u t) (h t) := by
  simp [superpositionFDeriv, fderivAlong]

omit [CompleteSpace E] [CompleteSpace F] in
/--
%%handwave
name:
  Fréchet derivative of a superposition operator
statement:
  Let \(K\) be compact and \(E\) finite-dimensional.  If \(f:E\to F\) is
  \(C^1\), then at \(u\in C(K,E)\) the superposition map
  \(\mathcal N_f(u)=f\circ u\) has derivative
  \[
    D\mathcal N_f(u)h:t\mapsto Df(u(t))h(t).
  \]
proof:
  On a compact thickening of \(u(K)\), \(Df\) is uniformly continuous.  The
  finite-dimensional mean-value estimate then bounds the remainder uniformly
  by \(o(\|h\|_\infty)\).
-/
theorem superposition_hasFDerivAt (f : E → F) (hf : ContDiff ℝ 1 f)
    (u : C(K, E)) :
    HasFDerivAt (superposition f hf.continuous)
      (superpositionFDeriv f hf u) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply isLittleO_iff.2
  intro c hc
  let S : Set E := Metric.cthickening 1 (range u)
  have hScompact : IsCompact S :=
    (isCompact_range u.continuous).cthickening
  have hfuniform : UniformContinuousOn (fderiv ℝ f) S :=
    hScompact.uniformContinuousOn_of_continuous
      (hf.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp hfuniform c hc
  have hrpos : 0 < min δ 1 := lt_min hδpos zero_lt_one
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, E)) hrpos] with h hh
  have hhnorm : ‖h‖ < min δ 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hh
  have hhδ : ‖h‖ < δ := hhnorm.trans_le (min_le_left _ _)
  have hh1 : ‖h‖ < 1 := hhnorm.trans_le (min_le_right _ _)
  apply (ContinuousMap.norm_le
    (superposition f hf.continuous (u + h) - superposition f hf.continuous u -
      superpositionFDeriv f hf u h)
    (mul_nonneg hc.le (norm_nonneg h))).2
  intro t
  let x : E := u t
  let y : E := u t + h t
  have hxrange : x ∈ range u := ⟨t, rfl⟩
  have hxS : x ∈ S := by
    exact Metric.mem_cthickening_of_dist_le x x 1 (range u) hxrange (by simp)
  have hxy : ‖y - x‖ = ‖h t‖ := by
    simp [x, y]
  have hxy_le : ‖y - x‖ ≤ ‖h‖ := by
    rw [hxy]
    exact ContinuousMap.norm_coe_le_norm h t
  have hsegmentS : segment ℝ x y ⊆ S := by
    intro z hz
    apply Metric.closedBall_subset_cthickening hxrange 1
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_sub_le_of_mem_segment hz).trans (hxy_le.trans hh1.le)
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ c := by
    intro z hz
    have hzx : dist z x < δ := by
      rw [dist_eq_norm]
      exact (norm_sub_le_of_mem_segment hz).trans_lt (hxy_le.trans_lt hhδ)
    have := hδ z (hsegmentS hz) x hxS hzx
    simpa [dist_eq_norm] using this.le
  simp only [ContinuousMap.sub_apply, superposition_apply, ContinuousMap.add_apply,
    superpositionFDeriv_apply]
  have hrem := ((convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _hz ↦ (hf.differentiable (by norm_num)) z) hbound
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)).trans
      (mul_le_mul_of_nonneg_left hxy_le hc.le)
  simpa [x, y] using hrem

omit [CompleteSpace E] [CompleteSpace F] in
/--
%%handwave
name:
  Differentiability of a superposition operator
statement:
  If \(K\) is compact, \(E\) is finite-dimensional, and \(f:E\to F\) is
  \(C^1\), then \(u\mapsto f\circ u\) is Fréchet differentiable on \(C(K,E)\).
proof:
  At every \(u\), its derivative is the pointwise operator
  \(h(t)\mapsto Df(u(t))h(t)\).
-/
theorem superposition_differentiable (f : E → F) (hf : ContDiff ℝ 1 f) :
    Differentiable ℝ (superposition (K := K) f hf.continuous) :=
  fun u ↦ (superposition_hasFDerivAt (K := K) f hf u).differentiableAt

omit [CompleteSpace E] [CompleteSpace F] in
/--
%%handwave
name:
  Derivative formula for a superposition operator
statement:
  Under the same hypotheses, the Fréchet derivative at \(u\) is
  \[
    D\mathcal N_f(u)h:t\mapsto Df(u(t))h(t).
  \]
proof:
  This is the derivative identified by the uniform remainder estimate.
-/
theorem fderiv_superposition (f : E → F) (hf : ContDiff ℝ 1 f) (u : C(K, E)) :
    fderiv ℝ (superposition (K := K) f hf.continuous) u =
      superpositionFDeriv (K := K) f hf u :=
  (superposition_hasFDerivAt (K := K) f hf u).fderiv

omit [CompleteSpace E] in
/--
%%handwave
name:
  Finite regularity of superposition operators
statement:
  For every \(n\in\mathbb N\), if \(f:E\to G\) is \(C^{n+1}\), then the
  superposition map \(u\mapsto f\circ u\) on \(C(K,E)\) is \(C^n\).
proof:
  Induct on \(n\).  The derivative is pointwise multiplication by
  \(Df\circ u\); the induction hypothesis applies to the superposition
  operator associated with \(Df\), and continuous pointwise evaluation
  preserves the remaining regularity.
-/
theorem superposition_contDiff_nat : ∀ n : ℕ,
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G],
      ∀ (f : E → G), ∀ hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f,
        ContDiff ℝ (n : WithTop ℕ∞) (superposition (K := K) f hf.continuous) := by
  intro n
  induction n with
  | zero =>
      intro G instG instSG instCG f hf
      exact contDiff_zero.mpr (superposition_differentiable (K := K) f
        (by simpa using hf)).continuous
  | succ n ih =>
      intro G instG instSG instCG f hf
      have htarget : ContDiff ℝ ((n : WithTop ℕ∞) + 1)
          (superposition (K := K) f hf.continuous) := by
        rw [contDiff_succ_iff_fderiv]
        have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
        refine ⟨superposition_differentiable (K := K) f hf1, ?_, ?_⟩
        · simp
        · let g : E → E →L[ℝ] G := fderiv ℝ f
          have hg : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) g := by
            exact hf.fderiv_right (by simp only [Nat.cast_succ]; rfl)
          have hNg : ContDiff ℝ (n : WithTop ℕ∞)
              (superposition g hg.continuous) :=
            ih (G := E →L[ℝ] G) g hg
          have hpointwise : ContDiff ℝ (n : WithTop ℕ∞)
              (fun u : C(K, E) ↦
                pointwiseApply (E := E) (F := G) (K := K)
                  (superposition g hg.continuous u)) :=
            by simpa [Function.comp_def] using
              (pointwiseApply (E := E) (F := G) (K := K)).contDiff.comp hNg
          convert hpointwise using 1
          funext u
          rw [fderiv_superposition f hf1 u]
          apply ContinuousLinearMap.ext
          intro h
          apply ContinuousMap.ext
          intro t
          rfl
      simpa only [Nat.cast_succ] using htarget

omit [CompleteSpace E] in
/--
%%handwave
name:
  Smoothness of superposition operators
statement:
  If \(K\) is compact, \(E\) is finite-dimensional, and \(f:E\to F\) is
  smooth, then \(u\mapsto f\circ u\) is smooth from \(C(K,E)\) to \(C(K,F)\).
proof:
  Smoothness means \(C^n\) for every finite \(n\); apply the finite-regularity
  theorem to each \(n\).
-/
theorem superposition_contDiff_infty (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superposition (K := K) f hf.continuous) := by
  rw [contDiff_infty]
  intro n
  have hn : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.mpr le_top
  exact superposition_contDiff_nat n f (hf.of_le hn)

end Superposition

section PicardResidual

variable [FiniteDimensional ℝ E]

def picardResidual (ε : ℝ) (hε : 0 ≤ ε) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (p : E × LocalCurve E ε) : LocalCurve E ε :=
  p.2 - ContinuousMap.const (Icc (-ε) ε) p.1 -
    localCurveIntegral ε hε (superposition f hf.continuous p.2)

/--
%%handwave
name:
  Smoothness of the Picard residual
statement:
  If \(f:E\to E\) is smooth, then
  \[
    R(x,u)=u-\underline{x}-V(f\circ u)
  \]
  is a smooth map from \(E\times C([-\varepsilon,\varepsilon],E)\) to the
  curve space, where \(V\) is the Volterra operator.
proof:
  Projection, the constant-curve embedding, and the Volterra operator are
  continuous linear maps, while the superposition map \(u\mapsto f\circ u\)
  is smooth.  Sums and compositions preserve smoothness.
-/
theorem picardResidual_contDiff (ε : ℝ) (hε : 0 ≤ ε) (f : E → E)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (picardResidual ε hε f hf) := by
  let C : E →L[ℝ] LocalCurve E ε :=
    ContinuousLinearMap.const ℝ (Icc (-ε) ε)
  let I : LocalCurve E ε →L[ℝ] LocalCurve E ε := localCurveIntegral ε hε
  apply ContDiff.sub
  · exact contDiff_snd.sub
      (by simpa [C, Function.comp_def] using C.contDiff.comp contDiff_fst)
  · simpa [I, Function.comp_def] using I.contDiff.comp
      ((superposition_contDiff_infty (K := Icc (-ε) ε) f hf).comp contDiff_snd)

def picardResidualFDeriv (ε : ℝ) (hε : 0 ≤ ε) (f : E → E)
    (hf : ContDiff ℝ ∞ f) (p : E × LocalCurve E ε) :
    (E × LocalCurve E ε) →L[ℝ] LocalCurve E ε :=
  ContinuousLinearMap.snd ℝ E (LocalCurve E ε) -
    (ContinuousLinearMap.const ℝ (Icc (-ε) ε)).comp
      (ContinuousLinearMap.fst ℝ E (LocalCurve E ε)) -
    (localCurveIntegral ε hε).comp
      ((superpositionFDeriv f (hf.of_le (by simp)) p.2).comp
        (ContinuousLinearMap.snd ℝ E (LocalCurve E ε)))

omit [CompleteSpace E] in
/--
%%handwave
name:
  Derivative of the Picard residual
statement:
  At \((x,u)\), the Picard residual has derivative
  \[
    DR(x,u)(\xi,h)=h-\underline{\xi}-V\bigl(t\mapsto Df(u(t))h(t)\bigr).
  \]
proof:
  Differentiate the two linear terms directly, use the derivative formula for
  the superposition operator, and compose with the Volterra operator.
-/
theorem picardResidual_hasFDerivAt (ε : ℝ) (hε : 0 ≤ ε) (f : E → E)
    (hf : ContDiff ℝ ∞ f) (p : E × LocalCurve E ε) :
    HasFDerivAt (picardResidual ε hε f hf)
      (picardResidualFDeriv ε hε f hf p) p := by
  have hsnd : HasFDerivAt (fun q : E × LocalCurve E ε ↦ q.2)
      (ContinuousLinearMap.snd ℝ E (LocalCurve E ε)) p :=
    (ContinuousLinearMap.snd ℝ E (LocalCurve E ε)).hasFDerivAt
  have hconst : HasFDerivAt
      (fun q : E × LocalCurve E ε ↦ ContinuousMap.const (Icc (-ε) ε) q.1)
      ((ContinuousLinearMap.const ℝ (Icc (-ε) ε)).comp
        (ContinuousLinearMap.fst ℝ E (LocalCurve E ε))) p :=
    by
      let C : E →L[ℝ] LocalCurve E ε :=
        ContinuousLinearMap.const ℝ (Icc (-ε) ε)
      simpa [C, Function.comp_def] using C.hasFDerivAt.comp p
        (ContinuousLinearMap.fst ℝ E (LocalCurve E ε)).hasFDerivAt
  have hsuper : HasFDerivAt
      (fun q : E × LocalCurve E ε ↦ superposition f hf.continuous q.2)
      ((superpositionFDeriv f (hf.of_le (by simp)) p.2).comp
        (ContinuousLinearMap.snd ℝ E (LocalCurve E ε))) p :=
    (superposition_hasFDerivAt f (hf.of_le (by simp)) p.2).comp p hsnd
  have hint : HasFDerivAt
      (fun q : E × LocalCurve E ε ↦
        localCurveIntegral ε hε (superposition f hf.continuous q.2))
      ((localCurveIntegral ε hε).comp
        ((superpositionFDeriv f (hf.of_le (by simp)) p.2).comp
          (ContinuousLinearMap.snd ℝ E (LocalCurve E ε)))) p :=
    by
      let I : LocalCurve E ε →L[ℝ] LocalCurve E ε := localCurveIntegral ε hε
      simpa [I, Function.comp_def] using I.hasFDerivAt.comp p hsuper
  exact hsnd.sub hconst |>.sub hint

def picardCurveDerivative (ε : ℝ) (hε : 0 ≤ ε) (f : E → E)
    (hf : ContDiff ℝ ∞ f) (u : LocalCurve E ε) :
    LocalCurve E ε →L[ℝ] LocalCurve E ε :=
  ContinuousLinearMap.id ℝ (LocalCurve E ε) -
    (localCurveIntegral ε hε).comp
      (superpositionFDeriv f (hf.of_le (by simp)) u)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Vertical derivative of the Picard residual
statement:
  At \((x,u)\), the derivative of the Picard residual in the curve variable
  is
  \[
    h\longmapsto h-V\bigl(t\mapsto Df(u(t))h(t)\bigr).
  \]
proof:
  Insert the vertical tangent vector \((0,h)\) into the full derivative
  formula; the constant-curve term disappears.
-/
theorem picardResidualFDeriv_comp_inr (ε : ℝ) (hε : 0 ≤ ε)
    (f : E → E) (hf : ContDiff ℝ ∞ f) (p : E × LocalCurve E ε) :
    (picardResidualFDeriv ε hε f hf p).comp
        (ContinuousLinearMap.inr ℝ E (LocalCurve E ε)) =
      picardCurveDerivative ε hε f hf p.2 := by
  ext h t
  simp [picardResidualFDeriv, picardCurveDerivative]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Norm bound for the linearized superposition operator
statement:
  If \(\|Df(u(t))\|\le M\) for every \(t\), with \(M\ge0\), then the operator
  \(h(t)\mapsto Df(u(t))h(t)\) on continuous curves has norm at most \(M\).
proof:
  Pointwise evaluation has norm bounded by the supremum of
  \(\|Df(u(t))\|\), which is at most \(M\).
-/
theorem superpositionFDeriv_norm_le_of_forall (ε : ℝ) (f : E → E)
    (hf : ContDiff ℝ 1 f) (u : LocalCurve E ε) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ t, ‖fderiv ℝ f (u t)‖ ≤ M) :
    ‖superpositionFDeriv f hf u‖ ≤ M := by
  apply (pointwiseApplyRight_norm_le (E := E) (F := E)
    (K := Icc (-ε) ε) (fderivAlong f hf u)).trans
  apply (ContinuousMap.norm_le (fderivAlong f hf u) hM0).2
  exact hM

omit [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Invertibility of the linearized Picard operator
statement:
  Suppose \(\varepsilon\ge0\), \(\|Df(u(t))\|\le M\), \(M\ge0\), and
  \(\varepsilon M<1\).  Then
  \[
    I-V\bigl(Df\circ u\bigr)
  \]
  is invertible on \(C([-\varepsilon,\varepsilon],E)\).
proof:
  The Volterra norm bound and the derivative bound give
  \(\|V(Df\circ u)\|<1\).  Hence the Neumann-series criterion makes
  \(I-V(Df\circ u)\) invertible.
-/
theorem picardCurveDerivative_isInvertible_of_small (ε : ℝ) (hε : 0 ≤ ε)
    (f : E → E) (hf : ContDiff ℝ ∞ f) (u : LocalCurve E ε) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ t, ‖fderiv ℝ f (u t)‖ ≤ M) (hsmall : ε * M < 1) :
    (picardCurveDerivative ε hε f hf u).IsInvertible := by
  let A : LocalCurve E ε →L[ℝ] LocalCurve E ε :=
    (localCurveIntegral ε hε).comp
      (superpositionFDeriv f (hf.of_le (by simp)) u)
  have hA : ‖A‖ < 1 := by
    apply lt_of_le_of_lt ((localCurveIntegral ε hε).opNorm_comp_le
      (superpositionFDeriv f (hf.of_le (by simp)) u))
    exact (mul_le_mul (norm_localCurveIntegral_le ε hε)
      (superpositionFDeriv_norm_le_of_forall ε f (hf.of_le (by simp)) u hM0 hM)
      (norm_nonneg (superpositionFDeriv f (hf.of_le (by simp)) u)) hε).trans_lt hsmall
  have hunit : IsUnit ((1 : LocalCurve E ε →L[ℝ] LocalCurve E ε) - A) :=
    isUnit_one_sub_of_norm_lt_one (R := LocalCurve E ε →L[ℝ] LocalCurve E ε) hA
  rcases hunit with ⟨a, ha⟩
  refine ⟨ContinuousLinearEquiv.ofUnit a, ?_⟩
  change (↑a : LocalCurve E ε →L[ℝ] LocalCurve E ε) =
    picardCurveDerivative ε hε f hf u
  simpa [picardCurveDerivative, A] using ha

/--
%%handwave
name:
  Locally unique smooth family of Picard fixed points
statement:
  Let \(u:[-\varepsilon,\varepsilon]\to E\) solve
  \[
    u(t)=x+\int_0^t f(u(s))\,ds.
  \]
  If \(\|Df(u(t))\|\le M\), \(M\ge0\), and \(\varepsilon M<1\), then there
  is a family \(y\mapsto\psi_y\), smooth at every nearby \(y\), with
  \(\psi_x=u\), satisfying the same integral equation with initial value
  \(y\); moreover, near \((x,u)\), a pair \((y,v)\) solves the equation if
  and only if \(v=\psi_y\).
proof:
  Apply the smooth implicit-function theorem to the Picard residual.  Its
  vertical derivative is invertible by the Neumann-series estimate, and the
  residual equation is precisely the Picard fixed-point equation.
-/
theorem exists_contDiffAt_picardFixedPoint_family_unique
    (ε : ℝ) (hε : 0 ≤ ε) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (x : E) (u : LocalCurve E ε) {M : ℝ}
    (hfixed : u = ContinuousMap.const (Icc (-ε) ε) x +
      localCurveIntegral ε hε (superposition f hf.continuous u))
    (hM0 : 0 ≤ M) (hM : ∀ t, ‖fderiv ℝ f (u t)‖ ≤ M)
    (hsmall : ε * M < 1) :
    ∃ ψ : E → LocalCurve E ε,
      ψ x = u ∧ ContDiffAt ℝ ∞ ψ x ∧
        (∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ ψ y) ∧
        (∀ᶠ y in 𝓝 x,
          ψ y = ContinuousMap.const (Icc (-ε) ε) y +
            localCurveIntegral ε hε (superposition f hf.continuous (ψ y))) ∧
        ∀ᶠ p in 𝓝 (x, u),
          picardResidual ε hε f hf p = 0 ↔ ψ p.1 = p.2 := by
  let F : E × LocalCurve E ε → LocalCurve E ε := picardResidual ε hε f hf
  have hF : ContDiff ℝ ∞ F := picardResidual_contDiff ε hε f hf
  have hderiv : fderiv ℝ F (x, u) = picardResidualFDeriv ε hε f hf (x, u) :=
    (picardResidual_hasFDerivAt ε hε f hf (x, u)).fderiv
  have hinv : ((fderiv ℝ F (x, u)).comp
      (ContinuousLinearMap.inr ℝ E (LocalCurve E ε))).IsInvertible := by
    rw [hderiv, picardResidualFDeriv_comp_inr]
    exact picardCurveDerivative_isInvertible_of_small ε hε f hf u hM0 hM hsmall
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ : E → LocalCurve E ε := hF.contDiffAt.implicitFunction hn hinv
  have hψx : ψ x = u := by
    exact hF.contDiffAt.implicitFunction_apply_self hn hinv
  have hψsmooth : ContDiffAt ℝ ∞ ψ x :=
    hF.contDiffAt.contDiffAt_implicitFunction hn hinv
  have hψsmoothNear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ ψ y := by
    exact ContDiff.eventually_contDiffAt_implicitFunction hF hn hinv
  have hres0 : F (x, u) = 0 := by
    change u - ContinuousMap.const (Icc (-ε) ε) x -
      localCurveIntegral ε hε (superposition f hf.continuous u) = 0
    nth_rewrite 1 [hfixed]
    abel
  have heq : ∀ᶠ y in 𝓝 x, F (y, ψ y) = F (x, u) :=
    hF.contDiffAt.eventually_apply_implicitFunction hn hinv
  have hfixedψ : ∀ᶠ y in 𝓝 x,
      ψ y = ContinuousMap.const (Icc (-ε) ε) y +
        localCurveIntegral ε hε (superposition f hf.continuous (ψ y)) := by
    filter_upwards [heq] with y hy
    rw [hres0] at hy
    change ψ y - ContinuousMap.const (Icc (-ε) ε) y -
      localCurveIntegral ε hε (superposition f hf.continuous (ψ y)) = 0 at hy
    calc
      ψ y = (ψ y - ContinuousMap.const (Icc (-ε) ε) y -
            localCurveIntegral ε hε (superposition f hf.continuous (ψ y))) +
          ContinuousMap.const (Icc (-ε) ε) y +
            localCurveIntegral ε hε (superposition f hf.continuous (ψ y)) := by abel
      _ = ContinuousMap.const (Icc (-ε) ε) y +
            localCurveIntegral ε hε (superposition f hf.continuous (ψ y)) := by
          rw [hy]
          simp
  have hunique : ∀ᶠ p in 𝓝 (x, u), F p = 0 ↔ ψ p.1 = p.2 := by
    filter_upwards [hF.contDiffAt.eventually_apply_eq_iff_implicitFunction hn hinv]
      with p hp
    simpa only [hres0] using hp
  exact ⟨ψ, hψx, hψsmooth, hψsmoothNear, hfixedψ, hunique⟩

/--
%%handwave
name:
  Smooth dependence of Picard fixed points on initial values
statement:
  Let \(u:[-\varepsilon,\varepsilon]\to E\) satisfy
  \[
    u(t)=x+\int_0^t f(u(s))\,ds,
  \]
  where \(f:E\to E\) is smooth.  If \(\|Df(u(t))\|\leq M\),
  \(M\geq0\), and \(\varepsilon M<1\), then there is a family
  \(y\mapsto\psi_y\) defined near \(x\), smooth at every nearby initial
  value, with \(\psi_x=u\) and
  \[
    \psi_y(t)=y+\int_0^t f(\psi_y(s))\,ds.
  \]
proof:
  [The implicit-function theorem gives a unique smooth local family of fixed points of the Picard operator](lean:JJMath.Manifold.exists_contDiffAt_picardFixedPoint_family_unique); discard the uniqueness clause and retain its smoothness, base value, and fixed-point equation.
-/
theorem exists_contDiffAt_picardFixedPoint_family
    (ε : ℝ) (hε : 0 ≤ ε) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (x : E) (u : LocalCurve E ε) {M : ℝ}
    (hfixed : u = ContinuousMap.const (Icc (-ε) ε) x +
      localCurveIntegral ε hε (superposition f hf.continuous u))
    (hM0 : 0 ≤ M) (hM : ∀ t, ‖fderiv ℝ f (u t)‖ ≤ M)
    (hsmall : ε * M < 1) :
    ∃ ψ : E → LocalCurve E ε,
      ψ x = u ∧ ContDiffAt ℝ ∞ ψ x ∧
        (∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ ψ y) ∧
        ∀ᶠ y in 𝓝 x,
          ψ y = ContinuousMap.const (Icc (-ε) ε) y +
            localCurveIntegral ε hε (superposition f hf.continuous (ψ y)) := by
  rcases exists_contDiffAt_picardFixedPoint_family_unique ε hε f hf x u hfixed
      hM0 hM hsmall with ⟨ψ, hψx, hψ, hψNear, hfixedψ, _⟩
  exact ⟨ψ, hψx, hψ, hψNear, hfixedψ⟩

/-- Reparametrize a local curve by the affine time map `τ ↦ t₀ + aτ`, while
remembering the scale `a` as a constant second coordinate. -/
def rescaleLocalCurve (ε : ℝ) (hε : 0 ≤ ε) (η t₀ : ℝ)
    (p : LocalCurve E ε × ℝ) : LocalCurve (E × ℝ) η where
  toFun τ :=
    (extendLocalCurve ε hε p.1 (t₀ + p.2 * (τ : ℝ)), p.2)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (extendLocalCurve_continuous ε hε p.1).comp
        (continuous_const.add (continuous_const.mul continuous_subtype_val))
    · exact continuous_const

omit [NormedSpace ℝ E] [CompleteSpace E] in
/--
%%handwave
name:
  Continuity of affine time rescaling of local curves
statement:
  Fix \(\varepsilon\ge0\), an auxiliary interval
  \([-\eta,\eta]\), and \(t_0\in\mathbb R\).  The map
  \[
    (u,a)\longmapsto\bigl(\tau\mapsto
      (\widetilde u(t_0+a\tau),a)\bigr)
  \]
  from local curves and scales to continuous \(E\times\mathbb R\)-valued
  curves is continuous in the supremum norm.
proof:
  Joint evaluation of continuous maps on a compact domain is continuous; the
  projected affine time argument and the constant scale coordinate are also
  continuous.
-/
theorem rescaleLocalCurve_continuous (ε : ℝ) (hε : 0 ≤ ε) (η t₀ : ℝ) :
    Continuous (rescaleLocalCurve (E := E) ε hε η t₀) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Continuous.prodMk
  · change Continuous (fun q : (LocalCurve E ε × ℝ) × Icc (-η) η =>
        q.1.1 (projIcc (-ε) ε (neg_le_self hε)
          (t₀ + q.1.2 * (q.2 : ℝ))))
    have ht : Continuous (fun q : (LocalCurve E ε × ℝ) × Icc (-η) η =>
        t₀ + q.1.2 * (q.2 : ℝ)) :=
      continuous_const.add (continuous_fst.snd.mul continuous_snd.subtype_val)
    have hp : Continuous (fun q : (LocalCurve E ε × ℝ) × Icc (-η) η =>
        projIcc (-ε) ε (neg_le_self hε) (t₀ + q.1.2 * (q.2 : ℝ))) :=
      continuous_projIcc.comp ht
    exact continuous_eval.comp (continuous_fst.fst.prodMk hp)
  · exact continuous_fst.snd

/-- The autonomous vector field which turns time rescaling into an initial-value
parameter. -/
def timeScaleVectorField (f : E → E) (p : E × ℝ) : E × ℝ :=
  (p.2 • f p.1, 0)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Smoothness of the time-scaled vector field
statement:
  If \(f:E\to E\) is smooth, then
  \(G(z,a)=(a f(z),0)\) is a smooth vector field on
  \(E\times\mathbb R\).
proof:
  It is assembled from projections, the smooth map \(f\), scalar
  multiplication, and a constant component.
-/
theorem timeScaleVectorField_contDiff (f : E → E) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (timeScaleVectorField f) := by
  unfold timeScaleVectorField
  fun_prop

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Extended local curve on its original interval
statement:
  If \(t\in[-\varepsilon,\varepsilon]\), then the endpoint-projected
  extension of \(u\) satisfies \(\widetilde u(t)=u(t)\).
proof:
  Projection onto the interval fixes every point already in the interval.
-/
@[simp]
theorem extendLocalCurve_apply_of_mem (ε : ℝ) (hε : 0 ≤ ε)
    (u : LocalCurve E ε) {t : ℝ} (ht : t ∈ Icc (-ε) ε) :
    extendLocalCurve ε hε u t = u ⟨t, ht⟩ := by
  simp [extendLocalCurve, projIcc_of_mem (neg_le_self hε) ht]

omit [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Affine time rescaling of a Picard solution
statement:
  Let \(u\) solve \(u'=f(u)\), \(u(0)=y\), on
  \([-\varepsilon,\varepsilon]\).  If
  \(t_0+a[-\eta,\eta]\subseteq[-\varepsilon,\varepsilon]\), then
  \[
    w(\tau)=(u(t_0+a\tau),a)
  \]
  satisfies
  \[
    w(\tau)=w(0)+\int_0^\tau (a f(w_1(s)),0)\,ds.
  \]
proof:
  Subtract the integral equation for \(u(t_0)\) from that for
  \(u(t_0+a\tau)\), then use the affine change of variables
  \(s=t_0+a r\).  The scale coordinate is constant.
-/
theorem rescaleLocalCurve_fixedPoint
    (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (y : E) (u : LocalCurve E ε) (t₀ a : ℝ)
    (ht₀ : t₀ ∈ Icc (-ε) ε)
    (htime : ∀ τ : Icc (-η) η,
      t₀ + a * (τ : ℝ) ∈ Icc (-ε) ε)
    (hfixed : u = ContinuousMap.const (Icc (-ε) ε) y +
      localCurveIntegral ε hε (superposition f hf.continuous u)) :
    rescaleLocalCurve ε hε η t₀ (u, a) =
      ContinuousMap.const (Icc (-η) η) (u ⟨t₀, ht₀⟩, a) +
        localCurveIntegral η hη
          (superposition (timeScaleVectorField f)
            (timeScaleVectorField_contDiff f hf).continuous
            (rescaleLocalCurve ε hε η t₀ (u, a))) := by
  let g : ℝ → E := fun s => f (extendLocalCurve ε hε u s)
  have hg : Continuous g :=
    hf.continuous.comp (extendLocalCurve_continuous ε hε u)
  have hfixed_apply (q : Icc (-ε) ε) :
      u q = y + ∫ s : ℝ in 0..(q : ℝ), g s := by
    have h := congrArg (fun v : LocalCurve E ε => v q) hfixed
    simpa [g, localCurveIntegral_apply] using h
  have hbetween (q : ℝ) (hq : q ∈ Icc (-ε) ε) :
      u ⟨q, hq⟩ = u ⟨t₀, ht₀⟩ + ∫ s : ℝ in t₀..q, g s := by
    rw [hfixed_apply ⟨q, hq⟩, hfixed_apply ⟨t₀, ht₀⟩]
    have hadd :
        (∫ s : ℝ in 0..t₀, g s) + ∫ s : ℝ in t₀..q, g s =
          ∫ s : ℝ in 0..q, g s :=
      intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable 0 t₀) (hg.intervalIntegrable t₀ q)
    rw [← hadd]
    abel
  let w : LocalCurve (E × ℝ) η :=
    superposition (timeScaleVectorField f)
      (timeScaleVectorField_contDiff f hf).continuous
      (rescaleLocalCurve ε hε η t₀ (u, a))
  have hw : Continuous (extendLocalCurve η hη w) :=
    extendLocalCurve_continuous η hη w
  ext τ <;> simp only [rescaleLocalCurve, ContinuousMap.add_apply,
    ContinuousMap.const_apply]
  · change extendLocalCurve ε hε u (t₀ + a * (τ : ℝ)) =
      u ⟨t₀, ht₀⟩ + ((localCurveIntegral η hη w) τ).1
    rw [extendLocalCurve_apply_of_mem ε hε u (htime τ)]
    rw [hbetween (t₀ + a * (τ : ℝ)) (htime τ)]
    congr 1
    rw [localCurveIntegral_apply]
    have hfst :
        (∫ s : ℝ in 0..(τ : ℝ), extendLocalCurve η hη w s).1 =
          ∫ s : ℝ in 0..(τ : ℝ), (extendLocalCurve η hη w s).1 := by
      symm
      simpa using (ContinuousLinearMap.fst ℝ E ℝ).intervalIntegral_comp_comm
        (hw.intervalIntegrable 0 (τ : ℝ))
    rw [hfst]
    symm
    calc
      (∫ s : ℝ in 0..(τ : ℝ), (extendLocalCurve η hη w s).1) =
          ∫ s : ℝ in 0..(τ : ℝ), a • g (a * s + t₀) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hzero : (0 : ℝ) ∈ Icc (-η) η := by constructor <;> linarith
        have hsIcc : s ∈ Icc (-η) η :=
          uIcc_subset_Icc hzero τ.2 hs
        change (extendLocalCurve η hη w s).1 = a • g (a * s + t₀)
        rw [extendLocalCurve_apply_of_mem η hη w hsIcc]
        simp [w, timeScaleVectorField, superposition, rescaleLocalCurve, g,
          add_comm t₀ (a * s)]
      _ = a • ∫ s : ℝ in 0..(τ : ℝ), g (a * s + t₀) := by
        rw [intervalIntegral.integral_smul]
      _ = ∫ s : ℝ in t₀..t₀ + a * (τ : ℝ), g s := by
        simpa only [zero_mul, mul_zero, zero_add,
          add_comm (a * (τ : ℝ)) t₀] using
          intervalIntegral.smul_integral_comp_mul_add
            (a := 0) (b := (τ : ℝ)) g a t₀
  · rw [localCurveIntegral_apply]
    change a = a + (∫ s : ℝ in 0..(τ : ℝ),
      extendLocalCurve η hη w s).2
    have hsnd :
        (∫ s : ℝ in 0..(τ : ℝ), extendLocalCurve η hη w s).2 =
          ∫ s : ℝ in 0..(τ : ℝ), (extendLocalCurve η hη w s).2 := by
      symm
      simpa using (ContinuousLinearMap.snd ℝ E ℝ).intervalIntegral_comp_comm
        (hw.intervalIntegrable 0 (τ : ℝ))
    rw [hsnd]
    rw [eq_comm, add_eq_left]
    calc
      (∫ s : ℝ in 0..(τ : ℝ), (extendLocalCurve η hη w s).2) =
          ∫ _s : ℝ in 0..(τ : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        change (timeScaleVectorField f
          ((rescaleLocalCurve ε hε η t₀ (u, a))
            (projIcc (-η) η (neg_le_self hη) s))).2 = 0
        rfl
      _ = 0 := by simp

/--
%%handwave
name:
  Uniformly admissible small affine time rescalings
statement:
  If \(t_0\in(-\varepsilon,\varepsilon)\), then for every compact interval
  \([-\eta,\eta]\), all sufficiently small \(a\) satisfy
  \[
    t_0+a\tau\in[-\varepsilon,\varepsilon]
    \quad\text{for every }\tau\in[-\eta,\eta].
  \]
proof:
  The compact set \(\{0\}\times[-\eta,\eta]\) lies in the open inverse image
  of \((-\varepsilon,\varepsilon)\) under \((a,\tau)\mapsto t_0+a\tau\).
  The tube lemma supplies a common neighborhood of \(a=0\).
-/
theorem eventually_forall_affine_mem_Icc
    (ε η t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (-ε) ε) :
    ∀ᶠ a in 𝓝 (0 : ℝ), ∀ τ : Icc (-η) η,
      t₀ + a * (τ : ℝ) ∈ Icc (-ε) ε := by
  let N : Set (ℝ × ℝ) :=
    (fun p : ℝ × ℝ => t₀ + p.1 * p.2) ⁻¹' Ioo (-ε) ε
  have hNopen : IsOpen N := isOpen_Ioo.preimage (by fun_prop)
  have hsubset : ({0} : Set ℝ) ×ˢ Icc (-η) η ⊆ N := by
    rintro ⟨_, τ⟩ ⟨rfl, hτ⟩
    simpa [N] using ht₀
  rcases generalized_tube_lemma isCompact_singleton isCompact_Icc hNopen hsubset with
    ⟨U, V, hUopen, _hVopen, hzeroU, hIccV, hUV⟩
  filter_upwards [hUopen.mem_nhds (hzeroU rfl)] with a ha
  intro τ
  have hmem : (a, (τ : ℝ)) ∈ U ×ˢ V := ⟨ha, hIccV τ.2⟩
  have h := hUV hmem
  exact ⟨h.1.le, h.2.le⟩

/--
%%handwave
name:
  Joint smoothness of a local Picard family at an interior time
statement:
  Suppose \(y\mapsto\psi_y\) is smooth at \(x\), \(\psi_x=u\), and nearby
  curves satisfy
  \[
    \psi_y(t)=y+\int_0^t f(\psi_y(s))\,ds.
  \]
  Then for every \(t_0\in(-\varepsilon,\varepsilon)\), the evaluation map
  \[
    (y,t)\longmapsto\widetilde{\psi_y}(t)
  \]
  is smooth at \((x,t_0)\).
proof:
  Rescale time around \(t_0\) and regard the scale as an initial-value
  parameter for the vector field \((z,a)\mapsto(a f(z),0)\).  The implicit
  Picard family for this time-scaled field is jointly smooth; local uniqueness
  identifies it with the rescaled original family, and undoing the affine
  rescaling yields the claim.
-/
theorem contDiffAt_uncurry_extendLocalCurve_of_picardFixedPoint
    (ε : ℝ) (hε : 0 ≤ ε) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (x : E) (u : LocalCurve E ε) (ψ : E → LocalCurve E ε)
    (hψx : ψ x = u) (hψ : ContDiffAt ℝ ∞ ψ x)
    (hfixedψ : ∀ᶠ y in 𝓝 x,
      ψ y = ContinuousMap.const (Icc (-ε) ε) y +
        localCurveIntegral ε hε (superposition f hf.continuous (ψ y)))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (-ε) ε) :
    ContDiffAt ℝ ∞
      (fun p : E × ℝ => extendLocalCurve ε hε (ψ p.1) p.2)
      (x, t₀) := by
  let q₀ : Icc (-ε) ε := ⟨t₀, ⟨ht₀.1.le, ht₀.2.le⟩⟩
  let z₀ : E := u q₀
  let g : E × ℝ → E × ℝ := timeScaleVectorField f
  have hg : ContDiff ℝ ∞ g := timeScaleVectorField_contDiff f hf
  let M : ℝ := ‖fderiv ℝ g (z₀, 0)‖
  let η : ℝ := 1 / (M + 1)
  have hM0 : 0 ≤ M := norm_nonneg _
  have hM1 : 0 < M + 1 := by linarith
  have hη : 0 < η := one_div_pos.mpr hM1
  have hηsmall : η * M < 1 := by
    dsimp [η]
    rw [one_div, inv_mul_eq_div]
    exact (div_lt_one hM1).2 (by linarith)
  let v₀ : LocalCurve (E × ℝ) η :=
    ContinuousMap.const (Icc (-η) η) (z₀, 0)
  have hfixedu : u = ContinuousMap.const (Icc (-ε) ε) x +
      localCurveIntegral ε hε (superposition f hf.continuous u) := by
    have hx := mem_of_mem_nhds hfixedψ
    change ψ x = ContinuousMap.const (Icc (-ε) ε) x +
      localCurveIntegral ε hε (superposition f hf.continuous (ψ x)) at hx
    simpa only [hψx] using hx
  have htime0 : ∀ τ : Icc (-η) η,
      t₀ + (0 : ℝ) * (τ : ℝ) ∈ Icc (-ε) ε := by
    intro τ
    simpa [q₀] using q₀.2
  have hbase := rescaleLocalCurve_fixedPoint ε η hε hη.le f hf
    x u t₀ 0 q₀.2 htime0 hfixedu
  have hrescale0 : rescaleLocalCurve ε hε η t₀ (u, 0) = v₀ := by
    ext τ <;>
      simp [rescaleLocalCurve, v₀, z₀, q₀,
        extendLocalCurve_apply_of_mem ε hε u q₀.2]
  rw [hrescale0] at hbase
  have hMv₀ : ∀ τ, ‖fderiv ℝ g (v₀ τ)‖ ≤ M := by
    intro τ
    simp [v₀, M]
  rcases exists_contDiffAt_picardFixedPoint_family_unique
      η hη.le g hg (z₀, 0) v₀ hbase hM0 hMv₀ hηsmall with
    ⟨χ, hχ0, hχsmooth, _hχsmoothNear, _hχfixed, hχunique⟩
  let init : E × ℝ → E × ℝ := fun p => (ψ p.1 q₀, p.2)
  let candidate : E × ℝ → LocalCurve (E × ℝ) η := fun p =>
    rescaleLocalCurve ε hε η t₀ (ψ p.1, p.2)
  have hinit0 : init (x, 0) = (z₀, 0) := by
    simp [init, z₀, hψx]
  have hcand0 : candidate (x, 0) = v₀ := by
    simp only [candidate, hψx]
    exact hrescale0
  have hevalψ : ContDiffAt ℝ ∞ (fun y : E => ψ y q₀) x := by
    simpa [Function.comp_def] using
      (ContinuousMap.evalCLM ℝ q₀).contDiff.contDiffAt.comp x hψ
  have hinitsmooth : ContDiffAt ℝ ∞ init (x, 0) := by
    simpa [init] using
      (hevalψ.comp (x, 0) contDiffAt_fst).prodMk contDiffAt_snd
  have hcandcontinuous : ContinuousAt candidate (x, 0) := by
    apply (rescaleLocalCurve_continuous ε hε η t₀).continuousAt.comp
    exact (hψ.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  have hpairtendsto : Tendsto (fun p => (init p, candidate p))
      (𝓝 (x, 0)) (𝓝 ((z₀, 0), v₀)) := by
    have hinitcont : ContinuousAt init (x, 0) := hinitsmooth.continuousAt
    rw [← hinit0, ← hcand0]
    exact hinitcont.prodMk hcandcontinuous
  have huniquepull : ∀ᶠ p in 𝓝 (x, 0),
      picardResidual η hη.le g hg (init p, candidate p) = 0 ↔
        χ (init p) = candidate p :=
    hpairtendsto.eventually hχunique
  have hfixedpull : ∀ᶠ p : E × ℝ in 𝓝 (x, 0),
      ψ p.1 = ContinuousMap.const (Icc (-ε) ε) p.1 +
        localCurveIntegral ε hε (superposition f hf.continuous (ψ p.1)) :=
    (show Tendsto (fun p : E × ℝ => p.1) (𝓝 (x, 0)) (𝓝 x) from
      continuousAt_fst).eventually hfixedψ
  have htimepull : ∀ᶠ p : E × ℝ in 𝓝 (x, 0),
      ∀ τ : Icc (-η) η,
        t₀ + p.2 * (τ : ℝ) ∈ Icc (-ε) ε :=
    (show Tendsto (fun p : E × ℝ => p.2) (𝓝 (x, 0)) (𝓝 (0 : ℝ)) from
      continuousAt_snd).eventually (eventually_forall_affine_mem_Icc ε η t₀ ht₀)
  let ηPoint : Icc (-η) η := ⟨η, ⟨by linarith [hη], le_rfl⟩⟩
  have hendpointEq : ∀ᶠ p in 𝓝 (x, 0),
      (χ (init p) ηPoint).1 =
        extendLocalCurve ε hε (ψ p.1) (t₀ + p.2 * η) := by
    filter_upwards [huniquepull, hfixedpull, htimepull] with p hpuniq hpfixed hptime
    have hcandfixed := rescaleLocalCurve_fixedPoint ε η hε hη.le f hf
      p.1 (ψ p.1) t₀ p.2 q₀.2 hptime hpfixed
    have hresidual : picardResidual η hη.le g hg (init p, candidate p) = 0 := by
      change candidate p - ContinuousMap.const (Icc (-η) η) (init p) -
        localCurveIntegral η hη.le
          (superposition g hg.continuous (candidate p)) = 0
      have hcandfixed' : candidate p =
          ContinuousMap.const (Icc (-η) η) (init p) +
            localCurveIntegral η hη.le
              (superposition g hg.continuous (candidate p)) := by
        simpa only [candidate, init, g, q₀] using hcandfixed
      rw [sub_sub, sub_eq_zero]
      exact hcandfixed'
    have hχcand : χ (init p) = candidate p := hpuniq.mp hresidual
    have heval := congrArg
      (fun w : LocalCurve (E × ℝ) η => (w ηPoint).1) hχcand
    simpa [candidate, ηPoint, rescaleLocalCurve] using heval
  have hχcomp : ContDiffAt ℝ ∞ (fun p => χ (init p)) (x, 0) := by
    have hχinit : ContDiffAt ℝ ∞ χ (init (x, 0)) := by
      rw [hinit0]
      exact hχsmooth
    exact hχinit.comp (x, 0) hinitsmooth
  have hendpointSmooth : ContDiffAt ℝ ∞
      (fun p : E × ℝ => (χ (init p) ηPoint).1) (x, 0) := by
    have heval : ContDiffAt ℝ ∞
        (fun p : E × ℝ => χ (init p) ηPoint) (x, 0) := by
      simpa [Function.comp_def] using
        (ContinuousMap.evalCLM ℝ ηPoint).contDiff.contDiffAt.comp (x, 0) hχcomp
    exact contDiffAt_fst.comp (x, 0) heval
  have hscaledSmooth : ContDiffAt ℝ ∞
      (fun p : E × ℝ =>
        extendLocalCurve ε hε (ψ p.1) (t₀ + p.2 * η)) (x, 0) :=
    hendpointSmooth.congr_of_eventuallyEq
      (hendpointEq.mono fun _ hp => hp.symm)
  let r : E × ℝ → E × ℝ := fun p => (p.1, (p.2 - t₀) / η)
  have hr : ContDiffAt ℝ ∞ r (x, t₀) := by
    dsimp [r]
    fun_prop
  have hr0 : r (x, t₀) = (x, 0) := by simp [r]
  have hscaledAtR : ContDiffAt ℝ ∞
      (fun p : E × ℝ =>
        extendLocalCurve ε hε (ψ p.1) (t₀ + p.2 * η)) (r (x, t₀)) := by
    rw [hr0]
    exact hscaledSmooth
  have hcomp := hscaledAtR.comp (x, t₀) hr
  have hfun :
      (fun p : E × ℝ =>
        extendLocalCurve ε hε (ψ p.1) (t₀ + p.2 * η)) ∘ r =
      (fun p : E × ℝ => extendLocalCurve ε hε (ψ p.1) p.2) := by
    funext p
    simp only [Function.comp_apply, r]
    congr 1
    field_simp
    ring
  rw [hfun] at hcomp
  exact hcomp

/--
%%handwave
name:
  Joint smoothness of a family of Picard solutions
statement:
  Under the hypotheses \(\|Df(u(t))\|\leq M\), \(M\geq0\), and
  \(\varepsilon M<1\) for a Picard solution \(u\) through \(x\), there is a
  family \(\psi_y\) with \(\psi_x=u\) satisfying the Picard equation near
  \(x\), such that
  \[
    (y,t)\longmapsto\psi_y(t)
  \]
  is smooth near every \((y,t_0)\) with \(y\) sufficiently close to \(x\)
  and \(|t_0|<\varepsilon\).
proof:
  First obtain smooth dependence of the fixed curve on its initial value.
  For each nearby solution and each interior time, rescale time and apply the
  Picard implicit-function argument to the associated time-scaled vector
  field; this identifies the resulting smooth map with \((y,t)\mapsto
  \psi_y(t)\).
-/
theorem exists_jointlySmooth_picardFixedPoint_family
    (ε : ℝ) (hε : 0 ≤ ε) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (x : E) (u : LocalCurve E ε) {M : ℝ}
    (hfixed : u = ContinuousMap.const (Icc (-ε) ε) x +
      localCurveIntegral ε hε (superposition f hf.continuous u))
    (hM0 : 0 ≤ M) (hM : ∀ t, ‖fderiv ℝ f (u t)‖ ≤ M)
    (hsmall : ε * M < 1) :
    ∃ ψ : E → LocalCurve E ε,
      ψ x = u ∧
      (∀ᶠ y in 𝓝 x,
        ψ y = ContinuousMap.const (Icc (-ε) ε) y +
          localCurveIntegral ε hε (superposition f hf.continuous (ψ y))) ∧
      ∀ᶠ y in 𝓝 x, ∀ t₀ ∈ Ioo (-ε) ε,
          ContDiffAt ℝ ∞
            (fun p : E × ℝ => extendLocalCurve ε hε (ψ p.1) p.2)
            (y, t₀) := by
  rcases exists_contDiffAt_picardFixedPoint_family ε hε f hf x u hfixed
      hM0 hM hsmall with ⟨ψ, hψx, _hψ, hψNear, hfixedψ⟩
  refine ⟨ψ, hψx, hfixedψ, ?_⟩
  rcases mem_nhds_iff.mp hfixedψ with ⟨U, hUsub, hUopen, hxU⟩
  filter_upwards [hψNear, hUopen.mem_nhds hxU] with y hψy hyU
  intro t₀ ht₀
  have hfixedAtY : ∀ᶠ z in 𝓝 y,
      ψ z = ContinuousMap.const (Icc (-ε) ε) z +
        localCurveIntegral ε hε (superposition f hf.continuous (ψ z)) :=
    Filter.mem_of_superset (hUopen.mem_nhds hyU) hUsub
  exact contDiffAt_uncurry_extendLocalCurve_of_picardFixedPoint
    ε hε f hf y (ψ y) ψ rfl hψy hfixedAtY t₀ ht₀

end PicardResidual

end JJMath.Manifold
