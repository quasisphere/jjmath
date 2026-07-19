import JJMath.Hyperbolic.Converse.LocalInverseTransition

/-!
# The one-jet openness boundary

This file isolates the remaining analytic input behind the `oneJetOpen`
component of the componentwise continuation route.

The theorem needed by the existing route is an openness statement for the locus
where a fixed real Mobius transition matches a pair of hyperbolic local charts
to first order.  The basepointed transition hypothesis is only used to choose
the real Mobius map globally; the local openness argument itself is an
at-the-point rigidity statement for holomorphic hyperbolic local isometries.

The reductions below keep that distinction explicit: once the at-point local
rigidity theorem is supplied, the existing public `oneJetOpen` theorem follows.
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name: A real affine function is determined at a nonreal point
statement:
  Let \(a,b,c,d\in\mathbb R\) and \(p\in\mathbb H\). If
  \[
    ap+b=cp+d,
  \]
  then \(a=c\) and \(b=d\).
proof:
  Taking imaginary parts gives \((a-c)\operatorname{Im}p=0\). Since \(\operatorname{Im}p>0\), this yields \(a=c\), and the original equality then gives \(b=d\).
-/
theorem real_affine_eq_at_upperHalfPlane
    {a b c d : ℝ} (p : ℍ)
    (h : (a : ℂ) * (p : ℂ) + (b : ℂ) =
        (c : ℂ) * (p : ℂ) + (d : ℂ)) :
    a = c ∧ b = d := by
  have hdiff :
      (((a - c : ℝ) : ℂ) * (p : ℂ) + ((b - d : ℝ) : ℂ)) = 0 := by
    calc
      (((a - c : ℝ) : ℂ) * (p : ℂ) + ((b - d : ℝ) : ℂ))
          =
        ((a : ℂ) * (p : ℂ) + (b : ℂ)) -
          ((c : ℂ) * (p : ℂ) + (d : ℂ)) := by
          rw [Complex.ofReal_sub, Complex.ofReal_sub]
          ring
      _ = 0 := by rw [h, sub_self]
  have him := congrArg Complex.im hdiff
  simp [Complex.add_im, Complex.mul_im] at him
  have ha : a = c := by
    have hmul : (a - c) * (p : ℂ).im = 0 := by
      simpa [sub_eq_add_neg, mul_comm] using him
    have hp : (p : ℂ).im ≠ 0 := p.im_ne_zero
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hp)
  constructor
  · exact ha
  · subst c
    have hbd : ((b : ℂ) : ℂ) = (d : ℂ) := by
      simpa using h
    exact_mod_cast hbd

/--
%%handwave
name: A real Mobius transformation is determined by one complex one-jet
statement:
  Let \(A,B\) be real Mobius transformations and \(p\in\mathbb H\). If \(A(p)=B(p)\) and \(A'(p)=B'(p)\), then \(A(z)=B(z)\) for every \(z\in\mathbb H\).
proof:
  Equality of the derivatives makes the squares of the two denominators equal at \(p\), so the denominators differ by a sign. The value equality forces the numerators to carry the same sign. Since the coefficients are real and \(p\) is nonreal, the affine coefficient lemma identifies the corresponding matrix rows up to that common sign; the two fractional-linear actions are therefore identical.
-/
theorem realMobiusRepresentativeAction_eq_of_value_derivative_eq
    (A B : RealMobiusRepresentative) (p : ℍ)
    (hvalue :
      realMobiusRepresentativeAction A p =
        realMobiusRepresentativeAction B p)
    (hderiv :
      realMobiusRepresentativeDerivativeAt A p =
        realMobiusRepresentativeDerivativeAt B p) :
    ∀ z : ℍ,
      realMobiusRepresentativeAction A z =
        realMobiusRepresentativeAction B z := by
  let denA : ℂ := UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p
  let denB : ℂ := UpperHalfPlane.denom (B : GL (Fin 2) ℝ) p
  let numA : ℂ := UpperHalfPlane.num (A : GL (Fin 2) ℝ) p
  let numB : ℂ := UpperHalfPlane.num (B : GL (Fin 2) ℝ) p
  have hderiv_den : denA⁻¹ ^ 2 = denB⁻¹ ^ 2 := by
    have hderiv' := hderiv
    dsimp [realMobiusRepresentativeDerivativeAt] at hderiv'
    rw [realMobiusRepresentativeAction_deriv,
      realMobiusRepresentativeAction_deriv] at hderiv'
    dsimp [denA, denB] at hderiv' ⊢
    simpa [inv_pow] using hderiv'
  have hden_sq : denA ^ 2 = denB ^ 2 := by
    have hdenA_ne : denA ≠ 0 := by
      dsimp [denA]
      exact UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p
    have hdenB_ne : denB ≠ 0 := by
      dsimp [denB]
      exact UpperHalfPlane.denom_ne_zero (B : GL (Fin 2) ℝ) p
    apply inv_injective
    simpa [inv_pow, hdenA_ne, hdenB_ne] using hderiv_den
  have hden_or : denA = denB ∨ denA = -denB :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hden_sq
  have hvalue_complex : numA / denA = numB / denB := by
    have h := congrArg (fun q : ℍ => (q : ℂ)) hvalue
    dsimp [realMobiusRepresentativeAction] at h
    simpa [numA, denA, numB, denB,
      UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.num, UpperHalfPlane.denom] using h
  rcases hden_or with hden | hden
  · have hnum : numA = numB := by
      have hdenB_ne : denB ≠ 0 := by
        dsimp [denB]
        exact UpperHalfPlane.denom_ne_zero (B : GL (Fin 2) ℝ) p
      rw [hden] at hvalue_complex
      have hmul :
          numA * denB = numB * denB :=
        (div_eq_div_iff hdenB_ne hdenB_ne).mp hvalue_complex
      exact mul_right_cancel₀ hdenB_ne hmul
    have hden_rows :
        (A : GL (Fin 2) ℝ) 1 0 = (B : GL (Fin 2) ℝ) 1 0 ∧
          (A : GL (Fin 2) ℝ) 1 1 = (B : GL (Fin 2) ℝ) 1 1 := by
      exact real_affine_eq_at_upperHalfPlane p (by
        simpa [denA, denB, UpperHalfPlane.denom] using hden)
    have hnum_rows :
        (A : GL (Fin 2) ℝ) 0 0 = (B : GL (Fin 2) ℝ) 0 0 ∧
          (A : GL (Fin 2) ℝ) 0 1 = (B : GL (Fin 2) ℝ) 0 1 := by
      exact real_affine_eq_at_upperHalfPlane p (by
        simpa [numA, numB, UpperHalfPlane.num] using hnum)
    intro z
    apply UpperHalfPlane.ext
    have hnum_z :
        UpperHalfPlane.num (A : GL (Fin 2) ℝ) z =
          UpperHalfPlane.num (B : GL (Fin 2) ℝ) z := by
      simp [UpperHalfPlane.num, hnum_rows.1, hnum_rows.2]
    have hden_z :
        UpperHalfPlane.denom (A : GL (Fin 2) ℝ) z =
          UpperHalfPlane.denom (B : GL (Fin 2) ℝ) z := by
      simp [UpperHalfPlane.denom, hden_rows.1, hden_rows.2]
    simpa [realMobiusRepresentativeAction,
      UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.num, UpperHalfPlane.denom] using
      congrArg₂ (fun n d : ℂ ↦ n / d) hnum_z hden_z
  · have hnum : numA = -numB := by
      have hdenB_ne : denB ≠ 0 := by
        dsimp [denB]
        exact UpperHalfPlane.denom_ne_zero (B : GL (Fin 2) ℝ) p
      rw [hden] at hvalue_complex
      have hneg : -numA = numB := by
        field_simp [hdenB_ne] at hvalue_complex ⊢
        simpa [mul_comm, mul_left_comm, mul_assoc] using hvalue_complex
      simpa using congrArg Neg.neg hneg
    have hden_rows :
        (A : GL (Fin 2) ℝ) 1 0 = -((B : GL (Fin 2) ℝ) 1 0) ∧
          (A : GL (Fin 2) ℝ) 1 1 = -((B : GL (Fin 2) ℝ) 1 1) := by
      exact real_affine_eq_at_upperHalfPlane p (by
        simpa [denA, denB, UpperHalfPlane.denom, neg_add, add_comm,
          add_left_comm, add_assoc] using hden)
    have hnum_rows :
        (A : GL (Fin 2) ℝ) 0 0 = -((B : GL (Fin 2) ℝ) 0 0) ∧
          (A : GL (Fin 2) ℝ) 0 1 = -((B : GL (Fin 2) ℝ) 0 1) := by
      exact real_affine_eq_at_upperHalfPlane p (by
        simpa [numA, numB, UpperHalfPlane.num, neg_add, add_comm,
          add_left_comm, add_assoc] using hnum)
    intro z
    apply UpperHalfPlane.ext
    have hnum_z :
        UpperHalfPlane.num (A : GL (Fin 2) ℝ) z =
          -UpperHalfPlane.num (B : GL (Fin 2) ℝ) z := by
      simp [UpperHalfPlane.num, hnum_rows.1, hnum_rows.2]
      ring
    have hden_z :
        UpperHalfPlane.denom (A : GL (Fin 2) ℝ) z =
          -UpperHalfPlane.denom (B : GL (Fin 2) ℝ) z := by
      simp [UpperHalfPlane.denom, hden_rows.1, hden_rows.2]
      ring
    have hdenB_z_ne :
        UpperHalfPlane.denom (B : GL (Fin 2) ℝ) z ≠ 0 :=
      UpperHalfPlane.denom_ne_zero (B : GL (Fin 2) ℝ) z
    calc
      (realMobiusRepresentativeAction A z : ℂ) =
        UpperHalfPlane.num (A : GL (Fin 2) ℝ) z /
          UpperHalfPlane.denom (A : GL (Fin 2) ℝ) z := by
          simp [realMobiusRepresentativeAction,
            UpperHalfPlane.coe_specialLinearGroup_apply,
            UpperHalfPlane.num, UpperHalfPlane.denom]
      _ =
        (-UpperHalfPlane.num (B : GL (Fin 2) ℝ) z) /
          (-UpperHalfPlane.denom (B : GL (Fin 2) ℝ) z) := by
          simpa using
            congrArg₂ (fun n d : ℂ ↦ n / d) hnum_z hden_z
      _ =
          UpperHalfPlane.num (B : GL (Fin 2) ℝ) z /
            UpperHalfPlane.denom (B : GL (Fin 2) ℝ) z := by
          field_simp [hdenB_z_ne]
      _ = (realMobiusRepresentativeAction B z : ℂ) := by
          simp [realMobiusRepresentativeAction,
            UpperHalfPlane.coe_specialLinearGroup_apply,
            UpperHalfPlane.num, UpperHalfPlane.denom]

/-- Value-level local rigidity input for the one-jet openness step.

This is the geometric statement suggested by the induced-isometry argument:
if the fixed real Mobius comparison has the correct value and oriented
first-order data at a point, then the value equality already persists locally.
The derivative part of one-jet persistence is then formal, by differentiating
this local equality. -/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (y : X),
      U.holomorphic_on_domain →
      U.local_biholomorph_on_domain →
      U.pulls_back_metric_on_domain →
      V.holomorphic_on_domain →
      V.local_biholomorph_on_domain →
      V.pulls_back_metric_on_domain →
      y ∈ U.domain →
      y ∈ V.domain →
      V.toUpperHalfPlane y =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane y) →
      HyperbolicLocalChartPointedFirstOrderMatch U V A y →
        ∃ W : Set X,
          IsOpen W ∧ y ∈ W ∧
            ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
              V.toUpperHalfPlane z =
                realMobiusRepresentativeAction A (U.toUpperHalfPlane z)

/--
Local PSL classification input for the one-jet openness step.

This is the remaining geometric assertion before value local rigidity: near
each overlap point, the transition between the two hyperbolic local charts is
locally represented by some element of `PSL(2,R)`/`SL(2,R)`.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionLocalPSLClassificationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g) (y : X),
      U.holomorphic_on_domain →
      U.local_biholomorph_on_domain →
      U.pulls_back_metric_on_domain →
      V.holomorphic_on_domain →
      V.local_biholomorph_on_domain →
      V.pulls_back_metric_on_domain →
      y ∈ U.domain →
      y ∈ V.domain →
        ∃ (B : RealMobiusRepresentative) (W : Set X),
          IsOpen W ∧ y ∈ W ∧
            ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
              V.toUpperHalfPlane z =
                realMobiusRepresentativeAction B (U.toUpperHalfPlane z)

/--
%%handwave
name: Pointed real-Mobius matching of two hyperbolic charts
statement:
  Let \(U,V\) be hyperbolic local charts on a complex one-manifold and let \(x\in\operatorname{dom}(U)\cap\operatorname{dom}(V)\). There exists a real Mobius transformation whose value and oriented first-order data carry \(U\) to \(V\) at \(x\).
proof:
  The Poincare pullback formula provides nonzero coordinate derivatives with equal hyperbolic norm. Transitivity of oriented orthonormal frames in the upper half-plane then supplies the required real Mobius transformation.
-/
theorem hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_complexOneManifold
    [ComplexOneManifold X] :
    HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_coordinateDerivativeData_proved
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem)

/--
%%handwave
name: Local real-Mobius classification from pointed value stability
statement:
  Suppose that a real Mobius transformation matching two holomorphic hyperbolic local charts to first order at a point also matches their values on a neighborhood. Then any two such charts are related near each common point by some real Mobius transformation.
proof:
  At the chosen common point, select a real Mobius transformation matching the two chart values and oriented first-order data. Apply the assumed pointed value-stability result to extend that value equality to a neighborhood.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionLocalPSLClassificationTheorem_of_valueStabilityFromHolomorphicLocalIsometry
    [ComplexOneManifold X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPSLClassificationTheorem
      X := by
  intro g U V y hUhol hUbih hUpull hVhol hVbih hVpull hyU hyV
  rcases
      hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_complexOneManifold
        g U V y hyU hyV with
    ⟨A, hA⟩
  rcases
      hValue g U V A y hUhol hUbih hUpull hVhol hVbih hVpull hA
        y hyU hyV hA.value_match with
    ⟨W, hWopen, hyW, hW⟩
  exact ⟨A, W, hWopen, hyW, hW⟩

/--
%%handwave
name: Local real-Mobius classification from componentwise propagation
statement:
  On a locally path-connected complex one-manifold, suppose every pointed real-Mobius match of two hyperbolic charts extends over the connected component of their overlap. Then near every common point the charts differ by a real Mobius transformation.
proof:
  Choose a pointed real-Mobius match at the common point. Its connected component in the open chart overlap is itself an open neighborhood, and componentwise propagation gives the desired identity there.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionLocalPSLClassificationTheorem_of_overlapComponentExtension
    [ComplexOneManifold X] [LocPathConnectedSpace X]
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPSLClassificationTheorem
      X := by
  intro g U V y _hUhol _hUbih _hUpull _hVhol _hVbih _hVpull hyU hyV
  rcases
      hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_complexOneManifold
        g U V y hyU hyV with
    ⟨A, hA⟩
  let overlap : Set X := U.domain ∩ V.domain
  let component : Set X := connectedComponentIn overlap y
  refine ⟨A, component, ?_, ?_, ?_⟩
  · simpa [component, overlap] using
      (U.isOpen_domain.inter V.isOpen_domain).connectedComponentIn
  · exact mem_connectedComponentIn ⟨hyU, hyV⟩
  · intro z hzComponent hzU hzV
    exact hExtend g U V A y hA z hzU hzV
      (by simpa [component, overlap] using hzComponent)

/--
%%handwave
name: First-order matching obtained by differentiating a local Mobius identity
statement:
  Let \(x\in\operatorname{dom}(U)\cap\operatorname{dom}(V)\). If, in the ambient coordinate at \(x\), the germs of \(V\) and \(A\circ U\) agree for a real Mobius transformation \(A\), then
  \[
    V'(x)=A'(U(x))U'(x)
  \]
  in that coordinate.
proof:
  Equal germs have equal derivatives. Apply the complex chain rule to the derivative of \(A\circ U\).
-/
theorem hyperbolicLocalChartConcreteFirstOrderMatch_of_eventuallyEq_realMobius_atPoint
    [ComplexOneManifold X] {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {A : RealMobiusRepresentative} {x : X}
    (hxU : x ∈ U.domain) (_hxV : x ∈ V.domain)
    (hEq :
      (fun z : ℂ =>
          (V.toUpperHalfPlane ((chartAt ℂ x).symm z) : ℂ)) =ᶠ[
            nhds ((chartAt ℂ x) x)]
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane ((chartAt ℂ x).symm z)) : ℂ))) :
    HyperbolicLocalChartConcreteFirstOrderMatch U V A x := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z₀ : ℂ := e x
  let F : ℂ → ℂ := fun z => (U.toUpperHalfPlane (e.symm z) : ℂ)
  let M : ℂ → ℂ := fun w =>
    (realMobiusRepresentativeAction A
      ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  have hsymm_z₀ : e.symm z₀ = x := by
    dsimp [e, z₀]
    exact (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hF_point : F z₀ = (U.toUpperHalfPlane x : ℂ) := by
    dsimp [F, z₀]
    rw [hsymm_z₀]
  have hF_diff : DifferentiableAt ℂ F z₀ := by
    simpa [F, e, z₀] using
      U.coordinateExpressionAt_differentiableAt hxU
  have hM_diff : DifferentiableAt ℂ M (U.toUpperHalfPlane x : ℂ) := by
    simpa [M] using
      realMobiusRepresentativeAction_differentiableAt A
        (U.toUpperHalfPlane x)
  have hchain :
      deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane (e.symm z)) : ℂ))
          z₀ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x) *
          deriv F z₀ := by
    have hcomp := deriv_comp_of_eq z₀ hM_diff hF_diff hF_point
    calc
      deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane (e.symm z)) : ℂ))
          z₀ =
        deriv (fun z : ℂ => M (F z)) z₀ := by
          congr 1
          ext z
          simp [M, F]
      _ = deriv M (U.toUpperHalfPlane x : ℂ) * deriv F z₀ := by
          simpa [Function.comp_def, hF_point] using hcomp
      _ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x) *
          deriv F z₀ := by
          rfl
  have hderiv_eq :
      deriv
          (fun z : ℂ =>
            (V.toUpperHalfPlane ((chartAt ℂ x).symm z) : ℂ))
          ((chartAt ℂ x) x) =
        deriv
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              (U.toUpperHalfPlane ((chartAt ℂ x).symm z)) : ℂ))
          ((chartAt ℂ x) x) :=
    Filter.EventuallyEq.deriv_eq hEq
  dsimp [HyperbolicLocalChartConcreteFirstOrderMatch,
    hyperbolicLocalChartCoordinateDerivativeAt,
    hyperbolicLocalChartCoordinateExpressionAt]
  simpa [e, z₀, F] using hderiv_eq.trans hchain

/--
%%handwave
name: Pointed value rigidity from local real-Mobius classification
statement:
  Suppose any two hyperbolic local charts are locally related by some real Mobius transformation. If a fixed real Mobius transformation \(A\) matches the values and first-order data of charts \(U,V\) at a common point \(y\), then \(V=A\circ U\) on a neighborhood of \(y\) inside their common domain.
proof:
  Local classification gives \(V=B\circ U\) near \(y\) for some real Mobius transformation \(B\). Differentiating gives the first-order relation for \(B\); comparison with the one for \(A\), followed by cancellation of the nonzero derivative of \(U\), shows that \(A\) and \(B\) have the same value and derivative at \(U(y)\). A real Mobius transformation is determined by that one-jet, so \(A=B\).
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem_of_localPSLClassification
    [ComplexOneManifold X]
    (hClass :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPSLClassificationTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem
      X := by
  intro g U V A y hUhol hUbih hUpull hVhol hVbih hVpull hyU hyV hyValue hyFirst
  rcases hClass g U V y hUhol hUbih hUpull hVhol hVbih hVpull hyU hyV with
    ⟨B, W, hWOpen, hyW, hWValueB⟩
  have hEventB :
      (fun z : ℂ =>
          (V.toUpperHalfPlane ((chartAt ℂ y).symm z) : ℂ)) =ᶠ[
            nhds ((chartAt ℂ y) y)]
        (fun z : ℂ =>
          (realMobiusRepresentativeAction B
            (U.toUpperHalfPlane ((chartAt ℂ y).symm z)) : ℂ)) := by
    let e : OpenPartialHomeomorph X ℂ := chartAt ℂ y
    let z₀ : ℂ := e y
    have hsurface :
        (W ∩ U.domain) ∩ V.domain ∈ nhds y :=
      ((hWOpen.inter U.isOpen_domain).inter V.isOpen_domain).mem_nhds
        ⟨⟨hyW, hyU⟩, hyV⟩
    have hpre :
        ∀ᶠ z in nhds z₀, e.symm z ∈ (W ∩ U.domain) ∩ V.domain :=
      (e.tendsto_symm (mem_chart_source ℂ y)) hsurface
    filter_upwards [hpre] with z hz
    exact congrArg (fun p : ℍ => (p : ℂ))
      (hWValueB (e.symm z) hz.1.1 hz.1.2 hz.2)
  have hBConcrete :
      HyperbolicLocalChartConcreteFirstOrderMatch U V B y :=
    hyperbolicLocalChartConcreteFirstOrderMatch_of_eventuallyEq_realMobius_atPoint
      hyU hyV hEventB
  have hAConcrete :
      HyperbolicLocalChartConcreteFirstOrderMatch U V A y :=
    hyFirst.concreteFirstOrderMatch
  let hData :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X :=
    hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem
  rcases hData g U y hyU with ⟨DU⟩
  have hDerivAB :
      realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane y) =
        realMobiusRepresentativeDerivativeAt B (U.toUpperHalfPlane y) := by
    dsimp [HyperbolicLocalChartConcreteFirstOrderMatch] at hAConcrete hBConcrete
    have hmul :
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane y) *
            hyperbolicLocalChartCoordinateDerivativeAt U y =
          realMobiusRepresentativeDerivativeAt B (U.toUpperHalfPlane y) *
            hyperbolicLocalChartCoordinateDerivativeAt U y := by
      exact hAConcrete.symm.trans hBConcrete
    exact mul_right_cancel₀ DU.coordinate_derivative_ne_zero hmul
  have hValueAB :
      realMobiusRepresentativeAction A (U.toUpperHalfPlane y) =
        realMobiusRepresentativeAction B (U.toUpperHalfPlane y) := by
    exact hyValue.symm.trans (hWValueB y hyW hyU hyV)
  have hActions :
      ∀ z : ℍ,
        realMobiusRepresentativeAction A z =
          realMobiusRepresentativeAction B z :=
    realMobiusRepresentativeAction_eq_of_value_derivative_eq
      A B (U.toUpperHalfPlane y) hValueAB hDerivAB
  refine ⟨W, hWOpen, hyW, ?_⟩
  intro z hzW hzU hzV
  calc
    V.toUpperHalfPlane z =
        realMobiusRepresentativeAction B (U.toUpperHalfPlane z) :=
      hWValueB z hzW hzU hzV
    _ = realMobiusRepresentativeAction A (U.toUpperHalfPlane z) :=
      (hActions (U.toUpperHalfPlane z)).symm

/-- Pointwise local rigidity input for the one-jet openness step.

Mathematically, this says: if two holomorphic hyperbolic local isometries into
`ℍ`, after applying a fixed real Mobius transformation to one of them, have the
same value and first derivative at a point, then that equality persists on a
neighborhood of the point.  This is the actual analytic boundary; it is the
local uniqueness theorem for the hyperbolic local-isometry equation. -/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (y : X),
      U.holomorphic_on_domain →
      U.local_biholomorph_on_domain →
      U.pulls_back_metric_on_domain →
      V.holomorphic_on_domain →
      V.local_biholomorph_on_domain →
      V.pulls_back_metric_on_domain →
      y ∈ U.domain →
      y ∈ V.domain →
      V.toUpperHalfPlane y =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane y) →
      HyperbolicLocalChartPointedFirstOrderMatch U V A y →
        ∃ W : Set X,
          IsOpen W ∧ y ∈ W ∧
            ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
              V.toUpperHalfPlane z =
                  realMobiusRepresentativeAction A (U.toUpperHalfPlane z) ∧
                HyperbolicLocalChartPointedFirstOrderMatch U V A z

/--
%%handwave
name: Full one-jet rigidity from value rigidity
statement:
  On a complex one-manifold, suppose that value and first-order matching at a point imply the local value identity \(V=A\circ U\). Then, after shrinking to that neighborhood, both the value identity and the intrinsic first-order matching hold at every common point.
proof:
  Differentiate the persistent value identity at each point to obtain the concrete coordinate derivative relation. The Poincare pullback formula supplies the nonzero coordinate derivative data that convert this relation back into intrinsic oriented first-order matching.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem_of_valueAtPointLocalRigidity
    [ComplexOneManifold X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem X := by
  intro g U V A y hUhol hUbih hUpull hVhol hVbih hVpull hyU hyV hyValue hyFirst
  rcases hValue g U V A y hUhol hUbih hUpull hVhol hVbih hVpull
      hyU hyV hyValue hyFirst with
    ⟨W, hWOpen, hyW, hWValue⟩
  refine ⟨W, hWOpen, hyW, ?_⟩
  intro z hzW hzU hzV
  have hzValue :
      V.toUpperHalfPlane z =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane z) :=
    hWValue z hzW hzU hzV
  have hEvent :
      (fun w : ℂ =>
          (V.toUpperHalfPlane ((chartAt ℂ z).symm w) : ℂ)) =ᶠ[
            nhds ((chartAt ℂ z) z)]
        (fun w : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane ((chartAt ℂ z).symm w)) : ℂ)) := by
    let e : OpenPartialHomeomorph X ℂ := chartAt ℂ z
    let z₀ : ℂ := e z
    have hsurface :
        (W ∩ U.domain) ∩ V.domain ∈ nhds z := by
      exact ((hWOpen.inter U.isOpen_domain).inter V.isOpen_domain).mem_nhds
        ⟨⟨hzW, hzU⟩, hzV⟩
    have hpre :
        ∀ᶠ w in nhds z₀, e.symm w ∈ (W ∩ U.domain) ∩ V.domain :=
      (e.tendsto_symm (mem_chart_source ℂ z)) hsurface
    filter_upwards [hpre] with w hw
    have hval := hWValue (e.symm w) hw.1.1 hw.1.2 hw.2
    exact congrArg (fun p : ℍ => (p : ℂ)) hval
  have hConcrete :
      HyperbolicLocalChartConcreteFirstOrderMatch U V A z :=
    hyperbolicLocalChartConcreteFirstOrderMatch_of_eventuallyEq_realMobius_atPoint
      hzU hzV hEvent
  let hData :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X :=
    hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem
  rcases hData g U z hzU with ⟨DU⟩
  rcases hData g V z hzV with ⟨DV⟩
  exact ⟨hzValue,
    HyperbolicLocalChartPointedFirstOrderMatch_of_concreteFirstOrderMatch
      DU DV hzValue hConcrete⟩

/--
%%handwave
name: Basepointed one-jet stability from pointwise rigidity
statement:
  If a pointed real-Mobius one-jet match of two hyperbolic charts persists locally at every overlap point, then it satisfies the corresponding basepointed local-stability property.
proof:
  Apply pointwise rigidity at the point under consideration. The additional distinguished base point used to select the transformation is irrelevant to this local conclusion.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_atPointLocalRigidity
    (hRigidity :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem X := by
  intro g U V A x₀ hUhol hUbih hUpull hVhol hVbih hVpull hpoint y hyU hyV hval hfirst
  exact
    hRigidity g U V A y hUhol hUbih hUpull hVhol hVbih hVpull hyU hyV hval hfirst

/--
%%handwave
name: Openness of the one-jet equality locus from pointwise rigidity
statement:
  If value and first-order matching with a fixed real Mobius transformation persist locally at each matching point, then the joint one-jet equality locus in the overlap of two hyperbolic charts is open.
proof:
  Pointwise rigidity gives the required local stability for holomorphic local isometries. The general stability-to-openness argument then supplies an open neighborhood of every point in the equality locus.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_atPointLocalRigidity
    (hRigidity :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_holomorphicLocalIsometryOneJetStability
    (hyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems_of_stability
      (pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_atPointLocalRigidity
        hRigidity))

/--
%%handwave
name: Openness of the one-jet equality locus from value rigidity
statement:
  On a complex one-manifold, if a pointed one-jet match implies local equality of chart values up to the fixed real Mobius transformation, then the locus of value and first-order matching is open.
proof:
  Persistent value equality differentiates to persistent first-order equality, giving pointwise one-jet rigidity. Apply openness of the equality locus from that pointwise rigidity.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueAtPointLocalRigidity
    [ComplexOneManifold X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_atPointLocalRigidity
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem_of_valueAtPointLocalRigidity
      hValue)

/--
%%handwave
name: Openness of one-jet matching from local real-Mobius classification
statement:
  On a complex one-manifold, if the transition between any two hyperbolic local charts is locally a real Mobius transformation, then the locus where a fixed real Mobius transformation matches their values and first-order data is open.
proof:
  Local classification and determination of a real Mobius transformation by one complex one-jet give value-level rigidity for the fixed transformation. Apply the resulting openness theorem.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_localPSLClassification
    [ComplexOneManifold X]
    (hClass :
      PointedHyperbolicLocalChartRealMobiusTransitionLocalPSLClassificationTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueAtPointLocalRigidity
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem_of_localPSLClassification
      hClass)

/--
%%handwave
name: Local value rigidity for hyperbolic chart one-jets
statement:
  Let \(U,V\) be hyperbolic local charts on a complex one-manifold, containing \(y\). If a real Mobius transformation \(A\) satisfies \(V(y)=A(U(y))\) and matches the oriented first-order data at \(y\), then \(V=A\circ U\) on a neighborhood of \(y\) inside the common chart domain.
proof:
  Pass to a fixed surface coordinate and invert the \(U\)-coordinate locally. The transition to \(V\) preserves the Poincare metric and has the same one-jet as \(A\), so local Schwarzian rigidity identifies the transition with \(A\). Pull the identity back to the surface.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem
    [ComplexOneManifold X] :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem
      X := by
  intro g U V A y _hUhol _hUbih _hUpull _hVhol _hVbih _hVpull
    hyU hyV hyValue hyFirst
  exact
    hyperbolicLocalChart_realMobiusTransition_value_eq_near_of_oneJet
      U V A hyU hyV hyValue hyFirst

/--
%%handwave
name: Openness of real-Mobius one-jet matching for hyperbolic charts
statement:
  For two hyperbolic local charts on a complex one-manifold and a fixed real Mobius transformation, the subset of their overlap where their values and oriented first-order data match is open.
proof:
  Local value rigidity holds for every matching point. The value identity can be differentiated to recover local first-order matching, so the one-jet equality locus is open.
-/
theorem
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
    [ComplexOneManifold X] :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueAtPointLocalRigidity
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem

/-- A tiny package for downstream files that want to name exactly the remaining
mathematical input, while receiving the already-compatible `oneJetOpen` theorem. -/
structure HyperbolicLocalChartOneJetOpenBoundaryTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  valueAtPointLocalRigidity :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem X

namespace HyperbolicLocalChartOneJetOpenBoundaryTheorems

/--
%%handwave
name: One-jet stability supplied by a value-rigidity package
statement:
  A package asserting local value rigidity for pointed real-Mobius one-jets on a complex one-manifold also yields local persistence of both values and first-order data.
proof:
  Convert value rigidity into pointwise one-jet rigidity by differentiating the local value identity, then forget the irrelevant distinguished base point.
-/
theorem oneJetLocalStability
    [ComplexOneManifold X]
    (B : HyperbolicLocalChartOneJetOpenBoundaryTheorems X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetLocalStabilityFromHolomorphicLocalIsometryTheorem_of_atPointLocalRigidity
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetAtPointLocalRigidityTheorem_of_valueAtPointLocalRigidity
      B.valueAtPointLocalRigidity)

/--
%%handwave
name: One-jet openness supplied by a value-rigidity package
statement:
  A package asserting local value rigidity for pointed real-Mobius one-jets on a complex one-manifold implies that the corresponding one-jet equality locus is open.
proof:
  Apply the general passage from value-level local rigidity to openness of joint value-and-first-order matching.
-/
theorem oneJetOpen
    [ComplexOneManifold X]
    (B : HyperbolicLocalChartOneJetOpenBoundaryTheorems X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_valueAtPointLocalRigidity
    B.valueAtPointLocalRigidity

end HyperbolicLocalChartOneJetOpenBoundaryTheorems

/-- Boundary package phrased directly as local PSL classification. -/
structure HyperbolicLocalChartOneJetOpenClassificationBoundaryTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  localPSLClassification :
    PointedHyperbolicLocalChartRealMobiusTransitionLocalPSLClassificationTheorem X

namespace HyperbolicLocalChartOneJetOpenClassificationBoundaryTheorems

/--
%%handwave
name: Value rigidity supplied by local real-Mobius classification
statement:
  A package asserting that every transition of hyperbolic local charts is locally real Mobius implies rigidity for any fixed real Mobius transformation having the prescribed one-jet.
proof:
  Local classification produces a possibly different real Mobius transformation; equality of its one-jet with the prescribed transformation identifies their actions.
-/
theorem valueAtPointLocalRigidity
    [ComplexOneManifold X]
    (B : HyperbolicLocalChartOneJetOpenClassificationBoundaryTheorems X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetValueAtPointLocalRigidityTheorem_of_localPSLClassification
    B.localPSLClassification

/--
%%handwave
name: One-jet openness supplied by local real-Mobius classification
statement:
  A package of local real-Mobius classification for hyperbolic chart transitions implies openness of the locus where a fixed real Mobius transformation matches the chart one-jets.
proof:
  Apply the classification-to-openness theorem to the packaged local classification hypothesis.
-/
theorem oneJetOpen
    [ComplexOneManifold X]
    (B : HyperbolicLocalChartOneJetOpenClassificationBoundaryTheorems X) :
    PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_localPSLClassification
    B.localPSLClassification

end HyperbolicLocalChartOneJetOpenClassificationBoundaryTheorems

end HyperbolicMetric

end

end JJMath
