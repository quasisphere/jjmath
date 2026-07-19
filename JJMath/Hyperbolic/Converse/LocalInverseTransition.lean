import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import JJMath.Hyperbolic.Converse.LocalIsometrySchwarzian

/-!
# Local inverse bridge for upper-half-plane coordinates

This file isolates the inverse-function-theorem step needed to convert a
surface hyperbolic local chart into a genuine transition map in the
upper-half-plane source coordinate.
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name: Poincare pullback formula in an arbitrary surface coordinate
statement:
  Let \(U\) be a hyperbolic local chart for a metric \(g\), let \(e\) be a complex surface chart, and suppose \(z\) lies in the target of \(e\) with \(e^{-1}(z)\in\operatorname{dom}(U)\). Then
  \[
    \frac{|(U\circ e^{-1})'(z)|^2}{\operatorname{Im}(U(e^{-1}(z)))^2}=\rho_{g,e}(z),
  \]
  where \(\rho_{g,e}\) is the squared conformal density of \(g\) in the \(e\)-coordinate.
proof:
  Factor \(U\circ e^{-1}\) through the coordinate stored by \(U\). The chain rule and multiplicativity of the squared complex norm split the numerator into the stored-map derivative and the chart-transition derivative. Combine the stored Poincare pullback formula with the conformal-density transition law.
-/
theorem hyperbolicLocalChart_pullbackSquaredDensityFormulaInChart
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X)
    {z : ℂ} (hzTarget : z ∈ e.target)
    (hzU : e.symm z ∈ U.domain) :
    Complex.normSq
        (deriv
          (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ))
          z) /
        ((U.toUpperHalfPlane (e.symm z) : ℂ).im ^ 2) =
      g.toConformalMetric.densitySqInChart e he z := by
  let L := U.local_isometry
  let x : X := e.symm z
  let τ : ℂ → ℂ := fun w ↦ L.chart (e.symm w)
  have hsymm_tendsto :
      Filter.Tendsto e.symm (nhds z) (nhds x) := by
    simpa [x, e.right_inv hzTarget] using
      e.tendsto_symm (e.map_target hzTarget)
  have hx_Lsource : x ∈ L.chart.source :=
    L.domain_subset_chart_source hzU
  have hτ_point : τ z = L.coordinate x := by
    dsimp [τ, x]
    exact (L.coordinate_eq_chart hzU).symm
  have hdomain :
      ∀ᶠ w in nhds z, e.symm w ∈ U.domain :=
    hsymm_tendsto (U.isOpen_domain.mem_nhds hzU)
  have hExpr :
      (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ)) =ᶠ[nhds z]
        (fun w : ℂ ↦ (L.localMap (τ w) : ℂ)) := by
    filter_upwards [hdomain] with w hw
    dsimp [τ]
    rw [L.toUpperHalfPlane_eq (e.symm w) hw]
    rw [L.coordinate_eq_chart hw]
  have hτ_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) τ z := by
    have hchart_mdiff :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) L.chart (e.symm z) :=
      mdifferentiableAt_atlas L.chart_mem_atlas (by
        simpa [x] using hx_Lsource)
    dsimp [τ]
    exact hchart_mdiff.comp z (mdifferentiableAt_atlas_symm he hzTarget)
  have hτ_diff : DifferentiableAt ℂ τ z := hτ_mdiff.differentiableAt
  have hlocal_diff :
      DifferentiableAt ℂ (fun w : ℂ ↦ (L.localMap w : ℂ))
        (L.coordinate x) :=
    L.holomorphic_on_domain (L.coordinate x)
      (L.coordinate_mem_domain x hzU)
  have hlocal_diff_at_τ :
      DifferentiableAt ℂ (fun w : ℂ ↦ (L.localMap w : ℂ)) (τ z) := by
    simpa [hτ_point] using hlocal_diff
  have hchain :
      deriv
          (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ))
          z =
        deriv (fun w : ℂ ↦ (L.localMap w : ℂ)) (L.coordinate x) *
          deriv τ z := by
    calc
      deriv
          (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ))
          z =
        deriv (fun w : ℂ ↦ (L.localMap (τ w) : ℂ)) z :=
          Filter.EventuallyEq.deriv_eq hExpr
      _ =
        deriv (fun w : ℂ ↦ (L.localMap w : ℂ)) (L.coordinate x) *
          deriv τ z := by
          simpa [Function.comp_def, hτ_point] using
            (deriv_comp_of_eq z hlocal_diff hτ_diff hτ_point)
  have hnorm :
      Complex.normSq
          (deriv
            (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ))
            z) =
        Complex.normSq
            (deriv (fun w : ℂ ↦ (L.localMap w : ℂ)) (L.coordinate x)) *
          Complex.normSq (deriv τ z) := by
    rw [hchain]
    exact Complex.normSq_mul _ _
  have hstored :
      g.toConformalMetric.densitySqInChart L.chart L.chart_mem_atlas
          (L.coordinate x) =
        Complex.normSq
            (deriv (fun w : ℂ ↦ (L.localMap w : ℂ)) (L.coordinate x)) /
          ((U.toUpperHalfPlane x : ℂ).im ^ 2) :=
    L.pulls_back_metric_on_domain x hzU
  have hchart_point : L.chart x = L.coordinate x :=
    (L.coordinate_eq_chart hzU).symm
  have hdensity_transition :
      g.toConformalMetric.densitySqInChart e he z =
        g.toConformalMetric.densitySqInChart L.chart L.chart_mem_atlas
            (L.coordinate x) *
          Complex.normSq (deriv τ z) := by
    have htransition :=
      g.toConformalMetric.densitySq_transition e he
        L.chart L.chart_mem_atlas hzTarget (by
          simpa [x] using hx_Lsource)
    dsimp [τ, x] at htransition ⊢
    simpa [τ, x, hchart_point] using htransition
  change
    Complex.normSq
        (deriv
          (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ))
          z) /
        ((U.toUpperHalfPlane (e.symm z) : ℂ).im ^ 2) =
      g.toConformalMetric.densitySqInChart e he z
  rw [hnorm, hdensity_transition, hstored]
  simp [x]
  ring

/--
%%handwave
name: Holomorphicity of a hyperbolic local chart in any surface coordinate
statement:
  Let \(U\) be a hyperbolic local chart and \(e\) a complex surface chart. If \(z\) lies in the target of \(e\) and \(e^{-1}(z)\in\operatorname{dom}(U)\), then \(U\circ e^{-1}\) is complex differentiable at \(z\).
proof:
  The coordinate expression remains differentiable after postcomposition with any real Mobius transformation. Specialize this fact to the identity transformation.
-/
theorem hyperbolicLocalChart_coordinateExpressionInChart_differentiableAt
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {z : ℂ} (hzTarget : z ∈ e.target)
    (hzU : e.symm z ∈ U.domain) :
    DifferentiableAt ℂ
      (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ))
      z := by
  have hId :
      DifferentiableAt ℂ
        (fun w : ℂ =>
          (realMobiusRepresentativeAction (1 : RealMobiusRepresentative)
            (U.toUpperHalfPlane (e.symm w)) : ℂ))
        z :=
    U.realMobius_postcomp_coordinateExpression_differentiableAt
      (1 : RealMobiusRepresentative) e he hzTarget hzU
  simpa [realMobiusRepresentativeAction_one] using hId

/--
%%handwave
name: Nonvanishing derivative of a hyperbolic coordinate
statement:
  Under the same hypotheses, the complex derivative \((U\circ e^{-1})'(z)\) is nonzero.
proof:
  The Poincare pullback formula identifies the squared norm of this derivative, divided by a positive imaginary-part square, with the strictly positive conformal density of the metric. If the derivative vanished, that density would be zero.
-/
theorem hyperbolicLocalChart_coordinateDerivativeInChart_ne
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X)
    {z : ℂ} (hzTarget : z ∈ e.target)
    (hzU : e.symm z ∈ U.domain) :
    deriv
        (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ))
        z ≠ 0 := by
  let d : ℂ :=
    deriv
      (fun w : ℂ ↦ (U.toUpperHalfPlane (e.symm w) : ℂ))
      z
  have hformula :=
    hyperbolicLocalChart_pullbackSquaredDensityFormulaInChart
      U he hzTarget hzU
  have hdensity_pos :
      0 <
    g.toConformalMetric.densitySqInChart e he z :=
    g.toConformalMetric.positive_densitySqInChart e he hzTarget
  intro hd
  have hzero :
      Complex.normSq d / ((U.toUpperHalfPlane (e.symm z) : ℂ).im ^ 2) = 0 := by
    simp [d, hd]
  rw [← hformula] at hdensity_pos
  rw [hzero] at hdensity_pos
  exact (lt_irrefl (0 : ℝ)) hdensity_pos

/--
%%handwave
name: Holomorphic inverse germ at a regular point
statement:
  Let \(D\subseteq\mathbb C\) be open, let \(a\in D\), and let \(F\) be holomorphic on \(D\) with \(F'(a)\ne0\). There is a map \(G:\mathbb C\to\mathbb C\) such that \(G(F(x))=x\) near \(a\), \(F(G(y))=y\) near \(F(a)\), and \(G\) has strict derivative \(F'(a)^{-1}\) at \(F(a)\).
proof:
  Holomorphicity on the open set makes \(F\) continuously differentiable near \(a\), hence strictly differentiable there. Apply the one-dimensional inverse function theorem at the nonzero derivative \(F'(a)\).
-/
theorem exists_eventually_inverse_of_holomorphicOn_deriv_ne
    {F : ℂ → ℂ} {D : Set ℂ} {a : ℂ}
    (hDopen : IsOpen D) (haD : a ∈ D)
    (hF : ∀ z, z ∈ D → DifferentiableAt ℂ F z)
    (hF_ne : deriv F a ≠ 0) :
    ∃ G : ℂ → ℂ,
      (∀ᶠ x in nhds a, G (F x) = x) ∧
        (∀ᶠ y in nhds (F a), F (G y) = y) ∧
          HasStrictDerivAt G (deriv F a)⁻¹ (F a) := by
  have hFOn : DifferentiableOn ℂ F D := by
    intro z hz
    exact (hF z hz).differentiableWithinAt
  have hFContDiffOn :
      ContDiffOn ℂ (1 : WithTop ℕ∞) F D :=
    hFOn.contDiffOn hDopen
  have hFContDiffAt :
      ContDiffAt ℂ (1 : WithTop ℕ∞) F a :=
    hFContDiffOn.contDiffAt (hDopen.mem_nhds haD)
  have hFAt : HasDerivAt F (deriv F a) a :=
    (hF a haD).hasDerivAt
  have hFStrict : HasStrictDerivAt F (deriv F a) a :=
    hFContDiffAt.hasStrictDerivAt' hFAt one_ne_zero
  let G : ℂ → ℂ :=
    hFStrict.localInverse F (deriv F a) a hF_ne
  refine ⟨G, ?_, ?_, ?_⟩
  · simpa [G] using
      hFStrict.eventually_left_inverse hF_ne
  · simpa [G] using
      hFStrict.eventually_right_inverse hF_ne
  · simpa [G] using
      hFStrict.to_localInverse hF_ne

/--
%%handwave
name: Local biholomorphism at a regular point
statement:
  Let \(D\subseteq\mathbb C\) be open, \(a\in D\), and let \(F\) be holomorphic on \(D\) with \(F'(a)\ne0\). Then \(F\) represents an open partial homeomorphism between neighborhoods containing \(a\) and \(F(a)\), and its inverse has strict derivative \(F'(a)^{-1}\) at \(F(a)\).
proof:
  Promote holomorphicity to continuous differentiability and strict differentiability at \(a\). The inverse function theorem packages the resulting inverse neighborhoods as an open partial homeomorphism with the stated inverse derivative.
-/
theorem exists_openPartialHomeomorph_of_holomorphicOn_deriv_ne
    {F : ℂ → ℂ} {D : Set ℂ} {a : ℂ}
    (hDopen : IsOpen D) (haD : a ∈ D)
    (hF : ∀ z, z ∈ D → DifferentiableAt ℂ F z)
    (hF_ne : deriv F a ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ F a ∈ e.target ∧
        (e : ℂ → ℂ) = F ∧
          HasStrictDerivAt e.symm (deriv F a)⁻¹ (F a) := by
  have hFOn : DifferentiableOn ℂ F D := by
    intro z hz
    exact (hF z hz).differentiableWithinAt
  have hFContDiffOn :
      ContDiffOn ℂ (1 : WithTop ℕ∞) F D :=
    hFOn.contDiffOn hDopen
  have hFContDiffAt :
      ContDiffAt ℂ (1 : WithTop ℕ∞) F a :=
    hFContDiffOn.contDiffAt (hDopen.mem_nhds haD)
  have hFAt : HasDerivAt F (deriv F a) a :=
    (hF a haD).hasDerivAt
  have hFStrict : HasStrictDerivAt F (deriv F a) a :=
    hFContDiffAt.hasStrictDerivAt' hFAt one_ne_zero
  let e : OpenPartialHomeomorph ℂ ℂ :=
    (hFStrict.hasStrictFDerivAt_equiv hF_ne).toOpenPartialHomeomorph F
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · exact HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
      (hFStrict.hasStrictFDerivAt_equiv hF_ne)
  · exact HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target
      (hFStrict.hasStrictFDerivAt_equiv hF_ne)
  · rfl
  · simpa [e] using
      hFStrict.to_localInverse hF_ne

/--
%%handwave
name: Local openness of a hyperbolic coordinate
statement:
  Let \(U\) be a hyperbolic local chart, let \(x\in\operatorname{dom}(U)\), and let \(W\) be a neighborhood of \(x\). There is an open set \(u\) in the upper half-plane such that
  \[
    U(x)\in u\subseteq U\bigl(W\cap\operatorname{dom}(U)\bigr).
  \]
proof:
  Write \(U\) in a surface coordinate at \(x\). Its derivative is nonzero, so the inverse function theorem supplies a local inverse around \(U(x)\). Shrink the inverse target so that it remains in the upper half-plane and its inverse lies in the chosen surface neighborhood and in the domain of \(U\).
-/
theorem HyperbolicLocalChart.exists_open_upperHalfPlane_subset_image_of_mem_nhds
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) {x : X} (hxU : x ∈ U.domain)
    {W : Set X} (hW : W ∈ nhds x) :
    ∃ u : Set ℍ,
      IsOpen u ∧ U.toUpperHalfPlane x ∈ u ∧
        u ⊆ U.toUpperHalfPlane '' (W ∩ U.domain) := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let a : ℂ := e x
  let F : ℂ → ℂ := fun z ↦ (U.toUpperHalfPlane (e.symm z) : ℂ)
  have haTarget : a ∈ e.target := by
    dsimp [a, e]
    exact mem_chart_target ℂ x
  have hsymm_a : e.symm a = x := by
    dsimp [a, e]
    exact (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  let D : Set ℂ := e.target ∩ e.symm ⁻¹' U.domain
  have hDopen : IsOpen D := by
    simpa [D] using e.isOpen_inter_preimage_symm U.isOpen_domain
  have haD : a ∈ D := by
    refine ⟨haTarget, ?_⟩
    simpa [hsymm_a] using hxU
  have hFdiff : ∀ z, z ∈ D → DifferentiableAt ℂ F z := by
    intro z hz
    exact
      hyperbolicLocalChart_coordinateExpressionInChart_differentiableAt
        U e (chart_mem_atlas ℂ x) hz.1 hz.2
  have hFne_a : deriv F a ≠ 0 := by
    simpa [F, a, e] using
      hyperbolicLocalChart_coordinateDerivativeInChart_ne
        U (e := e) (chart_mem_atlas ℂ x) (z := a) haTarget (by
          simpa [hsymm_a] using hxU)
  rcases
      exists_openPartialHomeomorph_of_holomorphicOn_deriv_ne
        hDopen haD hFdiff hFne_a with
    ⟨b, haSource, hpTargetRaw, hbcoe, _hbStrict⟩
  rcases mem_nhds_iff.mp hW with ⟨N, hNsub, hNopen, hxN⟩
  let p : ℂ := (U.toUpperHalfPlane x : ℂ)
  have hF_a : F a = p := by
    simp [F, p, hsymm_a]
  have hpTarget : p ∈ b.target := by
    simpa [hF_a] using hpTargetRaw
  have hLp : b.symm p = a := by
    have h := b.left_inv haSource
    simpa [hbcoe, hF_a] using h
  let D' : Set ℂ := e.target ∩ e.symm ⁻¹' (N ∩ U.domain)
  let H : Set ℂ := {w : ℂ | 0 < w.im}
  let Vc : Set ℂ := (b.target ∩ b.symm ⁻¹' D') ∩ H
  have hD'open : IsOpen D' := by
    simpa [D'] using e.isOpen_inter_preimage_symm (hNopen.inter U.isOpen_domain)
  have hHopen : IsOpen H :=
    isOpen_lt continuous_const Complex.continuous_im
  have hVcopen : IsOpen Vc := by
    have hbopen : IsOpen (b.target ∩ b.symm ⁻¹' D') := by
      simpa using b.isOpen_inter_preimage_symm hD'open
    simpa [Vc, H] using hbopen.inter hHopen
  have haD' : a ∈ D' := by
    refine ⟨haTarget, ?_⟩
    simpa [hsymm_a] using And.intro hxN hxU
  have hpVc : p ∈ Vc := by
    refine ⟨⟨hpTarget, ?_⟩, ?_⟩
    · simpa [hLp] using haD'
    · dsimp [H, p]
      exact (U.toUpperHalfPlane x).coe_im_pos
  let u : Set ℍ := (fun z : ℍ ↦ (z : ℂ)) ⁻¹' Vc
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa [u] using hVcopen.preimage UpperHalfPlane.continuous_coe
  · simpa [u, p] using hpVc
  · intro z hz
    let w : ℂ := (z : ℂ)
    have hwVc : w ∈ Vc := by
      simpa [u, w] using hz
    have hbtarget : w ∈ b.target := hwVc.1.1
    have hbD' : b.symm w ∈ D' := hwVc.1.2
    let x' : X := e.symm (b.symm w)
    have hx'N : x' ∈ N := by
      simpa [x', D'] using hbD'.2.1
    have hx'U : x' ∈ U.domain := by
      simpa [x', D'] using hbD'.2.2
    have hF_inv : F (b.symm w) = w := by
      have h := b.right_inv hbtarget
      simpa [hbcoe] using h
    have hcoord : U.toUpperHalfPlane x' = z := by
      apply UpperHalfPlane.ext
      simpa [x', F, w] using hF_inv
    exact ⟨x', ⟨hNsub hx'N, hx'U⟩, hcoord⟩

/--
%%handwave
name: Derivative of the inverse of a complex local homeomorphism
statement:
  Let \(e\) be an open partial homeomorphism of \(\mathbb C\) whose forward map is \(F\). If \(w\) lies in its target, \(F\) is differentiable at \(e^{-1}(w)\), and \(F'(e^{-1}(w))\ne0\), then
  \[
    (e^{-1})'(w)=F'(e^{-1}(w))^{-1}.
  \]
proof:
  Apply the inverse derivative theorem to the local homeomorphism, replacing its forward map by the everywhere equal function \(F\).
-/
theorem OpenPartialHomeomorph.hasDerivAt_symm_of_toFun_eq
    {F : ℂ → ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    (hcoe : (e : ℂ → ℂ) = F) {w : ℂ}
    (hw : w ∈ e.target)
    (hF : HasDerivAt F (deriv F (e.symm w)) (e.symm w))
    (hF_ne : deriv F (e.symm w) ≠ 0) :
    HasDerivAt e.symm (deriv F (e.symm w))⁻¹ w := by
  exact e.hasDerivAt_symm hw hF_ne (by
    simpa [hcoe] using hF)

/--
%%handwave
name: Formula for the derivative of an inverse branch
statement:
  Under the hypotheses above, the ordinary complex derivative of the inverse branch at \(w\) is \(F'(e^{-1}(w))^{-1}\).
proof:
  Take the derivative equality furnished by the inverse-derivative statement.
-/
theorem OpenPartialHomeomorph.deriv_symm_eq_inv_of_toFun_eq
    {F : ℂ → ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    (hcoe : (e : ℂ → ℂ) = F) {w : ℂ}
    (hw : w ∈ e.target)
    (hF : HasDerivAt F (deriv F (e.symm w)) (e.symm w))
    (hF_ne : deriv F (e.symm w) ≠ 0) :
    deriv (fun z : ℂ ↦ e.symm z) w =
      (deriv F (e.symm w))⁻¹ :=
  (OpenPartialHomeomorph.hasDerivAt_symm_of_toFun_eq e hcoe hw hF hF_ne).deriv

/--
%%handwave
name: Poincare metric identity for a coordinate transition
statement:
  Let \(F,G,L,\rho:\mathbb C\to\mathbb C\), and suppose on \(W\) that \(F\circ L\) is the identity, \(L'=1/(F'\circ L)\), the relevant derivatives and imaginary parts are nonzero, and
  \[
    \frac{|F'(L(w))|^2}{\operatorname{Im}(F(L(w)))^2}=\operatorname{Re}\rho(L(w))
    =\frac{|G'(L(w))|^2}{\operatorname{Im}(G(L(w)))^2}.
  \]
  Then
  \[
    \frac{|(G\circ L)'(w)|^2}{\operatorname{Im}(G(L(w)))^2}=\frac1{\operatorname{Im}(w)^2}
  \]
  for every \(w\in W\).
proof:
  The chain rule gives \((G\circ L)'=(G'\circ L)L'\). Substitute the inverse derivative and the two common-density identities, use \(F(L(w))=w\), and cancel the nonzero factor \(|F'(L(w))|^2\).
-/
theorem poincareTransition_metric_of_common_pullback_density
    {F G L rho : ℂ → ℂ} {W : Set ℂ}
    (hF_inv : ∀ w, w ∈ W → F (L w) = w)
    (hG_deriv :
      ∀ w, w ∈ W → HasDerivAt G (deriv G (L w)) (L w))
    (hL_deriv_at :
      ∀ w, w ∈ W → HasDerivAt L (deriv L w) w)
    (hL_deriv :
      ∀ w, w ∈ W → deriv L w = (deriv F (L w))⁻¹)
    (hF_ne : ∀ w, w ∈ W → deriv F (L w) ≠ 0)
    (hw_im_ne : ∀ w, w ∈ W → w.im ≠ 0)
    (hFMetric : ∀ w, w ∈ W →
      Complex.normSq (deriv F (L w)) / (F (L w)).im ^ 2 = (rho (L w)).re)
    (hGMetric : ∀ w, w ∈ W →
      Complex.normSq (deriv G (L w)) / (G (L w)).im ^ 2 = (rho (L w)).re) :
    ∀ w, w ∈ W →
      Complex.normSq (deriv (fun u : ℂ ↦ G (L u)) w) /
          (G (L w)).im ^ 2 =
        1 / (w.im ^ 2) := by
  intro w hw
  have hchain :
      deriv (fun u : ℂ ↦ G (L u)) w =
        deriv G (L w) * deriv L w := by
    simpa [Function.comp_def] using
      ((hG_deriv w hw).comp w (hL_deriv_at w hw)).deriv
  have hnormF_ne :
      Complex.normSq (deriv F (L w)) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp (hF_ne w hw)
  have hmetric_eq :
      Complex.normSq (deriv G (L w)) / (G (L w)).im ^ 2 =
        Complex.normSq (deriv F (L w)) / (w.im ^ 2) := by
    calc
      Complex.normSq (deriv G (L w)) / (G (L w)).im ^ 2 =
          (rho (L w)).re := hGMetric w hw
      _ =
          Complex.normSq (deriv F (L w)) / (F (L w)).im ^ 2 :=
            (hFMetric w hw).symm
      _ =
          Complex.normSq (deriv F (L w)) / (w.im ^ 2) := by
            rw [hF_inv w hw]
  calc
    Complex.normSq (deriv (fun u : ℂ ↦ G (L u)) w) /
        (G (L w)).im ^ 2 =
      (Complex.normSq (deriv G (L w)) *
          (Complex.normSq (deriv F (L w)))⁻¹) /
        (G (L w)).im ^ 2 := by
        rw [hchain, hL_deriv w hw, Complex.normSq_mul, Complex.normSq_inv]
    _ =
      (Complex.normSq (deriv G (L w)) / (G (L w)).im ^ 2) *
          (Complex.normSq (deriv F (L w)))⁻¹ := by
        ring
    _ =
      (Complex.normSq (deriv F (L w)) / (w.im ^ 2)) *
          (Complex.normSq (deriv F (L w)))⁻¹ := by
        rw [hmetric_eq]
    _ = 1 / (w.im ^ 2) := by
        field_simp [hnormF_ne, hw_im_ne w hw]

/--
%%handwave
name: Local rigidity of a Poincare coordinate transition
statement:
  Let \(W\subseteq\mathbb C\) be open and \(p\in W\). Suppose \(F\circ L\) is the identity on \(W\), \(F\) and \(G\) pull the same density back from the Poincare metric, all relevant derivatives are nonzero, and \(w\) and \(G(L(w))\) lie in the upper half-plane for \(w\in W\). If \(G\circ L\) has at \(p\) the same value and derivative as a real Mobius transformation \(A\), then there is an open neighborhood \(V\) of \(p\), contained in \(W\), on which \(G\circ L=A\).
proof:
  The inverse derivative and chain rules show that \(G\circ L\) is a holomorphic local diffeomorphism. The common-density calculation shows that it preserves the Poincare metric. Apply local rigidity of Poincare isometries with the prescribed one-jet at \(p\), and shrink to the resulting neighborhood.
-/
theorem poincareTransition_eq_realMobius_near_of_common_pullback_density
    {F G L rho : ℂ → ℂ} {W : Set ℂ} {p : ℂ}
    (A : RealMobiusRepresentative)
    (hWopen : IsOpen W) (hpW : p ∈ W)
    (hF_inv : ∀ w, w ∈ W → F (L w) = w)
    (hG_deriv :
      ∀ w, w ∈ W → HasDerivAt G (deriv G (L w)) (L w))
    (hL_deriv_at :
      ∀ w, w ∈ W → HasDerivAt L (deriv L w) w)
    (hL_deriv :
      ∀ w, w ∈ W → deriv L w = (deriv F (L w))⁻¹)
    (hF_ne : ∀ w, w ∈ W → deriv F (L w) ≠ 0)
    (hG_ne : ∀ w, w ∈ W → deriv G (L w) ≠ 0)
    (hw_im_pos : ∀ w, w ∈ W → 0 < w.im)
    (hG_im_pos : ∀ w, w ∈ W → 0 < (G (L w)).im)
    (hFMetric : ∀ w, w ∈ W →
      Complex.normSq (deriv F (L w)) / (F (L w)).im ^ 2 = (rho (L w)).re)
    (hGMetric : ∀ w, w ∈ W →
      Complex.normSq (deriv G (L w)) / (G (L w)).im ^ 2 = (rho (L w)).re)
    (hvalue : G (L p) =
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) p) : ℂ))
    (hderiv :
      deriv (fun u : ℂ ↦ G (L u)) p =
        deriv (fun w : ℂ =>
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)) p) :
    ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧
      ∀ w, w ∈ V →
        G (L w) =
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ) := by
  let T : ℂ → ℂ := fun u ↦ G (L u)
  have hTdiff : DifferentiableOn ℂ T W := by
    intro w hw
    exact (((hG_deriv w hw).comp w (hL_deriv_at w hw)).differentiableAt).differentiableWithinAt
  have hTderiv :
      ∀ w, w ∈ W →
        deriv T w = deriv G (L w) * deriv L w := by
    intro w hw
    simpa [T, Function.comp_def] using
      ((hG_deriv w hw).comp w (hL_deriv_at w hw)).deriv
  have hT_ne : ∀ w, w ∈ W → deriv T w ≠ 0 := by
    intro w hw
    rw [hTderiv w hw, hL_deriv w hw]
    exact mul_ne_zero (hG_ne w hw) (inv_ne_zero (hF_ne w hw))
  have hw_im_ne : ∀ w, w ∈ W → w.im ≠ 0 := by
    intro w hw
    exact ne_of_gt (hw_im_pos w hw)
  have hMetricReal :
      ∀ w, w ∈ W →
        Complex.normSq (deriv T w) / (T w).im ^ 2 =
          1 / (w.im ^ 2) := by
    intro w hw
    have hbase :=
      poincareTransition_metric_of_common_pullback_density
        hF_inv hG_deriv hL_deriv_at hL_deriv hF_ne hw_im_ne
        hFMetric hGMetric w hw
    simpa [T] using hbase
  have hMetric :
      ∀ w, w ∈ W →
        ((Complex.normSq (deriv T w) / (T w).im ^ 2 : ℝ) : ℂ) =
          ((((w.im ^ 2 : ℝ) : ℂ))⁻¹) := by
    intro w hw
    have hw_ne : w.im ≠ 0 := hw_im_ne w hw
    norm_num [hMetricReal w hw, Complex.ofReal_inv, Complex.ofReal_pow, hw_ne]
  rcases
    poincareLocalIsometry_eq_realMobius_near_of_oneJet_differentiableOn
      (f := T) (U := W) (z := p) A hWopen hpW hTdiff hT_ne
      (by simpa [T] using hG_im_pos) hw_im_pos hMetric
      (by simpa [T] using hvalue)
      (by simpa [T] using hderiv) with
    ⟨V, hVopen, hpV, hVW, hV⟩
  exact ⟨V, hVopen, hpV, hVW, by
    intro w hw
    simpa [T] using hV w hw⟩

/--
%%handwave
name: Local real-Mobius rigidity for hyperbolic charts
statement:
  Let \(U,V\) be hyperbolic local charts containing \(y\), and let \(A\) be a real Mobius transformation. If
  \[
    V(y)=A(U(y))
  \]
  and the first-order data of \(V\) and \(A\circ U\) agree at \(y\), then there is an open neighborhood \(W\) of \(y\) such that
  \[
    V(z)=A(U(z))
  \]
  whenever \(z\in W\cap\operatorname{dom}(U)\cap\operatorname{dom}(V)\).
proof:
  Express both charts in a common surface coordinate and construct a local inverse branch \(L\) for the \(U\)-coordinate. On a sufficiently small upper-half-plane neighborhood, both coordinate maps pull the same conformal density back from the Poincare metric. Their transition \(V\circ L\) therefore satisfies local Poincare rigidity, and the assumed value and first-order data identify it with \(A\). Pull this identity back to the surface.
-/
theorem hyperbolicLocalChart_realMobiusTransition_value_eq_near_of_oneJet
    [ComplexOneManifold X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative)
    {y : X}
    (hyU : y ∈ U.domain) (hyV : y ∈ V.domain)
    (hyValue :
      V.toUpperHalfPlane y =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane y))
    (hyFirst :
      HyperbolicLocalChartPointedFirstOrderMatch U V A y) :
    ∃ W : Set X,
      IsOpen W ∧ y ∈ W ∧
        ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
          V.toUpperHalfPlane z =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane z) := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ y
  let he : e ∈ atlas ℂ X := chart_mem_atlas ℂ y
  let a : ℂ := e y
  let F : ℂ → ℂ := fun z ↦ (U.toUpperHalfPlane (e.symm z) : ℂ)
  let G : ℂ → ℂ := fun z ↦ (V.toUpperHalfPlane (e.symm z) : ℂ)
  let rho : ℂ → ℂ :=
    fun z ↦ (g.toConformalMetric.densitySqInChart e he z : ℂ)
  let D : Set ℂ := e.target ∩ e.symm ⁻¹' U.domain
  have haTarget : a ∈ e.target := by
    dsimp [a, e]
    exact mem_chart_target ℂ y
  have hsymm_a : e.symm a = y := by
    dsimp [a, e]
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hDopen : IsOpen D := by
    simpa [D] using e.isOpen_inter_preimage_symm U.isOpen_domain
  have haD : a ∈ D := by
    refine ⟨haTarget, ?_⟩
    simpa [hsymm_a] using hyU
  have hFdiff : ∀ z, z ∈ D → DifferentiableAt ℂ F z := by
    intro z hz
    exact
      hyperbolicLocalChart_coordinateExpressionInChart_differentiableAt
        U e he hz.1 hz.2
  have hFne_a : deriv F a ≠ 0 := by
    simpa [F, a] using
      hyperbolicLocalChart_coordinateDerivativeInChart_ne
        U (e := e) he (z := a) haTarget (by
          simpa [hsymm_a] using hyU)
  rcases
      exists_openPartialHomeomorph_of_holomorphicOn_deriv_ne
        hDopen haD hFdiff hFne_a with
    ⟨b, haSource, hpTargetRaw, hbcoe, _hbStrict⟩
  let p : ℂ := (U.toUpperHalfPlane y : ℂ)
  have hF_a : F a = p := by
    simp [F, p, hsymm_a]
  have hpTarget : p ∈ b.target := by
    simpa [hF_a] using hpTargetRaw
  have hLp : b.symm p = a := by
    have h := b.left_inv haSource
    simpa [hbcoe, hF_a] using h
  let DUV : Set ℂ := e.target ∩ e.symm ⁻¹' (U.domain ∩ V.domain)
  let H : Set ℂ := {w : ℂ | 0 < w.im}
  let Wc : Set ℂ := (b.target ∩ b.symm ⁻¹' DUV) ∩ H
  have hDUVopen : IsOpen DUV := by
    simpa [DUV] using
      e.isOpen_inter_preimage_symm (U.isOpen_domain.inter V.isOpen_domain)
  have hHopen : IsOpen H :=
    isOpen_lt continuous_const Complex.continuous_im
  have hWcopen : IsOpen Wc := by
    have hbopen : IsOpen (b.target ∩ b.symm ⁻¹' DUV) := by
      simpa using b.isOpen_inter_preimage_symm hDUVopen
    simpa [Wc, H] using hbopen.inter hHopen
  have haDUV : a ∈ DUV := by
    refine ⟨haTarget, ?_⟩
    simpa [hsymm_a] using And.intro hyU hyV
  have hpWc : p ∈ Wc := by
    refine ⟨⟨hpTarget, ?_⟩, ?_⟩
    · simpa [hLp] using haDUV
    · dsimp [H, p]
      exact (U.toUpperHalfPlane y).coe_im_pos
  have hF_inv : ∀ w, w ∈ Wc → F (b.symm w) = w := by
    intro w hw
    have h := b.right_inv hw.1.1
    simpa [hbcoe] using h
  have hG_deriv :
      ∀ w, w ∈ Wc → HasDerivAt G (deriv G (b.symm w)) (b.symm w) := by
    intro w hw
    have hDuvw : b.symm w ∈ DUV := hw.1.2
    exact
      (hyperbolicLocalChart_coordinateExpressionInChart_differentiableAt
        V e he hDuvw.1 hDuvw.2.2).hasDerivAt
  have hL_deriv_at :
      ∀ w, w ∈ Wc →
        HasDerivAt (fun u : ℂ ↦ b.symm u)
          (deriv (fun u : ℂ ↦ b.symm u) w) w := by
    intro w hw
    have hDuvw : b.symm w ∈ DUV := hw.1.2
    have hFhas :
        HasDerivAt F (deriv F (b.symm w)) (b.symm w) :=
      (hyperbolicLocalChart_coordinateExpressionInChart_differentiableAt
        U e he hDuvw.1 hDuvw.2.1).hasDerivAt
    have hFne :
        deriv F (b.symm w) ≠ 0 :=
      hyperbolicLocalChart_coordinateDerivativeInChart_ne
        U (e := e) he (z := b.symm w) hDuvw.1 hDuvw.2.1
    exact
      (OpenPartialHomeomorph.hasDerivAt_symm_of_toFun_eq
        b hbcoe hw.1.1 hFhas hFne).differentiableAt.hasDerivAt
  have hL_deriv :
      ∀ w, w ∈ Wc →
        deriv (fun u : ℂ ↦ b.symm u) w = (deriv F (b.symm w))⁻¹ := by
    intro w hw
    have hDuvw : b.symm w ∈ DUV := hw.1.2
    have hFhas :
        HasDerivAt F (deriv F (b.symm w)) (b.symm w) :=
      (hyperbolicLocalChart_coordinateExpressionInChart_differentiableAt
        U e he hDuvw.1 hDuvw.2.1).hasDerivAt
    have hFne :
        deriv F (b.symm w) ≠ 0 :=
      hyperbolicLocalChart_coordinateDerivativeInChart_ne
        U (e := e) he (z := b.symm w) hDuvw.1 hDuvw.2.1
    simpa using
      OpenPartialHomeomorph.deriv_symm_eq_inv_of_toFun_eq
        b hbcoe hw.1.1 hFhas hFne
  have hF_ne : ∀ w, w ∈ Wc → deriv F (b.symm w) ≠ 0 := by
    intro w hw
    have hDuvw : b.symm w ∈ DUV := hw.1.2
    exact
      hyperbolicLocalChart_coordinateDerivativeInChart_ne
        U (e := e) he (z := b.symm w) hDuvw.1 hDuvw.2.1
  have hG_ne : ∀ w, w ∈ Wc → deriv G (b.symm w) ≠ 0 := by
    intro w hw
    have hDuvw : b.symm w ∈ DUV := hw.1.2
    exact
      hyperbolicLocalChart_coordinateDerivativeInChart_ne
        V (e := e) he (z := b.symm w) hDuvw.1 hDuvw.2.2
  have hw_im_pos : ∀ w, w ∈ Wc → 0 < w.im := by
    intro w hw
    exact hw.2
  have hG_im_pos : ∀ w, w ∈ Wc → 0 < (G (b.symm w)).im := by
    intro w hw
    exact (V.toUpperHalfPlane (e.symm (b.symm w))).coe_im_pos
  have hFMetric :
      ∀ w, w ∈ Wc →
        Complex.normSq (deriv F (b.symm w)) / (F (b.symm w)).im ^ 2 =
          (rho (b.symm w)).re := by
    intro w hw
    have hDuvw : b.symm w ∈ DUV := hw.1.2
    simpa [F, rho] using
      hyperbolicLocalChart_pullbackSquaredDensityFormulaInChart
        U he hDuvw.1 hDuvw.2.1
  have hGMetric :
      ∀ w, w ∈ Wc →
        Complex.normSq (deriv G (b.symm w)) / (G (b.symm w)).im ^ 2 =
          (rho (b.symm w)).re := by
    intro w hw
    have hDuvw : b.symm w ∈ DUV := hw.1.2
    simpa [G, rho] using
      hyperbolicLocalChart_pullbackSquaredDensityFormulaInChart
        V he hDuvw.1 hDuvw.2.2
  have hValueCoord :
      G (b.symm p) =
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) p) : ℂ) := by
    simpa [G, p, hLp, hsymm_a] using
      congrArg (fun q : ℍ ↦ (q : ℂ)) hyValue
  have hConcrete :
      deriv G a =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane y) *
          deriv F a := by
    simpa [G, F, a, e, hyperbolicLocalChartCoordinateDerivativeAt,
      hyperbolicLocalChartCoordinateExpressionAt] using
      hyFirst.concreteFirstOrderMatch
  have hL_deriv_p :
      deriv (fun u : ℂ ↦ b.symm u) p = (deriv F a)⁻¹ := by
    simpa [hLp] using hL_deriv p hpWc
  have hchain_p :
      deriv (fun u : ℂ ↦ G (b.symm u)) p =
        deriv G (b.symm p) * deriv (fun u : ℂ ↦ b.symm u) p := by
    simpa [Function.comp_def] using
      ((hG_deriv p hpWc).comp p (hL_deriv_at p hpWc)).deriv
  have hDerivCoord :
      deriv (fun u : ℂ ↦ G (b.symm u)) p =
        deriv (fun w : ℂ =>
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)) p := by
    calc
      deriv (fun u : ℂ ↦ G (b.symm u)) p =
          deriv G (b.symm p) * deriv (fun u : ℂ ↦ b.symm u) p :=
        hchain_p
      _ = deriv G a * (deriv F a)⁻¹ := by
        rw [hLp, hL_deriv_p]
      _ =
          (realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane y) *
              deriv F a) * (deriv F a)⁻¹ := by
        rw [hConcrete]
      _ = realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane y) := by
        field_simp [hFne_a]
      _ =
          deriv (fun w : ℂ =>
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)) p := by
        simp [realMobiusRepresentativeDerivativeAt, p]
  rcases
      poincareTransition_eq_realMobius_near_of_common_pullback_density
        (F := F) (G := G) (L := fun u : ℂ ↦ b.symm u) (rho := rho)
        (W := Wc) (p := p) A hWcopen hpWc
        hF_inv hG_deriv hL_deriv_at hL_deriv hF_ne hG_ne
        hw_im_pos hG_im_pos hFMetric hGMetric hValueCoord hDerivCoord with
    ⟨Vc, hVcopen, hpVc, _hVcWc, hVc⟩
  have hUcoeCont :
      ContinuousAt (fun x : X ↦ (U.toUpperHalfPlane x : ℂ)) y :=
    by
      simpa [Function.comp_def] using
        UpperHalfPlane.continuous_coe.continuousAt.comp
          (U.toUpperHalfPlane_continuousAt hyU)
  have hpre :
      (fun x : X ↦ (U.toUpperHalfPlane x : ℂ)) ⁻¹' Vc ∈ nhds y :=
    hUcoeCont (hVcopen.mem_nhds hpVc)
  rcases mem_nhds_iff.mp hpre with
    ⟨N, hNsub, hNopen, hyN⟩
  let Bsource : Set X := e.source ∩ e ⁻¹' b.source
  have hBsourceOpen : IsOpen Bsource := by
    simpa [Bsource] using e.isOpen_inter_preimage b.open_source
  have hyBsource : y ∈ Bsource := by
    refine ⟨mem_chart_source ℂ y, ?_⟩
    simpa [a, e] using haSource
  refine ⟨N ∩ Bsource, hNopen.inter hBsourceOpen, ⟨hyN, hyBsource⟩, ?_⟩
  intro z hzW hzU hzV
  have hzN : z ∈ N := hzW.1
  have hzEsource : z ∈ e.source := hzW.2.1
  have hzeBsource : e z ∈ b.source := hzW.2.2
  have hwVc : (U.toUpperHalfPlane z : ℂ) ∈ Vc :=
    hNsub hzN
  have hsymm_ez : e.symm (e z) = z :=
    e.left_inv hzEsource
  let w : ℂ := (U.toUpperHalfPlane z : ℂ)
  have hF_ez : F (e z) = w := by
    simp [F, w, hsymm_ez]
  have hL_w : b.symm w = e z := by
    have h := b.left_inv hzeBsource
    simpa [hbcoe, hF_ez] using h
  apply UpperHalfPlane.ext
  calc
    (V.toUpperHalfPlane z : ℂ) = G (e z) := by
      simp [G, hsymm_ez]
    _ = G (b.symm w) := by
      rw [hL_w]
    _ =
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ) :=
      hVc w hwVc
    _ =
        (realMobiusRepresentativeAction A (U.toUpperHalfPlane z) : ℂ) := by
      simp [w]

end HyperbolicMetric

end

end JJMath
