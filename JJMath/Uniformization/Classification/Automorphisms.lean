import JJMath.Uniformization.ComplexSurfaceMaps
import JJMath.ProjectiveGeometry.RiemannSphere
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Automorphisms of the simply connected uniformizing models

This file begins the analytic input for the deck-group classification.  The
main result identifies every biholomorphic automorphism of the complex plane
as an affine map.  The proof uses properness at infinity and Liouville's
theorem, rather than value-distribution theory.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

open Filter Set

noncomputable section

/--
%%handwave
name: Complex translation biholomorphism
statement:
  For $a\in\mathbb C$, define the biholomorphism
  $T_a:\mathbb C\to\mathbb C$ by $T_a(z)=z+a$, with inverse $T_{-a}$.
-/
def complexTranslationBiholomorphic (a : ℂ) : Biholomorphic ℂ ℂ where
  toHomeomorph :=
    { toFun := fun z ↦ z + a
      invFun := fun z ↦ z - a
      left_inv := by intro z; simp
      right_inv := by intro z; simp
      continuous_toFun := continuous_id.add continuous_const
      continuous_invFun := continuous_id.sub continuous_const }
  holomorphic_toFun :=
    mdifferentiable_iff_differentiable.mpr
      (show Differentiable ℂ (fun z : ℂ ↦ z + a) by fun_prop)
  holomorphic_invFun :=
    mdifferentiable_iff_differentiable.mpr
      (show Differentiable ℂ (fun z : ℂ ↦ z - a) by fun_prop)

/--
%%handwave
name: Inversion biholomorphism of the Riemann sphere
statement:
  Bundle the involution of $\widehat{\mathbb C}$ given by $z\mapsto z^{-1}$,
  with $0$ and $\infty$ interchanged, as a biholomorphism.
-/
def riemannSphereInvBiholomorphic :
    Biholomorphic RiemannSphere RiemannSphere where
  toHomeomorph := riemannSphereInvHomeomorph
  holomorphic_toFun := riemannSphereInv_mdifferentiable
  holomorphic_invFun := riemannSphereInv_mdifferentiable

/--
%%handwave
name: Translation biholomorphism of the Riemann sphere
statement:
  For $a\in\mathbb C$, extend $z\mapsto z+a$ by fixing $\infty$ and bundle
  the resulting automorphism of $\widehat{\mathbb C}$ as a biholomorphism.
-/
def riemannSphereTranslationBiholomorphic (a : ℂ) :
    Biholomorphic RiemannSphere RiemannSphere where
  toHomeomorph := Homeomorph.onePointCongr (complexTranslationHomeomorph a)
  holomorphic_toFun := riemannSphereTranslation_mdifferentiable a
  holomorphic_invFun := by
    simpa [Homeomorph.onePointCongr, complexTranslationHomeomorph,
      riemannSphereTranslation] using
      riemannSphereTranslation_mdifferentiable (-a)

/--
%%handwave
name: Affine restriction of a sphere automorphism fixing infinity
statement:
  If $B$ is a biholomorphism of $\widehat{\mathbb C}$ with
  $B(\infty)=\infty$, define the induced plane biholomorphism by
  $z\mapsto\chi_{\mathrm{fin}}(B(z))$ in the finite affine chart.
-/
noncomputable def biholomorphicComplexPlaneOfFixesInfinity
    (B : Biholomorphic RiemannSphere RiemannSphere)
    (hinfty : B.toHomeomorph OnePoint.infty = OnePoint.infty) :
    Biholomorphic ℂ ℂ := by
  let f : ℂ → ℂ := fun z ↦
    riemannSphereFiniteChart (B.toHomeomorph (z : RiemannSphere))
  let g : ℂ → ℂ := fun z ↦
    riemannSphereFiniteChart (B.toHomeomorph.symm (z : RiemannSphere))
  have hBfinite : ∀ z : ℂ,
      B.toHomeomorph (z : RiemannSphere) ≠ OnePoint.infty := by
    intro z hz
    apply OnePoint.coe_ne_infty z
    apply B.toHomeomorph.injective
    exact hz.trans hinfty.symm
  have hBinv_infty :
      B.toHomeomorph.symm OnePoint.infty = OnePoint.infty := by
    calc
      B.toHomeomorph.symm OnePoint.infty =
          B.toHomeomorph.symm (B.toHomeomorph OnePoint.infty) :=
        congrArg B.toHomeomorph.symm hinfty.symm
      _ = OnePoint.infty := B.toHomeomorph.symm_apply_apply OnePoint.infty
  have hBinvfinite : ∀ z : ℂ,
      B.toHomeomorph.symm (z : RiemannSphere) ≠ OnePoint.infty := by
    intro z hz
    apply OnePoint.coe_ne_infty z
    apply B.toHomeomorph.symm.injective
    exact hz.trans hBinv_infty.symm
  have hcoe_f : ∀ z : ℂ,
      ((f z : ℂ) : RiemannSphere) = B.toHomeomorph (z : RiemannSphere) := by
    intro z
    rw [← riemannSphereFiniteChart_symm_apply]
    exact riemannSphereFiniteChart.left_inv (by simp [hBfinite])
  have hcoe_g : ∀ z : ℂ,
      ((g z : ℂ) : RiemannSphere) = B.toHomeomorph.symm (z : RiemannSphere) := by
    intro z
    rw [← riemannSphereFiniteChart_symm_apply]
    exact riemannSphereFiniteChart.left_inv (by simp [hBinvfinite])
  have hleft : Function.LeftInverse g f := by
    intro z
    apply OnePoint.coe_injective
    calc
      ((g (f z) : ℂ) : RiemannSphere) =
          B.toHomeomorph.symm ((f z : ℂ) : RiemannSphere) := hcoe_g (f z)
      _ = B.toHomeomorph.symm (B.toHomeomorph (z : RiemannSphere)) := by
        rw [hcoe_f]
      _ = (z : RiemannSphere) := B.toHomeomorph.symm_apply_apply _
  have hright : Function.RightInverse g f := by
    intro z
    apply OnePoint.coe_injective
    calc
      ((f (g z) : ℂ) : RiemannSphere) =
          B.toHomeomorph ((g z : ℂ) : RiemannSphere) := hcoe_f (g z)
      _ = B.toHomeomorph (B.toHomeomorph.symm (z : RiemannSphere)) := by
        rw [hcoe_g]
      _ = (z : RiemannSphere) := B.toHomeomorph.apply_symm_apply _
  have hfiniteChart_mem : riemannSphereFiniteChart ∈ atlas ℂ RiemannSphere := by
    change riemannSphereFiniteChart ∈
      ({riemannSphereFiniteChart, riemannSphereInfinityChart} :
        Set (OpenPartialHomeomorph RiemannSphere ℂ))
    simp
  have hf : HolomorphicMap ℂ ℂ f := by
    intro z
    have hchart :=
      mdifferentiableAt_atlas (I := modelWithCornersSelf ℂ ℂ) hfiniteChart_mem
        (x := B.toHomeomorph (z : RiemannSphere)) (by simp [hBfinite])
    simpa [f, Function.comp_apply] using
      hchart.comp z
        ((B.holomorphic_toFun (z : RiemannSphere)).comp z
          (riemannSphereCoe_mdifferentiable z))
  have hg : HolomorphicMap ℂ ℂ g := by
    intro z
    have hchart :=
      mdifferentiableAt_atlas (I := modelWithCornersSelf ℂ ℂ) hfiniteChart_mem
        (x := B.toHomeomorph.symm (z : RiemannSphere)) (by simp [hBinvfinite])
    simpa [g, Function.comp_apply] using
      hchart.comp z
        ((B.holomorphic_invFun (z : RiemannSphere)).comp z
          (riemannSphereCoe_mdifferentiable z))
  exact
    { toHomeomorph :=
        { toFun := f
          invFun := g
          left_inv := hleft
          right_inv := hright
          continuous_toFun := hf.continuous
          continuous_invFun := hg.continuous }
      holomorphic_toFun := hf
      holomorphic_invFun := hg }

/--
%%handwave
name:
  Finite-chart restriction of a sphere automorphism
statement:
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be biholomorphic and
  fix infinity. If $F_0:\mathbb C\to\mathbb C$ is its restriction in the
  affine chart, then $F(F_0(z))$ is represented by the finite point
  $F_0(z)$; explicitly, $F(z)=F_0(z)$ after the canonical inclusion into
  the sphere.
proof:
  A finite point cannot map to infinity, since infinity is fixed and $F$ is
  injective. The affine chart and its inverse therefore cancel at $F(z)$.
-/
theorem coe_biholomorphicComplexPlaneOfFixesInfinity_apply
    (B : Biholomorphic RiemannSphere RiemannSphere)
    (hinfty : B.toHomeomorph OnePoint.infty = OnePoint.infty) (z : ℂ) :
    (((biholomorphicComplexPlaneOfFixesInfinity B hinfty).toHomeomorph z : ℂ) :
        RiemannSphere) = B.toHomeomorph (z : RiemannSphere) := by
  have hfinite : B.toHomeomorph (z : RiemannSphere) ≠ OnePoint.infty := by
    intro hz
    apply OnePoint.coe_ne_infty z
    apply B.toHomeomorph.injective
    exact hz.trans hinfty.symm
  change ((riemannSphereFiniteChart
    (B.toHomeomorph (z : RiemannSphere)) : ℂ) : RiemannSphere) = _
  rw [← riemannSphereFiniteChart_symm_apply]
  exact riemannSphereFiniteChart.left_inv (by simp [hfinite])

/--
%%handwave
name: Reciprocal-coordinate conjugate of a plane map at infinity
statement:
  For $f:\mathbb C\to\mathbb C$, define its reciprocal-coordinate expression
  by $g(w)=1/f(1/w)$ for $w\ne0$ and $g(0)=0$.
-/
def reciprocalConjugateAtInfinity (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun w ↦ (f w⁻¹)⁻¹) 0 0

/--
%%handwave
name:
  A proper entire map fixing zero is holomorphic in reciprocal coordinates
statement:
  Let $f:\mathbb C\to\mathbb C$ be entire and proper, with
  $f(z)=0$ exactly when $z=0$. Define
  $g(0)=0$ and $g(w)=1/f(1/w)$ for $w\ne0$. Then $g$ is entire.
proof:
  Properness gives $f(z)\to\infty$ as $z\to\infty$, hence $g(w)\to0$ as
  $w\to0$. Away from zero the reciprocal expression is holomorphic. The
  removable-singularity theorem therefore makes it holomorphic at zero as
  well.
-/
theorem reciprocalConjugateAtInfinity_differentiable
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hproper : IsProperMap f)
    (hzero : ∀ z, f z = 0 ↔ z = 0) :
    Differentiable ℂ (reciprocalConjugateAtInfinity f) := by
  let g : ℂ → ℂ := reciprocalConjugateAtInfinity f
  have hf_cocompact : Tendsto f (cocompact ℂ) (cocompact ℂ) :=
    (isProperMap_iff_tendsto_cocompact.mp hproper).2
  have hinv_to_cocompact :
      Tendsto Inv.inv (𝓝[≠] (0 : ℂ)) (cocompact ℂ) := by
    simpa [Metric.cobounded_eq_cocompact] using
      (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ))
  have hinv_to_zero :
      Tendsto Inv.inv (cocompact ℂ) (𝓝 (0 : ℂ)) := by
    simpa [Metric.cobounded_eq_cocompact] using
      (Filter.tendsto_inv₀_cobounded (α := ℂ))
  have hg_continuousAt_zero : ContinuousAt g 0 := by
    rw [show g = Function.update (fun w ↦ (f w⁻¹)⁻¹) 0 0 from rfl]
    rw [continuousAt_update_same]
    exact hinv_to_zero.comp (hf_cocompact.comp hinv_to_cocompact)
  have hg_punctured :
      ∀ᶠ w in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ g w := by
    filter_upwards [eventually_mem_nhdsWithin] with w hw
    have hw_ne : w ≠ 0 := by simpa using hw
    have hfw_ne : f w⁻¹ ≠ 0 := by
      exact (hzero w⁻¹).not.mpr (inv_ne_zero hw_ne)
    have hdiff : DifferentiableAt ℂ (fun u ↦ (f u⁻¹)⁻¹) w := by
      fun_prop
    apply hdiff.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hw_ne] with u hu
    simp [g, reciprocalConjugateAtInfinity, hu]
  have hg_zero : DifferentiableAt ℂ g 0 :=
    (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hg_punctured hg_continuousAt_zero).differentiableAt
  intro w
  by_cases hw : w = 0
  · simpa [hw] using hg_zero
  · have hfw_ne : f w⁻¹ ≠ 0 := by
      exact (hzero w⁻¹).not.mpr (inv_ne_zero hw)
    have hdiff : DifferentiableAt ℂ (fun u ↦ (f u⁻¹)⁻¹) w := by
      fun_prop
    apply hdiff.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hw] with u hu
    simp [reciprocalConjugateAtInfinity, hu]

/--
%%handwave
name:
  Automorphisms of the complex plane are affine
statement:
  If $F:\mathbb C\to\mathbb C$ is biholomorphic, then there are
  $a,b\in\mathbb C$ with $a\ne0$ such that $F(z)=az+b$ for every
  $z\in\mathbb C$.
proof:
  Translate the range so that $F(0)=0$. Properness makes
  $g(w)=1/F(1/w)$ removable at zero. Applying the same construction to
  $F^{-1}$ shows that the two reciprocal germs are inverse, so $g'(0)\ne0$.
  Divide $g$ by $w$ using its holomorphic divided difference. The reciprocal
  of that quotient shows that $F(z)-az$ tends to a finite limit at infinity.
  Liouville's theorem makes this difference constant, and the normalization
  makes the constant zero. Undoing the translation gives the result.
-/
theorem biholomorphic_complexPlane_eq_affine (B : Biholomorphic ℂ ℂ) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, B.toHomeomorph z = a * z + b := by
  let b : ℂ := B.toHomeomorph 0
  let N : Biholomorphic ℂ ℂ :=
    B.trans (complexTranslationBiholomorphic (-b))
  have hN_zero : N.toHomeomorph 0 = 0 := by
    simp [N, b, Biholomorphic.trans, complexTranslationBiholomorphic]
  have hN_zero_iff : ∀ z, N.toHomeomorph z = 0 ↔ z = 0 := by
    intro z
    constructor
    · intro hz
      exact N.toHomeomorph.injective (hz.trans hN_zero.symm)
    · rintro rfl
      exact hN_zero
  have hNinv_zero : N.toHomeomorph.symm 0 = 0 := by
    calc
      N.toHomeomorph.symm 0 =
          N.toHomeomorph.symm (N.toHomeomorph 0) :=
        congrArg N.toHomeomorph.symm hN_zero.symm
      _ = 0 := N.toHomeomorph.symm_apply_apply 0
  have hNinv_zero_iff : ∀ z, N.toHomeomorph.symm z = 0 ↔ z = 0 := by
    intro z
    constructor
    · intro hz
      apply N.toHomeomorph.symm.injective
      simpa [hNinv_zero] using hz
    · rintro rfl
      exact hNinv_zero
  have hN_diff : Differentiable ℂ N.toHomeomorph :=
    mdifferentiable_iff_differentiable.mp N.holomorphic_toFun
  have hNinv_diff : Differentiable ℂ N.toHomeomorph.symm :=
    mdifferentiable_iff_differentiable.mp N.holomorphic_invFun
  let g : ℂ → ℂ := reciprocalConjugateAtInfinity N.toHomeomorph
  let h : ℂ → ℂ := reciprocalConjugateAtInfinity N.toHomeomorph.symm
  have hg : Differentiable ℂ g :=
    reciprocalConjugateAtInfinity_differentiable N.toHomeomorph hN_diff
      N.toHomeomorph.isProperMap hN_zero_iff
  have hh : Differentiable ℂ h :=
    reciprocalConjugateAtInfinity_differentiable N.toHomeomorph.symm hNinv_diff
      N.toHomeomorph.symm.isProperMap hNinv_zero_iff
  have hg_zero : g 0 = 0 := by
    simp [g, reciprocalConjugateAtInfinity]
  have hh_zero : h 0 = 0 := by
    simp [h, reciprocalConjugateAtInfinity]
  have hgh : g ∘ h = id := by
    funext w
    by_cases hw : w = 0
    · simp [hw, hg_zero, hh_zero]
    · have hwinv_ne : w⁻¹ ≠ 0 := inv_ne_zero hw
      have hpre_ne : N.toHomeomorph.symm w⁻¹ ≠ 0 := by
        exact (hNinv_zero_iff w⁻¹).not.mpr hwinv_ne
      have hh_ne : h w ≠ 0 := by
        simpa [h, reciprocalConjugateAtInfinity, hw] using inv_ne_zero hpre_ne
      simp [Function.comp_apply, g, h, reciprocalConjugateAtInfinity,
        hw, hpre_ne]
  have hderiv_comp :
      HasDerivAt (g ∘ h) (deriv g (h 0) * deriv h 0) 0 :=
    (hg (h 0)).hasDerivAt.comp 0 (hh 0).hasDerivAt
  rw [hgh] at hderiv_comp
  have hderiv_mul : deriv g 0 * deriv h 0 = 1 := by
    simpa [hh_zero] using hderiv_comp.unique (hasDerivAt_id' 0)
  have hg_deriv_ne : deriv g 0 ≠ 0 :=
    left_ne_zero_of_mul_eq_one hderiv_mul
  let q : ℂ → ℂ := dslope g 0
  have hq_diff : Differentiable ℂ q := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope
      (f := g) (s := Set.univ) (c := 0) univ_mem).mpr hg.differentiableOn
  have hg_zero_iff : ∀ w, g w = 0 ↔ w = 0 := by
    intro w
    by_cases hw : w = 0
    · simp [hw, hg_zero]
    · have hN_ne : N.toHomeomorph w⁻¹ ≠ 0 := by
        exact (hN_zero_iff w⁻¹).not.mpr (inv_ne_zero hw)
      simp [g, reciprocalConjugateAtInfinity, inv_eq_zero, hN_ne, hw]
  have hq_ne : ∀ w, q w ≠ 0 := by
    intro w
    by_cases hw : w = 0
    · subst w
      simpa [q, dslope_same] using hg_deriv_ne
    · rw [show q w = slope g 0 w by
        exact dslope_of_ne g hw]
      simp only [slope_def_field, sub_zero, hg_zero]
      exact mul_ne_zero ((hg_zero_iff w).not.mpr hw) (inv_ne_zero hw)
  let k : ℂ → ℂ := fun w ↦ (q w)⁻¹
  have hk_diff : Differentiable ℂ k := by
    exact hq_diff.inv hq_ne
  let a : ℂ := k 0
  have ha_ne : a ≠ 0 := by
    exact inv_ne_zero (hq_ne 0)
  have hlinear_at_infinity :
      Tendsto (fun z ↦ N.toHomeomorph z - a * z)
        (cocompact ℂ) (𝓝 (deriv k 0)) := by
    have hinv_to_zero :
        Tendsto Inv.inv (cocompact ℂ) (𝓝 (0 : ℂ)) := by
      simpa [Metric.cobounded_eq_cocompact] using
        (Filter.tendsto_inv₀_cobounded (α := ℂ))
    have hdslope :
        Tendsto (dslope k 0) (𝓝 (0 : ℂ)) (𝓝 (deriv k 0)) := by
      have hc : ContinuousAt (dslope k 0) 0 :=
        continuousAt_dslope_same.mpr (hk_diff 0)
      simpa [dslope_same] using hc.tendsto
    apply (hdslope.comp hinv_to_zero).congr'
    have hne : ({0} : Set ℂ)ᶜ ∈ cocompact ℂ :=
      (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
    filter_upwards [hne] with z hz
    have hz_ne : z ≠ 0 := by simpa using hz
    have hNz_ne : N.toHomeomorph z ≠ 0 :=
      (hN_zero_iff z).not.mpr hz_ne
    have hq_formula : q z⁻¹ = z * (N.toHomeomorph z)⁻¹ := by
      rw [show q z⁻¹ = slope g 0 z⁻¹ by
        exact dslope_of_ne g (inv_ne_zero hz_ne)]
      simp [slope_def_field, g, reciprocalConjugateAtInfinity,
        inv_ne_zero hz_ne, mul_comm]
    have hk_formula : k z⁻¹ = N.toHomeomorph z * z⁻¹ := by
      rw [show k z⁻¹ = (q z⁻¹)⁻¹ from rfl, hq_formula]
      field_simp [hz_ne, hNz_ne]
    change dslope k 0 z⁻¹ = N.toHomeomorph z - a * z
    rw [show dslope k 0 z⁻¹ = slope k 0 z⁻¹ by
      exact dslope_of_ne k (inv_ne_zero hz_ne)]
    simp only [slope_def_field, sub_zero]
    rw [hk_formula]
    dsimp [a]
    field_simp [hz_ne]
  have hdiff_difference :
      Differentiable ℂ (fun z ↦ N.toHomeomorph z - a * z) := by
    fun_prop
  have hdifference_const :=
    hdiff_difference.eq_const_of_tendsto_cocompact hlinear_at_infinity
  have hN_linear : ∀ z, N.toHomeomorph z = a * z := by
    intro z
    have hderiv_zero : deriv k 0 = 0 := by
      have hzero := congrArg (fun F : ℂ → ℂ ↦ F 0) hdifference_const
      have hzero' : (0 : ℂ) = deriv k 0 := by
        simpa [hN_zero] using hzero
      exact hzero'.symm
    have hz := congrArg (fun F : ℂ → ℂ ↦ F z) hdifference_const
    rw [hderiv_zero] at hz
    exact sub_eq_zero.mp (by simpa using hz)
  refine ⟨a, b, ha_ne, ?_⟩
  intro z
  have hz := hN_linear z
  change B.toHomeomorph z + -b = a * z at hz
  calc
    B.toHomeomorph z = (B.toHomeomorph z + -b) + b := by ring
    _ = a * z + b := by rw [hz]

/--
%%handwave
name:
  Fixed-point-free plane automorphisms are nontrivial translations
statement:
  Let $F:\mathbb C\to\mathbb C$ be biholomorphic and suppose
  $F(z)\ne z$ for every $z\in\mathbb C$. Then there is a nonzero
  $b\in\mathbb C$ such that $F(z)=z+b$ for all $z$.
proof:
  Write $F(z)=az+b$ with $a\ne0$. If $a\ne1$, then
  $z=b/(1-a)$ is a fixed point. Hence $a=1$, and $b\ne0$ because a zero
  translation fixes every point.
-/
theorem biholomorphic_complexPlane_eq_translation_of_fixedPointFree
    (B : Biholomorphic ℂ ℂ)
    (hfree : ∀ z : ℂ, B.toHomeomorph z ≠ z) :
    ∃ b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, B.toHomeomorph z = z + b := by
  rcases biholomorphic_complexPlane_eq_affine B with ⟨a, b, ha, hB⟩
  have ha_one : a = 1 := by
    by_contra ha_one
    let z : ℂ := b / (1 - a)
    apply hfree z
    rw [hB]
    dsimp [z]
    field_simp [sub_ne_zero.mpr (Ne.symm ha_one)]
    ring
  have hb_ne : b ≠ 0 := by
    intro hb
    apply hfree 0
    simp [hB, ha_one, hb]
  refine ⟨b, hb_ne, ?_⟩
  intro z
  simpa [ha_one] using hB z

/--
%%handwave
name:
  Every automorphism of the Riemann sphere has a fixed point
statement:
  Every biholomorphic map
  $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fixes at least one point:
  there is $p\in\widehat{\mathbb C}$ with $F(p)=p$.
proof:
  If infinity is fixed, there is nothing to prove. Otherwise write
  $F(\infty)=c$, translate by $-c$, and invert; the resulting automorphism
  fixes infinity, so its finite-chart restriction is affine, say $az+b$ with
  $a\ne0$. The fundamental theorem of algebra gives a root of
  $(az+b)(z-c)-1$. At such a root the defining translation-and-inversion
  equation simplifies to $F(z)=z$.
-/
theorem biholomorphic_riemannSphere_has_fixedPoint
    (B : Biholomorphic RiemannSphere RiemannSphere) :
    ∃ p : RiemannSphere, B.toHomeomorph p = p := by
  induction hvalue : B.toHomeomorph OnePoint.infty using OnePoint.rec with
  | infty =>
      exact ⟨OnePoint.infty, hvalue⟩
  | coe c =>
      let T : Biholomorphic RiemannSphere RiemannSphere :=
        riemannSphereTranslationBiholomorphic (-c)
      let A : Biholomorphic RiemannSphere RiemannSphere :=
        T.trans riemannSphereInvBiholomorphic
      let H : Biholomorphic RiemannSphere RiemannSphere := B.trans A
      have hH_infty : H.toHomeomorph OnePoint.infty = OnePoint.infty := by
        change riemannSphereInv
          (riemannSphereTranslation (-c)
            (B.toHomeomorph OnePoint.infty)) = OnePoint.infty
        rw [hvalue]
        simp
      let P : Biholomorphic ℂ ℂ :=
        biholomorphicComplexPlaneOfFixesInfinity H hH_infty
      rcases biholomorphic_complexPlane_eq_affine P with
        ⟨a, b, ha, hP⟩
      let q : Polynomial ℂ :=
        Polynomial.C a * Polynomial.X ^ 2 +
          Polynomial.C (b - a * c) * Polynomial.X +
            Polynomial.C (-b * c - 1)
      have hq_degree : q.degree = 2 := by
        simpa [q] using
          (Polynomial.degree_quadratic (R := ℂ) (b := b - a * c)
            (c := -b * c - 1) ha)
      have hq_positive : 0 < q.degree := by
        rw [hq_degree]
        norm_num
      rcases Complex.exists_root hq_positive with ⟨z, hz⟩
      have hz_poly : (a * z + b) * (z - c) - 1 = 0 := by
        calc
          (a * z + b) * (z - c) - 1 = q.eval z := by
            simp [q]
            ring
          _ = 0 := hz
      have hz_product : (a * z + b) * (z - c) = 1 :=
        sub_eq_zero.mp hz_poly
      have hdenom : a * z + b ≠ 0 := by
        intro hzero
        rw [hzero, zero_mul] at hz_product
        exact zero_ne_one hz_product
      have hinv_denom : (a * z + b)⁻¹ = z - c := by
        calc
          (a * z + b)⁻¹ = (a * z + b)⁻¹ * 1 := by simp
          _ = (a * z + b)⁻¹ * ((a * z + b) * (z - c)) := by
            rw [hz_product]
          _ = z - c := by field_simp [hdenom]
      have hH_finite :
          H.toHomeomorph (z : RiemannSphere) =
            ((a * z + b : ℂ) : RiemannSphere) := by
        rw [← coe_biholomorphicComplexPlaneOfFixesInfinity_apply H hH_infty]
        exact congrArg ((↑) : ℂ → RiemannSphere) (hP z)
      have htranslated :
          riemannSphereTranslation (-c)
              (B.toHomeomorph (z : RiemannSphere)) =
            ((z - c : ℂ) : RiemannSphere) := by
        calc
          riemannSphereTranslation (-c)
                (B.toHomeomorph (z : RiemannSphere)) =
              riemannSphereInv
                (riemannSphereInv
                  (riemannSphereTranslation (-c)
                    (B.toHomeomorph (z : RiemannSphere)))) := by
            symm
            apply riemannSphereInv_inv
          _ = riemannSphereInv ((a * z + b : ℂ) : RiemannSphere) := by
            rw [← hH_finite]
            rfl
          _ = (((a * z + b)⁻¹ : ℂ) : RiemannSphere) := by
            exact riemannSphereInv_coe_of_ne_zero hdenom
          _ = ((z - c : ℂ) : RiemannSphere) := by
            rw [hinv_denom]
      refine ⟨(z : RiemannSphere), ?_⟩
      calc
        B.toHomeomorph (z : RiemannSphere) =
            riemannSphereTranslation c
              (riemannSphereTranslation (-c)
                (B.toHomeomorph (z : RiemannSphere))) := by
          symm
          induction B.toHomeomorph (z : RiemannSphere) using OnePoint.rec with
          | infty => simp
          | coe w => simp
        _ = riemannSphereTranslation c ((z - c : ℂ) : RiemannSphere) := by
          rw [htranslated]
        _ = (z : RiemannSphere) := by
          simp

end

end Uniformization

end JJMath
