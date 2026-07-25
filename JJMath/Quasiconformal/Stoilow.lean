import JJMath.Quasiconformal.MeasurableRiemannMapping
import JJMath.Quasiconformal.WeakHolomorphic
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Sobolev Stoilow factorization

This file uses the measurable Riemann mapping theorem to straighten the
Beltrami coefficient of a continuous planar map of bounded distortion.  The
remaining factor is weakly holomorphic and hence holomorphic by the Sobolev
Weyl lemma.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Holomorphic factor after cancellation of equal Beltrami coefficients
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally $W^{1,2}$ with
  weak differential $Df$. Let $\Phi:\mathbb C\to\mathbb C$ be a
  quasiconformal homeomorphism with weak differential $D\Phi$. If both
  differentials satisfy
  $$
    \partial_{\bar z}f=\mu\,\partial_zf,
    \qquad
    \partial_{\bar z}\Phi=\mu\,\partial_z\Phi
  $$
  almost everywhere, then there is an entire holomorphic function $g$ such
  that
  $$
    f=g\circ\Phi.
  $$
proof:
  Put $g=f\circ\Phi^{-1}$. The quasiconformal Sobolev chain rule gives the
  weak differential
  $$
    Dg(y)=Df(\Phi^{-1}(y))\circ D\Phi^{-1}(y).
  $$
  [The inverse differential is the pseudoinverse of $D\Phi$](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.inverseDifferentialCandidate_isWeakDerivativeOn), and [the Jacobian of $\Phi$ is positive almost everywhere](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.weakJacobian_pos_ae). Thus [equal Beltrami coefficients cancel in the composite differential](lean:JJMath.Quasiconformal.weakDBar_comp_realLinearPseudoInverse_eq_zero_of_same_beltrami), so $\partial_{\bar z}g=0$ almost everywhere. [The Sobolev Weyl lemma](lean:JJMath.Quasiconformal.IsLocalW12On.differentiableOn_complex_of_continuousOn_of_weakDBar_eq_zero_ae) makes $g$ holomorphic.
-/
theorem exists_differentiable_factor_of_same_weakBeltrami
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    {Φ : ℂ ≃ₜ ℂ} {dΦ : ℂ → ℂ →L[ℝ] ℂ}
    {μ : ℂ → ℂ} {K : ℝ}
    (hf : Continuous f)
    (hfW : IsLocalW12On Set.univ f df)
    (hΦqc : IsKQuasiconformalBetween K (wholePlaneSubtypeHomeomorph Φ))
    (hΦW : IsLocalW12On Set.univ Φ dΦ)
    (hfbel : WeakBeltramiEquationOn Set.univ μ df)
    (hΦbel : WeakBeltramiEquationOn Set.univ μ dΦ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z : ℂ, f z = g (Φ z) := by
  let P := wholePlaneSubtypeHomeomorph Φ
  have hΦambient :
      IsLocalW12On Set.univ (ambientMap P) dΦ := by
    apply hΦW.congr_ae
    filter_upwards with z
    rw [ambientMap_apply P ⟨z, Set.mem_univ z⟩]
    rfl
  obtain ⟨dΨ, hdΨcomp, hdΨL2, _hdΨdist⟩ :=
    hΦqc.exists_inverseDifferentialCandidate_memLpOn_compact hΦambient
  have hΨW :
      IsLocalW12On Set.univ (ambientMap P.symm) dΨ := by
    refine ⟨isOpen_univ,
      hΦqc.inverseDifferentialCandidate_isWeakDerivativeOn
        hΦambient hdΨcomp hdΨL2, ?_⟩
    intro C hC _hCuniv
    exact ⟨memLp_restrict_of_isCompact_of_continuousOn hC
      ((continuousOn_ambientMap P.symm).mono (Set.subset_univ _)),
      hdΨL2 C hC (Set.subset_univ _)⟩
  let g : ℂ → ℂ := fun y ↦ f (ambientMap P.symm y)
  let dg : ℂ → ℂ →L[ℝ] ℂ := fun y ↦
    (df (ambientMap P.symm y)).comp (dΨ y)
  have hgW : IsLocalW12On Set.univ g dg := by
    simpa only [g, dg] using
      hΦqc.symm.postcomp_continuous_isLocalW12On
        hΨW hfW hf.continuousOn
  have hgcont : Continuous g := by
    have heq : g = fun y ↦ f (Φ.symm y) := by
      funext y
      simp only [g]
      rw [ambientMap_apply P.symm ⟨y, Set.mem_univ y⟩]
      rfl
    rw [heq]
    exact hf.comp Φ.symm.continuous
  have hJpos :
      ∀ᵐ z ∂volume.restrict Set.univ,
        0 < weakJacobian (dΦ z) :=
    hΦqc.weakJacobian_pos_ae hΦambient
  have hfbel' :
      ∀ᵐ z ∂volume.restrict Set.univ,
        weakDBar (df z) = μ z * weakDZ (df z) := by
    simpa only [WeakBeltramiEquationOn, weakDBarField, weakDZField] using
      hfbel
  have hΦbel' :
      ∀ᵐ z ∂volume.restrict Set.univ,
        weakDBar (dΦ z) = μ z * weakDZ (dΦ z) := by
    simpa only [WeakBeltramiEquationOn, weakDBarField, weakDZField] using
      hΦbel
  have hdgbar :
      ∀ᵐ y ∂volume.restrict Set.univ, weakDBar (dg y) = 0 := by
    apply ae_restrict_target_of_ae_restrict_source_of_hasLusinNOn
      (P := fun z ↦
        weakDBar (df z) = μ z * weakDZ (df z) ∧
          weakDBar (dΦ z) = μ z * weakDZ (dΦ z) ∧
          0 < weakJacobian (dΦ z) ∧
          dΨ (ambientMap P z) = realLinearPseudoInverse (dΦ z))
      (Q := fun y ↦ weakDBar (dg y) = 0)
      P MeasurableSet.univ hΦqc.hasLusinNOn
    · filter_upwards [hfbel', hΦbel', hJpos, hdΨcomp]
        with z hfz hΦz hJz hΨz
      exact ⟨hfz, hΦz, hJz, hΨz⟩
    · intro z hz ⟨hfz, hΦz, hJz, hΨz⟩
      simp only [dg]
      rw [ambientMap_symm_apply_ambientMap P ⟨z, hz⟩, hΨz]
      exact
        weakDBar_comp_realLinearPseudoInverse_eq_zero_of_same_beltrami
          (df z) (dΦ z) (μ z) hJz hfz hΦz
  have hgdiffOn : DifferentiableOn ℂ g Set.univ :=
    hgW.differentiableOn_complex_of_continuousOn_of_weakDBar_eq_zero_ae
      hgcont.continuousOn hdgbar
  refine ⟨g, differentiableOn_univ.mp hgdiffOn, ?_⟩
  intro z
  simp only [g]
  rw [show Φ z = ambientMap P z by
    rw [ambientMap_apply P ⟨z, Set.mem_univ z⟩]
    rfl]
  exact congrArg f
    (ambientMap_symm_apply_ambientMap P ⟨z, Set.mem_univ z⟩).symm

/--
%%handwave
name:
  Sobolev Stoilow factorization on the plane
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and locally $W^{1,2}$ with
  weak differential $Df$. Suppose $K\geq1$ and
  $$
    \lVert Df(z)\rVert_{\mathrm{op}}^2
      \leq K\operatorname{Jac}f(z)
  $$
  almost everywhere. Then there are a quasiconformal homeomorphism
  $\Phi:\mathbb C\to\mathbb C$ fixing $0$ and $1$ and an entire holomorphic
  function $g$ such that
  $$
    f=g\circ\Phi.
  $$
proof:
  Extract the bounded measurable coefficient
  $\mu=\partial_{\bar z}f/\partial_zf$. [The whole-plane measurable Riemann mapping theorem](lean:JJMath.Quasiconformal.exists_normalized_plane_homeomorph_of_beltrami) gives a normalized quasiconformal $\Phi$ with the same coefficient. Apply [factorization after cancellation of the common coefficient](lean:JJMath.Quasiconformal.exists_differentiable_factor_of_same_weakBeltrami).
tags:
  milestone
-/
theorem exists_stoilow_factorization_of_boundedDistortion
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {K : ℝ}
    (hf : Continuous f)
    (hfW : IsLocalW12On Set.univ f df)
    (hK : 1 ≤ K)
    (hdist : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)) :
    ∃ Φ : ℂ ≃ₜ ℂ, ∃ g : ℂ → ℂ,
      Φ 0 = 0 ∧
        Φ 1 = 1 ∧
        Differentiable ℂ g ∧
        ∀ z : ℂ, f z = g (Φ z) := by
  obtain ⟨hk0, hk1, hμmeas, hfbel, hμbound⟩ :=
    hfW.boundedDistortion_beltramiData hK hdist
  have hμbound' :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖beltramiCoefficient df z‖ ≤ (K - 1) / (K + 1) := by
    simpa only [HasEssentialNormLEOn, Measure.restrict_univ] using hμbound
  obtain ⟨Φ, dΦ, hΦzero, hΦone, hΦqc, hΦW, hΦbel, _hΦJ⟩ :=
    exists_normalized_plane_homeomorph_of_beltrami
      (beltramiCoefficient df) hμmeas hk0 hk1 hμbound'
  obtain ⟨g, hgdiff, hfactor⟩ :=
    exists_differentiable_factor_of_same_weakBeltrami
      hf hfW hΦqc hΦW hfbel hΦbel
  exact ⟨Φ, g, hΦzero, hΦone, hgdiff, hfactor⟩

end

end Quasiconformal

end JJMath
