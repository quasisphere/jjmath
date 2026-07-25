import JJMath.Quasiconformal.PrincipalSolution
import JJMath.Quasiconformal.OpenDiscrete

/-!
# Principal homeomorphisms for compactly supported Beltrami coefficients

This file assembles the analytic principal solution, the planar open/discrete
theorem, and integer degree one at infinity into a whole-plane homeomorphism.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

set_option maxHeartbeats 2000000 in
/--
%%handwave
name:
  Principal homeomorphism for a compactly supported Beltrami coefficient
statement:
  Let $\mu:\mathbb C\to\mathbb C$ be measurable, vanish almost everywhere
  outside a disk, and satisfy $|\mu|\leq k<1$ almost everywhere. Then there
  are a homeomorphism $F:\mathbb C\to\mathbb C$ and a weak differential $DF$
  such that $F\in W^{1,2}_{\mathrm{loc}}(\mathbb C)$, $F$ preserves planar
  orientation,
  $$
    \partial_{\bar z}F=\mu\,\partial_zF,
    \qquad
    |DF|^2\leq\frac{1+k}{1-k}J_F
  $$
  almost everywhere, and $F(z)-z\to0$ as $z\to\infty$.
proof:
  Construct the continuous analytic principal solution by the near-$2$
  Beltrami resolvent and rough Cauchy transform. It is proper and nonconstant.
  The planar bounded-distortion theorem makes it open with discrete fibers
  and positive local indices. Its outer index at infinity is one, and boundary
  additivity identifies this with the sum of the positive local indices in
  each fiber. Hence every fiber is a singleton and the open continuous map is
  a homeomorphism. Its underlying function is unchanged, so all analytic
  conclusions and the normalization at infinity carry over.
-/
theorem exists_principalHomeomorphism_of_compactSupport
    (μ : ℂ → ℂ)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k R : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → μ z = 0) :
    ∃ F : ℂ ≃ₜ ℂ, ∃ dF : ℂ → ℂ →L[ℝ] ℂ,
      IsLocalW12On Set.univ F dF ∧
        PreservesPlanarOrientation (wholePlaneSubtypeHomeomorph F) ∧
        WeakBeltramiEquationOn Set.univ μ dF ∧
        (∀ᵐ z ∂(volume : Measure ℂ),
          ‖dF z‖ ^ 2 ≤ ((1 + k) / (1 - k)) * weakJacobian (dF z)) ∧
        Tendsto (fun z ↦ F z - z) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨P, h, hhp, hh2, hhsupport, hrest⟩ :=
    exists_analyticPrincipalSolution_of_compactSupport
      μ hμmeas hk0 hk1 hbound hzero
  dsimp only at hrest
  rcases hrest with ⟨hf, hproper, hW, hBeltrami, hdist, hInf⟩
  have hK : 1 ≤ (1 + k) / (1 - k) := by
    apply (le_div_iff₀ (sub_pos.mpr hk1)).2
    linarith
  obtain ⟨hopen, hdiscrete, hpos⟩ :=
    open_discrete_and_localIndex_pos_of_boundedDistortion_of_isProperMap
      hf hW hK hdist hproper
  let F : ℂ ≃ₜ ℂ :=
    homeomorphOfTendstoSubIdOfIsOpenMapOfLocalIndexPos
      hf hInf hopen hdiscrete hpos
  have hindexf (z : ℂ) :
      planarLocalIndex (principalBeltramiMap h) hf z
        (principalBeltramiMap h z) rfl
        (hdiscrete (principalBeltramiMap h z)) = 1 :=
    planarLocalIndex_eq_one_of_tendsto_sub_id_cocompact_zero
      hf hInf hopen hdiscrete hpos z
  have hindexF (z : ℂ) :
      planarLocalIndex F F.continuous z (F z) rfl
        (isDiscrete_fiber_homeomorph F (F z)) = 1 := by
    simpa only [F,
      homeomorphOfTendstoSubIdOfIsOpenMapOfLocalIndexPos_apply] using hindexf z
  have horient :
      PreservesPlanarOrientation (wholePlaneSubtypeHomeomorph F) :=
    preservesPlanarOrientation_wholePlaneSubtype_of_localIndex_eq_one
      F hindexF
  refine ⟨F,
    principalBeltramiWeakDifferential h
      (beurlingTransformL2 (hh2.toLp h) : ℂ → ℂ), ?_, horient, hBeltrami,
        hdist, ?_⟩
  · simpa only [F,
      homeomorphOfTendstoSubIdOfIsOpenMapOfLocalIndexPos_apply] using hW
  · simpa only [F,
      homeomorphOfTendstoSubIdOfIsOpenMapOfLocalIndexPos_apply] using hInf

end

end Quasiconformal

end JJMath
