import JJMath.Quasiconformal.Compactness
import JJMath.Quasiconformal.RiemannSphereBeltrami

/-!
# Beltrami compactness on the Riemann sphere

The analytic compactness engine works in the affine and reciprocal planar
charts. This file packages its hypotheses and conclusion using spherical
Beltrami differentials and quasiconformal surface maps.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

open Quasiconformal

namespace BeltramiDifferential

/--
%%handwave
name:
  Finite-coordinate realization determines the spherical Beltrami coefficient
statement:
  Let $\mu$ be a Beltrami differential on $\widehat{\mathbb C}$, and let
  $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be a normalized
  $K$-quasiconformal homeomorphism. If the finite-coordinate representative
  of $F$ belongs locally to $W^{1,2}$ and satisfies
  $$
    \partial_{\bar z}F_{\mathrm{fin}}
      =\mu_{\mathrm{fin}}\,\partial_zF_{\mathrm{fin}}
  $$
  almost everywhere, then $F$ realizes $\mu$ in both the finite and
  reciprocal coordinates.
proof:
  Conjugate $F$ by spherical inversion. The reciprocal-coordinate chain rule
  supplies a weak differential whose coefficient is the inversion pullback
  of $\mu_{\mathrm{fin}}$. Identify this coordinate map with the reciprocal
  representative of $F$, then replace the coefficient almost everywhere
  using the intrinsic $(-1,1)$-differential transition law.
-/
theorem isBeltramiDifferentialOf_of_finite
    {μ : BeltramiDifferential RiemannSphere}
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    {dFinite : ℂ → ℂ →L[ℝ] ℂ}
    (hFiniteLocal : IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph F hF.2.2) dFinite)
    (hFiniteBeltrami :
      WeakBeltramiEquationOn Set.univ (finiteCoefficient μ) dFinite) :
    IsBeltramiDifferentialOf μ F := by
  obtain ⟨dInfinity, hInfinityAsInvLocal, hInfinityBeltrami⟩ :=
    hqc.exists_invConjugate_finiteChart_weakDifferential_weakBeltrami
      hF hFiniteLocal hFiniteBeltrami
  have hInfinityLocal : IsLocalW12On Set.univ
      (riemannSphereInfinityChartHomeomorph F hF.1) dInfinity := by
    apply hInfinityAsInvLocal.congr_ae
    filter_upwards with z
    exact
      (riemannSphereFiniteChartHomeomorph_invConjugate_apply hF z).symm
  have hcompatible :
      inversionPullbackBeltrami (finiteCoefficient μ) =ᵐ[volume]
        infinityCoefficient μ :=
    (infinityCoefficient_ae_eq_inversionPullback μ).symm
  have hInfinityBeltrami' :
      WeakBeltramiEquationOn Set.univ
        (infinityCoefficient μ) dInfinity := by
    apply hInfinityBeltrami.congr_coefficient_ae
    simpa only [Measure.restrict_univ] using hcompatible
  intro x
  induction x using OnePoint.rec with
  | infty =>
      refine ⟨dInfinity, ?_, ?_⟩
      · have hsource :
            riemannSurfaceChartMapSource F OnePoint.infty
                (F OnePoint.infty) = Set.univ := by
          rw [hF.2.2]
          rw [← riemannSurfaceChartRepresentation_source]
          simp only [riemannSurfaceChartRepresentation,
            chartAt_riemannSphere_infty]
          exact
            riemannSphere_infinityChartRepresentation_source_eq_univ_of_map_zero
              F hF.1
        rw [hsource]
        have hmap :
            riemannSurfaceChartMap F OnePoint.infty (F OnePoint.infty) =
              riemannSphereInfinityChartHomeomorph F hF.1 := by
          funext z
          simp [riemannSurfaceChartMap, hF.2.2]
        rw [hmap]
        exact hInfinityLocal
      · have hsource :
            riemannSurfaceChartMapSource F OnePoint.infty
                (F OnePoint.infty) = Set.univ := by
          rw [hF.2.2]
          rw [← riemannSurfaceChartRepresentation_source]
          simp only [riemannSurfaceChartRepresentation,
            chartAt_riemannSphere_infty]
          exact
            riemannSphere_infinityChartRepresentation_source_eq_univ_of_map_zero
              F hF.1
        rw [hsource, achart_riemannSphere_infty]
        exact hInfinityBeltrami'
  | coe z =>
      have hfinite :
          F (z : RiemannSphere) ≠ OnePoint.infty := by
        intro hz
        exact OnePoint.coe_ne_infty z
          (F.injective (hz.trans hF.2.2.symm))
      induction hval : F (z : RiemannSphere) using OnePoint.rec with
      | infty => exact (hfinite hval).elim
      | coe w =>
          refine ⟨dFinite, ?_, ?_⟩
          · have hsource :
                riemannSurfaceChartMapSource F (z : RiemannSphere)
                    (w : RiemannSphere) = Set.univ := by
              rw [← riemannSurfaceChartRepresentation_source]
              simp only [riemannSurfaceChartRepresentation,
                chartAt_riemannSphere_coe]
              exact
                riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
                  F hF.2.2
            rw [hsource]
            have hmap :
                riemannSurfaceChartMap F (z : RiemannSphere)
                    (w : RiemannSphere) =
                  riemannSphereFiniteChartHomeomorph F hF.2.2 := by
              funext t
              simp [riemannSurfaceChartMap]
            rw [hmap]
            exact hFiniteLocal
          · have hsource :
                riemannSurfaceChartMapSource F (z : RiemannSphere)
                    (w : RiemannSphere) = Set.univ := by
              rw [← riemannSurfaceChartRepresentation_source]
              simp only [riemannSurfaceChartRepresentation,
                chartAt_riemannSphere_coe]
              exact
                riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
                  F hF.2.2
            rw [hsource, achart_riemannSphere_coe]
            exact hFiniteBeltrami

end BeltramiDifferential

namespace Quasiconformal

set_option maxHeartbeats 7000000 in
/--
%%handwave
name:
  Spherical compactness for convergent Beltrami differentials
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be $K$-quasiconformal homeomorphisms realizing measurable
  Beltrami differentials $\mu_n$, and suppose that $F_n$ are normalized so that they fix $0,1,\infty$. Suppose $\mu_n\to\mu$ almost everywhere and
  $$
  |\mu_n|,|\mu|\leq k<1
  $$
  essentially, where $k\geq0$. Then a subsequence, together with its
  inverses, converges uniformly on the sphere to a normalized homeomorphism
  $G$. The limit is
  $\frac{1+k}{1-k}$-quasiconformal and realizes $\mu$.
proof:
  Extract the affine weak differential from each realization.
  On the sphere, measurability, essential bounds, and almost-everywhere
  convergence are equivalent to their affine-coordinate forms. Apply
  [a subsequence and its inverses converge uniformly to a normalized sphere homeomorphism satisfying the limiting affine Beltrami equation](lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_spherical_compactness_of_isLocalW12On), then use the reciprocal chart to package the limiting affine equation as realization and quasiconformality.
tags:
  milestone
-/
theorem normalizedRiemannSphere_beltramiDifferential_compactness
    (K k : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n,
      IsKQuasiconformalBetweenRiemannSurfaces K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (μn : ℕ → BeltramiDifferential RiemannSphere)
    (hμnmeas : ∀ n, BeltramiDifferential.IsAEStronglyMeasurable (μn n))
    (hμnbound : ∀ n, BeltramiDifferential.HasEssentialNormLE (μn n) k)
    (hrealize : ∀ n,
      BeltramiDifferential.IsBeltramiDifferentialOf (μn n) (F n))
    (μ : BeltramiDifferential RiemannSphere)
    (hμmeas : BeltramiDifferential.IsAEStronglyMeasurable μ)
    (hμbound : BeltramiDifferential.HasEssentialNormLE μ k)
    (hμtendsto : BeltramiDifferential.AETendsto μn atTop μ)
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ∃ ξ : ℕ → ℕ, StrictMono ξ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        IsNormalizedRiemannSphereHomeomorph G ∧
        TendstoUniformly (fun n ↦ F (ξ n)) G atTop ∧
        TendstoUniformly (fun n ↦ (F (ξ n)).symm) G.symm atTop ∧
        IsKQuasiconformalBetweenRiemannSurfaces
            ((1 + k) / (1 - k)) G ∧
          BeltramiDifferential.IsBeltramiDifferentialOf μ G := by
  have hfiniteData (n : ℕ) :
      ∃ dFinite : ℂ → ℂ →L[ℝ] ℂ,
        IsLocalW12On Set.univ
            (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2)
            dFinite ∧
          WeakBeltramiEquationOn Set.univ
            (BeltramiDifferential.finiteCoefficient (μn n)) dFinite :=
    (hrealize n).exists_finite_weakDifferential (hnorm n)
  choose dFinite hFiniteLocal hFiniteBeltrami using hfiniteData
  have hqc' (n : ℕ) :
      IsKQuasiconformalRiemannSphere K (F n) :=
    (hqc n).toRiemannSphere
  have hμnmeas' (n : ℕ) :
      AEStronglyMeasurable
        (BeltramiDifferential.finiteCoefficient (μn n)) volume :=
    (BeltramiDifferential.isAEStronglyMeasurable_iff_finite (μn n)).mp
      (hμnmeas n)
  have hμnbound' :
      ∀ᵐ z ∂volume, ∀ n,
        ‖BeltramiDifferential.finiteCoefficient (μn n) z‖ ≤ k := by
    apply ae_all_iff.mpr
    intro n
    exact
      (BeltramiDifferential.hasEssentialNormLE_iff_finite (μn n) k).mp
        (hμnbound n)
  have hμmeas' :
      AEStronglyMeasurable
        (BeltramiDifferential.finiteCoefficient μ) volume :=
    (BeltramiDifferential.isAEStronglyMeasurable_iff_finite μ).mp hμmeas
  have hμbound' : HasEssentialNormLEOn Set.univ
      (BeltramiDifferential.finiteCoefficient μ) k := by
    simpa [HasEssentialNormLEOn] using
      (BeltramiDifferential.hasEssentialNormLE_iff_finite μ k).mp hμbound
  have hμtendsto' :
      ∀ᵐ z ∂volume,
        Tendsto
          (fun n ↦ BeltramiDifferential.finiteCoefficient (μn n) z)
          atTop
          (nhds (BeltramiDifferential.finiteCoefficient μ z)) :=
    (BeltramiDifferential.aeTendsto_iff_finite μn μ).mp hμtendsto
  obtain ⟨ξ, hξ, G, hGnorm, dG, hGconv, hGinvconv,
      hGqc, hGlocal, hGbel⟩ :=
    normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_spherical_compactness_of_isLocalW12On
      K k F hqc' hnorm dFinite hFiniteLocal
      (fun n ↦ BeltramiDifferential.finiteCoefficient (μn n))
      hμnmeas' hμnbound' hFiniteBeltrami
      (BeltramiDifferential.finiteCoefficient μ) hμmeas' hμbound'
      hμtendsto' hk0 hk1
  have hGrealize :
      BeltramiDifferential.IsBeltramiDifferentialOf μ G :=
    BeltramiDifferential.isBeltramiDifferentialOf_of_finite
      hGqc hGnorm hGlocal hGbel
  exact ⟨ξ, hξ, G, hGnorm, hGconv, hGinvconv,
    hGqc.toRiemannSurfaces, hGrealize⟩

end Quasiconformal

end

end JJMath
