import JJMath.Quasiconformal.PrincipalNormalization
import JJMath.Quasiconformal.SphericalBeltramiCompactness

/-!
# The measurable Riemann mapping theorem

This file truncates a bounded measurable Beltrami coefficient, applies the
compact-support principal construction, and passes to a normalized spherical
limit.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

open Quasiconformal

namespace Quasiconformal

set_option maxHeartbeats 6000000 in
/--
%%handwave
name:
  Measurable Riemann mapping theorem on the sphere
statement:
  Let $\mu$ be a measurable Beltrami differential on
  $\widehat{\mathbb C}$ whose essential norm is at most $k<1$, where
  $k\ge0$. Then there is an orientation-preserving homeomorphism
  $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ which is
  $\frac{1+k}{1-k}$-quasiconformal, fixes $0$, $1$, and $\infty$, and
  realizes $\mu$ on the whole sphere.
  Equivalently, its weak finite and reciprocal coordinate
  representatives satisfy the Beltrami equations with coefficients
  $\mu_{\mathrm{fin}}$ and $\mu_\infty$, respectively.
proof:
  Truncate $\mu_{\mathrm{fin}}$ to the disks $B(0,n)$. For each truncation, use the
  normalized compact-support principal construction and extend the resulting
  plane map over infinity. These sphere maps have a common distortion
  constant and fix $0$, $1$, and $\infty$. Promote the truncations to
  spherical Beltrami differentials. Their affine convergence is equivalent
  to chartwise almost-everywhere convergence, so
  [spherical compactness gives a normalized quasiconformal limit realizing $\mu$](lean:JJMath.Quasiconformal.normalizedRiemannSphere_beltramiDifferential_compactness).
tags:
  milestone
-/
theorem exists_normalized_riemannSphere_homeomorph_of_beltrami
    (μ : BeltramiDifferential RiemannSphere)
    (hμmeas : BeltramiDifferential.IsAEStronglyMeasurable μ)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbound : BeltramiDifferential.HasEssentialNormLE μ k) :
    ∃ F : RiemannSphere ≃ₜ RiemannSphere,
      ∃ _hFnorm : IsNormalizedRiemannSphereHomeomorph F,
        IsKQuasiconformalBetweenRiemannSurfaces
            ((1 + k) / (1 - k)) F ∧
          BeltramiDifferential.IsBeltramiDifferentialOf μ F := by
  let μfinite := BeltramiDifferential.finiteCoefficient μ
  have hμfiniteMeas :
      AEStronglyMeasurable μfinite (volume : Measure ℂ) :=
    (BeltramiDifferential.isAEStronglyMeasurable_iff_finite μ).mp hμmeas
  have hμfiniteBound :
      ∀ᵐ z ∂(volume : Measure ℂ), ‖μfinite z‖ ≤ k :=
    (BeltramiDifferential.hasEssentialNormLE_iff_finite μ k).mp hbound
  let μn : ℕ → ℂ → ℂ := fun n ↦
    (Metric.ball (0 : ℂ) (n : ℝ)).indicator μfinite
  have hμnmeas : ∀ n, AEStronglyMeasurable (μn n) volume := by
    intro n
    exact hμfiniteMeas.indicator measurableSet_ball
  have hμnbound :
      ∀ᵐ z ∂(volume : Measure ℂ), ∀ n, ‖μn n z‖ ≤ k := by
    filter_upwards [hμfiniteBound] with z hz
    intro n
    by_cases hzn : z ∈ Metric.ball (0 : ℂ) (n : ℝ)
    · simpa [μn, Set.indicator_of_mem hzn] using hz
    · simp [μn, Set.indicator_of_notMem hzn, hk0]
  have hμnzero (n : ℕ) :
      ∀ᵐ z ∂(volume : Measure ℂ),
        (n : ℝ) ≤ ‖z‖ → μn n z = 0 := by
    filter_upwards with z
    intro hz
    change (Metric.ball (0 : ℂ) (n : ℝ)).indicator μfinite z = 0
    rw [Set.indicator_of_notMem]
    simpa [Metric.mem_ball, dist_zero_right] using not_lt_of_ge hz
  have hsolution (n : ℕ) :
      ∃ F : ℂ ≃ₜ ℂ, ∃ dF : ℂ → ℂ →L[ℝ] ℂ,
        IsNormalizedRiemannSphereHomeomorph
            (planeHomeomorphExtension F) ∧
          IsKQuasiconformalRiemannSphere ((1 + k) / (1 - k))
            (planeHomeomorphExtension F) ∧
          IsLocalW12On Set.univ F dF ∧
          PreservesPlanarOrientation (wholePlaneSubtypeHomeomorph F) ∧
          WeakBeltramiEquationOn Set.univ (μn n) dF ∧
          ∀ᵐ z ∂(volume : Measure ℂ),
            ‖dF z‖ ^ 2 ≤
              ((1 + k) / (1 - k)) * weakJacobian (dF z) := by
    apply exists_normalizedPrincipalHomeomorphismExtension_of_compactSupport
      (μn n) (hμnmeas n) hk0 hk1
    · exact hμnbound.mono fun z hz ↦ hz n
    · exact hμnzero n
  choose Fn dFn hFnorm hFnqc hFnlocal _hFnorient hFnbel _hFndist
    using hsolution
  have hfiniteLocal (n : ℕ) :
      IsLocalW12On Set.univ
        (riemannSphereFiniteChartHomeomorph
          (planeHomeomorphExtension (Fn n)) (hFnorm n).2.2)
        (dFn n) := by
    rw [riemannSphereFiniteChartHomeomorph_planeHomeomorphExtension]
    exact hFnlocal n
  have hμntendsto :
      ∀ᵐ z ∂(volume : Measure ℂ),
        Tendsto (fun n ↦ μn n z) atTop (nhds (μfinite z)) := by
    filter_upwards with z
    have hlarge :
        ∀ᶠ n : ℕ in atTop, ‖z‖ < (n : ℝ) :=
      (tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖z‖)
    have heq :
        (fun n ↦ μn n z) =ᶠ[atTop] fun _n : ℕ ↦ μfinite z := by
      filter_upwards [hlarge] with n hn
      change (Metric.ball (0 : ℂ) (n : ℝ)).indicator μfinite z = μfinite z
      rw [Set.indicator_of_mem]
      simpa [Metric.mem_ball, dist_zero_right]
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  let μsphere : ℕ → BeltramiDifferential RiemannSphere := fun n ↦
    BeltramiDifferential.ofFinite (μn n)
  have hμsphereMeas (n : ℕ) :
      BeltramiDifferential.IsAEStronglyMeasurable (μsphere n) := by
    apply
      (BeltramiDifferential.isAEStronglyMeasurable_iff_finite
        (μsphere n)).mpr
    simpa [μsphere, BeltramiDifferential.finiteCoefficient_ofFinite] using
      hμnmeas n
  have hμsphereBound (n : ℕ) :
      BeltramiDifferential.HasEssentialNormLE (μsphere n) k := by
    apply
      (BeltramiDifferential.hasEssentialNormLE_iff_finite
        (μsphere n) k).mpr
    simpa [μsphere, BeltramiDifferential.finiteCoefficient_ofFinite] using
      hμnbound.mono fun z hz ↦ hz n
  have hμsphereRealized (n : ℕ) :
      BeltramiDifferential.IsBeltramiDifferentialOf (μsphere n)
        (planeHomeomorphExtension (Fn n)) := by
    apply BeltramiDifferential.isBeltramiDifferentialOf_of_finite
      (hFnqc n) (hFnorm n) (hfiniteLocal n)
    simpa [μsphere, BeltramiDifferential.finiteCoefficient_ofFinite] using
      hFnbel n
  have hμsphereTendsto :
      BeltramiDifferential.AETendsto μsphere atTop μ := by
    apply
      (BeltramiDifferential.aeTendsto_iff_finite μsphere μ).mpr
    simpa [μsphere, μfinite,
      BeltramiDifferential.finiteCoefficient_ofFinite] using hμntendsto
  obtain ⟨_ξ, _hξ, G, hGnorm, _hGconv, _hGinvconv,
      hGqc, hGcoefficient⟩ :=
    normalizedRiemannSphere_beltramiDifferential_compactness
      ((1 + k) / (1 - k)) k
      (fun n ↦ planeHomeomorphExtension (Fn n))
      (fun n ↦ (hFnqc n).toRiemannSurfaces) hFnorm
      μsphere hμsphereMeas hμsphereBound hμsphereRealized
      μ hμmeas hbound hμsphereTendsto hk0 hk1
  exact ⟨G, hGnorm, hGqc, hGcoefficient⟩

/--
%%handwave
name:
  Whole-plane form of the measurable Riemann mapping theorem
statement:
  Let $\mu:\mathbb C\to\mathbb C$ be measurable and satisfy
  $|\mu|\leq k<1$ almost everywhere, where $k\geq0$. Then there are a
  homeomorphism $\Phi:\mathbb C\to\mathbb C$ fixing $0$ and $1$ and a weak
  differential $D\Phi$ such that $\Phi$ is
  $\frac{1+k}{1-k}$-quasiconformal,
  $$
    \partial_{\bar z}\Phi=\mu\,\partial_z\Phi
  $$
  almost everywhere, and
  $$
    \operatorname{Jac}\Phi(z)>0
  $$
  for almost every $z\in\mathbb C$.
proof:
  Extend $\mu$ to the spherical differential whose reciprocal representative is its inversion pullback, apply [the normalized spherical measurable Riemann mapping theorem](lean:JJMath.Quasiconformal.exists_normalized_riemannSphere_homeomorph_of_beltrami), and pass to the whole-plane finite chart. [The finite-chart bridge preserves the quasiconformal constant](lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.finiteChartSetHomeomorph), and [the weak Jacobian of a planar quasiconformal homeomorphism is positive almost everywhere](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.weakJacobian_pos_ae).
-/
theorem exists_normalized_plane_homeomorph_of_beltrami
    (μ : ℂ → ℂ)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ Φ : ℂ ≃ₜ ℂ, ∃ dΦ : ℂ → ℂ →L[ℝ] ℂ,
      Φ 0 = 0 ∧
        Φ 1 = 1 ∧
        IsKQuasiconformalBetween ((1 + k) / (1 - k))
          (wholePlaneSubtypeHomeomorph Φ) ∧
        IsLocalW12On Set.univ Φ dΦ ∧
        WeakBeltramiEquationOn Set.univ μ dΦ ∧
        ∀ᵐ z ∂(volume : Measure ℂ), 0 < weakJacobian (dΦ z) := by
  let μSphere := BeltramiDifferential.ofFinite μ
  have hμSphereMeas :
      BeltramiDifferential.IsAEStronglyMeasurable μSphere := by
    rw [BeltramiDifferential.isAEStronglyMeasurable_iff_finite]
    change AEStronglyMeasurable
      (BeltramiDifferential.finiteCoefficient
        (BeltramiDifferential.ofFinite μ)) volume
    rw [BeltramiDifferential.finiteCoefficient_ofFinite]
    exact hμmeas
  have hμSphereBound :
      BeltramiDifferential.HasEssentialNormLE μSphere k := by
    rw [BeltramiDifferential.hasEssentialNormLE_iff_finite]
    change ∀ᵐ z ∂volume,
      ‖BeltramiDifferential.finiteCoefficient
          (BeltramiDifferential.ofFinite μ) z‖ ≤ k
    rw [BeltramiDifferential.finiteCoefficient_ofFinite]
    exact hbound
  obtain ⟨F, hFnorm, hFqc, hFcoefficient⟩ :=
    exists_normalized_riemannSphere_homeomorph_of_beltrami
      μSphere hμSphereMeas hk0 hk1 hμSphereBound
  obtain ⟨dΦ, hΦWChart, hΦbelChart⟩ :=
    hFcoefficient (((0 : ℂ) : RiemannSphere))
  let Φ : ℂ ≃ₜ ℂ :=
    riemannSphereFiniteChartHomeomorph F hFnorm.2.2
  have hsource :
      riemannSurfaceChartMapSource F (((0 : ℂ) : RiemannSphere))
          (F (((0 : ℂ) : RiemannSphere))) = Set.univ := by
    rw [hFnorm.1]
    rw [← riemannSurfaceChartRepresentation_source]
    simp only [riemannSurfaceChartRepresentation,
      chartAt_riemannSphere_coe]
    exact
      riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
        F hFnorm.2.2
  have hchartMap :
      riemannSurfaceChartMap F (((0 : ℂ) : RiemannSphere))
          (F (((0 : ℂ) : RiemannSphere))) =
        riemannSphereFiniteChartHomeomorph F hFnorm.2.2 := by
    funext z
    simp [riemannSurfaceChartMap, hFnorm.1]
  have hΦW : IsLocalW12On Set.univ Φ dΦ := by
    rw [hsource, hchartMap] at hΦWChart
    exact hΦWChart
  have hΦbel : WeakBeltramiEquationOn Set.univ μ dΦ := by
    rw [hsource, achart_riemannSphere_coe] at hΦbelChart
    change WeakBeltramiEquationOn Set.univ
      (BeltramiDifferential.finiteCoefficient
        (BeltramiDifferential.ofFinite μ)) dΦ at hΦbelChart
    rw [BeltramiDifferential.finiteCoefficient_ofFinite] at hΦbelChart
    exact hΦbelChart
  have hFqcSphere :
      IsKQuasiconformalRiemannSphere ((1 + k) / (1 - k)) F :=
    hFqc.toRiemannSphere
  have hset :
      wholePlaneSubtypeHomeomorph Φ =
        riemannSphereFiniteChartSetHomeomorph F hFnorm.2.2 := by
    ext z
    rfl
  have hΦqc : IsKQuasiconformalBetween ((1 + k) / (1 - k))
      (wholePlaneSubtypeHomeomorph Φ) := by
    rw [hset]
    exact hFqcSphere.finiteChartSetHomeomorph hFnorm
  have hΦambient : IsLocalW12On Set.univ
      (ambientMap (wholePlaneSubtypeHomeomorph Φ)) dΦ := by
    apply hΦW.congr_ae
    filter_upwards with z
    rw [ambientMap_apply _ ⟨z, Set.mem_univ z⟩]
    rfl
  have hJpos :
      ∀ᵐ z ∂(volume : Measure ℂ), 0 < weakJacobian (dΦ z) := by
    simpa only [Measure.restrict_univ] using hΦqc.weakJacobian_pos_ae hΦambient
  exact ⟨Φ, dΦ, hFnorm.finiteChart_fixes_zero_one.1,
    hFnorm.finiteChart_fixes_zero_one.2, hΦqc, hΦW, hΦbel, hJpos⟩

end Quasiconformal

end

end JJMath
