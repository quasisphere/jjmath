import JJMath.Quasiconformal.RiemannSphere
import JJMath.Quasiconformal.ConformalChange

/-!
# Beltrami differentials in the standard coordinates of the Riemann sphere

Beltrami differentials themselves are defined intrinsically on arbitrary
complex one-manifolds. This file contains only the coordinate adapters needed
to use a spherical Beltrami differential in the finite and reciprocal
standard charts.
-/

namespace JJMath

open Filter MeasureTheory Set
open Quasiconformal
open scoped Manifold Topology

noncomputable section

/--
%%handwave
name:
  Affine chart as a member of the spherical complex atlas
statement:
  The standard affine coordinate on
  $\widehat{\mathbb C}\setminus\{\infty\}$ is a chart in the complex atlas
  of the Riemann sphere.
-/
noncomputable def riemannSphereFiniteAtlasChart :
    atlas ℂ RiemannSphere :=
  ⟨riemannSphereFiniteChart, by
    change riemannSphereFiniteChart ∈
      ({riemannSphereFiniteChart, riemannSphereInfinityChart} : Set _)
    simp⟩

/--
%%handwave
name:
  Reciprocal chart as a member of the spherical complex atlas
statement:
  The reciprocal coordinate on
  $\widehat{\mathbb C}\setminus\{0\}$ is a chart in the complex atlas of
  the Riemann sphere.
-/
noncomputable def riemannSphereInfinityAtlasChart :
    atlas ℂ RiemannSphere :=
  ⟨riemannSphereInfinityChart, by
    change riemannSphereInfinityChart ∈
      ({riemannSphereFiniteChart, riemannSphereInfinityChart} : Set _)
    simp⟩

/--
%%handwave
name:
  Atlas chart selected at a finite point of the Riemann sphere
statement:
  At every finite point $z\in\mathbb C\subset\widehat{\mathbb C}$, the
  distinguished complex chart is the affine chart.
proof:
  This is the finite-point clause in the charted-space structure of the
  Riemann sphere.
-/
theorem achart_riemannSphere_coe (z : ℂ) :
    achart ℂ (z : RiemannSphere) = riemannSphereFiniteAtlasChart := by
  apply Subtype.ext
  exact chartAt_riemannSphere_coe z

/--
%%handwave
name:
  Atlas chart selected at infinity on the Riemann sphere
statement:
  At $\infty\in\widehat{\mathbb C}$, the distinguished complex chart is the
  reciprocal chart.
proof:
  This is the infinity clause in the charted-space structure of the Riemann
  sphere.
-/
theorem achart_riemannSphere_infty :
    achart ℂ (OnePoint.infty : RiemannSphere) =
      riemannSphereInfinityAtlasChart := by
  apply Subtype.ext
  exact chartAt_riemannSphere_infty

namespace BeltramiDifferential

/--
%%handwave
name:
  Finite-coordinate coefficient of a spherical Beltrami differential
statement:
  The finite-coordinate coefficient of a Beltrami differential $\mu$ on
  $\widehat{\mathbb C}$ is the scalar field $\mu_{\mathrm{fin}}$ in the
  affine coordinate.
-/
noncomputable def finiteCoefficient
    (μ : BeltramiDifferential RiemannSphere) : ℂ → ℂ :=
  PQDifferential.inChart μ riemannSphereFiniteAtlasChart

/--
%%handwave
name:
  Reciprocal-coordinate coefficient of a spherical Beltrami differential
statement:
  The reciprocal-coordinate coefficient of a Beltrami differential $\mu$
  on $\widehat{\mathbb C}$ is the scalar field $\mu_\infty$ in the
  coordinate $w=1/z$.
-/
noncomputable def infinityCoefficient
    (μ : BeltramiDifferential RiemannSphere) : ℂ → ℂ :=
  PQDifferential.inChart μ riemannSphereInfinityAtlasChart

/--
%%handwave
name:
  Finite-coordinate data of a realized spherical Beltrami differential
statement:
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fix
  $0,1,\infty$ and realize a Beltrami differential $\mu$. Then its affine
  representative belongs to $W^{1,2}_{\mathrm{loc}}(\mathbb C)$ and has a
  weak differential satisfying
  $$
    \partial_{\bar z}F_{\mathrm{fin}}
      =\mu_{\mathrm{fin}}\,\partial_zF_{\mathrm{fin}}
  $$
  almost everywhere on $\mathbb C$.
proof:
  Evaluate the realization condition at the source point $0$. Normalization
  makes both selected charts affine and makes the maximal coordinate source
  all of $\mathbb C$.
-/
theorem IsBeltramiDifferentialOf.exists_finite_weakDifferential
    {μ : BeltramiDifferential RiemannSphere}
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hμ : IsBeltramiDifferentialOf μ F)
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    ∃ dFinite : ℂ → ℂ →L[ℝ] ℂ,
      IsLocalW12On Set.univ
          (riemannSphereFiniteChartHomeomorph F hF.2.2) dFinite ∧
        WeakBeltramiEquationOn Set.univ (finiteCoefficient μ) dFinite := by
  have hzero := hμ ((0 : ℂ) : RiemannSphere)
  rw [hF.1] at hzero
  obtain ⟨dFinite, hLocal, hBeltrami⟩ := hzero
  refine ⟨dFinite, ?_, ?_⟩
  · have hsource :
        riemannSurfaceChartMapSource F
            ((0 : ℂ) : RiemannSphere) ((0 : ℂ) : RiemannSphere) =
          Set.univ := by
      rw [← riemannSurfaceChartRepresentation_source]
      simp only [riemannSurfaceChartRepresentation,
        chartAt_riemannSphere_coe]
      exact
        riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
          F hF.2.2
    rw [hsource] at hLocal
    have hmap :
        riemannSurfaceChartMap F
            ((0 : ℂ) : RiemannSphere) ((0 : ℂ) : RiemannSphere) =
          riemannSphereFiniteChartHomeomorph F hF.2.2 := by
      funext z
      simp [riemannSurfaceChartMap]
    rw [hmap] at hLocal
    exact hLocal
  · have hsource :
        riemannSurfaceChartMapSource F
            ((0 : ℂ) : RiemannSphere) ((0 : ℂ) : RiemannSphere) =
          Set.univ := by
      rw [← riemannSurfaceChartRepresentation_source]
      simp only [riemannSurfaceChartRepresentation,
        chartAt_riemannSphere_coe]
      exact
        riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
          F hF.2.2
    rw [hsource, achart_riemannSphere_coe] at hBeltrami
    exact hBeltrami

/--
%%handwave
name:
  Derivative of the reciprocal-to-affine chart transition
statement:
  At $w\ne0$, the complex tangent transition from the reciprocal
  coordinate $w$ to the affine coordinate $z=1/w$ has scalar
  $$
    \frac{dz}{dw}=-w^{-2}.
  $$
proof:
  Unfold the tangent-bundle coordinate transition. Near a nonzero point the
  chart transition is complex inversion, whose complex derivative is
  $-w^{-2}$.
-/
theorem complexTangentTransitionScalar_infinity_finite
    (w : ℂ) (hw : w ≠ 0) :
    complexTangentTransitionScalar
        riemannSphereInfinityAtlasChart
        riemannSphereFiniteAtlasChart
        (riemannSphereInfinityChart.symm w) =
      -(w ^ 2)⁻¹ := by
  unfold complexTangentTransitionScalar
  rw [tangentBundleCore_coordChange]
  simp [riemannSphereFiniteAtlasChart,
    riemannSphereInfinityAtlasChart]
  have hfun :
      (riemannSphereFiniteChart ∘
          riemannSphereInfinityChart.symm : ℂ → ℂ) =ᶠ[𝓝 w]
        fun z ↦ z⁻¹ := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with z hz
    simp only [Function.comp_apply,
      riemannSphereInfinityChart_symm_apply]
    rw [riemannSphereInv_coe_of_ne_zero hz]
    simp
  rw [hfun.deriv_eq]
  exact (hasDerivAt_inv hw).deriv

/--
%%handwave
name:
  Reciprocal-coordinate law for a spherical Beltrami differential
statement:
  If $w\ne0$, the finite and reciprocal coefficients of a Beltrami
  differential on the sphere satisfy
  $$
    \mu_\infty(w)
      =\mu_{\mathrm{fin}}(w^{-1})
        \frac{\overline{-w^{-2}}}{-w^{-2}}.
  $$
proof:
  Apply the transition law for the $(-1,1)$-differential line to the
  reciprocal and affine charts, insert the derivative
  $-w^{-2}$, and solve for the reciprocal coefficient.
-/
theorem infinityCoefficient_eq_inversionPullback_of_ne_zero
    (μ : BeltramiDifferential RiemannSphere)
    {w : ℂ} (hw : w ≠ 0) :
    infinityCoefficient μ w =
      inversionPullbackBeltrami (finiteCoefficient μ) w := by
  let x : RiemannSphere := riemannSphereInfinityChart.symm w
  have hxInf :
      x ∈ (riemannSphereInfinityAtlasChart :
        OpenPartialHomeomorph RiemannSphere ℂ).source := by
    exact riemannSphereInfinityChart.map_target (by simp)
  have hxFin :
      x ∈ (riemannSphereFiniteAtlasChart :
        OpenPartialHomeomorph RiemannSphere ℂ).source := by
    dsimp [x]
    change riemannSphereInv (w : RiemannSphere) ∈
      riemannSphereFiniteChart.source
    rw [riemannSphereInv_coe_of_ne_zero hw]
    simp
  have htrans :=
    PQDifferential.inChartAt_transition μ
      riemannSphereInfinityAtlasChart
      riemannSphereFiniteAtlasChart hxInf hxFin
  have hfin :
      PQDifferential.inChartAt μ
          riemannSphereFiniteAtlasChart x =
        finiteCoefficient μ w⁻¹ := by
    simp [finiteCoefficient, x,
      riemannSphereInv_coe_of_ne_zero hw]
    unfold PQDifferential.inChart
    change
      PQDifferential.inChartAt μ riemannSphereFiniteAtlasChart
          (↑(w⁻¹) : RiemannSphere) =
        PQDifferential.inChartAt μ riemannSphereFiniteAtlasChart
          (riemannSphereFiniteChart.symm w⁻¹)
    rw [riemannSphereFiniteChart_symm_apply]
  have hinf :
      PQDifferential.inChartAt μ
          riemannSphereInfinityAtlasChart x =
        infinityCoefficient μ w := rfl
  rw [hfin, hinf] at htrans
  dsimp [x] at htrans
  have hxeq :
      riemannSphereInv (w : RiemannSphere) =
        riemannSphereInfinityChart.symm w := rfl
  rw [hxeq] at htrans
  simp only [pqDifferentialTransitionScalar] at htrans
  rw [complexTangentTransitionScalar_infinity_finite w hw] at htrans
  simp at htrans
  have hcw : starRingEnd ℂ w ≠ 0 := by simpa using hw
  field_simp [hw, hcw] at htrans
  have hpull :
      inversionPullbackBeltrami (finiteCoefficient μ) w =
        (finiteCoefficient μ w⁻¹ * w ^ 2) /
          (starRingEnd ℂ w) ^ 2 := by
    rw [inversionPullbackBeltrami, conformalPullbackBeltrami]
    simp only [map_neg, map_inv₀, map_pow]
    field_simp [hw, hcw]
  rw [hpull]
  exact
    (eq_div_iff (pow_ne_zero 2 hcw)).2
      (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using htrans)

/--
%%handwave
name:
  Almost-everywhere reciprocal-coordinate law
statement:
  The coordinate representatives of every spherical Beltrami differential
  satisfy
  $$
    \mu_\infty
      =\iota^\ast\mu_{\mathrm{fin}}
  $$
  almost everywhere, where $\iota(w)=w^{-1}$.
proof:
  The coordinate law holds at every $w\ne0$, and the exceptional singleton
  has planar measure zero.
-/
theorem infinityCoefficient_ae_eq_inversionPullback
    (μ : BeltramiDifferential RiemannSphere) :
    infinityCoefficient μ =ᵐ[volume]
      inversionPullbackBeltrami (finiteCoefficient μ) := by
  have hne : ∀ᵐ w : ℂ ∂volume, w ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ)) :
        ∀ᵐ w : ℂ ∂volume, w ∈ ({0} : Set ℂ)ᶜ)
  filter_upwards [hne] with w hw
  exact infinityCoefficient_eq_inversionPullback_of_ne_zero μ hw

/--
%%handwave
name:
  Spherical Beltrami differential induced by a finite coefficient
statement:
  A scalar field $\nu:\mathbb C\to\mathbb C$ determines a Beltrami
  differential on the Riemann sphere by using $\nu$ in the affine chart,
  transporting it through the intrinsic $(-1,1)$-differential line on the
  finite part, and taking value $0$ at infinity.
-/
noncomputable def ofFinite
    (ν : ℂ → ℂ) : BeltramiDifferential RiemannSphere :=
  PQDifferential.ofChart riemannSphereFiniteAtlasChart ν

/--
%%handwave
name:
  Finite coefficient of the induced spherical Beltrami differential
statement:
  The spherical Beltrami differential induced by
  $\nu:\mathbb C\to\mathbb C$ has finite-coordinate coefficient exactly
  $\nu$.
proof:
  Transporting a chart coefficient into the intrinsic line fiber and back
  through the same chart cancels.
-/
theorem finiteCoefficient_ofFinite
    (ν : ℂ → ℂ) :
    finiteCoefficient (ofFinite ν) = ν := by
  funext z
  exact
    PQDifferential.inChart_ofChart
      riemannSphereFiniteAtlasChart ν
      (by simp [riemannSphereFiniteAtlasChart])

/--
%%handwave
name:
  Almost-everywhere convergence of spherical Beltrami differentials from one chart
statement:
  A family of Beltrami differentials $\mu_\alpha$ on
  $\widehat{\mathbb C}$ converges almost everywhere to $\mu$ along a filter
  $\mathcal F$ in every complex chart if and only if
  $$
    (\mu_\alpha)_{\mathrm{fin}}(z)
      \longrightarrow\mu_{\mathrm{fin}}(z)
  $$
  along $\mathcal F$ for almost every $z\in\mathbb C$.
proof:
  The forward implication selects the affine chart. Conversely, affine
  convergence is preserved by inversion and multiplication by the fixed
  unit-modulus transition factor, giving convergence in the reciprocal
  chart away from its null exceptional point.
-/
theorem aeTendsto_iff_finite
    {ι : Type*} {l : Filter ι}
    (μs : ι → BeltramiDifferential RiemannSphere)
    (μ : BeltramiDifferential RiemannSphere) :
    AETendsto μs l μ ↔
      ∀ᵐ z ∂volume,
        Tendsto (fun a ↦ finiteCoefficient (μs a) z) l
          (nhds (finiteCoefficient μ z)) := by
  constructor
  · intro h
    have hfin := h riemannSphereFiniteAtlasChart
    simpa [AETendsto, finiteCoefficient,
      riemannSphereFiniteAtlasChart] using hfin
  · intro hfin i
    have hi :
        (i : OpenPartialHomeomorph RiemannSphere ℂ) =
            riemannSphereFiniteChart ∨
          (i : OpenPartialHomeomorph RiemannSphere ℂ) =
            riemannSphereInfinityChart := by
      simpa only [atlas, Set.mem_insert_iff, Set.mem_singleton_iff] using
        i.property
    rcases hi with hi | hi
    · have hieq : i = riemannSphereFiniteAtlasChart := by
        apply Subtype.ext
        exact hi
      subst i
      simpa [finiteCoefficient,
        riemannSphereFiniteAtlasChart] using hfin
    · have hieq : i = riemannSphereInfinityAtlasChart := by
        apply Subtype.ext
        exact hi
      subst i
      have hpull :
          ∀ᵐ z ∂volume,
            Tendsto
              (fun a ↦
                inversionPullbackBeltrami (finiteCoefficient (μs a)) z)
              l
              (nhds (inversionPullbackBeltrami (finiteCoefficient μ) z)) :=
        ae_tendsto_inversionPullbackBeltrami hfin
      have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          (compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ)) :
            ∀ᵐ z : ℂ ∂volume, z ∈ ({0} : Set ℂ)ᶜ)
      have hinf :
          ∀ᵐ z ∂volume,
            Tendsto (fun a ↦ infinityCoefficient (μs a) z) l
              (nhds (infinityCoefficient μ z)) := by
        filter_upwards [hpull, hne] with z hz hzne
        have hs :
            (fun a ↦ infinityCoefficient (μs a) z) =
              fun a ↦
                inversionPullbackBeltrami (finiteCoefficient (μs a)) z := by
          funext a
          exact infinityCoefficient_eq_inversionPullback_of_ne_zero
            (μs a) hzne
        have hlimit :
            infinityCoefficient μ z =
              inversionPullbackBeltrami (finiteCoefficient μ) z :=
          infinityCoefficient_eq_inversionPullback_of_ne_zero μ hzne
        rw [hs, hlimit]
        exact hz
      simpa [infinityCoefficient,
        riemannSphereInfinityAtlasChart] using hinf

/--
%%handwave
name:
  Measurability of a spherical Beltrami differential from one chart
statement:
  A Beltrami differential on the Riemann sphere is measurable in every
  complex chart if and only if its finite-coordinate coefficient is
  measurable up to a planar null set.
proof:
  The spherical atlas consists of the affine and reciprocal charts. The
  reciprocal coefficient agrees almost everywhere with the inversion
  pullback of the finite coefficient, which is measurable whenever the
  finite coefficient is measurable.
-/
theorem isAEStronglyMeasurable_iff_finite
    (μ : BeltramiDifferential RiemannSphere) :
    IsAEStronglyMeasurable μ ↔
      AEStronglyMeasurable (finiteCoefficient μ) volume := by
  constructor
  · intro h
    have hfin := h riemannSphereFiniteAtlasChart
    simpa [BeltramiDifferential.IsAEStronglyMeasurable,
      PQDifferential.IsAEStronglyMeasurable,
      finiteCoefficient, riemannSphereFiniteAtlasChart] using hfin
  · intro hfin i
    have hi :
        (i : OpenPartialHomeomorph RiemannSphere ℂ) =
            riemannSphereFiniteChart ∨
          (i : OpenPartialHomeomorph RiemannSphere ℂ) =
            riemannSphereInfinityChart := by
      simpa only [atlas, Set.mem_insert_iff, Set.mem_singleton_iff] using
        i.property
    rcases hi with hi | hi
    · have hieq : i = riemannSphereFiniteAtlasChart := by
        apply Subtype.ext
        exact hi
      subst i
      simpa [finiteCoefficient, riemannSphereFiniteAtlasChart] using hfin
    · have hieq : i = riemannSphereInfinityAtlasChart := by
        apply Subtype.ext
        exact hi
      subst i
      have hpull :=
        AEStronglyMeasurable.inversionPullbackBeltrami hfin
      have hinf :
          AEStronglyMeasurable (infinityCoefficient μ) volume :=
        hpull.congr (infinityCoefficient_ae_eq_inversionPullback μ).symm
      simpa [infinityCoefficient,
        riemannSphereInfinityAtlasChart] using hinf

/--
%%handwave
name:
  Essential bound of a spherical Beltrami differential from one chart
statement:
  A Beltrami differential on the Riemann sphere satisfies
  $|\mu|\le k$ almost everywhere in every complex chart if and only if
  $$
    |\mu_{\mathrm{fin}}|\le k
  $$
  almost everywhere in the affine chart.
proof:
  The reciprocal coefficient is the inversion pullback of the finite
  coefficient almost everywhere, and the $(-1,1)$-transition factor has
  norm $1$.
-/
theorem hasEssentialNormLE_iff_finite
    (μ : BeltramiDifferential RiemannSphere) (k : ℝ) :
    HasEssentialNormLE μ k ↔
      ∀ᵐ z ∂volume, ‖finiteCoefficient μ z‖ ≤ k := by
  constructor
  · intro h
    have hfin := h riemannSphereFiniteAtlasChart
    simpa [HasEssentialNormLE, finiteCoefficient,
      riemannSphereFiniteAtlasChart] using hfin
  · intro hfin i
    have hi :
        (i : OpenPartialHomeomorph RiemannSphere ℂ) =
            riemannSphereFiniteChart ∨
          (i : OpenPartialHomeomorph RiemannSphere ℂ) =
            riemannSphereInfinityChart := by
      simpa only [atlas, Set.mem_insert_iff, Set.mem_singleton_iff] using
        i.property
    rcases hi with hi | hi
    · have hieq : i = riemannSphereFiniteAtlasChart := by
        apply Subtype.ext
        exact hi
      subst i
      simpa [finiteCoefficient, riemannSphereFiniteAtlasChart] using hfin
    · have hieq : i = riemannSphereInfinityAtlasChart := by
        apply Subtype.ext
        exact hi
      subst i
      have hpull :
          ∀ᵐ z ∂volume,
            ‖inversionPullbackBeltrami (finiteCoefficient μ) z‖ ≤ k :=
        ae_norm_inversionPullbackBeltrami_le hfin
      have hinf :
          ∀ᵐ z ∂volume, ‖infinityCoefficient μ z‖ ≤ k := by
        filter_upwards
          [hpull, infinityCoefficient_ae_eq_inversionPullback μ]
          with z hz heq
        simpa [heq] using hz
      simpa [infinityCoefficient,
        riemannSphereInfinityAtlasChart] using hinf

end BeltramiDifferential

end

end JJMath
