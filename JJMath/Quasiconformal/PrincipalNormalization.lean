import JJMath.Quasiconformal.PrincipalHomeomorphism
import JJMath.Quasiconformal.ConformalChange
import JJMath.Quasiconformal.Examples
import JJMath.Quasiconformal.PointRemovability
import JJMath.Quasiconformal.RiemannSphere
import JJMath.Quasiconformal.Compactness

/-!
# Normalization of principal Beltrami homeomorphisms

This file extends plane homeomorphisms over infinity and postcomposes
principal solutions by the unique complex-affine map fixing the images of
`0` and `1`.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  One-point extension of a plane homeomorphism
statement:
  Every homeomorphism $F:\mathbb C\to\mathbb C$ extends canonically to a
  homeomorphism $\widehat F:\widehat{\mathbb C}\to\widehat{\mathbb C}$
  which agrees with $F$ at finite points and fixes $\infty$.
-/
def planeHomeomorphExtension (F : ℂ ≃ₜ ℂ) :
    RiemannSphere ≃ₜ RiemannSphere :=
  Homeomorph.onePointCongr F

/--
%%handwave
name:
  Finite value of the one-point extension
statement:
  For $z\in\mathbb C$, the canonical extension satisfies
  $\widehat F(z)=F(z)$.
proof:
  The one-point extension acts by the original homeomorphism on finite
  points.
-/
@[simp]
theorem planeHomeomorphExtension_coe (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    planeHomeomorphExtension F (z : RiemannSphere) =
      ((F z : ℂ) : RiemannSphere) :=
  rfl

/--
%%handwave
name:
  Infinite value of the one-point extension
statement:
  The canonical extension of every plane homeomorphism fixes $\infty$.
proof:
  The added point is fixed by the one-point extension.
-/
@[simp]
theorem planeHomeomorphExtension_infty (F : ℂ ≃ₜ ℂ) :
    planeHomeomorphExtension F OnePoint.infty = OnePoint.infty :=
  rfl

/--
%%handwave
name:
  Affine normalization scale
statement:
  For a plane homeomorphism $F$, its normalization scale is
  $$
    a_F=(F(1)-F(0))^{-1}.
  $$
-/
def planeNormalizationScale (F : ℂ ≃ₜ ℂ) : ℂ :=
  (F 1 - F 0)⁻¹

/--
%%handwave
name:
  The affine normalization scale is nonzero
statement:
  For every plane homeomorphism $F$, one has
  $(F(1)-F(0))^{-1}\ne0$.
proof:
  Injectivity gives $F(1)\ne F(0)$ because $1\ne0$.
-/
theorem planeNormalizationScale_ne_zero (F : ℂ ≃ₜ ℂ) :
    planeNormalizationScale F ≠ 0 := by
  exact inv_ne_zero (sub_ne_zero.mpr (F.injective.ne one_ne_zero))

/--
%%handwave
name:
  Affinely normalized plane homeomorphism
statement:
  The affine normalization of $F:\mathbb C\to\mathbb C$ is
  $$
    N_F(z)=\frac{F(z)-F(0)}{F(1)-F(0)}.
  $$
  It is again a plane homeomorphism.
-/
def normalizedPlaneHomeomorph (F : ℂ ≃ₜ ℂ) : ℂ ≃ₜ ℂ :=
  F.trans
    ((Homeomorph.mulLeft₀ (planeNormalizationScale F)
      (planeNormalizationScale_ne_zero F)).trans
        (Homeomorph.addRight
          (-(planeNormalizationScale F * F 0))))

/--
%%handwave
name:
  Formula for affine normalization
statement:
  For every $z\in\mathbb C$,
  $$
    N_F(z)=(F(1)-F(0))^{-1}F(z)
      -(F(1)-F(0))^{-1}F(0).
  $$
proof:
  Expand the postcomposition by complex multiplication and translation.
-/
@[simp]
theorem normalizedPlaneHomeomorph_apply (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    normalizedPlaneHomeomorph F z =
      planeNormalizationScale F * F z -
        planeNormalizationScale F * F 0 :=
  rfl

/--
%%handwave
name:
  Affine normalization fixes zero
statement:
  The normalized homeomorphism satisfies $N_F(0)=0$.
proof:
  The two terms in the normalization formula cancel.
-/
@[simp]
theorem normalizedPlaneHomeomorph_zero (F : ℂ ≃ₜ ℂ) :
    normalizedPlaneHomeomorph F 0 = 0 := by
  simp

/--
%%handwave
name:
  Affine normalization fixes one
statement:
  The normalized homeomorphism satisfies $N_F(1)=1$.
proof:
  The difference $F(1)-F(0)$ cancels its nonzero inverse.
-/
@[simp]
theorem normalizedPlaneHomeomorph_one (F : ℂ ≃ₜ ℂ) :
    normalizedPlaneHomeomorph F 1 = 1 := by
  rw [normalizedPlaneHomeomorph_apply]
  change (F 1 - F 0)⁻¹ * F 1 - (F 1 - F 0)⁻¹ * F 0 = 1
  rw [← mul_sub]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (F.injective.ne one_ne_zero))

/--
%%handwave
name:
  Normalized one-point extension
statement:
  The one-point extension of $N_F$ fixes $0$, $1$, and $\infty$.
proof:
  The affine normalization fixes $0$ and $1$, while every one-point extension
  fixes the added point $\infty$.
-/
theorem normalized_planeHomeomorphExtension
    (F : ℂ ≃ₜ ℂ) :
    IsNormalizedRiemannSphereHomeomorph
      (planeHomeomorphExtension (normalizedPlaneHomeomorph F)) := by
  refine ⟨?_, ?_, rfl⟩
  · simpa using congrArg (fun z : ℂ ↦ (z : RiemannSphere))
      (normalizedPlaneHomeomorph_zero F)
  · simpa using congrArg (fun z : ℂ ↦ (z : RiemannSphere))
      (normalizedPlaneHomeomorph_one F)

/--
%%handwave
name:
  Finite chart of a one-point extension
statement:
  The finite-chart plane homeomorphism induced by $\widehat F$ is exactly
  the original homeomorphism $F:\mathbb C\to\mathbb C$.
proof:
  At every finite point, the one-point extension applies $F$, after which
  the finite chart removes the inclusion into the sphere.
-/
theorem riemannSphereFiniteChartHomeomorph_planeHomeomorphExtension
    (F : ℂ ≃ₜ ℂ) :
    riemannSphereFiniteChartHomeomorph (planeHomeomorphExtension F)
      (planeHomeomorphExtension_infty F) = F := by
  ext z
  simp [riemannSphereFiniteChartHomeomorph_apply]

/--
%%handwave
name:
  Whole-plane restriction of affine normalization
statement:
  As a homeomorphism between two copies of the universal planar domain,
  $N_F$ is the composite of $F$ with the complex-affine map
  $w\mapsto a_Fw-a_FF(0)$.
proof:
  Both sides have the same value at every point of the universal domain.
-/
theorem wholePlaneSubtypeHomeomorph_normalizedPlaneHomeomorph
    (F : ℂ ≃ₜ ℂ) :
    wholePlaneSubtypeHomeomorph (normalizedPlaneHomeomorph F) =
      (wholePlaneSubtypeHomeomorph F).trans
      (complexAffineHomeomorph (planeNormalizationScale F)
          (-(planeNormalizationScale F * F 0))
          (planeNormalizationScale_ne_zero F)) := by
  ext z
  simp [normalizedPlaneHomeomorph_apply]
  ring

/--
%%handwave
name:
  Affine normalization preserves planar orientation
statement:
  If a plane homeomorphism $F$ preserves orientation, then its normalization
  $N_F(z)=(F(z)-F(0))/(F(1)-F(0))$ also preserves orientation.
proof:
  The target normalization is a nonconstant complex-affine map and therefore
  preserves orientation. Compose it with the orientation-preserving map $F$.
-/
theorem preservesPlanarOrientation_normalizedPlaneHomeomorph
    (F : ℂ ≃ₜ ℂ)
    (hF : PreservesPlanarOrientation (wholePlaneSubtypeHomeomorph F)) :
    PreservesPlanarOrientation
      (wholePlaneSubtypeHomeomorph (normalizedPlaneHomeomorph F)) := by
  rw [wholePlaneSubtypeHomeomorph_normalizedPlaneHomeomorph]
  exact hF.trans
    (preservesPlanarOrientation_complexAffine
      (planeNormalizationScale F)
      (-(planeNormalizationScale F * F 0))
      (planeNormalizationScale_ne_zero F))

/--
%%handwave
name:
  Affine asymptotics give a quotient limit at infinity
statement:
  If $F(z)-az\to c$ as $z\to\infty$, then
  $$
    \frac{F(z)}z\longrightarrow a
    \qquad (z\to\infty).
  $$
proof:
  Write $F(z)/z=a+(F(z)-az)z^{-1}$. The second factor tends to zero because
  $z^{-1}\to0$ at infinity.
-/
theorem tendsto_div_cocompact_of_tendsto_sub_complexLinear
    (F : ℂ → ℂ) {a c : ℂ}
    (hF : Tendsto (fun z ↦ F z - a * z) (cocompact ℂ) (𝓝 c)) :
    Tendsto (fun z ↦ F z / z) (cocompact ℂ) (𝓝 a) := by
  have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa [Metric.cobounded_eq_cocompact] using
      (Filter.tendsto_inv₀_cobounded (α := ℂ))
  have herror : Tendsto (fun z ↦ (F z - a * z) * z⁻¹)
      (cocompact ℂ) (𝓝 0) := by
    simpa using hF.mul hinv
  have hne : ({0} : Set ℂ)ᶜ ∈ cocompact ℂ :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have heq : (fun z ↦ a + (F z - a * z) * z⁻¹) =ᶠ[cocompact ℂ]
      fun z ↦ F z / z := by
    filter_upwards [hne] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    field_simp [hz0]
    ring
  simpa using (tendsto_const_nhds.add herror).congr' heq

/--
%%handwave
name:
  Reciprocal conjugation turns affine behavior at infinity into a tangent
statement:
  Suppose $a\ne0$ and $F(z)/z\to a$ as $z\to\infty$. Then
  $$
    \frac{1/F(1/z)}z\longrightarrow a^{-1}
    \qquad (z\to0,\ z\ne0).
  $$
proof:
  Inversion sends the punctured-neighborhood filter at zero to the
  cocompact filter. For $z\ne0$, the displayed quotient is the reciprocal of
  $F(1/z)/(1/z)$.
-/
theorem tendsto_reciprocalConjugate_div_nhdsNE_zero
    (F : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0)
    (hF : Tendsto (fun z ↦ F z / z) (cocompact ℂ) (𝓝 a)) :
    Tendsto (fun z : ℂ ↦ (F z⁻¹)⁻¹ / z)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (𝓝 a⁻¹) := by
  have hinv : Tendsto (fun z : ℂ ↦ z⁻¹)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (cocompact ℂ) := by
    simpa [Metric.cobounded_eq_cocompact] using
      (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ))
  have hcomp := hF.comp hinv
  have hquot := hcomp.inv₀ ha
  have hne : ∀ᶠ z : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ),
      F z⁻¹ / z⁻¹ ≠ 0 := by
    exact hcomp.eventually
      (isOpen_compl_singleton.mem_nhds ha)
  apply hquot.congr'
  filter_upwards [eventually_mem_nhdsWithin, hne] with z hz hq
  have hz0 : z ≠ 0 := by simpa using hz
  have hFz0 : F z⁻¹ ≠ 0 := by
    intro hzero
    apply hq
    rw [hzero]
    simp
  change (F z⁻¹ / z⁻¹)⁻¹ = (F z⁻¹)⁻¹ / z
  field_simp [hz0, hFz0]

/--
%%handwave
name:
  Spherical quasiconformality of a one-point extension
statement:
  Let $F:\mathbb C\to\mathbb C$ be a $K$-quasiconformal homeomorphism whose
  canonical sphere extension fixes $0$, $1$, and $\infty$. Suppose
  $F(z)-az\to c$ as $z\to\infty$ for some $a\ne0$. Then the canonical
  extension is $K$-quasiconformal on the Riemann sphere in every pair of
  standard charts.
proof:
  The finite chart is $F$. On punctured reciprocal charts, precomposition and
  postcomposition by $z\mapsto z^{-1}$ preserve the distortion bound. Near
  the omitted point, the distortion inequality and the area formula give
  finite Dirichlet energy; shrinking smooth cutoffs remove the point from the
  weak derivative identity. The affine asymptotic gives a nonzero complex
  tangent at the filled point and hence preserves orientation there. The
  mixed chart assertions then follow by conformal restriction.
-/
theorem isKQuasiconformalRiemannSphere_planeHomeomorphExtension
    {K : ℝ} (F : ℂ ≃ₜ ℂ)
    (hFnorm : IsNormalizedRiemannSphereHomeomorph
      (planeHomeomorphExtension F))
    {a c : ℂ} (ha : a ≠ 0)
    (hFasymptotic : Tendsto (fun z ↦ F z - a * z)
      (cocompact ℂ) (𝓝 c))
    (hF : IsKQuasiconformalBetween K
      (wholePlaneSubtypeHomeomorph F)) :
    IsKQuasiconformalRiemannSphere K (planeHomeomorphExtension F) := by
  let S := planeHomeomorphExtension F
  have hfinite : IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph S .finite .finite) := by
    apply hF.restrict
      (riemannSphereChartRepresentation S .finite .finite).open_source
      (riemannSphereChartRepresentation S .finite .finite).open_target
      (Set.subset_univ _)
    intro z
    calc
      (riemannSphereChartHomeomorph S .finite .finite z : ℂ) =
          ambientMap (riemannSphereChartHomeomorph S .finite .finite) z :=
        (ambientMap_apply _ z).symm
      _ = riemannSphereFiniteChartHomeomorph S hFnorm.2.2 z :=
        ambientMap_finiteChartHomeomorph_apply S hFnorm.2.2 z
      _ = F z := by
        simpa only [S] using congrArg
          (fun G : ℂ ≃ₜ ℂ ↦ G (z : ℂ))
          (riemannSphereFiniteChartHomeomorph_planeHomeomorphExtension F)
      _ = wholePlaneSubtypeHomeomorph F
          ⟨(z : ℂ), Set.mem_univ _⟩ := by
        simp only [wholePlaneSubtypeHomeomorph_apply]
  let F0 := normalizedFiniteChartPuncturedHomeomorph S hFnorm
  have hF0 : IsKQuasiconformalBetween K F0 :=
    isKQuasiconformalBetween_normalizedFiniteChartPunctured_of_finiteChart
      hFnorm hfinite
  let P := (puncturedPlaneInversionHomeomorph.trans F0).trans
    puncturedPlaneInversionHomeomorph
  have hP : IsKQuasiconformalBetween K P :=
    hF0.precomp_puncturedPlaneInversion.postcomp_puncturedPlaneInversion
  let T := riemannSphereInvConjugate S
  have hTnorm : IsNormalizedRiemannSphereHomeomorph T :=
    hFnorm.invConjugate
  let H : ℂ ≃ₜ ℂ :=
    riemannSphereFiniteChartHomeomorph T hTnorm.2.2
  have hH0 : H 0 = 0 := hTnorm.finiteChart_fixes_zero_one.1
  have hagree : ∀ z : ℂ, ambientMap P z = H z := by
    intro z
    by_cases hz : z = 0
    · subst z
      simpa [ambientMap] using hH0.symm
    · let zp : ({0}ᶜ : Set ℂ) := ⟨z, hz⟩
      rw [show ambientMap P z = (P zp : ℂ) by
        exact ambientMap_apply P zp]
      change (riemannSphereFiniteChartHomeomorph S hFnorm.2.2 z⁻¹)⁻¹ = H z
      rw [show H z = riemannSphereInfinityChartHomeomorph S hFnorm.1 z by
        exact riemannSphereFiniteChartHomeomorph_invConjugate_apply hFnorm z]
      exact (riemannSphereInfinityChartHomeomorph_eq_inv_finiteChart_inv
        hFnorm z).symm
  have hquotient : Tendsto (fun z ↦ F z / z) (cocompact ℂ) (𝓝 a) :=
    tendsto_div_cocompact_of_tendsto_sub_complexLinear F hFasymptotic
  have htangent0 : Tendsto (fun z : ℂ ↦ (F z⁻¹)⁻¹ / z)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (𝓝 a⁻¹) :=
    tendsto_reciprocalConjugate_div_nhdsNE_zero F ha hquotient
  have htangent : Tendsto (fun z : ℂ ↦ H z / z)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (𝓝 a⁻¹) := by
    apply htangent0.congr'
    filter_upwards with z
    rw [show H z = riemannSphereInfinityChartHomeomorph S hFnorm.1 z by
      exact riemannSphereFiniteChartHomeomorph_invConjugate_apply hFnorm z]
    rw [riemannSphereInfinityChartHomeomorph_eq_inv_finiteChart_inv hFnorm]
    rw [show riemannSphereFiniteChartHomeomorph S hFnorm.2.2 = F by
      exact riemannSphereFiniteChartHomeomorph_planeHomeomorphExtension F]
  have hHorient : PreservesPlanarOrientation
      (wholePlaneSubtypeHomeomorph H) :=
    preservesPlanarOrientation_wholePlaneSubtype_of_punctured_of_tendsto_div
      H hH0 P hP.2.2.1 hagree (inv_ne_zero ha) htangent
  obtain ⟨dH, hHW, hHdist⟩ :=
    hP.exists_isLocalW12On_univ_of_punctured_continuous
      H.continuous hagree
  have hHqc : IsKQuasiconformalBetween K
      (wholePlaneSubtypeHomeomorph H) := by
    have hHWambient : IsLocalW12On Set.univ
        (ambientMap (wholePlaneSubtypeHomeomorph H)) dH := by
      apply hHW.congr_ae
      filter_upwards with z
      rw [ambientMap_apply _ ⟨z, Set.mem_univ z⟩]
      simp only [wholePlaneSubtypeHomeomorph_apply]
    exact ⟨hP.1, isOpen_univ, hHorient, dH, hHWambient,
      by simpa only [Measure.restrict_univ] using hHdist⟩
  have hinvfinite : IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph T .finite .finite) := by
    apply hHqc.restrict
      (riemannSphereChartRepresentation T .finite .finite).open_source
      (riemannSphereChartRepresentation T .finite .finite).open_target
      (Set.subset_univ _)
    intro z
    calc
      (riemannSphereChartHomeomorph T .finite .finite z : ℂ) =
          ambientMap (riemannSphereChartHomeomorph T .finite .finite) z :=
        (ambientMap_apply _ z).symm
      _ = H z := ambientMap_finiteChartHomeomorph_apply T hTnorm.2.2 z
      _ = wholePlaneSubtypeHomeomorph H
          ⟨(z : ℂ), Set.mem_univ _⟩ := by
        simp only [wholePlaneSubtypeHomeomorph_apply]
  exact isKQuasiconformalRiemannSphere_of_finiteChart_and_invConjugate_finiteChart
    hFnorm hfinite hinvfinite

/--
%%handwave
name:
  Normalized compact-support principal homeomorphism
statement:
  Let $\mu:\mathbb C\to\mathbb C$ be measurable, vanish almost everywhere
  outside a disk, and satisfy $|\mu|\le k<1$ almost everywhere. Then there
  are a plane homeomorphism $F$ and weak differential $DF$ such that the
  one-point extension of $F$ fixes $0$, $1$, and $\infty$, $F$ preserves
  planar orientation, $F\in W^{1,2}_{\mathrm{loc}}(\mathbb C)$, and
  $$
    \partial_{\bar z}F=\mu\,\partial_zF,
    \qquad
    |DF|^2\le\frac{1+k}{1-k}J_F
  $$
  almost everywhere.
proof:
  Start with the principal homeomorphism and postcompose by
  $w\mapsto(F(1)-F(0))^{-1}(w-F(0))$. Complex-affine postcomposition
  preserves the Beltrami coefficient, distortion bound, local Sobolev
  regularity, and orientation. Its one-point extension fixes the three
  normalized points.
-/
theorem exists_normalizedPrincipalHomeomorphismExtension_of_compactSupport
    (μ : ℂ → ℂ)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k R : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → μ z = 0) :
    ∃ F : ℂ ≃ₜ ℂ, ∃ dF : ℂ → ℂ →L[ℝ] ℂ,
      IsNormalizedRiemannSphereHomeomorph
          (planeHomeomorphExtension F) ∧
        IsKQuasiconformalRiemannSphere ((1 + k) / (1 - k))
          (planeHomeomorphExtension F) ∧
        IsLocalW12On Set.univ F dF ∧
        PreservesPlanarOrientation (wholePlaneSubtypeHomeomorph F) ∧
        WeakBeltramiEquationOn Set.univ μ dF ∧
        ∀ᵐ z ∂(volume : Measure ℂ),
          ‖dF z‖ ^ 2 ≤ ((1 + k) / (1 - k)) * weakJacobian (dF z) := by
  obtain ⟨P, dP, hPW, hPorient, hPBeltrami, hPdist, hPInf⟩ :=
    exists_principalHomeomorphism_of_compactSupport
      μ hμmeas hk0 hk1 hbound hzero
  let a : ℂ := planeNormalizationScale P
  let c : ℂ := -(a * P 0)
  let F : ℂ ≃ₜ ℂ := normalizedPlaneHomeomorph P
  let dF : ℂ → ℂ →L[ℝ] ℂ :=
    fun z ↦ (realLinearMapOfWirtinger a 0).comp (dP z)
  have hFW : IsLocalW12On Set.univ F dF := by
    have h := hPW.postcomp_complexAffine a c
    simpa only [F, dF, a, c, normalizedPlaneHomeomorph_apply] using h
  have hFBeltrami : WeakBeltramiEquationOn Set.univ μ dF := by
    simpa only [dF, a] using hPBeltrami.postcomp_complexLinear a
  have hFdist :
      ∀ᵐ z ∂(volume : Measure ℂ),
        ‖dF z‖ ^ 2 ≤ ((1 + k) / (1 - k)) * weakJacobian (dF z) := by
    have hPdist' :
        ∀ᵐ z ∂(volume.restrict Set.univ : Measure ℂ),
          ‖dP z‖ ^ 2 ≤
            ((1 + k) / (1 - k)) * weakJacobian (dP z) := by
      simpa using hPdist
    have h := metricDistortion_postcomp_complexLinear a hPdist'
    simpa only [Measure.restrict_univ, dF, a] using h
  have hForient :
      PreservesPlanarOrientation (wholePlaneSubtypeHomeomorph F) := by
    simpa only [F] using
      preservesPlanarOrientation_normalizedPlaneHomeomorph P hPorient
  have hK : 1 ≤ (1 + k) / (1 - k) := by
    apply (le_div_iff₀ (sub_pos.mpr hk1)).2
    linarith
  have hFqc : IsKQuasiconformalBetween ((1 + k) / (1 - k))
      (wholePlaneSubtypeHomeomorph F) := by
    have hFWambient : IsLocalW12On Set.univ
        (ambientMap (wholePlaneSubtypeHomeomorph F)) dF := by
      apply hFW.congr_ae
      filter_upwards with z
      rw [ambientMap_apply _ ⟨z, Set.mem_univ z⟩]
      simp only [wholePlaneSubtypeHomeomorph_apply]
    refine ⟨hK, isOpen_univ, hForient, dF, hFWambient, ?_⟩
    · simpa only [Measure.restrict_univ] using hFdist
  have hFnorm : IsNormalizedRiemannSphereHomeomorph
      (planeHomeomorphExtension F) := by
    simpa only [F] using normalized_planeHomeomorphExtension P
  have hFasymptotic : Tendsto (fun z ↦ F z - a * z)
      (cocompact ℂ) (𝓝 c) := by
    have hlim := (hPInf.const_mul a).add_const c
    convert hlim using 1
    · funext z
      simp only [F, normalizedPlaneHomeomorph_apply]
      ring
    · simp
  refine ⟨F, dF, hFnorm,
    isKQuasiconformalRiemannSphere_planeHomeomorphExtension F hFnorm
      (planeNormalizationScale_ne_zero P) hFasymptotic hFqc,
    hFW, hForient, hFBeltrami, hFdist⟩

end

end Quasiconformal

end JJMath
