import JJMath.Analysis.Sobolev.Pullback
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# L1 traces on Euclidean balls

This file contains the radial tail estimates and interior L1 trace existence
statements for scalar Sobolev functions on Euclidean balls.  The reflection and
gluing machinery built from these traces remains in `Extension.lean`.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal NNReal ContDiff Convolution Pointwise

namespace Uniformization

noncomputable section

open ContinuousLinearMap

/--
%%handwave
name:
  Lebesgue measure under scalar dilation
statement:
  Let \(H\) be a finite-dimensional real normed space with Lebesgue measure and let \(a\ne0\).  Under the dilation \(z\mapsto az\), the pushforward measure is \(\operatorname{ofReal}(|(a^{\dim H})^{-1}|)\) times Lebesgue measure.
proof:
  Apply the change-of-variables formula for the continuous linear equivalence \(a\,\mathrm{id}_H\), whose determinant has absolute value \(|a|^{\dim H}\).
-/
private theorem map_const_smul_volume_eq_smul
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {a : ℝ} (ha : a ≠ 0) :
    Measure.map (fun z : H ↦ a • z) MeasureTheory.volume =
      ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹| •
        (MeasureTheory.volume : Measure H) := by
  simpa using
    MeasureTheory.Measure.map_addHaar_smul
      (MeasureTheory.volume : Measure H) ha

/--
%%handwave
name:
  Almost-everywhere statements on the unit ball in polar coordinates
statement:
  If a property holds for almost every point of the Euclidean unit ball, then
  the same property holds for almost every polar point \(r\theta\), with
  \(0<r<1\), for the product of spherical measure and the radial polar
  measure.
proof:
  Remove the origin, which has zero Haar measure, and use the polar-coordinate
  homeomorphism from the punctured space to the unit sphere times the positive
  radii.  Restricting the polar product to \(r<1\) corresponds exactly to
  restricting the punctured space to the unit ball.
-/
theorem ae_polar_product_unitBall_of_ae_volume_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {P : H → Prop}
    (hP : ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball (0 : H) 1), P z) :
    ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
        ((MeasureTheory.Measure.volumeIoiPow
          (Module.finrank ℝ H - 1)).restrict
            {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
      P ((p.2 : ℝ) • (p.1 : H)) := by
  classical
  let B : Set H := Metric.ball (0 : H) 1
  let e : ({0}ᶜ : Set H) ≃ₜ
      (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    homeomorphUnitSphereProd H
  let μNZ : Measure ({0}ᶜ : Set H) :=
    (MeasureTheory.volume : Measure H).comap
      ((↑) : ({0}ᶜ : Set H) → H)
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let ν : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod μR
  let R : Set (Set.Ioi (0 : ℝ)) := {r | (r : ℝ) < 1}
  let S : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) < 1}
  let T : Set ({0}ᶜ : Set H) := {x | ‖(x : H)‖ < 1}
  have hNZ_meas : MeasurableSet ({0}ᶜ : Set H) :=
    (measurableSet_singleton (0 : H)).compl
  have hP_restrict_nonzero :
      ∀ᵐ z ∂(MeasureTheory.volume.restrict B).restrict ({0}ᶜ : Set H),
        P z :=
    ae_mono Measure.restrict_le_self hP
  have hP_subtype :
      ∀ᵐ x : ({0}ᶜ : Set H)
          ∂(MeasureTheory.volume.restrict B).comap
            ((↑) : ({0}ᶜ : Set H) → H),
        P (x : H) :=
    (ae_restrict_iff_subtype
      (μ := MeasureTheory.volume.restrict B) hNZ_meas).1
      hP_restrict_nonzero
  have hcomap_restrict :
      (MeasureTheory.volume.restrict B).comap
          ((↑) : ({0}ᶜ : Set H) → H) =
        μNZ.restrict T := by
    have hraw :=
      (MeasurableEmbedding.subtype_coe hNZ_meas).comap_restrict
        (MeasureTheory.volume : Measure H) B
    have hpreB :
        ((↑) : ({0}ᶜ : Set H) → H) ⁻¹' B = T := by
      ext x
      simp [B, T, Metric.mem_ball, dist_eq_norm]
    simpa [μNZ, hpreB] using hraw
  have hP_T : ∀ᵐ x : ({0}ᶜ : Set H) ∂μNZ.restrict T, P (x : H) := by
    simpa [hcomap_restrict] using hP_subtype
  have hmp : MeasurePreserving e μNZ ν := by
    simpa [e, μNZ, ν, μS, μR] using
      (MeasureTheory.volume : Measure H).measurePreserving_homeomorphUnitSphereProd
  have hmap_restrict :
      (μNZ.restrict (e ⁻¹' S)).map e = ν.restrict S := by
    have hrestrict := e.measurableEmbedding.restrict_map μNZ S
    rw [hmp.map_eq] at hrestrict
    exact hrestrict.symm
  have hpre :
      e ⁻¹' S = T := by
    ext x
    change (((homeomorphUnitSphereProd H) x).2 : ℝ) < 1 ↔
      ‖(x : H)‖ < 1
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  have hS_eq : S = Set.univ ×ˢ R := by
    ext p
    simp [S, R]
  have hmeasure :
      ν.restrict S = μS.prod (μR.restrict R) := by
    rw [hS_eq]
    have hprod :=
      Measure.prod_restrict (μ := μS) (ν := μR) Set.univ R
    simpa [ν] using hprod.symm
  have hmap_target :
      (μNZ.restrict T).map e = μS.prod (μR.restrict R) := by
    rw [← hpre, hmap_restrict, hmeasure]
  have hpush :
      ∀ᵐ p ∂(μNZ.restrict T).map e, P ((p.2 : ℝ) • (p.1 : H)) := by
    rw [e.measurableEmbedding.ae_map_iff]
    filter_upwards [hP_T] with x hx
    have hx_norm_ne : ‖(x : H)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact x.2
    have hdir :
        (((e x).1 : Metric.sphere (0 : H) 1) : H) =
          ((1 / ‖(x : H)‖) : ℝ) • (x : H) := by
      simp [e, homeomorphUnitSphereProd_apply_fst_coe, div_eq_mul_inv]
    have hr : (((e x).2 : Set.Ioi (0 : ℝ)) : ℝ) = ‖(x : H)‖ := by
      simp [e, homeomorphUnitSphereProd_apply_snd_coe]
    have hpoint : ((e x).2 : ℝ) • ((e x).1 : H) = (x : H) := by
      rw [hr, hdir, smul_smul]
      have hcoef : ‖(x : H)‖ * (1 / ‖(x : H)‖) = (1 : ℝ) := by
        field_simp [hx_norm_ne]
      rw [hcoef, one_smul]
    simpa [hpoint] using hx
  simpa [hmap_target, μS, μR, R] using hpush

/--
%%handwave
name:
  Absolute continuity after restriction
statement:
  If measures \(\mu\) and \(\nu\) satisfy \(\mu\ll\nu\), then for every measurable set \(S\) one has \(\mu|_S\ll\nu|_S\).
proof:
  A set null for \(\nu|_S\) has null intersection with \(S\) under \(\nu\), hence also under \(\mu\); this is exactly nullity for \(\mu|_S\).
-/
private theorem restrict_absolutelyContinuous_same_set
    {α : Type} [MeasurableSpace α] {μ ν : Measure α} (hμν : μ ≪ ν)
    {s : Set α} (hs : MeasurableSet s) :
    μ.restrict s ≪ ν.restrict s := by
  intro t ht
  rw [Measure.restrict_apply_eq_zero' hs] at ht ⊢
  exact hμν ht

/--
%%handwave
name:
  Ordinary radial measure is dominated by polar radial measure
statement:
  On \((0,\infty)\), the pullback of one-dimensional Lebesgue measure under the inclusion is absolutely continuous with respect to the radial measure \(r^n\,dr\).
proof:
  A set of zero \(r^n\,dr\)-measure is Lebesgue-null away from the origin because the density \(r^n\) is strictly positive on \((0,\infty)\).  Pulling back along the inclusion gives the claim.
-/
private theorem volumeIoi_absolutelyContinuous_volumeIoiPow (n : ℕ) :
    ((Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
        MeasureTheory.volume) : Measure (Set.Ioi (0 : ℝ))) ≪
      MeasureTheory.Measure.volumeIoiPow n := by
  rw [MeasureTheory.Measure.volumeIoiPow]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · measurability
  · filter_upwards with r
    have hrpow : 0 < (r : ℝ) ^ n := pow_pos r.2 n
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hrpow)

/--
%%handwave
name:
  Removing the polar weight on the unit radial interval
statement:
  Let \(P\) be a property of positive radii.  If \(P(r)\) holds for \(r^n\,dr\)-almost every \(0<r<1\), then for Lebesgue-almost every real \(t\), \(0<t<1\) implies \(P(t)\).
proof:
  Restrict the absolute continuity \(dt\ll r^n\,dr\) to \(0<r<1\), transfer the almost-everywhere statement, and rewrite the pullback along the inclusion.
-/
private theorem ae_volume_Ioo_zero_one_of_ae_volumeIoiPow_restrict
    {n : ℕ} {P : Set.Ioi (0 : ℝ) → Prop}
    (hP : ∀ᵐ r
        ∂((MeasureTheory.Measure.volumeIoiPow n).restrict
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
        P r) :
    ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
      ∀ (ht_pos : 0 < t), t < 1 → P ⟨t, ht_pos⟩ := by
  classical
  let μI : Measure (Set.Ioi (0 : ℝ)) :=
    Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ) MeasureTheory.volume
  let R : Set (Set.Ioi (0 : ℝ)) :=
    {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  have h_ac :
      μI.restrict R ≪
        (MeasureTheory.Measure.volumeIoiPow n).restrict R :=
    restrict_absolutelyContinuous_same_set
      (volumeIoi_absolutelyContinuous_volumeIoiPow n) (by
        dsimp [R]
        measurability)
  have hP_unweighted : ∀ᵐ r ∂μI.restrict R, P r :=
    h_ac.ae_le hP
  have hbad_restrict :
      μI.restrict R {r : Set.Ioi (0 : ℝ) | ¬ P r} = 0 := by
    simpa only [Set.mem_setOf_eq, not_not] using
      (ae_iff.mp hP_unweighted)
  have hbad :
      μI ({r : Set.Ioi (0 : ℝ) | ¬ P r} ∩ R) = 0 := by
    exact nonpos_iff_eq_zero.1
      ((Measure.le_restrict_apply R {r : Set.Ioi (0 : ℝ) | ¬ P r}).trans
        (le_of_eq hbad_restrict))
  have hbad_image :
      (MeasureTheory.volume : Measure ℝ)
        (((↑) : Set.Ioi (0 : ℝ) → ℝ) ''
          ({r : Set.Ioi (0 : ℝ) | ¬ P r} ∩ R)) = 0 := by
    simpa [μI] using
      (comap_subtype_coe_apply
        (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))
        (MeasureTheory.volume : Measure ℝ)
        ({r : Set.Ioi (0 : ℝ) | ¬ P r} ∩ R)).symm.trans hbad
  rw [ae_iff]
  refine measure_mono_null ?_ hbad_image
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  rcases not_forall.mp ht with ⟨ht_pos, ht_not_imp⟩
  have ht_lt_one : t < 1 := by
    by_contra ht_not_lt
    exact ht_not_imp (fun ht_lt_one ↦ False.elim (ht_not_lt ht_lt_one))
  have htP : ¬ P ⟨t, ht_pos⟩ := by
    intro hP
    exact ht_not_imp (fun _ ↦ hP)
  refine ⟨⟨t, ht_pos⟩, ?_, rfl⟩
  exact ⟨htP, by simpa [R] using ht_lt_one⟩

/--
%%handwave
name:
  Interior \(L^1\) trace on a Euclidean sphere
statement:
  A function has \(L^1\) trace \(\tau\) on the sphere of radius \(r\) from the
  inside if the normalized integral of
  \(|u(x)-\tau(r x/\|x\|)|\) over the inner collar
  \(r-\varepsilon<\|x\|<r\) tends to zero as \(\varepsilon\downarrow0\).
-/
def HasL1TraceFromInsideSphere
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (r : ℝ) (u τ : H → ℝ) : Prop :=
  Filter.Tendsto
    (fun ε : ℝ ↦
      ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | r - ε < ‖x‖ ∧ ‖x‖ < r},
          ENNReal.ofReal ‖u x - τ (((r / ‖x‖) : ℝ) • x)‖
            ∂MeasureTheory.volume)
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))

/--
%%handwave
name:
  Exterior \(L^1\) trace on a Euclidean sphere
statement:
  A function has \(L^1\) trace \(\tau\) on the sphere of radius \(r\) from the
  outside if the normalized integral of
  \(|u(x)-\tau(r x/\|x\|)|\) over the outer collar
  \(r<\|x\|<r+\varepsilon\) tends to zero as \(\varepsilon\downarrow0\).
-/
def HasL1TraceFromOutsideSphere
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (r : ℝ) (u τ : H → ℝ) : Prop :=
  Filter.Tendsto
    (fun ε : ℝ ↦
      ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | r < ‖x‖ ∧ ‖x‖ < r + ε},
          ENNReal.ofReal ‖u x - τ (((r / ‖x‖) : ℝ) • x)‖
            ∂MeasureTheory.volume)
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))

/--
%%handwave
name:
  A vanishing collar majorant gives an inside \(L^1\) trace
statement:
  Let \(\tau\) be a boundary representative and let \(R\ge0\) be a collar
  error majorant.  If, for all sufficiently small positive \(\varepsilon\),
  \[
    |w(x)-\tau(x/\|x\|)|\le R(x)
  \]
  for almost every \(x\) with \(1-\varepsilon<\|x\|<1\), and the normalized
  collar integrals of \(R\) tend to zero, then \(w\) has inside \(L^1\) trace
  \(\tau\) on the unit sphere.
proof:
  Use monotonicity of the nonnegative integral on each collar, multiply by
  \(1/\varepsilon\), and apply the squeeze theorem for extended nonnegative
  real-valued functions.
-/
theorem hasL1TraceFromInsideSphere_one_of_eventually_ae_bound
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {w τ : H → ℝ} {R : H → ℝ≥0∞}
    (hbound :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ᵐ x ∂MeasureTheory.volume.restrict
            {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          ENNReal.ofReal
            ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖ ≤ R x)
    (hR :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ENNReal.ofReal (1 / ε) *
            ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
              R x ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))) :
    HasL1TraceFromInsideSphere (H := H) 1 w τ := by
  rw [HasL1TraceFromInsideSphere]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hR
      (Filter.Eventually.of_forall fun _ε ↦ zero_le)
      ?_
  filter_upwards [hbound] with ε hε_bound
  have hlin :
      (∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          ENNReal.ofReal
            ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖
          ∂MeasureTheory.volume) ≤
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          R x ∂MeasureTheory.volume :=
    lintegral_mono_ae hε_bound
  exact mul_le_mul_right hlin _

/--
%%handwave
name:
  Radial tail majorant for a weak derivative on the unit ball
statement:
  The radial tail majorant associated to a weak derivative field \(Dw\) is
  the integral of the directional size of \(Dw\) along the radial segment from
  \(x\) to the unit sphere:
  \[
    \int_{\|x\|}^1
      |Dw(t x/\|x\|)(x/\|x\|)|\,dt .
  \]
-/
def euclideanSobolevUnitBallRadialTailMajorant
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (dw : H → H →L[ℝ] ℝ) (x : H) : ℝ≥0∞ :=
  ∫⁻ t in {t : ℝ | ‖x‖ < t ∧ t < 1},
    ENNReal.ofReal
      ‖dw (((t / ‖x‖) : ℝ) • x) (((1 / ‖x‖) : ℝ) • x)‖
      ∂MeasureTheory.volume

/--
%%handwave
name:
  Radial tail integral of a nonnegative function on the unit ball
statement:
  The radial tail integral associated to a nonnegative function \(F\) is
  \[
    \int_{\|x\|}^1 F(t x/\|x\|)\,dt .
  \]
-/
def euclideanSobolevUnitBallRadialTailIntegral
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : H → ℝ≥0∞) (x : H) : ℝ≥0∞ :=
  ∫⁻ t in {t : ℝ | ‖x‖ < t ∧ t < 1},
    F (((t / ‖x‖) : ℝ) • x) ∂MeasureTheory.volume

/--
%%handwave
name:
  The directional radial tail is bounded by the operator-norm radial tail
statement:
  Away from the origin, the radial majorant formed from a derivative field
  \(Dw\) is bounded by the radial tail integral of the operator norm
  \(|Dw|\).
proof:
  The radial direction \(x/\|x\|\) has norm one.  Hence
  \(|Dw(y)(x/\|x\|)|\le |Dw(y)|\) pointwise along the segment, and monotonicity
  of the nonnegative integral gives the result.
-/
theorem euclideanSobolev_unit_ball_radial_tailMajorant_le_norm_tailIntegral
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {dw : H → H →L[ℝ] ℝ} {x : H}
    (hx : 0 < ‖x‖) :
    euclideanSobolevUnitBallRadialTailMajorant dw x ≤
      euclideanSobolevUnitBallRadialTailIntegral
        (fun y : H ↦ ENNReal.ofReal ‖dw y‖) x := by
  dsimp [euclideanSobolevUnitBallRadialTailMajorant,
    euclideanSobolevUnitBallRadialTailIntegral]
  refine lintegral_mono fun t ↦ ?_
  have hdir_norm : ‖((1 / ‖x‖ : ℝ) • x)‖ = 1 := by
    calc
      ‖((1 / ‖x‖ : ℝ) • x)‖ =
          ‖(1 / ‖x‖ : ℝ)‖ * ‖x‖ := by
            exact norm_smul (1 / ‖x‖ : ℝ) x
      _ = (1 / ‖x‖) * ‖x‖ := by
            rw [Real.norm_of_nonneg (div_nonneg zero_le_one hx.le)]
      _ = 1 := by
            field_simp [ne_of_gt hx]
  have hle :
      ‖dw (((t / ‖x‖) : ℝ) • x)
          (((1 / ‖x‖) : ℝ) • x)‖ ≤
        ‖dw (((t / ‖x‖) : ℝ) • x)‖ := by
    calc
      ‖dw (((t / ‖x‖) : ℝ) • x)
          (((1 / ‖x‖) : ℝ) • x)‖ ≤
          ‖dw (((t / ‖x‖) : ℝ) • x)‖ *
            ‖((1 / ‖x‖ : ℝ) • x)‖ :=
            (dw (((t / ‖x‖) : ℝ) • x)).le_opNorm
              (((1 / ‖x‖) : ℝ) • x)
      _ = ‖dw (((t / ‖x‖) : ℝ) • x)‖ := by
            rw [hdir_norm, mul_one]
  exact ENNReal.ofReal_le_ofReal hle

/--
%%handwave
name:
  Polar formula for the radial tail majorant
statement:
  For a unit direction \(\theta\) and radius \(r>0\), the radial tail majorant at \(r\theta\) equals
  \[
    \int_{\{t:r<t<1\}}\!\!\|dw(t\theta)(\theta)\|\,dt.
  \]
proof:
  In the defining line integral, use \(\|r\theta\|=r\), simplify \((t/r)(r\theta)=t\theta\), and simplify the rescaled radial direction \((1/r)(r\theta)=\theta\).
-/
private theorem euclideanSobolevUnitBallRadialTailMajorant_polar
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {dw : H → H →L[ℝ] ℝ}
    (p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :
    euclideanSobolevUnitBallRadialTailMajorant dw
        (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
              ∫⁻ t in
                {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume := by
  have hθ_norm : ‖(p.1 : H)‖ = (1 : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm] using p.1.2
  have hr_pos : 0 < ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) := p.2.2
  have hr_ne : ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hr_norm :
      ‖(((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ =
        ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) := by
    simp [norm_smul, Real.norm_of_nonneg hr_pos.le, hθ_norm]
  have hpoint : ∀ t : ℝ,
      ((t / ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) : ℝ) •
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
        t • (p.1 : H) := by
    intro t
    rw [smul_smul]
    have hcoef :
        (t / ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
            ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) = t := by
      field_simp [hr_ne]
    rw [hcoef]
  have hdir :
      ((1 / ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) : ℝ) •
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
        (p.1 : H) := by
    rw [smul_smul]
    have hcoef :
        (1 / ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
            ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) = (1 : ℝ) := by
      field_simp [hr_ne]
    rw [hcoef, one_smul]
  dsimp [euclideanSobolevUnitBallRadialTailMajorant]
  rw [hr_norm]
  refine setLIntegral_congr_fun (by measurability) ?_
  intro t _ht
  change
    ENNReal.ofReal
        ‖dw (((t / ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) : ℝ) •
              (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)))
            (((1 / ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) : ℝ) •
              (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)))‖ =
      ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
  rw [hpoint t, hdir]

/--
%%handwave
name:
  Fubini principle with a null-measurable exceptional set
statement:
  Suppose the failure set \(\{(a,b):\neg P(a,b)\}\) is null-measurable for \(\mu\times\nu\), where \(\nu\) is \(\sigma\)-finite in the generalized sense.  If \(P(a,b)\) holds for \(\mu\)-almost every \(a\) and then for \(\nu\)-almost every \(b\), it holds for \((\mu\times\nu)\)-almost every pair.
proof:
  Replace the failure set by a measurable set equal to it almost everywhere.  Fubini shows that almost every section of this measurable replacement is null; the iterated hypothesis forces the replacement itself to be product-null, and hence so is the original failure set.
-/
private theorem ae_prod_of_ae_ae_of_nullMeasurable_bad
    {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    {P : α × β → Prop}
    (hbad : NullMeasurableSet {p : α × β | ¬ P p} (μ.prod ν))
    (hP : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, P (a, b)) :
    ∀ᵐ p ∂μ.prod ν, P p := by
  classical
  let bad : Set (α × β) := {p | ¬ P p}
  let B : Set (α × β) := MeasureTheory.toMeasurable (μ.prod ν) bad
  have hB_meas : MeasurableSet B := by
    simp [B, measurableSet_toMeasurable (μ.prod ν) bad]
  have hB_bad : B =ᵐ[μ.prod ν] bad := by
    simpa [B, bad] using hbad.toMeasurable_ae_eq
  have hB_bad_slices :
      ∀ᵐ a ∂μ, ∀ᵐ b ∂ν,
        (((a, b) : α × β) ∈ B) = (((a, b) : α × β) ∈ bad) :=
    Measure.ae_ae_of_ae_prod hB_bad
  have hnotB_slices :
      ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ((a, b) : α × β) ∉ B := by
    filter_upwards [hP, hB_bad_slices] with a hPa hBada
    filter_upwards [hPa, hBada] with b hPab hBadab hBmem
    have hbadmem : ((a, b) : α × β) ∈ bad := by
      rwa [← hBadab]
    have hnotP : ¬ P (a, b) := by
      simpa [bad] using hbadmem
    exact hnotP hPab
  have hnotB_prod :
      ∀ᵐ p ∂μ.prod ν, p ∉ B := by
    exact
      (Measure.ae_prod_iff_ae_ae
        (show MeasurableSet {p : α × β | p ∉ B} from hB_meas.compl)).2
        hnotB_slices
  have hB_zero : μ.prod ν B = 0 := by
    simpa [ae_iff] using hnotB_prod
  have hbad_zero : μ.prod ν bad = 0 := by
    have hto_zero :
        μ.prod ν (MeasureTheory.toMeasurable (μ.prod ν) bad) = 0 := by
      simpa [B] using hB_zero
    rw [measure_toMeasurable] at hto_zero
    simpa [bad] using hto_zero
  simpa [ae_iff, bad] using hbad_zero

/--
%%handwave
name:
  Points have zero spherical measure in dimension at least two
statement:
  On the unit sphere of a finite-dimensional real normed space of dimension
  at least two, every singleton has zero spherical measure.
proof:
  Use the polar definition of spherical measure.  The cone over a single
  sphere point is contained in the line spanned by that point.  Since the
  ambient dimension is at least two, this line is a proper linear subspace,
  hence has zero Haar measure.
-/
theorem toSphere_singleton_eq_zero_of_one_lt_finrank
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    (hfin : 1 < Module.finrank ℝ H)
    (v : Metric.sphere (0 : H) 1) :
    (MeasureTheory.volume : Measure H).toSphere
        ({v} : Set (Metric.sphere (0 : H) 1)) = 0 := by
  classical
  let L : Submodule ℝ H := ℝ ∙ (v : H)
  have hv_ne : (v : H) ≠ 0 := ne_zero_of_mem_unit_sphere v
  have hL_rank : Module.finrank ℝ L = 1 := by
    simpa [L] using (finrank_span_singleton (K := ℝ) hv_ne)
  have hL_ne_top : L ≠ ⊤ := by
    intro htop
    have hL_rank_top : Module.finrank ℝ L = Module.finrank ℝ H := by
      rw [htop, finrank_top]
    have hdim_eq_one : Module.finrank ℝ H = 1 := by
      rw [← hL_rank_top, hL_rank]
    omega
  have hcone_subset :
      Set.Ioo (0 : ℝ) 1 •
          ((↑) '' ({v} : Set (Metric.sphere (0 : H) 1))) ⊆
        (L : Set H) := by
    rintro x ⟨a, _ha, y, hy, rfl⟩
    rcases hy with ⟨θ, hθ, rfl⟩
    have hθ : θ = v := by simpa using hθ
    subst θ
    exact L.smul_mem a (Submodule.mem_span_singleton_self (v : H))
  have hline_zero :
      (MeasureTheory.volume : Measure H) (L : Set H) = 0 :=
    MeasureTheory.Measure.addHaar_submodule
      (MeasureTheory.volume : Measure H) L hL_ne_top
  have hcone_zero :
      (MeasureTheory.volume : Measure H)
          (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' ({v} : Set (Metric.sphere (0 : H) 1)))) = 0 :=
    measure_mono_null hcone_subset hline_zero
  rw [MeasureTheory.Measure.toSphere_apply'
    (μ := (MeasureTheory.volume : Measure H)) (hs := measurableSet_singleton v),
    hcone_zero, mul_zero]

/--
%%handwave
name:
  A stereographic chart covers almost every sphere direction
statement:
  In ambient dimension at least two, if a property holds for almost every
  direction in one stereographic coordinate source, then it holds for almost
  every direction on the whole unit sphere.
proof:
  The complement of a stereographic source is its pole.  By
  [points have zero spherical measure in dimension at least two](lean:JJMath.Uniformization.toSphere_singleton_eq_zero_of_one_lt_finrank),
  this pole can be discarded from any almost-everywhere statement.
-/
theorem ae_toSphere_of_ae_restrict_stereographic_source_of_one_lt_finrank
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (hfin : 1 < Module.finrank ℝ H)
    (v : Metric.sphere (0 : H) 1)
    {P : Metric.sphere (0 : H) 1 → Prop}
    (hP :
      ∀ᵐ θ ∂((MeasureTheory.volume : Measure H).toSphere.restrict
          (stereographic' n v).source), P θ) :
    ∀ᵐ θ ∂((MeasureTheory.volume : Measure H).toSphere), P θ := by
  have hsource_meas : MeasurableSet (stereographic' n v).source :=
    (stereographic' n v).open_source.measurableSet
  have hP_imp :
      ∀ᵐ θ ∂((MeasureTheory.volume : Measure H).toSphere),
        θ ∈ (stereographic' n v).source → P θ :=
    (ae_restrict_iff' hsource_meas).1 hP
  have hpole_zero :
      (MeasureTheory.volume : Measure H).toSphere
          ({v} : Set (Metric.sphere (0 : H) 1)) = 0 :=
    toSphere_singleton_eq_zero_of_one_lt_finrank hfin v
  have hsource_ae :
      ∀ᵐ θ ∂((MeasureTheory.volume : Measure H).toSphere),
        θ ∈ (stereographic' n v).source := by
    rw [stereographic'_source]
    simpa using (compl_mem_ae_iff.mpr hpole_zero)
  filter_upwards [hP_imp, hsource_ae] with θ hθ_imp hθ_source
  exact hθ_imp hθ_source

private def stereographicPolarPatchMap
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    ℝ × EuclideanSpace ℝ (Fin n) → H :=
  fun p ↦ p.1 • ((stereographic' n v).symm p.2 : H)

/--
%%handwave
name:
  Formula for a stereographic polar patch
statement:
  If \(\sigma_v(y)\) is the inverse stereographic image of \(y\) with pole \(v\), then the associated polar patch satisfies \(\Phi_v(r,y)=r\,\sigma_v(y)\).
proof:
  This is the definition of the polar patch map.
-/
private theorem stereographicPolarPatchMap_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (r : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    stereographicPolarPatchMap v (r, y) =
      r • ((stereographic' n v).symm y : H) :=
  rfl

/--
%%handwave
name:
  Inverse stereographic projection on its source
statement:
  For every sphere point \(\theta\) in the source of stereographic projection with pole \(v\), inverse stereographic projection sends its coordinate back to \(\theta\).
proof:
  Apply the left-inverse property of the stereographic chart and then forget the sphere subtype.
-/
private theorem stereographic'_symm_apply_apply_of_mem_source
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {θ : Metric.sphere (0 : H) 1}
    (hθ : θ ∈ (stereographic' n v).source) :
    ((stereographic' n v).symm ((stereographic' n v) θ) : H) = θ := by
  exact congrArg Subtype.val ((stereographic' n v).left_inv hθ)

/--
%%handwave
name:
  Polar patch in spherical coordinates
statement:
  If \(\theta\) lies in the stereographic source, then \(\Phi_v(r,\operatorname{stereo}_v(\theta))=r\theta\).
proof:
  Substitute the polar patch formula and use that inverse stereographic projection recovers \(\theta\) on the chart source.
-/
private theorem stereographicPolarPatchMap_apply_chart
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {θ : Metric.sphere (0 : H) 1}
    (hθ : θ ∈ (stereographic' n v).source)
    (r : ℝ) :
    stereographicPolarPatchMap v (r, (stereographic' n v) θ) =
      r • (θ : H) := by
  rw [stereographicPolarPatchMap_apply,
    stereographic'_symm_apply_apply_of_mem_source (n := n) v hθ]

/--
%%handwave
name:
  Explicit inverse-stereographic polar formula
statement:
  Let \(U:v^\perp\to\mathbb R^n\) be the orthonormal coordinate map.  The polar patch is
  \[
  \Phi_v(r,y)=r\left(\frac{4\,U^{-1}y}{\|U^{-1}y\|^2+4}
  +\frac{\|U^{-1}y\|^2-4}{\|U^{-1}y\|^2+4}\,v\right).
  \]
proof:
  Insert the standard explicit formula for inverse stereographic projection into \(\Phi_v(r,y)=r\,\sigma_v(y)\).
-/
private theorem stereographicPolarPatchMap_apply_explicit
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (r : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    stereographicPolarPatchMap v (r, y) =
      r •
        (let U : (ℝ ∙ (v : H))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
          (OrthonormalBasis.fromOrthogonalSpanSingleton n
            (ne_zero_of_mem_unit_sphere v)).repr
        (‖(U.symm y : H)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm y : H) +
          (‖(U.symm y : H)‖ ^ 2 + 4)⁻¹ •
                    (‖(U.symm y : H)‖ ^ 2 - 4) • v.val) := by
  rw [stereographicPolarPatchMap_apply, stereographic'_symm_apply]

private def stereographicPolarPatchCylinder (n : ℕ) :
    Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
  {p | 0 < p.1 ∧ p.1 < 1}

/--
%%handwave
name:
  Inverse stereographic projection has unit norm
statement:
  Every inverse stereographic image \(\sigma_v(y)\) lies on the unit sphere, so \(\|\sigma_v(y)\|=1\).
proof:
  Unpack membership in the unit sphere and rewrite distance from the origin as the norm.
-/
private theorem norm_stereographic'_symm
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖((stereographic' n v).symm y : H)‖ = 1 := by
  simpa [Metric.mem_sphere, dist_eq_norm] using
    ((stereographic' n v).symm y).2

/--
%%handwave
name:
  Radius of a stereographic polar point
statement:
  For every \(r\in\mathbb R\) and stereographic coordinate \(y\), \(\|\Phi_v(r,y)\|=|r|\).
proof:
  Use \(\Phi_v(r,y)=r\,\sigma_v(y)\), multiplicativity of the norm under real scaling, and \(\|\sigma_v(y)\|=1\).
-/
private theorem norm_stereographicPolarPatchMap
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (r : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ‖stereographicPolarPatchMap v (r, y)‖ = |r| := by
  rw [stereographicPolarPatchMap_apply, norm_smul,
    norm_stereographic'_symm (n := n) v y, mul_one]
  exact Real.norm_eq_abs r

/--
%%handwave
name:
  The positive polar cylinder maps into the unit ball
statement:
  The map \(\Phi_v\) sends every \((r,y)\) with \(0<r<1\) into the open unit ball.
proof:
  The image has norm \(|r|=r<1\).
-/
private theorem stereographicPolarPatchMap_mapsTo_cylinder_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    Set.MapsTo (stereographicPolarPatchMap v)
      (stereographicPolarPatchCylinder n)
      (Metric.ball (0 : H) 1) := by
  intro p hp
  have hnorm :
      ‖stereographicPolarPatchMap v p‖ = p.1 := by
    rw [norm_stereographicPolarPatchMap (n := n) v p.1 p.2,
      abs_of_nonneg hp.1.le]
  simpa [Metric.mem_ball, dist_eq_norm, hnorm] using hp.2

/--
%%handwave
name:
  Injectivity of a stereographic polar patch
statement:
  The map \((r,y)\mapsto r\,\sigma_v(y)\) is injective on the cylinder \(0<r<1\).
proof:
  Equality of two images first gives equality of their positive radii by taking norms.  Cancelling the common nonzero radius gives equality of the unit directions, and injectivity of inverse stereographic projection then gives equality of the coordinates.
-/
private theorem stereographicPolarPatchMap_injOn_cylinder
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    Set.InjOn (stereographicPolarPatchMap v)
      (stereographicPolarPatchCylinder n) := by
  intro p hp q hq hpq
  have hp_norm :
      ‖stereographicPolarPatchMap v p‖ = p.1 := by
    rw [norm_stereographicPolarPatchMap (n := n) v p.1 p.2,
      abs_of_nonneg hp.1.le]
  have hq_norm :
      ‖stereographicPolarPatchMap v q‖ = q.1 := by
    rw [norm_stereographicPolarPatchMap (n := n) v q.1 q.2,
      abs_of_nonneg hq.1.le]
  have hfirst : p.1 = q.1 := by
    rw [← hp_norm, hpq, hq_norm]
  have hdir :
      ((stereographic' n v).symm p.2 :
          Metric.sphere (0 : H) 1) =
        (stereographic' n v).symm q.2 := by
    apply Subtype.ext
    have hscaled0 :
        p.1 • ((stereographic' n v).symm p.2 : H) =
          q.1 • ((stereographic' n v).symm q.2 : H) := by
      simpa [stereographicPolarPatchMap_apply] using hpq
    have hscaled :
        p.1 • ((stereographic' n v).symm p.2 : H) =
          p.1 • ((stereographic' n v).symm q.2 : H) := by
      simpa [hfirst] using hscaled0
    have hcancel :=
      congrArg (fun z : H ↦ (p.1⁻¹ : ℝ) • z) hscaled
    simpa [smul_smul, hp.1.ne'] using hcancel
  have hsecond : p.2 = q.2 := by
    have hp_target : p.2 ∈ (stereographic' n v).target := by
      simp [stereographic'_target]
    have hq_target : q.2 ∈ (stereographic' n v).target := by
      simp [stereographic'_target]
    have happ := congrArg (fun θ => (stereographic' n v) θ) hdir
    simpa [(stereographic' n v).right_inv hp_target,
      (stereographic' n v).right_inv hq_target] using happ
  exact Prod.ext hfirst hsecond

/--
%%handwave
name:
  A cylinder over a null set is null
statement:
  If \(A\subseteq E\) has zero volume, then \((0,1)\times A\subseteq\mathbb R\times E\) has zero product volume.
proof:
  Product volume of the rectangle is bounded by \(\operatorname{vol}(0,1)\operatorname{vol}(A)=0\).
-/
private theorem volume_Ioo_prod_null_of_null
    {E : Type} [MeasureSpace E]
    {A : Set E}
    (hA : (MeasureTheory.volume : Measure E) A = 0) :
    (MeasureTheory.volume : Measure (ℝ × E))
        (Set.Ioo (0 : ℝ) 1 ×ˢ A) = 0 := by
  have hvol :
      (MeasureTheory.volume : Measure (ℝ × E)) =
        (MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure E) :=
    Measure.volume_eq_prod ℝ E
  refine le_antisymm ?_ zero_le
  rw [hvol]
  calc
    (MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure E)
        (Set.Ioo (0 : ℝ) 1 ×ˢ A) ≤
      (MeasureTheory.volume : Measure ℝ) (Set.Ioo (0 : ℝ) 1) *
        (MeasureTheory.volume : Measure E) A :=
        Measure.prod_prod_le _ _
    _ = 0 := by rw [hA, mul_zero]

/--
%%handwave
name:
  Nullity descends from a nondegenerate cylinder
statement:
  If \((0,1)\times A\) has zero product volume and volume on \(E\) is \(\sigma\)-finite in the generalized sense, then \(A\) has zero volume.
proof:
  The product formula gives \(0=\operatorname{vol}(0,1)\operatorname{vol}(A)\); since \(\operatorname{vol}(0,1)\ne0\), the second factor vanishes.
-/
private theorem volume_null_of_Ioo_prod_null
    {E : Type} [MeasureSpace E] [SFinite (MeasureTheory.volume : Measure E)]
    {A : Set E}
    (hprod : (MeasureTheory.volume : Measure (ℝ × E))
      (Set.Ioo (0 : ℝ) 1 ×ˢ A) = 0) :
    (MeasureTheory.volume : Measure E) A = 0 := by
  have hvol :
      (MeasureTheory.volume : Measure (ℝ × E)) =
        (MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure E) :=
    Measure.volume_eq_prod ℝ E
  rw [hvol, Measure.prod_prod] at hprod
  have hI :
      (MeasureTheory.volume : Measure ℝ) (Set.Ioo (0 : ℝ) 1) ≠ 0 := by
    simp
  exact (mul_eq_zero.mp hprod).resolve_left hI

/--
%%handwave
name:
  Linear coordinate changes preserve volume-null sets
statement:
  A continuous linear equivalence between finite-dimensional real normed spaces sends every Lebesgue-null set to a Lebesgue-null set.
proof:
  Enlarge the set to a measurable null set.  Haar uniqueness expresses pushforward volume under the equivalence as a positive scalar multiple of target volume, so the measurable image is null; monotonicity handles the original set.
-/
private theorem continuousLinearEquiv_image_volume_null
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasureSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure E)]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure F)]
    (e : E ≃L[ℝ] F) {s : Set E}
    (hs : (MeasureTheory.volume : Measure E) s = 0) :
    (MeasureTheory.volume : Measure F) (e '' s) = 0 := by
  classical
  let μE : Measure E := MeasureTheory.volume
  let μF : Measure F := MeasureTheory.volume
  let t : Set E := MeasureTheory.toMeasurable μE s
  have hst : s ⊆ t := subset_toMeasurable μE s
  have ht_meas : MeasurableSet t := measurableSet_toMeasurable μE s
  have ht_zero : μE t = 0 := by
    rw [measure_toMeasurable]
    exact hs
  have himage_subset : e '' s ⊆ e '' t := Set.image_mono hst
  have himage_meas : MeasurableSet (e '' t) :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image' ht_meas
  rcases
    LinearMap.exists_map_addHaar_eq_smul_addHaar
      (L := (e : E →ₗ[ℝ] F)) (μ := μE) (ν := μF) e.surjective with
    ⟨c, hc_pos, hmap⟩
  have hmap_image : c * μF (e '' t) = 0 := by
    have hmeasL : Measurable (((e : E →ₗ[ℝ] F) : E → F)) :=
      e.continuous.measurable
    calc
      c * μF (e '' t) = (c • μF) (e '' t) := by rfl
      _ = Measure.map ((e : E →ₗ[ℝ] F) : E → F) μE (e '' t) := by
        rw [← hmap]
      _ = μE (((e : E →ₗ[ℝ] F) : E → F) ⁻¹' (e '' t)) := by
        rw [Measure.map_apply hmeasL himage_meas]
      _ = μE t := by
        change μE (((e : E →ₗ[ℝ] F) : E → F) ⁻¹'
            (((e : E →ₗ[ℝ] F) : E → F) '' t)) = μE t
        have hinjL : Function.Injective (((e : E →ₗ[ℝ] F) : E → F)) :=
          e.injective
        rw [hinjL.preimage_image]
      _ = 0 := ht_zero
  have himage_t_zero : μF (e '' t) = 0 := by
    exact (mul_eq_zero.mp hmap_image).resolve_left (ne_of_gt hc_pos)
  exact measure_mono_null himage_subset himage_t_zero

/--
%%handwave
name:
  Image of a stereographic polar cylinder
statement:
  For \(A\subseteq\mathbb R^n\),
  \[
    \Phi_v\big((0,1)\times A\big)
    =(0,1)\cdot\{\theta\in\mathbb S:\theta\ne v,\ \operatorname{stereo}_v(\theta)\in A\}.
  \]
proof:
  In one direction write the angular factor as the inverse stereographic image of \(y\in A\).  In the other, parameterize a source direction by its stereographic coordinate and use the chart inverse identities.
-/
private theorem stereographicPolarPatchMap_image_Ioo_prod_eq_cone_chart_preimage
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    stereographicPolarPatchMap v '' (Set.Ioo (0 : ℝ) 1 ×ˢ A) =
      Set.Ioo (0 : ℝ) 1 •
        ((↑) '' ((stereographic' n v).source ∩
          (stereographic' n v) ⁻¹' A)) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨hr, hyA⟩
    refine Set.mem_smul.2 ⟨p.1, hr, ?_⟩
    refine ⟨((stereographic' n v).symm p.2 : H), ?_, ?_⟩
    · refine ⟨(stereographic' n v).symm p.2, ?_, rfl⟩
      have htarget : p.2 ∈ (stereographic' n v).target := by
        simp [stereographic'_target]
      refine ⟨(stereographic' n v).map_target htarget, ?_⟩
      simpa [(stereographic' n v).right_inv htarget] using hyA
    · rfl
  · rw [Set.mem_smul]
    rintro ⟨r, hr, x, hx, rfl⟩
    rcases hx with ⟨θ, hθ, rfl⟩
    rcases hθ with ⟨hθ_source, hθA⟩
    refine ⟨(r, (stereographic' n v) θ), ?_, ?_⟩
    · exact ⟨hr, hθA⟩
    · exact stereographicPolarPatchMap_apply_chart (n := n) v hθ_source r

/--
%%handwave
name:
  Vertical lines map to radial lines
statement:
  For every \(r,t\in\mathbb R\) and stereographic coordinate \(y\),
  \[
    \Phi_v((r,y)+t(1,0))=\Phi_v(r,y)+t\,\sigma_v(y).
  \]
proof:
  Expand the polar patch and use distributivity of scalar multiplication over addition.
-/
private theorem stereographicPolarPatchMap_vertical_segment
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (r t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    stereographicPolarPatchMap v
        (((r, y) : ℝ × EuclideanSpace ℝ (Fin n)) +
          t • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))) =
      stereographicPolarPatchMap v (r, y) +
        t • ((stereographic' n v).symm y : H) := by
  simp [stereographicPolarPatchMap, add_smul]

/--
%%handwave
name:
  Affine radial interpolation in a polar patch
statement:
  For \(r,s,u\in\mathbb R\),
  \[
    \Phi_v(r+u(s-r),y)=\Phi_v(r,y)+u(s-r)\,\sigma_v(y).
  \]
proof:
  Apply the vertical-line formula with displacement \(u(s-r)\).
-/
private theorem stereographicPolarPatchMap_vertical_affine
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (r s u : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    stereographicPolarPatchMap v (r + u * (s - r), y) =
      stereographicPolarPatchMap v (r, y) +
        (u * (s - r)) • ((stereographic' n v).symm y : H) := by
  simpa [Prod.smul_mk, smul_eq_mul] using
    stereographicPolarPatchMap_vertical_segment
      (n := n) v r (u * (s - r)) y

/--
%%handwave
name:
  Initial endpoint of radial interpolation
statement:
  The affine radial path satisfies \(\Phi_v(r+0(s-r),y)=\Phi_v(r,y)\).
proof:
  Simplify the zero scalar and the resulting sum.
-/
private theorem stereographicPolarPatchMap_vertical_affine_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (r s : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    stereographicPolarPatchMap v (r + (0 : ℝ) * (s - r), y) =
      stereographicPolarPatchMap v (r, y) := by
  simp

/--
%%handwave
name:
  Final endpoint of radial interpolation
statement:
  The affine radial path satisfies \(\Phi_v(r+1(s-r),y)=\Phi_v(s,y)\).
proof:
  Simplify \(r+(s-r)=s\).
-/
private theorem stereographicPolarPatchMap_vertical_affine_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (r s : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    stereographicPolarPatchMap v (r + (1 : ℝ) * (s - r), y) =
      stereographicPolarPatchMap v (s, y) := by
  simp [stereographicPolarPatchMap_apply]

/--
%%handwave
name:
  Continuity of the stereographic polar patch
statement:
  The map \(\Phi_v:\mathbb R\times\mathbb R^n\to H\), \((r,y)\mapsto r\,\sigma_v(y)\), is continuous.
proof:
  Inverse stereographic projection is continuous, as is scalar multiplication; compose these maps with the two coordinate projections.
-/
private theorem continuous_stereographicPolarPatchMap
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    Continuous (stereographicPolarPatchMap (n := n) v) := by
  have hsymm_cont :
      Continuous
        (fun y : EuclideanSpace ℝ (Fin n) =>
          ((stereographic' n v).symm y : H)) := by
    have hsymm_sphere :
        Continuous
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (stereographic' n v).symm y) := by
      apply continuousOn_univ.mp
      simpa [stereographic'_target] using
        (stereographic' n v).continuousOn_symm
    exact continuous_subtype_val.comp hsymm_sphere
  exact continuous_fst.smul (hsymm_cont.comp continuous_snd)

/--
%%handwave
name:
  Smoothness of inverse stereographic projection
statement:
  The ambient-space-valued map \(y\mapsto\sigma_v(y)\) from \(\mathbb R^n\) to \(H\) is smooth.
proof:
  Inverse stereographic projection is smooth as a map into the sphere, and the inclusion of the sphere into \(H\) is smooth.
-/
private theorem contDiff_stereographic'_symm_coe
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    ContDiff ℝ ⊤
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ((stereographic' n v).symm y : H)) := by
  let U : (ℝ ∙ (v : H))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
      (ne_zero_of_mem_unit_sphere v)).repr
  have h :
      ContDiff ℝ ⊤
        ((stereoInvFunAux (v : H) ∘
            ((↑) : (ℝ ∙ (v : H))ᗮ → H)) ∘ U.symm) :=
    ((contDiff_stereoInvFunAux (m := ⊤) (v := (v : H))).comp
        (ℝ ∙ (v : H))ᗮ.subtypeL.contDiff).comp U.symm.contDiff
  simpa [Function.comp_def, U, stereographic'_symm_apply,
    stereoInvFunAux_apply] using h

/--
%%handwave
name:
  Smoothness of the stereographic polar patch
statement:
  The polar patch \(\Phi_v(r,y)=r\,\sigma_v(y)\) is smooth on \(\mathbb R\times\mathbb R^n\).
proof:
  The first coordinate and the inverse stereographic direction are smooth, and scalar multiplication is a smooth bilinear operation.
-/
private theorem contDiff_stereographicPolarPatchMap
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    ContDiff ℝ ⊤ (stereographicPolarPatchMap (n := n) v) := by
  have hsymm :
      ContDiff ℝ ⊤
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((stereographic' n v).symm p.2 : H)) :=
    (contDiff_stereographic'_symm_coe (n := n) v).comp contDiff_snd
  simpa [stereographicPolarPatchMap] using contDiff_fst.smul hsymm

/--
%%handwave
name:
  Radial derivative of a stereographic polar patch
statement:
  At every \((r,y)\), the derivative of \(\Phi_v\) in the first-coordinate direction \((1,0)\) is the unit vector \(\sigma_v(y)\).
proof:
  Differentiate \(\Phi_v(r,y)=r\,\sigma_v(y)\).  The angular factor has zero derivative in the first-coordinate direction, while the derivative of \(r\) is \(1\).
-/
private theorem fderiv_stereographicPolarPatchMap_firstCoordinate
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (stereographicPolarPatchMap (n := n) v) p)
        ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) =
      (((stereographic' n v).symm p.2 : Metric.sphere (0 : H) 1) : H) := by
  have hsymm_diff :
      DifferentiableAt ℝ
        (fun y : EuclideanSpace ℝ (Fin n) =>
          ((stereographic' n v).symm y : H)) p.2 :=
    ((contDiff_stereographic'_symm_coe (n := n) v).differentiable
      (by simp)).differentiableAt
  have hsymm_prod_diff :
      DifferentiableAt ℝ
        (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((stereographic' n v).symm q.2 : H)) p :=
    hsymm_diff.comp p differentiableAt_snd
  have hfst_diff :
      DifferentiableAt ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin n) => q.1) p :=
    differentiableAt_fst
  have hsymm_prod_zero :
      (fderiv ℝ
          (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((stereographic' n v).symm q.2 : H)) p)
          ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) = 0 := by
    rw [fderiv_comp' (x := p)
      (g := fun y : EuclideanSpace ℝ (Fin n) =>
        (((stereographic' n v).symm y : Metric.sphere (0 : H) 1) : H))
      (f := fun q : ℝ × EuclideanSpace ℝ (Fin n) => q.2)
      hsymm_diff differentiableAt_snd]
    simp [fderiv_snd]
  change
    (fderiv ℝ
        (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          q.1 • (((stereographic' n v).symm q.2 :
            Metric.sphere (0 : H) 1) : H)) p)
        ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) =
      (((stereographic' n v).symm p.2 : Metric.sphere (0 : H) 1) : H)
  rw [show
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          q.1 • (((stereographic' n v).symm q.2 :
            Metric.sphere (0 : H) 1) : H)) =
        ((fun q : ℝ × EuclideanSpace ℝ (Fin n) => q.1) •
          fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
            (((stereographic' n v).symm q.2 :
              Metric.sphere (0 : H) 1) : H)) by
    rfl, fderiv_smul hfst_diff hsymm_prod_diff]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    fderiv_fst, hsymm_prod_zero]

/--
%%handwave
name:
  Radial component of a pulled-back covector field
statement:
  For a covector field \(dw\), the pullback through \(\Phi_v\), evaluated on \((1,0)\) at \(p=(r,y)\), is
  \[
    dw(\Phi_v(p))\big(\sigma_v(y)\big).
  \]
proof:
  Expand the composition of continuous linear maps and use that \(D\Phi_v(p)(1,0)=\sigma_v(y)\).
-/
private theorem stereographicPolarPatchMap_pullback_firstCoordinate_derivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (dw : H → H →L[ℝ] ℝ)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    ((dw (stereographicPolarPatchMap (n := n) v p)).comp
        (fderiv ℝ (stereographicPolarPatchMap (n := n) v) p))
        ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) =
      dw (stereographicPolarPatchMap v p)
        (((stereographic' n v).symm p.2 : Metric.sphere (0 : H) 1) : H) := by
  rw [ContinuousLinearMap.comp_apply,
    fderiv_stereographicPolarPatchMap_firstCoordinate]

private noncomputable def stereographicPolarPatchUnit
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : Metric.sphere (0 : H) 1) (z : H) :
    Metric.sphere (0 : H) 1 :=
  by
    classical
    exact
      if hz : z = 0 then v else
        ⟨(‖z‖⁻¹ : ℝ) • z, by
          have hnorm_ne : ‖z‖ ≠ 0 := by
            simpa [norm_eq_zero] using hz
          have hnorm :
              ‖(‖z‖⁻¹ : ℝ) • z‖ = (1 : ℝ) := by
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
            field_simp [hnorm_ne]
          simpa [Metric.mem_sphere, dist_eq_norm] using hnorm⟩

private noncomputable def stereographicPolarPatchInv
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) (z : H) :
    ℝ × EuclideanSpace ℝ (Fin n) :=
  (‖z‖, (stereographic' n v) (stereographicPolarPatchUnit v z))

/--
%%handwave
name:
  Normalizing a positive polar point recovers its direction
statement:
  If \(r>0\), then the unit normalization of \(\Phi_v(r,y)\) is \(\sigma_v(y)\).
proof:
  Since \(\|\Phi_v(r,y)\|=r\ne0\), normalization gives \(r^{-1}(r\,\sigma_v(y))=\sigma_v(y)\).
-/
private theorem stereographicPolarPatchUnit_apply_map
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {r : ℝ} (hr : 0 < r) (y : EuclideanSpace ℝ (Fin n)) :
    stereographicPolarPatchUnit v (stereographicPolarPatchMap v (r, y)) =
      (stereographic' n v).symm y := by
  apply Subtype.ext
  have hnorm :
      ‖stereographicPolarPatchMap v (r, y)‖ = r := by
    rw [norm_stereographicPolarPatchMap (n := n) v r y,
      abs_of_pos hr]
  have hz_ne :
      stereographicPolarPatchMap v (r, y) ≠ (0 : H) := by
    intro hz
    have hnorm_zero :
        ‖stereographicPolarPatchMap v (r, y)‖ = (0 : ℝ) := by
      rw [hz, norm_zero]
    linarith
  let σ : H := ((stereographic' n v).symm y : H)
  have hσ_norm : ‖σ‖ = (1 : ℝ) := by
    dsimp [σ]
    exact norm_stereographic'_symm (n := n) v y
  have hscaled_ne : r • σ ≠ (0 : H) := by
    simpa [σ, stereographicPolarPatchMap_apply] using hz_ne
  have hscaled_ne' :
      r • ((stereographic' n v).symm y : H) ≠ (0 : H) := by
    simpa [σ] using hscaled_ne
  have hcoef : (‖r • σ‖⁻¹ * r : ℝ) = 1 := by
    rw [norm_smul, hσ_norm, mul_one, Real.norm_of_nonneg hr.le]
    exact inv_mul_cancel₀ (ne_of_gt hr)
  rw [stereographicPolarPatchUnit]
  simp only [stereographicPolarPatchMap_apply]
  rw [dif_neg hscaled_ne']
  change
    (‖r • ((stereographic' n v).symm y : H)‖⁻¹ • r •
        ((stereographic' n v).symm y : H)) =
      ((stereographic' n v).symm y : H)
  change ((‖r • σ‖⁻¹ : ℝ) • (r • σ)) = σ
  rw [smul_smul, hcoef, one_smul]

/--
%%handwave
name:
  The polar coordinate map is a left inverse on positive radii
statement:
  If \(r>0\), the radius-and-stereographic-coordinate map sends \(\Phi_v(r,y)\) back to \((r,y)\).
proof:
  The norm of \(\Phi_v(r,y)\) is \(r\), its normalized direction is \(\sigma_v(y)\), and stereographic projection inverts \(\sigma_v\).
-/
private theorem stereographicPolarPatchInv_apply_map
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {r : ℝ} (hr : 0 < r) (y : EuclideanSpace ℝ (Fin n)) :
    stereographicPolarPatchInv v (stereographicPolarPatchMap v (r, y)) =
      (r, y) := by
  ext
  · simp [stereographicPolarPatchInv,
      norm_stereographicPolarPatchMap (n := n) v r y, abs_of_pos hr]
  · have htarget : y ∈ (stereographic' n v).target := by
      simp [stereographic'_target]
    simp [stereographicPolarPatchInv,
      stereographicPolarPatchUnit_apply_map (n := n) v hr y,
      (stereographic' n v).right_inv htarget]

/--
%%handwave
name:
  The polar inverse map is measurable
statement:
  The map sending a nonzero point of the ball to its radius and
  stereographic angular coordinate is Borel measurable.
proof:
  The radius is continuous.  The angular part is the normalized direction,
  followed by stereographic projection.  Normalization is continuous away from
  the origin and the origin is a singleton, while stereographic projection is
  continuous away from its pole and the pole is again a singleton.  Changing a
  function on these negligible closed pieces preserves Borel measurability.
-/
private theorem measurable_stereographicPolarPatchInv
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    Measurable (stereographicPolarPatchInv (n := n) v) := by
  classical
  have hst :
      Measurable (stereographic' n v : Metric.sphere (0 : H) 1 →
        EuclideanSpace ℝ (Fin n)) := by
    have hcont :
        ContinuousOn (stereographic' n v)
          ({v}ᶜ : Set (Metric.sphere (0 : H) 1)) := by
      simpa [stereographic'_source] using
        (stereographic' n v).continuousOn
    exact measurable_of_continuousOn_compl_singleton v hcont
  have hunit_val :
      Measurable (fun z : H =>
        if hz : z = 0 then (v : H) else (‖z‖⁻¹ : ℝ) • z) := by
    refine Measurable.ite (measurableSet_singleton (0 : H))
      measurable_const ?_
    exact (measurable_inv.comp continuous_norm.measurable).smul measurable_id
  have hunit :
      Measurable (stereographicPolarPatchUnit v) := by
    have hmem :
        ∀ z : H,
          (if hz : z = 0 then (v : H) else (‖z‖⁻¹ : ℝ) • z) ∈
            Metric.sphere (0 : H) 1 := by
      intro z
      by_cases hz : z = 0
      · simpa [hz] using v.2
      · have hnorm_ne : ‖z‖ ≠ 0 := by
          simpa [norm_eq_zero] using hz
        have hnorm :
            ‖(‖z‖⁻¹ : ℝ) • z‖ = (1 : ℝ) := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
          field_simp [hnorm_ne]
        simpa [hz, Metric.mem_sphere, dist_eq_norm] using hnorm
    have hunit_eq :
        stereographicPolarPatchUnit v =
          fun z : H =>
            (⟨if hz : z = 0 then (v : H) else (‖z‖⁻¹ : ℝ) • z,
              hmem z⟩ : Metric.sphere (0 : H) 1) := by
      funext z
      by_cases hz : z = 0
      · simp [stereographicPolarPatchUnit, hz]
      · simp [stereographicPolarPatchUnit, hz]
    simpa [hunit_eq] using hunit_val.subtype_mk (h := hmem)
  have hangular :
      Measurable (fun z : H =>
        (stereographic' n v) (stereographicPolarPatchUnit v z)) :=
    hst.comp hunit
  simpa [stereographicPolarPatchInv] using
    continuous_norm.measurable.prod hangular

/--
%%handwave
name:
  Almost-everywhere measurability of a stereographic polar patch
statement:
  For every measure \(\mu\) on \(\mathbb R\times\mathbb R^n\), the polar patch \(\Phi_v\) is \(\mu\)-almost-everywhere measurable.
proof:
  The polar patch is continuous, hence Borel measurable, and every measurable map is almost-everywhere measurable for any measure.
-/
private theorem aemeasurable_stereographicPolarPatchMap
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (μ : Measure (ℝ × EuclideanSpace ℝ (Fin n))) :
    AEMeasurable (stereographicPolarPatchMap (n := n) v) μ :=
  (continuous_stereographicPolarPatchMap (n := n) v).measurable.aemeasurable

/--
%%handwave
name:
  A polar patch sends null angular cylinders to null sets
statement:
  If \(A\subseteq\mathbb R^n\) is Lebesgue-null, then \(\Phi_v((0,1)\times A)\) is Lebesgue-null in \(H\).
proof:
  The cylinder is null by the product-measure formula.  After identifying the domain linearly with \(H\), the polar patch is differentiable on the cylinder, so the differentiable image of this null set is null; the final linear coordinate change also preserves null sets.
-/
private theorem stereographicPolarPatchMap_image_volume_null_of_null
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))) A = 0) :
    (MeasureTheory.volume : Measure H)
        (stereographicPolarPatchMap v '' (Set.Ioo (0 : ℝ) 1 ×ˢ A)) = 0 := by
  classical
  let D : Type := ℝ × EuclideanSpace ℝ (Fin n)
  have hDdim : Module.finrank ℝ D = Module.finrank ℝ H := by
    have hHdim : Module.finrank ℝ H = n + 1 := Fact.out
    dsimp [D]
    rw [hHdim]
    simp
    omega
  let L : D ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq hDdim
  haveI hDhaar :
      Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure D) := by
    dsimp [D]
    rw [Measure.volume_eq_prod]
    infer_instance
  let S : Set D := Set.Ioo (0 : ℝ) 1 ×ˢ A
  have hS_zero : (MeasureTheory.volume : Measure D) S = 0 := by
    simpa [D, S] using volume_Ioo_prod_null_of_null (E :=
      EuclideanSpace ℝ (Fin n)) hA
  let g : D → D := fun p => L.symm (stereographicPolarPatchMap v p)
  have hg_diff : DifferentiableOn ℝ g S := by
    have hcont :
        ContDiff ℝ ⊤
          (fun p : D => L.symm (stereographicPolarPatchMap v p)) :=
      L.symm.contDiff.comp (contDiff_stereographicPolarPatchMap (n := n) v)
    exact (hcont.differentiable (by simp)).differentiableOn
  have hg_zero : (MeasureTheory.volume : Measure D) (g '' S) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (MeasureTheory.volume : Measure D) hg_diff hS_zero
  have hL_zero : (MeasureTheory.volume : Measure H) (L '' (g '' S)) = 0 :=
    continuousLinearEquiv_image_volume_null L hg_zero
  have himage :
      stereographicPolarPatchMap v '' S = L '' (g '' S) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨g p, ⟨p, hp, rfl⟩, by simp [g, L]⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, by simp [g, L]⟩
  simpa [S, himage] using hL_zero

/--
%%handwave
name:
  A polar patch preserves Lebesgue-null sets
statement:
  If \(S\subseteq\mathbb R\times\mathbb R^n\) is Lebesgue-null, then \(\Phi_v(S)\) is Lebesgue-null in \(H\).
proof:
  Identify the domain with \(H\) by a continuous linear equivalence.  In these coordinates the smooth polar patch maps null sets to null sets, and the linear equivalence preserves nullity.
-/
private theorem stereographicPolarPatchMap_image_volume_null
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {S : Set (ℝ × EuclideanSpace ℝ (Fin n))}
    (hS : (MeasureTheory.volume :
        Measure (ℝ × EuclideanSpace ℝ (Fin n))) S = 0) :
    (MeasureTheory.volume : Measure H)
        (stereographicPolarPatchMap v '' S) = 0 := by
  classical
  let D : Type := ℝ × EuclideanSpace ℝ (Fin n)
  have hDdim : Module.finrank ℝ D = Module.finrank ℝ H := by
    have hHdim : Module.finrank ℝ H = n + 1 := Fact.out
    dsimp [D]
    rw [hHdim]
    simp
    omega
  let L : D ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq hDdim
  haveI hDhaar :
      Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure D) := by
    dsimp [D]
    rw [Measure.volume_eq_prod]
    infer_instance
  let g : D → D := fun p => L.symm (stereographicPolarPatchMap v p)
  have hg_diff : DifferentiableOn ℝ g S := by
    have hcont :
        ContDiff ℝ ⊤
          (fun p : D => L.symm (stereographicPolarPatchMap v p)) :=
      L.symm.contDiff.comp (contDiff_stereographicPolarPatchMap (n := n) v)
    exact (hcont.differentiable (by simp)).differentiableOn
  have hg_zero : (MeasureTheory.volume : Measure D) (g '' S) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (MeasureTheory.volume : Measure D) hg_diff (by simpa [D] using hS)
  have hL_zero : (MeasureTheory.volume : Measure H) (L '' (g '' S)) = 0 :=
    continuousLinearEquiv_image_volume_null L hg_zero
  have himage :
      stereographicPolarPatchMap v '' S = L '' (g '' S) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨g p, ⟨p, hp, rfl⟩, by simp [g, L]⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, by simp [g, L]⟩
  simpa [himage] using hL_zero

/--
%%handwave
name:
  Ambient formula for stereographic coordinates
statement:
  If \(U:v^\perp\to\mathbb R^n\) is the chosen orthonormal coordinate map, then
  \[
    \operatorname{stereo}_v(\theta)
    =U\!\left(\frac{2}{1-\langle v,\theta\rangle}
      \operatorname{proj}_{v^\perp}\theta\right).
  \]
proof:
  Unfold the definition of the stereographic chart and the standard ambient stereographic formula.
-/
private theorem stereographic'_apply_eq_stereoToFun
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (θ : Metric.sphere (0 : H) 1) :
    (stereographic' n v) θ =
      (let U : (ℝ ∙ (v : H))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
        (OrthonormalBasis.fromOrthogonalSpanSingleton n
          (ne_zero_of_mem_unit_sphere v)).repr
      U (stereoToFun (v : H) (θ : H))) := by
  let U : (ℝ ∙ (v : H))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
      (ne_zero_of_mem_unit_sphere v)).repr
  change U ((2 / (1 - innerSL ℝ (v : H) (θ : H))) •
      (ℝ ∙ (v : H))ᗮ.orthogonalProjection (θ : H)) =
    U (stereoToFun (v : H) (θ : H))
  simp [stereoToFun_apply]

/--
%%handwave
name:
  The inverse polar chart is differentiable at regular points
statement:
  At every nonzero point whose unit direction is not the stereographic pole,
  the coordinate map \(z\mapsto (|z|,\operatorname{stereo}(z/|z|))\),
  followed by a fixed linear coordinate equivalence, is differentiable.
proof:
  Near such a point the norm is positive and the unit direction remains in the
  stereographic source.  Hence the map is locally the product of the smooth
  norm, the smooth normalization \(z\mapsto z/|z|\), and stereographic
  projection, followed by a linear equivalence.
-/
private theorem contDiffAt_stereographicPolarPatchInv_of_mem_source
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (L : (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] H)
    {z : H}
    (hz : z ≠ 0)
    (hsource : stereographicPolarPatchUnit v z ∈
      (stereographic' n v).source) :
    ContDiffAt ℝ ⊤
      (fun z : H => L (stereographicPolarPatchInv (n := n) v z)) z := by
  classical
  let U : (ℝ ∙ (v : H))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
      (ne_zero_of_mem_unit_sphere v)).repr
  let ξ : H := (‖z‖⁻¹ : ℝ) • z
  have hunit_z :
      (stereographicPolarPatchUnit v z : H) = ξ := by
    simp [stereographicPolarPatchUnit, hz, ξ]
  have hunit_ne_v : stereographicPolarPatchUnit v z ≠ v := by
    simpa [stereographic'_source] using hsource
  have hξ_ne_v : ξ ≠ (v : H) := by
    intro hξ
    apply hunit_ne_v
    apply Subtype.ext
    simpa [hunit_z] using hξ
  have hξ_norm : ‖ξ‖ = (1 : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm, hunit_z] using
      (stereographicPolarPatchUnit v z).2
  have hv_norm : ‖(v : H)‖ = (1 : ℝ) :=
    norm_eq_of_mem_sphere v
  have hstereo_source : ξ ∈ {x : H | innerSL ℝ (v : H) x ≠ (1 : ℝ)} := by
    intro hinner
    have hv_eq_ξ : (v : H) = ξ :=
      (inner_eq_one_iff_of_norm_eq_one hv_norm hξ_norm).mp hinner
    exact hξ_ne_v hv_eq_ξ.symm
  have hnorm_cd :
      ContDiffAt ℝ ⊤ (fun w : H => ‖w‖) z :=
    contDiffAt_norm ℝ hz
  have hnorm_ne : ‖z‖ ≠ (0 : ℝ) := by
    simpa [norm_eq_zero] using hz
  have hunit_raw_cd :
      ContDiffAt ℝ ⊤ (fun w : H => (‖w‖⁻¹ : ℝ) • w) z :=
    hnorm_cd.inv hnorm_ne |>.smul contDiffAt_id
  have hstereo_cd :
      ContDiffAt ℝ ⊤ (stereoToFun (v : H)) ξ := by
    have hopen :
        IsOpen {x : H | innerSL ℝ (v : H) x ≠ (1 : ℝ)} := by
      simpa [Set.preimage, Set.mem_compl_iff] using
        ((innerSL ℝ (v : H)).continuous.isOpen_preimage
          ({(1 : ℝ)}ᶜ : Set ℝ) isOpen_compl_singleton)
    exact
      (contDiffOn_stereoToFun (v := (v : H)) (n := (⊤ : WithTop ℕ∞))).contDiffAt
        (hopen.mem_nhds hstereo_source)
  have hstereo_comp_cd :
      ContDiffAt ℝ ⊤
        (fun w : H => stereoToFun (v : H) ((‖w‖⁻¹ : ℝ) • w)) z := by
    let N : H → H := fun w => (‖w‖⁻¹ : ℝ) • w
    have hN_cd : ContDiffAt ℝ ⊤ N z := by
      simpa [N] using hunit_raw_cd
    have hNz : N z = ξ := rfl
    have hcomp : ContDiffAt ℝ ⊤ ((stereoToFun (v : H)) ∘ N) z := by
      rw [← contDiffWithinAt_univ]
      exact
        hstereo_cd.comp_contDiffWithinAt_of_eq (f := N) (s := Set.univ)
          z hN_cd.contDiffWithinAt hNz
    simpa [Function.comp_def, N] using hcomp
  have hangular_cd :
      ContDiffAt ℝ ⊤
        (fun w : H =>
          U (stereoToFun (v : H) ((‖w‖⁻¹ : ℝ) • w))) z :=
    U.contDiff.contDiffAt.comp z hstereo_comp_cd
  have hmodel_cd :
      ContDiffAt ℝ ⊤
        (fun w : H =>
          L (‖w‖,
            U (stereoToFun (v : H) ((‖w‖⁻¹ : ℝ) • w)))) z :=
    L.contDiff.contDiffAt.comp z (hnorm_cd.prodMk hangular_cd)
  have heq :
      (fun w : H => L (stereographicPolarPatchInv (n := n) v w)) =ᶠ[𝓝 z]
        (fun w : H =>
          L (‖w‖,
            U (stereoToFun (v : H) ((‖w‖⁻¹ : ℝ) • w)))) := by
    have hne_eventually : ∀ᶠ w : H in 𝓝 z, w ≠ 0 :=
      (isOpen_compl_singleton.mem_nhds (by simpa using hz))
    filter_upwards [hne_eventually] with w hw
    congr 1
    apply Prod.ext
    · rfl
    · have hstereo :=
        stereographic'_apply_eq_stereoToFun (n := n) v
          (stereographicPolarPatchUnit v w)
      simpa [U, stereographicPolarPatchInv, stereographicPolarPatchUnit, hw] using
        hstereo
  exact hmodel_cd.congr_of_eventuallyEq heq

/--
%%handwave
name:
  Differentiability of inverse polar coordinates at regular points
statement:
  Let \(L:\mathbb R\times\mathbb R^n\to H\) be a continuous linear equivalence.  At every nonzero \(z\) whose normalized direction lies in the stereographic source, the map
  \[
    z\longmapsto L\big(\|z\|,\operatorname{stereo}_v(z/\|z\|)\big)
  \]
  is differentiable.
proof:
  The same map is smooth at such a point: the norm and normalization are smooth away from zero, stereographic projection is smooth away from its pole, and \(L\) is linear.  Smoothness implies differentiability.
-/
private theorem differentiableAt_stereographicPolarPatchInv_of_mem_source
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (L : (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] H)
    {z : H}
    (hz : z ≠ 0)
    (hsource : stereographicPolarPatchUnit v z ∈
      (stereographic' n v).source) :
    DifferentiableAt ℝ
      (fun z : H => L (stereographicPolarPatchInv (n := n) v z)) z :=
  (contDiffAt_stereographicPolarPatchInv_of_mem_source
    (n := n) v L hz hsource).differentiableAt (by simp)

/--
%%handwave
name:
  The inverse polar chart is smooth on radial stereographic chart-cones
statement:
  On the image of a product cylinder \((0,1)\times A\) under the map
  \((r,y)\mapsto r\sigma(y)\), the inverse coordinate map
  \(z\mapsto (|z|,\operatorname{stereo}(z/|z|))\), followed by any fixed
  linear coordinate equivalence, is differentiable.
proof:
  Points in the image have positive radius and their unit directions lie in
  the stereographic source.  On a neighborhood of each such point,
  normalization \(z\mapsto z/|z|\), stereographic projection on the sphere,
  and the radius map are smooth, so their product is differentiable.
-/
private theorem differentiableOn_stereographicPolarPatchInv_image_Ioo_prod
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (L : (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] H)
    {A : Set (EuclideanSpace ℝ (Fin n))} :
    DifferentiableOn ℝ
      (fun z : H => L (stereographicPolarPatchInv (n := n) v z))
      (stereographicPolarPatchMap v ''
        (Set.Ioo (0 : ℝ) 1 ×ˢ A)) := by
  classical
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩
  rcases p with ⟨r, y⟩
  rcases hp with ⟨hr, _hyA⟩
  have hz_ne :
      stereographicPolarPatchMap (n := n) v (r, y) ≠ (0 : H) := by
    intro hz0
    have hnorm_zero :
        ‖stereographicPolarPatchMap (n := n) v (r, y)‖ = (0 : ℝ) := by
      rw [hz0, norm_zero]
    have hnorm_pos :
        ‖stereographicPolarPatchMap (n := n) v (r, y)‖ = r := by
      rw [norm_stereographicPolarPatchMap (n := n) v r y,
        abs_of_pos hr.1]
    have hr_zero : r = 0 := by
      rw [← hnorm_pos, hnorm_zero]
    exact (ne_of_gt hr.1) hr_zero
  have hsource :
      stereographicPolarPatchUnit v
          (stereographicPolarPatchMap (n := n) v (r, y)) ∈
        (stereographic' n v).source := by
    have htarget : y ∈ (stereographic' n v).target := by
      simp [stereographic'_target]
    simpa [stereographicPolarPatchUnit_apply_map (n := n) v hr.1 y] using
      (stereographic' n v).map_target htarget
  exact
    (differentiableAt_stereographicPolarPatchInv_of_mem_source
      (n := n) v L hz_ne hsource).differentiableWithinAt

/--
%%handwave
name:
  Null chart-cones pull back through stereographic polar coordinates
statement:
  If the image of a radial stereographic product cylinder
  \((0,1)\times A\) has zero Euclidean measure in the ambient space, then
  the product cylinder itself has zero product Lebesgue measure.
proof:
  On the image of the cylinder the inverse map is explicitly
  \(z\mapsto (|z|,\operatorname{stereo}(z/|z|))\).  This map is smooth away
  from the origin and from the stereographic pole.  Since the cylinder uses
  positive radii and directions in the chart source, the inverse map sends
  ambient null sets in the chart cone to product null sets.  Applying it to
  the null image of \((0,1)\times A\) and using that it is a left inverse on
  the cylinder gives the result.
-/
private theorem stereographicPolarPatchMap_Ioo_prod_volume_null_of_image_null
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {A : Set (EuclideanSpace ℝ (Fin n))}
    (himage :
      (MeasureTheory.volume : Measure H)
        (stereographicPolarPatchMap v ''
          (Set.Ioo (0 : ℝ) 1 ×ˢ A)) = 0) :
    (MeasureTheory.volume : Measure (ℝ × EuclideanSpace ℝ (Fin n)))
      (Set.Ioo (0 : ℝ) 1 ×ˢ A) = 0 := by
  classical
  let D : Type := ℝ × EuclideanSpace ℝ (Fin n)
  have hDdim : Module.finrank ℝ D = Module.finrank ℝ H := by
    have hHdim : Module.finrank ℝ H = n + 1 := Fact.out
    dsimp [D]
    rw [hHdim]
    simp
    omega
  let L : D ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq hDdim
  haveI hDhaar :
      Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure D) := by
    dsimp [D]
    rw [Measure.volume_eq_prod]
    infer_instance
  let S : Set D := Set.Ioo (0 : ℝ) 1 ×ˢ A
  let I : Set H := stereographicPolarPatchMap v '' S
  let F : H → H := fun z => L (stereographicPolarPatchInv (n := n) v z)
  have hF_diff : DifferentiableOn ℝ F I := by
    simpa [F, I, S, D] using
      differentiableOn_stereographicPolarPatchInv_image_Ioo_prod
        (n := n) v L (A := A)
  have hF_zero :
      (MeasureTheory.volume : Measure H) (F '' I) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (MeasureTheory.volume : Measure H) hF_diff (by simpa [I, S] using himage)
  have hinv_image_zero :
      (MeasureTheory.volume : Measure D)
        (stereographicPolarPatchInv (n := n) v '' I) = 0 := by
    have hlinear_zero :
        (MeasureTheory.volume : Measure D)
          (L.symm '' (F '' I)) = 0 :=
      continuousLinearEquiv_image_volume_null L.symm hF_zero
    have himage_eq :
        stereographicPolarPatchInv (n := n) v '' I =
          L.symm '' (F '' I) := by
      ext q
      constructor
      · rintro ⟨z, hzI, rfl⟩
        exact ⟨F z, ⟨z, hzI, rfl⟩, by simp [F, L]⟩
      · rintro ⟨w, ⟨z, hzI, rfl⟩, rfl⟩
        exact ⟨z, hzI, by simp [F, L]⟩
    simpa [himage_eq] using hlinear_zero
  have hS_subset :
      S ⊆ stereographicPolarPatchInv (n := n) v '' I := by
    intro p hp
    refine ⟨stereographicPolarPatchMap v p, ⟨p, hp, rfl⟩, ?_⟩
    exact stereographicPolarPatchInv_apply_map (n := n) v hp.1.1 p.2
  exact measure_mono_null hS_subset hinv_image_zero

/--
%%handwave
name:
  Measurability of a stereographic chart pullback
statement:
  If \(A\subseteq\mathbb R^n\) is measurable, then
  \[
    \{\theta\in\mathbb S:\theta\ne v,\ \operatorname{stereo}_v(\theta)\in A\}
  \]
  is measurable on the sphere.
proof:
  The stereographic source is open, and the chart is continuous on that source.  Its relative preimage of \(A\) is therefore measurable.
-/
private theorem stereographic_source_inter_preimage_measurable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    MeasurableSet
      ((stereographic' n v).source ∩ (stereographic' n v) ⁻¹' A) := by
  classical
  let e := stereographic' n v
  have hsource : MeasurableSet e.source := e.open_source.measurableSet
  let B : Set e.target := {y | (y : EuclideanSpace ℝ (Fin n)) ∈ A}
  have hB : MeasurableSet B := hA.preimage measurable_subtype_coe
  have hpre : MeasurableSet (e.toHomeomorphSourceTarget ⁻¹' B) :=
    e.toHomeomorphSourceTarget.measurable hB
  have himage :
      MeasurableSet
        (((↑) : e.source → Metric.sphere (0 : H) 1) ''
          (e.toHomeomorphSourceTarget ⁻¹' B)) :=
    (MeasurableEmbedding.subtype_coe hsource).measurableSet_image' hpre
  have hset :
      (((↑) : e.source → Metric.sphere (0 : H) 1) ''
          (e.toHomeomorphSourceTarget ⁻¹' B)) =
        e.source ∩ e ⁻¹' A := by
    ext θ
    constructor
    · rintro ⟨θ', hθ', rfl⟩
      exact ⟨θ'.property, by simpa [B, e] using hθ'⟩
    · rintro ⟨hθ_source, hθA⟩
      refine ⟨⟨θ, hθ_source⟩, ?_, rfl⟩
      simpa [B, e] using hθA
  have hgoal : MeasurableSet (e.source ∩ e ⁻¹' A) := by
    rw [← hset]
    exact himage
  simpa [e] using hgoal

/--
%%handwave
name:
  Stereographic coordinates preserve null sets on the sphere
statement:
  On a stereographic coordinate patch of the unit sphere, the push-forward of
  spherical measure is absolutely continuous with respect to Lebesgue measure
  in the Euclidean coordinate space.
proof:
  Use the explicit inverse stereographic formula.  In these coordinates the
  spherical measure has a smooth density with respect to Lebesgue measure.
  Equivalently, the image under the smooth inverse stereographic
  parametrization of a Lebesgue-null coordinate set has zero spherical
  measure, by the area formula.
-/
theorem stereographic_toSphere_restrict_chart_map_absolutelyContinuous_volume
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    Measure.map (stereographic' n v)
        ((MeasureTheory.volume : Measure H).toSphere.restrict
          (stereographic' n v).source) ≪
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  intro A hA
  let ν : Measure (EuclideanSpace ℝ (Fin n)) := MeasureTheory.volume
  let T : Set (EuclideanSpace ℝ (Fin n)) := MeasureTheory.toMeasurable ν A
  have hAT : A ⊆ T := subset_toMeasurable ν A
  have hT_meas : MeasurableSet T := measurableSet_toMeasurable ν A
  have hT_zero : ν T = 0 := by
    rw [measure_toMeasurable]
    exact hA
  have hmap_T_zero :
      Measure.map (stereographic' n v)
          ((MeasureTheory.volume : Measure H).toSphere.restrict
            (stereographic' n v).source) T = 0 := by
    have he_aemeas :
        AEMeasurable (stereographic' n v)
          ((MeasureTheory.volume : Measure H).toSphere.restrict
            (stereographic' n v).source) :=
      openPartialHomeomorph_aemeasurable_restrict_source
        (stereographic' n v) ((MeasureTheory.volume : Measure H).toSphere)
    rw [Measure.map_apply_of_aemeasurable he_aemeas hT_meas]
    have hsource_meas : MeasurableSet (stereographic' n v).source :=
      (stereographic' n v).open_source.measurableSet
    rw [Measure.restrict_apply' hsource_meas]
    have hpre_meas :
        MeasurableSet
          ((stereographic' n v).source ∩ (stereographic' n v) ⁻¹' T) :=
      stereographic_source_inter_preimage_measurable (n := n) v hT_meas
    have hset :
        (stereographic' n v ⁻¹' T) ∩ (stereographic' n v).source =
          (stereographic' n v).source ∩ (stereographic' n v) ⁻¹' T := by
      ext θ
      simp [and_comm]
    rw [hset]
    have hcone_zero :
        (MeasureTheory.volume : Measure H)
          (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' ((stereographic' n v).source ∩
              (stereographic' n v) ⁻¹' T))) = 0 := by
      rw [← stereographicPolarPatchMap_image_Ioo_prod_eq_cone_chart_preimage
        (n := n) v T]
      exact stereographicPolarPatchMap_image_volume_null_of_null (n := n) v hT_zero
    rw [MeasureTheory.Measure.toSphere_apply'
      (μ := (MeasureTheory.volume : Measure H)) (hs := hpre_meas),
      hcone_zero, mul_zero]
  exact le_antisymm
    (le_trans (measure_mono hAT) (le_of_eq hmap_T_zero)) zero_le

/--
%%handwave
name:
  Stereographic coordinates express spherical measure by a density
statement:
  On a stereographic coordinate patch of the unit sphere, the push-forward
  of spherical measure is Lebesgue measure multiplied by a nonnegative
  measurable density in the Euclidean coordinate space.
proof:
  Use the absolute continuity of the coordinate push-forward measure with
  respect to Lebesgue measure and apply the Radon-Nikodym theorem.
-/
theorem stereographic_toSphere_restrict_chart_map_eq_withDensity
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞,
      Measure.map (stereographic' n v)
          ((MeasureTheory.volume : Measure H).toSphere.restrict
            (stereographic' n v).source) =
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity ρ := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    Measure.map (stereographic' n v)
      ((MeasureTheory.volume : Measure H).toSphere.restrict
        (stereographic' n v).source)
  let ν : Measure (EuclideanSpace ℝ (Fin n)) :=
    MeasureTheory.volume
  refine ⟨μ.rnDeriv ν, ?_⟩
  have hμν : μ ≪ ν := by
    simpa [μ, ν] using
      stereographic_toSphere_restrict_chart_map_absolutelyContinuous_volume
        (n := n) v
  have hsing : μ.singularPart ν = 0 :=
    Measure.singularPart_eq_zero_of_ac hμν
  have hdec : μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
    Measure.haveLebesgueDecomposition_add μ ν
  rw [hsing, zero_add] at hdec
  simpa [μ, ν] using hdec

/--
%%handwave
name:
  Transfer of almost-everywhere properties to a stereographic sphere patch
statement:
  If \(P(y)\) holds for Lebesgue-almost every \(y\in\mathbb R^n\), then \(P(\operatorname{stereo}_v(\theta))\) holds for spherical-almost every \(\theta\ne v\), with spherical measure restricted to the stereographic source.
proof:
  The exceptional coordinate set is Lebesgue-null.  Its product with \(0<r<1\) is null, and the smooth polar patch sends this cylinder to the cone over the exceptional sphere directions.  The polar definition of spherical measure then makes that angular exceptional set null.
-/
private theorem ae_stereographic_toSphere_restrict_of_ae_volume
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {P : EuclideanSpace ℝ (Fin n) → Prop}
    (hP : ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
      P y) :
    ∀ᵐ θ : Metric.sphere (0 : H) 1
        ∂((MeasureTheory.volume : Measure H).toSphere.restrict
          (stereographic' n v).source),
      P ((stereographic' n v) θ) := by
  have he_aemeas :
      AEMeasurable (stereographic' n v)
        ((MeasureTheory.volume : Measure H).toSphere.restrict
          (stereographic' n v).source) :=
    openPartialHomeomorph_aemeasurable_restrict_source
      (stereographic' n v) ((MeasureTheory.volume : Measure H).toSphere)
  have hmap_ac :
      Measure.map (stereographic' n v)
          ((MeasureTheory.volume : Measure H).toSphere.restrict
            (stereographic' n v).source) ≪
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    stereographic_toSphere_restrict_chart_map_absolutelyContinuous_volume
      (n := n) v
  exact MeasureTheory.ae_of_ae_map he_aemeas (hmap_ac.ae_le hP)

/--
%%handwave
name:
  Stereographic coordinates have no vanishing density
statement:
  In a stereographic chart on the unit sphere, Lebesgue measure in the
  coordinate space is absolutely continuous with respect to the push-forward
  of spherical measure restricted to the chart source.
proof:
  If the chart push-forward of a coordinate set is zero, then the
  corresponding subset of the sphere has zero spherical measure.  Coning this
  subset over any fixed radial interval gives a Haar-null subset of the
  Euclidean ball.  Applying the inverse polar-stereographic coordinate map,
  which is smooth on that annulus, shows that the product of the radial
  interval with the coordinate set is null; since the radial interval has
  positive finite measure, the coordinate set itself is null.
-/
private theorem volume_absolutelyContinuous_stereographic_toSphere_restrict_chart_map_core
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))) ≪
      Measure.map (stereographic' n v)
        ((MeasureTheory.volume : Measure H).toSphere.restrict
          (stereographic' n v).source) := by
  classical
  intro A hA
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μchart : Measure (EuclideanSpace ℝ (Fin n)) :=
    Measure.map (stereographic' n v)
      (μS.restrict (stereographic' n v).source)
  let ν : Measure (EuclideanSpace ℝ (Fin n)) := MeasureTheory.volume
  let T : Set (EuclideanSpace ℝ (Fin n)) := MeasureTheory.toMeasurable μchart A
  have hAT : A ⊆ T := subset_toMeasurable μchart A
  have hT_meas : MeasurableSet T := measurableSet_toMeasurable μchart A
  have hT_zero : μchart T = 0 := by
    rw [measure_toMeasurable]
    exact hA
  have he_aemeas :
      AEMeasurable (stereographic' n v)
        (μS.restrict (stereographic' n v).source) :=
    openPartialHomeomorph_aemeasurable_restrict_source
      (stereographic' n v) μS
  have hpre_zero :
      μS ((stereographic' n v).source ∩
          (stereographic' n v) ⁻¹' T) = 0 := by
    have hmap_zero : μchart T = 0 := hT_zero
    rw [Measure.map_apply_of_aemeasurable he_aemeas hT_meas] at hmap_zero
    have hsource_meas : MeasurableSet (stereographic' n v).source :=
      (stereographic' n v).open_source.measurableSet
    rw [Measure.restrict_apply' hsource_meas] at hmap_zero
    simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hmap_zero
  have hpre_meas :
      MeasurableSet
        ((stereographic' n v).source ∩
          (stereographic' n v) ⁻¹' T) :=
    stereographic_source_inter_preimage_measurable (n := n) v hT_meas
  have hcone_zero :
      (MeasureTheory.volume : Measure H)
        (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' ((stereographic' n v).source ∩
            (stereographic' n v) ⁻¹' T))) = 0 := by
    have hto :=
      MeasureTheory.Measure.toSphere_apply'
        (μ := (MeasureTheory.volume : Measure H)) (hs := hpre_meas)
    rw [hto] at hpre_zero
    have hfin : Module.finrank ℝ H = n + 1 := Fact.out
    have hdim_ne_nat : Module.finrank ℝ H ≠ 0 := by
      omega
    have hdim_ne :
        (Module.finrank ℝ H : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hdim_ne_nat
    exact (mul_eq_zero.mp hpre_zero).resolve_left hdim_ne
  have himage_zero :
      (MeasureTheory.volume : Measure H)
        (stereographicPolarPatchMap v '' (Set.Ioo (0 : ℝ) 1 ×ˢ T)) = 0 := by
    rw [stereographicPolarPatchMap_image_Ioo_prod_eq_cone_chart_preimage
      (n := n) v T]
    exact hcone_zero
  have hprod_zero :
      (MeasureTheory.volume :
          Measure (ℝ × EuclideanSpace ℝ (Fin n)))
        (Set.Ioo (0 : ℝ) 1 ×ˢ T) = 0 :=
    stereographicPolarPatchMap_Ioo_prod_volume_null_of_image_null
      (n := n) v himage_zero
  have hT_volume_zero : ν T = 0 := by
    simpa [ν] using
      volume_null_of_Ioo_prod_null
        (E := EuclideanSpace ℝ (Fin n)) hprod_zero
  exact measure_mono_null hAT hT_volume_zero

/--
%%handwave
name:
  The stereographic chart density is nonzero almost everywhere
statement:
  The Radon-Nikodym density of spherical measure in a stereographic coordinate
  chart is nonzero for Lebesgue-almost every coordinate point.
proof:
  In stereographic coordinates the spherical measure has the explicit smooth
  positive density \(c(4+|y|^2)^{-m}\) with respect to Lebesgue measure.
  Hence its Radon-Nikodym derivative is positive, and in particular nonzero,
  almost everywhere.
-/
private theorem stereographic_toSphere_restrict_chart_rnDeriv_ne_zero_ae
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
      (Measure.map (stereographic' n v)
          ((MeasureTheory.volume : Measure H).toSphere.restrict
            (stereographic' n v).source)).rnDeriv
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))) y ≠ 0 := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    Measure.map (stereographic' n v)
      ((MeasureTheory.volume : Measure H).toSphere.restrict
        (stereographic' n v).source)
  let ν : Measure (EuclideanSpace ℝ (Fin n)) := MeasureTheory.volume
  have hνμ : ν ≪ μ := by
    simpa [μ, ν] using
      volume_absolutelyContinuous_stereographic_toSphere_restrict_chart_map_core
        (n := n) v
  have hpos : ∀ᵐ y ∂ν, 0 < μ.rnDeriv ν y := by
    exact Measure.rnDeriv_pos' (μ := ν) (ν := μ) hνμ
  filter_upwards [hpos] with y hy
  exact ne_of_gt hy

/--
%%handwave
name:
  Stereographic coordinates have a positive density
statement:
  In a stereographic chart on the unit sphere, Lebesgue measure in the
  coordinate space and the push-forward of spherical measure restricted to
  the chart source differ by a measurable density that is nonzero almost
  everywhere.
proof:
  The stereographic coordinate formula writes the spherical measure in the
  chart as a smooth strictly positive multiple of Lebesgue measure.  Since the
  density is finite and positive at every coordinate point, it is measurable
  and nonzero almost everywhere.
-/
private theorem stereographic_toSphere_restrict_chart_map_eq_withDensity_positive
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞,
      Measure.map (stereographic' n v)
        ((MeasureTheory.volume : Measure H).toSphere.restrict
          (stereographic' n v).source) =
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity ρ ∧
      AEMeasurable ρ
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
        ρ y ≠ 0 := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    Measure.map (stereographic' n v)
      ((MeasureTheory.volume : Measure H).toSphere.restrict
        (stereographic' n v).source)
  let ν : Measure (EuclideanSpace ℝ (Fin n)) :=
    MeasureTheory.volume
  refine ⟨μ.rnDeriv ν, ?_, ?_, ?_⟩
  · have hμν : μ ≪ ν := by
      simpa [μ, ν] using
        stereographic_toSphere_restrict_chart_map_absolutelyContinuous_volume
          (n := n) v
    have hsing : μ.singularPart ν = 0 :=
      Measure.singularPart_eq_zero_of_ac hμν
    have hdec : μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
      Measure.haveLebesgueDecomposition_add μ ν
    rw [hsing, zero_add] at hdec
    simpa [μ, ν] using hdec
  · exact (Measure.measurable_rnDeriv μ ν).aemeasurable
  · simpa [μ, ν] using
      stereographic_toSphere_restrict_chart_rnDeriv_ne_zero_ae
        (n := n) v

/--
%%handwave
name:
  Stereographic coordinates have no vanishing density
statement:
  In a stereographic chart on the unit sphere, Lebesgue measure in the
  coordinate space is absolutely continuous with respect to the push-forward
  of spherical measure restricted to the chart source.
proof:
  Write the chart measure as Lebesgue measure multiplied by a measurable
  density that is nonzero almost everywhere, then apply the standard
  absolute-continuity criterion for weighted measures.
-/
private theorem volume_absolutelyContinuous_stereographic_toSphere_restrict_chart_map
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))) ≪
      Measure.map (stereographic' n v)
        ((MeasureTheory.volume : Measure H).toSphere.restrict
          (stereographic' n v).source) := by
  exact
    volume_absolutelyContinuous_stereographic_toSphere_restrict_chart_map_core
      (n := n) v

/--
%%handwave
name:
  Inverse stereographic coordinates preserve null sets on the sphere
statement:
  The inverse stereographic parametrization
  \(y\mapsto\sigma(y)\) sends Lebesgue measure on the coordinate space
  quasi-measure-preservingly to spherical measure restricted to the
  stereographic source.
proof:
  In stereographic coordinates the spherical measure has a smooth strictly
  positive density with respect to Lebesgue measure, and the inverse chart is
  the inverse of the coordinate homeomorphism on the source.  Therefore a
  spherical null set in the chart source has a Lebesgue-null coordinate image,
  which is exactly quasi-measure-preservation of the inverse chart.
-/
private theorem stereographic_symm_toSphere_restrict_quasiMeasurePreserving
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    Measure.QuasiMeasurePreserving
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (stereographic' n v).symm y)
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n)))
      ((MeasureTheory.volume : Measure H).toSphere.restrict
        (stereographic' n v).source) := by
  classical
  let e := stereographic' n v
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μE : Measure (EuclideanSpace ℝ (Fin n)) := MeasureTheory.volume
  let μchart : Measure (EuclideanSpace ℝ (Fin n)) :=
    Measure.map e (μS.restrict e.source)
  have hsymm_meas : Measurable (fun y : EuclideanSpace ℝ (Fin n) => e.symm y) := by
    have hsymm_cont :
        Continuous (fun y : EuclideanSpace ℝ (Fin n) => e.symm y) := by
      apply continuousOn_univ.mp
      simpa [e, stereographic'_target] using e.continuousOn_symm
    exact hsymm_cont.measurable
  refine ⟨hsymm_meas, ?_⟩
  have hμE_ac : μE ≪ μchart := by
    simpa [μE, μchart, μS, e] using
      volume_absolutelyContinuous_stereographic_toSphere_restrict_chart_map
        (n := n) v
  have hsymm_map_chart :
      Measure.map (fun y : EuclideanSpace ℝ (Fin n) => e.symm y) μchart =
        μS.restrict e.source := by
    apply Measure.ext
    intro A hA
    have he_aemeas :
        AEMeasurable e (μS.restrict e.source) :=
      openPartialHomeomorph_aemeasurable_restrict_source e μS
    have hpre_meas :
        MeasurableSet (e.symm ⁻¹' A) :=
      hA.preimage hsymm_meas
    rw [Measure.map_apply hsymm_meas hA,
      Measure.map_apply_of_aemeasurable he_aemeas hpre_meas]
    have hsource_meas : MeasurableSet e.source :=
      e.open_source.measurableSet
    rw [Measure.restrict_apply' hsource_meas]
    have hpre_eq :
        e ⁻¹' (e.symm ⁻¹' A) ∩ e.source =
          A ∩ e.source := by
      ext θ
      constructor
      · rintro ⟨hθ, hθ_source⟩
        exact ⟨by simpa [e.left_inv hθ_source] using hθ, hθ_source⟩
      · rintro ⟨hθA, hθ_source⟩
        exact ⟨by simpa [e.left_inv hθ_source] using hθA, hθ_source⟩
    rw [hpre_eq]
    exact (Measure.restrict_apply' hsource_meas).symm
  calc
    Measure.map (fun y : EuclideanSpace ℝ (Fin n) => e.symm y) μE
        ≪ Measure.map (fun y : EuclideanSpace ℝ (Fin n) => e.symm y) μchart :=
      hμE_ac.map hsymm_meas
    _ = μS.restrict e.source := by rw [hsymm_map_chart]

/--
%%handwave
name:
  Weak derivatives are unchanged by changing the representative
statement:
  If two maps agree almost everywhere in the weak-derivative region, then a
  weak derivative field for one map is also a weak derivative field for the
  other.
proof:
  In every test identity, the left integrand is changed only on a null set,
  while the derivative-side integrand is unchanged.  Integrability and the
  integral identity therefore follow by almost-everywhere congruence of the
  Bochner integral.
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.congr_ae
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set H} {u u' : H → E} {du : H → H →L[ℝ] E}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hu' : u' =ᵐ[MeasureTheory.volume.restrict Ω] u) :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω u' du := by
  intro φ v
  rcases hweak φ v with ⟨hleft, hright, hEq⟩
  have hleft_ae :
      (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u z)
        =ᵐ[MeasureTheory.volume.restrict Ω]
      (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u' z) := by
    filter_upwards [hu'.symm] with z hz
    rw [hz]
  refine ⟨hleft.congr hleft_ae, hright, ?_⟩
  calc
    ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • u' z
        ∂MeasureTheory.volume
        = ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • u z
            ∂MeasureTheory.volume := by
          exact integral_congr_ae hleft_ae.symm
    _ = -∫ z in Ω, φ z • du z v ∂MeasureTheory.volume := hEq

/--
%%handwave
name:
  Endpoint bound for an absolutely continuous real function
statement:
  Let \(r<s\).  If \(f\) is absolutely continuous on \([r,s]\) and \(f'(t)=g(t)\) for almost every \(t\in[r,s]\), then
  \[
    \operatorname{ofReal}(\|f(r)-f(s)\|)
    \le \int_{r<t<s}^{-}\operatorname{ofReal}(\|g(t)\|)\,dt.
  \]
proof:
  The fundamental theorem of calculus writes \(f(s)-f(r)\) as the integral of \(f'\).  Apply the norm bound for the integral, replace \(f'\) by \(g\) almost everywhere, and note that the endpoints are Lebesgue-null.
-/
private theorem real_acl_endpoint_lintegral_bound
    {f g : ℝ → ℝ} {r s : ℝ}
    (hrs : r < s)
    (hacl : AbsolutelyContinuousOnInterval f r s)
    (hderiv : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc r s → HasDerivAt f (g t) t) :
    ENNReal.ofReal ‖f r - f s‖ ≤
      ∫⁻ t in {t : ℝ | r < t ∧ t < s},
        ENNReal.ofReal ‖g t‖ ∂MeasureTheory.volume := by
  let I : Set ℝ := {t : ℝ | r < t ∧ t < s}
  have hderiv_I :
      deriv f =ᵐ[MeasureTheory.volume.restrict I] g := by
    filter_upwards
      [ae_restrict_of_ae hderiv,
        self_mem_ae_restrict (by simpa [I, Set.Ioo] using measurableSet_Ioo)]
      with t ht_deriv htI
    have ht_uIcc : t ∈ Set.uIcc r s := by
      rw [Set.uIcc_of_le hrs.le]
      exact ⟨htI.1.le, htI.2.le⟩
    exact (ht_deriv ht_uIcc).deriv
  have hInterval :
      ∫ t in r..s, deriv f t ∂MeasureTheory.volume =
        ∫ t in I, deriv f t ∂MeasureTheory.volume := by
    rw [intervalIntegral.integral_of_le hrs.le]
    simpa [I, Set.Ioo] using
      (integral_Ioc_eq_integral_Ioo
        (f := fun t : ℝ => deriv f t)
        (μ := MeasureTheory.volume) (x := r) (y := s))
  have hnorm :
      ‖f r - f s‖ =
        ‖∫ t in I, deriv f t ∂MeasureTheory.volume‖ := by
    have hFTC :
        ∫ t in r..s, deriv f t ∂MeasureTheory.volume = f s - f r :=
      hacl.integral_deriv_eq_sub
    calc
      ‖f r - f s‖ = ‖-(f s - f r)‖ := by
        congr 1
        ring
      _ = ‖f s - f r‖ := by rw [norm_neg]
      _ = ‖∫ t in r..s, deriv f t ∂MeasureTheory.volume‖ := by
        rw [hFTC]
      _ = ‖∫ t in I, deriv f t ∂MeasureTheory.volume‖ := by
        rw [hInterval]
  have hnorm_enorm :
      ‖f r - f s‖ₑ =
        ‖∫ t in I, deriv f t ∂MeasureTheory.volume‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  calc
    ENNReal.ofReal ‖f r - f s‖
        = ‖f r - f s‖ₑ := by rw [ofReal_norm]
    _ = ‖∫ t in I, deriv f t ∂MeasureTheory.volume‖ₑ := hnorm_enorm
    _ ≤ ∫⁻ t in I, ‖deriv f t‖ₑ ∂MeasureTheory.volume :=
      MeasureTheory.enorm_integral_le_lintegral_enorm
        (μ := MeasureTheory.volume.restrict I) (fun t : ℝ => deriv f t)
    _ = ∫⁻ t in I, ENNReal.ofReal ‖deriv f t‖ ∂MeasureTheory.volume := by
      simp_rw [← ofReal_norm]
    _ = ∫⁻ t in I, ENNReal.ofReal ‖g t‖ ∂MeasureTheory.volume := by
      refine lintegral_congr_ae ?_
      filter_upwards [hderiv_I] with t ht
      rw [ht]

/--
%%handwave
name:
  Vertical endpoint bounds from linewise absolute continuity
statement:
  Suppose a representative is absolutely continuous on almost every radial
  line in a stereographic polar chart, and that its one-dimensional derivative
  on those lines is given almost everywhere by the radial component of the
  weak derivative.  Then, on almost every line and for every \(0<r<s<1\), the
  oscillation between \(r\sigma(y)\) and \(s\sigma(y)\) is bounded by the
  integral of this radial derivative over \((r,s)\).
proof:
  Fix a good transverse coordinate.  The fundamental theorem of calculus for
  absolutely continuous functions gives the endpoint difference as the
  integral of the one-dimensional derivative.  Taking norms and using the
  Bochner-integral norm bound gives the stated upper bound by the corresponding
  Lebesgue integral.
-/
theorem scalarWeakSobolev_stereographic_polar_patch_bound_of_linewise_acl
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {uacl : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hline :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ r s : ℝ, 0 < r → r < s → s < 1 →
          AbsolutelyContinuousOnInterval
            (fun ρ : ℝ => uacl (stereographicPolarPatchMap v (ρ, y))) r s ∧
          ∀ᵐ t ∂MeasureTheory.volume,
            t ∈ Set.uIcc r s →
              HasDerivAt
                (fun ρ : ℝ =>
                  uacl (stereographicPolarPatchMap v (ρ, y)))
                (du (stereographicPolarPatchMap v (t, y))
                  (((stereographic' n v).symm y :
                    Metric.sphere (0 : H) 1) : H)) t) :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ r s : ℝ, 0 < r → r < s → s < 1 →
          ENNReal.ofReal
            ‖uacl (stereographicPolarPatchMap v (r, y)) -
              uacl (stereographicPolarPatchMap v (s, y))‖ ≤
            ∫⁻ t in {t : ℝ | r < t ∧ t < s},
              ENNReal.ofReal
                ‖du (stereographicPolarPatchMap v (t, y))
                  (((stereographic' n v).symm y :
                    Metric.sphere (0 : H) 1) : H)‖
              ∂MeasureTheory.volume := by
  filter_upwards [hline] with y hy
  intro r s _hr hrs hs
  rcases hy r s _hr hrs hs with ⟨hacl, hderiv⟩
  exact real_acl_endpoint_lintegral_bound
    (f := fun ρ : ℝ => uacl (stereographicPolarPatchMap v (ρ, y)))
    (g := fun t : ℝ =>
      du (stereographicPolarPatchMap v (t, y))
        (((stereographic' n v).symm y :
          Metric.sphere (0 : H) 1) : H))
    hrs hacl hderiv

private def stereographicPolarPatchRadialDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    (du : H → H →L[ℝ] ℝ)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  du (stereographicPolarPatchMap v p)
    (((stereographic' n v).symm p.2 :
      Metric.sphere (0 : H) 1) : H)

private noncomputable def firstCoordinateAnchoredPrimitive
    {E : Type} [MeasurableSpace E]
    (G : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  ∫ t in (1 / 2 : ℝ)..p.1, G (t, p.2) ∂MeasureTheory.volume

private noncomputable def firstCoordinateAnchoredConstant
    {E : Type} [MeasurableSpace E]
    (U G : ℝ × E → ℝ) (y : E) : ℝ :=
  (3 : ℝ) *
    ∫ r in Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
      U (r, y) - firstCoordinateAnchoredPrimitive G (r, y)
        ∂MeasureTheory.volume

private noncomputable def firstCoordinateAnchoredRepresentative
    {E : Type} [MeasurableSpace E]
    (U G : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  firstCoordinateAnchoredConstant U G p.2 +
    firstCoordinateAnchoredPrimitive G p

/--
%%handwave
name:
  The anchored vertical primitive is measurable
statement:
  If \(U\) and \(G\) are measurable on \(\mathbb R\times E\), then the
  representative
  \[
    \widetilde U(r,y)
      = C(y)+\int_{1/2}^r G(t,y)\,dt,
    \qquad
    C(y)=3\int_{1/3}^{2/3}
      \Bigl(U(a,y)-\int_{1/2}^aG(t,y)\,dt\Bigr)\,da
  \]
  is measurable on \(\mathbb R\times E\).
proof:
  Write the variable-endpoint interval integral as the difference of
  integrals of measurable functions over fixed product spaces, using
  indicators of the measurable sets \(1/2<t\le r\) and \(r<t\le1/2\).
  Measurability of parameter integrals gives the primitive, and a second
  parameter-integral argument gives the averaged constant.
-/
theorem firstCoordinateAnchoredRepresentative_measurable
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U G : ℝ × E → ℝ}
    (_hU_meas : Measurable U) (_hG_meas : Measurable G) :
    Measurable (firstCoordinateAnchoredRepresentative U G) := by
  classical
  let A : Set ((ℝ × E) × ℝ) :=
    {q | (1 / 2 : ℝ) < q.2 ∧ q.2 ≤ q.1.1}
  let B : Set ((ℝ × E) × ℝ) :=
    {q | q.1.1 < q.2 ∧ q.2 ≤ (1 / 2 : ℝ)}
  let F : ((ℝ × E) × ℝ) → ℝ := fun q => G (q.2, q.1.2)
  have hF_meas : Measurable F := by
    exact _hG_meas.comp (measurable_snd.prodMk measurable_fst.snd)
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)
  have hB_meas : MeasurableSet B := by
    dsimp [B]
    exact (measurableSet_lt measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hA_int_meas :
      Measurable
        (fun p : ℝ × E =>
          ∫ t : ℝ, A.indicator F (p, t) ∂MeasureTheory.volume) :=
    ((hF_meas.indicator hA_meas).stronglyMeasurable.integral_prod_right').measurable
  have hB_int_meas :
      Measurable
        (fun p : ℝ × E =>
          ∫ t : ℝ, B.indicator F (p, t) ∂MeasureTheory.volume) :=
    ((hF_meas.indicator hB_meas).stronglyMeasurable.integral_prod_right').measurable
  have hprimitive_eq :
      firstCoordinateAnchoredPrimitive G =
        fun p : ℝ × E =>
          (∫ t : ℝ, A.indicator F (p, t) ∂MeasureTheory.volume) -
            ∫ t : ℝ, B.indicator F (p, t) ∂MeasureTheory.volume := by
    funext p
    have hA_slice :
        (fun t : ℝ => A.indicator F (p, t)) =
          (Set.Ioc (1 / 2 : ℝ) p.1).indicator
            (fun t : ℝ => G (t, p.2)) := by
      funext t
      by_cases ht : t ∈ Set.Ioc (1 / 2 : ℝ) p.1
      · have hAt : (p, t) ∈ A := by
          simpa [A, Set.mem_Ioc] using ht
        rw [Set.indicator_of_mem hAt, Set.indicator_of_mem ht]
      · have hAt : (p, t) ∉ A := by
          intro h
          exact ht (by simpa [A, Set.mem_Ioc] using h)
        rw [Set.indicator_of_notMem hAt, Set.indicator_of_notMem ht]
    have hB_slice :
        (fun t : ℝ => B.indicator F (p, t)) =
          (Set.Ioc p.1 (1 / 2 : ℝ)).indicator
            (fun t : ℝ => G (t, p.2)) := by
      funext t
      by_cases ht : t ∈ Set.Ioc p.1 (1 / 2 : ℝ)
      · have hBt : (p, t) ∈ B := by
          simpa [B, Set.mem_Ioc] using ht
        rw [Set.indicator_of_mem hBt, Set.indicator_of_mem ht]
      · have hBt : (p, t) ∉ B := by
          intro h
          exact ht (by simpa [B, Set.mem_Ioc] using h)
        rw [Set.indicator_of_notMem hBt, Set.indicator_of_notMem ht]
    rw [firstCoordinateAnchoredPrimitive, intervalIntegral, hA_slice, hB_slice,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      MeasureTheory.integral_indicator measurableSet_Ioc]
  have hprimitive_meas : Measurable (firstCoordinateAnchoredPrimitive G) := by
    rw [hprimitive_eq]
    exact hA_int_meas.sub hB_int_meas
  let S : Set (ℝ × E) := {q | q.1 ∈ Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)}
  let R : ℝ × E → ℝ :=
    fun q => U q - firstCoordinateAnchoredPrimitive G q
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_Ioo.preimage measurable_fst
  have hR_meas : Measurable R := by
    dsimp [R]
    exact _hU_meas.sub hprimitive_meas
  have hconstant_integral_meas :
      Measurable
        (fun y : E =>
          ∫ r : ℝ, S.indicator R (r, y) ∂MeasureTheory.volume) :=
    ((hR_meas.indicator hS_meas).stronglyMeasurable.integral_prod_left').measurable
  have hconstant_eq :
      firstCoordinateAnchoredConstant U G =
        fun y : E =>
          (3 : ℝ) *
            ∫ r : ℝ, S.indicator R (r, y) ∂MeasureTheory.volume := by
    funext y
    have hS_slice :
        (fun r : ℝ => S.indicator R (r, y)) =
          (Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)).indicator
            (fun r : ℝ =>
              U (r, y) - firstCoordinateAnchoredPrimitive G (r, y)) := by
      funext r
      by_cases hr : r ∈ Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)
      · have hSr : (r, y) ∈ S := by
          simpa [S] using hr
        rw [Set.indicator_of_mem hSr, Set.indicator_of_mem hr]
      · have hSr : (r, y) ∉ S := by
          intro h
          exact hr (by simpa [S] using h)
        rw [Set.indicator_of_notMem hSr, Set.indicator_of_notMem hr]
    rw [firstCoordinateAnchoredConstant, hS_slice,
      MeasureTheory.integral_indicator measurableSet_Ioo]
  have hconstant_meas : Measurable (firstCoordinateAnchoredConstant U G) := by
    rw [hconstant_eq]
    exact measurable_const.mul hconstant_integral_meas
  change Measurable
    (fun p : ℝ × E =>
      firstCoordinateAnchoredConstant U G p.2 +
        firstCoordinateAnchoredPrimitive G p)
  exact (hconstant_meas.comp measurable_snd).add hprimitive_meas

/--
%%handwave
name:
  Anchored primitive formula for a weakly differentiable function
statement:
  Suppose \(g\) is the weak derivative of \(u\) on \((0,1)\), and \(g_0=g\) almost everywhere there.  Then \(u\) agrees almost everywhere on \((0,1)\) with
  \[
    r\longmapsto
    3\int_{1/3}^{2/3}\left(u(a)-\int_{1/2}^{a}g_0(t)\,dt\right)da
    +\int_{1/2}^{r}g_0(t)\,dt.
  \]
proof:
  A one-dimensional weakly differentiable function has an absolutely continuous representative \(D+\int_{1/2}^r g\).  Averaging \(u(a)-\int_{1/2}^a g\) over the interval of length \(1/3\) identifies \(D\).  Replace \(g\) by \(g_0\) in all interval integrals using almost-everywhere equality.
-/
private theorem realWeakSobolev_anchoredPrimitive_ae_eq_on_unit_interval
    {u g g₀ : ℝ → ℝ}
    (hg₀_eq :
      g₀ =ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)] g)
    (hweak : IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1) u g) :
    (fun r : ℝ =>
      (3 : ℝ) *
          ∫ a in Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
            u a - ∫ t in (1 / 2 : ℝ)..a, g₀ t ∂MeasureTheory.volume
            ∂MeasureTheory.volume +
        ∫ t in (1 / 2 : ℝ)..r, g₀ t ∂MeasureTheory.volume)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)] u := by
  classical
  let Ω : Set ℝ := Set.Ioo (0 : ℝ) 1
  have hΩ_open : IsOpen Ω := by
    dsimp [Ω]
    exact isOpen_Ioo
  let hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t :=
    fun a b habΩ ↦
      realWeakSobolev_eq_primitive_add_const_ae_on_interval
        (Ω := Ω) hΩ_open hweak habΩ
  let hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b :=
    fun a b habΩ ↦
      realWeakSobolev_derivative_intervalIntegrable_on_uIcc
        (Ω := Ω) hΩ_open hweak habΩ
  let uacl : ℝ → ℝ :=
    realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive
  let D : ℝ := uacl (1 / 2 : ℝ)
  have hhalfΩ : (1 / 2 : ℝ) ∈ Ω := by
    dsimp [Ω]
    norm_num [Set.mem_Ioo]
  have huacl_eq :
      uacl =ᵐ[MeasureTheory.volume.restrict Ω] u := by
    dsimp [uacl]
    exact realWeakSobolevGluedPrimitiveRepresentative_ae_eq_on_open
      (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
      hg_interval (hprimitive := hprimitive)
  have huacl_formula :
      ∀ x ∈ Ω, uacl x = D + ∫ t in (1 / 2 : ℝ)..x, g t := by
    intro x hxΩ
    have hsegΩ : Set.uIcc (1 / 2 : ℝ) x ⊆ Ω :=
      Set.ordConnected_Ioo.uIcc_subset hhalfΩ hxΩ
    let Cbase : ℝ :=
      realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive
          (realOpenOrdComponentBase Ω (1 / 2 : ℝ)) +
        ∫ t in realOpenOrdComponentBase Ω (1 / 2 : ℝ)..(1 / 2 : ℝ), g t
    have hhalf_formula :
        uacl (1 / 2 : ℝ) = Cbase := by
      have h :=
        realWeakSobolevGluedPrimitiveRepresentative_eq_primitive_on_uIcc
          (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
          hg_interval (hprimitive := hprimitive) hsegΩ
          (Set.left_mem_uIcc : (1 / 2 : ℝ) ∈ Set.uIcc (1 / 2 : ℝ) x)
      simpa [uacl, Cbase] using h
    have hx_formula :
        uacl x = Cbase + ∫ t in (1 / 2 : ℝ)..x, g t := by
      have h :=
        realWeakSobolevGluedPrimitiveRepresentative_eq_primitive_on_uIcc
          (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
          hg_interval (hprimitive := hprimitive) hsegΩ
          (Set.right_mem_uIcc : x ∈ Set.uIcc (1 / 2 : ℝ) x)
      simpa [uacl, Cbase] using h
    have hCbase_eq_D : Cbase = D := by
      simpa [D] using hhalf_formula.symm
    rw [hx_formula, hCbase_eq_D]
  have hprimitive_g₀_eq_g :
      ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
        (∫ t in (1 / 2 : ℝ)..x, g₀ t ∂MeasureTheory.volume) =
          ∫ t in (1 / 2 : ℝ)..x, g t ∂MeasureTheory.volume := by
    filter_upwards [ae_restrict_mem hΩ_open.measurableSet] with x hxΩ
    have hsegΩ_cc : Set.uIcc (1 / 2 : ℝ) x ⊆ Ω :=
      Set.ordConnected_Ioo.uIcc_subset hhalfΩ hxΩ
    have hsegΩ_oc : Set.uIoc (1 / 2 : ℝ) x ⊆ Ω :=
      fun z hz ↦ hsegΩ_cc (Set.uIoc_subset_uIcc hz)
    have heq :
        g₀ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (1 / 2 : ℝ) x)] g :=
      ae_restrict_of_ae_restrict_of_subset hsegΩ_oc (by simpa [Ω] using hg₀_eq)
    exact intervalIntegral.integral_congr_ae_restrict heq
  let A : Set ℝ := Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)
  have hAΩ : A ⊆ Ω := by
    intro x hx
    dsimp [A, Ω] at hx ⊢
    rcases hx with ⟨hx_left, hx_right⟩
    constructor <;> linarith
  have hanchor_integrand :
      (fun a : ℝ => u a - ∫ t in (1 / 2 : ℝ)..a, g₀ t ∂MeasureTheory.volume)
        =ᵐ[MeasureTheory.volume.restrict A] fun _ : ℝ => D := by
    have hu_on_A :
        u =ᵐ[MeasureTheory.volume.restrict A] uacl :=
      ae_restrict_of_ae_restrict_of_subset hAΩ huacl_eq.symm
    have hprim_on_A :
        ∀ᵐ a ∂MeasureTheory.volume.restrict A,
          (∫ t in (1 / 2 : ℝ)..a, g₀ t ∂MeasureTheory.volume) =
            ∫ t in (1 / 2 : ℝ)..a, g t ∂MeasureTheory.volume :=
      ae_restrict_of_ae_restrict_of_subset hAΩ hprimitive_g₀_eq_g
    filter_upwards [hu_on_A, hprim_on_A, ae_restrict_mem measurableSet_Ioo]
      with a hua hprim haA
    have haΩ : a ∈ Ω := hAΩ haA
    have hform := huacl_formula a haΩ
    calc
      u a - ∫ t in (1 / 2 : ℝ)..a, g₀ t ∂MeasureTheory.volume
          = uacl a - ∫ t in (1 / 2 : ℝ)..a, g t ∂MeasureTheory.volume := by
            rw [hua, hprim]
      _ = D := by
            rw [hform]
            ring
  have hanchor_const :
      (3 : ℝ) *
          ∫ a in A,
            u a - ∫ t in (1 / 2 : ℝ)..a, g₀ t ∂MeasureTheory.volume
            ∂MeasureTheory.volume = D := by
    have hint_eq :
        (∫ a in A,
            u a - ∫ t in (1 / 2 : ℝ)..a, g₀ t ∂MeasureTheory.volume
            ∂MeasureTheory.volume) =
          ∫ _a in A, D ∂MeasureTheory.volume :=
      integral_congr_ae hanchor_integrand
    have hconst_int :
        (∫ _a in A, D ∂MeasureTheory.volume) = (1 / 3 : ℝ) * D := by
      rw [MeasureTheory.integral_const]
      have hmeasure :
          (MeasureTheory.volume.restrict A).real Set.univ = (1 / 3 : ℝ) := by
        rw [Measure.real_def, Measure.restrict_apply_univ]
        simp [A, Real.volume_Ioo]
        norm_num
      simp [hmeasure, smul_eq_mul]
    rw [hint_eq, hconst_int]
    ring
  have hanchored_eq_uacl :
      (fun r : ℝ =>
        (3 : ℝ) *
            ∫ a in A,
              u a - ∫ t in (1 / 2 : ℝ)..a, g₀ t ∂MeasureTheory.volume
              ∂MeasureTheory.volume +
          ∫ t in (1 / 2 : ℝ)..r, g₀ t ∂MeasureTheory.volume)
        =ᵐ[MeasureTheory.volume.restrict Ω] uacl := by
    filter_upwards [hprimitive_g₀_eq_g, ae_restrict_mem hΩ_open.measurableSet]
      with r hprim hrΩ
    have hform := huacl_formula r hrΩ
    calc
      (3 : ℝ) *
            ∫ a in A,
              u a - ∫ t in (1 / 2 : ℝ)..a, g₀ t ∂MeasureTheory.volume
              ∂MeasureTheory.volume +
          ∫ t in (1 / 2 : ℝ)..r, g₀ t ∂MeasureTheory.volume
          = D + ∫ t in (1 / 2 : ℝ)..r, g t ∂MeasureTheory.volume := by
            rw [hanchor_const, hprim]
      _ = uacl r := hform.symm
  simpa [Ω, A] using hanchored_eq_uacl.trans huacl_eq

/--
%%handwave
name:
  The anchored vertical primitive agrees with the original function on almost
  every good line
statement:
  Let \(U\) be measurable on \(\mathbb R\times E\), and let \(G_0\) be a
  measurable representative of \(G\) on the unit strip.  If almost every
  vertical slice has weak derivative \(G\), and \(G_0=G\) almost everywhere
  on the strip, then for almost every transverse coordinate \(y\), the
  anchored representative built from \(G_0(\cdot,y)\) agrees almost
  everywhere with \(U(\cdot,y)\) on \((0,1)\).
proof:
  On a good line replace \(G\) by \(G_0\) in the one-dimensional weak
  derivative identity.  The difference between \(U\) and the primitive of
  \(G_0\) is almost everywhere constant on compact subintervals of \((0,1)\).
  Averaging that difference over the fixed interval \((1/3,2/3)\) recovers
  the same constant, so the anchored primitive agrees with \(U\) almost
  everywhere on the line.
-/
theorem firstCoordinateAnchoredRepresentative_linewise_ae_eq_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U G G₀ : ℝ × E → ℝ}
    (_hU_meas : Measurable U) (_hG₀_meas : Measurable G₀)
    (_hG₀_eq :
      G₀ =ᵐ[MeasureTheory.volume.restrict
        {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}] G)
    (_hweak_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
          (fun r : ℝ => U (r, y)) (fun r : ℝ => G (r, y))) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      (fun r : ℝ => firstCoordinateAnchoredRepresentative U G₀ (r, y))
        =ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)]
      fun r : ℝ => U (r, y) := by
  classical
  have hstrip_eq :
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} =
        Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set E) := by
    ext p
    simp [Set.mem_Ioo]
  have hG₀_eq_prod :
      G₀ =ᵐ[((MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
          (MeasureTheory.volume : Measure E))] G := by
    have hmeasure :
        ((MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
            (MeasureTheory.volume : Measure E)) =
          ((MeasureTheory.volume : Measure ℝ).prod
            (MeasureTheory.volume : Measure E)).restrict
              (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set E)) := by
      simpa using
        (Measure.prod_restrict
          (μ := (MeasureTheory.volume : Measure ℝ))
          (ν := (MeasureTheory.volume : Measure E))
          (Set.Ioo (0 : ℝ) 1) (Set.univ : Set E))
    simpa [hstrip_eq, Measure.volume_eq_prod, hmeasure] using _hG₀_eq
  have hG₀_eq_swap :
      (fun p : E × ℝ => G₀ (p.2, p.1))
        =ᵐ[((MeasureTheory.volume : Measure E).prod
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)))]
        fun p : E × ℝ => G (p.2, p.1) := by
    have h :=
      (Measure.measurePreserving_swap
        (μ := (MeasureTheory.volume : Measure E))
        (ν := MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))).quasiMeasurePreserving.tendsto_ae
        hG₀_eq_prod
    simpa [Prod.swap] using h
  have hG₀_eq_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        (fun r : ℝ => G₀ (r, y))
          =ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun r : ℝ => G (r, y) := by
    simpa using Measure.ae_ae_eq_curry_of_prod hG₀_eq_swap
  filter_upwards [hG₀_eq_slices, _hweak_slices] with y hG₀_eq_y hweak_y
  have hline :=
    realWeakSobolev_anchoredPrimitive_ae_eq_on_unit_interval
      (u := fun r : ℝ => U (r, y))
      (g := fun r : ℝ => G (r, y))
      (g₀ := fun r : ℝ => G₀ (r, y))
      hG₀_eq_y hweak_y
  simpa [firstCoordinateAnchoredRepresentative, firstCoordinateAnchoredConstant,
    firstCoordinateAnchoredPrimitive] using hline

/--
%%handwave
name:
  The anchored vertical primitive agrees almost everywhere with the original
  function
statement:
  Let \(U\) be measurable on \(\mathbb R\times E\).  Let \(G_0\) be a
  measurable representative of \(G\) on the strip \(0<r<1\).  If almost every
  vertical slice \(U(\cdot,y)\) has weak derivative \(G(\cdot,y)\), and
  \(G_0=G\) almost everywhere on the strip, then the anchored representative
  built from \(G_0\) agrees with \(U\) almost everywhere on the strip.
proof:
  For a good vertical line, replace \(G\) by \(G_0\) in the one-dimensional
  weak derivative identity.  On the anchor interval \((1/3,2/3)\), the
  one-dimensional primitive representation says that
  \(U(r,y)-\int_{1/2}^rG_0(t,y)\,dt\) is almost everywhere constant.  Averaging
  over this anchor interval recovers that constant, so the anchored
  representative agrees with \(U\) almost everywhere on the line.  Fubini
  recombines the linewise statements on the product strip.
-/
theorem firstCoordinateAnchoredRepresentative_ae_eq_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U G G₀ : ℝ × E → ℝ}
    (_hU_meas : Measurable U) (_hG₀_meas : Measurable G₀)
    (_hG₀_eq :
      G₀ =ᵐ[MeasureTheory.volume.restrict
        {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}] G)
    (_hweak_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
          (fun r : ℝ => U (r, y)) (fun r : ℝ => G (r, y))) :
    firstCoordinateAnchoredRepresentative U G₀
      =ᵐ[MeasureTheory.volume.restrict
        {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}] U := by
  classical
  let strip : Set (ℝ × E) := {p | 0 < p.1 ∧ p.1 < 1}
  let μR : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)
  let μE : Measure E := MeasureTheory.volume
  let R : ℝ × E → ℝ := firstCoordinateAnchoredRepresentative U G₀
  have hline :
      ∀ᵐ y ∂μE,
        (fun r : ℝ => R (r, y)) =ᵐ[μR] fun r : ℝ => U (r, y) := by
    dsimp [R, μR, μE]
    exact firstCoordinateAnchoredRepresentative_linewise_ae_eq_on_unit_strip
      (U := U) (G := G) (G₀ := G₀)
      _hU_meas _hG₀_meas _hG₀_eq _hweak_slices
  have hR_meas : Measurable R := by
    dsimp [R]
    exact firstCoordinateAnchoredRepresentative_measurable
      (U := U) (G := G₀) _hU_meas _hG₀_meas
  have hP_meas :
      MeasurableSet {p : ℝ × E | R p = U p} :=
    measurableSet_eq_fun hR_meas _hU_meas
  have hP_swap_meas :
      MeasurableSet {p : E × ℝ | R (p.2, p.1) = U (p.2, p.1)} := by
    change MeasurableSet (Prod.swap ⁻¹' {p : ℝ × E | R p = U p})
    exact measurable_swap hP_meas
  have hswap_prod :
      ∀ᵐ p ∂μE.prod μR, R (p.2, p.1) = U (p.2, p.1) := by
    exact (Measure.ae_prod_iff_ae_ae hP_swap_meas).2 hline
  have hprod :
      ∀ᵐ p ∂μR.prod μE, R p = U p := by
    have h :=
      (Measure.measurePreserving_swap (μ := μR) (ν := μE)).quasiMeasurePreserving.tendsto_ae
        hswap_prod
    simpa [Prod.swap] using h
  have hstrip_eq :
      strip = Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set E) := by
    ext p
    simp [strip, Set.mem_Ioo]
  have hmeasure :
      μR.prod μE =
        (MeasureTheory.volume : Measure (ℝ × E)).restrict strip := by
    dsimp [μR, μE]
    rw [hstrip_eq, Measure.volume_eq_prod]
    simpa using Measure.prod_restrict
      (μ := (MeasureTheory.volume : Measure ℝ))
      (ν := (MeasureTheory.volume : Measure E))
      (Set.Ioo (0 : ℝ) 1) (Set.univ : Set E)
  dsimp [R, strip] at hprod hmeasure ⊢
  simpa [hmeasure]
    using hprod

/--
%%handwave
name:
  The anchored vertical primitive has the expected linewise derivative
statement:
  Under the same hypotheses, for almost every transverse coordinate \(y\),
  the anchored representative is absolutely continuous on every compact
  subinterval of \((0,1)\), and its derivative is \(G(r,y)\) for almost every
  \(r\).
proof:
  On good vertical lines, \(G_0=G\) almost everywhere on compact subintervals
  of \((0,1)\).  The anchored representative is a constant plus the primitive
  of \(G_0\), hence is absolutely continuous on each compact subinterval and
  has derivative \(G_0\) almost everywhere there.  Replace \(G_0\) by \(G\) on
  the same full-measure set.
-/
theorem firstCoordinateAnchoredRepresentative_linewise_acl_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U G G₀ : ℝ × E → ℝ}
    (_hG₀_meas : Measurable G₀)
    (_hG₀_eq :
      G₀ =ᵐ[MeasureTheory.volume.restrict
        {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}] G)
    (_hweak_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
          (fun r : ℝ => U (r, y)) (fun r : ℝ => G (r, y))) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      ∀ r s : ℝ, 0 < r → r < s → s < 1 →
        AbsolutelyContinuousOnInterval
          (fun ρ : ℝ =>
            firstCoordinateAnchoredRepresentative U G₀ (ρ, y)) r s ∧
        ∀ᵐ t ∂MeasureTheory.volume,
          t ∈ Set.uIcc r s →
            HasDerivAt
              (fun ρ : ℝ =>
                firstCoordinateAnchoredRepresentative U G₀ (ρ, y))
              (G (t, y)) t := by
  classical
  have hstrip_eq :
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} =
        Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set E) := by
    ext p
    simp [Set.mem_Ioo]
  have hG₀_eq_prod :
      G₀ =ᵐ[((MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
          (MeasureTheory.volume : Measure E))] G := by
    have hmeasure :
        ((MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
            (MeasureTheory.volume : Measure E)) =
          ((MeasureTheory.volume : Measure ℝ).prod
            (MeasureTheory.volume : Measure E)).restrict
              (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set E)) := by
      simpa using
        (Measure.prod_restrict
          (μ := (MeasureTheory.volume : Measure ℝ))
          (ν := (MeasureTheory.volume : Measure E))
          (Set.Ioo (0 : ℝ) 1) (Set.univ : Set E))
    simpa [hstrip_eq, Measure.volume_eq_prod, hmeasure] using _hG₀_eq
  have hG₀_eq_swap :
      (fun p : E × ℝ => G₀ (p.2, p.1))
        =ᵐ[((MeasureTheory.volume : Measure E).prod
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)))]
        fun p : E × ℝ => G (p.2, p.1) := by
    have h :=
      (Measure.measurePreserving_swap
        (μ := (MeasureTheory.volume : Measure E))
        (ν := MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))).quasiMeasurePreserving.tendsto_ae
        hG₀_eq_prod
    simpa [Prod.swap] using h
  have hG₀_eq_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        (fun r : ℝ => G₀ (r, y))
          =ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun r : ℝ => G (r, y) := by
    simpa using Measure.ae_ae_eq_curry_of_prod hG₀_eq_swap
  filter_upwards [hG₀_eq_slices, _hweak_slices] with y hG₀_eq_y hweak_y
  intro r s hr hrs hs
  let a : ℝ := min r (1 / 2 : ℝ)
  let b : ℝ := max s (1 / 2 : ℝ)
  let g : ℝ → ℝ := fun t => G (t, y)
  let g₀ : ℝ → ℝ := fun t => G₀ (t, y)
  let C : ℝ := firstCoordinateAnchoredConstant U G₀ y
  let F : ℝ → ℝ := fun ρ => C + ∫ t in (1 / 2 : ℝ)..ρ, g₀ t
  have ha_le_half : a ≤ (1 / 2 : ℝ) := by
    dsimp [a]
    exact min_le_right r (1 / 2 : ℝ)
  have hhalf_le_b : (1 / 2 : ℝ) ≤ b := by
    dsimp [b]
    exact le_max_right s (1 / 2 : ℝ)
  have ha_le_b : a ≤ b := ha_le_half.trans hhalf_le_b
  have hhalf_mem : (1 / 2 : ℝ) ∈ Set.uIcc a b :=
    Set.mem_uIcc_of_le ha_le_half hhalf_le_b
  have hrs_subset_big : Set.uIcc r s ⊆ Set.uIcc a b := by
    intro x hx
    have hxIcc : x ∈ Set.Icc r s := by
      simpa [Set.uIcc_of_le hrs.le] using hx
    have hax : a ≤ x := by
      exact (min_le_left r (1 / 2 : ℝ)).trans hxIcc.1
    have hxb : x ≤ b := by
      exact hxIcc.2.trans (le_max_left s (1 / 2 : ℝ))
    exact Set.mem_uIcc_of_le hax hxb
  have hbig_subset : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le ha_le_b] using hx
    have ha_pos : 0 < a := by
      dsimp [a]
      exact lt_min hr (by norm_num)
    have hb_lt : b < 1 := by
      dsimp [b]
      exact max_lt hs (by norm_num)
    exact ⟨lt_of_lt_of_le ha_pos hxIcc.1,
      lt_of_le_of_lt hxIcc.2 hb_lt⟩
  have hg_interval : IntervalIntegrable g MeasureTheory.volume a b := by
    exact realWeakSobolev_derivative_intervalIntegrable_on_uIcc
      (Ω := Set.Ioo (0 : ℝ) 1) isOpen_Ioo hweak_y hbig_subset
  have hG₀_eq_on_big :
      g =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] g₀ := by
    have hsub : Set.uIoc a b ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro x hx
      exact hbig_subset (Set.uIoc_subset_uIcc hx)
    exact ae_restrict_of_ae_restrict_of_subset hsub hG₀_eq_y.symm
  have hg₀_interval : IntervalIntegrable g₀ MeasureTheory.volume a b :=
    hg_interval.congr_ae hG₀_eq_on_big
  have hF_ac_big : AbsolutelyContinuousOnInterval F a b := by
    have hprimitive_ac :
        AbsolutelyContinuousOnInterval
          (fun ρ : ℝ => ∫ t in (1 / 2 : ℝ)..ρ, g₀ t) a b :=
      hg₀_interval.absolutelyContinuousOnInterval_intervalIntegral hhalf_mem
    have hconst_ac :
        AbsolutelyContinuousOnInterval (fun _ : ℝ => C) a b := by
      simpa [AbsolutelyContinuousOnInterval] using
        (tendsto_const_nhds :
          Filter.Tendsto
            (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0 : ℝ))
            (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
              Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b))
            (𝓝 (0 : ℝ)))
    simpa [F, Pi.add_apply] using hconst_ac.add hprimitive_ac
  have hF_deriv_big :
      ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
        t ∈ Set.uIcc a b → HasDerivAt F (g₀ t) t := by
    filter_upwards [hg₀_interval.ae_hasDerivAt_integral] with t ht htmem
    exact (ht htmem (1 / 2 : ℝ) hhalf_mem).const_add C
  have hG₀_eq_on_rs :
      ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
        t ∈ Set.uIcc r s → g₀ t = g t := by
    have hsub : Set.uIcc r s ⊆ Set.Ioo (0 : ℝ) 1 :=
      hrs_subset_big.trans hbig_subset
    exact ae_imp_of_ae_restrict
      (ae_restrict_of_ae_restrict_of_subset hsub hG₀_eq_y)
  constructor
  · have hF_ac_rs : AbsolutelyContinuousOnInterval F r s :=
      hF_ac_big.mono hrs_subset_big
    simpa [F, C, g₀, firstCoordinateAnchoredRepresentative,
      firstCoordinateAnchoredPrimitive] using hF_ac_rs
  · filter_upwards [hF_deriv_big, hG₀_eq_on_rs] with t hderiv ht_eq htmem
    have htbig : t ∈ Set.uIcc a b := hrs_subset_big htmem
    have hderiv_g₀ : HasDerivAt F (g₀ t) t := hderiv htbig
    have hderiv_g : HasDerivAt F (g t) t := by
      simpa [ht_eq htmem] using hderiv_g₀
    simpa [F, C, g, g₀, firstCoordinateAnchoredRepresentative,
      firstCoordinateAnchoredPrimitive] using hderiv_g

/--
%%handwave
name:
  The stereographic polar chart preserves null sets into the ball
statement:
  The map \((r,y)\mapsto r\sigma(y)\), restricted to \(0<r<1\), sends the
  product Lebesgue measure on the cylinder quasi-measure-preservingly into
  Lebesgue measure on the unit ball.
proof:
  Factor the map into inverse stereographic coordinates on the sphere and the
  ordinary polar-coordinate homeomorphism.  The inverse stereographic chart
  has a smooth positive Jacobian density with respect to spherical measure,
  while the radial polar coordinate formula identifies the product of
  spherical measure and \(r^{m-1}\,dr\) with Haar measure on the punctured
  ball.  Since the cylinder measure is mutually absolutely continuous with
  this weighted product measure on \(0<r<1\), null sets pull back to null sets.
-/
private theorem stereographicPolarPatchMap_quasiMeasurePreserving_cylinder_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    Measure.QuasiMeasurePreserving
      (stereographicPolarPatchMap (n := n) v)
      (MeasureTheory.volume.restrict (stereographicPolarPatchCylinder n))
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
  classical
  let E : Type := EuclideanSpace ℝ (Fin n)
  let μC : Measure (ℝ × E) :=
    MeasureTheory.volume.restrict (stereographicPolarPatchCylinder n)
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  have hT_meas :
      Measurable (stereographicPolarPatchMap (n := n) v) :=
    (continuous_stereographicPolarPatchMap (n := n) v).measurable
  refine ⟨hT_meas, ?_⟩
  intro B hB_zero
  let B₀ : Set H := MeasureTheory.toMeasurable μB B
  have hB_subset_B₀ : B ⊆ B₀ :=
    subset_toMeasurable μB B
  have hB₀_meas : MeasurableSet B₀ :=
    measurableSet_toMeasurable μB B
  have hB₀_zero : μB B₀ = 0 := by
    dsimp [B₀]
    rw [measure_toMeasurable]
    exact hB_zero
  have hB₀_ae : ∀ᵐ z ∂μB, z ∉ B₀ := by
    rw [ae_iff]
    simpa only [Set.mem_setOf_eq, not_not] using hB₀_zero
  have hpolar :
      ∀ᵐ p ∂(μS.prod (μR.restrict R)),
        ((p.2 : ℝ) • (p.1 : H)) ∉ B₀ := by
    simpa [μB, μS, μR, R] using
      ae_polar_product_unitBall_of_ae_volume_unitBall
        (H := H) (P := fun z : H ↦ z ∉ B₀) hB₀_ae
  have hpolar_meas :
      MeasurableSet
        {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
          ((p.2 : ℝ) • (p.1 : H)) ∉ B₀} := by
    exact hB₀_meas.compl.preimage (by measurability)
  have htheta :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        ∀ᵐ r : Set.Ioi (0 : ℝ) ∂μR.restrict R,
          ((r : ℝ) • (θ : H)) ∉ B₀ := by
    simpa [μS, μR, R] using
      (Measure.ae_prod_iff_ae_ae hpolar_meas).1 hpolar
  have hsource_meas : MeasurableSet (stereographic' n v).source :=
    (stereographic' n v).open_source.measurableSet
  have htheta_source :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂(μS.restrict (stereographic' n v).source),
        ∀ᵐ r : Set.Ioi (0 : ℝ) ∂μR.restrict R,
          ((r : ℝ) • (θ : H)) ∉ B₀ := by
    exact ae_restrict_of_ae htheta
  have htheta_real :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂(μS.restrict (stereographic' n v).source),
        ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
          0 < t → t < 1 → t • (θ : H) ∉ B₀ := by
    filter_upwards [htheta_source] with θ hθ
    exact
      ae_volume_Ioo_zero_one_of_ae_volumeIoiPow_restrict
        (n := Module.finrank ℝ H - 1)
        (P := fun r : Set.Ioi (0 : ℝ) ↦ ((r : ℝ) • (θ : H)) ∉ B₀)
        hθ
  have hangular :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
          0 < t → t < 1 →
            t • (((stereographic' n v).symm y :
              Metric.sphere (0 : H) 1) : H) ∉ B₀ := by
    simpa [E, μS] using
      (stereographic_symm_toSphere_restrict_quasiMeasurePreserving
        (n := n) v).tendsto_ae htheta_real
  have hswap_meas :
      MeasurableSet
        {q : E × ℝ |
          0 < q.2 → q.2 < 1 →
            q.2 • (((stereographic' n v).symm q.1 :
              Metric.sphere (0 : H) 1) : H) ∉ B₀} := by
    let A : Set (E × ℝ) := {q : E × ℝ | 0 < q.2}
    let C : Set (E × ℝ) := {q : E × ℝ | q.2 < 1}
    let D : Set (E × ℝ) :=
      {q : E × ℝ |
        q.2 • (((stereographic' n v).symm q.1 :
          Metric.sphere (0 : H) 1) : H) ∉ B₀}
    have hA : MeasurableSet A := by
      dsimp [A]
      measurability
    have hC : MeasurableSet C := by
      dsimp [C]
      measurability
    have hD : MeasurableSet D := by
      dsimp [D]
      have hmap :
          Measurable
            (fun q : E × ℝ =>
              q.2 • (((stereographic' n v).symm q.1 :
                Metric.sphere (0 : H) 1) : H)) := by
        simpa [stereographicPolarPatchMap_apply] using
          hT_meas.comp (measurable_snd.prodMk measurable_fst)
      exact hB₀_meas.compl.preimage hmap
    convert hA.compl.union (hC.compl.union hD) using 1
    ext q
    by_cases hqA : q ∈ A
    · by_cases hqC : q ∈ C
      · have h0 : 0 < q.2 := by
          simpa [A] using hqA
        have h1 : q.2 < 1 := by
          simpa [C] using hqC
        simp [A, C, D, h0, h1]
      · have hn1 : ¬ q.2 < 1 := by
          simpa [C] using hqC
        simp [A, C, D, hn1]
    · have hn0 : ¬ 0 < q.2 := by
        simpa [A] using hqA
      simp [A, C, D, hn0]
  have hswap :
      ∀ᵐ q ∂((MeasureTheory.volume : Measure E).prod
          (MeasureTheory.volume : Measure ℝ)),
        0 < q.2 → q.2 < 1 →
          q.2 • (((stereographic' n v).symm q.1 :
            Metric.sphere (0 : H) 1) : H) ∉ B₀ := by
    exact (Measure.ae_prod_iff_ae_ae hswap_meas).2 hangular
  have hprod :
      ∀ᵐ p ∂((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure E)),
        p ∈ stereographicPolarPatchCylinder n →
          stereographicPolarPatchMap v p ∉ B₀ := by
    have h :=
      (Measure.measurePreserving_swap
        (μ := (MeasureTheory.volume : Measure ℝ))
        (ν := (MeasureTheory.volume : Measure E))).quasiMeasurePreserving.tendsto_ae
        hswap
    filter_upwards [h] with p hp hpC
    exact hp hpC.1 hpC.2
  have hcylinder_meas :
      MeasurableSet (stereographicPolarPatchCylinder n : Set (ℝ × E)) := by
    dsimp [stereographicPolarPatchCylinder, E]
    measurability
  have hpre_ae :
      ∀ᵐ p ∂μC,
        p ∉ (stereographicPolarPatchMap (n := n) v ⁻¹' B₀) := by
    have hprod_volume :
        ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × E)),
          p ∈ stereographicPolarPatchCylinder n →
            stereographicPolarPatchMap v p ∉ B₀ := by
      simpa [Measure.volume_eq_prod, E] using hprod
    filter_upwards [ae_restrict_of_ae hprod_volume,
      ae_restrict_mem hcylinder_meas] with p hp hpC hpB
    exact hp hpC hpB
  have hpre_zero :
      μC (stereographicPolarPatchMap (n := n) v ⁻¹' B₀) = 0 := by
    simpa only [Set.mem_preimage, not_not] using ae_iff.mp hpre_ae
  have hmap_B₀ :
      Measure.map (stereographicPolarPatchMap (n := n) v) μC B₀ = 0 := by
    rw [Measure.map_apply hT_meas hB₀_meas]
    exact hpre_zero
  exact nonpos_iff_eq_zero.mp <|
    (measure_mono hB_subset_B₀).trans_eq hmap_B₀

/--
%%handwave
name:
  Compact finite distortion for stereographic polar coordinates
statement:
  On each compact subset of the polar cylinder \(0<r<1\), the pushforward of
  Euclidean measure by \((r,y)\mapsto r\sigma(y)\) is bounded by a finite
  multiple of Euclidean measure on any target set containing the compact
  image.
proof:
  The compact image stays away from the singular parts of the polar inverse.
  The explicit inverse \(z\mapsto (|z|,\operatorname{stereo}(z/|z|))\) is
  \(C^1\) near every point of the image, hence Lipschitz on the compact image
  after a finite cover.  Applying the finite-dimensional Lipschitz image
  estimate to this inverse, and accounting for a fixed linear coordinate
  equivalence, gives the claimed measure domination.
-/
private theorem stereographicPolarPatchMap_compactPull_cylinder_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1) :
    ∀ {K : Set (ℝ × EuclideanSpace ℝ (Fin n))} {Q : Set H},
      IsCompact K →
      K ⊆ stereographicPolarPatchCylinder n →
      stereographicPolarPatchMap v '' K ⊆ Q →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          Measure.map (stereographicPolarPatchMap (n := n) v)
              (MeasureTheory.volume.restrict K) ≤
            C • MeasureTheory.volume.restrict Q := by
  classical
  intro K Q hK hKU hTKQ
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let E : Type := EuclideanSpace ℝ (Fin n)
  let D : Type := ℝ × E
  have hDdim : Module.finrank ℝ D = Module.finrank ℝ H := by
    have hHdim : Module.finrank ℝ H = n + 1 := Fact.out
    dsimp [D, E]
    rw [hHdim]
    simp
    omega
  let L : D ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq hDdim
  haveI hDhaar :
      Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure D) := by
    dsimp [D, E]
    rw [Measure.volume_eq_prod]
    infer_instance
  let T : D → H := stereographicPolarPatchMap (n := n) v
  let S : H → D := stereographicPolarPatchInv (n := n) v
  let F : H → H := fun z => L (S z)
  let I : Set H := T '' K
  have hT_cont : Continuous T :=
    continuous_stereographicPolarPatchMap (n := n) v
  have hT_meas : Measurable T := hT_cont.measurable
  have hI_compact : IsCompact I := by
    simpa [I, T] using hK.image_of_continuousOn hT_cont.continuousOn
  have hF_loc : LocallyLipschitzOn I F := by
    intro z hzI
    rcases hzI with ⟨p, hpK, rfl⟩
    rcases p with ⟨r, y⟩
    have hpC : (r, y) ∈ stereographicPolarPatchCylinder n := hKU hpK
    have hr_pos : 0 < r := hpC.1
    have hz_ne :
        stereographicPolarPatchMap (n := n) v (r, y) ≠ (0 : H) := by
      intro hz0
      have hnorm_zero :
          ‖stereographicPolarPatchMap (n := n) v (r, y)‖ = (0 : ℝ) := by
        rw [hz0, norm_zero]
      have hnorm_pos :
          ‖stereographicPolarPatchMap (n := n) v (r, y)‖ = r := by
        rw [norm_stereographicPolarPatchMap (n := n) v r y,
          abs_of_pos hr_pos]
      have hr_zero : r = 0 := by
        rw [← hnorm_pos, hnorm_zero]
      exact (ne_of_gt hr_pos) hr_zero
    have hsource :
        stereographicPolarPatchUnit v
            (stereographicPolarPatchMap (n := n) v (r, y)) ∈
          (stereographic' n v).source := by
      have htarget : y ∈ (stereographic' n v).target := by
        simp [stereographic'_target]
      simpa [stereographicPolarPatchUnit_apply_map (n := n) v hr_pos y] using
        (stereographic' n v).map_target htarget
    have hcd :
        ContDiffAt ℝ 1 F
          (stereographicPolarPatchMap (n := n) v (r, y)) := by
      have htop :
          ContDiffAt ℝ ⊤
            (fun z : H => L (stereographicPolarPatchInv (n := n) v z))
            (stereographicPolarPatchMap (n := n) v (r, y)) :=
        contDiffAt_stereographicPolarPatchInv_of_mem_source
          (n := n) v L hz_ne hsource
      simpa [F, S] using
        htop.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
    rcases hcd.exists_lipschitzOnWith with ⟨M, t, ht, hLip⟩
    exact ⟨M, t, mem_nhdsWithin_of_mem_nhds ht, hLip⟩
  rcases hF_loc.exists_lipschitzOnWith_of_compact hI_compact with
    ⟨M, hF_lip⟩
  rcases
    lipschitzOnWith_volume_image_le_smul
      (H := H) (A := I) (F := F) hF_lip with
    ⟨Cinv, hCinv_ne_top, hF_image_le⟩
  let μD : Measure D := MeasureTheory.volume
  let μH : Measure H := MeasureTheory.volume
  haveI hmap_haar :
      Measure.IsAddHaarMeasure
        (Measure.map (L : D → H) μD) := by
    simpa using L.isAddHaarMeasure_map μD
  let c : ℝ≥0 :=
    MeasureTheory.Measure.addHaarScalarFactor
      (Measure.map (L : D → H) μD) μH
  have hmapL :
      Measure.map (L : D → H) μD = c • μH := by
    simpa [c, μD, μH] using
      (MeasureTheory.Measure.isAddLeftInvariant_eq_smul
        (Measure.map (L : D → H) μD) μH)
  refine ⟨(c : ℝ≥0∞) * Cinv, ?_, ?_⟩
  · have hCinv_lt_top : Cinv < (∞ : ℝ≥0∞) := lt_top_iff_ne_top.mpr hCinv_ne_top
    exact (ENNReal.mul_lt_top (ENNReal.coe_lt_top : (c : ℝ≥0∞) < (∞ : ℝ≥0∞))
      hCinv_lt_top).ne
  refine Measure.le_iff.2 ?_
  intro B hB
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    hT_meas.aemeasurable
  rw [Measure.map_apply_of_aemeasurable hT_aemeas_K hB,
    Measure.smul_apply, Measure.restrict_apply (hB.preimage hT_meas),
    Measure.restrict_apply hB]
  let A : Set D := T ⁻¹' B ∩ K
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    exact (hB.preimage hT_meas).inter hK.measurableSet
  have hLA_meas : MeasurableSet (L '' A) :=
    L.toHomeomorph.measurableEmbedding.measurableSet_image' hA_meas
  have hL_preimage :
      ((L : D →ₗ[ℝ] H) ⁻¹' (L '' A)) = A := by
    exact L.injective.preimage_image A
  have hA_measure :
      μD A = (c : ℝ≥0∞) * μH (L '' A) := by
    have hmap_apply :
        Measure.map (L : D → H) μD (L '' A) = μD A := by
      rw [Measure.map_apply L.continuous.measurable hLA_meas]
      rw [L.injective.preimage_image]
    calc
      μD A =
          Measure.map (L : D → H) μD (L '' A) := by
            exact hmap_apply.symm
      _ = (c • μH) (L '' A) := by
            rw [hmapL]
      _ = (c : ℝ≥0∞) * μH (L '' A) := by rfl
  have hLA_subset :
      L '' A ⊆ F '' (B ∩ I) := by
    rintro q ⟨p, hpA, rfl⟩
    rcases hpA with ⟨hpB, hpK⟩
    refine ⟨T p, ⟨hpB, ⟨p, hpK, rfl⟩⟩, ?_⟩
    rcases p with ⟨r, y⟩
    have hpC : (r, y) ∈ stereographicPolarPatchCylinder n := hKU hpK
    have hr_pos : 0 < r := hpC.1
    simp [F, S, T, stereographicPolarPatchInv_apply_map (n := n) v hr_pos y]
  have hI_Q : I ⊆ Q := by
    simpa [I, T] using hTKQ
  calc
    MeasureTheory.volume (T ⁻¹' B ∩ K)
        = μD A := by rfl
    _ = (c : ℝ≥0∞) * μH (L '' A) := hA_measure
    _ ≤ c * μH (F '' (B ∩ I)) :=
        mul_le_mul_right (measure_mono hLA_subset) (c : ℝ≥0∞)
    _ ≤ (c : ℝ≥0∞) * (Cinv * μH (B ∩ I)) :=
        mul_le_mul_right (hF_image_le (B ∩ I) Set.inter_subset_right) (c : ℝ≥0∞)
    _ ≤ (c : ℝ≥0∞) * (Cinv * μH (B ∩ Q)) := by
        exact mul_le_mul_right
          (mul_le_mul_right
            (measure_mono (Set.inter_subset_inter_right B hI_Q)) Cinv) (c : ℝ≥0∞)
    _ = ((c : ℝ≥0∞) * Cinv) * MeasureTheory.volume (B ∩ Q) := by
        simp [μH, mul_assoc]

/--
%%handwave
name:
  Measurability of the radial derivative in stereographic polar coordinates
statement:
  If the weak derivative field is square-integrable on the unit ball, then
  its radial component, pulled back by a stereographic polar chart, is
  measurable up to null sets on the cylinder \(0<r<1\).
proof:
  The derivative field has a measurable representative on the ball.  The polar
  chart is smooth, and its change-of-variables map sends the product measure
  on the cylinder absolutely continuously to Lebesgue measure on the ball.
  Composing with the measurable representative therefore gives an
  almost-everywhere measurable radial component.
-/
theorem stereographicPolarPatch_radialDerivative_aestronglyMeasurable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {du : H → H →L[ℝ] ℝ}
    (_hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    AEStronglyMeasurable
      (stereographicPolarPatchRadialDerivative v du)
      (MeasureTheory.volume.restrict
        (stereographicPolarPatchCylinder n)) := by
  classical
  let μC : Measure (ℝ × EuclideanSpace ℝ (Fin n)) :=
    MeasureTheory.volume.restrict (stereographicPolarPatchCylinder n)
  have hqmp :
      Measure.QuasiMeasurePreserving
        (stereographicPolarPatchMap (n := n) v)
        μC
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
    simpa [μC] using
      stereographicPolarPatchMap_quasiMeasurePreserving_cylinder_unitBall
        (n := n) v
  have hdu_comp :
      AEStronglyMeasurable
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          du (stereographicPolarPatchMap v p)) μC := by
    simpa [Function.comp_def] using
      _hdu.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  have hdir :
      AEStronglyMeasurable
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          (((stereographic' n v).symm p.2 :
            Metric.sphere (0 : H) 1) : H)) μC := by
    have hmeas :
        Measurable
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            (((stereographic' n v).symm p.2 :
              Metric.sphere (0 : H) 1) : H)) := by
      exact
        ((contDiff_stereographic'_symm_coe (n := n) v).continuous.measurable).comp
          measurable_snd
    exact hmeas.aestronglyMeasurable
  have hval :
      AEStronglyMeasurable
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          du (stereographicPolarPatchMap v p)
            (((stereographic' n v).symm p.2 :
              Metric.sphere (0 : H) 1) : H)) μC := by
    simpa using
      (ContinuousLinearMap.apply ℝ ℝ).flip.aestronglyMeasurable_comp₂
        hdu_comp hdir
  simpa [μC, stereographicPolarPatchRadialDerivative] using hval

/--
%%handwave
name:
  Pulling a weak derivative through a stereographic polar chart
statement:
  Let \(u\) be a scalar Sobolev function on the unit ball with weak derivative
  \(Du\).  On the stereographic polar cylinder \(0<r<1\), the pullback
  \(U(r,y)=u(r\sigma(y))\) has weak derivative obtained by composing
  \(Du(r\sigma(y))\) with the derivative of the polar coordinate map.
proof:
  The polar coordinate map is smooth and locally bi-Lipschitz on the cylinder,
  with inverse given by radius and stereographic angular coordinate.  Its
  image is an open subregion of the ball.  Restrict the weak-derivative
  identity to this image and apply
  [weak derivatives pull back under locally bi-Lipschitz coordinate changes](lean:JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues.comp_locallyBiLipschitz).
-/
private theorem scalarWeakSobolev_stereographic_polar_patch_pullback_weakDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u du)
    (_hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      (stereographicPolarPatchCylinder n)
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        u (stereographicPolarPatchMap v p))
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        (du (stereographicPolarPatchMap v p)).comp
          (fderiv ℝ (stereographicPolarPatchMap v) p)) := by
  classical
  have hC_open :
      IsOpen (stereographicPolarPatchCylinder n :
        Set (ℝ × EuclideanSpace ℝ (Fin n))) := by
    dsimp [stereographicPolarPatchCylinder]
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  haveI hProdHaar :
      Measure.IsAddHaarMeasure
        (MeasureTheory.volume :
          Measure (ℝ × EuclideanSpace ℝ (Fin n))) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  exact
    IsWeakDerivativeOnEuclideanRegionWithValues.comp_contDiff_qmp
      (U := stereographicPolarPatchCylinder n)
      (Ω := Metric.ball (0 : H) 1)
      (T := stereographicPolarPatchMap (n := n) v)
      hC_open
      Metric.isOpen_ball
      (stereographicPolarPatchMap_mapsTo_cylinder_unitBall (n := n) v)
      (contDiff_stereographicPolarPatchMap (n := n) v)
      (stereographicPolarPatchMap_quasiMeasurePreserving_cylinder_unitBall
        (n := n) v)
      (stereographicPolarPatchMap_compactPull_cylinder_unitBall
        (n := n) v)
      _hweak _hu _hdu

/--
%%handwave
name:
  Polar-coordinate slices have the one-dimensional weak derivative
statement:
  Let \(u\) be a scalar Sobolev function on the unit ball with weak derivative
  \(Du\).  For almost every stereographic transverse coordinate \(y\), the
  radial function \(r\mapsto u(r\sigma(y))\) has one-dimensional weak
  derivative \(r\mapsto Du(r\sigma(y))\sigma(y)\) on \((0,1)\).
proof:
  Pull the integration-by-parts identity back through the smooth polar chart.
  The derivative of the chart in the radial coordinate is \(\sigma(y)\).
  Fubini then gives the one-dimensional distributional identity on almost
  every vertical fiber.
-/
theorem scalarWeakSobolev_stereographic_polar_patch_fiberwise_realWeakDerivative_from_polar_chart_slices
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u du)
    (_hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
      IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
        (fun r : ℝ => u (stereographicPolarPatchMap v (r, y)))
        (fun r : ℝ =>
          stereographicPolarPatchRadialDerivative v du (r, y)) := by
  classical
  let U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p => u (stereographicPolarPatchMap v p)
  let DU :
      ℝ × EuclideanSpace ℝ (Fin n) →
        (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    fun p =>
      (du (stereographicPolarPatchMap v p)).comp
        (fderiv ℝ (stereographicPolarPatchMap v) p)
  have hpull :
      IsWeakDerivativeOnEuclideanRegionWithValues
        {p : ℝ × EuclideanSpace ℝ (Fin n) | 0 < p.1 ∧ p.1 < 1}
        U DU := by
    simpa [U, DU, stereographicPolarPatchCylinder] using
      scalarWeakSobolev_stereographic_polar_patch_pullback_weakDerivative
        (n := n) v _hweak _hu _hdu
  have hslices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
        IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
          (fun r : ℝ => U (r, y))
          (fun r : ℝ =>
            DU (r, y) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))) :=
    scalarWeakSobolev_firstCoordinate_fiberwise_realWeakDerivative_on_unit_strip
      (E := EuclideanSpace ℝ (Fin n)) (U := U) (DU := DU) hpull
  filter_upwards [hslices] with y hy
  have hG :
      (fun r : ℝ =>
          DU (r, y) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))) =
        (fun r : ℝ =>
          stereographicPolarPatchRadialDerivative v du (r, y)) := by
    funext r
    simpa [DU, stereographicPolarPatchRadialDerivative] using
      stereographicPolarPatchMap_pullback_firstCoordinate_derivative
        (n := n) v du (r, y)
  rw [hG] at hy
  simpa [U] using hy

/--
%%handwave
name:
  Explicit ACL representatives on almost every vertical unit strip
statement:
  Let \(U\) be a measurable scalar function on \((0,1)\times E\), and let
  \(G\) be an almost-everywhere measurable function on the same strip.  If for
  almost every transverse coordinate \(y\), the function \(r\mapsto U(r,y)\)
  has one-dimensional weak derivative \(r\mapsto G(r,y)\) on \((0,1)\), then
  there is a jointly measurable representative \(\widetilde U\), equal to
  \(U\) almost everywhere on the strip, such that almost every vertical slice
  is absolutely continuous on compact subintervals and has derivative \(G\)
  almost everywhere.
proof:
  On each good vertical line, \(U-\int G\) is almost everywhere constant.
  Choose this constant by averaging over a fixed interior interval, so the
  constant depends measurably on the transverse variable.  The resulting
  representative is the corresponding primitive; Fubini gives equality with
  \(U\) almost everywhere on the strip.
-/
theorem scalarWeakSobolev_firstCoordinate_explicit_acl_representative_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U G : ℝ × E → ℝ}
    (_hU_meas : Measurable U)
    (_hG_aemeas : AEStronglyMeasurable G
      (MeasureTheory.volume.restrict
        {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}))
    (hweak_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
          (fun r : ℝ => U (r, y)) (fun r : ℝ => G (r, y))) :
    ∃ Uacl : ℝ × E → ℝ,
      Measurable Uacl ∧
      Uacl =ᵐ[MeasureTheory.volume.restrict
          {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}] U ∧
        ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            AbsolutelyContinuousOnInterval
              (fun ρ : ℝ => Uacl (ρ, y)) r s ∧
            ∀ᵐ t ∂MeasureTheory.volume,
              t ∈ Set.uIcc r s →
                HasDerivAt
                  (fun ρ : ℝ => Uacl (ρ, y)) (G (t, y)) t := by
  classical
  let G₀ : ℝ × E → ℝ := _hG_aemeas.mk G
  let Uacl : ℝ × E → ℝ := firstCoordinateAnchoredRepresentative U G₀
  have hG₀_meas : Measurable G₀ := by
    dsimp [G₀]
    exact _hG_aemeas.measurable_mk
  have hG₀_eq :
      G₀ =ᵐ[MeasureTheory.volume.restrict
        {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}] G := by
    dsimp [G₀]
    exact _hG_aemeas.ae_eq_mk.symm
  refine ⟨Uacl, ?_, ?_, ?_⟩
  · dsimp [Uacl]
    exact firstCoordinateAnchoredRepresentative_measurable
      (U := U) (G := G₀) _hU_meas hG₀_meas
  · dsimp [Uacl]
    exact firstCoordinateAnchoredRepresentative_ae_eq_on_unit_strip
      (U := U) (G := G) (G₀ := G₀)
      _hU_meas hG₀_meas hG₀_eq hweak_slices
  · dsimp [Uacl]
    exact firstCoordinateAnchoredRepresentative_linewise_acl_on_unit_strip
      (U := U) (G := G) (G₀ := G₀)
      hG₀_meas hG₀_eq hweak_slices

/--
%%handwave
name:
  Coordinate ACL representatives from polar-coordinate slices
statement:
  Let \(u\) be a measurable scalar Sobolev function on the unit ball.  In the
  flat cylinder coordinates \((r,y)\mapsto r\sigma(y)\), there is a jointly
  measurable representative \(\widetilde U(r,y)\), equal almost everywhere to
  \(u(r\sigma(y))\) on the cylinder \(0<r<1\), such that for almost every
  transverse coordinate \(y\), the function \(r\mapsto \widetilde U(r,y)\) is
  absolutely continuous on compact subintervals of \((0,1)\) and has
  derivative \(Du(r\sigma(y))\sigma(y)\) almost everywhere.
proof:
  Pull the weak derivative identity through the smooth polar chart.  Fubini
  gives the one-dimensional weak derivative identity on almost every vertical
  fiber.  Choose the primitive representative on each good fiber using a fixed
  interior averaging anchor; this makes the additive constants measurable in
  the transverse variable.
-/
theorem scalarWeakSobolev_stereographic_polar_patch_coordinate_linewise_acl_representative_from_polar_chart_slices
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u du)
    (_hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hu_meas : Measurable u) :
    ∃ Uacl : ℝ × EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable Uacl ∧
      Uacl =ᵐ[MeasureTheory.volume.restrict
          (stereographicPolarPatchCylinder n)]
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          u (stereographicPolarPatchMap v p)) ∧
        ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            AbsolutelyContinuousOnInterval
              (fun ρ : ℝ => Uacl (ρ, y)) r s ∧
            ∀ᵐ t ∂MeasureTheory.volume,
              t ∈ Set.uIcc r s →
                HasDerivAt
                  (fun ρ : ℝ => Uacl (ρ, y))
                  (du (stereographicPolarPatchMap v (t, y))
                    (((stereographic' n v).symm y :
                      Metric.sphere (0 : H) 1) : H)) t := by
  let U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p => u (stereographicPolarPatchMap v p)
  let G : ℝ × EuclideanSpace ℝ (Fin n) → ℝ :=
    stereographicPolarPatchRadialDerivative v du
  have hU_meas : Measurable U := by
    dsimp [U]
    exact _hu_meas.comp (continuous_stereographicPolarPatchMap (n := n) v).measurable
  have hG_aemeas :
      AEStronglyMeasurable G
        (MeasureTheory.volume.restrict
          {p : ℝ × EuclideanSpace ℝ (Fin n) |
            0 < p.1 ∧ p.1 < 1}) := by
    have hG :=
      stereographicPolarPatch_radialDerivative_aestronglyMeasurable
        (n := n) v _hdu
    simpa [G, stereographicPolarPatchCylinder] using hG
  have hweak_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
        IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
          (fun r : ℝ => U (r, y)) (fun r : ℝ => G (r, y)) := by
    simpa [U, G] using
      scalarWeakSobolev_stereographic_polar_patch_fiberwise_realWeakDerivative_from_polar_chart_slices
        (n := n) v _hweak _hu _hdu
  rcases
    scalarWeakSobolev_firstCoordinate_explicit_acl_representative_on_unit_strip
      (E := EuclideanSpace ℝ (Fin n)) (U := U) (G := G)
      hU_meas hG_aemeas hweak_slices with
    ⟨Uacl, hUacl_meas, hUacl_eq, hUacl_line⟩
  refine ⟨Uacl, hUacl_meas, ?_, ?_⟩
  · simpa [U, stereographicPolarPatchCylinder] using hUacl_eq
  · filter_upwards [hUacl_line] with y hy
    intro r s hr hrs hs
    simpa [G, stereographicPolarPatchRadialDerivative] using hy r s hr hrs hs

/--
%%handwave
name:
  Coordinate ACL representatives transfer to the ball
statement:
  Suppose a jointly measurable representative has been constructed in the
  stereographic polar cylinder and agrees almost everywhere with the pulled
  back Sobolev function.  Then it can be pushed forward to a measurable
  representative on the ball, equal almost everywhere to the original
  function, and its vertical absolute-continuity and derivative statements
  become the corresponding radial statements in the ball.
proof:
  Use the polar inverse on the image of the chart and leave the original
  measurable representative elsewhere.  The polar chart is injective on the
  cylinder, and it maps product-null exceptional sets to Haar-null sets; hence
  the pushed representative still agrees almost everywhere with the original
  function in the ball.
-/
theorem scalarWeakSobolev_stereographic_polar_patch_linewise_acl_representative_of_coordinate_linewise_acl
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    {Uacl : ℝ × EuclideanSpace ℝ (Fin n) → ℝ}
    (_hu_meas : Measurable u)
    (_hUacl_meas : Measurable Uacl)
    (_hUacl_ae :
      Uacl =ᵐ[MeasureTheory.volume.restrict
          (stereographicPolarPatchCylinder n)]
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          u (stereographicPolarPatchMap v p)))
    (hline :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ r s : ℝ, 0 < r → r < s → s < 1 →
          AbsolutelyContinuousOnInterval
            (fun ρ : ℝ => Uacl (ρ, y)) r s ∧
          ∀ᵐ t ∂MeasureTheory.volume,
            t ∈ Set.uIcc r s →
              HasDerivAt
                (fun ρ : ℝ => Uacl (ρ, y))
                (du (stereographicPolarPatchMap v (t, y))
                  (((stereographic' n v).symm y :
                    Metric.sphere (0 : H) 1) : H)) t) :
    ∃ uacl : H → ℝ,
      Measurable uacl ∧
      uacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] u ∧
        ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            AbsolutelyContinuousOnInterval
              (fun ρ : ℝ => uacl (stereographicPolarPatchMap v (ρ, y))) r s ∧
            ∀ᵐ t ∂MeasureTheory.volume,
              t ∈ Set.uIcc r s →
                HasDerivAt
                  (fun ρ : ℝ =>
                    uacl (stereographicPolarPatchMap v (ρ, y)))
                  (du (stereographicPolarPatchMap v (t, y))
                    (((stereographic' n v).symm y :
                      Metric.sphere (0 : H) 1) : H)) t := by
  classical
  let D : Type := ℝ × EuclideanSpace ℝ (Fin n)
  let C : Set D := stereographicPolarPatchCylinder n
  let T : D → H := stereographicPolarPatchMap (n := n) v
  let S : H → D := stereographicPolarPatchInv (n := n) v
  let V : Set H := {z | S z ∈ C ∧ T (S z) = z}
  let uacl : H → ℝ := fun z ↦ if z ∈ V then Uacl (S z) else u z
  have hC_meas : MeasurableSet C := by
    dsimp [C, stereographicPolarPatchCylinder]
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  have hS_meas : Measurable S := by
    simpa [S] using measurable_stereographicPolarPatchInv (n := n) v
  have hT_meas : Measurable T := by
    simpa [T] using
      (continuous_stereographicPolarPatchMap (n := n) v).measurable
  have hV_meas : MeasurableSet V := by
    have hSC : MeasurableSet {z : H | S z ∈ C} :=
      hS_meas hC_meas
    have hTS_eq : MeasurableSet {z : H | T (S z) = z} :=
      measurableSet_eq_fun (hT_meas.comp hS_meas) measurable_id
    exact hSC.inter hTS_eq
  have huacl_meas : Measurable uacl := by
    dsimp [uacl]
    exact Measurable.ite hV_meas (_hUacl_meas.comp hS_meas) _hu_meas
  have hbad_restrict :
      (MeasureTheory.volume.restrict C)
        {p : D | Uacl p ≠ u (T p)} = 0 := by
    simpa [C, T, ae_iff] using _hUacl_ae
  have hbad_zero :
      (MeasureTheory.volume : Measure D)
        (C ∩ {p : D | Uacl p ≠ u (T p)}) = 0 := by
    rw [Measure.restrict_apply' hC_meas] at hbad_restrict
    simpa [Set.inter_comm] using hbad_restrict
  have hbad_image_zero :
      (MeasureTheory.volume : Measure H)
        (T '' (C ∩ {p : D | Uacl p ≠ u (T p)})) = 0 := by
    simpa [T, D] using
      stereographicPolarPatchMap_image_volume_null
        (n := n) v (S := C ∩ {p : D | Uacl p ≠ u (T p)}) hbad_zero
  have hnot_bad_image :
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)),
        z ∉ T '' (C ∩ {p : D | Uacl p ≠ u (T p)}) := by
    have hzero_restrict :
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))
          (T '' (C ∩ {p : D | Uacl p ≠ u (T p)})) = 0 := by
      have hle :
          (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))
              (T '' (C ∩ {p : D | Uacl p ≠ u (T p)})) ≤
            (MeasureTheory.volume : Measure H)
              (T '' (C ∩ {p : D | Uacl p ≠ u (T p)})) :=
        Measure.le_iff'.1 Measure.restrict_le_self _
      exact le_antisymm (hbad_image_zero ▸ hle) zero_le
    simpa [ae_iff, Set.image, and_assoc] using hzero_restrict
  have huacl_eq :
      uacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] u := by
    filter_upwards [hnot_bad_image] with z hz_not_bad
    by_cases hzV : z ∈ V
    · have hSzC : S z ∈ C := hzV.1
      have hTSz : T (S z) = z := hzV.2
      have hgood : Uacl (S z) = u (T (S z)) := by
        by_contra hbad
        exact hz_not_bad ⟨S z, ⟨hSzC, hbad⟩, hTSz⟩
      simp [uacl, hzV, hgood, hTSz]
    · simp [uacl, hzV]
  have hmap_mem_V :
      ∀ {ρ : ℝ} (y : EuclideanSpace ℝ (Fin n)),
        0 < ρ → ρ < 1 → T (ρ, y) ∈ V := by
    intro ρ y hρ_pos hρ_lt
    have hS_apply : S (T (ρ, y)) = (ρ, y) := by
      simpa [S, T] using
        stereographicPolarPatchInv_apply_map (n := n) v hρ_pos y
    constructor
    · simpa [C, hS_apply, stereographicPolarPatchCylinder] using
        And.intro hρ_pos hρ_lt
    · simp [hS_apply]
  have huacl_map :
      ∀ {ρ : ℝ} (y : EuclideanSpace ℝ (Fin n)),
        0 < ρ → ρ < 1 → uacl (T (ρ, y)) = Uacl (ρ, y) := by
    intro ρ y hρ_pos hρ_lt
    have hzV : T (ρ, y) ∈ V := hmap_mem_V y hρ_pos hρ_lt
    have hS_apply : S (T (ρ, y)) = (ρ, y) := by
      simpa [S, T] using
        stereographicPolarPatchInv_apply_map (n := n) v hρ_pos y
    simp [uacl, hzV, hS_apply]
  refine ⟨uacl, huacl_meas, huacl_eq, ?_⟩
  filter_upwards [hline] with y hy
  intro r s hr_pos hrs hs_lt
  rcases hy r s hr_pos hrs hs_lt with ⟨hacl, hderiv⟩
  have hinterval_eq :
      ∀ ρ : ℝ, ρ ∈ Set.uIcc r s →
        uacl (T (ρ, y)) = Uacl (ρ, y) := by
    intro ρ hρ
    have hρIcc : ρ ∈ Set.Icc r s := by
      simpa [Set.uIcc_of_le hrs.le] using hρ
    exact huacl_map y (lt_of_lt_of_le hr_pos hρIcc.1)
      (lt_of_le_of_lt hρIcc.2 hs_lt)
  constructor
  · exact
      absolutelyContinuousOnInterval_congr_on_uIcc
        (f := fun ρ : ℝ => Uacl (ρ, y))
        (h := fun ρ : ℝ => uacl (T (ρ, y)))
        hacl (fun ρ hρ => (hinterval_eq ρ hρ).symm)
  · filter_upwards [hderiv] with t ht htmem
    have htIcc : t ∈ Set.Icc r s := by
      simpa [Set.uIcc_of_le hrs.le] using htmem
    have ht_pos : 0 < t := lt_of_lt_of_le hr_pos htIcc.1
    have ht_lt : t < 1 := lt_of_le_of_lt htIcc.2 hs_lt
    have htd :
        HasDerivAt (fun ρ : ℝ => Uacl (ρ, y))
          (du (stereographicPolarPatchMap v (t, y))
            (((stereographic' n v).symm y :
              Metric.sphere (0 : H) 1) : H)) t :=
      ht htmem
    have hevent :
        (fun ρ : ℝ => uacl (T (ρ, y))) =ᶠ[𝓝 t]
          fun ρ : ℝ => Uacl (ρ, y) := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨ht_pos, ht_lt⟩] with ρ hρ
      exact huacl_map y hρ.1 hρ.2
    simpa [T] using htd.congr_of_eventuallyEq hevent

/--
%%handwave
name:
  ACL representatives from polar-coordinate slices
statement:
  Let \(u\) be a measurable scalar Sobolev function on the unit ball with weak
  derivative \(Du\).  In a stereographic polar chart, one can choose a
  measurable representative \(\tilde u\), equal to \(u\) almost everywhere in
  the ball, such that for almost every transverse coordinate \(y\), the
  radial function \(r\mapsto \tilde u(r\sigma(y))\) is absolutely continuous
  on every compact subinterval of \((0,1)\), and its derivative is
  \(Du(r\sigma(y))\sigma(y)\) almost everywhere.
proof:
  Pull the weak-derivative identity back through the polar chart.  The
  derivative of the chart in the radial coordinate is \(\sigma(y)\).  Fubini
  gives a one-dimensional weak derivative on almost every vertical slice; the
  one-dimensional Sobolev representative theorem then supplies the desired
  absolutely continuous representative on those slices.
-/
theorem scalarWeakSobolev_stereographic_polar_patch_linewise_acl_representative_from_polar_chart_slices
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u du)
    (_hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hu_meas : Measurable u) :
    ∃ uacl : H → ℝ,
      Measurable uacl ∧
      uacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] u ∧
        ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            AbsolutelyContinuousOnInterval
              (fun ρ : ℝ => uacl (stereographicPolarPatchMap v (ρ, y))) r s ∧
            ∀ᵐ t ∂MeasureTheory.volume,
              t ∈ Set.uIcc r s →
                HasDerivAt
                  (fun ρ : ℝ =>
                    uacl (stereographicPolarPatchMap v (ρ, y)))
                  (du (stereographicPolarPatchMap v (t, y))
                    (((stereographic' n v).symm y :
                      Metric.sphere (0 : H) 1) : H)) t := by
  rcases
    scalarWeakSobolev_stereographic_polar_patch_coordinate_linewise_acl_representative_from_polar_chart_slices
      (n := n) v _hweak _hu _hdu _hu_meas with
    ⟨Uacl, hUacl_meas, hUacl_ae, hline⟩
  exact
    scalarWeakSobolev_stereographic_polar_patch_linewise_acl_representative_of_coordinate_linewise_acl
      (n := n) v _hu_meas hUacl_meas hUacl_ae hline

/--
%%handwave
name:
  Vertical ACL representatives from polar-coordinate slices
statement:
  Let \(u\) be a measurable scalar \(W^{1,2}\) function on the unit ball with
  weak derivative \(Du\).  Pulling \(u\) back by a stereographic polar chart
  \((r,y)\mapsto r\sigma(y)\), choosing the one-dimensional ACL
  representative on almost every vertical line, and pushing this choice back
  gives a measurable representative \(\tilde u\), equal to \(u\) almost
  everywhere in the ball, such that for almost every transverse coordinate
  \(y\) and every \(0<r<s<1\),
  \[
    |\tilde u(r\sigma(y))-\tilde u(s\sigma(y))|
      \le \int_r^s |Du(t\sigma(y))\sigma(y)|\,dt .
  \]
proof:
  Pull the weak-derivative identity through the polar coordinate map.  The
  derivative in the radial coordinate is \(\sigma(y)\).  Fubini gives the
  one-dimensional weak derivative identity on almost every vertical fiber.
  On those fibers, apply the one-dimensional Sobolev representative theorem
  and choose the primitive representative; the polar coordinate map transfers
  this representative back to the ball.
-/
theorem scalarWeakSobolev_stereographic_polar_patch_acl_representative_from_polar_chart_slices
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u du)
    (_hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hu_meas : Measurable u) :
    ∃ uacl : H → ℝ,
      Measurable uacl ∧
      uacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] u ∧
        ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖uacl (stereographicPolarPatchMap v (r, y)) -
                uacl (stereographicPolarPatchMap v (s, y))‖ ≤
              ∫⁻ t in {t : ℝ | r < t ∧ t < s},
                ENNReal.ofReal
                  ‖du (stereographicPolarPatchMap v (t, y))
                    (((stereographic' n v).symm y :
                      Metric.sphere (0 : H) 1) : H)‖
                ∂MeasureTheory.volume := by
  rcases
    scalarWeakSobolev_stereographic_polar_patch_linewise_acl_representative_from_polar_chart_slices
      (n := n) v _hweak _hu _hdu _hu_meas with
    ⟨uacl, huacl_meas, huacl_ae, hline⟩
  refine ⟨uacl, huacl_meas, huacl_ae, ?_⟩
  exact
    scalarWeakSobolev_stereographic_polar_patch_bound_of_linewise_acl
      (n := n) v hline

/--
%%handwave
name:
  Vertical ACL representative for a measurable weak Sobolev function
statement:
  Let \(u\) be a measurable scalar \(W^{1,2}\) function on the unit ball with
  weak derivative \(Du\).  There is a measurable representative
  \(\tilde u\), equal to \(u\) almost everywhere in the ball, such that in a
  stereographic polar chart \((r,y)\mapsto r\sigma(y)\), for almost every
  transverse coordinate \(y\), the function \(\tilde u\) satisfies for every
  \(0<r<s<1\)
  \[
    |\tilde u(r\sigma(y))-\tilde u(s\sigma(y))|
      \le \int_r^s |Du(t\sigma(y))\sigma(y)|\,dt .
  \]
proof:
  Apply [the representative obtained from the polar-coordinate vertical slices](lean:JJMath.Uniformization.scalarWeakSobolev_stereographic_polar_patch_acl_representative_from_polar_chart_slices).
-/
theorem scalarWeakSobolev_stereographic_polar_patch_full_vertical_acl_bound_of_weak_measurable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u du)
    (_hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hu_meas : Measurable u) :
    ∃ uacl : H → ℝ,
      Measurable uacl ∧
      uacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] u ∧
        ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖uacl (stereographicPolarPatchMap v (r, y)) -
                uacl (stereographicPolarPatchMap v (s, y))‖ ≤
              ∫⁻ t in {t : ℝ | r < t ∧ t < s},
                ENNReal.ofReal
                  ‖du (stereographicPolarPatchMap v (t, y))
                    (((stereographic' n v).symm y :
                      Metric.sphere (0 : H) 1) : H)‖
                ∂MeasureTheory.volume := by
  exact
    scalarWeakSobolev_stereographic_polar_patch_acl_representative_from_polar_chart_slices
      (n := n) v _hweak _hu _hdu _hu_meas

/--
%%handwave
name:
  Vertical ACL representative from a fixed measurable representative
statement:
  Let \(w\) be a scalar \(W^{1,2}\) function on the unit ball and let
  \(w_0\) be a measurable representative equal to \(w\) almost everywhere in the
  ball.  There is a measurable ACL representative \(\tilde w\), equal to
  \(w_0\) almost everywhere, such that in a stereographic polar chart
  \((r,y)\mapsto r\sigma(y)\), for almost every transverse coordinate \(y\),
  the representative \(\tilde w\) satisfies for every \(0<r<s<1\)
  \[
    |\tilde w(r\sigma(y))-\tilde w(s\sigma(y))|
      \le \int_r^s |Dw(t\sigma(y))\sigma(y)|\,dt .
  \]
proof:
  The measurable representative has the same weak derivative as \(w\), since
  it agrees with \(w\) almost everywhere in the weak-derivative region.  Apply
  the measurable weak Sobolev representative statement in the polar chart.
-/
theorem scalarWeakSobolev_stereographic_polar_patch_full_vertical_acl_bound_of_measurable_representative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {w wpatch : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hwpatch_meas : Measurable wpatch)
    (_hwpatch_eq :
      wpatch =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w) :
    ∃ wacl : H → ℝ,
      Measurable wacl ∧
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] wpatch ∧
        ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖wacl (stereographicPolarPatchMap v (r, y)) -
                wacl (stereographicPolarPatchMap v (s, y))‖ ≤
              ∫⁻ t in {t : ℝ | r < t ∧ t < s},
                ENNReal.ofReal
                  ‖dw (stereographicPolarPatchMap v (t, y))
                    (((stereographic' n v).symm y :
                      Metric.sphere (0 : H) 1) : H)‖
                ∂MeasureTheory.volume := by
  have hweak_patch :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball (0 : H) 1) wpatch dw :=
    _hweak.congr_ae _hwpatch_eq
  have hwpatch : MemLp wpatch 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) :=
    (memLp_congr_ae _hwpatch_eq).2 _hw
  exact
    scalarWeakSobolev_stereographic_polar_patch_full_vertical_acl_bound_of_weak_measurable
      (n := n) v hweak_patch hwpatch _hdw _hwpatch_meas

/--
%%handwave
name:
  Full vertical ACL representative in a stereographic polar chart
statement:
  After pulling a scalar \(W^{1,2}\) function on the unit ball back by
  \((r,y)\mapsto r\sigma(y)\), there is one measurable representative on the
  ball, equal almost everywhere to the original function, such that for almost
  every transverse coordinate \(y\) the restriction to the vertical line
  \(0<r<1\) is absolutely continuous and satisfies, for every
  \(0<r<s<1\), the radial derivative integral bound.
proof:
  Pull the weak-derivative identity through the polar chart.  The derivative
  of the polar chart in the \(r\)-direction is \(\sigma(y)\), as computed in
  the formal geometry lemmas above.  On almost every vertical coordinate line,
  apply the one-dimensional Sobolev representative theorem and choose the
  primitive representative from a fixed interior anchor; this choice is
  jointly measurable in \((r,y)\).  The fundamental theorem of calculus for
  the line representative gives the displayed estimate, and the polar
  change-of-variables theorem gives equality with the original function
  almost everywhere in the ball.
-/
theorem scalarWeakSobolev_stereographic_polar_patch_full_vertical_acl_representative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wpatch : H → ℝ,
      Measurable wpatch ∧
      wpatch =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖wpatch (stereographicPolarPatchMap v (r, y)) -
                wpatch (stereographicPolarPatchMap v (s, y))‖ ≤
              ∫⁻ t in {t : ℝ | r < t ∧ t < s},
            ENNReal.ofReal
                  ‖dw (stereographicPolarPatchMap v (t, y))
                    (((stereographic' n v).symm y :
                      Metric.sphere (0 : H) 1) : H)‖
                ∂MeasureTheory.volume := by
  classical
  let wpatch : H → ℝ := _hw.aestronglyMeasurable.mk w
  have hwpatch_meas : Measurable wpatch := by
    dsimp [wpatch]
    exact _hw.aestronglyMeasurable.measurable_mk
  have hwpatch_eq :
      wpatch =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w := by
    dsimp [wpatch]
    exact _hw.aestronglyMeasurable.ae_eq_mk.symm
  rcases
    scalarWeakSobolev_stereographic_polar_patch_full_vertical_acl_bound_of_measurable_representative
      (n := n) v _hweak _hw _hdw hwpatch_meas hwpatch_eq with
    ⟨wacl, hwacl_meas, hwacl_eq_patch, hwacl_bound⟩
  refine ⟨wacl, hwacl_meas, ?_, hwacl_bound⟩
  exact hwacl_eq_patch.trans hwpatch_eq

/--
%%handwave
name:
  Radial ACL in flat stereographic product coordinates
statement:
  After pulling a scalar \(W^{1,2}\) function on the unit ball back by the
  map \((r,y)\mapsto r\sigma(y)\), there is a representative, equal to the
  original Sobolev function almost everywhere after pushing back to the ball,
  for which almost every vertical coordinate line satisfies the finite
  radial ACL estimate.
proof:
  Pull the weak-derivative identity through the locally bi-Lipschitz map
  \((r,y)\mapsto r\sigma(y)\).  The derivative in the \(r\)-direction is
  \(\sigma(y)\).  Apply the one-dimensional ACL representative theorem on
  almost every vertical line, then use the absolute continuity of the radial
  density \(r^{m-1}\,dr\) with respect to \(dr\).
-/
theorem scalarWeakSobolev_stereographic_polar_patch_volume_coordinate_acl_representative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wpatch : H → ℝ,
      Measurable wpatch ∧
      wpatch =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
            ∀ᵐ r : Set.Ioi (0 : ℝ)
                ∂((MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)).restrict
                    {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
              ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wpatch
                      (stereographicPolarPatchMap v
                        (((r : Set.Ioi (0 : ℝ)) : ℝ), y)) -
                    wpatch (stereographicPolarPatchMap v (s, y))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal
                      ‖dw (stereographicPolarPatchMap v (t, y))
                        (((stereographic' n v).symm y :
                          Metric.sphere (0 : H) 1) : H)‖
                    ∂MeasureTheory.volume := by
  classical
  rcases
    scalarWeakSobolev_stereographic_polar_patch_full_vertical_acl_representative
      (n := n) v _hweak _hw _hdw with
    ⟨wpatch, hwpatch_meas, hwpatch_eq, hline⟩
  refine ⟨wpatch, hwpatch_meas, hwpatch_eq, ?_⟩
  intro s hs_pos hs_lt_one
  filter_upwards [hline] with y hy
  filter_upwards with r
  intro hrs
  exact hy ((r : Set.Ioi (0 : ℝ)) : ℝ) s r.2 hrs hs_lt_one

/--
%%handwave
name:
  Radial ACL in stereographic radial coordinates
statement:
  On one stereographic coordinate patch, a scalar \(W^{1,2}\) function on the
  unit ball has a representative, equal almost everywhere to the original
  function, whose pullback by \((r,y)\mapsto r\sigma(y)\) satisfies the
  one-dimensional ACL estimate in the radial coordinate for almost every
  coordinate line.
proof:
  In the coordinates \((r,y)\), the map into the ball is smooth and locally
  bi-Lipschitz on compact subcylinders with radii bounded away from the origin.
  Pull back the weak derivative identity through this map using
  [weak derivatives pull back under locally bi-Lipschitz changes of variables](lean:JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues.comp_locallyBiLipschitz).
  The derivative in the radial coordinate is the inverse stereographic point
  \(\sigma(y)\).  The first-coordinate ACL theorem applied to the pulled-back
  function gives the displayed estimate; the stereographic chart transfers the
  transverse almost-everywhere statement back to the patch of the sphere.
-/
private theorem scalarWeakSobolev_stereographic_polar_patch_coordinate_acl_representative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wpatch : H → ℝ,
      Measurable wpatch ∧
      wpatch =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          ∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere.restrict
                (stereographic' n v).source),
            ∀ᵐ r : Set.Ioi (0 : ℝ)
                ∂((MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)).restrict
                    {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
              ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wpatch
                      (stereographicPolarPatchMap v
                        (((r : Set.Ioi (0 : ℝ)) : ℝ),
                          (stereographic' n v) θ)) -
                    wpatch
                      (stereographicPolarPatchMap v
                        (s, (stereographic' n v) θ))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal
                      ‖dw
                        (stereographicPolarPatchMap v
                          (t, (stereographic' n v) θ))
                        (((stereographic' n v).symm
                      ((stereographic' n v) θ) : Metric.sphere (0 : H) 1) :
                          H)‖
                    ∂MeasureTheory.volume := by
  classical
  rcases
    scalarWeakSobolev_stereographic_polar_patch_volume_coordinate_acl_representative
      (n := n) v _hweak _hw _hdw with
    ⟨wpatch, hwpatch_meas, hwpatch_eq, hcoord⟩
  refine ⟨wpatch, hwpatch_meas, hwpatch_eq, ?_⟩
  intro s hs_pos hs_lt_one
  exact
    ae_stereographic_toSphere_restrict_of_ae_volume
      (n := n) v (hcoord s hs_pos hs_lt_one)

/--
%%handwave
name:
  Radial ACL on one stereographic patch
statement:
  Fix a stereographic coordinate patch on the unit sphere.  A scalar
  \(W^{1,2}\) function on the unit ball has a representative, equal to the
  original function almost everywhere in the ball, such that on this patch
  almost every radial line satisfies the finite-endpoint radial ACL estimate.
proof:
  Write the patch in coordinates as \((y,r)\mapsto r\sigma(y)\), where
  \(\sigma\) is the inverse stereographic parametrization.  The explicit
  formula for inverse stereographic projection is smooth on all coordinate
  space, and on compact coordinate subcylinders the polar map is bi-Lipschitz
  onto its image.  Pull back the weak derivative identity through this
  locally bi-Lipschitz map using
  [weak derivatives pull back under locally bi-Lipschitz changes of variables](lean:JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues.comp_locallyBiLipschitz).
  In the pulled-back coordinates the radial derivative is the first coordinate
  derivative, so the one-dimensional ACL theorem on almost every vertical
  fiber gives the displayed radial estimate.
-/
private theorem scalarWeakSobolev_stereographic_polar_patch_acl_representative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wpatch : H → ℝ,
      Measurable wpatch ∧
      wpatch =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          ∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere.restrict
                (stereographic' n v).source),
            ∀ᵐ r : Set.Ioi (0 : ℝ)
                ∂((MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)).restrict
                    {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
              ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wpatch ((r : ℝ) • (θ : H)) -
                    wpatch (s • (θ : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                    ∂MeasureTheory.volume := by
  classical
  rcases
    scalarWeakSobolev_stereographic_polar_patch_coordinate_acl_representative
      (n := n) v _hweak _hw _hdw with
    ⟨wpatch, hwpatch_meas, hwpatch_eq, hpatch_coord⟩
  refine ⟨wpatch, hwpatch_meas, hwpatch_eq, ?_⟩
  intro s hs_pos hs_lt_one
  have hsource_meas : MeasurableSet (stereographic' n v).source :=
    (stereographic' n v).open_source.measurableSet
  filter_upwards [hpatch_coord s hs_pos hs_lt_one,
    ae_restrict_mem hsource_meas] with θ hθ_acl hθ_source
  filter_upwards [hθ_acl] with r hr_acl
  intro hrs
  have hbound := hr_acl hrs
  rw [stereographicPolarPatchMap_apply_chart (n := n) v hθ_source
      (((r : Set.Ioi (0 : ℝ)) : ℝ)),
    stereographicPolarPatchMap_apply_chart (n := n) v hθ_source s] at hbound
  have hdir :
      (((stereographic' n v).symm
        ((stereographic' n v) θ) : Metric.sphere (0 : H) 1) : H) =
        (θ : H) :=
    stereographic'_symm_apply_apply_of_mem_source (n := n) v hθ_source
  have hpoint : ∀ t : ℝ,
      stereographicPolarPatchMap v (t, (stereographic' n v) θ) =
        t • (θ : H) := by
    intro t
    exact stereographicPolarPatchMap_apply_chart (n := n) v hθ_source t
  simpa [hpoint, hdir] using hbound

/--
%%handwave
name:
  One stereographic chart gives the radial ACL representative in dimension at
  least two
statement:
  In ambient dimension at least two, a scalar \(W^{1,2}\) function on the unit
  ball has a representative, equal almost everywhere to the original function,
  whose radial ACL estimate holds for almost every direction and almost every
  radius.
proof:
  Apply the one-chart radial ACL theorem.  The only missing direction is the
  stereographic pole, which has zero spherical measure, so the chartwise
  almost-everywhere statement becomes a full spherical almost-everywhere
  statement.
-/
theorem
    scalarWeakSobolev_unit_ball_radial_acl_representative_one_stereographic_patch_of_one_lt_finrank
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (hfin : 1 < Module.finrank ℝ H)
    (v : Metric.sphere (0 : H) 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wacl : H → ℝ,
      Measurable wacl ∧
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          ∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere),
            ∀ᵐ r : Set.Ioi (0 : ℝ)
                ∂((MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)).restrict
                    {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
              ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((r : ℝ) • (θ : H)) -
                    wacl (s • (θ : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                    ∂MeasureTheory.volume := by
  rcases scalarWeakSobolev_stereographic_polar_patch_acl_representative
      (n := n) v hweak hw hdw with
    ⟨wpatch, hwpatch_meas, hwpatch_eq, hpatch⟩
  refine ⟨wpatch, hwpatch_meas, hwpatch_eq, ?_⟩
  intro s hs_pos hs_lt_one
  exact
    ae_toSphere_of_ae_restrict_stereographic_source_of_one_lt_finrank
      (n := n) hfin v (hpatch s hs_pos hs_lt_one)

/--
%%handwave
name:
  The polar segment evaluation map is quasi-measure-preserving
statement:
  For \(0<s<1\), the map
  \[
    (\theta,r,t)\mapsto t\theta
  \]
  from the polar product restricted to \(r<t<s\) sends null sets in the unit
  ball to null preimages.  Here \(r\) is measured with the radial polar
  measure and \(t\) with one-dimensional Lebesgue measure.
proof:
  It is enough to test measurable null sets in the ball, and then pass to
  arbitrary null sets by measurable hulls.  Polar coordinates show that for
  almost every direction, the set of bad radii is null for the radial polar
  measure.  Since Lebesgue measure on the positive ray is absolutely
  continuous with respect to the positive polar density \(r^{m-1}\,dr\), this
  remains true for the Lebesgue segment parameter \(t\).  Fubini over
  \((\theta,r,t)\), restricted to \(r<t<s\), gives the desired null preimage.
-/
theorem polarSegmentEval_quasiMeasurePreserving_restrict
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    (s : ℝ) (_hs_pos : 0 < s) (hs_lt_one : s < 1) :
    Measure.QuasiMeasurePreserving
      (fun q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ ↦
        q.2 • (q.1.1 : H))
      ((((MeasureTheory.volume : Measure H).toSphere.prod
          ((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})).prod
          MeasureTheory.volume).restrict
            {q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ |
              ((q.1.2 : Set.Ioi (0 : ℝ)) : ℝ) < q.2 ∧ q.2 < s})
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  let μBase : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod (μR.restrict R)
  let A : Set ((Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ) :=
    {q | ((q.1.2 : Set.Ioi (0 : ℝ)) : ℝ) < q.2 ∧ q.2 < s}
  let μSrc : Measure ((Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ) :=
    (μBase.prod MeasureTheory.volume).restrict A
  let μTgt : Measure H :=
    MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)
  let f : ((Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ) → H :=
    fun q ↦ q.2 • (q.1.1 : H)
  have hf_meas : Measurable f := by
    dsimp [f]
    measurability
  refine ⟨by simpa [f] using hf_meas, ?_⟩
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    measurability
  have hmeasurable_null :
      ∀ ⦃M : Set H⦄, MeasurableSet M → μTgt M = 0 →
        Measure.map f μSrc M = 0 := by
    intro M hM hM_zero
    have hP : ∀ᵐ z ∂μTgt, z ∉ M := by
      rw [ae_iff]
      simpa only [Set.mem_setOf_eq, not_not] using hM_zero
    have hpolar :
        ∀ᵐ p ∂μBase, ((p.2 : ℝ) • (p.1 : H)) ∉ M := by
      simpa [μBase, μS, μR, R, μTgt] using
        ae_polar_product_unitBall_of_ae_volume_unitBall
          (H := H) (P := fun z : H ↦ z ∉ M) hP
    have hpolar_pred_meas :
        MeasurableSet
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            ((p.2 : ℝ) • (p.1 : H)) ∉ M} := by
      exact hM.compl.preimage (by measurability)
    have htheta :
        ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
          ∀ᵐ r : Set.Ioi (0 : ℝ) ∂μR.restrict R,
            ((r : ℝ) • (θ : H)) ∉ M := by
      simpa [μBase] using
        (Measure.ae_prod_iff_ae_ae hpolar_pred_meas).1 hpolar
    have htheta_segment :
        ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
          ∀ r : Set.Ioi (0 : ℝ),
            ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
              ((r : ℝ) < t ∧ t < s) → t • (θ : H) ∉ M := by
      filter_upwards [htheta] with θ hθ
      intro r
      have ht_unweighted :
          ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
            ∀ (ht_pos : 0 < t), t < 1 →
              (((⟨t, ht_pos⟩ : Set.Ioi (0 : ℝ)) : ℝ) •
                (θ : H)) ∉ M :=
        ae_volume_Ioo_zero_one_of_ae_volumeIoiPow_restrict
          (n := Module.finrank ℝ H - 1)
          (P := fun ρ : Set.Ioi (0 : ℝ) ↦ ((ρ : ℝ) • (θ : H)) ∉ M)
          hθ
      filter_upwards [ht_unweighted] with t ht
      intro hrt
      exact ht (lt_trans r.2 hrt.1) (lt_trans hrt.2 hs_lt_one)
    have hbase :
        ∀ᵐ p ∂μBase,
          ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
            (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s) →
              t • (p.1 : H) ∉ M := by
      have hmap :
          ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂Measure.map Prod.fst μBase,
            ∀ r : Set.Ioi (0 : ℝ),
              ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
                ((r : ℝ) < t ∧ t < s) → t • (θ : H) ∉ M := by
        have hsmul :
            ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂((μR.restrict R Set.univ) • μS),
              ∀ r : Set.Ioi (0 : ℝ),
                ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
                  ((r : ℝ) < t ∧ t < s) → t • (θ : H) ∉ M :=
          Measure.ae_smul_measure htheta_segment (μR.restrict R Set.univ)
        simpa [μBase] using hsmul
      filter_upwards
        [ae_of_ae_map (μ := μBase) (f := Prod.fst)
          measurable_fst.aemeasurable hmap] with p hp
      exact hp p.2
    have hprod_pred_meas :
        MeasurableSet
          {q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ |
            (((q.1.2 : Set.Ioi (0 : ℝ)) : ℝ) < q.2 ∧ q.2 < s) →
              q.2 • (q.1.1 : H) ∉ M} := by
      let B : Set ((Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ) :=
        {q | ((q.1.2 : Set.Ioi (0 : ℝ)) : ℝ) < q.2 ∧ q.2 < s}
      let C : Set ((Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ) :=
        {q | q.2 • (q.1.1 : H) ∈ M}
      have hB : MeasurableSet B := by
        dsimp [B]
        measurability
      have hC : MeasurableSet C := by
        dsimp [C]
        exact hM.preimage (by measurability)
      convert hB.compl.union hC.compl using 1
      ext q
      by_cases hqB : q ∈ B
      · change
          ((q.1.2 : Set.Ioi (0 : ℝ)) : ℝ) < q.2 ∧ q.2 < s at hqB
        rcases hqB with ⟨hqB_left, hqB_right⟩
        simp [B, C, hqB_left, hqB_right]
      · change
          ¬ (((q.1.2 : Set.Ioi (0 : ℝ)) : ℝ) < q.2 ∧ q.2 < s) at hqB
        simp [B, C, hqB]
        intro hq_left hq_right
        exact False.elim (hqB ⟨hq_left, hq_right⟩)
    have hprod :
        ∀ᵐ q ∂μBase.prod MeasureTheory.volume,
          (((q.1.2 : Set.Ioi (0 : ℝ)) : ℝ) < q.2 ∧ q.2 < s) →
            q.2 • (q.1.1 : H) ∉ M :=
      (Measure.ae_prod_iff_ae_ae hprod_pred_meas).2 hbase
    have hsrc_ae : ∀ᵐ q ∂μSrc, f q ∉ M := by
      filter_upwards [ae_restrict_of_ae hprod, ae_restrict_mem hA_meas] with q hq hqA
      exact hq hqA
    have hpre_zero : μSrc (f ⁻¹' M) = 0 := by
      have hnot_pre : ∀ᵐ q ∂μSrc, q ∉ f ⁻¹' M := by
        simpa [Set.preimage] using hsrc_ae
      simpa using (ae_iff.mp hnot_pre)
    rw [Measure.map_apply hf_meas hM]
    exact hpre_zero
  intro N hN
  let M : Set H := toMeasurable μTgt N
  have hM_meas : MeasurableSet M :=
    measurableSet_toMeasurable μTgt N
  have hM_zero : μTgt M = 0 := by
    simpa [M] using (measure_toMeasurable (μ := μTgt) N).trans hN
  have hmapM_zero : Measure.map f μSrc M = 0 :=
    hmeasurable_null hM_meas hM_zero
  exact nonpos_iff_eq_zero.1
    ((measure_mono (subset_toMeasurable μTgt N)).trans_eq hmapM_zero)

/--
%%handwave
name:
  The radial derivative segment integral is measurable
statement:
  If the weak derivative is square-integrable on the unit ball, then for each
  fixed \(0<s<1\) the function of the polar pair \((\theta,r)\) given by
  \[
    \int_{\{t:r<t<s\}} |D w(t\theta)\theta|\,dt
  \]
  is measurable up to null sets for spherical measure times the restricted
  radial measure.
proof:
  Write the set integral as the integral over \(t\) of the indicator of the
  measurable region \(r<t<s\) times the pullback of \(|D w|\) by
  \((\theta,r,t)\mapsto t\theta\).  On this region the map lands in the unit
  ball, and polar coordinates make it quasi-measure-preserving into Lebesgue
  measure on the ball.  The square-integrability of \(D w\) gives
  almost-everywhere measurability of the pulled-back integrand; Tonelli then
  gives measurability of the parameter integral.
-/
theorem scalarWeakSobolev_unit_ball_radial_acl_segmentIntegral_aemeasurable_of_memLp
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {dw : H → H →L[ℝ] ℝ}
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (s : ℝ) (_hs_pos : 0 < s) (_hs_lt_one : s < 1) :
    AEMeasurable
      (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
        ∫⁻ t in
          {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
          ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
          ∂MeasureTheory.volume)
      ((MeasureTheory.volume : Measure H).toSphere.prod
        ((MeasureTheory.Measure.volumeIoiPow
          (Module.finrank ℝ H - 1)).restrict
            {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) := by
  classical
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.volume : Measure H).toSphere.prod
      ((MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ H - 1)).restrict
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})
  let A : Set ((Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ) :=
    {q | ((q.1.2 : Set.Ioi (0 : ℝ)) : ℝ) < q.2 ∧ q.2 < s}
  let F : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ → ℝ≥0∞ :=
    fun q ↦
      A.indicator
        (fun q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ ↦
          ENNReal.ofReal ‖dw (q.2 • (q.1.1 : H)) (q.1.1 : H)‖) q
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    measurability
  have hqmp :
      Measure.QuasiMeasurePreserving
        (fun q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ ↦
          q.2 • (q.1.1 : H))
        ((μ.prod MeasureTheory.volume).restrict A)
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
    simpa [μ, A] using
      polarSegmentEval_quasiMeasurePreserving_restrict
        (H := H) s _hs_pos _hs_lt_one
  have hDw :
      AEStronglyMeasurable
        (fun q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ ↦
          dw (q.2 • (q.1.1 : H)))
        ((μ.prod MeasureTheory.volume).restrict A) := by
    simpa [Function.comp_def] using
      _hdw.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  have hθ :
      AEStronglyMeasurable
        (fun q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ ↦
          (q.1.1 : H))
        ((μ.prod MeasureTheory.volume).restrict A) := by
    exact (by measurability : Measurable
      (fun q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ ↦
        (q.1.1 : H))).aestronglyMeasurable
  have hval :
      AEStronglyMeasurable
        (fun q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ ↦
          dw (q.2 • (q.1.1 : H)) (q.1.1 : H))
        ((μ.prod MeasureTheory.volume).restrict A) := by
    simpa using
      (ContinuousLinearMap.apply ℝ ℝ).flip.aestronglyMeasurable_comp₂
        hDw hθ
  have hF : AEMeasurable F (μ.prod MeasureTheory.volume) := by
    have hraw :
        AEMeasurable
          (A.indicator
            (fun q : (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) × ℝ ↦
              ENNReal.ofReal ‖dw (q.2 • (q.1.1 : H)) (q.1.1 : H)‖))
          (μ.prod MeasureTheory.volume) :=
      (aemeasurable_indicator_iff (μ := μ.prod MeasureTheory.volume) hA_meas).2
        hval.norm.aemeasurable.ennreal_ofReal
    simpa [F] using hraw
  have hInt :
      AEMeasurable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          ∫⁻ t, F (p, t) ∂MeasureTheory.volume) μ :=
    hF.lintegral_prod_right
  convert hInt using 1
  ext p
  have hpt_meas :
      MeasurableSet
        {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s} := by
    measurability
  rw [← lintegral_indicator hpt_meas]
  rfl

/--
%%handwave
name:
  The radial ACL exceptional set is null-measurable
statement:
  If the chosen representative is measurable and the weak derivative is
  square-integrable on the unit ball, then, for each fixed endpoint radius
  \(0<s<1\), the set of polar pairs where the finite radial ACL estimate
  fails is null-measurable for the product of spherical measure and the
  radial polar measure.
proof:
  The left side of the inequality is measurable because the representative is
  measurable and the polar evaluation maps are continuous.  The right side is
  an iterated nonnegative integral of an almost-everywhere measurable
  integrand, using square-integrability of the derivative and the
  polar-coordinate map.  Hence the failure set is a null-measurable comparison
  set of two almost-everywhere measurable extended-real functions.
-/
theorem scalarWeakSobolev_unit_ball_radial_acl_badSet_nullMeasurable_of_measurable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {wacl : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hwacl_meas : Measurable wacl)
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (s : ℝ) (hs_pos : 0 < s) (hs_lt_one : s < 1) :
    NullMeasurableSet
      {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
        ¬ (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
          ENNReal.ofReal
            ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
              wacl (s • (p.1 : H))‖ ≤
            ∫⁻ t in
              {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume)}
      ((MeasureTheory.volume : Measure H).toSphere.prod
        ((MeasureTheory.Measure.volumeIoiPow
          (Module.finrank ℝ H - 1)).restrict
            {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) := by
  classical
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.volume : Measure H).toSphere.prod
      ((MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ H - 1)).restrict
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})
  let lhs : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun p ↦
      ENNReal.ofReal
        ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
          wacl (s • (p.1 : H))‖
  let rhs : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun p ↦
      ∫⁻ t in
        {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
        ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
        ∂MeasureTheory.volume
  have hlhs : AEMeasurable lhs μ := by
    have hpoint_r :
        Measurable
          (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
            ((p.2 : ℝ) • (p.1 : H))) := by
      measurability
    have hpoint_s :
        Measurable
          (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
            s • (p.1 : H)) := by
      measurability
    have hreal :
        AEMeasurable
          (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
            ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
              wacl (s • (p.1 : H))‖) μ := by
      exact
        ((hwacl_meas.comp hpoint_r).aemeasurable.sub
          (hwacl_meas.comp hpoint_s).aemeasurable).norm
    simpa [lhs] using hreal.ennreal_ofReal
  have hrhs : AEMeasurable rhs μ := by
    simpa [μ, rhs] using
      scalarWeakSobolev_unit_ball_radial_acl_segmentIntegral_aemeasurable_of_memLp
        (H := H) (dw := dw) hdw s hs_pos hs_lt_one
  have hlt : NullMeasurableSet {p | rhs p < lhs p} μ :=
    nullMeasurableSet_lt hrhs hlhs
  have hr_lt_meas :
      NullMeasurableSet
        {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
          ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s} μ :=
    (by
      have hmeas :
          MeasurableSet
            {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
              ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s} := by
        measurability
      exact hmeas.nullMeasurableSet)
  have hbad :
      NullMeasurableSet
        ({p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
          ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s} ∩
          {p | rhs p < lhs p}) μ :=
    hr_lt_meas.inter hlt
  convert hbad using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, lhs, rhs]
  constructor
  · intro h
    have hr : ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s := by
      by_contra hnr
      exact h (fun hp ↦ False.elim (hnr hp))
    have hnot_le :
        ¬ ENNReal.ofReal
            ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
              wacl (s • (p.1 : H))‖ ≤
          ∫⁻ t in
            {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
            ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
            ∂MeasureTheory.volume := by
      intro hle
      exact h (fun _ ↦ hle)
    exact ⟨hr, lt_of_not_ge hnot_le⟩
  · intro h himp
    exact not_le_of_gt h.2 (himp h.1)

/--
%%handwave
name:
  Raywise radial ACL representative from two stereographic hemispheres
statement:
  A scalar \(W^{1,2}\) function on the unit ball has a representative,
  equal almost everywhere to the original function, whose finite radial ACL
  estimate holds for almost every direction and almost every radius.  The
  exceptional polar set is null-measurable.
proof:
  Choose a unit vector \(v\).  On the open half of the sphere where
  \(\langle\theta,v\rangle>0\), use the stereographic chart with pole
  \(-v\); on the complementary half, use the chart with pole \(v\).  These
  two choices cover all directions.  Define the representative by the same
  measurable half-space partition in the ball.  Along each positive radial
  line the sign of \(\langle r\theta,v\rangle\) is constant, so the chartwise
  radial ACL estimates become the desired estimate for this single
  representative.  Null-measurability of the failure set follows from the
  measurability of the representative and the square-integrability of the
  weak derivative.
-/
theorem
    scalarWeakSobolev_unit_ball_radial_acl_representative_raywise_polar_charts_two_hemispheres
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wacl : H → ℝ,
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          NullMeasurableSet
            {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
              ¬ (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
                    wacl (s • (p.1 : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                    ∂MeasureTheory.volume)}
            ((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) ∧
          ∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere),
            ∀ᵐ r : Set.Ioi (0 : ℝ)
                ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
              ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((r : ℝ) • (θ : H)) -
                    wacl (s • (θ : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                    ∂MeasureTheory.volume := by
  classical
  let n : ℕ := Module.finrank ℝ H - 1
  have hfin_pos : 0 < Module.finrank ℝ H :=
    Module.finrank_pos (R := ℝ) (M := H)
  haveI : Fact (Module.finrank ℝ H = n + 1) := by
    refine ⟨?_⟩
    dsimp [n]
    omega
  rcases (NormedSpace.sphere_nonempty (E := H) (x := (0 : H)) (r := (1 : ℝ))).2
      (by norm_num : (0 : ℝ) ≤ 1) with
    ⟨v₀, hv₀⟩
  let v : Metric.sphere (0 : H) 1 := ⟨v₀, hv₀⟩
  rcases scalarWeakSobolev_stereographic_polar_patch_acl_representative
      (n := n) v hweak hw hdw with
    ⟨wminusHemisphere, hwminus_meas, hwminus_eq, hwminus_acl⟩
  rcases scalarWeakSobolev_stereographic_polar_patch_acl_representative
      (n := n) (-v) hweak hw hdw with
    ⟨wplusHemisphere, hwplus_meas, hwplus_eq, hwplus_acl⟩
  let A : Set H := {z : H | 0 < inner ℝ z (v : H)}
  let wacl : H → ℝ := fun z ↦ if z ∈ A then wplusHemisphere z else wminusHemisphere z
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    measurability
  have hwacl_meas : Measurable wacl := by
    dsimp [wacl]
    exact Measurable.piecewise hA_meas hwplus_meas hwminus_meas
  have hwacl_eq :
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w := by
    filter_upwards [hwplus_eq, hwminus_eq] with z hzplus hzminus
    by_cases hzA : z ∈ A
    · simp [wacl, hzA, hzplus]
    · simp [wacl, hzA, hzminus]
  refine ⟨wacl, hwacl_eq, ?_⟩
  intro s hs_pos hs_lt_one
  have hbad :
      NullMeasurableSet
        {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
          ¬ (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
            ENNReal.ofReal
              ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
                wacl (s • (p.1 : H))‖ ≤
              ∫⁻ t in
                {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume)}
        ((MeasureTheory.volume : Measure H).toSphere.prod
          ((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) :=
    scalarWeakSobolev_unit_ball_radial_acl_badSet_nullMeasurable_of_measurable
      (H := H) (wacl := wacl) (dw := dw) hwacl_meas hdw s hs_pos hs_lt_one
  refine ⟨hbad, ?_⟩
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  have hsource_minus_meas : MeasurableSet (stereographic' n v).source :=
    (stereographic' n v).open_source.measurableSet
  have hsource_plus_meas : MeasurableSet (stereographic' n (-v)).source :=
    (stereographic' n (-v)).open_source.measurableSet
  have hminus_imp :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        θ ∈ (stereographic' n v).source →
          ∀ᵐ r : Set.Ioi (0 : ℝ)
              ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
            ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
              ENNReal.ofReal
                ‖wminusHemisphere ((r : ℝ) • (θ : H)) -
                  wminusHemisphere (s • (θ : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                  ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                  ∂MeasureTheory.volume :=
    (ae_restrict_iff' hsource_minus_meas).1
      (by simpa [μS] using hwminus_acl s hs_pos hs_lt_one)
  have hplus_imp :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        θ ∈ (stereographic' n (-v)).source →
          ∀ᵐ r : Set.Ioi (0 : ℝ)
              ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
            ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
              ENNReal.ofReal
                ‖wplusHemisphere ((r : ℝ) • (θ : H)) -
                  wplusHemisphere (s • (θ : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                  ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                  ∂MeasureTheory.volume :=
    (ae_restrict_iff' hsource_plus_meas).1
      (by simpa [μS] using hwplus_acl s hs_pos hs_lt_one)
  have hplus_half :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        0 < inner ℝ (θ : H) (v : H) →
          ∀ᵐ r : Set.Ioi (0 : ℝ)
              ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
            ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
              ENNReal.ofReal
                ‖wacl ((r : ℝ) • (θ : H)) -
                  wacl (s • (θ : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                  ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                  ∂MeasureTheory.volume := by
    filter_upwards [hplus_imp] with θ hθ_plus hθ_pos
    have hθ_source : θ ∈ (stereographic' n (-v)).source := by
      rw [stereographic'_source]
      intro hθ
      have hθeq : θ = (-v : Metric.sphere (0 : H) 1) := by
        simpa using hθ
      subst θ
      have hneg :
          inner ℝ ((-v : Metric.sphere (0 : H) 1) : H) (v : H) = -1 := by
        have hvnorm : ‖(v : H)‖ = 1 := norm_eq_of_mem_sphere v
        simp [hvnorm]
      have hbad_pos : (0 : ℝ) < -1 := by
        simpa [hneg] using hθ_pos
      norm_num at hbad_pos
    filter_upwards [hθ_plus hθ_source] with r hr
    intro hrs
    have hrA : ((r : ℝ) • (θ : H)) ∈ A := by
      dsimp [A]
      simpa [real_inner_smul_left] using mul_pos r.2 hθ_pos
    have hsA : (s • (θ : H)) ∈ A := by
      dsimp [A]
      simpa [real_inner_smul_left] using mul_pos hs_pos hθ_pos
    simpa [wacl, hrA, hsA] using hr hrs
  have hminus_half :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        ¬ 0 < inner ℝ (θ : H) (v : H) →
          ∀ᵐ r : Set.Ioi (0 : ℝ)
              ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
            ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
              ENNReal.ofReal
                ‖wacl ((r : ℝ) • (θ : H)) -
                  wacl (s • (θ : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                  ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                  ∂MeasureTheory.volume := by
    filter_upwards [hminus_imp] with θ hθ_minus hθ_not_pos
    have hθ_source : θ ∈ (stereographic' n v).source := by
      rw [stereographic'_source]
      intro hθ
      have hθeq : θ = v := by
        simpa using hθ
      subst θ
      have hvnorm : ‖(v : H)‖ = 1 := norm_eq_of_mem_sphere v
      apply hθ_not_pos
      simp [hvnorm]
    have hθ_nonpos : inner ℝ (θ : H) (v : H) ≤ 0 :=
      le_of_not_gt hθ_not_pos
    filter_upwards [hθ_minus hθ_source] with r hr
    intro hrs
    have hrA : ((r : ℝ) • (θ : H)) ∉ A := by
      dsimp [A]
      have hinner_nonpos :
          inner ℝ ((r : ℝ) • (θ : H)) (v : H) ≤ 0 := by
        simpa [real_inner_smul_left] using
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt r.2) hθ_nonpos
      exact not_lt_of_ge hinner_nonpos
    have hsA : (s • (θ : H)) ∉ A := by
      dsimp [A]
      have hinner_nonpos :
          inner ℝ (s • (θ : H)) (v : H) ≤ 0 := by
        simpa [real_inner_smul_left] using
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs_pos) hθ_nonpos
      exact not_lt_of_ge hinner_nonpos
    simpa [wacl, hrA, hsA] using hr hrs
  simpa [μS] using
    (hplus_half.and hminus_half).mono fun θ hθ ↦ by
      by_cases hθ_pos : 0 < inner ℝ (θ : H) (v : H)
      · exact hθ.1 hθ_pos
      · exact hθ.2 hθ_pos

/--
%%handwave
name:
  Raywise radial ACL in ambient dimension at least two
statement:
  In ambient dimension at least two, a scalar \(W^{1,2}\) function on the unit
  ball admits a measurable representative, equal to the original function
  almost everywhere, such that the finite radial ACL estimate holds for almost
  every direction and almost every radius, and the corresponding exceptional
  polar set is null-measurable.
proof:
  Choose one stereographic chart.  Its missing pole has zero spherical measure
  in ambient dimension at least two, so the one-chart radial ACL statement
  gives the almost-everywhere conclusion on the whole sphere.  The
  null-measurability of the failure set follows from the measurable
  representative and square-integrability of the weak derivative.
-/
private theorem
    scalarWeakSobolev_unit_ball_radial_acl_representative_raywise_polar_charts_of_one_lt_finrank
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    (hfin : 1 < Module.finrank ℝ H)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wacl : H → ℝ,
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          NullMeasurableSet
            {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
              ¬ (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
                    wacl (s • (p.1 : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                    ∂MeasureTheory.volume)}
            ((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) ∧
          ∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere),
            ∀ᵐ r : Set.Ioi (0 : ℝ)
                ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
              ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((r : ℝ) • (θ : H)) -
                    wacl (s • (θ : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                    ∂MeasureTheory.volume := by
  classical
  let n : ℕ := Module.finrank ℝ H - 1
  have hfin_pos : 0 < Module.finrank ℝ H :=
    Module.finrank_pos (R := ℝ) (M := H)
  haveI : Fact (Module.finrank ℝ H = n + 1) := by
    refine ⟨?_⟩
    dsimp [n]
    omega
  rcases (NormedSpace.sphere_nonempty (E := H) (x := (0 : H)) (r := (1 : ℝ))).2
      (by norm_num : (0 : ℝ) ≤ 1) with
    ⟨v₀, hv₀⟩
  let v : Metric.sphere (0 : H) 1 := ⟨v₀, hv₀⟩
  rcases
    scalarWeakSobolev_unit_ball_radial_acl_representative_one_stereographic_patch_of_one_lt_finrank
      (n := n) hfin v hweak hw hdw with
    ⟨wacl, hwacl_meas, hwacl_eq, hwacl_aeae⟩
  refine ⟨wacl, hwacl_eq, ?_⟩
  intro s hs_pos hs_lt_one
  exact
    ⟨scalarWeakSobolev_unit_ball_radial_acl_badSet_nullMeasurable_of_measurable
      (H := H) (wacl := wacl) (dw := dw) hwacl_meas hdw s hs_pos hs_lt_one,
      hwacl_aeae s hs_pos hs_lt_one⟩

/--
%%handwave
name:
  Raywise radial ACL in ambient dimension one
statement:
  In ambient dimension one, the unit sphere consists of the two radial
  directions.  A scalar \(W^{1,2}\) function on the unit interval therefore
  admits a representative whose restrictions to the two rays satisfy the
  finite radial ACL estimate, with a null-measurable exceptional polar set.
proof:
  This is a specialization of the two-chart half-space construction.  The
  two stereographic charts cover the sphere, and the representative is chosen
  by the same measurable half-space partition on the ball.
-/
theorem
    scalarWeakSobolev_unit_ball_radial_acl_representative_raywise_polar_charts_of_finrank_le_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    (_hfin_le : Module.finrank ℝ H ≤ 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wacl : H → ℝ,
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          NullMeasurableSet
            {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
              ¬ (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
                    wacl (s • (p.1 : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                    ∂MeasureTheory.volume)}
            ((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) ∧
          ∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere),
            ∀ᵐ r : Set.Ioi (0 : ℝ)
                ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
              ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((r : ℝ) • (θ : H)) -
                    wacl (s • (θ : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                    ∂MeasureTheory.volume := by
  exact
    scalarWeakSobolev_unit_ball_radial_acl_representative_raywise_polar_charts_two_hemispheres
      _hweak _hw _hdw

/--
%%handwave
name:
  Raywise radial ACL representative from local polar coordinates
statement:
  If \(w\) is a scalar \(W^{1,2}\) function on the Euclidean unit ball with
  weak derivative \(D w\), then it has a representative \(\widetilde w\) that
  agrees with \(w\) almost everywhere in the ball and, for every \(0<s<1\),
  for almost every direction \(\theta\), the finite radial segment from
  \(r\theta\) to \(s\theta\) satisfies
  \[
    |\widetilde w(r\theta)-\widetilde w(s\theta)|
      \le \int_r^s |D w(t\theta)\theta|\,dt
  \]
  for almost every radius \(0<r<s\).  The corresponding exceptional subset
  of polar space is null-measurable.
proof:
  Choose a unit vector \(v\), use the chart with pole \(-v\) on the
  hemisphere \(\langle\theta,v\rangle>0\), and use the chart with pole \(v\)
  on the complementary hemisphere.  On each chart the map
  \((y,r)\mapsto r\sigma(y)\) turns radial lines into vertical coordinate
  lines, so the chartwise ACL theorem gives the estimate.  Defining the
  representative by the same half-space partition in the ball gives one
  measurable representative, and null-measurability of the exceptional polar
  set follows from measurability of the two sides of the inequality.
-/
theorem scalarWeakSobolev_unit_ball_radial_acl_representative_raywise_polar_charts
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wacl : H → ℝ,
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          NullMeasurableSet
            {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
              ¬ (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
                    wacl (s • (p.1 : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                    ∂MeasureTheory.volume)}
            ((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) ∧
          ∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere),
            ∀ᵐ r : Set.Ioi (0 : ℝ)
                ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
              ((r : Set.Ioi (0 : ℝ)) : ℝ) < s →
                ENNReal.ofReal
                  ‖wacl ((r : ℝ) • (θ : H)) -
                    wacl (s • (θ : H))‖ ≤
                  ∫⁻ t in
                    {t : ℝ | ((r : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                    ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                    ∂MeasureTheory.volume := by
  exact
    scalarWeakSobolev_unit_ball_radial_acl_representative_raywise_polar_charts_two_hemispheres
      _hweak _hw _hdw

/--
%%handwave
name:
  A radial ACL representative from local polar coordinates
statement:
  If \(w\) is a scalar \(W^{1,2}\) function on the Euclidean unit ball with
  weak derivative \(D w\), then it has a representative \(\widetilde w\) that
  agrees with \(w\) almost everywhere in the ball and, for every \(0<s<1\),
  the finite radial segment from \(r\theta\) to \(s\theta\) satisfies
  \[
    |\widetilde w(r\theta)-\widetilde w(s\theta)|
      \le \int_r^s |D w(t\theta)\theta|\,dt
  \]
  for almost every polar pair \((\theta,r)\) with \(0<r<s\).
proof:
  Apply the raywise polar-coordinate ACL representative theorem and use
  Fubini to pass from almost every direction and then almost every radius to
  almost every polar pair.
-/
theorem scalarWeakSobolev_unit_ball_radial_acl_segmentIntegral_bound_ae_polar_endpoints
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wacl : H → ℝ,
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
            ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
              ENNReal.ofReal
                ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
                  wacl (s • (p.1 : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                  ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                  ∂MeasureTheory.volume := by
  rcases
    scalarWeakSobolev_unit_ball_radial_acl_representative_raywise_polar_charts
      _hweak _hw _hdw with
    ⟨wacl, hwacl_eq, hwacl_raywise⟩
  refine ⟨wacl, hwacl_eq, ?_⟩
  intro s hs_pos hs_lt_one
  rcases hwacl_raywise s hs_pos hs_lt_one with
    ⟨hbad_null, hpolar_ae_ae⟩
  exact
    ae_prod_of_ae_ae_of_nullMeasurable_bad
      hbad_null hpolar_ae_ae

/--
%%handwave
name:
  Full radial ACL on one stereographic patch
statement:
  On one stereographic coordinate patch of the unit sphere, a scalar
  \(W^{1,2}\) function on the unit ball has a representative, equal to the
  original function almost everywhere, such that for almost every direction in
  the patch and every \(0<r<s<1\),
  \[
    |\widetilde w(r\theta)-\widetilde w(s\theta)|
      \le \int_r^s |D w(t\theta)\theta|\,dt .
  \]
proof:
  Apply the full vertical ACL representative in stereographic polar
  coordinates and transfer the almost-everywhere statement from coordinate
  space to the spherical chart source.  The polar coordinate map sends
  \((r,\sigma^{-1}(\theta))\) to \(r\theta\), and its radial derivative is the
  direction \(\theta\).
-/
theorem scalarWeakSobolev_stereographic_polar_patch_all_segments_acl_representative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {n : ℕ} [Fact (Module.finrank ℝ H = n + 1)]
    (v : Metric.sphere (0 : H) 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wpatch : H → ℝ,
      Measurable wpatch ∧
      wpatch =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere.restrict
              (stereographic' n v).source),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖wpatch (r • (θ : H)) - wpatch (s • (θ : H))‖ ≤
            ∫⁻ t in {t : ℝ | r < t ∧ t < s},
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂MeasureTheory.volume := by
  classical
  rcases
    scalarWeakSobolev_stereographic_polar_patch_full_vertical_acl_representative
      (n := n) v _hweak _hw _hdw with
    ⟨wpatch, hwpatch_meas, hwpatch_eq, hpatch_coord⟩
  refine ⟨wpatch, hwpatch_meas, hwpatch_eq, ?_⟩
  have hsource_meas : MeasurableSet (stereographic' n v).source :=
    (stereographic' n v).open_source.measurableSet
  have hpatch :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere.restrict
            (stereographic' n v).source),
        ∀ r s : ℝ, 0 < r → r < s → s < 1 →
          ENNReal.ofReal
            ‖wpatch
                (stereographicPolarPatchMap v (r, (stereographic' n v) θ)) -
              wpatch
                (stereographicPolarPatchMap v (s, (stereographic' n v) θ))‖ ≤
          ∫⁻ t in {t : ℝ | r < t ∧ t < s},
            ENNReal.ofReal
              ‖dw
                (stereographicPolarPatchMap v (t, (stereographic' n v) θ))
                (((stereographic' n v).symm
                  ((stereographic' n v) θ) : Metric.sphere (0 : H) 1) :
                    H)‖
              ∂MeasureTheory.volume :=
    ae_stereographic_toSphere_restrict_of_ae_volume
      (n := n) v hpatch_coord
  filter_upwards [hpatch, ae_restrict_mem hsource_meas] with θ hθ hθ_source
  intro r s hr_pos hrs hs_lt
  have hbound := hθ r s hr_pos hrs hs_lt
  rw [stereographicPolarPatchMap_apply_chart (n := n) v hθ_source r,
    stereographicPolarPatchMap_apply_chart (n := n) v hθ_source s] at hbound
  have hdir :
      (((stereographic' n v).symm
        ((stereographic' n v) θ) : Metric.sphere (0 : H) 1) : H) =
        (θ : H) :=
    stereographic'_symm_apply_apply_of_mem_source (n := n) v hθ_source
  have hpoint : ∀ t : ℝ,
      stereographicPolarPatchMap v (t, (stereographic' n v) θ) =
        t • (θ : H) := by
    intro t
    exact stereographicPolarPatchMap_apply_chart (n := n) v hθ_source t
  simpa [hpoint, hdir] using hbound

/--
%%handwave
name:
  A radial ACL representative on almost every complete ray
statement:
  If \(w\) is a scalar \(W^{1,2}\) function on the Euclidean unit ball with
  weak derivative \(D w\), then it has a representative \(\widetilde w\),
  equal to \(w\) almost everywhere in the ball, such that for almost every
  direction \(\theta\) and every pair \(0<r<s<1\),
  \[
    |\widetilde w(r\theta)-\widetilde w(s\theta)|
      \le \int_r^s |D w(t\theta)\theta|\,dt .
  \]
proof:
  In stereographic polar coordinates, the pulled-back function has an
  absolutely continuous representative on almost every vertical line, and the
  fundamental theorem of calculus gives the estimate for all pairs of radii
  on that line.  Transfer these full-line statements through the two
  stereographic hemisphere charts, using that the chart changes preserve null
  sets on the sphere and that the two hemispheres cover all directions.
-/
theorem scalarWeakSobolev_unit_ball_radial_acl_all_segments_ae_sphere
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wacl : H → ℝ,
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖wacl (r • (θ : H)) - wacl (s • (θ : H))‖ ≤
            ∫⁻ t in {t : ℝ | r < t ∧ t < s},
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂MeasureTheory.volume := by
  classical
  let n : ℕ := Module.finrank ℝ H - 1
  have hfin_pos : 0 < Module.finrank ℝ H :=
    Module.finrank_pos (R := ℝ) (M := H)
  haveI : Fact (Module.finrank ℝ H = n + 1) := by
    refine ⟨?_⟩
    dsimp [n]
    omega
  rcases (NormedSpace.sphere_nonempty (E := H) (x := (0 : H)) (r := (1 : ℝ))).2
      (by norm_num : (0 : ℝ) ≤ 1) with
    ⟨v₀, hv₀⟩
  let v : Metric.sphere (0 : H) 1 := ⟨v₀, hv₀⟩
  rcases scalarWeakSobolev_stereographic_polar_patch_all_segments_acl_representative
      (n := n) v _hweak _hw _hdw with
    ⟨wminusHemisphere, hwminus_meas, hwminus_eq, hwminus_acl⟩
  rcases scalarWeakSobolev_stereographic_polar_patch_all_segments_acl_representative
      (n := n) (-v) _hweak _hw _hdw with
    ⟨wplusHemisphere, hwplus_meas, hwplus_eq, hwplus_acl⟩
  let A : Set H := {z : H | 0 < inner ℝ z (v : H)}
  let wacl : H → ℝ := fun z ↦ if z ∈ A then wplusHemisphere z else wminusHemisphere z
  have hwacl_eq :
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w := by
    filter_upwards [hwplus_eq, hwminus_eq] with z hzplus hzminus
    by_cases hzA : z ∈ A
    · simp [wacl, hzA, hzplus]
    · simp [wacl, hzA, hzminus]
  refine ⟨wacl, hwacl_eq, ?_⟩
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  have hsource_minus_meas : MeasurableSet (stereographic' n v).source :=
    (stereographic' n v).open_source.measurableSet
  have hsource_plus_meas : MeasurableSet (stereographic' n (-v)).source :=
    (stereographic' n (-v)).open_source.measurableSet
  have hminus_imp :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        θ ∈ (stereographic' n v).source →
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖wminusHemisphere (r • (θ : H)) -
                wminusHemisphere (s • (θ : H))‖ ≤
            ∫⁻ t in {t : ℝ | r < t ∧ t < s},
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂MeasureTheory.volume :=
    (ae_restrict_iff' hsource_minus_meas).1
      (by simpa [μS] using hwminus_acl)
  have hplus_imp :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        θ ∈ (stereographic' n (-v)).source →
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖wplusHemisphere (r • (θ : H)) -
                wplusHemisphere (s • (θ : H))‖ ≤
            ∫⁻ t in {t : ℝ | r < t ∧ t < s},
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂MeasureTheory.volume :=
    (ae_restrict_iff' hsource_plus_meas).1
      (by simpa [μS] using hwplus_acl)
  have hplus_half :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        0 < inner ℝ (θ : H) (v : H) →
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖wacl (r • (θ : H)) - wacl (s • (θ : H))‖ ≤
            ∫⁻ t in {t : ℝ | r < t ∧ t < s},
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂MeasureTheory.volume := by
    filter_upwards [hplus_imp] with θ hθ_plus hθ_pos
    have hθ_source : θ ∈ (stereographic' n (-v)).source := by
      rw [stereographic'_source]
      intro hθ
      have hθeq : θ = (-v : Metric.sphere (0 : H) 1) := by
        simpa using hθ
      subst θ
      have hneg :
          inner ℝ ((-v : Metric.sphere (0 : H) 1) : H) (v : H) = -1 := by
        have hvnorm : ‖(v : H)‖ = 1 := norm_eq_of_mem_sphere v
        simp [hvnorm]
      have hbad_pos : (0 : ℝ) < -1 := by
        simpa [hneg] using hθ_pos
      norm_num at hbad_pos
    have hθ_acl := hθ_plus hθ_source
    intro r s hr_pos hrs hs_lt
    have hs_pos : 0 < s := lt_trans hr_pos hrs
    have hrA : (r • (θ : H)) ∈ A := by
      dsimp [A]
      simpa [real_inner_smul_left] using mul_pos hr_pos hθ_pos
    have hsA : (s • (θ : H)) ∈ A := by
      dsimp [A]
      simpa [real_inner_smul_left] using mul_pos hs_pos hθ_pos
    simpa [wacl, hrA, hsA] using hθ_acl r s hr_pos hrs hs_lt
  have hminus_half :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        ¬ 0 < inner ℝ (θ : H) (v : H) →
          ∀ r s : ℝ, 0 < r → r < s → s < 1 →
            ENNReal.ofReal
              ‖wacl (r • (θ : H)) - wacl (s • (θ : H))‖ ≤
            ∫⁻ t in {t : ℝ | r < t ∧ t < s},
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂MeasureTheory.volume := by
    filter_upwards [hminus_imp] with θ hθ_minus hθ_not_pos
    have hθ_source : θ ∈ (stereographic' n v).source := by
      rw [stereographic'_source]
      intro hθ
      have hθeq : θ = v := by
        simpa using hθ
      subst θ
      have hvnorm : ‖(v : H)‖ = 1 := norm_eq_of_mem_sphere v
      apply hθ_not_pos
      simp [hvnorm]
    have hθ_nonpos : inner ℝ (θ : H) (v : H) ≤ 0 :=
      le_of_not_gt hθ_not_pos
    have hθ_acl := hθ_minus hθ_source
    intro r s hr_pos hrs hs_lt
    have hs_pos : 0 < s := lt_trans hr_pos hrs
    have hrA : (r • (θ : H)) ∉ A := by
      dsimp [A]
      have hinner_nonpos :
          inner ℝ (r • (θ : H)) (v : H) ≤ 0 := by
        simpa [real_inner_smul_left] using
          mul_nonpos_of_nonneg_of_nonpos hr_pos.le hθ_nonpos
      exact not_lt_of_ge hinner_nonpos
    have hsA : (s • (θ : H)) ∉ A := by
      dsimp [A]
      have hinner_nonpos :
          inner ℝ (s • (θ : H)) (v : H) ≤ 0 := by
        simpa [real_inner_smul_left] using
          mul_nonpos_of_nonneg_of_nonpos hs_pos.le hθ_nonpos
      exact not_lt_of_ge hinner_nonpos
    simpa [wacl, hrA, hsA] using hθ_acl r s hr_pos hrs hs_lt
  simpa [μS] using
    (hplus_half.and hminus_half).mono fun θ hθ ↦ by
      by_cases hθ_pos : 0 < inner ℝ (θ : H) (v : H)
      · exact hθ.1 hθ_pos
      · exact hθ.2 hθ_pos

/--
%%handwave
name:
  Fixed-endpoint radial absolute continuity for an ACL representative
statement:
  Let \(0<s<1\).  A scalar \(W^{1,2}\) function on the Euclidean unit ball has
  a representative agreeing with it almost everywhere in the ball such that
  almost every finite radial segment ending at \(s\theta\) satisfies the ACL
  segment estimate.
proof:
  Apply the representative form that works for all interior endpoints and
  specialize to the chosen endpoint radius.
-/
theorem scalarWeakSobolev_unit_ball_radial_acl_segmentIntegral_bound_ae_polar_endpoint
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {s : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ wacl : H → ℝ,
      wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
      ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
          ((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
        ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
          ENNReal.ofReal
            ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
              wacl (s • (p.1 : H))‖ ≤
            ∫⁻ t in
              {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
  rcases
    scalarWeakSobolev_unit_ball_radial_acl_segmentIntegral_bound_ae_polar_endpoints
      hweak hw hdw with
    ⟨wacl, hwacl_eq, hwacl_segments⟩
  exact ⟨wacl, hwacl_eq, hwacl_segments s hs_pos hs_lt_one⟩

/--
%%handwave
name:
  An \(L^1\)-Cauchy family of spherical slices converges in measure
statement:
  Let \(s_k\) be radii and suppose each slice \(\theta\mapsto w(s_k\theta)\) belongs to \(L^1\) of the unit sphere.  If these slices are Cauchy in \(L^1\), then there is a measurable \(\tau:H\to\mathbb R\) such that \(w(s_k\theta)\) converges in spherical measure to \(\tau(\theta)\).
proof:
  Completeness of \(L^1\) gives a limit class.  Choose a measurable representative on the sphere, extend it measurably to \(H\), and use that convergence in \(L^1\) implies convergence in measure.
-/
private theorem sphere_slices_tendstoInMeasure_of_L1_cauchy
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} (s : ℕ → ℝ)
    (hmem :
      ∀ n : ℕ,
        MemLp
          (fun θ : Metric.sphere (0 : H) 1 ↦ w ((s n) • (θ : H)))
          1 ((MeasureTheory.volume : Measure H).toSphere))
    (hcauchy :
      CauchySeq
        (fun n : ℕ ↦
          (hmem n).toLp
            (fun θ : Metric.sphere (0 : H) 1 ↦
              w ((s n) • (θ : H))))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        TendstoInMeasure ((MeasureTheory.volume : Measure H).toSphere)
          (fun n (θ : Metric.sphere (0 : H) 1) ↦
            w ((s n) • (θ : H)))
          Filter.atTop
          (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H)) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let Fseq : ℕ → Lp ℝ 1 μS :=
    fun n : ℕ ↦
      (hmem n).toLp
        (fun θ : Metric.sphere (0 : H) 1 ↦ w ((s n) • (θ : H)))
  rcases cauchySeq_tendsto_of_complete (u := Fseq) (by simpa [Fseq, μS] using hcauchy) with
    ⟨F, hF_tendsto⟩
  have hLp_tendsto :
      TendstoInMeasure μS
        (fun n (θ : Metric.sphere (0 : H) 1) ↦ Fseq n θ)
        Filter.atTop
        (fun θ : Metric.sphere (0 : H) 1 ↦ F θ) :=
    tendstoInMeasure_of_tendsto_Lp (μ := μS) (p := (1 : ℝ≥0∞))
      hF_tendsto
  have hslices_tendsto :
      TendstoInMeasure μS
        (fun n (θ : Metric.sphere (0 : H) 1) ↦
          w ((s n) • (θ : H)))
        Filter.atTop
        (fun θ : Metric.sphere (0 : H) 1 ↦ F θ) := by
    refine TendstoInMeasure.congr_left ?_ hLp_tendsto
    intro n
    simpa [Fseq, μS] using
      (hmem n).coeFn_toLp
  have hSphere_meas : MeasurableSet (Metric.sphere (0 : H) 1) :=
    Metric.isClosed_sphere.measurableSet
  have hF_meas :
      Measurable (fun θ : Metric.sphere (0 : H) 1 ↦ F θ) := by
    simpa [μS] using L1.measurable_coeFn (μ := μS) F
  rcases
    (MeasurableEmbedding.subtype_coe hSphere_meas).exists_measurable_extend
      hF_meas (fun _ : H ↦ ⟨(0 : ℝ)⟩) with
    ⟨τ, hτ_meas, hτ_ext⟩
  refine ⟨τ, hτ_meas, ?_⟩
  refine TendstoInMeasure.congr_right ?_ hslices_tendsto
  exact Filter.Eventually.of_forall fun θ ↦ by
    simpa [Function.comp_def] using (congrFun hτ_ext θ).symm

/--
%%handwave
name:
  Almost-everywhere equality on the ball gives almost-everywhere equality of slices
statement:
  If \(f=g\) almost everywhere in the unit ball of \(H\), then for \(r^{\dim H-1}dr\)-almost every \(0<r<1\), one has \(f(r\theta)=g(r\theta)\) for spherical-almost every unit direction \(\theta\).
proof:
  Apply the polar integration formula to the null set on which \(f\ne g\).  The corresponding product set of directions and radii is null, and Fubini gives the asserted almost-everywhere statement in the radial variable.
-/
private theorem ae_radius_sphere_slice_eq_of_ae_volume_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {f g : H → ℝ}
    (hfg : f =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] g) :
    ∀ᵐ r : Set.Ioi (0 : ℝ)
        ∂((MeasureTheory.Measure.volumeIoiPow
          (Module.finrank ℝ H - 1)).restrict
            {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        f ((r : ℝ) • (θ : H)) = g ((r : ℝ) • (θ : H)) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r | (r : ℝ) < 1}
  let νR : Measure (Set.Ioi (0 : ℝ)) := μR.restrict R
  have hpolar :
      ∀ᵐ p ∂μS.prod νR,
        f ((p.2 : ℝ) • (p.1 : H)) =
          g ((p.2 : ℝ) • (p.1 : H)) := by
    simpa [Filter.EventuallyEq, μS, μR, R, νR] using
      ae_polar_product_unitBall_of_ae_volume_unitBall
        (H := H) (P := fun z : H ↦ f z = g z) hfg
  have hswap :
      ∀ᵐ p ∂νR.prod μS,
        f ((p.1 : ℝ) • (p.2 : H)) =
          g ((p.1 : ℝ) • (p.2 : H)) := by
    have h :=
      (Measure.measurePreserving_swap (μ := νR) (ν := μS)).quasiMeasurePreserving.tendsto_ae
        hpolar
    simpa [Prod.swap] using h
  simpa [μS, μR, R, νR] using Measure.ae_ae_of_ae_prod hswap

/--
%%handwave
name:
  Selecting good radii converging to one
statement:
  If \(P(r)\) holds for \(r^n\,dr\)-almost every \(0<r<1\), then there are radii \(s_k\in(0,1)\) with \(P(s_k)\) for every \(k\) and \(s_k\to1\).
proof:
  For each \(k\), the interval \((1-1/(k+2),1)\) has positive \(r^n\,dr\)-measure, so it cannot be contained in the exceptional null set.  Choose a good radius there; the interval bounds force convergence to \(1\).
-/
private theorem exists_seq_tendsto_one_of_ae_volumeIoiPow_restrict
    {n : ℕ} {P : Set.Ioi (0 : ℝ) → Prop}
    (hP : ∀ᵐ r
        ∂((MeasureTheory.Measure.volumeIoiPow n).restrict
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
        P r) :
    ∃ s : ℕ → Set.Ioi (0 : ℝ),
      (∀ k : ℕ, ((s k : Set.Ioi (0 : ℝ)) : ℝ) < 1 ∧ P (s k)) ∧
        Filter.Tendsto (fun k : ℕ ↦ ((s k : Set.Ioi (0 : ℝ)) : ℝ))
          Filter.atTop (𝓝 (1 : ℝ)) := by
  classical
  let Q : ℝ → Prop := fun t ↦ ∀ ht_pos : 0 < t, t < 1 → P ⟨t, ht_pos⟩
  have hQae : ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ), Q t := by
    simpa [Q] using
      ae_volume_Ioo_zero_one_of_ae_volumeIoiPow_restrict
        (n := n) (P := P) hP
  have hQdense : Dense {t : ℝ | Q t} :=
    Measure.dense_of_ae (μ := (MeasureTheory.volume : Measure ℝ)) hQae
  have hchoose :
      ∀ k : ℕ,
        ∃ t : ℝ,
          Q t ∧ t ∈ Set.Ioo (1 - 1 / ((k : ℝ) + 1)) (1 : ℝ) := by
    intro k
    have hden_pos : 0 < (k : ℝ) + 1 := by positivity
    have hleft_lt_one : 1 - 1 / ((k : ℝ) + 1) < (1 : ℝ) := by
      have hdiv_pos : 0 < 1 / ((k : ℝ) + 1) := one_div_pos.mpr hden_pos
      linarith
    rcases hQdense.exists_mem_open isOpen_Ioo
        (Set.nonempty_Ioo.mpr hleft_lt_one) with
      ⟨t, htQ, htIoo⟩
    exact ⟨t, htQ, htIoo⟩
  choose s hs using hchoose
  have hs_pos : ∀ k : ℕ, 0 < s k := by
    intro k
    rcases hs k with ⟨_hsQ, hsIoo⟩
    have hden_ge_one : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hdiv_le_one : 1 / ((k : ℝ) + 1) ≤ (1 : ℝ) := by
      have h := one_div_le_one_div_of_le (a := (1 : ℝ))
        (b := (k : ℝ) + 1) zero_lt_one hden_ge_one
      simpa using h
    have hleft_nonneg : 0 ≤ 1 - 1 / ((k : ℝ) + 1) := by
      linarith
    exact lt_of_le_of_lt hleft_nonneg hsIoo.1
  refine ⟨fun k : ℕ ↦ ⟨s k, hs_pos k⟩, ?_, ?_⟩
  · intro k
    rcases hs k with ⟨hsQ, hsIoo⟩
    exact ⟨hsIoo.2, hsQ (hs_pos k) hsIoo.2⟩
  · have hdiv :
        Filter.Tendsto
          (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1))
          Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hleft :
        Filter.Tendsto
          (fun k : ℕ ↦ 1 - 1 / ((k : ℝ) + 1))
          Filter.atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft tendsto_const_nhds
      ?_ ?_
    · exact Filter.Eventually.of_forall fun k ↦ le_of_lt (hs k).2.1
    · exact Filter.Eventually.of_forall fun k ↦ le_of_lt (hs k).2.2

/--
%%handwave
name:
  Selecting boundary-approaching radii where representatives agree
statement:
  If \(f=g\) almost everywhere in the unit ball, then there are radii \(s_k<1\) with \(s_k\to1\) such that \(f(s_k\theta)=g(s_k\theta)\) for spherical-almost every \(\theta\), for every \(k\).
proof:
  Almost-everywhere equality in the ball yields the slice equality for almost every radial parameter.  Apply the selection of good radii converging to \(1\) to this radial property.
-/
private theorem exists_seq_tendsto_one_sphere_slice_eq_of_ae_volume_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {f g : H → ℝ}
    (hfg : f =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] g) :
    ∃ s : ℕ → Set.Ioi (0 : ℝ),
      (∀ k : ℕ,
        ((s k : Set.Ioi (0 : ℝ)) : ℝ) < 1 ∧
          (∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere),
            f (((s k : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
              g (((s k : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))) ∧
        Filter.Tendsto (fun k : ℕ ↦ ((s k : Set.Ioi (0 : ℝ)) : ℝ))
          Filter.atTop (𝓝 (1 : ℝ)) := by
  classical
  let P : Set.Ioi (0 : ℝ) → Prop :=
    fun r ↦
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        f ((r : ℝ) • (θ : H)) = g ((r : ℝ) • (θ : H))
  have hP :
      ∀ᵐ r : Set.Ioi (0 : ℝ)
          ∂((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
        P r :=
    ae_radius_sphere_slice_eq_of_ae_volume_unitBall (H := H) hfg
  rcases
    exists_seq_tendsto_one_of_ae_volumeIoiPow_restrict
      (n := Module.finrank ℝ H - 1) (P := P) hP with
    ⟨s, hs, hs_tendsto⟩
  refine ⟨s, ?_, hs_tendsto⟩
  intro k
  simpa [P] using hs k

/--
%%handwave
name:
  Square-integrability transfers to polar coordinates
statement:
  If a scalar function is square-integrable on the Euclidean unit ball, then
  its polar pullback \((\theta,r)\mapsto w(r\theta)\) is square-integrable
  for the product of spherical measure and the radial polar measure restricted
  to \(0<r<1\).
proof:
  Remove the origin and use the polar-coordinate homeomorphism between the
  punctured ball and the product of the unit sphere with the interval of
  positive radii.  This homeomorphism preserves the polar product measure,
  and the origin has zero Haar measure, so the \(L^2\) norm is unchanged up
  to this null set.
-/
private theorem polar_product_sphere_radius_memLp_two_of_memLp_two_unitBall
    {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {w : H → E}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    MemLp
      (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
        w ((p.2 : ℝ) • (p.1 : H)))
      2
      (((MeasureTheory.volume : Measure H).toSphere).prod
        ((MeasureTheory.Measure.volumeIoiPow
          (Module.finrank ℝ H - 1)).restrict
            {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) := by
  classical
  let B : Set H := Metric.ball (0 : H) 1
  let e : ({0}ᶜ : Set H) ≃ₜ
      (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    homeomorphUnitSphereProd H
  let μNZ : Measure ({0}ᶜ : Set H) :=
    (MeasureTheory.volume : Measure H).comap
      ((↑) : ({0}ᶜ : Set H) → H)
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let ν : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod μR
  let R : Set (Set.Ioi (0 : ℝ)) := {r | (r : ℝ) < 1}
  let S : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) < 1}
  let T : Set ({0}ᶜ : Set H) := {x | ‖(x : H)‖ < 1}
  let F : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → E :=
    fun p ↦ w ((p.2 : ℝ) • (p.1 : H))
  have hNZ_meas : MeasurableSet ({0}ᶜ : Set H) :=
    (measurableSet_singleton (0 : H)).compl
  have hw_NZ :
      MemLp w 2
        ((MeasureTheory.volume.restrict B).restrict ({0}ᶜ : Set H)) :=
    _hw.mono_measure Measure.restrict_le_self
  have hw_subtype_comap :
      MemLp (fun x : ({0}ᶜ : Set H) ↦ w (x : H)) 2
        ((MeasureTheory.volume.restrict B).comap
          ((↑) : ({0}ᶜ : Set H) → H)) := by
    have hmap :
        Measure.map ((↑) : ({0}ᶜ : Set H) → H)
            ((MeasureTheory.volume.restrict B).comap
              ((↑) : ({0}ᶜ : Set H) → H)) =
          (MeasureTheory.volume.restrict B).restrict ({0}ᶜ : Set H) :=
      map_comap_subtype_coe hNZ_meas (MeasureTheory.volume.restrict B)
    have hw_map :
        MemLp w 2
          (Measure.map ((↑) : ({0}ᶜ : Set H) → H)
            ((MeasureTheory.volume.restrict B).comap
              ((↑) : ({0}ᶜ : Set H) → H))) := by
      simpa [hmap] using hw_NZ
    exact
      (MeasurableEmbedding.subtype_coe hNZ_meas).memLp_map_measure_iff.1
        hw_map
  have hcomap_restrict :
      (MeasureTheory.volume.restrict B).comap
          ((↑) : ({0}ᶜ : Set H) → H) =
        μNZ.restrict T := by
    have hraw :=
      (MeasurableEmbedding.subtype_coe hNZ_meas).comap_restrict
        (MeasureTheory.volume : Measure H) B
    have hpreB :
        ((↑) : ({0}ᶜ : Set H) → H) ⁻¹' B = T := by
      ext x
      simp [B, T, Metric.mem_ball, dist_eq_norm]
    simpa [μNZ, hpreB] using hraw
  have hw_subtype :
      MemLp (fun x : ({0}ᶜ : Set H) ↦ w (x : H)) 2 (μNZ.restrict T) := by
    simpa [hcomap_restrict] using hw_subtype_comap
  have hmp : MeasurePreserving e μNZ ν := by
    simpa [e, μNZ, ν, μS, μR] using
      (MeasureTheory.volume : Measure H).measurePreserving_homeomorphUnitSphereProd
  have hmap_restrict :
      (μNZ.restrict (e ⁻¹' S)).map e = ν.restrict S := by
    have hrestrict := e.measurableEmbedding.restrict_map μNZ S
    rw [hmp.map_eq] at hrestrict
    exact hrestrict.symm
  have hpre :
      e ⁻¹' S = T := by
    ext x
    change (((homeomorphUnitSphereProd H) x).2 : ℝ) < 1 ↔
      ‖(x : H)‖ < 1
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  have hS_eq : S = Set.univ ×ˢ R := by
    ext p
    simp [S, R]
  have hmeasure :
      ν.restrict S = μS.prod (μR.restrict R) := by
    rw [hS_eq]
    have hprod :=
      Measure.prod_restrict (μ := μS) (ν := μR) Set.univ R
    simpa [ν] using hprod.symm
  have hmap_target :
      (μNZ.restrict T).map e = μS.prod (μR.restrict R) := by
    rw [← hpre, hmap_restrict, hmeasure]
  have hcomp_eq :
      F ∘ e = fun x : ({0}ᶜ : Set H) ↦ w (x : H) := by
    funext x
    have hx_norm_ne : ‖(x : H)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact x.2
    have hdir :
        (((e x).1 : Metric.sphere (0 : H) 1) : H) =
          ((1 / ‖(x : H)‖) : ℝ) • (x : H) := by
      simp [e, homeomorphUnitSphereProd_apply_fst_coe, div_eq_mul_inv]
    have hr : (((e x).2 : Set.Ioi (0 : ℝ)) : ℝ) = ‖(x : H)‖ := by
      simp [e, homeomorphUnitSphereProd_apply_snd_coe]
    have hpoint : ((e x).2 : ℝ) • ((e x).1 : H) = (x : H) := by
      rw [hr, hdir, smul_smul]
      have hcoef : ‖(x : H)‖ * (1 / ‖(x : H)‖) = (1 : ℝ) := by
        field_simp [hx_norm_ne]
      rw [hcoef, one_smul]
    simp [F, hpoint]
  have hF_map :
      MemLp F 2 ((μNZ.restrict T).map e) := by
    rw [e.measurableEmbedding.memLp_map_measure_iff]
    simpa [hcomp_eq] using hw_subtype
  simpa [F, μS, μR, R, hmap_target] using hF_map

/--
%%handwave
name:
  Square integrability of the radial derivative in polar coordinates
statement:
  If a covector field \(dw\) belongs to \(L^2\) on the unit ball, then
  \[
    (\theta,r)\longmapsto dw(r\theta)(\theta)
  \]
  belongs to \(L^2\) for spherical measure times \(r^{\dim H-1}dr\), restricted to \(0<r<1\).
proof:
  The evaluation is bounded pointwise by the operator norm \(\|dw(r\theta)\|\), since \(\|\theta\|=1\).  The polar-coordinate formula transfers the \(L^2\) bound of \(dw\) on the ball to the product measure.
-/
private theorem
    polar_product_sphere_radius_derivative_eval_memLp_two_of_memLp_two_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {dw : H → H →L[ℝ] ℝ}
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    MemLp
      (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
        dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H))
      2
      (((MeasureTheory.volume : Measure H).toSphere).prod
        ((MeasureTheory.Measure.volumeIoiPow
          (Module.finrank ℝ H - 1)).restrict
            {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) := by
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    ((MeasureTheory.volume : Measure H).toSphere).prod
      ((MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ H - 1)).restrict
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})
  have hdw_polar :
      MemLp
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          dw ((p.2 : ℝ) • (p.1 : H)))
        2 μ := by
    simpa [μ] using
      polar_product_sphere_radius_memLp_two_of_memLp_two_unitBall
        (H := H) (E := H →L[ℝ] ℝ) (w := dw) _hdw
  have hθ :
      AEStronglyMeasurable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          (p.1 : H)) μ := by
    exact (by measurability : Measurable
      (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
        (p.1 : H))).aestronglyMeasurable
  have hval :
      AEStronglyMeasurable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)) μ := by
    simpa using
      (ContinuousLinearMap.apply ℝ ℝ).flip.aestronglyMeasurable_comp₂
        hdw_polar.aestronglyMeasurable hθ
  refine hdw_polar.of_le hval ?_
  exact Filter.Eventually.of_forall fun p ↦ by
    have hθ_norm : ‖(p.1 : H)‖ = (1 : ℝ) := by
      simpa [Metric.mem_sphere, dist_eq_norm] using p.1.2
    calc
      ‖dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)‖ ≤
          ‖dw ((p.2 : ℝ) • (p.1 : H))‖ * ‖(p.1 : H)‖ :=
        (dw ((p.2 : ℝ) • (p.1 : H))).le_opNorm (p.1 : H)
      _ = ‖dw ((p.2 : ℝ) • (p.1 : H))‖ := by
        rw [hθ_norm, mul_one]

/--
%%handwave
name:
  Polar measure of a shrinking boundary collar tends to zero
statement:
  For spherical measure times \(r^{\dim H-1}dr\) on \(0<r<1\), the measure of
  \[
    \{(\theta,r):1-\varepsilon<r<1\}
  \]
  tends to zero as \(\varepsilon\downarrow0\).
proof:
  The collar measure factors into the finite measure of the sphere and the radial measure of \((1-\varepsilon,1)\).  The latter tends to zero by continuity of the integral, equivalently continuity from above for the shrinking intervals.
-/
private theorem polar_product_inner_collar_measure_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (((MeasureTheory.volume : Measure H).toSphere).prod
          ((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}))
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod (μR.restrict R)
  let S : ℝ → Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    fun ε : ℝ ↦
      {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
        (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}
  have hmeas : ∀ ε > (0 : ℝ), NullMeasurableSet (S ε) μ := by
    intro ε _hε
    dsimp [S, μ, μS, μR, R]
    exact (by measurability : MeasurableSet
      {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
        (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}).nullMeasurableSet
  have hmono : ∀ i j : ℝ, (0 : ℝ) < i → i ≤ j → S i ⊆ S j := by
    intro i j _hi hij p hp
    dsimp [S] at hp ⊢
    exact ⟨by linarith [hp.1, hij], hp.2⟩
  have hfinite : ∃ ε > (0 : ℝ), μ (S ε) ≠ ⊤ := by
    refine ⟨1, by norm_num, ?_⟩
    let R1 : Set (Set.Ioi (0 : ℝ)) :=
      {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
    have hS_subset : S 1 ⊆ Set.univ ×ˢ R1 := by
      intro p hp
      dsimp [S, R1] at hp ⊢
      exact ⟨trivial, hp.2⟩
    have hR1_meas : MeasurableSet R1 := by
      dsimp [R1]
      measurability
    have hR1_finite : μR R1 ≠ ⊤ := by
      have hR1_eq :
          R1 = Set.Iio (⟨(1 : ℝ), by norm_num⟩ : Set.Ioi (0 : ℝ)) := rfl
      rw [hR1_eq, MeasureTheory.Measure.volumeIoiPow_apply_Iio]
      exact ENNReal.ofReal_ne_top
    have hprod_finite : μ (Set.univ ×ˢ R1) ≠ ⊤ := by
      rw [show μ = μS.prod (μR.restrict R) by rfl]
      rw [Measure.prod_prod]
      have hμS_ne_top : μS Set.univ ≠ ⊤ := measure_ne_top μS Set.univ
      have hμR_restrict_R1_ne_top :
          (μR.restrict R) R1 ≠ ⊤ :=
        ne_top_of_le_ne_top hR1_finite
          (Measure.le_iff'.1 Measure.restrict_le_self R1)
      exact ENNReal.mul_ne_top hμS_ne_top hμR_restrict_R1_ne_top
    exact ne_top_of_le_ne_top hprod_finite (measure_mono hS_subset)
  have hS_empty : (⋂ ε > (0 : ℝ), S ε) = (∅ :
      Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ))) := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro p hp
    have hp_all : ∀ ε : ℝ, 0 < ε → p ∈ S ε := by
      intro ε hε
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hp ε) hε
    have hp_upper : (p.2 : ℝ) < 1 := (hp_all 1 (by norm_num)).2
    let δ : ℝ := (1 - (p.2 : ℝ)) / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact half_pos (sub_pos.mpr hp_upper)
    have hp_lower : (1 : ℝ) - δ < (p.2 : ℝ) := (hp_all δ hδ_pos).1
    dsimp [δ] at hp_lower
    have hone_lt : (1 : ℝ) < (p.2 : ℝ) := by
      have htwice :
          2 * (1 - (1 - (p.2 : ℝ)) / 2) < 2 * (p.2 : ℝ) := by
        exact mul_lt_mul_of_pos_left hp_lower (by norm_num : (0 : ℝ) < 2)
      ring_nf at htwice
      linarith [htwice]
    exact (not_lt_of_ge hp_upper.le) hone_lt
  have htendsto :=
    tendsto_measure_biInter_gt
      (μ := μ) (s := S) (a := (0 : ℝ)) hmeas hmono hfinite
  have htarget :
      Filter.Tendsto (μ ∘ S) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [hS_empty] using htendsto
  simpa [Function.comp_def, μ, μS, μR, R, S] using htarget

/--
%%handwave
name:
  Weighted radial derivative mass vanishes in shrinking collars
statement:
  If \(dw\in L^2\) on the unit ball, then
  \[
    \int_{\{(\theta,r):1-\varepsilon<r<1\}}^{-}
      \operatorname{ofReal}(\|dw(r\theta)(\theta)\|)
      \,d\theta\,r^{\dim H-1}dr
    \longrightarrow0
  \]
  as \(\varepsilon\downarrow0\).
proof:
  The radial evaluation belongs to \(L^2\), hence to \(L^1\) on the finite polar product space.  Absolute continuity of its integral, together with the fact that the collar measures tend to zero, gives the limit.
-/
private theorem
    polar_product_sphere_radius_derivative_eval_weighted_tail_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {dw : H → H →L[ℝ] ℝ}
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        ∫⁻ p in
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1},
          ENNReal.ofReal
            ‖dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)‖
          ∂(((MeasureTheory.volume : Measure H).toSphere).prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    ((MeasureTheory.volume : Measure H).toSphere).prod
      ((MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ H - 1)).restrict
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})
  let F : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p ↦ dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)
  have hR_finite :
      MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1} ≠ ⊤ := by
    have hR_eq :
        {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1} =
          Set.Iio (⟨(1 : ℝ), by norm_num⟩ : Set.Ioi (0 : ℝ)) := rfl
    rw [hR_eq, MeasureTheory.Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure
      ((MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)).restrict
        {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}) :=
    isFiniteMeasure_restrict.2 hR_finite
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hF_mem : MemLp F 2 μ := by
    simpa [F, μ] using
      polar_product_sphere_radius_derivative_eval_memLp_two_of_memLp_two_unitBall
        (H := H) (dw := dw) _hdw
  have hF_int : Integrable F μ :=
    hF_mem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hF_finite :
      (∫⁻ p, ENNReal.ofReal ‖F p‖ ∂μ) ≠ ⊤ :=
    ne_of_lt hF_int.norm.lintegral_lt_top
  have hmeasure :
      Filter.Tendsto
        (μ ∘
          (fun ε : ℝ ↦
            {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
              (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [Function.comp_def, μ] using
      polar_product_inner_collar_measure_tendsto_zero (H := H)
  have htendsto :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫⁻ p in
            {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
              (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1},
            ENNReal.ofReal ‖F p‖ ∂μ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_setLIntegral_zero hF_finite hmeasure
  simpa [F, μ] using htendsto

/--
%%handwave
name:
  Comparing unweighted and weighted radial measure near the boundary
statement:
  If \(\varepsilon\le1/2\), then on \(1-\varepsilon<r<1\),
  \[
    dr\le \big((1/2)^n\big)^{-1} r^n\,dr
  \]
  as measures on the positive real axis.
proof:
  Throughout the collar, \(r\ge1/2\), hence \(r^n\ge(1/2)^n\).  Integrating this pointwise lower bound for the density and rearranging gives the measure inequality.
-/
private theorem radial_comap_volume_restrict_inner_collar_le_volumeIoiPow
    (n : ℕ) {ε : ℝ} (hε_le_half : ε ≤ (1 / 2 : ℝ)) :
    (Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
        (MeasureTheory.volume : Measure ℝ)).restrict
        {r : Set.Ioi (0 : ℝ) |
          (1 : ℝ) - ε < (r : ℝ) ∧ (r : ℝ) < 1} ≤
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ n))⁻¹ •
        (MeasureTheory.Measure.volumeIoiPow n).restrict
          {r : Set.Ioi (0 : ℝ) |
            (1 : ℝ) - ε < (r : ℝ) ∧ (r : ℝ) < 1} := by
  classical
  let μI : Measure (Set.Ioi (0 : ℝ)) :=
    Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
      (MeasureTheory.volume : Measure ℝ)
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow n
  let K : Set (Set.Ioi (0 : ℝ)) :=
    {r : Set.Ioi (0 : ℝ) |
      (1 : ℝ) - ε < (r : ℝ) ∧ (r : ℝ) < 1}
  let δ : Set.Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun r ↦ ENNReal.ofReal (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n)
  let c : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ n)
  have hK_meas : MeasurableSet K := by
    dsimp [K]
    measurability
  have hc0 : c ≠ 0 := by
    have hcpos : 0 < c := by
      dsimp [c]
      exact ENNReal.ofReal_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    exact ne_of_gt hcpos
  have hctop : c ≠ ⊤ := by
    dsimp [c]
    exact ENNReal.ofReal_ne_top
  have hδ : ∀ᵐ r ∂μI.restrict K, c ≤ δ r := by
    filter_upwards [ae_restrict_mem hK_meas] with r hr
    have hhalf_le : (1 / 2 : ℝ) ≤ (r : ℝ) := by
      linarith [hr.1, hε_le_half]
    have hpow_le : (1 / 2 : ℝ) ^ n ≤ ((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf_le n
    exact ENNReal.ofReal_le_ofReal hpow_le
  have hμR_eq : μR = μI.withDensity δ := by
    dsimp [μR, μI, δ, MeasureTheory.Measure.volumeIoiPow]
  have hweighted_eq : μR.restrict K = (μI.restrict K).withDensity δ := by
    rw [hμR_eq, restrict_withDensity hK_meas δ]
  have hconst_le : c • μI.restrict K ≤ μR.restrict K := by
    rw [hweighted_eq, ← withDensity_const (μ := μI.restrict K) c]
    exact withDensity_mono hδ
  calc
    μI.restrict K = (1 : ℝ≥0∞) • μI.restrict K := by simp
    _ = (c⁻¹ * c) • μI.restrict K := by
      rw [ENNReal.inv_mul_cancel hc0 hctop]
    _ = c⁻¹ • (c • μI.restrict K) := by rw [smul_smul]
    _ ≤ c⁻¹ • μR.restrict K := by
      apply Measure.le_iff.2
      intro s hs
      rw [Measure.smul_apply, Measure.smul_apply]
      exact mul_le_mul_right (Measure.le_iff.1 hconst_le s hs) _
    _ =
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ n))⁻¹ •
        (MeasureTheory.Measure.volumeIoiPow n).restrict
          {r : Set.Ioi (0 : ℝ) |
            (1 : ℝ) - ε < (r : ℝ) ∧ (r : ℝ) < 1} := rfl

/--
%%handwave
name:
  Comparing unweighted and weighted radial integrals near the boundary
statement:
  If \(\varepsilon\le1/2\) and \(F\ge0\), then
  \[
    \int_{1-\varepsilon<r<1}^{-}F(r)\,dr
    \le \big((1/2)^n\big)^{-1}
       \int_{1-\varepsilon<r<1}^{-}F(r)r^n\,dr.
  \]
proof:
  Integrate \(F\) against the measure inequality \(dr\le((1/2)^n)^{-1}r^n\,dr\) on the collar.
-/
private theorem radial_comap_volume_setLIntegral_inner_collar_le_volumeIoiPow
    (n : ℕ) {ε : ℝ} (hε_le_half : ε ≤ (1 / 2 : ℝ))
    (F : Set.Ioi (0 : ℝ) → ℝ≥0∞) :
    ∫⁻ r in
        {r : Set.Ioi (0 : ℝ) |
          (1 : ℝ) - ε < (r : ℝ) ∧ (r : ℝ) < 1},
        F r
        ∂(Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
          (MeasureTheory.volume : Measure ℝ)) ≤
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ n))⁻¹ *
        ∫⁻ r in
          {r : Set.Ioi (0 : ℝ) |
            (1 : ℝ) - ε < (r : ℝ) ∧ (r : ℝ) < 1},
          F r ∂MeasureTheory.Measure.volumeIoiPow n := by
  let K : Set (Set.Ioi (0 : ℝ)) :=
    {r : Set.Ioi (0 : ℝ) |
      (1 : ℝ) - ε < (r : ℝ) ∧ (r : ℝ) < 1}
  have hmeasure_le :
      (Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
          (MeasureTheory.volume : Measure ℝ)).restrict K ≤
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ n))⁻¹ •
          (MeasureTheory.Measure.volumeIoiPow n).restrict K :=
    radial_comap_volume_restrict_inner_collar_le_volumeIoiPow
      n hε_le_half
  calc
    ∫⁻ r in K, F r
        ∂(Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
          (MeasureTheory.volume : Measure ℝ)) ≤
      ∫⁻ r, F r
        ∂((ENNReal.ofReal ((1 / 2 : ℝ) ^ n))⁻¹ •
          (MeasureTheory.Measure.volumeIoiPow n).restrict K) :=
        lintegral_mono' hmeasure_le le_rfl
    _ =
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ n))⁻¹ *
        ∫⁻ r in K, F r ∂MeasureTheory.Measure.volumeIoiPow n := by
      rw [lintegral_smul_measure, smul_eq_mul]

/--
%%handwave
name:
  Unweighted radial derivative tails vanish at the sphere
statement:
  If \(dw\in L^2\) on the unit ball, then
  \[
    \int_{\mathbb S}^{-}\int_{1-\varepsilon<t<1}^{-}
      \operatorname{ofReal}(\|dw(t\theta)(\theta)\|)\,dt\,d\theta
    \longrightarrow0
  \]
  as \(\varepsilon\downarrow0\).
proof:
  For small \(\varepsilon\), \(t\ge1/2\) on the collar, so unweighted radial measure is bounded by a fixed multiple of \(t^{\dim H-1}dt\).  Tonelli converts the iterated integral to the polar product integral, whose weighted collar tail tends to zero.
-/
private theorem
    polar_sphere_unweighted_radial_derivative_tail_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {dw : H → H →L[ℝ] ℝ}
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        ∫⁻ θ : Metric.sphere (0 : H) 1,
          ∫⁻ t in {t : ℝ | (1 : ℝ) - ε < t ∧ t < 1},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂(MeasureTheory.volume : Measure ℝ)
          ∂((MeasureTheory.volume : Measure H).toSphere))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let n : ℕ := Module.finrank ℝ H - 1
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow n
  let R : Set (Set.Ioi (0 : ℝ)) :=
    {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod (μR.restrict R)
  let C : ℝ≥0∞ := (ENNReal.ofReal ((1 / 2 : ℝ) ^ n))⁻¹
  let weighted : ℝ → ℝ≥0∞ :=
    fun ε : ℝ ↦
      ∫⁻ p in
        {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
          (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1},
        ENNReal.ofReal ‖dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)‖
        ∂μ
  have hweighted_tendsto :
      Filter.Tendsto weighted (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [weighted, μ, μS, μR, R, n] using
      polar_product_sphere_radius_derivative_eval_weighted_tail_tendsto_zero
        (H := H) (dw := dw) _hdw
  have hC_ne_top : C ≠ ⊤ := by
    have hbase_ne_zero :
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ≠ 0 := by
      exact ne_of_gt
        (ENNReal.ofReal_pos.mpr
          (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))
    exact ENNReal.inv_ne_top.2 hbase_ne_zero
  have hscaled_tendsto :
      Filter.Tendsto (fun ε : ℝ ↦ C * weighted ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa using ENNReal.Tendsto.const_mul hweighted_tendsto (Or.inr hC_ne_top)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 2 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hbound :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (∫⁻ θ : Metric.sphere (0 : H) 1,
          ∫⁻ t in {t : ℝ | (1 : ℝ) - ε < t ∧ t < 1},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂(MeasureTheory.volume : Measure ℝ)
          ∂μS) ≤ C * weighted ε := by
    filter_upwards [hsmall] with ε hε_lt_half
    have hε_le_half : ε ≤ (1 / 2 : ℝ) := le_of_lt hε_lt_half
    let K : Set (Set.Ioi (0 : ℝ)) :=
      {r : Set.Ioi (0 : ℝ) |
        (1 : ℝ) - ε < (r : ℝ) ∧ (r : ℝ) < 1}
    let S : Set ℝ := {t : ℝ | (1 : ℝ) - ε < t ∧ t < 1}
    have hK_subset_R : K ⊆ R := by
      intro r hr
      exact hr.2
    have hweighted_iter :
        weighted ε =
          ∫⁻ θ : Metric.sphere (0 : H) 1,
            ∫⁻ r in K,
              ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
              ∂μR
            ∂μS := by
      have hset :
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} =
            Set.univ ×ˢ K := by
        ext p
        simp [K]
      have hF_mem :
          MemLp
            (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
              dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H))
            2 μ := by
        simpa [μ, μS, μR, R, n] using
          polar_product_sphere_radius_derivative_eval_memLp_two_of_memLp_two_unitBall
            (H := H) (dw := dw) _hdw
      have hF_aemeas :
          AEMeasurable
            (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
              ENNReal.ofReal ‖dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)‖)
            ((μS.prod (μR.restrict R)).restrict (Set.univ ×ˢ K)) := by
        have hraw :
            AEMeasurable
              (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
                ENNReal.ofReal ‖dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)‖)
              μ :=
          hF_mem.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
        simpa [μ] using hraw.mono_measure Measure.restrict_le_self
      have hprod :=
        MeasureTheory.setLIntegral_prod
          (μ := μS) (ν := μR.restrict R)
          (s := Set.univ) (t := K)
          (f := fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
            ENNReal.ofReal ‖dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)‖)
          hF_aemeas
      have hinner :
          (fun θ : Metric.sphere (0 : H) 1 ↦
            ∫⁻ r in K,
              ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
              ∂(μR.restrict R)) =
          (fun θ : Metric.sphere (0 : H) 1 ↦
            ∫⁻ r in K,
              ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
              ∂μR) := by
        funext θ
        change
          (∫⁻ r, ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
              ∂((μR.restrict R).restrict K)) =
            (∫⁻ r, ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
              ∂(μR.restrict K))
        rw [Measure.restrict_restrict_of_subset hK_subset_R]
      calc
        weighted ε =
            ∫⁻ p in Set.univ ×ˢ K,
              ENNReal.ofReal ‖dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)‖
              ∂(μS.prod (μR.restrict R)) := by
          change
            (∫⁻ p in
              {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
                (1 : ℝ) - ε < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1},
              ENNReal.ofReal ‖dw ((p.2 : ℝ) • (p.1 : H)) (p.1 : H)‖
              ∂μ) = _
          rw [hset]
        _ =
            ∫⁻ θ in (Set.univ : Set (Metric.sphere (0 : H) 1)),
              ∫⁻ r in K,
                ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
                ∂(μR.restrict R)
              ∂μS := hprod
        _ =
            ∫⁻ θ : Metric.sphere (0 : H) 1,
              ∫⁻ r in K,
                ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
                ∂μR
              ∂μS := by
          rw [setLIntegral_univ]
          exact lintegral_congr fun θ ↦ congrFun hinner θ
    have hpoint :
        ∀ θ : Metric.sphere (0 : H) 1,
          (∫⁻ t in S,
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂(MeasureTheory.volume : Measure ℝ)) ≤
            C *
              ∫⁻ r in K,
                ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
                ∂μR := by
      intro θ
      let Fθ : Set.Ioi (0 : ℝ) → ℝ≥0∞ :=
        fun r ↦ ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
      have himage :
          ((↑) : Set.Ioi (0 : ℝ) → ℝ) '' K = S := by
        ext t
        constructor
        · rintro ⟨r, hr, rfl⟩
          simpa [S, K] using hr
        · intro ht
          have ht_pos : 0 < t := by
            have hhalf_lt : (1 / 2 : ℝ) < t := by
              linarith [ht.1, hε_le_half]
            linarith
          exact ⟨⟨t, ht_pos⟩, by simpa [K, S] using ht, rfl⟩
      have hsubtype :
          (∫⁻ r in K, Fθ r
              ∂(Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
                (MeasureTheory.volume : Measure ℝ))) =
            ∫⁻ t in S,
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂(MeasureTheory.volume : Measure ℝ) := by
        rw [MeasureTheory.setLIntegral_subtype
          (μ := (MeasureTheory.volume : Measure ℝ))
          measurableSet_Ioi K
          (fun t : ℝ ↦
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖),
          himage]
      have hradial :=
        radial_comap_volume_setLIntegral_inner_collar_le_volumeIoiPow
          n hε_le_half Fθ
      calc
        ∫⁻ t in S,
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂(MeasureTheory.volume : Measure ℝ) =
          ∫⁻ r in K, Fθ r
              ∂(Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
                (MeasureTheory.volume : Measure ℝ)) := hsubtype.symm
        _ ≤ C *
            ∫⁻ r in K,
              ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
              ∂μR := by
          simpa [Fθ, C, μR, K, n] using hradial
    calc
      (∫⁻ θ : Metric.sphere (0 : H) 1,
          ∫⁻ t in {t : ℝ | (1 : ℝ) - ε < t ∧ t < 1},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂(MeasureTheory.volume : Measure ℝ)
          ∂μS) =
          ∫⁻ θ : Metric.sphere (0 : H) 1,
            ∫⁻ t in S,
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂(MeasureTheory.volume : Measure ℝ)
            ∂μS := rfl
      _ ≤
          ∫⁻ θ : Metric.sphere (0 : H) 1,
            C *
              ∫⁻ r in K,
                ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
                ∂μR
            ∂μS := lintegral_mono hpoint
      _ ≤
          C *
            ∫⁻ θ : Metric.sphere (0 : H) 1,
              ∫⁻ r in K,
                ENNReal.ofReal ‖dw ((r : ℝ) • (θ : H)) (θ : H)‖
                ∂μR
              ∂μS := by
          rw [lintegral_const_mul' C _ hC_ne_top]
      _ = C * weighted ε := by rw [hweighted_iter]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hscaled_tendsto
      (Filter.Eventually.of_forall fun _ε ↦ zero_le)
      hbound

/--
%%handwave
name:
  Almost every radius has an integrable spherical slice
statement:
  If a scalar function is square-integrable on the Euclidean unit ball, then
  for almost every radius \(0<r<1\) its restriction
  \(\theta\mapsto w(r\theta)\) to the sphere is \(L^1\)-integrable.
proof:
  Apply polar coordinates to the square-integrable function.  Fubini gives
  square-integrability of the spherical slice for almost every radius.  The
  sphere has finite measure, so each such \(L^2\) slice is also in \(L^1\).
-/
private theorem ae_radius_sphere_slice_memLp_one_of_memLp_two_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∀ᵐ r : Set.Ioi (0 : ℝ)
        ∂((MeasureTheory.Measure.volumeIoiPow
          (Module.finrank ℝ H - 1)).restrict
            {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
      MemLp
        (fun θ : Metric.sphere (0 : H) 1 ↦
          w ((r : ℝ) • (θ : H)))
        1 ((MeasureTheory.volume : Measure H).toSphere) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  let νR : Measure (Set.Ioi (0 : ℝ)) := μR.restrict R
  let F : Set.Ioi (0 : ℝ) × Metric.sphere (0 : H) 1 → ℝ :=
    fun p ↦ w ((p.1 : ℝ) • (p.2 : H))
  have hpolar :
      MemLp
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          w ((p.2 : ℝ) • (p.1 : H)))
        2 (μS.prod νR) := by
    simpa [μS, μR, R, νR] using
      polar_product_sphere_radius_memLp_two_of_memLp_two_unitBall
        (H := H) (w := w) _hw
  have hF_mem : MemLp F 2 (νR.prod μS) := by
    have hswap :
        MeasurePreserving Prod.swap (νR.prod μS) (μS.prod νR) :=
      Measure.measurePreserving_swap (μ := νR) (ν := μS)
    simpa [F, Function.comp_def] using
      hpolar.comp_measurePreserving hswap
  have hF_sq_int :
      Integrable (fun p : Set.Ioi (0 : ℝ) × Metric.sphere (0 : H) 1 ↦
        F p ^ 2) (νR.prod μS) :=
    hF_mem.integrable_sq
  have hF_sq_slices :
      ∀ᵐ r ∂νR,
        Integrable
          (fun θ : Metric.sphere (0 : H) 1 ↦ F (r, θ) ^ 2) μS :=
    ((MeasureTheory.integrable_prod_iff hF_sq_int.aestronglyMeasurable).mp
      hF_sq_int).1
  have hF_meas_slices :
      ∀ᵐ r ∂νR,
        AEStronglyMeasurable
          (fun θ : Metric.sphere (0 : H) 1 ↦ F (r, θ)) μS :=
    hF_mem.aestronglyMeasurable.prodMk_left
  filter_upwards [hF_sq_slices, hF_meas_slices] with r hsq hmeas
  have hmem2 :
      MemLp
        (fun θ : Metric.sphere (0 : H) 1 ↦
          w ((r : ℝ) • (θ : H))) 2 μS := by
    simpa [F] using (memLp_two_iff_integrable_sq hmeas).2 hsq
  simpa [μS] using
    hmem2.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/--
%%handwave
name:
  Good radii approaching the sphere
statement:
  Suppose two representatives agree almost everywhere on the unit ball and
  the original function is square-integrable there.  Then one can choose
  radii \(s_n\uparrow1\) such that, on each chosen sphere, the two
  representatives agree almost everywhere and the original spherical slice is
  \(L^1\)-integrable.
proof:
  Use polar coordinates and Fubini.  The representative equality holds for
  almost every radius, and square-integrability gives \(L^1\)-integrability of
  the spherical slice for almost every radius.  Intersect these full-measure
  sets and choose a sequence from the resulting dense set tending to one.
-/
private theorem exists_seq_tendsto_one_sphere_slice_eq_memLp_of_ae_volume_unitBall
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {f g : H → ℝ}
    (hg : MemLp g 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hfg : f =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] g) :
    ∃ s : ℕ → Set.Ioi (0 : ℝ),
      (∀ k : ℕ,
        ((s k : Set.Ioi (0 : ℝ)) : ℝ) < 1 ∧
          (∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere),
            f (((s k : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
              g (((s k : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))) ∧
          MemLp
            (fun θ : Metric.sphere (0 : H) 1 ↦
              g (((s k : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
            1 ((MeasureTheory.volume : Measure H).toSphere)) ∧
        Filter.Tendsto (fun k : ℕ ↦ ((s k : Set.Ioi (0 : ℝ)) : ℝ))
          Filter.atTop (𝓝 (1 : ℝ)) := by
  classical
  let P : Set.Ioi (0 : ℝ) → Prop :=
    fun r ↦
      (∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        f ((r : ℝ) • (θ : H)) = g ((r : ℝ) • (θ : H))) ∧
      MemLp
        (fun θ : Metric.sphere (0 : H) 1 ↦
          g ((r : ℝ) • (θ : H)))
        1 ((MeasureTheory.volume : Measure H).toSphere)
  have hP_eq :
      ∀ᵐ r : Set.Ioi (0 : ℝ)
          ∂((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          f ((r : ℝ) • (θ : H)) = g ((r : ℝ) • (θ : H)) :=
    ae_radius_sphere_slice_eq_of_ae_volume_unitBall (H := H) hfg
  have hP_mem :
      ∀ᵐ r : Set.Ioi (0 : ℝ)
          ∂((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
        MemLp
          (fun θ : Metric.sphere (0 : H) 1 ↦
            g ((r : ℝ) • (θ : H)))
          1 ((MeasureTheory.volume : Measure H).toSphere) :=
    ae_radius_sphere_slice_memLp_one_of_memLp_two_unitBall (H := H) hg
  have hP : ∀ᵐ r
      ∂((MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ H - 1)).restrict
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
      P r := by
    filter_upwards [hP_eq, hP_mem] with r hr_eq hr_mem
    exact ⟨hr_eq, hr_mem⟩
  rcases
    exists_seq_tendsto_one_of_ae_volumeIoiPow_restrict
      (n := Module.finrank ℝ H - 1) (P := P) hP with
    ⟨s, hs, hs_tendsto⟩
  refine ⟨s, ?_, hs_tendsto⟩
  intro k
  simpa [P] using hs k

/--
%%handwave
name:
  Transferring radial segment bounds from a representative to the original function
statement:
  Let \(w_{\mathrm{ac}}=w\) almost everywhere in the unit ball.  Suppose \(w_{\mathrm{ac}}\) satisfies the radial segment estimate up to every \(s\in(0,1)\).  For radii \(s_k<1\) where \(w_{\mathrm{ac}}(s_k\theta)=w(s_k\theta)\) almost everywhere on the sphere, the same segment estimate with both endpoints evaluated using \(w\) holds for product-almost every \((\theta,r)\) with \(r<s_k\).
proof:
  Polar coordinates transfer the interior almost-everywhere equality \(w_{\mathrm{ac}}=w\) to product-almost every \((\theta,r)\).  Combine this with the assumed segment estimate and the endpoint equality at \(s_k\), then replace both function values.
-/
private theorem radial_acl_segments_for_original_of_representative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w wacl : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hwacl_eq : wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w)
    (hsegments :
      ∀ s : ℝ, 0 < s → s < 1 →
        ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s →
            ENNReal.ofReal
              ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
                wacl (s • (p.1 : H))‖ ≤
              ∫⁻ t in
                {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume)
    {s : ℕ → Set.Ioi (0 : ℝ)}
    (hs_lt : ∀ n : ℕ, ((s n : Set.Ioi (0 : ℝ)) : ℝ) < 1)
    (hs_endpoint :
      ∀ n : ℕ,
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))) :
    ∀ n : ℕ,
      ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
          ((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
        ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) <
            ((s n : Set.Ioi (0 : ℝ)) : ℝ) →
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) -
              w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ ≤
            ∫⁻ t in
              {t : ℝ |
                ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
                  t < ((s n : Set.Ioi (0 : ℝ)) : ℝ)},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  let ν : Measure (Set.Ioi (0 : ℝ)) := μR.restrict R
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod ν
  have hbase :
      ∀ᵐ p ∂μ,
        wacl ((p.2 : ℝ) • (p.1 : H)) =
          w ((p.2 : ℝ) • (p.1 : H)) := by
    simpa [μ, μS, μR, R, ν, Filter.EventuallyEq] using
      ae_polar_product_unitBall_of_ae_volume_unitBall
        (H := H) (P := fun z : H ↦ wacl z = w z) hwacl_eq
  intro n
  have hend :
      ∀ᵐ p ∂μ,
        wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
          w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) := by
    have hmap :
        ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂Measure.map Prod.fst μ,
          wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) := by
      have hsmul :
          ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂((ν Set.univ) • μS),
            wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
              w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) :=
        Measure.ae_smul_measure (hs_endpoint n) (ν Set.univ)
      simpa [μ, μS, μR, R, ν] using hsmul
    simpa [μ, μS, μR, R, ν] using
      (MeasureTheory.ae_of_ae_map
        (μ := μ) (f := Prod.fst) measurable_fst.aemeasurable hmap)
  have hseg :
      ∀ᵐ p ∂μ,
        ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) <
            ((s n : Set.Ioi (0 : ℝ)) : ℝ) →
          ENNReal.ofReal
            ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
              wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ ≤
            ∫⁻ t in
              {t : ℝ |
                ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
                  t < ((s n : Set.Ioi (0 : ℝ)) : ℝ)},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
    simpa [μ, μS, μR, R, ν] using
      hsegments (((s n : Set.Ioi (0 : ℝ)) : ℝ)) (s n).2 (hs_lt n)
  filter_upwards [hbase, hend, hseg] with p hp_base hp_end hp_seg hpr
  have hnorm :
      ‖w ((p.2 : ℝ) • (p.1 : H)) -
          w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ =
        ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
          wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ := by
    rw [← hp_base, ← hp_end]
  simpa [hnorm] using hp_seg hpr

/--
%%handwave
name:
  Transferring all radial segment bounds to selected original slices
statement:
  Let \(w_{\mathrm{ac}}=w\) almost everywhere in the unit ball and assume that, for almost every \(\theta\), every \(0<r<s<1\) satisfies the radial segment estimate for \(w_{\mathrm{ac}}\).  At any sequence of radii \(s_k<1\) where the two functions agree on almost every spherical slice, the corresponding estimate for \(w\) holds for product-almost every \((\theta,r)\) with \(r<s_k\).
proof:
  Specialize the all-segments hypothesis to each fixed \(s_k\), use Fubini to express it on the polar product, and apply the transfer from the representative to the original function.
-/
private theorem radial_acl_segments_for_original_of_representative_all_segments
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w wacl : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hwacl_eq : wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w)
    (hsegments :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        ∀ r s : ℝ, 0 < r → r < s → s < 1 →
          ENNReal.ofReal
            ‖wacl (r • (θ : H)) - wacl (s • (θ : H))‖ ≤
          ∫⁻ t in {t : ℝ | r < t ∧ t < s},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂MeasureTheory.volume)
    {s : ℕ → Set.Ioi (0 : ℝ)}
    (hs_lt : ∀ n : ℕ, ((s n : Set.Ioi (0 : ℝ)) : ℝ) < 1)
    (hs_endpoint :
      ∀ n : ℕ,
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))) :
    ∀ n : ℕ,
      ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
          ((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ H - 1)).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
        ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) <
            ((s n : Set.Ioi (0 : ℝ)) : ℝ) →
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) -
              w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ ≤
            ∫⁻ t in
              {t : ℝ |
                ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
                  t < ((s n : Set.Ioi (0 : ℝ)) : ℝ)},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  let ν : Measure (Set.Ioi (0 : ℝ)) := μR.restrict R
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod ν
  have hbase :
      ∀ᵐ p ∂μ,
        wacl ((p.2 : ℝ) • (p.1 : H)) =
          w ((p.2 : ℝ) • (p.1 : H)) := by
    simpa [μ, μS, μR, R, ν, Filter.EventuallyEq] using
      ae_polar_product_unitBall_of_ae_volume_unitBall
        (H := H) (P := fun z : H ↦ wacl z = w z) hwacl_eq
  intro n
  have hend :
      ∀ᵐ p ∂μ,
        wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
          w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) := by
    have hmap :
        ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂Measure.map Prod.fst μ,
          wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) := by
      have hsmul :
          ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂((ν Set.univ) • μS),
            wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
              w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) :=
        Measure.ae_smul_measure (hs_endpoint n) (ν Set.univ)
      simpa [μ, μS, μR, R, ν] using hsmul
    simpa [μ, μS, μR, R, ν] using
      (MeasureTheory.ae_of_ae_map
        (μ := μ) (f := Prod.fst) measurable_fst.aemeasurable hmap)
  have hseg :
      ∀ᵐ p ∂μ,
        ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) <
            ((s n : Set.Ioi (0 : ℝ)) : ℝ) →
          ENNReal.ofReal
            ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
              wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ ≤
            ∫⁻ t in
              {t : ℝ |
                ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
                  t < ((s n : Set.Ioi (0 : ℝ)) : ℝ)},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
    have hmap :
        ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂Measure.map Prod.fst μ,
          ∀ r s' : ℝ, 0 < r → r < s' → s' < 1 →
            ENNReal.ofReal
              ‖wacl (r • (θ : H)) - wacl (s' • (θ : H))‖ ≤
            ∫⁻ t in {t : ℝ | r < t ∧ t < s'},
              ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
              ∂MeasureTheory.volume := by
      have hsmul :
          ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂((ν Set.univ) • μS),
            ∀ r s' : ℝ, 0 < r → r < s' → s' < 1 →
              ENNReal.ofReal
                ‖wacl (r • (θ : H)) - wacl (s' • (θ : H))‖ ≤
              ∫⁻ t in {t : ℝ | r < t ∧ t < s'},
                ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                ∂MeasureTheory.volume :=
        Measure.ae_smul_measure hsegments (ν Set.univ)
      simpa [μ, μS, μR, R, ν] using hsmul
    filter_upwards
      [MeasureTheory.ae_of_ae_map
        (μ := μ) (f := Prod.fst) measurable_fst.aemeasurable hmap]
      with p hp hpr
    exact hp ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)
      (((s n : Set.Ioi (0 : ℝ)) : ℝ)) (p.2).2 hpr (hs_lt n)
  filter_upwards [hbase, hend, hseg] with p hp_base hp_end hp_seg hpr
  have hnorm :
      ‖w ((p.2 : ℝ) • (p.1 : H)) -
          w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ =
        ‖wacl ((p.2 : ℝ) • (p.1 : H)) -
          wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ := by
    rw [← hp_base, ← hp_end]
  simpa [hnorm] using hp_seg hpr

/--
%%handwave
name:
  \(L^1\) distance between spherical slices is bounded by radial variation
statement:
  Let \(0<a<b<1\).  Suppose an absolutely continuous representative obeys the radial segment bound and agrees almost everywhere with \(w\) on the spheres of radii \(a\) and \(b\).  If both slices are in \(L^1\), then their extended \(L^1\)-distance is at most
  \[
    \int_{\mathbb S}^{-}\int_{a<t<b}^{-}
      \operatorname{ofReal}(\|dw(t\theta)(\theta)\|)\,dt\,d\theta.
  \]
proof:
  The \(L^1\)-distance is the integral of the pointwise distance between the two slices.  Replace the endpoint values by the absolutely continuous representative, apply the radial segment bound almost everywhere, and use monotonicity of the outer integral.
-/
private theorem euclideanSobolev_unit_ball_radial_l1_slice_edist_le_segmentIntegral
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w wacl : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hsegments :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        ∀ r s : ℝ, 0 < r → r < s → s < 1 →
          ENNReal.ofReal
            ‖wacl (r • (θ : H)) - wacl (s • (θ : H))‖ ≤
          ∫⁻ t in {t : ℝ | r < t ∧ t < s},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂MeasureTheory.volume)
    {a b : Set.Ioi (0 : ℝ)}
    (hb_lt : ((b : Set.Ioi (0 : ℝ)) : ℝ) < 1)
    (hab : ((a : Set.Ioi (0 : ℝ)) : ℝ) < ((b : Set.Ioi (0 : ℝ)) : ℝ))
    (ha_endpoint :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        wacl (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
          w (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
    (hb_endpoint :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        wacl (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
          w (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
    (hmem_a :
      MemLp
        (fun θ : Metric.sphere (0 : H) 1 ↦
          w (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
        1 ((MeasureTheory.volume : Measure H).toSphere))
    (hmem_b :
      MemLp
        (fun θ : Metric.sphere (0 : H) 1 ↦
          w (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
        1 ((MeasureTheory.volume : Measure H).toSphere)) :
    edist
      (hmem_a.toLp
        (fun θ : Metric.sphere (0 : H) 1 ↦
          w (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))))
      (hmem_b.toLp
        (fun θ : Metric.sphere (0 : H) 1 ↦
          w (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))) ≤
      ∫⁻ θ : Metric.sphere (0 : H) 1,
        ∫⁻ t in
          {t : ℝ |
            ((a : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
              t < ((b : Set.Ioi (0 : ℝ)) : ℝ)},
          ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
          ∂MeasureTheory.volume
        ∂((MeasureTheory.volume : Measure H).toSphere) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let fa : Metric.sphere (0 : H) 1 → ℝ :=
    fun θ ↦ w (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))
  let fb : Metric.sphere (0 : H) 1 → ℝ :=
    fun θ ↦ w (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))
  have hpoint :
      ∀ᵐ θ : Metric.sphere (0 : H) 1 ∂μS,
        ‖fa θ - fb θ‖ₑ ≤
          ∫⁻ t in
            {t : ℝ |
              ((a : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
                t < ((b : Set.Ioi (0 : ℝ)) : ℝ)},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂MeasureTheory.volume := by
    filter_upwards [hsegments, ha_endpoint, hb_endpoint] with θ hseg haeq hbeq
    have hnorm :
        ‖fa θ - fb θ‖ =
          ‖wacl (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) -
            wacl (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))‖ := by
      dsimp [fa, fb]
      rw [← haeq, ← hbeq]
    have hseg_ab :=
      hseg ((a : Set.Ioi (0 : ℝ)) : ℝ)
        ((b : Set.Ioi (0 : ℝ)) : ℝ) a.2 hab hb_lt
    calc
      ‖fa θ - fb θ‖ₑ =
          ENNReal.ofReal ‖fa θ - fb θ‖ := by
            rw [ofReal_norm]
      _ = ENNReal.ofReal
          ‖wacl (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) -
            wacl (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))‖ := by
            rw [hnorm]
      _ ≤
          ∫⁻ t in
            {t : ℝ |
              ((a : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
                t < ((b : Set.Ioi (0 : ℝ)) : ℝ)},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂MeasureTheory.volume := hseg_ab
  calc
    edist
        (hmem_a.toLp
          (fun θ : Metric.sphere (0 : H) 1 ↦
            w (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))))
        (hmem_b.toLp
          (fun θ : Metric.sphere (0 : H) 1 ↦
            w (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))))
        = eLpNorm (fa - fb) 1 μS := by
          simpa [fa, fb, μS] using
            (Lp.edist_toLp_toLp
              (fun θ : Metric.sphere (0 : H) 1 ↦
                w (((a : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
              (fun θ : Metric.sphere (0 : H) 1 ↦
                w (((b : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
              hmem_a hmem_b)
    _ = ∫⁻ θ : Metric.sphere (0 : H) 1, ‖fa θ - fb θ‖ₑ ∂μS := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          rfl
    _ ≤ ∫⁻ θ : Metric.sphere (0 : H) 1,
        ∫⁻ t in
          {t : ℝ |
            ((a : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
              t < ((b : Set.Ioi (0 : ℝ)) : ℝ)},
          ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
          ∂MeasureTheory.volume
        ∂μS := lintegral_mono_ae hpoint
    _ =
      ∫⁻ θ : Metric.sphere (0 : H) 1,
        ∫⁻ t in
          {t : ℝ |
            ((a : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
              t < ((b : Set.Ioi (0 : ℝ)) : ℝ)},
          ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
          ∂MeasureTheory.volume
        ∂((MeasureTheory.volume : Measure H).toSphere) := by
          rfl

/--
%%handwave
name:
  Good endpoint sequences have \(L^1\)-Cauchy spherical slices
statement:
  Let \(s_n\uparrow1\) be radii such that \(0<s_n<1\), the radial ACL
  representative agrees with the original Sobolev function on almost every
  point of each sphere of radius \(s_n\), and the selected spherical slices
  \(\theta\mapsto w(s_n\theta)\) are \(L^1\)-integrable.  Then these slices
  form a Cauchy sequence in \(L^1\).
proof:
  Apply the radial ACL segment inequality between \(s_m\theta\) and
  \(s_n\theta\), integrate over the sphere, and use polar coordinates.  The
  resulting bound is controlled by the \(L^2\)-mass of the weak derivative in
  the collar between the two radii, which tends to zero as both radii tend to
  one.
-/
private theorem
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_endpoint_sequence_memLp_cauchy
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w wacl : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hwacl_eq : wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w)
    (hsegments :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        ∀ r s : ℝ, 0 < r → r < s → s < 1 →
          ENNReal.ofReal
            ‖wacl (r • (θ : H)) - wacl (s • (θ : H))‖ ≤
          ∫⁻ t in {t : ℝ | r < t ∧ t < s},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂MeasureTheory.volume)
    {s : ℕ → Set.Ioi (0 : ℝ)}
    (hs_lt : ∀ n : ℕ, ((s n : Set.Ioi (0 : ℝ)) : ℝ) < 1)
    (hs_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ ((s n : Set.Ioi (0 : ℝ)) : ℝ))
        Filter.atTop (𝓝 (1 : ℝ)))
    (hs_endpoint :
      ∀ n : ℕ,
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
    (hmem :
      ∀ n : ℕ,
        MemLp
          (fun θ : Metric.sphere (0 : H) 1 ↦
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
          1 ((MeasureTheory.volume : Measure H).toSphere)) :
    CauchySeq
      (fun n : ℕ ↦
        (hmem n).toLp
          (fun θ : Metric.sphere (0 : H) 1 ↦
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let u : ℕ → Lp ℝ 1 μS :=
    fun n : ℕ ↦
      (hmem n).toLp
        (fun θ : Metric.sphere (0 : H) 1 ↦
          w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
  let tail : ℝ → ℝ≥0∞ :=
    fun ε : ℝ ↦
      ∫⁻ θ : Metric.sphere (0 : H) 1,
        ∫⁻ t in {t : ℝ | (1 : ℝ) - ε < t ∧ t < 1},
          ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
          ∂(MeasureTheory.volume : Measure ℝ)
        ∂μS
  have htail_tendsto :
      Filter.Tendsto tail (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [tail, μS] using
      polar_sphere_unweighted_radial_derivative_tail_tendsto_zero
        (H := H) (dw := dw) hdw
  have hcauchy_u : CauchySeq u := by
    refine EMetric.cauchySeq_iff.2 ?_
    intro η hη
    have htail_small : ∀ᶠ ε in 𝓝[>] (0 : ℝ), tail ε < η :=
      htail_tendsto.eventually (Iio_mem_nhds hη)
    have hε_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε :=
      self_mem_nhdsWithin
    have hε_half : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 2 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    rcases (hε_pos.and (hε_half.and htail_small)).exists with
      ⟨δ, hδ_pos, hδ_half_tail⟩
    rcases hδ_half_tail with ⟨hδ_lt_half, hδ_tail⟩
    have hnear : ∀ᶠ k in Filter.atTop,
        (1 : ℝ) - δ < ((s k : Set.Ioi (0 : ℝ)) : ℝ) := by
      exact hs_tendsto (Ioi_mem_nhds (by linarith))
    rcases Filter.eventually_atTop.1 hnear with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hm_lower : (1 : ℝ) - δ < ((s m : Set.Ioi (0 : ℝ)) : ℝ) :=
      hN m hm
    have hn_lower : (1 : ℝ) - δ < ((s n : Set.Ioi (0 : ℝ)) : ℝ) :=
      hN n hn
    by_cases hmn_eq :
        ((s m : Set.Ioi (0 : ℝ)) : ℝ) =
          ((s n : Set.Ioi (0 : ℝ)) : ℝ)
    · have hfun :
          (fun θ : Metric.sphere (0 : H) 1 ↦
            w (((s m : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))) =ᵐ[μS]
          (fun θ : Metric.sphere (0 : H) 1 ↦
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))) := by
        filter_upwards [] with θ
        rw [hmn_eq]
      have hu_eq : u m = u n := by
        simpa [u, μS] using
          MemLp.toLp_congr (hmem m) (hmem n) hfun
      rw [hu_eq]
      simpa using hη
    · have hmn_or :
          ((s m : Set.Ioi (0 : ℝ)) : ℝ) <
              ((s n : Set.Ioi (0 : ℝ)) : ℝ) ∨
            ((s n : Set.Ioi (0 : ℝ)) : ℝ) <
              ((s m : Set.Ioi (0 : ℝ)) : ℝ) :=
        lt_or_gt_of_ne hmn_eq
      rcases hmn_or with hmn_lt | hnm_lt
      · let A : Set ℝ :=
          {t : ℝ |
            ((s m : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
              t < ((s n : Set.Ioi (0 : ℝ)) : ℝ)}
        let B : Set ℝ := {t : ℝ | (1 : ℝ) - δ < t ∧ t < 1}
        have hA_subset_B : A ⊆ B := by
          intro t ht
          exact ⟨lt_trans hm_lower ht.1, lt_trans ht.2 (hs_lt n)⟩
        have hed :
            edist (u m) (u n) ≤
              ∫⁻ θ : Metric.sphere (0 : H) 1,
                ∫⁻ t in A,
                  ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                  ∂(MeasureTheory.volume : Measure ℝ)
                ∂μS := by
          simpa [u, μS, A] using
            euclideanSobolev_unit_ball_radial_l1_slice_edist_le_segmentIntegral
              (H := H) (w := w) (wacl := wacl) (dw := dw)
              hsegments (a := s m) (b := s n) (hs_lt n) hmn_lt
              (hs_endpoint m) (hs_endpoint n) (hmem m) (hmem n)
        have hseg_tail :
            (∫⁻ θ : Metric.sphere (0 : H) 1,
                ∫⁻ t in A,
                  ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                  ∂(MeasureTheory.volume : Measure ℝ)
                ∂μS) ≤ tail δ := by
          dsimp [tail, B]
          apply lintegral_mono
          intro θ
          exact lintegral_mono_set hA_subset_B
        exact lt_of_le_of_lt (hed.trans hseg_tail) hδ_tail
      · let A : Set ℝ :=
          {t : ℝ |
            ((s n : Set.Ioi (0 : ℝ)) : ℝ) < t ∧
              t < ((s m : Set.Ioi (0 : ℝ)) : ℝ)}
        let B : Set ℝ := {t : ℝ | (1 : ℝ) - δ < t ∧ t < 1}
        have hA_subset_B : A ⊆ B := by
          intro t ht
          exact ⟨lt_trans hn_lower ht.1, lt_trans ht.2 (hs_lt m)⟩
        have hed :
            edist (u m) (u n) ≤
              ∫⁻ θ : Metric.sphere (0 : H) 1,
                ∫⁻ t in A,
                  ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                  ∂(MeasureTheory.volume : Measure ℝ)
                ∂μS := by
          rw [edist_comm]
          simpa [u, μS, A] using
            euclideanSobolev_unit_ball_radial_l1_slice_edist_le_segmentIntegral
              (H := H) (w := w) (wacl := wacl) (dw := dw)
              hsegments (a := s n) (b := s m) (hs_lt m) hnm_lt
              (hs_endpoint n) (hs_endpoint m) (hmem n) (hmem m)
        have hseg_tail :
            (∫⁻ θ : Metric.sphere (0 : H) 1,
                ∫⁻ t in A,
                  ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                  ∂(MeasureTheory.volume : Measure ℝ)
                ∂μS) ≤ tail δ := by
          dsimp [tail, B]
          apply lintegral_mono
          intro θ
          exact lintegral_mono_set hA_subset_B
        exact lt_of_le_of_lt (hed.trans hseg_tail) hδ_tail
  simpa [u, μS] using hcauchy_u

/--
%%handwave
name:
  Good endpoint radii with \(L^1\)-Cauchy spherical slices
statement:
  Let \(u\) be a scalar \(W^{1,2}\) function on the unit ball and let
  \(\widetilde u\) be a radial ACL representative agreeing with \(u\) almost
  everywhere.  There are radii \(s_n\uparrow1\), \(0<s_n<1\), such that
  \(\widetilde u(s_n\theta)=u(s_n\theta)\) for almost every direction on each
  chosen sphere, and the slices \(\theta\mapsto u(s_n\theta)\) are
  \(L^1\)-Cauchy on the unit sphere.
proof:
  The representative equality holds for almost every radius by polar Fubini.
  Select the radii from this full-measure set while also making the weak
  derivative energy in the outer collars tend to zero.  The radial ACL segment
  estimate integrated over pairs of selected radii, followed by polar
  coordinates and Cauchy--Schwarz, gives the \(L^1\)-Cauchy property.
-/
theorem
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_good_endpoint_radii_analytic_leaf
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w wacl : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hwacl_eq : wacl =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w)
    (_hsegments :
      ∀ᵐ θ : Metric.sphere (0 : H) 1
          ∂((MeasureTheory.volume : Measure H).toSphere),
        ∀ r s : ℝ, 0 < r → r < s → s < 1 →
          ENNReal.ofReal
            ‖wacl (r • (θ : H)) - wacl (s • (θ : H))‖ ≤
          ∫⁻ t in {t : ℝ | r < t ∧ t < s},
            ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
            ∂MeasureTheory.volume) :
    ∃ (s : ℕ → Set.Ioi (0 : ℝ))
        (hmem :
          ∀ n : ℕ,
            MemLp
              (fun θ : Metric.sphere (0 : H) 1 ↦
                w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
              1 ((MeasureTheory.volume : Measure H).toSphere)),
      (∀ n, ((s n : Set.Ioi (0 : ℝ)) : ℝ) < 1) ∧
        Filter.Tendsto
          (fun n : ℕ ↦ ((s n : Set.Ioi (0 : ℝ)) : ℝ))
          Filter.atTop (𝓝 (1 : ℝ)) ∧
        CauchySeq
          (fun n : ℕ ↦
            (hmem n).toLp
              (fun θ : Metric.sphere (0 : H) 1 ↦
                w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))) ∧
        (∀ n : ℕ,
          ∀ᵐ θ : Metric.sphere (0 : H) 1
              ∂((MeasureTheory.volume : Measure H).toSphere),
            wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
              w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H))) := by
  classical
  rcases
    exists_seq_tendsto_one_sphere_slice_eq_memLp_of_ae_volume_unitBall
      (H := H) (f := wacl) (g := w) _hw _hwacl_eq with
    ⟨s, hs_good, hs_tendsto⟩
  have hs_lt : ∀ n : ℕ, ((s n : Set.Ioi (0 : ℝ)) : ℝ) < 1 :=
    fun n ↦ (hs_good n).1
  have hs_endpoint :
      ∀ n : ℕ,
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          wacl (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) =
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)) :=
    fun n ↦ (hs_good n).2.1
  have hmem :
      ∀ n : ℕ,
        MemLp
          (fun θ : Metric.sphere (0 : H) 1 ↦
            w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))
          1 ((MeasureTheory.volume : Measure H).toSphere) :=
    fun n ↦ (hs_good n).2.2
  have hcauchy :
      CauchySeq
        (fun n : ℕ ↦
          (hmem n).toLp
            (fun θ : Metric.sphere (0 : H) 1 ↦
              w (((s n : Set.Ioi (0 : ℝ)) : ℝ) • (θ : H)))) :=
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_endpoint_sequence_memLp_cauchy
      (H := H) (w := w) (wacl := wacl) (dw := dw)
      _hw _hdw _hwacl_eq _hsegments hs_lt hs_tendsto hs_endpoint hmem
  exact ⟨s, hmem, hs_lt, hs_tendsto, hcauchy, hs_endpoint⟩

/--
%%handwave
name:
  \(L^1\)-Cauchy radial slices near the unit sphere
statement:
  For a scalar \(W^{1,2}\) function on the unit ball, one can choose radii
  \(s_n\uparrow1\), \(0<s_n<1\), such that the spherical slices
  \(\theta\mapsto u(s_n\theta)\) are \(L^1\)-Cauchy on the unit sphere, and
  the finite radial segment estimate from \(r\theta\) to \(s_n\theta\) holds
  for almost every polar pair.
proof:
  Choose the radial ACL representative and discard the exceptional polar set.
  Fubini gives a full-measure set of endpoint radii on which the chosen
  representative agrees with the original function on almost every sphere
  point.  Select \(s_n\) from this set with \(s_n\to1\).  For \(m,n\) large,
  integrate the one-dimensional radial segment estimate between
  \(s_m\theta\) and \(s_n\theta\) over the sphere.  Polar coordinates and
  Cauchy--Schwarz bound the result by the \(L^2\)-mass of the weak derivative
  in the thin collar between the two radii, which tends to zero.
-/
theorem
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_sphere_cauchySequence_data_analytic_leaf
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ (s : ℕ → ℝ)
        (hmem :
          ∀ n : ℕ,
            MemLp
              (fun θ : Metric.sphere (0 : H) 1 ↦ w ((s n) • (θ : H)))
              1 ((MeasureTheory.volume : Measure H).toSphere)),
      (∀ n, 0 < s n ∧ s n < 1) ∧
        Filter.Tendsto s Filter.atTop (𝓝 (1 : ℝ)) ∧
        CauchySeq
          (fun n : ℕ ↦
            (hmem n).toLp
              (fun θ : Metric.sphere (0 : H) 1 ↦
                w ((s n) • (θ : H)))) ∧
        (∀ n : ℕ,
          ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
            ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s n →
              ENNReal.ofReal
                ‖w ((p.2 : ℝ) • (p.1 : H)) -
                  w ((s n) • (p.1 : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s n},
                  ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                  ∂MeasureTheory.volume) := by
  classical
  rcases
    scalarWeakSobolev_unit_ball_radial_acl_all_segments_ae_sphere
      _hweak _hw _hdw with
    ⟨wacl, hwacl_eq, hsegments_acl⟩
  rcases
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_good_endpoint_radii_analytic_leaf
      (w := w) (wacl := wacl) (dw := dw) _hw _hdw hwacl_eq hsegments_acl with
    ⟨s, hmem, hs_lt, hs_tendsto, hcauchy, hs_endpoint⟩
  let sℝ : ℕ → ℝ := fun n : ℕ ↦ ((s n : Set.Ioi (0 : ℝ)) : ℝ)
  have hsegments_w :
      ∀ n : ℕ,
        ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < sℝ n →
            ENNReal.ofReal
              ‖w ((p.2 : ℝ) • (p.1 : H)) -
                w (sℝ n • (p.1 : H))‖ ≤
              ∫⁻ t in
                {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < sℝ n},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume := by
    simpa [sℝ] using
      radial_acl_segments_for_original_of_representative_all_segments
        (H := H) (w := w) (wacl := wacl) (dw := dw)
        hwacl_eq hsegments_acl hs_lt hs_endpoint
  refine ⟨sℝ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa [sℝ] using hmem n
  · intro n
    exact ⟨(s n).2, hs_lt n⟩
  · simpa [sℝ] using hs_tendsto
  · simpa [sℝ] using hcauchy
  · simpa [sℝ] using hsegments_w

/--
%%handwave
name:
  Radial \(L^1\)-Cauchy slices give convergence in measure on the sphere
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball admits a
  measurable boundary function \(\tau\) and radii \(s_n\to 1\), \(0<s_n<1\),
  such that \(w(s_n\theta)\) converges to \(\tau(\theta)\) in measure on the
  sphere, and the finite radial segment estimate from \(r\) to \(s_n\) holds
  almost everywhere in polar coordinates.
proof:
  First choose the radial ACL representative.  Fubini gives radii tending to
  \(1\) for which this representative agrees with \(w\) on almost every point
  of the corresponding sphere.  Along those radii the finite radial segment
  estimate may be written with the original representative.  Integrating these
  estimates in polar coordinates and applying Cauchy--Schwarz on thin collars
  shows that the boundary slices are Cauchy in \(L^1\), hence converge in
  measure to an \(L^1\)-limit \(\tau\) on the sphere.
-/
theorem euclideanSobolev_unit_ball_radial_l1_cauchy_trace_sphere_tendstoInMeasure_data_analytic_leaf
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ (τ : H → ℝ) (s : ℕ → ℝ),
      Measurable τ ∧
        (∀ n, 0 < s n ∧ s n < 1) ∧
        Filter.Tendsto s Filter.atTop (𝓝 (1 : ℝ)) ∧
        TendstoInMeasure ((MeasureTheory.volume : Measure H).toSphere)
          (fun n (θ : Metric.sphere (0 : H) 1) ↦ w ((s n) • (θ : H)))
          Filter.atTop
          (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H)) ∧
        (∀ n : ℕ,
          ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
            ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s n →
              ENNReal.ofReal
                ‖w ((p.2 : ℝ) • (p.1 : H)) -
                  w ((s n) • (p.1 : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s n},
                  ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                  ∂MeasureTheory.volume) := by
  classical
  rcases
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_sphere_cauchySequence_data_analytic_leaf
      _hweak _hw _hdw with
    ⟨s, hmem, hs_bounds, hs_tendsto, hcauchy, hsegments⟩
  rcases sphere_slices_tendstoInMeasure_of_L1_cauchy (w := w) s hmem hcauchy with
    ⟨τ, hτ_meas, hslices_tendsto⟩
  exact ⟨τ, s, hτ_meas, hs_bounds, hs_tendsto, hslices_tendsto, hsegments⟩

/--
%%handwave
name:
  Convergence in measure gives a radial endpoint subsequence
statement:
  From convergence in measure of the radial boundary slices on the sphere one
  can pass to radii \(s_{n_j}\to1\) along which \(w(s_{n_j}\theta)\) converges
  to the boundary function for almost every direction.  The finite radial
  segment estimates are preserved along the subsequence.
proof:
  Apply the standard subsequence theorem for convergence in measure to obtain
  almost-everywhere convergence on the sphere.  Since the selected indices tend
  to infinity, the corresponding radii still tend to \(1\), and all pointwise
  finite-segment estimates restrict to the chosen subsequence.
-/
private theorem
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_sphere_subsequence_data_analytic_leaf
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ (τ : H → ℝ) (s : ℕ → ℝ),
      Measurable τ ∧
        (∀ n, 0 < s n ∧ s n < 1) ∧
        Filter.Tendsto s Filter.atTop (𝓝 (1 : ℝ)) ∧
        Filter.Eventually
          (fun θ : Metric.sphere (0 : H) 1 ↦
            Filter.Tendsto
              (fun n : ℕ ↦ w ((s n) • (θ : H)))
              Filter.atTop (𝓝 (τ (θ : H))))
          (MeasureTheory.ae ((MeasureTheory.volume : Measure H).toSphere)) ∧
        (∀ n : ℕ,
          ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
            ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s n →
              ENNReal.ofReal
                ‖w ((p.2 : ℝ) • (p.1 : H)) -
                  w ((s n) • (p.1 : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s n},
                  ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                  ∂MeasureTheory.volume) := by
  classical
  rcases
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_sphere_tendstoInMeasure_data_analytic_leaf
      _hweak _hw _hdw with
    ⟨τ, s, hτ_meas, hs_bounds, hs_tendsto, hslices_measure, hsegments⟩
  rcases hslices_measure.exists_seq_tendsto_ae with
    ⟨ns, hns_strict, hslices_ae⟩
  refine ⟨τ, fun n : ℕ ↦ s (ns n), hτ_meas, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hs_bounds (ns n)
  · exact hs_tendsto.comp hns_strict.tendsto_atTop
  · filter_upwards [hslices_ae] with θ hθ
    simpa using hθ
  · intro n
    simpa using hsegments (ns n)

/--
%%handwave
name:
  Directional endpoint convergence lifts to polar-product convergence
statement:
  If the radial boundary slices converge almost everywhere on the sphere along
  radii \(s_n\to1\), and the finite segment estimates hold for those radii in
  polar coordinates, then the same data is valid almost everywhere for polar
  pairs.
proof:
  The convergence assertion depends only on the angular variable.  Push the
  polar-product measure forward by the first projection; it is a scalar
  multiple of spherical measure, so spherical almost-everywhere convergence
  pulls back to polar-product almost-everywhere convergence.  The finite
  segment estimates are already stated on the product.
-/
private theorem
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_subsequence_data_analytic_leaf
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ (τ : H → ℝ) (s : ℕ → ℝ),
      Measurable τ ∧
        (∀ n, 0 < s n ∧ s n < 1) ∧
        Filter.Tendsto s Filter.atTop (𝓝 (1 : ℝ)) ∧
        (∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          Filter.Tendsto
            (fun n : ℕ ↦ w ((s n) • (p.1 : H)))
            Filter.atTop (𝓝 (τ (p.1 : H)))) ∧
        (∀ n : ℕ,
          ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
            ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s n →
              ENNReal.ofReal
                ‖w ((p.2 : ℝ) • (p.1 : H)) -
                  w ((s n) • (p.1 : H))‖ ≤
                ∫⁻ t in
                  {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s n},
                  ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                  ∂MeasureTheory.volume) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  let ν : Measure (Set.Ioi (0 : ℝ)) := μR.restrict R
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod ν
  rcases
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_sphere_subsequence_data_analytic_leaf
      _hweak _hw _hdw with
    ⟨τ, s, hτ_meas, hs_bounds, hs_tendsto, hsphere_tendsto, hsegments⟩
  refine ⟨τ, s, hτ_meas, hs_bounds, hs_tendsto, ?_, ?_⟩
  · have hmap :
        Filter.Eventually
          (fun θ : Metric.sphere (0 : H) 1 ↦
            Filter.Tendsto
              (fun n : ℕ ↦ w ((s n) • (θ : H)))
              Filter.atTop (𝓝 (τ (θ : H))))
          (MeasureTheory.ae (Measure.map Prod.fst μ)) := by
      have hsmul :
          Filter.Eventually
            (fun θ : Metric.sphere (0 : H) 1 ↦
              Filter.Tendsto
                (fun n : ℕ ↦ w ((s n) • (θ : H)))
                Filter.atTop (𝓝 (τ (θ : H))))
            (MeasureTheory.ae ((ν Set.univ) • μS)) :=
        Measure.ae_smul_measure hsphere_tendsto (ν Set.univ)
      simpa [μ, μS, μR, R, ν] using hsmul
    simpa [μ, μS, μR, R, ν] using
      (MeasureTheory.ae_of_ae_map
        (μ := μ) (f := Prod.fst) measurable_fst.aemeasurable hmap)
  · simpa [μ, μS, μR, R, ν] using hsegments

/--
%%handwave
name:
  Radial \(L^1\)-Cauchy traces give endpoint bounds in polar coordinates
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every polar
  pair \((\theta,r)\) with \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
proof:
  For \(0<r<s<1\), apply the one-dimensional fundamental theorem of calculus
  on almost every radial segment and integrate over directions to obtain an
  \(L^1\)-estimate for \(w(s\theta)-w(r\theta)\).  Polar coordinates and
  Cauchy--Schwarz show that these radial slices are Cauchy in \(L^1\) as
  \(r,s \uparrow 1\).  Let \(\tau\) be the \(L^1\)-limit on the sphere.  Choose a
  sequence \(s_n \uparrow 1\) along which \(w(s_n\theta)\to\tau(\theta)\) for
  almost every direction, apply the finite-segment estimate for each \(s_n\),
  and pass to the limit to get the displayed tail bound.
-/
private theorem
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_polar_product_raw_analytic_leaf
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        (∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
              ((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
            ENNReal.ofReal
              ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
              ∫⁻ t in
                {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume) := by
  classical
  rcases
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_subsequence_data_analytic_leaf
      _hweak _hw _hdw with
    ⟨τ, s, hτ_meas, hs_bounds, hs_tendsto, hslices_tendsto, hsegments⟩
  refine ⟨τ, hτ_meas, ?_⟩
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}
  let μ : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod (μR.restrict R)
  have hR_meas : MeasurableSet R := by
    dsimp [R]
    measurability
  have hR_ae :
      Filter.Eventually (fun r : Set.Ioi (0 : ℝ) ↦ (r : ℝ) < 1)
        (MeasureTheory.ae (μR.restrict R)) := by
    simpa [R] using
      (MeasureTheory.self_mem_ae_restrict (μ := μR) hR_meas)
  have hprod_R : ∀ᵐ p ∂μ, ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < 1 := by
    have hpred_meas :
        MeasurableSet
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < 1} := by
      measurability
    exact (Measure.ae_prod_iff_ae_ae hpred_meas).2
      (Filter.Eventually.of_forall fun _ ↦ hR_ae)
  have hsegments_all :
      ∀ᵐ p ∂μ, ∀ n : ℕ,
        ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s n →
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) -
              w ((s n) • (p.1 : H))‖ ≤
            ∫⁻ t in
              {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s n},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
    simpa [μS, μR, R, μ] using (ae_all_iff.mpr hsegments)
  have hslices_tendsto' :
      ∀ᵐ p ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦ w ((s n) • (p.1 : H)))
          Filter.atTop (𝓝 (τ (p.1 : H))) := by
    simpa [μS, μR, R, μ] using hslices_tendsto
  filter_upwards [hslices_tendsto', hsegments_all, hprod_R] with p
    hp_tendsto hp_segments hpR
  let C : ℝ≥0∞ :=
    ∫⁻ t in
      {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
      ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
      ∂MeasureTheory.volume
  have hlt_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < s n := by
    exact hs_tendsto.eventually (Ioi_mem_nhds hpR)
  have hbound_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        ENNReal.ofReal
          ‖w ((p.2 : ℝ) • (p.1 : H)) -
            w ((s n) • (p.1 : H))‖ ≤ C := by
    filter_upwards [hlt_event] with n hn
    have hsubset :
        {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < s n} ⊆
          {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1} := by
      intro t ht
      exact ⟨ht.1, lt_trans ht.2 (hs_bounds n).2⟩
    exact (hp_segments n hn).trans (MeasureTheory.lintegral_mono_set hsubset)
  have hnorm_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          ‖w ((p.2 : ℝ) • (p.1 : H)) -
            w ((s n) • (p.1 : H))‖)
        Filter.atTop
        (𝓝 ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖) := by
    exact (tendsto_const_nhds.sub hp_tendsto).norm
  have henn_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) -
              w ((s n) • (p.1 : H))‖)
        Filter.atTop
        (𝓝 (ENNReal.ofReal
          ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖)) :=
    ENNReal.tendsto_ofReal hnorm_tendsto
  simpa [C] using (le_of_tendsto henn_tendsto hbound_event)

/--
%%handwave
name:
  Radial endpoint trace bound on the punctured unit ball
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  point \(0<\|x\|<1\),
  \[
    |w(x)-\tau(x/\|x\|)|
      \le
    \int_{\|x\|}^1
      |Dw(t x/\|x\|)(x/\|x\|)|\,dt .
  \]
proof:
  On almost every radial line the one-dimensional restriction of \(w\) has an
  absolutely continuous representative whose derivative is the radial
  directional derivative.  The endpoint limits at the unit sphere define
  \(\tau\), and the fundamental theorem of calculus on those lines gives the
  tail bound.
-/
private theorem
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_punctured_analytic_leaf
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ x ∂MeasureTheory.volume.restrict
            {x : H | 0 < ‖x‖ ∧ ‖x‖ < 1},
          ENNReal.ofReal
            ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖ ≤
            euclideanSobolevUnitBallRadialTailMajorant dw x := by
  classical
  let B : Set H := Metric.ball (0 : H) 1
  let P : Set H := {x : H | 0 < ‖x‖ ∧ ‖x‖ < 1}
  let e : ({0}ᶜ : Set H) ≃ₜ
      (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    homeomorphUnitSphereProd H
  let μNZ : Measure ({0}ᶜ : Set H) :=
    (MeasureTheory.volume : Measure H).comap
      ((↑) : ({0}ᶜ : Set H) → H)
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let ν : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod μR
  let S : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) < 1}
  let R : Set (Set.Ioi (0 : ℝ)) := {r | (r : ℝ) < 1}
  let T : Set ({0}ᶜ : Set H) := {x | ‖(x : H)‖ < 1}
  rcases
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_polar_product_raw_analytic_leaf
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hpolar_raw_prod⟩
  refine ⟨τ, hτ_meas, ?_⟩
  have hNZ_meas : MeasurableSet ({0}ᶜ : Set H) :=
    (measurableSet_singleton (0 : H)).compl
  have hS_eq : S = Set.univ ×ˢ R := by
    ext p
    simp [S, R]
  have hmeasure :
      ν.restrict S = μS.prod (μR.restrict R) := by
    rw [hS_eq]
    have hprod :=
      Measure.prod_restrict (μ := μS) (ν := μR) Set.univ R
    simpa [ν] using hprod.symm
  have hpolar_raw :
      ∀ᵐ p ∂ν.restrict S,
        ENNReal.ofReal
          ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            ∫⁻ t in
              {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
    simpa [ν, μS, μR, R, S, hmeasure] using hpolar_raw_prod
  have hpolar :
      ∀ᵐ p ∂ν.restrict S,
        ENNReal.ofReal
          ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
          euclideanSobolevUnitBallRadialTailMajorant dw
            ((p.2 : ℝ) • (p.1 : H)) := by
    filter_upwards [hpolar_raw] with p hp
    rw [euclideanSobolevUnitBallRadialTailMajorant_polar (dw := dw) p]
    exact hp
  have hmp : MeasurePreserving e μNZ ν := by
    simpa [e, μNZ, ν, μS, μR] using
      (MeasureTheory.volume : Measure H).measurePreserving_homeomorphUnitSphereProd
  have hmap_restrict :
      (μNZ.restrict (e ⁻¹' S)).map e = ν.restrict S := by
    have hrestrict := e.measurableEmbedding.restrict_map μNZ S
    rw [hmp.map_eq] at hrestrict
    exact hrestrict.symm
  have hpull_polar :
      ∀ᵐ x : ({0}ᶜ : Set H) ∂(μNZ.restrict (e ⁻¹' S)),
        ENNReal.ofReal
          ‖w (((e x).2 : ℝ) • ((e x).1 : H)) -
              τ ((e x).1 : H)‖ ≤
          euclideanSobolevUnitBallRadialTailMajorant dw
            (((e x).2 : ℝ) • ((e x).1 : H)) := by
    have hpolar' :
        ∀ᵐ p ∂(μNZ.restrict (e ⁻¹' S)).map e,
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            euclideanSobolevUnitBallRadialTailMajorant dw
              ((p.2 : ℝ) • (p.1 : H)) := by
      rw [hmap_restrict]
      simpa [ν, S] using hpolar
    exact MeasureTheory.ae_of_ae_map e.continuous.measurable.aemeasurable
      hpolar'
  have hpre :
      e ⁻¹' S = T := by
    ext x
    change (((homeomorphUnitSphereProd H) x).2 : ℝ) < 1 ↔
      ‖(x : H)‖ < 1
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  have hpull :
      ∀ᵐ x : ({0}ᶜ : Set H) ∂(μNZ.restrict T),
        ENNReal.ofReal
          ‖w (x : H) - τ (((1 / ‖(x : H)‖) : ℝ) • (x : H))‖ ≤
          euclideanSobolevUnitBallRadialTailMajorant dw (x : H) := by
    filter_upwards [by simpa [hpre] using hpull_polar] with x hx
    have hx_ne : (x : H) ≠ 0 := by
      intro hx_zero
      exact x.2 (by simp [hx_zero])
    have hx_norm_ne : ‖(x : H)‖ ≠ 0 := norm_ne_zero_iff.mpr hx_ne
    have hdir :
        ((e x).1 : H) = (((1 / ‖(x : H)‖) : ℝ) • (x : H)) := by
      simp [e, homeomorphUnitSphereProd_apply_fst_coe, div_eq_mul_inv]
    have hr :
        ((e x).2 : ℝ) = ‖(x : H)‖ := by
      simp [e, homeomorphUnitSphereProd_apply_snd_coe]
    have hpoint :
        ((e x).2 : ℝ) • ((e x).1 : H) = (x : H) := by
      rw [hr, hdir, smul_smul]
      have hcoef : ‖(x : H)‖ * (1 / ‖(x : H)‖) = (1 : ℝ) := by
        field_simp [hx_norm_ne]
      rw [hcoef, one_smul]
    have hx' := hx
    rw [hpoint, hdir] at hx'
    simpa using hx'
  have hcomap_restrict :
      (MeasureTheory.volume.restrict B).comap
          ((↑) : ({0}ᶜ : Set H) → H) =
        μNZ.restrict T := by
    have hraw :=
      (MeasurableEmbedding.subtype_coe hNZ_meas).comap_restrict
        (MeasureTheory.volume : Measure H) B
    have hpreB :
        ((↑) : ({0}ᶜ : Set H) → H) ⁻¹' B = T := by
      ext x
      simp [T, B, Metric.mem_ball, dist_eq_norm]
    simpa [μNZ, hpreB] using hraw
  have hpull_subtype :
      ∀ᵐ x : ({0}ᶜ : Set H) ∂((MeasureTheory.volume.restrict B).comap
          ((↑) : ({0}ᶜ : Set H) → H)),
        ENNReal.ofReal
          ‖w (x : H) - τ (((1 / ‖(x : H)‖) : ℝ) • (x : H))‖ ≤
          euclideanSobolevUnitBallRadialTailMajorant dw (x : H) := by
    simpa [hcomap_restrict] using hpull
  have hpull_original :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict B).restrict ({0}ᶜ : Set H),
        ENNReal.ofReal
          ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖ ≤
          euclideanSobolevUnitBallRadialTailMajorant dw x :=
      (ae_restrict_iff_subtype
      (μ := MeasureTheory.volume.restrict B) hNZ_meas).2 hpull_subtype
  have hmeasure_eq :
      (MeasureTheory.volume.restrict B).restrict ({0}ᶜ : Set H) =
        MeasureTheory.volume.restrict P := by
    rw [Measure.restrict_restrict hNZ_meas]
    congr 1
    ext x
    simp [P, B, Metric.mem_ball, dist_eq_norm, norm_pos_iff]
  rw [← hmeasure_eq]
  exact hpull_original

/--
%%handwave
name:
  Radial endpoint bounds for the polar product measure in explicit form
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  polar pair \((\theta,r)\) with \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
proof:
  This is exactly
  [the radial \(L^1\)-Cauchy trace endpoint estimate](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_l1_cauchy_trace_polar_product_raw_analytic_leaf).
-/
private theorem
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_analytic_leaf
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            ∫⁻ t in
              {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
  exact
    euclideanSobolev_unit_ball_radial_l1_cauchy_trace_polar_product_raw_analytic_leaf
      _hweak _hw _hdw

/--
%%handwave
name:
  Raywise radial endpoint bounds in explicit polar form
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  direction \(\theta\), for almost every \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
  Moreover the exceptional set for this inequality is null-measurable in the
  corresponding polar product measure.
proof:
  Apply
  [the polar-product endpoint estimate](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_analytic_leaf).
  The failure set has measure zero, hence is null-measurable, and Fubini gives
  the almost-everywhere statement on almost every radial line.
-/
private theorem
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_raywise_polar_raw_analytic
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        NullMeasurableSet
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            ¬ ENNReal.ofReal
                ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
              ∫⁻ t in
                {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume}
          ((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) ∧
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          ∀ᵐ r : Set.Ioi (0 : ℝ)
              ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
            ENNReal.ofReal
              ‖w ((r : ℝ) • (θ : H)) - τ (θ : H)‖ ≤
              ∫⁻ t in {t : ℝ | (r : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                ∂MeasureTheory.volume := by
  rcases
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_analytic_leaf
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hprod⟩
  refine ⟨τ, hτ_meas, ?_, ?_⟩
  · refine NullMeasurableSet.of_null ?_
    simpa [ae_iff] using hprod
  · exact Measure.ae_ae_of_ae_prod hprod

/--
%%handwave
name:
  Radial endpoint bounds for the polar product measure in explicit form
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  polar pair \((\theta,r)\) with \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
proof:
  This is exactly
  [the polar-product endpoint estimate](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_analytic_leaf).
-/
private theorem
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_analytic
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            ∫⁻ t in
              {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
  exact
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_analytic_leaf
      _hweak _hw _hdw

/--
%%handwave
name:
  Raywise radial endpoint bounds in explicit polar form
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  direction \(\theta\), for almost every \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
  Moreover the exceptional set for this inequality is null-measurable in the
  corresponding polar product measure.
proof:
  This is exactly
  [the raywise endpoint estimate with a null-measurable exceptional set](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_raywise_polar_raw_analytic).
-/
private theorem
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_raywise_polar_raw
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        NullMeasurableSet
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            ¬ ENNReal.ofReal
                ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
              ∫⁻ t in
                {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume}
          ((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) ∧
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          ∀ᵐ r : Set.Ioi (0 : ℝ)
              ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
            ENNReal.ofReal
              ‖w ((r : ℝ) • (θ : H)) - τ (θ : H)‖ ≤
              ∫⁻ t in {t : ℝ | (r : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                ∂MeasureTheory.volume := by
  exact
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_raywise_polar_raw_analytic
      _hweak _hw _hdw

/--
%%handwave
name:
  Radial endpoint bounds for the polar product in explicit form
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  polar pair \((\theta,r)\) with \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
proof:
  Apply the raywise polar endpoint estimate, which gives the inequality for
  almost every radius on almost every direction and identifies the exceptional
  set as null-measurable.  The product-measure form follows by Fubini for this
  null-measurable exceptional set.
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_core
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            ∫⁻ t in
              {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
              ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
              ∂MeasureTheory.volume := by
  exact
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_analytic
      _hweak _hw _hdw

/--
%%handwave
name:
  Radial endpoint bounds on almost every ray in explicit polar form
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  direction \(\theta\), for almost every \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
  The exceptional set in polar coordinates is null-measurable.
proof:
  Use polar decomposition to reduce the weak Sobolev information to almost
  every radial line.  On those lines the one-dimensional Sobolev
  representative is absolutely continuous and has an endpoint limit at
  \(r=1\); these endpoint limits define \(\tau\), and the fundamental theorem
  of calculus gives the tail estimate.
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_ae_polar_raw
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        NullMeasurableSet
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            ¬ ENNReal.ofReal
                ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
              ∫⁻ t in
                {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume}
          ((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) ∧
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          ∀ᵐ r : Set.Ioi (0 : ℝ)
              ∂((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1)).restrict
                  {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
            ENNReal.ofReal
              ‖w ((r : ℝ) • (θ : H)) - τ (θ : H)‖ ≤
              ∫⁻ t in {t : ℝ | (r : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (θ : H)) (θ : H)‖
                ∂MeasureTheory.volume := by
  rcases
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_core
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hprod⟩
  refine ⟨τ, hτ_meas, ?_, ?_⟩
  · refine NullMeasurableSet.of_null ?_
    simpa [ae_iff] using hprod
  · exact Measure.ae_ae_of_ae_prod hprod

/--
%%handwave
name:
  Radial endpoint bounds in explicit polar form
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  polar pair \((\theta,r)\) with \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
proof:
  Apply the polar-product form of the radial endpoint estimate.
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product_raw
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            ∫⁻ t in
              {t : ℝ | ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < t ∧ t < 1},
                ENNReal.ofReal ‖dw (t • (p.1 : H)) (p.1 : H)‖
                ∂MeasureTheory.volume := by
  exact
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_polar_product_raw_core
      _hweak _hw _hdw

/--
%%handwave
name:
  Radial endpoint bounds for the polar product measure
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  polar pair \((\theta,r)\) with \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
proof:
  Apply the explicit polar radial endpoint estimate and use
  \(\|r\theta\|=r\), \(r^{-1}(r\theta)=\theta\) for \(0<r<1\), to identify
  the radial tail integral with the stated majorant.
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product_core
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            euclideanSobolevUnitBallRadialTailMajorant dw
              ((p.2 : ℝ) • (p.1 : H)) := by
  rcases
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product_raw
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hraw⟩
  refine ⟨τ, hτ_meas, ?_⟩
  filter_upwards [hraw] with p hp
  rw [euclideanSobolevUnitBallRadialTailMajorant_polar (dw := dw) p]
  exact hp

/--
%%handwave
name:
  Radial endpoint bounds on almost every ray
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable boundary representative \(\tau\) such that, for almost every
  direction \(\theta\), the one-dimensional radial restriction satisfies, for
  almost every \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
  The exceptional set where this inequality fails is null-measurable in polar
  coordinates.
proof:
  Apply
  [the tail estimate for almost every polar pair](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product_core).
  Its exceptional set has measure zero, hence is null-measurable, and Fubini
  gives the corresponding almost-everywhere statement on almost every ray.
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_ae_polar
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        NullMeasurableSet
          {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
            ¬ ENNReal.ofReal
                ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
              euclideanSobolevUnitBallRadialTailMajorant dw
                ((p.2 : ℝ) • (p.1 : H))}
          ((MeasureTheory.volume : Measure H).toSphere.prod
            (((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1) :
                Measure (Set.Ioi (0 : ℝ)))).restrict
              {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})) ∧
        ∀ᵐ θ : Metric.sphere (0 : H) 1
            ∂((MeasureTheory.volume : Measure H).toSphere),
          ∀ᵐ r : Set.Ioi (0 : ℝ)
              ∂(((MeasureTheory.Measure.volumeIoiPow
                (Module.finrank ℝ H - 1) :
                  Measure (Set.Ioi (0 : ℝ)))).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1}),
            ENNReal.ofReal
              ‖w ((r : ℝ) • (θ : H)) - τ (θ : H)‖ ≤
              euclideanSobolevUnitBallRadialTailMajorant dw
                ((r : ℝ) • (θ : H)) := by
  rcases
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product_core
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hprod⟩
  refine ⟨τ, hτ_meas, ?_, ?_⟩
  · refine NullMeasurableSet.of_null ?_
    simpa [ae_iff] using hprod
  · exact Measure.ae_ae_of_ae_prod hprod

/--
%%handwave
name:
  Radial ACL endpoint trace bound for the polar product measure
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable endpoint representative \(\tau\) on the unit sphere such that,
  for almost every pair \((\theta,r)\) in the polar product measure with
  \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
proof:
  This is exactly
  [the tail estimate for almost every polar pair](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product_core).
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
            ((MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1)).restrict
                {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            euclideanSobolevUnitBallRadialTailMajorant dw
              ((p.2 : ℝ) • (p.1 : H)) := by
  exact
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product_core
      _hweak _hw _hdw

/--
%%handwave
name:
  Radial ACL endpoint trace bound in polar coordinates
statement:
  In positive dimension, a scalar \(W^{1,2}\) function on the unit ball has a
  measurable endpoint representative \(\tau\) on the unit sphere such that,
  for almost every direction \(\theta\) and radius \(0<r<1\),
  \[
    |w(r\theta)-\tau(\theta)|
      \le
    \int_r^1 |Dw(t\theta)\theta|\,dt .
  \]
proof:
  Apply the polar product measure form of the radial endpoint theorem and use
  the identity between restricting the product measure to \(r<1\) and taking
  the product with the restricted radial measure.
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ p ∂(((MeasureTheory.volume : Measure H).toSphere.prod
            (MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ H - 1))).restrict
              {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) |
                (p.2 : ℝ) < 1}),
          ENNReal.ofReal
            ‖w ((p.2 : ℝ) • (p.1 : H)) - τ (p.1 : H)‖ ≤
            euclideanSobolevUnitBallRadialTailMajorant dw
              ((p.2 : ℝ) • (p.1 : H)) := by
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) := {r | (r : ℝ) < 1}
  let S : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) < 1}
  rcases
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_polar_product
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hpolar⟩
  refine ⟨τ, hτ_meas, ?_⟩
  have hS_eq : S = Set.univ ×ˢ R := by
    ext p
    simp [S, R]
  have hmeasure :
      (μS.prod μR).restrict S = μS.prod (μR.restrict R) := by
    rw [hS_eq]
    have hprod :=
      Measure.prod_restrict (μ := μS) (ν := μR) Set.univ R
    simpa using hprod.symm
  simpa [μS, μR, R, S, hmeasure] using hpolar

/--
%%handwave
name:
  Radial ACL endpoint trace bound in positive dimension
statement:
  In a nonzero finite-dimensional Euclidean space, a scalar \(W^{1,2}\)
  function on the unit ball has a measurable radial endpoint representative
  \(\tau\) such that, for almost every point \(0<\|x\|<1\),
  \[
    |w(x)-\tau(x/\|x\|)|
      \le
    \int_{\|x\|}^1
      |Dw(t x/\|x\|)(x/\|x\|)|\,dt .
  \]
proof:
  This is exactly
  [the punctured-ball radial endpoint bound](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_punctured_analytic_leaf).
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_punctured_nontrivial
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ x ∂MeasureTheory.volume.restrict
            {x : H | 0 < ‖x‖ ∧ ‖x‖ < 1},
          ENNReal.ofReal
            ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖ ≤
            euclideanSobolevUnitBallRadialTailMajorant dw x := by
  exact
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_punctured_analytic_leaf
      _hweak _hw _hdw

/--
%%handwave
name:
  Radial ACL endpoint trace bound on the punctured ball
statement:
  A scalar \(W^{1,2}\) function on the unit ball has a measurable radial
  endpoint representative \(\tau\) such that, for almost every point
  \(0<\|x\|<1\),
  \[
    |w(x)-\tau(x/\|x\|)|
      \le
    \int_{\|x\|}^1
      |Dw(t x/\|x\|)(x/\|x\|)|\,dt .
  \]
proof:
  If the ambient space is trivial, the punctured unit ball is empty.  Otherwise
  apply the positive-dimensional radial absolute-continuity theorem.
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_punctured
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᵐ x ∂MeasureTheory.volume.restrict
            {x : H | 0 < ‖x‖ ∧ ‖x‖ < 1},
          ENNReal.ofReal
            ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖ ≤
            euclideanSobolevUnitBallRadialTailMajorant dw x := by
  classical
  rcases subsingleton_or_nontrivial H with hsub | hnontrivial
  · letI : Subsingleton H := hsub
    refine ⟨fun _ : H ↦ 0, measurable_const, ?_⟩
    have hpunct_empty :
        {x : H | ¬ x = 0 ∧ ‖x‖ < 1} = ∅ := by
      ext x
      constructor
      · intro hx
        have hx_zero : x = 0 := Subsingleton.elim x 0
        exact False.elim (hx.1 hx_zero)
      · intro hx
        cases hx
    simp [hpunct_empty]
  · letI : Nontrivial H := hnontrivial
    exact
      euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_punctured_nontrivial
        _hweak _hw _hdw

/--
%%handwave
name:
  Radial ACL endpoint trace bound on each thin collar
statement:
  A scalar \(W^{1,2}\) function on the unit ball has a measurable radial
  endpoint representative \(\tau\) such that, for every \(0<\varepsilon<1\),
  almost every point in the collar \(1-\varepsilon<\|x\|<1\) satisfies
  \[
    |w(x)-\tau(x/\|x\|)|
      \le
    \int_{\|x\|}^1
      |Dw(t x/\|x\|)(x/\|x\|)|\,dt .
  \]
proof:
  Apply the same bound on the punctured unit ball and restrict the ambient
  measure to the collar, which is contained in \(0<\|x\|<1\) whenever
  \(0<\varepsilon<1\).
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_all_thin_collars
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∀ᵐ x ∂MeasureTheory.volume.restrict
              {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            ENNReal.ofReal
              ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖ ≤
              euclideanSobolevUnitBallRadialTailMajorant dw x := by
  rcases
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_ae_punctured
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hpunct⟩
  refine ⟨τ, hτ_meas, ?_⟩
  intro ε _hε_pos hε_lt
  have hsubset :
      {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1} ⊆
        {x : H | 0 < ‖x‖ ∧ ‖x‖ < 1} := by
    intro x hx
    have hinner_pos : 0 < (1 : ℝ) - ε := by linarith
    exact ⟨lt_trans hinner_pos hx.1, hx.2⟩
  exact ae_mono (Measure.restrict_mono hsubset le_rfl) hpunct

/--
%%handwave
name:
  Radial ACL gives a pointwise trace tail bound
statement:
  A scalar \(W^{1,2}\) function on the unit ball has a measurable radial
  endpoint representative \(\tau\) such that, for all sufficiently small
  positive \(\varepsilon\), almost every \(x\) in the inner collar
  \(1-\varepsilon<\|x\|<1\) satisfies
  \[
    |w(x)-\tau(x/\|x\|)|
      \le
    \int_{\|x\|}^1
      |Dw(t x/\|x\|)(x/\|x\|)|\,dt .
  \]
proof:
  Apply the ACL representative on almost every radial segment.  The endpoint
  limits along the segment define \(\tau\) on the unit sphere, and the
  fundamental theorem of calculus along the segment bounds the endpoint
  difference by the integral of the directional weak derivative.
-/
theorem euclideanSobolev_unit_ball_radial_acl_trace_tail_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          ∀ᵐ x ∂MeasureTheory.volume.restrict
              {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            ENNReal.ofReal
              ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖ ≤
              euclideanSobolevUnitBallRadialTailMajorant dw x := by
  rcases
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound_all_thin_collars
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hbound⟩
  refine ⟨τ, hτ_meas, ?_⟩
  have hthin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hthin] with ε hε_pos hε_lt
  exact hbound ε hε_pos hε_lt

/--
%%handwave
name:
  Unit inner collars shrink to measure zero
statement:
  The Haar measure of the collars
  \(1-\varepsilon<\|x\|<1\) tends to zero as
  \(\varepsilon\downarrow0\).
proof:
  The collars are increasing with respect to \(\varepsilon\), have finite
  measure for one positive width, and their intersection over all positive
  widths is empty.  Continuity of measure from above gives the result.
-/
theorem unit_inner_collar_measure_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (MeasureTheory.volume : Measure H)
          {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1})
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let R : ℝ := 1
  let S : ℝ → Set H := fun ε : ℝ ↦
    {x : H | R - ε < ‖x‖ ∧ ‖x‖ < R}
  have hmeas : ∀ ε > (0 : ℝ),
      NullMeasurableSet (S ε) (MeasureTheory.volume : Measure H) := by
    intro ε _hε
    dsimp [S]
    exact (by measurability : MeasurableSet
      {x : H | R - ε < ‖x‖ ∧ ‖x‖ < R}).nullMeasurableSet
  have hmono : ∀ i j : ℝ, (0 : ℝ) < i → i ≤ j → S i ⊆ S j := by
    intro i j _hi hij x hx
    dsimp [S] at hx ⊢
    exact ⟨by linarith [hx.1, hij], hx.2⟩
  have hfinite : ∃ ε > (0 : ℝ),
      (MeasureTheory.volume : Measure H) (S ε) ≠ ⊤ := by
    refine ⟨1, by norm_num, ?_⟩
    have hS_subset : S 1 ⊆ Metric.closedBall (0 : H) R := by
      intro x hx
      dsimp [S] at hx
      simp [Metric.mem_closedBall, dist_eq_norm]
      exact hx.2.le
    have hclosed_ne_top :
        (MeasureTheory.volume : Measure H)
          (Metric.closedBall (0 : H) R) ≠ ⊤ :=
      (isCompact_closedBall (0 : H) R).measure_ne_top
    exact ne_top_of_le_ne_top hclosed_ne_top (measure_mono hS_subset)
  have hS_empty : (⋂ ε > (0 : ℝ), S ε) = (∅ : Set H) := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx_all : ∀ ε : ℝ, 0 < ε → x ∈ S ε := by
      intro ε hε
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hx ε) hε
    have hx_upper : ‖x‖ < R := (hx_all 1 (by norm_num)).2
    let δ : ℝ := (R - ‖x‖) / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact half_pos (sub_pos.mpr hx_upper)
    have hx_lower : R - δ < ‖x‖ := (hx_all δ hδ_pos).1
    dsimp [δ] at hx_lower
    have hR_lt_norm : R < ‖x‖ := by
      have htwice :
          2 * (R - (R - ‖x‖) / 2) < 2 * ‖x‖ := by
        exact mul_lt_mul_of_pos_left hx_lower (by norm_num : (0 : ℝ) < 2)
      ring_nf at htwice
      linarith [htwice]
    exact (not_lt_of_ge hx_upper.le) hR_lt_norm
  have htendsto :=
    tendsto_measure_biInter_gt
      (μ := (MeasureTheory.volume : Measure H))
      (s := S) (a := (0 : ℝ)) hmeas hmono hfinite
  have htarget :
      Filter.Tendsto ((MeasureTheory.volume : Measure H) ∘ S)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [hS_empty] using htendsto
  simpa [Function.comp_def, S, R] using htarget

/--
%%handwave
name:
  Unit-ball \(L^1\)-mass vanishes in shrinking inner collars
statement:
  If \(g\) is square-integrable in the unit ball, then its \(L^1\)-mass on
  the collars \(1-\varepsilon<\|x\|<1\) tends to zero.
proof:
  Square-integrability on the finite-measure unit ball implies
  integrability there.  Absolute continuity of the integral over shrinking
  collars, whose measure tends to zero, gives the result.
-/
theorem unit_ball_l1_inner_collar_mass_tendsto_zero
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {g : H → E}
    (hg : MemLp g 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let B : Set H := Metric.ball (0 : H) 1
  let F : H → ℝ≥0∞ :=
    fun x : H ↦ B.indicator (fun y : H ↦ ENNReal.ofReal ‖g y‖) x
  have hB_meas : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_ball
  have hB_subset : B ⊆ Metric.closedBall (0 : H) 1 :=
    Metric.ball_subset_closedBall
  have hclosed_ne_top :
      (MeasureTheory.volume : Measure H)
        (Metric.closedBall (0 : H) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : H) 1).measure_ne_top
  have hB_ne_top : (MeasureTheory.volume : Measure H) B ≠ ⊤ :=
    ne_top_of_le_ne_top hclosed_ne_top (measure_mono hB_subset)
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict B) :=
    isFiniteMeasure_restrict.2 hB_ne_top
  have hg_int : Integrable g (MeasureTheory.volume.restrict B) := by
    simpa [B] using hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hF_finite : ∫⁻ x, F x ∂MeasureTheory.volume ≠ ⊤ := by
    have hnorm_lt :
        (∫⁻ x, ENNReal.ofReal ‖g x‖
            ∂MeasureTheory.volume.restrict B) < ⊤ :=
      hg_int.norm.lintegral_lt_top
    have hF_eq :
        (∫⁻ x, F x ∂MeasureTheory.volume) =
          ∫⁻ x, ENNReal.ofReal ‖g x‖
            ∂MeasureTheory.volume.restrict B := by
      dsimp [F]
      rw [lintegral_indicator hB_meas]
    rw [hF_eq]
    exact ne_of_lt hnorm_lt
  have hmeasure :
      Filter.Tendsto
        ((MeasureTheory.volume : Measure H) ∘
          (fun ε : ℝ ↦
            {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [Function.comp_def] using
      unit_inner_collar_measure_tendsto_zero (H := H)
  have hF_tendsto :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            F x ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_setLIntegral_zero hF_finite hmeasure
  have heq :
      ∀ ε : ℝ,
        (∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            F x ∂MeasureTheory.volume) =
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume := by
    intro ε
    refine setLIntegral_congr_fun (by measurability) ?_
    intro x hx
    have hxB : x ∈ B := by
      dsimp [B]
      simpa [Metric.mem_ball, dist_eq_norm] using hx.2
    simp [F, hxB]
  exact hF_tendsto.congr' <|
    Filter.Eventually.of_forall fun ε ↦ by
      exact heq ε

/--
%%handwave
name:
  Dilating a radial subcollar lands in the same inner collar
statement:
  If \(q\ge 1\), then the dilation \(x\mapsto qx\) sends the set
  \[
    \{x:1-\varepsilon<\|x\|,\ \|qx\|<1\}
  \]
  into the collar \(1-\varepsilon<\|y\|<1\).
proof:
  The upper bound is part of the definition of the subcollar.  The lower
  bound follows from \(\|qx\|=q\|x\|\ge\|x\|\).
-/
theorem unit_inner_collar_dilation_subcollar_mapsTo
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {ε q : ℝ} (hq_one : 1 ≤ q) :
    Set.MapsTo (fun x : H ↦ q • x)
      {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}
      {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1} := by
  intro x hx
  have hq_nonneg : 0 ≤ q := le_trans zero_le_one hq_one
  have hnorm : ‖q • x‖ = q * ‖x‖ := by
    simpa [Real.norm_of_nonneg hq_nonneg] using norm_smul q x
  constructor
  · calc
      (1 : ℝ) - ε < ‖x‖ := hx.1
      _ ≤ q * ‖x‖ := by
        calc
          ‖x‖ = (1 : ℝ) * ‖x‖ := by ring
          _ ≤ q * ‖x‖ :=
            mul_le_mul_of_nonneg_right hq_one (norm_nonneg x)
      _ = ‖q • x‖ := hnorm.symm
  · exact hx.2

/--
%%handwave
name:
  Dilation of a radial subcollar has bounded measure distortion
statement:
  If \(q>0\) and \(q\ge1\), then pushing forward volume restricted to
  \[
    \{x:1-\varepsilon<\|x\|,\ \|qx\|<1\}
  \]
  by \(x\mapsto qx\) is bounded by the usual linear-dilation Jacobian factor
  times volume restricted to \(1-\varepsilon<\|y\|<1\).
proof:
  The dilation is a measurable embedding and its push-forward on Haar measure
  is the inverse determinant factor.  Restricting to the image of the
  subcollar and using the preceding inclusion gives the restricted measure
  inequality.
-/
theorem unit_inner_collar_dilation_subcollar_map_restrict_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {ε q : ℝ} (hq_pos : 0 < q) (hq_one : 1 ≤ q) :
    Measure.map (fun x : H ↦ q • x)
        (MeasureTheory.volume.restrict
          {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}) ≤
      ENNReal.ofReal |(q ^ Module.finrank ℝ H)⁻¹| •
        MeasureTheory.volume.restrict
          {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1} := by
  let T : H → H := fun x : H ↦ q • x
  let D : Set H := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}
  let S : Set H := {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1}
  let J : ℝ≥0∞ := ENNReal.ofReal |(q ^ Module.finrank ℝ H)⁻¹|
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hT_emb : MeasurableEmbedding T := by
    simpa [T] using
      measurableEmbedding_const_smul₀ (α := H) hq_ne
  have hmap_volume :
      Measure.map T MeasureTheory.volume =
        J • (MeasureTheory.volume : Measure H) := by
    simpa [T, J] using map_const_smul_volume_eq_smul (H := H) hq_ne
  have himage_subset : T '' D ⊆ S := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa [T, D, S] using
      unit_inner_collar_dilation_subcollar_mapsTo
        (H := H) (ε := ε) (q := q) hq_one hx
  have hmap_restrict_eq :
      Measure.map T (MeasureTheory.volume.restrict D) =
        (Measure.map T MeasureTheory.volume).restrict (T '' D) := by
    have hrestrict :=
      hT_emb.restrict_map (MeasureTheory.volume : Measure H) (T '' D)
    have hpre : T ⁻¹' (T '' D) = D :=
      hT_emb.injective.preimage_image D
    rw [hpre] at hrestrict
    exact hrestrict.symm
  calc
    Measure.map (fun x : H ↦ q • x)
        (MeasureTheory.volume.restrict
          {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1})
        = Measure.map T (MeasureTheory.volume.restrict D) := rfl
    _ = (Measure.map T MeasureTheory.volume).restrict (T '' D) :=
        hmap_restrict_eq
    _ = (J • (MeasureTheory.volume : Measure H)).restrict (T '' D) := by
        rw [hmap_volume]
    _ ≤ (J • (MeasureTheory.volume : Measure H)).restrict S :=
        Measure.restrict_mono himage_subset le_rfl
    _ = J • MeasureTheory.volume.restrict S := by
        rw [Measure.restrict_smul]
    _ = ENNReal.ofReal |(q ^ Module.finrank ℝ H)⁻¹| •
        MeasureTheory.volume.restrict
          {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1} := rfl

/--
%%handwave
name:
  Dilation pullback over a radial subcollar is controlled by collar mass
statement:
  Let \(F\) be measurable on the unit ball.  If \(q>0\) and \(q\ge1\), then
  \[
    \int_{\{1-\varepsilon<\|x\|,\ \|qx\|<1\}} F(qx)\,dx
      \le
    |q|^{-\dim H}
      \int_{\{1-\varepsilon<\|y\|<1\}} F(y)\,dy .
  \]
proof:
  Rewrite the left-hand side as an integral against the push-forward of the
  restricted measure by \(x\mapsto qx\), then apply the preceding restricted
  measure inequality.
-/
theorem unit_inner_collar_dilation_subcollar_lintegral_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {F : H → ℝ≥0∞}
    (hF : AEMeasurable F
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    {ε q : ℝ} (hq_pos : 0 < q) (hq_one : 1 ≤ q) :
    ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
        F (q • x) ∂MeasureTheory.volume ≤
      ENNReal.ofReal |(q ^ Module.finrank ℝ H)⁻¹| *
        ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
          F y ∂MeasureTheory.volume := by
  let T : H → H := fun x : H ↦ q • x
  let D : Set H := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}
  let S : Set H := {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1}
  let J : ℝ≥0∞ := ENNReal.ofReal |(q ^ Module.finrank ℝ H)⁻¹|
  have hT_meas : Measurable T := by
    dsimp [T]
    measurability
  have hS_subset_ball : S ⊆ Metric.ball (0 : H) 1 := by
    intro y hy
    dsimp [S] at hy
    simpa [Metric.mem_ball, dist_eq_norm] using hy.2
  have hF_S : AEMeasurable F (MeasureTheory.volume.restrict S) :=
    hF.mono_measure
      (Measure.restrict_mono hS_subset_ball le_rfl)
  have hmap_le :
      Measure.map T (MeasureTheory.volume.restrict D) ≤
        J • MeasureTheory.volume.restrict S := by
    simpa [T, D, S, J] using
      unit_inner_collar_dilation_subcollar_map_restrict_le
        (H := H) (ε := ε) (q := q) hq_pos hq_one
  have hmap_ac :
      Measure.map T (MeasureTheory.volume.restrict D) ≪
        MeasureTheory.volume.restrict S :=
    Measure.absolutelyContinuous_of_le_smul hmap_le
  have hF_map :
      AEMeasurable F (Measure.map T (MeasureTheory.volume.restrict D)) :=
    hF_S.mono_ac hmap_ac
  calc
    ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
        F (q • x) ∂MeasureTheory.volume
        = ∫⁻ x, F (T x) ∂MeasureTheory.volume.restrict D := by
            simp [T, D]
    _ = ∫⁻ y, F y ∂Measure.map T (MeasureTheory.volume.restrict D) :=
        (lintegral_map' hF_map hT_meas.aemeasurable).symm
    _ ≤ ∫⁻ y, F y ∂(J • MeasureTheory.volume.restrict S) :=
        lintegral_mono' hmap_le le_rfl
    _ = J * ∫⁻ y in S, F y ∂MeasureTheory.volume := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal |(q ^ Module.finrank ℝ H)⁻¹| *
        ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
          F y ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Dilation by a positive factor is null-set preserving in product form
statement:
  On any interval of positive dilation factors, the map
  \((x,q)\mapsto qx\) from \(H\times I\) to \(H\) sends null sets to null
  sets in the inverse-image sense.
proof:
  For each fixed \(q>1\), the map \(x\mapsto qx\) is a linear dilation with
  nonzero determinant, so it preserves null sets.  The product
  quasi-measure-preservation criterion applies this fiberwise fact for almost
  every dilation factor.
-/
theorem unit_inner_collar_dilation_product_interval_quasiMeasurePreserving
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] {ε : ℝ} :
    Measure.QuasiMeasurePreserving
      (fun p : H × ℝ ↦ p.2 • p.1)
      ((MeasureTheory.volume : Measure H).prod
        ((MeasureTheory.volume : Measure ℝ).restrict
          {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹}))
      (MeasureTheory.volume : Measure H) := by
  let I : Set ℝ := {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹}
  refine MeasureTheory.QuasiMeasurePreserving.prod_of_left
    (τ := (MeasureTheory.volume : Measure H)) ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem (by
        dsimp [I]
        measurability : MeasurableSet I)] with q hq
    have hq_ne : q ≠ 0 := by
      exact ne_of_gt (lt_trans zero_lt_one hq.1)
    simpa using
      (Measure.quasiMeasurePreserving_smul
        (μ := (MeasureTheory.volume : Measure H)) hq_ne)

/--
%%handwave
name:
  The admissible dilation map into the unit ball is null-set preserving
statement:
  Restricting the product dilation map \((x,q)\mapsto qx\) to pairs with
  \(1-\varepsilon<\|x\|<1\), \(1<q<(1-\varepsilon)^{-1}\), and
  \(\|qx\|<1\) gives a null-set-preserving map into the unit ball.
proof:
  The preceding product null-set-preservation result applies on the whole
  positive dilation interval.  Restrict the domain to the admissible set and
  the codomain to the unit ball, using the defining inequality \(\|qx\|<1\).
-/
theorem unit_inner_collar_dilation_admissible_product_quasiMeasurePreserving
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] {ε : ℝ} :
    Measure.QuasiMeasurePreserving
      (fun p : H × ℝ ↦ p.2 • p.1)
      (((MeasureTheory.volume : Measure H).prod
        ((MeasureTheory.volume : Measure ℝ).restrict
          {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹})).restrict
        {p : H × ℝ |
          ((1 : ℝ) - ε < ‖p.1‖ ∧ ‖p.1‖ < 1) ∧
            (1 < p.2 ∧ p.2 < ((1 : ℝ) - ε)⁻¹) ∧
            ‖p.2 • p.1‖ < 1})
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
  let A : Set (H × ℝ) :=
    {p : H × ℝ |
      ((1 : ℝ) - ε < ‖p.1‖ ∧ ‖p.1‖ < 1) ∧
        (1 < p.2 ∧ p.2 < ((1 : ℝ) - ε)⁻¹) ∧
        ‖p.2 • p.1‖ < 1}
  have hmaps : Set.MapsTo
      (fun p : H × ℝ ↦ p.2 • p.1) A (Metric.ball (0 : H) 1) := by
    intro p hp
    dsimp [A] at hp
    simpa [Metric.mem_ball, dist_eq_norm] using hp.2.2
  simpa [A] using
    (unit_inner_collar_dilation_product_interval_quasiMeasurePreserving
      (H := H) (ε := ε)).restrict hmaps

/--
%%handwave
name:
  The admissible dilation map is null-set preserving for the full product
statement:
  The same admissible dilation map \((x,q)\mapsto qx\) remains
  null-set-preserving when its domain is viewed as a restriction of the full
  product measure on \(H\times\mathbb R\).
proof:
  The admissible set is contained in \(H\times I\), where \(I\) is the
  interval of allowed dilation factors.  Therefore restricting the full
  product measure to the admissible set agrees with restricting the
  interval-product measure there.  The preceding restricted product result
  applies.
-/
theorem unit_inner_collar_dilation_admissible_full_product_quasiMeasurePreserving
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] {ε : ℝ} :
    Measure.QuasiMeasurePreserving
      (fun p : H × ℝ ↦ p.2 • p.1)
      (((MeasureTheory.volume : Measure H).prod
        (MeasureTheory.volume : Measure ℝ)).restrict
        {p : H × ℝ |
          ((1 : ℝ) - ε < ‖p.1‖ ∧ ‖p.1‖ < 1) ∧
            (1 < p.2 ∧ p.2 < ((1 : ℝ) - ε)⁻¹) ∧
            ‖p.2 • p.1‖ < 1})
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
  let μH : Measure H := MeasureTheory.volume
  let μR : Measure ℝ := MeasureTheory.volume
  let I : Set ℝ := {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹}
  let A : Set (H × ℝ) :=
    {p : H × ℝ |
      ((1 : ℝ) - ε < ‖p.1‖ ∧ ‖p.1‖ < 1) ∧
        (1 < p.2 ∧ p.2 < ((1 : ℝ) - ε)⁻¹) ∧
        ‖p.2 • p.1‖ < 1}
  let U : Set (H × ℝ) := Set.univ ×ˢ I
  have hA_subset_U : A ⊆ U := by
    intro p hp
    exact ⟨Set.mem_univ p.1, by simpa [I, A] using hp.2.1⟩
  have hprod_interval :
      μH.prod (μR.restrict I) = (μH.prod μR).restrict U := by
    have hprod := Measure.prod_restrict (μ := μH) (ν := μR)
      (Set.univ : Set H) I
    simpa [μH, μR, I, U] using hprod
  have hdomain_eq :
      ((μH.prod (μR.restrict I)).restrict A) =
        ((μH.prod μR).restrict A) := by
    rw [hprod_interval]
    exact Measure.restrict_restrict_of_subset hA_subset_U
  have hdomain_ac :
      ((μH.prod μR).restrict A) ≪
        ((μH.prod (μR.restrict I)).restrict A) := by
    rw [hdomain_eq]
  have hqmp :=
    unit_inner_collar_dilation_admissible_product_quasiMeasurePreserving
      (H := H) (ε := ε)
  simpa [μH, μR, I, A] using hqmp.mono_left hdomain_ac

/--
%%handwave
name:
  One-dimensional radial tails are bounded by dilation-factor tails
statement:
  If \(0<r\le 1\), then changing variables \(t=qr\) in a radial tail gives
  \[
    \int_{r<t<1} F(t/r)\,dt
      \le
    \int_{\{q:1<q,\ qr<1\}} F(q)\,dq .
  \]
proof:
  The map \(t\mapsto t/r\) sends \(r<t<1\) into
  \(\{q:1<q,\ qr<1\}\).  Its one-dimensional Jacobian factor is \(r\le1\),
  so the pushed-forward restricted measure is bounded by Lebesgue measure on
  the target set.
-/
theorem real_radial_tail_lintegral_le_dilation_sublevel
    {F : ℝ → ℝ≥0∞} {r : ℝ}
    (hr_pos : 0 < r) (hr_le_one : r ≤ 1) :
    ∫⁻ t in {t : ℝ | r < t ∧ t < 1}, F (t / r) ∂MeasureTheory.volume ≤
      ∫⁻ q in {q : ℝ | 1 < q ∧ q * r < 1}, F q ∂MeasureTheory.volume := by
  let T : ℝ → ℝ := fun t : ℝ ↦ t / r
  let It : Set ℝ := {t : ℝ | r < t ∧ t < 1}
  let Iq : Set ℝ := {q : ℝ | 1 < q ∧ q * r < 1}
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hcoef_ne : (1 / r : ℝ) ≠ 0 := one_div_ne_zero hr_ne
  have hT_emb : MeasurableEmbedding T := by
    simpa [T, div_eq_mul_inv, smul_eq_mul, mul_comm] using
      measurableEmbedding_const_smul₀ (α := ℝ) hcoef_ne
  have hmap_volume :
      Measure.map T (MeasureTheory.volume : Measure ℝ) =
        ENNReal.ofReal r • (MeasureTheory.volume : Measure ℝ) := by
    have hraw :=
      map_const_smul_volume_eq_smul (H := ℝ) hcoef_ne
    simpa [T, div_eq_mul_inv, smul_eq_mul, mul_comm, Module.finrank_self,
      abs_of_pos hr_pos] using hraw
  have himage_subset : T '' It ⊆ Iq := by
    intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    dsimp [T, It, Iq] at ht ⊢
    constructor
    · rw [one_lt_div hr_pos]
      simpa [one_mul] using ht.1
    · field_simp [hr_ne]
      exact ht.2
  have hmap_restrict_eq :
      Measure.map T (MeasureTheory.volume.restrict It) =
        (Measure.map T (MeasureTheory.volume : Measure ℝ)).restrict (T '' It) := by
    have hrestrict :=
      hT_emb.restrict_map (MeasureTheory.volume : Measure ℝ) (T '' It)
    have hpre : T ⁻¹' (T '' It) = It :=
      hT_emb.injective.preimage_image It
    rw [hpre] at hrestrict
    exact hrestrict.symm
  have hcoef_le_one : ENNReal.ofReal r ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr hr_le_one
  have hsmul_restrict_le :
      ENNReal.ofReal r • (MeasureTheory.volume : Measure ℝ).restrict (T '' It) ≤
        (MeasureTheory.volume : Measure ℝ).restrict (T '' It) := by
    refine Measure.le_iff.2 ?_
    intro A hA
    rw [Measure.smul_apply]
    calc
      ENNReal.ofReal r * (MeasureTheory.volume : Measure ℝ).restrict (T '' It) A
          ≤ 1 * (MeasureTheory.volume : Measure ℝ).restrict (T '' It) A :=
            mul_le_mul_left hcoef_le_one _
      _ = (MeasureTheory.volume : Measure ℝ).restrict (T '' It) A := by
            simp
  have hmap_le :
      Measure.map T (MeasureTheory.volume.restrict It) ≤
        MeasureTheory.volume.restrict Iq := by
    calc
      Measure.map T (MeasureTheory.volume.restrict It)
          = (Measure.map T (MeasureTheory.volume : Measure ℝ)).restrict (T '' It) :=
            hmap_restrict_eq
      _ = (ENNReal.ofReal r • (MeasureTheory.volume : Measure ℝ)).restrict (T '' It) := by
            rw [hmap_volume]
      _ = ENNReal.ofReal r • (MeasureTheory.volume : Measure ℝ).restrict (T '' It) := by
            rw [Measure.restrict_smul]
      _ ≤ (MeasureTheory.volume : Measure ℝ).restrict (T '' It) :=
            hsmul_restrict_le
      _ ≤ MeasureTheory.volume.restrict Iq :=
            Measure.restrict_mono himage_subset le_rfl
  calc
    ∫⁻ t in {t : ℝ | r < t ∧ t < 1}, F (t / r) ∂MeasureTheory.volume
        = ∫⁻ t, F (T t) ∂MeasureTheory.volume.restrict It := by
            simp [T, It]
    _ = ∫⁻ q, F q ∂Measure.map T (MeasureTheory.volume.restrict It) :=
        (hT_emb.lintegral_map (μ := MeasureTheory.volume.restrict It) F).symm
    _ ≤ ∫⁻ q, F q ∂MeasureTheory.volume.restrict Iq :=
        lintegral_mono' hmap_le le_rfl
    _ = ∫⁻ q in {q : ℝ | 1 < q ∧ q * r < 1}, F q ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Pointwise radial tails are bounded by dilation-factor sublevel integrals
statement:
  If \(0<\|x\|\le1\), then
  \[
    \int_{\|x\|<t<1} F(t x/\|x\|)\,dt
      \le
    \int_{\{q:1<q,\ \|qx\|<1\}} F(qx)\,dq .
  \]
proof:
  Apply the one-dimensional radial-tail estimate with \(r=\|x\|\) to the
  function \(q\mapsto F(qx)\).  On \(q>1\), the condition
  \(q\|x\|<1\) is equivalent to \(\|qx\|<1\).
-/
theorem euclideanSobolev_unit_ball_radial_tailIntegral_le_dilation_sublevel
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → ℝ≥0∞} {x : H}
    (hx_pos : 0 < ‖x‖) (hx_le_one : ‖x‖ ≤ 1) :
    euclideanSobolevUnitBallRadialTailIntegral F x ≤
      ∫⁻ q in {q : ℝ | 1 < q ∧ ‖q • x‖ < 1},
        F (q • x) ∂MeasureTheory.volume := by
  have hset :
      {q : ℝ | 1 < q ∧ q * ‖x‖ < 1} =
        {q : ℝ | 1 < q ∧ ‖q • x‖ < 1} := by
    ext q
    constructor
    · intro hq
      have hq_nonneg : 0 ≤ q := (zero_lt_one.trans hq.1).le
      have hnorm : ‖q • x‖ = q * ‖x‖ := by
        simpa [Real.norm_of_nonneg hq_nonneg] using norm_smul q x
      exact ⟨hq.1, by simpa [hnorm] using hq.2⟩
    · intro hq
      have hq_nonneg : 0 ≤ q := (zero_lt_one.trans hq.1).le
      have hnorm : ‖q • x‖ = q * ‖x‖ := by
        simpa [Real.norm_of_nonneg hq_nonneg] using norm_smul q x
      exact ⟨hq.1, by simpa [hnorm] using hq.2⟩
  simpa [euclideanSobolevUnitBallRadialTailIntegral, hset] using
    real_radial_tail_lintegral_le_dilation_sublevel
      (F := fun q : ℝ ↦ F (q • x)) hx_pos hx_le_one

/--
%%handwave
name:
  Averaging radial dilations over a collar is controlled by collar mass
statement:
  For a nonnegative function \(F\) on the unit ball and a collar
  \(1-\varepsilon<\|x\|<1\), the integral over dilation factors
  \(1<q<(1-\varepsilon)^{-1}\) of the pulled-back subcollar mass is bounded
  by the length of the \(q\)-interval times the \(F\)-mass of the collar.
proof:
  For each fixed \(q>1\), the dilation \(x\mapsto qx\) sends the subcollar
  \(\{1-\varepsilon<\|x\|,\ \|qx\|<1\}\) into the original collar.  Its
  inverse Jacobian factor is at most one because \(q\ge1\).  Integrating this
  fixed-\(q\) bound over the dilation interval gives the claim.
-/
theorem unit_inner_collar_dilation_subcollar_average_lintegral_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {F : H → ℝ≥0∞}
    (hF : AEMeasurable F
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    {ε : ℝ} :
    ∫⁻ q in {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹},
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
          F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume ≤
      (MeasureTheory.volume : Measure ℝ)
        {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹} *
        ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
          F y ∂MeasureTheory.volume := by
  let I : Set ℝ := {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹}
  let S : Set H := {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1}
  let M : ℝ≥0∞ := ∫⁻ y in S, F y ∂MeasureTheory.volume
  have hI_meas : MeasurableSet I := by
    dsimp [I]
    measurability
  have hpoint :
      ∀ q ∈ I,
        (∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
          F (q • x) ∂MeasureTheory.volume) ≤ M := by
    intro q hq
    have hq_pos : 0 < q := lt_trans zero_lt_one hq.1
    have hq_one : 1 ≤ q := hq.1.le
    let J : ℝ≥0∞ := ENNReal.ofReal |(q ^ Module.finrank ℝ H)⁻¹|
    have hraw :
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂MeasureTheory.volume ≤
          J * ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
            F y ∂MeasureTheory.volume := by
      simpa [J] using
        unit_inner_collar_dilation_subcollar_lintegral_le
          (H := H) (F := F) (ε := ε) (q := q) hF hq_pos hq_one
    have hq_nonneg : 0 ≤ q := hq_pos.le
    have hpow_ge_one : (1 : ℝ) ≤ q ^ Module.finrank ℝ H :=
      one_le_pow₀ hq_one
    have hinv_le_one : (q ^ Module.finrank ℝ H)⁻¹ ≤ (1 : ℝ) :=
      inv_le_one_of_one_le₀ hpow_ge_one
    have hinv_nonneg : 0 ≤ (q ^ Module.finrank ℝ H)⁻¹ :=
      inv_nonneg.mpr (pow_nonneg hq_nonneg _)
    have hJ_le_one : J ≤ 1 := by
      dsimp [J]
      rw [abs_of_nonneg hinv_nonneg]
      exact ENNReal.ofReal_le_one.mpr hinv_le_one
    calc
      ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
          F (q • x) ∂MeasureTheory.volume
          ≤ J * ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
              F y ∂MeasureTheory.volume := hraw
      _ = J * M := rfl
      _ ≤ 1 * M := mul_le_mul_left hJ_le_one M
      _ = M := by simp
  calc
    ∫⁻ q in {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹},
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
          F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume
        = ∫⁻ q in I,
            ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
              F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume := rfl
    _ ≤ ∫⁻ _q in I, M ∂MeasureTheory.volume :=
        setLIntegral_mono' hI_meas hpoint
    _ = (MeasureTheory.volume : Measure ℝ) I * M := by
        simp [M, lintegral_const, mul_comm]
    _ = (MeasureTheory.volume : Measure ℝ)
        {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹} *
        ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
          F y ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  The normalized dilation-factor interval has bounded length
statement:
  As \(\varepsilon\downarrow0\),
  \[
    \varepsilon^{-1}\,
      \left|\{q:1<q<(1-\varepsilon)^{-1}\}\right|
  \]
  is eventually bounded by \(2\).
proof:
  The interval length is \((1-\varepsilon)^{-1}-1=\varepsilon/(1-\varepsilon)\).
  Dividing by \(\varepsilon\) gives \((1-\varepsilon)^{-1}\), which is at
  most \(2\) for \(0<\varepsilon<1/2\).
-/
theorem unit_inner_collar_dilation_factor_interval_normalized_volume_le_two :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (1 / ε) *
          (MeasureTheory.volume : Measure ℝ)
            {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹} ≤
        (2 : ℝ≥0∞) := by
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 2 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt_half
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have hden_pos : 0 < (1 : ℝ) - ε := by linarith
  have hden_ne : (1 : ℝ) - ε ≠ 0 := ne_of_gt hden_pos
  have hvol :
      (MeasureTheory.volume : Measure ℝ)
          {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹} =
        ENNReal.ofReal (((1 : ℝ) - ε)⁻¹ - 1) := by
    have hset :
        {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹} =
          Set.Ioo (1 : ℝ) (((1 : ℝ) - ε)⁻¹) := rfl
    rw [hset, Real.volume_Ioo]
  have hscale_nonneg : 0 ≤ (1 / ε : ℝ) :=
    div_nonneg zero_le_one hε_pos.le
  have hreal_eq :
      (1 / ε) * (((1 : ℝ) - ε)⁻¹ - 1) =
        ((1 : ℝ) - ε)⁻¹ := by
    field_simp [hε_ne, hden_ne]
    ring
  have hreal_le : ((1 : ℝ) - ε)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hden_pos]
    nlinarith
  calc
    ENNReal.ofReal (1 / ε) *
        (MeasureTheory.volume : Measure ℝ)
          {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹}
        = ENNReal.ofReal (1 / ε) *
            ENNReal.ofReal (((1 : ℝ) - ε)⁻¹ - 1) := by
              rw [hvol]
    _ = ENNReal.ofReal ((1 / ε) * (((1 : ℝ) - ε)⁻¹ - 1)) := by
          rw [← ENNReal.ofReal_mul hscale_nonneg]
    _ = ENNReal.ofReal (((1 : ℝ) - ε)⁻¹) := by
          rw [hreal_eq]
    _ ≤ ENNReal.ofReal (2 : ℝ) :=
          ENNReal.ofReal_le_ofReal hreal_le
    _ = (2 : ℝ≥0∞) := by norm_num

/--
%%handwave
name:
  Integrating pointwise radial tails gives an \(x\)-first dilation average
statement:
  For all sufficiently small positive \(\varepsilon\), the collar integral of
  the radial tail is bounded by the \(x\)-first iterated integral over
  dilation factors \(1<q<(1-\varepsilon)^{-1}\) satisfying
  \(\|qx\|<1\).
proof:
  Apply the pointwise one-dimensional change of variables on each radial
  segment.  If \(x\) lies in the collar and \(q>1\) satisfies
  \(\|qx\|<1\), then \(q<(1-\varepsilon)^{-1}\), so the pointwise
  dilation-factor domain is contained in the displayed interval.
-/
theorem euclideanSobolev_unit_ball_radial_tailIntegral_collar_le_xfirst_dilation
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {F : H → ℝ≥0∞} :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          euclideanSobolevUnitBallRadialTailIntegral F x
          ∂MeasureTheory.volume ≤
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          ∫⁻ q in {q : ℝ |
              1 < q ∧ q < ((1 : ℝ) - ε)⁻¹ ∧ ‖q • x‖ < 1},
          F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt_one
  let S : Set H := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1}
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    measurability
  refine setLIntegral_mono' hS_meas ?_
  intro x hx
  have hx_pos : 0 < ‖x‖ := by
    have hinner_pos : 0 < (1 : ℝ) - ε := by linarith
    exact lt_trans hinner_pos hx.1
  have hx_le_one : ‖x‖ ≤ 1 := hx.2.le
  have htail :
      euclideanSobolevUnitBallRadialTailIntegral F x ≤
        ∫⁻ q in {q : ℝ | 1 < q ∧ ‖q • x‖ < 1},
          F (q • x) ∂MeasureTheory.volume :=
    euclideanSobolev_unit_ball_radial_tailIntegral_le_dilation_sublevel
      (F := F) (x := x) hx_pos hx_le_one
  have hsubset :
      {q : ℝ | 1 < q ∧ ‖q • x‖ < 1} ⊆
        {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹ ∧ ‖q • x‖ < 1} := by
    intro q hq
    have hq_pos : 0 < q := zero_lt_one.trans hq.1
    have hq_nonneg : 0 ≤ q := hq_pos.le
    have hden_pos : 0 < (1 : ℝ) - ε := by linarith
    have hnorm : ‖q • x‖ = q * ‖x‖ := by
      simpa [Real.norm_of_nonneg hq_nonneg] using norm_smul q x
    have hmul_lt : q * ((1 : ℝ) - ε) < 1 := by
      calc
        q * ((1 : ℝ) - ε) < q * ‖x‖ :=
          mul_lt_mul_of_pos_left hx.1 hq_pos
        _ = ‖q • x‖ := hnorm.symm
        _ < 1 := hq.2
    have hq_lt_inv : q < ((1 : ℝ) - ε)⁻¹ := by
      rw [← one_div]
      exact (lt_div_iff₀ hden_pos).2 hmul_lt
    exact ⟨hq.1, hq_lt_inv, hq.2⟩
  exact htail.trans (lintegral_mono_set hsubset)

/--
%%handwave
name:
  The dilation average can be integrated in either order for measurable data
statement:
  If \(F\) is measurable, then the \(x\)-first integral over the inner collar
  and the admissible dilation factors is bounded by the corresponding
  \(q\)-first integral.
proof:
  Apply Tonelli's theorem to the measurable nonnegative function
  \((x,q)\mapsto F(qx)\), restricted to the set
  \(1-\varepsilon<\|x\|<1\), \(1<q<(1-\varepsilon)^{-1}\), and
  \(\|qx\|<1\).  On the \(q\)-first side, the condition \(\|x\|<1\) is
  redundant because \(q>1\) and \(\|qx\|<1\).
-/
theorem euclideanSobolev_unit_ball_radial_tailIntegral_xfirst_dilation_le_qfirst_of_measurable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {F : H → ℝ≥0∞} (hF : Measurable F) {ε : ℝ} :
      (∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          ∫⁻ q in {q : ℝ |
              1 < q ∧ q < ((1 : ℝ) - ε)⁻¹ ∧ ‖q • x‖ < 1},
            F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume) ≤
        ∫⁻ q in {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹},
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  classical
  let μH : Measure H := MeasureTheory.volume
  let μR : Measure ℝ := MeasureTheory.volume
  let S : Set H := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1}
  let I : Set ℝ := {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹}
  let A : Set (H × ℝ) :=
    {p : H × ℝ | p.1 ∈ S ∧ p.2 ∈ I ∧ ‖p.2 • p.1‖ < 1}
  let G : H → ℝ → ℝ≥0∞ :=
    fun x q ↦ A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q)
  have hA_meas : MeasurableSet A := by
    dsimp [A, S, I]
    measurability
  have hsmul_cont : Continuous (fun p : H × ℝ ↦ p.2 • p.1) :=
    continuous_snd.smul continuous_fst
  have hbase_meas :
      Measurable (fun p : H × ℝ ↦ F (p.2 • p.1)) :=
    hF.comp hsmul_cont.measurable
  have hG_ae : AEMeasurable (Function.uncurry G) (μH.prod μR) := by
    simpa [G, Function.uncurry] using
      (hbase_meas.indicator hA_meas).aemeasurable
  have hswap :
      (∫⁻ x, ∫⁻ q, G x q ∂μR ∂μH) =
        ∫⁻ q, ∫⁻ x, G x q ∂μH ∂μR := by
    exact MeasureTheory.lintegral_lintegral_swap
      (μ := μH) (ν := μR) (f := G) hG_ae
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    measurability
  have hI_meas : MeasurableSet I := by
    dsimp [I]
    measurability
  have hleft_le :
      (∫⁻ x in S,
          ∫⁻ q in {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1},
            F (q • x) ∂μR ∂μH) ≤
        ∫⁻ x, ∫⁻ q, G x q ∂μR ∂μH := by
    rw [← lintegral_indicator hS_meas]
    refine lintegral_mono fun x ↦ ?_
    change S.indicator
        (fun x : H ↦
          ∫⁻ q in {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1},
            F (q • x) ∂μR) x ≤
      ∫⁻ q, G x q ∂μR
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      have hQ_meas : MeasurableSet {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1} := by
        have hnorm_open : IsOpen {q : ℝ | ‖q • x‖ < 1} := by
          exact isOpen_lt
            ((continuous_id.smul continuous_const).norm)
            continuous_const
        exact hI_meas.inter hnorm_open.measurableSet
      rw [← lintegral_indicator hQ_meas]
      refine lintegral_mono fun q ↦ ?_
      by_cases hq : q ∈ I ∧ ‖q • x‖ < 1
      · have hpA : (x, q) ∈ A := ⟨hx, hq.1, hq.2⟩
        change
          ({q : ℝ | q ∈ I ∧ ‖q • x‖ < 1}).indicator
              (fun q : ℝ ↦ F (q • x)) q ≤
            A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q)
        rw [Set.indicator_of_mem
          (s := {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1}) hq]
        rw [Set.indicator_of_mem hpA]
      · rw [Set.indicator_of_notMem
          (s := {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1}) hq]
        exact zero_le
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hright_le :
      (∫⁻ q, ∫⁻ x, G x q ∂μH ∂μR) ≤
        ∫⁻ q in I,
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂μH ∂μR := by
    rw [← lintegral_indicator hI_meas]
    refine lintegral_mono fun q ↦ ?_
    change (∫⁻ x, G x q ∂μH) ≤
      I.indicator
        (fun q : ℝ ↦
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂μH) q
    by_cases hqI : q ∈ I
    · rw [Set.indicator_of_mem hqI]
      have hD_meas :
          MeasurableSet {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1} := by
        have hinner_open : IsOpen {x : H | (1 : ℝ) - ε < ‖x‖} :=
          isOpen_lt continuous_const continuous_norm
        have hdil_open : IsOpen {x : H | ‖q • x‖ < 1} := by
          exact isOpen_lt
            ((continuous_const.smul continuous_id).norm)
            continuous_const
        exact (hinner_open.inter hdil_open).measurableSet
      rw [← lintegral_indicator hD_meas]
      refine lintegral_mono fun x ↦ ?_
      by_cases hxA : (x, q) ∈ A
      · have hxD :
            x ∈ {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1} :=
          ⟨hxA.1.1, hxA.2.2⟩
        change
          A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q) ≤
            ({x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}).indicator
              (fun x : H ↦ F (q • x)) x
        rw [Set.indicator_of_mem hxA]
        rw [Set.indicator_of_mem
          (s := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}) hxD]
      · change
          A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q) ≤
            ({x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}).indicator
              (fun x : H ↦ F (q • x)) x
        rw [Set.indicator_of_notMem hxA]
        exact zero_le
    · rw [Set.indicator_of_notMem hqI]
      rw [← lintegral_zero]
      refine lintegral_mono fun x ↦ ?_
      have hxA : (x, q) ∉ A := by
        intro hp
        exact hqI hp.2.1
      change A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q) ≤ 0
      rw [Set.indicator_of_notMem hxA]
  calc
    (∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
        ∫⁻ q in {q : ℝ |
            1 < q ∧ q < ((1 : ℝ) - ε)⁻¹ ∧ ‖q • x‖ < 1},
          F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume)
          = ∫⁻ x in S,
              ∫⁻ q in {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1},
                F (q • x) ∂μR ∂μH := by
              simp [S, I, μH, μR, and_assoc]
    _ ≤ ∫⁻ x, ∫⁻ q, G x q ∂μR ∂μH := hleft_le
    _ = ∫⁻ q, ∫⁻ x, G x q ∂μH ∂μR := hswap
    _ ≤ ∫⁻ q in I,
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂μH ∂μR := hright_le
    _ = ∫⁻ q in {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹},
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
          simp [I, μH, μR]

/--
%%handwave
name:
  The \(x\)-first radial dilation average is bounded by the \(q\)-first one
statement:
  For all sufficiently small positive \(\varepsilon\), the \(x\)-first
  iterated integral over pairs \((x,q)\) with \(x\) in the inner collar,
  \(1<q<(1-\varepsilon)^{-1}\), and \(\|qx\|<1\), is bounded by the
  corresponding \(q\)-first integral.
proof:
  This is Tonelli's theorem for the nonnegative function
  \((x,q)\mapsto F(qx)\) on the measurable subset cut out by those three
  inequalities.  The final \(x\)-section can be written as
  \(\{x:1-\varepsilon<\|x\|,\ \|qx\|<1\}\), since \(q>1\) and
  \(\|qx\|<1\) imply \(\|x\|<1\).
-/
theorem euclideanSobolev_unit_ball_radial_tailIntegral_xfirst_dilation_le_qfirst
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {F : H → ℝ≥0∞}
    (hF : AEMeasurable F
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            ∫⁻ q in {q : ℝ |
                1 < q ∧ q < ((1 : ℝ) - ε)⁻¹ ∧ ‖q • x‖ < 1},
              F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume) ≤
          ∫⁻ q in {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹},
            ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
              F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  refine Filter.Eventually.of_forall fun ε ↦ ?_
  classical
  let μH : Measure H := MeasureTheory.volume
  let μR : Measure ℝ := MeasureTheory.volume
  let S : Set H := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1}
  let I : Set ℝ := {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹}
  let A : Set (H × ℝ) :=
    {p : H × ℝ | p.1 ∈ S ∧ p.2 ∈ I ∧ ‖p.2 • p.1‖ < 1}
  let G : H → ℝ → ℝ≥0∞ :=
    fun x q ↦ A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q)
  have hA_meas : MeasurableSet A := by
    dsimp [A, S, I]
    measurability
  have hcomp_ae :
      AEMeasurable (fun p : H × ℝ ↦ F (p.2 • p.1))
        ((μH.prod μR).restrict A) := by
    have hqmp :
        Measure.QuasiMeasurePreserving
          (fun p : H × ℝ ↦ p.2 • p.1)
          ((μH.prod μR).restrict A)
          (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
      simpa [μH, μR, S, I, A, and_assoc] using
        unit_inner_collar_dilation_admissible_full_product_quasiMeasurePreserving
          (H := H) (ε := ε)
    exact hF.comp_quasiMeasurePreserving hqmp
  have hG_ae : AEMeasurable (Function.uncurry G) (μH.prod μR) := by
    have hindicator :
        AEMeasurable
          (A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)))
          (μH.prod μR) :=
      (aemeasurable_indicator_iff (μ := μH.prod μR) hA_meas).2 hcomp_ae
    simpa [G, Function.uncurry] using hindicator
  have hswap :
      (∫⁻ x, ∫⁻ q, G x q ∂μR ∂μH) =
        ∫⁻ q, ∫⁻ x, G x q ∂μH ∂μR := by
    exact MeasureTheory.lintegral_lintegral_swap
      (μ := μH) (ν := μR) (f := G) hG_ae
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    measurability
  have hI_meas : MeasurableSet I := by
    dsimp [I]
    measurability
  have hleft_le :
      (∫⁻ x in S,
          ∫⁻ q in {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1},
            F (q • x) ∂μR ∂μH) ≤
        ∫⁻ x, ∫⁻ q, G x q ∂μR ∂μH := by
    rw [← lintegral_indicator hS_meas]
    refine lintegral_mono fun x ↦ ?_
    change S.indicator
        (fun x : H ↦
          ∫⁻ q in {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1},
            F (q • x) ∂μR) x ≤
      ∫⁻ q, G x q ∂μR
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      have hQ_meas : MeasurableSet {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1} := by
        have hnorm_open : IsOpen {q : ℝ | ‖q • x‖ < 1} := by
          exact isOpen_lt
            ((continuous_id.smul continuous_const).norm)
            continuous_const
        exact hI_meas.inter hnorm_open.measurableSet
      rw [← lintegral_indicator hQ_meas]
      refine lintegral_mono fun q ↦ ?_
      by_cases hq : q ∈ I ∧ ‖q • x‖ < 1
      · have hpA : (x, q) ∈ A := ⟨hx, hq.1, hq.2⟩
        change
          ({q : ℝ | q ∈ I ∧ ‖q • x‖ < 1}).indicator
              (fun q : ℝ ↦ F (q • x)) q ≤
            A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q)
        rw [Set.indicator_of_mem
          (s := {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1}) hq]
        rw [Set.indicator_of_mem hpA]
      · rw [Set.indicator_of_notMem
          (s := {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1}) hq]
        exact zero_le
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hright_le :
      (∫⁻ q, ∫⁻ x, G x q ∂μH ∂μR) ≤
        ∫⁻ q in I,
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂μH ∂μR := by
    rw [← lintegral_indicator hI_meas]
    refine lintegral_mono fun q ↦ ?_
    change (∫⁻ x, G x q ∂μH) ≤
      I.indicator
        (fun q : ℝ ↦
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂μH) q
    by_cases hqI : q ∈ I
    · rw [Set.indicator_of_mem hqI]
      have hD_meas :
          MeasurableSet {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1} := by
        have hinner_open : IsOpen {x : H | (1 : ℝ) - ε < ‖x‖} :=
          isOpen_lt continuous_const continuous_norm
        have hdil_open : IsOpen {x : H | ‖q • x‖ < 1} := by
          exact isOpen_lt
            ((continuous_const.smul continuous_id).norm)
            continuous_const
        exact (hinner_open.inter hdil_open).measurableSet
      rw [← lintegral_indicator hD_meas]
      refine lintegral_mono fun x ↦ ?_
      by_cases hxA : (x, q) ∈ A
      · have hxD :
            x ∈ {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1} :=
          ⟨hxA.1.1, hxA.2.2⟩
        change
          A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q) ≤
            ({x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}).indicator
              (fun x : H ↦ F (q • x)) x
        rw [Set.indicator_of_mem hxA]
        rw [Set.indicator_of_mem
          (s := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}) hxD]
      · change
          A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q) ≤
            ({x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1}).indicator
              (fun x : H ↦ F (q • x)) x
        rw [Set.indicator_of_notMem hxA]
        exact zero_le
    · rw [Set.indicator_of_notMem hqI]
      rw [← lintegral_zero]
      refine lintegral_mono fun x ↦ ?_
      have hxA : (x, q) ∉ A := by
        intro hp
        exact hqI hp.2.1
      change A.indicator (fun p : H × ℝ ↦ F (p.2 • p.1)) (x, q) ≤ 0
      rw [Set.indicator_of_notMem hxA]
  calc
    (∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
        ∫⁻ q in {q : ℝ |
            1 < q ∧ q < ((1 : ℝ) - ε)⁻¹ ∧ ‖q • x‖ < 1},
          F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume)
          = ∫⁻ x in S,
              ∫⁻ q in {q : ℝ | q ∈ I ∧ ‖q • x‖ < 1},
                F (q • x) ∂μR ∂μH := by
              simp [S, I, μH, μR, and_assoc]
    _ ≤ ∫⁻ x, ∫⁻ q, G x q ∂μR ∂μH := hleft_le
    _ = ∫⁻ q, ∫⁻ x, G x q ∂μH ∂μR := hswap
    _ ≤ ∫⁻ q in I,
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂μH ∂μR := hright_le
    _ = ∫⁻ q in {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹},
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
          simp [I, μH, μR]

/--
%%handwave
name:
  Radial tail collars convert to dilation-factor averages
statement:
  For almost every point in a sufficiently thin inner collar, the radial tail
  integral can be integrated first over the dilation factor \(q=t/\|x\|\).
  Consequently,
  \[
    \int_{1-\varepsilon<\|x\|<1}
      \int_{\|x\|}^1 F(t x/\|x\|)\,dt\,dx
    \le
    \int_{1<q<(1-\varepsilon)^{-1}}
      \int_{\{1-\varepsilon<\|x\|,\ \|qx\|<1\}} F(qx)\,dx\,dq .
  \]
proof:
  Apply the one-dimensional change of variables along each radial segment,
  keeping the condition \(\|qx\|<1\), and then use Tonelli's theorem to swap
  the \(x\)- and \(q\)-integrals.  The almost-everywhere measurability of
  \(F\) is transported through these restricted dilation maps by the same
  null-set estimates used for the fixed-\(q\) collar bound.
-/
theorem euclideanSobolev_unit_ball_radial_tailIntegral_collar_le_dilation_average
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {F : H → ℝ≥0∞}
    (_hF : AEMeasurable F
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          euclideanSobolevUnitBallRadialTailIntegral F x
          ∂MeasureTheory.volume ≤
        ∫⁻ q in {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹},
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
            F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  filter_upwards
    [euclideanSobolev_unit_ball_radial_tailIntegral_collar_le_xfirst_dilation
      (H := H) (F := F),
     euclideanSobolev_unit_ball_radial_tailIntegral_xfirst_dilation_le_qfirst
      (H := H) (F := F) _hF] with ε hpoint hswap
  exact hpoint.trans hswap

/--
%%handwave
name:
  Radial tail integrals are controlled by ordinary collar mass
statement:
  There is a finite constant \(C\), depending only on the ambient Euclidean
  space, such that for all sufficiently small positive \(\varepsilon\),
  \[
    \frac1\varepsilon
      \int_{1-\varepsilon<\|x\|<1}
        \int_{\|x\|}^1 F(t x/\|x\|)\,dt\,dx
      \le
    C \int_{1-\varepsilon<\|y\|<1} F(y)\,dy .
  \]
proof:
  Put \(t=q\|x\|\).  Since \(\|x\|<1\), the radial tail is bounded by the
  \(q\)-average over \(1<q<(1-\varepsilon)^{-1}\) of \(F(qx)\), restricted to
  the subcollar where \(q\|x\|<1\).  For each such \(q\), the linear dilation
  \(x\mapsto qx\) sends that subcollar into
  \(1-\varepsilon<\|y\|<1\), and its Haar-measure distortion is uniformly
  bounded for \(q\) near \(1\).  Fubini in \((q,x)\) and the fact that the
  \(q\)-interval has length \(O(\varepsilon)\) give the estimate.
-/
theorem euclideanSobolev_unit_ball_radial_tailIntegral_normalized_collar_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {F : H → ℝ≥0∞}
    (hF : AEMeasurable F
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            euclideanSobolevUnitBallRadialTailIntegral F x
            ∂MeasureTheory.volume ≤
          C *
            ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
              F y ∂MeasureTheory.volume := by
  refine ⟨(2 : ℝ≥0∞), by norm_num, ?_⟩
  have hconvert :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            euclideanSobolevUnitBallRadialTailIntegral F x
            ∂MeasureTheory.volume ≤
          ∫⁻ q in {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹},
            ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
              F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume :=
    euclideanSobolev_unit_ball_radial_tailIntegral_collar_le_dilation_average
      (H := H) (F := F) hF
  have hfactor :=
    unit_inner_collar_dilation_factor_interval_normalized_volume_le_two
  filter_upwards [hconvert, hfactor] with ε hconvertε hfactorε
  let I : Set ℝ := {q : ℝ | 1 < q ∧ q < ((1 : ℝ) - ε)⁻¹}
  let S : Set H := {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1}
  let Q : ℝ≥0∞ :=
    ∫⁻ q in I,
      ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖q • x‖ < 1},
        F (q • x) ∂MeasureTheory.volume ∂MeasureTheory.volume
  let M : ℝ≥0∞ := ∫⁻ y in S, F y ∂MeasureTheory.volume
  have haverage : Q ≤ (MeasureTheory.volume : Measure ℝ) I * M := by
    simpa [Q, I, S, M] using
      unit_inner_collar_dilation_subcollar_average_lintegral_le
        (H := H) (F := F) (ε := ε) hF
  have hconvertε' :
      ∫⁻ x in S,
          euclideanSobolevUnitBallRadialTailIntegral F x
          ∂MeasureTheory.volume ≤ Q := by
    simpa [S, Q, I] using hconvertε
  have hfactorε' :
      ENNReal.ofReal (1 / ε) *
          (MeasureTheory.volume : Measure ℝ) I ≤
        (2 : ℝ≥0∞) := by
    simpa [I] using hfactorε
  calc
    ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          euclideanSobolevUnitBallRadialTailIntegral F x
          ∂MeasureTheory.volume
        = ENNReal.ofReal (1 / ε) *
            ∫⁻ x in S,
              euclideanSobolevUnitBallRadialTailIntegral F x
              ∂MeasureTheory.volume := rfl
    _ ≤ ENNReal.ofReal (1 / ε) * Q :=
        mul_le_mul_right hconvertε' _
    _ ≤ ENNReal.ofReal (1 / ε) *
        ((MeasureTheory.volume : Measure ℝ) I * M) :=
        mul_le_mul_right haverage _
    _ = (ENNReal.ofReal (1 / ε) *
          (MeasureTheory.volume : Measure ℝ) I) * M := by
        ac_rfl
    _ ≤ (2 : ℝ≥0∞) * M :=
        mul_le_mul_left hfactorε' M
    _ =
        (2 : ℝ≥0∞) *
          ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
            F y ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Radial derivative tail majorants are controlled by ordinary gradient mass
statement:
  There is a finite constant \(C\), depending only on the ambient Euclidean
  space, such that for all sufficiently small positive \(\varepsilon\),
  \[
    \frac1\varepsilon
      \int_{1-\varepsilon<\|x\|<1}
        R_{Dw}(x)\,dx
      \le
    C \int_{1-\varepsilon<\|y\|<1} |Dw(y)|\,dy ,
  \]
  where \(R_{Dw}\) is the radial derivative tail majorant.
proof:
  Bound the directional derivative in the radial tail by the operator norm of
  \(Dw\), then apply the radial tail integral estimate to \(F=|Dw|\).
-/
theorem euclideanSobolev_unit_ball_radial_tail_majorant_normalized_collar_le_gradient_collar
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {dw : H → H →L[ℝ] ℝ}
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            euclideanSobolevUnitBallRadialTailMajorant dw x
            ∂MeasureTheory.volume ≤
          C *
            ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
              ENNReal.ofReal ‖dw y‖ ∂MeasureTheory.volume := by
  let F : H → ℝ≥0∞ := fun y : H ↦ ENNReal.ofReal ‖dw y‖
  have hF : AEMeasurable F
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
    dsimp [F]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      _hdw.aestronglyMeasurable.aemeasurable.norm
  rcases
    euclideanSobolev_unit_ball_radial_tailIntegral_normalized_collar_le
      (H := H) (F := F) hF with
    ⟨C, hC_ne_top, hgeom⟩
  refine ⟨C, hC_ne_top, ?_⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hgeom, hsmall] with ε hgeomε hε_lt
  let S : Set H := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1}
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    measurability
  have htail_le :
      (∫⁻ x in S,
          euclideanSobolevUnitBallRadialTailMajorant dw x
          ∂MeasureTheory.volume) ≤
        ∫⁻ x in S,
          euclideanSobolevUnitBallRadialTailIntegral F x
          ∂MeasureTheory.volume := by
    refine setLIntegral_mono' hS_meas ?_
    intro x hx
    have hx_pos : 0 < ‖x‖ := by
      have hinner_pos : 0 < (1 : ℝ) - ε := by linarith
      exact lt_trans hinner_pos hx.1
    simpa [F] using
      euclideanSobolev_unit_ball_radial_tailMajorant_le_norm_tailIntegral
        (dw := dw) (x := x) hx_pos
  calc
    ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
          euclideanSobolevUnitBallRadialTailMajorant dw x
          ∂MeasureTheory.volume
        = ENNReal.ofReal (1 / ε) *
            ∫⁻ x in S,
              euclideanSobolevUnitBallRadialTailMajorant dw x
              ∂MeasureTheory.volume := rfl
    _ ≤ ENNReal.ofReal (1 / ε) *
          ∫⁻ x in S,
            euclideanSobolevUnitBallRadialTailIntegral F x
            ∂MeasureTheory.volume :=
          mul_le_mul_right htail_le _
    _ ≤ C *
          ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
            F y ∂MeasureTheory.volume := by
          simpa [S] using hgeomε
    _ = C *
          ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
            ENNReal.ofReal ‖dw y‖ ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Radial tail majorants have vanishing normalized collar mass
statement:
  If \(Dw\) is square-integrable in the unit ball, then the normalized
  \(L^1\)-mass of its radial tail majorant over the inner collars tends to
  zero:
  \[
    \frac1\varepsilon
      \int_{1-\varepsilon<\|x\|<1}
        \int_{\|x\|}^1
          |Dw(t x/\|x\|)(x/\|x\|)|\,dt\,dx
      \to 0 .
  \]
proof:
  Bound the normalized tail-majorant mass by a fixed finite multiple of the
  ordinary \(L^1\)-mass of \(Dw\) on the same collar, then use the absolute
  continuity of the \(L^1\)-integral for \(Dw\in L^2\) on the finite-measure
  unit ball.
-/
theorem euclideanSobolev_unit_ball_radial_tail_majorant_normalized_collar_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {dw : H → H →L[ℝ] ℝ}
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            euclideanSobolevUnitBallRadialTailMajorant dw x
            ∂MeasureTheory.volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  rcases
    euclideanSobolev_unit_ball_radial_tail_majorant_normalized_collar_le_gradient_collar
      (H := H) (dw := dw) _hdw with
    ⟨C, hC_ne_top, hbound⟩
  have hmass :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
            ENNReal.ofReal ‖dw y‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    unit_ball_l1_inner_collar_mass_tendsto_zero _hdw
  have hscaled :
      Filter.Tendsto
        (fun ε : ℝ ↦
          C *
            ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
              ENNReal.ofReal ‖dw y‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have hmul := ENNReal.Tendsto.const_mul hmass (Or.inr hC_ne_top)
    simpa using hmul
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hscaled
      (Filter.Eventually.of_forall fun _ε ↦ zero_le)
      hbound

/--
%%handwave
name:
  Radial endpoint trace data for unit-ball Sobolev functions
statement:
  A scalar \(W^{1,2}\) function on the unit ball has a measurable radial
  endpoint representative \(\tau\) and a nonnegative collar majorant \(R\)
  such that
  \[
    |w(x)-\tau(x/\|x\|)|\le R(x)
  \]
  for almost every point in every sufficiently thin inner collar, and the
  normalized collar integrals of \(R\) tend to zero.
proof:
  Combine
  [the radial ACL endpoint representative with the radial tail bound](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_acl_trace_tail_bound)
  and
  [the vanishing normalized collar mass of the radial tail majorant](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_tail_majorant_normalized_collar_tendsto_zero).
-/
theorem euclideanSobolev_unit_ball_radial_l1_trace_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ (τ : H → ℝ) (R : H → ℝ≥0∞),
      Measurable τ ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          ∀ᵐ x ∂MeasureTheory.volume.restrict
              {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            ENNReal.ofReal
              ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖ ≤ R x) ∧
        Filter.Tendsto
          (fun ε : ℝ ↦
            ENNReal.ofReal (1 / ε) *
              ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
                R x ∂MeasureTheory.volume)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  rcases
    euclideanSobolev_unit_ball_radial_acl_trace_tail_bound
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hbound⟩
  refine
    ⟨τ, euclideanSobolevUnitBallRadialTailMajorant dw,
      hτ_meas, hbound, ?_⟩
  exact
    euclideanSobolev_unit_ball_radial_tail_majorant_normalized_collar_tendsto_zero
      _hdw

/--
%%handwave
name:
  Interior \(L^1\) trace for Sobolev functions on the unit ball
statement:
  A scalar \(W^{1,2}\) function on the unit ball has a measurable \(L^1\)
  trace representative on the unit sphere from the inside.
proof:
  Apply
  [the radial endpoint representative admits a vanishing normalized collar majorant](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_l1_trace_bound).
  Then use
  [a vanishing collar majorant gives an inside \(L^1\) trace](lean:JJMath.Uniformization.hasL1TraceFromInsideSphere_one_of_eventually_ae_bound).
-/
theorem euclideanSobolev_unit_ball_has_l1_trace_from_inside_core
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        HasL1TraceFromInsideSphere (H := H) 1 w τ := by
  rcases
    euclideanSobolev_unit_ball_radial_l1_trace_bound
      _hweak _hw _hdw with
    ⟨τ, R, hτ_meas, hbound, hR⟩
  exact
    ⟨τ, hτ_meas,
      hasL1TraceFromInsideSphere_one_of_eventually_ae_bound
        (H := H) (w := w) (τ := τ) (R := R) hbound hR⟩

/--
%%handwave
name:
  Interior \(L^1\) trace for unit-ball Sobolev functions
statement:
  A scalar \(W^{1,2}\) function on the unit ball has a measurable \(L^1\)
  trace representative on the unit sphere from the inside.
proof:
  Apply
  [a scalar \(W^{1,2}\) function on the unit ball has an \(L^1\) trace on the unit sphere from the inside](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_has_l1_trace_from_inside_core).
tags:
  milestone
-/
theorem euclideanSobolev_unit_ball_has_l1_trace_from_inside
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        HasL1TraceFromInsideSphere (H := H) 1 w τ := by
  exact
    euclideanSobolev_unit_ball_has_l1_trace_from_inside_core
      _hweak _hw _hdw

end

end Uniformization

end JJMath
