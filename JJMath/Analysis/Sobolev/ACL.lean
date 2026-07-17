import JJMath.Analysis.Sobolev.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# ACL theorem for Euclidean weak Sobolev functions

This file contains the Kinnunen-style absolutely-continuous-on-lines step used
in the Rellich proof.  The hard analytic input is isolated as a smooth
approximation statement; the passage from smooth approximants to the
fundamental theorem on almost every segment is formalized here.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff Convolution

namespace Uniformization

noncomputable section

open ContinuousLinearMap

/--
%%handwave
name:
  Scalar weak derivative identity used in the ACL proof
statement:
  A scalar function on a Euclidean region has a weak derivative field if the
  integration-by-parts identity holds against every smooth compactly supported
  scalar test and every constant direction.
-/
abbrev KinnunenWeakDerivativeOnEuclideanRegionScalar {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (Ω : Set H) (u : H → ℝ) (du : H → H →L[ℝ] ℝ) : Prop :=
  ∀ (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v : H),
    Integrable
        (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u z)
        (MeasureTheory.volume.restrict Ω) ∧
      Integrable
        (fun z ↦ φ z • du z v)
        (MeasureTheory.volume.restrict Ω) ∧
        ∫ z in Ω,
            (fderiv ℝ (φ : H → ℝ) z v) • u z ∂MeasureTheory.volume =
          -∫ z in Ω, φ z • du z v ∂MeasureTheory.volume

/--
%%handwave
name:
  Directional weak derivatives are locally integrable on compact sets
statement:
  On every compact subset of an open Euclidean weak-derivative region, each
  directional weak derivative is integrable.
proof:
  Choose a smooth cutoff equal to one on the compact set and supported in the
  open region.  The weak-derivative identity gives integrability of the
  cutoff directional derivative; restricting to the compact set removes the
  cutoff.
-/
theorem kinnunenWeakDerivative_directionalDerivative_integrableOn_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (h : H) :
    Integrable (fun z ↦ du z h) (MeasureTheory.volume.restrict Q) := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hΩ_open hQΩ
  obtain ⟨ψ, hψ_smooth, _hψ_range, hψ_support, hψ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, H)) (n := ⊤)
      (Metric.isOpen_thickening) hQ.isClosed
      (Metric.self_subset_thickening hδ_pos Q)
  have hψ_tsupport_subset_cthickening :
      tsupport ψ ⊆ Metric.cthickening δ Q := by
    rw [tsupport, hψ_support]
    exact Metric.closure_thickening_subset_cthickening δ Q
  let φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := ψ
      smooth := hψ_smooth.contDiff
      support_subset := hψ_tsupport_subset_cthickening.trans hδΩ
      compact_support := by
        exact IsCompact.of_isClosed_subset (hQ.cthickening)
          (isClosed_tsupport ψ) hψ_tsupport_subset_cthickening }
  have hcutoff_int : Integrable (fun z ↦ φ z • du z h)
      (MeasureTheory.volume.restrict Ω) :=
    (hweak φ h).2.1
  have hcutoff_int_Q : Integrable (fun z ↦ φ z • du z h)
      (MeasureTheory.volume.restrict Q) := by
    have hres := hcutoff_int.restrict (s := Q)
    simpa [Measure.restrict_restrict_of_subset hQΩ] using hres
  have hcutoff_eq :
      (fun z ↦ φ z • du z h) =ᵐ[MeasureTheory.volume.restrict Q]
        fun z ↦ du z h := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      have hψ_eq_one : ψ z = 1 := (hψ_one z).1 hzQ
      simp [φ, hψ_eq_one]
  exact hcutoff_int_Q.congr hcutoff_eq

/--
%%handwave
name:
  Directional weak derivatives are locally integrable
statement:
  On an open Euclidean weak-derivative region, each directional weak
  derivative is locally integrable.
proof:
  Local integrability on an open set is tested on compact subsets.  Apply the
  compact integrability theorem.
-/
theorem kinnunenWeakDerivative_directionalDerivative_locallyIntegrableOn
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (h : H) :
    LocallyIntegrableOn (fun z ↦ du z h) Ω
      (MeasureTheory.volume : Measure H) := by
  rw [locallyIntegrableOn_iff hΩ_open.isLocallyClosed]
  intro K hKΩ hK
  exact kinnunenWeakDerivative_directionalDerivative_integrableOn_compact
    hK hKΩ hΩ_open hweak h

/--
%%handwave
name:
  Weak Sobolev functions are locally integrable on compact sets
statement:
  On every compact subset of an open Euclidean weak-derivative region, a
  scalar weak Sobolev function is integrable, provided one tests the weak
  derivative identity in a nonzero direction.
proof:
  Choose a continuous linear coordinate \(\ell\) with \(\ell(h)=1\).  A
  cutoff times \(\ell\) has directional derivative equal to one on the
  compact set.  The weak-derivative identity gives integrability of that
  derivative times the function, hence of the function itself on the compact
  set.
-/
theorem kinnunenWeakDerivative_function_integrableOn_compact_of_nonzero_direction
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} (hh : h ≠ 0) :
    Integrable u (MeasureTheory.volume.restrict Q) := by
  obtain ⟨L, hLh⟩ := SeparatingDual.exists_eq_one (R := ℝ) hh
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hΩ_open hQΩ
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_ltδ : η < δ := by
    dsimp [η]
    linarith
  have hclosed_eta : IsClosed (Metric.cthickening η Q) :=
    Metric.isClosed_cthickening
  have heta_subset_thickening :
      Metric.cthickening η Q ⊆ Metric.thickening δ Q :=
    Metric.cthickening_subset_thickening' hδ_pos hη_ltδ Q
  obtain ⟨χ, hχ_smooth, _hχ_range, hχ_support, hχ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, H)) (n := ⊤)
      (Metric.isOpen_thickening) hclosed_eta heta_subset_thickening
  have hχ_tsupport_subset_cthickening :
      tsupport χ ⊆ Metric.cthickening δ Q := by
    rw [tsupport, hχ_support]
    exact Metric.closure_thickening_subset_cthickening δ Q
  have hχ_deriv_zero :
      ∀ z ∈ Q, fderiv ℝ χ z = 0 := by
    intro z hzQ
    have hz_thick : z ∈ Metric.thickening η Q :=
      Metric.self_subset_thickening hη_pos Q hzQ
    have hnhds : Metric.thickening η Q ∈ 𝓝 z :=
      Metric.isOpen_thickening.mem_nhds hz_thick
    have hχ_eventually :
        χ =ᶠ[𝓝 z] fun _ : H ↦ (1 : ℝ) := by
      filter_upwards [hnhds] with y hy
      exact (hχ_one y).1 ((Metric.thickening_subset_cthickening η Q) hy)
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hχ_eventually]
    simp
  let φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := fun z : H ↦ χ z * L z
      smooth := by
        exact hχ_smooth.contDiff.mul L.contDiff
      support_subset := by
        exact (tsupport_mul_subset_left (f := χ) (g := fun z : H ↦ L z)).trans
          (hχ_tsupport_subset_cthickening.trans hδΩ)
      compact_support := by
        exact IsCompact.of_isClosed_subset (hQ.cthickening)
          (isClosed_tsupport _) ((tsupport_mul_subset_left
            (f := χ) (g := fun z : H ↦ L z)).trans hχ_tsupport_subset_cthickening) }
  have hφ_deriv_one :
      ∀ z ∈ Q, fderiv ℝ (φ : H → ℝ) z h = 1 := by
    intro z hzQ
    have hχz : χ z = 1 := by
      exact (hχ_one z).1 (Metric.self_subset_cthickening Q hzQ)
    have hχdiff : DifferentiableAt ℝ χ z :=
      (hχ_smooth.contDiff.differentiable (by simp)) z
    have hLdiff : DifferentiableAt ℝ (fun y : H ↦ L y) z :=
      L.isBoundedLinearMap.differentiableAt
    have hLfderiv : fderiv ℝ (fun y : H ↦ L y) z = L :=
      L.isBoundedLinearMap.fderiv
    change fderiv ℝ (fun y : H ↦ χ y * L y) z h = 1
    rw [fderiv_fun_mul hχdiff hLdiff]
    simp [hχz, hχ_deriv_zero z hzQ, hLfderiv, hLh]
  have htest_int : Integrable (fun z ↦ (fderiv ℝ (φ : H → ℝ) z h) • u z)
      (MeasureTheory.volume.restrict Ω) :=
    (hweak φ h).1
  have htest_int_Q : Integrable (fun z ↦ (fderiv ℝ (φ : H → ℝ) z h) • u z)
      (MeasureTheory.volume.restrict Q) := by
    have hres := htest_int.restrict (s := Q)
    simpa [Measure.restrict_restrict_of_subset hQΩ] using hres
  have htest_eq :
      (fun z ↦ (fderiv ℝ (φ : H → ℝ) z h) • u z)
        =ᵐ[MeasureTheory.volume.restrict Q] u := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      simp [hφ_deriv_one z hzQ]
  exact htest_int_Q.congr htest_eq

/--
%%handwave
name:
  Weak Sobolev functions are locally integrable
statement:
  On an open Euclidean weak-derivative region, a scalar weak Sobolev function
  is locally integrable as soon as the weak identity is available in one
  nonzero direction.
proof:
  Local integrability on an open set is tested on compact subsets.  Apply the
  compact theorem in the chosen nonzero direction.
-/
theorem kinnunenWeakDerivative_function_locallyIntegrableOn_of_nonzero_direction
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} (hh : h ≠ 0) :
    LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H) := by
  rw [locallyIntegrableOn_iff hΩ_open.isLocallyClosed]
  intro K hKΩ hK
  exact kinnunenWeakDerivative_function_integrableOn_compact_of_nonzero_direction
    hK hKΩ hΩ_open hweak hh

/--
%%handwave
name:
  Smooth functions satisfy the fundamental theorem on line segments
statement:
  If \(v\) is smooth on a finite-dimensional Euclidean space, then on every
  segment in direction \(h\),
  \[
    v(x+h)-v(x)=\int_0^1 Dv(x+t h)[h]\,dt .
  \]
proof:
  Apply the one-dimensional fundamental theorem of calculus to
  \(t\mapsto v(x+t h)\).  Its derivative is
  \(Dv(x+t h)[h]\) by the chain rule.
-/
theorem contDiff_endpoint_sub_eq_segmentIntegral_fderiv
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {v : H → ℝ} (hv : ContDiff ℝ ∞ v) (z h : H) :
    v (z + h) - v z =
      ∫ t in Set.Icc (0 : ℝ) 1,
        fderiv ℝ v (z + t • h) h ∂MeasureTheory.volume := by
  let γ : ℝ → H := fun t ↦ z + t • h
  let F : ℝ → ℝ := fun t ↦ v (γ t)
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt F (fderiv ℝ v (γ t) h) t := by
    intro t _ht
    have hvd : HasFDerivAt v (fderiv ℝ v (γ t)) (γ t) :=
      ((hv.differentiable (by simp)) (γ t)).hasFDerivAt
    have hγ : HasDerivAt γ h t := by
      simpa [γ] using ((hasDerivAt_id t).smul_const h).const_add z
    simpa [F, γ] using hvd.comp_hasDerivAt t hγ
  have hcont :
      ContinuousOn (fun t ↦ fderiv ℝ v (γ t) h) (Set.uIcc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    exact ((hv.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply
      continuous_const
  have hint :
      IntervalIntegrable (fun t ↦ fderiv ℝ v (γ t) h)
        MeasureTheory.volume (0 : ℝ) 1 :=
    hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at hFTC
  simpa [F, γ, add_comm, add_left_comm, add_assoc] using hFTC.symm

/--
%%handwave
name:
  Smooth approximation data along a fixed direction
statement:
  Smooth approximants to a weak Sobolev function converge at the two endpoints
  of almost every segment, and their directional derivatives converge after
  integration along the segment.
-/
structure ScalarWeakSobolevDirectionalSmoothApproxData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (K : Set H) (u : H → ℝ) (du : H → H →L[ℝ] ℝ) (h : H) where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  endpoint_tendsto :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      Filter.Tendsto
        (fun n : ℕ ↦ approximants n (z + h) - approximants n z)
        Filter.atTop (𝓝 (u (z + h) - u z))
  integral_tendsto :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (approximants n) (z + t • h) h ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • h) h ∂MeasureTheory.volume))

/--
%%handwave
name:
  Smooth approximation data with convergence in measure
statement:
  Smooth approximants to a weak Sobolev function converge in measure after
  taking endpoint differences on the prescribed segments, and their integrated
  directional derivatives converge in measure to the weak directional
  derivative integrated along those segments.
-/
structure ScalarWeakSobolevDirectionalSmoothApproxInMeasureData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (K : Set H) (u : H → ℝ) (du : H → H →L[ℝ] ℝ) (h : H) where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  endpoint_tendstoInMeasure :
    TendstoInMeasure (MeasureTheory.volume.restrict K)
      (fun n z ↦ approximants n (z + h) - approximants n z)
      Filter.atTop
      (fun z ↦ u (z + h) - u z)
  integral_tendstoInMeasure :
    TendstoInMeasure (MeasureTheory.volume.restrict K)
      (fun n z ↦
        ∫ t in Set.Icc (0 : ℝ) 1,
          fderiv ℝ (approximants n) (z + t • h) h ∂MeasureTheory.volume)
      Filter.atTop
      (fun z ↦
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • h) h ∂MeasureTheory.volume)

/--
%%handwave
name:
  Smooth approximation data with \(L^2\) endpoint and segment convergence
statement:
  Smooth approximants to a weak Sobolev function have endpoint differences
  and integrated directional derivatives converging in \(L^2\) on the compact
  set of segment origins.
-/
structure ScalarWeakSobolevDirectionalSmoothApproxL2Data
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (K : Set H) (u : H → ℝ) (du : H → H →L[ℝ] ℝ) (h : H) where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  endpoint_aestronglyMeasurable :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦ approximants n (z + h) - approximants n z)
        (MeasureTheory.volume.restrict K)
  endpoint_limit_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun z ↦ u (z + h) - u z)
      (MeasureTheory.volume.restrict K)
  endpoint_tendsto_l2 :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          ((fun z ↦ approximants n (z + h) - approximants n z) -
            fun z ↦ u (z + h) - u z)
          2 (MeasureTheory.volume.restrict K))
      Filter.atTop (𝓝 0)
  integral_aestronglyMeasurable :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (approximants n) (z + t • h) h ∂MeasureTheory.volume)
        (MeasureTheory.volume.restrict K)
  integral_limit_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun z ↦
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • h) h ∂MeasureTheory.volume)
      (MeasureTheory.volume.restrict K)
  integral_tendsto_l2 :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          ((fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                fderiv ℝ (approximants n) (z + t • h) h ∂MeasureTheory.volume) -
            fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                du (z + t • h) h ∂MeasureTheory.volume)
          2 (MeasureTheory.volume.restrict K))
      Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Local smooth approximation before restricting to segments
statement:
  Smooth functions approximate a scalar weak Sobolev function on the compact
  set \(Q\) in \(L^2\), and their directional derivatives in the fixed
  direction approximate the weak directional derivative in \(L^2(Q)\).
-/
structure ScalarWeakSobolevLocalSmoothApproxDirectionL2Data
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (Q : Set H) (u : H → ℝ) (du : H → H →L[ℝ] ℝ) (h : H) where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  value_aestronglyMeasurable :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦ approximants n z - u z)
        (MeasureTheory.volume.restrict Q)
  value_tendsto_l2 :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm (fun z ↦ approximants n z - u z)
          2 (MeasureTheory.volume.restrict Q))
      Filter.atTop (𝓝 0)
  directionalDerivative_aestronglyMeasurable :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦ fderiv ℝ (approximants n) z h - du z h)
        (MeasureTheory.volume.restrict Q)
  directionalDerivative_tendsto_l2 :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm (fun z ↦ fderiv ℝ (approximants n) z h - du z h)
          2 (MeasureTheory.volume.restrict Q))
      Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Scalar \(L^2\) functions admit smooth approximants for restricted volume
statement:
  Every scalar \(L^2\) function with respect to a restricted Euclidean volume
  measure can be approximated in \(L^2\) by globally smooth compactly
  supported functions.
proof:
  This is the standard smooth density theorem for \(L^p\) functions on
  finite-dimensional Euclidean spaces, applied with \(p=2\) to the restricted
  measure.
-/
theorem memLp_exists_contDiff_tendsto_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q : Set H} {u : H → ℝ}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q)) :
    ∃ v : ℕ → H → ℝ,
      (∀ n : ℕ, ContDiff ℝ ∞ (v n)) ∧
        (∀ n : ℕ,
          AEStronglyMeasurable
            (fun z ↦ v n z - u z)
            (MeasureTheory.volume.restrict Q)) ∧
          Filter.Tendsto
            (fun n : ℕ ↦
              eLpNorm (fun z ↦ v n z - u z)
                2 (MeasureTheory.volume.restrict Q))
            Filter.atTop (𝓝 0) := by
  classical
  let μ : Measure H := MeasureTheory.volume.restrict Q
  have happrox :
      ∀ n : ℕ, ∃ g : H → ℝ,
        HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
          eLpNorm (u - g) 2 μ ≤
            ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
    intro n
    exact MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := μ) (p := (2 : ℝ≥0∞))
      ENNReal.coe_ne_top (by norm_num) hu (by positivity)
  choose v _hv_comp hv_smooth hv_le using happrox
  refine ⟨v, hv_smooth, ?_, ?_⟩
  · intro n
    exact (hv_smooth n).continuous.aestronglyMeasurable.sub
      hu.aestronglyMeasurable
  · have hle :
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ v n z - u z) 2 μ) ≤
            fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
      intro n
      have hle' :
          eLpNorm (v n - u) 2 μ ≤
            ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
        rw [eLpNorm_sub_comm (v n) u 2 μ]
        exact hv_le n
      simpa [Pi.sub_apply] using hle'
    have hupper :
        Filter.Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) + 1)⁻¹))
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have hreal :
          Filter.Tendsto
            (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹))
            Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using ENNReal.tendsto_ofReal hreal
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ ↦ zero_le) hle

/--
%%handwave
name:
  Zero-direction smooth graph approximation
statement:
  In the zero direction, smooth \(L^2\)-approximation of the values already
  gives smooth approximation in the directional graph norm, since both the
  classical and weak zero-direction derivatives vanish.
-/
theorem scalarWeakSobolev_exists_local_smoothApprox_zero_direction_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q)) :
    Nonempty (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du (0 : H)) := by
  rcases memLp_exists_contDiff_tendsto_l2_on_compact (Q := Q) hu with
    ⟨v, hv_smooth, hv_meas, hv_tendsto⟩
  refine
    ⟨{ approximants := v
       smooth := hv_smooth
       value_aestronglyMeasurable := hv_meas
       value_tendsto_l2 := hv_tendsto
       directionalDerivative_aestronglyMeasurable := ?_
       directionalDerivative_tendsto_l2 := ?_ }⟩
  · intro n
    simpa using
      (aestronglyMeasurable_const :
        AEStronglyMeasurable
          (fun _ : H ↦ (0 : ℝ))
          (MeasureTheory.volume.restrict Q))
  · simp

/--
%%handwave
name:
  Smooth graph approximation on the empty set
statement:
  On the empty set, any smooth sequence approximates a weak Sobolev function
  in the directional graph norm, because all restricted \(L^2\) seminorms are
  zero.
-/
theorem scalarWeakSobolev_exists_local_smoothApprox_empty_l2
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H} :
    Nonempty
      (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data
        (∅ : Set H) u du h) := by
  refine
    ⟨{ approximants := fun _ ↦ 0
       smooth := fun _ ↦ contDiff_const
       value_aestronglyMeasurable := ?_
       value_tendsto_l2 := ?_
       directionalDerivative_aestronglyMeasurable := ?_
       directionalDerivative_tendsto_l2 := ?_ }⟩
  · intro n
    simp
  · simp
  · intro n
    simp
  · simp

/--
%%handwave
name:
  Cutoff derivative for a localized scalar weak Sobolev function
statement:
  If a weak Sobolev function \(u\) has weak derivative \(du\), then the
  expected directional derivative field of \(\chi u\) is
  \[
    d(\chi u)=\chi\,du+u\,d\chi .
  \]
-/
noncomputable def scalarWeakSobolevCutoffDerivative
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (χ u : H → ℝ) (du : H → H →L[ℝ] ℝ) :
    H → H →L[ℝ] ℝ :=
  fun z ↦ χ z • du z + u z • fderiv ℝ χ z

@[simp]
theorem scalarWeakSobolevCutoffDerivative_apply
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (χ u : H → ℝ) (du : H → H →L[ℝ] ℝ) (z v : H) :
    scalarWeakSobolevCutoffDerivative χ u du z v =
      χ z * du z v + u z * fderiv ℝ χ z v := by
  simp [scalarWeakSobolevCutoffDerivative]

/--
%%handwave
name:
  Smooth cutoff around a compact set
statement:
  A smooth cutoff for \(Q\subset\Omega\) is a smooth function equal to one on
  \(Q\), with derivative zero on \(Q\), and with compact support contained in
  \(\Omega\).
-/
structure ScalarWeakSobolevCutoff {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Q Ω : Set H) where
  toFun : H → ℝ
  smooth : ContDiff ℝ ∞ toFun
  support_subset : tsupport toFun ⊆ Ω
  compact_support : IsCompact (tsupport toFun)
  eq_one_on : ∀ z ∈ Q, toFun z = 1
  fderiv_eq_zero_on : ∀ z ∈ Q, fderiv ℝ toFun z = 0

namespace ScalarWeakSobolevCutoff

instance {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Q Ω : Set H} : CoeFun (ScalarWeakSobolevCutoff Q Ω)
      (fun _ ↦ H → ℝ) where
  coe χ := χ.toFun

/--
%%handwave
name:
  Cutoff derivative agrees with the original derivative on the compact set
statement:
  Since the cutoff is one and its differential is zero on \(Q\), the product
  derivative \(\chi\,du+u\,d\chi\) agrees with \(du\) on \(Q\).
-/
theorem cutoffDerivative_eq_on
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Q Ω : Set H} (χ : ScalarWeakSobolevCutoff Q Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H} :
    ∀ z ∈ Q,
      scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h = du z h := by
  intro z hz
  simp [χ.eq_one_on z hz, χ.fderiv_eq_zero_on z hz]

end ScalarWeakSobolevCutoff

/--
%%handwave
name:
  Compactly supported multipliers preserve local integrability
statement:
  If \(u\) is locally integrable on an open region and \(a\) is continuous
  with compact support contained in that region, then \(a u\) is integrable
  over the region.
proof:
  The product is supported in the compact support of \(a\).  On this compact
  set, local integrability gives integrability of \(u\), while continuity of
  \(a\) gives a uniform bound.  Bounded multiplication preserves
  integrability.
-/
theorem locallyIntegrableOn_mul_left_integrable_of_tsupport_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H]
    {Ω : Set H} {a u : H → ℝ}
    (hu : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H))
    (ha_cont : Continuous a)
    (ha_support : tsupport a ⊆ Ω)
    (ha_compact : IsCompact (tsupport a)) :
    Integrable (fun z ↦ a z * u z) (MeasureTheory.volume.restrict Ω) := by
  let K : Set H := tsupport a
  have huK_on : IntegrableOn u K (MeasureTheory.volume : Measure H) :=
    hu.integrableOn_compact_subset ha_support ha_compact
  rcases ha_compact.exists_bound_of_continuousOn ha_cont.continuousOn with
    ⟨C, hC⟩
  have hprodK : Integrable (fun z ↦ a z * u z)
      (MeasureTheory.volume.restrict K) := by
    exact huK_on.bdd_mul ha_cont.aestronglyMeasurable
      (ae_restrict_of_forall_mem ha_compact.measurableSet fun z hz ↦ hC z hz)
  have hprod_support : Function.support (fun z ↦ a z * u z) ⊆ K := by
    intro z hz
    exact subset_tsupport a (Function.support_mul_subset_left (f := a) (g := u) hz)
  have hglobal : Integrable (fun z ↦ a z * u z) MeasureTheory.volume :=
    (integrableOn_iff_integrable_of_support_subset hprod_support).mp hprodK
  exact hglobal.mono_measure
    (Measure.restrict_le_self (μ := MeasureTheory.volume) (s := Ω))

/--
%%handwave
name:
  Compactly supported multipliers give global integrability
statement:
  If \(u\) is locally integrable on an open region and \(a\) is continuous
  with compact support contained in that region, then \(a u\), extended by
  zero outside its support, is globally integrable.
proof:
  The previous compact-support multiplier theorem gives integrability over
  the region.  Since \(a u\) vanishes outside the region, integrability over
  the region is equivalent to global integrability.
-/
theorem locallyIntegrableOn_mul_left_integrable_global_of_tsupport_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H]
    {Ω : Set H} {a u : H → ℝ}
    (hu : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H))
    (ha_cont : Continuous a)
    (ha_support : tsupport a ⊆ Ω)
    (ha_compact : IsCompact (tsupport a)) :
    Integrable (fun z ↦ a z * u z) (MeasureTheory.volume : Measure H) := by
  have hΩ : IntegrableOn (fun z ↦ a z * u z) Ω
      (MeasureTheory.volume : Measure H) := by
    simpa [IntegrableOn] using
      locallyIntegrableOn_mul_left_integrable_of_tsupport_subset
        (Ω := Ω) hu ha_cont ha_support ha_compact
  have hsupport : Function.support (fun z ↦ a z * u z) ⊆ Ω := by
    intro z hz
    exact ha_support
      (subset_tsupport a (Function.support_mul_subset_left (f := a) (g := u) hz))
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hΩ

/--
%%handwave
name:
  Cutoff-localized values are globally integrable
statement:
  Multiplying a locally integrable function by a smooth cutoff whose compact
  support is contained in the region gives a globally integrable function.
-/
theorem scalarWeakSobolevCutoff_value_integrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H]
    {Q Ω : Set H} (χ : ScalarWeakSobolevCutoff Q Ω)
    {u : H → ℝ}
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H)) :
    Integrable (fun z ↦ χ z * u z) (MeasureTheory.volume : Measure H) :=
  locallyIntegrableOn_mul_left_integrable_global_of_tsupport_subset
    (Ω := Ω) hu_loc χ.smooth.continuous χ.support_subset χ.compact_support

/--
%%handwave
name:
  Cutoff-localized directional derivatives are globally integrable
statement:
  If \(u\) and the chosen directional weak derivative are locally integrable
  on the region, then the directional derivative of the cutoff-localized pair,
  \(\chi\,du(h)+u\,d\chi(h)\), is globally integrable.
proof:
  The first term is the compactly supported multiplier \(\chi\,du(h)\).  The
  second term is the compactly supported multiplier \(d\chi(h)\,u\), because
  the support of the derivative of a compactly supported smooth function is
  contained in the support of the function.  Add the two integrable terms.
-/
theorem scalarWeakSobolevCutoff_derivative_integrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H]
    {Q Ω : Set H} (χ : ScalarWeakSobolevCutoff Q Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H))
    (hdu_loc : LocallyIntegrableOn (fun z ↦ du z h) Ω
      (MeasureTheory.volume : Measure H)) :
    Integrable
      (fun z ↦ scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
      (MeasureTheory.volume : Measure H) := by
  have hχdu : Integrable (fun z : H ↦ χ z * du z h)
      (MeasureTheory.volume : Measure H) :=
    locallyIntegrableOn_mul_left_integrable_global_of_tsupport_subset
      (Ω := Ω) hdu_loc χ.smooth.continuous χ.support_subset χ.compact_support
  let a : H → ℝ := fun z ↦ fderiv ℝ (χ : H → ℝ) z h
  have ha_cont : Continuous a :=
    ((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have ha_tsupport_subset :
      tsupport a ⊆ tsupport (χ : H → ℝ) :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (χ : H → ℝ)) h
  have ha_support : tsupport a ⊆ Ω :=
    ha_tsupport_subset.trans χ.support_subset
  have ha_compact : IsCompact (tsupport a) :=
    χ.compact_support.of_isClosed_subset (isClosed_tsupport _) ha_tsupport_subset
  have hduχ : Integrable (fun z : H ↦ a z * u z)
      (MeasureTheory.volume : Measure H) :=
    locallyIntegrableOn_mul_left_integrable_global_of_tsupport_subset
      (Ω := Ω) hu_loc ha_cont ha_support ha_compact
  refine (hχdu.add hduχ).congr ?_
  exact ae_of_all (MeasureTheory.volume : Measure H) fun z ↦ by
    simp [scalarWeakSobolevCutoffDerivative, a]
    ring

/--
%%handwave
name:
  Weak product rule for cutoff localization
statement:
  If \(u\) has weak derivative \(du\) on \(\Omega\) and \(\chi\) is a smooth
  cutoff supported in \(\Omega\), then \(\chi u\) has weak derivative
  \(\chi\,du+u\,d\chi\) on \(\Omega\).
proof:
  Test the weak derivative identity for \(u\) against \(\chi\varphi\).  The
  classical product rule expands \(d(\chi\varphi)\), and the term containing
  \(d\chi\) is moved to the other side.  Compact support of the test and
  cutoff, together with local integrability of \(u\), gives the required
  integrability of all product terms.
-/
theorem scalarWeakSobolevCutoffDerivative_weakDerivative
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H]
    {Q Ω : Set H} (χ : ScalarWeakSobolevCutoff Q Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H)) :
    KinnunenWeakDerivativeOnEuclideanRegionScalar Ω
      (fun z ↦ χ z * u z)
      (scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du) := by
  intro φ v
  let μ : Measure H := MeasureTheory.volume.restrict Ω
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := fun z : H ↦ χ z * φ z
      smooth := χ.smooth.mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_right).trans φ.support_subset
      compact_support := by
        exact φ.compact_support.of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_right }
  have hψ := hweak ψ v
  have hB : Integrable
      (fun z : H ↦
        (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z) μ := by
    let a : H → ℝ :=
      fun z ↦ ((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v
    have ha_cont : Continuous a := by
      exact φ.smooth.continuous.mul
        ((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    have ha_support : tsupport a ⊆ Ω := by
      exact (tsupport_mul_subset_left).trans φ.support_subset
    have ha_compact : IsCompact (tsupport a) := by
      exact φ.compact_support.of_isClosed_subset
        (isClosed_tsupport _) tsupport_mul_subset_left
    simpa [a, μ] using
      locallyIntegrableOn_mul_left_integrable_of_tsupport_subset
        (Ω := Ω) hu_loc ha_cont ha_support ha_compact
  have hC : Integrable
      (fun z : H ↦ ((φ : H → ℝ) z * χ z) * du z v) μ := by
    refine hψ.2.1.congr ?_
    exact ae_of_all μ fun z ↦ by
      simp [ψ, mul_comm, mul_assoc]
  have hleft_ae :
      (fun z : H ↦ (fderiv ℝ (ψ : H → ℝ) z v) • u z)
        =ᵐ[μ]
      fun z ↦
        (χ z * fderiv ℝ (φ : H → ℝ) z v) * u z +
          (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z := by
    exact ae_of_all μ fun z ↦ by
      have hχdiff : DifferentiableAt ℝ (χ : H → ℝ) z :=
        (χ.smooth.differentiable (by simp)) z
      have hφdiff : DifferentiableAt ℝ (φ : H → ℝ) z :=
        (φ.smooth.differentiable (by simp)) z
      change
        fderiv ℝ (fun y : H ↦ χ y * φ y) z v • u z =
          (χ z * fderiv ℝ (φ : H → ℝ) z v) * u z +
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z
      rw [fderiv_fun_mul hχdiff hφdiff]
      simp [smul_eq_mul]
      ring
  have hsumAB : Integrable
      (fun z : H ↦
        (χ z * fderiv ℝ (φ : H → ℝ) z v) * u z +
          (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z) μ :=
    hψ.1.congr hleft_ae
  have hA : Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • (χ z * u z)) μ := by
    refine (hsumAB.sub hB).congr ?_
    exact ae_of_all μ fun z ↦ by
      simp only [Pi.sub_apply, smul_eq_mul]
      ring
  have hD : Integrable
      (fun z : H ↦ φ z •
        scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z v) μ := by
    refine (hC.add hB).congr ?_
    exact ae_of_all μ fun z ↦ by
      simp [scalarWeakSobolevCutoffDerivative]
      ring
  refine ⟨hA, hD, ?_⟩
  have hright_ae :
      (fun z : H ↦ ψ z • du z v) =ᵐ[μ]
        fun z ↦ ((φ : H → ℝ) z * χ z) * du z v := by
    exact ae_of_all μ fun z ↦ by
      simp [ψ, mul_comm, mul_assoc]
  have hraw :
      (∫ z, (fderiv ℝ (ψ : H → ℝ) z v) • u z ∂μ) =
        -∫ z, ψ z • du z v ∂μ := by
    simpa [μ] using hψ.2.2
  have hsum_eq :
      (∫ z,
        ((χ z * fderiv ℝ (φ : H → ℝ) z v) * u z +
          (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z) ∂μ) =
        -∫ z, ((φ : H → ℝ) z * χ z) * du z v ∂μ := by
    calc
      (∫ z,
        ((χ z * fderiv ℝ (φ : H → ℝ) z v) * u z +
          (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z) ∂μ)
          = ∫ z, (fderiv ℝ (ψ : H → ℝ) z v) • u z ∂μ := by
            exact integral_congr_ae hleft_ae.symm
      _ = -∫ z, ψ z • du z v ∂μ := hraw
      _ = -∫ z, ((φ : H → ℝ) z * χ z) * du z v ∂μ := by
            rw [integral_congr_ae hright_ae]
  have hsum_integral_add :
      (∫ z,
        ((χ z * fderiv ℝ (φ : H → ℝ) z v) * u z +
          (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z) ∂μ) =
        (∫ z, (fderiv ℝ (φ : H → ℝ) z v) • (χ z * u z) ∂μ) +
          ∫ z,
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ := by
    calc
      (∫ z,
        ((χ z * fderiv ℝ (φ : H → ℝ) z v) * u z +
          (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z) ∂μ)
          =
        ∫ z,
          (fderiv ℝ (φ : H → ℝ) z v) • (χ z * u z) +
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ := by
            exact integral_congr_ae (ae_of_all μ fun z ↦ by
              simp only [smul_eq_mul]
              ring)
      _ =
        (∫ z, (fderiv ℝ (φ : H → ℝ) z v) • (χ z * u z) ∂μ) +
          ∫ z,
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ :=
            integral_add hA hB
  have hderiv_integral_add :
      (∫ z, φ z •
        scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z v ∂μ) =
        (∫ z, ((φ : H → ℝ) z * χ z) * du z v ∂μ) +
          ∫ z,
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ := by
    calc
      (∫ z, φ z •
        scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z v ∂μ)
          =
        ∫ z,
          ((φ : H → ℝ) z * χ z) * du z v +
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ := by
            exact integral_congr_ae (ae_of_all μ fun z ↦ by
              simp [scalarWeakSobolevCutoffDerivative]
              ring_nf)
      _ =
        (∫ z, ((φ : H → ℝ) z * χ z) * du z v ∂μ) +
          ∫ z,
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ :=
            integral_add hC hB
  calc
    (∫ z in Ω,
        (fderiv ℝ (φ : H → ℝ) z v) • (χ z * u z)
        ∂MeasureTheory.volume)
        = (∫ z, (fderiv ℝ (φ : H → ℝ) z v) • (χ z * u z) ∂μ) := by
          rfl
    _ =
        (∫ z,
          ((χ z * fderiv ℝ (φ : H → ℝ) z v) * u z +
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z) ∂μ) -
          ∫ z,
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ := by
          rw [hsum_integral_add]
          ring
    _ =
        (-∫ z, ((φ : H → ℝ) z * χ z) * du z v ∂μ) -
          ∫ z,
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ := by
          rw [hsum_eq]
    _ =
        -((∫ z, ((φ : H → ℝ) z * χ z) * du z v ∂μ) +
          ∫ z,
            (((φ : H → ℝ) z) * fderiv ℝ (χ : H → ℝ) z v) * u z ∂μ) := by
          ring
    _ =
        -∫ z, φ z •
          scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z v ∂μ := by
          rw [← hderiv_integral_add]
    _ =
        -∫ z in Ω, φ z •
          scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z v
          ∂MeasureTheory.volume := by
          rfl

/--
%%handwave
name:
  Smooth cutoffs exist around compact subsets of open Euclidean regions
statement:
  If \(Q\) is compact and contained in an open Euclidean region \(\Omega\),
  there exists a smooth cutoff equal to one on \(Q\), with derivative zero on
  \(Q\), and with compact support contained in \(\Omega\).
proof:
  Choose two nested metric thickenings of \(Q\) inside \(\Omega\).  A smooth
  Urysohn cutoff is chosen to be one on the smaller closed thickening and
  supported in the larger open thickening.  It is therefore locally constant
  near every point of \(Q\), so its derivative vanishes on \(Q\).
-/
theorem exists_scalarWeakSobolevCutoff
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω) :
    Nonempty (ScalarWeakSobolevCutoff Q Ω) := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hΩ_open hQΩ
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_ltδ : η < δ := by
    dsimp [η]
    linarith
  have hclosed_eta : IsClosed (Metric.cthickening η Q) :=
    Metric.isClosed_cthickening
  have heta_subset_thickening :
      Metric.cthickening η Q ⊆ Metric.thickening δ Q :=
    Metric.cthickening_subset_thickening' hδ_pos hη_ltδ Q
  obtain ⟨χ, hχ_smooth, _hχ_range, hχ_support, hχ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, H)) (n := ⊤)
      (Metric.isOpen_thickening) hclosed_eta heta_subset_thickening
  have hχ_tsupport_subset_cthickening :
      tsupport χ ⊆ Metric.cthickening δ Q := by
    rw [tsupport, hχ_support]
    exact Metric.closure_thickening_subset_cthickening δ Q
  have hχ_deriv_zero :
      ∀ z ∈ Q, fderiv ℝ χ z = 0 := by
    intro z hzQ
    have hz_thick : z ∈ Metric.thickening η Q :=
      Metric.self_subset_thickening hη_pos Q hzQ
    have hnhds : Metric.thickening η Q ∈ 𝓝 z :=
      Metric.isOpen_thickening.mem_nhds hz_thick
    have hχ_eventually :
        χ =ᶠ[𝓝 z] fun _ : H ↦ (1 : ℝ) := by
      filter_upwards [hnhds] with y hy
      exact (hχ_one y).1 ((Metric.thickening_subset_cthickening η Q) hy)
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hχ_eventually]
    simp
  exact
    ⟨{ toFun := χ
       smooth := hχ_smooth.contDiff
       support_subset := hχ_tsupport_subset_cthickening.trans hδΩ
       compact_support := by
        exact IsCompact.of_isClosed_subset (hQ.cthickening)
          (isClosed_tsupport χ) hχ_tsupport_subset_cthickening
       eq_one_on := by
        intro z hzQ
        exact (hχ_one z).1 (Metric.self_subset_cthickening Q hzQ)
       fderiv_eq_zero_on := hχ_deriv_zero }⟩

/--
%%handwave
name:
  Removing a cutoff from local graph approximation
statement:
  If a cutoff is one with zero derivative on \(Q\), then any smooth
  graph-norm approximation to the localized pair
  \((\chi u,\chi\,du+u\,d\chi)\) on \(Q\) is also a smooth graph-norm
  approximation to \((u,du)\) on \(Q\).
-/
theorem scalarWeakSobolevLocalSmoothApprox_of_cutoff
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H]
    {Q P Ω : Set H} (hQ : IsCompact Q)
    (χ : ScalarWeakSobolevCutoff P Ω) (hQP : Q ⊆ P)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox :
      ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q
        (fun z ↦ χ z * u z)
        (scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du) h) :
    Nonempty (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h) := by
  let μ : Measure H := MeasureTheory.volume.restrict Q
  have hvalue_ae :
      (fun z : H ↦ χ z * u z) =ᵐ[μ] u := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      simp [χ.eq_one_on z (hQP hzQ)]
  have hderiv_ae :
      (fun z : H ↦ scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
        =ᵐ[μ] fun z ↦ du z h := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      exact χ.cutoffDerivative_eq_on z (hQP hzQ)
  refine
    ⟨{ approximants := happrox.approximants
       smooth := happrox.smooth
       value_aestronglyMeasurable := ?_
       value_tendsto_l2 := ?_
       directionalDerivative_aestronglyMeasurable := ?_
       directionalDerivative_tendsto_l2 := ?_ }⟩
  · intro n
    refine (happrox.value_aestronglyMeasurable n).congr ?_
    exact (Filter.EventuallyEq.rfl.sub hvalue_ae)
  · have hseq :
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ happrox.approximants n z - u z) 2 μ) =
        (fun n : ℕ ↦
          eLpNorm
            (fun z : H ↦ happrox.approximants n z - χ z * u z) 2 μ) := by
      funext n
      exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hvalue_ae.symm)
    simpa [μ, hseq] using happrox.value_tendsto_l2
  · intro n
    refine (happrox.directionalDerivative_aestronglyMeasurable n).congr ?_
    exact (Filter.EventuallyEq.rfl.sub hderiv_ae)
  · have hseq :
        (fun n : ℕ ↦
          eLpNorm
            (fun z : H ↦ fderiv ℝ (happrox.approximants n) z h - du z h)
            2 μ) =
        (fun n : ℕ ↦
          eLpNorm
            (fun z : H ↦
              fderiv ℝ (happrox.approximants n) z h -
                scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
            2 μ) := by
      funext n
      exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hderiv_ae.symm)
    simpa [μ, hseq] using happrox.directionalDerivative_tendsto_l2

/--
%%handwave
name:
  Cutoff localization preserves \(L^2\) values on the compact set
statement:
  If the cutoff is equal to one on \(Q\), then multiplying by the cutoff does
  not change the \(L^2\) class on \(Q\).
-/
theorem scalarWeakSobolevCutoff_value_memLp_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (χ : ScalarWeakSobolevCutoff Q Ω)
    {u : H → ℝ}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q)) :
    MemLp (fun z ↦ χ z * u z) 2 (MeasureTheory.volume.restrict Q) := by
  let μ : Measure H := MeasureTheory.volume.restrict Q
  have hvalue_ae :
      (fun z : H ↦ χ z * u z) =ᵐ[μ] u := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      simp [χ.eq_one_on z hzQ]
  exact MemLp.ae_eq hvalue_ae.symm hu

/--
%%handwave
name:
  Cutoff localization preserves \(L^2\) directional derivatives on the compact set
statement:
  Since the cutoff derivative vanishes and the cutoff is one on \(Q\), the
  localized directional derivative agrees with the original one in \(L^2(Q)\).
-/
theorem scalarWeakSobolevCutoff_derivative_memLp_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (χ : ScalarWeakSobolevCutoff Q Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q)) :
    MemLp
      (fun z ↦ scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
      2 (MeasureTheory.volume.restrict Q) := by
  let μ : Measure H := MeasureTheory.volume.restrict Q
  have hderiv_ae :
      (fun z : H ↦ scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
        =ᵐ[μ] fun z ↦ du z h := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      exact χ.cutoffDerivative_eq_on z hzQ
  exact MemLp.ae_eq hderiv_ae.symm hdu

/--
%%handwave
name:
  A standard sequence of smooth approximate identities
statement:
  In a finite-dimensional Euclidean space there is a fixed-ratio sequence of
  smooth bump functions centered at the origin whose supports shrink to the
  origin.
-/
noncomputable def scalarWeakSobolevStandardMollifier
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (n : ℕ) :
    ContDiffBump (0 : H) where
  rIn := (((n : ℝ) + 1)⁻¹) / 2
  rOut := ((n : ℝ) + 1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hpos : 0 < (((n : ℝ) + 1)⁻¹) := by positivity
    nlinarith

theorem scalarWeakSobolevStandardMollifier_rOut_tendsto_zero
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Filter.Tendsto
      (fun n : ℕ ↦ (scalarWeakSobolevStandardMollifier H n).rOut)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  simpa [scalarWeakSobolevStandardMollifier, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem scalarWeakSobolevStandardMollifier_fixed_ratio
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (n : ℕ) :
    (scalarWeakSobolevStandardMollifier H n).rOut =
      2 * (scalarWeakSobolevStandardMollifier H n).rIn := by
  simp [scalarWeakSobolevStandardMollifier]
  ring

theorem subset_of_exists_cthickening_subset
    {H : Type} [PseudoMetricSpace H] {Q P : Set H}
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P) :
    Q ⊆ P := by
  rcases hQP with ⟨δ, _hδ_pos, hδ⟩
  exact (Metric.self_subset_cthickening Q).trans hδ

private theorem normedBump_lintegral_ofReal_eq_one
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    (φ : ContDiffBump (0 : H)) :
    (∫⁻ t, ENNReal.ofReal
        (φ.normed (MeasureTheory.volume : Measure H) t)
      ∂(MeasureTheory.volume : Measure H)) = 1 := by
  let μ : Measure H := MeasureTheory.volume
  have hnonneg :
      0 ≤ᵐ[μ] fun t : H ↦ φ.normed μ t :=
    Filter.Eventually.of_forall fun t ↦ φ.nonneg_normed (μ := μ) t
  have h :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (φ.integrable_normed (μ := μ)) hnonneg
  rw [← h, φ.integral_normed (μ := μ)]
  simp

private theorem lintegral_enorm_sq_comp_sub_right_restrict_le_of_mapsTo
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} {f : H → ℝ} {h : H}
    (hmap : Set.MapsTo (fun z : H ↦ z - h) K Q) :
    (∫⁻ z in K, ‖f (z - h)‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H)) ≤
      ∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H) := by
  let τ : H → H := fun z ↦ z - h
  let F : H → ℝ≥0∞ := fun z ↦ ‖f z‖ₑ ^ (2 : ℝ)
  have hτ_mp :
      MeasurePreserving τ MeasureTheory.volume MeasureTheory.volume := by
    simpa [τ, sub_eq_add_neg] using
      (MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : Measure H) (-h))
  have hτ_emb : MeasurableEmbedding τ := by
    simpa [τ, sub_eq_add_neg] using
      (Homeomorph.addRight (-h)).isClosedEmbedding.measurableEmbedding
  have hτ_image : τ '' K ⊆ Q := by
    rintro y ⟨x, hxK, rfl⟩
    exact hmap hxK
  calc
    ∫⁻ z in K, ‖f (z - h)‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H)
        = ∫⁻ y in τ '' K, F y ∂MeasureTheory.volume := by
          simpa [τ, F] using hτ_mp.setLIntegral_comp_emb hτ_emb F K
    _ ≤ ∫⁻ y in Q, F y ∂MeasureTheory.volume :=
          lintegral_mono_set hτ_image
    _ = ∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H) := rfl

private theorem lintegral_enorm_comp_sub_right_restrict_le_of_mapsTo
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} {f : H → ℝ} {h : H}
    (hmap : Set.MapsTo (fun z : H ↦ z - h) K Q) :
    (∫⁻ z in K, ‖f (z - h)‖ₑ
        ∂(MeasureTheory.volume : Measure H)) ≤
      ∫⁻ z in Q, ‖f z‖ₑ
        ∂(MeasureTheory.volume : Measure H) := by
  let τ : H → H := fun z ↦ z - h
  let F : H → ℝ≥0∞ := fun z ↦ ‖f z‖ₑ
  have hτ_mp :
      MeasurePreserving τ MeasureTheory.volume MeasureTheory.volume := by
    simpa [τ, sub_eq_add_neg] using
      (MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : Measure H) (-h))
  have hτ_emb : MeasurableEmbedding τ := by
    simpa [τ, sub_eq_add_neg] using
      (Homeomorph.addRight (-h)).isClosedEmbedding.measurableEmbedding
  have hτ_image : τ '' K ⊆ Q := by
    rintro y ⟨x, hxK, rfl⟩
    exact hmap hxK
  calc
    ∫⁻ z in K, ‖f (z - h)‖ₑ
        ∂(MeasureTheory.volume : Measure H)
        = ∫⁻ y in τ '' K, F y ∂MeasureTheory.volume := by
          simpa [τ, F] using hτ_mp.setLIntegral_comp_emb hτ_emb F K
    _ ≤ ∫⁻ y in Q, F y ∂MeasureTheory.volume :=
          lintegral_mono_set hτ_image
    _ = ∫⁻ z in Q, ‖f z‖ₑ
        ∂(MeasureTheory.volume : Measure H) := rfl

private theorem normedBump_sub_right_mapsTo_of_ne_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} {φ : ContDiffBump (0 : H)}
    (hQP : Metric.cthickening φ.rOut Q ⊆ P)
    {t : H}
    (ht : φ.normed (MeasureTheory.volume : Measure H) t ≠ 0) :
    Set.MapsTo (fun z : H ↦ z - t) Q P := by
  intro z hzQ
  have ht_support :
      t ∈ Function.support
        (φ.normed (MeasureTheory.volume : Measure H)) := by
    simpa [Function.mem_support] using ht
  have ht_ball : t ∈ Metric.ball (0 : H) φ.rOut := by
    simpa [φ.support_normed_eq (μ := (MeasureTheory.volume : Measure H))]
      using ht_support
  have hdist : dist (z - t) z ≤ φ.rOut := by
    have hlt : ‖t‖ < φ.rOut := by
      simpa [Metric.mem_ball, dist_eq_norm] using ht_ball
    rw [dist_eq_norm]
    have hnorm : ‖z - t - z‖ = ‖t‖ := by
      calc
        ‖z - t - z‖ = ‖-t‖ := by
          congr 1
          abel
        _ = ‖t‖ := norm_neg t
    rw [hnorm]
    exact hlt.le
  exact hQP (Metric.mem_cthickening_of_dist_le (z - t) z φ.rOut Q hzQ hdist)

private theorem enorm_integral_sq_le_lintegral_enorm_sq_of_probability_mass_one
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hμ : μ Set.univ = 1)
    (hg : AEStronglyMeasurable g μ) :
    ‖∫ x, g x ∂μ‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  have hnorm :
      ‖∫ x, g x ∂μ‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ ∂μ :=
    MeasureTheory.enorm_integral_le_lintegral_enorm g
  have hholder :
      ∫⁻ x, ‖g x‖ₑ ∂μ ≤
        (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
    have hH : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have h :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq
        (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
        (f := fun x ↦ ‖g x‖ₑ) (g := fun _x ↦ (1 : ℝ≥0∞))
        hH hg.enorm aemeasurable_const
    simpa [hμ, one_div] using h
  exact (ENNReal.le_rpow_inv_iff (by norm_num : 0 < (2 : ℝ))).1
    (hnorm.trans hholder)

/--
%%handwave
name:
  Pointwise Jensen estimate for a normalized mollifier
statement:
  At each point, the square of the mollifier average is bounded by the
  mollifier average of the square.
proof:
  The normalized mollifier defines a probability measure because it is
  nonnegative and has total mass one.  Jensen's inequality for the convex
  function \(s\mapsto s^2\) gives the estimate.  Equivalently, this is the
  Cauchy-Schwarz inequality for the kernel-weighted integral.
-/
private theorem normedBump_convolution_pointwise_enorm_sq_le_kernel_lintegral_sq
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {φ : ContDiffBump (0 : H)}
    {f : H → ℝ}
    (_hf_int : Integrable f (MeasureTheory.volume : Measure H))
    (z : H) :
    ‖((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
        (MeasureTheory.volume : Measure H)] f : H → ℝ) z)‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t, ENNReal.ofReal
          (φ.normed (MeasureTheory.volume : Measure H) t) *
          ‖f (z - t)‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H) := by
  let μ : Measure H := MeasureTheory.volume
  let k : H → ℝ := φ.normed μ
  let ν : Measure H := μ.withDensity fun t ↦ ENNReal.ofReal (k t)
  have hk_meas : AEMeasurable (fun t : H ↦ ENNReal.ofReal (k t)) μ :=
    (φ.continuous_normed (μ := μ)).measurable.aemeasurable.ennreal_ofReal
  have hk_lt_top : ∀ᵐ t ∂μ, ENNReal.ofReal (k t) < (∞ : ℝ≥0∞) := by
    filter_upwards with t
    exact ENNReal.ofReal_lt_top
  have hν_univ : ν Set.univ = 1 := by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact normedBump_lintegral_ofReal_eq_one (H := H) φ
  have hqmp_vol :
      Measure.QuasiMeasurePreserving (fun t : H ↦ z - t) μ μ := by
    exact quasiMeasurePreserving_sub_left_of_right_invariant μ z
  have hqmp_ν :
      Measure.QuasiMeasurePreserving (fun t : H ↦ z - t) ν μ :=
    hqmp_vol.mono_left (withDensity_absolutelyContinuous μ fun t ↦ ENNReal.ofReal (k t))
  have hf_ν : AEStronglyMeasurable (fun t : H ↦ f (z - t)) ν :=
    _hf_int.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp_ν
  have hweighted_integral :
      ∫ t, f (z - t) ∂ν =
        ∫ t, k t • f (z - t) ∂μ := by
    change ∫ t, f (z - t)
          ∂μ.withDensity (fun t : H ↦ ENNReal.ofReal (k t)) =
        ∫ t, k t • f (z - t) ∂μ
    rw [integral_withDensity_eq_integral_toReal_smul₀ hk_meas
      hk_lt_top (fun t : H ↦ f (z - t))]
    apply integral_congr_ae
    filter_upwards with t
    simp [k, φ.nonneg_normed (μ := μ) t]
  have hJ :
      ‖∫ t, f (z - t) ∂ν‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ t, ‖f (z - t)‖ₑ ^ (2 : ℝ) ∂ν :=
    enorm_integral_sq_le_lintegral_enorm_sq_of_probability_mass_one
      hν_univ hf_ν
  have hlintegral :
      ∫⁻ t, ‖f (z - t)‖ₑ ^ (2 : ℝ) ∂ν =
        ∫⁻ t, (fun t : H ↦ ENNReal.ofReal (k t)) t *
            ‖f (z - t)‖ₑ ^ (2 : ℝ) ∂μ := by
    have hg_sq :
        AEMeasurable (fun t : H ↦ ‖f (z - t)‖ₑ ^ (2 : ℝ)) μ :=
      (_hf_int.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp_vol).enorm.pow_const _
    rw [lintegral_withDensity_eq_lintegral_mul₀ hk_meas hg_sq]
    rfl
  change ‖∫ t : H, k t • f (z - t) ∂μ‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t, ENNReal.ofReal (k t) * ‖f (z - t)‖ₑ ^ (2 : ℝ) ∂μ
  rw [← hweighted_integral, ← hlintegral]
  exact hJ

private theorem normedBump_convolution_pointwise_enorm_le_kernel_lintegral
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {φ : ContDiffBump (0 : H)}
    {f : H → ℝ}
    (_hf_int : Integrable f (MeasureTheory.volume : Measure H))
    (z : H) :
    ‖((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
        (MeasureTheory.volume : Measure H)] f : H → ℝ) z)‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal
          (φ.normed (MeasureTheory.volume : Measure H) t) *
          ‖f (z - t)‖ₑ
        ∂(MeasureTheory.volume : Measure H) := by
  let μ : Measure H := MeasureTheory.volume
  let k : H → ℝ := φ.normed μ
  let ν : Measure H := μ.withDensity fun t ↦ ENNReal.ofReal (k t)
  have hk_meas : AEMeasurable (fun t : H ↦ ENNReal.ofReal (k t)) μ :=
    (φ.continuous_normed (μ := μ)).measurable.aemeasurable.ennreal_ofReal
  have hk_lt_top : ∀ᵐ t ∂μ, ENNReal.ofReal (k t) < (∞ : ℝ≥0∞) := by
    filter_upwards with t
    exact ENNReal.ofReal_lt_top
  have hqmp_vol :
      Measure.QuasiMeasurePreserving (fun t : H ↦ z - t) μ μ := by
    exact quasiMeasurePreserving_sub_left_of_right_invariant μ z
  have hqmp_ν :
      Measure.QuasiMeasurePreserving (fun t : H ↦ z - t) ν μ :=
    hqmp_vol.mono_left (withDensity_absolutelyContinuous μ fun t ↦ ENNReal.ofReal (k t))
  have hweighted_integral :
      ∫ t, f (z - t) ∂ν =
        ∫ t, k t • f (z - t) ∂μ := by
    change ∫ t, f (z - t)
          ∂μ.withDensity (fun t : H ↦ ENNReal.ofReal (k t)) =
        ∫ t, k t • f (z - t) ∂μ
    rw [integral_withDensity_eq_integral_toReal_smul₀ hk_meas
      hk_lt_top (fun t : H ↦ f (z - t))]
    apply integral_congr_ae
    filter_upwards with t
    simp [k, φ.nonneg_normed (μ := μ) t]
  have hJ :
      ‖∫ t, f (z - t) ∂ν‖ₑ ≤
        ∫⁻ t, ‖f (z - t)‖ₑ ∂ν :=
    MeasureTheory.enorm_integral_le_lintegral_enorm (fun t ↦ f (z - t))
  have hlintegral :
      ∫⁻ t, ‖f (z - t)‖ₑ ∂ν =
        ∫⁻ t, (fun t : H ↦ ENNReal.ofReal (k t)) t *
            ‖f (z - t)‖ₑ ∂μ := by
    have hg :
        AEMeasurable (fun t : H ↦ ‖f (z - t)‖ₑ) μ :=
      (_hf_int.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp_vol).enorm
    rw [lintegral_withDensity_eq_lintegral_mul₀ hk_meas hg]
    rfl
  change ‖∫ t : H, k t • f (z - t) ∂μ‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal (k t) * ‖f (z - t)‖ₑ ∂μ
  rw [← hweighted_integral, ← hlintegral]
  exact hJ

/--
%%handwave
name:
  Kernel square integral bound from the support inclusion
statement:
  If the support-radius neighborhood of \(Q\) lies in \(P\), then integrating
  the kernel-weighted translated square over \(Q\) is bounded by the square
  integral over \(P\).
proof:
  Tonelli's theorem swaps the \(Q\)- and kernel-integrations.  For a fixed
  kernel point with nonzero weight, the support-radius hypothesis implies
  \(z\mapsto z-t\) maps \(Q\) into \(P\); translation-invariance of volume
  bounds the translated \(Q\)-integral by the \(P\)-integral.  Finally the
  normalized kernel has total mass one.
-/
private theorem normedBump_kernel_lintegral_sq_restrict_le_of_cthickening_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} {φ : ContDiffBump (0 : H)}
    (_hQP : Metric.cthickening φ.rOut Q ⊆ P)
    {f : H → ℝ}
    (_hf_int : Integrable f (MeasureTheory.volume : Measure H)) :
    (∫⁻ z in Q,
        ∫⁻ t, ENNReal.ofReal
            (φ.normed (MeasureTheory.volume : Measure H) t) *
            ‖f (z - t)‖ₑ ^ (2 : ℝ)
          ∂(MeasureTheory.volume : Measure H)
      ∂(MeasureTheory.volume : Measure H)) ≤
      ∫⁻ z in P, ‖f z‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H) := by
  let μ : Measure H := MeasureTheory.volume
  let μQ : Measure H := μ.restrict Q
  let k : H → ℝ := φ.normed μ
  let K : H → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (k t)
  let A : ℝ≥0∞ := ∫⁻ z in P, ‖f z‖ₑ ^ (2 : ℝ) ∂μ
  let F : H → H → ℝ≥0∞ := fun z t ↦ K t * ‖f (z - t)‖ₑ ^ (2 : ℝ)
  have hK_meas : AEMeasurable K μ :=
    (φ.continuous_normed (μ := μ)).measurable.aemeasurable.ennreal_ofReal
  have hprod_ac : μQ.prod μ ≪ μ.prod μ := by
    exact (Measure.absolutelyContinuous_restrict (μ := μ) (s := Q)).prod
      Measure.AbsolutelyContinuous.rfl
  have hsub_qmp :
      Measure.QuasiMeasurePreserving (fun p : H × H ↦ p.1 - p.2)
        (μQ.prod μ) μ := by
    exact (quasiMeasurePreserving_sub_of_right_invariant μ μ).mono_left hprod_ac
  have hf_sub :
      AEStronglyMeasurable (fun p : H × H ↦ f (p.1 - p.2)) (μQ.prod μ) :=
    _hf_int.aestronglyMeasurable.comp_quasiMeasurePreserving hsub_qmp
  have hK_snd :
      AEMeasurable (fun p : H × H ↦ K p.2) (μQ.prod μ) :=
    hK_meas.comp_snd
  have hF_ae : AEMeasurable (Function.uncurry F) (μQ.prod μ) := by
    simpa [F, Function.uncurry] using
      hK_snd.mul (hf_sub.enorm.pow_const (2 : ℝ))
  have hswap :
      (∫⁻ z, ∫⁻ t, F z t ∂μ ∂μQ) =
        ∫⁻ t, ∫⁻ z, F z t ∂μQ ∂μ :=
    lintegral_lintegral_swap hF_ae
  have hinner :
      ∀ t : H, (∫⁻ z, F z t ∂μQ) ≤ K t * A := by
    intro t
    by_cases ht : k t = 0
    · simp [F, K, A, ht]
    · have hmap : Set.MapsTo (fun z : H ↦ z - t) Q P :=
        normedBump_sub_right_mapsTo_of_ne_zero (Q := Q) (P := P) (φ := φ)
          _hQP ht
      have htrans :
          (∫⁻ z, ‖f (z - t)‖ₑ ^ (2 : ℝ) ∂μQ) ≤ A := by
        simpa [μQ, A] using
          lintegral_enorm_sq_comp_sub_right_restrict_le_of_mapsTo
            (K := Q) (Q := P) (f := f) (h := t) hmap
      have hz_ae :
          AEMeasurable (fun z : H ↦ ‖f (z - t)‖ₑ ^ (2 : ℝ)) μQ := by
        have hqmp :
            Measure.QuasiMeasurePreserving (fun z : H ↦ z - t) μQ μ := by
          have hvol :
              Measure.QuasiMeasurePreserving (fun z : H ↦ z - t) μ μ := by
            simpa [sub_eq_add_neg] using
              (MeasureTheory.measurePreserving_add_right μ (-t)).quasiMeasurePreserving
          exact hvol.mono_left (Measure.absolutelyContinuous_restrict (μ := μ) (s := Q))
        exact (_hf_int.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp).enorm.pow_const _
      calc
        ∫⁻ z, F z t ∂μQ
            = K t * ∫⁻ z, ‖f (z - t)‖ₑ ^ (2 : ℝ) ∂μQ := by
              change (∫⁻ z, K t * (‖f (z - t)‖ₑ ^ (2 : ℝ)) ∂μQ) =
                K t * ∫⁻ z, ‖f (z - t)‖ₑ ^ (2 : ℝ) ∂μQ
              rw [lintegral_const_mul'' (K t) hz_ae]
        _ ≤ K t * A := by
              gcongr
  calc
    (∫⁻ z in Q,
        ∫⁻ t, ENNReal.ofReal
            (φ.normed (MeasureTheory.volume : Measure H) t) *
            ‖f (z - t)‖ₑ ^ (2 : ℝ)
          ∂(MeasureTheory.volume : Measure H)
      ∂(MeasureTheory.volume : Measure H))
        = ∫⁻ z, ∫⁻ t, F z t ∂μ ∂μQ := by
          rfl
    _ = ∫⁻ t, ∫⁻ z, F z t ∂μQ ∂μ := hswap
    _ ≤ ∫⁻ t, K t * A ∂μ := lintegral_mono hinner
    _ = (∫⁻ t, K t ∂μ) * A := by
          rw [lintegral_mul_const'' _ hK_meas]
    _ = A := by
          rw [normedBump_lintegral_ofReal_eq_one (H := H) φ]
          simp
    _ = ∫⁻ z in P, ‖f z‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H) := rfl

/--
%%handwave
name:
  Local square integral contraction for a normalized mollifier
statement:
  Under the support-radius inclusion \(Q+B_r\subset P\), the square integral
  of the mollified function over \(Q\) is bounded by the square integral of
  the original function over \(P\).
proof:
  Jensen's inequality bounds the square of the mollifier average by the
  mollifier average of the square.  Tonelli's theorem then swaps the \(Q\)
  and kernel integrations.  Translation-invariance of volume and the support
  inclusion identify each translated \(Q\)-integral as a subintegral over
  \(P\), and the normalized kernel has total mass one.
-/
theorem normedBump_convolution_lintegral_sq_restrict_le_of_cthickening_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} {φ : ContDiffBump (0 : H)}
    (_hQP : Metric.cthickening φ.rOut Q ⊆ P)
    {f : H → ℝ}
    (_hf_int : Integrable f (MeasureTheory.volume : Measure H))
    (_hf : MemLp f 2 (MeasureTheory.volume.restrict P)) :
    (∫⁻ z in Q,
        ‖((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure H)] f : H → ℝ) z)‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H)) ≤
      ∫⁻ z in P, ‖f z‖ₑ ^ (2 : ℝ) ∂(MeasureTheory.volume : Measure H) := by
  calc
    (∫⁻ z in Q,
        ‖((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure H)] f : H → ℝ) z)‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H))
        ≤ ∫⁻ z in Q,
            ∫⁻ t, ENNReal.ofReal
                (φ.normed (MeasureTheory.volume : Measure H) t) *
                ‖f (z - t)‖ₑ ^ (2 : ℝ)
              ∂(MeasureTheory.volume : Measure H)
          ∂(MeasureTheory.volume : Measure H) := by
          exact lintegral_mono fun z ↦
            normedBump_convolution_pointwise_enorm_sq_le_kernel_lintegral_sq
              (φ := φ) _hf_int z
    _ ≤ ∫⁻ z in P, ‖f z‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume : Measure H) :=
          normedBump_kernel_lintegral_sq_restrict_le_of_cthickening_subset
            (Q := Q) (P := P) (φ := φ) _hQP _hf_int

/--
%%handwave
name:
  Kernel \(L^1\) bound from the support inclusion
statement:
  If the support-radius neighborhood of \(Q\) lies in \(P\), then integrating
  the kernel-weighted translated absolute value over \(Q\) is bounded by the
  \(L^1\) integral over \(P\).
proof:
  Tonelli's theorem swaps the \(Q\)- and kernel-integrations.  For a fixed
  kernel point with nonzero weight, the support-radius hypothesis implies
  \(z\mapsto z-t\) maps \(Q\) into \(P\); translation-invariance of volume
  bounds the translated \(Q\)-integral by the \(P\)-integral.  The normalized
  kernel has total mass one.
-/
private theorem normedBump_kernel_lintegral_enorm_restrict_le_of_cthickening_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} {φ : ContDiffBump (0 : H)}
    (_hQP : Metric.cthickening φ.rOut Q ⊆ P)
    {f : H → ℝ}
    (_hf_int : Integrable f (MeasureTheory.volume : Measure H)) :
    (∫⁻ z in Q,
        ∫⁻ t, ENNReal.ofReal
            (φ.normed (MeasureTheory.volume : Measure H) t) *
            ‖f (z - t)‖ₑ
          ∂(MeasureTheory.volume : Measure H)
      ∂(MeasureTheory.volume : Measure H)) ≤
      ∫⁻ z in P, ‖f z‖ₑ
        ∂(MeasureTheory.volume : Measure H) := by
  let μ : Measure H := MeasureTheory.volume
  let μQ : Measure H := μ.restrict Q
  let k : H → ℝ := φ.normed μ
  let K : H → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (k t)
  let A : ℝ≥0∞ := ∫⁻ z in P, ‖f z‖ₑ ∂μ
  let F : H → H → ℝ≥0∞ := fun z t ↦ K t * ‖f (z - t)‖ₑ
  have hK_meas : AEMeasurable K μ :=
    (φ.continuous_normed (μ := μ)).measurable.aemeasurable.ennreal_ofReal
  have hprod_ac : μQ.prod μ ≪ μ.prod μ := by
    exact (Measure.absolutelyContinuous_restrict (μ := μ) (s := Q)).prod
      Measure.AbsolutelyContinuous.rfl
  have hsub_qmp :
      Measure.QuasiMeasurePreserving (fun p : H × H ↦ p.1 - p.2)
        (μQ.prod μ) μ := by
    exact (quasiMeasurePreserving_sub_of_right_invariant μ μ).mono_left hprod_ac
  have hf_sub :
      AEStronglyMeasurable (fun p : H × H ↦ f (p.1 - p.2)) (μQ.prod μ) :=
    _hf_int.aestronglyMeasurable.comp_quasiMeasurePreserving hsub_qmp
  have hK_snd :
      AEMeasurable (fun p : H × H ↦ K p.2) (μQ.prod μ) :=
    hK_meas.comp_snd
  have hF_ae : AEMeasurable (Function.uncurry F) (μQ.prod μ) := by
    simpa [F, Function.uncurry] using hK_snd.mul hf_sub.enorm
  have hswap :
      (∫⁻ z, ∫⁻ t, F z t ∂μ ∂μQ) =
        ∫⁻ t, ∫⁻ z, F z t ∂μQ ∂μ :=
    lintegral_lintegral_swap hF_ae
  have hinner :
      ∀ t : H, (∫⁻ z, F z t ∂μQ) ≤ K t * A := by
    intro t
    by_cases ht : k t = 0
    · simp [F, K, A, ht]
    · have hmap : Set.MapsTo (fun z : H ↦ z - t) Q P :=
        normedBump_sub_right_mapsTo_of_ne_zero (Q := Q) (P := P) (φ := φ)
          _hQP ht
      have htrans :
          (∫⁻ z, ‖f (z - t)‖ₑ ∂μQ) ≤ A := by
        simpa [μQ, A] using
          lintegral_enorm_comp_sub_right_restrict_le_of_mapsTo
            (K := Q) (Q := P) (f := f) (h := t) hmap
      have hz_ae :
          AEMeasurable (fun z : H ↦ ‖f (z - t)‖ₑ) μQ := by
        have hqmp :
            Measure.QuasiMeasurePreserving (fun z : H ↦ z - t) μQ μ := by
          have hvol :
              Measure.QuasiMeasurePreserving (fun z : H ↦ z - t) μ μ := by
            simpa [sub_eq_add_neg] using
              (MeasureTheory.measurePreserving_add_right μ (-t)).quasiMeasurePreserving
          exact hvol.mono_left (Measure.absolutelyContinuous_restrict (μ := μ) (s := Q))
        exact (_hf_int.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp).enorm
      calc
        ∫⁻ z, F z t ∂μQ
            = K t * ∫⁻ z, ‖f (z - t)‖ₑ ∂μQ := by
              change (∫⁻ z, K t * ‖f (z - t)‖ₑ ∂μQ) =
                K t * ∫⁻ z, ‖f (z - t)‖ₑ ∂μQ
              rw [lintegral_const_mul'' (K t) hz_ae]
        _ ≤ K t * A := by
              gcongr
  calc
    (∫⁻ z in Q,
        ∫⁻ t, ENNReal.ofReal
            (φ.normed (MeasureTheory.volume : Measure H) t) *
            ‖f (z - t)‖ₑ
          ∂(MeasureTheory.volume : Measure H)
      ∂(MeasureTheory.volume : Measure H))
        = ∫⁻ z, ∫⁻ t, F z t ∂μ ∂μQ := by
          rfl
    _ = ∫⁻ t, ∫⁻ z, F z t ∂μQ ∂μ := hswap
    _ ≤ ∫⁻ t, K t * A ∂μ := lintegral_mono hinner
    _ = (∫⁻ t, K t ∂μ) * A := by
          rw [lintegral_mul_const'' _ hK_meas]
    _ = A := by
          rw [normedBump_lintegral_ofReal_eq_one (H := H) φ]
          simp
    _ = ∫⁻ z in P, ‖f z‖ₑ
        ∂(MeasureTheory.volume : Measure H) := rfl

/--
%%handwave
name:
  Local \(L^1\) contraction for a normalized mollifier
statement:
  If the support radius of a normalized nonnegative mollifier around \(Q\)
  stays inside \(P\), then convolution by the mollifier maps \(L^1(P)\) to
  \(L^1(Q)\) with operator norm at most one.
proof:
  The norm of the mollifier average is bounded by the mollifier average of
  the norm.  Tonelli's theorem then swaps the \(Q\) and kernel integrations.
  Translation-invariance of volume and the support inclusion identify each
  translated \(Q\)-integral as a subintegral over \(P\), and the normalized
  kernel has total mass one.
-/
theorem normedBump_convolution_eLpNorm_one_restrict_le_of_cthickening_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} {φ : ContDiffBump (0 : H)}
    (_hQP : Metric.cthickening φ.rOut Q ⊆ P)
    {f : H → ℝ}
    (_hf_int : Integrable f (MeasureTheory.volume : Measure H)) :
    eLpNorm
        ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
          (MeasureTheory.volume : Measure H)] f : H → ℝ))
        1 (MeasureTheory.volume.restrict Q) ≤
      eLpNorm f 1 (MeasureTheory.volume.restrict P) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (1 : ℝ≥0∞) ≠ 0) ENNReal.coe_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (1 : ℝ≥0∞) ≠ 0) ENNReal.coe_ne_top]
  simpa using
    ENNReal.rpow_le_rpow
      (calc
        (∫⁻ z in Q,
            ‖((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                (MeasureTheory.volume : Measure H)] f : H → ℝ) z)‖ₑ
            ∂(MeasureTheory.volume : Measure H))
            ≤ ∫⁻ z in Q,
                ∫⁻ t, ENNReal.ofReal
                    (φ.normed (MeasureTheory.volume : Measure H) t) *
                    ‖f (z - t)‖ₑ
                  ∂(MeasureTheory.volume : Measure H)
              ∂(MeasureTheory.volume : Measure H) := by
              exact lintegral_mono fun z ↦
                normedBump_convolution_pointwise_enorm_le_kernel_lintegral
                  (φ := φ) _hf_int z
        _ ≤ ∫⁻ z in P, ‖f z‖ₑ
            ∂(MeasureTheory.volume : Measure H) :=
              normedBump_kernel_lintegral_enorm_restrict_le_of_cthickening_subset
                (Q := Q) (P := P) (φ := φ) _hQP _hf_int)
      (by positivity : 0 ≤ (1 : ℝ)⁻¹)

/--
%%handwave
name:
  Local \(L^1\) contraction for normalized mollifier differences
statement:
  If the support radius of a normalized nonnegative mollifier around \(Q\)
  stays inside \(P\), then convolution cannot increase the \(L^1\)-distance
  between two integrable scalar functions when the output is restricted to
  \(Q\).
proof:
  Apply the \(L^1\)-contraction estimate to the difference of the two
  functions.  Linearity of the convolution integral identifies the mollified
  difference with the difference of the mollifications.
-/
theorem normedBump_convolution_sub_eLpNorm_one_restrict_le_of_cthickening_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} {φ : ContDiffBump (0 : H)}
    (_hQP : Metric.cthickening φ.rOut Q ⊆ P)
    {g v : H → ℝ}
    (_hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (_hv_int : Integrable v (MeasureTheory.volume : Measure H)) :
    eLpNorm
        (fun z ↦
          ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] g : H → ℝ) z) -
            ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] v : H → ℝ) z))
        1 (MeasureTheory.volume.restrict Q) ≤
      eLpNorm (fun z ↦ g z - v z) 1 (MeasureTheory.volume.restrict P) := by
  let μ : Measure H := MeasureTheory.volume
  let k : H → ℝ := φ.normed μ
  let w : H → ℝ := fun z ↦ g z - v z
  have hw_int : Integrable w μ := _hg_int.sub _hv_int
  have hsingle :
      eLpNorm (k ⋆[lsmul ℝ ℝ, μ] w : H → ℝ)
          1 (μ.restrict Q) ≤
        eLpNorm w 1 (μ.restrict P) := by
    exact
      normedBump_convolution_eLpNorm_one_restrict_le_of_cthickening_subset
        (Q := Q) (P := P) (φ := φ) _hQP hw_int
  have hkg : ConvolutionExists k g (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (L := lsmul ℝ ℝ) φ.continuous_normed _hg_int.locallyIntegrable
  have hkv : ConvolutionExists k v (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (L := lsmul ℝ ℝ) φ.continuous_normed _hv_int.locallyIntegrable
  have hconv :
      (fun z : H ↦
          ((k ⋆[lsmul ℝ ℝ, μ] g : H → ℝ) z) -
            ((k ⋆[lsmul ℝ ℝ, μ] v : H → ℝ) z))
        =
        (k ⋆[lsmul ℝ ℝ, μ] w : H → ℝ) := by
    funext x
    change (∫ t : H, k t • g (x - t) ∂μ) -
        (∫ t : H, k t • v (x - t) ∂μ) =
      ∫ t : H, k t • w (x - t) ∂μ
    have hsub :
        ∫ t : H, k t • g (x - t) - k t • v (x - t) ∂μ =
          (∫ t : H, k t • g (x - t) ∂μ) -
            (∫ t : H, k t • v (x - t) ∂μ) := by
      simpa using integral_sub (hkg x).integrable (hkv x).integrable
    rw [← hsub]
    congr 1
    funext t
    simp [w, sub_eq_add_neg, mul_add]
  calc
    eLpNorm
        (fun z ↦
          ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] g : H → ℝ) z) -
            ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] v : H → ℝ) z))
        1 (MeasureTheory.volume.restrict Q)
        = eLpNorm (k ⋆[lsmul ℝ ℝ, μ] w : H → ℝ) 1 (μ.restrict Q) := by
          simpa [k, μ] using congrArg (fun F : H → ℝ ↦ eLpNorm F 1 (μ.restrict Q)) hconv
    _ ≤ eLpNorm w 1 (μ.restrict P) := hsingle
    _ = eLpNorm (fun z ↦ g z - v z) 1 (MeasureTheory.volume.restrict P) := by
          rfl

/--
%%handwave
name:
  Local \(L^2\) contraction for a normalized mollifier
statement:
  If the support radius of a normalized nonnegative mollifier around \(Q\)
  stays inside \(P\), then convolution by the mollifier maps \(L^2(P)\) to
  \(L^2(Q)\) with operator norm at most one.
proof:
  Jensen's inequality gives
  \[
    \left|\int \varphi(t) f(x-t)\,dt\right|^2
    \leq \int \varphi(t)|f(x-t)|^2\,dt
  \]
  because \(\varphi\geq 0\) and \(\int\varphi=1\).  After integrating in
  \(x\in Q\), Tonelli's theorem and translation invariance move each
  translated \(Q\)-integral into \(P\), using the support-radius hypothesis.
-/
theorem normedBump_convolution_eLpNorm_restrict_le_of_cthickening_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} {φ : ContDiffBump (0 : H)}
    (_hQP : Metric.cthickening φ.rOut Q ⊆ P)
    {f : H → ℝ}
    (_hf_int : Integrable f (MeasureTheory.volume : Measure H))
    (_hf : MemLp f 2 (MeasureTheory.volume.restrict P)) :
    eLpNorm
        ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
          (MeasureTheory.volume : Measure H)] f : H → ℝ))
        2 (MeasureTheory.volume.restrict Q) ≤
      eLpNorm f 2 (MeasureTheory.volume.restrict P) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      ENNReal.coe_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      ENNReal.coe_ne_top]
  exact ENNReal.rpow_le_rpow
    (normedBump_convolution_lintegral_sq_restrict_le_of_cthickening_subset
      (Q := Q) (P := P) (φ := φ) _hQP _hf_int _hf)
    (by positivity)

/--
%%handwave
name:
  Local \(L^2\) contraction for normalized mollifier differences
statement:
  If the support radius of a normalized nonnegative mollifier around \(Q\)
  stays inside \(P\), then convolution cannot increase the \(L^2\)-distance
  between two locally square-integrable scalar functions when the output is
  restricted to \(Q\).
proof:
  For each point of \(Q\), Jensen's inequality bounds the square of the
  averaged difference by the average of the squared difference.  Integrating
  over \(Q\), using Tonelli's theorem and translation-invariance of volume,
  moves the translated \(Q\)-integrals into \(P\), because the support radius
  condition says that all sampled points remain in \(P\).
-/
theorem normedBump_convolution_sub_eLpNorm_restrict_le_of_cthickening_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} {φ : ContDiffBump (0 : H)}
    (_hQP : Metric.cthickening φ.rOut Q ⊆ P)
    {g v : H → ℝ}
    (_hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (_hv_int : Integrable v (MeasureTheory.volume : Measure H))
    (_hg : MemLp g 2 (MeasureTheory.volume.restrict P))
    (_hv : MemLp v 2 (MeasureTheory.volume.restrict P)) :
    eLpNorm
        (fun z ↦
          ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] g : H → ℝ) z) -
            ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] v : H → ℝ) z))
        2 (MeasureTheory.volume.restrict Q) ≤
      eLpNorm (fun z ↦ g z - v z) 2 (MeasureTheory.volume.restrict P) := by
  let μ : Measure H := MeasureTheory.volume
  let k : H → ℝ := φ.normed μ
  let w : H → ℝ := fun z ↦ g z - v z
  have hw_int : Integrable w μ := _hg_int.sub _hv_int
  have hw_mem : MemLp w 2 (μ.restrict P) := _hg.sub _hv
  have hsingle :
      eLpNorm (k ⋆[lsmul ℝ ℝ, μ] w : H → ℝ)
          2 (μ.restrict Q) ≤
        eLpNorm w 2 (μ.restrict P) := by
    exact
      normedBump_convolution_eLpNorm_restrict_le_of_cthickening_subset
        (Q := Q) (P := P) (φ := φ) _hQP hw_int hw_mem
  have hkg : ConvolutionExists k g (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (L := lsmul ℝ ℝ) φ.continuous_normed _hg_int.locallyIntegrable
  have hkv : ConvolutionExists k v (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (L := lsmul ℝ ℝ) φ.continuous_normed _hv_int.locallyIntegrable
  have hconv :
      (fun z : H ↦
          ((k ⋆[lsmul ℝ ℝ, μ] g : H → ℝ) z) -
            ((k ⋆[lsmul ℝ ℝ, μ] v : H → ℝ) z))
        =
        (k ⋆[lsmul ℝ ℝ, μ] w : H → ℝ) := by
    funext x
    change (∫ t : H, k t • g (x - t) ∂μ) -
        (∫ t : H, k t • v (x - t) ∂μ) =
      ∫ t : H, k t • w (x - t) ∂μ
    have hsub :
        ∫ t : H, k t • g (x - t) - k t • v (x - t) ∂μ =
          (∫ t : H, k t • g (x - t) ∂μ) -
            (∫ t : H, k t • v (x - t) ∂μ) := by
      simpa using integral_sub (hkg x).integrable (hkv x).integrable
    rw [← hsub]
    congr 1
    funext t
    simp [w, sub_eq_add_neg, mul_add]
  calc
    eLpNorm
        (fun z ↦
          ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] g : H → ℝ) z) -
            ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] v : H → ℝ) z))
        2 (MeasureTheory.volume.restrict Q)
        = eLpNorm (k ⋆[lsmul ℝ ℝ, μ] w : H → ℝ) 2 (μ.restrict Q) := by
          simpa [k, μ] using congrArg (fun F : H → ℝ ↦ eLpNorm F 2 (μ.restrict Q)) hconv
    _ ≤ eLpNorm w 2 (μ.restrict P) := hsingle
    _ = eLpNorm (fun z ↦ g z - v z) 2 (MeasureTheory.volume.restrict P) := by
          rfl

/--
%%handwave
name:
  Standard mollifiers converge in \(L^2\) for compactly supported continuous functions
statement:
  For a compactly supported continuous scalar function, the standard
  approximate identities converge to the function in \(L^2\) on every compact
  set.
proof:
  The normalized bump convolutions converge pointwise to the function by
  continuity.  Since the function has compact support, it is bounded; the
  normalized nonnegative kernels have mass one, so all the convolutions are
  bounded by a common constant.  This common bound gives uniform
  integrability on the finite-measure compact set, and Vitali's theorem
  upgrades the almost-everywhere convergence to \(L^2\)-convergence.
-/
theorem scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_hasCompactSupport
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q : Set H} (hQ : IsCompact Q)
    {v : H → ℝ} (hv_compact : HasCompactSupport v) (hv_cont : Continuous v) :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          (fun z ↦
            (((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                  (MeasureTheory.volume : Measure H)] v : H → ℝ) z) - v z)
          2 (MeasureTheory.volume.restrict Q))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  haveI : IsFiniteMeasure μQ := isFiniteMeasure_restrict.2 hQ.measure_ne_top
  let F : ℕ → H → ℝ := fun n ↦
    (scalarWeakSobolevStandardMollifier H n).normed
        (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
        (MeasureTheory.volume : Measure H)] v
  have hv_int : Integrable v (MeasureTheory.volume : Measure H) :=
    hv_cont.integrable_of_hasCompactSupport hv_compact
  have hv_mem : MemLp v 2 μQ :=
    (hv_cont.memLp_of_hasCompactSupport
      (μ := (MeasureTheory.volume : Measure H)) hv_compact).mono_measure
        (by
          dsimp [μQ]
          exact Measure.restrict_le_self)
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n) μQ := by
    intro n
    have hφ_int :
        Integrable
          ((scalarWeakSobolevStandardMollifier H n).normed
            (MeasureTheory.volume : Measure H))
          (MeasureTheory.volume : Measure H) :=
      (scalarWeakSobolevStandardMollifier H n).integrable_normed
    have hconv_int :
        Integrable (F n) (MeasureTheory.volume : Measure H) := by
      simpa [F] using
        hφ_int.integrable_convolution
          (L := lsmul ℝ ℝ) hv_int
    exact hconv_int.aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hpointwise_volume :
      ∀ᵐ x ∂(MeasureTheory.volume : Measure H),
        Filter.Tendsto (fun n : ℕ ↦ F n x) Filter.atTop (𝓝 (v x)) := by
    filter_upwards with x
    simpa [F] using
      ContDiffBump.convolution_tendsto_right_of_continuous
        (μ := (MeasureTheory.volume : Measure H))
        (φ := fun n : ℕ ↦ scalarWeakSobolevStandardMollifier H n)
        (l := Filter.atTop)
        (scalarWeakSobolevStandardMollifier_rOut_tendsto_zero H)
        hv_cont x
  have hpointwise :
      ∀ᵐ x ∂μQ,
        Filter.Tendsto (fun n : ℕ ↦ F n x) Filter.atTop (𝓝 (v x)) :=
    ae_mono (by
      dsimp [μQ]
      exact Measure.restrict_le_self) hpointwise_volume
  rcases hv_compact.exists_bound_of_continuous hv_cont with ⟨C, hC⟩
  let B : ℝ := (Real.toNNReal C : ℝ) + 1
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hC_le_B : C ≤ B := by
    have hle : C ≤ (Real.toNNReal C : ℝ) := Real.le_coe_toNNReal C
    dsimp [B]
    exact hle.trans (le_add_of_nonneg_right zero_le_one)
  have hv_bound : ∀ x : H, ‖v x‖ ≤ B := fun x ↦ (hC x).trans hC_le_B
  let C₀ : NNReal := Real.toNNReal (3 * B) + 1
  have h3B_lt_C₀ : 3 * B < (C₀ : ℝ) := by
    have hle : 3 * B ≤ (Real.toNNReal (3 * B) : ℝ) :=
      Real.le_coe_toNNReal (3 * B)
    exact hle.trans_lt (by dsimp [C₀]; exact lt_add_one _)
  have hF_bound : ∀ n : ℕ, ∀ x : H, ‖F n x‖ ≤ 3 * B := by
    intro n x
    have hdist :
        dist (F n x) (v x) ≤ 2 * B := by
      simpa [F] using
        ContDiffBump.dist_normed_convolution_le
          (φ := scalarWeakSobolevStandardMollifier H n)
          (μ := (MeasureTheory.volume : Measure H))
          (g := v) (x₀ := x) (ε := 2 * B)
          hv_cont.aestronglyMeasurable
          (by
            intro y _hy
            calc
              dist (v y) (v x) ≤ ‖v y‖ + ‖v x‖ := dist_le_norm_add_norm _ _
              _ ≤ B + B := add_le_add (hv_bound y) (hv_bound x)
              _ = 2 * B := by ring)
    calc
      ‖F n x‖ ≤ ‖v x‖ + 2 * B := norm_le_norm_add_const_of_dist_le hdist
      _ ≤ B + 2 * B := add_le_add (hv_bound x) le_rfl
      _ = 3 * B := by ring
  have hUI : UnifIntegrable F 2 μQ := by
    refine
      MeasureTheory.unifIntegrable_of
        (μ := μQ) (p := (2 : ℝ≥0∞))
        (by norm_num) ENNReal.coe_ne_top hF_meas ?_
    intro ε hε
    refine ⟨C₀, fun n ↦ ?_⟩
    have hzero :
        ({x : H | C₀ ≤ ‖F n x‖₊}.indicator (F n)) = fun _ : H ↦ (0 : ℝ) := by
      funext x
      rw [Set.indicator_of_notMem]
      intro hx
      have hx_real : (C₀ : ℝ) ≤ ‖F n x‖ := by
        exact_mod_cast hx
      exact not_le_of_gt ((hF_bound n x).trans_lt h3B_lt_C₀) hx_real
    rw [hzero]
    simp
  exact
    MeasureTheory.tendsto_Lp_finite_of_tendsto_ae
      (μ := μQ) (p := (2 : ℝ≥0∞))
      (by norm_num) ENNReal.coe_ne_top hF_meas hv_mem hUI hpointwise

/--
%%handwave
name:
  Standard mollifiers converge in \(L^1\) for compactly supported continuous functions
statement:
  For a compactly supported continuous scalar function, the standard
  approximate identities converge to the function in \(L^1\) on every compact
  set.
proof:
  The already-proved \(L^2\)-convergence on the compact set implies
  \(L^1\)-convergence there by the finite-measure comparison
  \(\|f\|_{L^1}\le \|f\|_{L^2}\,\mu(Q)^{1/2}\).
-/
theorem scalarWeakSobolev_standardMollifier_value_eLpNorm_one_tendsto_zero_of_hasCompactSupport
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q : Set H} (hQ : IsCompact Q)
    {v : H → ℝ} (hv_compact : HasCompactSupport v) (hv_cont : Continuous v) :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          (fun z ↦
            (((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                  (MeasureTheory.volume : Measure H)] v : H → ℝ) z) - v z)
          1 (MeasureTheory.volume.restrict Q))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  let F : ℕ → H → ℝ := fun n ↦
    (scalarWeakSobolevStandardMollifier H n).normed
        (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
        (MeasureTheory.volume : Measure H)] v
  let E : ℕ → H → ℝ := fun n z ↦ F n z - v z
  let q : ℝ := 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal
  let C : ℝ≥0∞ := μQ Set.univ ^ q
  have htwo :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (E n) 2 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [E, F, μQ] using
      scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_hasCompactSupport
        hQ hv_compact hv_cont
  have hμQ_ne_top : μQ Set.univ ≠ (∞ : ℝ≥0∞) := by
    simpa [μQ] using hQ.measure_ne_top
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hC_ne_top : C ≠ (∞ : ℝ≥0∞) := by
    exact (ENNReal.rpow_lt_top_of_nonneg hq_nonneg hμQ_ne_top).ne
  have hv_int : Integrable v (MeasureTheory.volume : Measure H) :=
    hv_cont.integrable_of_hasCompactSupport hv_compact
  have hE_meas : ∀ n : ℕ, AEStronglyMeasurable (E n) μQ := by
    intro n
    have hφ_int :
        Integrable
          ((scalarWeakSobolevStandardMollifier H n).normed
            (MeasureTheory.volume : Measure H))
          (MeasureTheory.volume : Measure H) :=
      (scalarWeakSobolevStandardMollifier H n).integrable_normed
    have hF_int :
        Integrable (F n) (MeasureTheory.volume : Measure H) := by
      simpa [F] using
        hφ_int.integrable_convolution
          (L := lsmul ℝ ℝ) hv_int
    have hE_int :
        Integrable (E n) (MeasureTheory.volume : Measure H) := by
      simpa [E] using hF_int.sub hv_int
    exact hE_int.aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hle :
      ∀ n : ℕ, eLpNorm (E n) 1 μQ ≤ eLpNorm (E n) 2 μQ * C := by
    intro n
    simpa [C, q] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μQ) (f := E n)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hE_meas n)
  have hscaled :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (E n) 2 μQ * C)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using ENNReal.Tendsto.mul_const htwo (Or.inr hC_ne_top)
  rw [ENNReal.tendsto_atTop_zero] at hscaled ⊢
  intro ε hε
  rcases hscaled ε hε with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ (hle n).trans (hN n hn)⟩

/--
%%handwave
name:
  Standard mollifiers converge to the value in \(L^2\)
statement:
  For a globally integrable scalar function which is \(L^2\) on a compact
  neighborhood \(P\) of a compact set \(Q\), the standard shrinking smooth
  approximate identities converge to the function in \(L^2(Q)\).
proof:
  Write the convolution error as an average of translation errors.  Local
  \(L^2\)-continuity of translations on the larger compact set, together with
  the fact that the mollifier supports shrink to the origin and have total
  mass one, gives convergence to zero on the smaller compact set.
-/
theorem scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_global_integrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} (hQ : IsCompact Q) (_hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    {g : H → ℝ}
    (hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (hg : MemLp g 2 (MeasureTheory.volume.restrict P)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          (fun z ↦
            (((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure H)] g : H → ℝ) z) - g z)
          2 (MeasureTheory.volume.restrict Q))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  let μP : Measure H := MeasureTheory.volume.restrict P
  let δ : ℝ := Classical.choose hQP
  have hδ_pos : 0 < δ := (Classical.choose_spec hQP).1
  have hδP : Metric.cthickening δ Q ⊆ P := (Classical.choose_spec hQP).2
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hε_top : ε = (∞ : ℝ≥0∞)
  · exact ⟨0, fun n _hn ↦ by simp [hε_top]⟩
  let η : ℝ := ε.toReal / 6
  have hη_pos : 0 < η := by
    dsimp [η]
    exact div_pos (ENNReal.toReal_pos hε.ne' hε_top) (by norm_num)
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hthreeη_le : ENNReal.ofReal (3 * η) ≤ ε := by
    rw [ENNReal.ofReal_le_iff_le_toReal hε_top]
    dsimp [η]
    have hε_toReal_nonneg : 0 ≤ ε.toReal := ENNReal.toReal_nonneg
    nlinarith
  obtain ⟨v, hv_compact, hv_smooth, hv_le⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := μP) (p := (2 : ℝ≥0∞))
      ENNReal.coe_ne_top (by norm_num) hg hη_pos
  have hv_int : Integrable v (MeasureTheory.volume : Measure H) :=
    hv_smooth.continuous.integrable_of_hasCompactSupport hv_compact
  have hv_memP : MemLp v 2 μP :=
    (hv_smooth.continuous.memLp_of_hasCompactSupport
      (μ := (MeasureTheory.volume : Measure H)) hv_compact).mono_measure
        (by
          dsimp [μP]
          exact Measure.restrict_le_self)
  have hgv_Q_le :
      eLpNorm (fun z : H ↦ v z - g z) 2 μQ ≤ ENNReal.ofReal η := by
    calc
      eLpNorm (fun z : H ↦ v z - g z) 2 μQ
          ≤ eLpNorm (fun z : H ↦ v z - g z) 2 μP := by
            exact eLpNorm_mono_measure _
              (by
                dsimp [μQ, μP]
                exact Measure.restrict_mono hQP_subset le_rfl)
      _ = eLpNorm (fun z : H ↦ g z - v z) 2 μP := by
            exact eLpNorm_sub_comm v g 2 μP
      _ ≤ ENNReal.ofReal η := by
            simpa [μP, Pi.sub_apply] using hv_le
  have hv_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun z ↦
              (((scalarWeakSobolevStandardMollifier H n).normed
                    (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                    (MeasureTheory.volume : Measure H)] v : H → ℝ) z) - v z)
            2 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [μQ] using
      scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_hasCompactSupport
        hQ hv_compact hv_smooth.continuous
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        (scalarWeakSobolevStandardMollifier H n).rOut ≤ δ := by
    exact
      (scalarWeakSobolevStandardMollifier_rOut_tendsto_zero H).eventually
        (eventually_le_nhds hδ_pos)
  have hv_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm
          (fun z ↦
            (((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                  (MeasureTheory.volume : Measure H)] v : H → ℝ) z) - v z)
          2 μQ ≤ ENNReal.ofReal η :=
    hv_tendsto.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr hη_pos))
  rcases Filter.eventually_atTop.1 (hsmall.and hv_eventually) with ⟨N, hN⟩
  refine ⟨N, fun n hnN ↦ ?_⟩
  let φ : ContDiffBump (0 : H) := scalarWeakSobolevStandardMollifier H n
  let G : H → ℝ :=
    φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure H)] g
  let V : H → ℝ :=
    φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure H)] v
  have hnsmall : φ.rOut ≤ δ := by
    simpa [φ] using (hN n hnN).1
  have hNv :
      eLpNorm (fun z : H ↦ V z - v z) 2 μQ ≤ ENNReal.ofReal η := by
    simpa [V, φ] using (hN n hnN).2
  have hφQP : Metric.cthickening φ.rOut Q ⊆ P :=
    (Metric.cthickening_mono hnsmall Q).trans hδP
  have hfirst_le :
      eLpNorm (fun z : H ↦ G z - V z) 2 μQ ≤ ENNReal.ofReal η := by
    have hfirst :=
      normedBump_convolution_sub_eLpNorm_restrict_le_of_cthickening_subset
        (Q := Q) (P := P) (φ := φ) hφQP hg_int hv_int hg hv_memP
    have hfirst' :
        eLpNorm (fun z : H ↦ G z - V z) 2 μQ ≤
          eLpNorm (fun z : H ↦ g z - v z) 2 μP := by
      simpa [G, V, μQ, μP] using hfirst
    exact hfirst'.trans
        (by simpa [μP, Pi.sub_apply] using hv_le)
  have hgv_Q_le' :
      eLpNorm (fun z : H ↦ g z - v z) 2 μQ ≤ ENNReal.ofReal η := by
    calc
      eLpNorm (fun z : H ↦ g z - v z) 2 μQ
          = eLpNorm (fun z : H ↦ v z - g z) 2 μQ := by
            simpa [Pi.sub_apply] using eLpNorm_sub_comm g v 2 μQ
      _ ≤ ENNReal.ofReal η := hgv_Q_le
  have hφ_int :
      Integrable (φ.normed (MeasureTheory.volume : Measure H))
        (MeasureTheory.volume : Measure H) := φ.integrable_normed
  have hG_int : Integrable G (MeasureTheory.volume : Measure H) := by
    simpa [G] using hφ_int.integrable_convolution (L := lsmul ℝ ℝ) hg_int
  have hV_int : Integrable V (MeasureTheory.volume : Measure H) := by
    simpa [V] using hφ_int.integrable_convolution (L := lsmul ℝ ℝ) hv_int
  have hG_meas : AEStronglyMeasurable G μQ :=
    hG_int.aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hV_meas : AEStronglyMeasurable V μQ :=
    hV_int.aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hg_meas : AEStronglyMeasurable g μQ :=
    hg.aestronglyMeasurable.mono_measure (by
      dsimp [μQ, μP]
      exact Measure.restrict_mono hQP_subset le_rfl)
  have hv_meas : AEStronglyMeasurable v μQ :=
    hv_memP.aestronglyMeasurable.mono_measure (by
      dsimp [μQ, μP]
      exact Measure.restrict_mono hQP_subset le_rfl)
  have htri1 :
      eLpNorm (fun z : H ↦ G z - g z) 2 μQ ≤
        eLpNorm (fun z : H ↦ G z - V z) 2 μQ +
          eLpNorm (fun z : H ↦ V z - g z) 2 μQ := by
    have h :=
      eLpNorm_sub_le
        (μ := μQ) (p := (2 : ℝ≥0∞))
        (hG_meas.sub hV_meas) (hg_meas.sub hV_meas) (by norm_num)
    calc
      eLpNorm (fun z : H ↦ G z - g z) 2 μQ
          = eLpNorm
              ((fun z : H ↦ G z - V z) - fun z : H ↦ g z - V z)
              2 μQ := by
            congr 1
            funext z
            simp [Pi.sub_apply]
      _ ≤ eLpNorm (fun z : H ↦ G z - V z) 2 μQ +
          eLpNorm (fun z : H ↦ g z - V z) 2 μQ := h
      _ = eLpNorm (fun z : H ↦ G z - V z) 2 μQ +
          eLpNorm (fun z : H ↦ V z - g z) 2 μQ := by
            rw [show
              eLpNorm (fun z : H ↦ g z - V z) 2 μQ =
                eLpNorm (fun z : H ↦ V z - g z) 2 μQ by
                  simpa [Pi.sub_apply] using eLpNorm_sub_comm g V 2 μQ]
  have htri2 :
      eLpNorm (fun z : H ↦ V z - g z) 2 μQ ≤
        eLpNorm (fun z : H ↦ V z - v z) 2 μQ +
          eLpNorm (fun z : H ↦ g z - v z) 2 μQ := by
    have h :=
      eLpNorm_sub_le
        (μ := μQ) (p := (2 : ℝ≥0∞))
        (hV_meas.sub hv_meas) (hg_meas.sub hv_meas) (by norm_num)
    calc
      eLpNorm (fun z : H ↦ V z - g z) 2 μQ
          = eLpNorm
              ((fun z : H ↦ V z - v z) - fun z : H ↦ g z - v z)
              2 μQ := by
            congr 1
            funext z
            simp [Pi.sub_apply]
      _ ≤ eLpNorm (fun z : H ↦ V z - v z) 2 μQ +
          eLpNorm (fun z : H ↦ g z - v z) 2 μQ := h
  have htotal :
      eLpNorm (fun z : H ↦ G z - g z) 2 μQ ≤
        ENNReal.ofReal η +
          (ENNReal.ofReal η + ENNReal.ofReal η) := by
    calc
      eLpNorm (fun z : H ↦ G z - g z) 2 μQ
          ≤ eLpNorm (fun z : H ↦ G z - V z) 2 μQ +
              eLpNorm (fun z : H ↦ V z - g z) 2 μQ := htri1
      _ ≤ ENNReal.ofReal η +
              (eLpNorm (fun z : H ↦ V z - v z) 2 μQ +
                eLpNorm (fun z : H ↦ g z - v z) 2 μQ) := by
            exact add_le_add hfirst_le htri2
      _ ≤ ENNReal.ofReal η +
              (ENNReal.ofReal η + ENNReal.ofReal η) := by
            exact add_le_add le_rfl (add_le_add hNv hgv_Q_le')
  have hsum :
      ENNReal.ofReal η + (ENNReal.ofReal η + ENNReal.ofReal η) =
        ENNReal.ofReal (3 * η) := by
    rw [← ENNReal.ofReal_add hη_nonneg hη_nonneg,
      ← ENNReal.ofReal_add hη_nonneg (add_nonneg hη_nonneg hη_nonneg)]
    congr 1
    ring
  have htotalε :
      eLpNorm (fun z : H ↦ G z - g z) 2 μQ ≤ ε :=
    htotal.trans (by simpa [hsum] using hthreeη_le)
  simpa [G, φ, μQ] using htotalε

/--
%%handwave
name:
  Standard mollifiers converge to the value in local \(L^1\)
statement:
  For a globally integrable scalar function, the standard shrinking smooth
  approximate identities converge to the function in \(L^1(Q)\), provided
  the shrinking kernel neighborhoods of the compact set \(Q\) eventually lie
  in a prescribed compact neighborhood \(P\).
proof:
  Approximate the function in \(L^1(P)\) by a smooth compactly supported
  function.  The smooth approximation is stable under the standard
  mollifiers in \(L^1(Q)\).  The two remaining error terms are controlled by
  the local \(L^1\)-contraction of normalized convolution and by restricting
  the original \(L^1(P)\)-approximation to \(Q\).
-/
theorem scalarWeakSobolev_standardMollifier_value_eLpNorm_one_tendsto_zero_of_global_integrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P : Set H} (hQ : IsCompact Q) (_hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    {g : H → ℝ}
    (hg_int : Integrable g (MeasureTheory.volume : Measure H)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          (fun z ↦
            (((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure H)] g : H → ℝ) z) - g z)
          1 (MeasureTheory.volume.restrict Q))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  let μP : Measure H := MeasureTheory.volume.restrict P
  let δ : ℝ := Classical.choose hQP
  have hδ_pos : 0 < δ := (Classical.choose_spec hQP).1
  have hδP : Metric.cthickening δ Q ⊆ P := (Classical.choose_spec hQP).2
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hε_top : ε = (∞ : ℝ≥0∞)
  · exact ⟨0, fun n _hn ↦ by simp [hε_top]⟩
  let η : ℝ := ε.toReal / 6
  have hη_pos : 0 < η := by
    dsimp [η]
    exact div_pos (ENNReal.toReal_pos hε.ne' hε_top) (by norm_num)
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hthreeη_le : ENNReal.ofReal (3 * η) ≤ ε := by
    rw [ENNReal.ofReal_le_iff_le_toReal hε_top]
    dsimp [η]
    have hε_toReal_nonneg : 0 ≤ ε.toReal := ENNReal.toReal_nonneg
    nlinarith
  have hg_intP : Integrable g μP :=
    hg_int.mono_measure (by
      dsimp [μP]
      exact Measure.restrict_le_self)
  have hg_memP : MemLp g 1 μP :=
    memLp_one_iff_integrable.mpr hg_intP
  obtain ⟨v, hv_compact, hv_smooth, hv_le⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := μP) (p := (1 : ℝ≥0∞))
      ENNReal.coe_ne_top (by norm_num) hg_memP hη_pos
  have hv_int : Integrable v (MeasureTheory.volume : Measure H) :=
    hv_smooth.continuous.integrable_of_hasCompactSupport hv_compact
  have hgv_Q_le :
      eLpNorm (fun z : H ↦ v z - g z) 1 μQ ≤ ENNReal.ofReal η := by
    calc
      eLpNorm (fun z : H ↦ v z - g z) 1 μQ
          ≤ eLpNorm (fun z : H ↦ v z - g z) 1 μP := by
            exact eLpNorm_mono_measure _
              (by
                dsimp [μQ, μP]
                exact Measure.restrict_mono hQP_subset le_rfl)
      _ = eLpNorm (fun z : H ↦ g z - v z) 1 μP := by
            exact eLpNorm_sub_comm v g 1 μP
      _ ≤ ENNReal.ofReal η := by
            simpa [μP, Pi.sub_apply] using hv_le
  have hv_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun z ↦
              (((scalarWeakSobolevStandardMollifier H n).normed
                    (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                    (MeasureTheory.volume : Measure H)] v : H → ℝ) z) - v z)
            1 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [μQ] using
      scalarWeakSobolev_standardMollifier_value_eLpNorm_one_tendsto_zero_of_hasCompactSupport
        hQ hv_compact hv_smooth.continuous
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        (scalarWeakSobolevStandardMollifier H n).rOut ≤ δ := by
    exact
      (scalarWeakSobolevStandardMollifier_rOut_tendsto_zero H).eventually
        (eventually_le_nhds hδ_pos)
  have hv_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm
          (fun z ↦
            (((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                  (MeasureTheory.volume : Measure H)] v : H → ℝ) z) - v z)
          1 μQ ≤ ENNReal.ofReal η :=
    hv_tendsto.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr hη_pos))
  rcases Filter.eventually_atTop.1 (hsmall.and hv_eventually) with ⟨N, hN⟩
  refine ⟨N, fun n hnN ↦ ?_⟩
  let φ : ContDiffBump (0 : H) := scalarWeakSobolevStandardMollifier H n
  let G : H → ℝ :=
    φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure H)] g
  let V : H → ℝ :=
    φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure H)] v
  have hnsmall : φ.rOut ≤ δ := by
    simpa [φ] using (hN n hnN).1
  have hNv :
      eLpNorm (fun z : H ↦ V z - v z) 1 μQ ≤ ENNReal.ofReal η := by
    simpa [V, φ] using (hN n hnN).2
  have hφQP : Metric.cthickening φ.rOut Q ⊆ P :=
    (Metric.cthickening_mono hnsmall Q).trans hδP
  have hfirst_le :
      eLpNorm (fun z : H ↦ G z - V z) 1 μQ ≤ ENNReal.ofReal η := by
    have hfirst :=
      normedBump_convolution_sub_eLpNorm_one_restrict_le_of_cthickening_subset
        (Q := Q) (P := P) (φ := φ) hφQP hg_int hv_int
    have hfirst' :
        eLpNorm (fun z : H ↦ G z - V z) 1 μQ ≤
          eLpNorm (fun z : H ↦ g z - v z) 1 μP := by
      simpa [G, V, μQ, μP] using hfirst
    exact hfirst'.trans
        (by simpa [μP, Pi.sub_apply] using hv_le)
  have hgv_Q_le' :
      eLpNorm (fun z : H ↦ g z - v z) 1 μQ ≤ ENNReal.ofReal η := by
    calc
      eLpNorm (fun z : H ↦ g z - v z) 1 μQ
          = eLpNorm (fun z : H ↦ v z - g z) 1 μQ := by
            simpa [Pi.sub_apply] using eLpNorm_sub_comm g v 1 μQ
      _ ≤ ENNReal.ofReal η := hgv_Q_le
  have hφ_int :
      Integrable (φ.normed (MeasureTheory.volume : Measure H))
        (MeasureTheory.volume : Measure H) := φ.integrable_normed
  have hG_int : Integrable G (MeasureTheory.volume : Measure H) := by
    simpa [G] using hφ_int.integrable_convolution (L := lsmul ℝ ℝ) hg_int
  have hV_int : Integrable V (MeasureTheory.volume : Measure H) := by
    simpa [V] using hφ_int.integrable_convolution (L := lsmul ℝ ℝ) hv_int
  have hG_meas : AEStronglyMeasurable G μQ :=
    hG_int.aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hV_meas : AEStronglyMeasurable V μQ :=
    hV_int.aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hg_meas : AEStronglyMeasurable g μQ :=
    hg_int.aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have hv_meas : AEStronglyMeasurable v μQ :=
    hv_int.aestronglyMeasurable.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_le_self)
  have htri1 :
      eLpNorm (fun z : H ↦ G z - g z) 1 μQ ≤
        eLpNorm (fun z : H ↦ G z - V z) 1 μQ +
          eLpNorm (fun z : H ↦ V z - g z) 1 μQ := by
    have h :=
      eLpNorm_sub_le
        (μ := μQ) (p := (1 : ℝ≥0∞))
        (hG_meas.sub hV_meas) (hg_meas.sub hV_meas) (by norm_num)
    calc
      eLpNorm (fun z : H ↦ G z - g z) 1 μQ
          = eLpNorm
              ((fun z : H ↦ G z - V z) - fun z : H ↦ g z - V z)
              1 μQ := by
            congr 1
            funext z
            simp [Pi.sub_apply]
      _ ≤ eLpNorm (fun z : H ↦ G z - V z) 1 μQ +
          eLpNorm (fun z : H ↦ g z - V z) 1 μQ := h
      _ = eLpNorm (fun z : H ↦ G z - V z) 1 μQ +
          eLpNorm (fun z : H ↦ V z - g z) 1 μQ := by
            rw [show
              eLpNorm (fun z : H ↦ g z - V z) 1 μQ =
                eLpNorm (fun z : H ↦ V z - g z) 1 μQ by
                  simpa [Pi.sub_apply] using eLpNorm_sub_comm g V 1 μQ]
  have htri2 :
      eLpNorm (fun z : H ↦ V z - g z) 1 μQ ≤
        eLpNorm (fun z : H ↦ V z - v z) 1 μQ +
          eLpNorm (fun z : H ↦ g z - v z) 1 μQ := by
    have h :=
      eLpNorm_sub_le
        (μ := μQ) (p := (1 : ℝ≥0∞))
        (hV_meas.sub hv_meas) (hg_meas.sub hv_meas) (by norm_num)
    calc
      eLpNorm (fun z : H ↦ V z - g z) 1 μQ
          = eLpNorm
              ((fun z : H ↦ V z - v z) - fun z : H ↦ g z - v z)
              1 μQ := by
            congr 1
            funext z
            simp [Pi.sub_apply]
      _ ≤ eLpNorm (fun z : H ↦ V z - v z) 1 μQ +
          eLpNorm (fun z : H ↦ g z - v z) 1 μQ := h
  have htotal :
      eLpNorm (fun z : H ↦ G z - g z) 1 μQ ≤
        ENNReal.ofReal η +
          (ENNReal.ofReal η + ENNReal.ofReal η) := by
    calc
      eLpNorm (fun z : H ↦ G z - g z) 1 μQ
          ≤ eLpNorm (fun z : H ↦ G z - V z) 1 μQ +
              eLpNorm (fun z : H ↦ V z - g z) 1 μQ := htri1
      _ ≤ ENNReal.ofReal η +
              (eLpNorm (fun z : H ↦ V z - v z) 1 μQ +
                eLpNorm (fun z : H ↦ g z - v z) 1 μQ) := by
            exact add_le_add hfirst_le htri2
      _ ≤ ENNReal.ofReal η +
              (ENNReal.ofReal η + ENNReal.ofReal η) := by
            exact add_le_add le_rfl (add_le_add hNv hgv_Q_le')
  have hsum :
      ENNReal.ofReal η + (ENNReal.ofReal η + ENNReal.ofReal η) =
        ENNReal.ofReal (3 * η) := by
    rw [← ENNReal.ofReal_add hη_nonneg hη_nonneg,
      ← ENNReal.ofReal_add hη_nonneg (add_nonneg hη_nonneg hη_nonneg)]
    congr 1
    ring
  have htotalε :
      eLpNorm (fun z : H ↦ G z - g z) 1 μQ ≤ ε :=
    htotal.trans (by simpa [hsum] using hthreeη_le)
  simpa [G, φ, μQ] using htotalε

/--
%%handwave
name:
  Reflected mollifiers are admissible weak-derivative tests
statement:
  If the closed \(r\)-neighborhood of \(Q\) lies in the weak-derivative
  region and \(z\in Q\), then the reflected mollifier
  \(y\mapsto\varphi(z-y)\) is a smooth compactly supported test function on
  the region.
proof:
  The reflection \(y\mapsto z-y\) is a smooth homeomorphism.  The support of
  the normalized mollifier is the closed ball of radius \(r\) around the
  origin, so the reflected support is contained in the closed ball of radius
  \(r\) around \(z\), hence in the closed thickening of \(Q\).
-/
noncomputable def scalarWeakSobolev_reflectedMollifierTest
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} {φ : ContDiffBump (0 : H)}
    (z : H) (hzQ : z ∈ Q)
    (hthickening : Metric.cthickening φ.rOut Q ⊆ Ω) :
    SmoothCompactlySupportedManifoldCoordinateFunction Ω where
  toFun := fun y : H ↦ φ.normed (MeasureTheory.volume : Measure H) (z - y)
  smooth := by
    have hsub : ContDiff ℝ ∞ (fun y : H ↦ z - y) :=
      contDiff_const.sub contDiff_id
    exact φ.contDiff_normed.comp hsub
  support_subset := by
    intro y hy
    have hpre : z - y ∈ tsupport (φ.normed (MeasureTheory.volume : Measure H)) := by
      have h :=
        (Set.ext_iff.mp
          (tsupport_comp_eq_preimage
            (φ.normed (MeasureTheory.volume : Measure H))
            (Homeomorph.subLeft z)) y).mp hy
      simpa using h
    have hdist : dist y z ≤ φ.rOut := by
      rw [φ.tsupport_normed_eq (μ := (MeasureTheory.volume : Measure H))] at hpre
      simpa [dist_eq_norm, norm_sub_rev] using hpre
    exact hthickening (Metric.mem_cthickening_of_dist_le y z φ.rOut Q hzQ hdist)
  compact_support := by
    change IsCompact
      (tsupport ((φ.normed (MeasureTheory.volume : Measure H)) ∘
        (Homeomorph.subLeft z)))
    rw [tsupport_comp_eq_preimage]
    exact (Homeomorph.subLeft z).isCompact_preimage.2
      (φ.hasCompactSupport_normed (μ := (MeasureTheory.volume : Measure H)))

/--
%%handwave
name:
  Reflected mollifier tests move the weak derivative onto the kernel
statement:
  If the support of a mollifier around every point of \(Q\) remains inside
  the weak-derivative region, then testing with \(y\mapsto\varphi(z-y)\)
  gives, for each \(z\in Q\), equality between the integral of the
  directional derivative of the reflected kernel times the function and the
  integral of the reflected kernel times the weak directional derivative.
proof:
  Apply the weak integration-by-parts identity to the reflected mollifier in
  the direction \(-h\).  Differentiating \(y\mapsto z-y\) contributes a
  minus sign, and linearity of the weak derivative contributes the other
  minus sign.  Since the reflected test and its directional derivative vanish
  outside the region, the restricted integrals are the global integrals.
-/
theorem scalarWeakSobolev_reflectedMollifier_weak_identity
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} {φ : ContDiffBump (0 : H)}
    (hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {g : H → ℝ} {dg : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω g dg)
    {h : H} :
    ∀ z ∈ Q,
      ∫ y : H,
          fderiv ℝ (φ.normed (MeasureTheory.volume : Measure H)) (z - y) h * g y
            ∂(MeasureTheory.volume : Measure H) =
        ∫ y : H,
          φ.normed (MeasureTheory.volume : Measure H) (z - y) * dg y h
            ∂(MeasureTheory.volume : Measure H) := by
  intro z hzQ
  let k : H → ℝ := φ.normed (MeasureTheory.volume : Measure H)
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    scalarWeakSobolev_reflectedMollifierTest z hzQ hthickening
  have hψ := hweak ψ (-h)
  have hderiv : ∀ y : H,
      fderiv ℝ (ψ : H → ℝ) y (-h) =
        fderiv ℝ k (z - y) h := by
    intro y
    change fderiv ℝ (fun y : H ↦ k (z - y)) y (-h) =
      fderiv ℝ k (z - y) h
    have hk_smooth : ContDiff ℝ ∞ k := by
      simpa [k] using
        (φ.contDiff_normed (μ := (MeasureTheory.volume : Measure H)) (n := ⊤))
    have hk : DifferentiableAt ℝ k (z - y) :=
      (hk_smooth.differentiable (by simp)) (z - y)
    have hinner : HasFDerivAt (fun y : H ↦ z - y) (-1 : H →L[ℝ] H) y := by
      simpa using (hasFDerivAt_id y).const_sub z
    have hcomp :
        HasFDerivAt (fun y : H ↦ k (z - y))
          ((fderiv ℝ k (z - y)).comp (-1 : H →L[ℝ] H)) y :=
      hk.hasFDerivAt.comp y hinner
    rw [hcomp.fderiv]
    simp
  have hleft_global :
      ∫ y in Ω, (fderiv ℝ (ψ : H → ℝ) y (-h)) • g y
          ∂(MeasureTheory.volume : Measure H) =
        ∫ y : H, (fderiv ℝ (ψ : H → ℝ) y (-h)) • g y
          ∂(MeasureTheory.volume : Measure H) := by
    exact
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := (MeasureTheory.volume : Measure H))
        (s := Ω)
        (f := fun y : H ↦ (fderiv ℝ (ψ : H → ℝ) y (-h)) • g y)
        fun y hyΩ ↦ by
          have hyψ : y ∉ tsupport (ψ : H → ℝ) :=
            fun hyψ ↦ hyΩ (ψ.support_subset hyψ)
          have hzero : fderiv ℝ (ψ : H → ℝ) y = 0 :=
            fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (ψ : H → ℝ)) hyψ
          simp [hzero]
  have hright_global :
      ∫ y in Ω, ψ y • dg y (-h)
          ∂(MeasureTheory.volume : Measure H) =
        ∫ y : H, ψ y • dg y (-h)
          ∂(MeasureTheory.volume : Measure H) := by
    exact
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := (MeasureTheory.volume : Measure H))
        (s := Ω)
        (f := fun y : H ↦ ψ y • dg y (-h))
        fun y hyΩ ↦ by
          have hyψ : y ∉ tsupport (ψ : H → ℝ) :=
            fun hyψ ↦ hyΩ (ψ.support_subset hyψ)
          have hzero : ψ y = 0 :=
            image_eq_zero_of_notMem_tsupport hyψ
          simp [hzero]
  have hweak_global :
      ∫ y : H, (fderiv ℝ (ψ : H → ℝ) y (-h)) • g y
          ∂(MeasureTheory.volume : Measure H) =
        -∫ y : H, ψ y • dg y (-h)
          ∂(MeasureTheory.volume : Measure H) := by
    have hweak_eq := hψ.2.2
    rw [hleft_global, hright_global] at hweak_eq
    exact hweak_eq
  calc
    ∫ y : H, fderiv ℝ k (z - y) h * g y
        ∂(MeasureTheory.volume : Measure H)
        =
        ∫ y : H, (fderiv ℝ (ψ : H → ℝ) y (-h)) • g y
        ∂(MeasureTheory.volume : Measure H) := by
          refine integral_congr_ae ?_
          exact ae_of_all (MeasureTheory.volume : Measure H) fun y ↦ by
            simp [smul_eq_mul, hderiv y]
    _ =
        -∫ y : H, ψ y • dg y (-h)
        ∂(MeasureTheory.volume : Measure H) := hweak_global
    _ =
        -∫ y : H, -(k (z - y) * dg y h)
        ∂(MeasureTheory.volume : Measure H) := by
          congr 1
          refine integral_congr_ae ?_
          exact ae_of_all (MeasureTheory.volume : Measure H) fun y ↦ by
            simp [ψ, scalarWeakSobolev_reflectedMollifierTest, k, smul_eq_mul]
    _ =
        ∫ y : H, k (z - y) * dg y h
        ∂(MeasureTheory.volume : Measure H) := by
          rw [integral_neg, neg_neg]

/--
%%handwave
name:
  The derivative kernel represents convolution with the weak derivative
statement:
  Under the same support condition, the convolution of \(g\) against the
  directional derivative of the mollifier kernel equals the convolution of
  the weak directional derivative against the mollifier kernel at every point
  of \(Q\).
proof:
  Fix \(z\in Q\) and use the test function \(y\mapsto\varphi(z-y)\).  Its
  support lies in the prescribed thickening of \(Q\), hence inside the open
  weak-derivative region.  The weak integration-by-parts identity gives
  exactly the desired equality after rewriting the two integrals in the
  convolution convention.
-/
theorem scalarWeakSobolev_mollifier_derivativeKernel_convolution_eq_weakDerivative_convolution_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (_hQ : IsCompact Q)
    {φ : ContDiffBump (0 : H)}
    (_hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {g : H → ℝ} {dg : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω g dg)
    {h : H}
    (_hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (_hdg_int : Integrable (fun z ↦ dg z h) (MeasureTheory.volume : Measure H)) :
    ∀ z ∈ Q,
      (((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure H))) ⋆[
          (lsmul ℝ ℝ).precompL H, (MeasureTheory.volume : Measure H)] g :
          H → H →L[ℝ] ℝ) z) h =
        ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
          (MeasureTheory.volume : Measure H)] (fun y : H ↦ dg y h) :
          H → ℝ) z) := by
  intro z hzQ
  let k : H → ℝ := φ.normed (MeasureTheory.volume : Measure H)
  let gd : H → ℝ := fun y ↦ dg y h
  have hweak_int :
      ∫ y : H, fderiv ℝ k (z - y) h * g y
          ∂(MeasureTheory.volume : Measure H) =
        ∫ y : H, k (z - y) * gd y
          ∂(MeasureTheory.volume : Measure H) := by
    simpa [k, gd] using
      scalarWeakSobolev_reflectedMollifier_weak_identity
        (Q := Q) (Ω := Ω) (φ := φ) _hthickening _hweak (h := h) z hzQ
  have hleft_exists :
      ConvolutionExistsAt (fderiv ℝ k) g z
        ((lsmul ℝ ℝ).precompL H) (MeasureTheory.volume : Measure H) := by
    have hk_support : HasCompactSupport (fderiv ℝ k) :=
      φ.hasCompactSupport_normed.fderiv (𝕜 := ℝ)
    have hk_smooth : ContDiff ℝ ∞ k := by
      simpa [k] using
        (φ.contDiff_normed (μ := (MeasureTheory.volume : Measure H)) (n := ⊤))
    have hk_cont : Continuous (fderiv ℝ k) :=
      hk_smooth.continuous_fderiv (by simp)
    exact
      HasCompactSupport.convolutionExists_left
        (μ := (MeasureTheory.volume : Measure H))
        (f := fderiv ℝ k) (g := g)
        (L := (lsmul ℝ ℝ).precompL H)
        hk_support hk_cont _hg_int.locallyIntegrable z
  have hleft :
      (((fderiv ℝ k) ⋆[
          (lsmul ℝ ℝ).precompL H, (MeasureTheory.volume : Measure H)] g :
          H → H →L[ℝ] ℝ) z) h =
        ∫ y : H, fderiv ℝ k (z - y) h * g y
          ∂(MeasureTheory.volume : Measure H) := by
    rw [MeasureTheory.convolution_eq_swap]
    rw [ContinuousLinearMap.integral_apply hleft_exists.integrable_swap h]
    rfl
  have hright :
      ((k ⋆[lsmul ℝ ℝ, (MeasureTheory.volume : Measure H)] gd : H → ℝ) z) =
        ∫ y : H, k (z - y) * gd y
          ∂(MeasureTheory.volume : Measure H) := by
    simpa [gd, smul_eq_mul] using
      (MeasureTheory.convolution_lsmul_swap
        (μ := (MeasureTheory.volume : Measure H)) (f := k) (g := gd) (x := z))
  calc
    (((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure H))) ⋆[
        (lsmul ℝ ℝ).precompL H, (MeasureTheory.volume : Measure H)] g :
        H → H →L[ℝ] ℝ) z) h
        = ∫ y : H, fderiv ℝ k (z - y) h * g y
          ∂(MeasureTheory.volume : Measure H) := by
            simpa [k] using hleft
    _ = ∫ y : H, k (z - y) * gd y
          ∂(MeasureTheory.volume : Measure H) := hweak_int
    _ = ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
          (MeasureTheory.volume : Measure H)] (fun y : H ↦ dg y h) :
          H → ℝ) z) := by
            simpa [k, gd] using hright.symm

/--
%%handwave
name:
  Mollification commutes with the weak directional derivative on a compact set
statement:
  Let \(Q\) be contained in an open weak-derivative region, and let the
  support radius of a mollifier be small enough that the closed thickening of
  \(Q\) by that radius still lies in the region.  Then, on \(Q\), the
  classical directional derivative of the mollification of \(g\) agrees
  almost everywhere with the mollification of the weak directional derivative
  \(dg(h)\).
proof:
  Test against compactly supported functions on \(Q\).  After expanding the
  convolution and translating the test functions, the support condition keeps
  all translated tests inside the open weak-derivative region.  The weak
  integration-by-parts identity transfers the derivative from the test to
  \(g\), Fubini interchanges the test and mollifier integrations, and the
  resulting distributional identity identifies the smooth derivative with the
  mollified weak derivative.
-/
theorem scalarWeakSobolev_mollifier_directionalDerivative_ae_eq_convolution_weakDerivative_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (_hQ : IsCompact Q)
    {φ : ContDiffBump (0 : H)}
    (_hthickening : Metric.cthickening φ.rOut Q ⊆ Ω)
    {g : H → ℝ} {dg : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω g dg)
    {h : H}
    (_hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (_hdg_int : Integrable (fun z ↦ dg z h) (MeasureTheory.volume : Measure H)) :
    (fun z : H ↦
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure H)] g : H → ℝ) z h)
      =ᵐ[MeasureTheory.volume.restrict Q]
        fun z : H ↦
          ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure H)] (fun y : H ↦ dg y h) :
            H → ℝ) z) := by
  have hkernel :=
    scalarWeakSobolev_mollifier_derivativeKernel_convolution_eq_weakDerivative_convolution_on_compact
      _hQ _hthickening _hweak _hg_int _hdg_int
  exact ae_restrict_of_forall_mem _hQ.measurableSet fun z hzQ ↦ by
    have hclassical :
        fderiv ℝ
            (φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
              (MeasureTheory.volume : Measure H)] g : H → ℝ) z =
          (((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure H))) ⋆[
              (lsmul ℝ ℝ).precompL H,
              (MeasureTheory.volume : Measure H)] g :
              H → H →L[ℝ] ℝ) z) := by
      exact
        (φ.hasCompactSupport_normed.hasFDerivAt_convolution_left
          (lsmul ℝ ℝ) φ.contDiff_normed _hg_int.locallyIntegrable z).fderiv
    calc
      fderiv ℝ
          (φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure H)] g : H → ℝ) z h
          =
          (((fderiv ℝ (φ.normed (MeasureTheory.volume : Measure H))) ⋆[
              (lsmul ℝ ℝ).precompL H,
              (MeasureTheory.volume : Measure H)] g :
              H → H →L[ℝ] ℝ) z) h := by
            rw [hclassical]
      _ =
          ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
            (MeasureTheory.volume : Measure H)] (fun y : H ↦ dg y h) :
            H → ℝ) z) :=
            hkernel z hzQ

/--
%%handwave
name:
  Standard mollifier derivatives converge to the weak directional derivative
statement:
  Let \(Q\subset P\subset\Omega\) with a positive thickening of \(Q\) inside
  \(P\).  If \(g\) has weak differential \(dg\) on \(\Omega\), if
  \(g,dg(\cdot)h\) are globally integrable and lie in \(L^2(P)\), then
  \[
    D_h(\rho_n*g)\longrightarrow dg(\cdot)h
      \quad\text{in }L^2(Q).
  \]
proof:
  Use [mollification commutes with the weak directional derivative on
  \(Q\)](lean:JJMath.Uniformization.scalarWeakSobolev_mollifier_directionalDerivative_ae_eq_convolution_weakDerivative_on_compact),
  then apply [standard mollifiers converge in \(L^2(Q)\)](lean:JJMath.Uniformization.scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_global_integrable)
  to \(dg(\cdot)h\).
-/
theorem scalarWeakSobolev_standardMollifier_directionalDerivative_eLpNorm_tendsto_zero_of_global_integrable_pair
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {g : H → ℝ} {dg : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω g dg)
    {h : H}
    (_hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (_hdg_int : Integrable (fun z ↦ dg z h) (MeasureTheory.volume : Measure H))
    (_hg : MemLp g 2 (MeasureTheory.volume.restrict P))
    (_hdg : MemLp (fun z ↦ dg z h) 2 (MeasureTheory.volume.restrict P)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          (fun z ↦
            fderiv ℝ
                ((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                  (MeasureTheory.volume : Measure H)] g : H → ℝ) z h -
              dg z h)
          2 (MeasureTheory.volume.restrict Q))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  let μ : Measure H := MeasureTheory.volume.restrict Q
  let gd : H → ℝ := fun z ↦ dg z h
  let δ : ℝ := Classical.choose _hQP
  have hδ_pos : 0 < δ := (Classical.choose_spec _hQP).1
  have hδP : Metric.cthickening δ Q ⊆ P := (Classical.choose_spec _hQP).2
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        (scalarWeakSobolevStandardMollifier H n).rOut ≤ δ := by
    exact
      (scalarWeakSobolevStandardMollifier_rOut_tendsto_zero H).eventually
        (eventually_le_nhds hδ_pos)
  have hcomm :
      ∀ᶠ n : ℕ in Filter.atTop,
        (fun z : H ↦
          fderiv ℝ
              ((scalarWeakSobolevStandardMollifier H n).normed
                (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                (MeasureTheory.volume : Measure H)] g : H → ℝ) z h)
          =ᵐ[μ]
            fun z : H ↦
              (((scalarWeakSobolevStandardMollifier H n).normed
                (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                (MeasureTheory.volume : Measure H)] gd : H → ℝ) z) := by
    filter_upwards [hsmall] with n hn
    have hthickening :
        Metric.cthickening (scalarWeakSobolevStandardMollifier H n).rOut Q ⊆ Ω :=
      (Metric.cthickening_mono hn Q).trans (hδP.trans _hPΩ)
    exact
      scalarWeakSobolev_mollifier_directionalDerivative_ae_eq_convolution_weakDerivative_on_compact
        _hQ hthickening _hweak _hg_int _hdg_int
  have hgd_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun z ↦
              (((scalarWeakSobolevStandardMollifier H n).normed
                    (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                    (MeasureTheory.volume : Measure H)] gd : H → ℝ) z) -
                gd z)
            2 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [μ, gd] using
      scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_global_integrable
        _hQ _hP _hQP _hdg_int _hdg
  refine hgd_tendsto.congr' ?_
  filter_upwards [hcomm] with n hn
  exact
    eLpNorm_congr_ae
      ((hn.symm.sub Filter.EventuallyEq.rfl) :
        (fun z : H ↦
          (((scalarWeakSobolevStandardMollifier H n).normed
                (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                (MeasureTheory.volume : Measure H)] gd : H → ℝ) z) -
            gd z)
          =ᵐ[μ]
            fun z : H ↦
          fderiv ℝ
              ((scalarWeakSobolevStandardMollifier H n).normed
                (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                (MeasureTheory.volume : Measure H)] g : H → ℝ) z h -
            dg z h)

/--
%%handwave
name:
  Standard mollifiers converge in the local graph norm
statement:
  Under the same compact-containment and integrability hypotheses, the
  standard mollifications satisfy
  \[
    \rho_n*g\to g,\qquad D_h(\rho_n*g)\to dg(\cdot)h
      \quad\text{in }L^2(Q).
  \]
proof:
  Combine [standard mollifiers converge to the value](lean:JJMath.Uniformization.scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_global_integrable)
  with [standard mollifier derivatives converge to the weak directional
  derivative](lean:JJMath.Uniformization.scalarWeakSobolev_standardMollifier_directionalDerivative_eLpNorm_tendsto_zero_of_global_integrable_pair).
-/
theorem scalarWeakSobolev_standardMollifier_graph_eLpNorm_tendsto_zero_of_global_integrable_pair
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {g : H → ℝ} {dg : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω g dg)
    {h : H}
    (_hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (_hdg_int : Integrable (fun z ↦ dg z h) (MeasureTheory.volume : Measure H))
    (_hg : MemLp g 2 (MeasureTheory.volume.restrict P))
    (_hdg : MemLp (fun z ↦ dg z h) 2 (MeasureTheory.volume.restrict P)) :
    Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun z ↦
              (((scalarWeakSobolevStandardMollifier H n).normed
                    (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                    (MeasureTheory.volume : Measure H)] g : H → ℝ) z) - g z)
            2 (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun z ↦
              fderiv ℝ
                  ((scalarWeakSobolevStandardMollifier H n).normed
                    (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                    (MeasureTheory.volume : Measure H)] g : H → ℝ) z h -
                dg z h)
            2 (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  exact
    ⟨scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_global_integrable
        _hQ _hP _hQP _hg_int _hg,
      scalarWeakSobolev_standardMollifier_directionalDerivative_eLpNorm_tendsto_zero_of_global_integrable_pair
        _hQ _hP _hQP _hPΩ _hΩ_open _hweak _hg_int _hdg_int _hg _hdg⟩

/--
%%handwave
name:
  A mollifier scale with graph \(L^2\) control
statement:
  Under the same hypotheses, for every \(\varepsilon>0\) there is a smooth
  approximate identity \(\rho\) such that
  \[
    \|\rho*g-g\|_{L^2(Q)}\le\varepsilon,\qquad
    \|D_h(\rho*g)-dg(\cdot)h\|_{L^2(Q)}\le\varepsilon .
  \]
proof:
  Extract a large enough scale from [convergence in the local graph
  norm](lean:JJMath.Uniformization.scalarWeakSobolev_standardMollifier_graph_eLpNorm_tendsto_zero_of_global_integrable_pair).
-/
theorem scalarWeakSobolev_exists_mollifier_graph_approx_of_global_integrable_pair
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {g : H → ℝ} {dg : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω g dg)
    {h : H}
    (_hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (_hdg_int : Integrable (fun z ↦ dg z h) (MeasureTheory.volume : Measure H))
    (_hg : MemLp g 2 (MeasureTheory.volume.restrict P))
    (_hdg : MemLp (fun z ↦ dg z h) 2 (MeasureTheory.volume.restrict P))
    {ε : ℝ} (_hε : 0 < ε) :
    ∃ φ : ContDiffBump (0 : H),
      eLpNorm
          (fun z ↦
            ((φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                (MeasureTheory.volume : Measure H)] g : H → ℝ) z) - g z)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε ∧
        eLpNorm
          (fun z ↦
            fderiv ℝ
                (φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                  (MeasureTheory.volume : Measure H)] g : H → ℝ) z h -
              dg z h)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε := by
  rcases
    scalarWeakSobolev_standardMollifier_graph_eLpNorm_tendsto_zero_of_global_integrable_pair
      _hQ _hP _hQP _hPΩ _hΩ_open _hweak _hg_int _hdg_int _hg _hdg with
    ⟨hvalue_tendsto, hderiv_tendsto⟩
  have hεENN : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr _hε
  have hvalue_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm
          (fun z ↦
            (((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                  (MeasureTheory.volume : Measure H)] g : H → ℝ) z) - g z)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε :=
    hvalue_tendsto.eventually (eventually_le_nhds hεENN)
  have hderiv_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm
          (fun z ↦
            fderiv ℝ
                ((scalarWeakSobolevStandardMollifier H n).normed
                  (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
                  (MeasureTheory.volume : Measure H)] g : H → ℝ) z h -
              dg z h)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε :=
    hderiv_tendsto.eventually (eventually_le_nhds hεENN)
  rcases (hvalue_eventually.and hderiv_eventually).exists with
    ⟨n, hvalue, hderiv⟩
  exact ⟨scalarWeakSobolevStandardMollifier H n, hvalue, hderiv⟩

/--
%%handwave
name:
  One-step smooth graph approximation for a globally integrable weak pair
statement:
  Under the same hypotheses, for every \(\varepsilon>0\) there is a smooth
  function \(v\) such that
  \[
    \|v-g\|_{L^2(Q)}\le\varepsilon,\qquad
    \|D_hv-dg(\cdot)h\|_{L^2(Q)}\le\varepsilon .
  \]
proof:
  Choose the mollifier supplied by [graph \(L^2\) control at one
  scale](lean:JJMath.Uniformization.scalarWeakSobolev_exists_mollifier_graph_approx_of_global_integrable_pair)
  and set \(v=\rho*g\).
-/
theorem scalarWeakSobolev_exists_local_contDiff_graph_approx_of_global_integrable_pair
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {g : H → ℝ} {dg : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω g dg)
    {h : H}
    (_hg_int : Integrable g (MeasureTheory.volume : Measure H))
    (_hdg_int : Integrable (fun z ↦ dg z h) (MeasureTheory.volume : Measure H))
    (_hg : MemLp g 2 (MeasureTheory.volume.restrict P))
    (_hdg : MemLp (fun z ↦ dg z h) 2 (MeasureTheory.volume.restrict P))
    {ε : ℝ} (_hε : 0 < ε) :
    ∃ v : H → ℝ,
      ContDiff ℝ ∞ v ∧
        eLpNorm (fun z ↦ v z - g z)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε ∧
        eLpNorm (fun z ↦ fderiv ℝ v z h - dg z h)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε := by
  rcases
    scalarWeakSobolev_exists_mollifier_graph_approx_of_global_integrable_pair
      _hQ _hP _hQP _hPΩ _hΩ_open _hweak _hg_int _hdg_int _hg _hdg _hε with
    ⟨φ, hvalue, hderiv⟩
  let v : H → ℝ :=
    (φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure H)] g : H → ℝ)
  refine ⟨v, ?_, ?_, ?_⟩
  · dsimp [v]
    exact
      φ.hasCompactSupport_normed.contDiff_convolution_left
        (lsmul ℝ ℝ) φ.contDiff_normed _hg_int.locallyIntegrable
  · simpa [v] using hvalue
  · simpa [v] using hderiv

/--
%%handwave
name:
  One-step smooth approximation for a cutoff-localized weak pair
statement:
  After multiplying by a smooth cutoff supported in the weak-derivative
  region, the localized weak Sobolev pair admits one smooth approximation
  whose value and chosen directional derivative are within a prescribed
  \(L^2(Q)\) tolerance.
proof:
  The cutoff makes the localized value and derivative globally integrable and
  \(L^2(P)\).  Apply [one-step smooth graph approximation for a globally
  integrable weak pair](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_contDiff_graph_approx_of_global_integrable_pair)
  to \((\chi u,\chi\,du+u\,d\chi)\).
-/
theorem scalarWeakSobolev_exists_local_contDiff_graph_approx_of_cutoff_localization
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hlocalizedWeak :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Ω
        (fun z ↦ χ z * u z)
        (scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du))
    {h : H}
    (_hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H))
    (_hdu_loc : LocallyIntegrableOn (fun z ↦ du z h) Ω
      (MeasureTheory.volume : Measure H))
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (_hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    {ε : ℝ} (_hε : 0 < ε) :
    ∃ v : H → ℝ,
      ContDiff ℝ ∞ v ∧
        eLpNorm (fun z ↦ v z - χ z * u z)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε ∧
        eLpNorm
          (fun z ↦
            fderiv ℝ v z h -
              scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε := by
  have hvalue_int : Integrable (fun z ↦ χ z * u z)
      (MeasureTheory.volume : Measure H) :=
    scalarWeakSobolevCutoff_value_integrable χ _hu_loc
  have hderiv_int :
      Integrable
        (fun z ↦ scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
        (MeasureTheory.volume : Measure H) :=
    scalarWeakSobolevCutoff_derivative_integrable χ _hu_loc _hdu_loc
  have hvalue_memLp :
      MemLp (fun z ↦ χ z * u z) 2
        (MeasureTheory.volume.restrict P) :=
    scalarWeakSobolevCutoff_value_memLp_on_compact _hP χ _hu
  have hderiv_memLp :
      MemLp
        (fun z ↦ scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
        2 (MeasureTheory.volume.restrict P) :=
    scalarWeakSobolevCutoff_derivative_memLp_on_compact _hP χ _hdu
  exact
    scalarWeakSobolev_exists_local_contDiff_graph_approx_of_global_integrable_pair
      _hQ _hP _hQP _hPΩ _hΩ_open _hlocalizedWeak hvalue_int hderiv_int
      hvalue_memLp hderiv_memLp _hε

/--
%%handwave
name:
  One-step mollifier graph approximation for a locally integrable pair
statement:
  Given a scalar weak Sobolev pair on an open Euclidean region, and given
  \(\varepsilon>0\), there is a smooth function whose values and chosen
  directional derivative are both within \(\varepsilon\) in \(L^2(Q)\),
  provided the function and directional derivative are locally integrable on
  the region where the weak derivative identity holds.
proof:
  Choose a cutoff equal to one on \(Q\), use the product rule for the
  localized weak pair, apply [one-step approximation after cutoff
  localization](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_contDiff_graph_approx_of_cutoff_localization),
  and then remove the cutoff on \(Q\).
-/
theorem scalarWeakSobolev_exists_local_contDiff_graph_approx_of_locallyIntegrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {f : H → ℝ} {df : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω f df)
    {h : H}
    (_hf_loc : LocallyIntegrableOn f Ω (MeasureTheory.volume : Measure H))
    (_hdf_loc : LocallyIntegrableOn (fun z ↦ df z h) Ω
      (MeasureTheory.volume : Measure H))
    (_hf : MemLp f 2 (MeasureTheory.volume.restrict P))
    (_hdf : MemLp (fun z ↦ df z h) 2 (MeasureTheory.volume.restrict P))
    {ε : ℝ} (_hε : 0 < ε) :
    ∃ v : H → ℝ,
      ContDiff ℝ ∞ v ∧
        eLpNorm (fun z ↦ v z - f z)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε ∧
        eLpNorm (fun z ↦ fderiv ℝ v z h - df z h)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε := by
  rcases exists_scalarWeakSobolevCutoff _hP _hPΩ _hΩ_open with ⟨χ⟩
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset _hQP
  have hlocalizedWeak :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Ω
        (fun z ↦ χ z * f z)
        (scalarWeakSobolevCutoffDerivative (χ : H → ℝ) f df) :=
    scalarWeakSobolevCutoffDerivative_weakDerivative χ _hweak _hf_loc
  rcases
    scalarWeakSobolev_exists_local_contDiff_graph_approx_of_cutoff_localization
      _hQ _hP _hQP _hPΩ _hΩ_open χ hlocalizedWeak _hf_loc _hdf_loc _hf _hdf _hε with
    ⟨v, hv_smooth, hv_value, hv_deriv⟩
  let μ : Measure H := MeasureTheory.volume.restrict Q
  have hvalue_ae :
      (fun z : H ↦ χ z * f z) =ᵐ[μ] f := by
    exact ae_restrict_of_forall_mem _hQ.measurableSet fun z hzQ ↦ by
      simp [χ.eq_one_on z (hQP_subset hzQ)]
  have hderiv_ae :
      (fun z : H ↦ scalarWeakSobolevCutoffDerivative (χ : H → ℝ) f df z h)
        =ᵐ[μ] fun z ↦ df z h := by
    exact ae_restrict_of_forall_mem _hQ.measurableSet fun z hzQ ↦ by
      exact χ.cutoffDerivative_eq_on z (hQP_subset hzQ)
  refine ⟨v, hv_smooth, ?_, ?_⟩
  · calc
      eLpNorm (fun z : H ↦ v z - f z) 2 μ
          = eLpNorm (fun z : H ↦ v z - χ z * f z) 2 μ := by
            exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hvalue_ae.symm)
      _ ≤ ENNReal.ofReal ε := hv_value
  · calc
      eLpNorm (fun z : H ↦ fderiv ℝ v z h - df z h) 2 μ
          =
          eLpNorm
            (fun z : H ↦
              fderiv ℝ v z h -
                scalarWeakSobolevCutoffDerivative (χ : H → ℝ) f df z h)
            2 μ := by
            exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hderiv_ae.symm)
      _ ≤ ENNReal.ofReal ε := hv_deriv

/--
%%handwave
name:
  One-step local smooth graph approximation in a nonzero direction
statement:
  Given a scalar weak Sobolev pair on an open Euclidean region, and given
  \(\varepsilon>0\), there is a smooth function whose values and nonzero
  directional derivative are both within \(\varepsilon\) in \(L^2(Q)\).
proof:
  In a nonzero direction, the weak derivative identity implies local
  integrability of the function and of the chosen directional derivative.
  Then apply [one-step approximation for locally integrable weak
  pairs](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_contDiff_graph_approx_of_locallyIntegrable).
-/
theorem scalarWeakSobolev_exists_local_contDiff_graph_approx_nonzero_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {f : H → ℝ} {df : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω f df)
    {h : H}
    (hh : h ≠ 0)
    (_hf : MemLp f 2 (MeasureTheory.volume.restrict P))
    (_hdf : MemLp (fun z ↦ df z h) 2 (MeasureTheory.volume.restrict P))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : H → ℝ,
      ContDiff ℝ ∞ v ∧
        eLpNorm (fun z ↦ v z - f z)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε ∧
        eLpNorm (fun z ↦ fderiv ℝ v z h - df z h)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε := by
  have hf_loc : LocallyIntegrableOn f Ω (MeasureTheory.volume : Measure H) :=
    kinnunenWeakDerivative_function_locallyIntegrableOn_of_nonzero_direction
      _hΩ_open _hweak hh
  have hdf_loc : LocallyIntegrableOn (fun z ↦ df z h) Ω
      (MeasureTheory.volume : Measure H) :=
    kinnunenWeakDerivative_directionalDerivative_locallyIntegrableOn
      _hΩ_open _hweak h
  exact
    scalarWeakSobolev_exists_local_contDiff_graph_approx_of_locallyIntegrable
      _hQ _hP _hQP _hPΩ _hΩ_open _hweak hf_loc hdf_loc _hf _hdf hε

/--
%%handwave
name:
  One-step local smooth graph approximation on a compact set
statement:
  Given a scalar weak Sobolev pair on an open Euclidean region, and given
  \(\varepsilon>0\), there is a smooth function whose values and chosen
  directional derivative are both within \(\varepsilon\) in \(L^2(Q)\).
proof:
  In the zero direction this is ordinary smooth density in \(L^2(Q)\), since
  both the classical and weak directional derivatives vanish.  In a nonzero
  direction, use [one-step approximation in a nonzero
  direction](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_contDiff_graph_approx_nonzero_on_compact).
-/
theorem scalarWeakSobolev_exists_local_contDiff_graph_approx_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {f : H → ℝ} {df : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω f df)
    {h : H}
    (_hf : MemLp f 2 (MeasureTheory.volume.restrict P))
    (_hdf : MemLp (fun z ↦ df z h) 2 (MeasureTheory.volume.restrict P))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : H → ℝ,
      ContDiff ℝ ∞ v ∧
        eLpNorm (fun z ↦ v z - f z)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε ∧
        eLpNorm (fun z ↦ fderiv ℝ v z h - df z h)
          2 (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε := by
  by_cases hh : h = 0
  · subst h
    let μ : Measure H := MeasureTheory.volume.restrict Q
    have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset _hQP
    have hf_Q : MemLp f 2 μ :=
      _hf.mono_measure (by
        dsimp [μ]
        exact Measure.restrict_mono hQP_subset le_rfl)
    obtain ⟨v, _hv_compact, hv_smooth, hv_le⟩ :=
      MeasureTheory.MemLp.exist_eLpNorm_sub_le
        (μ := μ) (p := (2 : ℝ≥0∞))
        ENNReal.coe_ne_top (by norm_num) hf_Q hε
    refine ⟨v, hv_smooth, ?_, ?_⟩
    · have hv_le' :
          eLpNorm (v - f) 2 μ ≤ ENNReal.ofReal ε := by
        rw [eLpNorm_sub_comm v f 2 μ]
        exact hv_le
      simpa [μ, Pi.sub_apply] using hv_le'
    · have hzero :
          (fun z : H ↦ fderiv ℝ v z (0 : H) - df z 0) =
            fun _ : H ↦ (0 : ℝ) := by
        funext z
        simp
      rw [hzero]
      simp
  · exact
      scalarWeakSobolev_exists_local_contDiff_graph_approx_nonzero_on_compact
        _hQ _hP _hQP _hPΩ _hΩ_open _hweak hh _hf _hdf hε

/--
%%handwave
name:
  Local Sobolev graph-density on a compact set
statement:
  A scalar weak Sobolev pair \((f,df)\) on an open Euclidean region admits
  smooth \(v_n\) such that
  \[
    v_n\to f,\qquad D_hv_n\to df(\cdot)h
      \quad\text{in }L^2(Q),
  \]
  whenever \(Q\Subset P\Subset\Omega\) and both terms are \(L^2(P)\).
proof:
  Apply [one-step smooth graph approximation on \(Q\)](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_contDiff_graph_approx_on_compact)
  with tolerances \((n+1)^{-1}\), and squeeze the two \(L^2\)-errors to zero.
-/
theorem scalarWeakSobolev_exists_local_smoothApprox_graph_density_of_memLp
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {f : H → ℝ} {df : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω f df)
    {h : H}
    (_hf : MemLp f 2 (MeasureTheory.volume.restrict P))
    (_hdf : MemLp (fun z ↦ df z h) 2 (MeasureTheory.volume.restrict P)) :
    Nonempty
      (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q f df h) := by
  classical
  let μ : Measure H := MeasureTheory.volume.restrict Q
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset _hQP
  have hf_Q : MemLp f 2 μ :=
    _hf.mono_measure (by
      dsimp [μ]
      exact Measure.restrict_mono hQP_subset le_rfl)
  have hdf_Q : MemLp (fun z ↦ df z h) 2 μ :=
    _hdf.mono_measure (by
      dsimp [μ]
      exact Measure.restrict_mono hQP_subset le_rfl)
  have happrox :
      ∀ n : ℕ, ∃ v : H → ℝ,
        ContDiff ℝ ∞ v ∧
          eLpNorm (fun z ↦ v z - f z) 2 μ ≤
              ENNReal.ofReal (((n : ℝ) + 1)⁻¹) ∧
          eLpNorm (fun z ↦ fderiv ℝ v z h - df z h) 2 μ ≤
              ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
    intro n
    exact
      scalarWeakSobolev_exists_local_contDiff_graph_approx_on_compact
        _hQ _hP _hQP _hPΩ _hΩ_open _hweak _hf _hdf
        (by positivity : 0 < (((n : ℝ) + 1)⁻¹))
  choose v hv_smooth hv_value_le hv_deriv_le using happrox
  refine
    ⟨{ approximants := v
       smooth := hv_smooth
       value_aestronglyMeasurable := ?_
       value_tendsto_l2 := ?_
       directionalDerivative_aestronglyMeasurable := ?_
       directionalDerivative_tendsto_l2 := ?_ }⟩
  · intro n
    exact (hv_smooth n).continuous.aestronglyMeasurable.sub
      hf_Q.aestronglyMeasurable
  · have hle :
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ v n z - f z) 2 μ) ≤
            fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
      intro n
      exact hv_value_le n
    have hupper :
        Filter.Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) + 1)⁻¹))
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have hreal :
          Filter.Tendsto
            (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹))
            Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using ENNReal.tendsto_ofReal hreal
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ ↦ zero_le) hle
  · intro n
    have hcont :
        Continuous (fun z : H ↦ fderiv ℝ (v n) z h) :=
      ((hv_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
    exact hcont.aestronglyMeasurable.sub hdf_Q.aestronglyMeasurable
  · have hle :
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ fderiv ℝ (v n) z h - df z h) 2 μ) ≤
            fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
      intro n
      exact hv_deriv_le n
    have hupper :
        Filter.Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) + 1)⁻¹))
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have hreal :
          Filter.Tendsto
            (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹))
            Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using ENNReal.tendsto_ofReal hreal
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ ↦ zero_le) hle

/--
%%handwave
name:
  Mollifier graph-density for a localized weak Sobolev pair
statement:
  If the localized pair \((\chi u,\chi\,du+u\,d\chi)\) satisfies the weak
  derivative identity on \(\Omega\), then it admits smooth approximants
  converging to that pair in the directional graph norm on \(Q\).
proof:
  The cutoff gives the required \(L^2(P)\) bounds for the localized pair, so
  apply [local Sobolev graph-density on a compact set](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_smoothApprox_graph_density_of_memLp).
-/
theorem scalarWeakSobolev_exists_local_smoothApprox_of_localized_weakDerivative
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hlocalizedWeak :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Ω
        (fun z ↦ χ z * u z)
        (scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du))
    {h : H}
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (_hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P)) :
    Nonempty
      (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q
        (fun z ↦ χ z * u z)
        (scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du) h) := by
  have hvalue_memLp :
      MemLp (fun z ↦ χ z * u z) 2
        (MeasureTheory.volume.restrict P) :=
    scalarWeakSobolevCutoff_value_memLp_on_compact _hP χ _hu
  have hderiv_memLp :
      MemLp
        (fun z ↦ scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du z h)
        2 (MeasureTheory.volume.restrict P) :=
    scalarWeakSobolevCutoff_derivative_memLp_on_compact _hP χ _hdu
  exact
    scalarWeakSobolev_exists_local_smoothApprox_graph_density_of_memLp
      _hQ _hP _hQP _hPΩ _hΩ_open _hlocalizedWeak hvalue_memLp hderiv_memLp

/--
%%handwave
name:
  Smooth graph-density after cutoff localization
statement:
  After multiplying by a smooth cutoff supported in the weak-derivative
  region, the localized pair \((\chi u,\chi\,du+u\,d\chi)\) admits smooth
  approximants converging in the directional graph norm on \(Q\).
proof:
  First apply [the weak product rule for a cutoff](lean:JJMath.Uniformization.scalarWeakSobolevCutoffDerivative_weakDerivative).
  Then use [mollifier graph-density for the localized weak pair](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_smoothApprox_of_localized_weakDerivative).
-/
theorem scalarWeakSobolev_exists_local_smoothApprox_cutoff_graph_density
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    (χ : ScalarWeakSobolevCutoff P Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} (_hh : h ≠ 0)
    (_hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H))
    (_hdu_loc : LocallyIntegrableOn (fun z ↦ du z h) Ω
      (MeasureTheory.volume : Measure H))
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (_hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P)) :
    Nonempty
      (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q
        (fun z ↦ χ z * u z)
        (scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du) h) := by
  have hlocalizedWeak :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Ω
        (fun z ↦ χ z * u z)
        (scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du) :=
    scalarWeakSobolevCutoffDerivative_weakDerivative χ _hweak _hu_loc
  exact
    scalarWeakSobolev_exists_local_smoothApprox_of_localized_weakDerivative
      _hQ _hP _hQP _hPΩ _hΩ_open χ hlocalizedWeak _hu _hdu

/--
%%handwave
name:
  Nonzero-direction smooth Sobolev graph-density core
statement:
  In a nonzero direction \(h\), a locally integrable scalar weak Sobolev pair
  \((u,du)\) can be approximated on \(Q\) by smooth functions \(v_n\) with
  \(v_n\to u\) and \(D_hv_n\to du(\cdot)h\) in \(L^2(Q)\).
proof:
  Choose a cutoff equal to one on \(Q\), use [smooth graph-density after
  cutoff localization](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_smoothApprox_cutoff_graph_density),
  and then remove the cutoff on \(Q\).
-/
theorem scalarWeakSobolev_exists_local_smoothApprox_nonzero_direction_l2_on_compact_core
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} (_hh : h ≠ 0)
    (_hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H))
    (_hdu_loc : LocallyIntegrableOn (fun z ↦ du z h) Ω
      (MeasureTheory.volume : Measure H))
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (_hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P)) :
    Nonempty (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h) := by
  rcases exists_scalarWeakSobolevCutoff _hP _hPΩ _hΩ_open with ⟨χ⟩
  rcases scalarWeakSobolev_exists_local_smoothApprox_cutoff_graph_density
      _hQ _hP _hQP _hPΩ _hΩ_open χ _hweak _hh _hu_loc _hdu_loc _hu _hdu with
    ⟨hlocalized⟩
  exact scalarWeakSobolevLocalSmoothApprox_of_cutoff
    _hQ χ (subset_of_exists_cthickening_subset _hQP) hlocalized

/--
%%handwave
name:
  Nonzero-direction smooth Sobolev approximation
statement:
  In a nonzero direction \(h\), a scalar weak Sobolev pair \((u,du)\) admits
  smooth approximants on \(Q\) converging to \(u\) and \(du(\cdot)h\) in the
  directional \(L^2\)-graph norm.
proof:
  First derive local integrability of \(u\) and \(du(\cdot)h\) from the weak
  derivative identity.  Then apply [smooth graph-density in a nonzero
  direction](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_smoothApprox_nonzero_direction_l2_on_compact_core).
-/
theorem scalarWeakSobolev_exists_local_smoothApprox_nonzero_direction_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} (hh : h ≠ 0)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P)) :
    Nonempty (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h) := by
  have hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H) :=
    kinnunenWeakDerivative_function_locallyIntegrableOn_of_nonzero_direction
      hΩ_open hweak hh
  have hdu_loc : LocallyIntegrableOn (fun z ↦ du z h) Ω
      (MeasureTheory.volume : Measure H) :=
    kinnunenWeakDerivative_directionalDerivative_locallyIntegrableOn
      hΩ_open hweak h
  exact
    scalarWeakSobolev_exists_local_smoothApprox_nonzero_direction_l2_on_compact_core
      hQ hP hQP hPΩ hΩ_open hweak hh hu_loc hdu_loc hu hdu

/--
%%handwave
name:
  Local Sobolev functions admit smooth \(L^2\) approximants
statement:
  If \(Q\Subset P\Subset\Omega\), \(u\in L^2(P)\), and \(du(\cdot)h\in
  L^2(P)\), then there are smooth \(v_n\) with
  \[
    v_n\to u,\qquad D_hv_n\to du(\cdot)h
      \quad\text{in }L^2(Q).
  \]
proof:
  If \(Q=\varnothing\) the claim is trivial.  If \(h=0\), use ordinary smooth
  density in \(L^2(Q)\).  Otherwise apply [nonzero-direction smooth Sobolev
  approximation](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_smoothApprox_nonzero_direction_l2_on_compact).
-/
theorem scalarWeakSobolev_exists_local_smoothApprox_direction_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H} (_hQ : IsCompact Q) (_hP : IsCompact P)
    (_hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (_hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P)) :
    Nonempty (ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h) := by
  by_cases hQ_empty : Q = ∅
  · subst Q
    exact scalarWeakSobolev_exists_local_smoothApprox_empty_l2
  by_cases hh : h = 0
  · subst h
    have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset _hQP
    have hu_Q : MemLp u 2 (MeasureTheory.volume.restrict Q) :=
      hu.mono_measure (Measure.restrict_mono hQP_subset le_rfl)
    exact scalarWeakSobolev_exists_local_smoothApprox_zero_direction_l2_on_compact hu_Q
  · exact
      scalarWeakSobolev_exists_local_smoothApprox_nonzero_direction_l2_on_compact
        _hQ _hP _hQP _hPΩ _hΩ_open _hweak hh hu hdu

/--
%%handwave
name:
  Translating a compact set into a larger set does not increase the \(L^2\) norm
statement:
  If translation by \(h\) maps \(K\) into \(Q\), then the \(L^2(K)\)-norm of
  \(f(\cdot+h)\) is bounded by the \(L^2(Q)\)-norm of \(f\).
proof:
  Translation preserves Euclidean volume.  Therefore the integral over \(K\)
  of \(|f(x+h)|^2\) is the integral of \(|f|^2\) over the translated set
  \(K+h\), which is bounded by the integral over \(Q\).
-/
theorem eLpNorm_comp_add_right_restrict_le_of_mapsTo
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} {f : H → ℝ} {h : H}
    (hmap : Set.MapsTo (fun z : H ↦ z + h) K Q) :
    eLpNorm (fun z : H ↦ f (z + h)) 2 (MeasureTheory.volume.restrict K) ≤
      eLpNorm f 2 (MeasureTheory.volume.restrict Q) := by
  let τ : H → H := fun z ↦ z + h
  let F : H → ℝ≥0∞ := fun z ↦ ‖f z‖ₑ ^ (2 : ℝ)
  have hτ_mp :
      MeasurePreserving τ MeasureTheory.volume MeasureTheory.volume := by
    simpa [τ] using
      (MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : Measure H) h)
  have hτ_emb : MeasurableEmbedding τ := by
    simpa [τ] using
      (Homeomorph.addRight h).isClosedEmbedding.measurableEmbedding
  have hτ_image : τ '' K ⊆ Q := by
    rintro y ⟨x, hxK, rfl⟩
    exact hmap hxK
  have hlintegral :
      ∫⁻ z in K, F (τ z) ∂MeasureTheory.volume ≤
        ∫⁻ z in Q, F z ∂MeasureTheory.volume := by
    calc
      ∫⁻ z in K, F (τ z) ∂MeasureTheory.volume
          = ∫⁻ y in τ '' K, F y ∂MeasureTheory.volume :=
            hτ_mp.setLIntegral_comp_emb hτ_emb F K
      _ ≤ ∫⁻ y in Q, F y ∂MeasureTheory.volume :=
            lintegral_mono_set hτ_image
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.coe_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
  exact ENNReal.rpow_le_rpow (by simpa [τ, F] using hlintegral) (by norm_num)

/--
%%handwave
name:
  Segment maps preserve null sets
statement:
  If every segment \(x+t h\), \(x\in K\), \(0\le t\le1\), remains in \(Q\),
  then the map \((x,t)\mapsto x+t h\) sends null sets in \(Q\) to null sets
  when pulled back to \(K\times[0,1]\).
proof:
  For each fixed \(t\), the map \(x\mapsto x+t h\) is a Euclidean
  translation and hence preserves null sets.  The segment containment
  hypothesis makes this a restricted null-set-preserving map from \(K\) to
  \(Q\), and the product criterion gives the result.
-/
theorem aclSegmentMap_quasiMeasurePreserving_restrict_prod
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} {h : H}
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    Measure.QuasiMeasurePreserving
      (fun p : H × ℝ ↦ p.1 + p.2 • h)
      ((MeasureTheory.volume.restrict K).prod
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
      (MeasureTheory.volume.restrict Q) := by
  refine MeasureTheory.QuasiMeasurePreserving.prod_of_left
    (τ := MeasureTheory.volume.restrict Q) ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))] with t ht
    have hmap : Set.MapsTo (fun z : H ↦ z + t • h) K Q := by
      intro z hz
      exact hsegments z hz t ht
    exact
      (MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : Measure H) (t • h)).quasiMeasurePreserving.restrict hmap

/--
%%handwave
name:
  Absolute segment integral
statement:
  The absolute segment integral of a scalar function in direction \(h\) from
  \(z\) is the integral over \(0\le t\le1\) of \(|f(z+t h)|\).
-/
noncomputable def aclSegmentIntegralAbs {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (h z : H) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1, ‖f (z + t • h)‖ ∂MeasureTheory.volume

private theorem acl_enorm_integral_sq_le_lintegral_enorm_sq_of_measure_univ_eq_one
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hμ : μ Set.univ = 1)
    (hg : AEStronglyMeasurable g μ) :
    ‖∫ x, g x ∂μ‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  have hnorm :
      ‖∫ x, g x ∂μ‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ ∂μ :=
    MeasureTheory.enorm_integral_le_lintegral_enorm g
  have hholder :
      ∫⁻ x, ‖g x‖ₑ ∂μ ≤
        (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
    have hH : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have h :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq
        (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
        (f := fun x ↦ ‖g x‖ₑ) (g := fun _x ↦ (1 : ℝ≥0∞))
        hH hg.enorm aemeasurable_const
    simpa [hμ, one_div] using h
  exact (ENNReal.le_rpow_inv_iff (by norm_num : 0 < (2 : ℝ))).1
    (hnorm.trans hholder)

theorem aclSegmentIntegral_iterated_lintegral_sq_le_of_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} {f : H → ℝ} {h : H}
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
        ∂MeasureTheory.volume ≤
      ∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
  let F : H → ℝ≥0∞ := fun z ↦ ‖f z‖ₑ ^ (2 : ℝ)
  have hslice :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∫⁻ z in K, F (z + t • h) ∂MeasureTheory.volume ≤
          ∫⁻ z in Q, F z ∂MeasureTheory.volume := by
    intro t ht
    let τ : H → H := fun z ↦ z + t • h
    have hτ_mp :
        MeasurePreserving τ MeasureTheory.volume MeasureTheory.volume := by
      simpa [τ] using
        (MeasureTheory.measurePreserving_add_right
          (MeasureTheory.volume : Measure H) (t • h))
    have hτ_emb : MeasurableEmbedding τ := by
      simpa [τ] using
        (Homeomorph.addRight (t • h)).isClosedEmbedding.measurableEmbedding
    have hτ_image : τ '' K ⊆ Q := by
      rintro y ⟨x, hxK, rfl⟩
      exact hsegments x hxK t ht
    calc
      ∫⁻ z in K, F (z + t • h) ∂MeasureTheory.volume
          = ∫⁻ z in K, F (τ z) ∂MeasureTheory.volume := rfl
      _ = ∫⁻ y in τ '' K, F y ∂MeasureTheory.volume :=
            hτ_mp.setLIntegral_comp_emb hτ_emb F K
      _ ≤ ∫⁻ y in Q, F y ∂MeasureTheory.volume :=
            lintegral_mono_set hτ_image
  calc
    ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
        ∂MeasureTheory.volume
        = ∫⁻ t in Set.Icc (0 : ℝ) 1,
            ∫⁻ z in K, F (z + t • h) ∂MeasureTheory.volume
            ∂MeasureTheory.volume := rfl
    _ ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1,
          ∫⁻ z in Q, F z ∂MeasureTheory.volume ∂MeasureTheory.volume :=
          setLIntegral_mono' measurableSet_Icc hslice
    _ = ∫⁻ z in Q, F z ∂MeasureTheory.volume := by
          simp [Real.volume_Icc]

theorem aclSegmentIntegral_lintegral_sq_le_iterated_lintegral_sq
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (_hK : IsCompact K) (_hQ : IsCompact Q)
    {f : H → ℝ} {h : H}
    (hf : AEStronglyMeasurable f (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∫⁻ z, ‖aclSegmentIntegralAbs f h z‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume.restrict K ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
        ∂MeasureTheory.volume := by
  let μK : Measure H := MeasureTheory.volume.restrict K
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  let G : H × ℝ → ℝ := fun p ↦ ‖f (p.1 + p.2 • h)‖
  have hμI_univ : μI Set.univ = 1 := by
    simp [μI, Real.volume_Icc]
  have hqmp :
      Measure.QuasiMeasurePreserving
        (fun p : H × ℝ ↦ p.1 + p.2 • h)
        (μK.prod μI) (MeasureTheory.volume.restrict Q) := by
    simpa [μK, μI] using
      aclSegmentMap_quasiMeasurePreserving_restrict_prod
        (H := H) (K := K) (Q := Q) (h := h) hsegments
  have hG_ae : AEStronglyMeasurable G (μK.prod μI) := by
    exact hf.norm.comp_quasiMeasurePreserving hqmp
  have hGsq_ae :
      AEMeasurable (fun p : H × ℝ ↦ ‖G p‖ₑ ^ (2 : ℝ)) (μK.prod μI) :=
    hG_ae.enorm.pow_const _
  have hslices :
      ∀ᵐ z ∂μK, AEStronglyMeasurable (fun t : ℝ ↦ G (z, t)) μI :=
    hG_ae.prodMk_left
  have hpoint :
      ∀ᵐ z ∂μK,
        ‖∫ t, G (z, t) ∂μI‖ₑ ^ (2 : ℝ) ≤
          ∫⁻ t, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μI := by
    filter_upwards [hslices] with z hz
    exact
      acl_enorm_integral_sq_le_lintegral_enorm_sq_of_measure_univ_eq_one
        hμI_univ hz
  calc
    ∫⁻ z, ‖aclSegmentIntegralAbs f h z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict K
        = ∫⁻ z, ‖∫ t, G (z, t) ∂μI‖ₑ ^ (2 : ℝ) ∂μK := by
          simp [aclSegmentIntegralAbs, μK, μI, G]
    _ ≤ ∫⁻ z, ∫⁻ t, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μI ∂μK :=
          lintegral_mono_ae hpoint
    _ = ∫⁻ t, ∫⁻ z, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μK ∂μI := by
          exact MeasureTheory.lintegral_lintegral_swap
            (μ := μK) (ν := μI)
            (f := fun z t ↦ ‖G (z, t)‖ₑ ^ (2 : ℝ)) hGsq_ae
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
          simp [μK, μI, G]

theorem aclSegmentIntegral_lintegral_sq_le_of_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (hQ : IsCompact Q)
    {f : H → ℝ} {h : H}
    (hf : AEStronglyMeasurable f (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∫⁻ z, ‖aclSegmentIntegralAbs f h z‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume.restrict K ≤
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict Q := by
  calc
    ∫⁻ z, ‖aclSegmentIntegralAbs f h z‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume.restrict K
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1,
            ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
            ∂MeasureTheory.volume :=
          aclSegmentIntegral_lintegral_sq_le_iterated_lintegral_sq
            hK hQ hf hsegments
    _ ≤ ∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume :=
          aclSegmentIntegral_iterated_lintegral_sq_le_of_segments
            hsegments

theorem aclSegmentIntegral_eLpNorm_le_of_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (hQ : IsCompact Q)
    {f : H → ℝ} {h : H}
    (hf : AEStronglyMeasurable f (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    eLpNorm (aclSegmentIntegralAbs f h)
        2 (MeasureTheory.volume.restrict K) ≤
      eLpNorm f 2 (MeasureTheory.volume.restrict Q) := by
  have hsq :
      ∫⁻ z, ‖aclSegmentIntegralAbs f h z‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume.restrict K ≤
        ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict Q :=
    aclSegmentIntegral_lintegral_sq_le_of_segments hK hQ hf hsegments
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.coe_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
  exact ENNReal.rpow_le_rpow hsq (by norm_num)

/--
%%handwave
name:
  Square-integrable functions are integrable on almost every segment
statement:
  If a scalar function is square-integrable on \(Q\), and every segment
  \(x+t h\) with \(x\in K\) and \(0\le t\le1\) remains in \(Q\), then for
  almost every \(x\in K\) its restriction to the segment is integrable in the
  segment parameter.
proof:
  Pull the function back to \(K\times[0,1]\) by the segment map.  The
  square-integral of this pullback is bounded by the square-integral on
  \(Q\), using translation invariance on each time-slice.  Since
  \(K\times[0,1]\) has finite measure, the pullback is integrable.  Fubini's
  theorem then gives integrability on almost every vertical slice.
-/
theorem aclSegment_integrable_restrict_Icc_ae_of_memLp
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (_hQ : IsCompact Q)
    {f : H → ℝ} {h : H}
    (hf : MemLp f 2 (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      Integrable (fun t : ℝ ↦ f (z + t • h))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let μK : Measure H := MeasureTheory.volume.restrict K
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  let g : H × ℝ → ℝ := fun p ↦ f (p.1 + p.2 • h)
  letI : IsFiniteMeasure μK := ⟨by simpa [μK] using hK.measure_lt_top⟩
  letI : IsFiniteMeasure μI := ⟨by simp [μI, Real.volume_Icc]⟩
  have hqmp :
      Measure.QuasiMeasurePreserving
        (fun p : H × ℝ ↦ p.1 + p.2 • h)
        (μK.prod μI) (MeasureTheory.volume.restrict Q) := by
    simpa [μK, μI] using
      aclSegmentMap_quasiMeasurePreserving_restrict_prod
        (H := H) (K := K) (Q := Q) (h := h) hsegments
  have hg_ae : AEStronglyMeasurable g (μK.prod μI) := by
    simpa [g, Function.comp_def] using
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  have hg_sq_ae :
      AEMeasurable (fun p : H × ℝ ↦ ‖g p‖ₑ ^ (2 : ℝ)) (μK.prod μI) :=
    hg_ae.enorm.pow_const _
  have hprod_eq :
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μK.prod μI =
        ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    calc
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μK.prod μI
          = ∫⁻ z, ∫⁻ t, ‖g (z, t)‖ₑ ^ (2 : ℝ) ∂μI ∂μK := by
            exact lintegral_prod (fun p : H × ℝ ↦ ‖g p‖ₑ ^ (2 : ℝ)) hg_sq_ae
      _ = ∫⁻ t, ∫⁻ z, ‖g (z, t)‖ₑ ^ (2 : ℝ) ∂μK ∂μI := by
            exact MeasureTheory.lintegral_lintegral_swap
              (μ := μK) (ν := μI)
              (f := fun z t ↦ ‖g (z, t)‖ₑ ^ (2 : ℝ)) hg_sq_ae
      _ = ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
            simp [μK, μI, g]
  have hprod_le :
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μK.prod μI ≤
        ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict Q := by
    calc
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μK.prod μI
          = ∫⁻ t in Set.Icc (0 : ℝ) 1,
              ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
              ∂MeasureTheory.volume := hprod_eq
      _ ≤ ∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume :=
            aclSegmentIntegral_iterated_lintegral_sq_le_of_segments
              (K := K) (Q := Q) (f := f) (h := h) hsegments
      _ = ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict Q := by
            simp
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.coe_ne_top
  have hf_sq_lt_top :
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict Q <
        (∞ : ℝ≥0∞) := by
    have hf_norm := hf.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top] at hf_norm
    have hf_norm_set :
        (∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume) ^
            ((1 : ℝ) / 2) < (∞ : ℝ≥0∞) := by
      simpa using hf_norm
    have hset :
        ∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume <
          (∞ : ℝ≥0∞) :=
      (ENNReal.rpow_lt_top_iff_of_pos
        (by norm_num : 0 < (1 : ℝ) / 2)).1 hf_norm_set
    simpa using hset
  have hg_sq_lt_top :
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μK.prod μI < (∞ : ℝ≥0∞) :=
    hprod_le.trans_lt hf_sq_lt_top
  have hg_mem_two : MemLp g 2 (μK.prod μI) := by
    refine ⟨hg_ae, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hg_sq_lt_top.ne
  have hg_mem_one : MemLp g 1 (μK.prod μI) :=
    hg_mem_two.mono_exponent (by norm_num)
  have hg_int : Integrable g (μK.prod μI) := by
    simpa using (memLp_one_iff_integrable.mp hg_mem_one)
  simpa [μK, μI, g] using hg_int.prod_right_ae

/--
%%handwave
name:
  Endpoint difference error is controlled by the local \(L^2\) error
statement:
  If \(K\) and its translate by \(h\) lie in \(Q\), then the \(L^2(K)\)-norm
  of
  \[
    (v_n-u)(x+h)-(v_n-u)(x)
  \]
  is at most twice the \(L^2(Q)\)-norm of \(v_n-u\).
proof:
  Use the \(L^2\) triangle inequality.  The unshifted term is controlled by
  restriction from \(Q\) to \(K\).  The shifted term is controlled by
  translation invariance of Euclidean volume and the inclusion \(K+h\subset Q\).
-/
theorem scalarWeakSobolev_localSmoothApprox_endpoint_error_eLpNorm_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (_hK : IsCompact K) (_hQ : IsCompact Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox : ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h)
    (_hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q)
    (n : ℕ) :
    eLpNorm
        ((fun z ↦ happrox.approximants n (z + h) -
            happrox.approximants n z) -
          fun z ↦ u (z + h) - u z)
        2 (MeasureTheory.volume.restrict K) ≤
      (2 : ℝ≥0∞) *
        eLpNorm (fun z ↦ happrox.approximants n z - u z)
          2 (MeasureTheory.volume.restrict Q) := by
  let e : H → ℝ := fun z ↦ happrox.approximants n z - u z
  have hKQ : K ⊆ Q := by
    intro x hx
    simpa using _hsegments x hx 0 (by simp)
  have hmap : Set.MapsTo (fun z : H ↦ z + h) K Q := by
    intro x hx
    simpa using _hsegments x hx 1 (by simp)
  have hbase_meas :
      AEStronglyMeasurable e (MeasureTheory.volume.restrict K) :=
    (happrox.value_aestronglyMeasurable n).mono_measure
      (Measure.restrict_mono hKQ le_rfl)
  have htranslate_qmp :
      Measure.QuasiMeasurePreserving (fun z : H ↦ z + h)
        (MeasureTheory.volume.restrict K) (MeasureTheory.volume.restrict Q) :=
    (MeasureTheory.measurePreserving_add_right
      (MeasureTheory.volume : Measure H) h).quasiMeasurePreserving.restrict hmap
  have htranslate_meas :
      AEStronglyMeasurable (fun z : H ↦ e (z + h))
        (MeasureTheory.volume.restrict K) := by
    simpa [Function.comp_def] using
      (happrox.value_aestronglyMeasurable n).comp_quasiMeasurePreserving
        htranslate_qmp
  have hbase_norm :
      eLpNorm e 2 (MeasureTheory.volume.restrict K) ≤
        eLpNorm e 2 (MeasureTheory.volume.restrict Q) :=
    eLpNorm_mono_measure e (Measure.restrict_mono hKQ le_rfl)
  have htranslate_norm :
      eLpNorm (fun z : H ↦ e (z + h)) 2
          (MeasureTheory.volume.restrict K) ≤
        eLpNorm e 2 (MeasureTheory.volume.restrict Q) :=
    eLpNorm_comp_add_right_restrict_le_of_mapsTo
      (K := K) (Q := Q) (f := e) (h := h) hmap
  have htriangle :
      eLpNorm (fun z : H ↦ e (z + h) - e z) 2
          (MeasureTheory.volume.restrict K) ≤
        eLpNorm (fun z : H ↦ e (z + h)) 2
            (MeasureTheory.volume.restrict K) +
          eLpNorm e 2 (MeasureTheory.volume.restrict K) :=
    eLpNorm_sub_le htranslate_meas hbase_meas (by norm_num)
  calc
    eLpNorm
        ((fun z ↦ happrox.approximants n (z + h) -
            happrox.approximants n z) -
          fun z ↦ u (z + h) - u z)
        2 (MeasureTheory.volume.restrict K)
        = eLpNorm (fun z : H ↦ e (z + h) - e z)
            2 (MeasureTheory.volume.restrict K) := by
          apply eLpNorm_congr_ae
          filter_upwards with z
          simp [e, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ eLpNorm (fun z : H ↦ e (z + h)) 2
            (MeasureTheory.volume.restrict K) +
          eLpNorm e 2 (MeasureTheory.volume.restrict K) := htriangle
    _ ≤ eLpNorm e 2 (MeasureTheory.volume.restrict Q) +
          eLpNorm e 2 (MeasureTheory.volume.restrict Q) :=
        add_le_add htranslate_norm hbase_norm
    _ = (2 : ℝ≥0∞) *
        eLpNorm (fun z ↦ happrox.approximants n z - u z)
          2 (MeasureTheory.volume.restrict Q) := by
        simp [e, two_mul]

/--
%%handwave
name:
  Local \(L^2\) approximation controls endpoint differences
statement:
  If smooth approximants converge to \(u\) in \(L^2(Q)\), and every segment
  from \(K\) in the chosen direction lies in \(Q\), then the endpoint
  differences of the approximants converge to the endpoint difference of
  \(u\) in \(L^2(K)\).
proof:
  The endpoint error is
  \[
    (v_n-u)(x+h)-(v_n-u)(x).
  \]
  The triangle inequality bounds its \(L^2(K)\)-norm by the sum of the
  \(L^2\)-norms of \(v_n-u\) on \(K\) and on the translated set \(K+h\).
  Both are bounded by the \(L^2(Q)\)-norm because \(K\) and \(K+h\) lie in
  \(Q\), and translation preserves Euclidean volume.
-/
theorem scalarWeakSobolev_localSmoothApprox_endpoint_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (hQ : IsCompact Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox : ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    (∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦ happrox.approximants n (z + h) - happrox.approximants n z)
        (MeasureTheory.volume.restrict K)) ∧
      AEStronglyMeasurable
        (fun z ↦ u (z + h) - u z)
        (MeasureTheory.volume.restrict K) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z ↦ happrox.approximants n (z + h) -
                happrox.approximants n z) -
              fun z ↦ u (z + h) - u z)
            2 (MeasureTheory.volume.restrict K))
        Filter.atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hv : Continuous (happrox.approximants n) :=
      (happrox.smooth n).continuous
    have htranslate :
        AEStronglyMeasurable
          (fun z ↦ happrox.approximants n (z + h))
          (MeasureTheory.volume.restrict K) := by
      exact (hv.comp (by fun_prop)).aestronglyMeasurable
    have hbase :
        AEStronglyMeasurable
          (fun z ↦ happrox.approximants n z)
          (MeasureTheory.volume.restrict K) :=
      hv.aestronglyMeasurable
    exact htranslate.sub hbase
  · have hKQ : K ⊆ Q := by
      intro x hx
      simpa using hsegments x hx 0 (by simp)
    have hbase :
        AEStronglyMeasurable u (MeasureTheory.volume.restrict K) :=
      (hu.mono_measure (Measure.restrict_mono hKQ le_rfl)).aestronglyMeasurable
    have hmap : Set.MapsTo (fun z : H ↦ z + h) K Q := by
      intro x hx
      simpa using hsegments x hx 1 (by simp)
    have htranslate_qmp :
        Measure.QuasiMeasurePreserving (fun z : H ↦ z + h)
          (MeasureTheory.volume.restrict K) (MeasureTheory.volume.restrict Q) :=
      (MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : Measure H) h).quasiMeasurePreserving.restrict hmap
    have htranslate :
        AEStronglyMeasurable (fun z : H ↦ u (z + h))
          (MeasureTheory.volume.restrict K) := by
      simpa [Function.comp_def] using
        hu.aestronglyMeasurable.comp_quasiMeasurePreserving htranslate_qmp
    exact htranslate.sub hbase
  · have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            (2 : ℝ≥0∞) *
              eLpNorm (fun z ↦ happrox.approximants n z - u z)
                2 (MeasureTheory.volume.restrict Q))
          Filter.atTop (𝓝 0) := by
      have h :=
        ENNReal.Tendsto.const_mul happrox.value_tendsto_l2
          (Or.inr (show (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) from ENNReal.coe_ne_top))
      simpa using h
    rw [ENNReal.tendsto_atTop_zero] at hmul ⊢
    intro ε hε
    rcases hmul ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn ↦ ?_⟩
    exact
      (scalarWeakSobolev_localSmoothApprox_endpoint_error_eLpNorm_le
        hK hQ happrox hsegments n).trans (hN n hn)

/--
%%handwave
name:
  Signed segment-integral error is bounded pointwise by the absolute error
statement:
  For almost every starting point in \(K\), the norm of the difference between
  the smooth directional-derivative segment integral and the weak
  directional-derivative segment integral is bounded by the segment integral
  of the pointwise directional-derivative error.
proof:
  For almost every segment, the weak derivative component and the derivative
  error are integrable along the interval.  Subtract the interval integrals,
  identify the result with the integral of the difference, and apply the
  norm-of-integral bound.
-/
theorem scalarWeakSobolev_localSmoothApprox_segmentIntegral_error_norm_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (_hK : IsCompact K) (_hQ : IsCompact Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox : ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h)
    (_hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q))
    (_hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q)
    (n : ℕ)
    (he_mem : MemLp
      (fun z ↦ fderiv ℝ (happrox.approximants n) z h - du z h)
      2 (MeasureTheory.volume.restrict Q)) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      ‖((fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              fderiv ℝ (happrox.approximants n) (z + t • h) h
                ∂MeasureTheory.volume) -
          fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              du (z + t • h) h ∂MeasureTheory.volume) z‖ ≤
        aclSegmentIntegralAbs
          (fun z ↦ fderiv ℝ (happrox.approximants n) z h - du z h) h z := by
  let s : H → ℝ := fun y ↦ fderiv ℝ (happrox.approximants n) y h
  let w : H → ℝ := fun y ↦ du y h
  let e : H → ℝ := fun y ↦ s y - w y
  have hs_cont : Continuous s := by
    simpa [s] using
      ((happrox.smooth n).continuous_fderiv (by simp)).clm_apply
        (continuous_const : Continuous fun _ : H ↦ h)
  have he_int_ae :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        Integrable (fun t : ℝ ↦ e (z + t • h))
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    simpa [e, s, w] using
      aclSegment_integrable_restrict_Icc_ae_of_memLp
        _hK _hQ (f := fun y : H ↦
          fderiv ℝ (happrox.approximants n) y h - du y h)
        (h := h) he_mem _hsegments
  filter_upwards [he_int_ae] with z he_int
  have hs_int :
      Integrable (fun t : ℝ ↦ s (z + t • h))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hcont : Continuous (fun t : ℝ ↦ s (z + t • h)) :=
      hs_cont.comp (by fun_prop)
    simpa [IntegrableOn] using
      (hcont.integrableOn_Icc (a := (0 : ℝ)) (b := 1))
  have hw_int :
      Integrable (fun t : ℝ ↦ w (z + t • h))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hsub := hs_int.sub he_int
    exact hsub.congr <| Filter.Eventually.of_forall fun t ↦ by
      simp [e, s, w]
  have hdiff :
      (∫ t in Set.Icc (0 : ℝ) 1, s (z + t • h) ∂MeasureTheory.volume) -
          ∫ t in Set.Icc (0 : ℝ) 1, w (z + t • h) ∂MeasureTheory.volume =
        ∫ t in Set.Icc (0 : ℝ) 1, e (z + t • h) ∂MeasureTheory.volume := by
    have hsub :=
      integral_sub
        (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
        hs_int hw_int
    calc
      (∫ t in Set.Icc (0 : ℝ) 1, s (z + t • h) ∂MeasureTheory.volume) -
          ∫ t in Set.Icc (0 : ℝ) 1, w (z + t • h) ∂MeasureTheory.volume
          = ∫ t in Set.Icc (0 : ℝ) 1,
              s (z + t • h) - w (z + t • h) ∂MeasureTheory.volume := hsub.symm
      _ = ∫ t in Set.Icc (0 : ℝ) 1, e (z + t • h) ∂MeasureTheory.volume := by
          apply integral_congr_ae
          filter_upwards with t
          simp [e, s, w]
  calc
    ‖((fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (happrox.approximants n) (z + t • h) h
              ∂MeasureTheory.volume) -
        fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (z + t • h) h ∂MeasureTheory.volume) z‖
        = ‖∫ t in Set.Icc (0 : ℝ) 1,
            e (z + t • h) ∂MeasureTheory.volume‖ := by
          simpa [s, w, Pi.sub_apply] using congrArg norm hdiff
    _ ≤ ∫ t in Set.Icc (0 : ℝ) 1,
          ‖e (z + t • h)‖ ∂MeasureTheory.volume :=
          norm_integral_le_integral_norm
            (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
            (fun t : ℝ ↦ e (z + t • h))
    _ = aclSegmentIntegralAbs
          (fun y ↦ fderiv ℝ (happrox.approximants n) y h - du y h)
          h z := by
          simp [aclSegmentIntegralAbs, e, s, w]

/--
%%handwave
name:
  Segment-integral error is controlled by the derivative error
statement:
  If the directional derivative errors converge on \(Q\), and all segments
  from \(K\) stay in \(Q\), then the \(L^2(K)\)-norm of the signed
  segment-integral error is bounded by the \(L^2(Q)\)-norm of the derivative
  error.
proof:
  For almost every base point, subtract the two segment integrals and bound
  the norm of the resulting integral by the integral of the norm of the
  derivative error.  Cauchy--Schwarz in the unit segment parameter and Fubini
  over \(K\times[0,1]\), together with translation invariance of Euclidean
  volume, give the \(L^2\)-bound.
-/
theorem scalarWeakSobolev_localSmoothApprox_segmentIntegral_error_eLpNorm_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (_hK : IsCompact K) (_hQ : IsCompact Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox : ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h)
    (_hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q))
    (_hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q)
    (n : ℕ) :
    eLpNorm
        ((fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              fderiv ℝ (happrox.approximants n) (z + t • h) h
                ∂MeasureTheory.volume) -
          fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              du (z + t • h) h ∂MeasureTheory.volume)
        2 (MeasureTheory.volume.restrict K) ≤
    eLpNorm (fun z ↦
          fderiv ℝ (happrox.approximants n) z h - du z h)
        2 (MeasureTheory.volume.restrict Q) := by
  let e : H → ℝ := fun z ↦
    fderiv ℝ (happrox.approximants n) z h - du z h
  by_cases htop : eLpNorm e 2 (MeasureTheory.volume.restrict Q) = (∞ : ℝ≥0∞)
  · have hrhs :
        eLpNorm (fun z ↦
            fderiv ℝ (happrox.approximants n) z h - du z h)
          2 (MeasureTheory.volume.restrict Q) = (∞ : ℝ≥0∞) := by
      simpa [e] using htop
    rw [hrhs]
    exact le_top
  have he_mem : MemLp e 2 (MeasureTheory.volume.restrict Q) :=
    ⟨happrox.directionalDerivative_aestronglyMeasurable n,
      lt_top_iff_ne_top.mpr htop⟩
  have hpoint :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        ‖((fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                fderiv ℝ (happrox.approximants n) (z + t • h) h
                  ∂MeasureTheory.volume) -
            fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                du (z + t • h) h ∂MeasureTheory.volume) z‖ ≤
          aclSegmentIntegralAbs e h z := by
    simpa [e] using
      scalarWeakSobolev_localSmoothApprox_segmentIntegral_error_norm_le
        _hK _hQ happrox _hdu _hsegments n he_mem
  calc
    eLpNorm
        ((fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              fderiv ℝ (happrox.approximants n) (z + t • h) h
                ∂MeasureTheory.volume) -
          fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              du (z + t • h) h ∂MeasureTheory.volume)
        2 (MeasureTheory.volume.restrict K)
        ≤ eLpNorm (aclSegmentIntegralAbs e h)
            2 (MeasureTheory.volume.restrict K) :=
          eLpNorm_mono_ae_real hpoint
    _ ≤ eLpNorm e 2 (MeasureTheory.volume.restrict Q) :=
          aclSegmentIntegral_eLpNorm_le_of_segments
            _hK _hQ (happrox.directionalDerivative_aestronglyMeasurable n) _hsegments
    _ = eLpNorm (fun z ↦
          fderiv ℝ (happrox.approximants n) z h - du z h)
        2 (MeasureTheory.volume.restrict Q) := rfl

/--
%%handwave
name:
  Local \(L^2\) approximation controls segment integrals
statement:
  If the directional derivatives of smooth approximants converge to the weak
  directional derivative in \(L^2(Q)\), and every segment from \(K\) remains
  in \(Q\), then the segment integrals of those directional derivatives
  converge in \(L^2(K)\).
proof:
  Apply Cauchy--Schwarz on each unit segment and Fubini over
  \(K\times[0,1]\).  For each fixed time, translation by \(t h\) preserves
  Euclidean measure and maps \(K\) into \(Q\), so the \(L^2(K)\) norm of the
  segment average is bounded by the \(L^2(Q)\) norm of the derivative error.
-/
theorem scalarWeakSobolev_localSmoothApprox_segmentIntegral_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (hQ : IsCompact Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox : ScalarWeakSobolevLocalSmoothApproxDirectionL2Data Q u du h)
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    (∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (happrox.approximants n) (z + t • h) h
              ∂MeasureTheory.volume)
        (MeasureTheory.volume.restrict K)) ∧
      AEStronglyMeasurable
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (z + t • h) h ∂MeasureTheory.volume)
        (MeasureTheory.volume.restrict K) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z ↦
                ∫ t in Set.Icc (0 : ℝ) 1,
                  fderiv ℝ (happrox.approximants n) (z + t • h) h
                    ∂MeasureTheory.volume) -
              fun z ↦
                ∫ t in Set.Icc (0 : ℝ) 1,
                  du (z + t • h) h ∂MeasureTheory.volume)
            2 (MeasureTheory.volume.restrict K))
        Filter.atTop (𝓝 0) := by
  let μK : Measure H := MeasureTheory.volume.restrict K
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  have hsegment_qmp :
      Measure.QuasiMeasurePreserving
        (fun p : H × ℝ ↦ p.1 + p.2 • h)
        (μK.prod μI) (MeasureTheory.volume.restrict Q) := by
    simpa [μK, μI] using
      aclSegmentMap_quasiMeasurePreserving_restrict_prod
        (H := H) (K := K) (Q := Q) (h := h) hsegments
  refine ⟨?_, ?_, ?_⟩
  · intro n
    let F : H × ℝ → ℝ :=
      fun p ↦ fderiv ℝ (happrox.approximants n) (p.1 + p.2 • h) h
    have hD_cont :
        Continuous (fun z : H ↦ fderiv ℝ (happrox.approximants n) z h) := by
      exact ((happrox.smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const
    have hF : AEStronglyMeasurable F (μK.prod μI) := by
      exact (hD_cont.comp (by fun_prop)).aestronglyMeasurable
    have hInt :
        AEStronglyMeasurable
          (fun z : H ↦ ∫ t, F (z, t) ∂μI) μK :=
      hF.integral_prod_right'
    simpa [F, μI] using hInt
  · let F : H × ℝ → ℝ :=
      fun p ↦ du (p.1 + p.2 • h) h
    have hF : AEStronglyMeasurable F (μK.prod μI) := by
      simpa [F, Function.comp_def] using
        hdu.aestronglyMeasurable.comp_quasiMeasurePreserving hsegment_qmp
    have hInt :
        AEStronglyMeasurable
          (fun z : H ↦ ∫ t, F (z, t) ∂μI) μK :=
      hF.integral_prod_right'
    simpa [F, μI] using hInt
  · have hderiv_tendsto := happrox.directionalDerivative_tendsto_l2
    rw [ENNReal.tendsto_atTop_zero] at hderiv_tendsto ⊢
    intro ε hε
    rcases hderiv_tendsto ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn ↦ ?_⟩
    exact
      (scalarWeakSobolev_localSmoothApprox_segmentIntegral_error_eLpNorm_le
        hK hQ happrox hdu hsegments n).trans (hN n hn)

/--
%%handwave
name:
  \(L^2\) convergence gives convergence in measure for smooth approximation data
statement:
  \(L^2\)-convergence of the endpoint differences and segment integrals
  implies convergence in measure of those same quantities.
proof:
  Apply the standard fact that convergence in \(L^p\), \(p\ne0\), implies
  convergence in measure, once the approximating and limiting functions are
  almost everywhere strongly measurable.
-/
def scalarWeakSobolev_smoothApproxInMeasureData_of_l2
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {K : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox : ScalarWeakSobolevDirectionalSmoothApproxL2Data K u du h) :
    ScalarWeakSobolevDirectionalSmoothApproxInMeasureData K u du h := by
  rcases happrox with
    ⟨v, hv_smooth, hendpoint_meas, hendpoint_lim_meas, hendpoint_l2,
      hintegral_meas, hintegral_lim_meas, hintegral_l2⟩
  refine
    { approximants := v
      smooth := hv_smooth
      endpoint_tendstoInMeasure := ?_
      integral_tendstoInMeasure := ?_ }
  · exact
      tendstoInMeasure_of_tendsto_eLpNorm
        (μ := MeasureTheory.volume.restrict K)
        (p := (2 : ℝ≥0∞))
        (by norm_num)
        hendpoint_meas hendpoint_lim_meas hendpoint_l2
  · exact
      tendstoInMeasure_of_tendsto_eLpNorm
        (μ := MeasureTheory.volume.restrict K)
        (p := (2 : ℝ≥0∞))
        (by norm_num)
        hintegral_meas hintegral_lim_meas hintegral_l2

/--
%%handwave
name:
  Convergence in measure gives almost-everywhere smooth approximation data
statement:
  If the endpoint differences and segment integrals of smooth approximants
  converge in measure, then after passing to a common subsequence they converge
  almost everywhere in both senses needed for the weak fundamental theorem.
proof:
  First take a subsequence along which the endpoint differences converge
  almost everywhere.  Along that subsequence, take a further subsequence along
  which the segment integrals converge almost everywhere.  The first
  convergence is preserved under the further subsequence, and smoothness is
  preserved by composition of the index maps.
-/
theorem scalarWeakSobolev_smoothApproxData_of_tendstoInMeasure
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {K : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox : ScalarWeakSobolevDirectionalSmoothApproxInMeasureData K u du h) :
    Nonempty (ScalarWeakSobolevDirectionalSmoothApproxData K u du h) := by
  rcases happrox with ⟨v, hv_smooth, hendpoint, hintegral⟩
  rcases hendpoint.exists_seq_tendsto_ae with
    ⟨ns, hns_strict, hendpoint_ae⟩
  have hintegral_subseq :
      TendstoInMeasure (MeasureTheory.volume.restrict K)
        (fun i z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (v (ns i)) (z + t • h) h ∂MeasureTheory.volume)
        Filter.atTop
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (z + t • h) h ∂MeasureTheory.volume) := by
    exact hintegral.comp hns_strict.tendsto_atTop
  rcases hintegral_subseq.exists_seq_tendsto_ae with
    ⟨ms, hms_strict, hintegral_ae⟩
  refine ⟨
    { approximants := fun i ↦ v (ns (ms i))
      smooth := fun i ↦ hv_smooth (ns (ms i))
      endpoint_tendsto := ?_
      integral_tendsto := ?_ }⟩
  · filter_upwards [hendpoint_ae] with z hz
    exact hz.comp hms_strict.tendsto_atTop
  · exact hintegral_ae

/--
%%handwave
name:
  Local smooth approximation in \(L^2\) for the ACL theorem
statement:
  If all segments \(x+t h\), \(x\in K\), \(0\le t\le1\), lie in \(Q\), then
  the smooth approximants \(v_n\) can be chosen so that
  \[
    v_n(\cdot+h)-v_n \to u(\cdot+h)-u
  \]
  and
  \[
    \int_0^1 D_hv_n(\cdot+t h)\,dt
      \to \int_0^1 du(\cdot+t h)h\,dt
  \]
  in \(L^2(K)\).
proof:
  Start with [local smooth approximation in the directional graph norm on
  \(Q\)](lean:JJMath.Uniformization.scalarWeakSobolev_exists_local_smoothApprox_direction_l2_on_compact).
  Translation of endpoints and Fubini along the segment family transfer the
  two graph-norm convergences to \(L^2(K)\).
-/
theorem scalarWeakSobolev_exists_smoothApprox_direction_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    Nonempty (ScalarWeakSobolevDirectionalSmoothApproxL2Data K u du h) := by
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
  have hu_Q : MemLp u 2 (MeasureTheory.volume.restrict Q) :=
    hu.mono_measure (Measure.restrict_mono hQP_subset le_rfl)
  have hdu_Q : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q) :=
    hdu.mono_measure (Measure.restrict_mono hQP_subset le_rfl)
  rcases scalarWeakSobolev_exists_local_smoothApprox_direction_l2_on_compact
      hQ hP hQP hPΩ hΩ_open hweak hu hdu with
    ⟨happrox⟩
  rcases scalarWeakSobolev_localSmoothApprox_endpoint_l2_on_compact
      hK hQ happrox hu_Q hsegments with
    ⟨hendpoint_meas, hendpoint_limit_meas, hendpoint_l2⟩
  rcases scalarWeakSobolev_localSmoothApprox_segmentIntegral_l2_on_compact
      hK hQ happrox hdu_Q hsegments with
    ⟨hintegral_meas, hintegral_limit_meas, hintegral_l2⟩
  exact
    ⟨{ approximants := happrox.approximants
       smooth := happrox.smooth
       endpoint_aestronglyMeasurable := hendpoint_meas
       endpoint_limit_aestronglyMeasurable := hendpoint_limit_meas
       endpoint_tendsto_l2 := hendpoint_l2
       integral_aestronglyMeasurable := hintegral_meas
       integral_limit_aestronglyMeasurable := hintegral_limit_meas
       integral_tendsto_l2 := hintegral_l2 }⟩

/--
%%handwave
name:
  Local smooth approximation in measure for the ACL theorem
statement:
  Under the same segment-containment hypotheses, the endpoint differences and
  integrated directional derivatives of the smooth approximants converge in
  measure on \(K\).
proof:
  Apply [the \(L^2(K)\) smooth approximation statement](lean:JJMath.Uniformization.scalarWeakSobolev_exists_smoothApprox_direction_l2_on_compact)
  and use that \(L^2\)-convergence implies convergence in measure.
-/
theorem scalarWeakSobolev_exists_smoothApprox_direction_inMeasure_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    Nonempty (ScalarWeakSobolevDirectionalSmoothApproxInMeasureData K u du h) := by
  rcases scalarWeakSobolev_exists_smoothApprox_direction_l2_on_compact
      hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments with
    ⟨happrox⟩
  exact ⟨scalarWeakSobolev_smoothApproxInMeasureData_of_l2 happrox⟩

/--
%%handwave
name:
  Local smooth approximation for the ACL theorem
statement:
  There is a subsequence of smooth approximants for which the endpoint
  differences and segment integrals both converge almost everywhere on \(K\).
proof:
  Use [convergence in measure of the two segment expressions](lean:JJMath.Uniformization.scalarWeakSobolev_exists_smoothApprox_direction_inMeasure_on_compact),
  then pass to a common almost-everywhere convergent subsequence.
-/
theorem scalarWeakSobolev_exists_geometric_smoothApprox_direction_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    Nonempty (ScalarWeakSobolevDirectionalSmoothApproxData K u du h) := by
  rcases scalarWeakSobolev_exists_smoothApprox_direction_inMeasure_on_compact
      hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments with
    ⟨happrox⟩
  exact scalarWeakSobolev_smoothApproxData_of_tendstoInMeasure happrox

/--
%%handwave
name:
  Smooth approximation gives the weak fundamental theorem on almost every segment
statement:
  If smooth \(v_n\) satisfy
  \(v_n(\cdot+h)-v_n\to u(\cdot+h)-u\) and
  \(\int_0^1 D_hv_n(\cdot+t h)\,dt\to
    \int_0^1 du(\cdot+t h)h\,dt\) almost everywhere on \(K\), then
  \[
    u(x+h)-u(x)=\int_0^1 du(x+t h)h\,dt
  \]
  for almost every \(x\in K\).
proof:
  Use the classical fundamental theorem for each \(v_n\).  At almost every
  \(x\), both sides converge to the weak expressions, so uniqueness of limits
  gives the identity.
-/
theorem scalarWeakSobolev_directional_acl_line_integral_eq_ae_of_smoothApproxData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {K : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {h : H}
    (happrox : ScalarWeakSobolevDirectionalSmoothApproxData K u du h) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      u (z + h) - u z =
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • h) h ∂MeasureTheory.volume := by
  rcases happrox with ⟨v, hv_smooth, hendpoint, hintegral⟩
  filter_upwards [hendpoint, hintegral] with z hz_endpoint hz_integral
  have hftc :
      ∀ n : ℕ,
        v n (z + h) - v n z =
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (v n) (z + t • h) h ∂MeasureTheory.volume := by
    intro n
    exact contDiff_endpoint_sub_eq_segmentIntegral_fderiv (hv_smooth n) z h
  have hz_integral' :
      Filter.Tendsto (fun n : ℕ ↦ v n (z + h) - v n z)
        Filter.atTop
        (𝓝 (∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • h) h ∂MeasureTheory.volume)) := by
    simpa [hftc] using hz_integral
  exact tendsto_nhds_unique hz_endpoint hz_integral'

/--
%%handwave
name:
  Weak Sobolev functions satisfy the fundamental theorem on almost every line
statement:
  If \(K,Q,P\) are compact with \(Q\) thickened inside \(P\subset\Omega\), if
  \(u\in L^2(P)\), \(du(\cdot)h\in L^2(P)\), and every segment
  \(x+t h\) from \(K\) lies in \(Q\), then
  \[
    u(x+h)-u(x)=\int_0^1 du(x+t h)h\,dt
  \]
  for almost every \(x\in K\).
proof:
  Combine [almost-everywhere smooth approximation along
  segments](lean:JJMath.Uniformization.scalarWeakSobolev_exists_geometric_smoothApprox_direction_on_compact)
  with [the limit-passing form of the segment fundamental theorem](lean:JJMath.Uniformization.scalarWeakSobolev_directional_acl_line_integral_eq_ae_of_smoothApproxData).
-/
theorem scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      u (z + h) - u z =
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • h) h ∂MeasureTheory.volume := by
  exact
    scalarWeakSobolev_directional_acl_line_integral_eq_ae_of_smoothApproxData
      (Classical.choice
        (scalarWeakSobolev_exists_geometric_smoothApprox_direction_on_compact
          hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments))

end

end Uniformization
end JJMath
