import JJMath.Analysis.Sobolev.Capacity
import JJMath.Analysis.Sobolev.Extension
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Poincare inequalities for surface Sobolev spaces

This file contains the capacitary Poincare estimates used in the energy
method, the equivalence between Dirichlet definiteness, capacitary Poincare,
and positive capacity, and the local Poincare inequality modulo constants.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal NNReal ContDiff Convolution

namespace Uniformization

noncomputable section

open ContinuousLinearMap

/--
%%handwave
name:
  Squared extended norm of a real number
statement:
  For every \(r\in\mathbb R\),
  \(\lVert r\rVert_{\!e}^{\,2}=\operatorname{ofReal}(r^2)\).
proof:
  Express the extended norm as the nonnegative-real embedding of \(|r|\),
  commute squaring with the embedding, and use \(|r|^2=r^2\).
-/
private theorem real_enorm_rpow_two_eq_ofReal_sq (r : ℝ) :
    ‖r‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (r ^ 2) := by
  rw [← ofReal_norm]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (norm_nonneg r) (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num [Real.rpow_natCast, sq, Real.norm_eq_abs]

/--
%%handwave
name:
  Local Euclidean \(L^2\) Poincare estimate on a ball
statement:
  For a Euclidean region \(\Omega\) and a ball \(B(c,r)\), this is the
  assertion that one finite constant works for every real-valued function
  \(u\) on the ambient vector space with a prescribed weak derivative field
  \(du\) on \(\Omega\): if \(u\) and \(du\) are square-integrable over
  \(B(c,r)\), then \(u\) is within that constant times
  \(\|du\|_{L^2(B(c,r))}\) of some constant function, measured in
  \(L^2(B(c,r))\).
-/
abbrev EuclideanSobolevPoincareL2EstimateOnBall
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    (Ω : Set H) (c : H) (r : ℝ) : Prop :=
  ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ {u : H → ℝ} {du : H → H →L[ℝ] ℝ},
      IsWeakDerivativeOnEuclideanRegionWithValues Ω u du →
        MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
        ∃ a : ℝ,
          AEStronglyMeasurable
            (fun y : H ↦ u y - a)
            (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
          eLpNorm (fun y : H ↦ u y - a) 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            C * eLpNorm du 2
              (MeasureTheory.volume.restrict (Metric.ball c r))

/--
%%handwave
name:
  Normalized bad sequence for the local Euclidean \(L^2\) Poincare inequality
statement:
  A normalized bad sequence on a ball consists of weak Sobolev functions whose
  \(L^2\)-norms on the ball are normalized to one, whose distance from every
  constant is at least one, and whose weak gradients converge to zero in
  \(L^2\) on the ball.
-/
structure EuclideanSobolevPoincareBadSequenceOnBall
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    (Ω : Set H) (c : H) (r : ℝ)
    (u : ℕ → H → ℝ) (du : ℕ → H → H →L[ℝ] ℝ) : Prop where
  weak :
    ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n)
  value_memLp :
    ∀ n : ℕ, MemLp (u n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r))
  derivative_memLp :
    ∀ n : ℕ, MemLp (du n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r))
  value_normalized :
    ∀ n : ℕ,
      eLpNorm (u n) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) = 1
  distance_from_constants :
    ∀ (n : ℕ) (a : ℝ),
      1 ≤ eLpNorm (fun y : H ↦ u n y - a) 2
        (MeasureTheory.volume.restrict (Metric.ball c r))
  gradient_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm (du n) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)))
      Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Failure of local Poincare gives a raw counterexample
statement:
  If the local Euclidean \(L^2\) Poincare estimate fails on a ball, then for
  every proposed finite constant there is a square-integrable weak Sobolev
  function for which no constant satisfies the corresponding estimate.
proof:
  This is the logical negation of the uniform estimate with the proposed
  finite constant fixed.
-/
theorem euclideanSobolev_poincare_rawCounterexample_of_failure_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hfail : ¬ EuclideanSobolevPoincareL2EstimateOnBall Ω c r)
    {C : ℝ≥0∞} (hC_top : C < ⊤) :
    ∃ (u : H → ℝ) (du : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
        MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
        MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
        ∀ a : ℝ,
          AEStronglyMeasurable
            (fun y : H ↦ u y - a)
            (MeasureTheory.volume.restrict (Metric.ball c r)) →
          ¬ eLpNorm (fun y : H ↦ u y - a) 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            C * eLpNorm du 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  classical
  by_contra hno
  apply hfail
  refine ⟨C, hC_top, ?_⟩
  intro u du hweak hu_mem hdu_mem
  by_contra hmissing
  have hbad :
      ∀ a : ℝ,
        AEStronglyMeasurable
          (fun y : H ↦ u y - a)
          (MeasureTheory.volume.restrict (Metric.ball c r)) →
        ¬ eLpNorm (fun y : H ↦ u y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          C * eLpNorm du 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    intro a hmeas hineq
    exact hmissing ⟨a, hmeas, hineq⟩
  exact hno ⟨u, du, hweak, hu_mem, hdu_mem, hbad⟩

/--
%%handwave
name:
  Center and scale data for one bad Poincare witness
statement:
  Center and scale data for a raw bad Poincare witness consists of a constant
  to subtract and a scalar by which to divide so that the resulting function
  has \(L^2\)-norm one, stays at \(L^2\)-distance at least one from every
  constant, and has weak-gradient \(L^2\)-norm bounded by \((n+1)^{-1}\).
-/
structure EuclideanSobolevPoincareCenterScaleDataOnBall
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    (Ω : Set H) (c : H) (r : ℝ) (n : ℕ)
    (u₀ : H → ℝ) (du₀ : H → H →L[ℝ] ℝ) where
  center : ℝ
  scale : ℝ
  weak :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun y : H ↦ scale * (u₀ y - center))
      (fun y : H ↦ scale • du₀ y)
  value_memLp :
    MemLp (fun y : H ↦ scale * (u₀ y - center)) 2
      (MeasureTheory.volume.restrict (Metric.ball c r))
  derivative_memLp :
    MemLp (fun y : H ↦ scale • du₀ y) 2
      (MeasureTheory.volume.restrict (Metric.ball c r))
  value_normalized :
    eLpNorm (fun y : H ↦ scale * (u₀ y - center)) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)) = 1
  distance_from_constants :
    ∀ a : ℝ,
      1 ≤ eLpNorm
        (fun y : H ↦ scale * (u₀ y - center) - a) 2
        (MeasureTheory.volume.restrict (Metric.ball c r))
  gradient_bound :
    eLpNorm (fun y : H ↦ scale • du₀ y) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
        ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)

/--
%%handwave
name:
  Best constant data for a strict Poincare witness
statement:
  Best constant data records an \(L^2\)-minimizing constant for a
  square-integrable weak Sobolev function on a ball, the resulting distance
  from constants, the weak derivative of the centered function, and the
  strict comparison between that distance and the weak-gradient norm.
-/
structure EuclideanSobolevPoincareBestCenterDataOnBall
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    (Ω : Set H) (c : H) (r : ℝ) (n : ℕ)
    (u₀ : H → ℝ) (du₀ : H → H →L[ℝ] ℝ) where
  center : ℝ
  distance : ℝ≥0∞
  centered_weak :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun y : H ↦ u₀ y - center) du₀
  centered_memLp :
    MemLp (fun y : H ↦ u₀ y - center) 2
      (MeasureTheory.volume.restrict (Metric.ball c r))
  derivative_memLp :
    MemLp du₀ 2 (MeasureTheory.volume.restrict (Metric.ball c r))
  distance_eq :
    eLpNorm (fun y : H ↦ u₀ y - center) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)) = distance
  distance_ne_zero : distance ≠ 0
  distance_lt_top : distance < ⊤
  distance_minimizes :
    ∀ a : ℝ,
      distance ≤ eLpNorm (fun y : H ↦ u₀ y - a) 2
        (MeasureTheory.volume.restrict (Metric.ball c r))
  gradient_strict :
    (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
        eLpNorm du₀ 2 (MeasureTheory.volume.restrict (Metric.ball c r)) <
      distance

/--
%%handwave
name:
  Subtracting a constant preserves a scalar Euclidean weak derivative
statement:
  If a scalar function on a finite-dimensional Euclidean region has a weak
  derivative field, then subtracting a constant from the function leaves the
  same weak derivative field.
proof:
  In the weak derivative identity, the only new term is the integral of the
  directional derivative of a compactly supported smooth test function times
  the constant.  This integral vanishes by integration by parts against the
  constant function, since the test is compactly supported in the region.
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.sub_const_real
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (a : ℝ)
    (hu : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du) :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun z : H ↦ u z - a) du := by
  intro φ v
  rcases hu φ v with ⟨hu_int, hdu_int, h_eq⟩
  let dφ : H → ℝ := fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v
  have hφ_compact : HasCompactSupport (φ : H → ℝ) := φ.compact_support
  have hφ_cont : Continuous (φ : H → ℝ) := φ.smooth.continuous
  have hdφ_compact : HasCompactSupport dφ := by
    simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) v
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ_int : Integrable dφ (MeasureTheory.volume : Measure H) :=
    hdφ_cont.integrable_of_hasCompactSupport hdφ_compact
  have hconst_intΩ :
      Integrable (fun z : H ↦ dφ z • a)
        (MeasureTheory.volume.restrict Ω) :=
    (hdφ_int.smul_const a).mono_measure Measure.restrict_le_self
  have hconst_zeroΩ :
      ∫ z in Ω, dφ z • a ∂MeasureTheory.volume = 0 := by
    have hsupport :
        ∀ z : H, z ∉ Ω → dφ z • a = 0 := by
      intro z hzΩ
      have hz_not_tsupport : z ∉ tsupport dφ := by
        intro hz
        exact hzΩ <| φ.support_subset <|
          (tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (φ : H → ℝ)) v) (by simpa [dφ] using hz)
      have hdφ_zero : dφ z = 0 :=
        image_eq_zero_of_notMem_tsupport hz_not_tsupport
      simp [hdφ_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
    have hφ_int : Integrable (φ : H → ℝ)
        (MeasureTheory.volume : Measure H) :=
      hφ_cont.integrable_of_hasCompactSupport hφ_compact
    have hibp :
        ∫ z, (φ : H → ℝ) z •
            fderiv ℝ (fun _ : H ↦ a) z v ∂MeasureTheory.volume =
          -∫ z, fderiv ℝ (φ : H → ℝ) z v • a
            ∂MeasureTheory.volume :=
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (μ := (MeasureTheory.volume : Measure H))
        (f := (φ : H → ℝ)) (g := fun _ : H ↦ a) (v := v)
        (by simpa [dφ] using hdφ_int.smul_const a)
        (by simp)
        (hφ_int.smul_const a)
        (fun z _hz ↦ (φ.smooth.differentiable (by simp)) z)
        (fun z _hz ↦ differentiableAt_const a)
    have hzero_neg :
        (0 : ℝ) =
          -∫ z, fderiv ℝ (φ : H → ℝ) z v • a
            ∂MeasureTheory.volume := by
      simpa using hibp
    simpa [dφ] using neg_eq_zero.mp hzero_neg.symm
  refine ⟨?_, hdu_int, ?_⟩
  · convert hu_int.sub hconst_intΩ using 1
    ext z
    simp [dφ]
    ring
  · calc
      ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • (u z - a)
          ∂MeasureTheory.volume
          =
        ∫ z in Ω,
          ((fderiv ℝ (φ : H → ℝ) z v) • u z -
            (fderiv ℝ (φ : H → ℝ) z v) • a)
          ∂MeasureTheory.volume := by
            congr 1
            ext z
            exact smul_sub ((fderiv ℝ (φ : H → ℝ) z) v) (u z) a
      _ =
        ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • u z
          ∂MeasureTheory.volume -
        ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • a
          ∂MeasureTheory.volume := by
            simpa [dφ] using integral_sub hu_int hconst_intΩ
      _ = -∫ z in Ω, φ z • du z v ∂MeasureTheory.volume - 0 := by
            rw [h_eq, hconst_zeroΩ]
      _ = -∫ z in Ω, φ z • du z v ∂MeasureTheory.volume := by
            simp

/--
%%handwave
name:
  Existence of an \(L^2\)-best constant on a finite-measure ball
statement:
  For a square-integrable real-valued function on a finite-measure Euclidean
  ball, there is a constant minimizing its \(L^2\)-distance from the function
  among all constants.
proof:
  Project the \(L^2\) class of the function onto the closed one-dimensional
  subspace of constant functions on the ball.  The representing constant is
  the minimizing center.
-/
theorem euclideanSobolev_poincare_exists_L2_best_center_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {c : H} {r : ℝ}
    [IsFiniteMeasure (MeasureTheory.volume.restrict (Metric.ball c r))]
    {u₀ : H → ℝ}
    (hu₀_mem : MemLp u₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ center : ℝ,
      ∀ a : ℝ,
        eLpNorm (fun y : H ↦ u₀ y - center) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
        eLpNorm (fun y : H ↦ u₀ y - a) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  classical
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let L : ℝ →L[ℝ] Lp ℝ (2 : ℝ≥0∞) μB :=
    Lp.constL (2 : ℝ≥0∞) μB ℝ
  let K : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) μB) :=
    LinearMap.range L.toLinearMap
  haveI : FiniteDimensional ℝ K := by
    dsimp [K]
    infer_instance
  have hK_closed : IsClosed (K : Set (Lp ℝ (2 : ℝ≥0∞) μB)) :=
    Submodule.closed_of_finiteDimensional K
  haveI : CompleteSpace K := hK_closed.completeSpace_coe
  haveI : K.HasOrthogonalProjection := inferInstance
  let F : Lp ℝ (2 : ℝ≥0∞) μB := hu₀_mem.toLp u₀
  let p : Lp ℝ (2 : ℝ≥0∞) μB := K.starProjection F
  have hp_mem : p ∈ K := by
    simp [p]
  rcases hp_mem with ⟨center, hcenter⟩
  have hp_mem : p ∈ K := ⟨center, hcenter⟩
  refine ⟨center, ?_⟩
  intro a
  have hp_eq : p = L center := by
    simpa [K, L] using hcenter.symm
  have hLa_mem : L a ∈ K := by
    exact ⟨a, rfl⟩
  have hnorm_min : ‖F - p‖ ≤ ‖F - L a‖ := by
    have hpq_mem : p - L a ∈ K := K.sub_mem hp_mem hLa_mem
    have horth : inner ℝ (F - p) (p - L a) = 0 := by
      change inner ℝ (F - K.starProjection F) (p - L a) = 0
      exact K.inner_left_of_mem_orthogonal hpq_mem
        (K.sub_starProjection_mem_orthogonal F)
    have hdecomp : F - L a = (F - p) + (p - L a) := by
      abel
    have hsq :
        ‖F - p‖ * ‖F - p‖ ≤ ‖F - L a‖ * ‖F - L a‖ := by
      rw [hdecomp,
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth]
      nlinarith [sq_nonneg (‖p - L a‖)]
    nlinarith [hsq, norm_nonneg (F - p), norm_nonneg (F - L a)]
  have hed_min : edist F p ≤ edist F (L a) := by
    rw [edist_dist, edist_dist]
    exact ENNReal.ofReal_le_ofReal (by simpa [dist_eq_norm] using hnorm_min)
  have hcenter_edist :
      edist F (L center) =
        eLpNorm (fun y : H ↦ u₀ y - center) 2 μB := by
    simpa [F, L, μB, Pi.sub_apply] using
      (Lp.edist_toLp_toLp u₀ (fun _ : H ↦ center)
        hu₀_mem
        (memLp_const center :
          MemLp (fun _ : H ↦ center) 2 μB))
  have ha_edist :
      edist F (L a) =
        eLpNorm (fun y : H ↦ u₀ y - a) 2 μB := by
    simpa [F, L, μB, Pi.sub_apply] using
      (Lp.edist_toLp_toLp u₀ (fun _ : H ↦ a)
        hu₀_mem
        (memLp_const a :
          MemLp (fun _ : H ↦ a) 2 μB))
  calc
    eLpNorm (fun y : H ↦ u₀ y - center) 2
        (MeasureTheory.volume.restrict (Metric.ball c r))
        = edist F (L center) := by
          simpa [μB] using hcenter_edist.symm
    _ = edist F p := by rw [hp_eq]
    _ ≤ edist F (L a) := hed_min
    _ = eLpNorm (fun y : H ↦ u₀ y - a) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) := by
          simpa [μB] using ha_edist

/--
%%handwave
name:
  Existence of an \(L^2\)-best constant for a weak Sobolev function on a ball
statement:
  For a square-integrable weak Sobolev function on a finite-dimensional
  Euclidean ball, there is a constant minimizing its \(L^2\)-distance from the
  function among all constants.  Subtracting this constant preserves the weak
  derivative.
proof:
  Choose the \(L^2\)-minimizing constant.  The weak derivative is unchanged by
  subtracting a constant, so the centered function has the same weak
  derivative field.
-/
theorem euclideanSobolev_poincare_exists_best_center_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    {u₀ : H → ℝ} {du₀ : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u₀ du₀)
    (hu₀_mem : MemLp u₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ center : ℝ,
      IsWeakDerivativeOnEuclideanRegionWithValues Ω
        (fun y : H ↦ u₀ y - center) du₀ ∧
      ∀ a : ℝ,
        eLpNorm (fun y : H ↦ u₀ y - center) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
        eLpNorm (fun y : H ↦ u₀ y - a) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    exact isFiniteMeasure_restrict.2
      (measure_ball_ne_top (μ := (volume : Measure H)))
  rcases euclideanSobolev_poincare_exists_L2_best_center_on_ball
      (c := c) (r := r) hu₀_mem with
    ⟨center, hcenter_min⟩
  exact ⟨center, hweak.sub_const_real center, hcenter_min⟩

/--
%%handwave
name:
  Strict distance data has a best constant
statement:
  If every constant lies at \(L^2\)-distance strictly larger than \(n+1\)
  times the weak-gradient norm from a square-integrable weak Sobolev function
  on a ball, then there is a constant minimizing this distance, and the
  centered function has the same weak derivative.
proof:
  View the function as an element of the Hilbert space \(L^2\) on the ball and
  project it onto the one-dimensional subspace of constant functions.  The
  strict comparison gives positivity of the distance, while finite
  square-integrability gives finiteness.  Subtracting a constant does not
  change the weak derivative.
-/
theorem euclideanSobolev_poincare_bestCenterData_of_strict_distance_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (_hr_pos : 0 < r)
    (_hΩ_open : IsOpen Ω)
    (_hballΩ : Metric.ball c r ⊆ Ω)
    (n : ℕ)
    {u₀ : H → ℝ} {du₀ : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u₀ du₀)
    (hu₀_mem : MemLp u₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdu₀_mem : MemLp du₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hstrict :
      ∀ a : ℝ,
        (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
            eLpNorm du₀ 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) <
          eLpNorm (fun y : H ↦ u₀ y - a) 2
              (MeasureTheory.volume.restrict (Metric.ball c r))) :
    Nonempty
      (EuclideanSobolevPoincareBestCenterDataOnBall Ω c r n u₀ du₀) := by
  classical
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  haveI : IsFiniteMeasure μB := by
    change IsFiniteMeasure ((volume : Measure H).restrict (Metric.ball c r))
    exact isFiniteMeasure_restrict.2 (measure_ball_ne_top (μ := (volume : Measure H)))
  rcases euclideanSobolev_poincare_exists_best_center_on_ball
      (Ω := Ω) (c := c) (r := r) hweak hu₀_mem with
    ⟨center, hcenter_weak, hcenter_min⟩
  let distance : ℝ≥0∞ :=
    eLpNorm (fun y : H ↦ u₀ y - center) 2 μB
  have hcenter_mem :
      MemLp (fun y : H ↦ u₀ y - center) 2 μB := by
    have hconst_mem : MemLp (fun _ : H ↦ center) 2 μB := memLp_const center
    simpa [μB, Pi.sub_apply] using hu₀_mem.sub hconst_mem
  have hdistance_ne_zero : distance ≠ 0 := by
    intro hzero
    have hlt :
        (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
            eLpNorm du₀ 2 μB < 0 := by
      simpa [distance, μB, hzero] using hstrict center
    exact (not_lt_of_ge bot_le) hlt
  refine ⟨
    { center := center
      distance := distance
      centered_weak := hcenter_weak
      centered_memLp := hcenter_mem
      derivative_memLp := hdu₀_mem
      distance_eq := rfl
      distance_ne_zero := hdistance_ne_zero
      distance_lt_top := ?_
      distance_minimizes := ?_
      gradient_strict := ?_ }⟩
  · simpa [distance] using hcenter_mem.2
  · intro a
    simpa [distance, μB] using hcenter_min a
  · simpa [distance, μB] using hstrict center

/--
%%handwave
name:
  Rescaling best constant data
statement:
  If a centered weak Sobolev function realizes the positive finite
  \(L^2\)-distance to constants and this distance is strictly larger than
  \(n+1\) times the weak-gradient norm, then dividing by that distance gives
  a normalized function whose \(L^2\)-norm is one, whose distance from every
  constant is at least one, and whose weak-gradient norm is at most
  \((n+1)^{-1}\).
proof:
  Multiply the centered function and its weak derivative by the inverse of the
  positive finite distance.  The \(L^2\)-norm and weak-gradient norm scale by
  the absolute value of this scalar, and minimality of the centered distance
  gives the lower bound against all constants after rescaling.
-/
theorem euclideanSobolev_poincare_exists_center_scale_of_bestCenterData_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {Ω : Set H} {c : H} {r : ℝ} {n : ℕ}
    {u₀ : H → ℝ} {du₀ : H → H →L[ℝ] ℝ}
    (hdata : EuclideanSobolevPoincareBestCenterDataOnBall Ω c r n u₀ du₀) :
    ∃ center scale : ℝ,
      IsWeakDerivativeOnEuclideanRegionWithValues Ω
        (fun y : H ↦ scale * (u₀ y - center))
        (fun y : H ↦ scale • du₀ y) ∧
      MemLp (fun y : H ↦ scale * (u₀ y - center)) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      MemLp (fun y : H ↦ scale • du₀ y) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      eLpNorm (fun y : H ↦ scale * (u₀ y - center)) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) = 1 ∧
      (∀ a : ℝ,
        1 ≤ eLpNorm
          (fun y : H ↦ scale * (u₀ y - center) - a) 2
          (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
      eLpNorm (fun y : H ↦ scale • du₀ y) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
  classical
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let D : ℝ≥0∞ := hdata.distance
  let scale : ℝ := D.toReal⁻¹
  have hD_ne_top : D ≠ (∞ : ℝ≥0∞) := by
    exact ne_of_lt (by simpa [D] using hdata.distance_lt_top)
  have hD_pos_toReal : 0 < D.toReal :=
    ENNReal.toReal_pos hdata.distance_ne_zero hD_ne_top
  have hscale_ne_zero : scale ≠ 0 := by
    exact inv_ne_zero hD_pos_toReal.ne'
  have hscale_enorm : ‖scale‖ₑ = D⁻¹ := by
    have hnorm_scale : ‖scale‖ = D.toReal⁻¹ := by
      change ‖D.toReal⁻¹‖ = D.toReal⁻¹
      rw [norm_inv, Real.norm_of_nonneg hD_pos_toReal.le]
    calc
      ‖scale‖ₑ = ENNReal.ofReal ‖scale‖ := (ofReal_norm scale).symm
      _ = ENNReal.ofReal D.toReal⁻¹ := by rw [hnorm_scale]
      _ = (ENNReal.ofReal D.toReal)⁻¹ :=
          ENNReal.ofReal_inv_of_pos hD_pos_toReal
      _ = D⁻¹ := by rw [ENNReal.ofReal_toReal hD_ne_top]
  refine ⟨hdata.center, scale, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [scale, smul_eq_mul] using
      (IsWeakDerivativeOnEuclideanRegionWithValues.const_smul
        (H := H) (E := ℝ) scale hdata.centered_weak)
  · simpa [scale, smul_eq_mul] using hdata.centered_memLp.const_smul scale
  · exact hdata.derivative_memLp.const_smul scale
  · calc
      eLpNorm (fun y : H ↦ scale * (u₀ y - hdata.center)) 2
          (MeasureTheory.volume.restrict (Metric.ball c r))
          = eLpNorm (fun y : H ↦ scale • (u₀ y - hdata.center)) 2 μB := by
              simp [μB, smul_eq_mul]
      _ = ‖scale‖ₑ *
          eLpNorm (fun y : H ↦ u₀ y - hdata.center) 2 μB := by
              simpa [Pi.smul_apply] using
                (eLpNorm_const_smul (μ := μB) (c := scale)
                  (f := fun y : H ↦ u₀ y - hdata.center) (p := (2 : ℝ≥0∞)))
      _ = D⁻¹ * D := by
              rw [hscale_enorm]
              exact congrArg (fun x ↦ D⁻¹ * x)
                (by simpa [D, μB] using hdata.distance_eq)
      _ = 1 := ENNReal.inv_mul_cancel hdata.distance_ne_zero hD_ne_top
  · intro a
    have hrescale :
        eLpNorm (fun y : H ↦ scale * (u₀ y - hdata.center) - a) 2 μB =
          D⁻¹ *
            eLpNorm
              (fun y : H ↦ u₀ y - (hdata.center + a / scale)) 2 μB := by
      calc
        eLpNorm (fun y : H ↦ scale * (u₀ y - hdata.center) - a) 2 μB
            = eLpNorm
                (fun y : H ↦
                  scale * (u₀ y - (hdata.center + a / scale))) 2 μB := by
                congr 1
                ext y
                field_simp [hscale_ne_zero]
                ring
        _ = eLpNorm
              (fun y : H ↦ scale • (u₀ y - (hdata.center + a / scale))) 2
              μB := by
                simp [smul_eq_mul]
        _ = ‖scale‖ₑ *
            eLpNorm
              (fun y : H ↦ u₀ y - (hdata.center + a / scale)) 2 μB := by
                simpa [Pi.smul_apply] using
                  (eLpNorm_const_smul (μ := μB) (c := scale)
                    (f := fun y : H ↦ u₀ y - (hdata.center + a / scale))
                    (p := (2 : ℝ≥0∞)))
        _ = D⁻¹ *
            eLpNorm
              (fun y : H ↦ u₀ y - (hdata.center + a / scale)) 2 μB := by
                rw [hscale_enorm]
    calc
      (1 : ℝ≥0∞) = D⁻¹ * D := by
          exact (ENNReal.inv_mul_cancel hdata.distance_ne_zero hD_ne_top).symm
      _ ≤ D⁻¹ *
          eLpNorm (fun y : H ↦ u₀ y - (hdata.center + a / scale)) 2 μB := by
          exact mul_le_mul_right (hdata.distance_minimizes _) D⁻¹
      _ = eLpNorm (fun y : H ↦ scale * (u₀ y - hdata.center) - a) 2 μB :=
          hrescale.symm
  · let Cnn : ℝ≥0 := (n : ℝ≥0) + 1
    let C : ℝ≥0∞ := (Cnn : ℝ≥0∞)
    have hCnn_pos : 0 < Cnn := by
      positivity
    have hC_ne_zero : C ≠ 0 :=
      ENNReal.coe_ne_zero.mpr hCnn_pos.ne'
    have hC_ne_top : C ≠ (∞ : ℝ≥0∞) := ENNReal.coe_ne_top
    have hC_inv_eq :
        C⁻¹ = ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
      rw [show C = (Cnn : ℝ≥0∞) from rfl]
      rw [show ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) =
          ((Cnn⁻¹ : ℝ≥0) : ℝ≥0∞) by simp [Cnn, one_div]]
      exact (ENNReal.coe_inv hCnn_pos.ne').symm
    have hgrad_scale :
        eLpNorm (fun y : H ↦ scale • du₀ y) 2 μB =
          D⁻¹ * eLpNorm du₀ 2 μB := by
      calc
        eLpNorm (fun y : H ↦ scale • du₀ y) 2 μB
            = ‖scale‖ₑ * eLpNorm du₀ 2 μB := by
                simpa [Pi.smul_apply] using
                  (eLpNorm_const_smul (μ := μB) (c := scale)
                    (f := du₀) (p := (2 : ℝ≥0∞)))
        _ = D⁻¹ * eLpNorm du₀ 2 μB := by
                rw [hscale_enorm]
    have hG_le :
        eLpNorm du₀ 2 μB ≤ C⁻¹ * D := by
      calc
        eLpNorm du₀ 2 μB
            = C⁻¹ * (C * eLpNorm du₀ 2 μB) := by
                rw [ENNReal.inv_mul_cancel_left hC_ne_zero hC_ne_top]
        _ ≤ C⁻¹ * D := by
                refine mul_le_mul_right ?_ C⁻¹
                simpa [C, Cnn, D, μB] using hdata.gradient_strict.le
    have hgrad_le :
        D⁻¹ * eLpNorm du₀ 2 μB ≤ C⁻¹ := by
      calc
        D⁻¹ * eLpNorm du₀ 2 μB ≤ D⁻¹ * (C⁻¹ * D) := by
            exact mul_le_mul_right hG_le D⁻¹
        _ = C⁻¹ := by
            rw [← mul_assoc, mul_comm (D⁻¹) (C⁻¹), mul_assoc,
              ENNReal.inv_mul_cancel hdata.distance_ne_zero hD_ne_top, mul_one]
    calc
      eLpNorm (fun y : H ↦ scale • du₀ y) 2
          (MeasureTheory.volume.restrict (Metric.ball c r))
          = D⁻¹ * eLpNorm du₀ 2 μB := by
              simpa [μB] using hgrad_scale
      _ ≤ C⁻¹ := hgrad_le
      _ = ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := hC_inv_eq

/--
%%handwave
name:
  Strict distance data gives a normalized center and scale
statement:
  If every constant lies at \(L^2\)-distance strictly larger than \(n+1\)
  times the weak-gradient norm from a square-integrable weak Sobolev function,
  then one can choose a best constant and rescale the centered function to
  have \(L^2\)-norm one, distance at least one from every constant, and
  weak-gradient norm at most \((n+1)^{-1}\).
proof:
  Choose the \(L^2\)-best constant, subtract it, and divide by the positive
  distance to the constants.  The strict comparison between this distance and
  \((n+1)\) times the gradient norm becomes the normalized gradient bound
  after scaling.
-/
theorem euclideanSobolev_poincare_exists_center_scale_of_strict_distance_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (n : ℕ)
    {u₀ : H → ℝ} {du₀ : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u₀ du₀)
    (hu₀_mem : MemLp u₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdu₀_mem : MemLp du₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hstrict :
      ∀ a : ℝ,
        (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
            eLpNorm du₀ 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) <
          eLpNorm (fun y : H ↦ u₀ y - a) 2
              (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ center scale : ℝ,
      IsWeakDerivativeOnEuclideanRegionWithValues Ω
        (fun y : H ↦ scale * (u₀ y - center))
        (fun y : H ↦ scale • du₀ y) ∧
      MemLp (fun y : H ↦ scale * (u₀ y - center)) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      MemLp (fun y : H ↦ scale • du₀ y) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      eLpNorm (fun y : H ↦ scale * (u₀ y - center)) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) = 1 ∧
      (∀ a : ℝ,
        1 ≤ eLpNorm
          (fun y : H ↦ scale * (u₀ y - center) - a) 2
          (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
      eLpNorm (fun y : H ↦ scale • du₀ y) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
  rcases
    euclideanSobolev_poincare_bestCenterData_of_strict_distance_on_ball
      hr_pos hΩ_open hballΩ n hweak hu₀_mem hdu₀_mem hstrict with
    ⟨hdata⟩
  exact
    euclideanSobolev_poincare_exists_center_scale_of_bestCenterData_on_ball
      hdata

/--
%%handwave
name:
  A square-integrable raw Poincare witness has a normalized center and scale
statement:
  A square-integrable raw witness that defeats the proposed constant \(n+1\)
  admits a constant to subtract and a scalar by which to rescale so that the
  centered function has \(L^2\)-norm one, remains at distance at least one
  from every constant, and has weak-gradient norm at most \((n+1)^{-1}\).
proof:
  The raw failure says exactly that every constant lies at \(L^2\)-distance
  strictly larger than \(n+1\) times the weak-gradient norm.  Apply the
  normalized center-and-scale construction for this strict distance data.
-/
theorem euclideanSobolev_poincare_exists_center_scale_of_rawCounterexample_witness_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (n : ℕ)
    {u₀ : H → ℝ} {du₀ : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u₀ du₀)
    (hu₀_mem : MemLp u₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdu₀_mem : MemLp du₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hraw :
      ∀ a : ℝ,
        AEStronglyMeasurable
          (fun y : H ↦ u₀ y - a)
          (MeasureTheory.volume.restrict (Metric.ball c r)) →
        ¬ eLpNorm (fun y : H ↦ u₀ y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
            eLpNorm du₀ 2
              (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ center scale : ℝ,
      IsWeakDerivativeOnEuclideanRegionWithValues Ω
        (fun y : H ↦ scale * (u₀ y - center))
        (fun y : H ↦ scale • du₀ y) ∧
      MemLp (fun y : H ↦ scale * (u₀ y - center)) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      MemLp (fun y : H ↦ scale • du₀ y) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      eLpNorm (fun y : H ↦ scale * (u₀ y - center)) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) = 1 ∧
      (∀ a : ℝ,
        1 ≤ eLpNorm
          (fun y : H ↦ scale * (u₀ y - center) - a) 2
          (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
      eLpNorm (fun y : H ↦ scale • du₀ y) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
  classical
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  have hshift_meas :
      ∀ a : ℝ,
        AEStronglyMeasurable (fun y : H ↦ u₀ y - a) μB := by
    intro a
    exact hu₀_mem.aestronglyMeasurable.sub
      (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : H ↦ a) μB)
  have hstrict :
      ∀ a : ℝ,
        (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
            eLpNorm du₀ 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) <
          eLpNorm (fun y : H ↦ u₀ y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    intro a
    exact lt_of_not_ge (hraw a (by simpa [μB] using hshift_meas a))
  exact
    euclideanSobolev_poincare_exists_center_scale_of_strict_distance_on_ball
      hr_pos hΩ_open hballΩ n hweak hu₀_mem hdu₀_mem hstrict

/--
%%handwave
name:
  Raw bad Poincare witnesses admit center and scale data
statement:
  A raw weak Sobolev witness that defeats the proposed constant \(n+1\) has
  center and scale data on the ball: subtract an \(L^2\)-best constant and
  divide by the resulting positive distance from constants.
proof:
  The \(L^2\)-projection onto the one-dimensional subspace of constants gives
  a best constant.  The raw failure forces the corresponding distance to be
  positive and larger than \((n+1)\) times the gradient norm.  Stability of
  weak derivatives under subtracting constants and multiplying by scalars
  gives the centered and rescaled weak derivative.
-/
theorem euclideanSobolev_poincare_centerScaleData_of_rawCounterexample_witness_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (n : ℕ)
    {u₀ : H → ℝ} {du₀ : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u₀ du₀)
    (hu₀_mem : MemLp u₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdu₀_mem : MemLp du₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hraw :
      ∀ a : ℝ,
        AEStronglyMeasurable
          (fun y : H ↦ u₀ y - a)
          (MeasureTheory.volume.restrict (Metric.ball c r)) →
        ¬ eLpNorm (fun y : H ↦ u₀ y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
            eLpNorm du₀ 2
              (MeasureTheory.volume.restrict (Metric.ball c r))) :
    Nonempty
      (EuclideanSobolevPoincareCenterScaleDataOnBall Ω c r n u₀ du₀) := by
  rcases
    euclideanSobolev_poincare_exists_center_scale_of_rawCounterexample_witness_on_ball
      hr_pos hΩ_open hballΩ n hweak hu₀_mem hdu₀_mem hraw with
    ⟨center, scale, hweak', hvalue_mem, hderivative_mem, hnorm, hdist, hgrad⟩
  exact ⟨
    { center := center
      scale := scale
      weak := hweak'
      value_memLp := hvalue_mem
      derivative_memLp := hderivative_mem
      value_normalized := hnorm
      distance_from_constants := hdist
      gradient_bound := hgrad }⟩

/--
%%handwave
name:
  A raw Poincare counterexample witness can be normalized
statement:
  A single weak Sobolev function that defeats the proposed Poincare constant
  \(n+1\) can be replaced by a centered and rescaled weak Sobolev function
  whose \(L^2\)-norm is one, whose distance from every constant is at least
  one, and whose weak-gradient \(L^2\)-norm is at most \((n+1)^{-1}\).
proof:
  Choose a constant minimizing the \(L^2\)-distance to constants, subtract it,
  and divide by that positive distance.  Weak derivatives are stable under
  subtracting constants and multiplying by scalars, and the failed Poincare
  inequality gives the gradient bound after division.
-/
theorem euclideanSobolev_poincare_normalize_rawCounterexample_witness_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (n : ℕ)
    {u₀ : H → ℝ} {du₀ : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u₀ du₀)
    (hu₀_mem : MemLp u₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdu₀_mem : MemLp du₀ 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hraw :
      ∀ a : ℝ,
        AEStronglyMeasurable
          (fun y : H ↦ u₀ y - a)
          (MeasureTheory.volume.restrict (Metric.ball c r)) →
        ¬ eLpNorm (fun y : H ↦ u₀ y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
            eLpNorm du₀ 2
              (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ (u : H → ℝ) (du : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
        MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
        MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
        eLpNorm u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) = 1 ∧
        (∀ a : ℝ,
          1 ≤ eLpNorm (fun y : H ↦ u y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
        eLpNorm du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
  classical
  let hdata :=
    euclideanSobolev_poincare_centerScaleData_of_rawCounterexample_witness_on_ball
      hr_pos hΩ_open hballΩ n hweak hu₀_mem hdu₀_mem hraw
  rcases hdata with ⟨hdata⟩
  refine
    ⟨fun y : H ↦ hdata.scale * (u₀ y - hdata.center),
      fun y : H ↦ hdata.scale • du₀ y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdata.weak
  · exact hdata.value_memLp
  · exact hdata.derivative_memLp
  · exact hdata.value_normalized
  · exact hdata.distance_from_constants
  · exact hdata.gradient_bound

/--
%%handwave
name:
  Raw Poincare counterexamples can be normalized
statement:
  A raw counterexample to a proposed Poincare constant \(n+1\) can be centered
  and rescaled so that its distance from every constant is at least one, its
  \(L^2\)-norm is one, and its weak-gradient \(L^2\)-norm is at most
  \((n+1)^{-1}\).
proof:
  Choose an \(L^2\)-best constant, subtract it, and divide by the resulting
  positive \(L^2\)-distance to the constants.  The raw counterexample
  inequality says this distance is larger than \((n+1)\) times the gradient
  norm, which gives the required normalized gradient bound.
-/
theorem euclideanSobolev_poincare_normalize_rawCounterexample_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (n : ℕ)
    (hraw :
      ∃ (u : H → ℝ) (du : H → H →L[ℝ] ℝ),
        IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
          MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
          MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
          ∀ a : ℝ,
            AEStronglyMeasurable
              (fun y : H ↦ u y - a)
              (MeasureTheory.volume.restrict (Metric.ball c r)) →
            ¬ eLpNorm (fun y : H ↦ u y - a) 2
                (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
              (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
                eLpNorm du 2
                  (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ (u : H → ℝ) (du : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
        MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
        MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
        eLpNorm u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) = 1 ∧
        (∀ a : ℝ,
          1 ≤ eLpNorm (fun y : H ↦ u y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
        eLpNorm du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
  rcases hraw with ⟨u₀, du₀, hweak, hu₀_mem, hdu₀_mem, hraw₀⟩
  exact
    euclideanSobolev_poincare_normalize_rawCounterexample_witness_on_ball
      hr_pos hΩ_open hballΩ n hweak hu₀_mem hdu₀_mem hraw₀

/--
%%handwave
name:
  Failure of local Poincare gives one normalized counterexample
statement:
  If the local Euclidean \(L^2\) Poincare estimate fails on a ball, then at
  every scale one can find a normalized counterexample whose weak-gradient
  \(L^2\)-norm is bounded by that scale.
proof:
  Apply failure of the estimate with the chosen finite constant.  Center the
  function by an \(L^2\)-best constant and divide by its distance from the
  constants.
-/
theorem euclideanSobolev_poincare_badSequence_term_of_failure_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (hfail : ¬ EuclideanSobolevPoincareL2EstimateOnBall Ω c r)
    (n : ℕ) :
    ∃ (u : H → ℝ) (du : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
        MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
        MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
        eLpNorm u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) = 1 ∧
        (∀ a : ℝ,
          1 ≤ eLpNorm (fun y : H ↦ u y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
        eLpNorm du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
  classical
  let C : ℝ≥0∞ := (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞)
  have hC_top : C < ⊤ := by
    exact ENNReal.coe_lt_top
  have hraw :
      ∃ (u : H → ℝ) (du : H → H →L[ℝ] ℝ),
        IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
          MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
          MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
          ∀ a : ℝ,
            AEStronglyMeasurable
              (fun y : H ↦ u y - a)
              (MeasureTheory.volume.restrict (Metric.ball c r)) →
            ¬ eLpNorm (fun y : H ↦ u y - a) 2
                (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
              (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) *
                eLpNorm du 2
                  (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    simpa [C] using
      euclideanSobolev_poincare_rawCounterexample_of_failure_on_ball
        (Ω := Ω) (c := c) (r := r) hfail hC_top
  exact
    euclideanSobolev_poincare_normalize_rawCounterexample_on_ball
      hr_pos hΩ_open hballΩ n hraw

/--
%%handwave
name:
  Failure of local Poincare produces a normalized bad sequence
statement:
  If the local Euclidean \(L^2\) Poincare estimate fails on a ball, then one
  can choose a normalized bad sequence on that ball.
proof:
  For the \(n\)-th term, use failure of the estimate with the finite constant
  \(n+1\).  Subtract an \(L^2\)-minimizing constant and rescale by the
  distance from the constants.  This makes the distance from all constants at
  least one, normalizes the \(L^2\)-norm, and forces the weak-gradient
  \(L^2\)-norm to tend to zero.
-/
theorem euclideanSobolev_poincare_badSequence_of_failure_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (hfail : ¬ EuclideanSobolevPoincareL2EstimateOnBall Ω c r) :
    ∃ (u : ℕ → H → ℝ) (du : ℕ → H → H →L[ℝ] ℝ),
      EuclideanSobolevPoincareBadSequenceOnBall Ω c r u du := by
  classical
  have hterms :
      ∀ n : ℕ, ∃ (u : H → ℝ) (du : H → H →L[ℝ] ℝ),
        IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
          MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
          MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
          eLpNorm u 2 (MeasureTheory.volume.restrict (Metric.ball c r)) = 1 ∧
          (∀ a : ℝ,
            1 ≤ eLpNorm (fun y : H ↦ u y - a) 2
              (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
          eLpNorm du 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
    intro n
    exact euclideanSobolev_poincare_badSequence_term_of_failure_on_ball
      hr_pos hΩ_open hballΩ hfail n
  choose u du hterm using hterms
  refine ⟨u, du, ?_⟩
  refine
    { weak := fun n ↦ (hterm n).1
      value_memLp := fun n ↦ (hterm n).2.1
      derivative_memLp := fun n ↦ (hterm n).2.2.1
      value_normalized := fun n ↦ (hterm n).2.2.2.1
      distance_from_constants := fun n ↦ (hterm n).2.2.2.2.1
      gradient_tendsto_zero := ?_ }
  have hnn :
      Filter.Tendsto
        (fun n : ℕ ↦ (1 / ((n : ℝ≥0) + 1) : ℝ≥0))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)
  have hupper :
      Filter.Tendsto
      (fun n : ℕ ↦ ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    exact (ENNReal.tendsto_coe_toNNReal
      (a := (0 : ℝ≥0∞)) (by simp)).comp hnn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun _n ↦ bot_le)
    (fun n ↦ (hterm n).2.2.2.2.2)

/--
%%handwave
name:
  Vanishing gradients give a uniform Sobolev bound on a ball
statement:
  If the \(L^2\)-norms of a sequence are uniformly bounded on a Euclidean
  ball and the \(L^2\)-norms of its weak derivatives tend to zero there, then
  the sequence is uniformly bounded in \(W^{1,2}\) on that ball.
proof:
  The value norms are bounded by hypothesis.  Since the derivative norms tend
  to zero, they are eventually bounded by one; the finitely many earlier
  derivative norms have a finite maximum.  Adding the two finite bounds gives
  the uniform \(W^{1,2}\) bound.
-/
theorem euclideanSobolev_vanishingGradient_h1_bound_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {c : H} {r : ℝ}
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hvalue_memLp : ∀ n : ℕ, MemLp (u n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hderivative_memLp : ∀ n : ℕ, MemLp (du n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hvalue_bound :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (u n) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C)
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du n) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    BoundedInEuclideanLocalSobolevH1WithValues
      (Metric.ball c r) u du := by
  classical
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  rcases hvalue_bound with ⟨Cu, hCu_top, hCu⟩
  have hdu_eventually_lt_one :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (du n) 2 μB < (1 : ℝ≥0∞) :=
    hgradient_tendsto_zero
      (isOpen_Iio.mem_nhds (by simp))
  rcases Filter.eventually_atTop.1 hdu_eventually_lt_one with
    ⟨N, hN⟩
  let Cd : ℝ≥0∞ :=
    (Finset.range N).sup (fun n : ℕ ↦ eLpNorm (du n) 2 μB) ⊔ 1
  have hCd_top : Cd < ⊤ := by
    dsimp [Cd]
    rw [sup_lt_iff]
    constructor
    · rw [Finset.sup_lt_iff ENNReal.zero_lt_top]
      intro n _hn
      simpa [μB] using (hderivative_memLp n).2
    · exact ENNReal.one_lt_top
  have hCd_bound :
      ∀ n : ℕ, eLpNorm (du n) 2 μB ≤ Cd := by
    intro n
    by_cases hn : n < N
    · have hn_mem : n ∈ Finset.range N := Finset.mem_range.mpr hn
      exact (Finset.le_sup (s := Finset.range N)
        (f := fun n : ℕ ↦ eLpNorm (du n) 2 μB) hn_mem).trans le_sup_left
    · have hNn : N ≤ n := Nat.le_of_not_gt hn
      exact (le_of_lt (hN n hNn)).trans le_sup_right
  refine ⟨Cu + Cd, ENNReal.add_lt_top.2 ⟨hCu_top, hCd_top⟩, ?_⟩
  intro n
  refine ⟨hvalue_memLp n, hderivative_memLp n, ?_⟩
  exact add_le_add (by simpa [μB] using hCu n) (hCd_bound n)

/--
%%handwave
name:
  Standard compact subballs lie inside the open ball
statement:
  If \(r>0\), then every closed ball
  \[
    \overline B\!\left(c,r\,\frac{k+1}{k+2}\right)
  \]
  is contained in \(B(c,r)\).
proof:
  The ratio \((k+1)/(k+2)\) is strictly less than one.
-/
theorem euclideanSobolev_standard_exhaustion_closedBall_subset_ball
    {H : Type} [PseudoMetricSpace H]
    {c : H} {r : ℝ}
    (hr_pos : 0 < r) (k : ℕ) :
    Metric.closedBall c (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))) ⊆
      Metric.ball c r := by
  intro z hz
  have hz_le :
      dist z c ≤ r * (((k : ℝ) + 1) / ((k : ℝ) + 2)) := by
    simpa [Metric.mem_closedBall] using hz
  have hden_pos : 0 < (k : ℝ) + 2 := by positivity
  have hratio_lt_one :
      (((k : ℝ) + 1) / ((k : ℝ) + 2)) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hradius_lt :
      r * (((k : ℝ) + 1) / ((k : ℝ) + 2)) < r := by
    calc
      r * (((k : ℝ) + 1) / ((k : ℝ) + 2)) < r * 1 :=
        mul_lt_mul_of_pos_left hratio_lt_one hr_pos
      _ = r := by ring
  simpa [Metric.mem_ball] using lt_of_le_of_lt hz_le hradius_lt

/--
%%handwave
name:
  Bounded Sobolev functions are square-integrable on the standard compact
  subballs
statement:
  If a Sobolev sequence is uniformly \(W^{1,2}\)-bounded on \(B(c,r)\) with
  \(r>0\), then every member of the sequence is square-integrable on each
  standard compact subball
  \[
    \overline B\!\left(c,r\,\frac{k+1}{k+2}\right).
  \]
proof:
  Each standard closed subball lies inside \(B(c,r)\).  Restrict the measure
  from the ball to that closed subball and use monotonicity of \(L^2\)
  integrability under restriction.
-/
theorem euclideanSobolev_standard_exhaustion_value_memLp_of_bounded_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du) :
    ∀ k n : ℕ,
      MemLp (u n) 2
        (MeasureTheory.volume.restrict
          (Metric.closedBall c
            (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) := by
  intro k n
  have hclosed_sub_ball :
      Metric.closedBall c (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))) ⊆
        Metric.ball c r := by
    exact euclideanSobolev_standard_exhaustion_closedBall_subset_ball hr_pos k
  have hμ :
      MeasureTheory.volume.restrict
          (Metric.closedBall c
            (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))) ≤
        MeasureTheory.volume.restrict (Metric.ball c r) :=
    Measure.restrict_mono hclosed_sub_ball le_rfl
  exact
    (BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
      hbounded n).mono_measure hμ

/--
%%handwave
name:
  Compact containment on a standard compact subball
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  For each standard compact subball, the \(L^2\)-classes of a uniformly
  \(W^{1,2}(B(c,r))\)-bounded scalar weak Sobolev sequence lie in one compact
  subset of the corresponding \(L^2\) space.
proof:
  Use the next standard closed subball as the larger compact set.  The smaller
  closed ball lies in the interior of the larger one, and the larger one lies
  inside \(B(c,r)\).  Restrict the Sobolev bound to the larger compact set and
  apply Euclidean Rellich compact containment.
-/
theorem euclideanSobolev_bounded_compact_containment_on_standard_subball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    (hmem_exhaustion_all :
      ∀ k n : ℕ,
        MemLp (u n) 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))
    (k : ℕ) :
    ∃ S : Set
        (Lp ℝ 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))),
      IsCompact S ∧
        ∀ n : ℕ,
          ((hmem_exhaustion_all k n).toLp (u n) :
            Lp ℝ 2
              (MeasureTheory.volume.restrict
                (Metric.closedBall c
                  (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))) ∈ S := by
  let K : Set H :=
    Metric.closedBall c (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))
  let Q : Set H :=
    Metric.closedBall c (r * (((k : ℝ) + 2) / ((k : ℝ) + 3)))
  have hρ_lt_next :
      r * (((k : ℝ) + 1) / ((k : ℝ) + 2)) <
        r * (((k : ℝ) + 2) / ((k : ℝ) + 3)) := by
    have hden₁ : 0 < (k : ℝ) + 2 := by positivity
    have hden₂ : 0 < (k : ℝ) + 3 := by positivity
    have hratio :
        (((k : ℝ) + 1) / ((k : ℝ) + 2)) <
          (((k : ℝ) + 2) / ((k : ℝ) + 3)) := by
      rw [div_lt_div_iff₀ hden₁ hden₂]
      nlinarith
    exact mul_lt_mul_of_pos_left hratio hr_pos
  have hnext_lt_r :
      r * (((k : ℝ) + 2) / ((k : ℝ) + 3)) < r := by
    have hden : 0 < (k : ℝ) + 3 := by positivity
    have hratio :
        (((k : ℝ) + 2) / ((k : ℝ) + 3)) < 1 := by
      rw [div_lt_one hden]
      linarith
    calc
      r * (((k : ℝ) + 2) / ((k : ℝ) + 3)) < r * 1 :=
        mul_lt_mul_of_pos_left hratio hr_pos
      _ = r := by ring
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  have hK_compact : IsCompact K := by
    simpa [K] using
      (isCompact_closedBall c
        (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))
  have hQ_compact : IsCompact Q := by
    simpa [Q] using
      (isCompact_closedBall c
        (r * (((k : ℝ) + 2) / ((k : ℝ) + 3))))
  have hKQ : K ⊆ interior Q := by
    dsimp [K, Q]
    exact (Metric.closedBall_subset_ball hρ_lt_next).trans
      Metric.ball_subset_interior_closedBall
  have hQball : Q ⊆ Metric.ball c r := by
    dsimp [Q]
    exact Metric.closedBall_subset_ball hnext_lt_r
  have hboundedQ :
      BoundedInEuclideanLocalSobolevH1WithValues Q u du :=
    BoundedInEuclideanLocalSobolevH1WithValues.mono_set hQball hbounded
  let hmemK : ∀ n : ℕ,
      MemLp (u n) 2 (MeasureTheory.volume.restrict K) := by
    intro n
    simpa [K] using hmem_exhaustion_all k n
  rcases
    euclideanRellichKondrachov_compact_containment_on_compact
      (K := K) (Q := Q) (Ω := Ω)
      hK_compact hKQ (hQball.trans hballΩ) hQ_compact hΩ_open
      u du hweak hboundedQ hmemK with
    ⟨S, hS_compact, hS_mem⟩
  refine ⟨S, by simpa [K] using hS_compact, ?_⟩
  intro n
  simpa [hmemK, K] using hS_mem n

/--
%%handwave
name:
  Bounded Sobolev sequences have a diagonal Cauchy subsequence on standard
  compact subballs
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  A scalar weak Sobolev sequence uniformly bounded in \(W^{1,2}(B(c,r))\)
  has a subsequence which is Cauchy in \(L^2\) on every closed subball
  \[
    \overline B\!\left(c,r\,\frac{k+1}{k+2}\right).
  \]
proof:
  For each \(k\), apply [compact-subball Rellich compactness](lean:JJMath.Uniformization.euclideanSobolev_bounded_subsequence_on_compact_of_ball)
  to the closed ball of radius \(r(k+1)/(k+2)\), using the next closed subball
  as the larger compact set.  The resulting compact subsets of the countably
  many \(L^2\)-spaces have compact product.  A convergent subsequence in this
  product is Cauchy in every coordinate, hence on every compact subball.
-/
theorem euclideanSobolev_bounded_subsequence_cauchy_on_standard_exhaustion_of_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du) :
    ∃ (φ : ℕ → ℕ)
      (hmem_exhaustion :
        ∀ k n : ℕ,
          MemLp (u (φ n)) 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))),
      StrictMono φ ∧
        ∀ k : ℕ,
          CauchySeq
            (fun n : ℕ ↦
              ((hmem_exhaustion k n).toLp (u (φ n)) :
                Lp ℝ 2
                  (MeasureTheory.volume.restrict
                    (Metric.closedBall c
                      (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))) := by
  have hmem_exhaustion_all :
      ∀ k n : ℕ,
        MemLp (u n) 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) :=
    euclideanSobolev_standard_exhaustion_value_memLp_of_bounded_on_ball
      hr_pos hbounded
  choose S hS_compact hS_mem using
    fun k : ℕ ↦
      euclideanSobolev_bounded_compact_containment_on_standard_subball
        hr_pos hΩ_open hballΩ hweak hbounded hmem_exhaustion_all k
  let X : ℕ →
      (k : ℕ) →
        Lp ℝ 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) :=
    fun n k ↦
      ((hmem_exhaustion_all k n).toLp (u n) :
        Lp ℝ 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))
  let T : Set
      ((k : ℕ) →
        Lp ℝ 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))) :=
    Set.pi Set.univ S
  have hT_compact : IsCompact T := by
    simpa [T] using isCompact_univ_pi hS_compact
  have hX_mem : ∀ n : ℕ, X n ∈ T := by
    intro n k _hk
    simpa [X] using hS_mem k n
  rcases hT_compact.tendsto_subseq hX_mem with
    ⟨a, _haT, φ, hφ, hφ_tendsto⟩
  refine ⟨φ, fun k n ↦ hmem_exhaustion_all k (φ n), hφ, ?_⟩
  intro k
  have hk_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ X (φ n) k)
        Filter.atTop (𝓝 (a k)) :=
    (continuous_apply k).tendsto a |>.comp hφ_tendsto
  simpa [X] using hk_tendsto.cauchySeq

/--
%%handwave
name:
  Extended-real perturbation estimate
statement:
  Let \(\delta\ge0\), let \(x\le C<\infty\), and suppose
  \(\delta C_{\mathbb R}\le\varepsilon\). Then
  \[\operatorname{ofReal}(1+\delta)x
    \le x+\operatorname{ofReal}(\varepsilon).\]
proof:
  Since \(x\) is finite, expand the left side as
  \(x+\operatorname{ofReal}(\delta)x\), bound \(x_{\mathbb R}\) by
  \(C_{\mathbb R}\), and apply the hypothesis.
-/
private theorem ennreal_ofReal_one_add_mul_le_add_of_le
    {δ ε : ℝ} {x C : ℝ≥0∞}
    (hδ_nonneg : 0 ≤ δ)
    (hC_ne_top : C ≠ ⊤)
    (hxC : x ≤ C)
    (hδC : δ * C.toReal ≤ ε) :
    ENNReal.ofReal (1 + δ) * x ≤ x + ENNReal.ofReal ε := by
  have hx_ne_top : x ≠ ⊤ := ne_top_of_le_ne_top hC_ne_top hxC
  have hxC_real : x.toReal ≤ C.toReal :=
    ENNReal.toReal_mono hC_ne_top hxC
  have hδx_le : δ * x.toReal ≤ ε :=
    (mul_le_mul_of_nonneg_left hxC_real hδ_nonneg).trans hδC
  have hδx :
      ENNReal.ofReal δ * x ≤ ENNReal.ofReal ε := by
    calc
      ENNReal.ofReal δ * x
          = ENNReal.ofReal δ * ENNReal.ofReal x.toReal := by
              rw [ENNReal.ofReal_toReal hx_ne_top]
      _ = ENNReal.ofReal (δ * x.toReal) := by
              rw [ENNReal.ofReal_mul hδ_nonneg]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hδx_le
  calc
    ENNReal.ofReal (1 + δ) * x
        = x + ENNReal.ofReal δ * x := by
            rw [ENNReal.ofReal_add zero_le_one hδ_nonneg, ENNReal.ofReal_one,
              add_mul, one_mul]
    _ ≤ x + ENNReal.ofReal ε := add_le_add_right hδx x

/--
%%handwave
name:
  The standard radial Jacobian factors tend to one
statement:
  For every \(\delta>0\), some standard exhaustion factor has \(L^2\) Jacobian
  loss at most \(1+\delta\):
  \[
    \left(\left(\frac{k+2}{k+1}\right)^{\dim H}\right)^{1/2}
      \le 1+\delta .
  \]
proof:
  The ratios \((k+2)/(k+1)\) tend to \(1\), so their fixed finite powers and
  square roots also tend to \(1\).
-/
theorem euclideanSobolev_standard_exhaustion_radial_contraction_jacobianFactor_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] :
    ∀ δ : ℝ, 0 < δ →
      ∃ k : ℕ,
        (ENNReal.ofReal
          ((((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ Module.finrank ℝ H)) ^
            ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal ≤
          ENNReal.ofReal (1 + δ) := by
  intro δ hδ
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hrecip :
      Filter.Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsum :
      Filter.Tendsto (fun k : ℕ ↦ (1 : ℝ) + (1 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hrecip)
  have hratio :
      Filter.Tendsto (fun k : ℕ ↦ (((k : ℝ) + 2) / ((k : ℝ) + 1)))
        Filter.atTop (𝓝 1) := by
    refine hsum.congr' ?_
    filter_upwards with k
    have hden : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hden]
    ring
  have hpow_real :
      Filter.Tendsto
        (fun k : ℕ ↦ (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ Module.finrank ℝ H)
        Filter.atTop (𝓝 1) := by
    simpa using hratio.pow (Module.finrank ℝ H)
  have hofReal :
      Filter.Tendsto
        (fun k : ℕ ↦ ENNReal.ofReal
          ((((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ Module.finrank ℝ H))
        Filter.atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hpow_real
  have hfactor :
      Filter.Tendsto
        (fun k : ℕ ↦
          (ENNReal.ofReal
            ((((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ Module.finrank ℝ H)) ^ q)
        Filter.atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa [q, ENNReal.one_rpow] using
      (Filter.Tendsto.ennrpow_const q hofReal)
  have htarget : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + δ) := by
    rw [ENNReal.one_lt_ofReal]
    linarith
  have heventually := hfactor.eventually (eventually_le_nhds htarget)
  rcases Filter.eventually_atTop.1 heventually with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa [q] using hk k le_rfl

/--
%%handwave
name:
  Pullback by a standard radial contraction has the Jacobian \(L^2\)-factor
statement:
  Pulling a function on the standard closed subball back to \(B(c,r)\) by the
  homothety \(z\mapsto c+\frac{k+1}{k+2}(z-c)\) multiplies its \(L^2\)-norm by
  at most
  \[
    \left(\left(\frac{k+2}{k+1}\right)^{\dim H}\right)^{1/2}.
  \]
proof:
  The homothety maps \(B(c,r)\) into the standard closed subball.  The
  push-forward of Haar measure under this homothety is the Haar measure on the
  image, scaled by the inverse Jacobian, and monotonicity compares the image
  ball with the closed subball.
-/
theorem euclideanSobolev_standard_exhaustion_radial_contraction_pullback_eLpNorm_le_of_jacobianFactor
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r : ℝ}
    (_hr_pos : 0 < r) (k : ℕ) :
    ∀ {w : H → ℝ},
      MemLp w 2
        (MeasureTheory.volume.restrict
          (Metric.closedBall c
            (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) →
      AEStronglyMeasurable
        (fun z : H ↦
          w (c + (((k : ℝ) + 1) / ((k : ℝ) + 2)) • (z - c)))
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      eLpNorm
        (fun z : H ↦
          w (c + (((k : ℝ) + 1) / ((k : ℝ) + 2)) • (z - c))) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
        (ENNReal.ofReal
          ((((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ Module.finrank ℝ H)) ^
            ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
          eLpNorm w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) := by
  intro w hw
  let a : ℝ := ((k : ℝ) + 1) / ((k : ℝ) + 2)
  let T : H → H := fun z ↦ c + a • (z - c)
  let B : Set H := Metric.ball c r
  let K : Set H := Metric.closedBall c (r * a)
  let J : ℝ≥0∞ :=
    ENNReal.ofReal ((((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ Module.finrank ℝ H)
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hJ_real :
      |(a ^ Module.finrank ℝ H)⁻¹| =
        (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ Module.finrank ℝ H := by
    have ha_inv : a⁻¹ = (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by
      dsimp [a]
      have hden1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hden2 : ((k : ℝ) + 2) ≠ 0 := by positivity
      field_simp [hden1, hden2]
    rw [← inv_pow, ha_inv]
    rw [abs_of_nonneg]
    positivity
  have hT_meas : Measurable T := by
    dsimp [T]
    measurability
  have hT_aemeas : AEMeasurable T (MeasureTheory.volume.restrict B) :=
    hT_meas.aemeasurable
  have hT_emb : MeasurableEmbedding T := by
    let f₁ : H → H := fun z ↦ -c + z
    let f₂ : H → H := fun z ↦ a • z
    let f₃ : H → H := fun z ↦ c + z
    have hT : T = f₃ ∘ f₂ ∘ f₁ := by
      funext z
      simp [T, f₁, f₂, f₃, sub_eq_add_neg, add_comm]
    rw [hT]
    exact (measurableEmbedding_addLeft c).comp
      ((measurableEmbedding_const_smul₀ (α := H) ha_ne).comp
        (measurableEmbedding_addLeft (-c)))
  have hT_image_subset : T '' B ⊆ K := by
    intro y hy
    rcases hy with ⟨z, hzB, rfl⟩
    dsimp [B, K, T]
    rw [Metric.mem_closedBall]
    have hzdist : dist z c < r := by
      simpa [B, Metric.mem_ball] using hzB
    have hsub : (c + a • (z - c)) - c = a • (z - c) := by abel
    calc
      dist (c + a • (z - c)) c = ‖a • (z - c)‖ := by
        rw [dist_eq_norm, hsub]
      _ = a * ‖z - c‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha_pos.le]
      _ = a * dist z c := by rw [dist_eq_norm]
      _ ≤ a * r := mul_le_mul_of_nonneg_left hzdist.le ha_pos.le
      _ = r * a := by ring
  have hmap_volume :
      Measure.map T MeasureTheory.volume = J • MeasureTheory.volume := by
    let f₁ : H → H := fun z ↦ -c + z
    let f₂ : H → H := fun z ↦ a • z
    let f₃ : H → H := fun z ↦ c + z
    have hT : T = f₃ ∘ f₂ ∘ f₁ := by
      funext z
      simp [T, f₁, f₂, f₃, sub_eq_add_neg, add_comm]
    rw [hT]
    calc
      Measure.map (f₃ ∘ f₂ ∘ f₁) MeasureTheory.volume
          = Measure.map f₃ (Measure.map f₂ (Measure.map f₁ MeasureTheory.volume)) := by
              rw [Measure.map_map, Measure.map_map]
              · rfl
              all_goals measurability
      _ = Measure.map f₃ (Measure.map f₂ MeasureTheory.volume) := by
              rw [show Measure.map f₁ MeasureTheory.volume = MeasureTheory.volume by
                simpa [f₁] using
                  MeasureTheory.map_add_left_eq_self
                    (MeasureTheory.volume : Measure H) (-c)]
      _ = Measure.map f₃ (J • MeasureTheory.volume) := by
              rw [show Measure.map f₂ MeasureTheory.volume = J • MeasureTheory.volume by
                calc
                  Measure.map f₂ MeasureTheory.volume
                      = ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹| •
                          MeasureTheory.volume := by
                          simpa [f₂] using
                            MeasureTheory.Measure.map_addHaar_smul
                              (MeasureTheory.volume : Measure H) ha_ne
                  _ = J • MeasureTheory.volume := by
                          simp [J, hJ_real]]
      _ = J • Measure.map f₃ MeasureTheory.volume := by
              rw [Measure.map_smul]
      _ = J • MeasureTheory.volume := by
              rw [show Measure.map f₃ MeasureTheory.volume = MeasureTheory.volume by
                simpa [f₃] using
                  MeasureTheory.map_add_left_eq_self
                    (MeasureTheory.volume : Measure H) c]
  have hmap_restrict_eq :
      Measure.map T (MeasureTheory.volume.restrict B) =
        (Measure.map T MeasureTheory.volume).restrict (T '' B) := by
    have hrestrict := hT_emb.restrict_map (MeasureTheory.volume : Measure H) (T '' B)
    have hpre : T ⁻¹' (T '' B) = B := hT_emb.injective.preimage_image B
    rw [hpre] at hrestrict
    exact hrestrict.symm
  have hmap_le :
      Measure.map T (MeasureTheory.volume.restrict B) ≤
        J • MeasureTheory.volume.restrict K := by
    calc
      Measure.map T (MeasureTheory.volume.restrict B)
          = (Measure.map T MeasureTheory.volume).restrict (T '' B) := hmap_restrict_eq
      _ = (J • MeasureTheory.volume).restrict (T '' B) := by rw [hmap_volume]
      _ ≤ (J • MeasureTheory.volume).restrict K :=
            Measure.restrict_mono hT_image_subset le_rfl
      _ = J • MeasureTheory.volume.restrict K := by rw [Measure.restrict_smul]
  have hJ_ne_top : J ≠ ⊤ := by
    simp [J]
  have hJ_ne_zero : J ≠ 0 := by
    dsimp [J]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hwK : MemLp w 2 (MeasureTheory.volume.restrict K) := by
    simpa [K, a] using hw
  have hw_map : MemLp w 2 (Measure.map T (MeasureTheory.volume.restrict B)) :=
    hwK.of_measure_le_smul hJ_ne_top hmap_le
  have hcomp_mem : MemLp (fun z : H ↦ w (T z)) 2
      (MeasureTheory.volume.restrict B) := by
    simpa [Function.comp_def] using hw_map.comp_of_map hT_aemeas
  refine ⟨?_, ?_⟩
  · simpa [T, B, a] using hcomp_mem.aestronglyMeasurable
  · calc
      eLpNorm
          (fun z : H ↦
            w (c + (((k : ℝ) + 1) / ((k : ℝ) + 2)) • (z - c))) 2
          (MeasureTheory.volume.restrict (Metric.ball c r))
          = eLpNorm (fun z : H ↦ w (T z)) 2
              (MeasureTheory.volume.restrict B) := by
              simp [T, B, a]
      _ = eLpNorm w 2 (Measure.map T (MeasureTheory.volume.restrict B)) := by
              exact (eLpNorm_map_measure hw_map.aestronglyMeasurable hT_aemeas).symm
      _ ≤ eLpNorm w 2 (J • MeasureTheory.volume.restrict K) :=
              eLpNorm_mono_measure w hmap_le
      _ = J ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
            eLpNorm w 2 (MeasureTheory.volume.restrict K) := by
              rw [eLpNorm_smul_measure_of_ne_zero hJ_ne_zero, smul_eq_mul]
      _ = (ENNReal.ofReal
            ((((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ Module.finrank ℝ H)) ^
              ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
            eLpNorm w 2
              (MeasureTheory.volume.restrict
                (Metric.closedBall c
                  (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) := by
              simp [J, K, a]

/--
%%handwave
name:
  Radial contraction has arbitrarily small \(L^2\) Jacobian loss
statement:
  Given \(\delta>0\), one can choose a standard compact subball so close to
  \(B(c,r)\) that pulling a function back by the radial contraction of
  \(B(c,r)\) onto that subball increases its \(L^2\)-norm by at most the
  factor \(1+\delta\).
proof:
  The radial contraction is an affine homothety centered at \(c\).  Its
  Jacobian tends to one as the contraction factor tends to one, and the
  standard exhaustion factors tend to one.
-/
theorem euclideanSobolev_standard_exhaustion_radial_contraction_pullback_eLpNorm_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r : ℝ}
    (hr_pos : 0 < r) :
    ∀ δ : ℝ, 0 < δ →
      ∃ k : ℕ,
        ∀ {w : H → ℝ},
          MemLp w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) →
          AEStronglyMeasurable
            (fun z : H ↦
              w (c + (((k : ℝ) + 1) / ((k : ℝ) + 2)) • (z - c)))
            (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
          eLpNorm
            (fun z : H ↦
              w (c + (((k : ℝ) + 1) / ((k : ℝ) + 2)) • (z - c))) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            ENNReal.ofReal (1 + δ) *
              eLpNorm w 2
                (MeasureTheory.volume.restrict
                  (Metric.closedBall c
                    (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) := by
  intro δ hδ
  rcases
    euclideanSobolev_standard_exhaustion_radial_contraction_jacobianFactor_le
      (H := H) δ hδ with
    ⟨k, hJ_le⟩
  refine ⟨k, ?_⟩
  intro w hwK
  rcases
    euclideanSobolev_standard_exhaustion_radial_contraction_pullback_eLpNorm_le_of_jacobianFactor
      (H := H) (c := c) (r := r) hr_pos k hwK with
    ⟨hmeas, hnorm⟩
  refine ⟨hmeas, hnorm.trans ?_⟩
  exact mul_le_mul' hJ_le le_rfl

/--
%%handwave
name:
  Radial gradient segment integral
statement:
  The radial gradient segment integral between \(z\) and \(c+a(z-c)\) is the
  integral over the straight segment from \(c+a(z-c)\) to \(z\) of the absolute
  value of the weak derivative applied to the segment velocity.
-/
noncomputable def euclideanRadialContractionGradientSegmentIntegral {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (dw : H → H →L[ℝ] ℝ) (c : H) (a : ℝ) (z : H) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1,
    ‖dw (c + (a + t * (1 - a)) • (z - c)) ((1 - a) • (z - c))‖
      ∂MeasureTheory.volume

/--
%%handwave
name:
  Radial homotheties have bounded inverse Jacobian on a ball
statement:
  If \(0<s\le1\), then the radial homothety
  \(z\mapsto c+s(z-c)\) sends \(B(c,r)\) into itself, and the push-forward of
  volume restricted to \(B(c,r)\) is bounded by the inverse-Jacobian multiple
  \(s^{-\dim H}\) of volume restricted to \(B(c,r)\).
proof:
  The map is the composition of a translation, the linear scaling
  \(z\mapsto sz\), and a translation back.  Translations preserve Haar measure,
  while the linear scaling multiplies Haar measure by the inverse absolute
  determinant.  Since \(0<s\le1\), the ball is mapped into itself, so
  restricting gives the stated inequality.
-/
theorem euclideanRadialHomothety_map_restrict_ball_le_smul
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r s : ℝ}
    (hs_pos : 0 < s)
    (hs_le_one : s ≤ 1) :
    Measure.map (fun z : H ↦ c + s • (z - c))
        (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
      ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| •
        MeasureTheory.volume.restrict (Metric.ball c r) := by
  let T : H → H := fun z ↦ c + s • (z - c)
  let B : Set H := Metric.ball c r
  let J : ℝ≥0∞ := ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹|
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hT_meas : Measurable T := by
    dsimp [T]
    measurability
  have hT_emb : MeasurableEmbedding T := by
    let f₁ : H → H := fun z ↦ -c + z
    let f₂ : H → H := fun z ↦ s • z
    let f₃ : H → H := fun z ↦ c + z
    have hT : T = f₃ ∘ f₂ ∘ f₁ := by
      funext z
      simp [T, f₁, f₂, f₃, sub_eq_add_neg, add_comm]
    rw [hT]
    exact (measurableEmbedding_addLeft c).comp
      ((measurableEmbedding_const_smul₀ (α := H) hs_ne).comp
        (measurableEmbedding_addLeft (-c)))
  have hT_image_subset : T '' B ⊆ B := by
    intro y hy
    rcases hy with ⟨z, hzB, rfl⟩
    dsimp [B, T]
    rw [Metric.mem_ball]
    have hzdist : dist z c < r := by
      simpa [B, Metric.mem_ball] using hzB
    have hsub : (c + s • (z - c)) - c = s • (z - c) := by abel
    calc
      dist (c + s • (z - c)) c = ‖s • (z - c)‖ := by
        rw [dist_eq_norm, hsub]
      _ = s * ‖z - c‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_pos.le]
      _ = s * dist z c := by rw [dist_eq_norm]
      _ ≤ 1 * dist z c :=
        mul_le_mul_of_nonneg_right hs_le_one dist_nonneg
      _ < r := by simpa using hzdist
  have hmap_volume :
      Measure.map T MeasureTheory.volume = J • MeasureTheory.volume := by
    let f₁ : H → H := fun z ↦ -c + z
    let f₂ : H → H := fun z ↦ s • z
    let f₃ : H → H := fun z ↦ c + z
    have hT : T = f₃ ∘ f₂ ∘ f₁ := by
      funext z
      simp [T, f₁, f₂, f₃, sub_eq_add_neg, add_comm]
    rw [hT]
    calc
      Measure.map (f₃ ∘ f₂ ∘ f₁) MeasureTheory.volume
          = Measure.map f₃ (Measure.map f₂ (Measure.map f₁ MeasureTheory.volume)) := by
              rw [Measure.map_map, Measure.map_map]
              · rfl
              all_goals measurability
      _ = Measure.map f₃ (Measure.map f₂ MeasureTheory.volume) := by
              rw [show Measure.map f₁ MeasureTheory.volume = MeasureTheory.volume by
                simpa [f₁] using
                  MeasureTheory.map_add_left_eq_self
                    (MeasureTheory.volume : Measure H) (-c)]
      _ = Measure.map f₃ (J • MeasureTheory.volume) := by
              rw [show Measure.map f₂ MeasureTheory.volume = J • MeasureTheory.volume by
                simpa [f₂, J] using
                  MeasureTheory.Measure.map_addHaar_smul
                    (MeasureTheory.volume : Measure H) hs_ne]
      _ = J • Measure.map f₃ MeasureTheory.volume := by
              rw [Measure.map_smul]
      _ = J • MeasureTheory.volume := by
              rw [show Measure.map f₃ MeasureTheory.volume = MeasureTheory.volume by
                simpa [f₃] using
                  MeasureTheory.map_add_left_eq_self
                    (MeasureTheory.volume : Measure H) c]
  have hmap_restrict_eq :
      Measure.map T (MeasureTheory.volume.restrict B) =
        (Measure.map T MeasureTheory.volume).restrict (T '' B) := by
    have hrestrict := hT_emb.restrict_map (MeasureTheory.volume : Measure H) (T '' B)
    have hpre : T ⁻¹' (T '' B) = B := hT_emb.injective.preimage_image B
    rw [hpre] at hrestrict
    exact hrestrict.symm
  calc
    Measure.map (fun z : H ↦ c + s • (z - c))
        (MeasureTheory.volume.restrict (Metric.ball c r))
        = Measure.map T (MeasureTheory.volume.restrict B) := by simp [T, B]
    _ = (Measure.map T MeasureTheory.volume).restrict (T '' B) := hmap_restrict_eq
    _ = (J • MeasureTheory.volume).restrict (T '' B) := by rw [hmap_volume]
    _ ≤ (J • MeasureTheory.volume).restrict B :=
          Measure.restrict_mono hT_image_subset le_rfl
    _ = J • MeasureTheory.volume.restrict B := by rw [Measure.restrict_smul]
    _ = ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| •
        MeasureTheory.volume.restrict (Metric.ball c r) := by
          simp [J, B]

/--
%%handwave
name:
  Pulling a nonnegative function back by a radial homothety
statement:
  If \(0<s\le1\), then pulling a nonnegative measurable function back from
  \(B(c,r)\) along \(z\mapsto c+s(z-c)\) increases its integral over the ball
  by at most the inverse-Jacobian factor \(s^{-\dim H}\).
proof:
  This is the preceding push-forward measure inequality, written in integral
  form.
-/
theorem euclideanRadialHomothety_lintegral_comp_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r s : ℝ}
    (hs_pos : 0 < s)
    (hs_le_one : s ≤ 1)
    {F : H → ℝ≥0∞}
    (hF : AEMeasurable F (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∫⁻ z in Metric.ball c r, F (c + s • (z - c)) ∂MeasureTheory.volume ≤
      ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| *
        ∫⁻ z in Metric.ball c r, F z ∂MeasureTheory.volume := by
  let T : H → H := fun z ↦ c + s • (z - c)
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let J : ℝ≥0∞ := ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹|
  have hT_meas : Measurable T := by
    dsimp [T]
    measurability
  have hT_aemeas : AEMeasurable T μB := hT_meas.aemeasurable
  have hmap_le : Measure.map T μB ≤ J • μB := by
    simpa [T, μB, J] using
      euclideanRadialHomothety_map_restrict_ball_le_smul
        (H := H) (c := c) (r := r) (s := s) hs_pos hs_le_one
  have hmap_ac : Measure.map T μB ≪ μB :=
    Measure.absolutelyContinuous_of_le_smul hmap_le
  have hF_map : AEMeasurable F (Measure.map T μB) :=
    hF.mono_ac hmap_ac
  calc
    ∫⁻ z in Metric.ball c r, F (c + s • (z - c)) ∂MeasureTheory.volume
        = ∫⁻ z, F (T z) ∂μB := by simp [T, μB]
    _ = ∫⁻ y, F y ∂Measure.map T μB :=
          (lintegral_map' hF_map hT_aemeas).symm
    _ ≤ ∫⁻ y, F y ∂J • μB :=
          lintegral_mono' hmap_le le_rfl
    _ = J * ∫⁻ y, F y ∂μB := by
          rw [lintegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| *
        ∫⁻ z in Metric.ball c r, F z ∂MeasureTheory.volume := by
          simp [J, μB]

/--
%%handwave
name:
  Radial homotheties are null-set preserving on a ball
statement:
  If \(0<s\le1\), then the radial homothety
  \(z\mapsto c+s(z-c)\) is null-set preserving from \(B(c,r)\), with
  restricted volume, to itself.
proof:
  The push-forward measure is bounded by a finite multiple of restricted
  volume on the ball.
-/
theorem euclideanRadialHomothety_quasiMeasurePreserving_restrict_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r s : ℝ}
    (hs_pos : 0 < s)
    (hs_le_one : s ≤ 1) :
    Measure.QuasiMeasurePreserving
      (fun z : H ↦ c + s • (z - c))
      (MeasureTheory.volume.restrict (Metric.ball c r))
      (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  refine ⟨?_, ?_⟩
  · measurability
  · exact Measure.absolutelyContinuous_of_le_smul
      (euclideanRadialHomothety_map_restrict_ball_le_smul
        (H := H) (c := c) (r := r) (s := s) hs_pos hs_le_one)

/--
%%handwave
name:
  Pullback by a radial homothety has the \(L^2\) Jacobian bound
statement:
  If \(0<s\le1\), then pulling an \(L^2\) function on \(B(c,r)\) back by the
  radial homothety \(z\mapsto c+s(z-c)\) multiplies its \(L^2\)-norm by at
  most the square root of the inverse Jacobian \(s^{-\dim H}\).
proof:
  Rewrite the pullback norm as the norm with respect to the push-forward
  measure.  The push-forward measure is bounded by the inverse-Jacobian
  multiple of restricted volume, and \(L^2\)-norms are monotone in the
  measure.  Finally use the formula for scaling a measure by a constant.
-/
theorem euclideanRadialHomothety_eLpNorm_comp_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r s : ℝ}
    (hs_pos : 0 < s)
    (hs_le_one : s ≤ 1)
    {f : H → ℝ}
    (hf : AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Metric.ball c r))) :
    eLpNorm (fun z : H ↦ f (c + s • (z - c))) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
      (ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹|) ^
          ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  let T : H → H := fun z ↦ c + s • (z - c)
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let J : ℝ≥0∞ := ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹|
  have hT_meas : Measurable T := by
    dsimp [T]
    measurability
  have hT_aemeas : AEMeasurable T μB := hT_meas.aemeasurable
  have hmap_le : Measure.map T μB ≤ J • μB := by
    simpa [T, μB, J] using
      euclideanRadialHomothety_map_restrict_ball_le_smul
        (H := H) (c := c) (r := r) (s := s) hs_pos hs_le_one
  have hmap_ac : Measure.map T μB ≪ μB :=
    Measure.absolutelyContinuous_of_le_smul hmap_le
  have hf_map : AEStronglyMeasurable f (Measure.map T μB) :=
    hf.mono_ac hmap_ac
  have hJ_ne_zero : J ≠ 0 := by
    dsimp [J]
    exact ne_of_gt
      (ENNReal.ofReal_pos.mpr
        (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ (ne_of_gt hs_pos)))))
  calc
    eLpNorm (fun z : H ↦ f (c + s • (z - c))) 2
        (MeasureTheory.volume.restrict (Metric.ball c r))
        = eLpNorm (fun z : H ↦ f (T z)) 2 μB := by
            simp [T, μB]
    _ = eLpNorm f 2 (Measure.map T μB) := by
            exact (eLpNorm_map_measure hf_map hT_aemeas).symm
    _ ≤ eLpNorm f 2 (J • μB) :=
            eLpNorm_mono_measure f hmap_le
    _ = J ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
          eLpNorm f 2 μB := by
            rw [eLpNorm_smul_measure_of_ne_zero hJ_ne_zero, smul_eq_mul]
    _ =
      (ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹|) ^
          ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) := by
        simp [J, μB]

/--
%%handwave
name:
  Square of an integral on a probability space
statement:
  If \(\mu(X)=1\) and \(g\) is strongly measurable, then
  \[\left\lVert\int_Xg\,d\mu\right\rVert_{\!e}^{\,2}
    \le\int_X\lVert g\rVert_{\!e}^{\,2}\,d\mu.\]
proof:
  Bound the norm of the integral by the integral of the norm and apply
  Hölder with exponents \(2,2\), using \(\lVert1\rVert_{L^2(\mu)}=1\).
-/
private theorem poincare_enorm_integral_sq_le_lintegral_enorm_sq_of_measure_univ_eq_one
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
  Radial gradient segment integrals satisfy the square estimate
statement:
  For \(r>0\) and \(0<a\le1\), the square integral over \(B(c,r)\) of the
  radial gradient segment integral is bounded by
  \[
    ((1-a)r)^2\,a^{-\dim H}
      \int_{B(c,r)} |D w|^2 .
  \]
proof:
  Apply Cauchy--Schwarz on the unit segment parameter, then use Tonelli to
  swap the \(z\)- and \(t\)-integrals.  For a fixed \(t\), the intermediate
  map \(z\mapsto c+(a+t(1-a))(z-c)\) is a radial homothety of ratio between
  \(a\) and \(1\), hence its inverse-Jacobian is at most \(a^{-\dim H}\).  The
  segment velocity has length at most \((1-a)r\).
-/
theorem euclideanRadialContractionGradientSegmentIntegral_lintegral_sq_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    {dw : H → H →L[ℝ] ℝ}
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∫⁻ z in Metric.ball c r,
        ‖euclideanRadialContractionGradientSegmentIntegral dw c a z‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume ≤
      (ENNReal.ofReal (((1 - a) * r) ^ 2) *
          ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|) *
        ∫⁻ z in Metric.ball c r, ‖dw z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
  let B : Set H := Metric.ball c r
  let μB : Measure H := MeasureTheory.volume.restrict B
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  let C : ℝ := (1 - a) * r
  let J : ℝ≥0∞ := ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|
  let F : H → ℝ≥0∞ := fun y ↦ ‖dw y‖ₑ ^ (2 : ℝ)
  let T : H × ℝ → H := fun p ↦ c + (a + p.2 * (1 - a)) • (p.1 - c)
  let V : H × ℝ → H := fun p ↦ (1 - a) • (p.1 - c)
  let G : H × ℝ → ℝ := fun p ↦ ‖dw (T p) (V p)‖
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (sub_nonneg.mpr ha_le_one) hr_pos.le
  have hF_ae : AEMeasurable F μB := by
    exact hdw.aestronglyMeasurable.enorm.pow_const _
  have hμI_univ : μI Set.univ = 1 := by
    simp [μI, Real.volume_Icc]
  have hT_qmp :
      Measure.QuasiMeasurePreserving T (μB.prod μI) μB := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_left
      (τ := μB) ?_ ?_
    · dsimp [T]
      fun_prop
    · filter_upwards [ae_restrict_mem
        (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))] with t ht
      let s : ℝ := a + t * (1 - a)
      have h1a_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha_le_one
      have hs_pos : 0 < s := by
        dsimp [s]
        have ht_nonneg : 0 ≤ t := ht.1
        have hprod_nonneg : 0 ≤ t * (1 - a) :=
          mul_nonneg ht_nonneg h1a_nonneg
        linarith
      have hs_le_one : s ≤ 1 := by
        dsimp [s]
        have ht_le_one : t ≤ 1 := ht.2
        have hprod_le : t * (1 - a) ≤ 1 * (1 - a) :=
          mul_le_mul_of_nonneg_right ht_le_one h1a_nonneg
        linarith
      simpa [T, s] using
        euclideanRadialHomothety_quasiMeasurePreserving_restrict_ball
          (H := H) (c := c) (r := r) (s := s) hs_pos hs_le_one
  have hdw_comp :
      AEStronglyMeasurable (fun p : H × ℝ ↦ dw (T p)) (μB.prod μI) := by
    simpa [Function.comp_def] using
      hdw.aestronglyMeasurable.comp_quasiMeasurePreserving hT_qmp
  have hV_cont : Continuous V := by
    dsimp [V]
    fun_prop
  have hV_ae : AEStronglyMeasurable V (μB.prod μI) :=
    hV_cont.aestronglyMeasurable
  have hEval_cont :
      Continuous (fun q : (H →L[ℝ] ℝ) × H ↦ q.1 q.2) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := H) (F := ℝ)).continuous
  have hApply_ae :
      AEStronglyMeasurable (fun p : H × ℝ ↦ dw (T p) (V p)) (μB.prod μI) :=
    hEval_cont.comp_aestronglyMeasurable (hdw_comp.prodMk hV_ae)
  have hG_ae : AEStronglyMeasurable G (μB.prod μI) := by
    simpa [G] using hApply_ae.norm
  have hGsq_ae :
      AEMeasurable (fun p : H × ℝ ↦ ‖G p‖ₑ ^ (2 : ℝ)) (μB.prod μI) :=
    hG_ae.enorm.pow_const _
  have hslices :
      ∀ᵐ z ∂μB, AEStronglyMeasurable (fun t : ℝ ↦ G (z, t)) μI :=
    hG_ae.prodMk_left
  have hpoint :
      ∀ᵐ z ∂μB,
        ‖∫ t, G (z, t) ∂μI‖ₑ ^ (2 : ℝ) ≤
          ∫⁻ t, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μI := by
    filter_upwards [hslices] with z hz
    exact
      poincare_enorm_integral_sq_le_lintegral_enorm_sq_of_measure_univ_eq_one
        hμI_univ hz
  have hslice_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∫⁻ z, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μB ≤
          (ENNReal.ofReal (C ^ 2) * J) *
            ∫⁻ z, F z ∂μB := by
    intro t ht
    let s : ℝ := a + t * (1 - a)
    have h1a_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha_le_one
    have ht_nonneg : 0 ≤ t := ht.1
    have ht_le_one : t ≤ 1 := ht.2
    have hs_pos : 0 < s := by
      dsimp [s]
      have hprod_nonneg : 0 ≤ t * (1 - a) :=
        mul_nonneg ht_nonneg h1a_nonneg
      linarith
    have hs_le_one : s ≤ 1 := by
      dsimp [s]
      have hprod_le : t * (1 - a) ≤ 1 * (1 - a) :=
        mul_le_mul_of_nonneg_right ht_le_one h1a_nonneg
      linarith
    have ha_le_s : a ≤ s := by
      dsimp [s]
      have hprod_nonneg : 0 ≤ t * (1 - a) :=
        mul_nonneg ht_nonneg h1a_nonneg
      linarith
    have hJs_le :
        ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| ≤ J := by
      have hinv_le : (s ^ Module.finrank ℝ H)⁻¹ ≤
          (a ^ Module.finrank ℝ H)⁻¹ := by
        have hpow : a ^ Module.finrank ℝ H ≤ s ^ Module.finrank ℝ H :=
          pow_le_pow_left₀ ha_pos.le ha_le_s _
        exact inv_anti₀ (pow_pos ha_pos _) hpow
      have hs_inv_nonneg : 0 ≤ (s ^ Module.finrank ℝ H)⁻¹ := by positivity
      have ha_inv_nonneg : 0 ≤ (a ^ Module.finrank ℝ H)⁻¹ := by positivity
      dsimp [J]
      rw [abs_of_nonneg hs_inv_nonneg, abs_of_nonneg ha_inv_nonneg]
      exact ENNReal.ofReal_le_ofReal hinv_le
    have hpoint_slice :
        ∀ᵐ z ∂μB,
          ‖G (z, t)‖ₑ ^ (2 : ℝ) ≤
            ENNReal.ofReal (C ^ 2) * F (c + s • (z - c)) := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hzB
      have hzdist : dist z c < r := by
        simpa [B, Metric.mem_ball] using hzB
      have hzc_norm : ‖z - c‖ ≤ r := by
        rw [← dist_eq_norm]
        exact hzdist.le
      have hvel_norm : ‖(1 - a) • (z - c)‖ ≤ C := by
        calc
          ‖(1 - a) • (z - c)‖ = (1 - a) * ‖z - c‖ := by
            simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg h1a_nonneg]
          _ ≤ (1 - a) * r :=
            mul_le_mul_of_nonneg_left hzc_norm h1a_nonneg
          _ = C := by simp [C]
      have h_apply_norm :
          ‖dw (c + s • (z - c)) ((1 - a) • (z - c))‖ ≤
            C * ‖dw (c + s • (z - c))‖ := by
        calc
          ‖dw (c + s • (z - c)) ((1 - a) • (z - c))‖
              ≤ ‖dw (c + s • (z - c))‖ * ‖(1 - a) • (z - c)‖ :=
                (dw (c + s • (z - c))).le_opNorm ((1 - a) • (z - c))
          _ ≤ ‖dw (c + s • (z - c))‖ * C :=
                mul_le_mul_of_nonneg_left hvel_norm
                  (norm_nonneg (dw (c + s • (z - c))))
          _ = C * ‖dw (c + s • (z - c))‖ := by ring
      have h_apply_abs :
          |dw (c + s • (z - c)) ((1 - a) • (z - c))| ≤
            C * ‖dw (c + s • (z - c))‖ := by
        simpa [Real.norm_eq_abs] using h_apply_norm
      have hsq_real :
          (G (z, t)) ^ 2 ≤ C ^ 2 * ‖dw (c + s • (z - c))‖ ^ 2 := by
        dsimp [G, T, V, s]
        nlinarith [h_apply_abs, abs_nonneg
          (dw (c + s • (z - c)) ((1 - a) • (z - c))),
          norm_nonneg (dw (c + s • (z - c))), hC_nonneg]
      have hG_nonneg : 0 ≤ G (z, t) := by
        change 0 ≤ ‖dw (T (z, t)) (V (z, t))‖
        exact norm_nonneg (dw (T (z, t)) (V (z, t)))
      calc
        ‖G (z, t)‖ₑ ^ (2 : ℝ)
            = ENNReal.ofReal ((G (z, t)) ^ 2) := by
                simp [Real.enorm_eq_ofReal, hG_nonneg]
        _ ≤ ENNReal.ofReal (C ^ 2 * ‖dw (c + s • (z - c))‖ ^ 2) :=
              ENNReal.ofReal_le_ofReal hsq_real
        _ = ENNReal.ofReal (C ^ 2) *
              ENNReal.ofReal (‖dw (c + s • (z - c))‖ ^ 2) := by
              rw [ENNReal.ofReal_mul]
              positivity
        _ = ENNReal.ofReal (C ^ 2) * F (c + s • (z - c)) := by
              simp [F]
    have hcomp :
        ∫⁻ z in Metric.ball c r, F (c + s • (z - c)) ∂MeasureTheory.volume ≤
          ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| *
            ∫⁻ z in Metric.ball c r, F z ∂MeasureTheory.volume :=
      euclideanRadialHomothety_lintegral_comp_le
        (H := H) (c := c) (r := r) (s := s) hs_pos hs_le_one hF_ae
    calc
      ∫⁻ z, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μB
          ≤ ∫⁻ z, ENNReal.ofReal (C ^ 2) * F (c + s • (z - c)) ∂μB :=
            lintegral_mono_ae hpoint_slice
      _ = ENNReal.ofReal (C ^ 2) *
            ∫⁻ z, F (c + s • (z - c)) ∂μB := by
            rw [lintegral_const_mul']
            simp
      _ ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| *
              ∫⁻ z, F z ∂μB) :=
            mul_le_mul_right (by simpa [μB, B] using hcomp) _
      _ ≤ ENNReal.ofReal (C ^ 2) *
            (J * ∫⁻ z, F z ∂μB) := by
            exact mul_le_mul_right
              (mul_le_mul_left hJs_le (∫⁻ z, F z ∂μB)) _
      _ = (ENNReal.ofReal (C ^ 2) * J) *
            ∫⁻ z, F z ∂μB := by
            ac_rfl
  calc
    ∫⁻ z in Metric.ball c r,
        ‖euclideanRadialContractionGradientSegmentIntegral dw c a z‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume
        = ∫⁻ z, ‖∫ t, G (z, t) ∂μI‖ₑ ^ (2 : ℝ) ∂μB := by
            simp [euclideanRadialContractionGradientSegmentIntegral, μB, μI, G, T, V, B]
    _ ≤ ∫⁻ z, ∫⁻ t, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μI ∂μB :=
          lintegral_mono_ae hpoint
    _ = ∫⁻ t, ∫⁻ z, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μB ∂μI := by
          exact MeasureTheory.lintegral_lintegral_swap
            (μ := μB) (ν := μI)
            (f := fun z t ↦ ‖G (z, t)‖ₑ ^ (2 : ℝ)) hGsq_ae
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ∫⁻ z, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μB ∂MeasureTheory.volume := by
          simp [μI]
    _ ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1,
          (ENNReal.ofReal (C ^ 2) * J) *
            ∫⁻ z, F z ∂μB ∂MeasureTheory.volume :=
          setLIntegral_mono' measurableSet_Icc hslice_bound
    _ = (ENNReal.ofReal (C ^ 2) * J) *
          ∫⁻ z, F z ∂μB := by
          simp [Real.volume_Icc]
    _ =
      (ENNReal.ofReal (((1 - a) * r) ^ 2) *
          ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|) *
        ∫⁻ z in Metric.ball c r, ‖dw z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
          simp [C, J, F, μB, B]

/--
%%handwave
name:
  Radial segment integrals are \(L^2\)-controlled by the gradient
statement:
  Let \(r>0\) and \(0<a\le1\).  There is a finite constant \(A\), depending
  only on \(a\), \(r\), and the ambient finite-dimensional Euclidean structure,
  such that the \(L^2(B(c,r))\)-norm of the radial gradient segment integral is
  at most \(A\|D w\|_{L^2(B(c,r))}\).
proof:
  The segment velocity has length at most \((1-a)r\).  After this pointwise
  bound, integrate over \(z\in B(c,r)\) and \(t\in[0,1]\).  For each fixed
  \(t\), the intermediate radial map
  \(z\mapsto c+(a+t(1-a))(z-c)\) has uniformly bounded inverse Jacobian,
  because \(a\le a+t(1-a)\le1\).  This bounds every time slice by a fixed
  multiple of the gradient \(L^2\)-norm on the ball.
-/
theorem euclideanRadialContractionGradientSegmentIntegral_eLpNorm_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {dw : H → H →L[ℝ] ℝ},
        MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
        eLpNorm
          (euclideanRadialContractionGradientSegmentIntegral dw c a) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ENNReal.ofReal A *
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  let C : ℝ := (1 - a) * r
  let j : ℝ := |(a ^ Module.finrank ℝ H)⁻¹|
  let q : ℝ := ((2 : ℝ≥0∞).toReal)⁻¹
  let A : ℝ := (C ^ 2 * j) ^ q
  have hbase_nonneg : 0 ≤ C ^ 2 * j :=
    mul_nonneg (sq_nonneg C) (abs_nonneg _)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    norm_num
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg hbase_nonneg q
  refine ⟨A, hA_nonneg, ?_⟩
  intro dw hdw
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let R : H → ℝ := euclideanRadialContractionGradientSegmentIntegral dw c a
  let K : ℝ≥0∞ := ENNReal.ofReal (C ^ 2) * ENNReal.ofReal j
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.coe_ne_top
  have hlin :
      ∫⁻ z, ‖R z‖ₑ ^ (2 : ℝ) ∂μB ≤
        K * ∫⁻ z, ‖dw z‖ₑ ^ (2 : ℝ) ∂μB := by
    simpa [R, μB, K, C, j] using
      euclideanRadialContractionGradientSegmentIntegral_lintegral_sq_le
        (H := H) (c := c) (r := r) (a := a) hr_pos ha_pos ha_le_one hdw
  have hK_eq : K = ENNReal.ofReal (C ^ 2 * j) := by
    dsimp [K]
    rw [← ENNReal.ofReal_mul (sq_nonneg C)]
  have hK_rpow : K ^ q = ENNReal.ofReal A := by
    rw [hK_eq]
    dsimp [A]
    rw [ENNReal.ofReal_rpow_of_nonneg hbase_nonneg hq_nonneg]
  change eLpNorm R 2 μB ≤ ENNReal.ofReal A * eLpNorm dw 2 μB
  calc
    eLpNorm R 2 μB
        = (∫⁻ z, ‖R z‖ₑ ^ (2 : ℝ) ∂μB) ^ q := by
            rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
            simp [q]
    _ ≤ (K * ∫⁻ z, ‖dw z‖ₑ ^ (2 : ℝ) ∂μB) ^ q :=
          ENNReal.rpow_le_rpow hlin hq_nonneg
    _ = K ^ q * (∫⁻ z, ‖dw z‖ₑ ^ (2 : ℝ) ∂μB) ^ q := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq_nonneg]
    _ = ENNReal.ofReal A * eLpNorm dw 2 μB := by
          rw [hK_rpow, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
          simp [q]

/--
%%handwave
name:
  Radial smooth approximation data
statement:
  Smooth approximation data for radial contraction consists of smooth
  functions \(v_n\) such that, for almost every point of the ball, the
  endpoint differences
  \[
    v_n(z)-v_n(c+a(z-c))
  \]
  converge to the corresponding Sobolev endpoint difference, and the
  integrals of \(D v_n\) along the radial segment from \(c+a(z-c)\) to \(z\)
  converge to the corresponding weak-derivative integral.
-/
structure ScalarWeakSobolevRadialSmoothApproxData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (B : Set H) (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) (c : H) (a : ℝ) where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  endpoint_tendsto :
    ∀ᵐ z ∂MeasureTheory.volume.restrict B,
      Filter.Tendsto
        (fun n : ℕ ↦ approximants n z -
          approximants n (c + a • (z - c)))
        Filter.atTop
        (𝓝 (w z - w (c + a • (z - c))))
  integral_tendsto :
    ∀ᵐ z ∂MeasureTheory.volume.restrict B,
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (approximants n)
              (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (∫ t in Set.Icc (0 : ℝ) 1,
          dw (c + (a + t * (1 - a)) • (z - c))
            ((1 - a) • (z - c)) ∂MeasureTheory.volume))

/--
%%handwave
name:
  Radial smooth approximation data with convergence in measure
statement:
  Smooth approximants to a weak Sobolev function converge in measure after
  taking radial endpoint differences, and their radial segment-integrals
  converge in measure to the corresponding weak-derivative segment-integrals.
-/
structure ScalarWeakSobolevRadialSmoothApproxInMeasureData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (B : Set H) (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) (c : H) (a : ℝ) where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  endpoint_tendstoInMeasure :
    TendstoInMeasure (MeasureTheory.volume.restrict B)
      (fun n z ↦ approximants n z -
        approximants n (c + a • (z - c)))
      Filter.atTop
      (fun z ↦ w z - w (c + a • (z - c)))
  integral_tendstoInMeasure :
    TendstoInMeasure (MeasureTheory.volume.restrict B)
      (fun n z ↦
        ∫ t in Set.Icc (0 : ℝ) 1,
          fderiv ℝ (approximants n)
            (c + (a + t * (1 - a)) • (z - c))
            ((1 - a) • (z - c)) ∂MeasureTheory.volume)
      Filter.atTop
      (fun z ↦
        ∫ t in Set.Icc (0 : ℝ) 1,
          dw (c + (a + t * (1 - a)) • (z - c))
            ((1 - a) • (z - c)) ∂MeasureTheory.volume)

/--
%%handwave
name:
  Radial smooth approximation data with \(L^2\) convergence
statement:
  Smooth approximants to a weak Sobolev function have radial endpoint
  differences and radial segment-integrals converging in \(L^2\) on the ball.
-/
structure ScalarWeakSobolevRadialSmoothApproxL2Data
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (B : Set H) (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) (c : H) (a : ℝ) where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  endpoint_aestronglyMeasurable :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦ approximants n z -
          approximants n (c + a • (z - c)))
        (MeasureTheory.volume.restrict B)
  endpoint_limit_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun z ↦ w z - w (c + a • (z - c)))
      (MeasureTheory.volume.restrict B)
  endpoint_tendsto_l2 :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          ((fun z ↦ approximants n z -
              approximants n (c + a • (z - c))) -
            fun z ↦ w z - w (c + a • (z - c)))
          2 (MeasureTheory.volume.restrict B))
      Filter.atTop (𝓝 0)
  integral_aestronglyMeasurable :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (approximants n)
              (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume)
        (MeasureTheory.volume.restrict B)
  integral_limit_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun z ↦
        ∫ t in Set.Icc (0 : ℝ) 1,
          dw (c + (a + t * (1 - a)) • (z - c))
            ((1 - a) • (z - c)) ∂MeasureTheory.volume)
      (MeasureTheory.volume.restrict B)
  integral_tendsto_l2 :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm
          ((fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                fderiv ℝ (approximants n)
                  (c + (a + t * (1 - a)) • (z - c))
                  ((1 - a) • (z - c)) ∂MeasureTheory.volume) -
            fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                dw (c + (a + t * (1 - a)) • (z - c))
                  ((1 - a) • (z - c)) ∂MeasureTheory.volume)
          2 (MeasureTheory.volume.restrict B))
      Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Graph-norm value convergence gives radial endpoint convergence
statement:
  If smooth approximants converge to \(w\) in \(L^2(B(c,r))\), then their
  radial endpoint differences
  \[
    v_n(z)-v_n(c+a(z-c))
  \]
  converge in \(L^2(B(c,r))\) to the corresponding endpoint difference of
  \(w\), for every \(0<a\le1\).
proof:
  Write the endpoint error as
  \[
    (v_n-w)(z)-(v_n-w)(c+a(z-c)).
  \]
  The triangle inequality controls this by the \(L^2\)-norm of \(v_n-w\) and
  by the \(L^2\)-norm of its radial pullback.  The radial homothety pullback
  estimate bounds the latter by a fixed Jacobian factor times
  \(\|v_n-w\|_{L^2(B(c,r))}\), which tends to zero.
-/
theorem scalarWeakSobolev_radialSmoothApprox_endpoint_l2_on_ball_of_graph
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r a : ℝ}
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hgraph :
      ScalarWeakSobolevSmoothApproxGraphL2Data
        (Metric.ball c r) w dw) :
    (∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦ hgraph.approximants n z -
          hgraph.approximants n (c + a • (z - c)))
        (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
      AEStronglyMeasurable
        (fun z ↦ w z - w (c + a • (z - c)))
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z ↦ hgraph.approximants n z -
                hgraph.approximants n (c + a • (z - c))) -
              fun z ↦ w z - w (c + a • (z - c)))
            2 (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 0) := by
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let T : H → H := fun z ↦ c + a • (z - c)
  let J : ℝ≥0∞ :=
    (ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|) ^
      ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hT_cont : Continuous T := by
    dsimp [T]
    fun_prop
  have hT_qmp :
      Measure.QuasiMeasurePreserving T μB μB := by
    simpa [T, μB] using
      euclideanRadialHomothety_quasiMeasurePreserving_restrict_ball
        (H := H) (c := c) (r := r) (s := a) ha_pos ha_le_one
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hv : Continuous (hgraph.approximants n) :=
      (hgraph.smooth n).continuous
    have hbase :
        AEStronglyMeasurable (hgraph.approximants n) μB :=
      hv.aestronglyMeasurable
    have hpull :
        AEStronglyMeasurable
          (fun z : H ↦ hgraph.approximants n (T z)) μB :=
      (hv.comp hT_cont).aestronglyMeasurable
    simpa [μB, T] using hbase.sub hpull
  · let e0 : H → ℝ := fun z ↦ hgraph.approximants 0 z - w z
    have hv0 : Continuous (hgraph.approximants 0) :=
      (hgraph.smooth 0).continuous
    have hv0_meas :
        AEStronglyMeasurable (hgraph.approximants 0) μB :=
      hv0.aestronglyMeasurable
    have he0_meas : AEStronglyMeasurable e0 μB := by
      simpa [e0, μB] using
        (hgraph.value_error_memLp 0).aestronglyMeasurable
    have hw_meas : AEStronglyMeasurable w μB := by
      refine (hv0_meas.sub he0_meas).congr ?_
      exact Filter.Eventually.of_forall fun z ↦ by simp [e0]
    have hw_pull :
        AEStronglyMeasurable (fun z : H ↦ w (T z)) μB := by
      simpa [Function.comp_def] using
        hw_meas.comp_quasiMeasurePreserving hT_qmp
    simpa [μB, T] using hw_meas.sub hw_pull
  · have hJ_ne_top : J ≠ ⊤ := by
      simp [J]
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            J *
              eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2 μB)
          Filter.atTop (𝓝 0) := by
      have hmul' :=
        ENNReal.Tendsto.const_mul
          (by simpa [μB] using hgraph.value_tendsto_l2)
          (Or.inr hJ_ne_top)
      have hzero : J * 0 = 0 := by
        exact mul_zero J
      simpa [μB, hzero] using hmul'
    have hsum :
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2 μB +
              J *
                eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2 μB)
          Filter.atTop (𝓝 0) := by
      have hbase : Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2 μB)
          Filter.atTop (𝓝 0) := by
        simpa [μB] using hgraph.value_tendsto_l2
      simpa using hbase.add hmul
    have hbound :
        ∀ n : ℕ,
          eLpNorm
            ((fun z ↦ hgraph.approximants n z -
                hgraph.approximants n (c + a • (z - c))) -
              fun z ↦ w z - w (c + a • (z - c)))
            2 μB ≤
          eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2 μB +
            J * eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2 μB := by
      intro n
      let e : H → ℝ := fun z ↦ hgraph.approximants n z - w z
      have he_meas : AEStronglyMeasurable e μB := by
        simpa [e, μB] using
          (hgraph.value_error_memLp n).aestronglyMeasurable
      have he_pull :
          AEStronglyMeasurable (fun z : H ↦ e (T z)) μB := by
        simpa [Function.comp_def] using
          he_meas.comp_quasiMeasurePreserving hT_qmp
      have htriangle :
          eLpNorm (fun z : H ↦ e z - e (T z)) 2 μB ≤
            eLpNorm e 2 μB + eLpNorm (fun z : H ↦ e (T z)) 2 μB :=
        eLpNorm_sub_le he_meas he_pull (by norm_num)
      have hpull :
          eLpNorm (fun z : H ↦ e (T z)) 2 μB ≤
            J * eLpNorm e 2 μB := by
        simpa [J, T, μB, e] using
          euclideanRadialHomothety_eLpNorm_comp_le
            (H := H) (c := c) (r := r) (s := a)
            ha_pos ha_le_one he_meas
      calc
        eLpNorm
            ((fun z ↦ hgraph.approximants n z -
                hgraph.approximants n (c + a • (z - c))) -
              fun z ↦ w z - w (c + a • (z - c)))
            2 μB
            = eLpNorm (fun z : H ↦ e z - e (T z)) 2 μB := by
                apply eLpNorm_congr_ae
                filter_upwards with z
                simp [e, T, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        _ ≤ eLpNorm e 2 μB + eLpNorm (fun z : H ↦ e (T z)) 2 μB :=
            htriangle
        _ ≤ eLpNorm e 2 μB + J * eLpNorm e 2 μB :=
            add_le_add_right hpull (eLpNorm e 2 μB)
        _ =
          eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2 μB +
            J * eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2 μB := by
            simp [e]
    rw [ENNReal.tendsto_atTop_zero] at hsum ⊢
    intro ε hε
    rcases hsum ε hε with ⟨N, hN⟩
    exact ⟨N, fun n hn ↦ (hbound n).trans (hN n hn)⟩

/--
%%handwave
name:
  \(L^2\) radial convergence gives convergence in measure
statement:
  \(L^2\)-convergence of radial endpoint differences and radial
  segment-integrals implies convergence in measure of the same quantities.
proof:
  Apply the standard implication from convergence in \(L^p\), with
  \(p=2\), to convergence in measure, using the measurability included in the
  radial \(L^2\) approximation data.
-/
def scalarWeakSobolev_radial_smoothApproxInMeasureData_of_l2
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {B : Set H} {w : H → ℝ} {dw : H → H →L[ℝ] ℝ} {c : H} {a : ℝ}
    (happrox : ScalarWeakSobolevRadialSmoothApproxL2Data B w dw c a) :
    ScalarWeakSobolevRadialSmoothApproxInMeasureData B w dw c a := by
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
        (μ := MeasureTheory.volume.restrict B)
        (p := (2 : ℝ≥0∞))
        (by norm_num)
        hendpoint_meas hendpoint_lim_meas hendpoint_l2
  · exact
      tendstoInMeasure_of_tendsto_eLpNorm
        (μ := MeasureTheory.volume.restrict B)
        (p := (2 : ℝ≥0∞))
        (by norm_num)
        hintegral_meas hintegral_lim_meas hintegral_l2

/--
%%handwave
name:
  Convergence in measure gives radial almost-everywhere smooth approximation
statement:
  If radial endpoint differences and radial segment-integrals of smooth
  approximants converge in measure, then after passing to a common
  subsequence they converge almost everywhere in both senses needed for the
  radial weak fundamental theorem.
proof:
  First choose a subsequence along which the endpoint differences converge
  almost everywhere.  Along this subsequence choose a further subsequence along
  which the segment integrals converge almost everywhere.  The first
  convergence is preserved under the further subsequence, and the composed
  approximants remain smooth.
-/
theorem scalarWeakSobolev_radial_smoothApproxData_of_tendstoInMeasure
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {B : Set H} {w : H → ℝ} {dw : H → H →L[ℝ] ℝ} {c : H} {a : ℝ}
    (happrox : ScalarWeakSobolevRadialSmoothApproxInMeasureData B w dw c a) :
    Nonempty (ScalarWeakSobolevRadialSmoothApproxData B w dw c a) := by
  rcases happrox with ⟨v, hv_smooth, hendpoint, hintegral⟩
  rcases hendpoint.exists_seq_tendsto_ae with
    ⟨ns, hns_strict, hendpoint_ae⟩
  have hintegral_subseq :
      TendstoInMeasure (MeasureTheory.volume.restrict B)
        (fun i z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (v (ns i))
              (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume)
        Filter.atTop
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            dw (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume) := by
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
  Radial smooth approximation gives the weak segment identity
statement:
  If smooth radial approximation data is available on a ball, then the
  Sobolev function satisfies, for almost every point of the ball, the radial
  endpoint identity with the weak derivative integrated along the segment.
proof:
  For each smooth approximant, apply the classical fundamental theorem of
  calculus on the radial segment.  Passing to the almost-everywhere limits of
  the endpoint differences and of the segment integrals gives the identity.
-/
theorem scalarWeakSobolev_radial_contraction_line_integral_eq_ae_of_smoothApproxData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {B : Set H} {w : H → ℝ} {dw : H → H →L[ℝ] ℝ} {c : H} {a : ℝ}
    (happrox : ScalarWeakSobolevRadialSmoothApproxData B w dw c a) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict B,
      w z - w (c + a • (z - c)) =
        ∫ t in Set.Icc (0 : ℝ) 1,
          dw (c + (a + t * (1 - a)) • (z - c)) ((1 - a) • (z - c))
            ∂MeasureTheory.volume := by
  rcases happrox with ⟨v, hv_smooth, hendpoint, hintegral⟩
  filter_upwards [hendpoint, hintegral] with z hz_endpoint hz_integral
  have hftc :
      ∀ n : ℕ,
        v n z - v n (c + a • (z - c)) =
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (v n)
              (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume := by
    intro n
    let x : H := z - c
    let p : H := c + a • x
    let ξ : H := (1 - a) • x
    have hendpoint : p + ξ = z := by
      calc
        p + ξ = c + (a • x + (1 - a) • x) := by
          simp [p, ξ, add_assoc]
        _ = c + (a + (1 - a)) • x := by
          rw [← add_smul]
        _ = z := by
          simp [x, sub_eq_add_neg, add_comm]
    have hpath :
        ∀ t : ℝ, p + t • ξ = c + (a + t * (1 - a)) • x := by
      intro t
      calc
        p + t • ξ = c + (a • x + t • ((1 - a) • x)) := by
          simp [p, ξ, add_assoc]
        _ = c + (a • x + (t * (1 - a)) • x) := by
          rw [smul_smul]
        _ = c + (a + t * (1 - a)) • x := by
          rw [← add_smul]
    have hseg :=
      contDiff_endpoint_sub_eq_segmentIntegral_fderiv (hv_smooth n) p ξ
    dsimp [p, ξ, x] at hendpoint hpath hseg ⊢
    calc
      v n z - v n (c + a • (z - c))
          = v n ((c + a • (z - c)) + (1 - a) • (z - c)) -
              v n (c + a • (z - c)) := by
              rw [hendpoint]
      _ =
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (v n)
              ((c + a • (z - c)) + t • ((1 - a) • (z - c)))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume := hseg
      _ =
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (v n)
              (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume := by
            refine integral_congr_ae ?_
            exact ae_of_all _ fun t ↦ by
              simpa using
                congrArg
                  (fun y : H ↦
                    (fderiv ℝ (v n) y) ((1 - a) • (z - c)))
                  (hpath t)
  have hz_integral' :
      Filter.Tendsto (fun n : ℕ ↦ v n z - v n (c + a • (z - c)))
        Filter.atTop
        (𝓝 (∫ t in Set.Icc (0 : ℝ) 1,
          dw (c + (a + t * (1 - a)) • (z - c)) ((1 - a) • (z - c))
            ∂MeasureTheory.volume)) := by
    simpa [hftc] using hz_integral
  exact tendsto_nhds_unique hz_endpoint hz_integral'

/--
%%handwave
name:
  Continuous functions on compact sets are square-integrable
statement:
  A continuous function with values in a normed target is square-integrable
  with respect to volume restricted to a compact Euclidean set.
proof:
  A continuous function is bounded on a compact set, and restricted volume is
  finite on compact sets.
-/
private theorem memLp_restrict_of_isCompact_of_continuousOn
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E]
    {K : Set H} (hK : IsCompact K) {f : H → E}
    (hf : ContinuousOn f K) :
    MemLp f 2 (MeasureTheory.volume.restrict K) := by
  classical
  let μK : Measure H := MeasureTheory.volume.restrict K
  haveI : IsFiniteMeasure μK := isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hf_aesm : AEStronglyMeasurable f μK := by
    simpa [μK] using
      hf.aestronglyMeasurable_of_isCompact hK hK.measurableSet
  rcases hK.exists_bound_of_continuousOn hf with ⟨C, hC⟩
  exact
    MemLp.of_bound (μ := μK) (p := (2 : ℝ≥0∞))
      hf_aesm C
      (ae_restrict_of_forall_mem hK.measurableSet hC)

/--
%%handwave
name:
  A bounded continuous multiplier belongs to \(L^2\) on a ball
statement:
  If \(a\) is continuous and globally bounded on a finite-dimensional
  Euclidean space, then \(a\in L^2(B(c,r))\).
proof:
  Restricted Lebesgue measure of a ball is finite. Strong measurability follows
  from continuity, and the global bound gives \(L^2\) membership.
-/
private theorem bounded_continuous_multiplier_memLp_two_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r : ℝ} {a : H → ℝ}
    (ha_cont : Continuous a)
    (ha_bound : ∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C) :
    MemLp a 2 (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  classical
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  haveI : IsFiniteMeasure μB := by
    change IsFiniteMeasure
      ((MeasureTheory.volume : Measure H).restrict (Metric.ball c r))
    exact isFiniteMeasure_restrict.2
      (measure_ball_ne_top (μ := (MeasureTheory.volume : Measure H)))
  rcases ha_bound with ⟨C, hC⟩
  exact
    MemLp.of_bound (μ := μB) (p := (2 : ℝ≥0∞))
      ha_cont.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)

/--
%%handwave
name:
  Integrability of a bounded multiplier times an \(L^2\) function
statement:
  If \(a\) is continuous and bounded and \(f\in L^2(B(c,r))\), then
  \(af\in L^1(B(c,r))\).
proof:
  The multiplier belongs to \(L^2\) on the ball, so Hölder's inequality for
  the product of two \(L^2\) functions gives integrability.
-/
private theorem bounded_continuous_multiplier_smul_integrable_of_memLp_two_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r : ℝ} {a f : H → ℝ}
    (ha_cont : Continuous a)
    (ha_bound : ∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C)
    (hf : MemLp f 2
      (MeasureTheory.volume.restrict (Metric.ball c r))) :
    Integrable (fun z : H ↦ a z • f z)
      (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  have ha_mem : MemLp a 2 μB :=
    bounded_continuous_multiplier_memLp_two_on_ball
      (c := c) (r := r) ha_cont ha_bound
  have hprod : Integrable (fun z : H ↦ a z * f z) μB :=
    MemLp.integrable_mul ha_mem (by simpa [μB] using hf)
  simpa [μB, smul_eq_mul] using hprod

/--
%%handwave
name:
  Convergence of bounded-multiplier integrals under \(L^2\) convergence
statement:
  Let \(a\) be bounded and continuous on a finite-dimensional Euclidean
  space. If \(f_n\to f\) in \(L^2(B(c,r))\), then
  \[\int_{B(c,r)}a f_n\longrightarrow\int_{B(c,r)}a f.\]
proof:
  Since \(a\in L^2(B(c,r))\), Hölder bounds the difference of the integrals by
  \(\lVert a\rVert_2\lVert f_n-f\rVert_2\), which tends to zero.
-/
private theorem bounded_continuous_multiplier_integral_tendsto_of_L2_on_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r : ℝ} {a : H → ℝ}
    (ha_cont : Continuous a)
    (ha_bound : ∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C)
    {fseq : ℕ → H → ℝ} {f : H → ℝ}
    (hseq_mem : ∀ n : ℕ, MemLp (fseq n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hf_mem : MemLp f 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (htend :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ fseq n z - f z) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z, a z • fseq n z
          ∂(MeasureTheory.volume.restrict (Metric.ball c r)))
      Filter.atTop
      (𝓝 (∫ z, a z • f z
        ∂(MeasureTheory.volume.restrict (Metric.ball c r)))) := by
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  have ha_mem : MemLp a 2 μB :=
    bounded_continuous_multiplier_memLp_two_on_ball
      (c := c) (r := r) ha_cont ha_bound
  have hlimit_int :
      Integrable (fun z : H ↦ a z • f z) μB :=
    bounded_continuous_multiplier_smul_integrable_of_memLp_two_on_ball
      (c := c) (r := r) ha_cont ha_bound (by simpa [μB] using hf_mem)
  have hseq_int :
      ∀ n : ℕ, Integrable (fun z : H ↦ a z • fseq n z) μB := by
    intro n
    exact
      bounded_continuous_multiplier_smul_integrable_of_memLp_two_on_ball
        (c := c) (r := r) ha_cont ha_bound
        (by simpa [μB] using hseq_mem n)
  have hraw_bound :
      ∀ n : ℕ,
        eLpNorm (fun z : H ↦ a z • (fseq n z - f z)) 1 μB ≤
          eLpNorm a 2 μB *
            eLpNorm (fun z : H ↦ fseq n z - f z) 2 μB := by
    intro n
    have hseqn_mem : MemLp (fseq n) 2 μB := by
      simpa [μB] using hseq_mem n
    have hf_mem' : MemLp f 2 μB := by
      simpa [μB] using hf_mem
    have hdiff_aesm :
        AEStronglyMeasurable (fun z : H ↦ fseq n z - f z) μB :=
      hseqn_mem.aestronglyMeasurable.sub hf_mem'.aestronglyMeasurable
    simpa [μB, smul_eq_mul] using
      (eLpNorm_smul_le_mul_eLpNorm
        (μ := μB) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (r := (1 : ℝ≥0∞))
        (f := fun z : H ↦ fseq n z - f z)
        (φ := a)
        (hf := hdiff_aesm)
        (hφ := ha_mem.aestronglyMeasurable))
  have hraw_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ a z • (fseq n z - f z)) 1 μB)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm a 2 μB *
              eLpNorm (fun z : H ↦ fseq n z - f z) 2 μB)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have hconst :
          Filter.Tendsto
            (fun n : ℕ ↦
              eLpNorm a 2 μB *
                eLpNorm (fun z : H ↦ fseq n z - f z) 2 μB)
            Filter.atTop (𝓝 (eLpNorm a 2 μB * (0 : ℝ≥0∞))) :=
        ENNReal.Tendsto.const_mul
          (by simpa [μB] using htend)
          (Or.inr ha_mem.eLpNorm_ne_top)
      have hzero : eLpNorm a 2 μB * (0 : ℝ≥0∞) = 0 := by
        rw [mul_zero]
      simpa [hzero] using hconst
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hraw_bound
  have hL1 :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z : H ↦ a z • fseq n z) -
              fun z : H ↦ a z • f z) 1 μB)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ by
          change a z * (fseq n z - f z) =
            a z * fseq n z - a z * f z
          ring)
      hraw_tendsto
  exact
    tendsto_integral_of_L1'
      (μ := μB)
      (f := fun z : H ↦ a z • f z)
      hlimit_int.aestronglyMeasurable
      (F := fun (n : ℕ) (z : H) ↦ a z • fseq n z)
      (Filter.Eventually.of_forall hseq_int)
      hL1

/--
%%handwave
name:
  Full derivative convergence from finitely many directions
statement:
  For finite-dimensional \(H\), if the \(L^2\)-norms of an
  operator-valued sequence vanish after evaluating on each vector of a fixed
  finite basis of \(H\), then the operator-valued \(L^2\)-norms themselves
  vanish.
proof:
  Identify operators with their finitely many values on a basis.  The
  operator norm is bounded by a fixed finite multiple of the finite sum of
  the coordinate norms, and this finite sum tends to zero.
-/
theorem continuousLinearMap_sequence_memLp_and_eLpNorm_tendsto_zero_of_basis_eval
    {α H E : Type} [MeasurableSpace α]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure α} (Fseq : ℕ → α → H →L[ℝ] E)
    (h_eval_mem : ∀ (n : ℕ) (i : Fin (Module.finrank ℝ H)),
      MemLp (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ)
    (h_eval_tendsto : ∀ i : Fin (Module.finrank ℝ H),
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    (∀ n : ℕ, MemLp (Fseq n) 2 μ) ∧
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (Fseq n) 2 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let ι := Fin (Module.finrank ℝ H)
  let B : ℕ → ℝ≥0∞ := fun n ↦
    ∑ i : ι, eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ
  let Ceval : ι → ℝ≥0∞ := fun _ ↦ 1
  have hCeval_top : ∀ i : ι, Ceval i < ⊤ := by
    intro i
    simp [Ceval]
  have h_eval_bound :
      ∀ (n : ℕ) (i : ι),
        MemLp (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ ∧
          eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ ≤
            Ceval i * B n := by
    intro n i
    refine ⟨h_eval_mem n i, ?_⟩
    calc
      eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ
          ≤ B n := by
            dsimp [B, ι]
            exact Finset.single_le_sum
              (f := fun j : ι ↦
                eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H j)) 2 μ)
              (fun j _hj ↦ zero_le)
              (Finset.mem_univ i)
      _ = Ceval i * B n := by simp [Ceval]
  rcases
    continuousLinearMap_sequence_memLp_and_eLpNorm_le_of_basis_eval_const_mul
      (Fseq := Fseq) (B := B) (Ceval := Ceval)
      hCeval_top h_eval_bound with
    ⟨C, hC_top, hfull⟩
  have hB_tendsto :
      Filter.Tendsto B Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    dsimp [B]
    simpa using
      (tendsto_finsetSum (s := Finset.univ)
        (f := fun i n ↦
          eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ)
        (a := fun _i : ι ↦ (0 : ℝ≥0∞))
        (x := Filter.atTop)
        (fun i _hi ↦ h_eval_tendsto i))
  have hC_ne_top : C ≠ ⊤ := ne_of_lt hC_top
  have hCB_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ C * B n)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul := ENNReal.Tendsto.const_mul hB_tendsto (Or.inr hC_ne_top)
    simpa using hmul
  refine ⟨fun n ↦ (hfull n).1, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hCB_tendsto
    (fun n ↦ zero_le)
    (fun n ↦ (hfull n).2)

/--
%%handwave
name:
  One-step smooth approximation in the full graph norm
statement:
  Let \(Q\Subset P\subset\Omega\).  If a scalar weak Sobolev pair on
  \(\Omega\) is globally integrable and square-integrable on \(P\), then for
  every positive tolerance there is a smooth function whose value and full
  derivative field are both within that tolerance in \(L^2(Q)\).
proof:
  Use a single sufficiently small mollifier.  Directional convergence holds
  for each vector in a finite basis, and the finite-basis comparison converts
  these finitely many directional estimates into the full operator-valued
  estimate.
-/
theorem euclideanSobolev_exists_smooth_full_graph_approx_on_compact_of_global_integrable_pair
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H}
    (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw_int : Integrable w (MeasureTheory.volume : Measure H))
    (hdw_int : Integrable dw (MeasureTheory.volume : Measure H))
    (hw : MemLp w 2 (MeasureTheory.volume.restrict P))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict P))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : H → ℝ,
      ContDiff ℝ ∞ v ∧
        eLpNorm (fun z ↦ v z - w z) 2
            (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε ∧
        eLpNorm (fun z ↦ fderiv ℝ v z - dw z) 2
            (MeasureTheory.volume.restrict Q) ≤ ENNReal.ofReal ε := by
  classical
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  let μP : Measure H := MeasureTheory.volume.restrict P
  let vseq : ℕ → H → ℝ := fun n ↦
    ((scalarWeakSobolevStandardMollifier H n).normed
      (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure H)] w : H → ℝ)
  have hweakK :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Ω w dw := by
    simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionWithValues] using hweak
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
  have hdw_Q : MemLp dw 2 μQ :=
    hdw.mono_measure (by
      dsimp [μQ, μP]
      exact Measure.restrict_mono hQP_subset le_rfl)
  have hv_smooth : ∀ n : ℕ, ContDiff ℝ ∞ (vseq n) := by
    intro n
    let φ : ContDiffBump (0 : H) := scalarWeakSobolevStandardMollifier H n
    change ContDiff ℝ ∞
      (φ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
        (MeasureTheory.volume : Measure H)] w : H → ℝ)
    exact
      φ.hasCompactSupport_normed.contDiff_convolution_left
        (lsmul ℝ ℝ) φ.contDiff_normed hw_int.locallyIntegrable
  have hvalue_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ vseq n z - w z) 2 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [vseq, μQ] using
      scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_global_integrable
        hQ hP hQP hw_int hw
  let Fseq : ℕ → H → H →L[ℝ] ℝ :=
    fun n z ↦ fderiv ℝ (vseq n) z - dw z
  have h_eval_mem :
      ∀ (n : ℕ) (i : Fin (Module.finrank ℝ H)),
        MemLp (fun z ↦ Fseq n z (Module.finBasis ℝ H i)) 2 μQ := by
    intro n i
    let e : H := Module.finBasis ℝ H i
    let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ e
    have hD_cont :
        Continuous (fun z : H ↦ fderiv ℝ (vseq n) z) :=
      (hv_smooth n).continuous_fderiv (by simp)
    have hD_eval_cont :
        Continuous (fun z : H ↦ fderiv ℝ (vseq n) z e) :=
      hD_cont.clm_apply continuous_const
    have hD_eval_mem :
        MemLp (fun z : H ↦ fderiv ℝ (vseq n) z e) 2 μQ :=
      memLp_restrict_of_isCompact_of_continuousOn hQ hD_eval_cont.continuousOn
    have hdw_eval_mem :
        MemLp (fun z : H ↦ dw z e) 2 μQ := by
      simpa [L, Function.comp_def] using L.comp_memLp' hdw_Q
    simpa [Fseq, e, ContinuousLinearMap.sub_apply] using
      hD_eval_mem.sub hdw_eval_mem
  have h_eval_tendsto :
      ∀ i : Fin (Module.finrank ℝ H),
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun z ↦ Fseq n z (Module.finBasis ℝ H i)) 2 μQ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    intro i
    let e : H := Module.finBasis ℝ H i
    let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ e
    have hdw_eval_int :
        Integrable (fun z : H ↦ dw z e)
          (MeasureTheory.volume : Measure H) := by
      simpa [L, Function.comp_def] using L.integrable_comp hdw_int
    have hdw_eval_mem :
        MemLp (fun z : H ↦ dw z e) 2 μP := by
      simpa [L, Function.comp_def] using L.comp_memLp' hdw
    have hdir :=
      scalarWeakSobolev_standardMollifier_directionalDerivative_eLpNorm_tendsto_zero_of_global_integrable_pair
        hQ hP hQP hPΩ hΩ_open hweakK hw_int hdw_eval_int hw hdw_eval_mem
    simpa [Fseq, vseq, e, μQ, ContinuousLinearMap.sub_apply] using hdir
  have hfull :=
    continuousLinearMap_sequence_memLp_and_eLpNorm_tendsto_zero_of_basis_eval
      (Fseq := Fseq) h_eval_mem h_eval_tendsto
  have hεENN : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hvalue_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (fun z ↦ vseq n z - w z) 2 μQ ≤ ENNReal.ofReal ε :=
    hvalue_tendsto.eventually (eventually_le_nhds hεENN)
  have hderiv_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (fun z ↦ fderiv ℝ (vseq n) z - dw z) 2 μQ ≤
          ENNReal.ofReal ε := by
    exact hfull.2.eventually (eventually_le_nhds hεENN)
  rcases Filter.eventually_atTop.1 (hvalue_event.and hderiv_event) with
    ⟨N, hN⟩
  refine ⟨vseq N, hv_smooth N, ?_, ?_⟩
  · exact (hN N le_rfl).1
  · exact (hN N le_rfl).2

/--
%%handwave
name:
  Smooth graph-norm approximation on compact Euclidean sets
statement:
  Let \(Q\Subset P\subset\Omega\).  If a scalar weak Sobolev pair on
  \(\Omega\) is globally integrable and square-integrable on \(P\), then the
  standard mollifications converge on \(Q\) in the full \(L^2\) graph norm.
proof:
  The value convergence is the usual compact mollifier convergence.  For the
  derivative, apply the directional mollifier convergence in each vector of a
  finite basis and then use the finite-basis comparison of operator-valued
  \(L^2\)-norms.
-/
theorem euclideanSobolev_smooth_graph_density_l2_on_compact_of_global_integrable_pair
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H}
    (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw_int : Integrable w (MeasureTheory.volume : Measure H))
    (hdw_int : Integrable dw (MeasureTheory.volume : Measure H))
    (hw : MemLp w 2 (MeasureTheory.volume.restrict P))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict P)) :
    Nonempty (ScalarWeakSobolevSmoothApproxGraphL2Data Q w dw) := by
  classical
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
  have hw_Q : MemLp w 2 μQ := by
    exact hw.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_mono hQP_subset le_rfl)
  have hdw_Q : MemLp dw 2 μQ := by
    exact hdw.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_mono hQP_subset le_rfl)
  have happrox :
      ∀ n : ℕ, ∃ v : H → ℝ,
        ContDiff ℝ ∞ v ∧
          eLpNorm (fun z ↦ v z - w z) 2 μQ ≤
              ENNReal.ofReal (((n : ℝ) + 1)⁻¹) ∧
          eLpNorm (fun z ↦ fderiv ℝ v z - dw z) 2 μQ ≤
              ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
    intro n
    exact
      euclideanSobolev_exists_smooth_full_graph_approx_on_compact_of_global_integrable_pair
        hQ hP hQP hPΩ hΩ_open hweak hw_int hdw_int hw hdw
        (by positivity : 0 < (((n : ℝ) + 1)⁻¹))
  choose v hv_smooth hv_value_le hv_deriv_le using happrox
  have hvalue_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ v n z - w z) 2 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hle :
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ v n z - w z) 2 μQ) ≤
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
      tendsto_const_nhds hupper (fun n ↦ zero_le) hle
  have hderiv_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ fderiv ℝ (v n) z - dw z) 2 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hle :
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ fderiv ℝ (v n) z - dw z) 2 μQ) ≤
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
      tendsto_const_nhds hupper (fun n ↦ zero_le) hle
  refine
    ⟨{ approximants := v
       smooth := hv_smooth
       value_error_memLp := ?_
       value_tendsto_l2 := hvalue_tendsto
       derivative_error_memLp := ?_
       derivative_tendsto_l2 := hderiv_tendsto }⟩
  · intro n
    have hv_cont : Continuous (v n) := (hv_smooth n).continuous
    have hv_mem :
        MemLp (v n) 2 μQ :=
      memLp_restrict_of_isCompact_of_continuousOn hQ hv_cont.continuousOn
    exact hv_mem.sub hw_Q
  · intro n
    have hD_cont :
        Continuous (fun z : H ↦ fderiv ℝ (v n) z) :=
      (hv_smooth n).continuous_fderiv (by simp)
    have hD_mem :
        MemLp (fun z : H ↦ fderiv ℝ (v n) z) 2 μQ :=
      memLp_restrict_of_isCompact_of_continuousOn hQ hD_cont.continuousOn
    exact hD_mem.sub hdw_Q

section StandardEuclideanBall

variable {ι : Type} [Fintype ι]

local notation "H" => EuclideanSpace ℝ ι

/--
%%handwave
name:
  Smooth graph-norm approximation on a ball
statement:
  Let \(B(c,r)\subset\Omega\), with \(r>0\).  A scalar weak \(W^{1,2}\)
  function on \(\Omega\), with square-integrable weak derivative on \(B(c,r)\),
  admits smooth approximants converging to it in the full \(L^2\) graph norm
  on \(B(c,r)\).
proof:
  This is the standard smooth density theorem for the Sobolev graph norm on
  a ball.  One takes compact subballs exhausting \(B(c,r)\), localizes inside
  \(\Omega\), applies mollifier graph-density there, uses a finite basis of
  the ambient Euclidean space to convert convergence of the finitely many
  directional derivatives into convergence of the full derivative field, and
  diagonalizes while the \(L^2\)-tails on the annuli tend to zero.
-/
theorem euclideanSobolev_smooth_graph_density_l2_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    Nonempty
      (ScalarWeakSobolevSmoothApproxGraphL2Data
        (Metric.ball c r) w dw) := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let B : Set H := Metric.ball c r
  let Q : Set H := Metric.closedBall c r
  let P : Set H := Metric.closedBall c (r + 1)
  rcases
    euclideanSobolev_global_integrable_extension_l2_from_ball
      hr_pos hΩ_open hballΩ hweak hw hdw with
    ⟨W, DW, hweak_ext, hW_int, hDW_int, hW_P, hDW_P, hW_eq, hDW_eq⟩
  have hQ : IsCompact Q := by
    dsimp [Q]
    exact isCompact_closedBall c r
  have hP : IsCompact P := by
    dsimp [P]
    exact isCompact_closedBall c (r + 1)
  have hQ_ball : Q ⊆ Metric.ball c (r + 1) := by
    intro z hz
    have hz_le : dist z c ≤ r := by
      simpa [Q, Metric.mem_closedBall] using hz
    have hz_lt : dist z c < r + 1 := by linarith
    simpa [Metric.mem_ball] using hz_lt
  rcases hQ.exists_cthickening_subset_open
      (Metric.isOpen_ball) hQ_ball with
    ⟨δ, hδ_pos, hδ_ball⟩
  have hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P := by
    refine ⟨δ, hδ_pos, ?_⟩
    exact hδ_ball.trans (by
      intro z hz
      exact Metric.ball_subset_closedBall hz)
  rcases
    euclideanSobolev_smooth_graph_density_l2_on_compact_of_global_integrable_pair
      (Q := Q) (P := P) (Ω := Set.univ)
      hQ hP hQP (by intro z hz; trivial) isOpen_univ
      hweak_ext hW_int hDW_int hW_P hDW_P with
    ⟨hgraph⟩
  have hBQ : B ⊆ Q := by
    dsimp [B, Q]
    exact Metric.ball_subset_closedBall
  have hμBQ :
      MeasureTheory.volume.restrict B ≤ MeasureTheory.volume.restrict Q :=
    Measure.restrict_mono hBQ le_rfl
  refine
    ⟨{ approximants := hgraph.approximants
       smooth := hgraph.smooth
       value_error_memLp := ?_
       value_tendsto_l2 := ?_
       derivative_error_memLp := ?_
       derivative_tendsto_l2 := ?_ }⟩
  · intro n
    have hmem :
        MemLp
          (fun z ↦ hgraph.approximants n z - W z)
          2 (MeasureTheory.volume.restrict B) :=
      (hgraph.value_error_memLp n).mono_measure hμBQ
    have hae :
        (fun z ↦ hgraph.approximants n z - W z)
          =ᵐ[MeasureTheory.volume.restrict B]
        fun z ↦ hgraph.approximants n z - w z :=
      Filter.EventuallyEq.rfl.sub hW_eq
    exact hmem.ae_eq hae
  · have hle :
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2
            (MeasureTheory.volume.restrict B)) ≤
        fun n : ℕ ↦
          eLpNorm (fun z ↦ hgraph.approximants n z - W z) 2
            (MeasureTheory.volume.restrict Q) := by
      intro n
      have hae :
          (fun z ↦ hgraph.approximants n z - W z)
            =ᵐ[MeasureTheory.volume.restrict B]
          fun z ↦ hgraph.approximants n z - w z :=
        Filter.EventuallyEq.rfl.sub hW_eq
      calc
        eLpNorm (fun z ↦ hgraph.approximants n z - w z) 2
            (MeasureTheory.volume.restrict B)
            =
          eLpNorm (fun z ↦ hgraph.approximants n z - W z) 2
            (MeasureTheory.volume.restrict B) := by
              exact eLpNorm_congr_ae hae.symm
        _ ≤
          eLpNorm (fun z ↦ hgraph.approximants n z - W z) 2
            (MeasureTheory.volume.restrict Q) :=
              eLpNorm_mono_measure _ hμBQ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hgraph.value_tendsto_l2
      (fun n ↦ zero_le) hle
  · intro n
    have hmem :
        MemLp
          (fun z ↦ fderiv ℝ (hgraph.approximants n) z - DW z)
          2 (MeasureTheory.volume.restrict B) :=
      (hgraph.derivative_error_memLp n).mono_measure hμBQ
    have hae :
        (fun z ↦ fderiv ℝ (hgraph.approximants n) z - DW z)
          =ᵐ[MeasureTheory.volume.restrict B]
        fun z ↦ fderiv ℝ (hgraph.approximants n) z - dw z :=
      Filter.EventuallyEq.rfl.sub hDW_eq
    exact hmem.ae_eq hae
  · have hle :
        (fun n : ℕ ↦
          eLpNorm
            (fun z ↦ fderiv ℝ (hgraph.approximants n) z - dw z) 2
            (MeasureTheory.volume.restrict B)) ≤
        fun n : ℕ ↦
          eLpNorm
            (fun z ↦ fderiv ℝ (hgraph.approximants n) z - DW z) 2
            (MeasureTheory.volume.restrict Q) := by
      intro n
      have hae :
          (fun z ↦ fderiv ℝ (hgraph.approximants n) z - DW z)
            =ᵐ[MeasureTheory.volume.restrict B]
          fun z ↦ fderiv ℝ (hgraph.approximants n) z - dw z :=
        Filter.EventuallyEq.rfl.sub hDW_eq
      calc
        eLpNorm
            (fun z ↦ fderiv ℝ (hgraph.approximants n) z - dw z) 2
            (MeasureTheory.volume.restrict B)
            =
          eLpNorm
            (fun z ↦ fderiv ℝ (hgraph.approximants n) z - DW z) 2
            (MeasureTheory.volume.restrict B) := by
              exact eLpNorm_congr_ae hae.symm
        _ ≤
          eLpNorm
            (fun z ↦ fderiv ℝ (hgraph.approximants n) z - DW z) 2
            (MeasureTheory.volume.restrict Q) :=
              eLpNorm_mono_measure _ hμBQ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hgraph.derivative_tendsto_l2
      (fun n ↦ zero_le) hle

/--
%%handwave
name:
  Smooth graph-norm approximation on a ball
statement:
  Let \(B(c,r)\subset\Omega\), with \(r>0\).  A scalar weak \(W^{1,2}\)
  function on \(\Omega\), with square-integrable weak derivative on \(B(c,r)\),
  admits smooth approximants converging to it in the full \(L^2\) graph norm
  on \(B(c,r)\).
proof:
  Apply the smooth density theorem for the Sobolev graph norm on Euclidean
  balls.
-/
theorem scalarWeakSobolev_exists_smoothApprox_graph_l2_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    Nonempty
      (ScalarWeakSobolevSmoothApproxGraphL2Data
        (Metric.ball c r) w dw) := by
  exact euclideanSobolev_smooth_graph_density_l2_on_ball
    hr_pos hΩ_open hballΩ hweak hw hdw

/--
%%handwave
name:
  Radial segment-integral measurability from graph approximation
statement:
  The smooth radial derivative segment-integrals and the weak-derivative
  radial segment-integral are almost everywhere strongly measurable on the
  ball.
proof:
  For smooth approximants, the integrands are measurable by continuity in the
  space variable and measurability of the radial segment map.  For the weak
  derivative, compose the almost everywhere strongly measurable derivative
  field with the radial segment map and integrate over the unit interval.
-/
theorem scalarWeakSobolev_radialSmoothApprox_segmentIntegral_meas_on_ball_of_graph
    {c : H} {r a : ℝ}
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hgraph :
      ScalarWeakSobolevSmoothApproxGraphL2Data
        (Metric.ball c r) w dw) :
    (∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (hgraph.approximants n)
              (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume)
        (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
      AEStronglyMeasurable
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            dw (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume)
        (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  let T : H × ℝ → H := fun p ↦ c + (a + p.2 * (1 - a)) • (p.1 - c)
  let V : H × ℝ → H := fun p ↦ (1 - a) • (p.1 - c)
  have hT_qmp :
      Measure.QuasiMeasurePreserving T (μB.prod μI) μB := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_left
      (τ := μB) ?_ ?_
    · dsimp [T]
      fun_prop
    · filter_upwards [ae_restrict_mem
        (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))] with t ht
      let s : ℝ := a + t * (1 - a)
      have h1a_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha_le_one
      have hs_pos : 0 < s := by
        dsimp [s]
        have ht_nonneg : 0 ≤ t := ht.1
        have hprod_nonneg : 0 ≤ t * (1 - a) :=
          mul_nonneg ht_nonneg h1a_nonneg
        linarith
      have hs_le_one : s ≤ 1 := by
        dsimp [s]
        have ht_le_one : t ≤ 1 := ht.2
        have hprod_le : t * (1 - a) ≤ 1 * (1 - a) :=
          mul_le_mul_of_nonneg_right ht_le_one h1a_nonneg
        linarith
      simpa [T, μB, s] using
        euclideanRadialHomothety_quasiMeasurePreserving_restrict_ball
           (c := c) (r := r) (s := s) hs_pos hs_le_one
  have hV_cont : Continuous V := by
    dsimp [V]
    fun_prop
  have hV_ae : AEStronglyMeasurable V (μB.prod μI) :=
    hV_cont.aestronglyMeasurable
  have hEval_cont :
      Continuous (fun q : (H →L[ℝ] ℝ) × H ↦ q.1 q.2) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := H) (F := ℝ)).continuous
  refine ⟨?_, ?_⟩
  · intro n
    let F : H × ℝ → ℝ :=
      fun p ↦
        fderiv ℝ (hgraph.approximants n) (T p) (V p)
    have hD_cont :
        Continuous (fun z : H ↦ fderiv ℝ (hgraph.approximants n) z) :=
      (hgraph.smooth n).continuous_fderiv (by simp)
    have hD_comp :
        AEStronglyMeasurable
          (fun p : H × ℝ ↦ fderiv ℝ (hgraph.approximants n) (T p))
          (μB.prod μI) := by
      exact (hD_cont.comp (by dsimp [T]; fun_prop)).aestronglyMeasurable
    have hF : AEStronglyMeasurable F (μB.prod μI) := by
      simpa [F] using
        hEval_cont.comp_aestronglyMeasurable (hD_comp.prodMk hV_ae)
    have hInt :
        AEStronglyMeasurable
          (fun z : H ↦ ∫ t, F (z, t) ∂μI) μB :=
      hF.integral_prod_right'
    simpa [F, T, V, μB, μI] using hInt
  · let e0 : H → H →L[ℝ] ℝ :=
      fun z ↦ fderiv ℝ (hgraph.approximants 0) z - dw z
    have hD0_cont :
        Continuous (fun z : H ↦ fderiv ℝ (hgraph.approximants 0) z) :=
      (hgraph.smooth 0).continuous_fderiv (by simp)
    have hD0_meas :
        AEStronglyMeasurable
          (fun z : H ↦ fderiv ℝ (hgraph.approximants 0) z) μB :=
      hD0_cont.aestronglyMeasurable
    have he0_meas : AEStronglyMeasurable e0 μB := by
      simpa [e0, μB] using
        (hgraph.derivative_error_memLp 0).aestronglyMeasurable
    have hdw_meas : AEStronglyMeasurable dw μB := by
      refine (hD0_meas.sub he0_meas).congr ?_
      exact Filter.Eventually.of_forall fun z ↦ by simp [e0]
    let F : H × ℝ → ℝ :=
      fun p ↦ dw (T p) (V p)
    have hdw_comp :
        AEStronglyMeasurable (fun p : H × ℝ ↦ dw (T p)) (μB.prod μI) := by
      simpa [Function.comp_def] using
        hdw_meas.comp_quasiMeasurePreserving hT_qmp
    have hF : AEStronglyMeasurable F (μB.prod μI) := by
      simpa [F] using
        hEval_cont.comp_aestronglyMeasurable (hdw_comp.prodMk hV_ae)
    have hInt :
        AEStronglyMeasurable
          (fun z : H ↦ ∫ t, F (z, t) ∂μI) μB :=
      hF.integral_prod_right'
    simpa [F, T, V, μB, μI] using hInt

/--
%%handwave
name:
  Derivative errors are integrable on almost every radial segment
statement:
  For smooth graph-norm approximants, the derivative-field error restricted
  to the radial segment from \(c+a(z-c)\) to \(z\), applied to the segment
  velocity, is integrable in the segment parameter for almost every
  \(z\in B(c,r)\).
proof:
  Pull the derivative-field error back to \(B(c,r)\times[0,1]\) along the
  radial segment map.  The radial \(L^2\) estimate for this pullback and
  finite measure of the product imply \(L^1\)-integrability on the product,
  and Fubini gives integrability on almost every vertical segment.
-/
theorem scalarWeakSobolev_radialSmoothApprox_derivativeError_integrable_ae_of_graph
    {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hgraph :
      ScalarWeakSobolevSmoothApproxGraphL2Data
        (Metric.ball c r) w dw)
    (n : ℕ) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball c r),
      Integrable
        (fun t : ℝ ↦
          (fderiv ℝ (hgraph.approximants n)
              (c + (a + t * (1 - a)) • (z - c)) -
            dw (c + (a + t * (1 - a)) • (z - c)))
            ((1 - a) • (z - c)))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let B : Set H := Metric.ball c r
  let μB : Measure H := MeasureTheory.volume.restrict B
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  let e : H → H →L[ℝ] ℝ :=
    fun y ↦ fderiv ℝ (hgraph.approximants n) y - dw y
  let C : ℝ := (1 - a) * r
  let J : ℝ≥0∞ := ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|
  let F : H → ℝ≥0∞ := fun y ↦ ‖e y‖ₑ ^ (2 : ℝ)
  let T : H × ℝ → H := fun p ↦ c + (a + p.2 * (1 - a)) • (p.1 - c)
  let V : H × ℝ → H := fun p ↦ (1 - a) • (p.1 - c)
  let g : H × ℝ → ℝ := fun p ↦ e (T p) (V p)
  letI : IsFiniteMeasure μB := by
    dsimp [μB, B]
    exact isFiniteMeasure_restrict.2
      (measure_ball_ne_top (μ := (MeasureTheory.volume : Measure H)))
  letI : IsFiniteMeasure μI := ⟨by simp [μI, Real.volume_Icc]⟩
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (sub_nonneg.mpr ha_le_one) hr_pos.le
  have he_mem : MemLp e 2 μB := by
    simpa [e, μB, B] using hgraph.derivative_error_memLp n
  have hF_ae : AEMeasurable F μB := by
    exact he_mem.aestronglyMeasurable.enorm.pow_const _
  have hT_qmp :
      Measure.QuasiMeasurePreserving T (μB.prod μI) μB := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_left
      (τ := μB) ?_ ?_
    · dsimp [T]
      fun_prop
    · filter_upwards [ae_restrict_mem
        (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))] with t ht
      let s : ℝ := a + t * (1 - a)
      have h1a_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha_le_one
      have ht_nonneg : 0 ≤ t := ht.1
      have ht_le_one : t ≤ 1 := ht.2
      have hs_pos : 0 < s := by
        dsimp [s]
        have hprod_nonneg : 0 ≤ t * (1 - a) :=
          mul_nonneg ht_nonneg h1a_nonneg
        linarith
      have hs_le_one : s ≤ 1 := by
        dsimp [s]
        have hprod_le : t * (1 - a) ≤ 1 * (1 - a) :=
          mul_le_mul_of_nonneg_right ht_le_one h1a_nonneg
        linarith
      simpa [T, μB, s] using
        euclideanRadialHomothety_quasiMeasurePreserving_restrict_ball
           (c := c) (r := r) (s := s) hs_pos hs_le_one
  have he_comp :
      AEStronglyMeasurable (fun p : H × ℝ ↦ e (T p)) (μB.prod μI) := by
    simpa [Function.comp_def] using
      he_mem.aestronglyMeasurable.comp_quasiMeasurePreserving hT_qmp
  have hV_cont : Continuous V := by
    dsimp [V]
    fun_prop
  have hV_ae : AEStronglyMeasurable V (μB.prod μI) :=
    hV_cont.aestronglyMeasurable
  have hEval_cont :
      Continuous (fun q : (H →L[ℝ] ℝ) × H ↦ q.1 q.2) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := H) (F := ℝ)).continuous
  have hg_ae : AEStronglyMeasurable g (μB.prod μI) := by
    simpa [g] using
      hEval_cont.comp_aestronglyMeasurable (he_comp.prodMk hV_ae)
  have hgsq_ae :
      AEMeasurable (fun p : H × ℝ ↦ ‖g p‖ₑ ^ (2 : ℝ)) (μB.prod μI) :=
    hg_ae.enorm.pow_const _
  have hslice_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∫⁻ z, ‖g (z, t)‖ₑ ^ (2 : ℝ) ∂μB ≤
          (ENNReal.ofReal (C ^ 2) * J) *
            ∫⁻ z, F z ∂μB := by
    intro t ht
    let s : ℝ := a + t * (1 - a)
    have h1a_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha_le_one
    have ht_nonneg : 0 ≤ t := ht.1
    have ht_le_one : t ≤ 1 := ht.2
    have hs_pos : 0 < s := by
      dsimp [s]
      have hprod_nonneg : 0 ≤ t * (1 - a) :=
        mul_nonneg ht_nonneg h1a_nonneg
      linarith
    have hs_le_one : s ≤ 1 := by
      dsimp [s]
      have hprod_le : t * (1 - a) ≤ 1 * (1 - a) :=
        mul_le_mul_of_nonneg_right ht_le_one h1a_nonneg
      linarith
    have ha_le_s : a ≤ s := by
      dsimp [s]
      have hprod_nonneg : 0 ≤ t * (1 - a) :=
        mul_nonneg ht_nonneg h1a_nonneg
      linarith
    have hJs_le :
        ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| ≤ J := by
      have hinv_le : (s ^ Module.finrank ℝ H)⁻¹ ≤
          (a ^ Module.finrank ℝ H)⁻¹ := by
        have hpow : a ^ Module.finrank ℝ H ≤ s ^ Module.finrank ℝ H :=
          pow_le_pow_left₀ ha_pos.le ha_le_s _
        exact inv_anti₀ (pow_pos ha_pos _) hpow
      have hs_inv_nonneg : 0 ≤ (s ^ Module.finrank ℝ H)⁻¹ := by positivity
      have ha_inv_nonneg : 0 ≤ (a ^ Module.finrank ℝ H)⁻¹ := by positivity
      dsimp [J]
      rw [abs_of_nonneg hs_inv_nonneg, abs_of_nonneg ha_inv_nonneg]
      exact ENNReal.ofReal_le_ofReal hinv_le
    have hpoint_slice :
        ∀ᵐ z ∂μB,
          ‖g (z, t)‖ₑ ^ (2 : ℝ) ≤
            ENNReal.ofReal (C ^ 2) * F (c + s • (z - c)) := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hzB
      have hzdist : dist z c < r := by
        simpa [B, Metric.mem_ball] using hzB
      have hzc_norm : ‖z - c‖ ≤ r := by
        rw [← dist_eq_norm]
        exact hzdist.le
      have hvel_norm : ‖(1 - a) • (z - c)‖ ≤ C := by
        calc
          ‖(1 - a) • (z - c)‖ = (1 - a) * ‖z - c‖ := by
            simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg h1a_nonneg]
          _ ≤ (1 - a) * r :=
            mul_le_mul_of_nonneg_left hzc_norm h1a_nonneg
          _ = C := by simp [C]
      have h_apply_norm :
          ‖e (c + s • (z - c)) ((1 - a) • (z - c))‖ ≤
            C * ‖e (c + s • (z - c))‖ := by
        calc
          ‖e (c + s • (z - c)) ((1 - a) • (z - c))‖
              ≤ ‖e (c + s • (z - c))‖ * ‖(1 - a) • (z - c)‖ :=
                (e (c + s • (z - c))).le_opNorm ((1 - a) • (z - c))
          _ ≤ ‖e (c + s • (z - c))‖ * C :=
                mul_le_mul_of_nonneg_left hvel_norm
                  (norm_nonneg (e (c + s • (z - c))))
          _ = C * ‖e (c + s • (z - c))‖ := by ring
      have h_apply_abs :
          |e (c + s • (z - c)) ((1 - a) • (z - c))| ≤
            C * ‖e (c + s • (z - c))‖ := by
        simpa [Real.norm_eq_abs] using h_apply_norm
      have hsq_abs :
          |g (z, t)| ^ 2 ≤ C ^ 2 * ‖e (c + s • (z - c))‖ ^ 2 := by
        dsimp [g, T, V, s]
        nlinarith [h_apply_abs, abs_nonneg
          (e (c + s • (z - c)) ((1 - a) • (z - c))),
          norm_nonneg (e (c + s • (z - c))), hC_nonneg]
      have hsq_real :
          (g (z, t)) ^ 2 ≤ C ^ 2 * ‖e (c + s • (z - c))‖ ^ 2 := by
        simpa [sq_abs] using hsq_abs
      calc
        ‖g (z, t)‖ₑ ^ (2 : ℝ)
            = ENNReal.ofReal ((g (z, t)) ^ 2) := by
                exact real_enorm_rpow_two_eq_ofReal_sq (g (z, t))
        _ ≤ ENNReal.ofReal (C ^ 2 * ‖e (c + s • (z - c))‖ ^ 2) :=
              ENNReal.ofReal_le_ofReal hsq_real
        _ = ENNReal.ofReal (C ^ 2) *
              ENNReal.ofReal (‖e (c + s • (z - c))‖ ^ 2) := by
              rw [ENNReal.ofReal_mul]
              positivity
        _ = ENNReal.ofReal (C ^ 2) * F (c + s • (z - c)) := by
              simp [F]
    have hcomp :
        ∫⁻ z in Metric.ball c r, F (c + s • (z - c)) ∂MeasureTheory.volume ≤
          ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| *
            ∫⁻ z in Metric.ball c r, F z ∂MeasureTheory.volume :=
      euclideanRadialHomothety_lintegral_comp_le
         (c := c) (r := r) (s := s) hs_pos hs_le_one hF_ae
    calc
      ∫⁻ z, ‖g (z, t)‖ₑ ^ (2 : ℝ) ∂μB
          ≤ ∫⁻ z, ENNReal.ofReal (C ^ 2) * F (c + s • (z - c)) ∂μB :=
            lintegral_mono_ae hpoint_slice
      _ = ENNReal.ofReal (C ^ 2) *
            ∫⁻ z, F (c + s • (z - c)) ∂μB := by
            rw [lintegral_const_mul']
            simp
      _ ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal |(s ^ Module.finrank ℝ H)⁻¹| *
              ∫⁻ z, F z ∂μB) :=
            mul_le_mul_right (by simpa [μB, B] using hcomp) _
      _ ≤ ENNReal.ofReal (C ^ 2) *
            (J * ∫⁻ z, F z ∂μB) := by
            exact mul_le_mul_right
              (mul_le_mul_left hJs_le (∫⁻ z, F z ∂μB)) _
      _ = (ENNReal.ofReal (C ^ 2) * J) *
            ∫⁻ z, F z ∂μB := by
            ac_rfl
  have hprod_le :
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μB.prod μI ≤
        (ENNReal.ofReal (C ^ 2) * J) *
          ∫⁻ z, F z ∂μB := by
    calc
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μB.prod μI
          = ∫⁻ z, ∫⁻ t, ‖g (z, t)‖ₑ ^ (2 : ℝ) ∂μI ∂μB := by
            exact lintegral_prod
              (fun p : H × ℝ ↦ ‖g p‖ₑ ^ (2 : ℝ)) hgsq_ae
      _ = ∫⁻ t, ∫⁻ z, ‖g (z, t)‖ₑ ^ (2 : ℝ) ∂μB ∂μI := by
            exact MeasureTheory.lintegral_lintegral_swap
              (μ := μB) (ν := μI)
              (f := fun z t ↦ ‖g (z, t)‖ₑ ^ (2 : ℝ)) hgsq_ae
      _ = ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ∫⁻ z, ‖g (z, t)‖ₑ ^ (2 : ℝ) ∂μB ∂MeasureTheory.volume := by
          simp [μI]
      _ ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1,
          (ENNReal.ofReal (C ^ 2) * J) *
            ∫⁻ z, F z ∂μB ∂MeasureTheory.volume :=
          setLIntegral_mono' measurableSet_Icc hslice_bound
      _ = (ENNReal.ofReal (C ^ 2) * J) *
          ∫⁻ z, F z ∂μB := by
          simp [Real.volume_Icc]
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.coe_ne_top
  have he_sq_lt_top :
      ∫⁻ z, ‖e z‖ₑ ^ (2 : ℝ) ∂μB < (∞ : ℝ≥0∞) := by
    have he_norm := he_mem.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top] at he_norm
    exact
      (ENNReal.rpow_lt_top_iff_of_pos
        (by norm_num : 0 < (1 : ℝ) / 2)).1 (by simpa using he_norm)
  have hconst_lt_top :
      (ENNReal.ofReal (C ^ 2) * J) < (∞ : ℝ≥0∞) := by
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hprod_lt_top :
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μB.prod μI < (∞ : ℝ≥0∞) := by
    exact hprod_le.trans_lt (ENNReal.mul_lt_top hconst_lt_top he_sq_lt_top)
  have hg_mem_two : MemLp g 2 (μB.prod μI) := by
    refine ⟨hg_ae, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hprod_lt_top.ne
  have hg_mem_one : MemLp g 1 (μB.prod μI) :=
    hg_mem_two.mono_exponent (by norm_num)
  have hg_int : Integrable g (μB.prod μI) := by
    simpa using (memLp_one_iff_integrable.mp hg_mem_one)
  simpa [B, μB, μI, e, T, V, g] using hg_int.prod_right_ae

/--
%%handwave
name:
  Signed radial segment-integral error is bounded by the absolute error
statement:
  For smooth graph-norm approximants, the norm of the difference between the
  smooth radial derivative segment-integral and the weak-derivative radial
  segment-integral is bounded almost everywhere by the radial integral of the
  pointwise derivative-field error.
proof:
  For almost every radial segment, the derivative-field error is integrable
  along the segment.  Subtract the two interval integrals, identify the result
  with the integral of the difference, and apply the norm-of-integral
  inequality.
-/
theorem scalarWeakSobolev_radialSmoothApprox_segmentIntegral_error_norm_le_of_graph
    {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hgraph :
      ScalarWeakSobolevSmoothApproxGraphL2Data
        (Metric.ball c r) w dw)
    (n : ℕ) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball c r),
      ‖((fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              fderiv ℝ (hgraph.approximants n)
                (c + (a + t * (1 - a)) • (z - c))
                ((1 - a) • (z - c)) ∂MeasureTheory.volume) -
          fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              dw (c + (a + t * (1 - a)) • (z - c))
                ((1 - a) • (z - c)) ∂MeasureTheory.volume) z‖ ≤
        euclideanRadialContractionGradientSegmentIntegral
          (fun y ↦ fderiv ℝ (hgraph.approximants n) y - dw y) c a z := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  have he_int_ae :
      ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball c r),
        Integrable
          (fun t : ℝ ↦
            (fderiv ℝ (hgraph.approximants n)
                (c + (a + t * (1 - a)) • (z - c)) -
              dw (c + (a + t * (1 - a)) • (z - c)))
              ((1 - a) • (z - c))) μI := by
    simpa [μI] using
      scalarWeakSobolev_radialSmoothApprox_derivativeError_integrable_ae_of_graph
        hr_pos ha_pos ha_le_one hgraph n
  filter_upwards [he_int_ae] with z he_int
  let γ : ℝ → H := fun t ↦ c + (a + t * (1 - a)) • (z - c)
  let v : H := (1 - a) • (z - c)
  let S : ℝ → ℝ := fun t ↦ fderiv ℝ (hgraph.approximants n) (γ t) v
  let W : ℝ → ℝ := fun t ↦ dw (γ t) v
  let E : ℝ → ℝ := fun t ↦
    (fderiv ℝ (hgraph.approximants n) (γ t) - dw (γ t)) v
  have hS_cont : Continuous S := by
    have hD_cont :
        Continuous (fun y : H ↦ fderiv ℝ (hgraph.approximants n) y v) :=
      ((hgraph.smooth n).continuous_fderiv (by simp)).clm_apply
        (continuous_const : Continuous fun _ : H ↦ v)
    have hγ_cont : Continuous γ := by
      dsimp [γ]
      fun_prop
    exact hD_cont.comp hγ_cont
  have hS_int : Integrable S μI := by
    simpa [S, μI, IntegrableOn] using
      (hS_cont.integrableOn_Icc (a := (0 : ℝ)) (b := 1))
  have hE_int : Integrable E μI := by
    simpa [E, γ, v, μI] using he_int
  have hW_int : Integrable W μI := by
    have hSE := hS_int.sub hE_int
    refine hSE.congr ?_
    exact Filter.Eventually.of_forall fun t ↦ by
      simp [S, W, E, ContinuousLinearMap.sub_apply]
  have hdiff :
      (∫ t, S t ∂μI) - ∫ t, W t ∂μI =
        ∫ t, E t ∂μI := by
    have hsub := integral_sub (μ := μI) hS_int hW_int
    calc
      (∫ t, S t ∂μI) - ∫ t, W t ∂μI
          = ∫ t, S t - W t ∂μI := hsub.symm
      _ = ∫ t, E t ∂μI := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t ↦ by
            simp [S, W, E, ContinuousLinearMap.sub_apply]
  calc
    ‖((fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (hgraph.approximants n)
              (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume) -
        fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            dw (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume) z‖
        = ‖∫ t, E t ∂μI‖ := by
            simpa [S, W, E, γ, v, μI, Pi.sub_apply] using congrArg norm hdiff
    _ ≤ ∫ t, ‖E t‖ ∂μI :=
        norm_integral_le_integral_norm
          (μ := μI) (f := E)
    _ =
        euclideanRadialContractionGradientSegmentIntegral
          (fun y ↦ fderiv ℝ (hgraph.approximants n) y - dw y) c a z := by
        simp [euclideanRadialContractionGradientSegmentIntegral, E, γ, v, μI]

/--
%%handwave
name:
  Radial segment-integral error is \(L^2\)-controlled by graph derivative error
statement:
  For smooth graph-norm approximants and \(0<a\le1\), there is a finite
  constant depending only on the ball and on \(a\) such that the
  \(L^2(B(c,r))\)-norm of the radial segment-integral error is bounded by that
  constant times the \(L^2(B(c,r))\)-norm of the full derivative-field error.
proof:
  Combine the almost-everywhere signed-error bound with the radial
  segment-integral \(L^2\) estimate for the absolute derivative-field error.
-/
theorem scalarWeakSobolev_radialSmoothApprox_segmentIntegral_error_eLpNorm_le_of_graph
    {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hgraph :
      ScalarWeakSobolevSmoothApproxGraphL2Data
        (Metric.ball c r) w dw) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ n : ℕ,
        eLpNorm
          ((fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                fderiv ℝ (hgraph.approximants n)
                  (c + (a + t * (1 - a)) • (z - c))
                  ((1 - a) • (z - c)) ∂MeasureTheory.volume) -
            fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                dw (c + (a + t * (1 - a)) • (z - c))
                  ((1 - a) • (z - c)) ∂MeasureTheory.volume)
          2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
        ENNReal.ofReal A *
        eLpNorm (fun z ↦ fderiv ℝ (hgraph.approximants n) z - dw z)
            2 (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  rcases euclideanRadialContractionGradientSegmentIntegral_eLpNorm_le
       (c := c) (r := r) (a := a) hr_pos ha_pos ha_le_one with
    ⟨A, hA_nonneg, hsegment_l2⟩
  refine ⟨A, hA_nonneg, ?_⟩
  intro n
  have hpoint :
      ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball c r),
        ‖((fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                fderiv ℝ (hgraph.approximants n)
                  (c + (a + t * (1 - a)) • (z - c))
                  ((1 - a) • (z - c)) ∂MeasureTheory.volume) -
            fun z ↦
              ∫ t in Set.Icc (0 : ℝ) 1,
                dw (c + (a + t * (1 - a)) • (z - c))
                  ((1 - a) • (z - c)) ∂MeasureTheory.volume) z‖ ≤
          euclideanRadialContractionGradientSegmentIntegral
            (fun y ↦ fderiv ℝ (hgraph.approximants n) y - dw y) c a z :=
    scalarWeakSobolev_radialSmoothApprox_segmentIntegral_error_norm_le_of_graph
      hr_pos ha_pos ha_le_one hgraph n
  exact (eLpNorm_mono_ae_real hpoint).trans
    (hsegment_l2 (by simpa using hgraph.derivative_error_memLp n))

/--
%%handwave
name:
  Graph-norm derivative convergence gives radial segment-integral convergence
statement:
  If smooth approximants converge to a weak Sobolev function in the derivative
  part of the \(L^2\) graph norm on \(B(c,r)\), then their radial
  derivative segment-integrals converge in \(L^2(B(c,r))\) to the corresponding
  weak-derivative segment-integral, for every \(0<a\le1\).
proof:
  Subtract the two segment integrals and bound the signed error by the radial
  integral of the pointwise derivative-field error.  The radial
  segment-integral \(L^2\) estimate controls this by the \(L^2(B(c,r))\)-norm
  of the full derivative error, which tends to zero by graph-norm convergence.
-/
theorem scalarWeakSobolev_radialSmoothApprox_segmentIntegral_l2_on_ball_of_graph
    {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hgraph :
      ScalarWeakSobolevSmoothApproxGraphL2Data
        (Metric.ball c r) w dw) :
    (∀ n : ℕ,
      AEStronglyMeasurable
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            fderiv ℝ (hgraph.approximants n)
              (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume)
        (MeasureTheory.volume.restrict (Metric.ball c r))) ∧
      AEStronglyMeasurable
        (fun z ↦
          ∫ t in Set.Icc (0 : ℝ) 1,
            dw (c + (a + t * (1 - a)) • (z - c))
              ((1 - a) • (z - c)) ∂MeasureTheory.volume)
        (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z ↦
                ∫ t in Set.Icc (0 : ℝ) 1,
                  fderiv ℝ (hgraph.approximants n)
                    (c + (a + t * (1 - a)) • (z - c))
                    ((1 - a) • (z - c)) ∂MeasureTheory.volume) -
              fun z ↦
                ∫ t in Set.Icc (0 : ℝ) 1,
                  dw (c + (a + t * (1 - a)) • (z - c))
                    ((1 - a) • (z - c)) ∂MeasureTheory.volume)
            2 (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 0) := by
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  rcases scalarWeakSobolev_radialSmoothApprox_segmentIntegral_meas_on_ball_of_graph
      ha_pos ha_le_one hgraph with
    ⟨hintegral_meas, hintegral_lim_meas⟩
  refine ⟨hintegral_meas, hintegral_lim_meas, ?_⟩
  rcases scalarWeakSobolev_radialSmoothApprox_segmentIntegral_error_eLpNorm_le_of_graph
      hr_pos ha_pos ha_le_one hgraph with
    ⟨A, _hA_nonneg, herror_bound⟩
  have hmul :
      Filter.Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal A *
            eLpNorm (fun z ↦ fderiv ℝ (hgraph.approximants n) z - dw z)
              2 μB)
        Filter.atTop (𝓝 0) := by
    have hmul' :=
      ENNReal.Tendsto.const_mul
        (by simpa [μB] using hgraph.derivative_tendsto_l2)
        (Or.inr (show ENNReal.ofReal A ≠ (∞ : ℝ≥0∞) from ENNReal.ofReal_ne_top))
    have hzero : ENNReal.ofReal A * 0 = 0 := by
      exact mul_zero (ENNReal.ofReal A)
    simpa [μB, hzero] using hmul'
  rw [ENNReal.tendsto_atTop_zero] at hmul ⊢
  intro ε hε
  rcases hmul ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbn :
      eLpNorm
        ((fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              fderiv ℝ (hgraph.approximants n)
                (c + (a + t * (1 - a)) • (z - c))
                ((1 - a) • (z - c)) ∂MeasureTheory.volume) -
          fun z ↦
            ∫ t in Set.Icc (0 : ℝ) 1,
              dw (c + (a + t * (1 - a)) • (z - c))
                ((1 - a) • (z - c)) ∂MeasureTheory.volume)
        2 μB ≤
      ENNReal.ofReal A *
        eLpNorm (fun z ↦ fderiv ℝ (hgraph.approximants n) z - dw z)
          2 μB := by
    simpa [μB] using herror_bound n
  exact hbn.trans (hN n hn)

/--
%%handwave
name:
  Smooth radial \(L^2\) approximation on a ball
statement:
  Let \(B(c,r)\subset\Omega\), with \(r>0\), and let \(0<a\le1\).  A scalar
  weak \(W^{1,2}\) function on \(\Omega\), with square-integrable weak
  derivative on \(B(c,r)\), admits smooth approximants whose radial endpoint
  differences and radial segment-integrals converge in \(L^2(B(c,r))\).
proof:
  Choose smooth graph-norm approximants on the ball.  The endpoint estimate is
  obtained from the radial homothety pullback bound, and the segment-integral
  estimate from the radial \(L^2\) bound for integrating derivative errors
  along radial segments.
-/
theorem scalarWeakSobolev_exists_radial_contraction_smoothApprox_l2_on_ball
    {Ω : Set H} {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    Nonempty
      (ScalarWeakSobolevRadialSmoothApproxL2Data
        (Metric.ball c r) w dw c a) := by
  rcases scalarWeakSobolev_exists_smoothApprox_graph_l2_on_ball
      hr_pos hΩ_open hballΩ hweak hw hdw with
    ⟨hgraph⟩
  rcases scalarWeakSobolev_radialSmoothApprox_endpoint_l2_on_ball_of_graph
      ha_pos ha_le_one hgraph with
    ⟨hendpoint_meas, hendpoint_lim_meas, hendpoint_l2⟩
  rcases scalarWeakSobolev_radialSmoothApprox_segmentIntegral_l2_on_ball_of_graph
      hr_pos ha_pos ha_le_one hgraph with
    ⟨hintegral_meas, hintegral_lim_meas, hintegral_l2⟩
  exact
    ⟨{ approximants := hgraph.approximants
       smooth := hgraph.smooth
       endpoint_aestronglyMeasurable := hendpoint_meas
       endpoint_limit_aestronglyMeasurable := hendpoint_lim_meas
       endpoint_tendsto_l2 := hendpoint_l2
       integral_aestronglyMeasurable := hintegral_meas
       integral_limit_aestronglyMeasurable := hintegral_lim_meas
       integral_tendsto_l2 := hintegral_l2 }⟩

/--
%%handwave
name:
  Smooth radial approximation in measure on a ball
statement:
  Let \(B(c,r)\subset\Omega\), with \(r>0\), and let \(0<a\le1\).  A scalar
  weak \(W^{1,2}\) function on \(\Omega\), with square-integrable weak
  derivative on \(B(c,r)\), admits smooth approximants whose radial endpoint
  differences and radial segment-integrals converge in measure on \(B(c,r)\).
proof:
  This is the graph-norm approximation input for the radial argument.
  Endpoint convergence is transferred through the radial homothety using its
  \(L^2\) pullback bound.  Segment-integral convergence follows from the
  radial \(L^2\) estimate for derivative errors.
-/
theorem scalarWeakSobolev_exists_radial_contraction_smoothApprox_inMeasure_on_ball
    {Ω : Set H} {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    Nonempty
      (ScalarWeakSobolevRadialSmoothApproxInMeasureData
        (Metric.ball c r) w dw c a) := by
  rcases scalarWeakSobolev_exists_radial_contraction_smoothApprox_l2_on_ball
      hr_pos ha_pos ha_le_one hΩ_open hballΩ hweak hw hdw with
    ⟨happrox⟩
  exact ⟨scalarWeakSobolev_radial_smoothApproxInMeasureData_of_l2 happrox⟩

/--
%%handwave
name:
  Smooth radial approximation on a ball
statement:
  Let \(B(c,r)\subset\Omega\), with \(r>0\), and let \(0<a\le1\).  A scalar
  weak \(W^{1,2}\) function on \(\Omega\), with square-integrable weak
  derivative on \(B(c,r)\), admits smooth approximants whose endpoint
  differences and radial segment-integrals converge almost everywhere on
  \(B(c,r)\).
proof:
  Choose smooth graph-norm approximants on the ball.  Endpoint convergence is
  transferred through the radial homothety using its null-set preservation and
  \(L^2\) Jacobian bound.  Convergence of the segment integrals follows from
  the radial \(L^2\) estimate for segment integrals applied to the derivative
  errors, followed by passage from \(L^2\)-convergence to almost-everywhere
  convergence along a subsequence.
-/
theorem scalarWeakSobolev_exists_radial_contraction_smoothApprox_on_ball
    {Ω : Set H} {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    Nonempty
      (ScalarWeakSobolevRadialSmoothApproxData
        (Metric.ball c r) w dw c a) := by
  rcases scalarWeakSobolev_exists_radial_contraction_smoothApprox_inMeasure_on_ball
      hr_pos ha_pos ha_le_one hΩ_open hballΩ hweak hw hdw with
    ⟨happrox⟩
  exact scalarWeakSobolev_radial_smoothApproxData_of_tendstoInMeasure happrox

/--
%%handwave
name:
  Radial weak fundamental theorem on almost every segment
statement:
  Let \(B(c,r)\subset\Omega\), with \(r>0\), and let \(0<a\le1\).  For a
  scalar weak Sobolev function \(w\) on \(\Omega\), the difference between
  \(w(z)\) and \(w(c+a(z-c))\) is, for almost every \(z\in B(c,r)\), the
  integral of the weak derivative along the radial segment from \(c+a(z-c)\)
  to \(z\), applied to the segment velocity.
proof:
  Choose smooth radial approximation data and apply the classical fundamental
  theorem on each smooth approximating segment.  The almost-everywhere limits
  of the endpoint differences and segment integrals give the identity.
-/
theorem scalarWeakSobolev_radial_contraction_line_integral_eq_ae
    {Ω : Set H} {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball c r),
      w z - w (c + a • (z - c)) =
        ∫ t in Set.Icc (0 : ℝ) 1,
          dw (c + (a + t * (1 - a)) • (z - c)) ((1 - a) • (z - c))
            ∂MeasureTheory.volume := by
  exact
    scalarWeakSobolev_radial_contraction_line_integral_eq_ae_of_smoothApproxData
      (Classical.choice
        (scalarWeakSobolev_exists_radial_contraction_smoothApprox_on_ball
          hr_pos ha_pos ha_le_one hΩ_open hballΩ hweak hw hdw))

/--
%%handwave
name:
  Radial absolute-continuity estimate
statement:
  Let \(B(c,r)\subset\Omega\), with \(r>0\), and let \(0<a\le1\).  For a
  scalar weak Sobolev function \(w\) on \(\Omega\), the difference
  \(w(z)-w(c+a(z-c))\) is bounded for almost every \(z\in B(c,r)\) by the
  integral of \(|D w|\) along the radial segment from \(c+a(z-c)\) to \(z\),
  with the derivative applied to the segment velocity.
proof:
  Apply [the radial weak fundamental theorem on almost every segment](lean:JJMath.Uniformization.scalarWeakSobolev_radial_contraction_line_integral_eq_ae),
  then take absolute values and use the triangle inequality for the integral.
-/
theorem scalarWeakSobolev_radial_contraction_segmentIntegral_bound_ae
    {Ω : Set H} {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball c r),
      ‖w z - w (c + a • (z - c))‖ ≤
        euclideanRadialContractionGradientSegmentIntegral dw c a z := by
  have hline :
      ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball c r),
        w z - w (c + a • (z - c)) =
          ∫ t in Set.Icc (0 : ℝ) 1,
            dw (c + (a + t * (1 - a)) • (z - c)) ((1 - a) • (z - c))
              ∂MeasureTheory.volume :=
    scalarWeakSobolev_radial_contraction_line_integral_eq_ae
      hr_pos ha_pos ha_le_one hΩ_open hballΩ hweak hw hdw
  filter_upwards [hline] with z hz
  rw [hz]
  simpa [euclideanRadialContractionGradientSegmentIntegral] using
    (norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      (f := fun t : ℝ ↦
        dw (c + (a + t * (1 - a)) • (z - c)) ((1 - a) • (z - c))))

/--
%%handwave
name:
  Radial contraction differences are controlled by the gradient on a ball
statement:
  Let \(B(c,r)\subset\Omega\), with \(r>0\), and let \(0<a\le 1\). There is a
  finite constant \(A\) such that, for every scalar weak Sobolev function \(w\)
  on \(\Omega\), with weak derivative \(D w\), the \(L^2(B(c,r))\)-norm of
  \(w(z)-w(c+a(z-c))\) is at most \(A\|D w\|_{L^2(B(c,r))}\).
proof:
  Combine [the pointwise bound by the integral of the weak derivative along the radial segment](lean:JJMath.Uniformization.scalarWeakSobolev_radial_contraction_segmentIntegral_bound_ae)
  with [the \(L^2(B(c,r))\)-norm of this radial segment integral is controlled by the \(L^2(B(c,r))\)-norm of the weak derivative](lean:JJMath.Uniformization.euclideanRadialContractionGradientSegmentIntegral_eLpNorm_le).
-/
theorem euclideanSobolev_radial_contraction_difference_eLpNorm_le_gradient
    {Ω : Set H} {c : H} {r a : ℝ}
    (hr_pos : 0 < r)
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
        IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw →
        MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
        MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
        eLpNorm
          (fun z : H ↦ w z - w (c + a • (z - c))) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ENNReal.ofReal A *
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  rcases euclideanRadialContractionGradientSegmentIntegral_eLpNorm_le
       (c := c) (r := r) (a := a) hr_pos ha_pos ha_le_one with
    ⟨A, hA_nonneg, hsegment_l2⟩
  refine ⟨A, hA_nonneg, ?_⟩
  intro w dw hweak hw hdw
  have hpoint :
      ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball c r),
        ‖w z - w (c + a • (z - c))‖ ≤
          euclideanRadialContractionGradientSegmentIntegral dw c a z :=
    scalarWeakSobolev_radial_contraction_segmentIntegral_bound_ae
      hr_pos ha_pos ha_le_one hΩ_open hballΩ hweak hw hdw
  exact (eLpNorm_mono_ae_real hpoint).trans (hsegment_l2 hdw)

/--
%%handwave
name:
  Radial contraction differences are controlled by the weak gradient
statement:
  For each standard radial contraction of \(B(c,r)\), there is a finite
  constant \(A\) such that the \(L^2\)-norm of the difference between a scalar
  weak Sobolev function and its contracted pullback is at most
  \(A\|D w\|_{L^2(B(c,r))}\).
proof:
  Apply [the \(L^2(B(c,r))\)-norm of \(w(z)-w(c+a(z-c))\) is controlled by the \(L^2(B(c,r))\)-norm of the weak derivative for every \(0<a\le1\)](lean:JJMath.Uniformization.euclideanSobolev_radial_contraction_difference_eLpNorm_le_gradient)
  to the standard factor \(a=(k+1)/(k+2)\).
-/
theorem euclideanSobolev_standard_exhaustion_radial_contraction_difference_eLpNorm_le_gradient
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
        IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw →
        MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
        MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
        eLpNorm
          (fun z : H ↦
            w z -
              w (c + (((k : ℝ) + 1) / ((k : ℝ) + 2)) • (z - c))) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ENNReal.ofReal A *
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  let a : ℝ := ((k : ℝ) + 1) / ((k : ℝ) + 2)
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    exact div_le_one_of_le₀ (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2) (by positivity)
  simpa [a] using
    euclideanSobolev_radial_contraction_difference_eLpNorm_le_gradient
       (Ω := Ω) (c := c) (r := r) (a := a)
      hr_pos ha_pos ha_le_one hΩ_open hballΩ

/--
%%handwave
name:
  Radial contraction estimate with arbitrarily small Jacobian loss
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  For every \(\delta>0\), there is a standard compact subball and a finite
  constant \(A\) such that every scalar weak Sobolev function \(w\) satisfies
  \[
    \|w\|_{L^2(B(c,r))}
      \le
    (1+\delta)\,\|w\|_{L^2(\overline B(c,r(k+1)/(k+2)))}
      + A\,\|D w\|_{L^2(B(c,r))}.
  \]
proof:
  Contract the ball radially toward \(c\) so that its image is the chosen
  compact subball.  The change-of-variables factor is made at most
  \(1+\delta\) by choosing the contraction close enough to the identity.  The
  difference between \(w\) and its radial contraction is controlled by
  integrating the weak gradient along the radial segments.
-/
theorem euclideanSobolev_standard_exhaustion_tail_scaled_eLpNorm_le_compact_add_gradient
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω) :
    ∀ δ : ℝ, 0 < δ →
      ∃ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw →
          MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) →
          eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            ENNReal.ofReal (1 + δ) *
              eLpNorm w 2
                (MeasureTheory.volume.restrict
                  (Metric.closedBall c
                    (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) +
              ENNReal.ofReal A *
                eLpNorm dw 2
                  (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  intro δ hδ
  rcases
    euclideanSobolev_standard_exhaustion_radial_contraction_pullback_eLpNorm_le
       (c := c) (r := r) hr_pos δ hδ with
    ⟨k, hpullback⟩
  rcases
    euclideanSobolev_standard_exhaustion_radial_contraction_difference_eLpNorm_le_gradient
      hr_pos hΩ_open hballΩ k with
    ⟨A, hA_nonneg, hdifference⟩
  refine ⟨k, A, hA_nonneg, ?_⟩
  intro w dw hweak hwB hdwB hwK
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let μK : Measure H :=
    MeasureTheory.volume.restrict
      (Metric.closedBall c
        (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))
  let wc : H → ℝ :=
    fun z : H ↦ w (c + (((k : ℝ) + 1) / ((k : ℝ) + 2)) • (z - c))
  rcases hpullback (w := w) (by simpa [μK] using hwK) with
    ⟨hwc_meas, hpullback_bound⟩
  have hwB_meas : AEStronglyMeasurable w μB := by
    simpa [μB] using hwB.1
  have hwc_meas_μB : AEStronglyMeasurable wc μB := by
    simpa [μB, wc] using hwc_meas
  have hdiff_meas :
      AEStronglyMeasurable (fun z : H ↦ w z - wc z) μB := by
    exact hwB_meas.sub hwc_meas_μB
  have htriangle :
      eLpNorm w 2 μB ≤
        eLpNorm (fun z : H ↦ w z - wc z) 2 μB +
          eLpNorm wc 2 μB := by
    calc
      eLpNorm w 2 μB
          = eLpNorm (fun z : H ↦ (w z - wc z) + wc z) 2 μB := by
              refine (eLpNorm_congr_ae ?_).symm
              exact Filter.Eventually.of_forall fun z ↦ by simp
      _ ≤
          eLpNorm (fun z : H ↦ w z - wc z) 2 μB +
            eLpNorm wc 2 μB :=
              eLpNorm_add_le hdiff_meas hwc_meas_μB
                (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hdiff_bound :
      eLpNorm (fun z : H ↦ w z - wc z) 2 μB ≤
        ENNReal.ofReal A *
          eLpNorm dw 2 μB := by
    simpa [μB, wc] using hdifference hweak hwB hdwB
  calc
    eLpNorm w 2
        (MeasureTheory.volume.restrict (Metric.ball c r))
        = eLpNorm w 2 μB := by simp [μB]
    _ ≤
        eLpNorm (fun z : H ↦ w z - wc z) 2 μB +
          eLpNorm wc 2 μB := htriangle
    _ ≤
        ENNReal.ofReal A * eLpNorm dw 2 μB +
          ENNReal.ofReal (1 + δ) * eLpNorm w 2 μK :=
            add_le_add hdiff_bound (by simpa [μB, μK, wc] using hpullback_bound)
    _ =
        ENNReal.ofReal (1 + δ) * eLpNorm w 2 μK +
          ENNReal.ofReal A * eLpNorm dw 2 μB := by
            rw [add_comm]
    _ =
        ENNReal.ofReal (1 + δ) *
          eLpNorm w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) +
          ENNReal.ofReal A *
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) := by
            simp [μB, μK]

/--
%%handwave
name:
  The radial \(L^2\)-tail estimate in extended norm form
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  For every \(L^2\)-bound \(C<\infty\) and every \(\varepsilon>0\), there is a
  standard compact subball and a finite constant \(A\) such that every scalar
  weak Sobolev function \(w\) with \(\|w\|_{L^2(B(c,r))}\le C\) satisfies
  \[
    \|w\|_{L^2(B(c,r))}
      \le
    \|w\|_{L^2(\overline B(c,r(k+1)/(k+2)))}
      + A\,\|D w\|_{L^2(B(c,r))}+\varepsilon .
  \]
proof:
  Use radial segments from the outer annulus to the compact subball.  The
  segment fundamental theorem estimates the change of \(w\) along each fiber
  by the weak gradient, and the assumed \(L^2\)-bound controls the part of the
  annulus whose measure is made small by taking the subball sufficiently close
  to \(B(c,r)\).
-/
theorem euclideanSobolev_standard_exhaustion_tail_eLpNorm_le_compact_add_gradient
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {C : ℝ≥0∞} (hC_top : C < ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw →
          MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) →
          eLpNorm w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C →
          eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          eLpNorm w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) +
            ENNReal.ofReal A *
              eLpNorm dw 2
                (MeasureTheory.volume.restrict (Metric.ball c r)) +
            ENNReal.ofReal ε := by
  intro ε hε
  let δ : ℝ := ε / (C.toReal + 1)
  have hC_ne_top : C ≠ ⊤ := hC_top.ne
  have hC_toReal_nonneg : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hden_pos : 0 < C.toReal + 1 := by positivity
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact div_pos hε hden_pos
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hδC_le : δ * C.toReal ≤ ε := by
    have hratio_le_one : C.toReal / (C.toReal + 1) ≤ 1 := by
      exact div_le_one_of_le₀ (by linarith) hden_pos.le
    have hδC_eq : δ * C.toReal = ε * (C.toReal / (C.toReal + 1)) := by
      dsimp [δ]
      field_simp [hden_pos.ne']
    calc
      δ * C.toReal = ε * (C.toReal / (C.toReal + 1)) := hδC_eq
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio_le_one hε.le
      _ = ε := by ring
  rcases
    euclideanSobolev_standard_exhaustion_tail_scaled_eLpNorm_le_compact_add_gradient
      hr_pos hΩ_open hballΩ δ hδ_pos with
    ⟨k, A, hA_nonneg, hscaled⟩
  refine ⟨k, A, hA_nonneg, ?_⟩
  intro w dw hweak hwB hdwB hwK hw_bound
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let μK : Measure H :=
    MeasureTheory.volume.restrict
      (Metric.closedBall c
        (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))
  have hclosed_sub_ball :
      Metric.closedBall c (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))) ⊆
        Metric.ball c r :=
    euclideanSobolev_standard_exhaustion_closedBall_subset_ball hr_pos k
  have hμK_le : μK ≤ μB := by
    dsimp [μK, μB]
    exact Measure.restrict_mono hclosed_sub_ball le_rfl
  have hinner_le_C :
      eLpNorm w 2 μK ≤ C :=
    (eLpNorm_mono_measure w hμK_le).trans (by simpa [μB] using hw_bound)
  have hloss :
      ENNReal.ofReal (1 + δ) * eLpNorm w 2 μK ≤
        eLpNorm w 2 μK + ENNReal.ofReal ε :=
    ennreal_ofReal_one_add_mul_le_add_of_le
      hδ_nonneg hC_ne_top hinner_le_C hδC_le
  have hscaled' :
      eLpNorm w 2 μB ≤
        ENNReal.ofReal (1 + δ) * eLpNorm w 2 μK +
          ENNReal.ofReal A *
            eLpNorm dw 2 μB := by
    simpa [μB, μK] using hscaled hweak hwB hdwB hwK
  calc
    eLpNorm w 2
        (MeasureTheory.volume.restrict (Metric.ball c r))
        = eLpNorm w 2 μB := by simp [μB]
    _ ≤
        ENNReal.ofReal (1 + δ) * eLpNorm w 2 μK +
          ENNReal.ofReal A *
            eLpNorm dw 2 μB := hscaled'
    _ ≤
        (eLpNorm w 2 μK + ENNReal.ofReal ε) +
          ENNReal.ofReal A *
            eLpNorm dw 2 μB := add_le_add_left hloss _
    _ =
        eLpNorm w 2 μK +
          ENNReal.ofReal A *
            eLpNorm dw 2 μB +
          ENNReal.ofReal ε := by
            rw [add_assoc,
              add_comm (ENNReal.ofReal ε)
                (ENNReal.ofReal A * eLpNorm dw 2 μB),
              ← add_assoc]
    _ =
        eLpNorm w 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) +
            ENNReal.ofReal A *
              eLpNorm dw 2
                (MeasureTheory.volume.restrict (Metric.ball c r)) +
            ENNReal.ofReal ε := by
              simp [μB, μK]

/--
%%handwave
name:
  The \(L^2\)-tail is bounded by compact mass, gradient, and annular error
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  For every \(L^2\)-bound \(C<\infty\) and every \(\varepsilon>0\), there is a
  standard compact subball and a finite constant \(A\) such that every scalar
  weak Sobolev function \(w\) with \(\|w\|_{L^2(B(c,r))}\le C\) satisfies
  \[
    \|w\|_{L^2(B(c,r))}
      \le
    \|w\|_{L^2(\overline B(c,r(k+1)/(k+2)))}
      + A\,\|D w\|_{L^2(B(c,r))}+\varepsilon .
  \]
proof:
  Use a radial retraction from the thin outer annulus to the chosen compact
  subball.  The segment fundamental theorem controls the change along radial
  fibers by the weak gradient, while the \(L^2\)-bound controls the small
  measure error from the annular layer.  The Jacobian and segment-length
  constants are absorbed into \(A\).
-/
theorem euclideanSobolev_standard_exhaustion_tail_norm_le_compact_add_gradient
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {C : ℝ≥0∞} (hC_top : C < ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw →
          MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) →
          eLpNorm w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C →
          (eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball c r))).toReal ≤
          (eLpNorm w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))).toReal +
            A *
              (eLpNorm dw 2
                (MeasureTheory.volume.restrict (Metric.ball c r))).toReal +
            ε := by
  intro ε hε
  rcases
    euclideanSobolev_standard_exhaustion_tail_eLpNorm_le_compact_add_gradient
      hr_pos hΩ_open hballΩ hC_top ε hε with
    ⟨k, A, hA_nonneg, htail⟩
  refine ⟨k, A, hA_nonneg, ?_⟩
  intro w dw hweak hwB hdwB hwK hw_bound
  have htail' :=
    htail hweak hwB hdwB hwK hw_bound
  have hwK_ne_top :
      eLpNorm w 2
        (MeasureTheory.volume.restrict
          (Metric.closedBall c
            (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) ≠ ⊤ :=
    hwK.eLpNorm_lt_top.ne
  have hdw_ne_top :
      eLpNorm dw 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) ≠ ⊤ :=
    hdwB.eLpNorm_lt_top.ne
  have hgrad_ne_top :
      ENNReal.ofReal A *
          eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdwB.eLpNorm_lt_top).ne
  have hsum_ne_top :
      eLpNorm w 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) +
        ENNReal.ofReal A *
          eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hwK_ne_top, hgrad_ne_top⟩
  have hright_ne_top :
      eLpNorm w 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) +
          ENNReal.ofReal A *
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) +
        ENNReal.ofReal ε ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hsum_ne_top, ENNReal.ofReal_ne_top⟩
  calc
    (eLpNorm w 2
      (MeasureTheory.volume.restrict (Metric.ball c r))).toReal
        ≤
      (eLpNorm w 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) +
          ENNReal.ofReal A *
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) +
        ENNReal.ofReal ε).toReal :=
          ENNReal.toReal_mono hright_ne_top htail'
    _ =
      (eLpNorm w 2
        (MeasureTheory.volume.restrict
          (Metric.closedBall c
            (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))).toReal +
        A *
          (eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball c r))).toReal +
        ε := by
          rw [ENNReal.toReal_add hsum_ne_top ENNReal.ofReal_ne_top,
            ENNReal.toReal_add hwK_ne_top hgrad_ne_top, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal hA_nonneg, ENNReal.toReal_ofReal hε.le]

/--
%%handwave
name:
  Small gradients control the \(L^2\)-tail outside a standard subball
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  For every \(L^2\)-bound \(C<\infty\) and every \(\varepsilon>0\), there is a
  standard compact subball and a gradient threshold \(\eta>0\) such that any
  scalar weak Sobolev function \(w\) with
  \(\|w\|_{L^2(B(c,r))}\le C\) and
  \(\|D w\|_{L^2(B(c,r))}\le\eta\) satisfies
  \[
    \|w\|_{L^2(B(c,r))}
      \le
    \|w\|_{L^2(\overline B(c,r(k+1)/(k+2)))}+\varepsilon .
  \]
proof:
  Choose a standard compact subball with very thin complementary annulus.
  Push annular points inward along radial segments.  The segment fundamental
  theorem bounds the change of \(w\) along those segments by the weak
  gradient, while the global \(L^2\)-bound controls the small boundary layer
  created by the radial projection.  Taking the annulus thin and then the
  gradient threshold small gives the estimate.
-/
theorem euclideanSobolev_standard_exhaustion_tail_norm_control_of_gradientSmall
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {C : ℝ≥0∞} (hC_top : C < ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∃ η : ℝ, 0 < η ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw →
          MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))) →
          eLpNorm w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C →
          eLpNorm dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            ENNReal.ofReal η →
          (eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball c r))).toReal ≤
          (eLpNorm w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))).toReal + ε := by
  intro ε hε
  have hε_half : 0 < ε / 2 := half_pos hε
  rcases
    euclideanSobolev_standard_exhaustion_tail_norm_le_compact_add_gradient
      hr_pos hΩ_open hballΩ hC_top (ε / 2) hε_half with
    ⟨k, A, hA_nonneg, htail⟩
  let η : ℝ := ε / (2 * (A + 1))
  have hA_plus_pos : 0 < A + 1 := by linarith
  have hden_pos : 0 < 2 * (A + 1) := by positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    exact div_pos hε hden_pos
  refine ⟨k, η, hη_pos, ?_⟩
  intro w dw hweak hwB hdwB hwK hw_bound hdw_small
  have hdw_toReal_le :
      (eLpNorm dw 2
        (MeasureTheory.volume.restrict (Metric.ball c r))).toReal ≤ η := by
    have hmono :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hdw_small
    simpa [η, ENNReal.toReal_ofReal hη_pos.le] using hmono
  have hgrad_term_le :
      A *
          (eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball c r))).toReal ≤
        ε / 2 := by
    have hA_eta_le : A * η ≤ ε / 2 := by
      have hratio_le_one : A / (A + 1) ≤ 1 := by
        exact div_le_one_of_le₀ (by linarith) hA_plus_pos.le
      have hA_eta_eq : A * η = (ε / 2) * (A / (A + 1)) := by
        dsimp [η]
        field_simp [hA_plus_pos.ne']
      calc
        A * η = (ε / 2) * (A / (A + 1)) := hA_eta_eq
        _ ≤ (ε / 2) * 1 :=
              mul_le_mul_of_nonneg_left hratio_le_one hε_half.le
        _ = ε / 2 := by ring
    exact (mul_le_mul_of_nonneg_left hdw_toReal_le hA_nonneg).trans hA_eta_le
  have htail' :
      (eLpNorm w 2
        (MeasureTheory.volume.restrict (Metric.ball c r))).toReal ≤
      (eLpNorm w 2
        (MeasureTheory.volume.restrict
          (Metric.closedBall c
            (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))).toReal +
        A *
          (eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball c r))).toReal +
        ε / 2 :=
    htail hweak hwB hdwB hwK hw_bound
  nlinarith

/--
%%handwave
name:
  Pairwise tail control from uniformly small gradients
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  For every uniform \(L^2\)-bound \(C<\infty\) and every \(\varepsilon>0\),
  there is a standard compact subball and a gradient threshold \(\eta>0\)
  such that two scalar weak Sobolev functions whose \(L^2(B(c,r))\)-norms are
  at most \(C\), and whose weak-gradient \(L^2(B(c,r))\)-norms are at most
  \(\eta\), have their \(L^2(B(c,r))\)-distance bounded by their distance on
  that compact subball plus \(\varepsilon\).
proof:
  Apply the one-function tail estimate to the difference of the two
  functions.  The difference has the difference of the weak derivative fields
  as its weak derivative, its \(L^2\)-norm is bounded by the sum of the two
  given \(L^2\)-bounds, and its weak-gradient norm is bounded by the sum of
  the two small gradient norms.
-/
theorem euclideanSobolev_standard_exhaustion_pair_tail_control_of_uniformGradientSmall
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {C : ℝ≥0∞} (hC_top : C < ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∃ η : ℝ, 0 < η ∧
        ∀ {v w : H → ℝ} {dv dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues Ω v dv →
          IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw →
          (hvB : MemLp v 2
            (MeasureTheory.volume.restrict (Metric.ball c r))) →
          (hwB : MemLp w 2
            (MeasureTheory.volume.restrict (Metric.ball c r))) →
          MemLp dv 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) →
          (hvK : MemLp v 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))) →
          (hwK : MemLp w 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))) →
          eLpNorm v 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C →
          eLpNorm w 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C →
          eLpNorm dv 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            ENNReal.ofReal η →
          eLpNorm dw 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            ENNReal.ofReal η →
          dist
            ((hvB.toLp v :
              Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r))))
            ((hwB.toLp w :
              Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r)))) ≤
          dist
            ((hvK.toLp v :
              Lp ℝ 2
                (MeasureTheory.volume.restrict
                  (Metric.closedBall c
                    (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))))
            ((hwK.toLp w :
              Lp ℝ 2
                (MeasureTheory.volume.restrict
                  (Metric.closedBall c
                    (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))) + ε := by
  intro ε hε
  have hCsum_top : C + C < ⊤ := ENNReal.add_lt_top.2 ⟨hC_top, hC_top⟩
  rcases
    euclideanSobolev_standard_exhaustion_tail_norm_control_of_gradientSmall
      hr_pos hΩ_open hballΩ hCsum_top ε hε with
    ⟨k, η₀, hη₀_pos, htail⟩
  refine ⟨k, η₀ / 2, half_pos hη₀_pos, ?_⟩
  intro v w dv dw hweak_v hweak_w hvB hwB hdvB hdwB hvK hwK
    hv_bound hw_bound hdv_small hdw_small
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  let μK : Measure H :=
    MeasureTheory.volume.restrict
      (Metric.closedBall c (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))
  let f : H → ℝ := fun z ↦ v z - w z
  let df : H → H →L[ℝ] ℝ := fun z ↦ dv z - dw z
  have hfweak :
      IsWeakDerivativeOnEuclideanRegionWithValues Ω f df := by
    simpa [f, df] using hweak_v.sub hweak_w
  have hfB : MemLp f 2 μB := by
    simpa [f, μB] using hvB.sub hwB
  have hdfB : MemLp df 2 μB := by
    simpa [df, μB] using hdvB.sub hdwB
  have hfK : MemLp f 2 μK := by
    simpa [f, μK] using hvK.sub hwK
  have hf_bound :
      eLpNorm f 2 μB ≤ C + C := by
    calc
      eLpNorm f 2 μB
          ≤ eLpNorm v 2 μB + eLpNorm w 2 μB := by
            simpa [f, μB] using
              (eLpNorm_sub_le
                (μ := μB) (p := (2 : ℝ≥0∞))
                hvB.aestronglyMeasurable hwB.aestronglyMeasurable
                (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      _ ≤ C + C := add_le_add
            (by simpa [μB] using hv_bound)
            (by simpa [μB] using hw_bound)
  have hdf_small :
      eLpNorm df 2 μB ≤ ENNReal.ofReal η₀ := by
    have hhalf_nonneg : 0 ≤ η₀ / 2 := (half_pos hη₀_pos).le
    calc
      eLpNorm df 2 μB
          ≤ eLpNorm dv 2 μB + eLpNorm dw 2 μB := by
            simpa [df, μB] using
              (eLpNorm_sub_le
                (μ := μB) (p := (2 : ℝ≥0∞))
                hdvB.aestronglyMeasurable hdwB.aestronglyMeasurable
                (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      _ ≤ ENNReal.ofReal (η₀ / 2) + ENNReal.ofReal (η₀ / 2) :=
            add_le_add
              (by simpa [μB] using hdv_small)
              (by simpa [μB] using hdw_small)
      _ = ENNReal.ofReal η₀ := by
            rw [← ENNReal.ofReal_add hhalf_nonneg hhalf_nonneg]
            congr 1
            ring
  have htail_f :
      (eLpNorm f 2 μB).toReal ≤ (eLpNorm f 2 μK).toReal + ε := by
    simpa [μB, μK] using
      htail hfweak hfB hdfB hfK hf_bound hdf_small
  have hdistB :
      dist
        ((hvB.toLp v :
          Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r))))
        ((hwB.toLp w :
          Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r)))) =
        (eLpNorm f 2 μB).toReal := by
    rw [Lp.dist_def]
    exact congrArg ENNReal.toReal
      (by
        simpa [f, μB] using
          eLpNorm_congr_ae (hvB.coeFn_toLp.sub hwB.coeFn_toLp))
  have hdistK :
      dist
        ((hvK.toLp v :
          Lp ℝ 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))))
        ((hwK.toLp w :
          Lp ℝ 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))) =
        (eLpNorm f 2 μK).toReal := by
    rw [Lp.dist_def]
    exact congrArg ENNReal.toReal
      (by
        simpa [f, μK] using
          eLpNorm_congr_ae (hvK.coeFn_toLp.sub hwK.coeFn_toLp))
  calc
    dist
        ((hvB.toLp v :
          Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r))))
        ((hwB.toLp w :
          Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r))))
        = (eLpNorm f 2 μB).toReal := hdistB
    _ ≤ (eLpNorm f 2 μK).toReal + ε := htail_f
    _ = dist
        ((hvK.toLp v :
          Lp ℝ 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))))
        ((hwK.toLp w :
          Lp ℝ 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))) + ε := by
          rw [← hdistK]

/--
%%handwave
name:
  Thin annulus control from uniformly small gradients
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  For a uniformly \(W^{1,2}\)-bounded scalar weak Sobolev sequence, if two
  terms have sufficiently small weak-gradient \(L^2(B(c,r))\)-norms, then
  their \(L^2(B(c,r))\)-distance is bounded, up to a prescribed error, by
  their \(L^2\)-distance on one sufficiently large standard compact subball.
proof:
  Choose a standard compact subball whose complement in \(B(c,r)\) is a thin
  annulus.  On the annulus, push points inward along radial segments and use
  the one-dimensional fundamental theorem for weak Sobolev representatives on
  almost every segment.  Cauchy--Schwarz bounds the resulting line integrals
  by the two gradient norms, and the uniform \(W^{1,2}\)-bound controls the
  harmless boundary-layer terms.  Taking the gradient threshold small enough
  gives the stated error.
-/
theorem euclideanSobolev_standard_exhaustion_tail_control_of_uniformGradientSmall
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    {φ : ℕ → ℕ}
    (_hφ : StrictMono φ)
    (hmem_exhaustion :
      ∀ k n : ℕ,
        MemLp (u (φ n)) 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∃ η : ℝ, 0 < η ∧
        ∀ n m : ℕ,
          eLpNorm (du (φ n)) 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            ENNReal.ofReal η →
          eLpNorm (du (φ m)) 2
              (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
            ENNReal.ofReal η →
          dist
            (((BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
                hbounded (φ n)).toLp (u (φ n)) :
              Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r))))
            (((BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
                hbounded (φ m)).toLp (u (φ m)) :
              Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r)))) ≤
          dist
            (((hmem_exhaustion k n).toLp (u (φ n)) :
              Lp ℝ 2
                (MeasureTheory.volume.restrict
                  (Metric.closedBall c
                    (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))))
          (((hmem_exhaustion k m).toLp (u (φ m)) :
            Lp ℝ 2
              (MeasureTheory.volume.restrict
                (Metric.closedBall c
                  (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))) + ε := by
  intro ε hε
  rcases BoundedInEuclideanLocalSobolevH1WithValues.value_eLpNorm_bound
      hbounded with
    ⟨C, hC_top, hC_bound⟩
  rcases
    euclideanSobolev_standard_exhaustion_pair_tail_control_of_uniformGradientSmall
      hr_pos hΩ_open hballΩ hC_top ε hε with
    ⟨k, η, hη_pos, htail⟩
  refine ⟨k, η, hη_pos, ?_⟩
  intro n m hn_small hm_small
  exact
    htail
      (hweak (φ n)) (hweak (φ m))
      (BoundedInEuclideanLocalSobolevH1WithValues.value_memLp hbounded (φ n))
      (BoundedInEuclideanLocalSobolevH1WithValues.value_memLp hbounded (φ m))
      (BoundedInEuclideanLocalSobolevH1WithValues.derivative_memLp hbounded (φ n))
      (BoundedInEuclideanLocalSobolevH1WithValues.derivative_memLp hbounded (φ m))
      (hmem_exhaustion k n) (hmem_exhaustion k m)
      (hC_bound (φ n)) (hC_bound (φ m))
      hn_small hm_small

/--
%%handwave
name:
  Vanishing gradients control the exhaustion tails
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  Suppose a scalar weak Sobolev sequence is uniformly \(W^{1,2}\)-bounded on
  \(B(c,r)\), and along a subsequence the weak-gradient \(L^2(B(c,r))\)-norms
  tend to zero.  Then, up to an arbitrarily small error and after passing far
  enough along the subsequence, the \(L^2(B(c,r))\)-distance between two terms
  is bounded by their \(L^2\)-distance on one sufficiently large standard
  compact subball.
proof:
  Split the ball into a standard compact subball and its thin outer annulus.
  The compact part is exactly the displayed compact-subball distance.  On the
  annulus, compare values with nearby points pushed inward along radial
  segments.  The line integral of the weak gradient controls this comparison,
  and the vanishing gradient norms make the annular contribution uniformly
  small for all sufficiently late terms.
-/
theorem euclideanSobolev_standard_exhaustion_tail_control_of_vanishingGradient
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hmem_exhaustion :
      ∀ k n : ℕ,
        MemLp (u (φ n)) 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du (φ n)) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        dist
          (((BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
              hbounded (φ n)).toLp (u (φ n)) :
            Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r))))
          (((BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
              hbounded (φ m)).toLp (u (φ m)) :
            Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r)))) ≤
        dist
          (((hmem_exhaustion k n).toLp (u (φ n)) :
            Lp ℝ 2
              (MeasureTheory.volume.restrict
                (Metric.closedBall c
                  (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))))
          (((hmem_exhaustion k m).toLp (u (φ m)) :
            Lp ℝ 2
              (MeasureTheory.volume.restrict
                (Metric.closedBall c
                  (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))) + ε := by
  intro ε hε
  rcases
    euclideanSobolev_standard_exhaustion_tail_control_of_uniformGradientSmall
      hr_pos hΩ_open hballΩ hweak hbounded hφ hmem_exhaustion ε hε with
    ⟨k, η, hη_pos, hcontrol⟩
  have hηENN_pos : (0 : ℝ≥0∞) < ENNReal.ofReal η :=
    ENNReal.ofReal_pos.mpr hη_pos
  have hsmall_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (du (φ n)) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
          ENNReal.ofReal η :=
    hgradient_tendsto_zero.eventually (eventually_le_nhds hηENN_pos)
  rcases Filter.eventually_atTop.1 hsmall_eventually with ⟨N, hN⟩
  refine ⟨k, N, ?_⟩
  intro n m hn hm
  exact hcontrol n m (hN n hn) (hN m hm)

/--
%%handwave
name:
  Standard compact-exhaustion Cauchy control upgrades to whole-ball Cauchy
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  Suppose a uniformly \(W^{1,2}(B(c,r))\)-bounded scalar weak Sobolev
  sequence has a subsequence which is Cauchy in \(L^2\) on every closed
  standard subball
  \[
    \overline B\!\left(c,r\,\frac{k+1}{k+2}\right).
  \]
  If the weak-gradient \(L^2(B(c,r))\)-norms of this subsequence tend to
  zero, then the same subsequence is Cauchy in \(L^2(B(c,r))\).
proof:
  Split the \(L^2\)-norm over \(B(c,r)\) into the compact subball and the
  thin outer annulus.  The compact part is small by the assumed Cauchy
  property.  On the annulus, compare values along short inward radial
  segments and use the vanishing weak-gradient norms to control the
  oscillation; the remaining finite-dimensional boundary layer has measure
  tending to zero along the standard exhaustion.  Letting the compact subball
  exhaust \(B(c,r)\) gives the whole-ball Cauchy property.
-/
theorem euclideanSobolev_standard_exhaustion_cauchy_to_ball_cauchy_of_vanishingGradient
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hmem_exhaustion :
      ∀ k n : ℕ,
        MemLp (u (φ n)) 2
          (MeasureTheory.volume.restrict
            (Metric.closedBall c
              (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))
    (hcauchy_exhaustion :
      ∀ k : ℕ,
        CauchySeq
          (fun n : ℕ ↦
            ((hmem_exhaustion k n).toLp (u (φ n)) :
              Lp ℝ 2
                (MeasureTheory.volume.restrict
                  (Metric.closedBall c
                    (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))))
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du (φ n)) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    CauchySeq
      (fun n : ℕ ↦
        ((BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
            hbounded (φ n)).toLp (u (φ n)) :
          Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r)))) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε_half : 0 < ε / 2 := half_pos hε
  rcases
    euclideanSobolev_standard_exhaustion_tail_control_of_vanishingGradient
      hr_pos hΩ_open hballΩ hweak hbounded hφ hmem_exhaustion
      hgradient_tendsto_zero (ε / 2) hε_half with
    ⟨k, Ntail, htail⟩
  rcases Metric.cauchySeq_iff.1 (hcauchy_exhaustion k) (ε / 2) hε_half with
    ⟨Ncompact, hcompact⟩
  refine ⟨max Ntail Ncompact, ?_⟩
  intro n hn m hm
  have hn_tail : Ntail ≤ n := le_trans (le_max_left _ _) hn
  have hm_tail : Ntail ≤ m := le_trans (le_max_left _ _) hm
  have hn_compact : Ncompact ≤ n := le_trans (le_max_right _ _) hn
  have hm_compact : Ncompact ≤ m := le_trans (le_max_right _ _) hm
  calc
    dist
        (((BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
            hbounded (φ n)).toLp (u (φ n)) :
          Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r))))
        (((BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
            hbounded (φ m)).toLp (u (φ m)) :
          Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r))))
        ≤
          dist
            (((hmem_exhaustion k n).toLp (u (φ n)) :
              Lp ℝ 2
                (MeasureTheory.volume.restrict
                  (Metric.closedBall c
                    (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))))
            (((hmem_exhaustion k m).toLp (u (φ m)) :
              Lp ℝ 2
                (MeasureTheory.volume.restrict
                  (Metric.closedBall c
                    (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))) + ε / 2 :=
            htail n m hn_tail hm_tail
    _ < ε / 2 + ε / 2 := by
          nlinarith [hcompact n hn_compact m hm_compact]
    _ = ε := by ring

/--
%%handwave
name:
  Bounded vanishing-gradient sequences have a Cauchy subsequence on a ball
statement:
  Let \(B\) be a ball contained in an open finite-dimensional Euclidean
  region.  If a scalar weak Sobolev sequence is uniformly bounded in
  \(W^{1,2}(B)\) and its weak-derivative \(L^2(B)\)-norms tend to zero, then
  some subsequence is Cauchy in \(L^2(B)\).
proof:
  Apply [compactness on compact subballs](lean:JJMath.Uniformization.euclideanSobolev_bounded_subsequence_on_compact_of_ball)
  along an increasing compact exhaustion of \(B\), and diagonalize to make
  the subsequence Cauchy on every compact subball.  The vanishing gradient
  controls oscillation across the thin outer annuli, while the uniform
  \(W^{1,2}(B)\)-bound supplies the finite initial control.  Letting the
  compact subball exhaust \(B\) gives the Cauchy property in \(L^2(B)\).
-/
theorem euclideanSobolev_bounded_vanishingGradient_cauchy_subsequence_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du n) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CauchySeq
        (fun n : ℕ ↦
          ((BoundedInEuclideanLocalSobolevH1WithValues.value_memLp
              hbounded (φ n)).toLp (u (φ n)) :
            Lp ℝ 2 (MeasureTheory.volume.restrict (Metric.ball c r)))) := by
  rcases
    euclideanSobolev_bounded_subsequence_cauchy_on_standard_exhaustion_of_ball
      hr_pos hΩ_open hballΩ hweak hbounded with
    ⟨φ, hmem_exhaustion, hφ, hcauchy_exhaustion⟩
  have hgradient_subseq :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du (φ n)) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    hgradient_tendsto_zero.comp hφ.tendsto_atTop
  exact
    ⟨φ, hφ,
      euclideanSobolev_standard_exhaustion_cauchy_to_ball_cauchy_of_vanishingGradient
        hr_pos hΩ_open hballΩ hweak hbounded hφ hmem_exhaustion
        hcauchy_exhaustion hgradient_subseq⟩

/--
%%handwave
name:
  Bounded vanishing-gradient sequences have a whole-ball \(L^2\) limit
statement:
  Let \(B\) be a ball contained in an open finite-dimensional Euclidean
  region.  If a scalar weak Sobolev sequence is uniformly bounded in
  \(W^{1,2}(B)\) and its weak-derivative \(L^2(B)\)-norms tend to zero, then
  some subsequence converges strongly in \(L^2(B)\) to a square-integrable
  limit.
proof:
  Apply [compactness on compact subballs](lean:JJMath.Uniformization.euclideanSobolev_bounded_subsequence_on_compact_of_ball)
  along an increasing compact exhaustion of \(B\), then diagonalize.  The
  uniform \(L^2(B)\)-bound gives uniform integrability, and the exhaustion
  tails have measure tending to zero, so the diagonal convergence on compact
  subballs upgrades to convergence on all of \(B\).
-/
theorem euclideanSobolev_bounded_vanishingGradient_L2_limit_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du n) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ (uLim : H → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ u (φ n) y - uLim y) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) ∧
      MemLp uLim 2 (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  rcases
    euclideanSobolev_bounded_vanishingGradient_cauchy_subsequence_on_ball
      hr_pos hΩ_open hballΩ hweak hbounded hgradient_tendsto_zero with
    ⟨φ, hφ, hφ_cauchy⟩
  rcases cauchySeq_tendsto_of_complete hφ_cauchy with
    ⟨uLimClass, huLimClass_tendsto⟩
  let uLim : H → ℝ := (uLimClass : H → ℝ)
  have hmem_subseq :
      ∀ n : ℕ, MemLp (u (φ n)) 2 μB := by
    intro n
    exact BoundedInEuclideanLocalSobolevH1WithValues.value_memLp hbounded (φ n)
  have hmem_lim : MemLp uLim 2 μB := by
    dsimp [uLim]
    exact Lp.memLp uLimClass
  refine ⟨uLim, φ, hφ, ?_, by simpa [μB] using hmem_lim⟩
  have hLp_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ (hmem_subseq n).toLp (u (φ n)))
        Filter.atTop
        (𝓝 (hmem_lim.toLp uLim)) := by
    simpa [uLim, hmem_subseq, hmem_lim, μB, Lp.toLp_coeFn] using
      huLimClass_tendsto
  exact
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (μ := μB) (p := 2)
      (fun n : ℕ ↦ u (φ n)) hmem_subseq uLim hmem_lim).mp
      hLp_tendsto

/--
%%handwave
name:
  Strong \(L^2\) limits of vanishing-gradient weak Sobolev functions have
  zero weak gradient
statement:
  On a ball contained in an open finite-dimensional Euclidean region, suppose
  \(u_n\) have weak derivative fields \(D u_n\), \(u_n\to u\) strongly in
  \(L^2(B)\), and \(D u_n\to 0\) strongly in \(L^2(B)\).  If the functions
  and derivative fields are square-integrable on \(B\), then \(u\) has zero
  weak derivative on \(B\).
proof:
  Test the weak-derivative identity against a compactly supported smooth
  function on \(B\) and a fixed direction.  Since the support is compactly
  contained in the ball, the test function and its derivative are bounded.
  Cauchy--Schwarz shows that the value and derivative pairings are continuous
  under the displayed \(L^2\)-convergences.  Passing to the limit gives the
  integration-by-parts identity with zero derivative.
-/
theorem euclideanSobolev_vanishingGradient_limit_has_zero_weakDerivative_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ} {uLim : H → ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hvalue_memLp : ∀ n : ℕ, MemLp (u n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hderivative_memLp : ∀ n : ℕ, MemLp (du n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hmem_lim : MemLp uLim 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hvalue_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ u n y - uLim y) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du n) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball c r) uLim
      (fun _ : H ↦ (0 : H →L[ℝ] ℝ)) := by
  classical
  let μB : Measure H := MeasureTheory.volume.restrict (Metric.ball c r)
  intro φ v
  let dφ : H → ℝ := fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v
  have hφ_cont : Continuous (φ : H → ℝ) := φ.smooth.continuous
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ_bound :
      ∃ C : NNReal, ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ C :=
    SmoothCompactlySupportedManifoldCoordinateFunction.exists_bound φ
  have hdφ_bound :
      ∃ C : NNReal, ∀ z : H, ‖dφ z‖ ≤ C := by
    simpa [dφ] using
      SmoothCompactlySupportedManifoldCoordinateFunction.exists_derivative_bound
        φ v
  have hleft_int :
      Integrable (fun z : H ↦ dφ z • uLim z) μB :=
    bounded_continuous_multiplier_smul_integrable_of_memLp_two_on_ball
      (c := c) (r := r) hdφ_cont hdφ_bound
      (by simpa [μB] using hmem_lim)
  have hright_int :
      Integrable
        (fun z : H ↦
          φ z • ((fun _ : H ↦ (0 : H →L[ℝ] ℝ)) z) v)
        μB := by
    simp [μB]
  have hvalue_pairing_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ z, dφ z • u n z ∂μB)
        Filter.atTop
        (𝓝 (∫ z, dφ z • uLim z ∂μB)) :=
    bounded_continuous_multiplier_integral_tendsto_of_L2_on_ball
      (c := c) (r := r) hdφ_cont hdφ_bound
      (fseq := u) (f := uLim)
      (by intro n; simpa [μB] using hvalue_memLp n)
      (by simpa [μB] using hmem_lim)
      (by simpa [μB] using hvalue_tendsto)
  have hdu_eval_mem :
      ∀ n : ℕ, MemLp (fun z : H ↦ du n z v) 2 μB := by
    intro n
    let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ v
    simpa [L, Function.comp_def, μB] using
      L.comp_memLp' (hderivative_memLp n)
  have hdu_eval_tendsto_raw :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z : H ↦ du n z v) 2 μB)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hbound :
        ∀ n : ℕ,
          eLpNorm (fun z : H ↦ du n z v) 2 μB ≤
            ENNReal.ofReal ‖v‖ * eLpNorm (du n) 2 μB := by
      intro n
      have hpoint :
          ∀ᵐ z ∂μB, ‖du n z v‖ ≤ ‖v‖ * ‖du n z‖ :=
        Filter.Eventually.of_forall fun z ↦ by
          calc
            ‖du n z v‖ ≤ ‖du n z‖ * ‖v‖ := (du n z).le_opNorm v
            _ = ‖v‖ * ‖du n z‖ := by rw [mul_comm]
      exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint 2
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal ‖v‖ * eLpNorm (du n) 2 μB)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have hconst :
          Filter.Tendsto
            (fun n : ℕ ↦ ENNReal.ofReal ‖v‖ * eLpNorm (du n) 2 μB)
            Filter.atTop (𝓝 (ENNReal.ofReal ‖v‖ * (0 : ℝ≥0∞))) :=
        ENNReal.Tendsto.const_mul
          (by simpa [μB] using hgradient_tendsto_zero)
          (Or.inr (show ENNReal.ofReal ‖v‖ ≠ (∞ : ℝ≥0∞) from
            ENNReal.ofReal_ne_top))
      have hzero : ENNReal.ofReal ‖v‖ * (0 : ℝ≥0∞) = 0 := by
        rw [mul_zero]
      simpa [hzero] using hconst
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hbound
  have hdu_eval_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ du n z v - (0 : ℝ)) 2 μB)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ by simp)
      hdu_eval_tendsto_raw
  have hderivative_pairing_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ z, φ z • du n z v ∂μB)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have h :=
      bounded_continuous_multiplier_integral_tendsto_of_L2_on_ball
        (c := c) (r := r) hφ_cont hφ_bound
        (fseq := fun (n : ℕ) (z : H) ↦ du n z v)
        (f := fun _ : H ↦ (0 : ℝ))
        (by intro n; exact hdu_eval_mem n)
        (by simp)
        hdu_eval_tendsto
    simpa [μB] using h
  have hdφ_tsupport_subset :
      tsupport dφ ⊆ tsupport (φ : H → ℝ) := by
    simpa [dφ] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : H → ℝ)) v)
  have hdφ_ball_subset :
      tsupport dφ ⊆ Metric.ball c r :=
    hdφ_tsupport_subset.trans φ.support_subset
  have hweak_ball :
      ∀ n : ℕ,
        ∫ z in Metric.ball c r, dφ z • u n z ∂MeasureTheory.volume =
          -∫ z in Metric.ball c r, φ z • du n z v
            ∂MeasureTheory.volume := by
    intro n
    let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
      { toFun := (φ : H → ℝ)
        smooth := φ.smooth
        support_subset := φ.support_subset.trans hballΩ
        compact_support := φ.compact_support }
    have h_eq := (hweak n ψ v).2.2
    have hvalue_restrict :
        ∫ z in Ω, dφ z • u n z ∂MeasureTheory.volume =
          ∫ z in Metric.ball c r, dφ z • u n z
            ∂MeasureTheory.volume := by
      exact
        setIntegral_eq_of_subset_of_forall_diff_eq_zero
          hΩ_open.measurableSet hballΩ
          (fun z hz ↦ by
            have hz_not_tsupport : z ∉ tsupport dφ := by
              intro hzt
              exact hz.2 (hdφ_ball_subset hzt)
            have hz_dφ : dφ z = 0 :=
              image_eq_zero_of_notMem_tsupport hz_not_tsupport
            simp [hz_dφ])
    have hderivative_restrict :
        ∫ z in Ω, φ z • du n z v ∂MeasureTheory.volume =
          ∫ z in Metric.ball c r, φ z • du n z v
            ∂MeasureTheory.volume := by
      exact
        setIntegral_eq_of_subset_of_forall_diff_eq_zero
          hΩ_open.measurableSet hballΩ
          (fun z hz ↦ by
            have hz_not_tsupport : z ∉ tsupport (φ : H → ℝ) := by
              intro hzt
              exact hz.2 (φ.support_subset hzt)
            have hz_φ : (φ : H → ℝ) z = 0 :=
              image_eq_zero_of_notMem_tsupport hz_not_tsupport
            simp [hz_φ])
    calc
      ∫ z in Metric.ball c r, dφ z • u n z ∂MeasureTheory.volume
          = ∫ z in Ω, dφ z • u n z ∂MeasureTheory.volume :=
            hvalue_restrict.symm
      _ = -∫ z in Ω, φ z • du n z v ∂MeasureTheory.volume := by
            simpa [ψ, dφ] using h_eq
      _ = -∫ z in Metric.ball c r, φ z • du n z v
            ∂MeasureTheory.volume := by
            rw [hderivative_restrict]
  have hleft_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ z, dφ z • u n z ∂μB)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have hright_neg :
        Filter.Tendsto
          (fun n : ℕ ↦ -∫ z, φ z • du n z v ∂μB)
          Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa using hderivative_pairing_tendsto_zero.neg
    exact
      Filter.Tendsto.congr'
        (Filter.Eventually.of_forall fun n ↦ by
          simpa [μB] using (hweak_ball n).symm)
        hright_neg
  have hlimit_zero :
      ∫ z, dφ z • uLim z ∂μB = 0 :=
    tendsto_nhds_unique hvalue_pairing_tendsto hleft_tendsto_zero
  refine ⟨by simpa [dφ, μB] using hleft_int, hright_int, ?_⟩
  simpa [dφ, μB] using hlimit_zero

/--
%%handwave
name:
  Bounded vanishing-gradient sequences have a zero-gradient limit on a ball
statement:
  Let \(B\) be a ball contained in an open finite-dimensional Euclidean
  region.  If a scalar weak Sobolev sequence is uniformly bounded in
  \(W^{1,2}(B)\) and its weak-derivative \(L^2(B)\)-norms tend to zero, then a
  subsequence converges strongly in \(L^2(B)\) to a square-integrable function
  whose weak gradient vanishes on \(B\).
proof:
  Apply [compactness on compact subballs](lean:JJMath.Uniformization.euclideanSobolev_bounded_subsequence_on_compact_of_ball)
  and diagonalize over a compact exhaustion of \(B\).  The uniform
  \(L^2(B)\)-bound controls the exhaustion tails, so the diagonal subsequence
  converges on the whole ball.  The weak-derivative identities pass to the
  \(L^2\)-limit, while the derivative fields converge to zero in \(L^2(B)\);
  hence the limiting weak derivative is zero.
-/
theorem euclideanSobolev_bounded_vanishingGradient_zeroGradient_limit_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du n) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ (uLim : H → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ u (φ n) y - uLim y) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) ∧
      MemLp uLim 2 (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball c r) uLim
        (fun _ : H ↦ (0 : H →L[ℝ] ℝ)) := by
  rcases
    euclideanSobolev_bounded_vanishingGradient_L2_limit_on_ball
      hr_pos hΩ_open hballΩ hweak hbounded hgradient_tendsto_zero with
    ⟨uLim, φ, hφ, hconv, hmem_lim⟩
  have hgradient_subseq :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du (φ n)) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    hgradient_tendsto_zero.comp hφ.tendsto_atTop
  have hweak_subseq :
      ∀ n : ℕ,
        IsWeakDerivativeOnEuclideanRegionWithValues Ω
          (u (φ n)) (du (φ n)) := by
    intro n
    exact hweak (φ n)
  have hvalue_memLp_subseq :
      ∀ n : ℕ, MemLp (u (φ n)) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    intro n
    exact BoundedInEuclideanLocalSobolevH1WithValues.value_memLp hbounded (φ n)
  have hderivative_memLp_subseq :
      ∀ n : ℕ, MemLp (du (φ n)) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    intro n
    exact BoundedInEuclideanLocalSobolevH1WithValues.derivative_memLp hbounded (φ n)
  have hweak_zero :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball c r) uLim
        (fun _ : H ↦ (0 : H →L[ℝ] ℝ)) :=
    euclideanSobolev_vanishingGradient_limit_has_zero_weakDerivative_on_ball
      hΩ_open hballΩ hweak_subseq hvalue_memLp_subseq
      hderivative_memLp_subseq hmem_lim hconv hgradient_subseq
  exact ⟨uLim, φ, hφ, hconv, hmem_lim, hweak_zero⟩

/--
%%handwave
name:
  Zero weak gradient on a Euclidean ball gives one almost-everywhere constant
statement:
  On a finite-dimensional Euclidean ball, a square-integrable scalar weak
  Sobolev function whose weak gradient is zero is almost everywhere equal to
  one real constant.
proof:
  This is the local Euclidean rigidity input before the Poincare inequality:
  vanishing distributional first derivatives imply that Sobolev
  representatives are constant on line segments, and the ball is connected.
-/
theorem euclideanSobolev_zeroGradient_ae_const_on_ball_of_weakDerivative_zero
    {c : H} {r : ℝ} {u : H → ℝ}
    (_hr_pos : 0 < r)
    (hvalue_mem : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hweak_zero :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball c r) u
        (fun _ : H ↦ (0 : H →L[ℝ] ℝ))) :
    ∃ a : ℝ,
      ∀ᵐ y ∂MeasureTheory.volume.restrict (Metric.ball c r), u y = a := by
  have hweak_zero' :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball c r) u
        (0 : H → H →L[ℝ] ℝ) := by
    simpa using hweak_zero
  refine
    euclideanSobolev_zero_gradient_constant_on_preconnected_finiteDimensional
      Metric.isOpen_ball Metric.isPreconnected_ball hweak_zero' ?_ ?_
  · intro K _hK hKball
    have hμKball :
        MeasureTheory.volume.restrict K ≤
          MeasureTheory.volume.restrict (Metric.ball c r) :=
      Measure.restrict_mono hKball le_rfl
    have hzero_mem :
        MemLp (0 : H → H →L[ℝ] ℝ) 2
          (MeasureTheory.volume.restrict K) := by
      refine ⟨aestronglyMeasurable_zero, ?_⟩
      change
        eLpNorm (0 : H → H →L[ℝ] ℝ) (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict K) < ⊤
      rw [eLpNorm_zero (α := H) (ε := H →L[ℝ] ℝ)
        (p := (2 : ℝ≥0∞)) (μ := MeasureTheory.volume.restrict K)]
      exact ENNReal.zero_lt_top
    exact ⟨hvalue_mem.mono_measure hμKball, hzero_mem⟩
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/--
%%handwave
name:
  Bounded vanishing-gradient sequences have an almost-everywhere constant limit
statement:
  Let \(B\) be a ball contained in an open finite-dimensional Euclidean
  region.  If a scalar weak Sobolev sequence is uniformly bounded in
  \(W^{1,2}(B)\) and its weak-derivative \(L^2(B)\)-norms tend to zero, then a
  subsequence converges strongly in \(L^2(B)\) to a function that is almost
  everywhere equal on \(B\) to one real constant.
proof:
  Use Rellich compactness on compact subballs and diagonalize over an
  exhaustion of \(B\).  The uniform bound controls the exhaustion tails, so the
  subsequence converges in \(L^2(B)\).  Passing the weak derivative identities
  to the limit gives zero weak gradient for the limit; zero-gradient rigidity
  on the preconnected ball identifies the limit almost everywhere with a
  constant.
-/
theorem euclideanSobolev_bounded_vanishingGradient_ae_const_limit_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du n) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ (uLim : H → ℝ) (a : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ u (φ n) y - uLim y) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) ∧
      (∀ᵐ y ∂MeasureTheory.volume.restrict (Metric.ball c r), uLim y = a) := by
  rcases
    euclideanSobolev_bounded_vanishingGradient_zeroGradient_limit_on_ball
      hr_pos hΩ_open hballΩ hweak hbounded hgradient_tendsto_zero with
    ⟨uLim, φ, hφ, hconv, hmem_lim, hweak_zero⟩
  rcases
    euclideanSobolev_zeroGradient_ae_const_on_ball_of_weakDerivative_zero
      hr_pos hmem_lim hweak_zero with
    ⟨a, hconst⟩
  exact ⟨uLim, a, φ, hφ, hconv, hconst⟩

/--
%%handwave
name:
  Bounded vanishing-gradient sequences converge to one constant
statement:
  Let \(B\) be a ball contained in an open finite-dimensional Euclidean
  region.  If a scalar weak Sobolev sequence is uniformly bounded in
  \(W^{1,2}(B)\) and its weak-derivative \(L^2(B)\)-norms tend to zero, then a
  subsequence converges strongly in \(L^2(B)\) to one constant function.
proof:
  Apply Rellich compactness on compact subballs and diagonalize over an
  exhaustion of \(B\).  The uniform \(L^2(B)\) bound controls the exhaustion
  tails, giving convergence on the whole ball.  Passing the weak derivative
  identities to the limit gives a zero weak derivative, and the zero-gradient
  rigidity theorem on the preconnected ball makes the limit constant.
-/
theorem euclideanSobolev_bounded_vanishingGradient_subsequence_constant_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du)
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du n) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ (a : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ u (φ n) y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  rcases
    euclideanSobolev_bounded_vanishingGradient_ae_const_limit_on_ball
      hr_pos hΩ_open hballΩ hweak hbounded hgradient_tendsto_zero with
    ⟨uLim, a, φ, hφ, hconv, hconst⟩
  refine ⟨a, φ, hφ, ?_⟩
  have hseq_eq :
      (fun n : ℕ ↦
        eLpNorm (fun y : H ↦ u (φ n) y - a) 2
          (MeasureTheory.volume.restrict (Metric.ball c r))) =
      (fun n : ℕ ↦
        eLpNorm (fun y : H ↦ u (φ n) y - uLim y) 2
          (MeasureTheory.volume.restrict (Metric.ball c r))) := by
    funext n
    exact eLpNorm_congr_ae <|
      hconst.mono fun y hy ↦ by simp [hy]
  rw [hseq_eq]
  exact hconv

/--
%%handwave
name:
  Vanishing-gradient compactness on a Euclidean ball
statement:
  Let \(B\) be a ball contained in an open finite-dimensional Euclidean
  region.  If a sequence of scalar weak Sobolev functions is uniformly bounded
  in \(L^2(B)\), its weak derivatives are square-integrable on \(B\), and the
  weak-derivative \(L^2(B)\)-norms tend to zero, then a subsequence converges
  strongly in \(L^2(B)\) to one constant function.
proof:
  Rellich compactness gives an \(L^2\)-convergent subsequence on compact
  subballs, and a diagonal exhaustion plus the uniform \(L^2\) bound upgrades
  this to convergence on the whole ball.  Passing the integration-by-parts
  identities to the limit shows that the limit has zero weak gradient.  The
  usual zero-gradient rigidity theorem on balls identifies the limit almost
  everywhere with a constant.
-/
theorem euclideanSobolev_vanishingGradient_subsequence_constant_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hvalue_memLp : ∀ n : ℕ, MemLp (u n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hderivative_memLp : ∀ n : ℕ, MemLp (du n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hvalue_bound :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (u n) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C)
    (hgradient_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (du n) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ (a : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ u (φ n) y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du :=
    euclideanSobolev_vanishingGradient_h1_bound_on_ball
      hvalue_memLp hderivative_memLp hvalue_bound hgradient_tendsto_zero
  exact
    euclideanSobolev_bounded_vanishingGradient_subsequence_constant_on_ball
      hr_pos hΩ_open hballΩ hweak hbounded hgradient_tendsto_zero

/--
%%handwave
name:
  Vanishing-gradient bad sequences converge to one constant
statement:
  From a normalized sequence on a Euclidean ball whose weak gradients tend to
  zero in \(L^2\), one can extract a subsequence and a real constant such that
  the subsequence converges to that constant in \(L^2\) on the ball.
proof:
  Apply Rellich compactness on compact subballs and use a diagonal exhaustion
  to obtain an \(L^2\)-limit on the whole ball.  The weak-gradient convergence
  passes through the distributional integration-by-parts identity, so the
  limit has zero weak gradient.  The zero-gradient rigidity theorem on balls
  then identifies the limit almost everywhere with one constant, giving the
  asserted strong \(L^2\)-convergence to that constant.
-/
theorem euclideanSobolev_poincare_badSequence_subsequence_constant_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hbad : EuclideanSobolevPoincareBadSequenceOnBall Ω c r u du) :
    ∃ (a : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ u (φ n) y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hvalue_bound :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (u n) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C := by
    refine ⟨1, by simp, ?_⟩
    intro n
    rw [hbad.value_normalized n]
  exact
    euclideanSobolev_vanishingGradient_subsequence_constant_on_ball
      hr_pos hΩ_open hballΩ hbad.weak hbad.value_memLp
      hbad.derivative_memLp hvalue_bound hbad.gradient_tendsto_zero

/--
%%handwave
name:
  Normalized bad sequences contradict compactness
statement:
  A normalized bad sequence for the local Euclidean \(L^2\) Poincare
  inequality on a ball cannot exist.
proof:
  Rellich compactness gives a subsequence converging strongly in \(L^2\) on
  compact subballs, and an exhaustion gives convergence on the whole ball.
  The weak-gradient convergence to zero passes to the distributional limit, so
  the limit has zero weak gradient.  The one-dimensional
  absolute-continuity-on-lines argument shows that the limit is almost
  everywhere constant on the ball.  This contradicts the normalization that
  every member of the sequence has \(L^2\)-distance at least one from every
  constant.
-/
theorem euclideanSobolev_poincare_badSequence_absurd_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hbad : EuclideanSobolevPoincareBadSequenceOnBall Ω c r u du) :
    False := by
  classical
  rcases euclideanSobolev_poincare_badSequence_subsequence_constant_on_ball
      hr_pos hΩ_open hballΩ hbad with
    ⟨a, φ, _hφ, hconv⟩
  have hconst :
      Filter.Tendsto (fun _n : ℕ ↦ (1 : ℝ≥0∞))
        Filter.atTop (𝓝 (1 : ℝ≥0∞)) :=
    tendsto_const_nhds
  have hle_eventually :
      (fun _n : ℕ ↦ (1 : ℝ≥0∞)) ≤ᶠ[Filter.atTop]
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ u (φ n) y - a) 2
            (MeasureTheory.volume.restrict (Metric.ball c r))) :=
    Filter.Eventually.of_forall fun n ↦
      hbad.distance_from_constants (φ n) a
  have hone_le_zero : (1 : ℝ≥0∞) ≤ 0 :=
    le_of_tendsto_of_tendsto hconst hconv hle_eventually
  exact (not_lt_of_ge hone_le_zero) zero_lt_one

/--
%%handwave
name:
  Compactness contradiction for the local Euclidean \(L^2\) Poincare inequality
statement:
  If no finite constant gives the local \(L^2\) Poincare inequality on a ball
  contained in an open Euclidean region, then the normalized bad sequence
  obtained from this failure contradicts compactness and zero-gradient
  rigidity.
proof:
  Choose functions whose distance from every constant on the ball is
  normalized to one while the weak gradients tend to zero in \(L^2\).  The
  [local Rellich compactness theorem on Euclidean compacts](lean:JJMath.Uniformization.euclideanRellichKondrachov_subsequence_on_compact)
  gives a strongly \(L^2\)-convergent subsequence on compact subballs, and an
  exhaustion gives convergence on the ball.  The integration-by-parts identity
  passes to the limit, so the limit has zero weak gradient.  The
  one-dimensional absolute-continuity-on-lines theorem, applied along line
  segments in the ball, implies that this limit is almost everywhere constant.
  This contradicts the normalization.
-/
theorem euclideanSobolev_poincare_L2_on_ball_contradiction
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (hfail : ¬ EuclideanSobolevPoincareL2EstimateOnBall Ω c r) :
    False := by
  rcases euclideanSobolev_poincare_badSequence_of_failure_on_ball
      hr_pos hΩ_open hballΩ hfail with
    ⟨u, du, hbad⟩
  exact euclideanSobolev_poincare_badSequence_absurd_on_ball
    hr_pos hΩ_open hballΩ hbad

/--
%%handwave
name:
  Local Euclidean \(L^2\) Poincare inequality on balls
statement:
  Let \(\Omega\) be an open subset of a standard finite-dimensional Euclidean
  space and suppose \(B(c,r)\subset\Omega\) with \(r>0\).  There is a finite
  constant such that every real-valued function on the ambient Euclidean space
  with weak derivative field on \(\Omega\), and with both the function and
  derivative field square-integrable over \(B(c,r)\), is within that constant
  times the derivative \(L^2(B(c,r))\)-norm of some constant function on
  \(B(c,r)\).  The constant is independent of the particular function and
  weak derivative field.
proof:
  Argue by contradiction and apply the compactness contradiction for the
  normalized bad sequence.
tags:
  milestone
-/
theorem euclideanSobolev_poincare_L2_on_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω) :
    EuclideanSobolevPoincareL2EstimateOnBall Ω c r := by
  classical
  by_contra hfail
  exact euclideanSobolev_poincare_L2_on_ball_contradiction
    hr_pos hΩ_open hballΩ hfail

/--
%%handwave
name:
  Euclidean zero-gradient Poincare consequence on balls
statement:
  On a ball contained in an open finite-dimensional Euclidean region, a
  scalar weak Sobolev function whose weak derivative vanishes almost
  everywhere is almost everywhere equal to a constant on that ball.
proof:
  Apply [the local \(L^2\) Poincare inequality on the ball](lean:JJMath.Uniformization.euclideanSobolev_poincare_L2_on_ball).
  Since the weak gradient vanishes almost everywhere, its \(L^2\)-seminorm on
  the ball is zero.  The inequality forces the \(L^2\)-distance from \(u\) to
  the chosen constant to be zero, and the measurability supplied by the
  inequality turns this into almost-everywhere equality.
-/
theorem euclideanSobolev_poincare_zero_gradient_ae_const_on_ball
    {Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hvalue_mem : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hderivative_mem : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdu_zero : ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, du z = 0) :
    ∃ a : ℝ,
      ∀ᵐ y ∂MeasureTheory.volume.restrict (Metric.ball c r), u y = a := by
  classical
  let B : Set H := Metric.ball c r
  rcases euclideanSobolev_poincare_L2_on_ball
      hr_pos hΩ_open hballΩ with
    ⟨C, _hC_top, hPoincare⟩
  rcases hPoincare hweak hvalue_mem hderivative_mem with
    ⟨a, hu_aestr, hineq⟩
  refine ⟨a, ?_⟩
  have hdu_zero_B : ∀ᵐ z ∂MeasureTheory.volume.restrict B, du z = 0 :=
    ae_restrict_of_ae_restrict_of_subset hballΩ hdu_zero
  have hdu_norm_zero :
      eLpNorm du 2 (MeasureTheory.volume.restrict B) = 0 := by
    have hcongr :
        eLpNorm du (2 : ℝ≥0∞) (MeasureTheory.volume.restrict B) =
          eLpNorm (fun _ : H ↦ (0 : H →L[ℝ] ℝ)) (2 : ℝ≥0∞)
            (MeasureTheory.volume.restrict B) :=
      eLpNorm_congr_ae hdu_zero_B
    exact hcongr.trans
      (eLpNorm_zero' (α := H) (ε := H →L[ℝ] ℝ)
        (p := (2 : ℝ≥0∞)) (μ := MeasureTheory.volume.restrict B))
  have hu_norm_zero :
      eLpNorm (fun y : H ↦ u y - a) 2
          (MeasureTheory.volume.restrict B) = 0 := by
    apply le_antisymm
    · calc
        eLpNorm (fun y : H ↦ u y - a) 2
            (MeasureTheory.volume.restrict B)
            ≤ C * eLpNorm du 2 (MeasureTheory.volume.restrict B) := hineq
        _ = 0 := by rw [hdu_norm_zero, mul_zero]
    · exact bot_le
  have hp_ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hsub_zero :
      (fun y : H ↦ u y - a) =ᵐ[MeasureTheory.volume.restrict B] 0 :=
    (eLpNorm_eq_zero_iff hu_aestr hp_ne).1 hu_norm_zero
  filter_upwards [hsub_zero] with y hy
  exact sub_eq_zero.mp hy

/--
%%handwave
name:
  Euclidean zero-gradient rigidity gives local constants
statement:
  On an open subset of a standard finite-dimensional Euclidean space, a
  real-valued weak Sobolev function whose weak derivative vanishes almost
  everywhere is locally almost everywhere constant.
proof:
  Around the chosen point, take a metric ball contained in the open region.
  Apply [the zero-gradient Poincare consequence on that ball](lean:JJMath.Uniformization.euclideanSobolev_poincare_zero_gradient_ae_const_on_ball).
-/
theorem euclideanSobolev_zero_gradient_locally_constant_on_open
    {Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hΩ_open : IsOpen Ω)
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hmem :
      ∀ K : Set H, IsCompact K → K ⊆ Ω →
        MemLp u 2 (MeasureTheory.volume.restrict K) ∧
          MemLp du 2 (MeasureTheory.volume.restrict K))
    (hdu_zero : ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, du z = 0) :
    ∀ z ∈ Ω, ∃ W : Set H, IsOpen W ∧ z ∈ W ∧ W ⊆ Ω ∧
      ∃ a : ℝ, ∀ᵐ y ∂MeasureTheory.volume.restrict W, u y = a := by
  intro z hzΩ
  rcases Metric.isOpen_iff.mp hΩ_open z hzΩ with ⟨R, hR_pos, hballΩ_R⟩
  let r : ℝ := R / 2
  have hr_pos : 0 < r := by
    positivity
  have hr_lt_R : r < R := by
    change R / 2 < R
    linarith
  have hclosedΩ : Metric.closedBall z r ⊆ Ω := by
    intro y hy
    apply hballΩ_R
    have hydist : dist y z ≤ r := by
      simpa [Metric.mem_closedBall] using hy
    simpa [Metric.mem_ball] using lt_of_le_of_lt hydist hr_lt_R
  have hballΩ : Metric.ball z r ⊆ Ω :=
    (Metric.ball_subset_closedBall).trans hclosedΩ
  have hclosed_compact : IsCompact (Metric.closedBall z r) :=
    isCompact_closedBall z r
  have hmem_closed :
      MemLp u 2 (MeasureTheory.volume.restrict (Metric.closedBall z r)) ∧
        MemLp du 2 (MeasureTheory.volume.restrict (Metric.closedBall z r)) :=
    hmem (Metric.closedBall z r) hclosed_compact hclosedΩ
  have hμ_ball_closed :
      MeasureTheory.volume.restrict (Metric.ball z r) ≤
        MeasureTheory.volume.restrict (Metric.closedBall z r) :=
    Measure.restrict_mono Metric.ball_subset_closedBall le_rfl
  have hvalue_mem_ball :
      MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball z r)) :=
    hmem_closed.1.mono_measure hμ_ball_closed
  have hderivative_mem_ball :
      MemLp du 2 (MeasureTheory.volume.restrict (Metric.ball z r)) :=
    hmem_closed.2.mono_measure hμ_ball_closed
  refine ⟨Metric.ball z r, Metric.isOpen_ball, ?_, hballΩ, ?_⟩
  · exact Metric.mem_ball_self hr_pos
  · exact
      euclideanSobolev_poincare_zero_gradient_ae_const_on_ball
        hr_pos hΩ_open hballΩ hweak hvalue_mem_ball
        hderivative_mem_ball hdu_zero

end StandardEuclideanBall

/--
%%handwave
name:
  \(L^2\) Poincaré inequality on a complex Euclidean ball
statement:
  For every \(r>0\), the ball \(B(c,r)\subset\mathbb C\) satisfies the
  \(L^2\) Poincaré inequality modulo constants for real functions with weak
  differential, with a finite constant depending on the ball.
proof:
  Identify \(\mathbb C\) isometrically and measure-preservingly with
  \(\mathbb R^2\), transport the function and differential, apply the
  Euclidean finite-dimensional ball inequality, and transfer the estimates
  back through the isometry.
-/
theorem complex_euclideanSobolev_poincare_L2_on_ball_self
    {c : ℂ} {r : ℝ} (hr_pos : 0 < r) :
    EuclideanSobolevPoincareL2EstimateOnBall (Metric.ball c r) c r := by
  classical
  let E : Type := EuclideanSpace ℝ (Fin 2)
  let L : ℂ ≃ₗᵢ[ℝ] E := Complex.orthonormalBasisOneI.repr
  let Cball : Set ℂ := Metric.ball c r
  let Eball : Set E := Metric.ball (L c) r
  rcases euclideanSobolev_poincare_L2_on_ball
      (ι := Fin 2) (Ω := Eball) (c := L c) (r := r)
      hr_pos Metric.isOpen_ball (fun _ hy ↦ hy) with
    ⟨C, hC_top, hPoincare⟩
  let LT : E →L[ℝ] ℂ := L.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let T : E → ℂ := fun y ↦ LT y
  let pre : (ℂ →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E ℂ ℝ).flip LT
  let A : ℝ≥0∞ := ENNReal.ofReal ‖pre‖
  refine ⟨C * A, ENNReal.mul_lt_top hC_top ENNReal.ofReal_lt_top, ?_⟩
  intro u du hweak hu hdu
  let uE : E → ℝ := fun y ↦ u (T y)
  let duE : E → E →L[ℝ] ℝ := fun y ↦ pre (du (T y))
  let emSymm : E ≃ᵐ ℂ := L.symm.toHomeomorph.toMeasurableEquiv
  have hmp0 : MeasurePreserving emSymm
      (MeasureTheory.volume : Measure E) (MeasureTheory.volume : Measure ℂ) := by
    simpa [L, emSymm] using
      Complex.orthonormalBasisOneI.measurePreserving_repr_symm
  have himage_Eball : emSymm '' Eball = Cball := by
    simpa [L, Eball, Cball, emSymm] using
      (L.symm.image_ball (L c) r)
  have hmpBall : MeasurePreserving emSymm
      (MeasureTheory.volume.restrict Eball)
      (MeasureTheory.volume.restrict Cball) := by
    rw [← himage_Eball]
    exact hmp0.restrict_image_emb emSymm.measurableEmbedding Eball
  have hT_maps : Set.MapsTo T Eball Cball := by
    intro y hy
    have hpre : (fun y : E ↦ L.symm y) ⁻¹' Cball = Eball := by
      simpa [L, Cball, Eball] using (L.symm.preimage_ball c r)
    have hy' : L.symm y ∈ Cball := by
      change y ∈ (fun y : E ↦ L.symm y) ⁻¹' Cball
      rw [hpre]
      exact hy
    simpa [T, LT] using hy'
  have hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict Eball)
      (MeasureTheory.volume.restrict Cball) := by
    simpa [T, LT, emSymm] using hmpBall.quasiMeasurePreserving
  have hT_compactPull :
      ∀ {K : Set E} {Q : Set ℂ}, IsCompact K → K ⊆ Eball → T '' K ⊆ Q →
        ∃ C₀ : ℝ≥0∞, C₀ ≠ ⊤ ∧
          Measure.map T (MeasureTheory.volume.restrict K) ≤
            C₀ • MeasureTheory.volume.restrict Q := by
    intro K Q _hK _hK_ball hKQ
    have hmpK : MeasurePreserving emSymm
        (MeasureTheory.volume.restrict K)
        (MeasureTheory.volume.restrict (emSymm '' K)) := by
      simpa [emSymm] using
        hmp0.restrict_image_emb emSymm.measurableEmbedding K
    refine ⟨1, by simp, ?_⟩
    have hmap_eq :
        Measure.map T (MeasureTheory.volume.restrict K) =
          MeasureTheory.volume.restrict (T '' K) := by
      simpa [T, LT, emSymm] using hmpK.map_eq
    rw [hmap_eq, one_smul]
    exact Measure.restrict_mono hKQ le_rfl
  have hT_smooth : ContDiff ℝ ⊤ T := by
    simpa [T] using LT.contDiff
  have hT_fderiv : ∀ y : E, fderiv ℝ T y = LT := by
    intro y
    simpa [T] using (LT.hasFDerivAt y).fderiv
  have huE : MemLp uE 2 (MeasureTheory.volume.restrict Eball) := by
    simpa [uE, T, LT, emSymm, Function.comp_def] using
      hu.comp_measurePreserving hmpBall
  have hdu_comp : MemLp (fun y : E ↦ du (T y)) 2
      (MeasureTheory.volume.restrict Eball) := by
    simpa [T, LT, emSymm, Function.comp_def] using
      hdu.comp_measurePreserving hmpBall
  have hduE : MemLp duE 2 (MeasureTheory.volume.restrict Eball) := by
    simpa [duE, pre] using hdu_comp.continuousLinearMap_comp pre
  have hweakE_raw :
      IsWeakDerivativeOnEuclideanRegionWithValues Eball uE
        (fun y : E ↦ (du (T y)).comp (fderiv ℝ T y)) := by
    simpa [uE] using
      IsWeakDerivativeOnEuclideanRegionWithValues.comp_contDiff_qmp
        (D := E) (H := ℂ) (U := Eball) (Ω := Cball) (T := T)
        Metric.isOpen_ball Metric.isOpen_ball hT_maps hT_smooth
        hT_qmp hT_compactPull hweak hu hdu
  have hweakE :
      IsWeakDerivativeOnEuclideanRegionWithValues Eball uE duE := by
    simpa [duE, pre, hT_fderiv, ContinuousLinearMap.compL_apply] using
      hweakE_raw
  rcases hPoincare hweakE huE hduE with
    ⟨a, haE, hineqE⟩
  refine ⟨a, ?_, ?_⟩
  · exact hu.aestronglyMeasurable.sub aestronglyMeasurable_const
  · have hnormC_eq_E :
        eLpNorm (fun z : ℂ ↦ u z - a) 2
            (MeasureTheory.volume.restrict Cball) =
          eLpNorm (fun y : E ↦ uE y - a) 2
            (MeasureTheory.volume.restrict Eball) := by
      have hnorm :=
        eLpNorm_comp_measurePreserving
          (p := (2 : ℝ≥0∞)) (g := fun z : ℂ ↦ u z - a)
          (μ := MeasureTheory.volume.restrict Eball)
          (ν := MeasureTheory.volume.restrict Cball)
          (hu.aestronglyMeasurable.sub aestronglyMeasurable_const)
          hmpBall
      simpa [uE, T, LT, emSymm, Function.comp_def] using hnorm.symm
    have hduE_le :
        eLpNorm duE 2 (MeasureTheory.volume.restrict Eball) ≤
          A * eLpNorm du 2 (MeasureTheory.volume.restrict Cball) := by
      have hpoint :
          ∀ᵐ y ∂MeasureTheory.volume.restrict Eball,
            ‖duE y‖ ≤ ‖pre‖ * ‖du (T y)‖ :=
        Filter.Eventually.of_forall fun y ↦ by
          have hpre_point :
              ‖pre (du (T y))‖ ≤ ‖pre‖ * ‖du (T y)‖ :=
            ContinuousLinearMap.le_opNorm pre (du (T y))
          simpa [duE] using hpre_point
      have hraw :
          eLpNorm duE 2 (MeasureTheory.volume.restrict Eball) ≤
            ENNReal.ofReal ‖pre‖ *
              eLpNorm (fun y : E ↦ du (T y)) 2
                (MeasureTheory.volume.restrict Eball) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint 2
      have hnorm :=
        eLpNorm_comp_measurePreserving
          (p := (2 : ℝ≥0∞)) (g := du)
          (μ := MeasureTheory.volume.restrict Eball)
          (ν := MeasureTheory.volume.restrict Cball)
          hdu.aestronglyMeasurable hmpBall
      calc
        eLpNorm duE 2 (MeasureTheory.volume.restrict Eball)
            ≤ ENNReal.ofReal ‖pre‖ *
                eLpNorm (fun y : E ↦ du (T y)) 2
                  (MeasureTheory.volume.restrict Eball) := hraw
        _ = A * eLpNorm du 2 (MeasureTheory.volume.restrict Cball) := by
          simpa [A, T, LT, emSymm, Function.comp_def] using congrArg (fun x ↦
            ENNReal.ofReal ‖pre‖ * x) hnorm
    calc
      eLpNorm (fun z : ℂ ↦ u z - a) 2
          (MeasureTheory.volume.restrict Cball)
          = eLpNorm (fun y : E ↦ uE y - a) 2
              (MeasureTheory.volume.restrict Eball) := hnormC_eq_E
      _ ≤ C * eLpNorm duE 2
              (MeasureTheory.volume.restrict Eball) := hineqE
      _ ≤ C * (A * eLpNorm du 2
              (MeasureTheory.volume.restrict Cball)) :=
            mul_le_mul_right hduE_le C
      _ = C * A * eLpNorm du 2
              (MeasureTheory.volume.restrict Cball) := by
            rw [mul_assoc]

/--
%%handwave
name:
  Scale-covariant planar $L^2$ Poincaré inequality
statement:
  There is a finite constant $C$, independent of the center $c\in\mathbb C$
  and radius $r>0$, such that every real-valued function $u$ on
  $B(c,r)$ with weak differential $du\in L^2$ and with $u\in L^2$ admits
  $a\in\mathbb R$ satisfying
  $$
    \|u-a\|_{L^2(B(c,r))}
      \le C r\,\|du\|_{L^2(B(c,r))}.
  $$
proof:
  Apply [the finite Poincaré estimate on the unit complex ball](lean:JJMath.Uniformization.complex_euclideanSobolev_poincare_L2_on_ball_self) after translating $c$ to the origin and dilating by $r$. Translation preserves both $L^2$ norms, while planar $L^2$ scaling contributes $r^{-1}$ to the function norm and cancels the chain-rule factor $r$ in the differential norm.
-/
theorem complex_euclideanSobolev_poincare_L2_scale_covariant :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {c : ℂ} {r : ℝ}, 0 < r →
        ∀ {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues (Metric.ball c r) u du →
          MemLp u 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp du 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) →
          ∃ a : ℝ,
            AEStronglyMeasurable (fun z : ℂ ↦ u z - a)
              (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
            eLpNorm (fun z : ℂ ↦ u z - a) 2
                (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
              C * ENNReal.ofReal r *
                eLpNorm du 2
                  (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  rcases complex_euclideanSobolev_poincare_L2_on_ball_self
      (c := (0 : ℂ)) (r := (1 : ℝ)) one_pos with
    ⟨C, hC_top, hPoincare⟩
  refine ⟨C, hC_top, ?_⟩
  intro c r hr_pos u du hweak hu hdu
  let uT : ℂ → ℝ := fun z ↦ u (z + c)
  let duT : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ du (z + c)
  let u0 : ℂ → ℝ := fun z ↦ uT (r • z)
  let du0 : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ r • duT (r • z)
  have hweakT :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball (0 : ℂ) r) uT duT := by
    simpa [uT, duT, preimage_add_right_ball_center] using
      hweak.comp_add_right c
  have huT : MemLp uT 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) r)) := by
    simpa [uT] using
      memLp_comp_add_right_restrict_ball_zero (f := u) hu
  have hduT : MemLp duT 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) r)) := by
    simpa [duT] using
      memLp_comp_add_right_restrict_ball_zero (f := du) hdu
  have hweak0 :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball (0 : ℂ) 1) u0 du0 := by
    have hraw := hweakT.comp_smul hr_pos.ne'
    have hpre :
        (fun z : ℂ ↦ r • z) ⁻¹' Metric.ball (0 : ℂ) r =
          Metric.ball (0 : ℂ) 1 := by
      simpa using
        preimage_const_smul_ball_zero_of_pos
          (H := ℂ) (a := r) (R := (1 : ℝ)) hr_pos
    rw [hpre] at hraw
    simpa [u0, du0] using hraw
  have hu0 : MemLp u0 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    simpa [u0] using
      memLp_comp_const_smul_of_memLp_restrict_ball_zero
        (a := r) (R := (1 : ℝ)) hr_pos (by simpa using huT)
  have hdu0 : MemLp du0 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    have hcomp :=
      memLp_comp_const_smul_of_memLp_restrict_ball_zero
        (a := r) (R := (1 : ℝ)) hr_pos (by simpa using hduT)
    simpa [du0] using hcomp.const_smul r
  rcases hPoincare hweak0 hu0 hdu0 with ⟨a, _ha0, hineq0⟩
  refine
    ⟨a, hu.aestronglyMeasurable.sub aestronglyMeasurable_const, ?_⟩
  have herror0 :
      eLpNorm (fun z : ℂ ↦ u0 z - a) 2
          (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)) =
        (ENNReal.ofReal r)⁻¹ *
          eLpNorm (fun z : ℂ ↦ uT z - a) 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) r)) := by
    simpa [u0] using
      eLpNorm_comp_pos_smul_complex_L2_restrict_ball_zero
        (R := (1 : ℝ)) hr_pos (fun z : ℂ ↦ uT z - a)
  have herrorT :
      eLpNorm (fun z : ℂ ↦ uT z - a) 2
          (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) r)) =
        eLpNorm (fun z : ℂ ↦ u z - a) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    simpa [uT] using
      eLpNorm_comp_add_right_restrict_ball_zero
        (fun z : ℂ ↦ u z - a) c r 2
  have hdu0norm :
      eLpNorm du0 2
          (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)) =
        eLpNorm duT 2
          (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) r)) := by
    simpa [du0] using
      eLpNorm_pos_smul_comp_pos_smul_complex_L2_restrict_ball_zero
        (R := (1 : ℝ)) hr_pos duT
  have hduTnorm :
      eLpNorm duT 2
          (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) r)) =
        eLpNorm du 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    simpa [duT] using
      eLpNorm_comp_add_right_restrict_ball_zero du c r 2
  rw [herror0, herrorT, hdu0norm, hduTnorm] at hineq0
  have hscaled :=
    (ENNReal.inv_mul_le_iff
      (ENNReal.ofReal_pos.mpr hr_pos).ne' ENNReal.ofReal_ne_top).mp hineq0
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

end

end Uniformization

end JJMath
