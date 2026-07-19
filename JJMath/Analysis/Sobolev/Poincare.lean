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
  Best constant approximation in \(L^2\)
statement:
  On a finite measure space, every real \(u\in L^2(\mu)\) admits a constant
  \(c\) such that
  \[\lVert u-c\rVert_{L^2(\mu)}\le\lVert u-a\rVert_{L^2(\mu)}
    \quad\text{for every }a\in\mathbb R.\]
proof:
  The constant functions form a closed finite-dimensional subspace of
  \(L^2(\mu)\). Take the orthogonal projection of \(u\) onto this subspace;
  the projection minimizes distance.
-/
private theorem exists_L2_best_center_on_finite_measure
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {u₀ : X → ℝ}
    (hu₀_mem : MemLp u₀ 2 μ) :
    ∃ center : ℝ,
      ∀ a : ℝ,
        eLpNorm (fun x : X ↦ u₀ x - center) 2 μ ≤
        eLpNorm (fun x : X ↦ u₀ x - a) 2 μ := by
  classical
  let L : ℝ →L[ℝ] Lp ℝ (2 : ℝ≥0∞) μ :=
    Lp.constL (2 : ℝ≥0∞) μ ℝ
  let K : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) μ) :=
    LinearMap.range L.toLinearMap
  haveI : FiniteDimensional ℝ K := by
    dsimp [K]
    infer_instance
  have hK_closed : IsClosed (K : Set (Lp ℝ (2 : ℝ≥0∞) μ)) :=
    Submodule.closed_of_finiteDimensional K
  haveI : CompleteSpace K := hK_closed.completeSpace_coe
  haveI : K.HasOrthogonalProjection := inferInstance
  let F : Lp ℝ (2 : ℝ≥0∞) μ := hu₀_mem.toLp u₀
  let p : Lp ℝ (2 : ℝ≥0∞) μ := K.starProjection F
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
        eLpNorm (fun x : X ↦ u₀ x - center) 2 μ := by
    simpa [F, L, Pi.sub_apply] using
      (Lp.edist_toLp_toLp u₀ (fun _ : X ↦ center)
        hu₀_mem
        (memLp_const center :
          MemLp (fun _ : X ↦ center) 2 μ))
  have ha_edist :
      edist F (L a) =
        eLpNorm (fun x : X ↦ u₀ x - a) 2 μ := by
    simpa [F, L, Pi.sub_apply] using
      (Lp.edist_toLp_toLp u₀ (fun _ : X ↦ a)
        hu₀_mem
        (memLp_const a :
          MemLp (fun _ : X ↦ a) 2 μ))
  calc
    eLpNorm (fun x : X ↦ u₀ x - center) 2 μ
        = edist F (L center) := hcenter_edist.symm
    _ = edist F p := by rw [hp_eq]
    _ ≤ edist F (L a) := hed_min
    _ = eLpNorm (fun x : X ↦ u₀ x - a) 2 μ := ha_edist

/--
%%handwave
name:
  Best constant approximation on a compact surface set
statement:
  Let \(K\) be compact in a surface with background volume. If
  \(u\in L^2(K)\), then some constant \(c\) minimizes
  \(\lVert u-a\rVert_{L^2(K)}\) over all \(a\in\mathbb R\).
proof:
  Background surface volume is finite on compact sets, so its restriction to
  \(K\) is finite. Apply [existence of a best constant on a finite measure space](lean:exists_L2_best_center_on_finite_measure).
-/
private theorem surface_exists_L2_best_center_on_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (hK : IsCompact K) {u₀ : X → ℝ}
    (hu₀_mem : MemLp u₀ 2 (g.volume.restrict K)) :
    ∃ center : ℝ,
      ∀ a : ℝ,
        eLpNorm (fun x : X ↦ u₀ x - center) 2 (g.volume.restrict K) ≤
        eLpNorm (fun x : X ↦ u₀ x - a) 2 (g.volume.restrict K) := by
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  haveI : IsFiniteMeasure (g.volume.restrict K) := by
    exact isFiniteMeasure_restrict.2 hK.measure_ne_top
  exact exists_L2_best_center_on_finite_measure hu₀_mem

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
  Rellich extraction on compact subsets of a bounded ball
statement:
  Let \(K\subset\operatorname{int}Q\subset Q\subset B\subset\Omega\), with
  \(K,Q\) compact and \(B\) a Euclidean ball.  A scalar weak Sobolev sequence
  that is uniformly \(W^{1,2}\)-bounded on \(B\) has a subsequence converging
  strongly in \(L^2(K)\).
proof:
  Restrict the uniform \(W^{1,2}\)-bound from the ball to \(Q\), then apply
  the Euclidean Rellich compactness theorem on compact inclusions.
-/
theorem euclideanSobolev_bounded_subsequence_on_compact_of_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {c : H} {r : ℝ} {K Q : Set H}
    (hK : IsCompact K)
    (hKQ : K ⊆ interior Q)
    (hQball : Q ⊆ Metric.ball c r)
    (hQ : IsCompact Q)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded :
      BoundedInEuclideanLocalSobolevH1WithValues
        (Metric.ball c r) u du) :
    ∃ (uLim : H → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoInEuclideanLocalL2Scalar K (fun n z ↦ u (φ n) z) uLim := by
  have hboundedQ :
      BoundedInEuclideanLocalSobolevH1WithValues Q u du :=
    BoundedInEuclideanLocalSobolevH1WithValues.mono_set hQball hbounded
  exact
    euclideanRellichKondrachov_subsequence_on_compact
      hK hKQ (hQball.trans hballΩ) hQ hΩ_open u du hweak hboundedQ

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
  Compact-subball Cauchy extraction for selected bounded Sobolev sequences
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  For any standard compact subball and any selected subsequence of a uniformly
  \(W^{1,2}(B(c,r))\)-bounded scalar weak Sobolev sequence, there is a further
  subsequence which is Cauchy in \(L^2\) on that compact subball.
proof:
  Apply compact Rellich extraction to the chosen compact subball, with the
  next standard compact subball as the containing compact set.  The resulting
  strong \(L^2\)-convergent subsubsequence is Cauchy in the corresponding
  \(L^2\) space.
-/
theorem euclideanSobolev_bounded_selected_subsequence_cauchy_on_standard_subball
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
    (k : ℕ) (f : ℕ → ℕ) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧
      CauchySeq
        (fun n : ℕ ↦
          ((hmem_exhaustion_all k (f (θ n))).toLp (u (f (θ n))) :
            Lp ℝ 2
              (MeasureTheory.volume.restrict
                (Metric.closedBall c
                  (r * (((k : ℝ) + 1) / ((k : ℝ) + 2))))))) := by
  rcases
    euclideanSobolev_bounded_compact_containment_on_standard_subball
      hr_pos hΩ_open hballΩ hweak hbounded hmem_exhaustion_all k with
    ⟨S, hS_compact, hS_mem⟩
  rcases
    cauchy_subsequence_of_compact_containment
      (fun n : ℕ ↦
        ((hmem_exhaustion_all k n).toLp (u n) :
          Lp ℝ 2
            (MeasureTheory.volume.restrict
              (Metric.closedBall c
                (r * (((k : ℝ) + 1) / ((k : ℝ) + 2)))))))
      hS_compact hS_mem f with
    ⟨θ, hθ, hcauchy⟩
  exact ⟨θ, hθ, hcauchy⟩

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
  Radial contraction estimate in polar coordinates
statement:
  Let \(0<a\le1\).  For a scalar weak Sobolev function on the unit ball, the
  radial difference between \(w(r\theta)\) and \(w(ar\theta)\) is bounded for
  almost every polar pair \((\theta,r)\), \(0<r<1\), by the corresponding
  radial segment integral of the weak derivative.
proof:
  Apply [the radial absolute-continuity estimate](lean:JJMath.Uniformization.scalarWeakSobolev_radial_contraction_segmentIntegral_bound_ae)
  with center \(0\) and radius \(1\), then transfer the resulting
  almost-everywhere statement to polar coordinates.
-/
theorem scalarWeakSobolev_unit_ball_radial_contraction_segmentIntegral_bound_ae_polar
    {a : ℝ}
    (ha_pos : 0 < a)
    (ha_le_one : a ≤ 1)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∀ᵐ p ∂((MeasureTheory.volume : Measure H).toSphere.prod
        ((MeasureTheory.Measure.volumeIoiPow
          (Module.finrank ℝ H - 1)).restrict
            {r : Set.Ioi (0 : ℝ) | (r : ℝ) < 1})),
      ‖w ((p.2 : ℝ) • (p.1 : H)) -
          w (a • ((p.2 : ℝ) • (p.1 : H)))‖ ≤
        euclideanRadialContractionGradientSegmentIntegral
          dw (0 : H) a ((p.2 : ℝ) • (p.1 : H)) := by
  have hvol :
      ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball (0 : H) 1),
        ‖w z - w (a • z)‖ ≤
          euclideanRadialContractionGradientSegmentIntegral dw (0 : H) a z := by
    have hraw :
        ∀ᵐ z ∂MeasureTheory.volume.restrict (Metric.ball (0 : H) 1),
          ‖w z - w ((0 : H) + a • (z - (0 : H)))‖ ≤
            euclideanRadialContractionGradientSegmentIntegral dw (0 : H) a z :=
      scalarWeakSobolev_radial_contraction_segmentIntegral_bound_ae
        (Ω := Metric.ball (0 : H) 1)
        (c := (0 : H)) (r := (1 : ℝ)) (a := a)
        (by norm_num) ha_pos ha_le_one Metric.isOpen_ball
        (Set.Subset.rfl) hweak hw hdw
    filter_upwards [hraw] with z hz
    simpa using hz
  exact
    ae_polar_product_unitBall_of_ae_volume_unitBall
      (P := fun z : H ↦
        ‖w z - w (a • z)‖ ≤
          euclideanRadialContractionGradientSegmentIntegral dw (0 : H) a z)
      hvol

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
  Vanishing-gradient compactness on a closed Euclidean ball
statement:
  Let \(B(c,r)\) be contained in an open finite-dimensional Euclidean region.
  If a scalar weak Sobolev sequence is uniformly \(L^2\)-bounded on the closed
  ball \(\overline B(c,r)\), its weak derivatives are square-integrable on
  \(B(c,r)\), and the derivative \(L^2(B(c,r))\)-norms tend to zero, then a
  subsequence converges strongly in \(L^2(\overline B(c,r))\) to one constant.
proof:
  The open-ball theorem gives convergence on \(B(c,r)\).  The boundary sphere
  has Euclidean measure zero, so the restricted Lebesgue measures of the open
  and closed balls are equal; hence the same convergence holds on the closed
  ball.
-/
theorem euclideanSobolev_vanishingGradient_subsequence_constant_on_closed_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {u : ℕ → H → ℝ} {du : ℕ → H → H →L[ℝ] ℝ}
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hvalue_memLp : ∀ n : ℕ, MemLp (u n) 2
      (MeasureTheory.volume.restrict (Metric.closedBall c r)))
    (hderivative_memLp : ∀ n : ℕ, MemLp (du n) 2
      (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hvalue_bound :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (u n) 2
          (MeasureTheory.volume.restrict (Metric.closedBall c r)) ≤ C)
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
            (MeasureTheory.volume.restrict (Metric.closedBall c r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  have hball_closed : Metric.ball c r ⊆ Metric.closedBall c r :=
    Metric.ball_subset_closedBall
  have hμ_ball_le :
      MeasureTheory.volume.restrict (Metric.ball c r) ≤
        MeasureTheory.volume.restrict (Metric.closedBall c r) :=
    Measure.restrict_mono hball_closed le_rfl
  have hvalue_memLp_ball :
      ∀ n : ℕ, MemLp (u n) 2
        (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    intro n
    exact (hvalue_memLp n).mono_measure hμ_ball_le
  have hvalue_bound_ball :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (u n) 2
          (MeasureTheory.volume.restrict (Metric.ball c r)) ≤ C := by
    rcases hvalue_bound with ⟨C, hC_top, hC⟩
    refine ⟨C, hC_top, fun n ↦ ?_⟩
    exact (eLpNorm_mono_measure (u n) hμ_ball_le).trans (hC n)
  rcases
    euclideanSobolev_vanishingGradient_subsequence_constant_on_ball
      hr_pos hΩ_open hballΩ hweak hvalue_memLp_ball
      hderivative_memLp hvalue_bound_ball hgradient_tendsto_zero with
    ⟨a, φ, hφ, hconv⟩
  refine ⟨a, φ, hφ, ?_⟩
  have hsphere_zero :
      MeasureTheory.volume (Metric.sphere c r : Set H) = 0 :=
    euclidean_volume_sphere_zero (c := c) (r := r) hr_pos
  have hclosed_eq_ball_ae :
      Metric.closedBall c r =ᵐ[MeasureTheory.volume] Metric.ball c r := by
    filter_upwards [compl_mem_ae_iff.mpr hsphere_zero] with y hy_not_sphere
    by_cases hy_closed : y ∈ Metric.closedBall c r
    · have hy_le : dist y c ≤ r := by
        simpa [Metric.mem_closedBall] using hy_closed
      apply propext
      constructor
      · intro _hy
        have hy_ne : dist y c ≠ r := by
          intro hy_eq
          exact hy_not_sphere (by simpa [Metric.mem_sphere] using hy_eq)
        exact (lt_of_le_of_ne hy_le hy_ne)
      · intro hy_ball
        exact Metric.ball_subset_closedBall hy_ball
    · apply propext
      constructor
      · intro hy
        exact False.elim (hy_closed hy)
      · intro hy_ball
        exact False.elim (hy_closed (Metric.ball_subset_closedBall hy_ball))
  have hμ_restrict :
      MeasureTheory.volume.restrict (Metric.closedBall c r) =
        MeasureTheory.volume.restrict (Metric.ball c r) :=
    Measure.restrict_congr_set hclosed_eq_ball_ae
  simpa [hμ_restrict] using hconv

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
private theorem complex_euclideanSobolev_poincare_L2_on_ball_self
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
  Dirichlet seminorm is definite on \(H^1_0\)
statement:
  The Dirichlet seminorm is a norm on the homogeneous zero-trace Sobolev
  space when zero Dirichlet energy forces zero local \(L^2\) mass on every
  compact set.
-/
def DirichletSeminormIsNormOnH10 {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) : Prop :=
  ∀ u : SobolevH1ZeroOnSurface g.volume,
    greenDirichletSeminormSq g u = 0 →
      ∀ K : Set X, IsCompact K → greenLocalL2SeminormSq g K u = 0

/--
%%handwave
name:
  Capacitary Poincare inequality
statement:
  The capacitary Poincare inequality says that, on every compact set, the
  local \(L^2\) mass of a zero-trace Sobolev function is bounded by a constant
  times its Dirichlet energy.
-/
def HasCapacitaryPoincareInequality {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) : Prop :=
  ∀ K : Set X, IsCompact K →
    ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h

/--
%%handwave
name:
  Poincare gives definiteness of the Dirichlet norm
statement:
  If the capacitary Poincare inequality holds, then zero Dirichlet energy
  forces zero local \(L^2\) mass on every compact set.
proof:
  Apply the Poincare inequality on each compact set.  When the Dirichlet
  energy is zero, the right-hand side is zero, while the local \(L^2\) mass is
  nonnegative.
-/
theorem dirichletSeminorm_isNorm_of_capacitary_poincare
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (hpoincare : HasCapacitaryPoincareInequality g) :
    DirichletSeminormIsNormOnH10 g := by
  intro u hu K hK
  rcases hpoincare K hK with ⟨P, _hP_nonneg, hP⟩
  have hlocal_nonneg : 0 ≤ greenLocalL2SeminormSq g K u :=
    greenLocalL2SeminormSq_nonneg g K u
  have hlocal_le_zero : greenLocalL2SeminormSq g K u ≤ 0 := by
    simpa [hu] using hP u
  exact le_antisymm hlocal_le_zero hlocal_nonneg

/--
%%handwave
name:
  Local \(L^2\) mass is monotone in the set
statement:
  If \(K\subset Q\), then the local \(L^2\) mass of a zero-trace Sobolev
  function on \(K\) is no larger than its local \(L^2\) mass on \(Q\).
proof:
  The integrand is the nonnegative function \(h^2\).  Since \(h\) is globally
  square-integrable, \(h^2\) is integrable on \(Q\), and monotonicity of
  nonnegative set integrals gives the result.
-/
theorem greenLocalL2SeminormSq_mono_set
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K Q : Set X}
    (hKQ : K ⊆ Q) (h : SobolevH1ZeroOnSurface g.volume) :
    greenLocalL2SeminormSq g K h ≤ greenLocalL2SeminormSq g Q h := by
  dsimp [greenLocalL2SeminormSq]
  have hIntQ : IntegrableOn (fun x : X ↦ h x ^ (2 : ℕ)) Q g.volume := by
    exact h.memLp_toFun.integrable_sq.integrableOn
  exact setIntegral_mono_set hIntQ
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (h x)))
    (ae_of_all _ hKQ)

/--
%%handwave
name:
  Failure of local control persists on larger compact sets
statement:
  If no Dirichlet constant controls the local \(L^2\) mass on \(K\), and
  \(K\subset Q\), then no such constant controls the local \(L^2\) mass on
  \(Q\).
proof:
  A bound on \(Q\) would imply the same bound on \(K\) by monotonicity of the
  nonnegative local \(L^2\) integral.
-/
theorem no_localL2_control_mono_superset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K Q : Set X}
    (hKQ : K ⊆ Q)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h) :
    ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      greenLocalL2SeminormSq g Q h ≤ P * greenDirichletSeminormSq g h := by
  intro hQcontrol
  apply hfail
  rcases hQcontrol with ⟨P, hP_nonneg, hP⟩
  refine ⟨P, hP_nonneg, ?_⟩
  intro h
  exact (greenLocalL2SeminormSq_mono_set hKQ h).trans (hP h)

/--
%%handwave
name:
  A relatively compact neighborhood still has failed control
statement:
  On a Riemann surface, if local \(L^2\) control fails on a compact set
  \(K\), then there is an open neighborhood \(Q\) of \(K\) with compact
  closure such that the same local \(L^2\)-Dirichlet estimate fails on
  \(\overline Q\).
proof:
  Choose an open neighborhood \(Q\supset K\) with compact closure.  Since
  \(K\subset \overline Q\), any estimate on \(\overline Q\) would restrict to
  an estimate on \(K\), contradicting the assumed failure.
-/
theorem exists_relcompact_open_superset_with_no_localL2_control
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X) (hK : IsCompact K)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h) :
    ∃ Q : Set X, IsOpen Q ∧ K ⊆ Q ∧ IsCompact (closure Q) ∧
      ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
        greenLocalL2SeminormSq g (closure Q) h ≤
          P * greenDirichletSeminormSq g h := by
  rcases exists_isOpen_superset_and_isCompact_closure hK with
    ⟨Q, hQ_open, hKQ, hQ_compact⟩
  refine ⟨Q, hQ_open, hKQ, hQ_compact, ?_⟩
  exact no_localL2_control_mono_superset
    (g := g) ((hKQ.trans subset_closure)) hfail

/--
%%handwave
name:
  Failure of finite-energy local control persists on larger compact sets
statement:
  If local \(L^2\)-Dirichlet control fails on \(K\) even after restricting to
  finite-energy zero-trace functions, and \(K\subset Q\), then the same
  restricted control fails on \(Q\).
proof:
  A restricted estimate on \(Q\) would imply the same restricted estimate on
  \(K\) by monotonicity of the nonnegative local \(L^2\) integral.
-/
theorem no_localL2_control_mono_superset_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K Q : Set X}
    (hKQ : K ⊆ Q)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
        greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h) :
    ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
        greenLocalL2SeminormSq g Q h ≤ P * greenDirichletSeminormSq g h := by
  intro hQcontrol
  apply hfail
  rcases hQcontrol with ⟨P, hP_nonneg, hP⟩
  refine ⟨P, hP_nonneg, ?_⟩
  intro h hInt
  exact (greenLocalL2SeminormSq_mono_set hKQ h).trans (hP h hInt)

/--
%%handwave
name:
  A relatively compact neighborhood still has failed finite-energy control
statement:
  On a Riemann surface, if local \(L^2\)-Dirichlet control fails on a compact
  set among finite-energy zero-trace functions, then the failure persists on
  the closure of some relatively compact open neighborhood of the compact set.
proof:
  Choose a relatively compact open neighborhood.  Since the original compact
  set lies in the closure of that neighborhood, any restricted estimate on the
  closure would restrict back to the original compact set.
-/
theorem exists_relcompact_open_superset_with_no_localL2_control_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X) (hK : IsCompact K)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
        greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h) :
    ∃ Q : Set X, IsOpen Q ∧ K ⊆ Q ∧ IsCompact (closure Q) ∧
      ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
        Integrable
          (fun x : X ↦
            g.gradientInner x (h.weakGradient x) (h.weakGradient x))
          g.volume →
        greenLocalL2SeminormSq g (closure Q) h ≤
          P * greenDirichletSeminormSq g h := by
  rcases exists_isOpen_superset_and_isCompact_closure hK with
    ⟨Q, hQ_open, hKQ, hQ_compact⟩
  refine ⟨Q, hQ_open, hKQ, hQ_compact, ?_⟩
  exact no_localL2_control_mono_superset_of_integrable
    (g := g) ((hKQ.trans subset_closure)) hfail

/--
%%handwave
name:
  Bad sequences have positive local mass
statement:
  If a sequence has local \(L^2\) mass dominating its Dirichlet energy on a
  set by nonnegative factors, then each local \(L^2\) mass is positive.
proof:
  The Dirichlet energy and the domination factor are nonnegative.  Since
  their product is strictly smaller than the local \(L^2\) mass, that mass is
  strictly positive.
-/
theorem bad_localL2_sequence_localL2_pos
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (H : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hH : ∀ n : ℕ,
      (n : ℝ) * greenDirichletSeminormSq g (H n) <
        greenLocalL2SeminormSq g K (H n)) :
    ∀ n : ℕ, 0 < greenLocalL2SeminormSq g K (H n) := by
  intro n
  have hD_nonneg : 0 ≤ greenDirichletSeminormSq g (H n) :=
    greenDirichletSeminormSq_nonneg g (H n)
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact lt_of_le_of_lt (mul_nonneg hn_nonneg hD_nonneg) (hH n)

/--
%%handwave
name:
  Shifted bad sequences have vanishing normalized energy
statement:
  If the local \(L^2\) mass of a sequence dominates its Dirichlet energy by
  the factors \(0,1,2,\ldots\), then after dropping the zeroth term the ratio
  of Dirichlet energy to local \(L^2\) mass tends to zero.
proof:
  The domination inequality for the \((n+1)\)-st term gives
  \(D_{n+1}/M_{n+1}\le 1/(n+1)\), where \(D\) is Dirichlet energy and \(M\)
  is local \(L^2\) mass.  The local masses are positive, and
  \(1/(n+1)\to0\), so the squeeze theorem applies.
-/
theorem bad_localL2_sequence_shifted_dirichlet_div_localL2_tendsto_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (H : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hH : ∀ n : ℕ,
      (n : ℝ) * greenDirichletSeminormSq g (H n) <
        greenLocalL2SeminormSq g K (H n)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        greenDirichletSeminormSq g (H (n + 1)) /
          greenLocalL2SeminormSq g K (H (n + 1)))
      Filter.atTop (𝓝 0) := by
  have hpos : ∀ n : ℕ, 0 < greenLocalL2SeminormSq g K (H n) :=
    bad_localL2_sequence_localL2_pos H hH
  have hnonneg : ∀ n : ℕ,
      0 ≤ greenDirichletSeminormSq g (H (n + 1)) /
        greenLocalL2SeminormSq g K (H (n + 1)) := by
    intro n
    exact div_nonneg (greenDirichletSeminormSq_nonneg g (H (n + 1)))
      (hpos (n + 1)).le
  have hle : ∀ n : ℕ,
      greenDirichletSeminormSq g (H (n + 1)) /
          greenLocalL2SeminormSq g K (H (n + 1)) ≤
        ((n : ℝ) + 1)⁻¹ := by
    intro n
    let D : ℝ := greenDirichletSeminormSq g (H (n + 1))
    let M : ℝ := greenLocalL2SeminormSq g K (H (n + 1))
    let c : ℝ := (n : ℝ) + 1
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    have hM_pos : 0 < M := by
      simpa [M] using hpos (n + 1)
    have hdom : c * D < M := by
      simpa [c, D, M, Nat.cast_add, Nat.cast_one] using hH (n + 1)
    have hmul_div : c * (D / M) < 1 := by
      have h' : c * D / M < 1 := (div_lt_one hM_pos).2 hdom
      simpa [mul_div_assoc] using h'
    have hmul_lt :
        c⁻¹ * (c * (D / M)) < c⁻¹ * 1 :=
      mul_lt_mul_of_pos_left hmul_div (inv_pos.mpr hc_pos)
    have hcancel : c⁻¹ * (c * (D / M)) = D / M := by
      rw [← mul_assoc, inv_mul_cancel₀ hc_pos.ne', one_mul]
    have hratio_lt : D / M < c⁻¹ := by
      simpa [hcancel] using hmul_lt
    exact le_of_lt (by simpa [D, M, c] using hratio_lt)
  have hupper :
      Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹)
        Filter.atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact squeeze_zero hnonneg hle hupper

/-- Smooth compactly supported surface tests are closed under real scalar multiplication. -/
def SmoothCompactlySupportedGlobalSurfaceFunction.const_smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℝ) (F : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    SmoothCompactlySupportedGlobalSurfaceFunction X where
  toFun := fun x ↦ c * F x
  gradient := fun x ↦ c • F.gradient x
  smooth := by
    intro e he
    have hF := F.smooth e he
    simpa [smul_eq_mul] using contDiffOn_const.mul hF
  gradient_eq := by
    intro e he z hz v
    have hdiff :
        DifferentiableAt ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z :=
      surfaceFunctionChartRepresentative_differentiableAt e he F.toFun F.smooth z hz
    have hfd :
        fderiv ℝ (fun w : ℂ ↦ c * F.toFun (e.symm w)) z =
          c • fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z := by
      simpa [smul_eq_mul] using
        fderiv_const_mul (𝕜 := ℝ)
          (a := fun w : ℂ ↦ F.toFun (e.symm w)) (x := z) hdiff c
    calc
      (c • F.gradient (e.symm z)) (surfaceChartTangentMap e z v)
          = c * F.gradient (e.symm z) (surfaceChartTangentMap e z v) := by
              simp
      _ = c * fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z v := by
              rw [F.gradient_eq e he z hz v]
      _ = (c • fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z) v := by
              simp [smul_eq_mul]
      _ = fderiv ℝ (fun w : ℂ ↦ c * F.toFun (e.symm w)) z v := by
              rw [hfd]
  compact_support := by
    simpa [smul_eq_mul] using
      hasCompactSupportOnSurface_mul_left
        (u := fun _ : X ↦ c) (v := F.toFun) F.compact_support

/--
%%handwave
name:
  Scalar multiplication preserves convergence in zero-trace \(H^1\)
statement:
  If \(u_n\to u\) in global zero-trace \(H^1\), then
  \(c\,u_n\to c\,u\) in the same topology for every \(c\in\mathbb R\).
proof:
  Scalar multiplication is continuous in the Sobolev norm; both the function
  and weak-gradient differences are multiplied by \(c\).
-/
theorem TendstoInGlobalSobolevH1Zero.const_smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {μ : Measure X} {F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X}
    {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ} (c : ℝ)
    (hF : TendstoInGlobalSobolevH1Zero μ F u du) :
    TendstoInGlobalSobolevH1Zero μ
      (fun n : ℕ ↦
        SmoothCompactlySupportedGlobalSurfaceFunction.const_smul c (F n))
      (c • u) (c • du) := by
  rcases hF with ⟨hval, hgrad⟩
  have hc_ne_top : ‖c‖ₑ ≠ (∞ : ℝ≥0∞) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_ne_top
  constructor
  · have hmul₀ :
        Filter.Tendsto
          (fun n : ℕ ↦
            ‖c‖ₑ *
              eLpNorm (fun x ↦ F n x - u x) 2 μ)
          Filter.atTop (𝓝 (‖c‖ₑ * 0)) :=
      ENNReal.Tendsto.const_mul hval (Or.inr hc_ne_top)
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            ‖c‖ₑ *
              eLpNorm (fun x ↦ F n x - u x) 2 μ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa using hmul₀
    refine hmul.congr' ?_
    filter_upwards [] with n
    calc
      ‖c‖ₑ * eLpNorm (fun x ↦ F n x - u x) 2 μ
          = eLpNorm (fun x ↦ c • (F n x - u x)) 2 μ := by
              exact (eLpNorm_const_smul
                (μ := μ) (c := c)
                (f := fun x ↦ F n x - u x) (p := (2 : ℝ≥0∞))).symm
      _ = eLpNorm
            (fun x ↦
              (SmoothCompactlySupportedGlobalSurfaceFunction.const_smul c (F n)) x -
                (c • u) x) 2 μ := by
              congr 1
              ext x
              simp [SmoothCompactlySupportedGlobalSurfaceFunction.const_smul,
                smul_eq_mul, mul_sub]
  · have hmul₀ :
        Filter.Tendsto
          (fun n : ℕ ↦
            ‖c‖ₑ *
              eLpNorm (fun x ↦ (F n).gradient x - du x) 2 μ)
          Filter.atTop (𝓝 (‖c‖ₑ * 0)) :=
      ENNReal.Tendsto.const_mul hgrad (Or.inr hc_ne_top)
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            ‖c‖ₑ *
              eLpNorm (fun x ↦ (F n).gradient x - du x) 2 μ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa using hmul₀
    refine hmul.congr' ?_
    filter_upwards [] with n
    calc
      ‖c‖ₑ * eLpNorm (fun x ↦ (F n).gradient x - du x) 2 μ
          = eLpNorm (fun x ↦ c • ((F n).gradient x - du x)) 2 μ := by
              exact (eLpNorm_const_smul
                (μ := μ) (c := c)
                (f := fun x ↦ (F n).gradient x - du x)
                (p := (2 : ℝ≥0∞))).symm
      _ = eLpNorm
            (fun x ↦
              (SmoothCompactlySupportedGlobalSurfaceFunction.const_smul c
                (F n)).gradient x - (c • du) x) 2 μ := by
              congr 1
              ext x
              simp [SmoothCompactlySupportedGlobalSurfaceFunction.const_smul,
                sub_eq_add_neg, smul_add, smul_neg]

/--
%%handwave
name:
  Scalar multiples preserve zero Sobolev trace
statement:
  If \(u\) has global zero Sobolev trace, then \(cu\) has global zero
  Sobolev trace, with weak gradient \(c\,du\).
proof:
  Multiply a compactly supported smooth approximating sequence by \(c\) and
  use scalar-multiplication continuity of zero-trace \(H^1\) convergence.
-/
theorem HasGlobalZeroSobolevTrace.const_smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {μ : Measure X} {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ} (c : ℝ)
    (h : HasGlobalZeroSobolevTrace μ u du) :
    HasGlobalZeroSobolevTrace μ (c • u) (c • du) := by
  rcases h with ⟨F, hF⟩
  exact ⟨fun n ↦
    SmoothCompactlySupportedGlobalSurfaceFunction.const_smul c (F n),
    hF.const_smul c⟩

/-- Zero-trace surface Sobolev functions are closed under real scalar multiplication. -/
def SobolevH1ZeroOnSurface.const_smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} (c : ℝ)
    (u : SobolevH1ZeroOnSurface μ) : SobolevH1ZeroOnSurface μ where
  toFun := c • u.toFun
  weakGradient := c • u.weakGradient
  memLp_toFun := u.memLp_toFun.const_smul c
  memLp_weakGradient := u.memLp_weakGradient.const_smul c
  weakGradient_is_gradient := u.weakGradient_is_gradient.const_smul c
  zero_trace := u.zero_trace.const_smul c

/--
%%handwave
name:
  Quadratic scaling of the local \(L^2\) seminorm
statement:
  For every measurable \(K\),
  \(\lVert cu\rVert_{L^2(K)}^2=c^2\lVert u\rVert_{L^2(K)}^2\).
proof:
  Move the constant through the squared absolute value and through the
  integral.
-/
theorem greenLocalL2SeminormSq_const_smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (c : ℝ) (u : SobolevH1ZeroOnSurface g.volume) :
    greenLocalL2SeminormSq g K (SobolevH1ZeroOnSurface.const_smul c u) =
      c ^ 2 * greenLocalL2SeminormSq g K u := by
  dsimp [greenLocalL2SeminormSq, SobolevH1ZeroOnSurface.const_smul]
  calc
    ∫ x in K, (c * u.toFun x) ^ 2 ∂g.volume =
        ∫ x in K, c ^ 2 * u.toFun x ^ 2 ∂g.volume := by
          refine integral_congr_ae ?_
          filter_upwards [] with x
          ring
    _ = c ^ 2 * ∫ x in K, u.toFun x ^ 2 ∂g.volume := by
          rw [integral_const_mul]

/--
%%handwave
name:
  Linearity of the cotangent inner product in the second argument
statement:
  For the cotangent inner product induced by a metric,
  \(\langle\xi,c\eta\rangle=c\langle\xi,\eta\rangle\).
proof:
  Express the cotangent inner product via the inverse metric and use linearity
  of evaluation in the second cotangent vector.
-/
theorem cotangentInner_smul_right_of_isMetricDual
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (cotangentInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (hinner : IsCotangentInnerForSurfaceMetric metric cotangentInner)
    (x : X) (ξ η : ℂ →L[ℝ] ℝ) (c : ℝ) :
    cotangentInner x ξ (c • η) = c * cotangentInner x ξ η := by
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  rcases hinner x ξ with ⟨v, hv, _hv_unique⟩
  calc
    cotangentInner x ξ (c • η) = (c • η) v := hv.2 (c • η)
    _ = c * η v := by simp
    _ = c * cotangentInner x ξ η := by rw [hv.2 η]

/--
%%handwave
name:
  Quadratic scaling of the surface gradient pairing
statement:
  For a background surface metric,
  \(\langle c\xi,c\xi\rangle_g=c^2\langle\xi,\xi\rangle_g\).
proof:
  Apply linearity of the cotangent inner product in each argument and collect
  the two scalar factors.
-/
theorem BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (x : X) (ξ : ℂ →L[ℝ] ℝ) (c : ℝ) :
    g.gradientInner x (c • ξ) (c • ξ) =
      c ^ 2 * g.gradientInner x ξ ξ := by
  calc
    g.gradientInner x (c • ξ) (c • ξ)
        = c * g.gradientInner x (c • ξ) ξ :=
            cotangentInner_smul_right_of_isMetricDual
              g.metric g.gradientInner (BackgroundSurfaceMetricOnSurface.gradientInner_isMetricDual g) x
              (c • ξ) ξ c
    _ = c * g.gradientInner x ξ (c • ξ) := by
            rw [BackgroundSurfaceMetricOnSurface.gradientInner_symm g x (c • ξ) ξ]
    _ = c * (c * g.gradientInner x ξ ξ) := by
            rw [cotangentInner_smul_right_of_isMetricDual
              g.metric g.gradientInner (BackgroundSurfaceMetricOnSurface.gradientInner_isMetricDual g) x ξ ξ c]
    _ = c ^ 2 * g.gradientInner x ξ ξ := by ring

/--
%%handwave
name:
  Quadratic scaling of Dirichlet energy
statement:
  For \(u\in W^{1,2}_0(X)\) and \(c\in\mathbb R\),
  \(\mathcal E(cu)=c^2\mathcal E(u)\).
proof:
  The weak gradient of \(cu\) is \(c\,du\); apply quadratic scaling of the
  metric gradient pairing under the integral.
-/
theorem greenDirichletSeminormSq_const_smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (c : ℝ) (u : SobolevH1ZeroOnSurface g.volume) :
    greenDirichletSeminormSq g (SobolevH1ZeroOnSurface.const_smul c u) =
      c ^ 2 * greenDirichletSeminormSq g u := by
  dsimp [greenDirichletSeminormSq, SobolevH1ZeroOnSurface.const_smul]
  calc
    ∫ x, g.gradientInner x (c • u.weakGradient x)
        (c • u.weakGradient x) ∂g.volume =
        ∫ x, c ^ 2 *
          g.gradientInner x (u.weakGradient x) (u.weakGradient x) ∂g.volume := by
          refine integral_congr_ae ?_
          filter_upwards [] with x
          exact
            BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul
              g x (u.weakGradient x) c
    _ = c ^ 2 *
        ∫ x, g.gradientInner x (u.weakGradient x) (u.weakGradient x) ∂g.volume := by
          rw [integral_const_mul]

/--
%%handwave
name:
  Local \(L^2\) normalization of a bad sequence
statement:
  If a sequence of zero-trace Sobolev functions has positive local \(L^2\)
  mass on a fixed measurable set and its Dirichlet energy divided by that
  mass tends to zero, then after rescaling each term there is a new sequence
  with local \(L^2\) mass one and Dirichlet energy tending to zero.
proof:
  Multiply the \(n\)-th function by the reciprocal square root of its local
  \(L^2\) mass.  The local \(L^2\) mass then becomes one, and the Dirichlet
  energy becomes exactly the old energy divided by the old local mass.
-/
theorem exists_unit_localL2_sequence_with_dirichlet_tendsto_zero_of_positive_localL2_ratio_tendsto
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (H : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hH_pos : ∀ n : ℕ, 0 < greenLocalL2SeminormSq g K (H n))
    (hH_ratio :
      Filter.Tendsto
        (fun n : ℕ ↦
          greenDirichletSeminormSq g (H n) /
            greenLocalL2SeminormSq g K (H n))
        Filter.atTop (𝓝 0)) :
    ∃ Z : ℕ → SobolevH1ZeroOnSurface g.volume,
      (∀ n : ℕ, greenLocalL2SeminormSq g K (Z n) = 1) ∧
        Filter.Tendsto
          (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
          Filter.atTop (𝓝 0) := by
  let scale : ℕ → ℝ :=
    fun n : ℕ ↦ (Real.sqrt (greenLocalL2SeminormSq g K (H n)))⁻¹
  let Z : ℕ → SobolevH1ZeroOnSurface g.volume :=
    fun n : ℕ ↦ SobolevH1ZeroOnSurface.const_smul (scale n) (H n)
  refine ⟨Z, ?_, ?_⟩
  · intro n
    let M : ℝ := greenLocalL2SeminormSq g K (H n)
    have hM_pos : 0 < M := by
      simpa [M] using hH_pos n
    have hsqrt_sq : (Real.sqrt M) ^ 2 = M :=
      Real.sq_sqrt hM_pos.le
    have hsqrt_ne : Real.sqrt M ≠ 0 :=
      (Real.sqrt_pos.2 hM_pos).ne'
    have hscale_sq_mul : (scale n) ^ 2 * M = 1 := by
      calc
        (scale n) ^ 2 * M =
            (Real.sqrt M)⁻¹ ^ 2 * M := by
              simp [scale, M]
        _ = (Real.sqrt M)⁻¹ ^ 2 * (Real.sqrt M) ^ 2 := by
              rw [hsqrt_sq]
        _ = 1 := by
              field_simp [hsqrt_ne]
    calc
      greenLocalL2SeminormSq g K (Z n)
          = (scale n) ^ 2 * greenLocalL2SeminormSq g K (H n) := by
              simpa [Z] using
                greenLocalL2SeminormSq_const_smul
                  (g := g) (K := K) (scale n) (H n)
      _ = 1 := by
              simpa [M] using hscale_sq_mul
  · refine hH_ratio.congr' ?_
    filter_upwards [] with n
    symm
    let M : ℝ := greenLocalL2SeminormSq g K (H n)
    let D : ℝ := greenDirichletSeminormSq g (H n)
    have hM_pos : 0 < M := by
      simpa [M] using hH_pos n
    have hsqrt_sq : (Real.sqrt M) ^ 2 = M :=
      Real.sq_sqrt hM_pos.le
    have hscale_sq : (scale n) ^ 2 = M⁻¹ := by
      calc
        (scale n) ^ 2 = (Real.sqrt M)⁻¹ ^ 2 := by
            simp [scale, M]
        _ = ((Real.sqrt M) ^ 2)⁻¹ := by ring
        _ = M⁻¹ := by rw [hsqrt_sq]
    calc
      greenDirichletSeminormSq g (Z n)
          = (scale n) ^ 2 * greenDirichletSeminormSq g (H n) := by
              simpa [Z] using
                greenDirichletSeminormSq_const_smul
                  (g := g) (scale n) (H n)
      _ = M⁻¹ * greenDirichletSeminormSq g (H n) := by
              rw [hscale_sq]
      _ = D / M := by
              simp [D, div_eq_inv_mul, mul_comm]

/--
%%handwave
name:
  Finite-energy bad sequences can be normalized
statement:
  If a finite-energy zero-trace Sobolev sequence has positive local \(L^2\)
  mass and its Dirichlet energy divided by that mass tends to zero, then
  rescaling each term gives a unit-local-mass sequence whose Dirichlet energy
  tends to zero and whose gradient-energy densities remain integrable.
proof:
  Use the same reciprocal-square-root scaling as for ordinary normalization.
  Quadratic scaling gives the unit local mass and the new Dirichlet energies;
  integrability of the gradient-energy density is preserved by multiplication
  by the scalar square.
-/
theorem exists_unit_localL2_sequence_with_dirichlet_tendsto_zero_of_positive_localL2_ratio_tendsto_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (H : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hH_pos : ∀ n : ℕ, 0 < greenLocalL2SeminormSq g K (H n))
    (hH_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((H n).weakGradient x) ((H n).weakGradient x))
        g.volume)
    (hH_ratio :
      Filter.Tendsto
        (fun n : ℕ ↦
          greenDirichletSeminormSq g (H n) /
            greenLocalL2SeminormSq g K (H n))
        Filter.atTop (𝓝 0)) :
    ∃ Z : ℕ → SobolevH1ZeroOnSurface g.volume,
      (∀ n : ℕ, greenLocalL2SeminormSq g K (Z n) = 1) ∧
        (∀ n : ℕ,
          Integrable
            (fun x : X ↦
              g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
            g.volume) ∧
        Filter.Tendsto
          (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
          Filter.atTop (𝓝 0) := by
  let scale : ℕ → ℝ :=
    fun n : ℕ ↦ (Real.sqrt (greenLocalL2SeminormSq g K (H n)))⁻¹
  let Z : ℕ → SobolevH1ZeroOnSurface g.volume :=
    fun n : ℕ ↦ SobolevH1ZeroOnSurface.const_smul (scale n) (H n)
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro n
    let M : ℝ := greenLocalL2SeminormSq g K (H n)
    have hM_pos : 0 < M := by
      simpa [M] using hH_pos n
    have hsqrt_sq : (Real.sqrt M) ^ 2 = M :=
      Real.sq_sqrt hM_pos.le
    have hsqrt_ne : Real.sqrt M ≠ 0 :=
      (Real.sqrt_pos.2 hM_pos).ne'
    have hscale_sq_mul : (scale n) ^ 2 * M = 1 := by
      calc
        (scale n) ^ 2 * M =
            (Real.sqrt M)⁻¹ ^ 2 * M := by
              simp [scale, M]
        _ = (Real.sqrt M)⁻¹ ^ 2 * (Real.sqrt M) ^ 2 := by
              rw [hsqrt_sq]
        _ = 1 := by
              field_simp [hsqrt_ne]
    calc
      greenLocalL2SeminormSq g K (Z n)
          = (scale n) ^ 2 * greenLocalL2SeminormSq g K (H n) := by
              simpa [Z] using
                greenLocalL2SeminormSq_const_smul
                  (g := g) (K := K) (scale n) (H n)
      _ = 1 := by
              simpa [M] using hscale_sq_mul
  · intro n
    have hscaled :
        Integrable
          (fun x : X ↦
            (scale n) ^ (2 : ℕ) *
              g.gradientInner x ((H n).weakGradient x) ((H n).weakGradient x))
          g.volume :=
      (hH_int n).const_mul ((scale n) ^ (2 : ℕ))
    simpa [Z, SobolevH1ZeroOnSurface.const_smul, Pi.smul_apply,
      BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul] using hscaled
  · refine hH_ratio.congr' ?_
    filter_upwards [] with n
    symm
    let M : ℝ := greenLocalL2SeminormSq g K (H n)
    let D : ℝ := greenDirichletSeminormSq g (H n)
    have hM_pos : 0 < M := by
      simpa [M] using hH_pos n
    have hsqrt_sq : (Real.sqrt M) ^ 2 = M :=
      Real.sq_sqrt hM_pos.le
    have hscale_sq : (scale n) ^ 2 = M⁻¹ := by
      calc
        (scale n) ^ 2 = (Real.sqrt M)⁻¹ ^ 2 := by
            simp [scale, M]
        _ = ((Real.sqrt M) ^ 2)⁻¹ := by ring
        _ = M⁻¹ := by rw [hsqrt_sq]
    calc
      greenDirichletSeminormSq g (Z n)
          = (scale n) ^ 2 * greenDirichletSeminormSq g (H n) := by
              simpa [Z] using
                greenDirichletSeminormSq_const_smul
                  (g := g) (scale n) (H n)
      _ = M⁻¹ * greenDirichletSeminormSq g (H n) := by
              rw [hscale_sq]
      _ = D / M := by
              simp [D, div_eq_inv_mul, mul_comm]

/--
%%handwave
name:
  One term of a finite sum stays uniformly positive along a subsequence
statement:
  Let \(I\) be finite and nonempty. If
  \(1\le\sum_{i\in I}m_n(i)\) for every \(n\), then there exist
  \(i_0\in I\), \(\delta>0\), and a strictly increasing \(\phi\) such that
  \(m_{\phi(n)}(i_0)\ge\delta\) for all \(n\).
proof:
  For each \(n\), some summand is at least \(1/|I|\). One index occurs
  infinitely often; enumerate that infinite fiber by a strictly increasing
  subsequence.
-/
private theorem exists_finite_index_strictMono_subsequence_uniform_lower_of_one_le_sum
    {ι : Type} [Fintype ι] [Nonempty ι]
    (m : ℕ → ι → ℝ)
    (hsum : ∀ n : ℕ, 1 ≤ ∑ i : ι, m n i) :
    ∃ i : ι, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, δ ≤ m (φ n) i := by
  classical
  let δ : ℝ := ((Fintype.card ι : ℝ))⁻¹
  have hcard_pos_nat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcard_pos : 0 < (Fintype.card ι : ℝ) :=
    Nat.cast_pos.mpr hcard_pos_nat
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hchoose : ∀ n : ℕ, ∃ i : ι, δ ≤ m n i := by
    intro n
    by_contra hnone
    have hall_lt : ∀ i : ι, m n i < δ := by
      intro i
      exact not_le.mp (fun hle ↦ hnone ⟨i, hle⟩)
    have hsum_lt :
        (∑ i : ι, m n i) < ∑ _i : ι, δ := by
      exact Finset.sum_lt_sum_of_nonempty
        (s := (Finset.univ : Finset ι))
        Finset.univ_nonempty
        (fun i _hi ↦ hall_lt i)
    have hsum_const : (∑ _i : ι, δ) = 1 := by
      simp [δ, hcard_ne]
    have hlt_one : (∑ i : ι, m n i) < 1 := by
      simpa [hsum_const] using hsum_lt
    exact not_lt_of_ge (hsum n) hlt_one
  choose f hf using hchoose
  rcases Finite.exists_infinite_fiber f with ⟨i₀, hi₀⟩
  have hsubseq : ∀ N : ℕ, ∃ n > N, f n = i₀ := by
    intro N
    rcases Set.Infinite.exists_gt (Set.infinite_coe_iff.mp hi₀) N with
      ⟨n, hn_mem, hNn⟩
    exact ⟨n, hNn, by simpa using hn_mem⟩
  rcases Nat.exists_strictMono_subsequence hsubseq with
    ⟨φ, hφ, hφ_mem⟩
  refine ⟨i₀, δ, hδ_pos, φ, hφ, ?_⟩
  intro n
  have hfn : δ ≤ m (φ n) (f (φ n)) := hf (φ n)
  simpa [hφ_mem n] using hfn

/--
%%handwave
name:
  One piece retains \(L^2\) mass along a subsequence
statement:
  For a finite nonempty family of sets \(K_i\), if
  \[1\le\sum_i\lVert u_n\rVert_{L^2(K_i),\mathbb R}\]
  for every \(n\), then some \(K_{i_0}\), \(\delta>0\), and strictly increasing
  \(\phi\) satisfy
  \(\operatorname{ofReal}(\delta)\le
    \lVert u_{\phi(n)}\rVert_{L^2(K_{i_0})}\) for all \(n\).
proof:
  Apply [the finite-sum subsequence pigeonhole principle](lean:exists_finite_index_strictMono_subsequence_uniform_lower_of_one_le_sum) to the real \(L^2\)-norms and lift the resulting inequality to extended nonnegative reals.
-/
private theorem exists_finite_index_strictMono_subsequence_uniform_eLpNorm_lower_of_one_le_sum_toReal
    {X E ι : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    [Fintype ι] [Nonempty ι]
    {μ : Measure X} (Kc : ι → Set X) (u : ℕ → X → E)
    (hsum : ∀ n : ℕ,
      1 ≤ ∑ i : ι,
        (eLpNorm (u n) 2 (μ.restrict (Kc i))).toReal) :
    ∃ i : ι, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ,
        ENNReal.ofReal δ ≤ eLpNorm (u (φ n)) 2 (μ.restrict (Kc i)) := by
  rcases
    exists_finite_index_strictMono_subsequence_uniform_lower_of_one_le_sum
      (m := fun n i ↦
        (eLpNorm (u n) 2 (μ.restrict (Kc i))).toReal)
      hsum with
    ⟨i, δ, hδ, φ, hφ, hlower⟩
  refine ⟨i, δ, hδ, φ, hφ, ?_⟩
  intro n
  exact ENNReal.ofReal_le_of_le_toReal (hlower n)

/--
%%handwave
name:
  Unit square integral gives unit \(L^2\)-norm
statement:
  If \(u\in L^2(K,\mu)\) and
  \(\int_Ku(x)^2\,d\mu=1\), then
  \(\lVert u\rVert_{L^2(K,\mu),\mathbb R}=1\).
proof:
  Identify the extended square integral with the embedding of the ordinary
  integral, use the hypothesis, and take the positive square root.
-/
private theorem eLpNorm_two_toReal_eq_one_of_integral_sq_eq_one
    {X : Type} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    {u : X → ℝ}
    (hu : MemLp u 2 (μ.restrict K))
    (hunit : ∫ x in K, u x ^ (2 : ℕ) ∂μ = 1) :
    (eLpNorm u 2 (μ.restrict K)).toReal = 1 := by
  let μK : Measure X := μ.restrict K
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hptop : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := ENNReal.coe_ne_top
  have h_int : Integrable (fun x : X ↦ ‖u x‖ ^ (2 : ℕ)) μK :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have h_int_sq : Integrable (fun x : X ↦ u x ^ (2 : ℕ)) μK := by
    refine h_int.congr ?_
    filter_upwards with x
    simp [Real.norm_eq_abs, sq_abs]
  have h_nonneg : 0 ≤ᵐ[μK] fun x : X ↦ u x ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  have h_int_eq : ∫ x, u x ^ (2 : ℕ) ∂μK = 1 := by
    simpa [μK] using hunit
  have h_lint_eq :
      ENNReal.ofReal (∫ x, u x ^ (2 : ℕ) ∂μK) =
        ∫⁻ x, ENNReal.ofReal (u x ^ (2 : ℕ)) ∂μK :=
    ofReal_integral_eq_lintegral_ofReal h_int_sq h_nonneg
  have h_lint :
      (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μK) = 1 := by
    calc
      (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μK)
          = ∫⁻ x, ENNReal.ofReal (u x ^ (2 : ℕ)) ∂μK := by
              apply lintegral_congr_ae
              filter_upwards with x
              exact real_enorm_rpow_two_eq_ofReal_sq (u x)
      _ = ENNReal.ofReal (∫ x, u x ^ (2 : ℕ) ∂μK) := h_lint_eq.symm
      _ = 1 := by simp [h_int_eq]
  have hnorm :
      eLpNorm u 2 μK = 1 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
    change (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μK) ^ (1 / (2 : ℝ)) = 1
    rw [h_lint]
    norm_num
  simp [μK, hnorm]

/--
%%handwave
name:
  Square of the real \(L^2\)-norm
statement:
  If \(u\in L^2(K,\mu)\), then
  \[\lVert u\rVert_{L^2(K,\mu),\mathbb R}^{\,2}
    =\int_Ku(x)^2\,d\mu.\]
proof:
  Express the real \(L^2\)-norm as the square root of the integral of
  \(|u|^2\), replace \(|u|^2\) by \(u^2\), and square.
-/
private theorem eLpNorm_two_toReal_sq_eq_integral_sq
    {X : Type} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    {u : X → ℝ}
    (hu : MemLp u 2 (μ.restrict K)) :
    (eLpNorm u 2 (μ.restrict K)).toReal ^ (2 : ℕ) =
      ∫ x in K, u x ^ (2 : ℕ) ∂μ := by
  let μK : Measure X := μ.restrict K
  have h_int_norm : Integrable (fun x : X ↦ ‖u x‖ ^ (2 : ℕ)) μK :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have h_int_sq : Integrable (fun x : X ↦ u x ^ (2 : ℕ)) μK := by
    refine h_int_norm.congr ?_
    filter_upwards with x
    simp [Real.norm_eq_abs, sq_abs]
  have h_nonneg : 0 ≤ ∫ x, u x ^ (2 : ℕ) ∂μK :=
    integral_nonneg fun x ↦ sq_nonneg (u x)
  have h_norm_sq_eq :
      ∫ x, ‖u x‖ ^ (2 : ℕ) ∂μK =
        ∫ x, u x ^ (2 : ℕ) ∂μK :=
    integral_congr_ae (by
      filter_upwards with x
      simp [Real.norm_eq_abs, sq_abs])
  have hnorm :
      (eLpNorm u 2 μK).toReal =
        Real.sqrt (∫ x, u x ^ (2 : ℕ) ∂μK) := by
    have hlp :=
      lpNorm_eq_integral_norm_rpow_toReal
        (μ := μK) (f := u) (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hu.aestronglyMeasurable
    have htoReal := toReal_eLpNorm
      (μ := μK) (f := u) (p := (2 : ℝ≥0∞)) hu.aestronglyMeasurable
    calc
      (eLpNorm u 2 μK).toReal = lpNorm u 2 μK := htoReal
      _ = (∫ x, ‖u x‖ ^ (2 : ℝ≥0∞).toReal ∂μK) ^
            ((2 : ℝ≥0∞).toReal)⁻¹ := hlp
      _ = (∫ x, ‖u x‖ ^ (2 : ℕ) ∂μK) ^ (1 / (2 : ℝ)) := by
            norm_num
      _ = (∫ x, u x ^ (2 : ℕ) ∂μK) ^ (1 / (2 : ℝ)) := by
            rw [h_norm_sq_eq]
      _ = Real.sqrt (∫ x, u x ^ (2 : ℕ) ∂μK) := by
            rw [Real.sqrt_eq_rpow]
  calc
    (eLpNorm u 2 (μ.restrict K)).toReal ^ (2 : ℕ)
        = (Real.sqrt (∫ x, u x ^ (2 : ℕ) ∂μK)) ^ (2 : ℕ) := by
            rw [hnorm]
    _ = ∫ x, u x ^ (2 : ℕ) ∂μK := by
            rw [Real.sq_sqrt h_nonneg]
    _ = ∫ x in K, u x ^ (2 : ℕ) ∂μ := rfl

/--
%%handwave
name:
  Unit local mass is detected by a finite cover
statement:
  Let \(K=\bigcup_{i\in I}K_i\) with \(I\) finite. If a zero-trace Sobolev
  function satisfies \(\int_Ku^2=1\), then
  \[1\le\sum_{i\in I}\lVert u\rVert_{L^2(K_i),\mathbb R}.\]
proof:
  The global \(L^2(K)\)-norm is one. Its norm over a finite union is at most
  the sum of the restricted norms; pass to real values using finiteness.
-/
private theorem one_le_sum_toReal_eLpNorm_on_finite_cover_of_greenLocalL2SeminormSq_eq_one
    {X ι : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [Fintype ι]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (Kc : ι → Set X) (hcover : K = ⋃ i : ι, Kc i)
    (u : SobolevH1ZeroOnSurface g.volume)
    (hunit : greenLocalL2SeminormSq g K u = 1) :
    1 ≤ ∑ i : ι,
      (eLpNorm (fun x : X ↦ u x) 2
        (g.volume.restrict (Kc i))).toReal := by
  let μ : Measure X := g.volume
  let f : X → ℝ := fun x ↦ u x
  have hglobal_mem : MemLp f 2 (μ.restrict K) :=
    u.memLp_toFun.mono_measure Measure.restrict_le_self
  have hlocal_ne_top :
      ∀ i : ι, eLpNorm f 2 (μ.restrict (Kc i)) ≠ (∞ : ℝ≥0∞) := by
    intro i
    exact
      (u.memLp_toFun.mono_measure Measure.restrict_le_self).eLpNorm_lt_top.ne
  have hsum_ne_top :
      (∑ i : ι, eLpNorm f 2 (μ.restrict (Kc i))) ≠ (∞ : ℝ≥0∞) := by
    simpa using
      (ENNReal.sum_ne_top.2 (by
        intro i _hi
        exact hlocal_ne_top i :
        ∀ i ∈ (Finset.univ : Finset ι),
          eLpNorm f 2 (μ.restrict (Kc i)) ≠ (∞ : ℝ≥0∞)))
  have hglobal_norm :
      (eLpNorm f 2 (μ.restrict K)).toReal = 1 := by
    exact
      eLpNorm_two_toReal_eq_one_of_integral_sq_eq_one
        (μ := μ) (K := K) (u := f) hglobal_mem
        (by simpa [μ, f, greenLocalL2SeminormSq] using hunit)
  have hsum_toReal :
      (∑ i : ι, eLpNorm f 2 (μ.restrict (Kc i))).toReal =
        ∑ i : ι, (eLpNorm f 2 (μ.restrict (Kc i))).toReal := by
    simpa using
      (ENNReal.toReal_sum
        (s := (Finset.univ : Finset ι))
        (f := fun i : ι ↦ eLpNorm f 2 (μ.restrict (Kc i)))
        (by
          intro i _hi
          exact hlocal_ne_top i))
  calc
    1 = (eLpNorm f 2 (μ.restrict K)).toReal := hglobal_norm.symm
    _ ≤ (∑ i : ι, eLpNorm f 2 (μ.restrict (Kc i))).toReal :=
        ENNReal.toReal_mono hsum_ne_top
          (eLpNorm_two_restrict_finite_iUnion_le_sum Kc hcover f)
    _ = ∑ i : ι, (eLpNorm f 2 (μ.restrict (Kc i))).toReal := hsum_toReal

/--
%%handwave
name:
  Compact mass retention from a finite Rellich cover
statement:
  Suppose compact sets \(K_i\) finitely cover \(\overline Q\), each subsequence
  admits a further subsequence converging in \(L^2(K_i)\) to a constant, and
  \(\int_{\overline Q}Z_n^2=1\). Then for some positive-measure \(K_i\), a
  subsequence retains a uniform positive \(L^2(K_i)\)-norm and converges there
  in \(L^2\) to a constant.
proof:
  The finite-cover norm inequality and the finite pigeonhole subsequence
  lemma select one piece with uniform mass. Apply the assumed compactness on
  that piece; the positive lower bound forces the piece to have positive
  measure.
-/
private theorem exists_compact_constant_L2_tendsto_subsequence_with_uniform_mass_of_finite_cover
    {X ι : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [Fintype ι]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (Kc : ι → Set X)
    (hKc_compact : ∀ i : ι, IsCompact (Kc i))
    (hcover : closure Q = ⋃ i : ι, Kc i)
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hpiece_constant :
      ∀ i : ι, ∀ η : ℕ → ℕ, StrictMono η →
        ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Filter.Tendsto
            (fun n : ℕ ↦
              eLpNorm (fun x : X ↦ Z (η (ψ n)) x - a) 2
                (g.volume.restrict (Kc i)))
            Filter.atTop (𝓝 0)) :
    ∃ K : Set X, IsCompact K ∧ 0 < g.volume K ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ a : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ n : ℕ,
          ENNReal.ofReal δ ≤
            eLpNorm (fun x : X ↦ Z (φ n) x) 2 (g.volume.restrict K)) ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ Z (φ n) x - a) 2 (g.volume.restrict K))
          Filter.atTop (𝓝 0) := by
  have hsum :
      ∀ n : ℕ,
        1 ≤ ∑ i : ι,
          (eLpNorm (fun x : X ↦ Z n x) 2
            (g.volume.restrict (Kc i))).toReal := by
    intro n
    exact
      one_le_sum_toReal_eLpNorm_on_finite_cover_of_greenLocalL2SeminormSq_eq_one
        (g := g) Kc hcover (Z n) (hZ_unit n)
  haveI : Nonempty ι := by
    classical
    by_contra hι
    haveI : IsEmpty ι := ⟨fun i ↦ hι ⟨i⟩⟩
    have hbad := hsum 0
    simp at hbad
    norm_num at hbad
  rcases
    exists_finite_index_strictMono_subsequence_uniform_eLpNorm_lower_of_one_le_sum_toReal
      (μ := g.volume) Kc (fun n : ℕ ↦ fun x : X ↦ Z n x) hsum with
    ⟨i, δ, hδ, φ, hφ, hlower⟩
  have hKc_i_pos : 0 < g.volume (Kc i) := by
    by_contra hnot_pos
    have hzero : g.volume (Kc i) = 0 :=
      le_antisymm (not_lt.mp hnot_pos) zero_le
    have hrestrict_zero : g.volume.restrict (Kc i) = 0 :=
      Measure.restrict_eq_zero.mpr hzero
    have hnorm_zero :
        eLpNorm (fun x : X ↦ Z (φ 0) x) 2
          (g.volume.restrict (Kc i)) = 0 := by
      rw [hrestrict_zero, eLpNorm_measure_zero]
    have hδENN_pos : 0 < ENNReal.ofReal δ :=
      ENNReal.ofReal_pos.mpr hδ
    exact not_lt_of_ge (by simpa [hnorm_zero] using hlower 0) hδENN_pos
  rcases hpiece_constant i φ hφ with ⟨a, ψ, hψ, hlim⟩
  refine ⟨Kc i, hKc_compact i, hKc_i_pos, δ, hδ, a, φ ∘ ψ, hφ.comp hψ, ?_, ?_⟩
  · intro n
    simpa [Function.comp_def] using hlower (ψ n)
  · simpa [Function.comp_def] using hlim

/--
%%handwave
name:
  Compact closure has a finite compact chart cover
statement:
  The compact closure of an open subset of a charted Hausdorff space is a
  finite union of compact sets, each lying in a coordinate chart source.
proof:
  Apply the finite compact chart-cover lemma to the compact set
  \(\overline Q\) with the ambient set equal to the whole space.
-/
private theorem exists_finite_compact_chart_cover_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [R1Space X]
    {Q : Set X} (hQ_compact : IsCompact (closure Q)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → X) (Kc : ι → Set X),
      (∀ i : ι, IsCompact (Kc i)) ∧
        (∀ i : ι, Kc i ⊆ (chartAt ℂ (c i)).source) ∧
        closure Q = ⋃ i : ι, Kc i := by
  have hsubset : closure Q ⊆ interior (Set.univ : Set X) := by
    intro x _hx
    simp
  rcases
    compact_exists_finite_compact_chart_cover_inside
      (H := ℂ) (X := X) (K := closure Q) (Q := Set.univ)
      hQ_compact hsubset with
    ⟨ι, hι, c, Kc, hKc_compact, hKc_sub, hcover⟩
  refine ⟨ι, hι, c, Kc, hKc_compact, ?_, hcover⟩
  intro i x hx
  exact (hKc_sub i hx).1

/--
%%handwave
name:
  Compact subsets of surface open sets have compact control neighborhoods
statement:
  If a compact set \(K\) in a Riemann surface is contained in an open set
  \(U\), then there is a compact set \(P\) with
  \(K\subset \operatorname{int} P\) and \(P\subset U\).
proof:
  Use local compactness and regularity to choose an open neighborhood \(V\) of
  \(K\) whose closure is compact and contained in \(U\).  Then
  \(P=\overline V\) works because \(V\subset\operatorname{int}\overline V\).
-/
private theorem compact_subset_open_exists_compact_between_interior_on_surface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    {K U : Set X} (hK : IsCompact K) (hU_open : IsOpen U) (hKU : K ⊆ U) :
    ∃ P : Set X, IsCompact P ∧ K ⊆ interior P ∧ P ⊆ U := by
  rcases exists_open_between_and_isCompact_closure hK hU_open hKU with
    ⟨V, hV_open, hKV, hclosureV_U, hclosureV_compact⟩
  refine ⟨closure V, hclosureV_compact, ?_, hclosureV_U⟩
  exact hKV.trans hV_open.subset_interior_closure

/--
%%handwave
name:
  Failure of local Poincare gives one raw counterexample
statement:
  If no constant controls the \(L^2\)-distance to constants by the local
  gradient energy, then for every prescribed nonnegative scale there is a
  locally Sobolev function whose distance to every constant is strictly larger
  than that scale times its local gradient energy.
proof:
  This is the logical negation of the desired estimate at the chosen scale.
  If no such counterexample existed, every locally Sobolev function would
  admit a constant satisfying the estimate at that scale, contradicting
  failure of the Poincare inequality.
-/
private theorem local_poincare_failure_gives_raw_counterexample
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {K U : Set X} {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hfail :
      ¬ ∃ C : ℝ, 0 ≤ C ∧
        ∀ (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ),
          IsLocalSobolevH1OnSurface g.volume U u du →
            ∃ a : ℝ,
              surfaceLocalL2SeminormSq g.volume K (fun x ↦ u x - a) ≤
                C * surfaceLocalGradientSeminormSq g U du) :
    ∃ (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ),
      IsLocalSobolevH1OnSurface g.volume U u du ∧
        ∀ a : ℝ,
          C * surfaceLocalGradientSeminormSq g U du <
            surfaceLocalL2SeminormSq g.volume K (fun x ↦ u x - a) := by
  classical
  by_contra hraw
  apply hfail
  refine ⟨C, hC_nonneg, ?_⟩
  intro u du hlocal
  by_contra hno_center
  apply hraw
  refine ⟨u, du, hlocal, ?_⟩
  intro a
  exact not_le.mp (not_exists.mp hno_center a)

/--
%%handwave
name:
  Failure of local Poincare gives a raw counterexample sequence
statement:
  If the local Poincare inequality modulo constants fails, then there is a
  sequence of locally Sobolev functions such that the distance from every
  constant dominates \((n+1)\) times the local gradient energy.
proof:
  Apply the one-step counterexample construction with scale \(n+1\) and use
  countable choice.
-/
private theorem local_poincare_failure_gives_raw_counterexample_sequence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {K U : Set X}
    (hfail :
      ¬ ∃ C : ℝ, 0 ≤ C ∧
        ∀ (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ),
          IsLocalSobolevH1OnSurface g.volume U u du →
            ∃ a : ℝ,
              surfaceLocalL2SeminormSq g.volume K (fun x ↦ u x - a) ≤
                C * surfaceLocalGradientSeminormSq g U du) :
    ∃ (u : ℕ → X → ℝ) (du : ℕ → X → ℂ →L[ℝ] ℝ),
      (∀ n : ℕ, IsLocalSobolevH1OnSurface g.volume U (u n) (du n)) ∧
        ∀ n : ℕ, ∀ a : ℝ,
          ((n : ℝ) + 1) * surfaceLocalGradientSeminormSq g U (du n) <
            surfaceLocalL2SeminormSq g.volume K (fun x ↦ u n x - a) := by
  classical
  have hterm :
      ∀ n : ℕ,
        ∃ (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ),
          IsLocalSobolevH1OnSurface g.volume U u du ∧
            ∀ a : ℝ,
              ((n : ℝ) + 1) * surfaceLocalGradientSeminormSq g U du <
                surfaceLocalL2SeminormSq g.volume K (fun x ↦ u x - a) := by
    intro n
    exact
      local_poincare_failure_gives_raw_counterexample
        (g := g) (K := K) (U := U)
        (C := (n : ℝ) + 1) (by positivity) hfail
  choose u hu using hterm
  choose du hdu using hu
  refine ⟨u, du, ?_, ?_⟩
  · intro n
    exact (hdu n).1
  · intro n a
    exact (hdu n).2 a

/--
%%handwave
name:
  A normalized sequence cannot have constant Rellich subsequences
statement:
  Suppose a sequence has \(L^2\)-distance at least one from every constant on
  a fixed measurable set, while every subsequence has a further subsequence
  converging in \(L^2\) to some constant on that same set.  Then this is
  impossible.
proof:
  Apply the constant-subsequence hypothesis to the identity subsequence.  The
  lower bound by one passes to the extracted subsequence, while the extracted
  \(L^2\)-distance tends to zero.  Taking limits gives \(1\le0\), a
  contradiction.
-/
private theorem normalized_constant_subsequence_absurd
    {X : Type} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    (w : ℕ → X → ℝ)
    (hdist : ∀ n : ℕ, ∀ a : ℝ,
      (1 : ℝ≥0∞) ≤ eLpNorm (fun x : X ↦ w n x - a) 2 (μ.restrict K))
    (hsubseq :
      ∀ η : ℕ → ℕ, StrictMono η →
        ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Filter.Tendsto
            (fun n : ℕ ↦
              eLpNorm (fun x : X ↦ w (η (ψ n)) x - a) 2
                (μ.restrict K))
            Filter.atTop (𝓝 0)) :
    False := by
  have hid : StrictMono (fun n : ℕ ↦ n) := by
    intro m n hmn
    exact hmn
  rcases hsubseq (fun n : ℕ ↦ n) hid with ⟨a, ψ, _hψ, hlim⟩
  have hconst :
      Filter.Tendsto (fun _n : ℕ ↦ (1 : ℝ≥0∞))
        Filter.atTop (𝓝 (1 : ℝ≥0∞)) :=
    tendsto_const_nhds
  have hle_eventually :
      (fun _n : ℕ ↦ (1 : ℝ≥0∞)) ≤ᶠ[Filter.atTop]
        (fun n : ℕ ↦
          eLpNorm (fun x : X ↦ w (ψ n) x - a) 2 (μ.restrict K)) :=
    Filter.Eventually.of_forall fun n ↦ hdist (ψ n) a
  have hone_le_zero : (1 : ℝ≥0∞) ≤ 0 :=
    le_of_tendsto_of_tendsto hconst hlim hle_eventually
  exact (not_lt_of_ge hone_le_zero) zero_lt_one

/--
%%handwave
name:
  Second countability of the trivial real line bundle
statement:
  If \(X\) is second countable, then the total space of the trivial real line
  bundle over \(X\) is second countable.
proof:
  The total space is homeomorphic to \(X\times\mathbb R\), a product of
  second-countable spaces.
-/
private theorem surface_value_totalSpace_secondCountable
    {X : Type} [TopologicalSpace X] [SecondCountableTopology X] :
    SecondCountableTopology (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ)) := by
  exact (Bundle.Trivial.homeomorphProd X ℝ).secondCountableTopology

/--
%%handwave
name:
  Pseudometrizability of the trivial real line bundle
statement:
  Over a second-countable Hausdorff surface, the total space of the trivial
  real line bundle is pseudometrizable.
proof:
  The base is locally compact and regular, hence its product with
  \(\mathbb R\) is regular. Transfer regularity through the bundle-product
  homeomorphism and use second countability to obtain pseudometrizability.
-/
private theorem surface_value_totalSpace_pseudoMetrizable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [T2Space X] [IsManifold SurfaceRealModel 1 X] :
    TopologicalSpace.PseudoMetrizableSpace
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ)) := by
  haveI : SecondCountableTopology
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ)) :=
    surface_value_totalSpace_secondCountable (X := X)
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : RegularSpace X := inferInstance
  haveI : T3Space X := inferInstance
  haveI : T3Space (X × ℝ) := inferInstance
  haveI : T3Space (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ)) :=
    (Bundle.Trivial.homeomorphProd X ℝ).symm.t3Space
  exact TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology _

/--
%%handwave
name:
  Surface cotangent total-space charts cover whole fibers over base charts
statement:
  If a point \(y\) lies in a surface coordinate chart centered at \(x\), then
  every scalar cotangent vector over \(y\) lies in the cotangent-bundle chart
  centered at the zero covector over \(x\).
proof:
  The total-space chart is the differential-bundle local trivialization
  followed by the base coordinate chart.  Its source consists precisely of
  the covectors whose base point lies in the corresponding base chart source.
-/
private theorem surface_differential_totalSpace_mem_chart_source_of_base_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel 1 X]
    (x y : X)
    (A : ManifoldDifferentialBundleFiber (I := SurfaceRealModel) (X := X) (E := ℝ) y)
    (hyx : y ∈ (chartAt ℂ x).source) :
    let q : ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ :=
      Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
        (0 : ManifoldDifferentialBundleFiber (I := SurfaceRealModel) (X := X) (E := ℝ) x)
    (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) y A :
      ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) ∈
      (chartAt (ModelProd ℂ (ℂ →L[ℝ] ℝ)) q).source := by
  intro q
  rw [FiberBundle.chartedSpace_chartAt]
  simp only [mfld_simps]
  constructor
  · simpa [q] using hyx
  · let p : ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ :=
        Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) y A
    have hybase : y ∈
        (trivializationAt (ℂ →L[ℝ] ℝ)
          (fun x : X ↦
            TangentSpace SurfaceRealModel x →L[ℝ] Bundle.Trivial X ℝ x) x).baseSet := by
      simpa [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet] using hyx
    have hfst := Bundle.Trivialization.coe_fst'
      (trivializationAt (ℂ →L[ℝ] ℝ)
        (fun x : X ↦
          TangentSpace SurfaceRealModel x →L[ℝ] Bundle.Trivial X ℝ x) x)
      (x := p) hybase
    simpa [q, p, hfst] using hyx

/--
%%handwave
name:
  The surface differential bundle total space is second countable
statement:
  The total space of the scalar cotangent bundle over a second-countable
  smooth real surface is second countable.
proof:
  Trivialize the finite-rank vector bundle over a countable coordinate cover.
  Each trivialization identifies the corresponding piece of the total space
  with an open subset of a product of second-countable spaces, and a
  countable union of such pieces covers the total space.
-/
private theorem surface_differential_totalSpace_secondCountable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel 1 X] :
    SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) := by
  let F := ℂ →L[ℝ] ℝ
  let Y := ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ
  haveI : SecondCountableTopology (ModelProd ℂ F) := by
    change SecondCountableTopology (ℂ × F)
    infer_instance
  let z : X → Y := fun x ↦
    Bundle.TotalSpace.mk' F x
      (0 : ManifoldDifferentialBundleFiber (I := SurfaceRealModel) (X := X) (E := ℝ) x)
  rcases countable_cover_nhds (fun x : X ↦ chart_source_mem_nhds ℂ x) with
    ⟨S, hS_count, hS_cover⟩
  let T : Set Y := z '' S
  have hT_count : T.Countable := hS_count.image z
  have hcover : ⋃ q ∈ T, (chartAt (ModelProd ℂ F) q).source = Set.univ := by
    ext p
    constructor
    · intro _
      trivial
    · intro _
      have hpbase : p.1 ∈ (⋃ x ∈ S, (chartAt ℂ x).source) := by
        rw [hS_cover]
        trivial
      rcases Set.mem_iUnion.mp hpbase with ⟨x, hxmem⟩
      rcases Set.mem_iUnion.mp hxmem with ⟨hxS, hpx⟩
      refine Set.mem_iUnion.mpr ⟨z x, ?_⟩
      refine Set.mem_iUnion.mpr ⟨⟨x, hxS, rfl⟩, ?_⟩
      change p ∈ (chartAt (ModelProd ℂ F) (z x)).source
      cases p with
      | mk y A =>
          exact surface_differential_totalSpace_mem_chart_source_of_base_mem
            (X := X) x y A hpx
  exact ChartedSpace.secondCountable_of_countable_cover (ModelProd ℂ F) hcover hT_count

/--
%%handwave
name:
  The surface differential bundle total space is Hausdorff
statement:
  If the base surface is Hausdorff, then the total space of its scalar
  cotangent bundle is Hausdorff.
proof:
  Separate two covectors by first comparing their base points.  If the base
  points differ, pull back disjoint base neighbourhoods along the bundle
  projection.  If the base points agree, use one local trivialization over
  that base point and separate the two images in the Hausdorff product chart.
-/
private theorem surface_differential_totalSpace_t2Space
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [IsManifold SurfaceRealModel 1 X] :
    T2Space (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) := by
  let F := ℂ →L[ℝ] ℝ
  let E : X → Type := fun x : X ↦
    TangentSpace SurfaceRealModel x →L[ℝ] Bundle.Trivial X ℝ x
  change T2Space (Bundle.TotalSpace F E)
  rw [t2Space_iff_disjoint_nhds]
  intro p q hpq
  by_cases hbase : p.1 = q.1
  · let e : Bundle.Trivialization F
        (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → X) :=
      trivializationAt F E p.1
    have hp_source : p ∈ e.source := by
      exact e.mem_source.mpr (FiberBundle.mem_baseSet_trivializationAt F E p.1)
    have hq_source : q ∈ e.source := by
      have hqbase : q.1 ∈ e.baseSet := by
        simpa [e, hbase] using FiberBundle.mem_baseSet_trivializationAt F E p.1
      exact e.mem_source.mpr hqbase
    have hneq : e p ≠ e q := by
      intro heq
      apply hpq
      calc
        p = e.toOpenPartialHomeomorph.symm (e p) := by
          simpa [Bundle.Trivialization.coe_coe] using
            (e.toOpenPartialHomeomorph.left_inv hp_source).symm
        _ = e.toOpenPartialHomeomorph.symm (e q) := by rw [heq]
        _ = q := by
          simpa [Bundle.Trivialization.coe_coe] using
            e.toOpenPartialHomeomorph.left_inv hq_source
    have hprod : Disjoint (𝓝 (e p)) (𝓝 (e q)) := disjoint_nhds_nhds.2 hneq
    have hmap_p :
        Filter.map (e : Bundle.TotalSpace F E → X × F) (𝓝 p) = 𝓝 (e p) := by
      simpa [Bundle.Trivialization.coe_coe] using
        e.toOpenPartialHomeomorph.map_nhds_eq hp_source
    have hmap_q :
        Filter.map (e : Bundle.TotalSpace F E → X × F) (𝓝 q) = 𝓝 (e q) := by
      simpa [Bundle.Trivialization.coe_coe] using
        e.toOpenPartialHomeomorph.map_nhds_eq hq_source
    have hmap : Disjoint (Filter.map e (𝓝 p)) (Filter.map e (𝓝 q)) := by
      rw [hmap_p, hmap_q]
      exact hprod
    exact Filter.disjoint_of_map hmap
  · have hbase_disj : Disjoint (𝓝 p.1) (𝓝 q.1) := disjoint_nhds_nhds.2 hbase
    have hmap : Disjoint
        (Filter.map (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → X) (𝓝 p))
        (Filter.map (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → X) (𝓝 q)) := by
      simpa [FiberBundle.map_proj_nhds] using hbase_disj
    exact Filter.disjoint_of_map hmap

/--
%%handwave
name:
  The surface differential bundle total space is pseudo-metrizable
statement:
  The total space of the scalar cotangent bundle over a second-countable
  Hausdorff smooth real surface is pseudo-metrizable.
proof:
  The preceding chart-cover argument gives second countability of the total
  space.  Local trivializations identify it locally with a finite-dimensional
  product, so it is locally compact.  The Hausdorff property follows by
  separating either the base points or, over a common base point, the fiber
  coordinates in one trivialization.  Urysohn's metrization theorem then gives
  a compatible pseudometric.
-/
private theorem surface_differential_totalSpace_pseudoMetrizable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [T2Space X] [IsManifold SurfaceRealModel 1 X] :
    TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) := by
  let F := ℂ →L[ℝ] ℝ
  haveI : SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) :=
    surface_differential_totalSpace_secondCountable (X := X)
  haveI : T2Space
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) :=
    surface_differential_totalSpace_t2Space (X := X)
  haveI : LocallyCompactSpace (ModelProd ℂ F) := by
    change LocallyCompactSpace (ℂ × F)
    infer_instance
  haveI : LocallyCompactSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) :=
    ChartedSpace.locallyCompactSpace (ModelProd ℂ F)
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)
  haveI : RegularSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) := inferInstance
  exact TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology _

/--
%%handwave
name:
  Coordinate weak gradients are intrinsic weak differentials
statement:
  On a real surface, a scalar weak gradient written in complex coordinate
  tangent variables gives the same integration-by-parts identities as the
  intrinsic scalar weak differential in the two-dimensional real model.
proof:
  A manifold coordinate test in the real surface model is the same smooth
  compactly supported coordinate test used in the surface definition.  After
  this identification, the two integrability statements and the weak
  integration-by-parts identity differ only by the order of scalar
  multiplication.
-/
private theorem surface_coordinate_weakGradient_to_manifoldWeakDerivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {U : Set X} {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (hlocal : IsLocalSobolevH1OnSurface g.volume U u du) :
    IsWeakDerivativeOnManifoldRegionBundle
      (I := SurfaceRealModel) U u (SurfaceCotangentField.ofCoordinateField du) := by
  rcases hlocal with ⟨hweak, _hmem⟩
  intro e he φ v
  let ψ : SmoothCompactlySupportedCoordinateFunction (surfaceChartRegion e U) :=
    { toFun := φ.toFun
      smooth := φ.smooth
      support_subset := by
        simpa [surfaceChartRegion, manifoldChartRegion] using φ.support_subset
      compact_support := φ.compact_support }
  rcases hweak e he ψ v with ⟨hleft, hright, heq⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [ψ, manifoldChartRegion, surfaceChartRegion, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using hleft
  · simpa [ψ, ManifoldDifferentialField.evalChart, SurfaceCotangentField.ofCoordinateField,
      manifoldChartRegion, surfaceChartRegion, smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using hright
  · simpa [ψ, ManifoldDifferentialField.evalChart, SurfaceCotangentField.ofCoordinateField,
      manifoldChartRegion, surfaceChartRegion, smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using heq

/--
%%handwave
name:
  Inverse-Gram contraction recovers vector evaluation
statement:
  Let \(G\) be positive definite, \(p=G\alpha\), and let \(q\) be another
  coordinate vector. Then
  \[\sum_{i,j}(G^{-1})_{ij}p_iq_j=\sum_i\alpha_iq_i.\]
proof:
  Positive definiteness makes \(G\) invertible, so \(G^{-1}p=\alpha\).
  Reorder the double sum, use symmetry of \(G^{-1}\), and substitute.
-/
private theorem inverseGram_contraction_eq_eval
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (α p q : ι → ℝ) (hp : p = Matrix.mulVec G α) :
    (∑ i : ι, ∑ j : ι, G⁻¹ i j * p i * q j) =
      ∑ i : ι, α i * q i := by
  classical
  have hG_unit : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hG.det_pos)
  have hCp : Matrix.mulVec G⁻¹ p = α := by
    rw [hp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG_unit,
      Matrix.one_mulVec]
  have hC_symm : G⁻¹.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have h := (hG.inv).isHermitian.apply i j
    simpa using h
  calc
    (∑ i : ι, ∑ j : ι, G⁻¹ i j * p i * q j)
        = ∑ j : ι, ∑ i : ι, q j * (G⁻¹ j i * p i) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j _
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [(hC_symm.apply i j).symm]
            ring
    _ = ∑ j : ι, q j * (Matrix.mulVec G⁻¹ p j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ = ∑ j : ι, q j * α j := by
            rw [hCp]
    _ = ∑ i : ι, α i * q i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring

/--
%%handwave
name:
  Real inner product is multiplication
statement:
  For \(a,b\in\mathbb R\), \(\langle a,b\rangle_{\mathbb R}=ab\).
proof:
  Expand the standard real inner product and use that real conjugation is the
  identity.
-/
private theorem real_inner_eq_mul_poincare (a b : ℝ) :
    inner ℝ a b = a * b := by
  calc
    inner ℝ a b = b * (starRingEnd ℝ) a := RCLike.inner_apply a b
    _ = a * b := by simp [mul_comm]

/--
%%handwave
name:
  Hilbert--Schmidt cotangent pairing equals the metric-dual pairing
statement:
  Let \(g\) be a Riemannian metric on a surface and let
  \(\langle\, ,\,\rangle_{g^*}\) be its metric-dual cotangent pairing. At every
  \(x\) and for cotangent vectors \(\xi,\eta\), the intrinsic
  Hilbert--Schmidt pairing of differentials equals
  \(\langle\xi,\eta\rangle_{g^*}\).
proof:
  Represent \(\xi\) by its metric-dual vector, expand in a finite basis, and
  write both pairings with the Gram matrix. [Inverse-Gram contraction recovers the metric-dual evaluation](lean:inverseGram_contraction_eq_eval).
-/
private theorem surface_manifoldHilbertSchmidtInnerAt_eq_metricDual
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (cotangentInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (hinner : IsCotangentInnerForSurfaceMetric metric cotangentInner)
    (x : X) (ξ η : ℂ →L[ℝ] ℝ) :
    manifoldDifferentialHilbertSchmidtInnerAt
      (I := SurfaceRealModel) (X := X) metric.toManifoldMetric x ξ η =
        cotangentInner x ξ η := by
  classical
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  rcases hinner x ξ with ⟨v, hv, _hv_unique⟩
  let ι := Fin (Module.finrank ℝ ℂ)
  let b : Module.Basis ι ℝ ℂ := Module.finBasis ℝ ℂ
  let G : Matrix ι ι ℝ :=
    manifoldMetricModelGramMatrix
      (I := SurfaceRealModel) (X := X) metric.toManifoldMetric x
  let α : ι → ℝ := fun i ↦ b.repr v i
  let p : ι → ℝ := fun i ↦ ξ (b i)
  let q : ι → ℝ := fun i ↦ η (b i)
  have hG_pos : G.PosDef :=
    manifoldMetricModelGramMatrix_posDef
      (I := SurfaceRealModel) (X := X) metric.toManifoldMetric x
  have hG_symm : G.IsSymm :=
    manifoldMetricModelGramMatrix_isSymm
      (I := SurfaceRealModel) (X := X) metric.toManifoldMetric x
  have hv_sum : (∑ i : ι, α i • (b i : ℂ)) = v := by
    dsimp [α]
    exact b.sum_repr v
  have hv_sum_tangent :
      (∑ i : ι, α i • (show TangentSpace SurfaceRealModel x from b i)) =
        (show TangentSpace SurfaceRealModel x from v) := by
    change (∑ i : ι, α i • (b i : ℂ)) = v
    exact hv_sum
  have hp : p = Matrix.mulVec G α := by
    ext j
    calc
      p j =
          metric.toContMDiffRiemannianMetric.inner x
            (show TangentSpace SurfaceRealModel x from v)
            (show TangentSpace SurfaceRealModel x from b j) := by
        exact hv.1 (show TangentSpace SurfaceRealModel x from b j)
      _ = metric.toContMDiffRiemannianMetric.inner x
            (∑ i : ι, α i • (show TangentSpace SurfaceRealModel x from b i))
            (show TangentSpace SurfaceRealModel x from b j) := by
          exact congrArg
            (fun w : TangentSpace SurfaceRealModel x ↦
              metric.toContMDiffRiemannianMetric.inner x w
                (show TangentSpace SurfaceRealModel x from b j))
            hv_sum_tangent.symm
      _ = ∑ i : ι,
            α i *
              metric.toContMDiffRiemannianMetric.inner x
                (show TangentSpace SurfaceRealModel x from b i)
                (show TangentSpace SurfaceRealModel x from b j) := by
          rw [map_sum]
          simp only [ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          change
            (metric.toContMDiffRiemannianMetric.inner x
              (α i • (show TangentSpace SurfaceRealModel x from b i)))
              (show TangentSpace SurfaceRealModel x from b j) =
                α i *
                  (metric.toContMDiffRiemannianMetric.inner x
                    (show TangentSpace SurfaceRealModel x from b i))
                    (show TangentSpace SurfaceRealModel x from b j)
          rw [map_smulₛₗ]
          rfl
      _ = ∑ i : ι, G i j * α i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [G, manifoldMetricModelGramMatrix,
            SmoothRiemannianMetricOnSurface.toManifoldMetric,
            manifoldTangentModelBasisVector, b]
          ring
      _ = ∑ i : ι, G j i * α i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hG_symm.apply j i]
      _ = Matrix.mulVec G α j := by
          simp [Matrix.mulVec, dotProduct]
  have hηv : η v = ∑ i : ι, α i * q i := by
    calc
      η v = η (∑ i : ι, α i • (b i : ℂ)) := by
        exact congrArg η hv_sum.symm
      _ = ∑ i : ι, α i * η (b i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [map_smulₛₗ]
        simp
      _ = ∑ i : ι, α i * q i := rfl
  calc
    manifoldDifferentialHilbertSchmidtInnerAt
        (I := SurfaceRealModel) (X := X) metric.toManifoldMetric x ξ η
        = ∑ i : ι, ∑ j : ι, G⁻¹ i j * p i * q j := by
          simp only [manifoldDifferentialHilbertSchmidtInnerAt,
            manifoldMetricInverseGramCoeffAt, G, p, q, b,
            manifoldTangentModelBasisVector, real_inner_eq_mul_poincare]
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          ring_nf
          rfl
    _ = ∑ i : ι, α i * q i := by
          exact inverseGram_contraction_eq_eval G hG_pos α p q hp
    _ = η v := hηv.symm
    _ = cotangentInner x ξ η := (hv.2 η).symm

/--
%%handwave
name:
  Coordinate and intrinsic cotangent square norms agree
statement:
  For scalar differentials on a real surface, the intrinsic Hilbert-Schmidt
  square norm of the differential determined by a coordinate cotangent vector
  is the cotangent metric pairing of that vector with itself.
proof:
  In any surface chart the Hilbert-Schmidt norm contracts the two covector
  components against the inverse Riemannian metric matrix.  This is precisely
  the cotangent metric used to define the gradient-energy density.
-/
theorem surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    (g : BackgroundSurfaceMetricOnSurface X) (x : X)
    (ξ : ℂ →L[ℝ] ℝ) :
    (manifoldDifferentialHilbertBundleGeometry
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric).fiberNormSq
      x ξ =
    g.gradientInner x ξ ξ := by
  change manifoldDifferentialHilbertSchmidtInnerCLMAt
    (I := SurfaceRealModel) (X := X) (E := ℝ)
    g.metric.toManifoldMetric x ξ ξ = g.gradientInner x ξ ξ
  rw [manifoldDifferentialHilbertSchmidtInnerCLMAt_apply]
  exact
    surface_manifoldHilbertSchmidtInnerAt_eq_metricDual
      (metric := g.metric) (cotangentInner := g.gradientInner)
      (BackgroundSurfaceMetricOnSurface.gradientInner_isMetricDual g) x ξ ξ

/--
%%handwave
name:
  Coordinate and intrinsic cotangent pairings agree
statement:
  For scalar differentials on a real surface, the intrinsic Hilbert--Schmidt
  fiber pairing of two coordinate cotangent vectors is the background
  cotangent metric pairing of those vectors.
proof:
  The Hilbert--Schmidt pairing contracts the two covectors against the
  inverse Riemannian metric matrix, which is the cotangent metric pairing.
-/
theorem surface_coordinate_cotangent_fiberInner_eq_gradientInner
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    (g : BackgroundSurfaceMetricOnSurface X) (x : X)
    (ξ η : ℂ →L[ℝ] ℝ) :
    manifoldDifferentialHilbertSchmidtInnerCLMAt
      (I := SurfaceRealModel) (X := X) (E := ℝ)
      g.metric.toManifoldMetric x ξ η =
    g.gradientInner x ξ η := by
  rw [manifoldDifferentialHilbertSchmidtInnerCLMAt_apply]
  exact
    surface_manifoldHilbertSchmidtInnerAt_eq_metricDual
      (metric := g.metric) (cotangentInner := g.gradientInner)
      (BackgroundSurfaceMetricOnSurface.gradientInner_isMetricDual g) x ξ η

/--
%%handwave
name:
  Agreement of manifold and surface local value seminorms
statement:
  For a real function \(u\) and set \(K\), the manifold local value
  seminorm squared equals \(\int_Ku^2\,d\mu\), the surface local
  \(L^2\)-seminorm squared.
proof:
  Unfold both definitions and use \(\lVert u(x)\rVert^2=u(x)^2\).
-/
private theorem real_manifoldLocalValueL2SeminormSq_eq_surfaceLocalL2SeminormSq
    {X : Type} [MeasurableSpace X]
    (μ : Measure X) (K : Set X) (u : X → ℝ) :
    manifoldLocalValueL2SeminormSq μ K u =
      surfaceLocalL2SeminormSq μ K u := by
  dsimp [manifoldLocalValueL2SeminormSq, surfaceLocalL2SeminormSq]
  refine integral_congr_ae ?_
  filter_upwards [] with x
  simp [sq_abs]

/--
%%handwave
name:
  Agreement of manifold and surface differential energies
statement:
  For a coordinate cotangent field \(du\) on a surface,
  the manifold differential seminorm squared over \(K\) equals
  \[\int_K\langle du,du\rangle_{g^*}\,d\mu.\]
proof:
  Unfold both integrals and identify the intrinsic fiber Hilbert--Schmidt norm
  with the metric-dual cotangent norm pointwise.
-/
private theorem surface_coordinate_manifoldLocalDifferentialSeminormSq_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    (g : BackgroundSurfaceMetricOnSurface X) (K : Set X)
    (du : X → ℂ →L[ℝ] ℝ) :
    manifoldLocalDifferentialSeminormSq SurfaceRealModel
      g.metric.toManifoldMetric g.volume K
      (SurfaceCotangentField.ofCoordinateField du) =
    surfaceLocalGradientSeminormSq g K du := by
  dsimp [manifoldLocalDifferentialSeminormSq, surfaceLocalGradientSeminormSq]
  refine integral_congr_ae ?_
  filter_upwards [] with x
  simpa [SurfaceCotangentField.ofCoordinateField] using
    surface_coordinate_cotangent_fiberNormSq_eq_gradientInner g x (du x)

/--
%%handwave
name:
  Agreement of manifold and surface local \(H^1\) seminorms
statement:
  For a real function \(u\) and coordinate weak differential \(du\), the
  manifold local \(H^1\)-seminorm squared on \(K\) equals the sum of the
  surface local \(L^2\)-mass and gradient energy.
proof:
  Combine [agreement of the value seminorms](lean:real_manifoldLocalValueL2SeminormSq_eq_surfaceLocalL2SeminormSq) with [agreement of the differential energies](lean:surface_coordinate_manifoldLocalDifferentialSeminormSq_eq).
-/
private theorem surface_coordinate_manifoldLocalH1SeminormSq_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    (g : BackgroundSurfaceMetricOnSurface X) (K : Set X)
    (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) :
    manifoldLocalH1SeminormSq SurfaceRealModel g.metric.toManifoldMetric
      g.volume K u (SurfaceCotangentField.ofCoordinateField du) =
    surfaceLocalH1SeminormSq g K u du := by
  dsimp [manifoldLocalH1SeminormSq, surfaceLocalH1SeminormSq]
  rw [real_manifoldLocalValueL2SeminormSq_eq_surfaceLocalL2SeminormSq,
    surface_coordinate_manifoldLocalDifferentialSeminormSq_eq]

/--
%%handwave
name:
  Nonnegativity of local surface gradient energy
statement:
  For every cotangent field \(du\) and set \(U\),
  \(0\le\int_U\langle du,du\rangle_{g^*}\,d\mu\).
proof:
  The metric-dual squared norm is pointwise nonnegative, so its integral is
  nonnegative.
-/
private theorem surfaceLocalGradientSeminormSq_nonneg
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) (U : Set X)
    (du : X → ℂ →L[ℝ] ℝ) :
    0 ≤ surfaceLocalGradientSeminormSq g U du := by
  dsimp [surfaceLocalGradientSeminormSq]
  exact integral_nonneg fun x ↦ g.gradientInner_nonneg x (du x)

/--
%%handwave
name:
  Quadratic scaling of local surface gradient energy
statement:
  For \(c\in\mathbb R\),
  \[\int_U\langle c\,du,c\,du\rangle_{g^*}\,d\mu
    =c^2\int_U\langle du,du\rangle_{g^*}\,d\mu.\]
proof:
  Apply bilinearity of the cotangent pairing pointwise and move the constant
  \(c^2\) outside the integral.
-/
private theorem surfaceLocalGradientSeminormSq_const_smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) (U : Set X)
    (c : ℝ) (du : X → ℂ →L[ℝ] ℝ) :
    surfaceLocalGradientSeminormSq g U (fun x ↦ c • du x) =
      c ^ (2 : ℕ) * surfaceLocalGradientSeminormSq g U du := by
  dsimp [surfaceLocalGradientSeminormSq]
  calc
    ∫ x in U, g.gradientInner x (c • du x) (c • du x) ∂g.volume =
        ∫ x in U, c ^ (2 : ℕ) * g.gradientInner x (du x) (du x) ∂g.volume := by
          refine integral_congr_ae ?_
          filter_upwards [] with x
          exact BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul
            g x (du x) c
    _ = c ^ (2 : ℕ) *
        ∫ x in U, g.gradientInner x (du x) (du x) ∂g.volume := by
          rw [integral_const_mul]

/--
%%handwave
name:
  Subtracting a constant preserves the weak gradient
statement:
  If \(du\) is a weak gradient of \(u\) on \(U\), then it is also a weak
  gradient of \(u-a\) for every constant \(a\in\mathbb R\).
proof:
  In the weak integration-by-parts identity, the new constant term is
  \(a\int D_v\varphi\). This vanishes because the test function is smooth and
  compactly supported; all remaining terms are unchanged.
-/
private theorem IsWeakGradientOnRegion.sub_const_real {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (a : ℝ) (hweak : IsWeakGradientOnRegion U u du) :
    IsWeakGradientOnRegion U (fun x : X ↦ u x - a) du := by
  intro e he φ v
  rcases hweak e he φ v with ⟨hu_int, hdu_int, h_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e U
  let μΩ : Measure ℂ := MeasureTheory.volume.restrict Ω
  let dφ : ℂ → ℝ := fun z : ℂ ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  have hφ_compact : HasCompactSupport (φ : ℂ → ℝ) := φ.compact_support
  have hφ_cont : Continuous (φ : ℂ → ℝ) := φ.smooth.continuous
  have hdφ_compact : HasCompactSupport dφ := by
    simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) v
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ_int : Integrable dφ (MeasureTheory.volume : Measure ℂ) :=
    hdφ_cont.integrable_of_hasCompactSupport hdφ_compact
  have hconst_intΩ :
      Integrable (fun z : ℂ ↦ dφ z • a)
        (MeasureTheory.volume.restrict Ω) :=
    (hdφ_int.smul_const a).mono_measure Measure.restrict_le_self
  have hconst_zeroΩ :
      ∫ z in Ω, dφ z • a ∂MeasureTheory.volume = 0 := by
    have hsupport :
        ∀ z : ℂ, z ∉ Ω → dφ z • a = 0 := by
      intro z hzΩ
      have hz_not_tsupport : z ∉ tsupport dφ := by
        intro hz
        exact hzΩ <| φ.support_subset <|
          (tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (φ : ℂ → ℝ)) v) (by simpa [dφ] using hz)
      have hdφ_zero : dφ z = 0 :=
        image_eq_zero_of_notMem_tsupport hz_not_tsupport
      simp [hdφ_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
    have hφ_int : Integrable (φ : ℂ → ℝ)
        (MeasureTheory.volume : Measure ℂ) :=
      hφ_cont.integrable_of_hasCompactSupport hφ_compact
    have hibp :
        ∫ z, (φ : ℂ → ℝ) z •
            fderiv ℝ (fun _ : ℂ ↦ a) z v ∂MeasureTheory.volume =
          -∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • a
            ∂MeasureTheory.volume :=
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (μ := (MeasureTheory.volume : Measure ℂ))
        (f := (φ : ℂ → ℝ)) (g := fun _ : ℂ ↦ a) (v := v)
        (by simpa [dφ] using hdφ_int.smul_const a)
        (by simp)
        (hφ_int.smul_const a)
        (fun z _hz ↦ (φ.smooth.differentiable (by simp)) z)
        (fun z _hz ↦ differentiableAt_const a)
    have hzero_neg :
        (0 : ℝ) =
          -∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • a
            ∂MeasureTheory.volume := by
      simpa using hibp
    simpa [dφ] using neg_eq_zero.mp hzero_neg.symm
  refine ⟨?_, hdu_int, ?_⟩
  · convert hu_int.sub hconst_intΩ using 1
    ext z
    simp [dφ]
    ring
  · calc
      ∫ z in surfaceChartRegion e U,
          (u (e.symm z) - a) * fderiv ℝ (φ : ℂ → ℝ) z v
          ∂MeasureTheory.volume
          =
        ∫ z in Ω,
          (u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v -
            fderiv ℝ (φ : ℂ → ℝ) z v • a) ∂MeasureTheory.volume := by
            congr 1
            ext z
            simp
            ring
      _ =
        ∫ z in Ω, u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
          ∂MeasureTheory.volume -
        ∫ z in Ω, fderiv ℝ (φ : ℂ → ℝ) z v • a
          ∂MeasureTheory.volume := by
            simpa [dφ] using integral_sub hu_int hconst_intΩ
      _ = -∫ z in Ω,
          du (e.symm z) (surfaceChartTangentMap e z v) * φ z
          ∂MeasureTheory.volume - 0 := by
            rw [h_eq, hconst_zeroΩ]
      _ = -∫ z in surfaceChartRegion e U,
          du (e.symm z) (surfaceChartTangentMap e z v) * φ z
          ∂MeasureTheory.volume := by
            simp [Ω]

/--
%%handwave
name:
  Local gradient energy is bounded by finite global Dirichlet energy
statement:
  If the geometric gradient-energy density of a zero-trace Sobolev function
  is integrable on the whole surface, then its integral over any region is at
  most the global Dirichlet energy.
proof:
  The local and global energies integrate the same nonnegative density.  Apply
  monotonicity of the Bochner integral under restriction of the measure.
-/
private theorem surfaceLocalGradientSeminormSq_le_greenDirichletSeminormSq_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X}
    (u : SobolevH1ZeroOnSurface g.volume)
    (hInt :
      Integrable
        (fun x : X ↦ g.gradientInner x (u.weakGradient x) (u.weakGradient x))
        g.volume) :
    surfaceLocalGradientSeminormSq g U u.weakGradient ≤
      greenDirichletSeminormSq g u := by
  dsimp [surfaceLocalGradientSeminormSq, greenDirichletSeminormSq]
  exact
    setIntegral_le_integral hInt
      (Filter.Eventually.of_forall fun x ↦
        BackgroundSurfaceMetricOnSurface.gradientInner_nonneg g x (u.weakGradient x))

/--
%%handwave
name:
  Finite global vanishing Dirichlet energy gives local vanishing gradient energy
statement:
  If the geometric gradient-energy density of each term in a zero-trace
  Sobolev sequence is globally integrable and the global Dirichlet energies
  tend to zero, then the local gradient energy on any region tends to zero.
proof:
  The local energy is nonnegative and is bounded by the corresponding global
  Dirichlet energy for each term.  Squeeze between zero and the global
  energies.
-/
private theorem surfaceLocalGradientSeminormSq_tendsto_zero_of_greenDirichlet_tendsto_zero_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X}
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦ surfaceLocalGradientSeminormSq g U (Z n).weakGradient)
      Filter.atTop (𝓝 0) := by
  have hnonneg :
      ∀ n : ℕ, 0 ≤ surfaceLocalGradientSeminormSq g U (Z n).weakGradient := by
    intro n
    exact surfaceLocalGradientSeminormSq_nonneg g U (Z n).weakGradient
  have hle :
      ∀ n : ℕ,
        surfaceLocalGradientSeminormSq g U (Z n).weakGradient ≤
          greenDirichletSeminormSq g (Z n) := by
    intro n
    exact
      surfaceLocalGradientSeminormSq_le_greenDirichletSeminormSq_of_integrable
        (g := g) (U := U) (Z n) (hZ_int n)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hZ_energy hnonneg hle

/--
%%handwave
name:
  Weak gradient of a zero-trace Sobolev function in surface coordinates
statement:
  For a zero-trace Sobolev function \(u\) on a surface, the coordinate
  pullback \(u\circ e^{-1}\) has Euclidean weak derivative equal to the chart
  pullback of its surface weak gradient.
proof:
  Apply the defining surface weak-gradient identity to the same compactly
  supported coordinate test and rewrite the tangent evaluation as chart
  pullback.
-/
private theorem surface_zeroTrace_chartPullback_weakGradient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : SobolevH1ZeroOnSurface g.volume)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    IsWeakDerivativeOnEuclideanRegionScalar (surfaceChartRegion e (Set.univ : Set X))
      (fun z : ℂ ↦ u (e.symm z))
      (ManifoldDifferentialField.chartPullback
        (I := SurfaceRealModel)
        (SurfaceCotangentField.ofCoordinateField u.weakGradient) e) := by
  intro φ v
  let ψ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X)) :=
    { toFun := φ
      smooth := φ.smooth
      support_subset := φ.support_subset
      compact_support := φ.compact_support }
  have h := (u.isLocalSobolevH1OnSurface (Set.univ : Set X)).1 e he ψ v
  simpa [ψ, IsWeakDerivativeOnEuclideanRegionScalar,
    IsWeakDerivativeOnEuclideanRegionWithValues,
    ManifoldDifferentialField.chartPullback, surfaceChartRegion,
    surfaceChartTangentMap, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/--
%%handwave
name:
  Vanishing \(L^2\)-norm of the gradient magnitude
statement:
  Let \(Z_n\) have integrable gradient-energy density and global Dirichlet
  energy tending to zero. For every set \(K\), the functions
  \[x\mapsto\sqrt{\langle dZ_n(x),dZ_n(x)\rangle_{g^*}}\]
  belong to \(L^2(K)\), and their \(L^2(K)\)-norms tend to zero.
proof:
  Their squares are exactly the nonnegative gradient-energy densities.
  Local energy is bounded by global energy and tends to zero; take square
  roots and use the squeeze theorem.
-/
private theorem sqrt_gradientInner_memLp_and_eLpNorm_tendsto_zero_on_set
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    (∀ n : ℕ,
      MemLp
        (fun x : X ↦
          Real.sqrt
            (g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x)))
        2 (g.volume.restrict K)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun x : X ↦
              Real.sqrt
                (g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x)))
            2 (g.volume.restrict K))
        Filter.atTop (𝓝 0) := by
  classical
  let Gseq : ℕ → X → ℝ := fun n x ↦
    g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x)
  let Sseq : ℕ → X → ℝ := fun n x ↦ Real.sqrt (Gseq n x)
  have hS_mem : ∀ n : ℕ, MemLp (Sseq n) 2 (g.volume.restrict K) := by
    intro n
    let μK : Measure X := g.volume.restrict K
    have hG_int_K : Integrable (Gseq n) μK := by
      simpa [Gseq, μK] using (hZ_int n).restrict (s := K)
    have hG_aestr : AEStronglyMeasurable (Gseq n) μK :=
      hG_int_K.aestronglyMeasurable
    have hS_aestr : AEStronglyMeasurable (Sseq n) μK := by
      simpa [Sseq] using
        (Real.continuous_sqrt.comp_aestronglyMeasurable hG_aestr)
    have hsq_int : Integrable (fun x : X ↦ (Sseq n x) ^ (2 : ℕ)) μK := by
      refine hG_int_K.congr ?_
      filter_upwards with x
      have hnonneg : 0 ≤ Gseq n x :=
        BackgroundSurfaceMetricOnSurface.gradientInner_nonneg
          g x ((Z n).weakGradient x)
      simp [Sseq, Real.sq_sqrt hnonneg]
    exact (memLp_two_iff_integrable_sq hS_aestr).2 hsq_int
  have hgrad_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ surfaceLocalGradientSeminormSq g K (Z n).weakGradient)
        Filter.atTop (𝓝 0) :=
    surfaceLocalGradientSeminormSq_tendsto_zero_of_greenDirichlet_tendsto_zero_of_integrable
      (g := g) (U := K) Z hZ_int hZ_energy
  have hS_bound :
      ∀ n : ℕ,
        eLpNorm (Sseq n) 2 (g.volume.restrict K) ≤
          ENNReal.ofReal
              (surfaceLocalGradientSeminormSq g K (Z n).weakGradient) ^
            ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
    intro n
    have hint_eq :
        ∫ x, ‖Sseq n x‖ ^ 2 ∂(g.volume.restrict K) =
          surfaceLocalGradientSeminormSq g K (Z n).weakGradient := by
      dsimp [surfaceLocalGradientSeminormSq]
      refine integral_congr_ae ?_
      filter_upwards with x
      have hnonneg : 0 ≤ Gseq n x :=
        BackgroundSurfaceMetricOnSurface.gradientInner_nonneg
          g x ((Z n).weakGradient x)
      simp [Sseq, Gseq, Real.sq_sqrt hnonneg]
    have hle :
        ∫ x, ‖Sseq n x‖ ^ 2 ∂(g.volume.restrict K) ≤
          surfaceLocalGradientSeminormSq g K (Z n).weakGradient := by
      rw [hint_eq]
    exact eLpNorm_two_le_of_integral_sq_le (hS_mem n) hle
  have hupper :
      Filter.Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal
              (surfaceLocalGradientSeminormSq g K (Z n).weakGradient) ^
            ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal)
        Filter.atTop (𝓝 0) := by
    have hofReal :
        Filter.Tendsto
          (fun n : ℕ ↦
            ENNReal.ofReal
              (surfaceLocalGradientSeminormSq g K (Z n).weakGradient))
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa using ENNReal.tendsto_ofReal hgrad_tendsto
    have hq_pos :
        0 < ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
      norm_num
    simpa [ENNReal.zero_rpow_of_pos hq_pos] using
      (Filter.Tendsto.ennrpow_const
        ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal hofReal)
  refine ⟨by simpa [Sseq, Gseq] using hS_mem, ?_⟩
  have hnonneg :
      (fun _n : ℕ ↦ (0 : ℝ≥0∞)) ≤ᶠ[Filter.atTop]
        fun n : ℕ ↦ eLpNorm (Sseq n) 2 (g.volume.restrict K) :=
    Filter.Eventually.of_forall fun _ ↦ zero_le
  have hle :
      (fun n : ℕ ↦ eLpNorm (Sseq n) 2 (g.volume.restrict K)) ≤ᶠ[Filter.atTop]
        fun n : ℕ ↦
          ENNReal.ofReal
              (surfaceLocalGradientSeminormSq g K (Z n).weakGradient) ^
            ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal :=
    Filter.Eventually.of_forall hS_bound
  simpa [Sseq, Gseq] using
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper hnonneg hle

/--
%%handwave
name:
  Surface \(L^2\)-norm controlled by its coordinate pullback
statement:
  Let \(K_0\) be compact in one chart and \(K_{\mathrm{coord}}=e(K_0)\).
  For a smooth positive surface measure, there is a finite \(C\) such that
  \[\lVert f-a\rVert_{L^2(K_0,\mu)}
    \le C\lVert(f-a)\circ e^{-1}\rVert_{L^2(K_{\mathrm{coord}})}\]
  whenever both sides are defined.
proof:
  In coordinates the surface measure is Lebesgue measure weighted by a smooth
  positive density. Bound that density above on the compact coordinate set
  and apply the weighted \(L^2\)-norm estimate.
-/
private theorem chartPullback_eLpNorm_two_sub_const_surface_le
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ : Set X} {Kcoord : Set H} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_source : K₀ ⊆ (chartAt H c).source)
    (hKcoord_def : Kcoord = (chartAt H c) '' K₀) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (f : X → ℝ) (a : ℝ),
        MemLp (fun x : X ↦ f x - a) 2 (μ.restrict K₀) →
        MemLp (fun z : H ↦ f ((chartAt H c).symm z) - a) 2
          (MeasureTheory.volume.restrict Kcoord) →
        eLpNorm (fun x : X ↦ f x - a) 2 (μ.restrict K₀) ≤
          C * eLpNorm (fun z : H ↦ f ((chartAt H c).symm z) - a) 2
            (MeasureTheory.volume.restrict Kcoord) := by
  classical
  let e : OpenPartialHomeomorph X H := chartAt H c
  have he : e ∈ atlas H X := chart_mem_atlas H c
  have hKcoord_eq : Kcoord = e '' K₀ := by
    simpa [e] using hKcoord_def
  have hKcoord_target : Kcoord ⊆ e.target := by
    rw [hKcoord_eq]
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact e.map_source (hK₀_source hxK)
  have hKcoord_compact : IsCompact Kcoord := by
    rw [hKcoord_eq]
    exact hK₀_compact.image_of_continuousOn (e.continuousOn.mono hK₀_source)
  have hKcoord_meas : MeasurableSet Kcoord := hKcoord_compact.measurableSet
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, _hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hρ_cont_Kcoord : ContinuousOn ρ Kcoord :=
    hρ_smooth.continuousOn.mono hKcoord_target
  rcases hKcoord_compact.exists_bound_of_continuousOn hρ_cont_Kcoord with
    ⟨M, hM⟩
  let R : ℝ := max M 1
  let c₁ : ℝ≥0∞ := ENNReal.ofReal R
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  let C : ℝ≥0∞ := c₁ ^ q
  have hR_pos : 0 < R := by
    dsimp [R]
    exact lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hc₁_ne_zero : c₁ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hR_pos)
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hC_top : C < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg hq_nonneg (by simp [c₁])
  have hδ_upper : ∀ᵐ z ∂ν.restrict Kcoord, δ z ≤ c₁ := by
    filter_upwards [ae_restrict_mem hKcoord_meas] with z hzK
    have hρ_le_norm : ρ z ≤ ‖ρ z‖ := le_abs_self (ρ z)
    have hnorm_le_R : ‖ρ z‖ ≤ R :=
      (hM z hzK).trans (le_max_left M 1)
    exact ENNReal.ofReal_le_ofReal (hρ_le_norm.trans hnorm_le_R)
  refine ⟨C, hC_top, ?_⟩
  intro f a hfbase_mem hFpull_mem
  let fbase : X → ℝ := fun x ↦ f x - a
  let Fpull : H → ℝ := fun z ↦ f (e.symm z) - a
  let μsK : Measure X := (μ.restrict e.source).restrict (e ⁻¹' Kcoord)
  have hpre_ae : e ⁻¹' Kcoord =ᵐ[μ.restrict e.source] K₀ := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx_source
    apply propext
    constructor
    · intro hxK
      rw [hKcoord_eq] at hxK
      rcases hxK with ⟨y, hyK₀, hyx⟩
      have hy_source : y ∈ e.source := hK₀_source hyK₀
      have hy_eq_x : y = x := e.injOn hy_source hx_source hyx
      simpa [hy_eq_x] using hyK₀
    · intro hxK₀
      rw [hKcoord_eq]
      exact ⟨x, hxK₀, rfl⟩
  have hμsK_eq : μsK = μ.restrict K₀ := by
    calc
      μsK = (μ.restrict e.source).restrict K₀ := by
        simpa [μsK] using Measure.restrict_congr_set hpre_ae
      _ = μ.restrict K₀ := Measure.restrict_restrict_of_subset hK₀_source
  have he_aemeas_source : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have he_aemeas_μsK : AEMeasurable e μsK := by
    exact he_aemeas_source.mono_measure (by
      dsimp [μsK]
      exact Measure.restrict_le_self)
  have hsymm_big :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
    have hsymm_vol :
        AEMeasurable e.symm (MeasureTheory.volume.restrict e.target) :=
      openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume
    have h_ac :
        Measure.map e (μ.restrict e.source) ≪
          MeasureTheory.volume.restrict e.target := by
      rw [hmap]
      exact withDensity_absolutelyContinuous _ _
    exact hsymm_vol.mono_ac h_ac
  have hmap_μsK_le :
      Measure.map e μsK ≤ Measure.map e (μ.restrict e.source) :=
    Measure.map_mono_of_aemeasurable (by
      dsimp [μsK]
      exact Measure.restrict_le_self) he_aemeas_source
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μsK) :=
    hsymm_big.mono_measure hmap_μsK_le
  have hmap_symm : Measure.map e.symm (Measure.map e μsK) = μsK := by
    have hmap_comp :
        Measure.map e.symm (Measure.map e μsK) =
          Measure.map (fun x : X ↦ e.symm (e x)) μsK := by
      simpa [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable hsymm_aemeas he_aemeas_μsK)
    have hleft :
        (fun x : X ↦ e.symm (e x)) =ᵐ[μsK] fun x ↦ x := by
      have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
        dsimp [μsK]
        exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
      exact hsource_ae.mono fun x hx_source ↦ e.left_inv hx_source
    calc
      Measure.map e.symm (Measure.map e μsK)
          = Measure.map (fun x : X ↦ e.symm (e x)) μsK := hmap_comp
      _ = Measure.map (fun x : X ↦ x) μsK := Measure.map_congr hleft
      _ = μsK := by rw [Measure.map_id']
  have hfbase_μsK : MemLp fbase 2 μsK := by
    simpa [hμsK_eq, fbase] using hfbase_mem
  have hfbase_aestr_map_symm :
      AEStronglyMeasurable fbase (Measure.map e.symm (Measure.map e μsK)) := by
    simpa [hmap_symm] using hfbase_μsK.aestronglyMeasurable
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μsK) := by
    simpa [Fpull, fbase, Function.comp_def] using
      hfbase_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hcomp_eq :
      (fun x : X ↦ Fpull (e x)) =ᵐ[μsK] fbase := by
    have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
      dsimp [μsK]
      exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
    exact hsource_ae.mono fun x hx_source ↦ by
      simp [Fpull, fbase, e.left_inv hx_source]
  have hmap_restrict :
      (Measure.map e (μ.restrict e.source)).restrict Kcoord =
        Measure.map e μsK := by
    dsimp [μsK]
    exact Measure.restrict_map_of_aemeasurable he_aemeas_source hKcoord_meas
  have hweighted_eq :
      (ν.withDensity δ).restrict Kcoord = Measure.map e μsK := by
    calc
      (ν.withDensity δ).restrict Kcoord
          = (Measure.map e (μ.restrict e.source)).restrict Kcoord := by
              simpa [ν, δ] using congrArg (fun m : Measure H ↦ m.restrict Kcoord) hmap.symm
      _ = Measure.map e μsK := hmap_restrict
  have hweighted_norm :
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict Kcoord) =
        eLpNorm fbase 2 (μ.restrict K₀) := by
    calc
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict Kcoord)
          = eLpNorm Fpull 2 (Measure.map e μsK) := by rw [hweighted_eq]
      _ = eLpNorm (fun x : X ↦ Fpull (e x)) 2 μsK := by
            exact eLpNorm_map_measure hFpull_aestr he_aemeas_μsK
      _ = eLpNorm fbase 2 μsK := eLpNorm_congr_ae hcomp_eq
      _ = eLpNorm fbase 2 (μ.restrict K₀) := by rw [hμsK_eq]
  have hνKcoord_eq :
      ν.restrict Kcoord = MeasureTheory.volume.restrict Kcoord := by
    simpa [ν] using
      Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume) hKcoord_target
  have hupper :
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict Kcoord) ≤
        C * eLpNorm Fpull 2 (ν.restrict Kcoord) := by
    simpa [C, q] using
      eLpNorm_two_withDensity_upper_bound_on_restrict_le
        (ν := ν) (δ := δ) (K := Kcoord) (c := c₁)
        hKcoord_meas hc₁_ne_zero hδ_upper Fpull
  calc
    eLpNorm (fun x : X ↦ f x - a) 2 (μ.restrict K₀)
        = eLpNorm fbase 2 (μ.restrict K₀) := rfl
    _ = eLpNorm Fpull 2 ((ν.withDensity δ).restrict Kcoord) := hweighted_norm.symm
    _ ≤ C * eLpNorm Fpull 2 (ν.restrict Kcoord) := hupper
    _ = C *
          eLpNorm (fun z : H ↦ f ((chartAt H c).symm z) - a) 2
            (MeasureTheory.volume.restrict Kcoord) := by
        rw [hνKcoord_eq]

/--
%%handwave
name:
  Vanishing coordinate evaluation of pulled-back weak gradients
statement:
  Let \(Z_n\) have integrable gradient density and Dirichlet energy tending to
  zero. On a chart ball compactly contained in the chart target, for every
  fixed \(v\in\mathbb C\), the scalar fields
  \(z\mapsto(e^*dZ_n)_z(v)\) lie in \(L^2\), and their \(L^2\)-norms tend to
  zero.
proof:
  Pull the intrinsic gradient magnitude to coordinates and use compact chart
  norm comparison. Pointwise evaluation of a differential is uniformly
  bounded by its Hilbert--Schmidt norm on the compact chart ball.
-/
private theorem chartBall_chartPullback_weakGradient_eval_memLp_tendsto_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel 1 X]
    [SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0))
    (c : X) {r R : ℝ} (hr_pos : 0 < r) (hrR : r < R)
    (hclosed_target :
      Metric.closedBall ((chartAt ℂ c) c) R ⊆ (chartAt ℂ c).target)
    (v : ℂ) :
    (∀ n : ℕ,
      MemLp
        (fun z : ℂ ↦
          ManifoldDifferentialField.chartPullback
            (I := SurfaceRealModel)
            (SurfaceCotangentField.ofCoordinateField (Z n).weakGradient)
            (chartAt ℂ c) z v)
        2
        (MeasureTheory.volume.restrict
          (Metric.ball ((chartAt ℂ c) c) r))) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun z : ℂ ↦
              ManifoldDifferentialField.chartPullback
                (I := SurfaceRealModel)
                (SurfaceCotangentField.ofCoordinateField (Z n).weakGradient)
                (chartAt ℂ c) z v)
            2
            (MeasureTheory.volume.restrict
              (Metric.ball ((chartAt ℂ c) c) r)))
        Filter.atTop (𝓝 0) := by
  classical
  haveI : ProperSpace ℂ := FiniteDimensional.proper ℝ ℂ
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ c
  let zc : ℂ := e c
  let B : Set ℂ := Metric.ball zc r
  let Kcoord : Set ℂ := Metric.closedBall zc r
  let Ksurf : Set X := e.symm '' Kcoord
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ c
  have hKcoord_target : Kcoord ⊆ e.target := by
    dsimp [Kcoord, zc, e]
    exact (Metric.closedBall_subset_closedBall (x := (chartAt ℂ c) c)
      (le_of_lt hrR)).trans hclosed_target
  have hB_Kcoord : B ⊆ Kcoord := by
    dsimp [B, Kcoord]
    exact Metric.ball_subset_closedBall
  have hB_region : B ⊆ surfaceChartRegion e (Set.univ : Set X) := by
    intro z hz
    exact ⟨hKcoord_target (hB_Kcoord hz), trivial⟩
  have hKcoord_region :
      Kcoord ⊆ surfaceChartRegion e (Set.univ : Set X) := by
    intro z hz
    exact ⟨hKcoord_target hz, trivial⟩
  have hKcoord_compact : IsCompact Kcoord := by
    dsimp [Kcoord]
    exact isCompact_closedBall zc r
  have hKcoord_meas : MeasurableSet Kcoord := hKcoord_compact.measurableSet
  have hB_meas : MeasurableSet B := by
    dsimp [B]
    exact Metric.isOpen_ball.measurableSet
  have hKsurf_compact : IsCompact Ksurf := by
    dsimp [Ksurf]
    exact hKcoord_compact.image_of_continuousOn
      (e.continuousOn_symm.mono hKcoord_target)
  have hKsurf_source : Ksurf ⊆ e.source := by
    rintro x ⟨z, hzK, rfl⟩
    exact e.map_target (hKcoord_target hzK)
  have hKcoord_def : Kcoord = e '' Ksurf := by
    ext z
    constructor
    · intro hz
      refine ⟨e.symm z, ⟨z, hz, rfl⟩, ?_⟩
      exact e.right_inv (hKcoord_target hz)
    · rintro ⟨x, ⟨w, hwK, rfl⟩, rfl⟩
      simpa [e.right_inv (hKcoord_target hwK)] using hwK
  let hμ : SmoothPositiveMeasureOnManifold (I := SurfaceRealModel) g.volume :=
    { finite_on_compact :=
        (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).finite_on_compact
      chart_density :=
        (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).chart_density }
  let Sseq : ℕ → X → ℝ := fun n x ↦
    Real.sqrt
      (g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
  let Spull : ℕ → ℂ → ℝ := fun n z ↦ Sseq n (e.symm z)
  let Dseq : ℕ → ℂ → ℝ := fun n z ↦
    ManifoldDifferentialField.chartPullback
      (I := SurfaceRealModel)
      (SurfaceCotangentField.ofCoordinateField (Z n).weakGradient) e z v
  rcases
    sqrt_gradientInner_memLp_and_eLpNorm_tendsto_zero_on_set
      (g := g) (K := Ksurf) Z hZ_int hZ_energy with
    ⟨hS_mem, hS_tendsto⟩
  have hSpull_mem_Kcoord : ∀ n : ℕ,
      MemLp (Spull n) 2 (MeasureTheory.volume.restrict Kcoord) := by
    intro n
    simpa [Spull, Sseq, e, Kcoord] using
      smoothPositiveMeasureOnManifold_chartPullback_memLp_on_compact_of_memLp
        (I := SurfaceRealModel) (μ := g.volume) hμ e he
        hKsurf_compact hKsurf_source hKcoord_def (hS_mem n)
  have hSpull_tendsto_Kcoord :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (Spull n) 2
          (MeasureTheory.volume.restrict Kcoord))
        Filter.atTop (𝓝 0) := by
    rcases
      localRellich_chartPullback_eLpNorm_two_le_on_compact
        (H := ℂ) (X := X) (E := ℝ) (I := SurfaceRealModel)
        (μ := g.volume) hμ c hKsurf_compact hKsurf_source
        (by simpa [e, Kcoord] using hKcoord_def) with
      ⟨Cchart, hCchart_top, hCchart⟩
    have hbound : ∀ n : ℕ,
        eLpNorm (Spull n) 2 (MeasureTheory.volume.restrict Kcoord) ≤
          Cchart * eLpNorm (Sseq n) 2 (g.volume.restrict Ksurf) := by
      intro n
      simpa [Spull, Sseq, e, Kcoord] using hCchart (Sseq n) (hS_mem n)
    have hC_ne_top : Cchart ≠ ⊤ := ne_of_lt hCchart_top
    have hupper :
        Filter.Tendsto
          (fun n : ℕ ↦
            Cchart * eLpNorm (Sseq n) 2 (g.volume.restrict Ksurf))
          Filter.atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hS_tendsto (Or.inr hC_ne_top)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper
        (fun _n ↦ zero_le)
        hbound
  have hSpull_mem_B : ∀ n : ℕ,
      MemLp (Spull n) 2 (MeasureTheory.volume.restrict B) := by
    intro n
    exact (hSpull_mem_Kcoord n).mono_measure
      (Measure.restrict_mono hB_Kcoord le_rfl)
  have hSpull_tendsto_B :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (Spull n) 2
          (MeasureTheory.volume.restrict B))
        Filter.atTop (𝓝 0) := by
    have hle : ∀ n : ℕ,
        eLpNorm (Spull n) 2 (MeasureTheory.volume.restrict B) ≤
          eLpNorm (Spull n) 2 (MeasureTheory.volume.restrict Kcoord) := by
      intro n
      exact eLpNorm_mono_measure (Spull n)
        (Measure.restrict_mono hB_Kcoord le_rfl)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hSpull_tendsto_Kcoord
        (fun _n ↦ zero_le)
        hle
  rcases
    manifoldDifferentialCompactEvaluation_pointwise_norm_le
      (I := SurfaceRealModel) (X := X) (E := ℝ)
      g.metric.toManifoldMetric e he Kcoord v hKcoord_region hKcoord_compact with
    ⟨Ceval, hCeval⟩
  let β : ContDiffBump zc :=
    { rIn := r
      rOut := R
      rIn_pos := hr_pos
      rIn_lt_rOut := hrR }
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X)) :=
    { toFun := β
      smooth := β.contDiff
      support_subset := by
        intro z hz
        have hzR : z ∈ Metric.closedBall zc R := by
          simpa [β] using (by
            rw [β.tsupport_eq] at hz
            exact hz)
        exact ⟨by simpa [e, zc] using hclosed_target hzR, trivial⟩
      compact_support := by
        rw [β.tsupport_eq]
        simpa [β] using (isCompact_closedBall zc R) }
  have hD_mem : ∀ n : ℕ,
      MemLp (Dseq n) 2 (MeasureTheory.volume.restrict B) := by
    intro n
    have hweak :=
      surface_zeroTrace_chartPullback_weakGradient
        (g := g) (Z n) e he
    rcases hweak ψ v with ⟨_hleft_int, hright_int, _hidentity⟩
    have hright_B :
        Integrable
          (fun z : ℂ ↦ ψ z • Dseq n z)
          (MeasureTheory.volume.restrict B) := by
      have hright' :
          Integrable
            (fun z : ℂ ↦
              ψ z •
                ManifoldDifferentialField.chartPullback
                  (I := SurfaceRealModel)
                  (SurfaceCotangentField.ofCoordinateField (Z n).weakGradient)
                  e z v)
            (MeasureTheory.volume.restrict
              (surfaceChartRegion e (Set.univ : Set X))) := by
        simpa [Dseq, smul_eq_mul] using hright_int
      exact hright'.mono_measure
        (Measure.restrict_mono hB_region le_rfl)
    have hprod_eq :
        (fun z : ℂ ↦ ψ z • Dseq n z) =ᵐ[
            MeasureTheory.volume.restrict B] Dseq n := by
      filter_upwards [ae_restrict_mem hB_meas] with z hzB
      have hzK : z ∈ Kcoord := hB_Kcoord hzB
      have hψ_one : ψ z = 1 := by
        have hzClosed : z ∈ Metric.closedBall zc β.rIn := by
          simpa [β, Kcoord] using hzK
        simpa [ψ] using β.one_of_mem_closedBall hzClosed
      simp [hψ_one]
    have hD_int : Integrable (Dseq n) (MeasureTheory.volume.restrict B) :=
      hright_B.congr hprod_eq
    have hD_aestr : AEStronglyMeasurable (Dseq n)
        (MeasureTheory.volume.restrict B) :=
      hD_int.aestronglyMeasurable
    have hpoint :
        ∀ᵐ z ∂MeasureTheory.volume.restrict B,
          ‖Dseq n z‖ ≤ (Ceval : ℝ) * ‖Spull n z‖ := by
      filter_upwards [ae_restrict_mem hB_meas] with z hzB
      have hzK : z ∈ Kcoord := hB_Kcoord hzB
      have h_eval :=
        hCeval z hzK
          ((SurfaceCotangentField.ofCoordinateField (Z n).weakGradient) (e.symm z))
      have hnonneg :
          0 ≤
            g.gradientInner (e.symm z)
              ((Z n).weakGradient (e.symm z))
              ((Z n).weakGradient (e.symm z)) :=
        BackgroundSurfaceMetricOnSurface.gradientInner_nonneg
          g (e.symm z) ((Z n).weakGradient (e.symm z))
      calc
        ‖Dseq n z‖ ≤
            (Ceval : ℝ) *
              Real.sqrt
                (g.gradientInner (e.symm z)
                  ((Z n).weakGradient (e.symm z))
                  ((Z n).weakGradient (e.symm z))) := by
          simpa [Dseq, ManifoldDifferentialField.chartPullback_apply,
            ManifoldDifferentialField.evalChart,
            SurfaceCotangentField.ofCoordinateField,
            surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
              g (e.symm z) ((Z n).weakGradient (e.symm z))] using h_eval
        _ = (Ceval : ℝ) * ‖Spull n z‖ := by
          simp [Spull, Sseq, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _)]
    exact MemLp.of_le_mul (hSpull_mem_B n) hD_aestr hpoint
  have hD_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (Dseq n) 2
          (MeasureTheory.volume.restrict B))
        Filter.atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ,
        eLpNorm (Dseq n) 2 (MeasureTheory.volume.restrict B) ≤
          ENNReal.ofReal (Ceval : ℝ) *
            eLpNorm (Spull n) 2 (MeasureTheory.volume.restrict B) := by
      intro n
      have hpoint :
          ∀ᵐ z ∂MeasureTheory.volume.restrict B,
            ‖Dseq n z‖ ≤ (Ceval : ℝ) * ‖Spull n z‖ := by
        filter_upwards [ae_restrict_mem hB_meas] with z hzB
        have hzK : z ∈ Kcoord := hB_Kcoord hzB
        have h_eval :=
          hCeval z hzK
            ((SurfaceCotangentField.ofCoordinateField (Z n).weakGradient) (e.symm z))
        have hnonneg :
            0 ≤
              g.gradientInner (e.symm z)
                ((Z n).weakGradient (e.symm z))
                ((Z n).weakGradient (e.symm z)) :=
          BackgroundSurfaceMetricOnSurface.gradientInner_nonneg
            g (e.symm z) ((Z n).weakGradient (e.symm z))
        calc
          ‖Dseq n z‖ ≤
              (Ceval : ℝ) *
                Real.sqrt
                  (g.gradientInner (e.symm z)
                    ((Z n).weakGradient (e.symm z))
                    ((Z n).weakGradient (e.symm z))) := by
            simpa [Dseq, ManifoldDifferentialField.chartPullback_apply,
              ManifoldDifferentialField.evalChart,
              SurfaceCotangentField.ofCoordinateField,
              surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
                g (e.symm z) ((Z n).weakGradient (e.symm z))] using h_eval
          _ = (Ceval : ℝ) * ‖Spull n z‖ := by
            simp [Spull, Sseq, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
      exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint 2
    have hCeval_ne_top : ENNReal.ofReal (Ceval : ℝ) ≠ ⊤ := by
      simp
    have hupper :
        Filter.Tendsto
          (fun n : ℕ ↦
            ENNReal.ofReal (Ceval : ℝ) *
              eLpNorm (Spull n) 2 (MeasureTheory.volume.restrict B))
          Filter.atTop (𝓝 0) :=
      by
        simpa using
          ENNReal.Tendsto.const_mul hSpull_tendsto_B (Or.inr hCeval_ne_top)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper
        (fun _n ↦ zero_le)
        hbound
  refine ⟨?_, ?_⟩
  · intro n
    simpa [Dseq, e, B] using hD_mem n
  · simpa [Dseq, e, B] using hD_tendsto

/--
%%handwave
name:
  Vanishing \(L^2\)-norm of pulled-back weak gradients on a chart ball
statement:
  Under vanishing Dirichlet energy, the full operator-valued chart pullbacks
  \(e^*dZ_n\) belong to \(L^2\) on every protected chart ball and converge to
  zero in that \(L^2\)-norm.
proof:
  Evaluate the operators on a finite basis of \(\mathbb C\). Each component
  tends to zero by [the fixed-direction chart estimate](lean:chartBall_chartPullback_weakGradient_eval_memLp_tendsto_zero), and finite-dimensional basis evaluation reconstructs the operator norm.
-/
private theorem chartBall_chartPullback_weakGradient_memLp_tendsto_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel 1 X]
    [SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0))
    (c : X) {r R : ℝ} (hr_pos : 0 < r) (hrR : r < R)
    (hclosed_target :
      Metric.closedBall ((chartAt ℂ c) c) R ⊆ (chartAt ℂ c).target) :
    (∀ n : ℕ,
      MemLp
        (ManifoldDifferentialField.chartPullback
          (I := SurfaceRealModel)
          (SurfaceCotangentField.ofCoordinateField (Z n).weakGradient)
          (chartAt ℂ c))
        2
        (MeasureTheory.volume.restrict
          (Metric.ball ((chartAt ℂ c) c) r))) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (ManifoldDifferentialField.chartPullback
              (I := SurfaceRealModel)
              (SurfaceCotangentField.ofCoordinateField (Z n).weakGradient)
              (chartAt ℂ c))
            2
            (MeasureTheory.volume.restrict
              (Metric.ball ((chartAt ℂ c) c) r)))
        Filter.atTop (𝓝 0) := by
  classical
  let Fseq : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n ↦
    ManifoldDifferentialField.chartPullback
      (I := SurfaceRealModel)
      (SurfaceCotangentField.ofCoordinateField (Z n).weakGradient)
      (chartAt ℂ c)
  have h_eval_mem : ∀ (n : ℕ) (i : Fin (Module.finrank ℝ ℂ)),
      MemLp (fun z : ℂ ↦ Fseq n z (Module.finBasis ℝ ℂ i)) 2
        (MeasureTheory.volume.restrict
          (Metric.ball ((chartAt ℂ c) c) r)) := by
    intro n i
    exact
      (chartBall_chartPullback_weakGradient_eval_memLp_tendsto_zero
        (g := g) Z hZ_int hZ_energy c hr_pos hrR hclosed_target
        (Module.finBasis ℝ ℂ i)).1 n
  have h_eval_tendsto : ∀ i : Fin (Module.finrank ℝ ℂ),
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : ℂ ↦ Fseq n z (Module.finBasis ℝ ℂ i)) 2
            (MeasureTheory.volume.restrict
              (Metric.ball ((chartAt ℂ c) c) r)))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    intro i
    exact
      (chartBall_chartPullback_weakGradient_eval_memLp_tendsto_zero
        (g := g) Z hZ_int hZ_energy c hr_pos hrR hclosed_target
        (Module.finBasis ℝ ℂ i)).2
  rcases
    continuousLinearMap_sequence_memLp_and_eLpNorm_tendsto_zero_of_basis_eval
      (μ := MeasureTheory.volume.restrict
        (Metric.ball ((chartAt ℂ c) c) r))
      (Fseq := Fseq) h_eval_mem h_eval_tendsto with
    ⟨hmem, htendsto⟩
  refine ⟨?_, ?_⟩
  · intro n
    simpa [Fseq] using hmem n
  · simpa [Fseq] using htendsto

/--
%%handwave
name:
  Vanishing local square estimates give vanishing \(L^2\)-seminorms
statement:
  If \(v_n\in L^2(K)\) and the integrals \(\int_K |v_n|^2\) are bounded by
  real numbers tending to \(0\), then the \(L^2(K)\)-seminorms of \(v_n\)
  tend to \(0\).
proof:
  The \(L^2\)-seminorm is the square root of the corresponding extended
  nonnegative integral.  The real square-integral bound transfers to an
  extended-real bound, and the squeeze theorem gives convergence to zero.
-/
private theorem eLpNorm_two_tendsto_zero_of_surfaceLocalL2SeminormSq_le
    {X : Type} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    (v : ℕ → X → ℝ) (B : ℕ → ℝ)
    (hmem : ∀ n : ℕ, MemLp (v n) 2 (μ.restrict K))
    (hle : ∀ n : ℕ, surfaceLocalL2SeminormSq μ K (v n) ≤ B n)
    (hB_tendsto : Filter.Tendsto B Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦ eLpNorm (v n) 2 (μ.restrict K))
      Filter.atTop (𝓝 0) := by
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hq_pos : 0 < q := by
    norm_num [q]
  have hnorm_le :
      ∀ n : ℕ,
        eLpNorm (v n) 2 (μ.restrict K) ≤
          ENNReal.ofReal (B n) ^ q := by
    intro n
    have hsq :
        ∫ x, ‖v n x‖ ^ 2 ∂(μ.restrict K) ≤ B n := by
      simpa [surfaceLocalL2SeminormSq, Real.norm_eq_abs, sq_abs] using hle n
    simpa [q] using
      eLpNorm_two_le_of_integral_sq_le (μ := μ.restrict K)
        (f := v n) (C := B n) (hmem n) hsq
  have hupper :
      Filter.Tendsto (fun n : ℕ ↦ ENNReal.ofReal (B n) ^ q)
        Filter.atTop (𝓝 0) := by
    have hofReal :
        Filter.Tendsto (fun n : ℕ ↦ ENNReal.ofReal (B n))
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa using ENNReal.tendsto_ofReal hB_tendsto
    simpa [ENNReal.zero_rpow_of_pos hq_pos] using
      (Filter.Tendsto.ennrpow_const q hofReal)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper
      (fun _ ↦ zero_le)
      hnorm_le

/--
%%handwave
name:
  Local Poincare gives vanishing \(L^2\) distance to moving constants
statement:
  Under a local Poincare inequality modulo constants, if the local gradient
  energy of a Sobolev sequence tends to zero on the controlling region, then
  along every subsequence there are constants whose \(L^2\)-errors on the
  compact set tend to zero.
proof:
  Apply Poincare to each selected term to choose a constant.  The squared
  \(L^2\)-error is bounded by the Poincare constant times the local gradient
  energy, which tends to zero along the selected subsequence.  Convert this
  squared estimate to convergence of the \(L^2\)-seminorm.
-/
private theorem local_poincare_moving_constants_eLpNorm_tendsto_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {K U : Set X} (hK_compact : IsCompact K)
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hgrad_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ surfaceLocalGradientSeminormSq g U (Z n).weakGradient)
        Filter.atTop (𝓝 0))
    (hlocal :
      ∀ n : ℕ, IsLocalSobolevH1OnSurface g.volume U
        (fun x : X ↦ Z n x) (Z n).weakGradient)
    (hpoincare :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ),
          IsLocalSobolevH1OnSurface g.volume U u du →
            ∃ a : ℝ,
              surfaceLocalL2SeminormSq g.volume K (fun x ↦ u x - a) ≤
                C * surfaceLocalGradientSeminormSq g U du) :
    ∀ η : ℕ → ℕ, StrictMono η →
      ∃ a : ℕ → ℝ,
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ Z (η n) x - a n) 2
              (g.volume.restrict K))
          Filter.atTop (𝓝 0) := by
  intro η hη
  rcases hpoincare with ⟨C, _hC_nonneg, hP⟩
  have hchoose : ∀ n : ℕ, ∃ a : ℝ,
      surfaceLocalL2SeminormSq g.volume K (fun x : X ↦ Z (η n) x - a) ≤
        C * surfaceLocalGradientSeminormSq g U (Z (η n)).weakGradient := by
    intro n
    exact hP (fun x : X ↦ Z (η n) x) (Z (η n)).weakGradient (hlocal (η n))
  choose a ha using hchoose
  refine ⟨a, ?_⟩
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  let μK : Measure X := g.volume.restrict K
  haveI : IsFiniteMeasure μK := isFiniteMeasure_restrict.2 hK_compact.measure_ne_top
  let v : ℕ → X → ℝ := fun n x ↦ Z (η n) x - a n
  let B : ℕ → ℝ :=
    fun n ↦ C * surfaceLocalGradientSeminormSq g U (Z (η n)).weakGradient
  have hmem : ∀ n : ℕ, MemLp (v n) 2 (g.volume.restrict K) := by
    intro n
    have hZ_mem : MemLp (fun x : X ↦ Z (η n) x) 2 (g.volume.restrict K) :=
      (Z (η n)).memLp_toFun.mono_measure Measure.restrict_le_self
    have hconst_mem : MemLp (fun _x : X ↦ a n) 2 (g.volume.restrict K) := by
      simpa [μK] using (memLp_const (a n) :
        MemLp (fun _x : X ↦ a n) 2 μK)
    simpa [v] using hZ_mem.sub hconst_mem
  have hle : ∀ n : ℕ, surfaceLocalL2SeminormSq g.volume K (v n) ≤ B n := by
    intro n
    simpa [v, B] using ha n
  have hB_tendsto : Filter.Tendsto B Filter.atTop (𝓝 0) := by
    have hgradη :
        Filter.Tendsto
          (fun n : ℕ ↦ surfaceLocalGradientSeminormSq g U (Z (η n)).weakGradient)
          Filter.atTop (𝓝 0) :=
      hgrad_tendsto.comp hη.tendsto_atTop
    simpa [B] using tendsto_const_nhds.mul hgradη
  simpa [v] using
    eLpNorm_two_tendsto_zero_of_surfaceLocalL2SeminormSq_le
      (μ := g.volume) (K := K) v B hmem hle hB_tendsto

/--
%%handwave
name:
  Positive area anchors moving constants
statement:
  On a finite positive-measure set, suppose \(u_n\) has uniformly bounded
  \(L^2\)-mass and \(u_n-b_n\to0\) in \(L^2\) for some real constants
  \(b_n\).  Then a subsequence of \(u_n\) converges in \(L^2\) to one
  constant.
proof:
  The \(L^2\)-bound on \(u_n\) and the convergence of \(u_n-b_n\) imply that
  the constant functions \(b_n\) have bounded \(L^2\)-norm on the positive
  finite-measure set.  Hence the real sequence \(b_n\) is bounded.  Extract a
  convergent subsequence \(b_{n_j}\to b\), and use the triangle inequality to
  combine \(u_{n_j}-b_{n_j}\to0\) with \(b_{n_j}\to b\).
-/
private theorem positive_measure_moving_constants_extract_constant_subsequence
    {X : Type} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    (hK_pos : 0 < μ K) (hK_ne_top : μ K ≠ (∞ : ℝ≥0∞))
    (u : ℕ → X → ℝ) (b : ℕ → ℝ)
    (hmem : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K))
    (hvalue_bound : ∀ n : ℕ, ∫ x in K, (u n x) ^ (2 : ℕ) ∂μ ≤ 1)
    (hb :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun x : X ↦ u n x - b n) 2
          (μ.restrict K))
        Filter.atTop (𝓝 0)) :
    ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun x : X ↦ u (ψ n) x - a) 2
          (μ.restrict K))
        Filter.atTop (𝓝 0) := by
  classical
  let μK : Measure X := μ.restrict K
  haveI : IsFiniteMeasure μK := by
    simpa [μK] using (isFiniteMeasure_restrict (μ := μ) (s := K)).2 hK_ne_top
  have hμK_univ_ne_top : μK Set.univ ≠ (∞ : ℝ≥0∞) := by
    simpa [μK] using hK_ne_top
  have hμK_univ_pos : 0 < μK Set.univ := by
    simpa [μK] using hK_pos
  have hμK_univ_ne_zero : μK Set.univ ≠ 0 :=
    ne_of_gt hμK_univ_pos
  have hμK_ne_zero : μK ≠ 0 :=
    (Measure.measure_univ_ne_zero).1 hμK_univ_ne_zero
  let v : ℕ → X → ℝ := fun n x ↦ u n x - b n
  have hv_mem : ∀ n : ℕ, MemLp (v n) 2 μK := by
    intro n
    have hconst : MemLp (fun _x : X ↦ b n) 2 μK := memLp_const (b n)
    simpa [v] using (hmem n).sub hconst
  have hu_norm_le_one : ∀ n : ℕ, eLpNorm (u n) 2 μK ≤ 1 := by
    intro n
    have hint : ∫ x, ‖u n x‖ ^ (2 : ℕ) ∂μK ≤ 1 := by
      simpa [μK, Real.norm_eq_abs, sq_abs] using hvalue_bound n
    simpa using
      eLpNorm_two_le_of_integral_sq_le
        (μ := μK) (f := u n) (C := 1) (hmem n) hint
  have hv_norm_le_one_eventually :
      ∀ᶠ n : ℕ in Filter.atTop, eLpNorm (v n) 2 μK ≤ 1 := by
    have hone_nhds : Set.Iio (1 : ℝ≥0∞) ∈ 𝓝 (0 : ℝ≥0∞) := by
      exact isOpen_Iio.mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num)
    exact (hb.eventually hone_nhds).mono fun n hn ↦ le_of_lt hn
  have hconst_norm_le_two_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (fun _x : X ↦ b n) 2 μK ≤ (2 : ℝ≥0∞) := by
    refine hv_norm_le_one_eventually.mono ?_
    intro n hvn
    have htri :
        eLpNorm (fun x : X ↦ u n x - v n x) 2 μK ≤
          eLpNorm (u n) 2 μK + eLpNorm (v n) 2 μK :=
      eLpNorm_sub_le (hmem n).aestronglyMeasurable
        (hv_mem n).aestronglyMeasurable (by norm_num)
    have hconst_eq :
        eLpNorm (fun _x : X ↦ b n) 2 μK =
          eLpNorm (fun x : X ↦ u n x - v n x) 2 μK := by
      refine eLpNorm_congr_ae ?_
      filter_upwards with x
      simp [v]
    calc
      eLpNorm (fun _x : X ↦ b n) 2 μK
          = eLpNorm (fun x : X ↦ u n x - v n x) 2 μK := hconst_eq
      _ ≤ eLpNorm (u n) 2 μK + eLpNorm (v n) 2 μK := htri
      _ ≤ (1 : ℝ≥0∞) + 1 := add_le_add (hu_norm_le_one n) hvn
      _ = (2 : ℝ≥0∞) := by norm_num
  let m : ℝ := (μ K).toReal
  have hm_pos : 0 < m := by
    exact ENNReal.toReal_pos (ne_of_gt hK_pos) hK_ne_top
  let B : ℝ := Real.sqrt (4 / m)
  have hB_nonneg : 0 ≤ B := Real.sqrt_nonneg _
  have hb_bounded_eventually :
      ∀ᶠ n : ℕ in Filter.atTop, b n ∈ Set.Icc (-B) B := by
    refine hconst_norm_le_two_eventually.mono ?_
    intro n hconst_le
    have hconst_mem : MemLp (fun _x : X ↦ b n) 2 (μ.restrict K) := by
      simpa [μK] using (memLp_const (b n) : MemLp (fun _x : X ↦ b n) 2 μK)
    have hsq_eq :
        (eLpNorm (fun _x : X ↦ b n) 2 (μ.restrict K)).toReal ^ (2 : ℕ) =
          ∫ x in K, (b n) ^ (2 : ℕ) ∂μ :=
      eLpNorm_two_toReal_sq_eq_integral_sq
        (μ := μ) (K := K) (u := fun _x : X ↦ b n) hconst_mem
    have hconst_int_eq :
        ∫ x in K, (b n) ^ (2 : ℕ) ∂μ = m * (b n) ^ (2 : ℕ) := by
      simp [m, measureReal_def, smul_eq_mul, mul_comm]
    have htoReal_le_two :
        (eLpNorm (fun _x : X ↦ b n) 2 (μ.restrict K)).toReal ≤ 2 := by
      have hle : eLpNorm (fun _x : X ↦ b n) 2 (μ.restrict K) ≤
          (2 : ℝ≥0∞) := by
        simpa [μK] using hconst_le
      exact ENNReal.toReal_mono (by norm_num) hle
    have hm_sq_le : m * (b n) ^ (2 : ℕ) ≤ 4 := by
      calc
        m * (b n) ^ (2 : ℕ)
            = ∫ x in K, (b n) ^ (2 : ℕ) ∂μ := hconst_int_eq.symm
        _ = (eLpNorm (fun _x : X ↦ b n) 2 (μ.restrict K)).toReal ^ (2 : ℕ) :=
            hsq_eq.symm
        _ ≤ 4 := by
          have hnorm_nonneg :
              0 ≤ (eLpNorm (fun _x : X ↦ b n) 2
                (μ.restrict K)).toReal :=
            ENNReal.toReal_nonneg
          nlinarith [htoReal_le_two,
            hnorm_nonneg]
    have hb_sq_le : (b n) ^ (2 : ℕ) ≤ 4 / m := by
      rw [le_div_iff₀ hm_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hm_sq_le
    have hb_abs_le : |b n| ≤ B := by
      simpa [B] using Real.abs_le_sqrt hb_sq_le
    exact (abs_le.mp hb_abs_le)
  have hfreq : ∃ᶠ n : ℕ in Filter.atTop, b n ∈ Set.Icc (-B) B :=
    hb_bounded_eventually.frequently
  rcases tendsto_subseq_of_frequently_bounded
      (Metric.isBounded_Icc (-B) B) hfreq with
    ⟨a, _ha, ψ, hψ, hbψ⟩
  refine ⟨a, ψ, hψ, ?_⟩
  have hv_lim :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (v (ψ n)) 2 μK)
        Filter.atTop (𝓝 0) :=
    hb.comp hψ.tendsto_atTop
  have hbψ_zero :
      Filter.Tendsto (fun n : ℕ ↦ b (ψ n) - a) Filter.atTop (𝓝 0) := by
    have hconsta :
        Filter.Tendsto (fun _n : ℕ ↦ a) Filter.atTop (𝓝 a) :=
      tendsto_const_nhds
    simpa [Function.comp_def] using hbψ.sub hconsta
  have hconst_lim :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun _x : X ↦ b (ψ n) - a) 2 μK)
        Filter.atTop (𝓝 0) := by
    have hnorm_zero :
        Filter.Tendsto (fun n : ℕ ↦ ‖b (ψ n) - a‖) Filter.atTop (𝓝 0) :=
      by simpa using hbψ_zero.norm
    have hofReal_zero :
        Filter.Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal ‖b (ψ n) - a‖)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa using ENNReal.tendsto_ofReal hnorm_zero
    let c : ℝ≥0∞ := μK Set.univ ^ (1 / (2 : ℝ))
    have hc_ne_top : c ≠ (∞ : ℝ≥0∞) := by
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num : 0 ≤ (1 / (2 : ℝ)))
        hμK_univ_ne_top
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal ‖b (ψ n) - a‖ * c)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa using
        ENNReal.Tendsto.mul hofReal_zero (Or.inr hc_ne_top)
          tendsto_const_nhds (Or.inr ENNReal.zero_ne_top)
    refine hmul.congr' ?_
    filter_upwards with n
    rw [eLpNorm_const' (μ := μK) (p := (2 : ℝ≥0∞))
      (c := b (ψ n) - a) (by norm_num) ENNReal.coe_ne_top]
    rw [ofReal_norm]
    simp [c, ENNReal.toReal_ofNat]
  have hupper :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (v (ψ n)) 2 μK +
          eLpNorm (fun _x : X ↦ b (ψ n) - a) 2 μK)
        Filter.atTop (𝓝 0) := by
    simpa using hv_lim.add hconst_lim
  have hle :
      (fun n : ℕ ↦
        eLpNorm (fun x : X ↦ u (ψ n) x - a) 2 μK) ≤ᶠ[Filter.atTop]
        (fun n : ℕ ↦ eLpNorm (v (ψ n)) 2 μK +
          eLpNorm (fun _x : X ↦ b (ψ n) - a) 2 μK) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hsum :
        eLpNorm
            (fun x : X ↦ v (ψ n) x + (b (ψ n) - a)) 2 μK ≤
          eLpNorm (v (ψ n)) 2 μK +
            eLpNorm (fun _x : X ↦ b (ψ n) - a) 2 μK :=
      eLpNorm_add_le (hv_mem (ψ n)).aestronglyMeasurable
        (aestronglyMeasurable_const : AEStronglyMeasurable
          (fun _x : X ↦ b (ψ n) - a) μK)
        (by norm_num)
    have hcongr :
        eLpNorm (fun x : X ↦ u (ψ n) x - a) 2 μK =
          eLpNorm (fun x : X ↦ v (ψ n) x + (b (ψ n) - a)) 2 μK := by
      refine eLpNorm_congr_ae ?_
      filter_upwards with x
      simp [v]
    exact hcongr.trans_le hsum
  have hzero :
      Filter.Tendsto (fun _n : ℕ ↦ (0 : ℝ≥0∞))
        Filter.atTop (𝓝 0) :=
    tendsto_const_nhds
  have hnonneg :
      (fun _n : ℕ ↦ (0 : ℝ≥0∞)) ≤ᶠ[Filter.atTop]
        (fun n : ℕ ↦ eLpNorm (fun x : X ↦ u (ψ n) x - a) 2 μK) :=
    Filter.Eventually.of_forall fun n ↦ zero_le
  simpa [μK] using
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero hupper hnonneg hle

/--
%%handwave
name:
  Local Poincare and a positive-area anchor give constant subsequences
statement:
  Let \(K\) have positive area.  Suppose \(u_n\) has uniformly bounded
  \(L^2(K)\)-mass and the local Poincare distance of \(u_n\) to constants
  tends to zero.  Then every subsequence has a further subsequence converging
  in \(L^2(K)\) to one constant.
proof:
  Choose almost-minimizing constants \(a_n\).  The \(L^2(K)\)-bound on
  \(u_n\), the fact that \(u_n-a_n\to0\), and the positive area of \(K\)
  make the real sequence \(a_n\) bounded.  Bolzano-Weierstrass gives a
  convergent subsequence \(a_{n_j}\to a\).  The triangle inequality then
  gives \(u_{n_j}\to a\) in \(L^2(K)\).
-/
private theorem positive_compact_piece_constant_subsequence_of_local_poincare_mod_constants
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {K U : Set X}
    (_hK_compact : IsCompact K) (_hK_pos : 0 < g.volume K)
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hvalue_bound : ∀ n : ℕ, greenLocalL2SeminormSq g K (Z n) ≤ 1)
    (hgrad_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ surfaceLocalGradientSeminormSq g U (Z n).weakGradient)
        Filter.atTop (𝓝 0))
    (hlocal :
      ∀ n : ℕ, IsLocalSobolevH1OnSurface g.volume U
        (fun x : X ↦ Z n x) (Z n).weakGradient)
    (hpoincare :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ),
          IsLocalSobolevH1OnSurface g.volume U u du →
            ∃ a : ℝ,
              surfaceLocalL2SeminormSq g.volume K (fun x ↦ u x - a) ≤
                C * surfaceLocalGradientSeminormSq g U du) :
    ∀ η : ℕ → ℕ, StrictMono η →
      ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ Z (η (ψ n)) x - a) 2
              (g.volume.restrict K))
          Filter.atTop (𝓝 0) := by
  intro η hη
  rcases
    local_poincare_moving_constants_eLpNorm_tendsto_zero
      (g := g) (K := K) (U := U) _hK_compact
      Z hgrad_tendsto hlocal hpoincare η hη with
    ⟨b, hb⟩
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  have hK_ne_top : g.volume K ≠ (∞ : ℝ≥0∞) :=
    _hK_compact.measure_ne_top
  have hmem : ∀ n : ℕ,
      MemLp (fun x : X ↦ Z (η n) x) 2 (g.volume.restrict K) := by
    intro n
    exact (Z (η n)).memLp_toFun.mono_measure Measure.restrict_le_self
  have hvalue_boundη :
      ∀ n : ℕ, ∫ x in K, (Z (η n) x) ^ (2 : ℕ) ∂g.volume ≤ 1 := by
    intro n
    simpa [greenLocalL2SeminormSq] using hvalue_bound (η n)
  rcases
    positive_measure_moving_constants_extract_constant_subsequence
      (μ := g.volume) (K := K) _hK_pos hK_ne_top
      (fun n : ℕ ↦ fun x : X ↦ Z (η n) x) b
      hmem hvalue_boundη hb with
    ⟨a, ψ, hψ, hlim⟩
  exact ⟨a, ψ, hψ, hlim⟩

/--
%%handwave
name:
  Rellich data give compact constant subsequences
statement:
  Let \(K\subset\operatorname{int}P\subset P\subset
  \operatorname{int}Q\subset Q\subset U\), where \(K,P,Q\) are compact,
  \(U\) is open, and \(\operatorname{int}P\) is preconnected.  If a sequence
  is locally Sobolev on \(U\), uniformly \(W^{1,2}\)-bounded on \(Q\), and
  its differential energy on \(Q\) tends to zero, then every subsequence has a
  further subsequence converging in \(L^2(K)\) to a constant.
proof:
  Apply the manifold Rellich extraction theorem to the chosen subsequence.
  The uniform bound is inherited by subsequences, and the vanishing
  differential energy is preserved by composition with a strictly increasing
  index map.
-/
private theorem compact_control_constant_subsequence_of_local_rellich_data
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [SecondCountableTopology (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [TopologicalSpace.PseudoMetrizableSpace
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K P Q U : Set X} (hK_compact : IsCompact K) (hKP : K ⊆ interior P)
    (hP_compact : IsCompact P) (hPQ : P ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ_compact : IsCompact Q)
    (hU_open : IsOpen U) (hP_preconnected : IsPreconnected (interior P))
    (u : ℕ → X → ℝ) (du : ℕ → ManifoldDifferentialField I X ℝ)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded :
      BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hgrad_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ manifoldLocalDifferentialSeminormSq I g μ Q (du n))
        Filter.atTop (𝓝 0)) :
    ∀ η : ℕ → ℕ, StrictMono η →
      ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ u (η (ψ n)) x - a) 2
              (μ.restrict K))
          Filter.atTop (𝓝 0) := by
  intro η hη
  have hlocalη : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U
        (fun x : X ↦ u (η n) x) (du (η n)) := by
    intro n
    exact hlocal (η n)
  have hboundedη :
      BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q
        (fun n : ℕ ↦ fun x : X ↦ u (η n) x)
        (fun n : ℕ ↦ du (η n)) := by
    rcases hbounded with ⟨C, hC⟩
    exact ⟨C, fun n : ℕ ↦ hC (η n)⟩
  have hgrad_tendstoη :
      Filter.Tendsto
        (fun n : ℕ ↦
          manifoldLocalDifferentialSeminormSq I g μ Q (du (η n)))
        Filter.atTop (𝓝 0) :=
    hgrad_tendsto.comp hη.tendsto_atTop
  rcases
    localRellich_zeroGradient_subsequence_constant_on_preconnected_interior
      (I := I) (g := g) (μ := μ) (K := K) (P := P) (Q := Q) (U := U) hμ
      hK_compact hKP hP_compact hPQ hQU hQ_compact hU_open
      hP_preconnected
      (fun n : ℕ ↦ fun x : X ↦ u (η n) x)
      (fun n : ℕ ↦ du (η n)) hlocalη hboundedη hgrad_tendstoη with
    ⟨a, ψ, hψ, hlim⟩
  refine ⟨a, ψ, hψ, ?_⟩
  simpa [TendstoInLocalL2OnManifoldWithValues] using hlim

/--
%%handwave
name:
  Compact control neighborhoods have constant Rellich subsequences
statement:
  Let \(K\subset\operatorname{int}P\subset P\subset
  \operatorname{int}Q\subset Q\subset U\), where \(K,P,Q\) are compact,
  \(U\) is open, and \(\operatorname{int}P\) is preconnected.  This is the
  compact-control extraction step needed for a zero-trace sequence with
  vanishing Dirichlet energy.
proof:
  Once the restrictions are known to be locally Sobolev on \(U\), uniformly
  \(W^{1,2}\)-bounded on \(Q\), and to have differential energy tending to
  zero on \(Q\), the extraction is an immediate subsequence application of
  [local Rellich compactness with vanishing gradients gives constant limits](lean:JJMath.Uniformization.localRellich_zeroGradient_subsequence_constant).
  The remaining point is to supply the uniform compact value bound; it is not
  a consequence of Dirichlet energy convergence alone.
-/
private theorem compact_control_constant_subsequence_of_zero_trace_energy_tendsto
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel 1 X]
    [hDiffSC : SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    [hDiffPseudo : TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {K P Q U : Set X} (hK_compact : IsCompact K) (hKP : K ⊆ interior P)
    (hP_compact : IsCompact P) (hP_preconnected : IsPreconnected (interior P))
    (hPQ : P ⊆ interior Q) (hQU : Q ⊆ U) (hQ_compact : IsCompact Q)
    (hU_open : IsOpen U)
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (_hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0))
    (du : ℕ → ManifoldDifferentialField SurfaceRealModel X ℝ)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues
        (I := SurfaceRealModel) g.metric.toManifoldMetric g.volume U
        (fun x : X ↦ Z n x) (du n))
    (hbounded :
      BoundedInLocalSobolevH1OnManifoldWithValues
        (I := SurfaceRealModel) g.metric.toManifoldMetric g.volume Q
        (fun n : ℕ ↦ fun x : X ↦ Z n x) du)
    (hgrad_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          manifoldLocalDifferentialSeminormSq SurfaceRealModel
            g.metric.toManifoldMetric g.volume Q (du n))
        Filter.atTop (𝓝 0)) :
    ∀ η : ℕ → ℕ, StrictMono η →
      ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ Z (η (ψ n)) x - a) 2
              (g.volume.restrict K))
          Filter.atTop (𝓝 0) := by
  letI : SecondCountableTopology
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ)) :=
    surface_value_totalSpace_secondCountable (X := X)
  letI : TopologicalSpace.PseudoMetrizableSpace
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ)) :=
    surface_value_totalSpace_pseudoMetrizable (X := X)
  letI : SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) := hDiffSC
  letI : TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) := hDiffPseudo
  let hμ : SmoothPositiveMeasureOnManifold (I := SurfaceRealModel) g.volume :=
    { finite_on_compact :=
        (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).finite_on_compact
      chart_density :=
        (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).chart_density }
  exact
    compact_control_constant_subsequence_of_local_rellich_data
      (H := ℂ) (X := X) (I := SurfaceRealModel)
      (g := g.metric.toManifoldMetric) (μ := g.volume)
      hμ hK_compact hKP hP_compact hPQ hQU hQ_compact hU_open
      hP_preconnected
      (fun n : ℕ ↦ fun x : X ↦ Z n x) du hlocal hbounded hgrad_tendsto

/--
%%handwave
name:
  Compact pieces in preconnected neighborhoods have constant Rellich subsequences
statement:
  Let \(K_i\) be one compact member of a finite cover, and suppose \(K_i\)
  lies in an open preconnected coordinate neighborhood.  Suppose moreover
  that each piece has a compact control neighborhood on which the sequence is
  uniformly locally \(W^{1,2}\)-bounded and its differential energy tends to
  zero.  Then every subsequence has a further subsequence converging in
  \(L^2(K_i)\) to a single constant.
proof:
  For the selected piece, unpack its compact control neighborhood and
  intrinsic Sobolev control data.  Apply the compact-control extraction step
  on that neighborhood.
-/
private theorem compact_preconnected_piece_constant_subsequence_of_zero_trace_energy_tendsto
    {X ι : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel 1 X]
    [SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (Kc Uc : ι → Set X)
    (hKc_compact : ∀ i : ι, IsCompact (Kc i))
    (_hKcU : ∀ i : ι, Kc i ⊆ Uc i)
    (hUc_open : ∀ i : ι, IsOpen (Uc i))
    (_hUc_preconnected : ∀ i : ι, IsPreconnected (Uc i))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0))
    (hcontrol :
      ∀ i : ι,
        ∃ (P Q : Set X), IsCompact P ∧ Kc i ⊆ interior P ∧
          IsPreconnected (interior P) ∧ P ⊆ interior Q ∧ Q ⊆ Uc i ∧
          IsCompact Q ∧
          ∃ du : ℕ → ManifoldDifferentialField SurfaceRealModel X ℝ,
            (∀ n : ℕ,
              IsLocalSobolevH1OnManifoldWithValues
                (I := SurfaceRealModel) g.metric.toManifoldMetric g.volume (Uc i)
                (fun x : X ↦ Z n x) (du n)) ∧
              BoundedInLocalSobolevH1OnManifoldWithValues
                (I := SurfaceRealModel) g.metric.toManifoldMetric g.volume Q
                (fun n : ℕ ↦ fun x : X ↦ Z n x) du ∧
              Filter.Tendsto
                (fun n : ℕ ↦
                  manifoldLocalDifferentialSeminormSq SurfaceRealModel
                    g.metric.toManifoldMetric g.volume Q (du n))
                Filter.atTop (𝓝 0)) :
    ∀ i : ι, ∀ η : ℕ → ℕ, StrictMono η →
      ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ Z (η (ψ n)) x - a) 2
              (g.volume.restrict (Kc i)))
          Filter.atTop (𝓝 0) := by
  intro i
  rcases hcontrol i with
    ⟨P, Q, hP_compact, hKcP, hP_preconnected, hPQ, hQU, hQ_compact,
      du, hlocal, hbounded, hgrad_tendsto⟩
  exact
    compact_control_constant_subsequence_of_zero_trace_energy_tendsto
      (g := g) (K := Kc i) (P := P) (Q := Q) (U := Uc i)
      (hKc_compact i) hKcP hP_compact hP_preconnected hPQ hQU hQ_compact
      (hUc_open i) Z hZ_energy
      du hlocal hbounded hgrad_tendsto

/--
%%handwave
name:
  Controlled finite compact covers have constant Rellich extraction
statement:
  Suppose a finite compact cover of \(\overline Q\) is subordinate to
  preconnected open sets, and suppose each piece has compact control collars
  on which the zero-trace Sobolev sequence is uniformly \(W^{1,2}\)-bounded
  and has differential energy tending to zero.  Then each cover element has
  the constant \(L^2\)-subsequence extraction property.
proof:
  Apply the compact-control Rellich extraction theorem separately on each
  finite cover element.
-/
private theorem finite_compact_rellich_cover_on_closure_of_relcompact_open_of_intrinsic_compact_control
    {X ι : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [Fintype ι] [IsManifold SurfaceRealModel 1 X]
    [SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (Kc Uc : ι → Set X)
    (hKc_compact : ∀ i : ι, IsCompact (Kc i))
    (hKcU : ∀ i : ι, Kc i ⊆ Uc i)
    (hUc_open : ∀ i : ι, IsOpen (Uc i))
    (hUc_preconnected : ∀ i : ι, IsPreconnected (Uc i))
    (hcover : closure Q = ⋃ i : ι, Kc i)
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0))
    (hcontrol :
      ∀ i : ι,
        ∃ (P Qc : Set X), IsCompact P ∧ Kc i ⊆ interior P ∧
          IsPreconnected (interior P) ∧ P ⊆ interior Qc ∧ Qc ⊆ Uc i ∧
          IsCompact Qc ∧
          ∃ du : ℕ → ManifoldDifferentialField SurfaceRealModel X ℝ,
            (∀ n : ℕ,
              IsLocalSobolevH1OnManifoldWithValues
                (I := SurfaceRealModel) g.metric.toManifoldMetric g.volume (Uc i)
                (fun x : X ↦ Z n x) (du n)) ∧
              BoundedInLocalSobolevH1OnManifoldWithValues
                (I := SurfaceRealModel) g.metric.toManifoldMetric g.volume Qc
                (fun n : ℕ ↦ fun x : X ↦ Z n x) du ∧
              Filter.Tendsto
                (fun n : ℕ ↦
                  manifoldLocalDifferentialSeminormSq SurfaceRealModel
                    g.metric.toManifoldMetric g.volume Qc (du n))
                Filter.atTop (𝓝 0)) :
    ∃ (ι' : Type) (_ : Fintype ι') (Kc' : ι' → Set X),
      (∀ i : ι', IsCompact (Kc' i)) ∧
        closure Q = ⋃ i : ι', Kc' i ∧
        ∀ i : ι', ∀ η : ℕ → ℕ, StrictMono η →
          ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            Filter.Tendsto
              (fun n : ℕ ↦
                eLpNorm (fun x : X ↦ Z (η (ψ n)) x - a) 2
                  (g.volume.restrict (Kc' i)))
              Filter.atTop (𝓝 0) := by
  refine ⟨ι, inferInstance, Kc, hKc_compact, hcover, ?_⟩
  exact
    compact_preconnected_piece_constant_subsequence_of_zero_trace_energy_tendsto
      (g := g) Kc Uc hKc_compact hKcU hUc_open hUc_preconnected
      Z hZ_energy hcontrol

/--
%%handwave
name:
  Compact closure has a finite cover by preconnected coordinate neighborhoods
statement:
  The compact closure \(\overline Q\) of an open subset of a Riemann surface
  is a finite union of compact sets \(K_i\), each contained in an open
  preconnected coordinate neighborhood \(U_i\).
proof:
  Around each point of \(\overline Q\), choose a coordinate chart and a small
  coordinate ball whose closed ball is still contained in the chart target.
  Pull the closed balls and open balls back to the surface.  Compactness of
  \(\overline Q\) gives a finite subcover, and the standard compact
  shrinking lemma gives compact pieces subordinate to the chosen open balls.
-/
private theorem exists_finite_compact_preconnected_cover_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {Q : Set X} (hQ_compact : IsCompact (closure Q)) :
    ∃ (ι : Type) (_ : Fintype ι) (Kc Uc : ι → Set X),
      (∀ i : ι, IsCompact (Kc i)) ∧
        (∀ i : ι, Kc i ⊆ Uc i) ∧
        (∀ i : ι, IsOpen (Uc i)) ∧
        (∀ i : ι, IsPreconnected (Uc i)) ∧
        closure Q = ⋃ i : ι, Kc i := by
  classical
  have hball_exists :
      ∀ x : X, ∃ r : ℝ, 0 < r ∧
        Metric.ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target := by
    intro x
    have hx_target : (chartAt ℂ x) x ∈ (chartAt ℂ x).target := by
      simp
    rcases Metric.isOpen_iff.mp (chartAt ℂ x).open_target
        ((chartAt ℂ x) x) hx_target with
      ⟨r, hr_pos, hball_subset⟩
    exact ⟨r, hr_pos, hball_subset⟩
  choose r hr_pos hball_subset using hball_exists
  let U : X → Set X :=
    fun x : X ↦
      (chartAt ℂ x).source ∩
        (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) (r x)
  have hU_open : ∀ x : X, IsOpen (U x) := by
    intro x
    exact (chartAt ℂ x).isOpen_inter_preimage Metric.isOpen_ball
  have hU_preconnected : ∀ x : X, IsPreconnected (U x) := by
    intro x
    have himage :
        (chartAt ℂ x).symm ''
            Metric.ball ((chartAt ℂ x) x) (r x) =
          U x := by
      simpa [U] using
        (chartAt ℂ x).symm_image_eq_source_inter_preimage
          (hball_subset x)
    have hpre_image :
        IsPreconnected
          ((chartAt ℂ x).symm ''
            Metric.ball ((chartAt ℂ x) x) (r x)) :=
      Metric.isPreconnected_ball.image (chartAt ℂ x).symm
        ((chartAt ℂ x).continuousOn_symm.mono (hball_subset x))
    simpa [← himage] using hpre_image
  have hcover_open : closure Q ⊆ ⋃ x : X, U x := by
    intro x _hx
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    have hx_source : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hx_ball :
        (chartAt ℂ x) x ∈ Metric.ball ((chartAt ℂ x) x) (r x) :=
      Metric.mem_ball_self (hr_pos x)
    exact ⟨hx_source, hx_ball⟩
  rcases hQ_compact.elim_finite_subcover U hU_open hcover_open with
    ⟨t, ht⟩
  rcases hQ_compact.finite_compact_cover t U
      (fun i _hi ↦ hU_open i) ht with
    ⟨Kpiece, hKpiece_compact, hKpiece_sub, hK_eq⟩
  let ι : Type := {x : X // x ∈ t}
  letI : Fintype ι := by
    dsimp [ι]
    infer_instance
  refine
    ⟨ι, inferInstance, (fun i : ι ↦ Kpiece i.1), (fun i : ι ↦ U i.1),
      ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hKpiece_compact i.1
  · intro i
    exact hKpiece_sub i.1
  · intro i
    exact hU_open i.1
  · intro i
    exact hU_preconnected i.1
  · rw [hK_eq]
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨y, hy⟩
      rw [Set.mem_iUnion] at hy
      rcases hy with ⟨hyt, hxy⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨y, hyt⟩, hxy⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hxi⟩
      rw [Set.mem_iUnion]
      refine ⟨(i : X), ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨i.2, hxi⟩

/--
%%handwave
name:
  Finite compact cover by protected chart balls
statement:
  If \(\overline Q\) is compact in a Riemann surface, it has a finite compact
  cover \(K_i\), with chart centers \(c_i\) and radii
  \(0<r_i<R_i\), such that \(K_i\) lies over the inner ball
  \(B(e_i(c_i),r_i)\) and the closed outer ball of radius \(R_i\) lies in the
  chart target.
proof:
  Around each point choose a protected outer chart ball and a smaller inner
  ball. Compactness gives a finite subcover; compactly shrink that subcover
  inside the inner chart neighborhoods.
-/
private theorem exists_finite_compact_chart_ball_cover_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {Q : Set X} (hQ_compact : IsCompact (closure Q)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (Kc : ι → Set X) (cc : ι → X) (r R : ι → ℝ),
      (∀ i : ι, IsCompact (Kc i)) ∧
        closure Q = ⋃ i : ι, Kc i ∧
        (∀ i : ι, 0 < r i) ∧
        (∀ i : ι, r i < R i) ∧
        (∀ i : ι,
          Metric.closedBall ((chartAt ℂ (cc i)) (cc i)) (R i) ⊆
            (chartAt ℂ (cc i)).target) ∧
        (∀ i : ι,
          Kc i ⊆
            (chartAt ℂ (cc i)).source ∩
              (chartAt ℂ (cc i)) ⁻¹'
                Metric.ball ((chartAt ℂ (cc i)) (cc i)) (r i)) := by
  classical
  have hclosedBall_exists :
      ∀ x : X, ∃ R : ℝ, 0 < R ∧
        Metric.closedBall ((chartAt ℂ x) x) R ⊆ (chartAt ℂ x).target := by
    intro x
    have hx_target : (chartAt ℂ x) x ∈ (chartAt ℂ x).target := by
      simp
    rcases Metric.isOpen_iff.mp (chartAt ℂ x).open_target
        ((chartAt ℂ x) x) hx_target with
      ⟨ρ, hρ_pos, hball_subset⟩
    refine ⟨ρ / 2, by positivity, ?_⟩
    exact (Metric.closedBall_subset_ball (by linarith)).trans hball_subset
  choose R hR_pos hclosedBall_subset using hclosedBall_exists
  let r : X → ℝ := fun x : X ↦ R x / 2
  have hr_pos : ∀ x : X, 0 < r x := by
    intro x
    dsimp [r]
    linarith [hR_pos x]
  have hrR : ∀ x : X, r x < R x := by
    intro x
    dsimp [r]
    linarith [hR_pos x]
  let U : X → Set X :=
    fun x : X ↦
      (chartAt ℂ x).source ∩
        (chartAt ℂ x) ⁻¹'
          Metric.ball ((chartAt ℂ x) x) (r x)
  have hU_open : ∀ x : X, IsOpen (U x) := by
    intro x
    exact (chartAt ℂ x).isOpen_inter_preimage Metric.isOpen_ball
  have hcover_open : closure Q ⊆ ⋃ x : X, U x := by
    intro x _hx
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    have hx_source : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hx_ball :
        (chartAt ℂ x) x ∈
          Metric.ball ((chartAt ℂ x) x) (r x) :=
      Metric.mem_ball_self (hr_pos x)
    exact ⟨hx_source, hx_ball⟩
  rcases hQ_compact.elim_finite_subcover U hU_open hcover_open with
    ⟨t, ht⟩
  rcases hQ_compact.finite_compact_cover t U
      (fun i _hi ↦ hU_open i) ht with
    ⟨Kpiece, hKpiece_compact, hKpiece_sub, hK_eq⟩
  let ι : Type := {x : X // x ∈ t}
  letI : Fintype ι := by
    dsimp [ι]
    infer_instance
  refine
    ⟨ι, inferInstance, (fun i : ι ↦ Kpiece i.1),
      (fun i : ι ↦ i.1), (fun i : ι ↦ r i.1), (fun i : ι ↦ R i.1),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hKpiece_compact i.1
  · rw [hK_eq]
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨y, hy⟩
      rw [Set.mem_iUnion] at hy
      rcases hy with ⟨hyt, hxy⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨y, hyt⟩, hxy⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hxi⟩
      rw [Set.mem_iUnion]
      refine ⟨(i : X), ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨i.2, hxi⟩
  · intro i
    exact hr_pos i.1
  · intro i
    exact hrR i.1
  · intro i
    exact hclosedBall_subset i.1
  · intro i
    exact hKpiece_sub i.1

/--
%%handwave
name:
  Constant subsequence on a positive compact chart-ball piece
statement:
  Let \(K\subset\overline Q\) be compact of positive area and contained in a
  protected chart ball. If \(Z_n\) has unit \(L^2(\overline Q)\)-mass,
  integrable gradient energy, and Dirichlet energy tending to zero, then every
  subsequence has a further subsequence converging in \(L^2(K)\) to a
  constant.
proof:
  In the chart, the pulled-back weak gradients tend to zero in \(L^2\).
  Euclidean Poincaré gives moving constants with vanishing error. Unit mass
  bounds the values, positive area bounds those constants, and Rellich
  compactness yields a further subsequence converging to one constant; transfer
  the norm estimate back to the surface.
-/
private theorem positive_compact_chart_ball_piece_constant_subsequence_of_unit_localL2_and_dirichlet_tendsto_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel 1 X]
    [SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q K : Set X}
    (hK_compact : IsCompact K) (hKQ : K ⊆ closure Q)
    (c : X) {r R : ℝ} (hr_pos : 0 < r) (hrR : r < R)
    (hclosed_target :
      Metric.closedBall ((chartAt ℂ c) c) R ⊆ (chartAt ℂ c).target)
    (hK_chart :
      K ⊆
        (chartAt ℂ c).source ∩
          (chartAt ℂ c) ⁻¹' Metric.ball ((chartAt ℂ c) c) r)
    (hK_pos : 0 < g.volume K)
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∀ η : ℕ → ℕ, StrictMono η →
      ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ Z (η (ψ n)) x - a) 2
              (g.volume.restrict K))
          Filter.atTop (𝓝 0) := by
  classical
  intro η hη
  haveI : ProperSpace ℂ := FiniteDimensional.proper ℝ ℂ
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ c
  let zc : ℂ := e c
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  let B : Set ℂ := Metric.ball zc r
  let Kclosed : Set ℂ := Metric.closedBall zc r
  let KclosedSurf : Set X := e.symm '' Kclosed
  let Kcoord : Set ℂ := e '' K
  let uη : ℕ → ℂ → ℝ := fun n z ↦ Z (η n) (e.symm z)
  let Dη : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n ↦
    ManifoldDifferentialField.chartPullback
      (I := SurfaceRealModel)
      (SurfaceCotangentField.ofCoordinateField (Z (η n)).weakGradient) e
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ c
  have hK_source : K ⊆ e.source := fun x hx ↦ (hK_chart hx).1
  have hKcoord_B : Kcoord ⊆ B := by
    rintro z ⟨x, hxK, rfl⟩
    exact (hK_chart hxK).2
  have hKcoord_compact : IsCompact Kcoord := by
    dsimp [Kcoord]
    exact hK_compact.image_of_continuousOn (e.continuousOn.mono hK_source)
  have hKcoord_meas : MeasurableSet Kcoord := hKcoord_compact.measurableSet
  have hKclosed_target : Kclosed ⊆ e.target := by
    dsimp [Kclosed, zc, e]
    exact (Metric.closedBall_subset_closedBall (x := (chartAt ℂ c) c)
      (le_of_lt hrR)).trans hclosed_target
  have hB_Kclosed : B ⊆ Kclosed := by
    dsimp [B, Kclosed]
    exact Metric.ball_subset_closedBall
  have hBΩ : B ⊆ Ω := by
    intro z hz
    exact ⟨hKclosed_target (hB_Kclosed hz), trivial⟩
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, surfaceChartRegion] using e.open_target
  have hKclosed_compact : IsCompact Kclosed := by
    dsimp [Kclosed]
    exact isCompact_closedBall zc r
  have hKclosedSurf_compact : IsCompact KclosedSurf := by
    dsimp [KclosedSurf]
    exact hKclosed_compact.image_of_continuousOn
      (e.continuousOn_symm.mono hKclosed_target)
  have hKclosedSurf_source : KclosedSurf ⊆ e.source := by
    rintro x ⟨z, hzK, rfl⟩
    exact e.map_target (hKclosed_target hzK)
  have hKclosed_def : Kclosed = e '' KclosedSurf := by
    ext z
    constructor
    · intro hz
      refine ⟨e.symm z, ⟨z, hz, rfl⟩, ?_⟩
      exact e.right_inv (hKclosed_target hz)
    · rintro ⟨x, ⟨w, hwK, rfl⟩, rfl⟩
      simpa [e.right_inv (hKclosed_target hwK)] using hwK
  let hμ : SmoothPositiveMeasureOnManifold (I := SurfaceRealModel) g.volume :=
    { finite_on_compact :=
        (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).finite_on_compact
      chart_density :=
        (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).chart_density }
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  have hvalue_B_mem : ∀ n : ℕ,
      MemLp (uη n) 2 (MeasureTheory.volume.restrict B) := by
    intro n
    have hZ_mem_closedSurf :
        MemLp (fun x : X ↦ Z (η n) x) 2
          (g.volume.restrict KclosedSurf) :=
      (Z (η n)).memLp_toFun.mono_measure Measure.restrict_le_self
    have hclosed :
        MemLp (fun z : ℂ ↦ Z (η n) (e.symm z)) 2
          (MeasureTheory.volume.restrict Kclosed) := by
      simpa [e, Kclosed] using
        smoothPositiveMeasureOnManifold_chartPullback_memLp_on_compact_of_memLp
          (I := SurfaceRealModel) (μ := g.volume) hμ e he
          hKclosedSurf_compact hKclosedSurf_source hKclosed_def
          hZ_mem_closedSurf
    exact hclosed.mono_measure
      (Measure.restrict_mono hB_Kclosed le_rfl)
  rcases
    chartBall_chartPullback_weakGradient_memLp_tendsto_zero
      (g := g) Z hZ_int hZ_energy c hr_pos hrR hclosed_target with
    ⟨hD_mem_raw, hD_tendsto_raw⟩
  have hD_mem : ∀ n : ℕ,
      MemLp (Dη n) 2 (MeasureTheory.volume.restrict B) := by
    intro n
    simpa [Dη, e, B, zc] using hD_mem_raw (η n)
  have hD_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (Dη n) 2
          (MeasureTheory.volume.restrict B))
        Filter.atTop (𝓝 0) := by
    simpa [Dη, e, B, zc] using
      hD_tendsto_raw.comp hη.tendsto_atTop
  rcases complex_euclideanSobolev_poincare_L2_on_ball_self
      (c := zc) (r := r) hr_pos with
    ⟨Cp, hCp_top, hPoincare⟩
  have hchoose : ∀ n : ℕ, ∃ b : ℝ,
      AEStronglyMeasurable
        (fun y : ℂ ↦ uη n y - b)
        (MeasureTheory.volume.restrict B) ∧
      eLpNorm (fun y : ℂ ↦ uη n y - b) 2
          (MeasureTheory.volume.restrict B) ≤
        Cp * eLpNorm (Dη n) 2 (MeasureTheory.volume.restrict B) := by
    intro n
    have hweakΩ :
        IsWeakDerivativeOnEuclideanRegionScalar Ω (uη n) (Dη n) := by
      simpa [Ω, uη, Dη, e] using
        surface_zeroTrace_chartPullback_weakGradient
          (g := g) (Z (η n)) e he
    have hweak :
        IsWeakDerivativeOnEuclideanRegionScalar B (uη n) (Dη n) :=
      IsWeakDerivativeOnEuclideanRegionWithValues.mono_set hweakΩ hBΩ
    exact hPoincare hweak (hvalue_B_mem n) (hD_mem n)
  choose b hb using hchoose
  have hb_B_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : ℂ ↦ uη n y - b n) 2
            (MeasureTheory.volume.restrict B))
        Filter.atTop (𝓝 0) := by
    have hCp_ne_top : Cp ≠ ⊤ := ne_of_lt hCp_top
    have hupper :
        Filter.Tendsto
          (fun n : ℕ ↦
            Cp * eLpNorm (Dη n) 2 (MeasureTheory.volume.restrict B))
          Filter.atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hD_tendsto (Or.inr hCp_ne_top)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper
        (fun _n ↦ zero_le)
        (fun n ↦ (hb n).2)
  have hb_Kcoord_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : ℂ ↦ uη n y - b n) 2
            (MeasureTheory.volume.restrict Kcoord))
        Filter.atTop (𝓝 0) := by
    have hle : ∀ n : ℕ,
        eLpNorm (fun y : ℂ ↦ uη n y - b n) 2
            (MeasureTheory.volume.restrict Kcoord) ≤
          eLpNorm (fun y : ℂ ↦ uη n y - b n) 2
            (MeasureTheory.volume.restrict B) := by
      intro n
      exact eLpNorm_mono_measure (fun y : ℂ ↦ uη n y - b n)
        (Measure.restrict_mono hKcoord_B le_rfl)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hb_B_tendsto
        (fun _n ↦ zero_le)
        hle
  rcases
    chartPullback_eLpNorm_two_sub_const_surface_le
      (H := ℂ) (X := X) (I := SurfaceRealModel) (μ := g.volume)
      hμ c hK_compact hK_source
      (by simp [Kcoord, e] : Kcoord = (chartAt ℂ c) '' K) with
    ⟨Csurf, hCsurf_top, hCsurf⟩
  haveI : IsFiniteMeasure (g.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK_compact.measure_ne_top
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict Kcoord) :=
    isFiniteMeasure_restrict.2 hKcoord_compact.measure_ne_top
  have hsurface_diff_mem : ∀ n : ℕ,
      MemLp (fun x : X ↦ Z (η n) x - b n) 2 (g.volume.restrict K) := by
    intro n
    have hZK : MemLp (fun x : X ↦ Z (η n) x) 2
        (g.volume.restrict K) :=
      (Z (η n)).memLp_toFun.mono_measure Measure.restrict_le_self
    have hconst : MemLp (fun _x : X ↦ b n) 2 (g.volume.restrict K) :=
      memLp_const (b n)
    simpa using hZK.sub hconst
  have hcoord_diff_mem : ∀ n : ℕ,
      MemLp (fun z : ℂ ↦ Z (η n) (e.symm z) - b n) 2
        (MeasureTheory.volume.restrict Kcoord) := by
    intro n
    have hZcoord : MemLp (fun z : ℂ ↦ Z (η n) (e.symm z)) 2
        (MeasureTheory.volume.restrict Kcoord) := by
      simpa [Kcoord, e] using
        smoothPositiveMeasureOnManifold_chartPullback_memLp_on_compact_of_memLp
          (I := SurfaceRealModel) (μ := g.volume) hμ e he
          hK_compact hK_source
          (by simp [Kcoord, e] : Kcoord = e '' K)
          ((Z (η n)).memLp_toFun.mono_measure Measure.restrict_le_self)
    have hconst : MemLp (fun _z : ℂ ↦ b n) 2
        (MeasureTheory.volume.restrict Kcoord) :=
      memLp_const (b n)
    simpa using hZcoord.sub hconst
  have hb_surface_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun x : X ↦ Z (η n) x - b n) 2
            (g.volume.restrict K))
        Filter.atTop (𝓝 0) := by
    have hle : ∀ n : ℕ,
        eLpNorm (fun x : X ↦ Z (η n) x - b n) 2
            (g.volume.restrict K) ≤
          Csurf *
            eLpNorm (fun z : ℂ ↦ Z (η n) ((chartAt ℂ c).symm z) - b n) 2
              (MeasureTheory.volume.restrict Kcoord) := by
      intro n
      exact hCsurf (fun x : X ↦ Z (η n) x) (b n)
        (hsurface_diff_mem n)
        (by simpa [e] using hcoord_diff_mem n)
    have hcoord_tendsto' :
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun z : ℂ ↦ Z (η n) ((chartAt ℂ c).symm z) - b n) 2
              (MeasureTheory.volume.restrict Kcoord))
          Filter.atTop (𝓝 0) := by
      simpa [uη, e] using hb_Kcoord_tendsto
    have hC_ne_top : Csurf ≠ ⊤ := ne_of_lt hCsurf_top
    have hupper :
        Filter.Tendsto
          (fun n : ℕ ↦
            Csurf *
              eLpNorm
                (fun z : ℂ ↦ Z (η n) ((chartAt ℂ c).symm z) - b n) 2
                (MeasureTheory.volume.restrict Kcoord))
          Filter.atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hcoord_tendsto' (Or.inr hC_ne_top)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper
        (fun _n ↦ zero_le)
        hle
  have hvalue_bound : ∀ n : ℕ, greenLocalL2SeminormSq g K (Z n) ≤ 1 := by
    intro n
    calc
      greenLocalL2SeminormSq g K (Z n)
          ≤ greenLocalL2SeminormSq g (closure Q) (Z n) :=
            greenLocalL2SeminormSq_mono_set hKQ (Z n)
      _ = 1 := hZ_unit n
  have hvalue_boundη :
      ∀ n : ℕ, ∫ x in K, (Z (η n) x) ^ (2 : ℕ) ∂g.volume ≤ 1 := by
    intro n
    simpa [greenLocalL2SeminormSq] using hvalue_bound (η n)
  have hmemη : ∀ n : ℕ,
      MemLp (fun x : X ↦ Z (η n) x) 2 (g.volume.restrict K) := by
    intro n
    exact (Z (η n)).memLp_toFun.mono_measure Measure.restrict_le_self
  have hK_ne_top : g.volume K ≠ (∞ : ℝ≥0∞) :=
    hK_compact.measure_ne_top
  exact
    positive_measure_moving_constants_extract_constant_subsequence
      (μ := g.volume) (K := K) hK_pos hK_ne_top
      (fun n : ℕ ↦ fun x : X ↦ Z (η n) x) b
      hmemη hvalue_boundη hb_surface_tendsto

/--
%%handwave
name:
  Finite compact chart cover with constant Rellich extraction for finite-energy sequences
statement:
  Let \(Q\) be an open subset of a Riemann surface with compact closure.  If
  a sequence of zero-trace Sobolev functions has local \(L^2\) mass one on
  \(\overline Q\), finite geometric gradient energy in every term, and
  Dirichlet energy tending to zero, then \(\overline Q\) has a finite compact
  cover such that on each cover element every subsequence has a further
  subsequence converging in \(L^2\) to a constant.
proof:
  Use a finite compact cover by pieces contained in coordinate balls.  Zero
  area pieces are trivial.  On positive-area pieces, apply the finite-energy
  chart-ball extraction theorem.
-/
private theorem exists_finite_compact_rellich_cover_on_closure_of_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (_hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (_hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ (ι : Type) (_ : Fintype ι) (Kc : ι → Set X),
      (∀ i : ι, IsCompact (Kc i)) ∧
        closure Q = ⋃ i : ι, Kc i ∧
        ∀ i : ι, ∀ η : ℕ → ℕ, StrictMono η →
          ∃ a : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            Filter.Tendsto
              (fun n : ℕ ↦
                eLpNorm (fun x : X ↦ Z (η (ψ n)) x - a) 2
                  (g.volume.restrict (Kc i)))
              Filter.atTop (𝓝 0) := by
  classical
  letI : IsManifold SurfaceRealModel ∞ X := g.metric.isManifold_real
  letI : IsManifold SurfaceRealModel 1 X := inferInstance
  letI : SecondCountableTopology
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) :=
    surface_differential_totalSpace_secondCountable (X := X)
  letI : TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := SurfaceRealModel) X ℝ) :=
    surface_differential_totalSpace_pseudoMetrizable (X := X)
  rcases exists_finite_compact_chart_ball_cover_closure
      (X := X) (Q := Q) hQ_compact with
    ⟨ι, hι, Kc, cc, r, R, hKc_compact, hcover, hr_pos, hrR,
      hclosed_target, hK_chart⟩
  letI : Fintype ι := hι
  have hKc_closure : ∀ i : ι, Kc i ⊆ closure Q := by
    intro i x hx
    rw [hcover]
    exact Set.mem_iUnion.2 ⟨i, hx⟩
  refine ⟨ι, hι, Kc, hKc_compact, hcover, ?_⟩
  intro i η hη
  by_cases hzero : g.volume (Kc i) = 0
  · refine ⟨0, fun n : ℕ ↦ n, strictMono_id, ?_⟩
    have hrestrict_zero : g.volume.restrict (Kc i) = 0 :=
      Measure.restrict_eq_zero.mpr hzero
    simp [hrestrict_zero]
  · have hpos : 0 < g.volume (Kc i) :=
      lt_of_le_of_ne zero_le (fun h ↦ hzero h.symm)
    exact
      positive_compact_chart_ball_piece_constant_subsequence_of_unit_localL2_and_dirichlet_tendsto_of_integrable
        (g := g) (Q := Q) (K := Kc i)
        (hKc_compact i) (hKc_closure i) (cc i)
        (hr_pos i) (hrR i) (hclosed_target i) (hK_chart i) hpos
        Z _hZ_unit hZ_int hZ_energy η hη

/--
%%handwave
name:
  A retained \(L^2\) lower bound rules out the zero constant
statement:
  If a sequence converges in \(L^2\) to a constant on a measure space and the
  same sequence has a uniform positive \(L^2\) lower bound, then the constant
  is not zero.
proof:
  If the constant were zero, \(L^2\)-convergence would make the norms of the
  sequence eventually smaller than the retained positive lower bound, a
  contradiction.
-/
theorem constant_ne_zero_of_L2_tendsto_and_uniform_eLpNorm_lower
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → X → ℝ} {a δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ n : ℕ, ENNReal.ofReal δ ≤ eLpNorm (u n) 2 μ)
    (hlim :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun x : X ↦ u n x - a) 2 μ)
        Filter.atTop (𝓝 0)) :
    a ≠ 0 := by
  intro ha
  have hlim_zero :
      Filter.Tendsto (fun n : ℕ ↦ eLpNorm (u n) 2 μ)
        Filter.atTop (𝓝 0) := by
    simpa [ha] using hlim
  have hδENN : (0 : ℝ≥0∞) < ENNReal.ofReal δ :=
    ENNReal.ofReal_pos.mpr hδ
  have hsmall_eventually :
      ∀ᶠ n : ℕ in Filter.atTop, eLpNorm (u n) 2 μ < ENNReal.ofReal δ :=
    hlim_zero.eventually (isOpen_Iio.mem_nhds hδENN)
  rcases Filter.eventually_atTop.1 hsmall_eventually with ⟨N, hN⟩
  exact not_lt_of_ge (hlower N) (hN N le_rfl)

/--
%%handwave
name:
  Almost-everywhere convergence to a nonzero constant gives a fixed sign
statement:
  On a finite positive-measure set, if a sequence of a.e. measurable real
  functions converges almost everywhere to a nonzero constant, then there is a
  positive finite-measure measurable subset, a positive threshold, a sign, and
  a subsequence whose signed values are all at least that threshold on the
  subset.
proof:
  Choose the sign of the limiting constant and a threshold below its
  absolute value.  Egorov's theorem gives a positive-measure measurable subset
  on which convergence is uniform, after discarding a small exceptional set.
  Dropping finitely many terms then gives the asserted lower bound for every
  term of the tail subsequence.
-/
theorem exists_fixed_sign_measurable_set_of_ae_tendsto_nonzero_constant
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    {A₀ : Set X} (hA₀_meas : MeasurableSet A₀)
    (hA₀_ne_top : μ A₀ ≠ (∞ : ℝ≥0∞)) (hA₀_pos : 0 < μ A₀)
    (W : ℕ → X → ℝ) (hW_aemeas : ∀ n : ℕ, AEStronglyMeasurable (W n) μ)
    {a : ℝ} (ha : a ≠ 0)
    (hW_tendsto :
      ∀ᵐ x ∂μ, x ∈ A₀ →
        Filter.Tendsto (fun n : ℕ ↦ W n x) Filter.atTop (𝓝 a)) :
    ∃ A : Set X, MeasurableSet A ∧ μ A ≠ (∞ : ℝ≥0∞) ∧
      0 < μ A ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ n : ℕ, ∀ x ∈ A, ρ ≤ s * W (ψ n) x := by
  classical
  let p : X → (ℕ → ℝ) → Prop :=
    fun x values ↦ x ∈ A₀ →
      Filter.Tendsto values Filter.atTop (𝓝 a)
  let hW_aemeas' : ∀ n : ℕ, AEMeasurable (W n) μ :=
    fun n ↦ (hW_aemeas n).aemeasurable
  let G : Set X := aeSeqSet hW_aemeas' p
  let F : ℕ → X → ℝ := aeSeq hW_aemeas' p
  have hG_meas : MeasurableSet G := by
    simpa [G] using (aeSeq.aeSeqSet_measurableSet (hf := hW_aemeas') (p := p))
  have hG_compl_zero : μ Gᶜ = 0 := by
    simpa [G, p, hW_aemeas'] using
      (aeSeq.measure_compl_aeSeqSet_eq_zero
        (hf := hW_aemeas') (p := p) hW_tendsto)
  have hA₀_diff_G_zero : μ (A₀ \ G) = 0 :=
    measure_mono_null (by intro x hx; exact hx.2) hG_compl_zero
  have hA₀_inter_G_eq : μ (A₀ ∩ G) = μ A₀ := by
    have hdecomp : μ (A₀ ∩ G) + μ (A₀ \ G) = μ A₀ :=
      measure_inter_add_diff A₀ hG_meas
    simpa [hA₀_diff_G_zero] using hdecomp
  have hA₀G_pos : 0 < μ (A₀ ∩ G) := by
    simpa [hA₀_inter_G_eq] using hA₀_pos
  have choose_tail
      {ρ s : ℝ} (hρ : 0 < ρ) (hρsa : ρ < s * a)
      (hsign : s = 1 ∨ s = -1) :
      ∃ A : Set X, MeasurableSet A ∧ μ A ≠ (∞ : ℝ≥0∞) ∧
        0 < μ A ∧
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ n : ℕ, ∀ x ∈ A, ρ ≤ s * W (ψ n) x := by
    let Tail : ℕ → Set X :=
      fun N ↦ {x : X | ∀ n : ℕ, N ≤ n → ρ ≤ s * F n x}
    let E : ℕ → Set X := fun N ↦ (A₀ ∩ G) ∩ Tail N
    have hTail_meas : ∀ N : ℕ, MeasurableSet (Tail N) := by
      intro N
      rw [show Tail N =
          ⋂ n : ℕ, ⋂ _hn : N ≤ n, {x : X | ρ ≤ s * F n x} by
        ext x
        simp [Tail]]
      refine MeasurableSet.iInter ?_
      intro n
      refine MeasurableSet.iInter ?_
      intro _hn
      exact measurableSet_le measurable_const
        (measurable_const.mul
          (by
            simpa [F] using
              (aeSeq.measurable hW_aemeas' p n)))
    have hE_meas : ∀ N : ℕ, MeasurableSet (E N) := by
      intro N
      exact (hA₀_meas.inter hG_meas).inter (hTail_meas N)
    have hcover : A₀ ∩ G ⊆ ⋃ N : ℕ, E N := by
      intro x hx
      have hxA₀ : x ∈ A₀ := hx.1
      have hxG : x ∈ G := hx.2
      have hFx_tendsto :
          Filter.Tendsto (fun n : ℕ ↦ F n x) Filter.atTop (𝓝 a) := by
        simpa [F, p] using
          (aeSeq.prop_of_mem_aeSeqSet hW_aemeas' (p := p) hxG hxA₀)
      have hsFx_tendsto :
          Filter.Tendsto (fun n : ℕ ↦ s * F n x) Filter.atTop (𝓝 (s * a)) :=
        tendsto_const_nhds.mul hFx_tendsto
      have heventually :
          ∀ᶠ n : ℕ in Filter.atTop, ρ ≤ s * F n x :=
        (hsFx_tendsto.eventually (isOpen_Ioi.mem_nhds hρsa)).mono
          fun _ hn ↦ le_of_lt hn
      rcases Filter.eventually_atTop.1 heventually with ⟨N, hN⟩
      refine Set.mem_iUnion.2 ⟨N, ?_⟩
      refine ⟨⟨hxA₀, hxG⟩, ?_⟩
      intro n hn
      exact hN n hn
    have hE_pos : ∃ N : ℕ, 0 < μ (E N) := by
      by_contra hnone
      have hnone' : ∀ N : ℕ, ¬ 0 < μ (E N) := not_exists.mp hnone
      have hE_zero : ∀ N : ℕ, μ (E N) = 0 := by
        intro N
        exact le_antisymm (not_lt.mp (hnone' N)) zero_le
      have hUnion_zero : μ (⋃ N : ℕ, E N) = 0 :=
        measure_iUnion_null hE_zero
      have hA₀G_zero : μ (A₀ ∩ G) = 0 :=
        measure_mono_null hcover hUnion_zero
      exact (ne_of_gt hA₀G_pos) hA₀G_zero
    rcases hE_pos with ⟨N, hEN_pos⟩
    have hEN_subset_A₀ : E N ⊆ A₀ := by
      intro x hx
      exact hx.1.1
    have hEN_ne_top : μ (E N) ≠ (∞ : ℝ≥0∞) :=
      ne_of_lt ((measure_mono hEN_subset_A₀).trans_lt
        (lt_top_iff_ne_top.2 hA₀_ne_top))
    refine ⟨E N, hE_meas N, hEN_ne_top, hEN_pos, fun n : ℕ ↦ N + n, ?_, ?_⟩
    · intro i j hij
      exact Nat.add_lt_add_left hij N
    · intro n x hx
      have hxG : x ∈ G := hx.1.2
      have htail : x ∈ Tail N := hx.2
      have hF_lower : ρ ≤ s * F (N + n) x :=
        htail (N + n) (Nat.le_add_right N n)
      have hFW : F (N + n) x = W (N + n) x := by
        simpa [F] using
          (aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hW_aemeas' (p := p) hxG (N + n))
      simpa [hFW] using hF_lower
  by_cases ha_pos : 0 < a
  · let ρ : ℝ := a / 2
    have hρ : 0 < ρ := by
      dsimp [ρ]
      linarith
    have hρa : ρ < (1 : ℝ) * a := by
      dsimp [ρ]
      linarith
    rcases choose_tail hρ hρa (Or.inl rfl) with
      ⟨A, hA_meas, hA_ne_top, hA_pos, ψ, hψ, hlower⟩
    exact ⟨A, hA_meas, hA_ne_top, hA_pos, ρ, hρ, 1, Or.inl rfl, ψ, hψ, hlower⟩
  · have ha_neg : a < 0 := lt_of_le_of_ne (not_lt.mp ha_pos) ha
    let ρ : ℝ := -a / 2
    have hρ : 0 < ρ := by
      dsimp [ρ]
      linarith
    have hρa : ρ < (-1 : ℝ) * a := by
      dsimp [ρ]
      linarith
    rcases choose_tail hρ hρa (Or.inr rfl) with
      ⟨A, hA_meas, hA_ne_top, hA_pos, ψ, hψ, hlower⟩
    exact ⟨A, hA_meas, hA_ne_top, hA_pos, ρ, hρ, -1, Or.inr rfl, ψ, hψ, hlower⟩

/--
%%handwave
name:
  Capacity competitors from a fixed signed lower bound
statement:
  Let \(Z_n\in W^{1,2}_0(X)\) have Dirichlet energies tending to zero. If along
  a subsequence \(sZ_n\ge\rho>0\) on \(L\), with \(s=\pm1\), then for every
  \(\varepsilon>0\) there is \(u\in W^{1,2}_0(X)\) such that
  \(u\ge1\) on \(L\) and \(\mathcal E(u)<\varepsilon\).
proof:
  Rescale \(Z_n\) by \(s/\rho\). The fixed-sign bound gives \(u\ge1\), while
  quadratic homogeneity and vanishing energy give the required tolerance.
-/
theorem capacity_competitors_of_fixed_sign_lower_bound_and_dirichlet_tendsto_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0))
    {L : Set X} {ρ s : ℝ} {φ : ℕ → ℕ}
    (hρ : 0 < ρ) (hsign : s = 1 ∨ s = -1) (hφ : StrictMono φ)
    (hlower : ∀ n : ℕ, ∀ x ∈ L, ρ ≤ s * Z (φ n) x) :
    ∀ ε : ℝ, 0 < ε →
      ∃ u : SobolevH1ZeroOnSurface g.volume,
        (∀ x ∈ L, 1 ≤ u x) ∧ greenDirichletSeminormSq g u < ε := by
  intro ε hε
  let c : ℝ := s / ρ
  have hs_sq : s ^ 2 = 1 := by
    rcases hsign with rfl | rfl <;> norm_num
  have hc_sq_pos : 0 < c ^ 2 := by
    dsimp [c]
    rw [div_pow, hs_sq]
    positivity
  have hc_ne : c ≠ 0 := by
    intro hc
    rw [hc] at hc_sq_pos
    norm_num at hc_sq_pos
  have hsubseq_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z (φ n)))
        Filter.atTop (𝓝 0) :=
    hZ_energy.comp hφ.tendsto_atTop
  have hδ_pos : 0 < ε / c ^ 2 :=
    div_pos hε hc_sq_pos
  have hlt_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        greenDirichletSeminormSq g (Z (φ n)) < ε / c ^ 2 :=
    hsubseq_energy.eventually (isOpen_Iio.mem_nhds hδ_pos)
  rcases Filter.eventually_atTop.1 hlt_eventually with ⟨N, hN⟩
  refine ⟨SobolevH1ZeroOnSurface.const_smul c (Z (φ N)), ?_, ?_⟩
  · intro x hxL
    have hlower_N : ρ ≤ s * Z (φ N) x :=
      hlower N x hxL
    calc
      1 = ρ⁻¹ * ρ := by
            field_simp [hρ.ne']
      _ ≤ ρ⁻¹ * (s * Z (φ N) x) :=
            mul_le_mul_of_nonneg_left hlower_N (inv_nonneg.mpr hρ.le)
      _ = c * Z (φ N) x := by
            dsimp [c]
            rw [div_mul_eq_mul_div, inv_mul_eq_div]
  · calc
      greenDirichletSeminormSq g
          (SobolevH1ZeroOnSurface.const_smul c (Z (φ N)))
          = c ^ 2 * greenDirichletSeminormSq g (Z (φ N)) := by
              simpa using
                greenDirichletSeminormSq_const_smul
                  (g := g) c (Z (φ N))
      _ < c ^ 2 * (ε / c ^ 2) :=
            mul_lt_mul_of_pos_left (hN N le_rfl) hc_sq_pos
      _ = ε := by
            field_simp [hc_ne]

/--
%%handwave
name:
  Compact mass retention and local convergence to a constant
statement:
  Let \(\overline Q\) be compact. If \(Z_n\in W^{1,2}_0(X)\) has unit
  \(L^2(\overline Q)\)-mass, integrable gradient energy, and Dirichlet energy
  tending to zero, then some positive-measure compact \(K\) and subsequence
  satisfy a uniform positive \(L^2(K)\)-mass bound and converge in \(L^2(K)\)
  to a constant.
proof:
  Use the finite compact Rellich chart cover of \(\overline Q\), then apply
  finite-cover mass retention and select a piece on which a subsequence
  converges to one constant.
-/
theorem exists_compact_constant_L2_tendsto_subsequence_with_uniform_mass_of_unit_localL2_dirichlet_tendsto_zero_on_compact_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ K : Set X, IsCompact K ∧ 0 < g.volume K ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ a : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ n : ℕ,
          ENNReal.ofReal δ ≤
            eLpNorm (fun x : X ↦ Z (φ n) x) 2 (g.volume.restrict K)) ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ Z (φ n) x - a) 2 (g.volume.restrict K))
          Filter.atTop (𝓝 0) := by
  rcases
    exists_finite_compact_rellich_cover_on_closure_of_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy with
    ⟨ι, hι, Kc, hKc_compact, hcover, hpiece_constant⟩
  letI : Fintype ι := hι
  exact
    exists_compact_constant_L2_tendsto_subsequence_with_uniform_mass_of_finite_cover
      (g := g) (Q := Q) Kc hKc_compact hcover Z hZ_unit hpiece_constant

/--
%%handwave
name:
  Compact mass retention on a relatively compact open set
statement:
  Under unit local \(L^2\)-mass and vanishing Dirichlet energy on a relatively
  compact open \(Q\), a subsequence retains uniformly positive mass on a
  positive-measure compact \(K\subset\overline Q\) and converges there in
  \(L^2\) to a constant.
proof:
  Apply [compact mass retention and convergence to a constant on \(\overline Q\)](lean:exists_compact_constant_L2_tendsto_subsequence_with_uniform_mass_of_unit_localL2_dirichlet_tendsto_zero_on_compact_of_integrable).
-/
theorem exists_compact_constant_L2_tendsto_subsequence_with_uniform_mass_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (_hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ K : Set X, IsCompact K ∧ 0 < g.volume K ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ a : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ n : ℕ,
          ENNReal.ofReal δ ≤
            eLpNorm (fun x : X ↦ Z (φ n) x) 2 (g.volume.restrict K)) ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun x : X ↦ Z (φ n) x - a) 2 (g.volume.restrict K))
          Filter.atTop (𝓝 0) :=
  exists_compact_constant_L2_tendsto_subsequence_with_uniform_mass_of_unit_localL2_dirichlet_tendsto_zero_on_compact_of_integrable
    (g := g) _hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy

/--
%%handwave
name:
  Constant \(L^2\) limit on a finite positive-measure set
statement:
  Under the same normalized vanishing-energy hypotheses, there are a
  measurable set \(A\) with \(0<\mu(A)<\infty\), a constant \(a\), and a
  subsequence converging to \(a\) in \(L^2(A)\) while retaining a uniform
  positive \(L^2(A)\)-mass.
proof:
  Take the compact set from the compact mass-retention theorem; compactness
  makes it measurable and of finite measure.
-/
theorem exists_constant_L2_tendsto_subsequence_with_uniform_mass_on_measurable_set_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ A : Set X, MeasurableSet A ∧ g.volume A ≠ (∞ : ℝ≥0∞) ∧
      0 < g.volume A ∧
        ∃ δ : ℝ, 0 < δ ∧ ∃ a : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
          (∀ n : ℕ,
            ENNReal.ofReal δ ≤
              eLpNorm (fun x : X ↦ Z (φ n) x) 2 (g.volume.restrict A)) ∧
          Filter.Tendsto
            (fun n : ℕ ↦
              eLpNorm (fun x : X ↦ Z (φ n) x - a) 2 (g.volume.restrict A))
            Filter.atTop (𝓝 0) := by
  rcases
    exists_compact_constant_L2_tendsto_subsequence_with_uniform_mass_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy with
    ⟨K, hK_compact, hK_pos, δ, hδ, a, φ, hφ, hlower, hlim⟩
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  have hK_ne_top : g.volume K ≠ (∞ : ℝ≥0∞) :=
    hK_compact.measure_ne_top
  exact
    ⟨K, hK_compact.measurableSet, hK_ne_top, hK_pos,
      δ, hδ, a, φ, hφ, hlower, hlim⟩

/--
%%handwave
name:
  Nonzero constant \(L^2\) limit on a measurable set
statement:
  A unit-local-mass sequence with vanishing Dirichlet energy has, on some set
  \(A\) of finite positive measure, a subsequence converging in \(L^2(A)\) to
  a nonzero constant.
proof:
  The preceding extraction gives convergence to a constant and a uniform
  positive lower bound on the subsequence norms; such a limit cannot be zero.
-/
theorem exists_nonzero_constant_L2_tendsto_subsequence_on_measurable_set_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ A : Set X, MeasurableSet A ∧ g.volume A ≠ (∞ : ℝ≥0∞) ∧
      0 < g.volume A ∧
        ∃ a : ℝ, a ≠ 0 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Filter.Tendsto
            (fun n : ℕ ↦
              eLpNorm (fun x : X ↦ Z (φ n) x - a) 2 (g.volume.restrict A))
            Filter.atTop (𝓝 0) := by
  rcases
    exists_constant_L2_tendsto_subsequence_with_uniform_mass_on_measurable_set_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy with
    ⟨A, hA_meas, hA_ne_top, hA_pos, δ, hδ, a, φ, hφ, hlower, hlim⟩
  have ha : a ≠ 0 :=
    constant_ne_zero_of_L2_tendsto_and_uniform_eLpNorm_lower
      (μ := g.volume.restrict A) (u := fun n : ℕ ↦ fun x : X ↦ Z (φ n) x)
      hδ hlower hlim
  exact ⟨A, hA_meas, hA_ne_top, hA_pos, a, ha, φ, hφ, hlim⟩

/--
%%handwave
name:
  Almost-everywhere convergence to a nonzero constant
statement:
  Under unit local \(L^2\)-mass and vanishing Dirichlet energy, there are a
  finite positive-measure set \(A\), \(a\ne0\), and a subsequence converging
  pointwise almost everywhere on \(A\) to \(a\).
proof:
  First extract \(L^2(A)\)-convergence to a nonzero constant, hence convergence
  in measure, then pass to an almost-everywhere convergent subsequence.
-/
theorem exists_nonzero_constant_ae_tendsto_subsequence_on_measurable_set_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ A : Set X, MeasurableSet A ∧ g.volume A ≠ (∞ : ℝ≥0∞) ∧
      0 < g.volume A ∧
        ∃ a : ℝ, a ≠ 0 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ᵐ x ∂g.volume, x ∈ A →
            Filter.Tendsto (fun n : ℕ ↦ Z (φ n) x) Filter.atTop (𝓝 a) := by
  rcases
    exists_nonzero_constant_L2_tendsto_subsequence_on_measurable_set_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy with
    ⟨A, hA_meas, hA_ne_top, hA_pos, a, ha, φ, hφ, hφ_L2⟩
  have hseq_aestr :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun x : X ↦ Z (φ n) x) (g.volume.restrict A) := by
    intro n
    exact (Z (φ n)).memLp_toFun.aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hconst_aestr :
      AEStronglyMeasurable (fun _x : X ↦ a) (g.volume.restrict A) :=
    aestronglyMeasurable_const
  have hconv_measure :
      TendstoInMeasure (g.volume.restrict A)
        (fun n x ↦ Z (φ n) x) Filter.atTop (fun _x : X ↦ a) := by
    exact
      tendstoInMeasure_of_tendsto_eLpNorm
        (μ := g.volume.restrict A) (p := (2 : ℝ≥0∞))
        (by norm_num) hseq_aestr hconst_aestr
        (by simpa [Pi.sub_apply] using hφ_L2)
  rcases hconv_measure.exists_seq_tendsto_ae with
    ⟨ψ, hψ, hψ_ae_restrict⟩
  refine ⟨A, hA_meas, hA_ne_top, hA_pos, a, ha, φ ∘ ψ, hφ.comp hψ, ?_⟩
  have hψ_ae_volume :
      ∀ᵐ x ∂g.volume, x ∈ A →
        Filter.Tendsto (fun n : ℕ ↦ Z (φ (ψ n)) x)
          Filter.atTop (𝓝 a) := by
    exact (ae_restrict_iff' hA_meas).1 hψ_ae_restrict
  filter_upwards [hψ_ae_volume] with x hx hxA
  simpa [Function.comp_def] using hx hxA

/--
%%handwave
name:
  Fixed-sign lower bound on a measurable set
statement:
  Under unit local \(L^2\)-mass and vanishing Dirichlet energy, some
  finite positive-measure set \(A\), \(\rho>0\), sign \(s=\pm1\), and
  subsequence satisfy \(sZ_n(x)\ge\rho\) for every \(x\in A\).
proof:
  Extract almost-everywhere convergence to a nonzero constant and choose a
  positive-measure subset on which the convergence has a uniform signed lower
  bound.
-/
theorem exists_fixed_sign_measurable_set_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ A : Set X, MeasurableSet A ∧ g.volume A ≠ (∞ : ℝ≥0∞) ∧
      0 < g.volume A ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
            ∀ n : ℕ, ∀ x ∈ A, ρ ≤ s * Z (φ n) x := by
  rcases
    exists_nonzero_constant_ae_tendsto_subsequence_on_measurable_set_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy with
    ⟨A₀, hA₀_meas, hA₀_ne_top, hA₀_pos, a, ha, φ₀, hφ₀, hφ₀_tendsto⟩
  rcases exists_fixed_sign_measurable_set_of_ae_tendsto_nonzero_constant
      (μ := g.volume) hA₀_meas hA₀_ne_top hA₀_pos
      (fun n : ℕ ↦ Z (φ₀ n))
      (fun n : ℕ ↦ (Z (φ₀ n)).memLp_toFun.aestronglyMeasurable)
      ha hφ₀_tendsto with
    ⟨A, hA_meas, hA_ne_top, hA_pos, ρ, hρ, s, hsign, ψ, hψ, hlower⟩
  refine ⟨A, hA_meas, hA_ne_top, hA_pos, ρ, hρ, s, hsign, φ₀ ∘ ψ, hφ₀.comp hψ, ?_⟩
  intro n x hxA
  exact hlower n x hxA

/--
%%handwave
name:
  Fixed-sign lower bound on a compact set
statement:
  Under the normalized vanishing-energy hypotheses, there are a compact
  \(L\) of positive measure, \(\rho>0\), \(s=\pm1\), and a subsequence with
  \(sZ_n\ge\rho\) on \(L\).
proof:
  Obtain the bound on a measurable finite positive-measure set, then use inner
  regularity to choose a positive-measure compact subset.
-/
theorem exists_fixed_sign_compact_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ L : Set X, IsCompact L ∧ 0 < g.volume L ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ n : ℕ, ∀ x ∈ L, ρ ≤ s * Z (φ n) x := by
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  haveI : TopologicalSpace.PseudoMetrizableSpace X := by
    haveI : RegularSpace X := inferInstance
    exact TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology X
  haveI : SigmaCompactSpace X := inferInstance
  haveI : IsLocallyFiniteMeasure g.volume := inferInstance
  haveI : Measure.InnerRegularCompactLTTop g.volume := inferInstance
  rcases
    exists_fixed_sign_measurable_set_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy with
    ⟨A, hA_meas, hA_ne_top, hA_pos, ρ, hρ, s, hsign, φ, hφ, hlower⟩
  rcases exists_compact_subset_pos_measure_of_measurable_pos_measure
      (μ := g.volume) hA_meas hA_ne_top hA_pos with
    ⟨L, hL_compact, hLA, hL_pos⟩
  exact
    ⟨L, hL_compact, hL_pos, ρ, hρ, s, hsign, φ, hφ,
      fun n x hxL ↦ hlower n x (hLA hxL)⟩

/--
%%handwave
name:
  Positive-measure zero-capacity compact set from normalized vanishing energy
statement:
  If \(Z_n\in W^{1,2}_0(X)\) has unit local \(L^2\)-mass on
  \(\overline Q\), integrable gradient energy, and Dirichlet energy tending to
  zero, then some compact \(L\) has positive measure and capacity zero.
proof:
  Extract a fixed signed lower bound on a positive-measure compact set and
  apply [the construction of arbitrarily small-energy capacity competitors](lean:capacity_competitors_of_fixed_sign_lower_bound_and_dirichlet_tendsto_zero).
-/
theorem exists_compact_zero_capacity_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (Z : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hZ_unit : ∀ n : ℕ, greenLocalL2SeminormSq g (closure Q) (Z n) = 1)
    (hZ_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((Z n).weakGradient x) ((Z n).weakGradient x))
        g.volume)
    (hZ_energy :
      Filter.Tendsto
        (fun n : ℕ ↦ greenDirichletSeminormSq g (Z n))
        Filter.atTop (𝓝 0)) :
    ∃ L : Set X, IsCompact L ∧ 0 < g.volume L ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ u : SobolevH1ZeroOnSurface g.volume,
          (∀ x ∈ L, 1 ≤ u x) ∧ greenDirichletSeminormSq g u < ε := by
  rcases
    exists_fixed_sign_compact_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy with
    ⟨L, hL_compact, hL_pos, ρ, hρ, s, hsign, φ, hφ, hlower⟩
  exact
    ⟨L, hL_compact, hL_pos,
      capacity_competitors_of_fixed_sign_lower_bound_and_dirichlet_tendsto_zero
        (g := g) Z hZ_energy hρ hsign hφ hlower⟩

/--
%%handwave
name:
  Zero-capacity compact set from a vanishing energy-to-mass ratio
statement:
  If \(H_n\) has positive local \(L^2(\overline Q)\)-mass and
  \(\mathcal E(H_n)/\lVert H_n\rVert_{L^2(\overline Q)}^2\to0\), then some
  positive-measure compact set has capacity zero.
proof:
  Normalize each \(H_n\) to unit local mass, obtaining a sequence of vanishing
  energy, and apply the normalized extraction theorem.
-/
theorem exists_compact_zero_capacity_of_positive_localL2_ratio_tendsto_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (H : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hH_pos : ∀ n : ℕ, 0 < greenLocalL2SeminormSq g (closure Q) (H n))
    (hH_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((H n).weakGradient x) ((H n).weakGradient x))
        g.volume)
    (hH_ratio :
      Filter.Tendsto
        (fun n : ℕ ↦
          greenDirichletSeminormSq g (H n) /
            greenLocalL2SeminormSq g (closure Q) (H n))
        Filter.atTop (𝓝 0)) :
    ∃ L : Set X, IsCompact L ∧ 0 < g.volume L ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ u : SobolevH1ZeroOnSurface g.volume,
          (∀ x ∈ L, 1 ≤ u x) ∧ greenDirichletSeminormSq g u < ε := by
  rcases
    exists_unit_localL2_sequence_with_dirichlet_tendsto_zero_of_positive_localL2_ratio_tendsto_of_integrable
      (g := g) (K := closure Q) H hH_pos hH_int hH_ratio with
    ⟨Z, hZ_unit, hZ_int, hZ_energy⟩
  exact
    exists_compact_zero_capacity_of_unit_localL2_dirichlet_tendsto_zero_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact Z hZ_unit hZ_int hZ_energy

/--
%%handwave
name:
  Zero-capacity compact set from a bad local \(L^2\) sequence
statement:
  If \(n\mathcal E(H_n)<\lVert H_n\rVert_{L^2(\overline Q)}^2\) for all \(n\),
  then some compact set of positive measure has capacity zero.
proof:
  Shift the sequence by one index; its energy-to-local-mass ratio tends to
  zero, so apply the vanishing-ratio capacity theorem.
-/
theorem exists_compact_zero_capacity_of_bad_localL2_sequence_on_relcompact_open_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (H : ℕ → SobolevH1ZeroOnSurface g.volume)
    (hH_int : ∀ n : ℕ,
      Integrable
        (fun x : X ↦
          g.gradientInner x ((H n).weakGradient x) ((H n).weakGradient x))
        g.volume)
    (hH : ∀ n : ℕ,
      (n : ℝ) * greenDirichletSeminormSq g (H n) <
        greenLocalL2SeminormSq g (closure Q) (H n)) :
    ∃ L : Set X, IsCompact L ∧ 0 < g.volume L ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ u : SobolevH1ZeroOnSurface g.volume,
          (∀ x ∈ L, 1 ≤ u x) ∧ greenDirichletSeminormSq g u < ε := by
  exact
    exists_compact_zero_capacity_of_positive_localL2_ratio_tendsto_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact (fun n : ℕ ↦ H (n + 1))
      (fun n : ℕ ↦
        bad_localL2_sequence_localL2_pos
          (g := g) (K := closure Q) H hH (n + 1))
      (fun n : ℕ ↦ hH_int (n + 1))
      (by
        simpa using
          bad_localL2_sequence_shifted_dirichlet_div_localL2_tendsto_zero
            (g := g) (K := closure Q) H hH)

/--
%%handwave
name:
  Failure of local \(L^2\) control produces a zero-capacity compact set
statement:
  If no constant \(P\ge0\) bounds
  \(\lVert h\rVert_{L^2(\overline Q)}^2\le P\mathcal E(h)\) for all
  finite-energy \(h\in W^{1,2}_0(X)\), then some positive-measure compact set
  has capacity zero.
proof:
  Failure of the estimate yields a bad sequence with arbitrarily large
  mass-to-energy ratio; apply the bad-sequence capacity theorem.
-/
theorem exists_compact_zero_capacity_of_relcompact_open_no_localL2_control_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    {Q : Set X} (hQ_open : IsOpen Q) (hQ_compact : IsCompact (closure Q))
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
      greenLocalL2SeminormSq g (closure Q) h ≤
        P * greenDirichletSeminormSq g h) :
    ∃ L : Set X, IsCompact L ∧ 0 < g.volume L ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ u : SobolevH1ZeroOnSurface g.volume,
          (∀ x ∈ L, 1 ≤ u x) ∧ greenDirichletSeminormSq g u < ε := by
  rcases exists_bad_localL2_sequence_of_no_localL2_control_of_integrable
      (closure Q) hfail with
    ⟨H, hH_int, hH⟩
  exact
    exists_compact_zero_capacity_of_bad_localL2_sequence_on_relcompact_open_of_integrable
      (g := g) hQ_open hQ_compact H hH_int hH

/--
%%handwave
name:
  Failure of compact local \(L^2\) control produces zero capacity
statement:
  Let \(K\) be compact. If no finite constant controls the \(L^2(K)\)-mass of
  all finite-energy zero-trace Sobolev functions by their Dirichlet energy,
  then some compact set of positive measure has capacity zero.
proof:
  Enlarge \(K\) to a relatively compact open neighborhood on which local
  control still fails, then apply the relatively compact open-set theorem.
-/
theorem exists_compact_subset_zero_capacity_of_no_localL2_control_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X) (hK : IsCompact K)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
      greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h) :
    ∃ L : Set X, IsCompact L ∧ 0 < g.volume L ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ u : SobolevH1ZeroOnSurface g.volume,
          (∀ x ∈ L, 1 ≤ u x) ∧ greenDirichletSeminormSq g u < ε := by
  rcases exists_relcompact_open_superset_with_no_localL2_control_of_integrable
      K hK hfail with
    ⟨Q, hQ_open, _hKQ, hQ_compact, hQ_fail⟩
  exact
    exists_compact_zero_capacity_of_relcompact_open_no_localL2_control_of_integrable
      (g := g) hQ_open hQ_compact hQ_fail

/--
%%handwave
name:
  Squared local \(L^2\) control for finite-energy functions
statement:
  If the background metric has positive capacity at infinity, then on every
  compact set the squared local \(L^2\) seminorm of any finite-energy
  zero-trace Sobolev function is controlled by its Dirichlet seminorm squared.
proof:
  Argue by contradiction within the finite-energy class.  A failed estimate
  gives a finite-energy bad sequence; the Rellich extraction then produces a
  positive-area compact set with zero capacity, contradicting positive
  capacity at infinity.
-/
theorem greenLocalL2SeminormSq_le_const_mul_dirichlet_of_positive_capacity_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X) (hK : IsCompact K)
    (hcap : HasPositiveCapacityAtInfinity g) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
      greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h := by
  by_contra hfail
  rcases exists_compact_subset_zero_capacity_of_no_localL2_control_of_integrable
      K hK hfail with
    ⟨L, hL_compact, hL_pos, hL_zero_capacity⟩
  rcases hcap L hL_compact hL_pos with ⟨c, hc_pos, hcapL⟩
  rcases hL_zero_capacity c hc_pos with ⟨u, hu_ge, hu_energy_lt⟩
  exact not_le_of_gt hu_energy_lt (hcapL u hu_ge)

/--
%%handwave
name:
  Admissible functions have at least the compact-set mass
statement:
  If a zero-trace Sobolev function is at least one on a compact set \(K\),
  then its squared local \(L^2\) mass over \(K\) is at least the area of
  \(K\).
proof:
  On \(K\), the pointwise inequality \(u\ge 1\) gives \(u^2\ge 1\).  Integrate
  this inequality over the restricted measure on \(K\); the integral of the
  constant function one is exactly the area of \(K\).
-/
theorem greenLocalL2SeminormSq_ge_measure_of_one_le_on
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X]
    {g : BackgroundSurfaceMetricOnSurface X} {K : Set X}
    (hK : IsCompact K) (u : SobolevH1ZeroOnSurface g.volume)
    (hu_ge : ∀ x ∈ K, 1 ≤ u x) :
    (g.volume K).toReal ≤ greenLocalL2SeminormSq g K u := by
  let μK : Measure X := g.volume.restrict K
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  haveI : IsFiniteMeasure μK := by
    exact isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hsq_int : Integrable (fun x : X ↦ u x ^ (2 : ℕ)) μK := by
    exact (u.memLp_toFun.mono_measure Measure.restrict_le_self).integrable_sq
  have hnonneg_one : 0 ≤ᵐ[μK] (fun _x : X ↦ (1 : ℝ)) :=
    Filter.Eventually.of_forall fun _x ↦ by norm_num
  have hle_sq :
      (fun _x : X ↦ (1 : ℝ)) ≤ᵐ[μK]
        fun x : X ↦ u x ^ (2 : ℕ) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
    have hx : 1 ≤ u x := hu_ge x hxK
    have hx_nonneg : 0 ≤ u x := le_trans (by norm_num) hx
    have hsquare : (1 : ℝ) * 1 ≤ u x * u x :=
      mul_le_mul hx hx (by norm_num) hx_nonneg
    simpa [pow_two] using hsquare
  have h_integral_le :
      ∫ x, (1 : ℝ) ∂μK ≤ ∫ x, u x ^ (2 : ℕ) ∂μK :=
    integral_mono_of_nonneg hnonneg_one hsq_int hle_sq
  have hconst :
      ∫ x, (1 : ℝ) ∂μK = (g.volume K).toReal := by
    rw [integral_const]
    have hmeasure : μK.real Set.univ = (g.volume K).toReal := by
      rw [Measure.real_def, Measure.restrict_apply_univ]
    simp [hmeasure, smul_eq_mul]
  calc
    (g.volume K).toReal = ∫ x, (1 : ℝ) ∂μK := hconst.symm
    _ ≤ ∫ x, u x ^ (2 : ℕ) ∂μK := h_integral_le
    _ = greenLocalL2SeminormSq g K u := by
        simp [greenLocalL2SeminormSq, μK]

/--
%%handwave
name:
  Capacitary Poincare gives positive capacity
statement:
  If local \(L^2\) mass on compact sets is controlled by Dirichlet energy,
  then every positive-area compact set has a positive Dirichlet-capacity
  lower bound.
proof:
  For a compact set \(K\) of positive area, take the Poincare constant on
  \(K\).  Any admissible function \(u\ge 1\) on \(K\) has local \(L^2\) mass at
  least the area of \(K\), while Poincare bounds that mass by the constant
  times the Dirichlet energy.  Dividing gives a positive lower bound; if the
  Poincare constant were zero, there would be no admissible competitor.
-/
theorem positive_capacity_of_capacitary_poincare
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (hpoincare : HasCapacitaryPoincareInequality g) :
    HasPositiveCapacityAtInfinity g := by
  intro K hK hK_pos
  rcases hpoincare K hK with ⟨P, hP_nonneg, hP⟩
  have hK_ne_top : g.volume K ≠ (∞ : ℝ≥0∞) :=
    (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).finite_on_compact K hK
  have hK_toReal_pos : 0 < (g.volume K).toReal :=
    ENNReal.toReal_pos (ne_of_gt hK_pos) hK_ne_top
  by_cases hP_zero : P = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro u hu_ge
    have hlower :
        (g.volume K).toReal ≤ greenLocalL2SeminormSq g K u :=
      greenLocalL2SeminormSq_ge_measure_of_one_le_on
        (g := g) hK u hu_ge
    have hupper :
        greenLocalL2SeminormSq g K u ≤ P * greenDirichletSeminormSq g u :=
      hP u
    have harea_le_zero : (g.volume K).toReal ≤ 0 := by
      simpa [hP_zero] using hlower.trans hupper
    exact False.elim ((not_le_of_gt hK_toReal_pos) harea_le_zero)
  · have hP_pos : 0 < P :=
      lt_of_le_of_ne hP_nonneg (Ne.symm hP_zero)
    refine ⟨(g.volume K).toReal / P,
      div_pos hK_toReal_pos hP_pos, ?_⟩
    intro u hu_ge
    have hlower :
        (g.volume K).toReal ≤ greenLocalL2SeminormSq g K u :=
      greenLocalL2SeminormSq_ge_measure_of_one_le_on
        (g := g) hK u hu_ge
    have hupper :
        greenLocalL2SeminormSq g K u ≤ P * greenDirichletSeminormSq g u :=
      hP u
    have hmul :
        (g.volume K).toReal ≤ P * greenDirichletSeminormSq g u :=
      hlower.trans hupper
    calc
      (g.volume K).toReal / P
          ≤ (P * greenDirichletSeminormSq g u) / P :=
            div_le_div_of_nonneg_right hmul hP_nonneg
      _ = greenDirichletSeminormSq g u := by
            field_simp [hP_pos.ne']

/--
%%handwave
name:
  Capacitary Poincare controls the local \(L^2\) norm
statement:
  If the capacitary Poincare inequality holds, then on every compact set the
  local \(L^2\) norm of a zero-trace Sobolev function is controlled by its
  Dirichlet norm.
proof:
  Apply the squared capacitary Poincare inequality and take square roots.
-/
theorem greenLocalL2SeminormSq_sqrt_le_const_mul_sqrt_dirichlet_of_capacitary_poincare
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X) (hK : IsCompact K)
    (hpoincare : HasCapacitaryPoincareInequality g) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Real.sqrt (greenLocalL2SeminormSq g K h) ≤
        P * Real.sqrt (greenDirichletSeminormSq g h) := by
  rcases hpoincare K hK with ⟨P, hP_nonneg, hP⟩
  refine ⟨Real.sqrt P, Real.sqrt_nonneg P, ?_⟩
  intro h
  let L : ℝ := greenLocalL2SeminormSq g K h
  let D : ℝ := greenDirichletSeminormSq g h
  have hbound : L ≤ P * D := by
    simpa [L, D] using hP h
  calc
    Real.sqrt L ≤ Real.sqrt (P * D) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt P * Real.sqrt D := Real.sqrt_mul hP_nonneg D
    _ = Real.sqrt P * Real.sqrt (greenDirichletSeminormSq g h) := by
      simp [D]

/--
%%handwave
name:
  Local \(L^2\) seminorm is controlled by capacity for finite-energy functions
statement:
  If the background metric has positive capacity at infinity, then on every
  compact set the local \(L^2\) norm of a finite-energy zero-trace Sobolev
  function is controlled by its Dirichlet norm.
proof:
  Apply the squared finite-energy capacitary estimate and take square roots.
-/
theorem greenLocalL2SeminormSq_sqrt_le_const_mul_sqrt_dirichlet_of_positive_capacity_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [ComplexOneManifold X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X) (hK : IsCompact K)
    (hcap : HasPositiveCapacityAtInfinity g) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
      Real.sqrt (greenLocalL2SeminormSq g K h) ≤
        P * Real.sqrt (greenDirichletSeminormSq g h) := by
  rcases greenLocalL2SeminormSq_le_const_mul_dirichlet_of_positive_capacity_of_integrable
      (g := g) K hK hcap with
    ⟨P, hP_nonneg, hP⟩
  refine ⟨Real.sqrt P, Real.sqrt_nonneg P, ?_⟩
  intro h hInt
  let L : ℝ := greenLocalL2SeminormSq g K h
  let D : ℝ := greenDirichletSeminormSq g h
  have hbound : L ≤ P * D := by
    simpa [L, D] using hP h hInt
  calc
    Real.sqrt L ≤ Real.sqrt (P * D) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt P * Real.sqrt D := Real.sqrt_mul hP_nonneg D
    _ = Real.sqrt P * Real.sqrt (greenDirichletSeminormSq g h) := by
      simp [D]


end

end Uniformization

end JJMath
