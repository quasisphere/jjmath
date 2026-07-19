import JJMath.Uniformization.GreenFunctionCore
import JJMath.AnalyticContinuation.LocalBranch
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Compact-superlevel Green functions

This module contains the lightweight potential-theoretic layer for compact-
superlevel Green data and its exponential pointed disk map.  It deliberately
avoids the Sobolev and energy-method imports; those files import this module
when they need to produce compact-superlevel Green data by variational means.
-/

namespace JJMath

open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization

/--
%%handwave
name:
  Green function data with compact positive superlevels
statement:
  A compact-superlevel Green function has the usual local Green-function
  properties at the pole and away from it, together with compact positive
  superlevel sets.  It does not separately require topological convergence to
  zero along the cocompact filter.
-/
structure CompactSuperlevelGreenFunctionWithPole
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (p : X) where
  toFun : X → ℝ
  positive_away_pole : ∀ x : X, x ≠ p → 0 < toFun x
  harmonic_away_pole : IsHarmonicOnSurface {x : X | x ≠ p} toFun
  tends_to_infinity_at_pole :
    Filter.Tendsto toFun (𝓝[≠] p) Filter.atTop
  logarithmic_singularity :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ H : X → ℝ,
        IsHarmonicOnSurface χ.chart.source H ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            toFun x + Real.log ‖χ.chart x - χ.chart p‖ = H x
  compact_positive_superlevel :
    ∀ a : ℝ, 0 < a → IsCompact ({p} ∪ {x : X | a ≤ toFun x})

/--
%%handwave
name:
  Plane maps associated to compact-superlevel Green data
statement:
  A holomorphic plane map is associated to compact-superlevel Green data when
  its logarithmic modulus is \(-G\) away from the pole, its only zero is the
  pole, and that zero is simple.
-/
structure CompactSuperlevelGreenFunctionPlaneMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) where
  toFun : X → ℂ
  holomorphic : HolomorphicMap X ℂ toFun
  log_norm_eq : ∀ x : X, x ≠ p → Real.log ‖toFun x‖ = -G.toFun x
  zero_fiber : ∀ x : X, toFun x = 0 ↔ x = p
  simple_zero :
    ∀ χ : PointedSurfaceCoordinate X p,
      surfaceComplexDerivativeInCoordinate χ toFun ≠ 0

/--
%%handwave
name:
  Compact-superlevel Green plane maps land in the unit disk
statement:
  The plane map associated to compact-superlevel Green data has norm strictly
  less than one everywhere.
proof:
  At the pole the map vanishes.  Away from the pole, positivity of \(G\) gives
  \(\log |f|=-G<0=\log 1\), hence \(|f|<1\).
-/
theorem compactSuperlevelGreenFunctionPlaneMap_norm_lt_one
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (F : CompactSuperlevelGreenFunctionPlaneMap X G) :
    ∀ x : X, ‖F.toFun x‖ < 1 := by
  intro x
  by_cases hxp : x = p
  · have hxzero : F.toFun x = 0 := (F.zero_fiber x).mpr hxp
    simpa [hxzero] using (zero_lt_one : (0 : ℝ) < 1)
  · have hxnonzero : F.toFun x ≠ 0 := by
      intro hxzero
      exact hxp ((F.zero_fiber x).mp hxzero)
    have hnorm_pos : 0 < ‖F.toFun x‖ := norm_pos_iff.mpr hxnonzero
    have hlog_neg : Real.log ‖F.toFun x‖ < 0 := by
      rw [F.log_norm_eq x hxp]
      exact neg_neg_of_pos (G.positive_away_pole x hxp)
    have hlt_exp : ‖F.toFun x‖ < Real.exp (0 : ℝ) :=
      (Real.log_lt_iff_lt_exp hnorm_pos).mp hlog_neg
    simpa [Real.exp_zero] using hlt_exp

/--
%%handwave
name:
  Disk maps associated to compact-superlevel Green data
statement:
  A pointed disk map is associated to compact-superlevel Green data when its
  logarithmic modulus is \(-G\) away from the pole, its only zero is the pole,
  and that zero is simple.
-/
def IsCompactSuperlevelGreenFunctionExponentialPointedDiskMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p)
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0) : Prop :=
  (∀ x : X, x ≠ p →
    Real.log ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ = -G.toFun x) ∧
    (∀ x : X, (((F.toFun x : Complex.UnitDisc) : ℂ) = 0) ↔ x = p) ∧
      ∀ χ : PointedSurfaceCoordinate X p,
        surfaceComplexDerivativeInCoordinate χ
          (fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)) ≠ 0

/--
%%handwave
name:
  Associated plane maps package as pointed disk maps
statement:
  A holomorphic plane map associated to compact-superlevel Green data packages
  as a pointed holomorphic map to the unit disk with the expected logarithmic
  modulus, zero fiber, and simple zero.
proof:
  The norm estimate puts the plane map in the unit disk.  The disk-valued map
  is holomorphic because the unit disk has the charted structure induced by
  its open embedding in the complex plane.  The remaining fields are inherited
  from the plane map.
-/
theorem compactSuperlevelGreenFunctionPlaneMap_to_pointedDiskMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (F : CompactSuperlevelGreenFunctionPlaneMap X G) :
    ∃ Φ : PointedHolomorphicMap X Complex.UnitDisc p 0,
      IsCompactSuperlevelGreenFunctionExponentialPointedDiskMap X G Φ := by
  let ΦtoFun : X → Complex.UnitDisc :=
    fun x : X ↦
      Complex.UnitDisc.mk (F.toFun x)
        (compactSuperlevelGreenFunctionPlaneMap_norm_lt_one X G F x)
  have hΦ_holo : HolomorphicMap X Complex.UnitDisc ΦtoFun := by
    refine holomorphicMap_unitDisc_of_coe (F := ΦtoFun) ?_
    simpa [ΦtoFun] using F.holomorphic
  have hΦ_base : ΦtoFun p = 0 := by
    ext
    have hpzero : F.toFun p = 0 := (F.zero_fiber p).mpr rfl
    simp [ΦtoFun, hpzero]
  refine ⟨
    { toFun := ΦtoFun
      holomorphic := hΦ_holo
      base_eq := hΦ_base },
    ?_, ?_, ?_⟩
  · intro x hxp
    simpa [ΦtoFun] using F.log_norm_eq x hxp
  · intro x
    constructor
    · intro hxzero
      apply (F.zero_fiber x).mp
      simpa [ΦtoFun] using hxzero
    · intro hxp
      have hxzero : F.toFun x = 0 := (F.zero_fiber x).mpr hxp
      simp [ΦtoFun, hxzero]
  · intro χ
    simpa [ΦtoFun] using F.simple_zero χ

/--
%%handwave
name:
  Punctured plane maps associated to compact-superlevel Green data
statement:
  A punctured plane map associated to compact-superlevel Green data is a
  holomorphic function on the punctured surface whose logarithmic modulus is
  \(-G\), which has no zeros away from the pole, and whose local form at the
  pole is \((z-z(p))\) times a nonvanishing holomorphic factor.
-/
structure CompactSuperlevelGreenFunctionPuncturedPlaneMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) where
  toFun : X → ℂ
  holomorphic_away_pole :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) toFun {x : X | x ≠ p}
  log_norm_eq : ∀ x : X, x ≠ p → Real.log ‖toFun x‖ = -G.toFun x
  nonzero_away_pole : ∀ x : X, x ≠ p → toFun x ≠ 0
  pole_factorizations :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ r : ℝ,
        0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
          ∃ A : ℂ → ℂ,
            DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
              A (χ.chart p) ≠ 0 ∧
                ∀ z ∈ Metric.ball (χ.chart p) r,
                  z ≠ χ.chart p →
                    toFun (χ.chart.symm z) =
                    (z - χ.chart p) * A z

/--
%%handwave
name:
  Punctured exponential logarithm data for compact-superlevel Green data
statement:
  Punctured exponential logarithm data for compact-superlevel Green data is a
  nonvanishing holomorphic function on the punctured surface whose logarithmic
  modulus is \(-G\), together with local holomorphic logarithms whose real
  parts are \(-G\), and the local first-order factorization at the pole.
-/
structure CompactSuperlevelGreenFunctionPuncturedHolomorphicLog
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) where
  toExp : X → ℂ
  holomorphic_away_pole :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) toExp {x : X | x ≠ p}
  log_norm_eq : ∀ x : X, x ≠ p → Real.log ‖toExp x‖ = -G.toFun x
  nonzero_away_pole : ∀ x : X, x ≠ p → toExp x ≠ 0
  local_holomorphic_logs :
    ∀ x : X, x ≠ p →
      ∃ U : Set X,
        x ∈ U ∧ IsOpen U ∧ U ⊆ {y : X | y ≠ p} ∧
          ∃ L : X → ℂ,
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
              (∀ y ∈ U, (L y).re = -G.toFun y) ∧
                ∀ y ∈ U, toExp y = Complex.exp (L y)
  pole_factorizations :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ r : ℝ,
        0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
          ∃ A : ℂ → ℂ,
            DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
              A (χ.chart p) ≠ 0 ∧
                ∀ z ∈ Metric.ball (χ.chart p) r,
                  z ≠ χ.chart p →
                    toExp (χ.chart.symm z) =
                    (z - χ.chart p) * A z

/--
%%handwave
name:
  Local punctured logarithms for compact-superlevel Green data
statement:
  Local punctured logarithms for compact-superlevel Green data are local
  holomorphic functions on punctured neighborhoods whose real parts are
  \(-G\).
-/
def CompactSuperlevelGreenFunctionLocalPuncturedLogs
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) : Prop :=
  ∀ x : X, x ≠ p →
    ∃ U : Set X,
      x ∈ U ∧ IsOpen U ∧ U ⊆ {y : X | y ≠ p} ∧
        ∃ L : X → ℂ,
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
            ∀ y ∈ U, (L y).re = -G.toFun y

/--
%%handwave
name:
  Chosen punctured logarithm domain
statement:
  From local punctured logarithms, choose one logarithm domain around each
  punctured point.
-/
noncomputable def compactSuperlevelGreenFunctionLocalPuncturedLogDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (q : {x : X // x ≠ p}) : Set X :=
  Classical.choose (hlocal q.1 q.2)

/--
%%handwave
name: Properties of a chosen punctured logarithm domain
statement:
  Given local holomorphic logarithms of $-G$ away from the pole, the chosen domain around each $q\ne p$ contains $q$, is open, avoids $p$, and supports a holomorphic function whose real part is $-G$.
proof:
  These are precisely the properties of the witness selected from the local-existence hypothesis at $q$.
-/
theorem compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (q : {x : X // x ≠ p}) :
    q.1 ∈ compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q ∧
      IsOpen (compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q) ∧
        compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q ⊆
          {y : X | y ≠ p} ∧
          ∃ L : X → ℂ,
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L
              (compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q) ∧
              ∀ y ∈ compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q,
                (L y).re = -G.toFun y :=
  Classical.choose_spec (hlocal q.1 q.2)

/--
%%handwave
name:
  Chosen punctured logarithm
statement:
  From local punctured logarithms, choose one holomorphic logarithm around
  each punctured point.
-/
noncomputable def compactSuperlevelGreenFunctionLocalPuncturedLogFunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (q : {x : X // x ≠ p}) : X → ℂ :=
  Classical.choose
    (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
      hlocal q).2.2.2

/--
%%handwave
name: Properties of a chosen punctured logarithm
statement:
  On the chosen punctured neighborhood of $q\ne p$, the chosen logarithm is holomorphic and has real part $-G$ at every point.
proof:
  Select the function furnished by the chosen-domain specification and retain its two defining properties.
-/
theorem compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (q : {x : X // x ≠ p}) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q)
      (compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q) ∧
      ∀ y ∈ compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q,
        (compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q y).re =
          -G.toFun y :=
  Classical.choose_spec
    (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
      hlocal q).2.2.2

/--
%%handwave
name:
  Compact-superlevel Green data have local punctured logarithms
statement:
  Around every point away from the pole, \(-G\) is the real part of a
  holomorphic function on a punctured neighborhood.
proof:
  Since \(G\) is harmonic away from the pole, so is \(-G\).  Choose a
  coordinate ball contained in the punctured coordinate image and apply the
  planar harmonic-conjugate theorem.  Pull the resulting holomorphic function
  back through the coordinate chart.
-/
theorem compactSuperlevelGreenFunction_has_local_punctured_logs
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    CompactSuperlevelGreenFunctionLocalPuncturedLogs X G := by
  intro x hx_punctured
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hx_source : x ∈ e.source := by
    simp [e]
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' {y : X | y ≠ p}
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm (isOpen_ne (x := p))
  have hexS : e x ∈ S := by
    refine ⟨?_, ?_⟩
    · simp [e]
    · have hsymm : e.symm (e x) = x := e.left_inv hx_source
      simpa [S, hsymm] using hx_punctured
  rcases Metric.isOpen_iff.mp hS_open (e x) hexS with
    ⟨R, hR_pos, hball_subset⟩
  have hneg :
      IsHarmonicOnSurface {y : X | y ≠ p} (fun y : X ↦ -G.toFun y) :=
    harmonicOnSurface_neg G.harmonic_away_pole
  have hcoord_harm :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ -G.toFun (e.symm z)) (Metric.ball (e x) R) :=
    (hneg e he).mono (by
      intro z hz
      exact hball_subset hz)
  rcases hcoord_harm.exists_analyticOnNhd_ball_re_eq with
    ⟨F, hF_hol, hF_re⟩
  let U : Set X := e.source ∩ e ⁻¹' Metric.ball (e x) R
  let L : X → ℂ := fun y : X ↦ F (e y)
  have hU_open : IsOpen U := by
    dsimp [U]
    exact e.isOpen_inter_preimage Metric.isOpen_ball
  have hxU : x ∈ U := by
    refine ⟨hx_source, ?_⟩
    simpa using Metric.mem_ball_self (x := e x) hR_pos
  have hU_punctured : U ⊆ {y : X | y ≠ p} := by
    intro y hy
    have hy_source : y ∈ e.source := hy.1
    have hy_ball : e y ∈ Metric.ball (e x) R := hy.2
    have hey_punctured : e.symm (e y) ≠ p :=
      (hball_subset hy_ball).2
    have hsymm : e.symm (e y) = y := e.left_inv hy_source
    simpa [hsymm] using hey_punctured
  have hL_mdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U := by
    have hchart :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e U :=
      (mdifferentiableOn_atlas (I := 𝓘(ℂ)) he).mono (by
        intro y hy
        exact hy.1)
    have hF_mdiff :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F (Metric.ball (e x) R) := by
      exact mdifferentiableOn_iff_differentiableOn.mpr
        hF_hol.differentiableOn
    have hmaps : U ⊆ e ⁻¹' Metric.ball (e x) R := by
      intro y hy
      exact hy.2
    simpa [L, Function.comp_def] using hF_mdiff.comp hchart hmaps
  refine ⟨U, hxU, hU_open, hU_punctured, L, hL_mdiff, ?_⟩
  intro y hy
  have hy_source : y ∈ e.source := hy.1
  have hy_ball : e y ∈ Metric.ball (e x) R := hy.2
  have hsymm : e.symm (e y) = y := e.left_inv hy_source
  calc
    (L y).re = -G.toFun (e.symm (e y)) := by
      simpa [L] using hF_re hy_ball
    _ = -G.toFun y := by rw [hsymm]

/--
%%handwave
name:
  Local punctured exponentials for compact-superlevel Green data
statement:
  Local punctured exponentials for compact-superlevel Green data are local
  nonvanishing holomorphic functions on punctured neighborhoods whose
  logarithmic moduli are \(-G\).
-/
def CompactSuperlevelGreenFunctionLocalPuncturedExponentials
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) : Prop :=
  ∀ x : X, x ≠ p →
    ∃ U : Set X,
      x ∈ U ∧ IsOpen U ∧ U ⊆ {y : X | y ≠ p} ∧
        ∃ E : X → ℂ,
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) E U ∧
            (∀ y ∈ U, Real.log ‖E y‖ = -G.toFun y) ∧
              ∀ y ∈ U, E y ≠ 0

/--
%%handwave
name:
  Single-valued punctured exponential gluing data
statement:
  Single-valued punctured exponential gluing data consists of a global
  nonvanishing holomorphic function on the punctured surface whose logarithmic
  modulus is \(-G\), compatible local holomorphic logarithms with real part
  \(-G\), and the first-order local factorization at the pole.
-/
structure CompactSuperlevelGreenFunctionPuncturedExponentialGluingData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) where
  toExp : X → ℂ
  holomorphic_away_pole :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) toExp {x : X | x ≠ p}
  log_norm_eq : ∀ x : X, x ≠ p → Real.log ‖toExp x‖ = -G.toFun x
  nonzero_away_pole : ∀ x : X, x ≠ p → toExp x ≠ 0
  local_holomorphic_logs :
    ∀ x : X, x ≠ p →
      ∃ U : Set X,
        x ∈ U ∧ IsOpen U ∧ U ⊆ {y : X | y ≠ p} ∧
          ∃ L : X → ℂ,
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
              (∀ y ∈ U, (L y).re = -G.toFun y) ∧
                ∀ y ∈ U, toExp y = Complex.exp (L y)
  pole_factorizations :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ r : ℝ,
        0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
          ∃ A : ℂ → ℂ,
            DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
              A (χ.chart p) ≠ 0 ∧
                ∀ z ∈ Metric.ball (χ.chart p) r,
                  z ≠ χ.chart p →
                    toExp (χ.chart.symm z) =
                    (z - χ.chart p) * A z

namespace CompactSuperlevelGreenFunctionPuncturedExponentialGluingData

/--
%%handwave
name:
  Gluing data give punctured exponential logarithm data
statement:
  A single-valued punctured exponential with compatible local logarithms and
  the pole factorization packages as punctured exponential logarithm data.
-/
def toPuncturedHolomorphicLog
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (D : CompactSuperlevelGreenFunctionPuncturedExponentialGluingData X G) :
    CompactSuperlevelGreenFunctionPuncturedHolomorphicLog X G where
  toExp := D.toExp
  holomorphic_away_pole := D.holomorphic_away_pole
  log_norm_eq := D.log_norm_eq
  nonzero_away_pole := D.nonzero_away_pole
  local_holomorphic_logs := D.local_holomorphic_logs
  pole_factorizations := D.pole_factorizations

end CompactSuperlevelGreenFunctionPuncturedExponentialGluingData

/--
%%handwave
name:
  Exponential branch-system data
statement:
  Exponential branch-system data for a compact-superlevel Green function is a
  holomorphic local branch system on the surface whose transition group is
  the unit circle acting by multiplication, whose local branches have
  logarithmic modulus \(-G\), whose branches admit local logarithms away from
  the pole, and whose branches through the pole have the first-order local
  zero factorization.
-/
structure CompactSuperlevelGreenFunctionExponentialBranchSystemData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) where
  branchIndex : Type
  system :
    AnalyticContinuation.HolomorphicLocalBranchSystem
      Circle X ℂ branchIndex
  action_eq : ∀ γ : Circle, ∀ z : ℂ, system.act γ z = (γ : ℂ) * z
  transitions : system.HasLocalTransitions
  log_norm_eq :
    ∀ i : branchIndex, ∀ x : X, x ∈ system.domain i →
      x ≠ p → Real.log ‖system.branch i x‖ = -G.toFun x
  nonzero_away_pole :
    ∀ i : branchIndex, ∀ x : X, x ∈ system.domain i →
      x ≠ p → system.branch i x ≠ 0
  local_holomorphic_logs :
    ∀ i : branchIndex, ∀ x : X, x ∈ system.domain i →
      x ≠ p →
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧ U ⊆ system.domain i ∩ {y : X | y ≠ p} ∧
            ∃ L : X → ℂ,
              MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                (∀ y ∈ U, (L y).re = -G.toFun y) ∧
                  ∀ y ∈ U, system.branch i y = Complex.exp (L y)
  pole_factorizations :
    ∀ i : branchIndex, p ∈ system.domain i →
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ r : ℝ,
          0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
            ∃ A : ℂ → ℂ,
              DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
                A (χ.chart p) ≠ 0 ∧
                  ∀ z ∈ Metric.ball (χ.chart p) r,
                    z ≠ χ.chart p →
                      system.branch i (χ.chart.symm z) =
                      (z - χ.chart p) * A z

/--
%%handwave
name:
  Local exponential branch atlas
statement:
  A local exponential branch atlas is an open cover by holomorphic complex
  branches with unit-circle transition constants, logarithmic modulus
  \(-G\) away from the pole, local logarithms on the punctured surface, and
  first-order factorizations for branches through the pole.
-/
structure CompactSuperlevelGreenFunctionLocalExponentialBranchAtlas
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) where
  branchIndex : Type
  domain : branchIndex → Set X
  domain_open : ∀ i : branchIndex, IsOpen (domain i)
  branch : branchIndex → X → ℂ
  branch_holomorphicOn :
    ∀ i : branchIndex,
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (branch i) (domain i)
  covers : ∀ x : X, ∃ i : branchIndex, x ∈ domain i
  local_transition :
    ∀ i j : branchIndex, ∀ x : X, x ∈ domain i ∩ domain j →
      ∃ U : Set X,
        IsOpen U ∧ x ∈ U ∧ U ⊆ domain i ∩ domain j ∧
          ∃ γ : Circle,
            ∀ y : X, y ∈ U → branch j y = (γ : ℂ) * branch i y
  log_norm_eq :
    ∀ i : branchIndex, ∀ x : X, x ∈ domain i →
      x ≠ p → Real.log ‖branch i x‖ = -G.toFun x
  nonzero_away_pole :
    ∀ i : branchIndex, ∀ x : X, x ∈ domain i →
      x ≠ p → branch i x ≠ 0
  local_holomorphic_logs :
    ∀ i : branchIndex, ∀ x : X, x ∈ domain i →
      x ≠ p →
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧ U ⊆ domain i ∩ {y : X | y ≠ p} ∧
            ∃ L : X → ℂ,
              MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                (∀ y ∈ U, (L y).re = -G.toFun y) ∧
                  ∀ y ∈ U, branch i y = Complex.exp (L y)
  pole_factorizations :
    ∀ i : branchIndex, p ∈ domain i →
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ r : ℝ,
          0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
            ∃ A : ℂ → ℂ,
              DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
                A (χ.chart p) ≠ 0 ∧
                  ∀ z ∈ Metric.ball (χ.chart p) r,
                    z ≠ χ.chart p →
                      branch i (χ.chart.symm z) =
                      (z - χ.chart p) * A z

/--
%%handwave
name:
  Pole exponential branch
statement:
  A pole exponential branch is a holomorphic branch through the pole whose
  logarithmic modulus is \(-G\) away from the pole, which admits ordinary
  holomorphic logarithms off the pole, and whose coordinate expression has a
  first-order zero at the pole.
-/
structure CompactSuperlevelGreenFunctionPoleExponentialBranch
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) where
  domain : Set X
  domain_open : IsOpen domain
  mem_domain : p ∈ domain
  branch : X → ℂ
  branch_holomorphicOn :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) branch domain
  log_norm_eq :
    ∀ x : X, x ∈ domain → x ≠ p →
      Real.log ‖branch x‖ = -G.toFun x
  nonzero_away_pole :
    ∀ x : X, x ∈ domain → x ≠ p → branch x ≠ 0
  local_holomorphic_logs :
    ∀ x : X, x ∈ domain → x ≠ p →
      ∃ U : Set X,
        x ∈ U ∧ IsOpen U ∧ U ⊆ domain ∩ {y : X | y ≠ p} ∧
          ∃ L : X → ℂ,
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
              (∀ y ∈ U, (L y).re = -G.toFun y) ∧
                ∀ y ∈ U, branch y = Complex.exp (L y)
  pole_factorizations :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ r : ℝ,
        0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
          ∃ A : ℂ → ℂ,
            DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
              A (χ.chart p) ≠ 0 ∧
                ∀ z ∈ Metric.ball (χ.chart p) r,
                  z ≠ χ.chart p →
                    branch (χ.chart.symm z) =
                    (z - χ.chart p) * A z

/--
%%handwave
name:
  Nonvanishing holomorphic branches have local logarithms
statement:
  A nonvanishing holomorphic branch on an open surface domain admits local
  holomorphic logarithms.  If its logarithmic modulus is a prescribed real
  function \(u\), the real part of the local logarithm is \(u\).
proof:
  At a point where the branch is nonzero, either its value or its negative
  lies in the slit plane.  Shrink the domain so this remains true.  In the
  first case use the principal logarithm; in the second use
  \(\log(-E)+\pi i\).  The exponential identity and the real-part formula
  follow from the principal logarithm identities.
-/
theorem local_holomorphic_logs_of_nonzero_holomorphic_branch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {E : X → ℂ} {u : X → ℝ}
    (hU_open : IsOpen U)
    (hE_hol : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) E U)
    (hE_ne : ∀ x : X, x ∈ U → E x ≠ 0)
    (hlog_norm : ∀ x : X, x ∈ U → Real.log ‖E x‖ = u x) :
    ∀ x : X, x ∈ U →
      ∃ V : Set X,
        x ∈ V ∧ IsOpen V ∧ V ⊆ U ∧
          ∃ L : X → ℂ,
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L V ∧
              (∀ y ∈ V, (L y).re = u y) ∧
                ∀ y ∈ V, E y = Complex.exp (L y) := by
  intro x hxU
  have hx_nonzero : E x ≠ 0 := hE_ne x hxU
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hx_nonzero with
    hx_slit | hx_neg_slit
  · let V : Set X := U ∩ E ⁻¹' Complex.slitPlane
    have hV_open : IsOpen V := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      have hyU : y ∈ U := hy.1
      have hy_slit : E y ∈ Complex.slitPlane := hy.2
      have hE_at :
          MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) E y :=
        hE_hol.mdifferentiableAt (hU_open.mem_nhds hyU)
      have hpre : E ⁻¹' Complex.slitPlane ∈ 𝓝 y :=
        hE_at.continuousAt.preimage_mem_nhds
          (Complex.isOpen_slitPlane.mem_nhds hy_slit)
      exact Filter.inter_mem (hU_open.mem_nhds hyU) hpre
    have hxV : x ∈ V := ⟨hxU, hx_slit⟩
    let L : X → ℂ := fun y : X ↦ Complex.log (E y)
    refine ⟨V, hxV, hV_open, (by intro y hy; exact hy.1), L, ?_, ?_, ?_⟩
    · have hlog_mdiff :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) Complex.log Complex.slitPlane := by
        exact mdifferentiableOn_iff_differentiableOn.mpr
          (differentiableOn_id.clog (fun z hz ↦ hz))
      have hmaps : V ⊆ E ⁻¹' Complex.slitPlane := by
        intro y hy
        exact hy.2
      exact hlog_mdiff.comp (hE_hol.mono (by intro y hy; exact hy.1)) hmaps
    · intro y hy
      simp [L, Complex.log_re, hlog_norm y hy.1]
    · intro y hy
      exact (Complex.exp_log (Complex.slitPlane_ne_zero hy.2)).symm
  · let V : Set X := U ∩ (fun y : X ↦ -E y) ⁻¹' Complex.slitPlane
    have hV_open : IsOpen V := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      have hyU : y ∈ U := hy.1
      have hy_slit : -E y ∈ Complex.slitPlane := hy.2
      have hE_at :
          MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) E y :=
        hE_hol.mdifferentiableAt (hU_open.mem_nhds hyU)
      have hneg_at :
          MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y : X ↦ -E y) y :=
        hE_at.neg
      have hpre : (fun y : X ↦ -E y) ⁻¹' Complex.slitPlane ∈ 𝓝 y :=
        hneg_at.continuousAt.preimage_mem_nhds
          (Complex.isOpen_slitPlane.mem_nhds hy_slit)
      exact Filter.inter_mem (hU_open.mem_nhds hyU) hpre
    have hxV : x ∈ V := ⟨hxU, hx_neg_slit⟩
    let L : X → ℂ :=
      fun y : X ↦ Complex.log (-E y) + (Real.pi : ℂ) * Complex.I
    refine ⟨V, hxV, hV_open, (by intro y hy; exact hy.1), L, ?_, ?_, ?_⟩
    · have hlog_mdiff :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) Complex.log Complex.slitPlane := by
        exact mdifferentiableOn_iff_differentiableOn.mpr
          (differentiableOn_id.clog (fun z hz ↦ hz))
      have hmaps : V ⊆ (fun y : X ↦ -E y) ⁻¹' Complex.slitPlane := by
        intro y hy
        exact hy.2
      have hneg_hol :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun y : X ↦ -E y) V :=
        (hE_hol.mono (by intro y hy; exact hy.1)).neg
      have hlog_comp :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
            (fun y : X ↦ Complex.log (-E y)) V :=
        hlog_mdiff.comp hneg_hol hmaps
      have hconst :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
            (fun _ : X ↦ (Real.pi : ℂ) * Complex.I) V :=
        mdifferentiableOn_const
      exact hlog_comp.add hconst
    · intro y hy
      have hnorm : ‖-E y‖ = ‖E y‖ := norm_neg (E y)
      simp [L, Complex.log_re, hnorm, hlog_norm y hy.1]
    · intro y hy
      have hneg_ne : -E y ≠ 0 :=
        Complex.slitPlane_ne_zero hy.2
      calc
        E y = -(-E y) := by simp
        _ = Complex.exp (Complex.log (-E y) + (Real.pi : ℂ) * Complex.I) := by
          rw [Complex.exp_add, Complex.exp_log hneg_ne,
            Complex.exp_pi_mul_I]
          ring
        _ = Complex.exp (L y) := rfl

/--
%%handwave
name:
  Pole exponential branch from the logarithmic singularity
statement:
  Compact-superlevel Green data determine a pole exponential branch.
proof:
  In a pointed coordinate, the removable logarithmic singularity writes
  \(G+\log|z-z(p)|\) as a harmonic function.  Choose a holomorphic conjugate
  for its negative on a small coordinate ball and set
  \(f=(z-z(p))\exp B\).  This is holomorphic through the pole, has the
  required logarithmic modulus off the pole, and has a simple first-order
  factorization.  The same local factorization transfers to every pointed
  coordinate by holomorphic coordinate changes.
-/
theorem compactSuperlevelGreenFunction_poleExponentialBranch
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    Nonempty (CompactSuperlevelGreenFunctionPoleExponentialBranch X G) := by
  classical
  let χ : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := by simp }
  let z₀ : ℂ := χ.chart p
  rcases G.logarithmic_singularity χ with ⟨H, hH_harm, hH_eq⟩
  have hH_eq_nhds :
      {x : X |
        x ∈ χ.chart.source ∩ {x : X | x ≠ p} →
          G.toFun x + Real.log ‖χ.chart x - χ.chart p‖ = H x} ∈ 𝓝 p := by
    simpa using eventually_nhdsWithin_iff.mp hH_eq
  rcases mem_nhds_iff.mp hH_eq_nhds with
    ⟨W, hW_subset, hW_open, hpW⟩
  let Scoord : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' W
  have hScoord_open : IsOpen Scoord := by
    simpa [Scoord] using χ.chart.isOpen_inter_preimage_symm hW_open
  have hz₀_Scoord : z₀ ∈ Scoord := by
    refine ⟨?_, ?_⟩
    · exact χ.chart.map_source χ.base_mem_source
    · simpa [z₀, χ.chart.left_inv χ.base_mem_source] using hpW
  rcases Metric.isOpen_iff.mp hScoord_open z₀ hz₀_Scoord with
    ⟨R, hR_pos, hball_subset_Scoord⟩
  let B : Set ℂ := Metric.ball z₀ R
  have hB_open : IsOpen B := by
    simp [B]
  have hB_target : B ⊆ χ.chart.target := by
    intro z hz
    exact (hball_subset_Scoord (by simpa [B] using hz)).1
  have hB_W : ∀ z ∈ B, χ.chart.symm z ∈ W := by
    intro z hz
    exact (hball_subset_Scoord (by simpa [B] using hz)).2
  have hneg_harm :
      IsHarmonicOnSurface χ.chart.source (fun x : X ↦ -H x) :=
    harmonicOnSurface_neg hH_harm
  have hcoord_harm :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ -H (χ.chart.symm z)) B :=
    (hneg_harm χ.chart χ.chart_mem_atlas).mono (by
      intro z hz
      exact ⟨hB_target hz, χ.chart.map_target (hB_target hz)⟩)
  rcases hcoord_harm.exists_analyticOnNhd_ball_re_eq with
    ⟨F, hF_hol, hF_re⟩
  let domain : Set X := χ.chart.source ∩ χ.chart ⁻¹' B
  let branch : X → ℂ := fun x : X ↦
    (χ.chart x - z₀) * Complex.exp (F (χ.chart x))
  have hdomain_open : IsOpen domain := by
    dsimp [domain]
    exact χ.chart.isOpen_inter_preimage hB_open
  have hp_domain : p ∈ domain := by
    refine ⟨χ.base_mem_source, ?_⟩
    simpa [B, z₀] using Metric.mem_ball_self (x := z₀) hR_pos
  have hbranch_hol :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) branch domain := by
    let C : ℂ → ℂ := fun z : ℂ ↦ (z - z₀) * Complex.exp (F z)
    have hC_diff : DifferentiableOn ℂ C B := by
      dsimp [C]
      exact (differentiableOn_id.sub_const z₀).mul
        hF_hol.differentiableOn.cexp
    have hC_mdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) C B :=
      mdifferentiableOn_iff_differentiableOn.mpr hC_diff
    have hchart :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) χ.chart domain :=
      (mdifferentiableOn_atlas (I := 𝓘(ℂ)) χ.chart_mem_atlas).mono
        (by intro x hx; exact hx.1)
    have hmaps : domain ⊆ χ.chart ⁻¹' B := by
      intro x hx
      exact hx.2
    simpa [branch, C, Function.comp_def] using hC_mdiff.comp hchart hmaps
  have hlog_norm :
      ∀ x : X, x ∈ domain → x ≠ p →
        Real.log ‖branch x‖ = -G.toFun x := by
    intro x hx hx_ne
    have hx_source : x ∈ χ.chart.source := hx.1
    have hxB : χ.chart x ∈ B := hx.2
    have hxW : x ∈ W := by
      have hsymm : χ.chart.symm (χ.chart x) = x :=
        χ.chart.left_inv hx_source
      simpa [hsymm] using hB_W (χ.chart x) hxB
    have hregular :
        G.toFun x + Real.log ‖χ.chart x - χ.chart p‖ = H x :=
      hW_subset hxW ⟨hx_source, hx_ne⟩
    have hcoord_ne : χ.chart x - z₀ ≠ 0 := by
      intro hzero
      have hx_eq : χ.chart x = χ.chart p := by
        simpa [sub_eq_zero, z₀] using hzero
      exact hx_ne (χ.chart.injOn hx_source χ.base_mem_source hx_eq)
    have hcoord_pos : 0 < ‖χ.chart x - z₀‖ :=
      norm_pos_iff.mpr hcoord_ne
    have hexp_pos : 0 < Real.exp (F (χ.chart x)).re :=
      Real.exp_pos _
    have hF_re_x : (F (χ.chart x)).re = -H x := by
      have hsymm : χ.chart.symm (χ.chart x) = x :=
        χ.chart.left_inv hx_source
      simpa [hsymm] using hF_re hxB
    calc
      Real.log ‖branch x‖ =
          Real.log (‖χ.chart x - z₀‖ *
            ‖Complex.exp (F (χ.chart x))‖) := by
        simp [branch]
      _ = Real.log (‖χ.chart x - z₀‖ *
            Real.exp (F (χ.chart x)).re) := by
        rw [Complex.norm_exp]
      _ = Real.log ‖χ.chart x - z₀‖ + (F (χ.chart x)).re := by
        rw [Real.log_mul hcoord_pos.ne' hexp_pos.ne', Real.log_exp]
      _ = Real.log ‖χ.chart x - χ.chart p‖ - H x := by
        rw [hF_re_x]
        ring
      _ = -G.toFun x := by
        linarith
  have hnonzero :
      ∀ x : X, x ∈ domain → x ≠ p → branch x ≠ 0 := by
    intro x hx hx_ne
    have hx_source : x ∈ χ.chart.source := hx.1
    have hcoord_ne : χ.chart x - z₀ ≠ 0 := by
      intro hzero
      have hx_eq : χ.chart x = χ.chart p := by
        simpa [sub_eq_zero, z₀] using hzero
      exact hx_ne (χ.chart.injOn hx_source χ.base_mem_source hx_eq)
    exact mul_ne_zero hcoord_ne (Complex.exp_ne_zero (F (χ.chart x)))
  have hlocal_logs :
      ∀ x : X, x ∈ domain → x ≠ p →
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧ U ⊆ domain ∩ {y : X | y ≠ p} ∧
            ∃ L : X → ℂ,
              MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                (∀ y ∈ U, (L y).re = -G.toFun y) ∧
                  ∀ y ∈ U, branch y = Complex.exp (L y) := by
    let U₀ : Set X := domain ∩ {y : X | y ≠ p}
    have hU₀_open : IsOpen U₀ :=
      hdomain_open.inter (isOpen_ne (x := p))
    have hbranch_U₀ :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) branch U₀ :=
      hbranch_hol.mono (by intro y hy; exact hy.1)
    have hnonzero_U₀ : ∀ y : X, y ∈ U₀ → branch y ≠ 0 := by
      intro y hy
      exact hnonzero y hy.1 hy.2
    have hlog_U₀ : ∀ y : X, y ∈ U₀ → Real.log ‖branch y‖ = -G.toFun y := by
      intro y hy
      exact hlog_norm y hy.1 hy.2
    have hhelper :=
      local_holomorphic_logs_of_nonzero_holomorphic_branch
        hU₀_open hbranch_U₀ hnonzero_U₀ hlog_U₀
    intro x hx hx_ne
    exact hhelper x ⟨hx, hx_ne⟩
  have hfactor :
      ∀ ψ : PointedSurfaceCoordinate X p,
        ∃ r : ℝ,
          0 < r ∧ Metric.ball (ψ.chart p) r ⊆ ψ.chart.target ∧
            ∃ A : ℂ → ℂ,
              DifferentiableOn ℂ A (Metric.ball (ψ.chart p) r) ∧
                A (ψ.chart p) ≠ 0 ∧
                  ∀ z ∈ Metric.ball (ψ.chart p) r,
                    z ≠ ψ.chart p →
                      branch (ψ.chart.symm z) =
                      (z - ψ.chart p) * A z := by
    intro ψ
    let w₀ : ℂ := ψ.chart p
    let T : ℂ → ℂ := fun z : ℂ ↦ χ.chart (ψ.chart.symm z)
    let q : ℂ → ℂ := dslope T w₀
    have hw₀_target : w₀ ∈ ψ.chart.target := by
      dsimp [w₀]
      exact ψ.chart.map_source ψ.base_mem_source
    have hw₀_sourceχ : ψ.chart.symm w₀ ∈ χ.chart.source := by
      dsimp [w₀]
      simpa [ψ.chart.left_inv ψ.base_mem_source] using χ.base_mem_source
    have hT_w₀ : T w₀ = z₀ := by
      dsimp [T, w₀, z₀]
      rw [ψ.chart.left_inv ψ.base_mem_source]
    have hT_an : AnalyticAt ℂ T w₀ := by
      dsimp [T, w₀]
      exact chartTransition_analyticAt ψ.chart ψ.chart_mem_atlas
        χ.chart χ.chart_mem_atlas hw₀_target hw₀_sourceχ
    rcases hT_an.exists_ball_analyticOnNhd with
      ⟨rT, hrT_pos, hT_hol⟩
    have hpre_B : T ⁻¹' B ∈ 𝓝 w₀ := by
      have hT_cont : ContinuousAt T w₀ := hT_an.differentiableAt.continuousAt
      have hTw₀B : T w₀ ∈ B := by
        rw [hT_w₀]
        simpa [B] using Metric.mem_ball_self (x := z₀) hR_pos
      exact hT_cont.preimage_mem_nhds (hB_open.mem_nhds hTw₀B)
    have htarget_nhds : ψ.chart.target ∈ 𝓝 w₀ :=
      ψ.chart.open_target.mem_nhds hw₀_target
    have hballT_nhds : Metric.ball w₀ rT ∈ 𝓝 w₀ :=
      Metric.ball_mem_nhds w₀ hrT_pos
    have hgood_nhds :
        ψ.chart.target ∩ (T ⁻¹' B ∩ Metric.ball w₀ rT) ∈ 𝓝 w₀ :=
      Filter.inter_mem htarget_nhds (Filter.inter_mem hpre_B hballT_nhds)
    rcases Metric.mem_nhds_iff.mp hgood_nhds with
      ⟨r, hr_pos, hball_good⟩
    have hball_target : Metric.ball w₀ r ⊆ ψ.chart.target := by
      intro z hz
      exact (hball_good hz).1
    have hball_T_B : ∀ z ∈ Metric.ball w₀ r, T z ∈ B := by
      intro z hz
      exact (hball_good hz).2.1
    have hball_T_hol : Metric.ball w₀ r ⊆ Metric.ball w₀ rT := by
      intro z hz
      exact (hball_good hz).2.2
    let A : ℂ → ℂ := fun z : ℂ ↦ q z * Complex.exp (F (T z))
    have hT_diff :
        DifferentiableOn ℂ T (Metric.ball w₀ r) :=
      hT_hol.differentiableOn.mono hball_T_hol
    have hq_diff :
        DifferentiableOn ℂ q (Metric.ball w₀ r) := by
      exact (Complex.differentiableOn_dslope
        (Metric.ball_mem_nhds w₀ hr_pos)).mpr hT_diff
    have hF_comp_diff :
        DifferentiableOn ℂ (fun z : ℂ ↦ F (T z)) (Metric.ball w₀ r) :=
      hF_hol.differentiableOn.comp hT_diff (by
        intro z hz
        exact hball_T_B z hz)
    have hA_diff :
        DifferentiableOn ℂ A (Metric.ball w₀ r) := by
      dsimp [A]
      exact hq_diff.mul hF_comp_diff.cexp
    have hq_w₀_ne : q w₀ ≠ 0 := by
      dsimp [q, T, w₀]
      simpa [dslope_same] using
        pointedCoordinate_transition_deriv_ne_zero X χ ψ
    have hA_ne : A w₀ ≠ 0 := by
      dsimp [A]
      rw [hT_w₀]
      exact mul_ne_zero hq_w₀_ne (Complex.exp_ne_zero (F z₀))
    refine ⟨r, hr_pos, by simpa [w₀] using hball_target, A, hA_diff, ?_, ?_⟩
    · simpa [w₀] using hA_ne
    · intro z hz hz_ne
      have hz_target : z ∈ ψ.chart.target := hball_target hz
      have hsymm_source : ψ.chart.symm z ∈ ψ.chart.source :=
        ψ.chart.map_target hz_target
      have hTz_B : T z ∈ B := hball_T_B z hz
      have hT_factor :
          T z - z₀ = (z - w₀) * q z := by
        have h := sub_smul_dslope T w₀ z
        simpa [q, smul_eq_mul, hT_w₀] using h.symm
      calc
        branch (ψ.chart.symm z) =
            (T z - z₀) * Complex.exp (F (T z)) := by
          simp [branch, T]
        _ = ((z - w₀) * q z) * Complex.exp (F (T z)) := by
          rw [hT_factor]
        _ = (z - w₀) * A z := by
          ring
        _ = (z - ψ.chart p) * A z := by
          simp [w₀]
  refine ⟨
    { domain := domain
      domain_open := hdomain_open
      mem_domain := hp_domain
      branch := branch
      branch_holomorphicOn := hbranch_hol
      log_norm_eq := hlog_norm
      nonzero_away_pole := hnonzero
      local_holomorphic_logs := hlocal_logs
      pole_factorizations := hfactor }⟩

/-- Branch labels for the pole branch together with one punctured branch at each punctured point. -/
abbrev CompactSuperlevelGreenFunctionLocalExponentialBranchIndex
    (X : Type) (p : X) : Type :=
  Unit ⊕ {x : X // x ≠ p}

/-- The concrete domain family associated to a pole branch and chosen punctured logarithms. -/
noncomputable def compactSuperlevelGreenFunctionPolePuncturedBranchDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G) :
    CompactSuperlevelGreenFunctionLocalExponentialBranchIndex X p → Set X
  | Sum.inl _ => P.domain
  | Sum.inr q => compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q

/-- The concrete branch family associated to a pole branch and chosen punctured logarithms. -/
noncomputable def compactSuperlevelGreenFunctionPolePuncturedBranch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G) :
    CompactSuperlevelGreenFunctionLocalExponentialBranchIndex X p → X → ℂ
  | Sum.inl _ => P.branch
  | Sum.inr q =>
      fun y : X ↦
        Complex.exp
          (compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q y)

/--
%%handwave
name:
  Local circle transitions for pole and punctured exponential branches
statement:
  The pole branch and the punctured exponential branches have local
  unit-circle transition constants on every overlap.
proof:
  Away from the pole, choose a small coordinate disk inside the overlap.  The
  local holomorphic logarithms of the two branches have the same real part
  \(-G\), so they differ by an imaginary constant; exponentiating gives a
  unit-circle factor.  At the pole, only the pole branch occurs, and the
  transition is the identity.
-/
def CompactSuperlevelGreenFunctionPolePuncturedBranchesHaveLocalCircleTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G) : Prop :=
  ∀ i j : CompactSuperlevelGreenFunctionLocalExponentialBranchIndex X p,
    ∀ x : X,
      x ∈ compactSuperlevelGreenFunctionPolePuncturedBranchDomain P hlocal i ∩
          compactSuperlevelGreenFunctionPolePuncturedBranchDomain P hlocal j →
        ∃ U : Set X,
          IsOpen U ∧ x ∈ U ∧
            U ⊆ compactSuperlevelGreenFunctionPolePuncturedBranchDomain P hlocal i ∩
                compactSuperlevelGreenFunctionPolePuncturedBranchDomain P hlocal j ∧
              ∃ γ : Circle,
                ∀ y : X, y ∈ U →
                  compactSuperlevelGreenFunctionPolePuncturedBranch P hlocal j y =
                    (γ : ℂ) *
                      compactSuperlevelGreenFunctionPolePuncturedBranch P hlocal i y

/--
%%handwave
name:
  Equal real-part logarithms give a circle transition
statement:
  If two holomorphic logarithms on overlapping surface neighborhoods have the
  same real part and exponentiate to two branches, then near any overlap point
  the branches differ by multiplication by a unit complex constant.
proof:
  Shrink to a connected coordinate disk inside the overlap.  Pull both
  logarithms to the disk.  Since their real parts agree there, the plane
  imaginary-constant lemma gives \(L_2=L_1+ic\).  Exponentiating gives the
  transition factor \(\exp(ic)\), which lies on the unit circle.
-/
theorem local_circle_transition_of_holomorphic_logs
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {u : X → ℝ} {U₁ U₂ : Set X}
    {L₁ L₂ E₁ E₂ : X → ℂ} {x : X}
    (hU₁_open : IsOpen U₁) (hU₂_open : IsOpen U₂)
    (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂)
    (hL₁ : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L₁ U₁)
    (hL₂ : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L₂ U₂)
    (hL₁_re : ∀ y ∈ U₁, (L₁ y).re = u y)
    (hL₂_re : ∀ y ∈ U₂, (L₂ y).re = u y)
    (hE₁ : ∀ y ∈ U₁, E₁ y = Complex.exp (L₁ y))
    (hE₂ : ∀ y ∈ U₂, E₂ y = Complex.exp (L₂ y)) :
    ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ V ⊆ U₁ ∩ U₂ ∧
        ∃ γ : Circle, ∀ y : X, y ∈ V → E₂ y = (γ : ℂ) * E₁ y := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hx_source : x ∈ e.source := by
    simp [e]
  let Scoord : Set ℂ := e.target ∩ e.symm ⁻¹' (U₁ ∩ U₂)
  have hScoord_open : IsOpen Scoord := by
    simpa [Scoord] using e.isOpen_inter_preimage_symm
      (hU₁_open.inter hU₂_open)
  have hz0_Scoord : e x ∈ Scoord := by
    refine ⟨?_, ?_⟩
    · simp [e]
    · have hsymm : e.symm (e x) = x := e.left_inv hx_source
      simpa [Scoord, hsymm] using ⟨hx₁, hx₂⟩
  rcases Metric.isOpen_iff.mp hScoord_open (e x) hz0_Scoord with
    ⟨R, hR_pos, hball_subset⟩
  let B : Set ℂ := Metric.ball (e x) R
  have hB_open : IsOpen B := by
    simp [B]
  have hB_connected : IsConnected B := by
    simpa [B] using Metric.isConnected_ball (x := e x) hR_pos
  have hB_target : B ⊆ e.target := by
    intro z hz
    exact (hball_subset (by simpa [B] using hz)).1
  have hsymm_mdiff :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm B :=
    (mdifferentiableOn_atlas_symm (I := 𝓘(ℂ)) he).mono hB_target
  have hmaps₁ : B ⊆ e.symm ⁻¹' U₁ := by
    intro z hz
    exact (hball_subset (by simpa [B] using hz)).2.1
  have hmaps₂ : B ⊆ e.symm ⁻¹' U₂ := by
    intro z hz
    exact (hball_subset (by simpa [B] using hz)).2.2
  let F₁ : ℂ → ℂ := fun z : ℂ ↦ L₁ (e.symm z)
  let F₂ : ℂ → ℂ := fun z : ℂ ↦ L₂ (e.symm z)
  have hF₁_mdiff :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F₁ B := by
    simpa [F₁, Function.comp_def] using hL₁.comp hsymm_mdiff hmaps₁
  have hF₂_mdiff :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F₂ B := by
    simpa [F₂, Function.comp_def] using hL₂.comp hsymm_mdiff hmaps₂
  have hF₁_hol : AnalyticOnNhd ℂ F₁ B := by
    exact (Complex.analyticOnNhd_iff_differentiableOn hB_open).2
      (mdifferentiableOn_iff_differentiableOn.mp hF₁_mdiff)
  have hF₂_hol : AnalyticOnNhd ℂ F₂ B := by
    exact (Complex.analyticOnNhd_iff_differentiableOn hB_open).2
      (mdifferentiableOn_iff_differentiableOn.mp hF₂_mdiff)
  have hre : ∀ z ∈ B, (F₂ z).re = (F₁ z).re := by
    intro z hz
    calc
      (F₂ z).re = u (e.symm z) := hL₂_re (e.symm z) (hmaps₂ hz)
      _ = (F₁ z).re := (hL₁_re (e.symm z) (hmaps₁ hz)).symm
  rcases analyticOnNhd_eq_add_imaginary_constant_of_re_eq
      hF₂_hol hF₁_hol hB_open hB_connected hre with
    ⟨c, hc⟩
  let V : Set X := e.source ∩ e ⁻¹' B
  have hV_open : IsOpen V := by
    dsimp [V]
    exact e.isOpen_inter_preimage hB_open
  have hxV : x ∈ V := by
    refine ⟨hx_source, ?_⟩
    simpa [B] using Metric.mem_ball_self (x := e x) hR_pos
  have hV_subset : V ⊆ U₁ ∩ U₂ := by
    intro y hy
    have hy_source : y ∈ e.source := hy.1
    have hyB : e y ∈ B := hy.2
    have hsymm : e.symm (e y) = y := e.left_inv hy_source
    exact
      ⟨by simpa [hsymm] using hmaps₁ hyB,
        by simpa [hsymm] using hmaps₂ hyB⟩
  refine ⟨V, hV_open, hxV, hV_subset, Circle.exp c, ?_⟩
  intro y hy
  have hyU₁ : y ∈ U₁ := (hV_subset hy).1
  have hyU₂ : y ∈ U₂ := (hV_subset hy).2
  have hy_source : y ∈ e.source := hy.1
  have hyB : e y ∈ B := hy.2
  have hsymm : e.symm (e y) = y := e.left_inv hy_source
  have hlogs :
      L₂ y = L₁ y + c * Complex.I := by
    have hlocal := hc (e y) hyB
    simpa [F₁, F₂, hsymm] using hlocal
  calc
    E₂ y = Complex.exp (L₂ y) := hE₂ y hyU₂
    _ = Complex.exp (L₁ y + c * Complex.I) := by rw [hlogs]
    _ = (Circle.exp c : ℂ) * E₁ y := by
      rw [Complex.exp_add, Circle.coe_exp, hE₁ y hyU₁]
      ring
/--
%%handwave
name:
  Circle transitions among the pole and punctured exponential branches
statement:
  Let \(X\) be a Riemann surface, let \(G\) be a compact-superlevel Green
  function with pole \(p\), choose an exponential branch \(P\) near \(p\),
  and choose local holomorphic logarithms with real part \(-G\) at every
  point of \(X\setminus\{p\}\).  For any two resulting exponential branches
  and any point \(x\) in the overlap of their domains, there are an open
  neighborhood \(U\) of \(x\) in the overlap and \(\gamma\in S^1\) such that
  \(E_j(y)=\gamma E_i(y)\) for every \(y\in U\).
proof:
  If \(x=p\), both branch labels must denote the pole branch, so take
  \(\gamma=1\).  If \(x\ne p\), obtain a local holomorphic logarithm for each
  branch, both with real part \(-G\), and use [two exponentials of holomorphic logarithms with equal real parts differ locally by a unit complex constant](lean:JJMath.Uniformization.local_circle_transition_of_holomorphic_logs).
-/
theorem compactSuperlevelGreenFunction_polePuncturedBranches_haveLocalCircleTransitions
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G) :
    CompactSuperlevelGreenFunctionPolePuncturedBranchesHaveLocalCircleTransitions
      P hlocal := by
  intro i j x hx
  by_cases hxp : x = p
  · subst hxp
    cases i with
    | inl _ =>
        cases j with
        | inl _ =>
            refine ⟨P.domain, P.domain_open, P.mem_domain, ?_, 1, ?_⟩
            · intro y hy
              simp [compactSuperlevelGreenFunctionPolePuncturedBranchDomain,
                hy]
            · intro y hy
              simp [compactSuperlevelGreenFunctionPolePuncturedBranch]
        | inr q =>
            have hp_ne :=
              (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
                hlocal q).2.2.1 hx.2
            exact False.elim (hp_ne rfl)
    | inr q =>
        have hp_ne :=
          (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
            hlocal q).2.2.1 hx.1
        exact False.elim (hp_ne rfl)
  · have hi_log :
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧
            U ⊆ compactSuperlevelGreenFunctionPolePuncturedBranchDomain P hlocal i ∩
                {y : X | y ≠ p} ∧
              ∃ L : X → ℂ,
                MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                  (∀ y ∈ U, (L y).re = -G.toFun y) ∧
                    ∀ y ∈ U,
                      compactSuperlevelGreenFunctionPolePuncturedBranch P hlocal i y =
                        Complex.exp (L y) := by
      cases i with
      | inl _ =>
          simpa [compactSuperlevelGreenFunctionPolePuncturedBranch,
            compactSuperlevelGreenFunctionPolePuncturedBranchDomain] using
            P.local_holomorphic_logs x hx.1 hxp
      | inr q =>
          refine
            ⟨compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q,
              hx.1,
              (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
                hlocal q).2.1,
              ?_,
              compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q,
              (compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
                hlocal q).1,
              (compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
                hlocal q).2,
              ?_⟩
          · intro y hy
            exact
              ⟨hy,
                (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
                  hlocal q).2.2.1 hy⟩
          · intro y hy
            rfl
    have hj_log :
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧
            U ⊆ compactSuperlevelGreenFunctionPolePuncturedBranchDomain P hlocal j ∩
                {y : X | y ≠ p} ∧
              ∃ L : X → ℂ,
                MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                  (∀ y ∈ U, (L y).re = -G.toFun y) ∧
                    ∀ y ∈ U,
                      compactSuperlevelGreenFunctionPolePuncturedBranch P hlocal j y =
                        Complex.exp (L y) := by
      cases j with
      | inl _ =>
          simpa [compactSuperlevelGreenFunctionPolePuncturedBranch,
            compactSuperlevelGreenFunctionPolePuncturedBranchDomain] using
            P.local_holomorphic_logs x hx.2 hxp
      | inr q =>
          refine
            ⟨compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q,
              hx.2,
              (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
                hlocal q).2.1,
              ?_,
              compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q,
              (compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
                hlocal q).1,
              (compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
                hlocal q).2,
              ?_⟩
          · intro y hy
            exact
              ⟨hy,
                (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
                  hlocal q).2.2.1 hy⟩
          · intro y hy
            rfl
    rcases hi_log with
      ⟨Uᵢ, hxUᵢ, hUᵢ_open, hUᵢ_subset, Lᵢ, hLᵢ, hLᵢ_re, hbranchᵢ⟩
    rcases hj_log with
      ⟨Uⱼ, hxUⱼ, hUⱼ_open, hUⱼ_subset, Lⱼ, hLⱼ, hLⱼ_re, hbranchⱼ⟩
    rcases
      local_circle_transition_of_holomorphic_logs
        (u := fun y : X ↦ -G.toFun y)
        (U₁ := Uᵢ) (U₂ := Uⱼ)
        (L₁ := Lᵢ) (L₂ := Lⱼ)
        (E₁ := compactSuperlevelGreenFunctionPolePuncturedBranch P hlocal i)
        (E₂ := compactSuperlevelGreenFunctionPolePuncturedBranch P hlocal j)
        hUᵢ_open hUⱼ_open hxUᵢ hxUⱼ
        hLᵢ hLⱼ hLᵢ_re hLⱼ_re hbranchᵢ hbranchⱼ with
      ⟨V, hV_open, hxV, hV_subset_logs, γ, hγ⟩
    refine ⟨V, hV_open, hxV, ?_, γ, hγ⟩
    intro y hy
    have hy_logs : y ∈ Uᵢ ∩ Uⱼ := hV_subset_logs hy
    exact ⟨(hUᵢ_subset hy_logs.1).1, (hUⱼ_subset hy_logs.2).1⟩

namespace CompactSuperlevelGreenFunctionLocalExponentialBranchAtlas

/--
%%handwave
name:
  Local exponential branch atlases give branch-system data
statement:
  A local exponential branch atlas canonically packages as exponential
  branch-system data, with the unit circle acting by multiplication.
-/
def toExponentialBranchSystemData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (A : CompactSuperlevelGreenFunctionLocalExponentialBranchAtlas X G) :
    CompactSuperlevelGreenFunctionExponentialBranchSystemData X G := by
  classical
  let S :
      AnalyticContinuation.HolomorphicLocalBranchSystem
        Circle X ℂ A.branchIndex :=
    { act := fun γ z ↦ (γ : ℂ) * z
      act_holomorphic := by
        intro γ
        exact mdifferentiable_iff_differentiable.mpr
          ((differentiable_const (γ : ℂ)).mul differentiable_id)
      act_one := by
        intro z
        simp
      act_mul := by
        intro γ δ z
        simp [mul_assoc]
      domain := A.domain
      domain_open := A.domain_open
      branch := A.branch
      branch_holomorphicOn := A.branch_holomorphicOn
      covers := A.covers }
  refine
    { branchIndex := A.branchIndex
      system := S
      action_eq := ?_
      transitions := ?_
      log_norm_eq := ?_
      nonzero_away_pole := ?_
      local_holomorphic_logs := ?_
      pole_factorizations := ?_ }
  · intro γ z
    rfl
  · intro i j x hx
    rcases A.local_transition i j x hx with
      ⟨U, hU_open, hxU, hU_subset, γ, hγ⟩
    exact ⟨
      { neighborhood := U
        neighborhood_open := hU_open
        mem_neighborhood := hxU
        subset_overlap := hU_subset
        transition := γ
        transition_eq := by
          intro y hy
          exact hγ y hy }⟩
  · exact A.log_norm_eq
  · exact A.nonzero_away_pole
  · exact A.local_holomorphic_logs
  · exact A.pole_factorizations

end CompactSuperlevelGreenFunctionLocalExponentialBranchAtlas

namespace CompactSuperlevelGreenFunctionExponentialBranchSystemData

/--
%%handwave
name:
  Branch-system data give punctured exponential gluing data
statement:
  On a simply connected surface, exponential branch-system data determine a
  single-valued punctured exponential with compatible local logarithms and
  the first-order pole factorization.
proof:
  Apply the simply connected continuation theorem for holomorphic local
  branch systems.  Local agreement with a branch transfers the logarithmic
  modulus and nonvanishing because the transition constants have modulus one.
  Local logarithms are adjusted by an imaginary constant representing the
  unit transition.  Near the pole, the global continuation agrees with a unit
  multiple of a branch through the pole, so the branch's first-order
  factorization is multiplied by the same nonzero constant.
-/
theorem toPuncturedExponentialGluingData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (D : CompactSuperlevelGreenFunctionExponentialBranchSystemData X G) :
    Nonempty
      (CompactSuperlevelGreenFunctionPuncturedExponentialGluingData X G) := by
  classical
  let S := D.system
  rcases
    AnalyticContinuation.HolomorphicLocalBranchSystem.exists_singleValuedContinuation_of_simplyConnected_localTransitions
        (S := S) D.transitions with
    ⟨C⟩
  refine ⟨
    { toExp := C.global
      holomorphic_away_pole := ?_
      log_norm_eq := ?_
      nonzero_away_pole := ?_
      local_holomorphic_logs := ?_
      pole_factorizations := ?_ }⟩
  · exact
      (AnalyticContinuation.HolomorphicLocalBranchSystem.SingleValuedContinuation.mdifferentiable
        (S := S) C).mdifferentiableOn
  · intro x hxp
    rcases C.local_agreement x with
      ⟨U, _hU_open, hxU, i, γ, hU_domain, hglobal_eq⟩
    have hx_domain : x ∈ S.domain i := hU_domain hxU
    have hglobal :
        C.global x = (γ : ℂ) * S.branch i x := by
      rw [hglobal_eq x hxU, D.action_eq γ (S.branch i x)]
    calc
      Real.log ‖C.global x‖ =
          Real.log ‖(γ : ℂ) * S.branch i x‖ := by
        rw [hglobal]
      _ = Real.log ‖S.branch i x‖ := by
        rw [norm_mul, Circle.norm_coe, one_mul]
      _ = -G.toFun x := D.log_norm_eq i x hx_domain hxp
  · intro x hxp
    rcases C.local_agreement x with
      ⟨U, _hU_open, hxU, i, γ, hU_domain, hglobal_eq⟩
    have hx_domain : x ∈ S.domain i := hU_domain hxU
    have hglobal :
        C.global x = (γ : ℂ) * S.branch i x := by
      rw [hglobal_eq x hxU, D.action_eq γ (S.branch i x)]
    rw [hglobal]
    exact mul_ne_zero (Circle.coe_ne_zero γ)
      (D.nonzero_away_pole i x hx_domain hxp)
  · intro x hxp
    rcases C.local_agreement x with
      ⟨V, hV_open, hxV, i, γ, hV_domain, hglobal_eq⟩
    have hx_domain : x ∈ S.domain i := hV_domain hxV
    rcases D.local_holomorphic_logs i x hx_domain hxp with
      ⟨U, hxU, hU_open, hU_subset, L₀, hL₀_hol, hL₀_re, hbranch_exp⟩
    have hγ_norm : ‖(γ : ℂ)‖ = 1 := Circle.norm_coe γ
    rcases (Complex.norm_eq_one_iff (γ : ℂ)).mp hγ_norm with
      ⟨θ, hθ⟩
    let W : Set X := U ∩ V
    let L : X → ℂ := fun y : X ↦ L₀ y + θ * Complex.I
    refine ⟨W, ⟨hxU, hxV⟩, hU_open.inter hV_open, ?_, L, ?_, ?_, ?_⟩
    · intro y hy
      exact (hU_subset hy.1).2
    · have hconst : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
          (fun _ : X ↦ θ * Complex.I) W :=
        mdifferentiableOn_const
      exact (hL₀_hol.mono (by intro y hy; exact hy.1)).add hconst
    · intro y hy
      simp [L, hL₀_re y hy.1]
    · intro y hy
      have hyV : y ∈ V := hy.2
      have hglobal :
          C.global y = (γ : ℂ) * S.branch i y := by
        rw [hglobal_eq y hyV, D.action_eq γ (S.branch i y)]
      calc
        C.global y = (γ : ℂ) * S.branch i y := hglobal
        _ = Complex.exp (θ * Complex.I) * Complex.exp (L₀ y) := by
          rw [hθ, hbranch_exp y hy.1]
        _ = Complex.exp (L y) := by
          simp [L, Complex.exp_add, mul_comm]
  · intro χ
    rcases C.local_agreement p with
      ⟨U, hU_open, hpU, i, γ, hU_domain, hglobal_eq⟩
    have hp_domain : p ∈ S.domain i := hU_domain hpU
    rcases D.pole_factorizations i hp_domain χ with
      ⟨r₀, hr₀_pos, hball₀_target, A, hA_diff, hA_ne, hA_factor⟩
    let V : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' U
    have hV_open : IsOpen V := by
      simpa [V] using χ.chart.isOpen_inter_preimage_symm hU_open
    have hpV : χ.chart p ∈ V := by
      refine ⟨?_, ?_⟩
      · exact χ.chart.map_source χ.base_mem_source
      · simpa [V, χ.chart.left_inv χ.base_mem_source] using hpU
    rcases Metric.isOpen_iff.mp hV_open (χ.chart p) hpV with
      ⟨r₁, hr₁_pos, hball₁_subset⟩
    let r : ℝ := min r₀ r₁
    have hr_pos : 0 < r := lt_min hr₀_pos hr₁_pos
    have hball_target : Metric.ball (χ.chart p) r ⊆ χ.chart.target := by
      intro z hz
      exact hball₀_target (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left r₀ r₁)))
    let A' : ℂ → ℂ := fun z : ℂ ↦ (γ : ℂ) * A z
    refine ⟨r, hr_pos, hball_target, A', ?_, ?_, ?_⟩
    · exact (hA_diff.mono (by
        intro z hz
        exact Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left r₀ r₁)))).const_mul
          (γ : ℂ)
    · exact mul_ne_zero (Circle.coe_ne_zero γ) hA_ne
    · intro z hz hz_center
      have hz₀ : z ∈ Metric.ball (χ.chart p) r₀ :=
        Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left r₀ r₁))
      have hz₁ : z ∈ Metric.ball (χ.chart p) r₁ :=
        Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right r₀ r₁))
      have hyU : χ.chart.symm z ∈ U := (hball₁_subset hz₁).2
      have hglobal :
          C.global (χ.chart.symm z) =
            (γ : ℂ) * S.branch i (χ.chart.symm z) := by
        rw [hglobal_eq (χ.chart.symm z) hyU,
          D.action_eq γ (S.branch i (χ.chart.symm z))]
      calc
        C.global (χ.chart.symm z) =
            (γ : ℂ) * S.branch i (χ.chart.symm z) := hglobal
        _ = (γ : ℂ) * ((z - χ.chart p) * A z) := by
          rw [hA_factor z hz₀ hz_center]
        _ = (z - χ.chart p) * A' z := by
          simp [A', mul_assoc, mul_comm]

end CompactSuperlevelGreenFunctionExponentialBranchSystemData

/--
%%handwave
name:
  Pole and punctured branches form a local exponential branch atlas
statement:
  A pole exponential branch, chosen punctured logarithms, and local
  unit-circle transition constants package as a local exponential branch
  atlas.
proof:
  Use the pole branch as the distinguished branch through the pole.  For each
  punctured point, exponentiate the chosen local logarithm.  The logarithmic
  modulus, nonvanishing, local logarithm, and pole-factorization fields are
  inherited from the pole branch and the chosen logarithm data.  The transition
  field is exactly the supplied local circle-transition datum.
-/
noncomputable def compactSuperlevelGreenFunctionLocalExponentialBranchAtlasOfPoleBranch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (htrans :
      CompactSuperlevelGreenFunctionPolePuncturedBranchesHaveLocalCircleTransitions
        P hlocal) :
    CompactSuperlevelGreenFunctionLocalExponentialBranchAtlas X G := by
  classical
  refine
    { branchIndex := CompactSuperlevelGreenFunctionLocalExponentialBranchIndex X p
      domain := compactSuperlevelGreenFunctionPolePuncturedBranchDomain P hlocal
      domain_open := ?_
      branch := compactSuperlevelGreenFunctionPolePuncturedBranch P hlocal
      branch_holomorphicOn := ?_
      covers := ?_
      local_transition := ?_
      log_norm_eq := ?_
      nonzero_away_pole := ?_
      local_holomorphic_logs := ?_
      pole_factorizations := ?_ }
  · intro i
    cases i with
    | inl _ =>
        simpa [compactSuperlevelGreenFunctionPolePuncturedBranchDomain] using
          P.domain_open
    | inr q =>
        exact
          (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
            hlocal q).2.1
  · intro i
    cases i with
    | inl _ =>
        simpa [compactSuperlevelGreenFunctionPolePuncturedBranch,
          compactSuperlevelGreenFunctionPolePuncturedBranchDomain] using
          P.branch_holomorphicOn
    | inr q =>
        have hL :
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
              (compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q)
              (compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q) :=
          (compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
            hlocal q).1
        have hexp_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
            (fun z : ℂ ↦ Complex.exp z) := by
          exact mdifferentiable_iff_differentiable.mpr
            (Complex.differentiable_exp (𝕜 := ℂ))
        simpa [compactSuperlevelGreenFunctionPolePuncturedBranch,
          compactSuperlevelGreenFunctionPolePuncturedBranchDomain,
          Function.comp_def] using
          hexp_mdiff.comp_mdifferentiableOn hL
  · intro x
    by_cases hxp : x = p
    · refine ⟨Sum.inl (), ?_⟩
      simpa [compactSuperlevelGreenFunctionPolePuncturedBranchDomain, hxp] using
        P.mem_domain
    · let q : {x : X // x ≠ p} := ⟨x, hxp⟩
      refine ⟨Sum.inr q, ?_⟩
      simpa [compactSuperlevelGreenFunctionPolePuncturedBranchDomain, q] using
        (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
          hlocal q).1
  · exact htrans
  · intro i x hx hxp
    cases i with
    | inl _ =>
        simpa [compactSuperlevelGreenFunctionPolePuncturedBranch,
          compactSuperlevelGreenFunctionPolePuncturedBranchDomain] using
          P.log_norm_eq x hx hxp
    | inr q =>
        have hLre :
            (compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q x).re =
              -G.toFun x :=
          (compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
            hlocal q).2 x hx
        simp [compactSuperlevelGreenFunctionPolePuncturedBranch,
          Complex.norm_exp, hLre]
  · intro i x hx hxp
    cases i with
    | inl _ =>
        simpa [compactSuperlevelGreenFunctionPolePuncturedBranch,
          compactSuperlevelGreenFunctionPolePuncturedBranchDomain] using
          P.nonzero_away_pole x hx hxp
    | inr q =>
        exact Complex.exp_ne_zero
          (compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q x)
  · intro i x hx hxp
    cases i with
    | inl _ =>
        simpa [compactSuperlevelGreenFunctionPolePuncturedBranch,
          compactSuperlevelGreenFunctionPolePuncturedBranchDomain] using
          P.local_holomorphic_logs x hx hxp
    | inr q =>
        refine
          ⟨compactSuperlevelGreenFunctionLocalPuncturedLogDomain hlocal q,
            hx,
            (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
              hlocal q).2.1,
            ?_,
            compactSuperlevelGreenFunctionLocalPuncturedLogFunction hlocal q,
            (compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
              hlocal q).1,
            (compactSuperlevelGreenFunctionLocalPuncturedLogFunction_spec
              hlocal q).2,
            ?_⟩
        · intro y hy
          exact
            ⟨hy,
              (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
                hlocal q).2.2.1 hy⟩
        · intro y hy
          rfl
  · intro i hp_domain χ
    cases i with
    | inl _ =>
        exact P.pole_factorizations χ
    | inr q =>
        have hp_ne : p ≠ p :=
          (compactSuperlevelGreenFunctionLocalPuncturedLogDomain_spec
            hlocal q).2.2.1 hp_domain
        exact False.elim (hp_ne rfl)
/--
%%handwave
name:
  Exponential branch atlas determined by a pole branch
statement:
  Let \(G\) be a compact-superlevel Green function with pole \(p\).  Suppose
  one has chosen an exponential branch near \(p\), local holomorphic
  logarithms with real part \(-G\) on the punctured surface, and local
  transition constants in \(S^1\) for every pair of the resulting branches.
  Then \(G\) admits a local exponential branch atlas covering the whole
  surface, with those unit-circle transition functions and with the prescribed
  first-order factorization at \(p\).
proof:
  Use the pole branch as the distinguished chart and exponentiate the chosen
  punctured logarithm at every other point.  [These domains and branches, with the supplied circle transitions, form the required local exponential branch atlas](lean:JJMath.Uniformization.compactSuperlevelGreenFunctionLocalExponentialBranchAtlasOfPoleBranch).
-/
theorem compactSuperlevelGreenFunction_localExponentialBranchAtlas_of_poleBranch
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (htrans :
      CompactSuperlevelGreenFunctionPolePuncturedBranchesHaveLocalCircleTransitions
        P hlocal) :
    Nonempty
      (CompactSuperlevelGreenFunctionLocalExponentialBranchAtlas X G) :=
  ⟨compactSuperlevelGreenFunctionLocalExponentialBranchAtlasOfPoleBranch
    P hlocal htrans⟩

/--
%%handwave
name:
  Local punctured logarithms exponentiate locally
statement:
  Local holomorphic logarithms with real part \(-G\) exponentiate to local
  nonvanishing holomorphic functions whose logarithmic moduli are \(-G\).
proof:
  Compose each local logarithm with the complex exponential.  Holomorphicity
  follows by composition, nonvanishing from nonvanishing of the exponential,
  and the modulus identity from \(|e^z|=e^{\operatorname{Re} z}\).
-/
theorem compactSuperlevelGreenFunction_local_punctured_logs_exponentiate
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G) :
    CompactSuperlevelGreenFunctionLocalPuncturedExponentials X G := by
  intro x hxp
  rcases hlocal x hxp with
    ⟨U, hxU, hU_open, hU_punctured, L, hL_hol, hL_re⟩
  let E : X → ℂ := fun y : X ↦ Complex.exp (L y)
  have hexp_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℂ ↦ Complex.exp z) := by
    exact mdifferentiable_iff_differentiable.mpr
      (Complex.differentiable_exp (𝕜 := ℂ))
  have hE_hol : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) E U := by
    simpa [E, Function.comp_def] using
      hexp_mdiff.comp_mdifferentiableOn hL_hol
  refine ⟨U, hxU, hU_open, hU_punctured, E, hE_hol, ?_, ?_⟩
  · intro y hy
    simp [E, Complex.norm_exp, hL_re y hy]
  · intro y _hy
    exact Complex.exp_ne_zero (L y)

/--
%%handwave
name:
  Local exponential branch atlas from local logarithms and the pole model
statement:
  The local holomorphic logarithms of \(-G\) on the punctured surface, together
  with the logarithmic singularity at the pole, form a local exponential
  branch atlas whose transition constants lie in the unit circle.
proof:
  Away from the pole, exponentiate the local logarithm branches.  Near the
  pole, use the removable logarithmic singularity to build one branch with a
  simple zero.  On overlaps away from the pole, local logarithms with the same
  real part differ by an imaginary constant, so the exponentials differ by a
  unit constant.  Since only the pole branch contains the pole, transitions at
  the pole are trivial.
-/
theorem compactSuperlevelGreenFunction_localExponentialBranchAtlas
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (hlocalLogs : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (_hlocalExp :
      CompactSuperlevelGreenFunctionLocalPuncturedExponentials X G) :
    Nonempty
      (CompactSuperlevelGreenFunctionLocalExponentialBranchAtlas X G) := by
  rcases compactSuperlevelGreenFunction_poleExponentialBranch X G with
    ⟨P⟩
  exact
    compactSuperlevelGreenFunction_localExponentialBranchAtlas_of_poleBranch
      X P hlocalLogs
      (compactSuperlevelGreenFunction_polePuncturedBranches_haveLocalCircleTransitions
        X P hlocalLogs)

/--
%%handwave
name:
  Exponential branch system from local logarithms and the pole model
statement:
  The local holomorphic logarithms of \(-G\) on the punctured surface, together
  with the logarithmic singularity at the pole, form a holomorphic local
  branch system on the whole surface whose transition group is the unit circle.
proof:
  Away from the pole, exponentiate the local logarithms.  Near the pole, write
  \(G+\log|z-z(p)|\) as a harmonic function and exponentiate a holomorphic
  conjugate of its negative; multiplying by \(z-z(p)\) gives the pole branch.
  On small connected overlaps, equal logarithmic moduli imply that two
  nonzero holomorphic branches differ by a unit constant, and the pole branch
  has the same transition behavior after the simple zero is factored out.
-/
theorem compactSuperlevelGreenFunction_exponentialBranchSystemData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (hlocalLogs : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (hlocalExp :
      CompactSuperlevelGreenFunctionLocalPuncturedExponentials X G) :
    Nonempty
      (CompactSuperlevelGreenFunctionExponentialBranchSystemData X G) := by
  rcases compactSuperlevelGreenFunction_localExponentialBranchAtlas
      X G hlocalLogs hlocalExp with
    ⟨A⟩
  exact ⟨
    CompactSuperlevelGreenFunctionLocalExponentialBranchAtlas.toExponentialBranchSystemData
      A⟩

/--
%%handwave
name:
  Punctured exponential gluing data from local exponentials
statement:
  On a simply connected surface, the local punctured exponentials associated
  to a compact-superlevel Green function have trivial exponential monodromy
  and determine a single-valued punctured exponential with the expected
  first-order factorization at the pole.
proof:
  Continue the local holomorphic logarithms along paths in the punctured
  surface.  On overlaps the logarithms differ by imaginary constants.  The
  logarithmic pole contributes exactly the integral \(2\pi\)-period around a
  small positively oriented loop, so exponentiation kills the pole monodromy,
  while simple connectedness of the unpunctured surface kills all remaining
  monodromy.  The local expression near the pole is then
  \((z-z(p))\) times a nonvanishing holomorphic factor.
-/
theorem compactSuperlevelGreenFunction_punctured_exponential_gluingData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (hlocalLogs : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (hlocalExp :
      CompactSuperlevelGreenFunctionLocalPuncturedExponentials X G) :
    Nonempty
      (CompactSuperlevelGreenFunctionPuncturedExponentialGluingData X G) := by
  rcases compactSuperlevelGreenFunction_exponentialBranchSystemData
      X G hlocalLogs hlocalExp with
    ⟨D⟩
  exact
    CompactSuperlevelGreenFunctionExponentialBranchSystemData.toPuncturedExponentialGluingData
      D

/--
%%handwave
name:
  Local punctured exponentials glue
statement:
  The local punctured exponentials obtained from local logarithms glue to a
  global nonvanishing holomorphic function on the punctured surface, carrying
  compatible local logarithms.
proof:
  On overlaps the logarithms differ by imaginary constants, so their
  exponentials differ by unit constants.  The logarithmic pole contributes an
  integral \(2\pi\)-period and simple connectedness kills all other monodromy,
  hence the unit constants multiply to one around every continuation loop.
-/
theorem compactSuperlevelGreenFunction_local_punctured_exponentials_glue
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (hlocalLogs : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G)
    (hlocalExp :
      CompactSuperlevelGreenFunctionLocalPuncturedExponentials X G) :
    Nonempty (CompactSuperlevelGreenFunctionPuncturedHolomorphicLog X G) := by
  rcases compactSuperlevelGreenFunction_punctured_exponential_gluingData
      X G hlocalLogs hlocalExp with
    ⟨D⟩
  exact ⟨
    CompactSuperlevelGreenFunctionPuncturedExponentialGluingData.toPuncturedHolomorphicLog
      D⟩

/--
%%handwave
name:
  Local punctured logarithms glue after exponentiation
statement:
  If compact-superlevel Green data have local punctured logarithms, then on a
  simply connected surface their exponentials glue to a single nonvanishing
  holomorphic function on the punctured surface.
proof:
  On overlaps, local logarithms differ by imaginary constants.  Around the
  puncture the logarithmic pole contributes an integral \(2\pi\)-period, and
  simple connectedness kills all other periods.  Therefore the exponentials
  are single-valued and glue holomorphically.
-/
theorem compactSuperlevelGreenFunction_punctured_logs_glue_after_exp
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (hlocal : CompactSuperlevelGreenFunctionLocalPuncturedLogs X G) :
    Nonempty (CompactSuperlevelGreenFunctionPuncturedHolomorphicLog X G) := by
  exact compactSuperlevelGreenFunction_local_punctured_exponentials_glue
    X G hlocal
      (compactSuperlevelGreenFunction_local_punctured_logs_exponentiate
        X G hlocal)

/--
%%handwave
name:
  Compact-superlevel Green data have a punctured exponential logarithm
statement:
  On a simply connected surface, compact-superlevel Green data admit a
  nonvanishing holomorphic function on the punctured surface whose logarithmic
  modulus is \(-G\) and which locally has holomorphic logarithms with real
  part \(-G\).
proof:
  Local harmonic conjugates of \(-G\) differ by imaginary constants.  The
  only possible period around the puncture is the integral \(2\pi\)-period
  produced by the logarithmic pole, and exponentiation kills this period.
  Simple connectedness kills all remaining monodromy, so the local
  exponentials glue to a single nonvanishing holomorphic function.
-/
theorem compactSuperlevelGreenFunction_has_punctured_holomorphic_log
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    Nonempty (CompactSuperlevelGreenFunctionPuncturedHolomorphicLog X G) := by
  exact compactSuperlevelGreenFunction_punctured_logs_glue_after_exp X G
    (compactSuperlevelGreenFunction_has_local_punctured_logs X G)

/--
%%handwave
name:
  Compact-superlevel Green data exponentiate on the punctured surface
statement:
  On a simply connected surface, compact-superlevel Green data exponentiate
  on the punctured surface to a nonvanishing holomorphic function whose
  logarithmic modulus is \(-G\).
proof:
  Locally choose harmonic conjugates for \(G\) on the punctured surface and
  form \(\exp(-G-iP)\).  The logarithmic pole contributes integral period
  \(2\pi\), which exponentiation kills, and simple connectedness kills the
  remaining monodromy.
-/
theorem compactSuperlevelGreenFunction_punctured_exponential_planeMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    Nonempty (CompactSuperlevelGreenFunctionPuncturedPlaneMap X G) := by
  rcases compactSuperlevelGreenFunction_has_punctured_holomorphic_log X G with
    ⟨L⟩
  refine ⟨
    { toFun := L.toExp
      holomorphic_away_pole := L.holomorphic_away_pole
      log_norm_eq := L.log_norm_eq
      nonzero_away_pole := L.nonzero_away_pole
      pole_factorizations := L.pole_factorizations }⟩

/--
%%handwave
name:
  Zero extension of a punctured compact-superlevel plane map
statement:
  The zero extension of a punctured compact-superlevel plane map agrees with
  the punctured map away from the pole and takes value zero at the pole.
-/
noncomputable def compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G) : X → ℂ := by
  classical
  exact fun x : X ↦ if x = p then 0 else F.toFun x

/--
%%handwave
name: Zero extension at the Green-function pole
statement:
  The zero extension to $X$ of a punctured holomorphic plane map takes the value $0$ at its pole $p$.
proof:
  At $p$, the defining case distinction selects the value $0$.
-/
theorem compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G) :
    compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F p = 0 := by
  classical
  simp [compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension]

/--
%%handwave
name: Zero extension away from the Green-function pole
statement:
  If $x\ne p$, the zero extension of a punctured holomorphic plane map agrees at $x$ with the original punctured map.
proof:
  The inequality $x\ne p$ selects the non-pole branch of the defining case distinction.
-/
theorem compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension_of_ne
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p x : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G)
    (hxp : x ≠ p) :
    compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F x =
      F.toFun x := by
  classical
  simp [compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension, hxp]

/--
%%handwave
name:
  Pole factorizations for punctured compact-superlevel plane maps
statement:
  A punctured plane map has the expected pole factorization if, in every
  pointed coordinate, its zero extension is locally \((z-z(p))A(z)\), where
  \(A\) is holomorphic near the coordinate origin and \(A(z(p))\ne0\).
-/
def CompactSuperlevelGreenFunctionPuncturedPlaneMapHasPoleFactorizations
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G) : Prop :=
  ∀ χ : PointedSurfaceCoordinate X p,
    ∃ r : ℝ,
      0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
        ∃ A : ℂ → ℂ,
          DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
            A (χ.chart p) ≠ 0 ∧
              ∀ z ∈ Metric.ball (χ.chart p) r,
                compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F
                  (χ.chart.symm z) =
                  (z - χ.chart p) * A z

/--
%%handwave
name:
  Punctured plane maps have pole factorizations
statement:
  The punctured plane map associated to compact-superlevel Green data has the
  local form \((z-z(p))A(z)\) near the pole in every pointed coordinate, with
  \(A\) holomorphic and nonzero at the pole.
proof:
  The logarithmic singularity makes \(G+\log|z-z(p)|\) harmonic near the
  pole.  Taking a harmonic conjugate gives a holomorphic branch \(B\) of the
  regular part, and the punctured exponential is
  \((z-z(p))\exp(B(z))\).  The exponential factor is holomorphic and
  nonvanishing at the pole.
-/
theorem compactSuperlevelGreenFunctionPuncturedPlaneMap_has_poleFactorizations
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G) :
    CompactSuperlevelGreenFunctionPuncturedPlaneMapHasPoleFactorizations
      X F := by
  intro χ
  rcases F.pole_factorizations χ with
    ⟨r, hr_pos, hball_target, A, hA_diff, hA_ne, hfactor⟩
  refine ⟨r, hr_pos, hball_target, A, hA_diff, hA_ne, ?_⟩
  intro z hz
  by_cases hz_center : z = χ.chart p
  · subst hz_center
    have hsymm :
        χ.chart.symm (χ.chart p) = p :=
      χ.chart.left_inv χ.base_mem_source
    simp [compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension,
      hsymm]
  · have hsymm_ne : χ.chart.symm z ≠ p := by
      intro hsymm_eq
      have hz_target : z ∈ χ.chart.target := hball_target hz
      have hright : χ.chart (χ.chart.symm z) = z :=
        χ.chart.right_inv hz_target
      exact hz_center (by
        rw [← hright, hsymm_eq])
    rw [compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension_of_ne
      F hsymm_ne]
    exact hfactor z hz hz_center

/--
%%handwave
name:
  Pole factorizations make the zero simple
statement:
  If the zero extension has the local form \((z-z(p))A(z)\) in every pointed
  coordinate, with \(A(z(p))\ne0\), then the derivative of the zero extension
  at the pole is nonzero in every pointed coordinate.
proof:
  Differentiate the local identity.  At \(z=z(p)\), the derivative of
  \((z-z(p))A(z)\) is \(A(z(p))\).
-/
theorem compactSuperlevelGreenFunctionPuncturedPlaneMap_zeroExtension_simple_zero_of_poleFactorizations
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G)
    (hfactor :
      CompactSuperlevelGreenFunctionPuncturedPlaneMapHasPoleFactorizations
        X F) :
    ∀ χ : PointedSurfaceCoordinate X p,
      surfaceComplexDerivativeInCoordinate χ
        (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F) ≠ 0 := by
  intro χ
  rcases hfactor χ with
    ⟨r, hr_pos, _hball_target, A, hA_diff, hA_ne, hfactorχ⟩
  have hz0_ball : χ.chart p ∈ Metric.ball (χ.chart p) r := by
    simpa using Metric.mem_ball_self (x := χ.chart p) hr_pos
  have hA_at : DifferentiableAt ℂ A (χ.chart p) :=
    hA_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz0_ball)
  have hlocal :
      (fun z : ℂ ↦
        compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F
          (χ.chart.symm z))
        =ᶠ[𝓝 (χ.chart p)]
        (fun z : ℂ ↦ (z - χ.chart p) * A z) := by
    filter_upwards [Metric.ball_mem_nhds (χ.chart p) hr_pos] with z hz
    exact hfactorχ z hz
  have hderiv_left :
      deriv
        (fun z : ℂ ↦
          compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F
            (χ.chart.symm z)) (χ.chart p)
        =
        deriv (fun z : ℂ ↦ (z - χ.chart p) * A z) (χ.chart p) :=
    hlocal.deriv_eq
  have hfirst :
      DifferentiableAt ℂ (fun z : ℂ ↦ z - χ.chart p) (χ.chart p) :=
    differentiableAt_id.sub_const _
  have hderiv_right :
      deriv (fun z : ℂ ↦ (z - χ.chart p) * A z) (χ.chart p) =
        A (χ.chart p) := by
    rw [deriv_fun_mul hfirst hA_at]
    simp
  have hderiv :
      surfaceComplexDerivativeInCoordinate χ
        (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F) =
        A (χ.chart p) := by
    simpa [surfaceComplexDerivativeInCoordinate] using
      hderiv_left.trans hderiv_right
  simpa [hderiv] using hA_ne

/--
%%handwave
name:
  Pole factorizations give a holomorphic zero extension
statement:
  If a punctured plane map has the local pole factorization
  \((z-z(p))A(z)\) with \(A(z(p))\ne0\), then its zero extension is
  holomorphic on the whole surface and has a simple zero at the pole.
proof:
  Away from the pole this is the original holomorphic punctured map.  Near
  the pole, the factorization gives an honest holomorphic formula for the
  zero extension.  Differentiating the formula at \(z(p)\) gives
  \(A(z(p))\), which is nonzero.
-/
theorem compactSuperlevelGreenFunctionPuncturedPlaneMap_zeroExtension_holomorphic_simple_zero_of_poleFactorizations
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G)
    (hfactor :
      CompactSuperlevelGreenFunctionPuncturedPlaneMapHasPoleFactorizations
        X F) :
    HolomorphicMap X ℂ
      (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F) ∧
      ∀ χ : PointedSurfaceCoordinate X p,
        surfaceComplexDerivativeInCoordinate χ
          (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · change MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F)
    rw [← mdifferentiableOn_univ]
    refine mdifferentiableOn_of_locally_mdifferentiableOn ?_
    intro x _hx
    by_cases hxp : x = p
    · let χ : PointedSurfaceCoordinate X p :=
        { chart := chartAt ℂ p
          chart_mem_atlas := chart_mem_atlas ℂ p
          base_mem_source := by simp }
      rcases hfactor χ with
        ⟨r, hr_pos, _hball_target, A, hA_diff, _hA_ne, hfactorχ⟩
      let U : Set X := χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) r
      have hU_open : IsOpen U := by
        dsimp [U]
        exact χ.chart.isOpen_inter_preimage Metric.isOpen_ball
      have hpU : p ∈ U := by
        refine ⟨χ.base_mem_source, ?_⟩
        simpa using Metric.mem_ball_self (x := χ.chart p) hr_pos
      have hxU : x ∈ U := by
        simpa [hxp] using hpU
      let B : X → ℂ := fun y : X ↦
        (χ.chart y - χ.chart p) * A (χ.chart y)
      have hB_eq :
          ∀ y ∈ U,
            compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F y =
              B y := by
        intro y hy
        have hy_source : y ∈ χ.chart.source := hy.1
        have hy_ball : χ.chart y ∈ Metric.ball (χ.chart p) r := hy.2
        have hsymm : χ.chart.symm (χ.chart y) = y :=
          χ.chart.left_inv hy_source
        calc
          compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F y
              =
              compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F
                (χ.chart.symm (χ.chart y)) := by rw [hsymm]
          _ = (χ.chart y - χ.chart p) * A (χ.chart y) := by
            exact hfactorχ (χ.chart y) hy_ball
          _ = B y := rfl
      have hchart :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) χ.chart U :=
        (mdifferentiableOn_atlas (I := 𝓘(ℂ)) χ.chart_mem_atlas).mono
          (by
            intro y hy
            exact hy.1)
      let C : ℂ → ℂ := fun z : ℂ ↦ (z - χ.chart p) * A z
      have hC_diff :
          DifferentiableOn ℂ C (Metric.ball (χ.chart p) r) := by
        dsimp [C]
        exact (differentiableOn_id.sub_const (χ.chart p)).mul hA_diff
      have hC_mdiff :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) C
            (Metric.ball (χ.chart p) r) :=
        mdifferentiableOn_iff_differentiableOn.mpr hC_diff
      have hmaps : U ⊆ χ.chart ⁻¹' Metric.ball (χ.chart p) r := by
        intro y hy
        exact hy.2
      have hB_mdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) B U := by
        simpa [B, C, Function.comp_def] using
          hC_mdiff.comp hchart hmaps
      have hFext_U :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
            (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F)
            U :=
        hB_mdiff.congr (by
          intro y hy
          exact hB_eq y hy)
      exact ⟨U, hU_open, hxU, by simpa using hFext_U⟩
    · let U : Set X := {y : X | y ≠ p}
      have hU_open : IsOpen U := by
        simpa [U] using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
      have hxU : x ∈ U := hxp
      have hFext_U :
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
            (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F)
            U :=
        F.holomorphic_away_pole.congr (by
          intro y hy
          exact
            compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension_of_ne
              F hy)
      exact ⟨U, hU_open, hxU, by simpa using hFext_U⟩
  · exact
      compactSuperlevelGreenFunctionPuncturedPlaneMap_zeroExtension_simple_zero_of_poleFactorizations
        X F hfactor

/--
%%handwave
name:
  The zero extension is holomorphic with a simple zero
statement:
  The zero extension of a punctured plane map controlled by compact-superlevel
  Green data is holomorphic on the surface and has a simple zero at the pole.
proof:
  In a pointed coordinate, the logarithmic singularity writes
  \(G+\log|z-z(p)|\) as a harmonic function.  The punctured map is therefore
  \(z-z(p)\) times the exponential of a holomorphic branch with nonzero value
  at the pole.  Riemann's removable singularity theorem gives the holomorphic
  extension, and the displayed factorization gives the nonzero derivative.
-/
theorem compactSuperlevelGreenFunctionPuncturedPlaneMap_zeroExtension_holomorphic_simple_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G) :
    HolomorphicMap X ℂ
      (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F) ∧
      ∀ χ : PointedSurfaceCoordinate X p,
        surfaceComplexDerivativeInCoordinate χ
          (compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F) ≠ 0 := by
  exact
    compactSuperlevelGreenFunctionPuncturedPlaneMap_zeroExtension_holomorphic_simple_zero_of_poleFactorizations
      X F
      (compactSuperlevelGreenFunctionPuncturedPlaneMap_has_poleFactorizations
        X G F)

/--
%%handwave
name:
  Punctured exponentials extend with a simple zero
statement:
  A punctured plane map whose logarithmic modulus is \(-G\), for
  compact-superlevel Green data \(G\), extends across the pole to a
  holomorphic plane map with only a simple zero at the pole.
proof:
  In a pointed coordinate, the logarithmic singularity writes
  \(G+\log |z-z(p)|\) as a harmonic function.  Thus the punctured exponential
  is \((z-z(p))\) times a nowhere-zero holomorphic factor.  This gives a
  removable extension across the pole, identifies the zero fiber, and makes
  the derivative in every pointed coordinate nonzero.
-/
theorem compactSuperlevelGreenFunctionPuncturedPlaneMap_extends_to_planeMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (F : CompactSuperlevelGreenFunctionPuncturedPlaneMap X G) :
    Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G) := by
  let Fext : X → ℂ :=
    compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension F
  have hFext_pole : Fext p = 0 := by
    simpa [Fext] using
      compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension_pole F
  have hFext_away : ∀ x : X, x ≠ p → Fext x = F.toFun x := by
    intro x hxp
    simpa [Fext] using
      compactSuperlevelGreenFunctionPuncturedPlaneMapZeroExtension_of_ne F hxp
  rcases
    compactSuperlevelGreenFunctionPuncturedPlaneMap_zeroExtension_holomorphic_simple_zero
      X G F with
    ⟨hhol, hsimple⟩
  refine ⟨
    { toFun := Fext
      holomorphic := hhol
      log_norm_eq := ?_
      zero_fiber := ?_
      simple_zero := ?_ }⟩
  · intro x hxp
    rw [hFext_away x hxp]
    exact F.log_norm_eq x hxp
  · intro x
    constructor
    · intro hxzero
      by_cases hxp : x = p
      · exact hxp
      · have hxF_zero : F.toFun x = 0 := by
          simpa [hFext_away x hxp] using hxzero
        exact False.elim ((F.nonzero_away_pole x hxp) hxF_zero)
    · intro hxp
      simp [hxp, hFext_pole]
  · exact hsimple

/--
%%handwave
name:
  Compact-superlevel Green data exponentiate to plane maps
statement:
  On a simply connected surface, compact-superlevel Green data exponentiate
  to a holomorphic plane map whose logarithmic modulus is \(-G\), whose only
  zero is the pole, and whose zero is simple.
proof:
  Choose local harmonic conjugates on the punctured surface.  The logarithmic
  pole supplies the single local period around the puncture, and
  exponentiation kills that period.  Simple connectedness kills all remaining
  monodromy.  The local form \(z-p\) times a nowhere-zero holomorphic factor
  gives the simple zero at the pole.
-/
theorem compactSuperlevelGreenFunction_exponential_planeMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G) := by
  rcases compactSuperlevelGreenFunction_punctured_exponential_planeMap X G with
    ⟨F⟩
  exact
    compactSuperlevelGreenFunctionPuncturedPlaneMap_extends_to_planeMap
      X G F

/--
%%handwave
name:
  Compact-superlevel Green data exponentiate to pointed disk maps
statement:
  On a simply connected surface, compact-superlevel Green data exponentiate
  to a holomorphic map to the unit disk with logarithmic modulus \(-G\), only
  zero at the pole, and simple zero there.
proof:
  Choose local harmonic conjugates on the punctured surface.  The logarithmic
  pole supplies the single local period around the puncture, and
  exponentiation kills that period.  Simple connectedness kills all remaining
  monodromy, so \(\exp(-G-iP)\) is a single-valued pointed disk map.
-/
theorem compactSuperlevelGreenFunction_exponential_pointedDiskMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    ∃ F : PointedHolomorphicMap X Complex.UnitDisc p 0,
      IsCompactSuperlevelGreenFunctionExponentialPointedDiskMap X G F := by
  rcases compactSuperlevelGreenFunction_exponential_planeMap X G with ⟨F⟩
  exact compactSuperlevelGreenFunctionPlaneMap_to_pointedDiskMap X G F

/--
%%handwave
name:
  Compact-superlevel modulus makes the pointed disk map proper
statement:
  A pointed disk map whose logarithmic modulus is \(-G\), for compact-
  superlevel Green data \(G\), is proper.
proof:
  Compact subsets of the unit disk lie in a closed subdisk \(\{|z|\le r\}\)
  with \(r<1\).  The logarithmic modulus identity turns the preimage of this
  closed subdisk into the positive superlevel set \(G\ge-\log r\), together
  with the pole.  This set is compact by the compact-superlevel axiom.
-/
theorem pointedDiskMap_isProper_of_compactSuperlevelGreenFunction_modulus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hlog : ∀ x : X, x ≠ p →
      Real.log ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ = -G.toFun x)
    (hzero : ∀ x : X, (((F.toFun x : Complex.UnitDisc) : ℂ) = 0) ↔ x = p) :
    IsProperMap F.toFun := by
  classical
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨F.holomorphic.continuous, ?_⟩
  intro K hK
  rcases compact_unitDisc_subset_closed_norm_lt_one hK with
    ⟨r, hr_pos, hr_lt_one, hK_norm⟩
  let a : ℝ := -Real.log r
  have ha : 0 < a := by
    dsimp [a]
    exact neg_pos.mpr (Real.log_neg hr_pos hr_lt_one)
  let C : Set X := {p} ∪ {x : X | a ≤ G.toFun x}
  have hpre_subset : F.toFun ⁻¹' K ⊆ C := by
    intro x hxK
    by_cases hxp : x = p
    · exact Or.inl hxp
    · right
      have hxnorm_le :
          ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ ≤ r :=
        hK_norm (F.toFun x) hxK
      have hxF_ne_zero : ((F.toFun x : Complex.UnitDisc) : ℂ) ≠ 0 := by
        intro hxzero
        exact hxp ((hzero x).mp hxzero)
      have hxnorm_pos : 0 < ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ :=
        norm_pos_iff.mpr hxF_ne_zero
      have hlog_le :
          Real.log ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ ≤ Real.log r :=
        Real.log_le_log hxnorm_pos hxnorm_le
      have hneg_le : -G.toFun x ≤ Real.log r := by
        simpa [hlog x hxp] using hlog_le
      dsimp [a]
      linarith
  have hpre_closed : IsClosed (F.toFun ⁻¹' K) :=
    hK.isClosed.preimage F.holomorphic.continuous
  exact IsCompact.of_isClosed_subset
    (by simpa [C, a] using G.compact_positive_superlevel a ha)
    hpre_closed hpre_subset

/--
%%handwave
name:
  Associated compact-superlevel disk maps are proper
statement:
  The pointed disk map associated to compact-superlevel Green data is proper.
proof:
  Apply the properness criterion for pointed disk maps controlled by the
  logarithmic modulus of compact-superlevel Green data.
-/
theorem compactSuperlevelGreenFunction_pointedDiskMap_isProper
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hF : IsCompactSuperlevelGreenFunctionExponentialPointedDiskMap X G F) :
    IsProperMap F.toFun :=
  pointedDiskMap_isProper_of_compactSuperlevelGreenFunction_modulus
    X G F hF.1 hF.2.1

/--
%%handwave
name:
  Compact-superlevel Green functions exponentiate properly
statement:
  On a simply connected surface, a compact-superlevel Green function
  exponentiates with its harmonic conjugate to a proper holomorphic pointed
  disk map.
proof:
  The logarithmic pole supplies the single local period around the puncture,
  and exponentiation kills it.  Simple connectedness kills all remaining
  periods.  Positivity gives image in the unit disk, the logarithmic
  singularity gives a simple zero at the pole, and compact positive
  superlevel sets give properness.
-/
theorem compactSuperlevelGreenFunction_exponential_proper_pointedDiskMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    ∃ F : PointedHolomorphicMap X Complex.UnitDisc p 0,
      (∀ x : X, x ≠ p →
        Real.log ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ = -G.toFun x) ∧
      (∀ x : X, (((F.toFun x : Complex.UnitDisc) : ℂ) = 0) ↔ x = p) ∧
      (∀ χ : PointedSurfaceCoordinate X p,
        surfaceComplexDerivativeInCoordinate χ
          (fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)) ≠ 0) ∧
      IsProperMap F.toFun := by
  rcases compactSuperlevelGreenFunction_exponential_pointedDiskMap X G with
    ⟨F, hF⟩
  exact
    ⟨F, hF.1, hF.2.1, hF.2.2,
      compactSuperlevelGreenFunction_pointedDiskMap_isProper X G F hF⟩


end Uniformization

end JJMath
