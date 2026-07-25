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

end Uniformization

end JJMath
