import JJMath.Manifold.AnnularPeriod
import JJMath.RiemannianGeometry.SurfaceMetric
import Mathlib.Analysis.Convex.MetricSpace

/-!
# Smooth path connectivity of connected surfaces

This file proves that any two points of a connected smooth surface can be
joined by a globally smooth path with sitting half-lines at both endpoints.
The sitting condition makes repeated concatenation smooth without a separate
corner-smoothing argument.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X]

/-- Two points are joined by a globally smooth path which is constant before
time zero and after time one. -/
def SmoothSittingJoined (x y : X) : Prop :=
  ∃ gamma : ℝ → X,
    ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma ∧
      (∀ t, t ≤ 0 → gamma t = x) ∧
      (∀ t, 1 ≤ t → gamma t = y)

theorem smoothSittingJoined_refl (x : X) : SmoothSittingJoined x x := by
  refine ⟨fun _ ↦ x, contMDiff_const, ?_, ?_⟩ <;> simp

theorem smoothSittingJoined_symm {x y : X} :
    SmoothSittingJoined x y → SmoothSittingJoined y x := by
  rintro ⟨gamma, hgamma, hleft, hright⟩
  refine ⟨fun t ↦ gamma (1 - t), ?_, ?_, ?_⟩
  · exact hgamma.comp (by
      rw [contMDiff_iff_contDiff]
      fun_prop)
  · intro t ht
    exact hright (1 - t) (by linarith)
  · intro t ht
    exact hleft (1 - t) (by linarith)

theorem smoothSittingJoined_trans {x y z : X} :
    SmoothSittingJoined x y → SmoothSittingJoined y z →
      SmoothSittingJoined x z := by
  rintro ⟨gamma, hgamma, hgamma_left, hgamma_right⟩
    ⟨delta, hdelta, hdelta_left, hdelta_right⟩
  let shiftedDelta : ℝ → X := fun t ↦ delta (t - 3)
  have hshiftedDelta :
      ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ shiftedDelta := by
    exact hdelta.comp (by
      rw [contMDiff_iff_contDiff]
      fun_prop)
  have hagree : gamma =ᶠ[nhds 2] shiftedDelta := by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) < 3 by norm_num)] with t ht
    change gamma t = delta (t - 3)
    rw [hgamma_right t ht.1.le,
      hdelta_left (t - 3) (sub_nonpos.mpr ht.2.le)]
  let joined : ℝ → X := piecewise (Iic 2) gamma shiftedDelta
  have hjoined :
      ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ joined := by
    exact ContMDiff.piecewise_Iic hgamma hshiftedDelta hagree
  refine ⟨fun t ↦ joined (4 * t), ?_, ?_, ?_⟩
  · exact hjoined.comp (by
      rw [contMDiff_iff_contDiff]
      fun_prop)
  · intro t ht
    have h4t : 4 * t ≤ (2 : ℝ) := by linarith
    change joined (4 * t) = x
    rw [show joined (4 * t) = gamma (4 * t) by
      simp [joined, h4t]]
    exact hgamma_left (4 * t) (by linarith)
  · intro t ht
    have h4t : ¬ 4 * t ≤ (2 : ℝ) := by linarith
    change joined (4 * t) = z
    rw [show joined (4 * t) = delta (4 * t - 3) by
      simp [joined, shiftedDelta, h4t]]
    exact hdelta_right (4 * t - 3) (by linarith)

/-- Every point has an open neighborhood whose points can be joined to it by
a smooth path with sitting half-lines. -/
theorem exists_open_smoothSittingJoined_from
    (x : X) : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, SmoothSittingJoined x y := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hex_target : e x ∈ e.target := by simp [e]
  have htarget_nhds : e.target ∈ nhds (e x) :=
    e.open_target.mem_nhds hex_target
  rcases Metric.nhds_basis_ball.mem_iff.mp htarget_nhds with
    ⟨r, hr, hball_target⟩
  let B : Set ℂ := Metric.ball (e x) r
  let W : Set X := e.symm '' B
  have hB_open : IsOpen B := Metric.isOpen_ball
  have hW_open : IsOpen W :=
    e.isOpen_image_symm_of_subset_target hB_open hball_target
  have hxW : x ∈ W := by
    refine ⟨e x, Metric.mem_ball_self hr, ?_⟩
    exact e.left_inv (by simp [e])
  refine ⟨W, hW_open, hxW, ?_⟩
  intro y hyW
  rcases hyW with ⟨b, hbB, rfl⟩
  have hb_target : b ∈ e.target := hball_target hbB
  let step : ℝ → ℝ := fun t ↦ JJMath.Manifold.annularStep (2 * t - 1)
  let line : ℝ → ℂ := fun t ↦
    (1 - step t) • e x + step t • b
  have hstep_nonneg (t : ℝ) : 0 ≤ step t := by
    exact Real.smoothTransition.nonneg _
  have hstep_le_one (t : ℝ) : step t ≤ 1 := by
    exact Real.smoothTransition.le_one _
  have hline_ball (t : ℝ) : line t ∈ B := by
    apply (convex_ball (e x) r) (Metric.mem_ball_self hr) hbB
      (sub_nonneg.mpr (hstep_le_one t)) (hstep_nonneg t)
    simp
  have hline_target (t : ℝ) : line t ∈ e.target :=
    hball_target (hline_ball t)
  have hline_smooth : ContDiff ℝ ∞ line := by
    dsimp only [line, step]
    fun_prop
  let gamma : ℝ → X := fun t ↦ e.symm (line t)
  have hgamma_smooth :
      ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma := by
    rw [← contMDiffOn_univ]
    simpa [gamma, e, SurfaceRealModel, Function.comp_def] using
      (contMDiffOn_extChartAt_symm (I := SurfaceRealModel) x).comp
        hline_smooth.contMDiff.contMDiffOn
        (fun t _ht ↦ by simpa [e, SurfaceRealModel] using hline_target t)
  refine ⟨gamma, hgamma_smooth, ?_, ?_⟩
  · intro t ht
    have hstep : step t = 0 := by
      apply JJMath.Manifold.annularStep_eq_zero_of_le_neg_one
      dsimp [step]
      linarith
    change e.symm (line t) = x
    rw [show line t = e x by simp [line, hstep]]
    exact e.left_inv (by simp [e])
  · intro t ht
    have hstep : step t = 1 := by
      apply JJMath.Manifold.annularStep_eq_one_of_one_le
      dsimp [step]
      linarith
    change e.symm (line t) = e.symm b
    rw [show line t = b by simp [line, hstep]]

/-- Any two points of a connected smooth surface can be joined by a globally
smooth path which is constant on the two exterior half-lines. -/
theorem smoothSittingJoined_all [ConnectedSpace X] (x y : X) :
    SmoothSittingJoined x y := by
  let S : Set X := {z | SmoothSittingJoined x z}
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases exists_open_smoothSittingJoined_from z with ⟨W, hWopen, hzW, hW⟩
    refine Filter.mem_of_superset (hWopen.mem_nhds hzW) ?_
    intro w hw
    exact smoothSittingJoined_trans hz (hW w hw)
  have hS_compl_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases exists_open_smoothSittingJoined_from z with ⟨W, hWopen, hzW, hW⟩
    refine Filter.mem_of_superset (hWopen.mem_nhds hzW) ?_
    intro w hw hS_w
    exact hz (smoothSittingJoined_trans hS_w
      (smoothSittingJoined_symm (hW w hw)))
  have hS_clopen : IsClopen S :=
    ⟨isOpen_compl_iff.mp hS_compl_open, hS_open⟩
  have hS_nonempty : S.Nonempty := ⟨x, smoothSittingJoined_refl x⟩
  have hS_univ : S = univ := hS_clopen.eq_univ hS_nonempty
  change y ∈ S
  rw [hS_univ]
  exact mem_univ y

theorem smoothSittingJoined_all_exists [ConnectedSpace X] (x y : X) :
    ∃ gamma : ℝ → X,
      ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma ∧
        (∀ t, t ≤ 0 → gamma t = x) ∧
        (∀ t, 1 ≤ t → gamma t = y) :=
  smoothSittingJoined_all x y

end

end Uniformization
end JJMath
