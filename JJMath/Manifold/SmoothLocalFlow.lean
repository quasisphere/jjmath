import JJMath.Manifold.SmoothDependence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth local flows in finite-dimensional normed spaces

A bump function first extends a smooth coordinate vector field from an open
neighborhood to the whole model space.  Picard--Lindelöf supplies one local
trajectory, and the smooth implicit-function result for the Picard equation
then produces a flow germ which is smooth jointly in the initial value and
time.
-/

open Set MeasureTheory Filter
open scoped Interval ENat ContDiff Topology

noncomputable section

namespace JJMath.Manifold

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

section SmoothExtension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
/-- A smooth function on an open neighborhood in a finite-dimensional real
normed space has a globally smooth representative which agrees with it near
the chosen point.  A bump function makes the representative vanish outside a
smaller coordinate neighborhood. -/
theorem exists_contDiff_eventuallyEq_of_contDiffOn
    {f : E → F} {U : Set E} {x : E} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨R, hRpos, hR⟩ : ∃ R > 0, Metric.ball x R ⊆ U :=
    Metric.isOpen_iff.mp hU x hx
  let r : ℝ := R / 2
  have hrpos : 0 < r := half_pos hRpos
  have hr : Metric.closedBall x r ⊆ U := by
    exact (Metric.closedBall_subset_ball (show r < R by
      dsimp [r]
      linarith)).trans hR
  let b : ContDiffBump x :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hrpos
      rIn_lt_rOut := half_lt_self hrpos }
  let g : E → F := fun y => b y • f y
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Metric.closedBall x r
    · have hyU : y ∈ U := hr hy
      have hfy : ContDiffAt ℝ ∞ f y :=
        (hf y hyU).contDiffAt (hU.mem_nhds hyU)
      exact b.contDiffAt.smul hfy
    · have hycomp : y ∈ (Metric.closedBall x r)ᶜ := hy
      have heq : g =ᶠ[𝓝 y] (fun _ => (0 : F)) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hycomp]
          with z hz
        have hbzero : b z = 0 := by
          apply b.zero_of_le_dist
          have hz' : r < dist z x := by
            simpa [Metric.mem_closedBall, dist_comm] using hz
          exact hz'.le
        simp [g, hbzero]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  refine ⟨g, hg, ?_⟩
  have hball : Metric.ball x (r / 2) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (half_pos hrpos)
  filter_upwards [hball] with y hy
  have hb1 : b y = 1 := by
    apply b.one_of_mem_closedBall
    exact Metric.mem_closedBall.mpr (le_of_lt hy)
  simp [g, hb1]

end SmoothExtension

omit [FiniteDimensional ℝ E] in
/-- A Picard fixed point satisfies the autonomous differential equation at
every interior time. -/
theorem hasDerivAt_extendLocalCurve_of_picardFixedPoint
    (ε : ℝ) (hε : 0 ≤ ε) (f : E → E) (hf : Continuous f)
    (y : E) (u : LocalCurve E ε)
    (hfixed : u = ContinuousMap.const (Icc (-ε) ε) y +
      localCurveIntegral ε hε (superposition f hf u))
    {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    HasDerivAt (extendLocalCurve ε hε u)
      (f (extendLocalCurve ε hε u t)) t := by
  let g : ℝ → E := extendLocalCurve ε hε (superposition f hf u)
  have hg : Continuous g := extendLocalCurve_continuous ε hε _
  have hc : HasDerivAt (fun s : ℝ => y + ∫ r : ℝ in 0..s, g r) (g t) t := by
    convert (hasDerivAt_const (x := t) y).add
      (hg.integral_hasStrictDerivAt 0 t).hasDerivAt using 1
    all_goals simp
  have heq : extendLocalCurve ε hε u =ᶠ[𝓝 t]
      (fun s : ℝ => y + ∫ r : ℝ in 0..s, g r) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [extendLocalCurve_apply_of_mem ε hε u ⟨hs.1.le, hs.2.le⟩]
    have h := congrArg (fun v : LocalCurve E ε =>
      v ⟨s, ⟨hs.1.le, hs.2.le⟩⟩) hfixed
    simpa [localCurveIntegral_apply, g] using h
  have hvalue : g t = f (extendLocalCurve ε hε u t) := by
    simp [g, extendLocalCurve_apply_of_mem ε hε _ ⟨ht.1.le, ht.2.le⟩]
  rw [← hvalue]
  exact hc.congr_of_eventuallyEq heq

omit [FiniteDimensional ℝ E] in
/--
%%handwave
name:
  Derivative of a local flow at time zero
statement:
  Let \(\Phi(y,t)\) be smooth near \((x,0)\), satisfy
  \(\Phi(y,0)=y\) for \(y\) near \(x\), and solve the Picard equation for a
  smooth vector field \(f\).  Then for \(v\in E\) and \(a\in\mathbb R\),
  \[
    D\Phi_{(x,0)}(v,a)=v+a f(x).
  \]
proof:
  Along the initial-value slice \(y\mapsto\Phi(y,0)\), the map is the
  identity, so its derivative is \(v\).  Along the time slice
  \(t\mapsto\Phi(x,t)\), the Picard equation gives derivative \(f(x)\) at
  zero.  Linearity of the total derivative combines the two directions.
-/
theorem fderiv_uncurry_extendLocalCurve_apply_zero
    (ε : ℝ) (hε : 0 ≤ ε) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (x : E) (ψ : E → LocalCurve E ε)
    (hε0 : 0 < ε)
    (hinit : ∀ᶠ y in nhds x,
      ψ y ⟨0, by constructor <;> linarith [hε0]⟩ = y)
    (hfixed : ∀ᶠ y in nhds x,
      ψ y = ContinuousMap.const (Icc (-ε) ε) y +
        localCurveIntegral ε hε (superposition f hf.continuous (ψ y)))
    (hsmooth : ContDiffAt ℝ ∞
      (fun p : E × ℝ => extendLocalCurve ε hε (ψ p.1) p.2) (x, 0))
    (v : E) (a : ℝ) :
    fderiv ℝ (fun p : E × ℝ => extendLocalCurve ε hε (ψ p.1) p.2)
        (x, 0) (v, a) = v + a • f x := by
  let F : E × ℝ → E := fun p => extendLocalCurve ε hε (ψ p.1) p.2
  let i : E → E × ℝ := fun y => (y, 0)
  let j : ℝ → E × ℝ := fun t => (x, t)
  have hF : DifferentiableAt ℝ F (x, 0) :=
    hsmooth.differentiableAt (by norm_num)
  have hi : HasFDerivAt i (ContinuousLinearMap.inl ℝ E ℝ) x := by
    simpa [i] using (hasFDerivAt_id x).prodMk
      (hasFDerivAt_const (0 : ℝ) x)
  have hj : HasFDerivAt j (ContinuousLinearMap.inr ℝ E ℝ) 0 := by
    simpa [j] using (hasFDerivAt_const x (0 : ℝ)).prodMk
      (hasFDerivAt_id (0 : ℝ))
  have hFi : HasFDerivAt (F ∘ i)
      ((fderiv ℝ F (x, 0)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
    exact hF.hasFDerivAt.comp x hi
  have hFi_id : F ∘ i =ᶠ[nhds x] id := by
    filter_upwards [hinit] with y hy
    simpa [F, i, extendLocalCurve_apply_of_mem ε hε (ψ y)
      (show (0 : ℝ) ∈ Icc (-ε) ε by
        constructor <;> linarith [hε0])] using hy
  have hleft : (fderiv ℝ F (x, 0)) (v, 0) = v := by
    have hFi' : HasFDerivAt (F ∘ i) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).congr_of_eventuallyEq hFi_id
    have heq := hFi.unique hFi'
    have happ := congrArg (fun L : E →L[ℝ] E => L v) heq
    simpa using happ
  have hfixedx := mem_of_mem_nhds hfixed
  have hinitx := mem_of_mem_nhds hinit
  have htime : HasDerivAt (F ∘ j) (f x) 0 := by
    have ht : (0 : ℝ) ∈ Ioo (-ε) ε := by
      constructor <;> linarith [hε0]
    have hode := hasDerivAt_extendLocalCurve_of_picardFixedPoint
      ε hε f hf.continuous x (ψ x) hfixedx ht
    have hvalue : extendLocalCurve ε hε (ψ x) 0 = x := by
      rw [extendLocalCurve_apply_of_mem ε hε (ψ x)
        (show (0 : ℝ) ∈ Icc (-ε) ε by
          constructor <;> linarith [hε0])]
      exact hinitx
    simpa [F, j, hvalue] using hode
  have hFj : HasFDerivAt (F ∘ j)
      ((fderiv ℝ F (x, 0)).comp (ContinuousLinearMap.inr ℝ E ℝ)) 0 := by
    exact hF.hasFDerivAt.comp 0 hj
  have hright : (fderiv ℝ F (x, 0)) (0, a) = a • f x := by
    have heq := hFj.unique htime.hasFDerivAt
    have happ := congrArg (fun L : ℝ →L[ℝ] E => L a) heq
    simpa using happ
  change fderiv ℝ F (x, 0) (v, a) = _
  rw [show (v, a) = (v, 0) + (0, a) by ext <;> simp,
    map_add, hleft, hright]

/--
%%handwave
name:
  Existence of a jointly smooth local flow
statement:
  Let \(E\) be a finite-dimensional real normed space, let
  \(f:E\to E\) be smooth, and fix \(x\in E\).  There are
  \(\varepsilon>0\) and curves \(\psi_y:[-\varepsilon,\varepsilon]\to E\),
  for \(y\) near \(x\), such that
  \[
    \psi_y(0)=y,\qquad
    \psi_y(t)=y+\int_0^t f(\psi_y(s))\,ds,
  \]
  and \((y,t)\mapsto\psi_y(t)\) is smooth near every
  \((y,t_0)\) with \(|t_0|<\varepsilon\).
proof:
  Start with a local integral curve through \(x\), shorten its time interval
  until \(\varepsilon\sup\|Df\|<1\), and use the implicit-function theorem
  for the Picard operator to obtain a smooth family in the initial value.
  Applying the same argument to the time-rescaled vector field promotes this
  to joint smoothness at every interior time.
-/
theorem exists_jointlySmooth_localFlow
    (f : E → E) (hf : ContDiff ℝ ∞ f) (x : E) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ ψ : E → LocalCurve E ε,
      ψ x ⟨0, by constructor <;> linarith [hε]⟩ = x ∧
      (∀ᶠ y in 𝓝 x,
        ψ y ⟨0, by constructor <;> linarith [hε]⟩ = y) ∧
      (∀ᶠ y in 𝓝 x,
        ψ y = ContinuousMap.const (Icc (-ε) ε) y +
          localCurveIntegral ε hε.le
            (superposition f hf.continuous (ψ y))) ∧
      ∀ᶠ y in 𝓝 x, ∀ t₀ ∈ Ioo (-ε) ε,
          ContDiffAt ℝ ∞
            (fun p : E × ℝ =>
              extendLocalCurve ε hε.le (ψ p.1) p.2)
            (y, t₀) := by
  rcases (hf.of_le (by norm_num)).contDiffAt
      |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0 with
    ⟨α, hα0, δ, hδ, hα⟩
  have hαderiv0 : HasDerivAt α (f (α 0)) 0 := by
    exact hα 0 (by constructor <;> linarith)
  let M : ℝ := ‖fderiv ℝ f x‖ + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hnorm_cont : ContinuousAt (fun t : ℝ => ‖fderiv ℝ f (α t)‖) 0 := by
    simpa [Function.comp_def] using
      ((hf.continuous_fderiv (by norm_num)).norm.continuousAt.comp
        hαderiv0.continuousAt)
  have hnorm0 : ‖fderiv ℝ f (α 0)‖ < M := by
    rw [hα0]
    dsimp [M]
    linarith
  have hbound_event : ∀ᶠ t : ℝ in 𝓝 0, ‖fderiv ℝ f (α t)‖ < M :=
    hnorm_cont (Iio_mem_nhds hnorm0)
  obtain ⟨r, hr, hbound⟩ :=
    Metric.eventually_nhds_iff_ball.mp hbound_event
  let ε : ℝ := min δ (min r (1 / M)) / 2
  have hminpos : 0 < min δ (min r (1 / M)) := by positivity
  have hε : 0 < ε := half_pos hminpos
  have hεδ : ε < δ :=
    (half_lt_self hminpos).trans_le (min_le_left _ _)
  have hεr : ε < r :=
    (half_lt_self hminpos).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hεM : ε * M < 1 := by
    have hεinv : ε < 1 / M :=
      (half_lt_self hminpos).trans_le
        ((min_le_right _ _).trans (min_le_right _ _))
    calc
      ε * M < (1 / M) * M := mul_lt_mul_of_pos_right hεinv hM
      _ = 1 := by field_simp
  let u : LocalCurve E ε :=
    { toFun := fun t => α t
      continuous_toFun := by
        rw [continuous_iff_continuousAt]
        intro t
        apply (hα (t : ℝ) ?_).continuousAt.comp continuousAt_subtype_val
        constructor <;> linarith [t.2.1, t.2.2, hεδ] }
  have hfixed : u = ContinuousMap.const (Icc (-ε) ε) x +
      localCurveIntegral ε hε.le (superposition f hf.continuous u) := by
    ext t
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply,
      localCurveIntegral_apply]
    have hsub : uIcc (0 : ℝ) (t : ℝ) ⊆ Ioo (-δ) δ := by
      intro s hs
      have hsIcc : s ∈ Icc (-ε) ε := by
        exact uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-ε) ε by
          constructor <;> linarith) t.2 hs
      constructor <;> linarith [hsIcc.1, hsIcc.2, hεδ]
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) (t : ℝ),
        HasDerivAt α (f (α s)) s := fun s hs => by
      apply hα s
      simpa only [zero_sub, zero_add] using hsub hs
    have hint : IntervalIntegrable (fun s : ℝ => f (α s)) volume 0 (t : ℝ) :=
      (hf.continuous.comp_continuousOn
        (HasDerivAt.continuousOn hderiv)).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hintegral :
        (∫ s : ℝ in 0..(t : ℝ),
          extendLocalCurve ε hε.le (superposition f hf.continuous u) s) =
        ∫ s : ℝ in 0..(t : ℝ), f (α s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsIcc : s ∈ Icc (-ε) ε :=
        uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-ε) ε by
          constructor <;> linarith) t.2 hs
      rw [extendLocalCurve_apply_of_mem ε hε.le _ hsIcc]
      rfl
    rw [hintegral, hFTC, hα0]
    simp [u]
  have hMu : ∀ t, ‖fderiv ℝ f (u t)‖ ≤ M := by
    intro t
    apply (hbound (t : ℝ) ?_).le
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_le.mpr t.2).trans_lt hεr
  rcases exists_jointlySmooth_picardFixedPoint_family ε hε.le f hf x u hfixed
      hM.le hMu hεM with ⟨ψ, hψx, hfixedψ, hsmoothψ⟩
  have hinitψ : ∀ᶠ y in 𝓝 x,
      ψ y ⟨0, by constructor <;> linarith [hε]⟩ = y := by
    filter_upwards [hfixedψ] with y hy
    have h := congrArg
      (fun v : LocalCurve E ε => v ⟨0, by constructor <;> linarith [hε]⟩) hy
    simpa [localCurveIntegral_apply] using h
  refine ⟨ε, hε, ψ, ?_, hinitψ, hfixedψ, hsmoothψ⟩
  rw [hψx]
  simpa [u] using hα0

end JJMath.Manifold
