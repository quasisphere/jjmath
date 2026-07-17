import JJMath.ComplexAnalysis.KoebeQuarter
import JJMath.Uniformization.RadoSecondCountable
import JJMath.Uniformization.GreenFunctionCore
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.ODE.Gronwall

/-!
# Hubbard's normalized exhaustion argument

This file develops the complex-analytic estimates used in Hubbard's proof
that a connected noncompact Riemann surface with vanishing first real
cohomology is conformally equivalent to either the disk or the plane.

The first step is the precise consequence of Koebe's theorem used in the
unbounded-conformal-radius case: outside the image of the normalized unit
disk, the reciprocal of the normalized map is bounded by four.  A set-level
form transports this estimate from the initial exhaustion member to every
later member.
-/

open scoped Manifold Topology

open Filter Metric Set

noncomputable section

namespace JJMath.Uniformization

open JJMath.ComplexAnalysis

/--
%%handwave
name:
  A locally uniform limit of univalent functions is constant or univalent
statement:
  Let holomorphic injective functions on a connected plane domain converge
  locally uniformly.  Their limit is either constant or injective.
proof:
  If two distinct points had the same limiting value, isolate that value near
  the first point by the isolated-zero theorem.  Uniform convergence leaves a
  positive boundary gap on a small disk.  The quantitative open-mapping
  theorem then forces the value at the second point for every sufficiently
  late function to be attained inside that disk, contradicting injectivity.
-/
theorem tendstoLocallyUniformlyOn_injOn_or_eqOn_const
    {U : Set ℂ} (hUopen : IsOpen U) (hUpre : IsPreconnected U)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop U)
    (hFdiff : ∀ᶠ n : ℕ in Filter.atTop, DifferentiableOn ℂ (F n) U)
    (hFinj : ∀ᶠ n : ℕ in Filter.atTop, Set.InjOn (F n) U) :
    (∃ c : ℂ, Set.EqOn f (Function.const ℂ c) U) ∨ Set.InjOn f U := by
  by_cases hconst : ∃ c : ℂ, Set.EqOn f (Function.const ℂ c) U
  · exact Or.inl hconst
  right
  have hfdiff : DifferentiableOn ℂ f U :=
    hconv.differentiableOn hFdiff hUopen
  have hfanalytic : AnalyticOnNhd ℂ f U := hfdiff.analyticOnNhd hUopen
  intro x hx y hy hxy
  by_contra hxyne
  have hnotlocal : ¬ ∀ᶠ z in 𝓝 x, f z = f x := by
    intro hlocal
    exact hconst ⟨f x,
      hfanalytic.eqOn_of_preconnected_of_eventuallyEq
        analyticOnNhd_const hUpre hx hlocal⟩
  have hne_punctured : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x :=
    ((hfanalytic x hx).eventually_eq_or_eventually_ne analyticAt_const).resolve_left
      hnotlocal
  have hU_nhds : ∀ᶠ z in 𝓝 x, z ∈ U := hUopen.mem_nhds hx
  obtain ⟨ρ, hρ, hρU, hρne⟩ :
      ∃ ρ > 0, closedBall x ρ ⊆ U ∧
        ∀ z ∈ closedBall x ρ, z ≠ x → f z ≠ f x := by
    simpa only [setOf_and, subset_inter_iff] using
      nhds_basis_closedBall.mem_iff.mp
        (hU_nhds.and (eventually_nhdsWithin_iff.mp hne_punctured))
  let r : ℝ := min (ρ / 2) (dist x y / 2)
  have hdist : 0 < dist x y := dist_pos.mpr hxyne
  have hr : 0 < r := by
    simp only [r, lt_min_iff]
    exact ⟨half_pos hρ, half_pos hdist⟩
  have hrρ : r < ρ :=
    (min_le_left (ρ / 2) (dist x y / 2)).trans_lt (half_lt_self hρ)
  have hry : r < dist x y :=
    (min_le_right (ρ / 2) (dist x y / 2)).trans_lt (half_lt_self hdist)
  have hballU : closedBall x r ⊆ U :=
    (closedBall_subset_closedBall hrρ.le).trans hρU
  have hy_not_ball : y ∉ closedBall x r := by
    intro hyball
    have := hyball
    rw [mem_closedBall, dist_comm] at this
    exact (not_lt_of_ge this) hry
  have hne_sphere : ∀ z ∈ sphere x r, f z ≠ f x := by
    intro z hz
    exact hρne z (closedBall_subset_closedBall hrρ.le (sphere_subset_closedBall hz))
      (ne_of_mem_sphere hz hr.ne.symm)
  have hsphere_nonempty : (sphere x r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  have hcont_sphere : ContinuousOn (fun z : ℂ ↦ ‖f z - f x‖) (sphere x r) :=
    continuous_norm.comp_continuousOn
      ((hfdiff.continuousOn.sub continuousOn_const).mono
        (sphere_subset_closedBall.trans hballU))
  obtain ⟨z₀, hz₀, hz₀min⟩ :=
    (isCompact_sphere x r).exists_isMinOn hsphere_nonempty hcont_sphere
  let ε : ℝ := ‖f z₀ - f x‖
  have hε : 0 < ε := norm_pos_iff.mpr (sub_ne_zero.mpr (hne_sphere z₀ hz₀))
  have hboundary_min : ∀ z ∈ sphere x r, ε ≤ dist (f z) (f x) := by
    intro z hz
    simpa [ε, dist_eq_norm] using hz₀min hz
  let K : Set ℂ := insert y (closedBall x r)
  have hKU : K ⊆ U := by
    intro z hz
    rcases hz with rfl | hz
    · exact hy
    · exact hballU hz
  have hKcompact : IsCompact K :=
    (isCompact_closedBall x r).insert y
  have hconvK : TendstoUniformlyOn F f Filter.atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen).mp hconv
      K hKU hKcompact
  have hclose : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ z ∈ K, dist (f z) (F n z) < ε / 8 :=
    Metric.tendstoUniformlyOn_iff.mp hconvK (ε / 8) (by positivity)
  obtain ⟨n, hndiff, hninj, hnclose⟩ :=
    (hFdiff.and (hFinj.and hclose)).exists
  have hxK : x ∈ K := by
    exact mem_insert_iff.mpr (Or.inr (mem_closedBall_self hr.le))
  have hyK : y ∈ K := mem_insert y _
  have hboundary : ∀ z ∈ sphere x r, ε / 2 ≤ ‖F n z - F n x‖ := by
    intro z hz
    have hzK : z ∈ K := by
      exact mem_insert_iff.mpr (Or.inr (sphere_subset_closedBall hz))
    have htri := dist_triangle4 (f z) (F n z) (F n x) (f x)
    have hxclose : dist (F n x) (f x) < ε / 8 := by
      simpa [dist_comm] using hnclose x hxK
    have hdistbound : ε / 2 ≤ dist (F n z) (F n x) := by
      linarith [hboundary_min z hz, hnclose z hzK, hxclose]
    simpa only [dist_eq_norm] using hdistbound
  have htarget : F n y ∈ ball (F n x) ((ε / 2) / 2) := by
    rw [mem_ball]
    have htri := dist_triangle4 (F n y) (f y) (f x) (F n x)
    have hyclose : dist (F n y) (f y) < ε / 8 := by
      simpa [dist_comm] using hnclose y hyK
    have hxclose : dist (f x) (F n x) < ε / 8 := hnclose x hxK
    rw [hxy] at htri hxclose
    rw [dist_self, add_zero] at htri
    linarith
  have hndcc : DiffContOnCl ℂ (F n) (ball x r) :=
    hndiff.diffContOnCl_ball hballU
  have hnfrequent : ∃ᶠ z in 𝓝 x, F n z ≠ F n x := by
    by_contra hnotfreq
    have hnlocal : ∀ᶠ z in 𝓝 x, F n z = F n x := by
      simpa only [not_ne_iff] using (not_frequently.mp hnotfreq)
    have hnanalytic : AnalyticOnNhd ℂ (F n) (ball x r) :=
      hndcc.differentiableOn.analyticOnNhd isOpen_ball
    have hneqOn := hnanalytic.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (convex_ball x r).isPreconnected (mem_ball_self hr) hnlocal
    let w : ℂ := x + (r / 2 : ℝ)
    have hwball : w ∈ ball x r := by
      rw [mem_ball, dist_eq_norm]
      simp only [w, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    have hwne : w ≠ x := by
      intro hw
      have : (r / 2 : ℂ) = 0 := by
        simpa [w] using sub_eq_zero.mpr hw
      have hre : r / 2 = 0 := by
        simpa using congrArg Complex.re this
      linarith
    exact hwne (hninj (hballU (ball_subset_closedBall hwball))
      (hballU (ball_subset_closedBall (mem_ball_self hr))) (hneqOn hwball))
  obtain ⟨z, hzball, hzeq⟩ :=
    hndcc.ball_subset_image_closedBall hr hboundary hnfrequent htarget
  have hzy : z = y :=
    hninj (hballU hzball) hy hzeq
  exact hy_not_ball (hzy ▸ hzball)

/--
%%handwave
name:
  Holomorphicity of an eventual-domain locally uniform limit
statement:
  Let a sequence of complex-valued functions on a Riemann surface converge
  locally uniformly.  If every point has a neighborhood on which all
  sufficiently late functions are holomorphic, then the limit is
  holomorphic.
proof:
  Around each point, shrink a complex coordinate chart to a Euclidean ball
  contained in such a neighborhood.  The coordinate representatives of the
  tail are holomorphic on that ball and converge locally uniformly there, so
  the classical Weierstrass theorem makes the coordinate representative of
  the limit holomorphic.
-/
theorem locallyUniformLimit_eventuallyHolomorphic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (F : ℕ → X → ℂ) (g : X → ℂ)
    (hconv : TendstoLocallyUniformly F g Filter.atTop)
    (hholo : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n) U) :
    HolomorphicMap X ℂ g := by
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  intro x
  rcases hholo x with ⟨U, hUopen, hxU, hholoU⟩
  let e := extChartAt 𝓘(ℂ) x
  let V : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hxV : e x ∈ V := by
    refine ⟨mem_extChartAt_target (I := 𝓘(ℂ)) x, ?_⟩
    simpa [e] using hxU
  have hsymm_contAt : ContinuousAt e.symm (e x) :=
    (continuousOn_extChartAt_symm (I := 𝓘(ℂ)) x).continuousAt
      ((isOpen_extChartAt_target (I := 𝓘(ℂ)) x).mem_nhds hxV.1)
  have hV_nhds : V ∈ 𝓝 (e x) := by
    refine Filter.inter_mem
      ((isOpen_extChartAt_target (I := 𝓘(ℂ)) x).mem_nhds hxV.1) ?_
    exact hsymm_contAt (hUopen.mem_nhds hxV.2)
  rcases Metric.mem_nhds_iff.mp hV_nhds with ⟨r, hr, hrV⟩
  let W : Set ℂ := Metric.ball (e x) r
  have hWopen : IsOpen W := Metric.isOpen_ball
  have hxW : e x ∈ W := Metric.mem_ball_self hr
  have hWV : W ⊆ V := hrV
  have hconvChart :
      TendstoLocallyUniformlyOn
        (fun n : ℕ ↦ fun z : ℂ ↦ F n (e.symm z))
        (fun z : ℂ ↦ g (e.symm z)) Filter.atTop W := by
    have hglobal :
        TendstoLocallyUniformlyOn F g
          Filter.atTop Set.univ := hconv.tendstoLocallyUniformlyOn
    have hcomp := hglobal.comp e.symm
      (fun z (_hz : z ∈ W) ↦ Set.mem_univ (e.symm z))
      ((continuousOn_extChartAt_symm (I := 𝓘(ℂ)) x).mono
        (fun z hz ↦ (hWV hz).1))
    simpa [Function.comp_def] using hcomp
  have hFdiff :
      ∀ᶠ n in Filter.atTop,
        DifferentiableOn ℂ (fun z : ℂ ↦ F n (e.symm z)) W := by
    filter_upwards [hholoU] with n hn
    have hcomp :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n ∘ e.symm) W :=
      hn.comp
        ((mdifferentiableOn_extChartAt_symm (I := 𝓘(ℂ)) (x := x)).mono
          (fun z hz ↦ (hWV hz).1))
        (fun z hz ↦ (hWV hz).2)
    rw [mdifferentiableOn_iff_differentiableOn] at hcomp
    simpa [Function.comp_def] using hcomp
  have hdiffOn : DifferentiableOn ℂ (fun z : ℂ ↦ g (e.symm z)) W :=
    hconvChart.differentiableOn hFdiff hWopen
  have hdiffAt : DifferentiableAt ℂ (fun z : ℂ ↦ g (e.symm z)) (e x) :=
    hdiffOn.differentiableAt (hWopen.mem_nhds hxW)
  have hI : Set.range 𝓘(ℂ) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  have hFcontU : ∀ᶠ n : ℕ in Filter.atTop, ContinuousOn (F n) U :=
    hholoU.mono fun _n hn ↦ hn.continuousOn
  have hgcontU : ContinuousOn g U :=
    (hconv.tendstoLocallyUniformlyOn.mono (Set.subset_univ U)).continuousOn
      hFcontU.frequently
  rw [mdifferentiableAt_iff_of_mem_source
    (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (x := x) (x' := x) (y := g x)
    (f := g) (mem_chart_source ℂ x) (Set.mem_univ (g x))]
  refine ⟨hgcontU.continuousAt (hUopen.mem_nhds hxU), ?_⟩
  rw [hI, differentiableWithinAt_univ]
  simpa [Function.comp_def, e] using hdiffAt

/--
%%handwave
name:
  Injectivity survives an expanding-domain normal limit
statement:
  Suppose complex-valued functions on a Riemann surface converge
  locally uniformly to a nonconstant function.  If the functions are
  eventually holomorphic near every point and eventually injective on every
  compact set, then the limit is injective.
proof:
  The eventual-domain Weierstrass theorem makes the limit holomorphic.  If two
  distinct points had the same value, isolate the first point in that fiber
  and work in a small complex coordinate disk around it.  Uniform convergence
  leaves a positive boundary gap, so the quantitative open-mapping theorem
  forces the approximating value at the second point to occur in the coordinate
  disk.  Compact-local injectivity then identifies this point with the second
  one, contradicting the choice of the isolated neighborhood.
-/
theorem locallyUniformLimit_injective_of_eventuallyInjectiveOn_compacts
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (F : ℕ → X → ℂ) (g : X → ℂ)
    (hconv : TendstoLocallyUniformly F g Filter.atTop)
    (hholo : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n) U)
    (hinj : ∀ K : Set X, IsCompact K →
      ∀ᶠ n : ℕ in Filter.atTop, Set.InjOn (F n) K)
    (hnonconstant : (Set.range g).Nontrivial) :
    Function.Injective g := by
  have hg : HolomorphicMap X ℂ g :=
    locallyUniformLimit_eventuallyHolomorphic X F g hconv hholo
  intro x y hxy
  by_contra hxyne
  rcases nonconstant_holomorphicMap_exists_isolatedFiber_neighborhood
      hg hnonconstant x with ⟨P, hPopen, hxP, hPiso⟩
  have hy_not_P : y ∉ P := by
    intro hyP
    exact (hPiso y hyP (Ne.symm hxyne)) hxy.symm
  rcases hholo x with ⟨V, hVopen, hxV, hlate⟩
  let e := extChartAt 𝓘(ℂ) x
  have hx_target : e x ∈ e.target :=
    mem_extChartAt_target (I := 𝓘(ℂ)) x
  have hx_source : x ∈ e.source :=
    mem_extChartAt_source (I := 𝓘(ℂ)) x
  have hsymm_contAt : ContinuousAt e.symm (e x) :=
    (continuousOn_extChartAt_symm (I := 𝓘(ℂ)) x).continuousAt
      ((isOpen_extChartAt_target (I := 𝓘(ℂ)) x).mem_nhds hx_target)
  have hlocal : e.target ∩ e.symm ⁻¹' (P ∩ V) ∈ 𝓝 (e x) := by
    refine Filter.inter_mem
      ((isOpen_extChartAt_target (I := 𝓘(ℂ)) x).mem_nhds hx_target) ?_
    have hxPV : e.symm (e x) ∈ P ∩ V := by
      simpa [e.left_inv hx_source] using And.intro hxP hxV
    exact hsymm_contAt ((hPopen.inter hVopen).mem_nhds hxPV)
  rcases Metric.mem_nhds_iff.mp hlocal with ⟨R, hR, hRsub⟩
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hclosed_sub : closedBall (e x) r ⊆ e.target ∩ e.symm ⁻¹' (P ∩ V) :=
    (closedBall_subset_ball hrR).trans hRsub
  have hball_target : ball (e x) R ⊆ e.target := fun z hz ↦ (hRsub hz).1
  have hballV : MapsTo e.symm (ball (e x) R) V :=
    fun z hz ↦ (hRsub hz).2.2
  let Fc : ℕ → ℂ → ℂ := fun n z ↦ F n (e.symm z)
  let gc : ℂ → ℂ := fun z ↦ g (e.symm z)
  have hconvChart : TendstoLocallyUniformlyOn Fc gc Filter.atTop (ball (e x) R) := by
    have hglobal : TendstoLocallyUniformlyOn F g Filter.atTop Set.univ :=
      hconv.tendstoLocallyUniformlyOn
    have hcomp := hglobal.comp e.symm
      (fun z (_hz : z ∈ ball (e x) R) ↦ Set.mem_univ (e.symm z))
      ((continuousOn_extChartAt_symm (I := 𝓘(ℂ)) x).mono hball_target)
    simpa [Fc, gc, Function.comp_def] using hcomp
  have hFdiff : ∀ᶠ n : ℕ in Filter.atTop,
      DifferentiableOn ℂ (Fc n) (ball (e x) R) := by
    filter_upwards [hlate] with n hn
    have hcomp :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n ∘ e.symm) (ball (e x) R) :=
      hn.comp
        ((mdifferentiableOn_extChartAt_symm (I := 𝓘(ℂ)) (x := x)).mono
          hball_target)
        hballV
    rw [mdifferentiableOn_iff_differentiableOn] at hcomp
    simpa [Fc, Function.comp_def] using hcomp
  have hgdiff : DifferentiableOn ℂ gc (ball (e x) R) :=
    hconvChart.differentiableOn hFdiff isOpen_ball
  have hcenter : e.symm (e x) = x := e.left_inv hx_source
  have hne_sphere : ∀ z ∈ sphere (e x) r, gc z ≠ gc (e x) := by
    intro z hz
    have hzclosed : z ∈ closedBall (e x) r := sphere_subset_closedBall hz
    have hz_target : z ∈ e.target := (hclosed_sub hzclosed).1
    have hzP : e.symm z ∈ P := (hclosed_sub hzclosed).2.1
    have hzne : e.symm z ≠ x := by
      intro hzx
      have := congrArg e hzx
      rw [e.right_inv hz_target] at this
      have hzcenter : z = e x := this
      exact (ne_of_mem_sphere hz hr.ne.symm) hzcenter
    simpa [gc, hcenter] using hPiso (e.symm z) hzP hzne
  have hsphere_nonempty : (sphere (e x) r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  have hcont_sphere : ContinuousOn (fun z : ℂ ↦ ‖gc z - gc (e x)‖)
      (sphere (e x) r) :=
    continuous_norm.comp_continuousOn
      ((hgdiff.continuousOn.sub continuousOn_const).mono
        (sphere_subset_closedBall.trans (closedBall_subset_ball hrR)))
  obtain ⟨z₀, hz₀, hz₀min⟩ :=
    (isCompact_sphere (e x) r).exists_isMinOn hsphere_nonempty hcont_sphere
  let ε : ℝ := ‖gc z₀ - gc (e x)‖
  have hε : 0 < ε := norm_pos_iff.mpr (sub_ne_zero.mpr (hne_sphere z₀ hz₀))
  have hboundary_min : ∀ z ∈ sphere (e x) r,
      ε ≤ dist (gc z) (gc (e x)) := by
    intro z hz
    simpa [ε, dist_eq_norm] using hz₀min hz
  have hconvClosed : TendstoUniformlyOn Fc gc Filter.atTop (closedBall (e x) r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hconvChart
      (closedBall (e x) r) (closedBall_subset_ball hrR)
      (isCompact_closedBall (e x) r)
  have hclose : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ z ∈ closedBall (e x) r, dist (gc z) (Fc n z) < ε / 8 :=
    Metric.tendstoUniformlyOn_iff.mp hconvClosed (ε / 8) (by positivity)
  have hyconv : Tendsto (fun n : ℕ ↦ F n y) Filter.atTop (𝓝 (g y)) :=
    hconv.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ y)
  have hyclose : ∀ᶠ n : ℕ in Filter.atTop,
      dist (F n y) (g y) < ε / 8 :=
    (Metric.tendsto_nhds.mp hyconv) (ε / 8) (by positivity)
  let K : Set X := insert y (e.symm '' closedBall (e x) r)
  have hsymm_cont : ContinuousOn e.symm (closedBall (e x) r) :=
    (continuousOn_extChartAt_symm (I := 𝓘(ℂ)) x).mono
      (fun z hz ↦ (hclosed_sub hz).1)
  have hKcompact : IsCompact K :=
    ((isCompact_closedBall (e x) r).image_of_continuousOn hsymm_cont).insert y
  obtain ⟨n, hndiff, hnclose, hnyclose, hninj⟩ :=
    (hFdiff.and (hclose.and (hyclose.and (hinj K hKcompact)))).exists
  have hcenter_closed : e x ∈ closedBall (e x) r := mem_closedBall_self hr.le
  have hboundary : ∀ z ∈ sphere (e x) r,
      ε / 2 ≤ ‖Fc n z - Fc n (e x)‖ := by
    intro z hz
    have hzclosed : z ∈ closedBall (e x) r := sphere_subset_closedBall hz
    have htri := dist_triangle4 (gc z) (Fc n z) (Fc n (e x)) (gc (e x))
    have hxclose : dist (Fc n (e x)) (gc (e x)) < ε / 8 := by
      simpa [dist_comm] using hnclose (e x) hcenter_closed
    have hdistbound : ε / 2 ≤ dist (Fc n z) (Fc n (e x)) := by
      linarith [hboundary_min z hz, hnclose z hzclosed, hxclose]
    simpa only [dist_eq_norm] using hdistbound
  have htarget : F n y ∈ ball (Fc n (e x)) ((ε / 2) / 2) := by
    rw [mem_ball]
    have htri := dist_triangle4 (F n y) (g y) (g x) (Fc n (e x))
    have hxclose : dist (g x) (Fc n (e x)) < ε / 8 := by
      simpa [gc, Fc, hcenter] using hnclose (e x) hcenter_closed
    rw [hxy] at htri hxclose
    rw [dist_self, add_zero] at htri
    linarith
  have hndcc : DiffContOnCl ℂ (Fc n) (ball (e x) r) :=
    hndiff.diffContOnCl_ball (closedBall_subset_ball hrR)
  have hnfrequent : ∃ᶠ z in 𝓝 (e x), Fc n z ≠ Fc n (e x) := by
    by_contra hnotfreq
    have hnlocal : ∀ᶠ z in 𝓝 (e x), Fc n z = Fc n (e x) := by
      simpa only [not_ne_iff] using (not_frequently.mp hnotfreq)
    have hnanalytic : AnalyticOnNhd ℂ (Fc n) (ball (e x) r) :=
      hndcc.differentiableOn.analyticOnNhd isOpen_ball
    have hneqOn := hnanalytic.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (convex_ball (e x) r).isPreconnected
        (mem_ball_self hr) hnlocal
    have hneqClosed :
        Set.EqOn (Fc n) (Function.const ℂ (Fc n (e x)))
          (closedBall (e x) r) := by
      have hcontClosed : ContinuousOn (Fc n) (closedBall (e x) r) := by
        simpa [closure_ball (e x) hr.ne.symm] using hndcc.continuousOn
      refine Set.EqOn.of_subset_closure (t := closedBall (e x) r) hneqOn
        hcontClosed continuousOn_const ball_subset_closedBall ?_
      rw [closure_ball (e x) hr.ne.symm]
    have heq := hneqClosed (sphere_subset_closedBall hz₀)
    have hpos := hboundary z₀ hz₀
    rw [heq] at hpos
    simp only [Function.const_apply, sub_self, norm_zero] at hpos
    linarith
  obtain ⟨z, hzclosed, hzeq⟩ :=
    hndcc.ball_subset_image_closedBall hr hboundary hnfrequent htarget
  have hzK : e.symm z ∈ K := mem_insert_iff.mpr (Or.inr ⟨z, hzclosed, rfl⟩)
  have hyK : y ∈ K := mem_insert y _
  have hzy : e.symm z = y := hninj hzK hyK hzeq
  have hzP : e.symm z ∈ P := (hclosed_sub hzclosed).2.1
  exact hy_not_P (hzy ▸ hzP)


/-- Arzelà--Ascoli on the tails of all compact restrictions, followed by a
diagonal extraction and the eventual-domain Weierstrass theorem. -/
theorem eventualDomain_montel_of_tail_equicontinuous
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SecondCountableTopology X]
    (Kex : CompactExhaustion X) (F : ℕ → X → ℂ)
    (htail :
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ m : ℕ,
        ∃ N : ℕ,
          (∀ n : ℕ, ContinuousOn (F (φ (N + n))) (Kex m)) ∧
          (∀ x ∈ Kex m, ∃ Q : Set ℂ, IsCompact Q ∧
            ∀ n : ℕ, F (φ (N + n)) x ∈ Q) ∧
          EquicontinuousOn (fun n : ℕ ↦ F (φ (N + n))) (Kex m))
    (hholo : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n) U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℂ,
        HolomorphicMap X ℂ f ∧
          TendstoLocallyUniformly
            (fun n : ℕ ↦ F (φ n)) f Filter.atTop := by
  rcases
    functions_subsequence_tendstoLocallyUniformly_of_compactExhaustion_tail_equicontinuous
      Kex htail with
    ⟨φ, hφ, f, hconv⟩
  have hφ_top : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ.tendsto_atTop
  have hholo_sub :
      ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F (φ n)) U := by
    intro x
    rcases hholo x with ⟨U, hUopen, hxU, hlate⟩
    exact ⟨U, hUopen, hxU, hφ_top.eventually hlate⟩
  exact ⟨φ, hφ, f,
    locallyUniformLimit_eventuallyHolomorphic X
      (fun n : ℕ ↦ F (φ n)) f hconv hholo_sub,
    hconv⟩

/-- A uniformly bounded holomorphic family has a common coordinate
Lipschitz estimate on a smaller coordinate disk. -/
theorem holomorphicMaps_chart_dist_le_of_norm_le
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {V : Set X} (F : ℕ → X → ℂ) {B : ℝ}
    (hholo : ∀ n : ℕ,
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n) V)
    (hbound : ∀ n : ℕ, ∀ z ∈ V, ‖F n z‖ ≤ B)
    (x y : X) {R : ℝ}
    (hball :
      Metric.ball ((extChartAt 𝓘(ℂ) x) x) R ⊆
        (extChartAt 𝓘(ℂ) x).target)
    (hballV : Set.MapsTo (extChartAt 𝓘(ℂ) x).symm
      (Metric.ball ((extChartAt 𝓘(ℂ) x) x) R) V)
    (hy_source : y ∈ (extChartAt 𝓘(ℂ) x).source)
    (hy_ball :
      (extChartAt 𝓘(ℂ) x) y ∈
        Metric.ball ((extChartAt 𝓘(ℂ) x) x) R) :
    ∀ n : ℕ,
      dist (F n x) (F n y) ≤
        ((2 * B) / R) *
          dist ((extChartAt 𝓘(ℂ) x) x) ((extChartAt 𝓘(ℂ) x) y) := by
  intro n
  let e := extChartAt 𝓘(ℂ) x
  let f : ℂ → ℂ := fun z : ℂ ↦ F n (e.symm z)
  have hx_source : x ∈ e.source := mem_extChartAt_source (I := 𝓘(ℂ)) x
  have hdiff : DifferentiableOn ℂ f (Metric.ball (e x) R) := by
    have hcomp :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n ∘ e.symm)
          (Metric.ball (e x) R) :=
      (hholo n).comp
        ((mdifferentiableOn_extChartAt_symm (I := 𝓘(ℂ)) (x := x)).mono
          hball)
        hballV
    rw [mdifferentiableOn_iff_differentiableOn] at hcomp
    simpa [f, Function.comp_def, e] using hcomp
  have hR : 0 < R := by
    exact lt_of_le_of_lt dist_nonneg (by
      simpa [Metric.mem_ball] using hy_ball)
  have hmaps :
      Set.MapsTo f (Metric.ball (e x) R)
        (Metric.closedBall (f (e x)) (2 * B)) := by
    intro z hz
    have hzV : e.symm z ∈ V := hballV hz
    have hxV : e.symm (e x) ∈ V := hballV (Metric.mem_ball_self hR)
    have hzdist : dist (f z) (f (e x)) ≤ 2 * B := by
      calc
        dist (f z) (f (e x)) = ‖f z - f (e x)‖ := by rw [dist_eq_norm]
        _ ≤ ‖f z‖ + ‖f (e x)‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hbound n _ hzV) (hbound n _ hxV)
        _ = 2 * B := by ring
    simpa [Metric.mem_closedBall] using hzdist
  have hschwarz :
      dist (f (e y)) (f (e x)) ≤
        ((2 * B) / R) * dist (e y) (e x) :=
    Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hy_ball
  have hy_eq : e.symm (e y) = y := e.left_inv hy_source
  have hx_eq : e.symm (e x) = x := e.left_inv hx_source
  change
      dist (F n (e.symm (e y))) (F n (e.symm (e x))) ≤
        ((2 * B) / R) * dist (e y) (e x) at hschwarz
  rw [hy_eq, hx_eq] at hschwarz
  simpa [e, dist_comm] using hschwarz

/-- A family which is holomorphic and uniformly bounded on an open set is
equicontinuous on every subset of that open set. -/
theorem boundedHolomorphicMaps_equicontinuousOn
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {V K : Set X} (hVopen : IsOpen V) (hKV : K ⊆ V)
    (F : ℕ → X → ℂ) {B : ℝ} (hB : 0 < B)
    (hholo : ∀ n : ℕ,
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n) V)
    (hbound : ∀ n : ℕ, ∀ z ∈ V, ‖F n z‖ ≤ B) :
    EquicontinuousOn F K := by
  intro x hx U hU
  rcases Metric.mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
  let e := extChartAt 𝓘(ℂ) x
  have hx_target : e x ∈ e.target :=
    mem_extChartAt_target (I := 𝓘(ℂ)) x
  have hxV : e.symm (e x) ∈ V := by
    have hx_source : x ∈ e.source :=
      mem_extChartAt_source (I := 𝓘(ℂ)) x
    simpa [e.left_inv hx_source] using hKV hx
  have hsymm_contAt : ContinuousAt e.symm (e x) :=
    (continuousOn_extChartAt_symm (I := 𝓘(ℂ)) x).continuousAt
      ((isOpen_extChartAt_target (I := 𝓘(ℂ)) x).mem_nhds hx_target)
  have hlocal_target : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e x) := by
    refine Filter.inter_mem
      ((isOpen_extChartAt_target (I := 𝓘(ℂ)) x).mem_nhds hx_target) ?_
    exact hsymm_contAt (hVopen.mem_nhds hxV)
  rcases Metric.mem_nhds_iff.mp hlocal_target with
    ⟨R, hR, hRsubset⟩
  have hball_target : Metric.ball (e x) R ⊆ e.target :=
    fun z hz ↦ (hRsubset hz).1
  have hballV : Set.MapsTo e.symm (Metric.ball (e x) R) V :=
    fun z hz ↦ (hRsubset hz).2
  let δ : ℝ := min (R / 2) (ε * R / (4 * B))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hR) (by positivity)
  have hδR : δ < R := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcoef_nonneg : 0 ≤ (2 * B) / R := by positivity
  have hcoefδ : ((2 * B) / R) * δ < ε := by
    have hδle : δ ≤ ε * R / (4 * B) := by
      dsimp [δ]
      exact min_le_right _ _
    have hmul_le :
        ((2 * B) / R) * δ ≤
          ((2 * B) / R) * (ε * R / (4 * B)) :=
      mul_le_mul_of_nonneg_left hδle hcoef_nonneg
    have hcalc :
        ((2 * B) / R) * (ε * R / (4 * B)) = ε / 2 := by
      field_simp [hR.ne', hB.ne']
      ring
    have hhalf : ε / 2 < ε := by linarith
    exact hmul_le.trans_lt (by simpa [hcalc] using hhalf)
  have hchartBall :
      e ⁻¹' Metric.ball (e x) δ ∈ 𝓝 x :=
    (continuousAt_extChartAt (I := 𝓘(ℂ)) x).preimage_mem_nhds
      (Metric.ball_mem_nhds (e x) hδpos)
  have hsource : e.source ∈ 𝓝 x :=
    extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x
  have hlocal : e.source ∩ e ⁻¹' Metric.ball (e x) δ ∈ 𝓝 x :=
    Filter.inter_mem hsource hchartBall
  filter_upwards [mem_nhdsWithin_of_mem_nhds hlocal] with y hy n
  have hy_source : y ∈ e.source := hy.1
  have hyδ : e y ∈ Metric.ball (e x) δ := hy.2
  have hcoordδ : dist (e x) (e y) < δ := by
    simpa [Metric.mem_ball, dist_comm] using hyδ
  have hyR : e y ∈ Metric.ball (e x) R := by
    rw [Metric.mem_ball]
    have hcoordδ' : dist (e y) (e x) < δ := by
      simpa [dist_comm] using hcoordδ
    exact hcoordδ'.trans hδR
  have hdist :
      dist (F n x) (F n y) ≤
        ((2 * B) / R) * dist (e x) (e y) :=
    holomorphicMaps_chart_dist_le_of_norm_le X F hholo hbound
      x y hball_target hballV hy_source hyR n
  have hsmall : ((2 * B) / R) * dist (e x) (e y) < ε :=
    (mul_lt_mul_of_pos_left hcoordδ (by positivity)).trans hcoefδ
  exact hεU (lt_of_le_of_lt hdist hsmall)

/--
%%handwave
name:
  Montel extraction on expanding domains
statement:
  Let complex-valued functions be defined on a Riemann surface and become
  holomorphic and uniformly bounded on a neighborhood of each member of a
  compact exhaustion.  Then some subsequence converges locally uniformly to
  a holomorphic function on the whole surface.
proof:
  The coordinate Schwarz estimate makes every sufficiently late tail
  equicontinuous on each compact member.  Its values lie in one compact
  Euclidean disk, so Arzelà--Ascoli gives compact-restriction subsequences.
  A diagonal extraction gives locally uniform convergence, and the
  eventual-domain Weierstrass theorem makes the limit holomorphic.
-/
theorem eventualDomain_montel_of_eventually_boundedOn_exhaustion_neighborhoods
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SecondCountableTopology X]
    (Kex : CompactExhaustion X) (F : ℕ → X → ℂ)
    (hlocalBound :
      ∀ m : ℕ, ∃ V : Set X, ∃ N : ℕ, ∃ B : ℝ,
        IsOpen V ∧ Kex m ⊆ V ∧ 0 < B ∧
          ∀ n : ℕ, N ≤ n →
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n) V ∧
              ∀ x ∈ V, ‖F n x‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℂ,
        HolomorphicMap X ℂ f ∧
          TendstoLocallyUniformly
            (fun n : ℕ ↦ F (φ n)) f Filter.atTop := by
  have htail :
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ m : ℕ,
        ∃ N : ℕ,
          (∀ n : ℕ, ContinuousOn (F (φ (N + n))) (Kex m)) ∧
          (∀ x ∈ Kex m, ∃ Q : Set ℂ, IsCompact Q ∧
            ∀ n : ℕ, F (φ (N + n)) x ∈ Q) ∧
          EquicontinuousOn (fun n : ℕ ↦ F (φ (N + n))) (Kex m) := by
    intro φ hφ m
    rcases hlocalBound m with
      ⟨V, N, B, hVopen, hKV, hB, hlate⟩
    have hindex : ∀ n : ℕ, N ≤ φ (N + n) := by
      intro n
      exact le_trans (Nat.le_add_right N n) (StrictMono.id_le hφ (N + n))
    have hholoTail : ∀ n : ℕ,
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F (φ (N + n))) V :=
      fun n ↦ (hlate _ (hindex n)).1
    have hboundTail : ∀ n : ℕ, ∀ x ∈ V, ‖F (φ (N + n)) x‖ ≤ B :=
      fun n ↦ (hlate _ (hindex n)).2
    refine ⟨N, ?_, ?_, ?_⟩
    · intro n
      exact (hholoTail n).continuousOn.mono hKV
    · intro x hx
      refine ⟨Metric.closedBall (0 : ℂ) B,
        isCompact_closedBall (0 : ℂ) B, ?_⟩
      intro n
      have hnorm := hboundTail n x (hKV hx)
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    · exact boundedHolomorphicMaps_equicontinuousOn
        X hVopen hKV (fun n : ℕ ↦ F (φ (N + n))) hB
        hholoTail hboundTail
  have hholo : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F n) U := by
    intro x
    rcases hlocalBound (Kex.find x) with
      ⟨V, N, _B, hVopen, hKV, _hB, hlate⟩
    refine ⟨V, hVopen, hKV (Kex.mem_find x), ?_⟩
    exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ (hlate n hn).1⟩
  exact eventualDomain_montel_of_tail_equicontinuous X Kex F htail hholo

/-- A holomorphic transition map between centered disks which fixes the
origin and has derivative one cannot decrease the radius. -/
theorem normalized_transition_source_radius_le_target_radius
    {r s : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hmaps : MapsTo f (ball 0 r) (ball 0 s))
    (hzero : f 0 = 0) (hone : deriv f 0 = 1) :
    r ≤ s := by
  have hmaps_closed : MapsTo f (ball 0 r) (closedBall (f 0) s) := by
    intro z hz
    simpa [hzero] using ball_subset_closedBall (hmaps hz)
  have hschwarz : ‖deriv f 0‖ ≤ s / r :=
    Complex.norm_deriv_le_div_of_mapsTo_ball
      hf.differentiableOn hmaps_closed hr
  rw [hone, norm_one] at hschwarz
  have hrs : (1 : ℝ) * r ≤ s :=
    (le_div_iff₀ hr).mp (by simpa using hschwarz)
  linarith

/-- If the normalized transition between two centered disks is not the
identity on its source, then the target radius is strictly larger. -/
theorem normalized_transition_source_radius_lt_target_radius
    {r s : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hmaps : MapsTo f (ball 0 r) (ball 0 s))
    (hzero : f 0 = 0) (hone : deriv f 0 = 1)
    (hnotid : ¬EqOn f id (ball 0 r)) :
    r < s := by
  have hrs : r ≤ s :=
    normalized_transition_source_radius_le_target_radius
      hr hf hmaps hzero hone
  apply hrs.lt_of_ne
  intro hrs_eq
  subst s
  have hmaps_closed : MapsTo f (ball 0 r) (closedBall (f 0) r) := by
    intro z hz
    simpa [hzero] using ball_subset_closedBall (hmaps hz)
  have hdslope : ‖dslope f 0 0‖ = r / r := by
    simp [hone, hr.ne']
  have haffine :=
    Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
      hf.differentiableOn hmaps_closed (mem_ball_self hr) hdslope
  apply hnotid
  intro z hz
  have hz_eq := haffine hz
  simpa [hzero, hone] using hz_eq

/-- An omitted value of a normalized univalent function on the unit disk has
reciprocal norm at most four. -/
theorem koebe_omitted_value_reciprocal_norm_le_four
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1))
    (hzero : f 0 = 0)
    (hone : deriv f 0 = 1)
    {w : ℂ} (hw : w ∉ f '' ball 0 1) :
    ‖w⁻¹‖ ≤ 4 := by
  have hquarter : ball (0 : ℂ) (1 / 4 : ℝ) ⊆ f '' ball 0 1 :=
    koebe_quarter_normalized hf hinj hzero hone
  have hw_not_ball : w ∉ ball (0 : ℂ) (1 / 4 : ℝ) := by
    intro hw_ball
    exact hw (hquarter hw_ball)
  have hw_norm : (1 / 4 : ℝ) ≤ ‖w‖ := by
    simpa [mem_ball_zero_iff, not_lt] using hw_not_ball
  have hw_pos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hw_norm
  rw [norm_inv]
  apply (inv_le_comm₀ hw_pos (by norm_num : (0 : ℝ) < 4)).mpr
  norm_num at hw_norm ⊢
  exact hw_norm

/-- Suppose a normalized univalent disk map parametrizes a subset of the
image of an injective map on a larger set.  At every point of the larger set
outside the parametrized core, the reciprocal of the latter map is bounded
by four.  This is the estimate applied to `1 / φₘ` in Hubbard's exhaustion
argument. -/
theorem koebe_reciprocal_norm_le_four_outside_core
    {X : Type*} {core larger : Set X} {f : ℂ → ℂ} {φ : X → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hfinj : InjOn f (ball 0 1))
    (hfzero : f 0 = 0)
    (hfone : deriv f 0 = 1)
    (himage : f '' ball 0 1 ⊆ φ '' core)
    (hcore : core ⊆ larger)
    (hφinj : InjOn φ larger)
    {x : X} (hx : x ∈ larger) (hxcore : x ∉ core) :
    ‖(φ x)⁻¹‖ ≤ 4 := by
  apply koebe_omitted_value_reciprocal_norm_le_four hf hfinj hfzero hfone
  intro hximage
  rcases himage hximage with ⟨y, hycore, hy⟩
  have hy_larger : y ∈ larger := hcore hycore
  have hyx : y = x := hφinj hy_larger hx hy
  exact hxcore (hyx ▸ hycore)

/-- The analytic quotient `f(z) / z` of a disk self-map fixing the origin has
norm at most one.  At the origin the quotient is interpreted as `f'(0)`. -/
theorem diskSelfMap_diskNormalizedQuotient_norm_le_one
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1))
    (hzero : f 0 = 0) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖diskNormalizedQuotient f z‖ ≤ 1 := by
  have hmapsClosed : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
    intro w hw
    simpa [hzero] using ball_subset_closedBall (hmaps hw)
  have hq := Complex.norm_dslope_le_div_of_mapsTo_ball
    hf.differentiableOn hmapsClosed hz
  by_cases hz0 : z = 0
  · subst z
    simpa [diskNormalizedQuotient, dslope_same] using hq
  · rw [diskNormalizedQuotient, if_neg hz0]
    rw [dslope_of_ne _ hz0] at hq
    calc
      ‖f z / z‖ = ‖slope f 0 z‖ := by
        congr 1
        simp [slope_def_module, hzero, div_eq_mul_inv, mul_comm]
      _ ≤ 1 := by simpa using hq

/-- A disk self-map fixing the origin and having positive real derivative
`a` is close to the identity on compact subdisks when `a` is close to one.
This is the Borel--Carathéodory estimate applied to `f(z) / z - a`. -/
theorem normalized_diskSelfMap_quotient_sub_one_norm_le
    {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1))
    (hzero : f 0 = 0) (hderiv : deriv f 0 = (a : ℂ))
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖diskNormalizedQuotient f z - 1‖ ≤
      2 * (1 - a) * ‖z‖ / (1 - ‖z‖) + (1 - a) := by
  by_cases ha : a = 1
  · subst a
    have hmapsClosed : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
      intro w hw
      simpa [hzero] using ball_subset_closedBall (hmaps hw)
    have haffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
      hf.differentiableOn hmapsClosed (mem_ball_self zero_lt_one)
      (by simp [hderiv])
    have hfz : f z = z := by
      simpa [hzero, hderiv] using haffine hz
    by_cases hz0 : z = 0
    · simp [hz0, hderiv]
    · rw [diskNormalizedQuotient, if_neg hz0, hfz]
      field_simp
      simp
  · have hM : 0 < 1 - a := sub_pos.mpr (lt_of_le_of_ne ha1 ha)
    let q : ℂ → ℂ := diskNormalizedQuotient f
    let g : ℂ → ℂ := fun w ↦ q w - (a : ℂ)
    have hq : AnalyticOnNhd ℂ q (ball 0 1) := by
      simpa [q] using diskNormalizedQuotient_analyticOnNhd hf hzero
    have hgdiff : DifferentiableOn ℂ g (ball 0 1) :=
      hq.differentiableOn.sub (differentiableOn_const (c := (a : ℂ)))
    have hgMaps : MapsTo g (ball 0 1) {w : ℂ | w.re ≤ 1 - a} := by
      intro w hw
      have hnorm :=
        diskSelfMap_diskNormalizedQuotient_norm_le_one hf hmaps hzero hw
      have hre : (q w).re ≤ 1 :=
        (Complex.re_le_norm (q w)).trans hnorm
      simpa [g] using sub_le_sub_right hre a
    have hgzero : g 0 = 0 := by
      simp [g, q, hderiv]
    have hBC : ‖g z‖ ≤ 2 * (1 - a) * ‖z‖ / (1 - ‖z‖) :=
      Complex.borelCaratheodory_zero hM hgdiff hgMaps zero_lt_one hz hgzero
    calc
      ‖diskNormalizedQuotient f z - 1‖ = ‖g z + ((a : ℂ) - 1)‖ := by
        congr 1
        simp [g, q]
      _ ≤ ‖g z‖ + ‖(a : ℂ) - 1‖ := norm_add_le _ _
      _ ≤ 2 * (1 - a) * ‖z‖ / (1 - ‖z‖) + (1 - a) := by
        rw [show ‖(a : ℂ) - 1‖ = 1 - a by
          calc
            ‖(a : ℂ) - 1‖ = ‖a - 1‖ := by
              simpa using Complex.norm_real (a - 1)
            _ = |a - 1| := Real.norm_eq_abs _
            _ = 1 - a := by
              rw [abs_of_nonpos (sub_nonpos.mpr ha1)]
              ring]
        gcongr

/-- The corresponding pointwise estimate for the self-map itself. -/
theorem normalized_diskSelfMap_sub_id_norm_le
    {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1))
    (hzero : f 0 = 0) (hderiv : deriv f 0 = (a : ℂ))
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖f z - z‖ ≤ ‖z‖ *
      (2 * (1 - a) * ‖z‖ / (1 - ‖z‖) + (1 - a)) := by
  have hmul := diskNormalizedQuotient_mul hzero z
  calc
    ‖f z - z‖ = ‖z * (diskNormalizedQuotient f z - 1)‖ := by
      rw [mul_sub, mul_one, hmul]
    _ = ‖z‖ * ‖diskNormalizedQuotient f z - 1‖ := norm_mul _ _
    _ ≤ ‖z‖ *
        (2 * (1 - a) * ‖z‖ / (1 - ‖z‖) + (1 - a)) :=
      mul_le_mul_of_nonneg_left
        (normalized_diskSelfMap_quotient_sub_one_norm_le
          hf hmaps hzero hderiv ha0 ha1 hz) (norm_nonneg z)

/-- A univalent disk map which is uniformly close to the identity on a
closed disk assumes the value at the center somewhere in that disk. -/
theorem diskMap_mem_image_closedBall_of_closeToIdentity
    {f : ℂ → ℂ} {w : ℂ} {δ : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1))
    (hδ : 0 < δ)
    (hclosed : closedBall w δ ⊆ ball (0 : ℂ) 1)
    (hclose : ∀ z ∈ closedBall w δ, ‖f z - z‖ < δ / 8) :
    w ∈ f '' closedBall w δ := by
  have hdiffCl : DiffContOnCl ℂ f (ball w δ) := by
    refine ⟨hf.differentiableOn.mono
      (ball_subset_closedBall.trans hclosed), ?_⟩
    rw [closure_ball w hδ.ne']
    exact hf.continuousOn.mono hclosed
  have hboundary : ∀ z ∈ sphere w δ,
      δ / 2 ≤ ‖f z - f w‖ := by
    intro z hz
    have hzclosed : z ∈ closedBall w δ := sphere_subset_closedBall hz
    have hwclosed : w ∈ closedBall w δ := mem_closedBall_self hδ.le
    have htri : ‖z - w‖ ≤ ‖z - f z‖ + ‖f z - f w‖ + ‖f w - w‖ := by
      calc
        ‖z - w‖ = ‖(z - f z) + (f z - f w) + (f w - w)‖ := by
          congr 1
          ring
        _ ≤ ‖z - f z‖ + ‖f z - f w‖ + ‖f w - w‖ :=
          (norm_add_le _ _).trans (by
            gcongr
            exact norm_add_le _ _)
    have hzclose : ‖z - f z‖ < δ / 8 := by
      simpa [norm_sub_rev] using hclose z hzclosed
    have hwclose : ‖f w - w‖ < δ / 8 := hclose w hwclosed
    have hzw : ‖z - w‖ = δ := by
      simpa [mem_sphere_iff_norm] using hz
    rw [hzw] at htri
    linarith
  have hfrequent : ∃ᶠ z in 𝓝 w, f z ≠ f w := by
    apply not_eventually.mp
    intro heq
    have hwball : w ∈ ball (0 : ℂ) 1 :=
      hclosed (mem_closedBall_self hδ.le)
    have hlocal : {z : ℂ | f z = f w} ∩ ball (0 : ℂ) 1 ∈ 𝓝 w :=
      Filter.inter_mem heq (isOpen_ball.mem_nhds hwball)
    rcases Metric.mem_nhds_iff.mp hlocal with ⟨ε, hε, hεsub⟩
    let z : ℂ := w + (ε / 2 : ℝ)
    have hzmem : z ∈ ball w ε := by
      rw [mem_ball, dist_eq_norm]
      have hzsub : z - w = ((ε / 2 : ℝ) : ℂ) := by
        simp [z]
      rw [hzsub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    have hzlocal := hεsub hzmem
    have hzw : z = w := hinj hzlocal.2 hwball hzlocal.1
    have hεzero : (ε / 2 : ℂ) = 0 := by
      simpa [z] using sub_eq_zero.mpr hzw
    have : ε / 2 = 0 := by
      simpa using congrArg Complex.re hεzero
    linarith
  have hwtarget : w ∈ ball (f w) ((δ / 2) / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hwclose := hclose w (mem_closedBall_self hδ.le)
    simpa [norm_sub_rev] using lt_of_lt_of_le hwclose (by linarith)
  exact hdiffCl.ball_subset_image_closedBall hδ hboundary hfrequent hwtarget

/-- Disk self-maps fixing the origin whose positive real derivatives tend to
one eventually cover every prescribed point of the disk. -/
theorem normalized_diskSelfMaps_eventually_mem_image
    (F : ℕ → ℂ → ℂ) (a : ℕ → ℝ)
    (hF : ∀ n : ℕ, AnalyticOnNhd ℂ (F n) (ball 0 1))
    (hinj : ∀ n : ℕ, InjOn (F n) (ball 0 1))
    (hmaps : ∀ n : ℕ, MapsTo (F n) (ball 0 1) (ball 0 1))
    (hzero : ∀ n : ℕ, F n 0 = 0)
    (hderiv : ∀ n : ℕ, deriv (F n) 0 = (a n : ℂ))
    (ha0 : ∀ n : ℕ, 0 < a n) (ha1 : ∀ n : ℕ, a n ≤ 1)
    (hatendsto : Tendsto a Filter.atTop (𝓝 1))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∀ᶠ n : ℕ in Filter.atTop, w ∈ F n '' ball (0 : ℂ) 1 := by
  let δ : ℝ := (1 - ‖w‖) / 4
  let ρ : ℝ := ‖w‖ + δ
  have hwnorm : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ1 : ρ < 1 := by
    dsimp [ρ, δ]
    linarith
  let C : ℝ := ρ * (2 * ρ / (1 - ρ) + 1)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos hρ0 (by
      have : 0 < 1 - ρ := sub_pos.mpr hρ1
      positivity)
  let η : ℝ := δ / (8 * C)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have haLower : ∀ᶠ n : ℕ in Filter.atTop, 1 - η < a n :=
    hatendsto (Ioi_mem_nhds (by linarith : 1 - η < (1 : ℝ)))
  filter_upwards [haLower] with n han
  have hclosed : closedBall w δ ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hzw : ‖z - w‖ ≤ δ := by
      simpa [mem_closedBall, dist_eq_norm] using hz
    have hzNorm : ‖z‖ ≤ ρ := by
      calc
        ‖z‖ ≤ ‖z - w‖ + ‖w‖ := norm_le_norm_sub_add z w
        _ ≤ δ + ‖w‖ := by gcongr
        _ = ρ := by simp [ρ, add_comm]
    rw [mem_ball_zero_iff]
    exact hzNorm.trans_lt hρ1
  have hsmall : (1 - a n) * C < δ / 8 := by
    have hnonneg : 0 ≤ 1 - a n := sub_nonneg.mpr (ha1 n)
    have hlt : 1 - a n < η := by linarith
    have hmul := mul_lt_mul_of_pos_right hlt hC
    have hηC : η * C = δ / 8 := by
      dsimp [η]
      field_simp [hC.ne']
    simpa [hηC] using hmul
  have hclose : ∀ z ∈ closedBall w δ, ‖F n z - z‖ < δ / 8 := by
    intro z hz
    have hzNorm : ‖z‖ ≤ ρ := by
      have hzw : ‖z - w‖ ≤ δ := by
        simpa [mem_closedBall, dist_eq_norm] using hz
      calc
        ‖z‖ ≤ ‖z - w‖ + ‖w‖ := norm_le_norm_sub_add z w
        _ ≤ δ + ‖w‖ := by gcongr
        _ = ρ := by simp [ρ, add_comm]
    have hzball : z ∈ ball (0 : ℂ) 1 := hclosed hz
    have hpoint := normalized_diskSelfMap_sub_id_norm_le
      (hF n) (hmaps n) (hzero n) (hderiv n) (ha0 n) (ha1 n) hzball
    have hdenom : 0 < 1 - ρ := sub_pos.mpr hρ1
    have hzdenom : 0 < 1 - ‖z‖ := by
      exact sub_pos.mpr (hzNorm.trans_lt hρ1)
    have hfactorNonneg : 0 ≤ 1 - a n := sub_nonneg.mpr (ha1 n)
    have hinnerNonneg :
        0 ≤ 2 * (1 - a n) * ‖z‖ / (1 - ‖z‖) + (1 - a n) := by
      positivity
    have hinner :
        2 * (1 - a n) * ‖z‖ / (1 - ‖z‖) + (1 - a n) ≤
          2 * (1 - a n) * ρ / (1 - ρ) + (1 - a n) := by
      gcongr
    have hbound :
        ‖z‖ * (2 * (1 - a n) * ‖z‖ / (1 - ‖z‖) + (1 - a n)) ≤
          (1 - a n) * C := by
      calc
        ‖z‖ * (2 * (1 - a n) * ‖z‖ / (1 - ‖z‖) + (1 - a n))
            ≤ ρ * (2 * (1 - a n) * ρ / (1 - ρ) + (1 - a n)) := by
              exact mul_le_mul hzNorm hinner hinnerNonneg hρ0.le
        _ = (1 - a n) * C := by
          dsimp [C]
          field_simp [hdenom.ne']
    exact hpoint.trans_lt (hbound.trans_lt hsmall)
  rcases diskMap_mem_image_closedBall_of_closeToIdentity
      (hF n) (hinj n) hδ hclosed hclose with ⟨z, hz, hzw⟩
  exact ⟨z, hclosed hz, hzw⟩

/--
%%handwave
name:
  Quantitative kernel estimate for a disk self-map
statement:
  Let an injective holomorphic self-map of the unit disk fix zero and have
  derivative \(a\in(0,1]\) there.  Fix \(q\in[0,1)\).  If
  \[
    (1-a)\rho\left(\frac{2\rho}{1-\rho}+1\right)
      < \frac{1-q}{16},\qquad \rho=\frac{q+1}{2},
  \]
  then every point of norm at most \(q\) belongs to the image of the map.
proof:
  Schwarz's lemma and the Borel--Carathéodory estimate make the map uniformly
  close to the identity on the intermediate closed disk of radius \(\rho\)
  when its derivative is close to one.  A quantitative open-mapping argument
  then puts the prescribed point in its image.
-/
theorem normalized_diskSelfMap_mem_image_of_deriv_close
    {f : ℂ → ℂ} {a q : ℝ} {w : ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1))
    (hzero : f 0 = 0) (hderiv : deriv f 0 = (a : ℂ))
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw : ‖w‖ ≤ q)
    (hsmall :
      (1 - a) *
          (((q + 1) / 2) *
            (2 * ((q + 1) / 2) / (1 - ((q + 1) / 2)) + 1)) <
        ((1 - q) / 2) / 8) :
    w ∈ f '' ball (0 : ℂ) 1 := by
  let δ : ℝ := (1 - q) / 2
  let ρ : ℝ := (q + 1) / 2
  let C : ℝ := ρ * (2 * ρ / (1 - ρ) + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    linarith
  have hC : 0 < C := by
    dsimp [C]
    have : 0 < 1 - ρ := sub_pos.mpr hρ1
    positivity
  have hclosed : closedBall w δ ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hzw : ‖z - w‖ ≤ δ := by
      simpa [mem_closedBall, dist_eq_norm] using hz
    have hzNorm : ‖z‖ ≤ ρ := by
      calc
        ‖z‖ ≤ ‖z - w‖ + ‖w‖ := norm_le_norm_sub_add z w
        _ ≤ δ + q := add_le_add hzw hw
        _ = ρ := by simp [δ, ρ]; ring
    rw [mem_ball_zero_iff]
    exact hzNorm.trans_lt hρ1
  have hclose : ∀ z ∈ closedBall w δ, ‖f z - z‖ < δ / 8 := by
    intro z hz
    have hzNorm : ‖z‖ ≤ ρ := by
      have hzw : ‖z - w‖ ≤ δ := by
        simpa [mem_closedBall, dist_eq_norm] using hz
      calc
        ‖z‖ ≤ ‖z - w‖ + ‖w‖ := norm_le_norm_sub_add z w
        _ ≤ δ + q := add_le_add hzw hw
        _ = ρ := by simp [δ, ρ]; ring
    have hzball : z ∈ ball (0 : ℂ) 1 := hclosed hz
    have hpoint := normalized_diskSelfMap_sub_id_norm_le
      hf hmaps hzero hderiv ha0 ha1 hzball
    have hdenom : 0 < 1 - ρ := sub_pos.mpr hρ1
    have hzdenom : 0 < 1 - ‖z‖ :=
      sub_pos.mpr (hzNorm.trans_lt hρ1)
    have hfactorNonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    have hinnerNonneg :
        0 ≤ 2 * (1 - a) * ‖z‖ / (1 - ‖z‖) + (1 - a) := by
      positivity
    have hinner :
        2 * (1 - a) * ‖z‖ / (1 - ‖z‖) + (1 - a) ≤
          2 * (1 - a) * ρ / (1 - ρ) + (1 - a) := by
      gcongr
    have hbound :
        ‖z‖ * (2 * (1 - a) * ‖z‖ / (1 - ‖z‖) + (1 - a)) ≤
          (1 - a) * C := by
      calc
        ‖z‖ * (2 * (1 - a) * ‖z‖ / (1 - ‖z‖) + (1 - a)) ≤
            ρ * (2 * (1 - a) * ρ / (1 - ρ) + (1 - a)) :=
          mul_le_mul hzNorm hinner hinnerNonneg hρ0.le
        _ = (1 - a) * C := by
          dsimp [C]
          field_simp [hdenom.ne']
    exact hpoint.trans_lt (hbound.trans_lt (by simpa [δ, ρ, C] using hsmall))
  rcases diskMap_mem_image_closedBall_of_closeToIdentity
      hf hinj hδ hclosed hclose with ⟨z, hz, hzw⟩
  exact ⟨z, hclosed hz, hzw⟩

/-- A univalent analytic function has nonzero derivative at every point of
its domain. -/
theorem analyticOnNhd_deriv_ne_zero_of_injOn
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    deriv f z ≠ 0 := by
  let U : TopologicalSpace.Opens ℂ := ⟨ball (0 : ℂ) 1, isOpen_ball⟩
  let zU : U := ⟨z, hz⟩
  let g : U → ℂ := fun x ↦ f x
  letI : ComplexOneManifold U := openSubset_complexOneManifold U
  have hg : HolomorphicMap U ℂ g := by
    intro x
    have hf' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (x : ℂ) :=
      (hf x x.2).differentiableAt.mdifferentiableAt
    have hsubSmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤
        (Subtype.val : U → ℂ) := contMDiff_subtype_val
    have hsub : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (Subtype.val : U → ℂ) x :=
      hsubSmooth.contMDiffAt.mdifferentiableAt (by simp)
    change MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ Subtype.val) x
    exact hf'.comp x hsub
  have hginj : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (hinj x.2 y.2 hxy)
  let χ : PointedSurfaceCoordinate U zU :=
    { chart := chartAt ℂ zU
      chart_mem_atlas := chart_mem_atlas ℂ zU
      base_mem_source := mem_chart_source ℂ zU }
  have hne := injective_holomorphicMap_surfaceComplexDerivative_ne_zero
    χ hg hginj
  let hU : Nonempty U := ⟨zU⟩
  let E : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.refl ℂ
  have hz_target : z ∈ (E.subtypeRestr hU).target := by
    have hz_source : z ∈ E.source := by simp [E]
    simpa [E, zU] using E.map_subtype_source hU (x := zU) hz_source
  have heq :
      (fun w : ℂ ↦ f ↑((E.subtypeRestr hU).symm w)) =ᶠ[𝓝 z] f := by
    filter_upwards [(E.subtypeRestr hU).open_target.mem_nhds hz_target] with w hw
    have hval : (↑((E.subtypeRestr hU).symm w) : ℂ) = w := by
      simpa [E, Function.comp_def] using E.subtypeRestr_symm_apply hU hw
    simp [hval]
  have hraw :
      deriv (fun w : ℂ ↦ f ↑((E.subtypeRestr hU).symm w)) z ≠ 0 := by
    simpa [χ, zU, g, U, E, hU, surfaceComplexDerivativeInCoordinate,
      TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq] using hne
  rwa [heq.deriv_eq] at hraw

/-- The Bieberbach second-coefficient estimate, applied after recentering at
an arbitrary point, gives a crude pre-Schwarzian bound for a univalent map of
the disk.  This form is sufficient for compact-local normality. -/
theorem univalent_disk_second_derivative_norm_le
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv (deriv f) z‖ ≤
      (4 / (1 - ‖z‖)) * ‖deriv f z‖ := by
  let δ : ℝ := 1 - ‖z‖
  have hzNorm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hδ : 0 < δ := by simpa [δ] using sub_pos.mpr hzNorm
  let d : ℂ := deriv f z
  have hd : d ≠ 0 := by
    simpa [d] using analyticOnNhd_deriv_ne_zero_of_injOn hf hinj hz
  have hdNorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  let inner : ℂ → ℂ := fun w ↦ z + (δ : ℂ) * w
  have hinner : AnalyticOnNhd ℂ inner (ball 0 1) := by
    exact analyticOnNhd_const.add
      (analyticOnNhd_const.mul analyticOnNhd_id)
  have hinnerMaps : MapsTo inner (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    have hmul : δ * ‖w‖ < δ := by
      calc
        δ * ‖w‖ = ‖w‖ * δ := mul_comm _ _
        _ < 1 * δ := mul_lt_mul_of_pos_right hw hδ
        _ = δ := one_mul _
    calc
      ‖inner w‖ ≤ ‖z‖ + δ * ‖w‖ := by
        simpa [inner, norm_mul, Complex.norm_real, abs_of_pos hδ] using
          norm_add_le z ((δ : ℂ) * w)
      _ < ‖z‖ + δ := by linarith
      _ = 1 := by simp [δ]
  let denom : ℂ := (δ : ℂ) * d
  have hdenom : denom ≠ 0 := mul_ne_zero hδc hd
  let F : ℂ → ℂ := fun w ↦ (f (inner w) - f z) / denom
  have hF : AnalyticOnNhd ℂ F (ball 0 1) := by
    have hcomp : AnalyticOnNhd ℂ (fun w ↦ f (inner w)) (ball 0 1) := by
      simpa [Function.comp_def] using hf.comp hinner hinnerMaps
    exact (hcomp.sub analyticOnNhd_const).div analyticOnNhd_const
      (fun _ _ ↦ hdenom)
  have hF0 : F 0 = 0 := by simp [F, inner]
  have hFinj : InjOn F (ball (0 : ℂ) 1) := by
    intro u hu v hv huv
    have hiu := hinnerMaps hu
    have hiv := hinnerMaps hv
    have hfu : f (inner u) = f (inner v) := by
      dsimp [F] at huv
      field_simp [hdenom] at huv
      exact sub_left_inj.mp huv
    have huvInner := hinj hiu hiv hfu
    dsimp [inner] at huvInner
    exact mul_left_cancel₀ hδc (add_left_cancel huvInner)
  have hFderivEq :
      (deriv F) =ᶠ[𝓝 (0 : ℂ)]
        fun w ↦ deriv f (inner w) * (δ : ℂ) / denom := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
    have hinnerDeriv : HasDerivAt inner (δ : ℂ) w := by
      dsimp [inner]
      convert (hasDerivAt_const w z).add
        ((hasDerivAt_const w (δ : ℂ)).mul (hasDerivAt_id w)) using 1;
          simp
    have hfDeriv : HasDerivAt f (deriv f (inner w)) (inner w) :=
      (hf (inner w) (hinnerMaps hw)).differentiableAt.hasDerivAt
    have hraw := ((hfDeriv.comp w hinnerDeriv).sub_const (f z)).div_const denom
    convert hraw.deriv using 1
  have hF1 : deriv F 0 = 1 := by
    have hpoint := hFderivEq.eq_of_nhds
    rw [hpoint]
    rw [show inner 0 = z by simp [inner]]
    rw [show deriv f z * (δ : ℂ) = denom by simp [denom, d, mul_comm]]
    exact div_self hdenom
  have hFsecond :
      deriv (deriv F) 0 =
        (deriv (deriv f) z * (δ : ℂ)) * (δ : ℂ) / denom := by
    rw [hFderivEq.deriv_eq]
    have hdf : HasDerivAt (deriv f) (deriv (deriv f) z) z :=
      (hf.deriv z hz).differentiableAt.hasDerivAt
    have hinner0 : HasDerivAt inner (δ : ℂ) 0 := by
      dsimp [inner]
      convert (hasDerivAt_const 0 z).add
        ((hasDerivAt_const 0 (δ : ℂ)).mul (hasDerivAt_id 0)) using 1;
          simp
    have hdf' : HasDerivAt (deriv f) (deriv (deriv f) z) (inner 0) := by
      simpa [inner] using hdf
    have hraw := ((hdf'.comp 0 hinner0).mul_const (δ : ℂ)).div_const denom
    exact hraw.deriv
  have hqBound := bieberbach_second_coefficient hF hFinj hF0 hF1
  have hFsecondBound : ‖deriv (deriv F) 0‖ ≤ 4 := by
    rw [deriv_deriv_eq_two_mul_deriv_diskNormalizedQuotient hF hF0]
    rw [norm_mul]
    norm_num at hqBound ⊢
    linarith
  rw [hFsecond] at hFsecondBound
  have hraw : δ * ‖deriv (deriv f) z‖ / ‖d‖ ≤ 4 := by
    have hsource :
        ‖deriv (deriv f) z‖ * (δ * δ) / (‖d‖ * δ) ≤ 4 := by
      simpa [denom, norm_div, norm_mul, Complex.norm_real, abs_of_pos hδ,
        mul_assoc, mul_comm, mul_left_comm] using hFsecondBound
    rw [show δ * ‖deriv (deriv f) z‖ / ‖d‖ =
        ‖deriv (deriv f) z‖ * (δ * δ) / (‖d‖ * δ) by
      field_simp [hδ.ne', hdNorm.ne']]
    exact hsource
  have hmul : δ * ‖deriv (deriv f) z‖ ≤ 4 * ‖d‖ :=
    (div_le_iff₀ hdNorm).mp hraw
  rw [show (4 / (1 - ‖z‖)) * ‖deriv f z‖ =
      (4 * ‖d‖) / δ by simp [δ, d]; ring]
  exact (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hmul)

/-- A crude Koebe growth estimate.  The precise classical constant is not
needed here; this exponential bound already makes normalized univalent maps
compact-locally bounded. -/
theorem univalent_disk_normalized_norm_le_exp
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖f z‖ ≤ ρ * Real.exp (4 * ρ / (1 - ρ)) := by
  let K : ℝ := 4 * ρ / (1 - ρ)
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hzBall : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hz.trans_lt hρ1
  let path : ℝ → ℂ := fun t ↦ (t : ℂ) * z
  have hpathMaps : MapsTo path (Icc (0 : ℝ) 1) (ball (0 : ℂ) 1) := by
    intro t ht
    rw [mem_ball_zero_iff]
    have htAbs : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2
    calc
      ‖path t‖ = |t| * ‖z‖ := by simp [path]
      _ ≤ 1 * ρ := mul_le_mul htAbs hz (norm_nonneg z) (by norm_num)
      _ < 1 := by simpa using hρ1
  let g : ℝ → ℂ := fun t ↦ deriv f (path t)
  let g' : ℝ → ℂ := fun t ↦ deriv (deriv f) (path t) * z
  have hgCont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    have hp : Continuous path := by
      dsimp [path]
      fun_prop
    simpa [g, Function.comp_def] using
      hf.deriv.continuousOn.comp' hp.continuousOn hpathMaps
  have hgDeriv : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt g (g' t) (Ici t) t := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hpt := hpathMaps htIcc
    have houter : HasDerivAt (deriv f)
        (deriv (deriv f) (path t)) (path t) :=
      (hf.deriv (path t) hpt).differentiableAt.hasDerivAt
    have hinnerC : HasDerivAt (fun w : ℂ ↦ w * z) z (t : ℂ) := by
      convert (hasDerivAt_id (t : ℂ)).mul_const z using 1 <;> simp
    have hcompC := houter.comp (t : ℂ) hinnerC
    have hcompR : HasDerivAt g (g' t) t := by
      simpa [g, g', path, Function.comp_def] using hcompC.comp_ofReal
    exact hcompR.hasDerivWithinAt
  have hgGrowth : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖g' t‖ ≤ K * ‖g t‖ + 0 := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hpt := hpathMaps htIcc
    have htAbs : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2.le
    have hpathNorm : ‖path t‖ ≤ ρ := by
      calc
        ‖path t‖ = |t| * ‖z‖ := by simp [path]
        _ ≤ 1 * ρ := mul_le_mul htAbs hz (norm_nonneg z) (by norm_num)
        _ = ρ := one_mul ρ
    have hsecond := univalent_disk_second_derivative_norm_le hf hinj hpt
    have hfrac : 4 / (1 - ‖path t‖) ≤ 4 / (1 - ρ) := by
      exact div_le_div_of_nonneg_left (by norm_num) hden
        (by linarith)
    have hcoef : (4 / (1 - ‖path t‖)) * ‖z‖ ≤ K := by
      calc
        (4 / (1 - ‖path t‖)) * ‖z‖
            ≤ (4 / (1 - ρ)) * ρ :=
              mul_le_mul hfrac hz (norm_nonneg z)
                (div_nonneg (by norm_num) hden.le)
        _ = K := by dsimp [K]; ring
    dsimp [g, g']
    rw [norm_mul, add_zero]
    calc
      ‖deriv (deriv f) (path t)‖ * ‖z‖
          ≤ ((4 / (1 - ‖path t‖)) * ‖deriv f (path t)‖) * ‖z‖ :=
            mul_le_mul_of_nonneg_right hsecond (norm_nonneg z)
      _ = ((4 / (1 - ‖path t‖)) * ‖z‖) * ‖deriv f (path t)‖ := by ring
      _ ≤ K * ‖deriv f (path t)‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hg0 : ‖g 0‖ ≤ 1 := by simp [g, path, h1]
  have hgBound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖g t‖ ≤ Real.exp K := by
    intro t ht
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      hgCont hgDeriv hg0 hgGrowth t ht
    rw [gronwallBound_ε0] at hgr
    have hK0 : 0 ≤ K := by
      exact div_nonneg (mul_nonneg (by norm_num) hρ0) hden.le
    calc
      ‖g t‖ ≤ Real.exp (K * (t - 0)) := by simpa using hgr
      _ ≤ Real.exp K := by
        apply Real.exp_le_exp.mpr
        nlinarith [ht.1, ht.2]
  let H : ℝ → ℂ := fun t ↦ f (path t)
  let H' : ℝ → ℂ := fun t ↦ deriv f (path t) * z
  have hHDeriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt H (H' t) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hpt := hpathMaps ht
    have houter : HasDerivAt f (deriv f (path t)) (path t) :=
      (hf (path t) hpt).differentiableAt.hasDerivAt
    have hinnerC : HasDerivAt (fun w : ℂ ↦ w * z) z (t : ℂ) := by
      convert (hasDerivAt_id (t : ℂ)).mul_const z using 1 <;> simp
    have hcompC := houter.comp (t : ℂ) hinnerC
    have hcompR : HasDerivAt H (H' t) t := by
      simpa [H, H', path, Function.comp_def] using hcompC.comp_ofReal
    exact hcompR.hasDerivWithinAt
  have hHBound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖H' t‖ ≤ Real.exp K * ρ := by
    intro t ht
    have hgt := hgBound t ⟨ht.1, ht.2.le⟩
    dsimp [H', g] at hgt ⊢
    rw [norm_mul]
    exact mul_le_mul hgt hz (norm_nonneg z) (Real.exp_pos K).le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hHDeriv hHBound
  simpa [H, path, h0, K, mul_comm] using hmv

/--
%%handwave
name:
  Growth estimate for normalized univalent disk maps
statement:
  Let an injective holomorphic map on a disk of positive radius fix zero and
  have derivative one there.  At every point of relative radius
  \(0\leq\rho<1\), its norm is at most the source radius times
  \(\rho\exp(4\rho/(1-\rho))\).
proof:
  Rescale to the unit disk, apply the logarithmic-derivative estimate obtained
  from Grönwall's area theorem, and integrate the resulting derivative bound
  along the radial segment.
-/
theorem univalent_disk_normalized_norm_le_exp_scaled
    {f : ℂ → ℂ} {r ρ : ℝ}
    (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hinj : InjOn f (ball 0 r))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ ρ * r) :
    ‖f z‖ ≤ r * (ρ * Real.exp (4 * ρ / (1 - ρ))) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let F : ℂ → ℂ := fun w ↦ f ((r : ℂ) * w) / (r : ℂ)
  have hinner : AnalyticOnNhd ℂ (fun w : ℂ ↦ (r : ℂ) * w)
      (ball 0 1) := analyticOnNhd_const.mul analyticOnNhd_id
  have hmaps : MapsTo (fun w : ℂ ↦ (r : ℂ) * w)
      (ball 0 1) (ball (0 : ℂ) r) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    calc
      ‖(r : ℂ) * w‖ = r * ‖w‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      _ < r * 1 := mul_lt_mul_of_pos_left hw hr
      _ = r := mul_one r
  have hF : AnalyticOnNhd ℂ F (ball 0 1) := by
    exact (hf.comp hinner hmaps).div analyticOnNhd_const
      (fun _ _ ↦ hrC)
  have hFinj : InjOn F (ball (0 : ℂ) 1) := by
    intro u hu v hv huv
    dsimp [F] at huv
    have hfu : f ((r : ℂ) * u) = f ((r : ℂ) * v) := by
      have hmul := (div_eq_div_iff hrC hrC).mp huv
      exact mul_right_cancel₀ hrC hmul
    have huv' := hinj (hmaps hu) (hmaps hv) hfu
    exact mul_left_cancel₀ hrC huv'
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hfDer : HasDerivAt f 1 0 := by
    simpa [h1] using
      (hf 0 (mem_ball_self hr)).differentiableAt.hasDerivAt
  have hinnerDer : HasDerivAt (fun w : ℂ ↦ (r : ℂ) * w) (r : ℂ) 0 := by
    convert (hasDerivAt_const 0 (r : ℂ)).mul (hasDerivAt_id 0) using 1 <;> simp
  have hFDer : HasDerivAt F 1 0 := by
    have hfDer' : HasDerivAt f 1 ((r : ℂ) * 0) := by
      simpa using hfDer
    have hraw := (hfDer'.comp 0 hinnerDer).div_const (r : ℂ)
    convert hraw using 1 <;> simp [hrC]
  have hF1 : deriv F 0 = 1 := hFDer.deriv
  let w : ℂ := z / (r : ℂ)
  have hw : ‖w‖ ≤ ρ := by
    rw [show ‖w‖ = ‖z‖ / r by
      simp [w, Complex.norm_real, abs_of_pos hr]]
    exact (div_le_iff₀ hr).2 (by simpa [mul_comm] using hz)
  have hbound := univalent_disk_normalized_norm_le_exp
    hF hFinj hF0 hF1 hρ0 hρ1 hw
  have hzw : (r : ℂ) * w = z := by
    dsimp [w]
    field_simp [hrC]
  have hnormF : ‖F w‖ = ‖f z‖ / r := by
    simp [F, hzw, Complex.norm_real, abs_of_pos hr]
  rw [hnormF] at hbound
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (div_le_iff₀ hr).mp hbound

/--
%%handwave
name:
  Scaled Koebe quarter theorem
statement:
  If an injective holomorphic map on a disk of radius \(r>0\) fixes zero and
  has derivative one at zero, then its image contains the disk of radius
  \(r/4\) centered at zero.
proof:
  Rescale the source disk to the unit disk and apply the normalized Koebe
  quarter theorem, proved from Grönwall's area theorem.
-/
theorem koebe_quarter_normalized_scaled
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hinj : InjOn f (ball 0 r))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ball (0 : ℂ) (r / 4) ⊆ f '' ball 0 r := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let F : ℂ → ℂ := fun w ↦ f ((r : ℂ) * w) / (r : ℂ)
  have hinner : AnalyticOnNhd ℂ (fun w : ℂ ↦ (r : ℂ) * w)
      (ball 0 1) := analyticOnNhd_const.mul analyticOnNhd_id
  have hmaps : MapsTo (fun w : ℂ ↦ (r : ℂ) * w)
      (ball 0 1) (ball (0 : ℂ) r) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simpa using mul_lt_mul_of_pos_left hw hr
  have hF : AnalyticOnNhd ℂ F (ball 0 1) :=
    (hf.comp hinner hmaps).div analyticOnNhd_const (fun _ _ ↦ hrC)
  have hFinj : InjOn F (ball (0 : ℂ) 1) := by
    intro u hu v hv huv
    dsimp [F] at huv
    have hfu : f ((r : ℂ) * u) = f ((r : ℂ) * v) := by
      have hmul := (div_eq_div_iff hrC hrC).mp huv
      exact mul_right_cancel₀ hrC hmul
    exact mul_left_cancel₀ hrC (hinj (hmaps hu) (hmaps hv) hfu)
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hfDer : HasDerivAt f 1 0 := by
    simpa [h1] using
      (hf 0 (mem_ball_self hr)).differentiableAt.hasDerivAt
  have hinnerDer : HasDerivAt (fun w : ℂ ↦ (r : ℂ) * w) (r : ℂ) 0 := by
    convert (hasDerivAt_const 0 (r : ℂ)).mul (hasDerivAt_id 0) using 1 <;> simp
  have hFDer : HasDerivAt F 1 0 := by
    have hfDer' : HasDerivAt f 1 ((r : ℂ) * 0) := by
      simpa using hfDer
    have hraw := (hfDer'.comp 0 hinnerDer).div_const (r : ℂ)
    convert hraw using 1 <;> simp [hrC]
  have hquarter := koebe_quarter_normalized hF hFinj hF0 hFDer.deriv
  intro a ha
  let b : ℂ := a / (r : ℂ)
  have hb : b ∈ ball (0 : ℂ) (1 / 4 : ℝ) := by
    rw [mem_ball_zero_iff] at ha ⊢
    rw [show ‖b‖ = ‖a‖ / r by
      simp [b, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]]
    exact (div_lt_iff₀ hr).2
      (by simpa [div_eq_mul_inv, mul_comm] using ha)
  obtain ⟨w, hw, hFw⟩ := hquarter hb
  refine ⟨(r : ℂ) * w, hmaps hw, ?_⟩
  dsimp [F, b] at hFw
  exact (div_left_inj' hrC).mp hFw

end JJMath.Uniformization
