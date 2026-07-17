import JJMath.Uniformization.LiouvilleExistence
import JJMath.Uniformization.PoissonExtensionDisc
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Semicontinuity.Lindelof
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Harmonic and subharmonic functions on Riemann surfaces

This file isolates the harmonic, subharmonic, and superharmonic background
needed for Perron's method.  The goal is to keep the plane circle-mean
comparison machinery separate from the Perron envelope construction.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

/--
%%handwave
name:
  Harmonic function on a surface region
statement:
  A real-valued function is harmonic on a surface region when, in every
  complex coordinate, its coordinate expression is harmonic on the part of the
  coordinate image lying over the region.
-/
def IsHarmonicOnSurface {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
    InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ ↦ u (e.symm z))
      (e.target ∩ e.symm ⁻¹' U)

/--
%%handwave
name:
  Constant functions are harmonic on surface regions
statement:
  Constant real-valued functions are harmonic on every surface region.
-/
theorem harmonicOnSurface_const
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (c : ℝ) :
    IsHarmonicOnSurface U (fun _ : X ↦ c) := by
  intro e _he
  simp

/--
%%handwave
name:
  Harmonicity restricts to smaller surface regions
statement:
  A harmonic function on a surface region remains harmonic on every smaller
  region.
-/
theorem harmonicOnSurface_mono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U V : Set X} {u : X → ℝ}
    (hUV : U ⊆ V) (hu : IsHarmonicOnSurface V u) :
    IsHarmonicOnSurface U u := by
  intro e he
  exact (hu e he).mono (by
    intro z hz
    exact ⟨hz.1, hUV hz.2⟩)

/--
%%handwave
name:
  Harmonicity restricts to open subspaces
statement:
  If a function is harmonic on an open surface region, then its restriction to
  that open region, viewed as a surface in its own right, is harmonic on the
  whole subspace.
proof:
  Use the open embedding of the subspace into the original surface.  Charts on
  the open subspace are restrictions of ambient charts, so the coordinate
  harmonicity condition transports through the embedding.
-/
theorem harmonicOnSurface_openSubtype_univ_of_ambient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (U : TopologicalSpace.Opens X) {u : X → ℝ}
    (hu : IsHarmonicOnSurface (U : Set X) u) :
    IsHarmonicOnSurface (Set.univ : Set U) (fun x : U ↦ u x) := by
  intro e he z hz
  by_cases hU : Nonempty U
  · rcases TopologicalSpace.Opens.chart_eq (H := ℂ) hU he with ⟨x, rfl⟩
    let E : OpenPartialHomeomorph X ℂ := chartAt ℂ (x : X)
    have hz_target : z ∈ (E.subtypeRestr hU).target := hz.1
    have hz_ambient_target : z ∈ E.target :=
      E.subtypeRestr_target_subset hU hz_target
    have hz_ambient_U : E.symm z ∈ (U : Set X) := by
      have hval :
          ((E.subtypeRestr hU).symm z : X) = E.symm z := by
        simpa [Function.comp_def] using E.subtypeRestr_symm_apply hU hz_target
      have hz_subtype : ((E.subtypeRestr hU).symm z : X) ∈ (U : Set X) :=
        ((E.subtypeRestr hU).symm z).property
      simpa [hval] using hz_subtype
    have hambient :
        InnerProductSpace.HarmonicAt
          (fun w : ℂ ↦ u (E.symm w)) z :=
      hu E (chart_mem_atlas ℂ (x : X)) z
        ⟨hz_ambient_target, hz_ambient_U⟩
    have heq :
        (fun w : ℂ ↦ u ((E.subtypeRestr hU).symm w)) =ᶠ[𝓝 z]
          (fun w : ℂ ↦ u (E.symm w)) := by
      filter_upwards [(E.subtypeRestr hU).open_target.mem_nhds hz_target] with w hw
      have hval :
          ((E.subtypeRestr hU).symm w : X) = E.symm w := by
        simpa [Function.comp_def] using E.subtypeRestr_symm_apply hU hw
      simp [hval]
    exact (InnerProductSpace.harmonicAt_congr_nhds heq).2 hambient
  · haveI : IsEmpty U := not_nonempty_iff.mp hU
    exact isEmptyElim (e.symm z)

/--
%%handwave
name:
  Harmonicity on a region restricts to an open subspace
statement:
  If a function is harmonic on a region of a surface, then its restriction to
  any open subspace is harmonic on the inverse image of that region.
proof:
  Charts of the open subspace are restrictions of ambient charts.  In those
  charts the restricted function has the same coordinate expression as the
  ambient function near every point of the inverse-image region.
-/
theorem harmonicOnSurface_openSubtype_of_ambient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (U : TopologicalSpace.Opens X) {V : Set X} {u : X → ℝ}
    (hu : IsHarmonicOnSurface V u) :
    IsHarmonicOnSurface {x : U | (x : X) ∈ V} (fun x : U ↦ u x) := by
  intro e he z hz
  by_cases hU : Nonempty U
  · rcases TopologicalSpace.Opens.chart_eq (H := ℂ) hU he with ⟨x, rfl⟩
    let E : OpenPartialHomeomorph X ℂ := chartAt ℂ (x : X)
    have hz_target : z ∈ (E.subtypeRestr hU).target := hz.1
    have hz_ambient_target : z ∈ E.target :=
      E.subtypeRestr_target_subset hU hz_target
    have hz_ambient_V : E.symm z ∈ V := by
      have hval :
          ((E.subtypeRestr hU).symm z : X) = E.symm z := by
        simpa [Function.comp_def] using E.subtypeRestr_symm_apply hU hz_target
      rw [← hval]
      exact hz.2
    have hambient :
        InnerProductSpace.HarmonicAt
          (fun w : ℂ ↦ u (E.symm w)) z :=
      hu E (chart_mem_atlas ℂ (x : X)) z
        ⟨hz_ambient_target, hz_ambient_V⟩
    have heq :
        (fun w : ℂ ↦ u ((E.subtypeRestr hU).symm w)) =ᶠ[nhds z]
          (fun w : ℂ ↦ u (E.symm w)) := by
      filter_upwards [(E.subtypeRestr hU).open_target.mem_nhds hz_target] with w hw
      have hval :
          ((E.subtypeRestr hU).symm w : X) = E.symm w := by
        simpa [Function.comp_def] using E.subtypeRestr_symm_apply hU hw
      simp [hval]
    exact (InnerProductSpace.harmonicAt_congr_nhds heq).2 hambient
  · haveI : IsEmpty U := not_nonempty_iff.mp hU
    exact isEmptyElim (e.symm z)

/--
%%handwave
name:
  Harmonicity is local on the surface region
statement:
  A function is harmonic on a surface region if every point of the region has
  a smaller surface region around it on which the function is harmonic.
proof:
  Harmonicity on surfaces is checked pointwise in coordinate charts.  At a
  coordinate point over the large region, choose one of the smaller harmonic
  regions containing the underlying surface point and use the same coordinate
  chart there.
-/
theorem harmonicOnSurface_of_locally_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ}
    (hlocal : ∀ x ∈ U, ∃ V : Set X, x ∈ V ∧ V ⊆ U ∧
      IsHarmonicOnSurface V u) :
    IsHarmonicOnSurface U u := by
  intro e he z hz
  rcases hlocal (e.symm z) hz.2 with ⟨V, hxV, _hVU, hV⟩
  exact hV e he z ⟨hz.1, hxV⟩

/--
%%handwave
name:
  Differences of harmonic functions are harmonic
statement:
  The difference of two harmonic functions on the same surface region is
  harmonic.
-/
theorem harmonicOnSurface_sub
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u v : X → ℝ}
    (hu : IsHarmonicOnSurface U u) (hv : IsHarmonicOnSurface U v) :
    IsHarmonicOnSurface U (fun x ↦ u x - v x) := by
  intro e he
  simpa [Pi.sub_apply] using (hu e he).sub (hv e he)

/--
%%handwave
name:
  Sums of harmonic functions are harmonic
statement:
  The sum of two harmonic functions on the same surface region is harmonic.
-/
theorem harmonicOnSurface_add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u v : X → ℝ}
    (hu : IsHarmonicOnSurface U u) (hv : IsHarmonicOnSurface U v) :
    IsHarmonicOnSurface U (fun x ↦ u x + v x) := by
  intro e he
  simpa [Pi.add_apply] using (hu e he).add (hv e he)

/--
%%handwave
name:
  Negatives of harmonic functions are harmonic
statement:
  The negative of a harmonic function on a surface region is harmonic.
-/
theorem harmonicOnSurface_neg
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ}
    (hu : IsHarmonicOnSurface U u) :
    IsHarmonicOnSurface U (fun x ↦ -u x) := by
  intro e he
  simpa [Pi.neg_apply] using (hu e he).neg

/--
%%handwave
name:
  Scalar multiples of harmonic functions are harmonic
statement:
  A real scalar multiple of a harmonic function on a surface region is
  harmonic.
-/
theorem harmonicOnSurface_const_mul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} (c : ℝ)
    (hu : IsHarmonicOnSurface U u) :
    IsHarmonicOnSurface U (fun x ↦ c * u x) := by
  intro e he
  simpa [Pi.smul_apply, smul_eq_mul] using
    (hu e he).const_smul (c := c)

/--
%%handwave
name:
  Harmonic functions are continuous on surface regions
statement:
  A harmonic function on an open surface region is continuous on that region.
proof:
  In every complex coordinate the function is harmonic, hence continuous, on
  the corresponding open subset of the complex plane.  Transporting this local
  continuity through the coordinate charts gives continuity on the surface
  region.
-/
theorem harmonicOnSurface_continuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ}
    (_hU_open : IsOpen U)
    (hu : IsHarmonicOnSurface U u) :
    ContinuousOn u U := by
  intro x hx
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hcoord_cont : ContinuousOn (fun z : ℂ ↦ u (e.symm z))
      (e.target ∩ e.symm ⁻¹' U) :=
    (hu e he).continuousOn
  have hlocal : ContinuousOn u (U ∩ e.source) := by
    have hsubset : U ∩ e.source ⊆ e.source := by
      intro y hy
      exact hy.2
    rw [e.symm.continuousOn_iff_continuousOn_comp_right (f := u)
      (s := U ∩ e.source) hsubset]
    exact hcoord_cont.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1⟩)
  have hxlocal : x ∈ U ∩ e.source := ⟨hx, mem_chart_source ℂ x⟩
  have hlocal_at : ContinuousWithinAt u (U ∩ e.source) x :=
    hlocal.continuousWithinAt hxlocal
  have hsource_nhds : e.source ∈ 𝓝 x := chart_source_mem_nhds ℂ x
  exact (continuousWithinAt_inter hsource_nhds).1 hlocal_at

/--
%%handwave
name:
  Harmonic functions are locally constant at local maxima
statement:
  A complex-plane harmonic function that has a local maximum at a point is
  locally constant near that point.
proof:
  Near the point, write the harmonic function as the real part of a
  holomorphic function \(F\).  Then \(\exp F\) is holomorphic and its norm is
  \(\exp u\), so the local maximum of \(u\) gives a local maximum of
  \(\|\exp F\|\).  The maximum modulus principle makes this norm locally
  constant, and injectivity of the real exponential gives local constancy of
  \(u\).
-/
theorem harmonicAt_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {z : ℂ}
    (hu : InnerProductSpace.HarmonicAt u z)
    (hzmax : IsLocalMax u z) :
    ∀ᶠ y in 𝓝 z, u y = u z := by
  have hhu_event : ∀ᶠ y in 𝓝 z, InnerProductSpace.HarmonicAt u y :=
    hu.eventually
  have hset : {y : ℂ | InnerProductSpace.HarmonicAt u y} ∈ 𝓝 z := hhu_event
  rcases Metric.mem_nhds_iff.mp hset with ⟨R, hRpos, hRsub⟩
  have hHarmBall : InnerProductSpace.HarmonicOnNhd u (Metric.ball z R) := by
    intro y hy
    exact hRsub hy
  rcases hHarmBall.exists_analyticOnNhd_ball_re_eq with ⟨F, hF_an, hF_re⟩
  let g : ℂ → ℂ := fun y ↦ Complex.exp (F y)
  have hg_diff : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ g y := by
    filter_upwards [Metric.ball_mem_nhds z hRpos] with y hy
    exact (hF_an y hy).differentiableAt.cexp
  have hnorm_eq_rexp :
      (fun y ↦ ‖g y‖) =ᶠ[𝓝 z] (fun y ↦ Real.exp (u y)) := by
    filter_upwards [Metric.ball_mem_nhds z hRpos] with y hy
    simp [g, Complex.norm_exp, hF_re hy]
  have hnormmax : IsLocalMax (norm ∘ g) z := by
    have hrexpmax : IsLocalMax (fun y ↦ Real.exp (u y)) z :=
      hzmax.comp_mono Real.exp_monotone
    exact hrexpmax.congr hnorm_eq_rexp.symm
  have hnorm_const : ∀ᶠ y in 𝓝 z, ‖g y‖ = ‖g z‖ :=
    Complex.norm_eventually_eq_of_isLocalMax hg_diff hnormmax
  filter_upwards [Metric.ball_mem_nhds z hRpos, hnorm_const] with y hy hgy
  have hzball : z ∈ Metric.ball z R := Metric.mem_ball_self hRpos
  have hexp : Real.exp (u y) = Real.exp (u z) := by
    simpa [g, Complex.norm_exp, hF_re hy, hF_re hzball] using hgy
  exact Real.exp_injective hexp

/--
%%handwave
name:
  Surface harmonic functions are locally constant at local maxima
statement:
  A harmonic function on a surface region that has a local maximum at an
  interior point is locally constant near that point.
proof:
  Pass to a complex coordinate around the point.  The coordinate expression is
  harmonic in the complex plane and has a local maximum, so
  [it is locally constant near that
  point](lean:JJMath.Uniformization.harmonicAt_eventually_eq_of_isLocalMax).
  Pull the resulting local equality back through the chart.
-/
theorem harmonicOnSurface_eventually_eq_of_isLocalMax
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} {x : X}
    (hu : IsHarmonicOnSurface U u)
    (hxU : x ∈ U)
    (hxmax : IsLocalMax u x) :
    ∀ᶠ y in 𝓝 x, u y = u x := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hxsource : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hztarget : e x ∈ e.target := e.map_source hxsource
  have hzU : e.symm (e x) ∈ U := by
    simpa [e.left_inv hxsource] using hxU
  have hcoord_harm :
      InnerProductSpace.HarmonicAt (fun z : ℂ ↦ u (e.symm z)) (e x) :=
    hu e he (e x) ⟨hztarget, hzU⟩
  have hcoord_max : IsLocalMax (fun z : ℂ ↦ u (e.symm z)) (e x) := by
    have hcont : ContinuousAt e.symm (e x) := e.continuousAt_symm hztarget
    have hxmax' : IsLocalMax u (e.symm (e x)) := by
      simpa [e.left_inv hxsource] using hxmax
    simpa [Function.comp_def] using hxmax'.comp_continuous hcont
  have hcoord_event :
      ∀ᶠ z in 𝓝 (e x), u (e.symm z) = u (e.symm (e x)) :=
    harmonicAt_eventually_eq_of_isLocalMax hcoord_harm hcoord_max
  have hback :
      ∀ᶠ y in 𝓝 x, u (e.symm (e y)) = u (e.symm (e x)) :=
    e.continuousAt hxsource hcoord_event
  filter_upwards [hback, e.open_source.mem_nhds hxsource] with y hy hysource
  simpa [e.left_inv hysource, e.left_inv hxsource] using hy

/--
%%handwave
name:
  Strong maximum principle for surface harmonic functions
statement:
  On a preconnected open surface region, a harmonic function that attains its
  maximum in the region is constant on the region.
proof:
  The set where the function takes the maximum value is nonempty.  It is open
  because [surface harmonic functions are locally constant at local
  maxima](lean:JJMath.Uniformization.harmonicOnSurface_eventually_eq_of_isLocalMax),
  and its complement inside the region is open by continuity.  Preconnectedness
  forces the complement to be empty.
-/
theorem harmonicOnSurface_eqOn_of_isPreconnected_of_isMaxOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hu : IsHarmonicOnSurface U u)
    {c : X} (hcU : c ∈ U) (hm : IsMaxOn u U c) :
    Set.EqOn u (fun _ ↦ u c) U := by
  let V : Set X := U ∩ {x | u x = u c}
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 ?_
    intro x hxV
    have hxU : x ∈ U := hxV.1
    have hx_eq : u x = u c := hxV.2
    have hxmaxU : IsMaxOn u U x := by
      intro y hy
      simpa [hx_eq] using hm hy
    have hxlocalmax : IsLocalMax u x :=
      hxmaxU.isLocalMax (hU_open.mem_nhds hxU)
    have hevent : ∀ᶠ y in 𝓝 x, u y = u x :=
      harmonicOnSurface_eventually_eq_of_isLocalMax hu hxU hxlocalmax
    have heqset : {y : X | u y = u c} ∈ 𝓝 x := by
      filter_upwards [hevent] with y hy
      exact hy.trans hx_eq
    exact Filter.inter_mem (hU_open.mem_nhds hxU) heqset
  have hcont : ContinuousOn u U := harmonicOnSurface_continuousOn hU_open hu
  let W : Set X := U ∩ {x | u x ≠ u c}
  have hWo : IsOpen W :=
    hcont.isOpen_inter_preimage hU_open isOpen_ne
  have hdVW : Disjoint V W := by
    rw [Set.disjoint_left]
    intro x hxV hxW
    exact hxW.2 hxV.2
  have hUVW : U ⊆ V ∪ W := by
    intro x hx
    by_cases hx_eq : u x = u c
    · exact Or.inl ⟨hx, hx_eq⟩
    · exact Or.inr ⟨hx, hx_eq⟩
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  have hsubset : U ⊆ V :=
    hU_preconnected.subset_left_of_subset_union hVo hWo hdVW hUVW hVne
  intro x hx
  exact (hsubset hx).2

/--
%%handwave
name:
  Analytic precomposition preserves harmonicity
statement:
  If a real-valued function is harmonic at the image point of an analytic
  complex map, then its precomposition with that map is harmonic at the
  original point.
proof:
  Locally write the harmonic function as the real part of a holomorphic
  function, compose the holomorphic function with the analytic map, and take
  real parts.
-/
theorem harmonicAt_comp_analyticAt
    {u : ℂ → ℝ} {g : ℂ → ℂ} {z : ℂ}
    (hu : InnerProductSpace.HarmonicAt u (g z))
    (hg : AnalyticAt ℂ g z) :
    InnerProductSpace.HarmonicAt (fun y ↦ u (g y)) z := by
  have hopen : IsOpen {w : ℂ | InnerProductSpace.HarmonicAt u w} :=
    InnerProductSpace.isOpen_setOf_harmonicAt u
  rcases Metric.mem_nhds_iff.mp (hopen.mem_nhds hu) with ⟨R, hR, hRsub⟩
  have hu_ball :
      InnerProductSpace.HarmonicOnNhd u (Metric.ball (g z) R) := by
    intro w hw
    exact hRsub hw
  rcases InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
      hu_ball with ⟨F, hF, hF_re⟩
  have hF_at : AnalyticAt ℂ F (g z) :=
    hF (g z) (Metric.mem_ball_self hR)
  have hcomp : AnalyticAt ℂ (F ∘ g) z :=
    hF_at.comp hg
  have hre_harmonic :
      InnerProductSpace.HarmonicAt (fun y ↦ ((F ∘ g) y).re) z :=
    hcomp.harmonicAt_re
  have heq :
      (fun y ↦ ((F ∘ g) y).re) =ᶠ[𝓝 z] (fun y ↦ u (g y)) := by
    filter_upwards [hg.continuousAt (Metric.ball_mem_nhds (g z) hR)] with y hy
    exact hF_re hy
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).1 hre_harmonic

/--
%%handwave
name:
  Complex-smooth plane maps are analytic
statement:
  A complex-smooth map between open pieces of the complex plane is analytic at
  each point where it is complex-smooth.
proof:
  Complex smoothness gives complex differentiability on a neighborhood.  The
  Cauchy integral theorem then upgrades local complex differentiability to
  analyticity.
-/
theorem analyticAt_of_contDiffAt_top_complex {f : ℂ → ℂ} {z : ℂ}
    (h : ContDiffAt ℂ ⊤ f z) :
    AnalyticAt ℂ f z := by
  let s : Set ℂ := {w : ℂ | ContDiffAt ℂ ⊤ f w}
  have hs : s ∈ 𝓝 z := h.eventually (by simp)
  have hd : DifferentiableOn ℂ f s := by
    intro w hw
    have hw' : ContDiffAt ℂ ⊤ f w := by
      simpa [s] using hw
    exact (hw'.differentiableAt (by simp)).differentiableWithinAt
  exact hd.analyticAt hs

/--
%%handwave
name:
  Analyticity of coordinate changes
statement:
  The transition map between two complex charts of a Riemann surface is
  analytic at every point where the two charts overlap.
proof:
  Both charts belong to the maximal complex-smooth atlas.  The inverse of the
  first chart and the second chart are therefore complex-smooth at the
  relevant points, so their composition is complex-smooth and hence analytic.
-/
theorem chartTransition_analyticAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X)
    {z : ℂ} (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    AnalyticAt ℂ (fun w : ℂ ↦ e' (e.symm w)) z := by
  have hsymm_mdiff :
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ⊤ e.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) he) hz
  have hchart_mdiff :
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ⊤ e' (e.symm z) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) he') hz'
  exact analyticAt_of_contDiffAt_top_complex
    ((hchart_mdiff.comp z hsymm_mdiff).contDiffAt)

/--
%%handwave
name:
  Harmonic maximum principle for nonpositive boundary values
statement:
  If a harmonic function on a relatively compact connected open surface
  region is continuous on the closed region and nonpositive on a nonempty
  boundary, then it is nonpositive throughout the region.
proof:
  If the function had a positive interior maximum, the strong maximum
  principle would make it constant on the connected region.  Continuity up to
  the closure would then force the same positive value at a boundary point,
  contradicting the boundary inequality.
-/
theorem harmonic_nonpositive_of_boundary_nonpositive
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hU_compact : IsCompact (closure U))
    (hU_frontier_nonempty : (frontier U).Nonempty)
    (hu_harmonic : IsHarmonicOnSurface U u)
    (hu_continuous : ContinuousOn u (closure U))
    (hbd : ∀ x ∈ frontier U, u x ≤ 0) :
    ∀ x ∈ U, u x ≤ 0 := by
  rcases hU_frontier_nonempty with ⟨b, hbfrontier⟩
  have hbclosure : b ∈ closure U := frontier_subset_closure hbfrontier
  rcases hU_compact.exists_isMaxOn ⟨b, hbclosure⟩ hu_continuous with
    ⟨c, hcclosure, hcmax_closure⟩
  have hc_mem : c ∈ U ∪ frontier U := by
    simpa [closure_eq_self_union_frontier] using hcclosure
  rcases hc_mem with hcU | hcfrontier
  · have hcmaxU : IsMaxOn u U c := by
      intro y hy
      exact hcmax_closure (subset_closure hy)
    have heqU : Set.EqOn u (fun _ ↦ u c) U :=
      harmonicOnSurface_eqOn_of_isPreconnected_of_isMaxOn
        hU_open hU_preconnected hu_harmonic hcU hcmaxU
    have heq_closure : Set.EqOn u (fun _ ↦ u c) (closure U) :=
      heqU.of_subset_closure hu_continuous continuousOn_const
        subset_closure subset_rfl
    have huc_nonpos : u c ≤ 0 := by
      have hbc : u b = u c := heq_closure hbclosure
      rw [← hbc]
      exact hbd b hbfrontier
    intro x hx
    exact (heqU hx).trans_le huc_nonpos
  · have huc_nonpos : u c ≤ 0 := hbd c hcfrontier
    intro x hx
    exact (hcmax_closure (subset_closure hx)).trans huc_nonpos

/--
%%handwave
name:
  Componentwise maximum principle geometry
statement:
  An open set has componentwise maximum-principle geometry if each point lies
  in a connected open subregion with compact closure and nonempty boundary,
  whose boundary is contained in the boundary of the original set.
-/
def HasComponentwiseMaximumPrincipleGeometry
    {X : Type} [TopologicalSpace X] (U : Set X) : Prop :=
  ∀ x ∈ U, ∃ C : Set X,
    x ∈ C ∧ IsOpen C ∧ IsPreconnected C ∧ C ⊆ U ∧
      IsCompact (closure C) ∧ (frontier C).Nonempty ∧ frontier C ⊆ frontier U

/--
%%handwave
name:
  Connected maximum-principle geometry
statement:
  A relatively compact connected open set with nonempty boundary has
  componentwise maximum-principle geometry.
-/
theorem hasComponentwiseMaximumPrincipleGeometry_of_preconnected
    {X : Type} [TopologicalSpace X] {U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hU_compact : IsCompact (closure U))
    (hU_frontier_nonempty : (frontier U).Nonempty) :
    HasComponentwiseMaximumPrincipleGeometry U := by
  intro x hx
  exact ⟨U, hx, hU_open, hU_preconnected, subset_rfl, hU_compact,
    hU_frontier_nonempty, subset_rfl⟩

/--
%%handwave
name:
  Componentwise harmonic maximum principle
statement:
  If every component relevant to an open set has the connected
  maximum-principle geometry, then a harmonic function that is nonpositive on
  the boundary is nonpositive throughout the set.
proof:
  Apply the connected maximum principle on the connected subregion containing
  each point.  The subregion boundary lies in the boundary of the original
  open set, so the boundary inequality restricts to it.
-/
theorem harmonic_nonpositive_of_boundary_nonpositive_componentwise
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ}
    (hU_geometry : HasComponentwiseMaximumPrincipleGeometry U)
    (hu_harmonic : IsHarmonicOnSurface U u)
    (hu_continuous : ContinuousOn u (closure U))
    (hbd : ∀ x ∈ frontier U, u x ≤ 0) :
    ∀ x ∈ U, u x ≤ 0 := by
  intro x hx
  rcases hU_geometry x hx with
    ⟨C, hxC, hC_open, hC_preconnected, hCU, hC_compact,
      hC_frontier_nonempty, hC_frontier_subset⟩
  have hC_harmonic : IsHarmonicOnSurface C u :=
    harmonicOnSurface_mono hCU hu_harmonic
  have hC_continuous : ContinuousOn u (closure C) :=
    hu_continuous.mono (closure_mono hCU)
  have hC_boundary : ∀ y ∈ frontier C, u y ≤ 0 := by
    intro y hy
    exact hbd y (hC_frontier_subset hy)
  exact harmonic_nonpositive_of_boundary_nonpositive
    hC_open hC_preconnected hC_compact hC_frontier_nonempty
    hC_harmonic hC_continuous hC_boundary x hxC

/--
%%handwave
name:
  Subharmonic function on a surface region
statement:
  A finite real-valued function is subharmonic on a surface region when it is
  upper semicontinuous there and satisfies the harmonic comparison principle on
  every relatively compact connected open subregion with nonempty boundary.
-/
def IsSubharmonicOnSurface {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) : Prop :=
  UpperSemicontinuousOn u U ∧
    ∀ V : Set X,
      IsOpen V →
        IsPreconnected V →
          (frontier V).Nonempty →
            V ⊆ U →
              IsCompact (closure V) →
                closure V ⊆ U →
                  ∀ h : X → ℝ,
                    IsHarmonicOnSurface V h →
                      ContinuousOn h (closure V) →
                        (∀ x ∈ frontier V, u x ≤ h x) →
                          ∀ x ∈ V, u x ≤ h x

/--
%%handwave
name:
  Plane comparison subharmonicity
statement:
  A real-valued function on a plane domain is subharmonic in the comparison
  sense when it is upper semicontinuous and satisfies the harmonic comparison
  principle on every relatively compact connected open subdomain with
  nonempty boundary.
-/
def IsSubharmonicByPlaneComparisonOn (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  UpperSemicontinuousOn u U ∧
    ∀ V : Set ℂ,
      IsOpen V →
        IsPreconnected V →
          (frontier V).Nonempty →
            V ⊆ U →
              IsCompact (closure V) →
                closure V ⊆ U →
                  ∀ h : ℂ → ℝ,
                    InnerProductSpace.HarmonicOnNhd h V →
                      ContinuousOn h (closure V) →
                        (∀ x ∈ frontier V, u x ≤ h x) →
                          ∀ x ∈ V, u x ≤ h x

/--
%%handwave
name:
  Plane comparison subharmonicity restricts to smaller domains
statement:
  A function satisfying harmonic comparison on a plane domain satisfies the same
  comparison principle on every smaller plane domain.
-/
theorem subharmonicByPlaneComparisonOn_mono
    {U V : Set ℂ} {u : ℂ → ℝ}
    (hVU : V ⊆ U)
    (hu : IsSubharmonicByPlaneComparisonOn U u) :
    IsSubharmonicByPlaneComparisonOn V u := by
  refine ⟨hu.1.mono hVU, ?_⟩
  intro W hW_open hW_preconnected hW_frontier_nonempty hWV hW_compact
    hW_closure h hharmonic hcontinuous hboundary x hxW
  exact hu.2 W hW_open hW_preconnected hW_frontier_nonempty
    (hWV.trans hVU) hW_compact (hW_closure.trans hVU)
    h hharmonic hcontinuous hboundary x hxW

/--
%%handwave
name:
  Plane comparison subharmonicity is unchanged by equality on the domain
statement:
  If two functions agree on a plane domain, then comparison-subharmonicity of
  one on that domain implies comparison-subharmonicity of the other.
-/
theorem subharmonicByPlaneComparisonOn_congr_on
    {U : Set ℂ} {u v : ℂ → ℝ}
    (hu : IsSubharmonicByPlaneComparisonOn U u)
    (huv : Set.EqOn u v U) :
    IsSubharmonicByPlaneComparisonOn U v := by
  refine ⟨?_, ?_⟩
  · rw [upperSemicontinuousOn_iff]
    intro x hxU
    have hux : UpperSemicontinuousWithinAt u U x :=
      hu.1.upperSemicontinuousWithinAt hxU
    rw [upperSemicontinuousWithinAt_iff] at hux ⊢
    intro a hva
    have hua : u x < a := by
      simpa [huv hxU] using hva
    filter_upwards [hux a hua, self_mem_nhdsWithin] with y hylt hyU
    simpa [huv hyU] using hylt
  · intro W hW_open hW_preconnected hW_frontier_nonempty hWU hW_compact
      hW_closure h hharmonic hcontinuous hboundary x hxW
    have hboundary_u : ∀ y ∈ frontier W, u y ≤ h y := by
      intro y hy
      rw [huv (hW_closure (frontier_subset_closure hy))]
      exact hboundary y hy
    have hu_le : u x ≤ h x :=
      hu.2 W hW_open hW_preconnected hW_frontier_nonempty hWU
        hW_compact hW_closure h hharmonic hcontinuous hboundary_u x hxW
    simpa [huv (hWU hxW)] using hu_le

/--
%%handwave
name:
  Circle trace upper bound
statement:
  A real number \(M\) is an upper bound for the trace of a function on the
  circle of center \(c\) and radius \(r\) when the function is at most \(M\)
  along one full positively oriented parametrization of the circle.
-/
def CircleTraceUpperBound (u : ℂ → ℝ) (c : ℂ) (r M : ℝ) : Prop :=
  ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi), u (circleMap c r θ) ≤ M

/--
%%handwave
name:
  Extended circle average with an upper bound
statement:
  If a real-valued function on a circle is bounded above by \(M\), its
  extended circle average is
  \[
    M-\fint (M-u).
  \]
  The second average is a nonnegative extended integral, so the result may be
  \(-\infty\) when the negative part is not integrable.
-/
noncomputable def upperCircleAverageERealWithBound
    (u : ℂ → ℝ) (c : ℂ) (r M : ℝ) : EReal :=
  (M : EReal) -
    ((MeasureTheory.laverage
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
      (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))) : EReal)

private theorem laverage_add_const_left
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] [NeZero μ]
    (a : ENNReal) (f : α → ENNReal) :
    MeasureTheory.laverage μ (fun x ↦ a + f x) =
      a + MeasureTheory.laverage μ f := by
  rw [MeasureTheory.laverage_eq', MeasureTheory.laverage_eq']
  rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const]
  simp

private theorem laverage_add_left_of_aemeasurable
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f g : α → ENNReal}
    (hf : AEMeasurable f μ) :
    MeasureTheory.laverage μ (fun x ↦ f x + g x) =
      MeasureTheory.laverage μ f + MeasureTheory.laverage μ g := by
  rw [MeasureTheory.laverage_eq, MeasureTheory.laverage_eq, MeasureTheory.laverage_eq]
  rw [MeasureTheory.lintegral_add_left' hf, ENNReal.add_div]

private theorem upperSemicontinuousOn_circleTrace_aemeasurable
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U) :
    AEMeasurable
      (fun θ : ℝ ↦ u (circleMap c r θ))
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
  let s : Set ℝ := Set.uIoc (0 : ℝ) (2 * Real.pi)
  have hmaps :
      Set.MapsTo (circleMap c r) s U := by
    intro θ _hθ
    exact hclosed (circleMap_mem_closedBall c hr.le θ)
  have htrace :
      UpperSemicontinuousOn
        (fun θ : ℝ ↦ u (circleMap c r θ))
        s := by
    simpa [Function.comp_def, s] using
      hu.comp ((continuous_circleMap c r).continuousOn) hmaps
  have htrace_meas :
      Measurable
        (s.restrict (fun θ : ℝ ↦ u (circleMap c r θ))) :=
    (upperSemicontinuousOn_iff_restrict.mpr htrace).measurable
  exact aemeasurable_restrict_of_measurable_subtype
    (μ := MeasureTheory.volume) (s := s) measurableSet_uIoc htrace_meas

private theorem upperSemicontinuousOn_circleTraceSub_aemeasurable
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U) :
    AEMeasurable
      (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
  exact (aemeasurable_const.sub
    (upperSemicontinuousOn_circleTrace_aemeasurable hu hr hclosed)).ennreal_ofReal

private theorem ereal_sub_add_coe_cancel_ennreal
    {M d : ℝ} (hd : 0 ≤ d) (L : ENNReal) :
    (M : EReal) - (L : EReal) =
      (M + d : EReal) -
        (((ENNReal.ofReal d + L : ENNReal) : EReal)) := by
  by_cases hLtop : L = ⊤
  · simp [hLtop]
  · lift L to NNReal using hLtop
    rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, max_eq_left hd]
    simp_rw [EReal.coe_nnreal_eq_coe_real]
    rw [← EReal.coe_sub M (L : ℝ)]
    rw [← EReal.coe_add d (L : ℝ)]
    rw [← EReal.coe_add M d]
    rw [← EReal.coe_sub (M + d) (d + (L : ℝ))]
    norm_cast
    ring

private theorem ereal_sub_ennreal_add_eq_add_sub_ennreal
    (Mu Mv : ℝ) (Lu Lv : ENNReal) :
    ((Mu + Mv : ℝ) : EReal) -
        (((Lu + Lv : ENNReal) : EReal)) =
      ((Mu : EReal) - (Lu : EReal)) +
        ((Mv : EReal) - (Lv : EReal)) := by
  by_cases hLu : Lu = ⊤
  · simp [hLu]
  by_cases hLv : Lv = ⊤
  · simp [hLv]
  lift Lu to NNReal using hLu
  lift Lv to NNReal using hLv
  rw [EReal.coe_ennreal_add]
  simp_rw [EReal.coe_nnreal_eq_coe_real]
  rw [← EReal.coe_sub Mu (Lu : ℝ)]
  rw [← EReal.coe_sub Mv (Lv : ℝ)]
  rw [← EReal.coe_add (Mu - (Lu : ℝ)) (Mv - (Lv : ℝ))]
  rw [← EReal.coe_add (Lu : ℝ) (Lv : ℝ)]
  rw [← EReal.coe_sub (Mu + Mv) ((Lu : ℝ) + (Lv : ℝ))]
  norm_cast
  rw [NNReal.coe_add]
  ring_nf

private theorem laverage_eq_zero_of_self_le_sub_laverage
    {a : ℝ} {L : ENNReal}
    (h : (a : EReal) ≤ (a : EReal) - (L : EReal)) :
    L = 0 := by
  by_cases htop : L = ⊤
  · subst htop
    simp [EReal.sub_top] at h
  · lift L to NNReal using htop
    have hle : a ≤ a - (L : ℝ) := by
      have h' : (a : EReal) ≤ ((a - (L : ℝ) : ℝ) : EReal) := by
        simpa [EReal.coe_nnreal_eq_coe_real, EReal.coe_sub] using h
      exact EReal.coe_le_coe_iff.mp h'
    have hLreal : (L : ℝ) = 0 := by
      have hnonneg : 0 ≤ (L : ℝ) := L.2
      linarith
    apply ENNReal.coe_eq_zero.mpr
    apply Subtype.ext
    exact hLreal

private theorem ae_eq_zero_of_laverage_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] {f : α → ENNReal}
    (hf : AEMeasurable f μ)
    (havg : MeasureTheory.laverage μ f = 0) :
    f =ᵐ[μ] 0 := by
  have hint : ∫⁻ x, f x ∂μ = 0 := by
    rw [← MeasureTheory.measure_mul_laverage μ f, havg, mul_zero]
  exact (MeasureTheory.lintegral_eq_zero_iff' hf).mp hint

private theorem ae_eq_zero_false_of_pos_measure_subset_ne_zero
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ENNReal} {A s : Set α}
    (hAs : A ⊆ s)
    (hApos : 0 < μ A)
    (hae : f =ᵐ[μ.restrict s] 0)
    (hA_ne_zero : ∀ x ∈ A, f x ≠ 0) :
    False := by
  have hzero : (μ.restrict s) {x | f x ≠ 0} = 0 := by
    simpa [Filter.EventuallyEq] using MeasureTheory.ae_iff.mp hae
  have hA_zero : μ A = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      μ A = μ.restrict s A := (MeasureTheory.Measure.restrict_eq_self μ hAs).symm
      _ ≤ μ.restrict s {x | f x ≠ 0} := MeasureTheory.measure_mono hA_ne_zero
      _ = 0 := hzero
  exact hApos.ne' hA_zero

private theorem volume_inter_Ioc_pos_of_mem_nhds_of_mem_Ioc
    {N : Set ℝ} {θ a b : ℝ}
    (hab : a < b) (hθ : θ ∈ Set.Ioc a b) (hN : N ∈ 𝓝 θ) :
    0 < MeasureTheory.volume (N ∩ Set.Ioc a b) := by
  rcases Metric.mem_nhds_iff.mp hN with ⟨ε, hεpos, hεsub⟩
  by_cases hθlt : θ < b
  · let δ : ℝ := min (ε / 2) (min ((θ - a) / 2) ((b - θ) / 2))
    have hδpos : 0 < δ := by
      dsimp [δ]
      have hε2 : 0 < ε / 2 := by positivity
      have hθa2 : 0 < (θ - a) / 2 := by linarith [hθ.1]
      have hbθ2 : 0 < (b - θ) / 2 := by linarith [hθlt]
      exact lt_min hε2 (lt_min hθa2 hbθ2)
    have hsub : Set.Ioo (θ - δ) (θ + δ) ⊆ N ∩ Set.Ioc a b := by
      intro x hx
      have hxball : x ∈ Metric.ball θ ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hdist_lt : |x - θ| < δ := by
          rw [abs_lt]
          constructor <;> linarith [hx.1, hx.2]
        have hδ_lt_eps : δ < ε := by
          have hδ_le_eps : δ ≤ ε / 2 := by
            dsimp [δ]
            exact min_le_left _ _
          linarith
        exact hdist_lt.trans hδ_lt_eps
      have hxN : x ∈ N := hεsub hxball
      have hδ_le_θa : δ ≤ (θ - a) / 2 := by
        dsimp [δ]
        exact (min_le_right _ _).trans (min_le_left _ _)
      have hδ_le_bθ : δ ≤ (b - θ) / 2 := by
        dsimp [δ]
        exact (min_le_right _ _).trans (min_le_right _ _)
      have hxa : a < x := by linarith [hx.1, hδ_le_θa]
      have hxb : x ≤ b := by linarith [hx.2, hδ_le_bθ]
      exact ⟨hxN, hxa, hxb⟩
    have hIpos : 0 < MeasureTheory.volume (Set.Ioo (θ - δ) (θ + δ)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith [hδpos])
    exact hIpos.trans_le (MeasureTheory.measure_mono hsub)
  · have hθeq : θ = b := le_antisymm hθ.2 (le_of_not_gt hθlt)
    let δ : ℝ := min (ε / 2) ((θ - a) / 2)
    have hδpos : 0 < δ := by
      dsimp [δ]
      have hε2 : 0 < ε / 2 := by positivity
      have hθa2 : 0 < (θ - a) / 2 := by linarith [hθ.1]
      exact lt_min hε2 hθa2
    have hsub : Set.Ioo (θ - δ) θ ⊆ N ∩ Set.Ioc a b := by
      intro x hx
      have hxball : x ∈ Metric.ball θ ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hdist_lt : |x - θ| < δ := by
          rw [abs_lt]
          constructor <;> linarith [hx.1, hx.2]
        have hδ_lt_eps : δ < ε := by
          have hδ_le_eps : δ ≤ ε / 2 := by
            dsimp [δ]
            exact min_le_left _ _
          linarith
        exact hdist_lt.trans hδ_lt_eps
      have hxN : x ∈ N := hεsub hxball
      have hδ_le_θa : δ ≤ (θ - a) / 2 := by
        dsimp [δ]
        exact min_le_right _ _
      have hxa : a < x := by linarith [hx.1, hδ_le_θa]
      have hxb : x ≤ b := by linarith [hx.2, hθeq]
      exact ⟨hxN, hxa, hxb⟩
    have hIpos : 0 < MeasureTheory.volume (Set.Ioo (θ - δ) θ) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith [hδpos])
    exact hIpos.trans_le (MeasureTheory.measure_mono hsub)

private theorem volume_inter_uIoc_pos_of_mem_nhds_of_mem_uIoc
    {N : Set ℝ} {θ a b : ℝ}
    (hab : a < b) (hθ : θ ∈ Set.uIoc a b) (hN : N ∈ 𝓝 θ) :
    0 < MeasureTheory.volume (N ∩ Set.uIoc a b) := by
  rw [Set.uIoc_of_le hab.le] at hθ ⊢
  exact volume_inter_Ioc_pos_of_mem_nhds_of_mem_Ioc hab hθ hN

private theorem laverage_circleTraceSub_eq_add_of_le
    {u : ℂ → ℝ} {c : ℂ} {r M N : ℝ}
    (hM : CircleTraceUpperBound u c r M) (hMN : M ≤ N) :
    MeasureTheory.laverage
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
      (fun θ : ℝ ↦ ENNReal.ofReal (N - u (circleMap c r θ))) =
        ENNReal.ofReal (N - M) +
          MeasureTheory.laverage
            (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
            (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ))) := by
  let s : Set ℝ := Set.uIoc (0 : ℝ) (2 * Real.pi)
  have hs_ne_top : MeasureTheory.volume s ≠ ⊤ := by
    simp [s]
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hs_ne_zero : MeasureTheory.volume s ≠ 0 := by
    simp [s]
  haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict s) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr hs_ne_top⟩
  haveI : NeZero (MeasureTheory.volume s) := ⟨hs_ne_zero⟩
  calc
    MeasureTheory.laverage
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
        (fun θ : ℝ ↦ ENNReal.ofReal (N - u (circleMap c r θ)))
        = MeasureTheory.laverage
            (MeasureTheory.volume.restrict s)
            (fun θ : ℝ ↦ ENNReal.ofReal (N - u (circleMap c r θ))) := rfl
    _ = MeasureTheory.laverage
          (MeasureTheory.volume.restrict s)
          (fun θ : ℝ ↦
            ENNReal.ofReal (N - M) +
              ENNReal.ofReal (M - u (circleMap c r θ))) := by
        apply MeasureTheory.laverage_congr
        filter_upwards
          [MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume)
            measurableSet_uIoc] with θ hθ
        have hNM_nonneg : 0 ≤ N - M := sub_nonneg.mpr hMN
        have hMu_nonneg : 0 ≤ M - u (circleMap c r θ) :=
          sub_nonneg.mpr (hM θ hθ)
        have hsplit :
            N - u (circleMap c r θ) =
              (N - M) + (M - u (circleMap c r θ)) := by
          ring
        rw [hsplit, ENNReal.ofReal_add hNM_nonneg hMu_nonneg]
    _ = ENNReal.ofReal (N - M) +
          MeasureTheory.laverage
            (MeasureTheory.volume.restrict s)
            (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ))) := by
        exact laverage_add_const_left (MeasureTheory.volume.restrict s)
          (ENNReal.ofReal (N - M))
          (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))
    _ = ENNReal.ofReal (N - M) +
          MeasureTheory.laverage
            (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
            (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ))) := rfl

private theorem upperCircleAverageERealWithBound_eq_of_bounds_of_le
    {u : ℂ → ℝ} {c : ℂ} {r M N : ℝ}
    (hM : CircleTraceUpperBound u c r M) (hMN : M ≤ N) :
    upperCircleAverageERealWithBound u c r M =
      upperCircleAverageERealWithBound u c r N := by
  let L : ENNReal :=
    MeasureTheory.laverage
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
      (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))
  have hshift :
      MeasureTheory.laverage
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
        (fun θ : ℝ ↦ ENNReal.ofReal (N - u (circleMap c r θ))) =
          ENNReal.ofReal (N - M) + L := by
    simpa [L] using laverage_circleTraceSub_eq_add_of_le hM hMN
  have hNM_nonneg : 0 ≤ N - M := sub_nonneg.mpr hMN
  unfold upperCircleAverageERealWithBound
  rw [hshift]
  change (M : EReal) - (L : EReal) =
    (N : EReal) - (((ENNReal.ofReal (N - M) + L : ENNReal) : EReal))
  calc
    (M : EReal) - (L : EReal)
        = (M + (N - M) : EReal) -
            (((ENNReal.ofReal (N - M) + L : ENNReal) : EReal)) :=
          ereal_sub_add_coe_cancel_ennreal hNM_nonneg L
    _ = (N : EReal) -
          (((ENNReal.ofReal (N - M) + L : ENNReal) : EReal)) := by
        have hMN_eq : M + (N - M) = N := by ring
        rw [← EReal.coe_sub N M]
        rw [← EReal.coe_add M (N - M)]
        rw [hMN_eq]

/--
%%handwave
name:
  Extended circle average is independent of the upper bound
statement:
  The extended circle average computed from \(M-\fint(M-u)\) is independent of
  the chosen finite upper bound for the trace.
proof:
  If \(M\leq N\), then \(N-u=(N-M)+(M-u)\).  The normalized nonnegative
  integral of the constant \(N-M\) is \(N-M\), so the extra term cancels.
  The general case follows by comparing both bounds with their maximum.
-/
theorem upperCircleAverageERealWithBound_eq_of_bounds
    {u : ℂ → ℝ} {c : ℂ} {r M N : ℝ}
    (hM : CircleTraceUpperBound u c r M)
    (hN : CircleTraceUpperBound u c r N) :
    upperCircleAverageERealWithBound u c r M =
      upperCircleAverageERealWithBound u c r N := by
  by_cases hMN : M ≤ N
  · exact upperCircleAverageERealWithBound_eq_of_bounds_of_le hM hMN
  · exact (upperCircleAverageERealWithBound_eq_of_bounds_of_le hN
      (le_of_lt (lt_of_not_ge hMN))).symm

/--
%%handwave
name:
  Upper semicontinuous circle traces are bounded above
statement:
  The trace of an upper semicontinuous finite-valued function on a compactly
  contained circle has a finite upper bound.
proof:
  Restrict the function to the compact circle.  Upper semicontinuity is
  preserved by restriction and by the circle parametrization, and an upper
  semicontinuous real-valued function on a compact space attains a finite
  maximum.
-/
theorem upperSemicontinuousOn_exists_circle_trace_upper_bound
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U) :
    ∃ M : ℝ, CircleTraceUpperBound u c r M := by
  have hmaps :
      Set.MapsTo (circleMap c r) (Set.uIcc (0 : ℝ) (2 * Real.pi)) U := by
    intro θ _hθ
    exact hclosed (circleMap_mem_closedBall c hr.le θ)
  have htrace :
      UpperSemicontinuousOn
        (fun θ : ℝ ↦ u (circleMap c r θ))
        (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    simpa [Function.comp_def] using
      hu.comp ((continuous_circleMap c r).continuousOn) hmaps
  rcases UpperSemicontinuousOn.bddAbove_of_isCompact
      isCompact_uIcc htrace with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro θ hθ
  exact hM ⟨θ, Set.uIoc_subset_uIcc hθ, rfl⟩

/--
%%handwave
name:
  Monotonicity of extended circle averages
statement:
  If two functions are bounded above on the same circle by the same real
  number and the first trace is pointwise at most the second, then the
  extended circle average of the first is at most the extended circle average
  of the second.
proof:
  The pointwise inequality reverses after subtracting from the common upper
  bound.  Monotonicity of the nonnegative integral gives the reverse
  inequality for the subtracted averages, hence the desired inequality after
  subtracting from \(M\).
-/
theorem upperCircleAverageERealWithBound_mono
    {u v : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (_huM : CircleTraceUpperBound u c r M)
    (_hvM : CircleTraceUpperBound v c r M)
    (huv : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
      u (circleMap c r θ) ≤ v (circleMap c r θ)) :
    upperCircleAverageERealWithBound u c r M ≤
      upperCircleAverageERealWithBound v c r M := by
  apply EReal.sub_le_sub le_rfl
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  rw [MeasureTheory.laverage_eq, MeasureTheory.laverage_eq]
  apply ENNReal.div_le_div_right
  apply MeasureTheory.lintegral_mono_ae
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume)
      measurableSet_uIoc] with θ hθ
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (huv θ hθ) M)

/--
%%handwave
name:
  Monotonicity of extended circle averages with different bounds
statement:
  If one circle trace is pointwise at most another, then the extended circle
  average of the first is at most the extended circle average of the second,
  independently of which finite upper bounds are used to present the two
  averages.
proof:
  The upper bound for the larger trace is also an upper bound for the smaller
  trace.  Replace the smaller trace's chosen bound by that common bound using
  [independence of the finite upper
  bound](lean:JJMath.Uniformization.upperCircleAverageERealWithBound_eq_of_bounds),
  then apply monotonicity with a common bound.
-/
theorem upperCircleAverageERealWithBound_mono_of_bounds
    {u v : ℂ → ℝ} {c : ℂ} {r M N : ℝ}
    (hM : CircleTraceUpperBound u c r M)
    (hN : CircleTraceUpperBound v c r N)
    (huv : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
      u (circleMap c r θ) ≤ v (circleMap c r θ)) :
    upperCircleAverageERealWithBound u c r M ≤
      upperCircleAverageERealWithBound v c r N := by
  have hNu : CircleTraceUpperBound u c r N := by
    intro θ hθ
    exact (huv θ hθ).trans (hN θ hθ)
  calc
    upperCircleAverageERealWithBound u c r M
        = upperCircleAverageERealWithBound u c r N :=
          upperCircleAverageERealWithBound_eq_of_bounds hM hNu
    _ ≤ upperCircleAverageERealWithBound v c r N :=
          upperCircleAverageERealWithBound_mono hNu hN huv

/--
%%handwave
name:
  Lower average of an upper-bounded integrable circle trace
statement:
  If an ordinarily integrable circle trace is bounded above by \(M\), then the
  nonnegative average of \(M-u\) is \(\operatorname{ofReal}(M-\fint u)\).
proof:
  The function \(M-u\) is nonnegative on the parametrizing interval and
  integrable because the trace of \(u\) is integrable.  Apply the standard
  identity relating the lower integral of `ofReal` to the Bochner average of a
  nonnegative integrable function, and use linearity of ordinary averages to
  rewrite \(\fint(M-u)\) as \(M-\fint u\).
-/
theorem laverage_ofReal_circleTraceSub_eq_ofReal_sub_circleAverage
    {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hM : CircleTraceUpperBound u c r M)
    (hu : CircleIntegrable u c r) :
    MeasureTheory.laverage
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
      (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ))) =
        ENNReal.ofReal (M - Real.circleAverage u c r) := by
  let s : Set ℝ := Set.uIoc (0 : ℝ) (2 * Real.pi)
  let tr : ℝ → ℝ := fun θ ↦ u (circleMap c r θ)
  have hs_ne_top : MeasureTheory.volume s ≠ ⊤ := by
    simp [s]
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hs_ne_zero : MeasureTheory.volume s ≠ 0 := by
    simp [s]
  have htr_int : MeasureTheory.IntegrableOn tr s := by
    simpa [tr, s, CircleIntegrable] using
      (intervalIntegrable_iff.mp hu)
  have hconst_int : MeasureTheory.IntegrableOn (fun _ : ℝ ↦ M) s :=
    MeasureTheory.integrableOn_const hs_ne_top
  have hg_int : MeasureTheory.IntegrableOn (fun θ : ℝ ↦ M - tr θ) s :=
    hconst_int.sub htr_int
  have hg_nonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict s] (fun θ : ℝ ↦ M - tr θ) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume)
      measurableSet_uIoc] with θ hθ
    exact sub_nonneg.mpr (hM θ hθ)
  have havg_sub :
      (⨍ θ in s, M - tr θ) = M - Real.circleAverage u c r := by
    have havg_tr :
        (⨍ θ in s, tr θ) = Real.circleAverage u c r := by
      rw [Real.circleAverage_eq_intervalAverage]
    calc
      (⨍ θ in s, M - tr θ)
          = (⨍ θ in s, (fun _ : ℝ ↦ M) θ) - (⨍ θ in s, tr θ) := by
            rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq,
              MeasureTheory.setAverage_eq]
            rw [MeasureTheory.integral_sub hconst_int htr_int]
            simp [smul_eq_mul, sub_eq_add_neg, mul_add]
      _ = M - Real.circleAverage u c r := by
            rw [MeasureTheory.setAverage_const hs_ne_zero hs_ne_top M, havg_tr]
  calc
    MeasureTheory.laverage
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
        (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))
        = MeasureTheory.laverage
            (MeasureTheory.volume.restrict s)
            (fun θ : ℝ ↦ ENNReal.ofReal (M - tr θ)) := rfl
    _ = ENNReal.ofReal (⨍ θ in s, M - tr θ) := by
          rw [MeasureTheory.laverage_eq, MeasureTheory.ofReal_setAverage hg_int hg_nonneg,
            MeasureTheory.Measure.restrict_apply_univ]
    _ = ENNReal.ofReal (M - Real.circleAverage u c r) := by
          rw [havg_sub]

/--
%%handwave
name:
  Extended circle averages agree with ordinary circle averages
statement:
  When the circle trace is ordinarily integrable, the extended average
  \(M-\fint(M-u)\) agrees with the usual real-valued circle average.
proof:
  Rewrite the nonnegative integral of \(M-u\) as the ordinary integral of
  \(M-u\).  The average of the constant \(M\) is \(M\), so subtracting gives
  the ordinary average of \(u\).
-/
theorem upperCircleAverageERealWithBound_eq_real_circleAverage
    {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hM : CircleTraceUpperBound u c r M)
    (hu : CircleIntegrable u c r) :
    upperCircleAverageERealWithBound u c r M =
      ((Real.circleAverage u c r : ℝ) : EReal) := by
  have hlavg :
      MeasureTheory.laverage
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
        (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ))) =
          ENNReal.ofReal (M - Real.circleAverage u c r) :=
    laverage_ofReal_circleTraceSub_eq_ofReal_sub_circleAverage hM hu
  have hsphere_bound : ∀ x ∈ Metric.sphere c |r|, u x ≤ M := by
    intro x hx
    have hx_image : x ∈ circleMap c r '' Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      simpa [image_circleMap_Ioc] using hx
    rcases hx_image with ⟨θ, hθ, rfl⟩
    exact hM θ (by simpa [Set.uIoc_of_le Real.two_pi_pos.le] using hθ)
  have havg_le : Real.circleAverage u c r ≤ M :=
    Real.circleAverage_mono_on_of_le_circle hu hsphere_bound
  have hnonneg : 0 ≤ M - Real.circleAverage u c r :=
    sub_nonneg.mpr havg_le
  unfold upperCircleAverageERealWithBound
  rw [hlavg, EReal.coe_ennreal_ofReal, max_eq_left hnonneg]
  rw [← EReal.coe_sub]
  congr
  ring

/--
%%handwave
name:
  Integrable extended circle average is independent of the upper bound
statement:
  For an ordinarily integrable circle trace, the extended circle average is
  independent of the finite upper bound used to present it.
proof:
  For each upper bound,
  [the extended average agrees with the ordinary circle
  average](lean:JJMath.Uniformization.upperCircleAverageERealWithBound_eq_real_circleAverage).
-/
theorem upperCircleAverageERealWithBound_eq_of_bounds_of_circleIntegrable
    {u : ℂ → ℝ} {c : ℂ} {r M N : ℝ}
    (hM : CircleTraceUpperBound u c r M)
    (hN : CircleTraceUpperBound u c r N)
    (hu : CircleIntegrable u c r) :
    upperCircleAverageERealWithBound u c r M =
      upperCircleAverageERealWithBound u c r N := by
  rw [upperCircleAverageERealWithBound_eq_real_circleAverage hM hu,
    upperCircleAverageERealWithBound_eq_real_circleAverage hN hu]

/--
%%handwave
name:
  Harmonic functions satisfy the extended circle-mean identity
statement:
  If a harmonic function is defined on a neighborhood of a closed Euclidean
  disc, then every upper-bound presentation of its extended circle average is
  its value at the center.
proof:
  Harmonic functions are continuous, hence their circle traces are ordinarily
  integrable.  The extended average agrees with the ordinary circle average,
  and the ordinary circle average is the center value by the harmonic
  mean-value theorem.
-/
theorem harmonicOnNhd_upperCircleAverageERealWithBound_eq
    {V : Set ℂ} {h : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hh : InnerProductSpace.HarmonicOnNhd h V)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ V)
    (hM : CircleTraceUpperBound h c r M) :
    upperCircleAverageERealWithBound h c r M = (h c : EReal) := by
  have hcircle_int : CircleIntegrable h c r := by
    have hcont_closed : ContinuousOn h (Metric.closedBall c r) :=
      hh.continuousOn.mono hclosed
    have hsphere_subset : Metric.sphere c |r| ⊆ Metric.closedBall c r := by
      rw [abs_of_pos hr]
      exact Metric.sphere_subset_closedBall
    exact (hcont_closed.mono hsphere_subset).circleIntegrable'
  rw [upperCircleAverageERealWithBound_eq_real_circleAverage hM hcircle_int]
  have hh_abs : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c |r|) := by
    rw [abs_of_pos hr]
    exact hh.mono hclosed
  rw [HarmonicOnNhd.circleAverage_eq (f := h) (c := c) (R := r) hh_abs]

/--
%%handwave
name:
  Extended circle-mean subharmonicity in the plane
statement:
  A real-valued function on a plane domain is subharmonic in the extended
  circle-mean sense when it is upper semicontinuous and, on every compactly
  contained circle, its value at the center is at most the extended circle
  average of its trace.  The average is computed using any finite upper bound
  for the trace.
-/
def IsSubharmonicByExtendedCircleAverageOn (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  UpperSemicontinuousOn u U ∧
    ∀ c ∈ U, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ U →
      (∃ M : ℝ, CircleTraceUpperBound u c r M) ∧
        ∀ M : ℝ, CircleTraceUpperBound u c r M →
          (u c : EReal) ≤ upperCircleAverageERealWithBound u c r M

/--
%%handwave
name:
  Extended circle-mean subharmonicity restricts to smaller domains
statement:
  A function satisfying the extended circle-mean subharmonicity condition on a
  plane domain satisfies the same condition on every smaller plane domain.
-/
theorem subharmonicByExtendedCircleAverageOn_mono
    {U V : Set ℂ} {u : ℂ → ℝ}
    (hVU : V ⊆ U)
    (hu : IsSubharmonicByExtendedCircleAverageOn U u) :
    IsSubharmonicByExtendedCircleAverageOn V u := by
  refine ⟨hu.1.mono hVU, ?_⟩
  intro c hcV r hr hclosed
  exact hu.2 c (hVU hcV) r hr (hclosed.trans hVU)

/--
%%handwave
name:
  Extended circle means recover ordinary circle means
statement:
  If an extended circle-mean subharmonic function has an ordinarily integrable
  trace on a compactly contained circle, then its value at the center is at
  most the ordinary circle average of that trace.
proof:
  Use the finite upper bound supplied by the extended circle-mean condition.
  For an integrable trace, [the extended average agrees with the ordinary
  circle average](lean:JJMath.Uniformization.upperCircleAverageERealWithBound_eq_real_circleAverage).
-/
theorem subharmonicByExtendedCircleAverageOn_le_circleAverage
    {U : Set ℂ} {u : ℂ → ℝ}
    (hu : IsSubharmonicByExtendedCircleAverageOn U u)
    {c : ℂ} {r : ℝ}
    (hcU : c ∈ U) (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U)
    (hcircle : CircleIntegrable u c r) :
    u c ≤ Real.circleAverage u c r := by
  rcases hu.2 c hcU r hr hclosed with ⟨⟨M, hM⟩, hineq⟩
  have hle : (u c : EReal) ≤ ((Real.circleAverage u c r : ℝ) : EReal) := by
    calc
      (u c : EReal) ≤ upperCircleAverageERealWithBound u c r M :=
        hineq M hM
      _ = ((Real.circleAverage u c r : ℝ) : EReal) :=
        upperCircleAverageERealWithBound_eq_real_circleAverage hM hcircle
  exact EReal.coe_le_coe_iff.mp hle

/--
%%handwave
name:
  Extended circle averages commute with sums
statement:
  For upper semicontinuous traces on a compactly contained circle, the
  extended circle average of a sum is the sum of the extended circle averages.
proof:
  With upper bounds \(M_u\) and \(M_v\),
  \[
    (M_u+M_v)-(u+v)=(M_u-u)+(M_v-v).
  \]
  The two summands on the right are nonnegative measurable functions on the
  circle parameter interval.  Additivity of the nonnegative integral gives the
  identity, and the finite upper-bound terms cancel in the extended reals.
-/
theorem upperCircleAverageERealWithBound_add_of_upperSemicontinuousOn
    {U : Set ℂ} {u v : ℂ → ℝ} {c : ℂ} {r Mu Mv : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (_hv : UpperSemicontinuousOn v U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U)
    (hMu : CircleTraceUpperBound u c r Mu)
    (hMv : CircleTraceUpperBound v c r Mv) :
    upperCircleAverageERealWithBound (fun z ↦ u z + v z) c r (Mu + Mv) =
      upperCircleAverageERealWithBound u c r Mu +
        upperCircleAverageERealWithBound v c r Mv := by
  let s : Set ℝ := Set.uIoc (0 : ℝ) (2 * Real.pi)
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict s
  let Fu : ℝ → ENNReal :=
    fun θ ↦ ENNReal.ofReal (Mu - u (circleMap c r θ))
  let Fv : ℝ → ENNReal :=
    fun θ ↦ ENNReal.ofReal (Mv - v (circleMap c r θ))
  have hFu_meas : AEMeasurable Fu μ := by
    simpa [Fu, μ, s] using
      upperSemicontinuousOn_circleTraceSub_aemeasurable
        (u := u) (c := c) (r := r) (M := Mu) hu hr hclosed
  have hsum_laverage :
      MeasureTheory.laverage μ
        (fun θ : ℝ ↦
          ENNReal.ofReal
            ((Mu + Mv) -
              ((fun z : ℂ ↦ u z + v z) (circleMap c r θ)))) =
        MeasureTheory.laverage μ (fun θ : ℝ ↦ Fu θ + Fv θ) := by
    apply MeasureTheory.laverage_congr
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume)
        measurableSet_uIoc] with θ hθ
    have hMu_nonneg : 0 ≤ Mu - u (circleMap c r θ) :=
      sub_nonneg.mpr (hMu θ hθ)
    have hMv_nonneg : 0 ≤ Mv - v (circleMap c r θ) :=
      sub_nonneg.mpr (hMv θ hθ)
    have hsplit :
        (Mu + Mv) -
            ((fun z : ℂ ↦ u z + v z) (circleMap c r θ)) =
          (Mu - u (circleMap c r θ)) +
            (Mv - v (circleMap c r θ)) := by
      ring
    rw [hsplit, ENNReal.ofReal_add hMu_nonneg hMv_nonneg]
  have havg_add :
      MeasureTheory.laverage μ
        (fun θ : ℝ ↦
          ENNReal.ofReal
            ((Mu + Mv) -
              ((fun z : ℂ ↦ u z + v z) (circleMap c r θ)))) =
        MeasureTheory.laverage μ Fu + MeasureTheory.laverage μ Fv := by
    rw [hsum_laverage]
    exact laverage_add_left_of_aemeasurable hFu_meas
  unfold upperCircleAverageERealWithBound
  change
    ((Mu + Mv : ℝ) : EReal) -
        ((MeasureTheory.laverage μ
          (fun θ : ℝ ↦
            ENNReal.ofReal
              ((Mu + Mv) -
                ((fun z : ℂ ↦ u z + v z) (circleMap c r θ)))) : ENNReal) : EReal) =
      ((Mu : EReal) -
          ((MeasureTheory.laverage μ Fu : ENNReal) : EReal)) +
        ((Mv : EReal) -
          ((MeasureTheory.laverage μ Fv : ENNReal) : EReal))
  rw [havg_add]
  exact ereal_sub_ennreal_add_eq_add_sub_ennreal Mu Mv
    (MeasureTheory.laverage μ Fu) (MeasureTheory.laverage μ Fv)

/--
%%handwave
name:
  Sums preserve extended circle-mean subharmonicity
statement:
  The sum of two extended circle-mean subharmonic functions on the same plane
  domain is extended circle-mean subharmonic.
proof:
  Upper semicontinuity is preserved by addition.  On each compactly contained
  circle, take finite upper bounds for the two traces; their sum is an upper
  bound for the summed trace.  The center inequalities add, and
  [extended circle averages commute with
  sums](lean:JJMath.Uniformization.upperCircleAverageERealWithBound_add_of_upperSemicontinuousOn).
  If the target presentation uses a different upper bound, replace it using
  [independence of the finite upper
  bound](lean:JJMath.Uniformization.upperCircleAverageERealWithBound_eq_of_bounds).
-/
theorem subharmonicByExtendedCircleAverageOn_add
    {U : Set ℂ} {u v : ℂ → ℝ}
    (hu : IsSubharmonicByExtendedCircleAverageOn U u)
    (hv : IsSubharmonicByExtendedCircleAverageOn U v) :
    IsSubharmonicByExtendedCircleAverageOn U (fun z ↦ u z + v z) := by
  refine ⟨hu.1.add hv.1, ?_⟩
  intro c hcU r hr hclosed
  rcases hu.2 c hcU r hr hclosed with ⟨⟨Mu, hMu⟩, hu_avg⟩
  rcases hv.2 c hcU r hr hclosed with ⟨⟨Mv, hMv⟩, hv_avg⟩
  have hsum_bound :
      CircleTraceUpperBound (fun z ↦ u z + v z) c r (Mu + Mv) := by
    intro θ hθ
    exact add_le_add (hMu θ hθ) (hMv θ hθ)
  refine ⟨⟨Mu + Mv, hsum_bound⟩, ?_⟩
  intro M hM
  calc
    ((u c + v c : ℝ) : EReal)
        = (u c : EReal) + (v c : EReal) := by
          rw [EReal.coe_add]
    _ ≤ upperCircleAverageERealWithBound u c r Mu +
          upperCircleAverageERealWithBound v c r Mv :=
        add_le_add (hu_avg Mu hMu) (hv_avg Mv hMv)
    _ = upperCircleAverageERealWithBound (fun z ↦ u z + v z) c r (Mu + Mv) := by
        rw [upperCircleAverageERealWithBound_add_of_upperSemicontinuousOn
          hu.1 hv.1 hr hclosed hMu hMv]
    _ = upperCircleAverageERealWithBound (fun z ↦ u z + v z) c r M :=
        upperCircleAverageERealWithBound_eq_of_bounds hsum_bound hM

/--
%%handwave
name:
  Interior constants extend lower bounds to the boundary
statement:
  If an upper semicontinuous function on the closure of a set is equal to a
  constant on the set, then the boundary values are at least that constant.
proof:
  If a boundary value were strictly smaller, upper semicontinuity would make
  the function strictly smaller than the constant throughout some relative
  neighborhood in the closure.  Since the boundary point lies in the closure
  of the set, that neighborhood meets the set, contradicting constancy there.
-/
theorem upperSemicontinuousOn_constOn_le_of_mem_frontier
    {X : Type} [TopologicalSpace X] {V : Set X} {u : X → ℝ} {a : ℝ} {b : X}
    (hu : UpperSemicontinuousOn u (closure V))
    (heq : Set.EqOn u (fun _ ↦ a) V)
    (hb : b ∈ frontier V) :
    a ≤ u b := by
  by_contra hnot
  have hlt : u b < a := lt_of_not_ge hnot
  have hbclosure : b ∈ closure V := frontier_subset_closure hb
  have hwithin : UpperSemicontinuousWithinAt u (closure V) b :=
    hu.upperSemicontinuousWithinAt hbclosure
  rw [upperSemicontinuousWithinAt_iff] at hwithin
  have hsmall : {x : X | u x < a} ∈ 𝓝[closure V] b :=
    hwithin a hlt
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsmall with
    ⟨W, hW, hWsub⟩
  rcases mem_closure_iff_nhds.mp hbclosure W hW with ⟨y, hyW, hyV⟩
  have hylt : u y < a := hWsub ⟨hyW, subset_closure hyV⟩
  have hyeq : u y = a := heq hyV
  linarith

/--
%%handwave
name:
  Harmonic functions satisfy extended circle means
statement:
  A harmonic function on a plane region is extended circle-mean subharmonic on
  that region.
proof:
  Harmonic functions are continuous, hence upper semicontinuous.  On every
  compactly contained circle, the harmonic mean-value theorem gives equality
  between the center value and every extended circle average presentation.
-/
theorem harmonicOnNhd_extendedCircleAverageOn
    {U : Set ℂ} {h : ℂ → ℝ}
    (hh : InnerProductSpace.HarmonicOnNhd h U) :
    IsSubharmonicByExtendedCircleAverageOn U h := by
  refine ⟨hh.continuousOn.upperSemicontinuousOn, ?_⟩
  intro c _hcU r hr hclosed
  refine ⟨upperSemicontinuousOn_exists_circle_trace_upper_bound
    hh.continuousOn.upperSemicontinuousOn hr hclosed, ?_⟩
  intro M hM
  rw [harmonicOnNhd_upperCircleAverageERealWithBound_eq hh hr hclosed hM]

/--
%%handwave
name:
  Extended circle subharmonic minus harmonic
statement:
  The difference between an extended circle-mean subharmonic function and a
  harmonic function on the same plane region is extended circle-mean
  subharmonic.
proof:
  The negative of a harmonic function is harmonic, hence extended circle-mean
  subharmonic.  Then use
  [extended circle-mean subharmonicity is closed under
  sums](lean:JJMath.Uniformization.subharmonicByExtendedCircleAverageOn_add).
-/
theorem subharmonicByExtendedCircleAverageOn_sub_harmonic
    {U : Set ℂ} {u h : ℂ → ℝ}
    (hu : IsSubharmonicByExtendedCircleAverageOn U u)
    (hh : InnerProductSpace.HarmonicOnNhd h U) :
    IsSubharmonicByExtendedCircleAverageOn U (fun z ↦ u z - h z) := by
  have hneg :
      IsSubharmonicByExtendedCircleAverageOn U (fun z ↦ -h z) :=
    harmonicOnNhd_extendedCircleAverageOn hh.neg
  simpa [sub_eq_add_neg] using
    subharmonicByExtendedCircleAverageOn_add hu hneg

/--
%%handwave
name:
  Extended circle-mean subharmonic functions are locally constant at maxima
statement:
  If an extended circle-mean subharmonic function attains its maximum at an
  interior point of its domain, then it is locally constant near that point.
proof:
  On every sufficiently small circle centered at the maximum point, the
  function is bounded above by the center value.  The extended circle-mean
  inequality then says that the lower integral of the nonnegative drop from
  the center value is zero.  A strict drop anywhere on such a circle would,
  by upper semicontinuity, persist on an arc of positive length, forcing the
  lower integral to be positive.
-/
theorem subharmonicByExtendedCircleAverageOn_eventually_eq_of_isMaxOn
    {U : Set ℂ} {u : ℂ → ℝ}
    (hU_open : IsOpen U)
    (hu : IsSubharmonicByExtendedCircleAverageOn U u)
    {c : ℂ} (hcU : c ∈ U) (hm : IsMaxOn u U c) :
    ∀ᶠ z in 𝓝 c, u z = u c := by
  rcases Metric.isOpen_iff.mp hU_open c hcU with ⟨r, hr, hrsub⟩
  let ρ : ℝ := r / 2
  have hρpos : 0 < ρ := by positivity
  have hρlt : ρ < r := by
    dsimp [ρ]
    linarith
  have hclosedρ : Metric.closedBall c ρ ⊆ U := by
    intro z hz
    exact hrsub (Metric.closedBall_subset_ball hρlt hz)
  have heq_ball : ∀ z ∈ Metric.ball c ρ, u z = u c := by
    intro z hzball
    have hzU : z ∈ U := hclosedρ (Metric.ball_subset_closedBall hzball)
    have hzle : u z ≤ u c := hm hzU
    by_contra hzne
    have hzlt : u z < u c := lt_of_le_of_ne hzle hzne
    by_cases hzc : z = c
    · subst hzc
      exact hzne rfl
    let R : ℝ := dist z c
    have hRpos : 0 < R := by
      dsimp [R]
      exact dist_pos.mpr hzc
    have hRlt : R < ρ := by
      dsimp [R]
      simpa [Metric.mem_ball] using hzball
    have hclosedR : Metric.closedBall c R ⊆ U := by
      intro y hy
      exact hclosedρ (Metric.closedBall_subset_closedBall hRlt.le hy)
    have hM : CircleTraceUpperBound u c R (u c) := by
      intro θ hθ
      exact hm (hclosedR (circleMap_mem_closedBall c hRpos.le θ))
    rcases hu.2 c hcU R hRpos hclosedR with ⟨_hbound, hineq⟩
    let s : Set ℝ := Set.uIoc (0 : ℝ) (2 * Real.pi)
    let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict s
    let f : ℝ → ENNReal :=
      fun θ ↦ ENNReal.ofReal (u c - u (circleMap c R θ))
    have hs_ne_top : MeasureTheory.volume s ≠ ⊤ := by
      simp [s]
      exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    haveI : MeasureTheory.IsFiniteMeasure μ := ⟨by
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr hs_ne_top⟩
    have hLzero : MeasureTheory.laverage μ f = 0 := by
      apply laverage_eq_zero_of_self_le_sub_laverage
      simpa [upperCircleAverageERealWithBound, μ, f, s] using hineq (u c) hM
    have hf_meas : AEMeasurable f μ := by
      simpa [f, μ, s] using
        upperSemicontinuousOn_circleTraceSub_aemeasurable
          (u := u) (c := c) (r := R) (M := u c) hu.1 hRpos hclosedR
    have hzero_ae : f =ᵐ[μ] 0 :=
      ae_eq_zero_of_laverage_eq_zero hf_meas hLzero
    have hz_sphere_abs : z ∈ Metric.sphere c |R| := by
      have hz_sphere : z ∈ Metric.sphere c R := by
        simp [R, dist_eq_norm]
      simpa [abs_of_pos hRpos] using hz_sphere
    rw [← image_circleMap_Ioc c R] at hz_sphere_abs
    rcases hz_sphere_abs with ⟨θ₀, hθ₀, hθ₀_eq⟩
    let a : ℝ := (u z + u c) / 2
    have hzlt_a : u z < a := by
      dsimp [a]
      linarith
    have halt_uc : a < u c := by
      dsimp [a]
      linarith
    have hwithin : UpperSemicontinuousWithinAt u U z :=
      hu.1.upperSemicontinuousWithinAt hzU
    rw [upperSemicontinuousWithinAt_iff] at hwithin
    have hsmall : {y : ℂ | u y < a} ∈ 𝓝[U] z :=
      hwithin a hzlt_a
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsmall with
      ⟨N, hN, hNsub⟩
    let P : Set ℝ := (circleMap c R) ⁻¹' N
    have hP_nhds : P ∈ 𝓝 θ₀ := by
      have hN' : N ∈ 𝓝 (circleMap c R θ₀) := by
        simpa [hθ₀_eq] using hN
      exact (continuous_circleMap c R).continuousAt.preimage_mem_nhds hN'
    have hθ₀_u : θ₀ ∈ s := by
      simpa [s, Set.uIoc_of_le Real.two_pi_pos.le] using hθ₀
    have hP_pos : 0 < MeasureTheory.volume (P ∩ s) := by
      simpa [s] using
        volume_inter_uIoc_pos_of_mem_nhds_of_mem_uIoc
          (N := P) (θ := θ₀) Real.two_pi_pos hθ₀_u hP_nhds
    have hP_ne_zero : ∀ θ ∈ P ∩ s, f θ ≠ 0 := by
      intro θ hθP
      have hθU : circleMap c R θ ∈ U :=
        hclosedR (circleMap_mem_closedBall c hRpos.le θ)
      have hlt_a : u (circleMap c R θ) < a :=
        hNsub ⟨hθP.1, hθU⟩
      have hlt_uc : u (circleMap c R θ) < u c :=
        hlt_a.trans halt_uc
      have hdrop_pos : 0 < u c - u (circleMap c R θ) :=
        sub_pos.mpr hlt_uc
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hdrop_pos)
    exact ae_eq_zero_false_of_pos_measure_subset_ne_zero
      (μ := MeasureTheory.volume) (f := f) (A := P ∩ s) (s := s)
      Set.inter_subset_right hP_pos hzero_ae hP_ne_zero
  filter_upwards [Metric.ball_mem_nhds c hρpos] with z hz
  exact heq_ball z hz

/--
%%handwave
name:
  Strong maximum principle for extended circle means
statement:
  On a preconnected open plane domain, an extended circle-mean subharmonic
  function that attains its maximum at an interior point is constant on the
  domain.
proof:
  The set where the function equals the interior maximum is open by
  [local constancy at an interior
  maximum](lean:JJMath.Uniformization.subharmonicByExtendedCircleAverageOn_eventually_eq_of_isMaxOn).
  Its complement inside the domain is also open by upper semicontinuity.
  Preconnectedness forces the equality set to be the whole domain.
-/
theorem subharmonicByExtendedCircleAverageOn_eqOn_of_isPreconnected_of_isMaxOn
    {U : Set ℂ} {u : ℂ → ℝ}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hu : IsSubharmonicByExtendedCircleAverageOn U u)
    {c : ℂ} (hcU : c ∈ U) (hm : IsMaxOn u U c) :
    Set.EqOn u (fun _ ↦ u c) U := by
  let V : Set ℂ := U ∩ {x | u x = u c}
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 ?_
    intro x hxV
    have hxU : x ∈ U := hxV.1
    have hx_eq : u x = u c := hxV.2
    have hxmaxU : IsMaxOn u U x := by
      intro y hy
      simpa [hx_eq] using hm hy
    have hevent : ∀ᶠ y in 𝓝 x, u y = u x :=
      subharmonicByExtendedCircleAverageOn_eventually_eq_of_isMaxOn
        hU_open hu hxU hxmaxU
    have heqset : {y : ℂ | u y = u c} ∈ 𝓝 x := by
      filter_upwards [hevent] with y hy
      exact hy.trans hx_eq
    exact Filter.inter_mem (hU_open.mem_nhds hxU) heqset
  let W : Set ℂ := U ∩ {x | u x ≠ u c}
  have hWo : IsOpen W := by
    refine isOpen_iff_mem_nhds.2 ?_
    intro x hxW
    have hxU : x ∈ U := hxW.1
    have hxle : u x ≤ u c := hm hxU
    have hxlt : u x < u c := lt_of_le_of_ne hxle hxW.2
    have hwithin : UpperSemicontinuousWithinAt u U x :=
      hu.1.upperSemicontinuousWithinAt hxU
    rw [upperSemicontinuousWithinAt_iff] at hwithin
    have hsmall : {y : ℂ | u y < u c} ∈ 𝓝[U] x :=
      hwithin (u c) hxlt
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsmall with
      ⟨N, hN, hNsub⟩
    have hUN_subset : U ∩ N ⊆ W := by
      intro y hy
      have hylt : u y < u c := hNsub ⟨hy.2, hy.1⟩
      exact ⟨hy.1, (ne_of_lt hylt)⟩
    exact Filter.mem_of_superset
      (Filter.inter_mem (hU_open.mem_nhds hxU) hN) hUN_subset
  have hdVW : Disjoint V W := by
    rw [Set.disjoint_left]
    intro x hxV hxW
    exact hxW.2 hxV.2
  have hUVW : U ⊆ V ∪ W := by
    intro x hx
    by_cases hx_eq : u x = u c
    · exact Or.inl ⟨hx, hx_eq⟩
    · exact Or.inr ⟨hx, hx_eq⟩
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  have hsubset : U ⊆ V :=
    hU_preconnected.subset_left_of_subset_union hVo hWo hdVW hUVW hVne
  intro x hx
  exact (hsubset hx).2

/--
%%handwave
name:
  Extended circle-mean maximum principle
statement:
  If an extended circle-mean subharmonic function is upper semicontinuous on
  the closure of a relatively compact preconnected plane region and is bounded
  above by a constant on the frontier, then it is bounded by that constant in
  the region.
proof:
  Choose a point where the upper semicontinuous function attains its maximum
  on the compact closure.  If the maximum is attained in the interior, the
  extended circle-mean inequality on arbitrarily small circles forces the
  function to be locally constant at that maximum.  Preconnectedness propagates
  this constancy to the frontier, where the assumed boundary bound applies.
-/
theorem subharmonicByExtendedCircleAverageOn_le_constant_of_boundary_le
    {V : Set ℂ} {u : ℂ → ℝ} {M : ℝ}
    (hV_open : IsOpen V)
    (hV_preconnected : IsPreconnected V)
    (hV_frontier_nonempty : (frontier V).Nonempty)
    (hV_compact : IsCompact (closure V))
    (hu_upper_closure : UpperSemicontinuousOn u (closure V))
    (hu : IsSubharmonicByExtendedCircleAverageOn V u)
    (hboundary : ∀ x ∈ frontier V, u x ≤ M) :
    ∀ x ∈ V, u x ≤ M := by
  rcases hV_frontier_nonempty with ⟨b, hbfrontier⟩
  have hbclosure : b ∈ closure V := frontier_subset_closure hbfrontier
  rcases UpperSemicontinuousOn.exists_isMaxOn
      (f := u) (s := closure V) ⟨b, hbclosure⟩ hV_compact
      hu_upper_closure with
    ⟨c, hcclosure, hcmax_closure⟩
  have hc_mem : c ∈ V ∪ frontier V := by
    simpa [closure_eq_self_union_frontier] using hcclosure
  rcases hc_mem with hcV | hcfrontier
  · have hcmaxV : IsMaxOn u V c := by
      intro y hy
      exact hcmax_closure (subset_closure hy)
    have heqV : Set.EqOn u (fun _ ↦ u c) V :=
      subharmonicByExtendedCircleAverageOn_eqOn_of_isPreconnected_of_isMaxOn
        hV_open hV_preconnected hu hcV hcmaxV
    have huc_le_ub : u c ≤ u b :=
      upperSemicontinuousOn_constOn_le_of_mem_frontier
        hu_upper_closure heqV hbfrontier
    have huc_le_M : u c ≤ M :=
      huc_le_ub.trans (hboundary b hbfrontier)
    intro x hx
    exact (heqV hx).trans_le huc_le_M
  · have huc_le_M : u c ≤ M := hboundary c hcfrontier
    intro x hx
    exact (hcmax_closure (subset_closure hx)).trans huc_le_M

/--
%%handwave
name:
  Continuous majorants dominate the extended circle average
statement:
  If a continuous boundary function lies above an upper semicontinuous trace
  on a circle and below the chosen finite upper bound, then the extended
  circle average of the trace is at most the ordinary circle average of that
  continuous majorant.
proof:
  The boundary majorization gives a pointwise inequality of circle traces.
  Monotonicity of the extended circle average compares the original trace with
  the continuous one.  Since continuous boundary data is circle-integrable,
  [the extended average agrees with the ordinary circle
  average](lean:JJMath.Uniformization.upperCircleAverageERealWithBound_eq_real_circleAverage)
  for the majorant.
-/
theorem upperCircleAverageERealWithBound_le_circleAverage_of_continuous_majorant
    {u φ : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hM : CircleTraceUpperBound u c r M)
    (hφ_cont : ContinuousOn φ (frontier (Metric.ball c r)))
    (hφ_major : ∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z)
    (hφ_bound : ∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) :
    upperCircleAverageERealWithBound u c r M ≤
      ((Real.circleAverage φ c r : ℝ) : EReal) := by
  have hφM : CircleTraceUpperBound φ c r M := by
    intro θ _hθ
    exact hφ_bound (circleMap c r θ) (by
      rw [frontier_ball c hr.ne']
      exact circleMap_mem_sphere c hr.le θ)
  have huφ : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
      u (circleMap c r θ) ≤ φ (circleMap c r θ) := by
    intro θ _hθ
    exact hφ_major (circleMap c r θ) (by
      rw [frontier_ball c hr.ne']
      exact circleMap_mem_sphere c hr.le θ)
  have hφ_int : CircleIntegrable φ c r := by
    have hφ_sphere : ContinuousOn φ (Metric.sphere c r) := by
      rw [← frontier_ball c hr.ne']
      exact hφ_cont
    exact ContinuousOn.circleIntegrable hr.le hφ_sphere
  calc
    upperCircleAverageERealWithBound u c r M
        ≤ upperCircleAverageERealWithBound φ c r M :=
          upperCircleAverageERealWithBound_mono_of_bounds hM hφM huφ
    _ = ((Real.circleAverage φ c r : ℝ) : EReal) :=
          upperCircleAverageERealWithBound_eq_real_circleAverage hφM hφ_int

/--
%%handwave
name:
  Parametrized circle bounds hold on the boundary circle
statement:
  A finite upper bound for the trace along one full circle parametrization is
  an upper bound at every point of the boundary circle.
proof:
  The image of the interval \((0,2\pi]\) under the circle parametrization is
  exactly the sphere.  Since the boundary of a positive-radius ball is that
  sphere, every boundary point has such a parametrization.
-/
theorem CircleTraceUpperBound.le_on_frontier_ball
    {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hM : CircleTraceUpperBound u c r M) :
    ∀ z ∈ frontier (Metric.ball c r), u z ≤ M := by
  intro z hz
  have hz_sphere_abs : z ∈ Metric.sphere c |r| := by
    rw [abs_of_pos hr]
    simpa [frontier_ball c hr.ne'] using hz
  rw [← image_circleMap_Ioc c r] at hz_sphere_abs
  rcases hz_sphere_abs with ⟨θ, hθ, rfl⟩
  exact hM θ (by simpa [Set.uIoc_of_le Real.two_pi_pos.le] using hθ)

/--
%%handwave
name:
  Extended circle average is a lower bound for continuous majorant averages
statement:
  The extended circle average of an upper semicontinuous trace is a lower
  bound for all ordinary circle averages of continuous boundary functions
  lying above the trace and below the chosen finite upper bound.
proof:
  Apply [continuous majorants dominate the extended circle
  average](lean:JJMath.Uniformization.upperCircleAverageERealWithBound_le_circleAverage_of_continuous_majorant)
  to each member of the defining family, then use the universal lower-bound
  property of the infimum.
-/
theorem upperCircleAverageERealWithBound_le_sInf_continuous_majorants
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (_hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (_hclosed : Metric.closedBall c r ⊆ U)
    (hM : CircleTraceUpperBound u c r M) :
    upperCircleAverageERealWithBound u c r M ≤
      sInf {A : EReal | ∃ φ : ℂ → ℝ,
        ContinuousOn φ (frontier (Metric.ball c r)) ∧
        (∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z) ∧
        (∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) ∧
        A = ((Real.circleAverage φ c r : ℝ) : EReal)} := by
  refine le_sInf ?_
  intro A hA
  rcases hA with ⟨φ, hφ_cont, hφ_major, hφ_bound, rfl⟩
  exact upperCircleAverageERealWithBound_le_circleAverage_of_continuous_majorant
    hr hM hφ_cont hφ_major hφ_bound

/--
%%handwave
name:
  The subtracted circle trace is lower semicontinuous
statement:
  If \(u\) is upper semicontinuous on a neighborhood of the closed disc, then
  the parametrized function \(\theta \mapsto M-u(c+r e^{i\theta})\) is lower
  semicontinuous on one closed period of the circle.
proof:
  The circle parametrization maps the closed period into the closed disc.
  Composing with \(u\) preserves upper semicontinuity.  The map
  \(x\mapsto M-x\) is continuous and antitone, so composing with it turns
  upper semicontinuity into lower semicontinuity.
-/
theorem circleTraceSub_lowerSemicontinuousOn
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U) :
    LowerSemicontinuousOn
      (fun θ : ℝ ↦ M - u (circleMap c r θ))
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
  have hmaps :
      Set.MapsTo (circleMap c r) (Set.uIcc (0 : ℝ) (2 * Real.pi)) U := by
    intro θ _hθ
    exact hclosed (circleMap_mem_closedBall c hr.le θ)
  have htrace :
      UpperSemicontinuousOn
        (fun θ : ℝ ↦ u (circleMap c r θ))
        (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    simpa [Function.comp_def] using
      hu.comp ((continuous_circleMap c r).continuousOn) hmaps
  let g : ℝ → ℝ := fun x ↦ M - x
  have hg_cont : Continuous g := by
    fun_prop
  have hg_anti : Antitone g := by
    intro x y hxy
    exact sub_le_sub_left hxy M
  simpa [g, Function.comp_def] using
    hg_cont.comp_upperSemicontinuousOn_antitone htrace hg_anti

/--
%%handwave
name:
  The subtracted boundary trace is lower semicontinuous
statement:
  If \(u\) is upper semicontinuous on a neighborhood of the closed disc, then
  the boundary function \(z\mapsto M-u(z)\) is lower semicontinuous on the
  boundary circle.
proof:
  The boundary circle lies in the closed disc, hence in the domain where \(u\)
  is upper semicontinuous.  Composing \(u\) with the continuous antitone map
  \(x\mapsto M-x\) turns upper semicontinuity into lower semicontinuity.
-/
theorem circleTraceSub_lowerSemicontinuousOn_frontier
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U) :
    LowerSemicontinuousOn
      (fun z : ℂ ↦ M - u z)
      (frontier (Metric.ball c r)) := by
  have hfrontier_subset_U : frontier (Metric.ball c r) ⊆ U := by
    intro z hz
    have hz_closed : z ∈ Metric.closedBall c r := by
      have hz_closure : z ∈ closure (Metric.ball c r) :=
        frontier_subset_closure hz
      rwa [closure_ball c hr.ne'] at hz_closure
    exact hclosed hz_closed
  have htrace : UpperSemicontinuousOn u (frontier (Metric.ball c r)) :=
    hu.mono hfrontier_subset_U
  let g : ℝ → ℝ := fun x ↦ M - x
  have hg_cont : Continuous g := by
    fun_prop
  have hg_anti : Antitone g := by
    intro x y hxy
    exact sub_le_sub_left hxy M
  simpa [g, Function.comp_def] using
    hg_cont.comp_upperSemicontinuousOn_antitone htrace hg_anti

/--
%%handwave
name:
  The subtracted boundary trace is nonnegative
statement:
  If \(M\) bounds the circle trace of \(u\), then \(M-u\) is nonnegative on
  the boundary circle.
proof:
  The trace bound holds at every point of the boundary circle, so subtracting
  \(u\) from \(M\) gives a nonnegative value.
-/
theorem circleTraceSub_nonnegative_on_frontier
    {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hM : CircleTraceUpperBound u c r M) :
    ∀ z ∈ frontier (Metric.ball c r), 0 ≤ M - u z := by
  intro z hz
  exact sub_nonneg.mpr (CircleTraceUpperBound.le_on_frontier_ball hr hM z hz)

/--
%%handwave
name:
  Boundary circles are compact
statement:
  The boundary of a positive-radius Euclidean disc in the plane is compact.
proof:
  The boundary is the corresponding metric sphere, and metric spheres in the
  proper metric space \(\mathbb C\) are compact.
-/
theorem isCompact_frontier_ball
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsCompact (frontier (Metric.ball c r)) := by
  rw [frontier_ball c hr.ne']
  exact isCompact_sphere c r

/--
%%handwave
name:
  Continuous majorants exist below the infinite threshold
statement:
  For a finite upper bound \(M\), the constant boundary function \(M\) is a
  continuous majorant whose ordinary circle average is finite, hence below
  \(+\infty\).
proof:
  The constant function \(M\) is continuous, lies above the trace by the
  boundary form of the trace bound, and lies below \(M\) by equality.  Its
  average is a real number, so its coercion to the extended reals is strictly
  below \(+\infty\).
-/
theorem exists_continuous_majorant_circleAverage_lt_top
    {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hM : CircleTraceUpperBound u c r M) :
    ∃ φ : ℂ → ℝ,
      ContinuousOn φ (frontier (Metric.ball c r)) ∧
      (∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z) ∧
      (∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) ∧
      ((Real.circleAverage φ c r : ℝ) : EReal) < ⊤ := by
  refine ⟨fun _ : ℂ ↦ M, continuousOn_const, ?_, ?_, ?_⟩
  · exact CircleTraceUpperBound.le_on_frontier_ball hr hM
  · intro z _hz
    rfl
  · exact EReal.coe_lt_top (Real.circleAverage (fun _ : ℂ ↦ M) c r)

/--
%%handwave
name:
  A large minorant average gives a small subtracted average
statement:
  If the ordinary circle average of \(\psi\) is larger than \(M-b\), then the
  ordinary circle average of \(M-\psi\) is smaller than \(b\).
proof:
  Continuous boundary data is circle-integrable.  Linearity of the ordinary
  circle average gives
  \[
    \fint (M-\psi)=M-\fint\psi,
  \]
  and the conclusion is real arithmetic.
-/
theorem circleAverage_const_sub_lt_of_lt_circleAverage
    {ψ : ℂ → ℝ} {c : ℂ} {r M b : ℝ}
    (hr : 0 < r)
    (hψ_cont : ContinuousOn ψ (frontier (Metric.ball c r)))
    (hψ_avg : M - b < Real.circleAverage ψ c r) :
    Real.circleAverage (fun z : ℂ ↦ M - ψ z) c r < b := by
  have hψ_sphere : ContinuousOn ψ (Metric.sphere c r) := by
    rw [← frontier_ball c hr.ne']
    exact hψ_cont
  have hψ_int : CircleIntegrable ψ c r :=
    ContinuousOn.circleIntegrable hr.le hψ_sphere
  have hconst_int : CircleIntegrable (fun _ : ℂ ↦ M) c r :=
    circleIntegrable_const M c r
  calc
    Real.circleAverage (fun z : ℂ ↦ M - ψ z) c r
        = Real.circleAverage (fun _ : ℂ ↦ M) c r -
            Real.circleAverage ψ c r := by
          exact Real.circleAverage_fun_sub hconst_int hψ_int
    _ = M - Real.circleAverage ψ c r := by
          rw [Real.circleAverage_const]
    _ < b := by
          linarith

/--
%%handwave
name:
  Lower averages recover ordinary averages of nonnegative continuous traces
statement:
  For continuous nonnegative boundary data \(\psi\), the lower average of
  \(\psi\) along the circle parametrization agrees with the ordinary circle
  average of \(\psi\).
proof:
  The trace is integrable because the boundary data is continuous on the
  circle, and it is nonnegative by hypothesis.  The standard relation between
  the lower integral of `ofReal` and the Bochner integral of a nonnegative
  integrable function identifies the lower average with the ordinary average.
-/
theorem laverage_ofReal_circleTrace_eq_ofReal_circleAverage
    {ψ : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hψ_cont : ContinuousOn ψ (frontier (Metric.ball c r)))
    (hψ_nonneg : ∀ z ∈ frontier (Metric.ball c r), 0 ≤ ψ z) :
    MeasureTheory.laverage
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
      (fun θ : ℝ ↦ ENNReal.ofReal (ψ (circleMap c r θ))) =
        ENNReal.ofReal (Real.circleAverage ψ c r) := by
  let s : Set ℝ := Set.uIoc (0 : ℝ) (2 * Real.pi)
  let tr : ℝ → ℝ := fun θ ↦ ψ (circleMap c r θ)
  have hψ_sphere : ContinuousOn ψ (Metric.sphere c r) := by
    rw [← frontier_ball c hr.ne']
    exact hψ_cont
  have hψ_int : CircleIntegrable ψ c r :=
    ContinuousOn.circleIntegrable hr.le hψ_sphere
  have htr_int : MeasureTheory.IntegrableOn tr s := by
    simpa [tr, s, CircleIntegrable] using
      (intervalIntegrable_iff.mp hψ_int)
  have htr_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict s] tr := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume)
      measurableSet_uIoc] with θ _hθ
    exact hψ_nonneg (circleMap c r θ) (by
      rw [frontier_ball c hr.ne']
      exact circleMap_mem_sphere c hr.le θ)
  have havg_tr : (⨍ θ in s, tr θ) = Real.circleAverage ψ c r := by
    rw [Real.circleAverage_eq_intervalAverage]
  calc
    MeasureTheory.laverage
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
        (fun θ : ℝ ↦ ENNReal.ofReal (ψ (circleMap c r θ)))
        = MeasureTheory.laverage
            (MeasureTheory.volume.restrict s)
            (fun θ : ℝ ↦ ENNReal.ofReal (tr θ)) := rfl
    _ = ENNReal.ofReal (⨍ θ in s, tr θ) := by
          rw [MeasureTheory.laverage_eq, MeasureTheory.ofReal_setAverage htr_int htr_nonneg,
            MeasureTheory.Measure.restrict_apply_univ]
    _ = ENNReal.ofReal (Real.circleAverage ψ c r) := by
          rw [havg_tr]

/--
%%handwave
name:
  Continuous minorant averages lie below the lower average
statement:
  If \(\psi\) is a continuous nonnegative boundary function with
  \(\psi\leq M-u\) on the circle, then its ordinary circle average is at most
  the lower average of \(M-u\).
proof:
  The lower average of \(\psi\) is its ordinary circle average.  Monotonicity
  of the lower integral applies to the pointwise inequality
  \(\psi\leq M-u\) along the circle parametrization.
-/
theorem circleAverage_le_laverage_of_continuous_minorant
    {u ψ : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hψ_cont : ContinuousOn ψ (frontier (Metric.ball c r)))
    (hψ_nonneg : ∀ z ∈ frontier (Metric.ball c r), 0 ≤ ψ z)
    (hψ_le : ∀ z ∈ frontier (Metric.ball c r), ψ z ≤ M - u z) :
    ((Real.circleAverage (E := ℝ) ψ c r : ℝ) : EReal) ≤
      ((MeasureTheory.laverage
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
        (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))) : EReal) := by
  let μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))
  let Fψ : ℝ → ENNReal := fun θ ↦ ENNReal.ofReal (ψ (circleMap c r θ))
  let Fu : ℝ → ENNReal := fun θ ↦ ENNReal.ofReal (M - u (circleMap c r θ))
  have hψ_avg_nonneg : 0 ≤ Real.circleAverage ψ c r := by
    apply Real.circleAverage_nonneg_of_nonneg
    intro z hz
    have hz_frontier : z ∈ frontier (Metric.ball c r) := by
      rw [frontier_ball c hr.ne']
      simpa [abs_of_pos hr] using hz
    exact hψ_nonneg z hz_frontier
  have hlavgψ :
      MeasureTheory.laverage μ Fψ =
        ENNReal.ofReal (Real.circleAverage ψ c r) := by
    simpa [μ, Fψ] using
      laverage_ofReal_circleTrace_eq_ofReal_circleAverage
        (ψ := ψ) (c := c) (r := r) hr hψ_cont hψ_nonneg
  have hle_lavg : MeasureTheory.laverage μ Fψ ≤ MeasureTheory.laverage μ Fu := by
    rw [MeasureTheory.laverage_eq, MeasureTheory.laverage_eq]
    apply ENNReal.div_le_div_right
    apply MeasureTheory.lintegral_mono
    intro θ
    apply ENNReal.ofReal_le_ofReal
    exact hψ_le (circleMap c r θ) (by
      rw [frontier_ball c hr.ne']
      exact circleMap_mem_sphere c hr.le θ)
  calc
    ((Real.circleAverage (E := ℝ) ψ c r : ℝ) : EReal)
        = (ENNReal.ofReal (Real.circleAverage ψ c r) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left hψ_avg_nonneg]
    _ = (MeasureTheory.laverage μ Fψ : EReal) := by
          rw [hlavgψ]
    _ ≤ (MeasureTheory.laverage μ Fu : EReal) := by
          rw [EReal.coe_ennreal_le_coe_ennreal_iff]
          exact hle_lavg
    _ = ((MeasureTheory.laverage
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
        (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))) : EReal) := rfl

/--
%%handwave
name:
  Finite thresholds for extended circle averages
statement:
  The finite-threshold inequality
  \[
    M-\fint(M-u) < b
  \]
  is equivalent, in the extended-real sense, to
  \[
    M-b < \fint(M-u).
  \]
proof:
  This is the usual rearrangement of a finite subtraction inequality.  The
  only extended-real point is that the lower average may be \(+\infty\), which
  is allowed because the other terms are finite.
-/
theorem upperCircleAverageERealWithBound_lt_coe_iff
    {u : ℂ → ℝ} {c : ℂ} {r M b : ℝ} :
    upperCircleAverageERealWithBound u c r M < (b : EReal) ↔
      ((M - b : ℝ) : EReal) <
        ((MeasureTheory.laverage
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
          (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))) : EReal) := by
  let L : ENNReal :=
    MeasureTheory.laverage
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
      (fun θ : ℝ ↦ ENNReal.ofReal (M - u (circleMap c r θ)))
  change (M : EReal) - (L : EReal) < (b : EReal) ↔
    ((M - b : ℝ) : EReal) < (L : EReal)
  rw [EReal.coe_sub]
  rw [EReal.sub_lt_iff (a := (b : EReal)) (b := (L : EReal)) (c := (M : EReal))
      (.inl (EReal.coe_ennreal_ne_bot L)) (.inr (EReal.coe_ne_top M))]
  rw [EReal.sub_lt_iff (a := (L : EReal)) (b := (b : EReal)) (c := (M : EReal))
      (.inl (EReal.coe_ne_bot b)) (.inl (EReal.coe_ne_top b))]
  rw [add_comm]

/--
%%handwave
name:
  Upper semicontinuous functions are infima of countably many continuous majorants
statement:
  If an upper semicontinuous real-valued function on a compact metrizable set
  is given, then it is the pointwise infimum of a countable family of
  continuous majorants.
proof:
  First show that all continuous majorants have the original function as their
  pointwise infimum.  If \(b>u(x)\), choose \(a\) with \(u(x)<a<b\); the
  superlevel set \(\{u\ge a\}\) is closed, and Urysohn's lemma separates it
  from \(x\), producing a continuous majorant whose value at \(x\) is below
  \(b\).  Then apply the theorem saying that
  [a countable subfamily has the same lower
  envelope](lean:exists_countable_upperSemicontinuous_isGLB).

  References include Ransford, *Potential Theory in the Complex Plane*,
  Theorem 2.1.3, and Bourbaki, *General Topology*, Chapter IX, §1.
-/
theorem upperSemicontinuousOn_compact_exists_countable_continuous_majorants
    {K : Set ℂ} {u : ℂ → ℝ}
    (hK : IsCompact K)
    (hu : UpperSemicontinuousOn u K) :
    ∃ g : ℕ → ℂ → ℝ,
      (∀ n, ContinuousOn (g n) K) ∧
      (∀ n z, z ∈ K → u z ≤ g n z) ∧
      (∀ z ∈ K, u z = ⨅ n : ℕ, g n z) := by
  classical
  by_cases hK_nonempty : K.Nonempty
  · let U : K → ℝ := fun z ↦ u z
    have hU : UpperSemicontinuous U := by
      change UpperSemicontinuous (K.restrict u)
      rw [upperSemicontinuousOn_iff_restrict]
      exact hu
    rcases UpperSemicontinuousOn.bddAbove_of_isCompact hK hu with ⟨M, hM_image⟩
    have hM : ∀ z : K, U z ≤ M := by
      intro z
      exact hM_image (Set.mem_image_of_mem u z.2)
    have exists_continuous_majorant_lt :
        ∀ x : K, ∀ b : ℝ, U x < b →
          ∃ f : K → ℝ, Continuous f ∧ (∀ y : K, U y ≤ f y) ∧ f x < b := by
      intro x b hxb
      rcases exists_between hxb with ⟨a, hxa, hab⟩
      let A : Set K := {y | a ≤ U y}
      have hA_closed : IsClosed A := by
        simpa [A] using hU.isClosed_preimage a
      have hx_not_A : x ∉ A := by
        exact not_le_of_gt hxa
      have hdisj : Disjoint ({x} : Set K) A := by
        rw [Set.disjoint_left]
        intro y hyx hyA
        rw [Set.mem_singleton_iff] at hyx
        exact hx_not_A (hyx ▸ hyA)
      rcases exists_continuous_zero_one_of_isClosed
          (s := ({x} : Set K)) (t := A) isClosed_singleton hA_closed hdisj with
        ⟨q, hq_zero, hq_one, hq_mem⟩
      let B : ℝ := max M a
      let f : K → ℝ := fun y ↦ a + (B - a) * q y
      have hB_ge_M : M ≤ B := le_max_left M a
      have hB_ge_a : a ≤ B := le_max_right M a
      refine ⟨f, ?_, ?_, ?_⟩
      · simpa [f] using (continuous_const.add (continuous_const.mul q.continuous))
      · intro y
        by_cases hyA : y ∈ A
        · have hqy : q y = 1 := hq_one hyA
          calc
            U y ≤ M := hM y
            _ ≤ B := hB_ge_M
            _ = f y := by
              simp [f, hqy]
        · have hUy_le_a : U y ≤ a := le_of_not_ge hyA
          have hnonneg : 0 ≤ (B - a) * q y := by
            exact mul_nonneg (sub_nonneg.mpr hB_ge_a) (hq_mem y).1
          have ha_le_f : a ≤ f y := by
            simpa [f] using add_le_add_left hnonneg a
          exact hUy_le_a.trans ha_le_f
      · have hqx : q x = 0 := hq_zero (by simp)
        calc
          f x = a := by simp [f, hqx]
          _ < b := hab
    let 𝓕 : Set (K → ℝ) := {f | Continuous f ∧ ∀ z : K, U z ≤ f z}
    have h𝓕_cont : ∀ f ∈ 𝓕, UpperSemicontinuous f := by
      intro f hf
      exact hf.1.upperSemicontinuous
    have h𝓕_glb : IsGLB 𝓕 U := by
      rw [isGLB_pi]
      intro x
      refine ⟨?_, ?_⟩
      · rintro y ⟨f, hf, rfl⟩
        exact hf.2 x
      · intro b hb
        by_contra hnot
        have hxb : U x < b := lt_of_not_ge hnot
        rcases exists_continuous_majorant_lt x b hxb with
          ⟨f, hf_cont, hf_major, hfx_lt⟩
        have hf_mem : f ∈ 𝓕 := ⟨hf_cont, hf_major⟩
        exact not_lt_of_ge (hb (Set.mem_image_of_mem (fun f ↦ f x) hf_mem)) hfx_lt
    rcases exists_countable_upperSemicontinuous_isGLB
        (X := K) (E := ℝ) (s := U) (𝓕 := 𝓕) h𝓕_cont h𝓕_glb with
      ⟨𝓕', h𝓕'_sub, h𝓕'_count, h𝓕'_glb⟩
    have h𝓕'_nonempty : 𝓕'.Nonempty := by
      rcases hK_nonempty with ⟨z₀, hz₀⟩
      let x₀ : K := ⟨z₀, hz₀⟩
      have hpoint : IsGLB (Function.eval x₀ '' 𝓕') (U x₀) :=
        (isGLB_pi.mp h𝓕'_glb) x₀
      rcases hpoint.exists_between (by linarith : U x₀ < U x₀ + 1) with
        ⟨_, ⟨F₀, hF₀, rfl⟩, _hlo, _hhi⟩
      exact ⟨F₀, hF₀⟩
    rcases h𝓕'_nonempty with ⟨F₀, hF₀⟩
    let Fseq : ℕ → K → ℝ := Set.enumerateCountable h𝓕'_count F₀
    have hFseq_range : Set.range Fseq = 𝓕' :=
      Set.range_enumerateCountable_of_mem h𝓕'_count hF₀
    let g : ℕ → ℂ → ℝ := fun n z ↦ if hz : z ∈ K then Fseq n ⟨z, hz⟩ else 0
    refine ⟨g, ?_, ?_, ?_⟩
    · intro n
      have hFn : Fseq n ∈ 𝓕' := by
        rw [← hFseq_range]
        exact Set.mem_range_self n
      have hcont : Continuous (Fseq n) := (h𝓕'_sub hFn).1
      rw [continuousOn_iff_continuous_restrict]
      simpa [g, Set.restrict] using hcont
    · intro n z hz
      have hFn : Fseq n ∈ 𝓕' := by
        rw [← hFseq_range]
        exact Set.mem_range_self n
      have hmajor : ∀ x : K, U x ≤ Fseq n x := (h𝓕'_sub hFn).2
      simpa [g, U, hz] using hmajor ⟨z, hz⟩
    · intro z hz
      let x : K := ⟨z, hz⟩
      have hpoint : IsGLB (Function.eval x '' 𝓕') (U x) :=
        (isGLB_pi.mp h𝓕'_glb) x
      have hpoint_range : IsGLB (Set.range fun n : ℕ ↦ Fseq n x) (U x) := by
        rw [← hFseq_range, ← Set.range_comp'] at hpoint
        simpa [Function.comp_def] using hpoint
      simpa [g, U, hz, x] using hpoint_range.ciInf_eq.symm
  · refine ⟨fun _ _ ↦ 0, ?_, ?_, ?_⟩
    · intro n
      exact continuousOn_const
    · intro n z hz
      exact False.elim (hK_nonempty ⟨z, hz⟩)
    · intro z hz
      exact False.elim (hK_nonempty ⟨z, hz⟩)

/--
%%handwave
name:
  Upper semicontinuous functions are decreasing limits of continuous majorants
statement:
  If an upper semicontinuous real-valued function on a compact metrizable set
  is bounded above by \(M\), then it is the pointwise decreasing limit of
  continuous majorants that are also bounded above by \(M\).
proof:
  Start from the countable continuous majorants supplied by the classical
  theorem.  Truncate each majorant by \(M\), then take finite infima.  The
  resulting sequence is continuous, decreasing, still majorizes the original
  function, is bounded above by \(M\), and has the same pointwise infimum.
-/
theorem upperSemicontinuousOn_compact_exists_antitone_continuous_bounded_majorants
    {K : Set ℂ} {u : ℂ → ℝ} {M : ℝ}
    (hK : IsCompact K)
    (hu : UpperSemicontinuousOn u K)
    (hM : ∀ z ∈ K, u z ≤ M) :
    ∃ φ : ℕ → ℂ → ℝ,
      (∀ n, ContinuousOn (φ n) K) ∧
      (∀ n z, z ∈ K → u z ≤ φ n z) ∧
      (∀ n z, z ∈ K → φ n z ≤ M) ∧
      (∀ n z, z ∈ K → φ (n + 1) z ≤ φ n z) ∧
      (∀ z ∈ K, Filter.Tendsto (fun n : ℕ ↦ φ n z) Filter.atTop (𝓝 (u z))) := by
  by_cases hK_nonempty : K.Nonempty
  · rcases upperSemicontinuousOn_compact_exists_countable_continuous_majorants
      hK hu with ⟨g, hg_cont, hg_major, hg_inf⟩
    let gM : ℕ → ℂ → ℝ := fun n z ↦ min M (g n z)
    let φ : ℕ → ℂ → ℝ := fun n ↦
      (Finset.range (n + 1)).inf' (by simp) (fun k ↦ gM k)
    have hgM_cont : ∀ n, ContinuousOn (gM n) K := by
      intro n
      have h : ContinuousOn (fun z : ℂ ↦ (fun _ : ℂ ↦ M) z ⊓ g n z) K :=
        continuousOn_const.inf (hg_cont n)
      simpa [gM] using h
    have hgM_major : ∀ n z, z ∈ K → u z ≤ gM n z := by
      intro n z hz
      exact le_min (hM z hz) (hg_major n z hz)
    have hgM_bound : ∀ n z, z ∈ K → gM n z ≤ M := by
      intro n z _hz
      exact min_le_left M (g n z)
    have hφ_cont : ∀ n, ContinuousOn (φ n) K := by
      intro n
      simpa [φ] using
        (ContinuousOn.finset_inf'
          (s := Finset.range (n + 1)) (f := fun k z ↦ gM k z)
          (by simp) (fun k _hk ↦ hgM_cont k))
    have hφ_major : ∀ n z, z ∈ K → u z ≤ φ n z := by
      intro n z hz
      simpa [φ, Finset.inf'_apply] using
        (Finset.le_inf' (s := Finset.range (n + 1)) (by simp)
          (fun k ↦ gM k z) (a := u z)
          (fun k _hk ↦ hgM_major k z hz))
    have hφ_bound : ∀ n z, z ∈ K → φ n z ≤ M := by
      intro n z hz
      have h0 : 0 ∈ Finset.range (n + 1) := by simp
      have hle0 : φ n z ≤ gM 0 z := by
        simpa [φ, Finset.inf'_apply] using
          (Finset.inf'_le (s := Finset.range (n + 1))
            (fun k ↦ gM k z) h0)
      exact hle0.trans (hgM_bound 0 z hz)
    have hφ_mono : ∀ n z, z ∈ K → φ (n + 1) z ≤ φ n z := by
      intro n z _hz
      let s₁ := Finset.range (n + 1)
      let s₂ := Finset.range (n + 1 + 1)
      have hs₁ : s₁.Nonempty := by simp [s₁]
      have hs₂ : s₂.Nonempty := by simp [s₂]
      have hmono_raw :
          s₂.inf' hs₂ (fun k ↦ gM k z) ≤
            s₁.inf' hs₁ (fun k ↦ gM k z) := by
        refine Finset.le_inf' hs₁ (fun k ↦ gM k z) ?_
        intro k hk
        have hk' : k ∈ s₂ := by
          rw [Finset.mem_range] at hk ⊢
          exact Nat.lt_trans hk (Nat.lt_succ_self (n + 1))
        exact Finset.inf'_le (s := s₂) (fun k ↦ gM k z) hk'
      simpa [φ, s₁, s₂, Finset.inf'_apply, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hmono_raw
    have hφ_tendsto :
        ∀ z ∈ K, Filter.Tendsto (fun n : ℕ ↦ φ n z) Filter.atTop (𝓝 (u z)) := by
      intro z hz
      have hgM_iInf : (⨅ n : ℕ, gM n z) = u z := by
        apply le_antisymm
        · have hbdd_gM : BddBelow (Set.range fun n : ℕ ↦ gM n z) :=
            ⟨u z, by
              rintro _ ⟨n, rfl⟩
              exact hgM_major n z hz⟩
          calc
            (⨅ n : ℕ, gM n z) ≤ (⨅ n : ℕ, g n z) :=
              ciInf_mono hbdd_gM (fun n ↦ min_le_right M (g n z))
            _ = u z := (hg_inf z hz).symm
        · exact le_ciInf (fun n : ℕ ↦ hgM_major n z hz)
      have hφ_le_gM : ∀ n, φ n z ≤ gM n z := by
        intro n
        have hn : n ∈ Finset.range (n + 1) := by simp
        simpa [φ, Finset.inf'_apply] using
          (Finset.inf'_le (s := Finset.range (n + 1))
            (fun k ↦ gM k z) hn)
      have hbdd_φ : BddBelow (Set.range fun n : ℕ ↦ φ n z) :=
        ⟨u z, by
          rintro _ ⟨n, rfl⟩
          exact hφ_major n z hz⟩
      have hbdd_gM : BddBelow (Set.range fun n : ℕ ↦ gM n z) :=
        ⟨u z, by
          rintro _ ⟨n, rfl⟩
          exact hgM_major n z hz⟩
      have hInf_eq_gM :
          (⨅ n : ℕ, φ n z) = (⨅ n : ℕ, gM n z) := by
        apply le_antisymm
        · exact le_ciInf (fun n : ℕ ↦
            (ciInf_le hbdd_φ n).trans (hφ_le_gM n))
        · refine le_ciInf ?_
          intro n
          let s := Finset.range (n + 1)
          have hs : s.Nonempty := by simp [s]
          have hle_raw :
              (⨅ n : ℕ, gM n z) ≤ s.inf' hs (fun k ↦ gM k z) := by
            refine Finset.le_inf' hs (fun k ↦ gM k z) ?_
            intro k _hk
            exact ciInf_le hbdd_gM k
          simpa [φ, s, Finset.inf'_apply] using hle_raw
      have hanti : Antitone (fun n : ℕ ↦ φ n z) :=
        antitone_nat_of_succ_le (fun n ↦ hφ_mono n z hz)
      have htendsto :
          Filter.Tendsto (fun n : ℕ ↦ φ n z) Filter.atTop
            (𝓝 (⨅ n : ℕ, φ n z)) :=
        tendsto_atTop_ciInf hanti hbdd_φ
      simpa [hInf_eq_gM, hgM_iInf] using htendsto
    exact ⟨φ, hφ_cont, hφ_major, hφ_bound, hφ_mono, hφ_tendsto⟩
  · refine ⟨fun _ _ ↦ M, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact continuousOn_const
    · intro n z hz
      exact False.elim (hK_nonempty ⟨z, hz⟩)
    · intro n z hz
      rfl
    · intro n z hz
      rfl
    · intro z hz
      exact False.elim (hK_nonempty ⟨z, hz⟩)

/--
%%handwave
name:
  Decreasing continuous majorants converge in extended circle average
statement:
  If continuous majorants, all bounded above by \(M\), decrease pointwise on
  the boundary circle to \(u\), then their ordinary circle averages converge in
  the extended real line to the extended circle average of \(u\).
proof:
  Subtract the majorants from \(M\).  The resulting nonnegative continuous
  functions increase pointwise to \(M-u\).  For each approximant, the ordinary
  average is \(M\) minus the lower average of this nonnegative trace, and the
  monotone convergence theorem identifies the limit with
  \(M-\fint(M-u)\).
-/
theorem tendsto_circleAverage_of_antitone_continuous_bounded_majorants
    {u : ℂ → ℝ} {φ : ℕ → ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hφ_cont : ∀ n, ContinuousOn (φ n) (frontier (Metric.ball c r)))
    (hφ_major : ∀ n z, z ∈ frontier (Metric.ball c r) → u z ≤ φ n z)
    (hφ_bound : ∀ n z, z ∈ frontier (Metric.ball c r) → φ n z ≤ M)
    (hφ_mono : ∀ n z, z ∈ frontier (Metric.ball c r) → φ (n + 1) z ≤ φ n z)
    (hφ_tendsto : ∀ z ∈ frontier (Metric.ball c r),
      Filter.Tendsto (fun n : ℕ ↦ φ n z) Filter.atTop (𝓝 (u z))) :
    Filter.Tendsto
      (fun n : ℕ ↦ ((Real.circleAverage (φ n) c r : ℝ) : EReal))
      Filter.atTop
      (𝓝 (upperCircleAverageERealWithBound u c r M)) := by
  let s : Set ℝ := Set.uIoc (0 : ℝ) (2 * Real.pi)
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict s
  let F : ℕ → ℝ → ENNReal :=
    fun n θ ↦ ENNReal.ofReal (M - φ n (circleMap c r θ))
  let Flim : ℝ → ENNReal :=
    fun θ ↦ ENNReal.ofReal (M - u (circleMap c r θ))
  have hs_meas : MeasurableSet s := measurableSet_uIoc
  have hcircle_frontier : ∀ θ : ℝ, circleMap c r θ ∈ frontier (Metric.ball c r) := by
    intro θ
    rw [frontier_ball c hr.ne']
    exact circleMap_mem_sphere c hr.le θ
  have hF_meas : ∀ n, AEMeasurable (F n) μ := by
    intro n
    have htrace_cont :
        ContinuousOn (fun θ : ℝ ↦ φ n (circleMap c r θ)) s := by
      exact (hφ_cont n).comp ((continuous_circleMap c r).continuousOn)
        (fun θ _hθ ↦ hcircle_frontier θ)
    have htrace_ae :
        AEMeasurable (fun θ : ℝ ↦ φ n (circleMap c r θ))
          (MeasureTheory.volume.restrict s) :=
      htrace_cont.aemeasurable hs_meas
    simpa [F, μ] using (aemeasurable_const.sub htrace_ae).ennreal_ofReal
  have hF_mono : ∀ᵐ θ ∂μ, Monotone fun n : ℕ ↦ F n θ := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume) hs_meas] with θ _hθ
    refine monotone_nat_of_le_succ ?_
    intro n
    exact ENNReal.ofReal_le_ofReal
      (sub_le_sub_left
        (hφ_mono n (circleMap c r θ) (hcircle_frontier θ)) M)
  have hF_tendsto :
      ∀ᵐ θ ∂μ,
        Filter.Tendsto (fun n : ℕ ↦ F n θ) Filter.atTop (𝓝 (Flim θ)) := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume) hs_meas] with θ _hθ
    have _hu_le_M : u (circleMap c r θ) ≤ M :=
      (hφ_major 0 (circleMap c r θ) (hcircle_frontier θ)).trans
        (hφ_bound 0 (circleMap c r θ) (hcircle_frontier θ))
    exact ENNReal.tendsto_ofReal
      (tendsto_const_nhds.sub
        (hφ_tendsto (circleMap c r θ) (hcircle_frontier θ)))
  have hlintegral :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫⁻ θ, F n θ ∂μ)
        Filter.atTop
        (𝓝 (∫⁻ θ, Flim θ ∂μ)) :=
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
      hF_meas hF_mono hF_tendsto
  have hμ_ne_zero : μ Set.univ ≠ 0 := by
    simp [μ, s]
  have hlavg :
      Filter.Tendsto
        (fun n : ℕ ↦ MeasureTheory.laverage μ (F n))
        Filter.atTop
        (𝓝 (MeasureTheory.laverage μ Flim)) := by
    simpa [MeasureTheory.laverage_eq] using
      ENNReal.Tendsto.div_const
        (m := fun n : ℕ ↦ ∫⁻ θ, F n θ ∂μ)
        (a := ∫⁻ θ, Flim θ ∂μ)
        (b := μ Set.univ)
        hlintegral (Or.inr hμ_ne_zero)
  have hlavg_ereal :
      Filter.Tendsto
        (fun n : ℕ ↦ ((MeasureTheory.laverage μ (F n) : ENNReal) : EReal))
        Filter.atTop
        (𝓝 ((MeasureTheory.laverage μ Flim : ENNReal) : EReal)) :=
    EReal.tendsto_coe_ennreal.mpr hlavg
  have hshift :
      Filter.Tendsto
        (fun n : ℕ ↦
          (M : EReal) - ((MeasureTheory.laverage μ (F n) : ENNReal) : EReal))
        Filter.atTop
        (𝓝 ((M : EReal) - ((MeasureTheory.laverage μ Flim : ENNReal) : EReal))) := by
    rw [show
        (fun n : ℕ ↦
          (M : EReal) - ((MeasureTheory.laverage μ (F n) : ENNReal) : EReal)) =
        (fun n : ℕ ↦
          (M : EReal) + -((MeasureTheory.laverage μ (F n) : ENNReal) : EReal)) by
          ext n
          rw [sub_eq_add_neg]]
    rw [show
        (M : EReal) - ((MeasureTheory.laverage μ Flim : ENNReal) : EReal) =
        (M : EReal) + -((MeasureTheory.laverage μ Flim : ENNReal) : EReal) by
          rw [sub_eq_add_neg]]
    have hneg_lavg :
        Filter.Tendsto
          (fun n : ℕ ↦ -((MeasureTheory.laverage μ (F n) : ENNReal) : EReal))
          Filter.atTop
          (𝓝 (-((MeasureTheory.laverage μ Flim : ENNReal) : EReal))) :=
      (continuous_neg.tendsto
        ((MeasureTheory.laverage μ Flim : ENNReal) : EReal)).comp hlavg_ereal
    have hpair :
        Filter.Tendsto
          (fun n : ℕ ↦
            ((M : EReal), -((MeasureTheory.laverage μ (F n) : ENNReal) : EReal)))
          Filter.atTop
          (𝓝 ((M : EReal), -((MeasureTheory.laverage μ Flim : ENNReal) : EReal))) :=
      tendsto_const_nhds.prodMk_nhds hneg_lavg
    simpa using
      ((EReal.continuousAt_add
        (p := ((M : EReal), -((MeasureTheory.laverage μ Flim : ENNReal) : EReal)))
        (Or.inl (EReal.coe_ne_top M))
        (Or.inl (EReal.coe_ne_bot M))).tendsto.comp hpair)
  have hφM : ∀ n, CircleTraceUpperBound (φ n) c r M := by
    intro n θ _hθ
    exact hφ_bound n (circleMap c r θ) (hcircle_frontier θ)
  have hφ_int : ∀ n, CircleIntegrable (φ n) c r := by
    intro n
    have hφ_sphere : ContinuousOn (φ n) (Metric.sphere c r) := by
      rw [← frontier_ball c hr.ne']
      exact hφ_cont n
    exact ContinuousOn.circleIntegrable hr.le hφ_sphere
  have hsource :
      (fun n : ℕ ↦
          (M : EReal) - ((MeasureTheory.laverage μ (F n) : ENNReal) : EReal))
        =ᶠ[Filter.atTop]
      (fun n : ℕ ↦ ((Real.circleAverage (φ n) c r : ℝ) : EReal)) := by
    exact Filter.Eventually.of_forall fun n ↦ by
      calc
        (M : EReal) - ((MeasureTheory.laverage μ (F n) : ENNReal) : EReal)
            = upperCircleAverageERealWithBound (φ n) c r M := by
                rfl
        _ = ((Real.circleAverage (φ n) c r : ℝ) : EReal) :=
                upperCircleAverageERealWithBound_eq_real_circleAverage
                  (hφM n) (hφ_int n)
  simpa [upperCircleAverageERealWithBound, μ, s, Flim] using
    Filter.Tendsto.congr' hsource hshift

/--
%%handwave
name:
  Finite-threshold continuous majorant approximation
statement:
  If the extended circle average of an upper semicontinuous trace is strictly
  below a finite real threshold \(b\), then there is a continuous boundary
  majorant, still bounded above by \(M\), whose ordinary circle average is
  below \(b\).
proof:
  Approximate the original upper semicontinuous trace from above by a
  decreasing sequence of continuous majorants bounded above by \(M\).  Their
  ordinary circle averages converge to the extended circle average, so one of
  them lies below the prescribed finite threshold.
-/
theorem exists_continuous_majorant_circleAverage_lt_of_upperCircleAverage_lt_coe
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r M b : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U)
    (hM : CircleTraceUpperBound u c r M)
    (hB : upperCircleAverageERealWithBound u c r M < (b : EReal)) :
    ∃ φ : ℂ → ℝ,
      ContinuousOn φ (frontier (Metric.ball c r)) ∧
      (∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z) ∧
      (∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) ∧
      Real.circleAverage φ c r < b := by
  have hfrontier_subset_U : frontier (Metric.ball c r) ⊆ U := by
    intro z hz
    have hz_closed : z ∈ Metric.closedBall c r := by
      have hz_closure : z ∈ closure (Metric.ball c r) :=
        frontier_subset_closure hz
      rwa [closure_ball c hr.ne'] at hz_closure
    exact hclosed hz_closed
  have hu_frontier : UpperSemicontinuousOn u (frontier (Metric.ball c r)) :=
    hu.mono hfrontier_subset_U
  have hM_frontier : ∀ z ∈ frontier (Metric.ball c r), u z ≤ M :=
    CircleTraceUpperBound.le_on_frontier_ball hr hM
  rcases upperSemicontinuousOn_compact_exists_antitone_continuous_bounded_majorants
      (K := frontier (Metric.ball c r)) (u := u) (M := M)
      (isCompact_frontier_ball c hr) hu_frontier hM_frontier with
    ⟨φ, hφ_cont, hφ_major, hφ_bound, hφ_mono, hφ_tendsto⟩
  have havg_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ ((Real.circleAverage (φ n) c r : ℝ) : EReal))
        Filter.atTop
        (𝓝 (upperCircleAverageERealWithBound u c r M)) :=
    tendsto_circleAverage_of_antitone_continuous_bounded_majorants
      hr hφ_cont hφ_major hφ_bound hφ_mono hφ_tendsto
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        ((Real.circleAverage (φ n) c r : ℝ) : EReal) < (b : EReal) :=
    havg_tendsto.eventually (eventually_lt_nhds hB)
  rcases hevent.exists with ⟨n, hn⟩
  refine ⟨φ n, hφ_cont n, hφ_major n, hφ_bound n, ?_⟩
  exact EReal.coe_lt_coe_iff.mp hn

/--
%%handwave
name:
  Continuous majorants approximate extended circle averages from above
statement:
  If the extended circle average of an upper semicontinuous trace is strictly
  below a threshold, then there is a continuous boundary function lying above
  the trace and below the chosen finite upper bound whose ordinary circle
  average is still below that threshold.
proof:
  On the compact boundary circle,
  [upper semicontinuous functions are decreasing limits of continuous
  majorants](lean:JJMath.Uniformization.upperSemicontinuousOn_compact_exists_antitone_continuous_bounded_majorants).
  After imposing the upper bound \(M\),
  [their averages converge to the extended circle
  average](lean:JJMath.Uniformization.tendsto_circleAverage_of_antitone_continuous_bounded_majorants).
  A finite threshold below the limit is therefore eventually satisfied.
-/
theorem exists_continuous_majorant_circleAverage_lt_of_upperCircleAverage_lt
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U)
    (hM : CircleTraceUpperBound u c r M)
    {B : EReal}
    (hB : upperCircleAverageERealWithBound u c r M < B) :
    ∃ φ : ℂ → ℝ,
      ContinuousOn φ (frontier (Metric.ball c r)) ∧
      (∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z) ∧
      (∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) ∧
      ((Real.circleAverage φ c r : ℝ) : EReal) < B := by
  refine EReal.rec (motive := fun B ↦
    upperCircleAverageERealWithBound u c r M < B →
      ∃ φ : ℂ → ℝ,
        ContinuousOn φ (frontier (Metric.ball c r)) ∧
        (∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z) ∧
        (∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) ∧
        ((Real.circleAverage φ c r : ℝ) : EReal) < B) ?_ ?_ ?_ B hB
  · intro hbot
    exact (not_lt_bot hbot).elim
  · intro b hfinite
    rcases exists_continuous_majorant_circleAverage_lt_of_upperCircleAverage_lt_coe
        hu hr hclosed hM hfinite with
      ⟨φ, hφ_cont, hφ_major, hφ_bound, hφ_lt⟩
    exact ⟨φ, hφ_cont, hφ_major, hφ_bound, EReal.coe_lt_coe_iff.2 hφ_lt⟩
  · intro _htop
    exact exists_continuous_majorant_circleAverage_lt_top hr hM

/--
%%handwave
name:
  Continuous majorants attain the infimum bound
statement:
  For an upper semicontinuous function on a compactly contained circle, the
  infimum of the ordinary averages of continuous boundary majorants is at most
  the extended circle average computed from any finite upper bound.
proof:
  If the infimum were strictly above the extended average, then
  [a continuous majorant would have ordinary average below that
  infimum](lean:JJMath.Uniformization.exists_continuous_majorant_circleAverage_lt_of_upperCircleAverage_lt),
  contradicting the defining lower-bound property of the infimum.
-/
theorem sInf_continuous_majorants_le_upperCircleAverageERealWithBound
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U)
    (hM : CircleTraceUpperBound u c r M) :
    sInf {A : EReal | ∃ φ : ℂ → ℝ,
        ContinuousOn φ (frontier (Metric.ball c r)) ∧
        (∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z) ∧
        (∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) ∧
        A = ((Real.circleAverage φ c r : ℝ) : EReal)} ≤
      upperCircleAverageERealWithBound u c r M := by
  let S : Set EReal := {A : EReal | ∃ φ : ℂ → ℝ,
    ContinuousOn φ (frontier (Metric.ball c r)) ∧
    (∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z) ∧
    (∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) ∧
    A = ((Real.circleAverage φ c r : ℝ) : EReal)}
  change sInf S ≤ upperCircleAverageERealWithBound u c r M
  by_contra hnot
  have hlt : upperCircleAverageERealWithBound u c r M < sInf S :=
    lt_of_not_ge hnot
  rcases exists_continuous_majorant_circleAverage_lt_of_upperCircleAverage_lt
      hu hr hclosed hM hlt with
    ⟨φ, hφ_cont, hφ_major, hφ_bound, hφ_lt⟩
  have hA : ((Real.circleAverage φ c r : ℝ) : EReal) ∈ S := by
    exact ⟨φ, hφ_cont, hφ_major, hφ_bound, rfl⟩
  exact not_lt_of_ge (sInf_le hA) hφ_lt

/--
%%handwave
name:
  Upper semicontinuous traces are continuous-majorant envelopes
statement:
  For an upper semicontinuous function on a compactly contained circle, the
  extended circle average computed from a finite upper bound is the infimum of
  the ordinary circle averages of continuous boundary functions lying between
  the trace and that upper bound.
proof:
  One inequality follows because the extended circle average is a lower bound
  for every continuous majorant average.  For the reverse inequality,
  [a continuous majorant can be chosen below every strict finite
  threshold](lean:JJMath.Uniformization.exists_continuous_majorant_circleAverage_lt_of_upperCircleAverage_lt),
  and the \(+\infty\) threshold is handled by the constant majorant.
-/
theorem upperCircleAverageERealWithBound_eq_sInf_continuous_majorants
    {U : Set ℂ} {u : ℂ → ℝ} {c : ℂ} {r M : ℝ}
    (hu : UpperSemicontinuousOn u U)
    (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U)
    (hM : CircleTraceUpperBound u c r M) :
    upperCircleAverageERealWithBound u c r M =
      sInf {A : EReal | ∃ φ : ℂ → ℝ,
        ContinuousOn φ (frontier (Metric.ball c r)) ∧
        (∀ z ∈ frontier (Metric.ball c r), u z ≤ φ z) ∧
        (∀ z ∈ frontier (Metric.ball c r), φ z ≤ M) ∧
        A = ((Real.circleAverage φ c r : ℝ) : EReal)} := by
  exact le_antisymm
    (upperCircleAverageERealWithBound_le_sInf_continuous_majorants
      hu hr hclosed hM)
    (sInf_continuous_majorants_le_upperCircleAverageERealWithBound
      hu hr hclosed hM)

/--
%%handwave
name:
  Comparison subharmonic functions satisfy the extended circle-mean inequality
statement:
  A harmonic-comparison subharmonic function on an open plane domain satisfies
  the extended circle-mean inequality on every compactly contained circle.
proof:
  Approximate the upper semicontinuous trace from above by continuous boundary
  functions on the circle.  Solve the harmonic Dirichlet problem on the disc
  for those boundary functions.  Comparison gives the center inequality for
  each harmonic extension, the harmonic mean-value theorem rewrites the center
  as the circle average of the boundary data, and monotone convergence of
  \(M-h_n\) gives the extended average of the original trace.
-/
theorem planeComparisonSubharmonic_le_upperCircleAverageERealWithBound
    {U : Set ℂ} {u : ℂ → ℝ} (_hU_open : IsOpen U)
    (hu : IsSubharmonicByPlaneComparisonOn U u)
    {c : ℂ} {r M : ℝ}
    (_hcU : c ∈ U) (hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U)
    (hM : CircleTraceUpperBound u c r M) :
    (u c : EReal) ≤ upperCircleAverageERealWithBound u c r M := by
  rw [upperCircleAverageERealWithBound_eq_sInf_continuous_majorants
    hu.1 hr hclosed hM]
  refine le_sInf ?_
  intro A hA
  rcases hA with ⟨φ, hφ_cont, hφ_major, _hφ_bound, rfl⟩
  have hc_ball : c ∈ Metric.ball c r := by
    simpa [Metric.mem_ball] using hr
  have hV_subset : Metric.ball c r ⊆ U := by
    exact Metric.ball_subset_closedBall.trans hclosed
  have hfrontier_nonempty : (frontier (Metric.ball c r)).Nonempty := by
    rw [frontier_ball c hr.ne']
    exact NormedSpace.sphere_nonempty.mpr hr.le
  have hclosure_compact : IsCompact (closure (Metric.ball c r)) := by
    rw [closure_ball c hr.ne']
    exact isCompact_closedBall c r
  have hclosure_subset : closure (Metric.ball c r) ⊆ U := by
    rw [closure_ball c hr.ne']
    exact hclosed
  let h : ℂ → ℝ := poissonDiskDirichletCandidate c r φ
  have hharmonic :
      InnerProductSpace.HarmonicOnNhd h (Metric.ball c r) :=
    poissonDiskDirichletCandidate_harmonicOn c hr φ hφ_cont
  have hcontinuous : ContinuousOn h (closure (Metric.ball c r)) :=
    poissonDiskDirichletCandidate_continuousOn_closedBall c hr φ hφ_cont
  have hboundary : ∀ z ∈ frontier (Metric.ball c r), u z ≤ h z := by
    intro z hz
    change u z ≤ poissonDiskDirichletCandidate c r φ z
    rw [poissonDiskDirichletCandidate_boundary_eq c r φ z hz]
    exact hφ_major z hz
  have huc_le_hc : u c ≤ h c :=
    hu.2 (Metric.ball c r) Metric.isOpen_ball Metric.isPreconnected_ball
      hfrontier_nonempty hV_subset hclosure_compact hclosure_subset
      h hharmonic hcontinuous hboundary c hc_ball
  have hcenter :
      h c = Real.circleAverage φ c r := by
    exact poissonDiskDirichletCandidate_center_eq_circleAverage c hr φ
  exact EReal.coe_le_coe_iff.mpr (by simpa [hcenter] using huc_le_hc)

/--
%%handwave
name:
  Comparison subharmonicity gives extended circle means
statement:
  On an open plane domain, harmonic-comparison subharmonicity implies the
  extended circle-mean inequality on every compactly contained circle.
proof:
  Upper semicontinuity supplies a finite upper bound for every compactly
  contained circle, and
  [comparison gives the extended circle-mean
  inequality](lean:JJMath.Uniformization.planeComparisonSubharmonic_le_upperCircleAverageERealWithBound)
  for any such bound.
-/
theorem subharmonicByPlaneComparisonOn_to_extendedCircleAverageOn
    {U : Set ℂ} {u : ℂ → ℝ} (hU_open : IsOpen U) :
    IsSubharmonicByPlaneComparisonOn U u →
      IsSubharmonicByExtendedCircleAverageOn U u := by
  intro hu
  refine ⟨hu.1, ?_⟩
  intro c hcU r hr hclosed
  refine ⟨upperSemicontinuousOn_exists_circle_trace_upper_bound
    hu.1 hr hclosed, ?_⟩
  intro M hM
  exact planeComparisonSubharmonic_le_upperCircleAverageERealWithBound
    hU_open hu hcU hr hclosed hM

/--
%%handwave
name:
  Extended circle means give comparison subharmonicity
statement:
  On an open plane domain, extended circle-mean subharmonicity implies the
  harmonic comparison principle.
proof:
  Subtract a harmonic comparison function.  The extended circle-mean identity
  for harmonic functions and monotonicity of extended circle averages show
  that the difference still satisfies the extended circle-mean inequality.
  The circle-mean maximum principle then rules out a positive interior maximum
  when the boundary values are nonpositive.
-/
theorem subharmonicByExtendedCircleAverageOn_to_planeComparisonOn
    {U : Set ℂ} {u : ℂ → ℝ} (_hU_open : IsOpen U) :
    IsSubharmonicByExtendedCircleAverageOn U u →
      IsSubharmonicByPlaneComparisonOn U u := by
  intro hu
  refine ⟨hu.1, ?_⟩
  intro V hV_open hV_preconnected hV_frontier_nonempty hVU hV_compact
    hV_closure h hharmonic hcontinuous hboundary x hxV
  have huV : IsSubharmonicByExtendedCircleAverageOn V u :=
    subharmonicByExtendedCircleAverageOn_mono hVU hu
  have hdiff_circle :
      IsSubharmonicByExtendedCircleAverageOn V (fun z ↦ u z - h z) :=
    subharmonicByExtendedCircleAverageOn_sub_harmonic huV hharmonic
  have hdiff_upper_closure :
      UpperSemicontinuousOn (fun z ↦ u z - h z) (closure V) := by
    have hu_upper_closure : UpperSemicontinuousOn u (closure V) :=
      hu.1.mono hV_closure
    have hneg_upper : UpperSemicontinuousOn (fun z ↦ -h z) (closure V) :=
      hcontinuous.neg.upperSemicontinuousOn
    simpa [sub_eq_add_neg] using hu_upper_closure.add hneg_upper
  have hdiff_boundary : ∀ y ∈ frontier V, u y - h y ≤ 0 := by
    intro y hy
    linarith [hboundary y hy]
  have hdiff_nonpositive : ∀ y ∈ V, u y - h y ≤ 0 :=
    subharmonicByExtendedCircleAverageOn_le_constant_of_boundary_le
      hV_open hV_preconnected hV_frontier_nonempty hV_compact
      hdiff_upper_closure hdiff_circle hdiff_boundary
  linarith [hdiff_nonpositive x hxV]

/--
%%handwave
name:
  Extended circle means and comparison are equivalent
statement:
  On an open plane domain, extended circle-mean subharmonicity and
  harmonic-comparison subharmonicity are equivalent.
proof:
  This combines the two directions:
  [comparison gives extended circle
  means](lean:JJMath.Uniformization.subharmonicByPlaneComparisonOn_to_extendedCircleAverageOn)
  and [extended circle means give
  comparison](lean:JJMath.Uniformization.subharmonicByExtendedCircleAverageOn_to_planeComparisonOn).
-/
theorem subharmonicByPlaneComparisonOn_iff_extendedCircleAverageOn
    {U : Set ℂ} {u : ℂ → ℝ} (hU_open : IsOpen U) :
    IsSubharmonicByPlaneComparisonOn U u ↔
      IsSubharmonicByExtendedCircleAverageOn U u :=
  ⟨subharmonicByPlaneComparisonOn_to_extendedCircleAverageOn hU_open,
    subharmonicByExtendedCircleAverageOn_to_planeComparisonOn hU_open⟩

/--
%%handwave
name:
  Sums preserve plane comparison subharmonicity
statement:
  The sum of two comparison-subharmonic functions on the same open plane
  domain is comparison-subharmonic.
proof:
  By
  [extended circle means and comparison are
  equivalent](lean:JJMath.Uniformization.subharmonicByPlaneComparisonOn_iff_extendedCircleAverageOn),
  it suffices to prove the statement for extended circle means, where it
  follows from
  [additivity of extended circle
  averages](lean:JJMath.Uniformization.subharmonicByExtendedCircleAverageOn_add).
-/
theorem subharmonicByPlaneComparisonOn_add
    {U : Set ℂ} {u v : ℂ → ℝ} (hU_open : IsOpen U)
    (hu : IsSubharmonicByPlaneComparisonOn U u)
    (hv : IsSubharmonicByPlaneComparisonOn U v) :
    IsSubharmonicByPlaneComparisonOn U (fun z ↦ u z + v z) := by
  have hu_circle :
      IsSubharmonicByExtendedCircleAverageOn U u :=
    (subharmonicByPlaneComparisonOn_iff_extendedCircleAverageOn hU_open).1 hu
  have hv_circle :
      IsSubharmonicByExtendedCircleAverageOn U v :=
    (subharmonicByPlaneComparisonOn_iff_extendedCircleAverageOn hU_open).1 hv
  exact (subharmonicByPlaneComparisonOn_iff_extendedCircleAverageOn hU_open).2
    (subharmonicByExtendedCircleAverageOn_add hu_circle hv_circle)

/--
%%handwave
name:
  Subharmonicity respects equality on the region
statement:
  If two functions agree on a surface region, then subharmonicity of one on
  that region is equivalent to subharmonicity of the other there.
proof:
  Upper semicontinuity is checked with the relative neighborhood filter, so
  equality on the region transports it directly.  In the comparison
  principle, every test region and its frontier lie in the given region, so
  the same pointwise equality transfers both the boundary hypothesis and the
  interior conclusion.
-/
theorem subharmonicOnSurface_congr_on
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u v : X → ℝ}
    (hu : IsSubharmonicOnSurface U u)
    (huv : Set.EqOn u v U) :
    IsSubharmonicOnSurface U v := by
  refine ⟨?_, ?_⟩
  · rw [upperSemicontinuousOn_iff]
    intro x hxU
    have hux : UpperSemicontinuousWithinAt u U x :=
      hu.1.upperSemicontinuousWithinAt hxU
    rw [upperSemicontinuousWithinAt_iff] at hux ⊢
    intro a hva
    have hua : u x < a := by
      simpa [huv hxU] using hva
    filter_upwards [hux a hua, self_mem_nhdsWithin] with y hylt hyU
    simpa [huv hyU] using hylt
  · intro W hW_open hW_preconnected hW_frontier_nonempty hWU hW_compact
      hW_closure h hharmonic hcontinuous hboundary x hxW
    have hboundary_u : ∀ y ∈ frontier W, u y ≤ h y := by
      intro y hy
      rw [huv (hW_closure (frontier_subset_closure hy))]
      exact hboundary y hy
    have hu_le : u x ≤ h x :=
      hu.2 W hW_open hW_preconnected hW_frontier_nonempty hWU
        hW_compact hW_closure h hharmonic hcontinuous hboundary_u x hxW
    simpa [huv (hWU hxW)] using hu_le

/--
%%handwave
name:
  Surface subharmonicity in a chart
statement:
  A surface-subharmonic function becomes a comparison-subharmonic function
  after precomposition with the inverse of any complex coordinate chart.
proof:
  Upper semicontinuity is preserved by the inverse chart.  For comparison,
  map a Euclidean test region back through the chart.  The image relation for
  open partial homeomorphisms transports openness, connectedness, compact
  closure, and frontier points.  A Euclidean harmonic comparison function
  pulls back to a surface harmonic comparison function because transition maps
  between complex charts are analytic.
-/
theorem subharmonicOnSurface_to_planeComparisonOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ}
    (hu : IsSubharmonicOnSurface U u)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    IsSubharmonicByPlaneComparisonOn
      (e.target ∩ e.symm ⁻¹' U) (fun z : ℂ ↦ u (e.symm z)) := by
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hS_target : S ⊆ e.target := fun z hz ↦ hz.1
  refine ⟨?_, ?_⟩
  · have hmaps : Set.MapsTo e.symm S U := fun z hz ↦ hz.2
    simpa [S, Function.comp_def] using
      hu.1.comp (e.continuousOn_symm.mono hS_target) hmaps
  · intro V hV_open hV_preconnected hV_frontier_nonempty hVS hV_compact
      hV_closure h h_harmonic h_continuous hboundary z hzV
    let W : Set X := e.source ∩ e ⁻¹' V
    have hW_subset_source : W ⊆ e.source := fun x hx ↦ hx.1
    have himage : e.IsImage W V := by
      intro x hxsource
      simp [W, hxsource]
    have hV_subset_target : V ⊆ e.target := fun y hy ↦ (hVS hy).1
    have hW_open : IsOpen W := by
      simpa [W] using e.isOpen_inter_preimage hV_open
    have hW_eq_symm_image : W = e.symm '' V := by
      have hsymm := himage.symm_image_eq
      have htarget_inter : e.target ∩ V = V :=
        Set.inter_eq_right.mpr hV_subset_target
      have hsource_inter : e.source ∩ W = W :=
        Set.inter_eq_right.mpr hW_subset_source
      rw [htarget_inter, hsource_inter] at hsymm
      exact hsymm.symm
    have hW_preconnected : IsPreconnected W := by
      rw [hW_eq_symm_image]
      exact hV_preconnected.image e.symm
        (e.continuousOn_symm.mono hV_subset_target)
    have hclosureV_subset_target : closure V ⊆ e.target :=
      fun y hy ↦ (hV_closure hy).1
    let K : Set X := e.symm '' closure V
    have hK_compact : IsCompact K :=
      hV_compact.image_of_continuousOn
        (e.continuousOn_symm.mono hclosureV_subset_target)
    have hK_subset_source : K ⊆ e.source := by
      rintro x ⟨y, hy, rfl⟩
      exact e.map_target (hclosureV_subset_target hy)
    have hW_subset_K : W ⊆ K := by
      intro x hxW
      refine ⟨e x, subset_closure hxW.2, ?_⟩
      exact e.left_inv hxW.1
    have hclosureW_subset_K : closure W ⊆ K :=
      closure_minimal hW_subset_K hK_compact.isClosed
    have hW_compact : IsCompact (closure W) :=
      hK_compact.of_isClosed_subset isClosed_closure hclosureW_subset_K
    have hclosureW_subset_source : closure W ⊆ e.source :=
      hclosureW_subset_K.trans hK_subset_source
    have hclosure_maps : Set.MapsTo e (closure W) (closure V) := by
      intro x hx
      exact (himage.closure.apply_mem_iff (hclosureW_subset_source hx)).2 hx
    have hW_subset_U : W ⊆ U := by
      intro x hxW
      have hxS : e x ∈ S := hVS hxW.2
      simpa [e.left_inv hxW.1] using hxS.2
    have hclosureW_subset_U : closure W ⊆ U := by
      intro x hx
      have hxS : e x ∈ S := hV_closure (hclosure_maps hx)
      simpa [e.left_inv (hclosureW_subset_source hx)] using hxS.2
    have hW_frontier_nonempty : (frontier W).Nonempty := by
      rcases hV_frontier_nonempty with ⟨y, hy⟩
      have hytarget : y ∈ e.target :=
        hclosureV_subset_target (frontier_subset_closure hy)
      exact ⟨e.symm y, (himage.frontier.symm_apply_mem_iff hytarget).2 hy⟩
    let H : X → ℝ := fun x ↦ h (e x)
    have hH_harmonic : IsHarmonicOnSurface W H := by
      intro f hf y hy
      have hytarget : y ∈ f.target := hy.1
      have hysymmW : f.symm y ∈ W := hy.2
      have hysymm_source : f.symm y ∈ e.source := hW_subset_source hysymmW
      have heyV : e (f.symm y) ∈ V :=
        (himage.apply_mem_iff hysymm_source).2 hysymmW
      have hh_at : InnerProductSpace.HarmonicAt h (e (f.symm y)) :=
        h_harmonic (e (f.symm y)) heyV
      have htransition :
          AnalyticAt ℂ (fun w : ℂ ↦ e (f.symm w)) y :=
        chartTransition_analyticAt f hf e he hytarget hysymm_source
      simpa [H, Function.comp_def] using
        harmonicAt_comp_analyticAt hh_at htransition
    have hH_continuous : ContinuousOn H (closure W) :=
      h_continuous.comp (e.continuousOn.mono hclosureW_subset_source)
        hclosure_maps
    have hboundaryW : ∀ x ∈ frontier W, u x ≤ H x := by
      intro x hx
      have hxsource : x ∈ e.source :=
        hclosureW_subset_source (frontier_subset_closure hx)
      have hex_frontier : e x ∈ frontier V :=
        (himage.frontier.apply_mem_iff hxsource).2 hx
      have hbound := hboundary (e x) hex_frontier
      simpa [H, e.left_inv hxsource] using hbound
    have hz_target : z ∈ e.target := hV_subset_target hzV
    have hzW : e.symm z ∈ W := by
      refine ⟨e.map_target hz_target, ?_⟩
      simpa [e.right_inv hz_target] using hzV
    have hle : u (e.symm z) ≤ H (e.symm z) :=
      hu.2 W hW_open hW_preconnected hW_frontier_nonempty hW_subset_U
        hW_compact hclosureW_subset_U H hH_harmonic hH_continuous
        hboundaryW (e.symm z) hzW
    simpa [H, e.right_inv hz_target] using hle

/--
%%handwave
name:
  Plane comparison subharmonicity transports to a chart
statement:
  A comparison-subharmonic function on a plane region contained in a chart
  target pulls back to a surface-subharmonic function on the corresponding
  chart preimage.
proof:
  This is the reverse chart-transfer argument.  Surface test regions are
  pushed forward to Euclidean test regions by the chart.  The defining chart
  itself turns surface harmonic comparison functions into Euclidean harmonic
  comparison functions.
-/
theorem planeComparisonOn_to_subharmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {S : Set ℂ} {f : ℂ → ℝ}
    (hf : IsSubharmonicByPlaneComparisonOn S f) :
    IsSubharmonicOnSurface (e.source ∩ e ⁻¹' S) (fun x : X ↦ f (e x)) := by
  let U : Set X := e.source ∩ e ⁻¹' S
  have hU_source : U ⊆ e.source := fun x hx ↦ hx.1
  refine ⟨?_, ?_⟩
  · have hmaps : Set.MapsTo e U S := fun x hx ↦ hx.2
    simpa [U, Function.comp_def] using
      hf.1.comp (e.continuousOn.mono hU_source) hmaps
  · intro W hW_open hW_preconnected hW_frontier_nonempty hWU hW_compact
      hW_closure h h_harmonic h_continuous hboundary x hxW
    let V : Set ℂ := e.target ∩ e.symm ⁻¹' W
    have hW_subset_source : W ⊆ e.source := fun y hy ↦ (hWU hy).1
    have himage : e.IsImage W V := by
      intro y hysource
      constructor
      · intro hyV
        simpa [e.left_inv hysource] using hyV.2
      · intro hyW
        exact ⟨e.map_source hysource, by simpa [e.left_inv hysource] using hyW⟩
    have hV_subset_target : V ⊆ e.target := fun z hz ↦ hz.1
    have hV_open : IsOpen V := by
      simpa [V] using e.isOpen_inter_preimage_symm hW_open
    have hV_eq_image : V = e '' W := by
      have himage_eq := himage.image_eq
      have hsource_inter : e.source ∩ W = W :=
        Set.inter_eq_right.mpr hW_subset_source
      have htarget_inter : e.target ∩ V = V :=
        Set.inter_eq_right.mpr hV_subset_target
      rw [hsource_inter, htarget_inter] at himage_eq
      exact himage_eq.symm
    have hV_preconnected : IsPreconnected V := by
      rw [hV_eq_image]
      exact hW_preconnected.image e (e.continuousOn.mono hW_subset_source)
    have hclosureW_subset_source : closure W ⊆ e.source :=
      fun y hy ↦ (hW_closure hy).1
    let K : Set ℂ := e '' closure W
    have hK_compact : IsCompact K :=
      hW_compact.image_of_continuousOn
        (e.continuousOn.mono hclosureW_subset_source)
    have hK_subset_target : K ⊆ e.target := by
      rintro z ⟨y, hy, rfl⟩
      exact e.map_source (hclosureW_subset_source hy)
    have hV_subset_K : V ⊆ K := by
      intro z hzV
      refine ⟨e.symm z, subset_closure hzV.2, ?_⟩
      exact e.right_inv hzV.1
    have hclosureV_subset_K : closure V ⊆ K :=
      closure_minimal hV_subset_K hK_compact.isClosed
    have hV_compact : IsCompact (closure V) :=
      hK_compact.of_isClosed_subset isClosed_closure hclosureV_subset_K
    have hclosureV_subset_target : closure V ⊆ e.target :=
      hclosureV_subset_K.trans hK_subset_target
    have hclosure_maps : Set.MapsTo e.symm (closure V) (closure W) := by
      intro z hz
      exact (himage.closure.symm_apply_mem_iff
        (hclosureV_subset_target hz)).2 hz
    have hV_subset_S : V ⊆ S := by
      intro z hzV
      have hxW : e.symm z ∈ W := hzV.2
      have hxU : e.symm z ∈ U := hWU hxW
      simpa [e.right_inv hzV.1] using hxU.2
    have hclosureV_subset_S : closure V ⊆ S := by
      intro z hz
      have hxW : e.symm z ∈ closure W := hclosure_maps hz
      have hxU : e.symm z ∈ U := hW_closure hxW
      simpa [e.right_inv (hclosureV_subset_target hz)] using hxU.2
    have hV_frontier_nonempty : (frontier V).Nonempty := by
      rcases hW_frontier_nonempty with ⟨y, hy⟩
      have hysource : y ∈ e.source :=
        hclosureW_subset_source (frontier_subset_closure hy)
      exact ⟨e y, (himage.frontier.apply_mem_iff hysource).2 hy⟩
    let H : ℂ → ℝ := fun z ↦ h (e.symm z)
    have hH_harmonic : InnerProductSpace.HarmonicOnNhd H V := by
      simpa [H, V] using h_harmonic e he
    have hH_continuous : ContinuousOn H (closure V) :=
      h_continuous.comp (e.continuousOn_symm.mono hclosureV_subset_target)
        hclosure_maps
    have hboundaryV : ∀ z ∈ frontier V, f z ≤ H z := by
      intro z hz
      have hztarget : z ∈ e.target :=
        hclosureV_subset_target (frontier_subset_closure hz)
      have hsymm_frontier : e.symm z ∈ frontier W :=
        (himage.frontier.symm_apply_mem_iff hztarget).2 hz
      have hbound := hboundary (e.symm z) hsymm_frontier
      simpa [H, e.right_inv hztarget] using hbound
    have hxsource : x ∈ e.source := hW_subset_source hxW
    have hexV : e x ∈ V := by
      exact ⟨e.map_source hxsource, by simpa [e.left_inv hxsource] using hxW⟩
    have hle : f (e x) ≤ H (e x) :=
      hf.2 V hV_open hV_preconnected hV_frontier_nonempty hV_subset_S
        hV_compact hclosureV_subset_S H hH_harmonic hH_continuous
        hboundaryV (e x) hexV
    simpa [H, e.left_inv hxsource] using hle

/--
%%handwave
name:
  Subharmonicity restricts to smaller surface regions
statement:
  A subharmonic function on a surface region remains subharmonic on every
  smaller region.
proof:
  Restrict upper semicontinuity to the smaller region.  Every relatively
  compact harmonic-comparison domain contained in the smaller region is also
  contained in the original one, so the same boundary comparison proves the
  required interior comparison.
-/
theorem subharmonicOnSurface_mono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U V : Set X} {u : X → ℝ}
    (hVU : V ⊆ U)
    (hu : IsSubharmonicOnSurface U u) :
    IsSubharmonicOnSurface V u := by
  refine ⟨hu.1.mono hVU, ?_⟩
  intro W hW_open hW_preconnected hW_frontier_nonempty hWV hW_compact
    hW_closure h hharmonic hcontinuous hboundary x hxW
  exact hu.2 W hW_open hW_preconnected hW_frontier_nonempty
    (hWV.trans hVU) hW_compact (hW_closure.trans hVU)
    h hharmonic hcontinuous hboundary x hxW

/--
%%handwave
name:
  Constant functions are subharmonic on surface regions
statement:
  Constant real-valued functions are subharmonic on every surface region.
proof:
  Constants are upper semicontinuous, and the comparison principle follows
  from the minimum principle for harmonic functions applied to the test
  harmonic function minus the constant.
-/
theorem subharmonicOnSurface_const
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (U : Set X) (c : ℝ) :
    IsSubharmonicOnSurface U (fun _ : X ↦ c) := by
  refine ⟨upperSemicontinuousOn_const, ?_⟩
  intro V hV_open hV_preconnected hV_frontier_nonempty _hVU hV_compact
    _hV_closure h hharmonic hcontinuous hboundary x hxV
  have hdiff_harmonic : IsHarmonicOnSurface V (fun x ↦ c - h x) := by
    simpa using
      harmonicOnSurface_sub (harmonicOnSurface_const V c) hharmonic
  have hdiff_continuous : ContinuousOn (fun x ↦ c - h x) (closure V) :=
    continuousOn_const.sub hcontinuous
  have hdiff_boundary : ∀ x ∈ frontier V, c - h x ≤ 0 := by
    intro y hy
    linarith [hboundary y hy]
  have hdiff_nonpositive : ∀ x ∈ V, c - h x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive hV_open hV_preconnected
      hV_compact hV_frontier_nonempty
      hdiff_harmonic hdiff_continuous hdiff_boundary
  linarith [hdiff_nonpositive x hxV]

/--
%%handwave
name:
  Adding a constant preserves subharmonicity
statement:
  If a function is subharmonic on a surface region, then adding a real
  constant to it is subharmonic on the same region.
proof:
  Upper semicontinuity is preserved by adding a constant.  For comparison,
  subtract the same constant from the harmonic test function.
-/
theorem subharmonicOnSurface_const_add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} (c : ℝ)
    (hu : IsSubharmonicOnSurface U u) :
    IsSubharmonicOnSurface U (fun x ↦ c + u x) := by
  refine ⟨upperSemicontinuousOn_const.add hu.1, ?_⟩
  intro V hV_open hV_preconnected hV_frontier_nonempty hVU hV_compact
    hV_closure h hharmonic hcontinuous hboundary x hxV
  have hshift_harmonic : IsHarmonicOnSurface V (fun x ↦ h x - c) := by
    simpa using
      harmonicOnSurface_sub hharmonic (harmonicOnSurface_const V c)
  have hshift_continuous : ContinuousOn (fun x ↦ h x - c) (closure V) :=
    hcontinuous.sub continuousOn_const
  have hshift_boundary : ∀ y ∈ frontier V, u y ≤ h y - c := by
    intro y hy
    linarith [hboundary y hy]
  have hu_le : u x ≤ h x - c :=
    hu.2 V hV_open hV_preconnected hV_frontier_nonempty hVU
      hV_compact hV_closure (fun x ↦ h x - c) hshift_harmonic
      hshift_continuous hshift_boundary x hxV
  linarith

/--
%%handwave
name:
  Adding a constant on the right preserves subharmonicity
statement:
  If a function is subharmonic on a surface region, then adding a real
  constant on the right is subharmonic on the same region.
-/
theorem subharmonicOnSurface_add_const
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} (c : ℝ)
    (hu : IsSubharmonicOnSurface U u) :
    IsSubharmonicOnSurface U (fun x ↦ u x + c) := by
  simpa [add_comm] using subharmonicOnSurface_const_add c hu

/--
%%handwave
name:
  Subharmonic minus harmonic is subharmonic
statement:
  If \(u\) is subharmonic and \(h\) is harmonic on the same open surface
  region, then \(u-h\) is subharmonic.
proof:
  Upper semicontinuity follows by adding the continuous function \(-h\).  For
  comparison, if a harmonic function \(g\) bounds \(u-h\) on the boundary of a
  test region, then \(g+h\) is harmonic and bounds \(u\) on that boundary.
  Applying subharmonic comparison to \(u\) gives the desired interior
  inequality.
-/
theorem subharmonicOnSurface_sub_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u h : X → ℝ}
    (hU_open : IsOpen U)
    (hu : IsSubharmonicOnSurface U u)
    (hh : IsHarmonicOnSurface U h) :
    IsSubharmonicOnSurface U (fun x ↦ u x - h x) := by
  have hh_cont : ContinuousOn h U :=
    harmonicOnSurface_continuousOn hU_open hh
  refine ⟨?_, ?_⟩
  · have hneg_upper : UpperSemicontinuousOn (fun x ↦ -h x) U :=
      hh_cont.neg.upperSemicontinuousOn
    simpa [sub_eq_add_neg] using hu.1.add hneg_upper
  · intro V hV_open hV_preconnected hV_frontier_nonempty hVU hV_compact
      hV_closure g hg_harmonic hg_continuous hboundary x hxV
    have hh_V : IsHarmonicOnSurface V h :=
      harmonicOnSurface_mono hVU hh
    have hsum_harmonic : IsHarmonicOnSurface V (fun y ↦ g y + h y) :=
      harmonicOnSurface_add hg_harmonic hh_V
    have hsum_continuous : ContinuousOn (fun y ↦ g y + h y) (closure V) :=
      hg_continuous.add (hh_cont.mono hV_closure)
    have hsum_boundary : ∀ y ∈ frontier V, u y ≤ g y + h y := by
      intro y hy
      linarith [hboundary y hy]
    have hu_le : u x ≤ g x + h x :=
      hu.2 V hV_open hV_preconnected hV_frontier_nonempty hVU
        hV_compact hV_closure (fun y ↦ g y + h y) hsum_harmonic
        hsum_continuous hsum_boundary x hxV
    linarith

/--
%%handwave
name:
  Subharmonic plus harmonic is subharmonic
statement:
  If \(u\) is subharmonic and \(h\) is harmonic on the same open surface
  region, then \(u+h\) is subharmonic.
-/
theorem subharmonicOnSurface_add_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u h : X → ℝ}
    (hU_open : IsOpen U)
    (hu : IsSubharmonicOnSurface U u)
    (hh : IsHarmonicOnSurface U h) :
    IsSubharmonicOnSurface U (fun x ↦ u x + h x) := by
  have hneg : IsHarmonicOnSurface U (fun x ↦ -h x) :=
    harmonicOnSurface_neg hh
  simpa [sub_eq_add_neg] using
    subharmonicOnSurface_sub_harmonic hU_open hu hneg

/--
%%handwave
name:
  Harmonic functions are subharmonic
statement:
  A harmonic real-valued function on an open surface region is subharmonic on
  that region.
-/
theorem harmonicOnSurface_subharmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {h : X → ℝ}
    (hU_open : IsOpen U)
    (hh : IsHarmonicOnSurface U h) :
    IsSubharmonicOnSurface U h := by
  have hzero : IsSubharmonicOnSurface U (fun _ : X ↦ 0) :=
    subharmonicOnSurface_const U 0
  simpa using subharmonicOnSurface_add_harmonic hU_open hzero hh

private theorem subharmonicOnSurface_eventually_eq_of_isMaxOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ} (hU_open : IsOpen U)
    (hu : IsSubharmonicOnSurface U u)
    {x : X} (hxU : x ∈ U) (hxmax : IsMaxOn u U x) :
    ∀ᶠ y in 𝓝 x, u y = u x := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hxsource : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hU_open
  have hcoord_comp :
      IsSubharmonicByPlaneComparisonOn S (fun z : ℂ ↦ u (e.symm z)) := by
    simpa [S] using subharmonicOnSurface_to_planeComparisonOn hu e he
  have hcoord_circle :
      IsSubharmonicByExtendedCircleAverageOn S (fun z : ℂ ↦ u (e.symm z)) :=
    (subharmonicByPlaneComparisonOn_iff_extendedCircleAverageOn hS_open).1
      hcoord_comp
  have hexS : e x ∈ S := by
    exact ⟨e.map_source hxsource, by simpa [e.left_inv hxsource] using hxU⟩
  have hcoord_max :
      IsMaxOn (fun z : ℂ ↦ u (e.symm z)) S (e x) := by
    intro z hzS
    have hzU : e.symm z ∈ U := hzS.2
    have hle := hxmax hzU
    simpa [e.left_inv hxsource] using hle
  have hcoord_event :
      ∀ᶠ z in 𝓝 (e x), u (e.symm z) = u (e.symm (e x)) :=
    subharmonicByExtendedCircleAverageOn_eventually_eq_of_isMaxOn
      hS_open hcoord_circle hexS hcoord_max
  have hback :
      ∀ᶠ y in 𝓝 x, u (e.symm (e y)) = u (e.symm (e x)) :=
    e.continuousAt hxsource hcoord_event
  filter_upwards [hback, e.open_source.mem_nhds hxsource] with y hy hysource
  simpa [e.left_inv hysource, e.left_inv hxsource] using hy

private theorem upperSemicontinuousOn_of_locally_open_aux
    {X : Type} [TopologicalSpace X] {U : Set X} {u : X → ℝ}
    (hlocal : ∀ x ∈ U, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      UpperSemicontinuousOn u (U ∩ N)) :
    UpperSemicontinuousOn u U := by
  rw [upperSemicontinuousOn_iff]
  intro x hxU
  rcases hlocal x hxU with ⟨N, hN_open, hxN, hN_upper⟩
  have hwithin : UpperSemicontinuousWithinAt u (U ∩ N) x :=
    hN_upper.upperSemicontinuousWithinAt ⟨hxU, hxN⟩
  have hN_mem : N ∈ 𝓝[U] x :=
    nhdsWithin_le_nhds (hN_open.mem_nhds hxN)
  rw [upperSemicontinuousWithinAt_iff] at hwithin ⊢
  intro y hy
  simpa [nhdsWithin_inter_of_mem' hN_mem] using hwithin y hy

private theorem subharmonicComparisonPrinciple_of_locally_aux
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ}
    (_hU_open : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      IsSubharmonicOnSurface (U ∩ N) u) :
    ∀ V : Set X,
      IsOpen V →
        IsPreconnected V →
          (frontier V).Nonempty →
            V ⊆ U →
              IsCompact (closure V) →
                closure V ⊆ U →
                  ∀ h : X → ℝ,
                    IsHarmonicOnSurface V h →
                      ContinuousOn h (closure V) →
                        (∀ x ∈ frontier V, u x ≤ h x) →
                          ∀ x ∈ V, u x ≤ h x := by
  intro V hV_open hV_preconnected hV_frontier_nonempty hVU hV_compact
    hV_closure h hharmonic hcontinuous hboundary x hxV
  let w : X → ℝ := fun y ↦ u y - h y
  have hu_upper : UpperSemicontinuousOn u U :=
    upperSemicontinuousOn_of_locally_open_aux (fun y hy ↦ by
      rcases hlocal y hy with ⟨N, hN_open, hyN, hy_sub⟩
      exact ⟨N, hN_open, hyN, hy_sub.1⟩)
  have hw_upper_closure : UpperSemicontinuousOn w (closure V) := by
    have hu_closure : UpperSemicontinuousOn u (closure V) :=
      hu_upper.mono hV_closure
    have hneg_upper : UpperSemicontinuousOn (fun y ↦ -h y) (closure V) :=
      hcontinuous.neg.upperSemicontinuousOn
    simpa [w, sub_eq_add_neg] using hu_closure.add hneg_upper
  have hw_boundary : ∀ y ∈ frontier V, w y ≤ 0 := by
    intro y hy
    dsimp [w]
    linarith [hboundary y hy]
  by_contra hnot
  have hxlt : h x < u x := lt_of_not_ge hnot
  have hxw_pos : 0 < w x := by
    dsimp [w]
    linarith
  rcases UpperSemicontinuousOn.exists_isMaxOn
      (f := w) (s := closure V) ⟨x, subset_closure hxV⟩
      hV_compact hw_upper_closure with
    ⟨c, hc_closure, hcmax_closure⟩
  have hwc_pos : 0 < w c :=
    hxw_pos.trans_le (hcmax_closure (subset_closure hxV))
  have hc_mem : c ∈ V ∪ frontier V := by
    simpa [closure_eq_self_union_frontier] using hc_closure
  have hcV : c ∈ V := by
    rcases hc_mem with hcV | hcfrontier
    · exact hcV
    · have hcle0 : w c ≤ 0 := hw_boundary c hcfrontier
      exact False.elim (not_lt_of_ge hcle0 hwc_pos)
  let A : Set X := V ∩ {y | w y = w c}
  let B : Set X := V ∩ {y | w y < w c}
  have hA_open : IsOpen A := by
    refine isOpen_iff_mem_nhds.2 ?_
    intro y hyA
    have hyV : y ∈ V := hyA.1
    have hy_eq : w y = w c := hyA.2
    rcases hlocal y (hVU hyV) with ⟨N, hN_open, hyN, hy_sub⟩
    let L : Set X := V ∩ N
    have hL_open : IsOpen L := hV_open.inter hN_open
    have hL_sub_u : IsSubharmonicOnSurface L u := by
      refine subharmonicOnSurface_mono ?_ hy_sub
      intro z hz
      exact ⟨hVU hz.1, hz.2⟩
    have hh_L : IsHarmonicOnSurface L h :=
      harmonicOnSurface_mono (fun z hz ↦ hz.1) hharmonic
    have hw_sub : IsSubharmonicOnSurface L w := by
      simpa [w] using
        subharmonicOnSurface_sub_harmonic hL_open hL_sub_u hh_L
    have hyL : y ∈ L := ⟨hyV, hyN⟩
    have hymaxL : IsMaxOn w L y := by
      intro z hz
      have hle : w z ≤ w c := hcmax_closure (subset_closure hz.1)
      simpa [hy_eq] using hle
    have hevent :
        ∀ᶠ z in 𝓝 y, w z = w y :=
      subharmonicOnSurface_eventually_eq_of_isMaxOn hL_open hw_sub hyL hymaxL
    have heq_wc : {z : X | w z = w c} ∈ 𝓝 y := by
      filter_upwards [hevent] with z hz
      exact hz.trans hy_eq
    exact Filter.inter_mem (hV_open.mem_nhds hyV) heq_wc
  have hB_open : IsOpen B := by
    have hw_upper_V : UpperSemicontinuousOn w V :=
      hw_upper_closure.mono subset_closure
    rcases upperSemicontinuousOn_iff_preimage_Iio.mp hw_upper_V (w c) with
      ⟨O, hO_open, hO_eq⟩
    change IsOpen (V ∩ w ⁻¹' Set.Iio (w c))
    rw [hO_eq]
    exact hV_open.inter hO_open
  have hAB_disjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    exact hyB.2.ne hyA.2
  have hV_subset_AB : V ⊆ A ∪ B := by
    intro y hyV
    have hle : w y ≤ w c := hcmax_closure (subset_closure hyV)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inr ⟨hyV, hlt⟩
    · exact Or.inl ⟨hyV, heq⟩
  have hA_nonempty : (V ∩ A).Nonempty := ⟨c, hcV, hcV, rfl⟩
  have hV_subset_A : V ⊆ A :=
    hV_preconnected.subset_left_of_subset_union
      hA_open hB_open hAB_disjoint hV_subset_AB hA_nonempty
  rcases hV_frontier_nonempty with ⟨b, hbfrontier⟩
  have hconst : Set.EqOn w (fun _ ↦ w c) V := by
    intro y hy
    exact (hV_subset_A hy).2
  have hwc_le_wb : w c ≤ w b :=
    upperSemicontinuousOn_constOn_le_of_mem_frontier
      hw_upper_closure hconst hbfrontier
  have hwb_le : w b ≤ 0 := hw_boundary b hbfrontier
  exact not_lt_of_ge (hwc_le_wb.trans hwb_le) hwc_pos

private theorem subharmonicOnSurface_of_locally_aux
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      IsSubharmonicOnSurface (U ∩ N) u) :
    IsSubharmonicOnSurface U u := by
  refine ⟨?_, subharmonicComparisonPrinciple_of_locally_aux hU_open hlocal⟩
  exact upperSemicontinuousOn_of_locally_open_aux (fun x hx ↦ by
    rcases hlocal x hx with ⟨N, hN_open, hxN, hN_sub⟩
    exact ⟨N, hN_open, hxN, hN_sub.1⟩)

/--
%%handwave
name:
  Sums of subharmonic functions are subharmonic
statement:
  The sum of two subharmonic functions on the same open surface region is
  subharmonic.
proof:
  Work locally in a complex coordinate disc.  There,
  [extended circle means and comparison are
  equivalent](lean:JJMath.Uniformization.subharmonicByPlaneComparisonOn_iff_extendedCircleAverageOn).
  The circle-mean statement is closed under sums because
  [extended circle means are closed under
  sums](lean:JJMath.Uniformization.subharmonicByExtendedCircleAverageOn_add).
  Transport the resulting local comparison statement back through the
  coordinate chart and globalize by locality.
-/
theorem subharmonicOnSurface_add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u v : X → ℝ}
    (hU_open : IsOpen U)
    (hu : IsSubharmonicOnSurface U u)
    (hv : IsSubharmonicOnSurface U v) :
    IsSubharmonicOnSurface U (fun x ↦ u x + v x) := by
  refine subharmonicOnSurface_of_locally_aux hU_open ?_
  intro x hxU
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hxsource : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hU_open
  have hu_plane :
      IsSubharmonicByPlaneComparisonOn S (fun z : ℂ ↦ u (e.symm z)) := by
    simpa [S] using subharmonicOnSurface_to_planeComparisonOn hu e he
  have hv_plane :
      IsSubharmonicByPlaneComparisonOn S (fun z : ℂ ↦ v (e.symm z)) := by
    simpa [S] using subharmonicOnSurface_to_planeComparisonOn hv e he
  have hsum_plane :
      IsSubharmonicByPlaneComparisonOn S
        (fun z : ℂ ↦ u (e.symm z) + v (e.symm z)) :=
    subharmonicByPlaneComparisonOn_add hS_open hu_plane hv_plane
  let N : Set X := e.source
  refine ⟨N, e.open_source, hxsource, ?_⟩
  have hchart_sum :
      IsSubharmonicOnSurface (e.source ∩ e ⁻¹' S)
        (fun y : X ↦ u (e.symm (e y)) + v (e.symm (e y))) := by
    simpa [Function.comp_def] using
      planeComparisonOn_to_subharmonicOnSurface e he hsum_plane
  have hdomain_eq : U ∩ N = e.source ∩ e ⁻¹' S := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.2, e.map_source hy.2, by simpa [e.left_inv hy.2] using hy.1⟩
    · intro hy
      exact ⟨by simpa [e.left_inv hy.1] using hy.2.2, hy.1⟩
  have hchart_sum' :
      IsSubharmonicOnSurface (U ∩ N)
        (fun y : X ↦ u (e.symm (e y)) + v (e.symm (e y))) := by
    simpa [hdomain_eq] using hchart_sum
  refine subharmonicOnSurface_congr_on hchart_sum' ?_
  intro y hy
  have hysource : y ∈ e.source := hy.2
  simp [e.left_inv hysource]

/--
%%handwave
name:
  Nonnegative scalar multiples of subharmonic functions are subharmonic
statement:
  If \(u\) is subharmonic and \(c\ge 0\), then \(cu\) is subharmonic.
proof:
  For \(c=0\), this is the constant case.  For \(c>0\), upper
  semicontinuity follows by composing with the monotone continuous map
  \(t\mapsto ct\).  For comparison, divide the harmonic test function by
  \(c\), apply subharmonic comparison to \(u\), and multiply back by \(c\).
-/
theorem subharmonicOnSurface_const_mul_nonneg
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hu : IsSubharmonicOnSurface U u) :
    IsSubharmonicOnSurface U (fun x ↦ c * u x) := by
  by_cases hc_zero : c = 0
  · simpa [hc_zero] using subharmonicOnSurface_const U 0
  have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc_zero)
  have husc :
      UpperSemicontinuousOn (fun x ↦ c * u x) U := by
    have hcont : Continuous (fun t : ℝ ↦ c * t) :=
      continuous_const.mul continuous_id
    have hmono : Monotone (fun t : ℝ ↦ c * t) := by
      intro a b hab
      exact mul_le_mul_of_nonneg_left hab hc
    simpa [Function.comp_def] using
      hcont.comp_upperSemicontinuousOn hu.1 hmono
  refine ⟨husc, ?_⟩
  intro V hV_open hV_preconnected hV_frontier_nonempty hVU hV_compact
    hV_closure h hharmonic hcontinuous hboundary x hxV
  have hscaled_harmonic : IsHarmonicOnSurface V (fun x ↦ c⁻¹ * h x) :=
    harmonicOnSurface_const_mul c⁻¹ hharmonic
  have hscaled_continuous : ContinuousOn (fun x ↦ c⁻¹ * h x) (closure V) :=
    continuousOn_const.mul hcontinuous
  have hscaled_boundary : ∀ y ∈ frontier V, u y ≤ c⁻¹ * h y := by
    intro y hy
    have hmul := mul_le_mul_of_nonneg_left (hboundary y hy) (inv_nonneg.mpr hc)
    rw [← mul_assoc, inv_mul_cancel₀ hc_pos.ne', one_mul] at hmul
    exact hmul
  have hu_le : u x ≤ c⁻¹ * h x :=
    hu.2 V hV_open hV_preconnected hV_frontier_nonempty hVU
      hV_compact hV_closure (fun x ↦ c⁻¹ * h x) hscaled_harmonic
      hscaled_continuous hscaled_boundary x hxV
  calc
    c * u x ≤ c * (c⁻¹ * h x) := mul_le_mul_of_nonneg_left hu_le hc
    _ = h x := by
      rw [← mul_assoc, mul_inv_cancel₀ hc_pos.ne', one_mul]

/--
%%handwave
name:
  Maximum of two subharmonic functions
statement:
  The pointwise maximum of two subharmonic functions on the same surface
  region is subharmonic.
proof:
  Upper semicontinuity is preserved by finite maxima.  For the comparison
  principle, if a harmonic function bounds the maximum on the boundary, then
  it separately bounds each subharmonic function there, hence separately
  bounds each one inside the test region.
-/
theorem subharmonicOnSurface_sup
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u v : X → ℝ}
    (hu : IsSubharmonicOnSurface U u)
    (hv : IsSubharmonicOnSurface U v) :
    IsSubharmonicOnSurface U (fun x ↦ u x ⊔ v x) := by
  refine ⟨hu.1.sup hv.1, ?_⟩
  intro W hW_open hW_preconnected hW_frontier_nonempty hWU hW_compact
    hW_closure h hharmonic hcontinuous hboundary x hxW
  have hu_boundary : ∀ y ∈ frontier W, u y ≤ h y := by
    intro y hy
    exact (le_sup_left : u y ≤ u y ⊔ v y).trans (hboundary y hy)
  have hv_boundary : ∀ y ∈ frontier W, v y ≤ h y := by
    intro y hy
    exact (le_sup_right : v y ≤ u y ⊔ v y).trans (hboundary y hy)
  have hu_le : u x ≤ h x :=
    hu.2 W hW_open hW_preconnected hW_frontier_nonempty hWU
      hW_compact hW_closure h hharmonic hcontinuous hu_boundary x hxW
  have hv_le : v x ≤ h x :=
    hv.2 W hW_open hW_preconnected hW_frontier_nonempty hWU
      hW_compact hW_closure h hharmonic hcontinuous hv_boundary x hxW
  exact sup_le hu_le hv_le

/--
%%handwave
name:
  Upper semicontinuity is local on open neighborhoods
statement:
  If every point of a set has an open neighborhood on which a function is
  upper semicontinuous relative to the set, then the function is upper
  semicontinuous on the whole set.
-/
theorem upperSemicontinuousOn_of_locally_open
    {X : Type} [TopologicalSpace X] {U : Set X} {u : X → ℝ}
    (hlocal : ∀ x ∈ U, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      UpperSemicontinuousOn u (U ∩ N)) :
    UpperSemicontinuousOn u U := by
  exact upperSemicontinuousOn_of_locally_open_aux hlocal

/--
%%handwave
name:
  Local subharmonic comparison globalizes
statement:
  On an open surface region, the harmonic comparison principle for a function
  follows from the same comparison principle on an open neighborhood of every
  point.
proof:
  Suppose a harmonic comparison function bounds the candidate on the boundary
  of a relatively compact connected test region.  If the bound failed inside,
  upper semicontinuity would give a positive compact maximum of the difference.
  Applying the local comparison principle near such a maximum, and then
  propagating through the connected test region, contradicts the boundary
  inequality.
-/
theorem subharmonicComparisonPrinciple_of_locally
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      IsSubharmonicOnSurface (U ∩ N) u) :
    ∀ V : Set X,
      IsOpen V →
        IsPreconnected V →
          (frontier V).Nonempty →
            V ⊆ U →
              IsCompact (closure V) →
                closure V ⊆ U →
                  ∀ h : X → ℝ,
                    IsHarmonicOnSurface V h →
                      ContinuousOn h (closure V) →
                        (∀ x ∈ frontier V, u x ≤ h x) →
                          ∀ x ∈ V, u x ≤ h x := by
  exact subharmonicComparisonPrinciple_of_locally_aux hU_open hlocal

/--
%%handwave
name:
  Locally subharmonic functions are subharmonic
statement:
  On an open surface region, a real-valued function that is subharmonic in a
  neighborhood of every point of the region is subharmonic on the whole
  region.
proof:
  [Upper semicontinuity is local on open
  neighborhoods](lean:JJMath.Uniformization.upperSemicontinuousOn_of_locally_open).
  The comparison principle globalizes by
  [local subharmonic comparison](lean:JJMath.Uniformization.subharmonicComparisonPrinciple_of_locally).
-/
theorem subharmonicOnSurface_of_locally
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      IsSubharmonicOnSurface (U ∩ N) u) :
    IsSubharmonicOnSurface U u := by
  exact subharmonicOnSurface_of_locally_aux hU_open hlocal

/--
%%handwave
name:
  Subharmonicity restricts to open subspaces
statement:
  If a function is subharmonic on an open surface region, then its restriction
  to that open region, viewed as a surface in its own right, is subharmonic on
  the whole subspace.
proof:
  Work locally in a subtype chart.  Each subtype chart is the restriction of an
  ambient chart, so the ambient comparison-subharmonic coordinate expression
  restricts to the subtype chart target.  Transport that plane comparison
  statement back to the subtype surface and globalize by local subharmonicity.
-/
theorem subharmonicOnSurface_openSubtype_univ_of_ambient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (U : TopologicalSpace.Opens X) {u : X → ℝ}
    (hu : IsSubharmonicOnSurface (U : Set X) u) :
    IsSubharmonicOnSurface (Set.univ : Set U) (fun x : U ↦ u x) := by
  haveI : ComplexOneManifold U := by exact {}
  refine subharmonicOnSurface_of_locally (X := U)
    (U := (Set.univ : Set U)) isOpen_univ ?_
  intro x _hx
  let hU : Nonempty U := ⟨x⟩
  let E : OpenPartialHomeomorph X ℂ := chartAt ℂ (x : X)
  let e : OpenPartialHomeomorph U ℂ := E.subtypeRestr hU
  have he : e ∈ atlas ℂ U := by
    change (chartAt ℂ (x : X)).subtypeRestr hU ∈ atlas ℂ U
    rw [← TopologicalSpace.Opens.chartAt_eq (H := ℂ) (s := U) (x := x)]
    exact chart_mem_atlas ℂ x
  let S : Set ℂ := E.target ∩ E.symm ⁻¹' (U : Set X)
  have hu_plane :
      IsSubharmonicByPlaneComparisonOn S (fun z : ℂ ↦ u (E.symm z)) := by
    simpa [S] using subharmonicOnSurface_to_planeComparisonOn hu E
      (chart_mem_atlas ℂ (x : X))
  have he_target_subset_S : e.target ⊆ S := by
    intro z hz
    have hzE : z ∈ E.target := E.subtypeRestr_target_subset hU hz
    have hzU : E.symm z ∈ (U : Set X) := by
      have hval : (e.symm z : X) = E.symm z := by
        simpa [e, Function.comp_def] using E.subtypeRestr_symm_apply hU hz
      have hz_subtype : (e.symm z : X) ∈ (U : Set X) := (e.symm z).property
      simpa [hval] using hz_subtype
    exact ⟨hzE, hzU⟩
  have hu_plane_target_ambient :
      IsSubharmonicByPlaneComparisonOn e.target (fun z : ℂ ↦ u (E.symm z)) :=
    subharmonicByPlaneComparisonOn_mono he_target_subset_S hu_plane
  have hu_plane_target :
      IsSubharmonicByPlaneComparisonOn e.target
        (fun z : ℂ ↦ u (e.symm z)) := by
    refine subharmonicByPlaneComparisonOn_congr_on hu_plane_target_ambient ?_
    intro z hz
    have hval : (e.symm z : X) = E.symm z := by
      simpa [e, Function.comp_def] using E.subtypeRestr_symm_apply hU hz
    simp [hval]
  let N : Set U := e.source
  refine ⟨N, e.open_source, ?_, ?_⟩
  · have hxE : (x : X) ∈ E.source := mem_chart_source ℂ (x : X)
    simp [N, e, E, OpenPartialHomeomorph.subtypeRestr_source, hxE]
  · have hchart :
        IsSubharmonicOnSurface (e.source ∩ e ⁻¹' e.target)
          (fun y : U ↦ u (e.symm (e y))) := by
      simpa [Function.comp_def] using
        planeComparisonOn_to_subharmonicOnSurface e he hu_plane_target
    have hdomain_eq :
        (Set.univ : Set U) ∩ N = e.source ∩ e ⁻¹' e.target := by
      ext y
      constructor
      · intro hy
        have hysource : y ∈ e.source := hy.2
        exact ⟨hysource, e.map_source hysource⟩
      · intro hy
        exact ⟨Set.mem_univ y, hy.1⟩
    have hchart' :
        IsSubharmonicOnSurface ((Set.univ : Set U) ∩ N)
          (fun y : U ↦ u (e.symm (e y))) := by
      simpa [hdomain_eq] using hchart
    refine subharmonicOnSurface_congr_on hchart' ?_
    intro y hy
    have hysource : y ∈ e.source := hy.2
    simp [e.left_inv hysource]

/--
%%handwave
name:
  Superharmonic function on a surface region
statement:
  A function is superharmonic when its negative is subharmonic.
-/
def IsSuperharmonicOnSurface {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) : Prop :=
  IsSubharmonicOnSurface U (fun x ↦ -u x)

/--
%%handwave
name:
  Superharmonicity restricts to smaller surface regions
statement:
  A superharmonic function on a surface region remains superharmonic on every
  smaller region.
-/
theorem superharmonicOnSurface_mono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U V : Set X} {u : X → ℝ}
    (hVU : V ⊆ U)
    (hu : IsSuperharmonicOnSurface U u) :
    IsSuperharmonicOnSurface V u :=
  subharmonicOnSurface_mono hVU hu

/--
%%handwave
name:
  Constant functions are superharmonic
statement:
  Constant real-valued functions are superharmonic on every surface region.
-/
theorem superharmonicOnSurface_const
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (U : Set X) (c : ℝ) :
    IsSuperharmonicOnSurface U (fun _ : X ↦ c) := by
  simpa [IsSuperharmonicOnSurface] using subharmonicOnSurface_const U (-c)

/--
%%handwave
name:
  Harmonic functions are superharmonic
statement:
  A harmonic real-valued function on an open surface region is superharmonic
  on that region.
-/
theorem harmonicOnSurface_superharmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {h : X → ℝ}
    (hU_open : IsOpen U)
    (hh : IsHarmonicOnSurface U h) :
    IsSuperharmonicOnSurface U h := by
  simpa [IsSuperharmonicOnSurface] using
    harmonicOnSurface_subharmonic hU_open (harmonicOnSurface_neg hh)

/--
%%handwave
name:
  Adding a constant preserves superharmonicity
statement:
  If a function is superharmonic on a surface region, then adding a constant
  to it is superharmonic on the same region.
-/
theorem superharmonicOnSurface_const_add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} (c : ℝ)
    (hu : IsSuperharmonicOnSurface U u) :
    IsSuperharmonicOnSurface U (fun x ↦ c + u x) := by
  have hshift :
      IsSubharmonicOnSurface U (fun x ↦ (-c) + (-u x)) :=
    subharmonicOnSurface_const_add (-c) hu
  simpa [IsSuperharmonicOnSurface, neg_add, add_comm] using hshift

/--
%%handwave
name:
  Adding a constant on the right preserves superharmonicity
statement:
  If a function is superharmonic on a surface region, then adding a constant
  on the right is superharmonic on the same region.
-/
theorem superharmonicOnSurface_add_const
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} (c : ℝ)
    (hu : IsSuperharmonicOnSurface U u) :
    IsSuperharmonicOnSurface U (fun x ↦ u x + c) := by
  simpa [add_comm] using superharmonicOnSurface_const_add c hu

/--
%%handwave
name:
  Superharmonic plus harmonic is superharmonic
statement:
  If \(u\) is superharmonic and \(h\) is harmonic on the same open surface
  region, then \(u+h\) is superharmonic.
-/
theorem superharmonicOnSurface_add_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u h : X → ℝ}
    (hU_open : IsOpen U)
    (hu : IsSuperharmonicOnSurface U u)
    (hh : IsHarmonicOnSurface U h) :
    IsSuperharmonicOnSurface U (fun x ↦ u x + h x) := by
  have hsub :
      IsSubharmonicOnSurface U (fun x ↦ (-u x) - h x) :=
    subharmonicOnSurface_sub_harmonic hU_open hu hh
  simpa [IsSuperharmonicOnSurface, sub_eq_add_neg, neg_add,
    add_comm, add_left_comm, add_assoc] using hsub

/--
%%handwave
name:
  Superharmonic minus harmonic is superharmonic
statement:
  If \(u\) is superharmonic and \(h\) is harmonic on the same open surface
  region, then \(u-h\) is superharmonic.
-/
theorem superharmonicOnSurface_sub_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u h : X → ℝ}
    (hU_open : IsOpen U)
    (hu : IsSuperharmonicOnSurface U u)
    (hh : IsHarmonicOnSurface U h) :
    IsSuperharmonicOnSurface U (fun x ↦ u x - h x) := by
  have hneg : IsHarmonicOnSurface U (fun x ↦ -h x) :=
    harmonicOnSurface_neg hh
  simpa [sub_eq_add_neg] using
    superharmonicOnSurface_add_harmonic hU_open hu hneg

/--
%%handwave
name:
  Nonnegative scalar multiples of superharmonic functions are superharmonic
statement:
  If \(u\) is superharmonic and \(c\ge0\), then \(cu\) is superharmonic.
-/
theorem superharmonicOnSurface_const_mul_nonneg
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hu : IsSuperharmonicOnSurface U u) :
    IsSuperharmonicOnSurface U (fun x ↦ c * u x) := by
  have hscaled :
      IsSubharmonicOnSurface U (fun x ↦ c * (-u x)) :=
    subharmonicOnSurface_const_mul_nonneg hc hu
  simpa [IsSuperharmonicOnSurface, mul_neg] using hscaled

/--
%%handwave
name:
  Minima of superharmonic functions are superharmonic
statement:
  The pointwise minimum of two superharmonic functions on the same surface
  region is superharmonic.
proof:
  The negatives \(-u\) and \(-v\) are subharmonic.  By [the pointwise maximum of two subharmonic functions is subharmonic](lean:JJMath.Uniformization.subharmonicOnSurface_sup), their maximum is subharmonic; since \(-\min(u,v)=\max(-u,-v)\), negating gives the claim.
-/
theorem superharmonicOnSurface_inf
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u v : X → ℝ}
    (hu : IsSuperharmonicOnSurface U u)
    (hv : IsSuperharmonicOnSurface U v) :
    IsSuperharmonicOnSurface U (fun x ↦ u x ⊓ v x) := by
  have hsup :
      IsSubharmonicOnSurface U (fun x ↦ (-u x) ⊔ (-v x)) :=
    subharmonicOnSurface_sup hu hv
  have hrewrite :
      (fun x : X ↦ -(u x ⊓ v x)) = (fun x : X ↦ (-u x) ⊔ (-v x)) := by
    funext x
    exact (max_neg_neg (u x) (v x)).symm
  change IsSubharmonicOnSurface U (fun x ↦ -(u x ⊓ v x))
  rw [hrewrite]
  exact hsup

/--
%%handwave
name:
  Minimum with a constant preserves superharmonicity
statement:
  The pointwise minimum of a superharmonic function and a constant is
  superharmonic.
-/
theorem superharmonicOnSurface_inf_const
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ} (c : ℝ)
    (hu : IsSuperharmonicOnSurface U u) :
    IsSuperharmonicOnSurface U (fun x ↦ u x ⊓ c) := by
  simpa using
    superharmonicOnSurface_inf hu (superharmonicOnSurface_const U c)

/--
%%handwave
name:
  Minimum with a constant on the left preserves superharmonicity
statement:
  The pointwise minimum of a constant and a superharmonic function is
  superharmonic.
-/
theorem superharmonicOnSurface_const_inf
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ} (c : ℝ)
    (hu : IsSuperharmonicOnSurface U u) :
    IsSuperharmonicOnSurface U (fun x ↦ c ⊓ u x) := by
  simpa [inf_comm] using superharmonicOnSurface_inf_const c hu

/--
%%handwave
name:
  Compact sets in surface open sets have compactly contained neighborhoods
statement:
  If a compact subset of a Riemann surface lies in an open set, then it has an
  open neighborhood whose closure is compact and still lies in that open set.
-/
theorem exists_surface_open_between_and_isCompact_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧ IsCompact (closure V) :=
  exists_open_between_and_isCompact_closure hK hU hKU

/--
%%handwave
name:
  Surface points have compactly contained neighborhoods
statement:
  Every point of an open set in a Riemann surface has an open neighborhood
  whose closure is compact and contained in the original open set.
-/
theorem exists_surface_open_nhds_isCompact_closure_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} (hU : IsOpen U) {p : X} (hp : p ∈ U) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ closure V ⊆ U ∧ IsCompact (closure V) := by
  rcases exists_surface_open_between_and_isCompact_closure
      (X := X) (K := {p}) (U := U) isCompact_singleton hU
      (by intro x hx; simpa using hx ▸ hp) with
    ⟨V, hV_open, hpV, hV_closure, hV_compact⟩
  exact ⟨V, hV_open, hpV (by simp), hV_closure, hV_compact⟩

/--
%%handwave
name:
  Locally superharmonic functions are superharmonic
statement:
  On an open surface region, a real-valued function that is superharmonic in
  a neighborhood of every point of the region is superharmonic on the whole
  region.
proof:
  Superharmonicity is local.  Lower semicontinuity is local on an open cover,
  and the comparison principle globalizes by applying the local comparison
  principle to the open set where the candidate comparison inequality would
  fail.
-/
theorem superharmonicOnSurface_of_locally
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      IsSuperharmonicOnSurface (U ∩ N) u) :
    IsSuperharmonicOnSurface U u := by
  exact subharmonicOnSurface_of_locally hU_open (fun x hx ↦ by
    rcases hlocal x hx with ⟨N, hN_open, hxN, hN_super⟩
    exact ⟨N, hN_open, hxN, hN_super⟩)

end Uniformization

end JJMath
