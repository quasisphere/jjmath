import JJMath.Uniformization.HubbardUniformization
import JJMath.ProjectiveGeometry.RiemannSphere
import JJMath.Uniformization.Biholomorphic
import JJMath.Uniformization.ExteriorMassTransport
import JJMath.Uniformization.SimplyConnectedExhaustion
import JJMath.Uniformization.SurfaceTopDegree
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Compact zero-cohomology uniformization

This file isolates the compact step in Hubbard's proof.  Removing a point from
a compact connected surface with vanishing first cohomology again gives
vanishing first cohomology; the open-surface theorem then uniformizes the
punctured surface.  The disk alternative is excluded by removable singularity,
while the plane alternative identifies the original compact surface with the
one-point compactification of the plane.
-/

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace JJMath.Uniformization

open JJMath.Manifold

universe u v w

section MayerVietorisAlgebra

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- If the degree-one Mayer--Vietoris connecting map is injective, vanishing
of ambient and right-hand first cohomology forces vanishing on the left-hand
member of the cover. -/
theorem deRhamH1_left_subsingleton_of_connecting_injective
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    [Subsingleton
      (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1)]
    (U V : TopologicalSpace.Opens M) (hcover : U ⊔ V = ⊤)
    [Subsingleton
      (DeRhamCohomology (I := I) (M := V) (A := ℝ) 1)]
    (hconnecting : Function.Injective
      (deRhamMayerVietorisConnectingOfPartitionOfUnity
        (A := ℝ) I U V hcover 1)) :
    Subsingleton
      (DeRhamCohomology (I := I) (M := U) (A := ℝ) 1) := by
  let rho := deRhamCohomologyRestrictionOfLE
    (I := I) (A := ℝ)
    (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := U)
    inf_le_left 1
  let sigma := deRhamCohomologyRestrictionOfLE
    (I := I) (A := ℝ)
    (W := (U ⊓ V : TopologicalSpace.Opens M)) (V := V)
    inf_le_right 1
  let connecting :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity
      (A := ℝ) I U V hcover 1
  have hrho : Function.Injective rho :=
    deRhamH1_left_restriction_injective_of_ambient_right_subsingleton
      I U V hcover
  have hconnecting_zero : connecting 0 = 0 := by
    have hsmul :=
      deRhamMayerVietorisConnectingOfPartitionOfUnity_smul
        I U V hcover 1 (0 : ℝ)
          (0 : DeRhamCohomology
            (I := I) (M := (U ⊓ V : TopologicalSpace.Opens M))
            (A := ℝ) 1)
    simpa [connecting] using hsmul
  have hzero : ∀ alpha : DeRhamCohomology
      (I := I) (M := U) (A := ℝ) 1, alpha = 0 := by
    intro alpha
    apply hrho
    rw [rho.map_zero]
    apply hconnecting
    change connecting (rho alpha) = connecting 0
    rw [hconnecting_zero]
    have hexact :=
      deRham_mayerVietoris_exact_difference_connecting_of_partitionOfUnity
        (A := ℝ) I U V hcover 1
    apply (hexact (rho alpha)).mpr
    refine ⟨(alpha, 0), ?_⟩
    change rho alpha - sigma 0 = rho alpha
    rw [sigma.map_zero, sub_zero]
  constructor
  intro alpha beta
  rw [hzero alpha, hzero beta]

end MayerVietorisAlgebra

/-- Removing a point from a compact Riemann surface gives a
noncompact Riemann surface. -/
theorem puncturedSurfaceOpen_noncompact
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [CompactSpace X] (p : X) :
    NoncompactSpace (puncturedSurfaceOpen p) := by
  rw [← not_compactSpace_iff]
  intro hcompact
  letI : CompactSpace (puncturedSurfaceOpen p) := hcompact
  have hpunctured : IsCompact (puncturedSurfaceOpen p : Set X) :=
    isCompact_iff_compactSpace.mpr inferInstance
  have hopen : IsOpen ({p} : Set X) := by
    simpa [puncturedSurfaceOpen] using hpunctured.isClosed.isOpen_compl
  letI : Filter.NeBot (𝓝[≠] p) :=
    punctured_nhds_neBot_riemannSurface X p
  exact not_isOpen_singleton p hopen

/--
%%handwave
name:
  Removable point for continuous holomorphic maps
statement:
  Let \(X\) be a Riemann surface, \(p\in X\), and \(f:X\to\mathbb C\).  If
  \(f\) is continuous at \(p\) and holomorphic throughout some punctured
  neighborhood of \(p\), then \(f\) is holomorphic at \(p\).
proof:
  Write the map in a complex coordinate centered at \(p\).  The resulting
  complex-valued function is continuous at the center and holomorphic in a
  punctured neighborhood, so Riemann's removable-singularity theorem applies.
-/
theorem mdifferentiableAt_of_continuousAt_of_eventually_punctured
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] (p : X) (f : X → ℂ)
    (hcont : ContinuousAt f p)
    (hdiff : ∀ᶠ x in 𝓝[≠] p,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hc_target : c ∈ e.target := e.map_source hp_source
  have he_symm_cont : ContinuousAt e.symm c :=
    (e.continuousOn_symm c hc_target).continuousAt
      (e.open_target.mem_nhds hc_target)
  have hcoord_cont : ContinuousAt (fun z : ℂ ↦ f (e.symm z)) c := by
    have h := hcont.comp_of_eq he_symm_cont (e.left_inv hp_source)
    simpa [Function.comp_def] using h
  have hcoord_diff : ∀ᶠ z in 𝓝[≠] c,
      DifferentiableAt ℂ (fun w : ℂ ↦ f (e.symm w)) z := by
    rw [eventually_nhdsWithin_iff] at hdiff ⊢
    have hdiff' : ∀ᶠ x in 𝓝 (e.symm c),
        x ∈ ({p} : Set X)ᶜ →
          MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := by
      simpa [c, e.left_inv hp_source] using hdiff
    filter_upwards
      [e.open_target.mem_nhds hc_target, he_symm_cont.eventually hdiff']
      with z hz_target hzdiff
    intro hzc
    have hx_source : e.symm z ∈ e.source := e.map_target hz_target
    have hxp : e.symm z ≠ p := by
      intro heq
      apply hzc
      calc
        z = e (e.symm z) := (e.right_inv hz_target).symm
        _ = e p := congrArg e heq
        _ = c := rfl
    have hmd := hzdiff hxp
    rw [mdifferentiableAt_iff_of_mem_source
      (x := p) hx_source (mem_chart_source ℂ (f (e.symm z)))] at hmd
    simpa [e, Function.comp_def, differentiableWithinAt_univ,
      e.right_inv hz_target] using hmd.2
  have hcoord_diff_at :
      DifferentiableAt ℂ (fun z : ℂ ↦ f (e.symm z)) c :=
    (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hcoord_diff hcoord_cont).differentiableAt
  rw [mdifferentiableAt_iff_of_mem_source hp_source (mem_chart_source ℂ (f p))]
  exact ⟨hcont, by
    simpa [e, c, Function.comp_def] using
      hcoord_diff_at.differentiableWithinAt⟩

/--
%%handwave
name:
  Removable point for continuous holomorphic maps between surfaces
statement:
  Let \(X,Y\) be Riemann surfaces, \(p\in X\), and \(f:X\to Y\).  If \(f\)
  is continuous at \(p\) and holomorphic throughout some punctured
  neighborhood of \(p\), then \(f\) is holomorphic at \(p\).
proof:
  Compose with a complex coordinate of \(Y\) centered at \(f(p)\), apply the
  complex-valued removable-point theorem, and translate the conclusion back
  through the same coordinate.
-/
theorem mdifferentiableAt_of_continuousAt_of_eventually_punctured_target
    (X : Type) (Y : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [ComplexOneManifold Y]
    (p : X) (f : X → Y)
    (hcont : ContinuousAt f p)
    (hdiff : ∀ᶠ x in 𝓝[≠] p,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p := by
  let e' : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f p)
  let h : X → ℂ := fun x ↦ e' (f x)
  have hfp : f p ∈ e'.source := mem_chart_source ℂ (f p)
  have he'_cont : ContinuousAt e' (f p) :=
    (e'.continuousOn (f p) hfp).continuousAt
      (e'.open_source.mem_nhds hfp)
  have hh_cont : ContinuousAt h p := he'_cont.comp hcont
  have hh_diff : ∀ᶠ x in 𝓝[≠] p,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) h x := by
    rw [eventually_nhdsWithin_iff] at hdiff ⊢
    have hsource : ∀ᶠ x in 𝓝 p, f x ∈ e'.source :=
      hcont.eventually (e'.open_source.mem_nhds hfp)
    filter_upwards [hdiff, hsource] with x hfx hfx_source
    intro hxp
    have he'_md : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e' (f x) :=
      (mdifferentiableOn_atlas (I := 𝓘(ℂ))
        (chart_mem_atlas ℂ (f p)) (f x) hfx_source).mdifferentiableAt
        (e'.open_source.mem_nhds hfx_source)
    exact he'_md.comp x (hfx hxp)
  have hh := mdifferentiableAt_of_continuousAt_of_eventually_punctured
    X p h hh_cont hh_diff
  rw [mdifferentiableAt_iff_of_mem_source (f := h)
    (mem_chart_source ℂ p) (mem_chart_source ℂ (h p))] at hh
  rw [mdifferentiableAt_iff_of_mem_source (f := f)
    (mem_chart_source ℂ p) (mem_chart_source ℂ (f p))]
  exact ⟨hcont, by simpa [h, e', Function.comp_def] using hh.2⟩

/-- A function agreeing on an open set with a holomorphic function on the
corresponding open subtype is holomorphic on that open set. -/
private theorem mdifferentiableOn_of_eq_openSubtype
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (U : TopologicalSpace.Opens X) (f : U → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (F : X → ℂ) (hF : ∀ x (hx : x ∈ U), F x = f ⟨x, hx⟩) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F U := by
  classical
  intro x hxU
  let xU : U := ⟨x, hxU⟩
  let retract : X → U := fun y ↦
    if hy : y ∈ U then ⟨y, hy⟩ else xU
  have hretract : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) retract x := by
    have hsmooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ⊤ retract x := by
      rw [← contMDiffAt_subtype_iff (U := U) (x := xU)]
      have heq : (fun y : U ↦ retract y) = id := by
        funext y
        simp [retract]
      rw [heq]
      exact contMDiffAt_id
    exact hsmooth.mdifferentiableAt (by simp)
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ retract) x :=
    (hf (retract x)).comp x hretract
  have heq : F =ᶠ[𝓝 x] f ∘ retract := by
    filter_upwards [U.isOpen.mem_nhds hxU] with y hyU
    rw [hF y hyU]
    apply congrArg f
    apply Subtype.ext
    change y = ↑(if hy : y ∈ U then (⟨y, hy⟩ : U) else xU)
    split <;> simp_all
  exact (hcomp.congr_of_eventuallyEq heq).mdifferentiableWithinAt

/--
%%handwave
name:
  Removable singularity for a bounded punctured-surface map
statement:
  Let $X$ be a Riemann surface, let $p\in X$, and let
  $f:X\setminus\{p\}\to\mathbb C$ be holomorphic. If there is a constant
  $C$ such that $|f(x)|\le C$ for all $x\ne p$, then there is a holomorphic
  map $F:X\to\mathbb C$ satisfying $F(x)=f(x)$ for every $x\ne p$.
proof:
  Choose a complex coordinate centered at $p$. In that coordinate, boundedness
  gives a finite punctured limit, and assigning this limit at the center
  produces a holomorphic extension. Patch this value with $f$ away from $p$;
  the two descriptions agree on a punctured neighborhood.
-/
theorem bounded_punctured_holomorphicMap_extends
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (f : puncturedSurfaceOpen p → ℂ)
    (hf : HolomorphicMap (puncturedSurfaceOpen p) ℂ f)
    (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    ∃ F : X → ℂ,
      HolomorphicMap X ℂ F ∧
        ∀ x (hxp : x ≠ p), F x = f ⟨x, hxp⟩ := by
  classical
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  let g : X → ℂ := fun x ↦ if hxp : x ≠ p then f ⟨x, hxp⟩ else 0
  have hgU : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g U := by
    apply mdifferentiableOn_of_eq_openSubtype U f hf g
    intro x hx
    have hxp : x ≠ p := by simpa [U, puncturedSurfaceOpen] using hx
    simp [g, hxp]
  let χ : PointedSurfaceCoordinate X p := {
    chart := chartAt ℂ p
    chart_mem_atlas := chart_mem_atlas ℂ p
    base_mem_source := mem_chart_source ℂ p }
  let c : ℂ := χ.chart p
  let gχ : ℂ → ℂ := fun z ↦ g (χ.chart.symm z)
  have hc_target : c ∈ χ.chart.target := χ.chart.map_source χ.base_mem_source
  have htarget_nhds : χ.chart.target ∈ 𝓝 c :=
    χ.chart.open_target.mem_nhds hc_target
  have hgχ_diff : DifferentiableOn ℂ gχ (χ.chart.target \ {c}) := by
    intro z hz
    have hz_target : z ∈ χ.chart.target := hz.1
    have hz_ne : z ≠ c := by simpa using hz.2
    have hx_ne : χ.chart.symm z ≠ p := by
      intro heq
      exact hz_ne (by simpa [c, heq] using (χ.chart.right_inv hz_target).symm)
    have hxU : χ.chart.symm z ∈ U := by
      simpa [U, puncturedSurfaceOpen] using hx_ne
    have hg_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (χ.chart.symm z) :=
      (hgU (χ.chart.symm z) hxU).mdifferentiableAt
        (U.isOpen.mem_nhds hxU)
    have hsymm_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ.chart.symm z :=
      (mdifferentiableOn_atlas_symm (I := 𝓘(ℂ)) χ.chart_mem_atlas
        z hz_target).mdifferentiableAt
        (χ.chart.open_target.mem_nhds hz_target)
    have hcomp := hg_at.comp z hsymm_at
    rw [mdifferentiableAt_iff_differentiableAt] at hcomp
    exact hcomp.differentiableWithinAt
  have hgχ_bounded : BddAbove
      (norm ∘ gχ '' (χ.chart.target \ {c})) := by
    rcases hbound with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz_target : z ∈ χ.chart.target := hz.1
    have hz_ne : z ≠ c := by simpa using hz.2
    have hx_ne : χ.chart.symm z ≠ p := by
      intro heq
      exact hz_ne (by simpa [c, heq] using (χ.chart.right_inv hz_target).symm)
    simpa [Function.comp_apply, gχ, g, hx_ne] using hC ⟨χ.chart.symm z, hx_ne⟩
  let q : ℂ → ℂ := Function.update gχ c ((𝓝[≠] c).limUnder gχ)
  have hq_diff : DifferentiableOn ℂ q χ.chart.target := by
    exact Complex.differentiableOn_update_limUnder_of_bddAbove
      htarget_nhds hgχ_diff hgχ_bounded
  let L : ℂ := (𝓝[≠] c).limUnder gχ
  let F : X → ℂ := Function.update g p L
  have hF_away : ∀ x (hxp : x ≠ p), F x = f ⟨x, hxp⟩ := by
    intro x hxp
    simp [F, g, hxp]
  have hF_hol : HolomorphicMap X ℂ F := by
    intro x
    by_cases hxp : x = p
    · subst x
      have hq_at : DifferentiableAt ℂ q c :=
        (hq_diff c hc_target).differentiableAt htarget_nhds
      have hq_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) q c := by
        rw [mdifferentiableAt_iff_differentiableAt]
        exact hq_at
      have hchart : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ.chart p :=
        (mdifferentiableOn_atlas (I := 𝓘(ℂ)) χ.chart_mem_atlas
          p χ.base_mem_source).mdifferentiableAt
          (χ.chart.open_source.mem_nhds χ.base_mem_source)
      have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (q ∘ χ.chart) p :=
        hq_mdiff.comp p hchart
      have heq : F =ᶠ[𝓝 p] q ∘ χ.chart := by
        filter_upwards [χ.chart.open_source.mem_nhds χ.base_mem_source] with y hy
        by_cases hyp : y = p
        · subst y
          simp [F, q, L, c, Function.comp_apply]
        · have hyc : χ.chart y ≠ c := by
            intro hyc
            apply hyp
            exact χ.chart.injOn hy χ.base_mem_source hyc
          simp [F, q, L, gχ, g, c, hyp, hyc, Function.comp_apply,
            χ.chart.left_inv hy]
      exact hcomp.congr_of_eventuallyEq heq
    · have hxU : x ∈ U := by simpa [U, puncturedSurfaceOpen] using hxp
      have hg_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g x :=
        (hgU x hxU).mdifferentiableAt (U.isOpen.mem_nhds hxU)
      have heq : F =ᶠ[𝓝 x] g := by
        filter_upwards [isOpen_ne.mem_nhds hxp] with y hy
        simp [F, hy]
      exact hg_at.congr_of_eventuallyEq heq
  exact ⟨F, hF_hol, hF_away⟩

/--
%%handwave
name:
  A punctured compact surface is not the unit disk
statement:
  If $X$ is a compact Riemann surface and $p\in X$, then
  $X\setminus\{p\}$ is not biholomorphic to the unit disk $\mathbb D$.
proof:
  Suppose $B:X\setminus\{p\}\to\mathbb D$ were biholomorphic. Its complex
  coordinate is bounded, so [it extends holomorphically across $p$ to all of $X$](lean:JJMath.Uniformization.bounded_punctured_holomorphicMap_extends). Every holomorphic function on the compact connected surface $X$ is constant, contradicting the injectivity of $B$.
-/
theorem compact_puncturedSurfaceOpen_not_biholomorphic_unitDisc
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [CompactSpace X] (p : X) :
    ¬ BiholomorphicSurfaces (puncturedSurfaceOpen p) Complex.UnitDisc := by
  rintro ⟨B⟩
  let f : puncturedSurfaceOpen p → ℂ := fun x ↦ (B.toHomeomorph x : ℂ)
  have hf : HolomorphicMap (puncturedSurfaceOpen p) ℂ f := by
    exact holomorphicMap_unitDisc_coe.comp B.holomorphic_toFun
  have hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
    refine ⟨1, ?_⟩
    intro x
    change ‖((B.toHomeomorph x : Complex.UnitDisc) : ℂ)‖ ≤ 1
    exact le_of_lt (Complex.UnitDisc.norm_lt_one (B.toHomeomorph x))
  rcases bounded_punctured_holomorphicMap_extends X p f hf hbound with
    ⟨F, hF_hol, hF_away⟩
  let half : Complex.UnitDisc := ⟨(2 : ℂ)⁻¹, by
    rw [Subsemigroup.mem_unitBall]
    norm_num⟩
  let x₀ : puncturedSurfaceOpen p := B.toHomeomorph.symm 0
  let x₁ : puncturedSurfaceOpen p := B.toHomeomorph.symm half
  have hconst : F (x₀ : X) = F (x₁ : X) :=
    hF_hol.apply_eq_of_compactSpace (x₀ : X) (x₁ : X)
  have hx₀ : F (x₀ : X) = 0 := by
    rw [hF_away (x₀ : X) x₀.2]
    change ((B.toHomeomorph x₀ : Complex.UnitDisc) : ℂ) = 0
    simp [x₀]
  have hx₁ : F (x₁ : X) = (2 : ℂ)⁻¹ := by
    rw [hF_away (x₁ : X) x₁.2]
    change ((B.toHomeomorph x₁ : Complex.UnitDisc) : ℂ) = (2 : ℂ)⁻¹
    have hx : B.toHomeomorph x₁ = half := by simp [x₁]
    rw [hx]
    rfl
  rw [hx₀, hx₁] at hconst
  norm_num at hconst

/--
%%handwave
name:
  Depuncturing a planar compact surface
statement:
  Let \(X\) be a compact Riemann surface and \(p\in X\).  If
  \(X\setminus\{p\}\) is biholomorphic to \(\mathbb C\), then \(X\) is
  biholomorphic to the standard Riemann sphere
  \(\widehat{\mathbb C}=\mathbb C\cup\{\infty\}\).
proof:
  The punctured biholomorphism extends uniquely to a homeomorphism sending
  \(p\) to \(\infty\).  It and its inverse are holomorphic away from those
  points.  Continuity and the removable-point theorem make both maps
  holomorphic at the two added points.
-/
theorem compact_biholomorphic_riemannSphere_of_punctured_complexPlane
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [CompactSpace X] (p : X)
    (hplane : BiholomorphicSurfaces (puncturedSurfaceOpen p) ℂ) :
    BiholomorphicSurfaces X RiemannSphere := by
  classical
  rcases hplane with ⟨F⟩
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  let inclusion : ℂ → X := fun z => ((F.toHomeomorph.symm z : U) : X)
  have hinclusion : Topology.IsEmbedding inclusion :=
    Topology.IsEmbedding.subtypeVal.comp F.toHomeomorph.symm.isEmbedding
  have hrange : Set.range inclusion = ({p} : Set X)ᶜ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (F.toHomeomorph.symm z).2
    · intro hxp
      have hxp' : x ≠ p := by simpa using hxp
      refine ⟨F.toHomeomorph ⟨x, hxp'⟩, ?_⟩
      simp [inclusion]
  let sphereToX : RiemannSphere ≃ₜ X :=
    OnePoint.equivOfIsEmbeddingOfRangeEq p inclusion hinclusion hrange
  let e : X ≃ₜ RiemannSphere := sphereToX.symm
  have he_p : e p = OnePoint.infty := by
    apply sphereToX.injective
    simp [e, sphereToX]
  have he_away (x : X) (hxp : x ≠ p) :
      e x = (F.toHomeomorph ⟨x, hxp⟩ : RiemannSphere) := by
    apply sphereToX.injective
    simp [e, sphereToX, inclusion]
  have he_symm_coe (z : ℂ) :
      e.symm (z : RiemannSphere) =
        ((F.toHomeomorph.symm z : U) : X) := by
    simp [e, sphereToX, inclusion]

  let fU : U → ℂ := fun x ↦ F.toHomeomorph x
  let g : X → ℂ := fun x ↦
    if hxp : x ≠ p then fU ⟨x, hxp⟩ else 0
  have hg_on : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g U := by
    apply mdifferentiableOn_of_eq_openSubtype U fU F.holomorphic_toFun g
    intro x hx
    have hxp : x ≠ p := by simpa [U, puncturedSurfaceOpen] using hx
    simp [g, fU, hxp]
  have hg_away (x : X) (hxp : x ≠ p) :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g x := by
    have hxU : x ∈ U := by simpa [U, puncturedSurfaceOpen] using hxp
    exact (hg_on x hxU).mdifferentiableAt (U.isOpen.mem_nhds hxU)
  have he_md_away (x : X) (hxp : x ≠ p) :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e x := by
    have hcomp := (riemannSphereCoe_mdifferentiable (g x)).comp x
      (hg_away x hxp)
    have heq : e =ᶠ[𝓝 x] fun y ↦ (g y : RiemannSphere) := by
      filter_upwards [isOpen_ne.mem_nhds hxp] with y hyp
      simp [he_away y hyp, g, fU, hyp]
    exact hcomp.congr_of_eventuallyEq heq
  have he_md : HolomorphicMap X RiemannSphere e := by
    intro x
    by_cases hxp : x = p
    · subst x
      apply mdifferentiableAt_of_continuousAt_of_eventually_punctured_target
        X RiemannSphere p e e.continuous.continuousAt
      rw [eventually_nhdsWithin_iff]
      exact Filter.Eventually.of_forall fun x hxp ↦ he_md_away x hxp
    · exact he_md_away x hxp

  let hInv : ℂ → X := fun z ↦ ((F.toHomeomorph.symm z : U) : X)
  have hhInv : HolomorphicMap ℂ X hInv := by
    have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (Subtype.val : U → X) :=
      (contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))).mdifferentiable (by simp)
    exact hval.comp F.holomorphic_invFun
  have he_symm_md_coe (z : ℂ) :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm (z : RiemannSphere) := by
    have hmem : riemannSphereFiniteChart ∈ atlas ℂ RiemannSphere := by
      change riemannSphereFiniteChart ∈
        ({riemannSphereFiniteChart, riemannSphereInfinityChart} :
          Set (OpenPartialHomeomorph RiemannSphere ℂ))
      simp
    have hchart : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        riemannSphereFiniteChart (z : RiemannSphere) :=
      (mdifferentiableOn_atlas (I := 𝓘(ℂ)) hmem
        (z : RiemannSphere) (by simp)).mdifferentiableAt
        (by simp)
    have hcomp := (hhInv (riemannSphereFiniteChart (z : RiemannSphere))).comp
      (z : RiemannSphere) hchart
    have heq : e.symm =ᶠ[𝓝 (z : RiemannSphere)]
        fun w ↦ hInv (riemannSphereFiniteChart w) := by
      filter_upwards
        [riemannSphereFiniteChart.open_source.mem_nhds (by simp)]
        with w hw
      induction w using OnePoint.rec with
      | infty => simp at hw
      | coe w => simp [hInv, he_symm_coe]
    exact hcomp.congr_of_eventuallyEq heq
  have he_symm_md : HolomorphicMap RiemannSphere X e.symm := by
    intro z
    induction z using OnePoint.rec with
    | coe z => exact he_symm_md_coe z
    | infty =>
        apply mdifferentiableAt_of_continuousAt_of_eventually_punctured_target
          RiemannSphere X OnePoint.infty e.symm e.symm.continuous.continuousAt
        rw [eventually_nhdsWithin_iff]
        filter_upwards [] with z hz
        induction z using OnePoint.rec with
        | infty => exact False.elim (hz rfl)
        | coe z => exact he_symm_md_coe z
  exact ⟨{
    toHomeomorph := e
    holomorphic_toFun := he_md
    holomorphic_invFun := he_symm_md }⟩

/-- Assuming the punctured surface has vanishing first de Rham cohomology,
the open-surface theorem and removable singularity uniformize the compact
surface by the sphere. -/
theorem compact_deRhamH1Zero_biholomorphic_riemannSphere_of_punctured
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [CompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (p : X)
    (hpunctured : Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := puncturedSurfaceOpen p) (A := ℝ) 1)) :
    BiholomorphicSurfaces X RiemannSphere := by
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  letI : RiemannSurface U :=
    puncturedSurfaceOpen_riemannSurface X p
  letI : NoncompactSpace U := puncturedSurfaceOpen_noncompact X p
  letI : Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := U) (A := ℝ) 1) := by
    simpa [U] using hpunctured
  rcases noncompact_deRhamH1Zero_biholomorphic_complexPlane_or_unitDisc U with
    hplane | hdisk
  · exact compact_biholomorphic_riemannSphere_of_punctured_complexPlane X p hplane
  · exact False.elim
      (compact_puncturedSurfaceOpen_not_biholomorphic_unitDisc X p hdisk)

/-- A coordinate disk centered at any prescribed surface point. -/
theorem exists_closedCoordinateDisk_centered
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    ∃ D : ClosedCoordinateDisk X,
      p ∈ D.expandedOpenDisk D.closedRadius ∧
        D.openDisk.chart p = D.openDisk.center := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hc_target : c ∈ e.target := e.map_source hp_source
  have htarget : e.target ∈ 𝓝 c := e.open_target.mem_nhds hc_target
  rcases Metric.mem_nhds_iff.mp htarget with ⟨R, hRpos, hball⟩
  let r : ℝ := R / 2
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  let D : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e (chart_mem_atlas ℂ p) c
      hrpos hrR hball
  refine ⟨D, ?_, rfl⟩
  refine ⟨hp_source, ?_⟩
  change dist (e p) c < r
  simpa [c] using hrpos

/-- The punctured surface and a centered coordinate disk cover the surface. -/
theorem puncturedSurfaceOpen_sup_centeredCoordinateDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (p : X) (D : ClosedCoordinateDisk X)
    (hp : p ∈ D.expandedOpenDisk D.closedRadius) :
    puncturedSurfaceOpen p ⊔
        ⟨D.expandedOpenDisk D.closedRadius,
          D.expandedOpenDisk_isOpen D.closedRadius⟩ = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_sup,
    TopologicalSpace.Opens.coe_top, Set.mem_union, Set.mem_univ, iff_true]
  by_cases hxp : x = p
  · right
    simpa [hxp] using hp
  · left
    exact hxp

/--
%%handwave
name:
  Nonzero compact-surface Mayer--Vietoris boundary
statement:
  For the cover of a compact Riemann surface by a once-punctured
  surface and a coordinate disk centered at the puncture, the degree-one
  Mayer--Vietoris connecting homomorphism from the annular overlap into second
  de Rham cohomology is injective.
proof:
  A positive compactly supported area form has nonzero cohomology class,
  because integration kills exact two-forms by Stokes' theorem.  Put its
  support in a coordinate disk lying in the exterior of another disk on the
  punctured surface.  Exterior mass transport makes its restriction there
  exact, while the Poincare lemma makes its restriction to the disk exact.
  Mayer--Vietoris exactness therefore places the nonzero class in the image of
  the connecting map.  First cohomology of the annular overlap is generated
  by any nonzero class, so the connecting map is injective.
-/
theorem compact_coordinatePuncture_mayerVietorisConnecting_injective
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [CompactSpace X] (p : X) (D : ClosedCoordinateDisk X)
    (hp : p ∈ D.expandedOpenDisk D.closedRadius)
    (hcenter : D.openDisk.chart p = D.openDisk.center) :
    let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
    let V : TopologicalSpace.Opens X :=
      ⟨D.expandedOpenDisk D.closedRadius,
        D.expandedOpenDisk_isOpen D.closedRadius⟩
    let hcover : U ⊔ V = ⊤ :=
      puncturedSurfaceOpen_sup_centeredCoordinateDisk p D hp
    Function.Injective
      (deRhamMayerVietorisConnectingOfPartitionOfUnity
        (A := ℝ) SurfaceRealModel U V hcover 1) := by
  classical
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  let V : TopologicalSpace.Opens X :=
    ⟨D.expandedOpenDisk D.closedRadius,
      D.expandedOpenDisk_isOpen D.closedRadius⟩
  let hcover : U ⊔ V = ⊤ :=
    puncturedSurfaceOpen_sup_centeredCoordinateDisk p D hp
  letI : RiemannSurface U :=
    puncturedSurfaceOpen_riemannSurface X p
  letI : NoncompactSpace U := puncturedSurfaceOpen_noncompact X p
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : SigmaCompactSpace X := by infer_instance
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩

  let u0 : U := Classical.choice (inferInstance : Nonempty U)
  obtain ⟨u1, _hu1univ, hu1ne⟩ :=
    exists_ne_mem_open_of_mem (X := U) isOpen_univ (Set.mem_univ u0)
  obtain ⟨K, _hu0int, _hKrad, _hKuniv, hu1K⟩ :=
    exists_closedCoordinateDisk_mem_interior_subset_open_avoids_point
      (X := U) isOpen_univ (Set.mem_univ u0) hu1ne
  have hu1Kc : u1 ∈ K.carrierᶜ := hu1K
  have hKcOpen : IsOpen K.carrierᶜ := K.compact.isClosed.isOpen_compl
  obtain ⟨u2, hu2Kc, hu2ne⟩ :=
    exists_ne_mem_open_of_mem hKcOpen hu1Kc
  obtain ⟨B, hu1Bint, _hBrad, hBKc, _hu2B⟩ :=
    exists_closedCoordinateDisk_mem_interior_subset_open_avoids_point
      hKcOpen hu1Kc hu2ne

  let S : Set X := Subtype.val '' interior B.carrier
  let C : Set X := Subtype.val '' B.carrier
  have hSopen : IsOpen S :=
    U.2.isOpenMap_subtype_val _ isOpen_interior
  have hCcompact : IsCompact C :=
    B.compact.image continuous_subtype_val
  have hSC : S ⊆ C := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, interior_subset hy, rfl⟩
  have hu1S : (u1 : X) ∈ S := ⟨u1, hu1Bint, rfl⟩
  obtain ⟨g⟩ := riemannSurface_has_smoothRiemannianMetric X
  obtain ⟨measureGeometry⟩ :=
    smoothRiemannianMetricOnSurface_induces_measure_geometry X g
  obtain ⟨omega, homegaPos, homegaZero⟩ :=
    exists_closedSurfaceTwoForm_integral_pos_supported_in_compact
      g measureGeometry S C hSopen hCcompact hSC (u1 : X) hu1S
  let omegaClass : DeRhamCohomology
      (I := SurfaceRealModel) (M := X) (A := ℝ) 2 :=
    (DeRhamExactClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 2).mkQ omega
  have homegaClass : omegaClass ≠ 0 := by
    apply surfaceTwoForm_deRhamClass_ne_zero_of_integral_ne_zero
      g measureGeometry omega
    exact ne_of_gt homegaPos

  obtain ⟨E⟩ := connected_noncompact_has_smoothRelativelyCompactExhaustion
    U (not_compactSpace_iff.mpr inferInstance)
  have hKexterior : IsExteriorComponent K.carrier K.carrierᶜ :=
    closedCoordinateDisk_complement_isExteriorComponent K
  let omegaU : SmoothForms
      (I := SurfaceRealModel) (M := U) ℝ 2 :=
    restrictSmoothFormsToOpen
      (I := SurfaceRealModel) (A := ℝ) U 2 omega.1
  have homegaUZero : ∀ x : U, x ∉ B.carrier → omegaU.toFun x = 0 := by
    intro x hxB
    apply restrictSmoothFormsToOpen_toFun_eq_zero_of_ambient_eq_zero
      SurfaceRealModel U omega.1 x
    apply homegaZero
    intro hxC
    rcases hxC with ⟨y, hyB, hyx⟩
    have hyEq : y = x := Subtype.ext hyx
    exact hxB (hyEq ▸ hyB)
  obtain ⟨thetaU, hthetaU⟩ :=
    hKexterior.exists_primitive_of_compactSupport
      E K.compact B.compact hBKc omegaU homegaUZero

  letI : Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := V) (A := ℝ) 2) := by
    rcases D.expandedOpenDisk_diffeomorphic_ball with ⟨phi⟩
    apply deRhamCohomology_subsingleton_of_diffeomorphic
      SurfaceRealModel (𝓘(ℝ, ℂ)) phi 2
    apply deRham_poincareLemma_convex_open
    · exact convex_ball D.openDisk.center D.closedRadius
    · exact ⟨D.openDisk.center,
        Metric.mem_ball_self D.closedRadius_pos⟩
  have homegaRestrictionU :
      deRhamCohomologyRestrictionToOpen
        (I := SurfaceRealModel) (M := X) (A := ℝ) U 2 omegaClass = 0 := by
    change (DeRhamExactClosedForms
      (I := SurfaceRealModel) (M := U) (A := ℝ) 2).mkQ
        (deRhamClosedFormsRestrictionToOpen
          (I := SurfaceRealModel) (M := X) (A := ℝ) U 2 omega) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change omegaU ∈ DeRhamExactForms
      (I := SurfaceRealModel) (M := U) (A := ℝ) 2
    rw [DeRhamExactForms]
    exact ⟨thetaU, hthetaU⟩
  have homegaRestrictionV :
      deRhamCohomologyRestrictionToOpen
        (I := SurfaceRealModel) (M := X) (A := ℝ) V 2 omegaClass = 0 :=
    Subsingleton.elim _ _
  have homegaRestriction :
      deRhamMayerVietorisRestriction
        (I := SurfaceRealModel) (A := ℝ) U V 2 omegaClass = 0 := by
    apply Prod.ext
    · exact homegaRestrictionU
    · exact homegaRestrictionV

  let connecting :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity
      (A := ℝ) SurfaceRealModel U V hcover 1
  have hexact :=
    deRham_mayerVietoris_exact_connecting_restriction_of_partitionOfUnity
      (A := ℝ) SurfaceRealModel U V hcover 1
  have hrange : omegaClass ∈ Set.range connecting :=
    (hexact omegaClass).mp homegaRestriction
  rcases hrange with ⟨tau, htauImage⟩
  have hconnectingZero : connecting 0 = 0 := by
    have hsmul :=
      deRhamMayerVietorisConnectingOfPartitionOfUnity_smul
        SurfaceRealModel U V hcover 1 (0 : ℝ) tau
    simpa [connecting] using hsmul
  have htau : tau ≠ 0 := by
    intro htauZero
    apply homegaClass
    rw [← htauImage, htauZero]
    exact hconnectingZero

  rcases D.puncturedExpandedOpenDisk_diffeomorphic_annularCylinder
      p hp hcenter with ⟨phi0⟩
  change Function.Injective connecting
  intro alpha beta hab
  let v : Circle := Classical.choice (inferInstance : Nonempty Circle)
  obtain ⟨a, ha⟩ :=
    deRhamH1_eq_smul_of_diffeomorphic_annularCylinder
      SurfaceRealModel phi0 v tau htau alpha
  obtain ⟨b, hb⟩ :=
    deRhamH1_eq_smul_of_diffeomorphic_annularCylinder
      SurfaceRealModel phi0 v tau htau beta
  rw [ha, hb] at hab
  have hsmulA :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity_smul
      SurfaceRealModel U V hcover 1 a tau
  have hsmulB :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity_smul
      SurfaceRealModel U V hcover 1 b tau
  change connecting (a • tau) = a • connecting tau at hsmulA
  change connecting (b • tau) = b • connecting tau at hsmulB
  have hab' : a • omegaClass = b • omegaClass := by
    rw [← htauImage]
    exact hsmulA.symm.trans (hab.trans hsmulB)
  have habZero : (a - b) • omegaClass = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hab'
  have habScalar : a = b := by
    apply sub_eq_zero.mp
    exact (smul_eq_zero.mp habZero).resolve_right homegaClass
  rw [ha, hb, habScalar]

/--
%%handwave
name:
  Vanishing first cohomology after deleting one point
statement:
  If a compact Riemann surface has vanishing first real de Rham
  cohomology, then deleting any one point again gives a surface with vanishing
  first real de Rham cohomology.
proof:
  Cover the compact surface by the punctured surface and a coordinate disk at
  the deleted point.  Their intersection is an annulus.  The disk has zero
  first cohomology, and the annular connecting map into second cohomology is
  injective.  Mayer--Vietoris exactness therefore forces the restriction of
  every punctured-surface class to the annulus to vanish.  Ambient vanishing
  makes this restriction injective, so the original class vanishes.
-/
theorem compact_deRhamH1Zero_puncturedSurfaceOpen
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [CompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (p : X) :
    Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := puncturedSurfaceOpen p) (A := ℝ) 1) := by
  rcases exists_closedCoordinateDisk_centered X p with ⟨D, hp, hcenter⟩
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  let V : TopologicalSpace.Opens X :=
    ⟨D.expandedOpenDisk D.closedRadius,
      D.expandedOpenDisk_isOpen D.closedRadius⟩
  let hcover : U ⊔ V = ⊤ :=
    puncturedSurfaceOpen_sup_centeredCoordinateDisk p D hp
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : SigmaCompactSpace X := by infer_instance
  letI : Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := V) (A := ℝ) 1) := by
    simpa [V] using D.expandedOpenDisk_deRhamH1_subsingleton
  apply deRhamH1_left_subsingleton_of_connecting_injective
    SurfaceRealModel U V hcover
  exact compact_coordinatePuncture_mayerVietorisConnecting_injective
    X p D hp hcenter

/--
%%handwave
name:
  Compact zero-cohomology uniformization
statement:
  Every compact Riemann surface with vanishing first real de Rham
  cohomology is biholomorphic to the Riemann sphere.
proof:
  Delete one point.  The punctured surface still has vanishing first
  cohomology and is noncompact, so open-surface uniformization identifies it
  with either the plane or the disk.  A disk coordinate would be a bounded
  holomorphic function and hence would extend across the puncture; compactness
  would then make it constant.  Thus the punctured surface is the plane, and
  adjoining the deleted point gives the Riemann sphere.
-/
theorem compact_deRhamH1Zero_biholomorphic_riemannSphere
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [CompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)] :
    BiholomorphicSurfaces X RiemannSphere := by
  inhabit X
  exact compact_deRhamH1Zero_biholomorphic_riemannSphere_of_punctured
    X default (compact_deRhamH1Zero_puncturedSurfaceOpen X default)

/--
%%handwave
name:
  Uniformization of simply connected Riemann surfaces
statement:
  Every simply connected Riemann surface is biholomorphic to the Riemann
  sphere, the complex plane, or the unit disk.
proof:
  Integrate closed real one-forms from a base point.  A finite-grid homotopy
  argument makes the integral path-independent, so every closed one-form is
  exact and first real de Rham cohomology vanishes.  If the surface is compact,
  compact zero-cohomology uniformization gives the Riemann sphere.  Otherwise,
  open-surface zero-cohomology uniformization gives either the complex plane
  or the unit disk.
-/
theorem simplyConnected_riemannSurface_uniformization
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X] :
    BiholomorphicSurfaces X RiemannSphere ∨
      BiholomorphicSurfaces X ℂ ∨
        BiholomorphicSurfaces X Complex.UnitDisc := by
  classical
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  letI : Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1) :=
    simplyConnected_surface_deRhamH1_zero (X := X)
  by_cases hcompact : CompactSpace X
  · letI : CompactSpace X := hcompact
    exact Or.inl (compact_deRhamH1Zero_biholomorphic_riemannSphere X)
  · letI : NoncompactSpace X := not_compactSpace_iff.mp hcompact
    rcases
        noncompact_deRhamH1Zero_biholomorphic_complexPlane_or_unitDisc X with
      hplane | hdisk
    · exact Or.inr (Or.inl hplane)
    · exact Or.inr (Or.inr hdisk)

end JJMath.Uniformization
