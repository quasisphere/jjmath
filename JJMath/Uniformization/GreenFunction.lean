import JJMath.Uniformization.EvansPotential
import JJMath.Uniformization.GreenFunctionCompactSuperlevel
import JJMath.Uniformization.GreenFunctionCore
import JJMath.Uniformization.H1ZeroExhaustion
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Order.Field

/-!
# Green-function route to uniformization

This file records the high-level formalization targets for proving the
hyperbolic case of uniformization by constructing Green functions with one
pole and exponentiating their harmonic conjugates.
-/

namespace JJMath

open scoped _root_.Manifold _root_.Topology ContDiff

namespace Uniformization




/--
%%handwave
name:
  Unbranched holomorphic plane maps are local homeomorphisms
statement:
  A holomorphic map from a Riemann surface to the complex plane whose
  coordinate derivative is nonzero at every point is a local homeomorphism.
proof:
  In a source coordinate the map is a holomorphic function of one complex
  variable with nonzero derivative.  The inverse function theorem gives a
  local inverse in the coordinate plane, and composing with the source chart
  gives a local homeomorphism on the surface.
-/
theorem unbranched_holomorphicPlaneMap_isLocalHomeomorph
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx F ≠ 0) :
    IsLocalHomeomorph F := by
  classical
  refine IsLocalHomeomorph.mk F ?_
  intro x
  let χx : PointedSurfaceCoordinate X x :=
    { chart := chartAt ℂ x
      chart_mem_atlas := chart_mem_atlas ℂ x
      base_mem_source := mem_chart_source ℂ x }
  let e : OpenPartialHomeomorph X ℂ := χx.chart
  let a : ℂ := e x
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ F (e.symm z)
  have ha_target : a ∈ e.target := by
    dsimp [a, e, χx]
    exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hdiff_on : DifferentiableOn ℂ fcoord e.target := by
    simpa [fcoord, e] using
      differentiableOn_surfaceCoordinate_symm
        (X := X) hF χx
  have hcontdiff_on :
      ContDiffOn ℂ (1 : WithTop ℕ∞) fcoord e.target :=
    hdiff_on.contDiffOn e.open_target
  have hcontdiff_at :
      ContDiffAt ℂ (1 : WithTop ℕ∞) fcoord a :=
    hcontdiff_on.contDiffAt (e.open_target.mem_nhds ha_target)
  have hdiff_at : DifferentiableAt ℂ fcoord a :=
    (hdiff_on a ha_target).differentiableAt
      (e.open_target.mem_nhds ha_target)
  have hderiv_at : HasDerivAt fcoord (deriv fcoord a) a :=
    hdiff_at.hasDerivAt
  have hstrict : HasStrictDerivAt fcoord (deriv fcoord a) a :=
    hcontdiff_at.hasStrictDerivAt' hderiv_at one_ne_zero
  have hderiv_ne : deriv fcoord a ≠ 0 := by
    simpa [surfaceComplexDerivativeInCoordinate, χx, e, a, fcoord] using
      hunbranched x χx
  let einv : OpenPartialHomeomorph ℂ ℂ :=
    (hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      fcoord
  have ha_einv : a ∈ einv.source := by
    simpa [einv] using
      HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
        (hstrict.hasStrictFDerivAt_equiv hderiv_ne)
  let E : OpenPartialHomeomorph X ℂ := e.trans einv
  refine ⟨E, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨χx.base_mem_source, ha_einv⟩
  · intro y hy
    have hy_source : y ∈ e.source := by
      have hy_e_trans : y ∈ (e.trans einv).source := hy
      rw [OpenPartialHomeomorph.trans_source] at hy_e_trans
      exact hy_e_trans.1
    calc
      F y = einv (e y) := by
        simp [einv, fcoord, e.left_inv hy_source]
      _ = E y := rfl

/--
%%handwave
name:
  Inverses of bijective unbranched plane maps are holomorphic
statement:
  The inverse homeomorphism of a bijective unbranched holomorphic map from a
  Riemann surface to the complex plane is holomorphic.
proof:
  Around each image point, use the one-variable inverse function theorem in a
  source coordinate.  The resulting holomorphic inverse branch agrees with the
  global inverse because the original map is injective.
-/
theorem bijective_unbranched_holomorphicPlaneMap_inverse_holomorphic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx F ≠ 0)
    (hinj : Function.Injective F)
    (hsurj : Function.Surjective F) :
    HolomorphicMap ℂ X
      ((unbranched_holomorphicPlaneMap_isLocalHomeomorph X F hF hunbranched).toHomeomorphOfBijective
        ⟨hinj, hsurj⟩).symm := by
  classical
  let hlocal : IsLocalHomeomorph F :=
    unbranched_holomorphicPlaneMap_isLocalHomeomorph X F hF hunbranched
  let H : X ≃ₜ ℂ :=
    hlocal.toHomeomorphOfBijective ⟨hinj, hsurj⟩
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H.symm
  intro z
  let x : X := H.symm z
  have hxF : F x = z := by
    change H x = z
    exact H.apply_symm_apply z
  let χx : PointedSurfaceCoordinate X x :=
    { chart := chartAt ℂ x
      chart_mem_atlas := chart_mem_atlas ℂ x
      base_mem_source := mem_chart_source ℂ x }
  let e : OpenPartialHomeomorph X ℂ := χx.chart
  let a : ℂ := e x
  let fcoord : ℂ → ℂ := fun w : ℂ ↦ F (e.symm w)
  have ha_target : a ∈ e.target := by
    dsimp [a, e, χx]
    exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hfa : fcoord a = z := by
    have hleft : e.symm (e x) = x := e.left_inv χx.base_mem_source
    simpa [fcoord, a, hleft] using hxF
  have hdiff_on : DifferentiableOn ℂ fcoord e.target := by
    simpa [fcoord, e] using
      differentiableOn_surfaceCoordinate_symm
        (X := X) hF χx
  have hcontdiff_on :
      ContDiffOn ℂ (1 : WithTop ℕ∞) fcoord e.target :=
    hdiff_on.contDiffOn e.open_target
  have hcontdiff_at :
      ContDiffAt ℂ (1 : WithTop ℕ∞) fcoord a :=
    hcontdiff_on.contDiffAt (e.open_target.mem_nhds ha_target)
  have hdiff_at : DifferentiableAt ℂ fcoord a :=
    (hdiff_on a ha_target).differentiableAt
      (e.open_target.mem_nhds ha_target)
  have hderiv_at : HasDerivAt fcoord (deriv fcoord a) a :=
    hdiff_at.hasDerivAt
  have hstrict : HasStrictDerivAt fcoord (deriv fcoord a) a :=
    hcontdiff_at.hasStrictDerivAt' hderiv_at one_ne_zero
  have hderiv_ne : deriv fcoord a ≠ 0 := by
    simpa [surfaceComplexDerivativeInCoordinate, χx, e, a, fcoord] using
      hunbranched x χx
  let einv : OpenPartialHomeomorph ℂ ℂ :=
    (hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      fcoord
  have ha_einv : a ∈ einv.source := by
    simpa [einv] using
      HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
        (hstrict.hasStrictFDerivAt_equiv hderiv_ne)
  have hinv_strict :
      HasStrictDerivAt einv.symm (deriv fcoord a)⁻¹ (fcoord a) := by
    simpa [einv] using hstrict.to_localInverse hderiv_ne
  have hinv_diff_at_z : DifferentiableAt ℂ einv.symm z := by
    have hinv_diff_at_fa : DifferentiableAt ℂ einv.symm (fcoord a) :=
      hinv_strict.hasDerivAt.differentiableAt
    simpa [hfa] using hinv_diff_at_fa
  have hinv_mdiff_at_z :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) einv.symm z :=
    hinv_diff_at_z.mdifferentiableAt
  have hinv_at_z : einv.symm z = a := by
    have hleft : einv.symm (einv a) = a := einv.left_inv ha_einv
    simpa [einv, hfa] using hleft
  have he_symm_mdiff_at_a :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm a :=
    mdifferentiableAt_atlas_symm χx.chart_mem_atlas ha_target
  have he_symm_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm (einv.symm z) := by
    simpa [hinv_at_z] using he_symm_mdiff_at_a
  let branch : ℂ → X :=
    fun w : ℂ ↦ e.symm (einv.symm w)
  have hbranch_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) branch z := by
    simpa [branch] using
      he_symm_mdiff.comp z hinv_mdiff_at_z
  have hright :
      ∀ᶠ w in 𝓝 (fcoord a), fcoord (einv.symm w) = w := by
    filter_upwards
      [einv.open_target.mem_nhds (einv.map_source ha_einv)] with w hw
    exact einv.right_inv hw
  have hright_at_z :
      ∀ᶠ w in 𝓝 z, fcoord (einv.symm w) = w := by
    simpa [hfa] using hright
  have hevent :
      (fun w : ℂ ↦ H.symm w) =ᶠ[𝓝 z] branch := by
    filter_upwards [hright_at_z] with w hw
    have hFbranch : F (branch w) = w := by
      simpa [branch, fcoord] using hw
    have hHbranch : H (branch w) = w := by
      simpa [H, hlocal] using hFbranch
    exact (H.symm_apply_eq).2 hHbranch.symm
  exact hbranch_mdiff.congr_of_eventuallyEq hevent

/--
%%handwave
name:
  Bijective unbranched holomorphic plane maps are biholomorphic
statement:
  A bijective holomorphic map from a Riemann surface to the complex
  plane, with nonzero derivative everywhere, is biholomorphic.
proof:
  The local inverse theorem gives holomorphic inverse branches.  Bijectivity
  glues these local branches into the inverse homeomorphism, hence the inverse
  is holomorphic.
-/
theorem biholomorphicToComplexPlane_of_bijective_unbranched_holomorphicPlaneMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx F ≠ 0)
    (hinj : Function.Injective F)
    (hsurj : Function.Surjective F) :
    BiholomorphicToComplexPlane X := by
  let hloc : IsLocalHomeomorph F :=
    unbranched_holomorphicPlaneMap_isLocalHomeomorph X F hF hunbranched
  let e : X ≃ₜ ℂ :=
    hloc.toHomeomorphOfBijective ⟨hinj, hsurj⟩
  refine ⟨{
    toHomeomorph := e
    holomorphic_toFun := ?_
    holomorphic_invFun := ?_
  }⟩
  · simpa [e, hloc] using hF
  · simpa [e, hloc] using
      bijective_unbranched_holomorphicPlaneMap_inverse_holomorphic
        X F hF hunbranched hinj hsurj

/--
%%handwave
name:
  A proper pointed disk map with one simple zero has degree one
statement:
  A proper pointed holomorphic disk map whose fiber over \(0\) consists of one
  simple zero has degree one.
proof:
  Proper holomorphic maps between Riemann surfaces have constant
  finite degree.  The fiber over \(0\) consists of the single marked point, and
  the derivative condition says that this point contributes multiplicity one.
-/
theorem proper_pointedDiskMap_degree_one_of_simple_single_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hproper : IsProperMap F.toFun)
    (hzero : ∀ x : X, (((F.toFun x : Complex.UnitDisc) : ℂ) = 0) ↔ x = p)
    (hsimple : ∀ χ : PointedSurfaceCoordinate X p,
      surfaceComplexDerivativeInCoordinate χ
        (fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)) ≠ 0) :
    ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z := by
  classical
  have hφ_open :
      Topology.IsOpenEmbedding (fun z : Complex.UnitDisc ↦ (z : ℂ)) := by
    simpa using
      ((Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal)
  have _hp_multiplicity_one :
      ∀ χ : PointedSurfaceCoordinate X p,
        holomorphicMapLocalMultiplicityAtValueInCoordinate χ
          (fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)) 0 = 1 := by
    intro χ
    exact
      holomorphicMapLocalMultiplicityAtValueInCoordinate_eq_one_of_deriv_ne_zero
        χ F.holomorphic_coe_unitDisc ((hzero p).mpr rfl) (hsimple χ)
  exact
    proper_holomorphicMap_degree_one_of_simple_single_zero_to_openComplexModel
      (X := X) (Y := Complex.UnitDisc) (p := p) (F := F.toFun)
      (φ := fun z : Complex.UnitDisc ↦ (z : ℂ))
      hφ_open F.holomorphic_coe_unitDisc hproper hzero _hp_multiplicity_one

/--
%%handwave
name:
  Spherical universal cover
statement:
  A Riemann surface has spherical universal cover when each based
  universal cover is biholomorphic to the Riemann sphere.
-/
def HasSphericalUniversalCover (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  ∀ x₀ : X,
    @BiholomorphicSurfaces (PathHomotopyUniversalCover X x₀) RiemannSphere
      inferInstance inferInstance inferInstance inferInstance

/--
%%handwave
name:
  The sphere and plane are not biholomorphic
statement:
  No Riemann surface is biholomorphic both to the Riemann sphere and to the
  complex plane.
proof:
  A biholomorphism is in particular a homeomorphism.  The Riemann sphere is
  compact, while the complex plane is not compact.
tags:
  milestone
-/
theorem not_biholomorphicToRiemannSphere_and_complexPlane
    (Y : Type) [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    BiholomorphicSurfaces Y RiemannSphere → ¬ BiholomorphicToComplexPlane Y := by
  intro hsphere hplane
  rcases hsphere with ⟨eSphere⟩
  rcases hplane with ⟨ePlane⟩
  letI : CompactSpace Y := Homeomorph.compactSpace eSphere.toHomeomorph.symm
  letI : CompactSpace ℂ := Homeomorph.compactSpace ePlane.toHomeomorph
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℂ)) inferInstance

/--
%%handwave
name:
  The sphere and upper half-plane are not biholomorphic
statement:
  No Riemann surface is biholomorphic both to the Riemann sphere and to the
  upper half-plane.
proof:
  A biholomorphism is in particular a homeomorphism.  The Riemann sphere is
  compact, while the upper half-plane is not compact.
tags:
  milestone
-/
theorem not_biholomorphicToRiemannSphere_and_upperHalfPlane
    (Y : Type) [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    BiholomorphicSurfaces Y RiemannSphere → ¬ BiholomorphicToUpperHalfPlane Y := by
  intro hsphere hupper
  rcases hsphere with ⟨eSphere⟩
  rcases hupper with ⟨eUpper⟩
  letI : CompactSpace Y := Homeomorph.compactSpace eSphere.toHomeomorph.symm
  letI : CompactSpace UpperHalfPlane := Homeomorph.compactSpace eUpper.toHomeomorph
  exact
    (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace UpperHalfPlane))
      inferInstance

/--
%%handwave
name:
  Bounded nonconstant holomorphic functions pull back
statement:
  A biholomorphism pulls bounded nonconstant holomorphic functions back to
  bounded nonconstant holomorphic functions.
proof:
  Compose the function with the biholomorphic equivalence.  Holomorphicity
  follows by composition, and the range is unchanged because the underlying
  homeomorphism is surjective.
-/
theorem biholomorphicSurfaces_preserves_bounded_nonconstant_holomorphicFunction
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (hXY : BiholomorphicSurfaces X Y)
    (hY : HasBoundedNonconstantHolomorphicFunction Y) :
    HasBoundedNonconstantHolomorphicFunction X := by
  rcases hXY with ⟨e⟩
  rcases hY with ⟨f, hf, hbdd, hnonconstant⟩
  refine ⟨fun x : X ↦ f (e.toHomeomorph x), ?_, ?_, ?_⟩
  · change HolomorphicMap X ℂ (f ∘ e.toHomeomorph)
    exact hf.comp e.holomorphic_toFun
  · have hrange :
        Set.range (fun x : X ↦ f (e.toHomeomorph x)) = Set.range f := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨e.toHomeomorph x, rfl⟩
      · rintro ⟨y, rfl⟩
        rcases e.toHomeomorph.surjective y with ⟨x, hx⟩
        exact ⟨x, by simp [hx]⟩
    rwa [hrange]
  · have hrange :
        Set.range (fun x : X ↦ f (e.toHomeomorph x)) = Set.range f := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨e.toHomeomorph x, rfl⟩
      · rintro ⟨y, rfl⟩
        rcases e.toHomeomorph.surjective y with ⟨x, hx⟩
        exact ⟨x, by simp [hx]⟩
    rwa [hrange]

/--
%%handwave
name:
  The plane has no bounded nonconstant holomorphic functions
statement:
  Every bounded holomorphic function on the complex plane is constant.
proof:
  This is Mathlib's Liouville theorem.
-/
theorem complexPlane_has_no_bounded_nonconstant_holomorphicFunction :
    ¬ HasBoundedNonconstantHolomorphicFunction ℂ := by
  rintro ⟨f, hf, hbdd, hnonconstant⟩
  have hdiff : Differentiable ℂ f :=
    (show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f from hf).differentiable
  have hsubsingleton : (Set.range f).Subsingleton := by
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
    exact hdiff.apply_eq_apply_of_bounded hbdd z w
  exact hnonconstant.not_subsingleton hsubsingleton

/--
%%handwave
name:
  The Cayley transform maps the upper half-plane into the unit disk
statement:
  For every \(z\) in the upper half-plane,
  \[
    \left|\frac{z-i}{z+i}\right|<1.
  \]
proof:
  The denominator is nonzero because \(\operatorname{Im}z>0\).  Squaring the
  two norms reduces the inequality
  \(|z-i|<|z+i|\) to
  \((\operatorname{Im}z-1)^2<
    (\operatorname{Im}z+1)^2\), which follows from
  \(\operatorname{Im}z>0\).
-/
private theorem green_upperHalfPlane_cayley_norm_lt_one (z : UpperHalfPlane) :
    ‖((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)‖ < 1 := by
  have hden : (z : ℂ) + Complex.I ≠ 0 := by
    intro hzero
    have him : ((z : ℂ) + Complex.I).im = 0 := by rw [hzero]; simp
    have : z.im + 1 = 0 := by simpa [UpperHalfPlane.coe_im] using him
    linarith [z.im_pos]
  rw [Complex.norm_div]
  refine (div_lt_one (norm_pos_iff.mpr hden)).2 ?_
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith [z.im_pos]

/--
%%handwave
name:
  The upper half-plane has a bounded nonconstant holomorphic function
statement:
  The upper half-plane carries a bounded nonconstant holomorphic complex-valued
  function.
proof:
  Use \(z\mapsto (z-i)/(z+i)\).  It is holomorphic on the upper half-plane
  because the denominator is nonzero there, and
  [its absolute value is strictly less than one](lean:JJMath.Uniformization.upperHalfPlane_cayley_norm_lt_one).  It is
  not constant, since it sends \(i\) to \(0\) but does not send \(1+i\) to
  \(0\).
-/
theorem upperHalfPlane_has_bounded_nonconstant_holomorphicFunction :
    HasBoundedNonconstantHolomorphicFunction UpperHalfPlane := by
  let f : UpperHalfPlane → ℂ :=
    fun z ↦ ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)
  refine ⟨f, ?_, ?_, ?_⟩
  · change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f
    rw [UpperHalfPlane.mdifferentiable_iff]
    let g : ℂ → ℂ := fun z ↦ (z - Complex.I) / (z + Complex.I)
    have hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im} := by
      have hnum : DifferentiableOn ℂ (fun z : ℂ ↦ z - Complex.I)
          {z : ℂ | 0 < z.im} :=
        (differentiable_id.sub (differentiable_const (c := Complex.I))).differentiableOn
      have hden_diff : DifferentiableOn ℂ (fun z : ℂ ↦ z + Complex.I)
          {z : ℂ | 0 < z.im} :=
        (differentiable_id.add (differentiable_const (c := Complex.I))).differentiableOn
      exact hnum.div hden_diff (by
        intro z hz hzero
        have him : (z + Complex.I).im = 0 := by rw [hzero]; simp
        have : z.im + 1 = 0 := by simpa using him
        have hzpos : 0 < z.im := hz
        linarith)
    exact hg.congr (by
      intro z hz
      simp [f, g, UpperHalfPlane.ofComplex_apply_of_im_pos hz])
  · exact isBounded_iff_forall_norm_le.2
      ⟨1, by
        rintro _ ⟨z, rfl⟩
        exact le_of_lt (green_upperHalfPlane_cayley_norm_lt_one z)⟩
  · let w : UpperHalfPlane := (1 : ℝ) +ᵥ UpperHalfPlane.I
    refine Set.nontrivial_of_mem_mem_ne
      (show (0 : ℂ) ∈ Set.range f from
        ⟨UpperHalfPlane.I, by simp [f]⟩)
      (show f w ∈ Set.range f from ⟨w, rfl⟩)
      ?_
    have hnum : ((w : ℂ) - Complex.I) ≠ 0 := by
      simp [w]
    have hden : ((w : ℂ) + Complex.I) ≠ 0 := by
      apply ne_of_apply_ne Complex.im
      simp [w]
    exact (div_ne_zero hnum hden).symm

/--
%%handwave
name:
  The plane and upper half-plane are not biholomorphic
statement:
  No Riemann surface is biholomorphic both to the complex plane and to the
  upper half-plane.
proof:
  The
  [upper half-plane has nonconstant bounded holomorphic functions](lean:JJMath.Uniformization.upperHalfPlane_has_bounded_nonconstant_holomorphicFunction),
  while [the complex plane has none](lean:JJMath.Uniformization.complexPlane_has_no_bounded_nonconstant_holomorphicFunction)
  by Liouville's theorem.  Pulling such a function back along a biholomorphism
  would contradict this.
tags:
  milestone
-/
theorem not_biholomorphicToComplexPlane_and_upperHalfPlane
    (Y : Type) [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    BiholomorphicToComplexPlane Y → ¬ BiholomorphicToUpperHalfPlane Y := by
  intro hplane hupper
  rcases hplane with ⟨ePlane⟩
  rcases hupper with ⟨eUpper⟩
  let ePlaneInv : Biholomorphic ℂ Y :=
    { toHomeomorph := ePlane.toHomeomorph.symm
      holomorphic_toFun := ePlane.holomorphic_invFun
      holomorphic_invFun := ePlane.holomorphic_toFun }
  have hCUpper : BiholomorphicSurfaces ℂ UpperHalfPlane :=
    ⟨ePlaneInv.trans eUpper⟩
  exact complexPlane_has_no_bounded_nonconstant_holomorphicFunction
    (biholomorphicSurfaces_preserves_bounded_nonconstant_holomorphicFunction
      hCUpper upperHalfPlane_has_bounded_nonconstant_holomorphicFunction)

/--
%%handwave
name:
  Standard universal covers are mutually exclusive
statement:
  The spherical, parabolic, and hyperbolic universal-cover alternatives are
  mutually exclusive.
proof:
  The sphere is compact while the complex plane and upper half-plane are not.
  The complex plane is parabolic: every bounded holomorphic function on it is
  constant.  The upper half-plane has nonconstant bounded holomorphic
  functions, for instance the Cayley disk coordinate.  Biholomorphic
  equivalence preserves compactness and bounded holomorphic function theory,
  so no two alternatives can hold at once.
-/
theorem uniformizing_universal_cover_models_mutually_exclusive
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    (HasSphericalUniversalCover X →
        ¬ HasParabolicUniversalCover X ∧ ¬ HasUpperHalfPlaneUniformizingCover X) ∧
      (HasParabolicUniversalCover X →
        ¬ HasSphericalUniversalCover X ∧ ¬ HasUpperHalfPlaneUniformizingCover X) ∧
        (HasUpperHalfPlaneUniformizingCover X →
          ¬ HasSphericalUniversalCover X ∧ ¬ HasParabolicUniversalCover X) := by
  classical
  letI : PathConnectedSpace X := inferInstance
  rcases (inferInstance : PathConnectedSpace X).nonempty with ⟨x₀⟩
  constructor
  · intro hsphere
    constructor
    · intro hplane
      exact
        (not_biholomorphicToRiemannSphere_and_complexPlane
          (PathHomotopyUniversalCover X x₀) (hsphere x₀)) (hplane x₀)
    · intro hupper
      exact
        (not_biholomorphicToRiemannSphere_and_upperHalfPlane
          (PathHomotopyUniversalCover X x₀) (hsphere x₀)) (hupper x₀)
  · constructor
    · intro hplane
      constructor
      · intro hsphere
        exact
          (not_biholomorphicToRiemannSphere_and_complexPlane
            (PathHomotopyUniversalCover X x₀) (hsphere x₀)) (hplane x₀)
      · intro hupper
        exact
          (not_biholomorphicToComplexPlane_and_upperHalfPlane
            (PathHomotopyUniversalCover X x₀) (hplane x₀)) (hupper x₀)
    · intro hupper
      constructor
      · intro hsphere
        exact
          (not_biholomorphicToRiemannSphere_and_upperHalfPlane
            (PathHomotopyUniversalCover X x₀) (hsphere x₀)) (hupper x₀)
      · intro hplane
        exact
          (not_biholomorphicToComplexPlane_and_upperHalfPlane
            (PathHomotopyUniversalCover X x₀) (hplane x₀)) (hupper x₀)

end Uniformization

end JJMath
