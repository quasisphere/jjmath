import JJMath.Uniformization.Classification.HolomorphicCover
import JJMath.Uniformization.PuncturedGreenConjugate
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Geometry.Manifold.Instances.Quotient

/-!
# Standard parabolic Riemann surfaces

This file defines the punctured plane and translation quotients of the complex
plane by full lattices.  It also records the topology and covering map supplied
by Mathlib's properly discontinuous quotient construction.
-/

namespace JJMath

open scoped Manifold Topology ContDiff

namespace Uniformization

/-- The complex cylinder, modelled as the punctured complex plane. -/
noncomputable abbrev ComplexCylinder := puncturedSurfaceOpen (0 : ℂ)

/--
%%handwave
name: Exponential covering of the complex cylinder
statement:
  Define the covering projection
  $\exp:\mathbb C\to\mathbb C^\times$ by $z\mapsto e^z$.
-/
noncomputable def complexExponentialCover : ℂ → ComplexCylinder :=
  fun z ↦ ⟨Complex.exp z, Complex.exp_ne_zero z⟩

/--
%%handwave
name:
  The exponential map is a covering of the punctured plane
statement:
  The map $z\mapsto e^z$ from $\mathbb C$ to $\mathbb C^\times$ is a
  topological covering map.
proof:
  This is the standard exponential covering theorem, with the nonvanishing
  value packaged as a point of the punctured plane.
-/
theorem complexExponentialCover_isCoveringMap :
    IsCoveringMap complexExponentialCover := by
  simpa [complexExponentialCover, ComplexCylinder, puncturedSurfaceOpen] using
    Complex.isCoveringMap_exp

/--
%%handwave
name:
  The exponential projection is holomorphic
statement:
  The map $z\mapsto e^z$ from $\mathbb C$ to $\mathbb C^\times$ is
  holomorphic.
proof:
  The complex exponential is entire and never vanishes, so it factors
  holomorphically through the punctured plane.
-/
theorem complexExponentialCover_holomorphic :
    HolomorphicMap ℂ ComplexCylinder complexExponentialCover := by
  have hcoe :
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
        (((↑) : ComplexCylinder → ℂ) ∘ complexExponentialCover) := by
    rw [contMDiff_iff_contDiff]
    simpa [complexExponentialCover, Function.comp_def] using
      (Complex.contDiff_exp (𝕜 := ℂ) (n := ∞))
  have hcylinder :
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
        complexExponentialCover :=
    (ContMDiff.subtypeVal_comp_iff
      (puncturedSurfaceOpen (0 : ℂ)) complexExponentialCover).mp hcoe
  exact hcylinder.mdifferentiable (by simp)

/--
%%handwave
name:
  The exponential map holomorphically covers the punctured plane
statement:
  The map $\exp:\mathbb C\to\mathbb C^\times$ is a holomorphic covering
  map.
proof:
  Use the standard exponential covering theorem and the holomorphicity of the
  complex exponential, restricted to its nonzero range.
tags:
  milestone
-/
theorem complexExponentialCover_isHolomorphicCoveringMap :
    IsHolomorphicCoveringMap complexExponentialCover :=
  ⟨complexExponentialCover_isCoveringMap, complexExponentialCover_holomorphic⟩

/--
%%handwave
name:
  The punctured-plane inclusion is holomorphic
statement:
  The inclusion $\mathbb C^\times\hookrightarrow\mathbb C$ is holomorphic.
proof:
  The punctured plane is an open complex submanifold of the plane, and the
  inclusion is the open embedding that defines its complex structure.
-/
theorem complexCylinder_coe_holomorphic :
    HolomorphicMap ComplexCylinder ℂ (fun z : ComplexCylinder ↦ (z : ℂ)) := by
  exact
    (contMDiff_subtype_val
      (I := modelWithCornersSelf ℂ ℂ)
      (U := puncturedSurfaceOpen (0 : ℂ))
      (n := (1 : WithTop ℕ∞))).mdifferentiable one_ne_zero

/--
%%handwave
name:
  A holomorphic homeomorphism onto the punctured plane is biholomorphic
statement:
  If a Riemann surface $X$ is carried homeomorphically onto
  $\mathbb C^\times$ by a holomorphic map, then that homeomorphism and its
  inverse are holomorphic.
proof:
  After inclusion into $\mathbb C$, the map is an injective holomorphic
  function, so its coordinate derivative never vanishes. The complex inverse
  function theorem supplies a holomorphic inverse branch at every point of
  the punctured plane. Each branch agrees locally with the inverse
  homeomorphism.
-/
theorem biholomorphicSurfaces_complexCylinder_of_homeomorph_holomorphic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (H : X ≃ₜ ComplexCylinder)
    (hH : HolomorphicMap X ComplexCylinder H) :
    BiholomorphicSurfaces X ComplexCylinder := by
  classical
  let F : X → ℂ := fun x ↦ (H x : ℂ)
  have hF : HolomorphicMap X ℂ F := by
    exact complexCylinder_coe_holomorphic.comp hH
  have hF_injective : Function.Injective F := by
    intro x y hxy
    apply H.injective
    exact Subtype.ext hxy
  have hunbranched :
      ∀ x : X, ∀ chi : PointedSurfaceCoordinate X x,
        surfaceComplexDerivativeInCoordinate chi F ≠ 0 := by
    intro x chi
    exact injective_holomorphicMap_surfaceComplexDerivative_ne_zero
      chi hF hF_injective
  refine ⟨{
    toHomeomorph := H
    holomorphic_toFun := hH
    holomorphic_invFun := ?_
  }⟩
  change MDifferentiable (modelWithCornersSelf ℂ ℂ)
    (modelWithCornersSelf ℂ ℂ) H.symm
  intro z
  let x : X := H.symm z
  have hxH : H x = z := by
    exact H.apply_symm_apply z
  let chi : PointedSurfaceCoordinate X x :=
    { chart := chartAt ℂ x
      chart_mem_atlas := chart_mem_atlas ℂ x
      base_mem_source := mem_chart_source ℂ x }
  let e : OpenPartialHomeomorph X ℂ := chi.chart
  let a : ℂ := e x
  let fcoord : ℂ → ℂ := fun w : ℂ ↦ F (e.symm w)
  have ha_target : a ∈ e.target := by
    dsimp [a, e, chi]
    exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hfa : fcoord a = (z : ℂ) := by
    have hleft : e.symm (e x) = x := e.left_inv chi.base_mem_source
    simpa [fcoord, a, F, hleft] using
      congrArg ((↑) : ComplexCylinder → ℂ) hxH
  have hdiff_on : DifferentiableOn ℂ fcoord e.target := by
    simpa [fcoord, e] using
      differentiableOn_surfaceCoordinate_symm (X := X) hF chi
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
    simpa [surfaceComplexDerivativeInCoordinate, chi, e, a, fcoord] using
      hunbranched x chi
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
  have hinv_diff_at_z : DifferentiableAt ℂ einv.symm (z : ℂ) := by
    have hinv_diff_at_fa : DifferentiableAt ℂ einv.symm (fcoord a) :=
      hinv_strict.hasDerivAt.differentiableAt
    simpa [hfa] using hinv_diff_at_fa
  have hinv_mdiff_at_z :
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) einv.symm (z : ℂ) :=
    hinv_diff_at_z.mdifferentiableAt
  have hinv_at_z : einv.symm (z : ℂ) = a := by
    have hleft : einv.symm (einv a) = a := einv.left_inv ha_einv
    simpa [einv, hfa] using hleft
  have he_symm_mdiff_at_a :
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) e.symm a :=
    mdifferentiableAt_atlas_symm chi.chart_mem_atlas ha_target
  have he_symm_mdiff :
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ)
        e.symm (einv.symm (z : ℂ)) := by
    simpa [hinv_at_z] using he_symm_mdiff_at_a
  let branch : ComplexCylinder → X :=
    fun w : ComplexCylinder ↦ e.symm (einv.symm (w : ℂ))
  have hcoe_mdiff :
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ)
        (fun w : ComplexCylinder ↦ (w : ℂ)) z :=
    complexCylinder_coe_holomorphic z
  have hbranch_mdiff :
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) branch z := by
    simpa [branch] using
      he_symm_mdiff.comp z (hinv_mdiff_at_z.comp z hcoe_mdiff)
  have hright :
      ∀ᶠ w in nhds (fcoord a), fcoord (einv.symm w) = w := by
    filter_upwards
      [einv.open_target.mem_nhds (einv.map_source ha_einv)] with w hw
    exact einv.right_inv hw
  have hright_at_z :
      ∀ᶠ w in nhds (z : ℂ), fcoord (einv.symm w) = w := by
    simpa [hfa] using hright
  have hright_cylinder :
      ∀ᶠ w : ComplexCylinder in nhds z,
        fcoord (einv.symm (w : ℂ)) = (w : ℂ) :=
    (continuous_subtype_val : Continuous ((↑) : ComplexCylinder → ℂ)).continuousAt
      hright_at_z
  have hevent :
      (fun w : ComplexCylinder ↦ H.symm w) =ᶠ[nhds z] branch := by
    filter_upwards [hright_cylinder] with w hw
    have hFbranch : F (branch w) = (w : ℂ) := by
      simpa [branch, fcoord] using hw
    have hHbranch : H (branch w) = w :=
      Subtype.ext hFbranch
    exact (H.symm_apply_eq).2 hHbranch.symm
  exact hbranch_mdiff.congr_of_eventuallyEq hevent

/--
%%handwave
name: Fundamental period of the complex exponential
statement:
  Define the fundamental exponential period $\omega_0=2\pi i$.
-/
noncomputable def complexExponentialPeriod : ℂ :=
  2 * Real.pi * Complex.I

/--
%%handwave
name: Exponential covering with prescribed period
statement:
  For $\omega\ne0$, rescale the exponential map to
  $z\mapsto\exp(2\pi i z/\omega)$, so that $\omega$ is a period.
-/
noncomputable def scaledComplexExponentialCover (omega : ℂ) :
    ℂ → ComplexCylinder :=
  fun z ↦ ⟨Complex.exp (complexExponentialPeriod / omega * z),
    Complex.exp_ne_zero _⟩

/--
%%handwave
name:
  A rescaled exponential covers the punctured plane
statement:
  For every nonzero $\omega\in\mathbb C$, the map
  $z\mapsto\exp(2\pi i z/\omega)$ from $\mathbb C$ to
  $\mathbb C^\times$ is a topological covering map.
proof:
  Multiplication by $2\pi i/\omega$ is a homeomorphism of the plane, and the
  usual exponential map is a covering. Precompose that covering by this
  homeomorphism.
-/
theorem scaledComplexExponentialCover_isCoveringMap
    (omega : ℂ) (homega : omega ≠ 0) :
    IsCoveringMap (scaledComplexExponentialCover omega) := by
  have hperiod : complexExponentialPeriod ≠ 0 := by
    simp [complexExponentialPeriod, Complex.I_ne_zero]
  have hscale : complexExponentialPeriod / omega ≠ 0 :=
    div_ne_zero hperiod homega
  have h := complexExponentialCover_isCoveringMap.comp_homeomorph
    (Homeomorph.mulLeft₀ (complexExponentialPeriod / omega) hscale)
  simpa [scaledComplexExponentialCover, complexExponentialCover,
    Function.comp_def, Homeomorph.coe_mulLeft₀] using h

/--
%%handwave
name:
  A rescaled exponential projection is holomorphic
statement:
  For every nonzero $\omega\in\mathbb C$, the map
  $z\mapsto\exp(2\pi i z/\omega)$ from $\mathbb C$ to
  $\mathbb C^\times$ is holomorphic.
proof:
  Complex scaling is entire, and composing it with the holomorphic
  exponential projection remains holomorphic.
-/
theorem scaledComplexExponentialCover_holomorphic
    (omega : ℂ) :
    HolomorphicMap ℂ ComplexCylinder
      (scaledComplexExponentialCover omega) := by
  have hscale : HolomorphicMap ℂ ℂ
      (fun z : ℂ ↦ complexExponentialPeriod / omega * z) := by
    exact (show Differentiable ℂ
      (fun z : ℂ ↦ complexExponentialPeriod / omega * z) by
        fun_prop).mdifferentiable
  simpa [scaledComplexExponentialCover, complexExponentialCover,
    Function.comp_def] using complexExponentialCover_holomorphic.comp hscale

/--
%%handwave
name:
  Fibers of a rescaled exponential are cyclic translation orbits
statement:
  Let $\omega\ne0$. For $z,w\in\mathbb C$, one has
  $\exp(2\pi i z/\omega)=\exp(2\pi i w/\omega)$ if and only if
  $z-w\in\mathbb Z\omega$, equivalently $z$ and $w$ lie in the same
  translation orbit of $\mathbb Z\omega$.
proof:
  Equality of two exponential values says that their exponents differ by an
  integral multiple of $2\pi i$. Since $2\pi i/\omega$ is nonzero, cancel it
  to obtain an integral multiple of $\omega$, and reverse the calculation for
  the converse.
-/
theorem scaledComplexExponentialCover_eq_iff_mem_orbit
    (omega : ℂ) (homega : omega ≠ 0) {z w : ℂ} :
    scaledComplexExponentialCover omega z =
        scaledComplexExponentialCover omega w ↔
      z ∈ AddAction.orbit (AddSubgroup.zmultiples omega) w := by
  have hperiod : complexExponentialPeriod ≠ 0 := by
    simp [complexExponentialPeriod, Complex.I_ne_zero]
  have hscale : complexExponentialPeriod / omega ≠ 0 :=
    div_ne_zero hperiod homega
  have hperiod_scale :
      complexExponentialPeriod =
        (complexExponentialPeriod / omega) * omega := by
    field_simp
  constructor
  · intro h
    have hexp :
        Complex.exp (complexExponentialPeriod / omega * z) =
          Complex.exp (complexExponentialPeriod / omega * w) := by
      exact congrArg Subtype.val h
    rcases Complex.exp_eq_exp_iff_exists_int.mp hexp with ⟨n, hn⟩
    have hnperiod :
        (n : ℂ) * complexExponentialPeriod =
          complexExponentialPeriod / omega * ((n : ℂ) * omega) := by
      conv_lhs => rw [hperiod_scale]
      ring
    have hscaled :
        complexExponentialPeriod / omega * z =
          complexExponentialPeriod / omega *
            (w + (n : ℂ) * omega) := by
      calc
        complexExponentialPeriod / omega * z =
            complexExponentialPeriod / omega * w +
              (n : ℂ) * complexExponentialPeriod := by
          simpa [complexExponentialPeriod] using hn
        _ = complexExponentialPeriod / omega *
              (w + (n : ℂ) * omega) := by
          rw [hnperiod]
          ring
    have hzw : z = w + (n : ℂ) * omega :=
      mul_left_cancel₀ hscale hscaled
    apply AddAction.mem_orbit_iff.mpr
    let ell : AddSubgroup.zmultiples omega :=
      ⟨(n : ℂ) * omega,
        AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp [zsmul_eq_mul]⟩⟩
    refine ⟨ell, ?_⟩
    change (n : ℂ) * omega + w = z
    rw [hzw]
    ac_rfl
  · intro horbit
    rcases AddAction.mem_orbit_iff.mp horbit with ⟨ell, hell⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp ell.property with ⟨n, hn⟩
    have hell' : (n : ℂ) * omega + w = z := by
      change (ell : ℂ) + w = z at hell
      rw [← hn] at hell
      simpa [zsmul_eq_mul] using hell
    have hnperiod :
        (n : ℂ) * complexExponentialPeriod =
          complexExponentialPeriod / omega * ((n : ℂ) * omega) := by
      conv_lhs => rw [hperiod_scale]
      ring
    apply Subtype.ext
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨n, ?_⟩
    change complexExponentialPeriod / omega * z =
      complexExponentialPeriod / omega * w +
        (n : ℂ) * (2 * Real.pi * Complex.I)
    rw [← complexExponentialPeriod]
    calc
      complexExponentialPeriod / omega * z =
          complexExponentialPeriod / omega * ((n : ℂ) * omega + w) := by
        rw [hell']
      _ = complexExponentialPeriod / omega * w +
          complexExponentialPeriod / omega * ((n : ℂ) * omega) := by
        ring
      _ = complexExponentialPeriod / omega * w +
          (n : ℂ) * complexExponentialPeriod := by
        rw [hnperiod]

/--
%%handwave
name:
  A rescaled exponential is onto the punctured plane
statement:
  For every nonzero $\omega\in\mathbb C$, every point of
  $\mathbb C^\times$ equals $\exp(2\pi i z/\omega)$ for some
  $z\in\mathbb C$.
proof:
  The ordinary exponential projection is onto, and multiplication by the
  nonzero factor $2\pi i/\omega$ is onto. Their composite is therefore onto.
-/
theorem scaledComplexExponentialCover_surjective
    (omega : ℂ) (homega : omega ≠ 0) :
    Function.Surjective (scaledComplexExponentialCover omega) := by
  have hperiod : complexExponentialPeriod ≠ 0 := by
    simp [complexExponentialPeriod, Complex.I_ne_zero]
  have hscale : complexExponentialPeriod / omega ≠ 0 :=
    div_ne_zero hperiod homega
  have hmul : Function.Surjective
      (fun z : ℂ ↦ complexExponentialPeriod / omega * z) :=
    (Homeomorph.mulLeft₀ (complexExponentialPeriod / omega) hscale).surjective
  have hexp : Function.Surjective complexExponentialCover :=
    Complex.isAddQuotientCoveringMap_exp.surjective
  simpa [scaledComplexExponentialCover, complexExponentialCover,
    Function.comp_def] using hexp.comp hmul

/-- A full complex lattice is a discrete `ℤ`-submodule of `ℂ` whose real
span is all of `ℂ`. -/
structure ComplexLattice where
  /-- The underlying additive subgroup, represented as a `ℤ`-submodule. -/
  carrier : Submodule ℤ ℂ
  /-- A lattice is discrete in the subspace topology. -/
  [discreteTopology : DiscreteTopology carrier]
  /-- A complex lattice has full real span. -/
  span_top : Submodule.span ℝ (carrier : Set ℂ) = ⊤

attribute [instance] ComplexLattice.discreteTopology


noncomputable instance ComplexLattice.properlyDiscontinuousVAdd
    (Lambda : ComplexLattice) :
    ProperlyDiscontinuousVAdd Lambda.carrier ℂ := by
  letI : DiscreteTopology Lambda.carrier.toAddSubgroup :=
    Lambda.discreteTopology
  exact
    Lambda.carrier.toAddSubgroup.properlyDiscontinuousVAdd_of_tendsto_cofinite
      (Lambda.carrier.toAddSubgroup.tendsto_coe_cofinite_of_discrete
        DiscreteTopology.isDiscrete)

/-- The complex torus associated to a full lattice, as the orbit quotient by
translations. -/
abbrev ComplexTorus (Lambda : ComplexLattice) :=
  AddAction.orbitRel.Quotient Lambda.carrier ℂ

/--
%%handwave
name: Quotient projection to a complex torus
statement:
  For a full lattice $\Lambda\subset\mathbb C$, define
  $q_\Lambda:\mathbb C\to\mathbb C/\Lambda$ by sending $z$ to its translation
  orbit.
-/
noncomputable def complexTorusQuotientMk (Lambda : ComplexLattice) : ℂ → ComplexTorus Lambda :=
  Quotient.mk (AddAction.orbitRel Lambda.carrier ℂ)

/--
%%handwave
name:
  A lattice quotient is a translation covering
statement:
  For a full lattice $\Lambda\subset\mathbb C$, the quotient projection
  $q:\mathbb C\to\mathbb C/\Lambda$ is the covering map associated to the
  properly discontinuous translation action of $\Lambda$.
proof:
  Discreteness of $\Lambda$ makes its translation action properly
  discontinuous, so the standard orbit-quotient construction is a covering.
-/
theorem complexTorusQuotientMk_isAddQuotientCoveringMap
    (Lambda : ComplexLattice) :
    IsAddQuotientCoveringMap (complexTorusQuotientMk Lambda) Lambda.carrier := by
  exact isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd

/--
%%handwave
name:
  A lattice quotient projection is a covering map
statement:
  For a full lattice $\Lambda\subset\mathbb C$, the projection
  $q:\mathbb C\to\mathbb C/\Lambda$ is a topological covering map.
proof:
  Forget the translation-group data from the covering supplied by the
  properly discontinuous quotient construction.
-/
theorem complexTorusQuotientMk_isCoveringMap (Lambda : ComplexLattice) :
    IsCoveringMap (complexTorusQuotientMk Lambda) :=
  (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).isCoveringMap

/--
%%handwave
name:
  A lattice quotient projection is locally a homeomorphism
statement:
  For every $z\in\mathbb C$, the projection
  $q:\mathbb C\to\mathbb C/\Lambda$ restricts to a homeomorphism on a
  neighborhood of $z$.
proof:
  Every covering map is a local homeomorphism.
-/
theorem complexTorusQuotientMk_isLocalHomeomorph (Lambda : ComplexLattice) :
    IsLocalHomeomorph (complexTorusQuotientMk Lambda) :=
  (complexTorusQuotientMk_isCoveringMap Lambda).isLocalHomeomorph

/--
%%handwave
name: Complex charts on a lattice quotient
statement:
  Equip $\mathbb C/\Lambda$ with the complex charts induced by the quotient
  covering, using a fixed representative of each orbit to give an explicit
  right inverse to the quotient map.
-/
@[implicit_reducible]
noncomputable def ComplexTorus.chartedSpace (Lambda : ComplexLattice) :
    ChartedSpace ℂ (ComplexTorus Lambda) :=
  (complexTorusQuotientMk_isLocalHomeomorph Lambda).chartedSpaceOfRightInverse
    (fun q ↦ Quotient.out_eq q)

noncomputable instance (priority := 1100) ComplexTorus.instChartedSpace
    (Lambda : ComplexLattice) : ChartedSpace ℂ (ComplexTorus Lambda) :=
  ComplexTorus.chartedSpace Lambda

/--
%%handwave
name:
  Formula for a preferred lattice-quotient chart
statement:
  At $q\in\mathbb C/\Lambda$, the preferred complex chart is obtained by
  first taking the local inverse of the quotient projection through the
  chosen representative of $q$, then using the standard chart of
  $\mathbb C$.
proof:
  This is the defining formula for the charted structure induced from local
  inverses of the quotient projection.
-/
theorem ComplexTorus.chartAt_eq (Lambda : ComplexLattice)
    (q : ComplexTorus Lambda) :
    chartAt ℂ q =
      ((complexTorusQuotientMk_isLocalHomeomorph Lambda).localInverseAt
        (Quotient.out q)).trans (chartAt ℂ (Quotient.out q)) :=
  rfl

/--
%%handwave
name:
  A quotient chart chooses a lift of each point
statement:
  If $r$ lies in the source of the preferred chart at
  $q\in\mathbb C/\Lambda$, then applying the quotient projection to the chart
  value of $r$ returns $r$.
proof:
  The chart value is the selected local inverse of the quotient projection,
  so the right-inverse identity gives the result.
-/
theorem ComplexTorus.quotientMk_chartAt (Lambda : ComplexLattice)
    (q r : ComplexTorus Lambda) (hr : r ∈ (chartAt ℂ q).source) :
    complexTorusQuotientMk Lambda ((chartAt ℂ q) r) = r := by
  rw [ComplexTorus.chartAt_eq] at hr ⊢
  have hr' : r ∈
      ((complexTorusQuotientMk_isLocalHomeomorph Lambda).localInverseAt
        (Quotient.out q)).source := by
    simpa [OpenPartialHomeomorph.trans_source, chartAt_self_eq] using hr
  change complexTorusQuotientMk Lambda
      ((complexTorusQuotientMk_isLocalHomeomorph Lambda).localInverseAt
        (Quotient.out q) r) = r
  exact (complexTorusQuotientMk_isLocalHomeomorph Lambda).apply_localInverseAt_of_mem hr'

/--
%%handwave
name:
  The inverse quotient chart is the quotient projection
statement:
  On the target of a preferred chart of $\mathbb C/\Lambda$, its inverse is
  the quotient projection $q:\mathbb C\to\mathbb C/\Lambda$.
proof:
  The preferred chart is defined from a local inverse of $q$; reversing it
  recovers $q$ on the chart target.
-/
theorem ComplexTorus.chartAt_symm_eq_quotientMk (Lambda : ComplexLattice)
    (q : ComplexTorus Lambda) (z : ℂ) :
    (chartAt ℂ q).symm z = complexTorusQuotientMk Lambda z := by
  rw [ComplexTorus.chartAt_eq]
  change
    ((complexTorusQuotientMk_isLocalHomeomorph Lambda).localInverseAt
      (Quotient.out q)).symm z = complexTorusQuotientMk Lambda z
  rw [(complexTorusQuotientMk_isLocalHomeomorph Lambda).localInverseAt_symm]

/--
%%handwave
name:
  The quotient projection is injective in a quotient chart
statement:
  The projection $q:\mathbb C\to\mathbb C/\Lambda$ is injective on the
  target of every preferred quotient chart.
proof:
  That target is an evenly covered sheet on which the selected local inverse
  and the quotient projection are mutually inverse.
-/
theorem ComplexTorus.quotientMk_injOn_chartAt_target (Lambda : ComplexLattice)
    (q : ComplexTorus Lambda) :
    (chartAt ℂ q).target.InjOn (complexTorusQuotientMk Lambda) := by
  rw [ComplexTorus.chartAt_eq]
  simpa [OpenPartialHomeomorph.trans_target, chartAt_self_eq] using
    (complexTorusQuotientMk_isLocalHomeomorph Lambda).injOn_localInverseAt_target

/--
%%handwave
name:
  A complex lattice quotient is a complex manifold
statement:
  For every full lattice $\Lambda\subset\mathbb C$, the translation quotient
  $\mathbb C/\Lambda$ is a complex one-manifold.
proof:
  The properly discontinuous action gives quotient charts.  Two local lifts
  of the same quotient point differ locally by a fixed lattice element, so
  every chart transition is locally a complex translation.
-/
theorem complexTorus_isManifold (Lambda : ComplexLattice) :
    IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ (ComplexTorus Lambda) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change ∃ q : ComplexTorus Lambda, chartAt ℂ q = e at he
  change ∃ q : ComplexTorus Lambda, chartAt ℂ q = e' at he'
  rcases he with ⟨q, rfl⟩
  rcases he' with ⟨q', rfl⟩
  simp only [mfld_simps]
  intro z hz
  let x : ComplexTorus Lambda := (chartAt ℂ q).symm z
  let w : ℂ := (chartAt ℂ q') x
  have hx_source : x ∈ (chartAt ℂ q').source := hz.2
  have hw_target : w ∈ (chartAt ℂ q').target :=
    (chartAt ℂ q').map_source hx_source
  have hmk_w : complexTorusQuotientMk Lambda w = x :=
    ComplexTorus.quotientMk_chartAt Lambda q' x hx_source
  have hmk_z : complexTorusQuotientMk Lambda z = x := by
    rw [← ComplexTorus.chartAt_symm_eq_quotientMk Lambda q z]
  have horbit : w ∈ AddAction.orbit Lambda.carrier z :=
    (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).apply_eq_iff_mem_orbit.mp
      (hmk_w.trans hmk_z.symm)
  rcases AddAction.mem_orbit_iff.mp horbit with ⟨ell, hell⟩
  have hell_target : ell +ᵥ z ∈ (chartAt ℂ q').target := by
    rw [hell]
    exact hw_target
  have htarget : (chartAt ℂ q).target ∈ nhds z :=
    (chartAt ℂ q).open_target.mem_nhds hz.1
  have hsource : (fun t : ℂ ↦ (chartAt ℂ q).symm t) ⁻¹'
      (chartAt ℂ q').source ∈ nhds z :=
    ((chartAt ℂ q).continuousAt_symm hz.1).preimage_mem_nhds
      ((chartAt ℂ q').open_source.mem_nhds hx_source)
  have hell_nhds : (fun t : ℂ ↦ ell +ᵥ t) ⁻¹'
      (chartAt ℂ q').target ∈ nhds z :=
    (continuous_const_vadd ell).continuousAt.preimage_mem_nhds
      ((chartAt ℂ q').open_target.mem_nhds hell_target)
  have heq :
      (fun t : ℂ ↦ (chartAt ℂ q') ((chartAt ℂ q).symm t)) =ᶠ[nhds z]
        (fun t : ℂ ↦ ell +ᵥ t) := by
    filter_upwards [htarget, hsource, hell_nhds] with t ht_target ht_source hell_t_target
    apply ComplexTorus.quotientMk_injOn_chartAt_target Lambda q'
      ((chartAt ℂ q').map_source ht_source) hell_t_target
    rw [ComplexTorus.quotientMk_chartAt Lambda q'
      ((chartAt ℂ q).symm t) ht_source]
    rw [ComplexTorus.chartAt_symm_eq_quotientMk Lambda q t]
    exact
      (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).apply_eq_iff_mem_orbit.mpr
        ⟨-ell, by simp⟩
  have hsmooth : ContDiffAt ℂ ⊤ (fun t : ℂ ↦ ell +ᵥ t) z := by
    change ContDiffAt ℂ ⊤ (fun t : ℂ ↦ (ell : ℂ) + t) z
    exact (contDiff_const.add contDiff_id).contDiffAt
  exact (hsmooth.congr_of_eventuallyEq heq).contDiffWithinAt

instance ComplexTorus.instManifold (Lambda : ComplexLattice) :
    IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ (ComplexTorus Lambda) :=
  complexTorus_isManifold Lambda

instance ComplexTorus.instT2Space (Lambda : ComplexLattice) :
    T2Space (ComplexTorus Lambda) := inferInstance


instance ComplexTorus.instComplexOneManifold (Lambda : ComplexLattice) :
    ComplexOneManifold (ComplexTorus Lambda) where
  toT2Space := inferInstance
  toIsManifold := inferInstance


/--
%%handwave
name:
  The lattice quotient projection is holomorphic
statement:
  For a full lattice $\Lambda\subset\mathbb C$, the quotient projection
  $q:\mathbb C\to\mathbb C/\Lambda$ is holomorphic.
proof:
  In a quotient chart, $q$ is locally the inverse chart composed with a
  translation by a lattice vector, hence has a holomorphic coordinate
  expression.
-/
theorem complexTorusQuotientMk_holomorphic (Lambda : ComplexLattice) :
    HolomorphicMap ℂ (ComplexTorus Lambda) (complexTorusQuotientMk Lambda) := by
  intro z
  let qz : ComplexTorus Lambda := complexTorusQuotientMk Lambda z
  let e : OpenPartialHomeomorph (ComplexTorus Lambda) ℂ := chartAt ℂ qz
  have hqz_source : qz ∈ e.source := mem_chart_source ℂ qz
  let w : ℂ := e qz
  have hw_target : w ∈ e.target := e.map_source hqz_source
  have hmk_w : complexTorusQuotientMk Lambda w = qz :=
    ComplexTorus.quotientMk_chartAt Lambda qz qz hqz_source
  have horbit : w ∈ AddAction.orbit Lambda.carrier z :=
    (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).apply_eq_iff_mem_orbit.mp
      hmk_w
  rcases AddAction.mem_orbit_iff.mp horbit with ⟨ell, hell⟩
  have hell_target : ell +ᵥ z ∈ e.target := by
    rw [hell]
    exact hw_target
  have htranslation : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ)
      (fun t : ℂ ↦ ell +ᵥ t) z := by
    rw [mdifferentiableAt_iff_differentiableAt]
    change DifferentiableAt ℂ (fun t : ℂ ↦ (ell : ℂ) + t) z
    exact (contDiff_const.add contDiff_id).contDiffAt.differentiableAt one_ne_zero
  have he_symm : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) e.symm (ell +ᵥ z) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ qz) hell_target
  have hcomp : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ)
      (e.symm ∘ fun t : ℂ ↦ ell +ᵥ t) z :=
    he_symm.comp z htranslation
  apply hcomp.congr_of_eventuallyEq
  have hell_nhds : (fun t : ℂ ↦ ell +ᵥ t) ⁻¹' e.target ∈ nhds z :=
    (continuous_const_vadd ell).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds hell_target)
  filter_upwards [hell_nhds] with t ht
  change complexTorusQuotientMk Lambda t = e.symm (ell +ᵥ t)
  rw [ComplexTorus.chartAt_symm_eq_quotientMk Lambda qz]
  exact
    (complexTorusQuotientMk_isAddQuotientCoveringMap Lambda).apply_eq_iff_mem_orbit.mpr
      ⟨-ell, by simp⟩

/--
%%handwave
name:
  The plane holomorphically covers every complex torus
statement:
  For a full lattice $\Lambda\subset\mathbb C$, the quotient projection
  $\mathbb C\to\mathbb C/\Lambda$ is a holomorphic covering map.
proof:
  Proper discontinuity gives the covering property.  In quotient charts the
  projection differs locally from a chart inverse only by a translation, so
  it is holomorphic.
tags:
  milestone
-/
theorem complexTorusQuotientMk_isHolomorphicCoveringMap
    (Lambda : ComplexLattice) :
    IsHolomorphicCoveringMap (complexTorusQuotientMk Lambda) :=
  ⟨complexTorusQuotientMk_isCoveringMap Lambda,
    complexTorusQuotientMk_holomorphic Lambda⟩

/--
%%handwave
name:
  Holomorphicity descends through a complex-torus quotient
statement:
  Let $\Lambda\subset\mathbb C$ be a full lattice and
  $q:\mathbb C\to\mathbb C/\Lambda$ its quotient projection. If
  $F:\mathbb C/\Lambda\to Y$ is a map to a complex one-manifold such that
  $F\circ q$ is holomorphic, then $F$ is holomorphic.
proof:
  In each preferred quotient chart, the chart value is a local lift and the
  quotient projection sends that lift back to the original point. Thus $F$
  agrees locally with the holomorphic map $F\circ q$ composed with the
  holomorphic quotient chart.
-/
theorem holomorphicMap_of_comp_complexTorusQuotientMk
    (Lambda : ComplexLattice)
    {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [ComplexOneManifold Y] {F : ComplexTorus Lambda → Y}
    (hF : HolomorphicMap ℂ Y (F ∘ complexTorusQuotientMk Lambda)) :
    HolomorphicMap (ComplexTorus Lambda) Y F := by
  intro q
  let e : OpenPartialHomeomorph (ComplexTorus Lambda) ℂ := chartAt ℂ q
  have hq_source : q ∈ e.source := mem_chart_source ℂ q
  have he_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) e q :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ q) hq_source
  have hcomp : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ)
      ((F ∘ complexTorusQuotientMk Lambda) ∘ e) q :=
    (hF (e q)).comp q he_mdiff
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hq_source] with r hr
  change F r = F (complexTorusQuotientMk Lambda (e r))
  rw [ComplexTorus.quotientMk_chartAt Lambda q r hr]

/--
%%handwave
name:
  A discrete subgroup of the plane has rank at most two
statement:
  If $L\subset\mathbb C$ is a discrete additive subgroup, then
  $\operatorname{rank}_{\mathbb Z}L\leq 2$.
proof:
  The integral rank of a discrete subgroup equals the real dimension of its
  real span, which is at most
  $\dim_{\mathbb R}\mathbb C=2$.
-/
theorem discreteComplexSubmodule_finrank_le_two
    (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    Module.finrank ℤ L ≤ 2 := by
  have hspan : Submodule.span ℤ (L : Set ℂ) = L := Submodule.span_eq L
  letI : DiscreteTopology (Submodule.span ℤ (L : Set ℂ)) :=
    hspan.symm ▸ inferInstance
  have hrank := Real.finrank_eq_int_finrank_of_discrete
    (s := (L : Set ℂ))
    (inferInstance : DiscreteTopology (Submodule.span ℤ (L : Set ℂ)))
  have hreal : Set.finrank ℝ (L : Set ℂ) ≤ 2 := by
    rw [Set.finrank]
    calc
      Module.finrank ℝ (Submodule.span ℝ (L : Set ℂ)) ≤
          Module.finrank ℝ ℂ := Submodule.finrank_le _
      _ = 2 := Complex.finrank_real_complex
  rw [hrank] at hreal
  change Module.finrank ℤ (Submodule.span ℤ (L : Set ℂ)) ≤ 2 at hreal
  exact hspan ▸ hreal

/--
%%handwave
name:
  A discrete subgroup of the plane has rank zero, one, or two
statement:
  If $L\subset\mathbb C$ is a discrete additive subgroup, then its integral
  rank is $0$, $1$, or $2$.
proof:
  The real rank of the span of a discrete integral submodule equals its
  integral rank and is at most the real dimension $2$ of $\mathbb C$.
-/
theorem discreteComplexSubmodule_finrank_cases
    (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    Module.finrank ℤ L = 0 ∨
      Module.finrank ℤ L = 1 ∨ Module.finrank ℤ L = 2 := by
  have h := discreteComplexSubmodule_finrank_le_two L
  omega

/--
%%handwave
name:
  A discrete rank-zero subgroup of the plane is trivial
statement:
  If $L\subset\mathbb C$ is a discrete integral submodule and
  $\operatorname{rank}_{\mathbb Z}L=0$, then $L=\{0\}$.
proof:
  For a discrete integral submodule of a finite-dimensional real vector
  space, the integral rank equals the real dimension of its real span. Rank
  zero therefore makes that real span trivial, and hence every element of
  $L$ is zero.
-/
theorem discreteComplexSubmodule_eq_bot_of_finrank_zero
    (L : Submodule ℤ ℂ) [DiscreteTopology L]
    (hrank : Module.finrank ℤ L = 0) : L = ⊥ := by
  have hspan : Submodule.span ℤ (L : Set ℂ) = L := Submodule.span_eq L
  letI : DiscreteTopology (Submodule.span ℤ (L : Set ℂ)) :=
    hspan.symm ▸ inferInstance
  have hrank_eq := Real.finrank_eq_int_finrank_of_discrete
    (s := (L : Set ℂ))
    (inferInstance : DiscreteTopology (Submodule.span ℤ (L : Set ℂ)))
  have hreal :
      Module.finrank ℝ (Submodule.span ℝ (L : Set ℂ)) = 0 := by
    change Set.finrank ℝ (L : Set ℂ) = 0
    rw [hrank_eq]
    change Module.finrank ℤ (Submodule.span ℤ (L : Set ℂ)) = 0
    rw [hspan]
    exact hrank
  have hreal_bot : Submodule.span ℝ (L : Set ℂ) = ⊥ :=
    Submodule.finrank_eq_zero.mp hreal
  apply le_antisymm
  · intro z hz
    have hzspan : z ∈ Submodule.span ℝ (L : Set ℂ) :=
      Submodule.subset_span hz
    rw [hreal_bot] at hzspan
    simpa using hzspan
  · exact bot_le

/--
%%handwave
name:
  A discrete rank-two subgroup of the plane is a full lattice
statement:
  If $L\subset\mathbb C$ is a discrete integral submodule and
  $\operatorname{rank}_{\mathbb Z}L=2$, then its real span is all of
  $\mathbb C$.
proof:
  The integral rank of a discrete subgroup equals the real dimension of its
  real span. Thus the span has real dimension two, equal to the real
  dimension of $\mathbb C$, and a subspace of full dimension is the whole
  space.
-/
theorem discreteComplexSubmodule_span_top_of_finrank_two
    (L : Submodule ℤ ℂ) [DiscreteTopology L]
    (hrank : Module.finrank ℤ L = 2) :
    Submodule.span ℝ (L : Set ℂ) = ⊤ := by
  have hspan : Submodule.span ℤ (L : Set ℂ) = L := Submodule.span_eq L
  letI : DiscreteTopology (Submodule.span ℤ (L : Set ℂ)) :=
    hspan.symm ▸ inferInstance
  have hrank_eq := Real.finrank_eq_int_finrank_of_discrete
    (s := (L : Set ℂ))
    (inferInstance : DiscreteTopology (Submodule.span ℤ (L : Set ℂ)))
  apply Submodule.eq_top_of_finrank_eq
  calc
    Module.finrank ℝ (Submodule.span ℝ (L : Set ℂ)) =
        Set.finrank ℝ (L : Set ℂ) := rfl
    _ = Module.finrank ℤ (Submodule.span ℤ (L : Set ℂ)) := hrank_eq
    _ = Module.finrank ℤ L := by rw [hspan]
    _ = 2 := hrank
    _ = Module.finrank ℝ ℂ := Complex.finrank_real_complex.symm

/--
%%handwave
name:
  A discrete rank-one subgroup of the plane is cyclic
statement:
  If $L\subset\mathbb C$ is a discrete integral submodule and
  $\operatorname{rank}_{\mathbb Z}L=1$, then there is a nonzero
  $\omega\in\mathbb C$ such that $L=\mathbb Z\omega$.
proof:
  A discrete subgroup of a finite-dimensional real vector space is a finite
  free integral module. A free module of rank one has a nonzero basis vector
  $\omega$, and every element is a unique integral multiple of that vector.
-/
theorem discreteComplexSubmodule_eq_zmultiples_of_finrank_one
    (L : Submodule ℤ ℂ) [DiscreteTopology L]
    (hrank : Module.finrank ℤ L = 1) :
    ∃ omega : ℂ, omega ≠ 0 ∧
      L.toAddSubgroup = AddSubgroup.zmultiples omega := by
  rcases finrank_eq_one_iff'.mp hrank with ⟨v, hv, hgen⟩
  let omega : ℂ := v
  have homega : omega ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact hz
  refine ⟨omega, homega, ?_⟩
  ext z
  constructor
  · intro hz
    rcases hgen ⟨z, hz⟩ with ⟨n, hn⟩
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨n, ?_⟩
    have hn' := congrArg Subtype.val hn
    simpa [omega] using hn'
  · intro hz
    rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨n, rfl⟩
    exact L.smul_mem n v.property

/--
%%handwave
name: Complex lattice from a discrete rank-two subgroup
statement:
  If $L\subseteq\mathbb C$ is a discrete integral submodule of rank two,
  regard $L$ as a full complex lattice using the fact that its real span is
  all of $\mathbb C$.
-/
def complexLatticeOfDiscreteFinrankTwo
    (L : Submodule ℤ ℂ) [DiscreteTopology L]
    (hrank : Module.finrank ℤ L = 2) : ComplexLattice where
  carrier := L
  span_top := discreteComplexSubmodule_span_top_of_finrank_two L hrank

/--
%%handwave
name: Plane-cylinder-torus classification predicate
statement:
  A Riemann surface $X$ satisfies this predicate when $X$ is biholomorphic to
  $\mathbb C$, to $\mathbb C^\times$, or to $\mathbb C/\Lambda$ for some full
  lattice $\Lambda\subset\mathbb C$.
-/
def IsPlaneCylinderOrTorus (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  BiholomorphicSurfaces X ℂ ∨
    BiholomorphicSurfaces X ComplexCylinder ∨
      ∃ Lambda : ComplexLattice, BiholomorphicSurfaces X (ComplexTorus Lambda)

end Uniformization

end JJMath
