import JJMath.Uniformization.Hyperbolic
import JJMath.Uniformization.RadoSecondCountable
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Set.Subsingleton
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Holomorphic maps between complex surfaces

This file collects mapping infrastructure shared by the current uniformization
proofs: the standard complex structures on the disk and half-plane, pointed
surface coordinates, compact exhaustions, the inverse-function criterion for
bijective unbranched disk maps, and the Cayley equivalence.
-/

namespace JJMath

open scoped Manifold Topology unitInterval

namespace Uniformization

/--
%%handwave
name:
  Standard charted structure on the unit disk
statement:
  The unit disk inherits its complex charted-space structure from its open
  embedding in the complex plane.
-/
noncomputable instance instChartedSpaceComplexUnitDisc :
    ChartedSpace ℂ Complex.UnitDisc :=
  Topology.IsOpenEmbedding.singletonChartedSpace
    (show Topology.IsOpenEmbedding ((↑) : Complex.UnitDisc → ℂ) from
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal)

/--
%%handwave
name:
  The unit disk is contractible
statement:
  The open unit disk is contractible.
-/
noncomputable instance instContractibleSpaceComplexUnitDisc :
    ContractibleSpace Complex.UnitDisc := by
  change ContractibleSpace (Metric.ball (0 : ℂ) 1)
  exact Metric.contractibleSpace_ball (show (0 : ℝ) < 1 by norm_num)

/--
%%handwave
name:
  The unit disk is locally path connected
statement:
  The open unit disk is locally path connected.
-/
instance instLocPathConnectedSpaceComplexUnitDisc :
    LocPathConnectedSpace Complex.UnitDisc := by
  change LocPathConnectedSpace (Metric.ball (0 : ℂ) 1)
  exact Metric.isOpen_ball.locPathConnectedSpace

/--
%%handwave
name:
  Bounded nonconstant holomorphic function
statement:
  A Riemann surface carries a bounded nonconstant holomorphic function when
  there is a holomorphic complex-valued function whose range is bounded and
  contains at least two points.
-/
def HasBoundedNonconstantHolomorphicFunction (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∃ f : X → ℂ,
    HolomorphicMap X ℂ f ∧
      Bornology.IsBounded (Set.range f) ∧
        (Set.range f).Nontrivial

/--
%%handwave
name:
  Pointed surface coordinate
statement:
  A pointed surface coordinate is a complex chart whose source contains the
  chosen base point.
-/
structure PointedSurfaceCoordinate (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] (p : X) where
  /-- The chart used near the base point. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chart belongs to the surface atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The base point lies in the chart source. -/
  base_mem_source : p ∈ chart.source

/--
%%handwave
name:
  Surface derivative in a coordinate
statement:
  The complex derivative of a complex-valued holomorphic function at a point is
  computed after expressing the function in a chosen local coordinate.
-/
noncomputable def surfaceComplexDerivativeInCoordinate {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (χ : PointedSurfaceCoordinate X p) (f : X → ℂ) : ℂ :=
  deriv (fun z : ℂ ↦ f (χ.chart.symm z)) (χ.chart p)

theorem differentiableOn_surfaceCoordinate_symm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {f : X → ℂ} (hf : HolomorphicMap X ℂ f)
    {p : X} (χ : PointedSurfaceCoordinate X p) :
    DifferentiableOn ℂ (fun z : ℂ ↦ f (χ.chart.symm z)) χ.chart.target := by
  have hsymm : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) χ.chart.symm χ.chart.target :=
    mdifferentiableOn_atlas_symm (I := 𝓘(ℂ)) χ.chart_mem_atlas
  have hcomp : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ χ.chart.symm) χ.chart.target :=
    hf.comp_mdifferentiableOn hsymm
  intro z hz
  have hz' := hcomp z hz
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at hz'
  exact hz'

theorem holomorphicMap_unitDisc_of_coe
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : X → Complex.UnitDisc}
    (hF : HolomorphicMap X ℂ (fun x ↦ (F x : ℂ))) :
    HolomorphicMap X Complex.UnitDisc F := by
  let hOpen : Topology.IsOpenEmbedding ((↑) : Complex.UnitDisc → ℂ) :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F
  have hinv :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        (hOpen.toOpenPartialHomeomorph ((↑) : Complex.UnitDisc → ℂ)).symm
        (Set.range ((↑) : Complex.UnitDisc → ℂ)) := by
    exact (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℂ)) hOpen (n := 1)).mdifferentiableOn
      one_ne_zero
  have hcoe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (((↑) : Complex.UnitDisc → ℂ) ∘ F) := by
    simpa [Function.comp_def, HolomorphicMap] using hF
  have hcomp :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        ((hOpen.toOpenPartialHomeomorph ((↑) : Complex.UnitDisc → ℂ)).symm ∘
          (((↑) : Complex.UnitDisc → ℂ) ∘ F))
        Set.univ := by
    refine hinv.comp (mdifferentiableOn_univ.mpr hcoe) ?_
    intro x _
    exact ⟨F x, rfl⟩
  rw [← mdifferentiableOn_univ]
  convert hcomp using 1
  ext x
  simpa [Function.comp_def] using congrArg ((↑) : Complex.UnitDisc → ℂ)
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      (f := ((↑) : Complex.UnitDisc → ℂ)) hOpen (x := F x)).symm

/--
%%handwave
name:
  The unit disk inclusion is holomorphic
statement:
  The inclusion of the unit disk into the complex plane is holomorphic.
-/
theorem holomorphicMap_unitDisc_coe :
    HolomorphicMap Complex.UnitDisc ℂ (fun z : Complex.UnitDisc ↦ (z : ℂ)) := by
  let hOpen : Topology.IsOpenEmbedding ((↑) : Complex.UnitDisc → ℂ) :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
  have h :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        ((↑) : Complex.UnitDisc → ℂ) := by
    simpa using
      (contMDiff_isOpenEmbedding
        (I := 𝓘(ℂ)) (n := (1 : WithTop ℕ∞)) hOpen)
  exact h.mdifferentiable one_ne_zero

private theorem contMDiff_unitDisc_coe :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
      (fun z : Complex.UnitDisc ↦ (z : ℂ)) := by
  let hOpen : Topology.IsOpenEmbedding ((↑) : Complex.UnitDisc → ℂ) :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
  simpa using
    (contMDiff_isOpenEmbedding
      (I := 𝓘(ℂ)) (n := (1 : WithTop ℕ∞)) hOpen)

/--
%%handwave
name:
  Holomorphic maps into the upper half-plane from complex coordinates
statement:
  A map into the upper half-plane is holomorphic if its underlying
  complex-valued map is holomorphic.
proof:
  The upper half-plane has the charted structure induced by its open embedding
  into the complex plane.
-/
theorem holomorphicMap_upperHalfPlane_of_coe
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : X → UpperHalfPlane}
    (hF : HolomorphicMap X ℂ (fun x ↦ (F x : ℂ))) :
    HolomorphicMap X UpperHalfPlane F := by
  let hOpen : Topology.IsOpenEmbedding ((↑) : UpperHalfPlane → ℂ) :=
    UpperHalfPlane.isOpenEmbedding_coe
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F
  have hinv :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        (hOpen.toOpenPartialHomeomorph ((↑) : UpperHalfPlane → ℂ)).symm
        (Set.range ((↑) : UpperHalfPlane → ℂ)) := by
    exact (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℂ)) hOpen (n := 1)).mdifferentiableOn
      one_ne_zero
  have hcoe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (((↑) : UpperHalfPlane → ℂ) ∘ F) := by
    simpa [Function.comp_def, HolomorphicMap] using hF
  have hcomp :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        ((hOpen.toOpenPartialHomeomorph ((↑) : UpperHalfPlane → ℂ)).symm ∘
          (((↑) : UpperHalfPlane → ℂ) ∘ F))
        Set.univ := by
    refine hinv.comp (mdifferentiableOn_univ.mpr hcoe) ?_
    intro x _
    exact ⟨F x, rfl⟩
  rw [← mdifferentiableOn_univ]
  convert hcomp using 1
  ext x
  simpa [Function.comp_def] using congrArg ((↑) : UpperHalfPlane → ℂ)
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      (f := ((↑) : UpperHalfPlane → ℂ)) hOpen (x := F x)).symm

/--
%%handwave
name:
  The upper half-plane inclusion is holomorphic
statement:
  The inclusion of the upper half-plane into the complex plane is holomorphic.
-/
theorem holomorphicMap_upperHalfPlane_coe :
    HolomorphicMap UpperHalfPlane ℂ (fun z : UpperHalfPlane ↦ (z : ℂ)) := by
  exact UpperHalfPlane.mdifferentiable_coe

private theorem contMDiff_upperHalfPlane_coe :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
      (fun z : UpperHalfPlane ↦ (z : ℂ)) := by
  simpa using
    (contMDiff_isOpenEmbedding
      (I := 𝓘(ℂ)) (n := (1 : WithTop ℕ∞))
      UpperHalfPlane.isOpenEmbedding_coe)

/--
%%handwave
name:
  Holomorphic maps are continuous
statement:
  A holomorphic map between complex manifolds is continuous.
-/
theorem HolomorphicMap.continuous
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] {f : X → Y}
    (hf : HolomorphicMap X Y f) :
    Continuous f := by
  exact MDifferentiable.continuous (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
    (show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f from hf)

/--
%%handwave
name:
  Holomorphic maps compose
statement:
  The composite of two holomorphic maps between complex manifolds is
  holomorphic.
-/
theorem HolomorphicMap.comp
    {X Y Z : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z] {f : X → Y} {g : Y → Z}
    (hg : HolomorphicMap Y Z g) (hf : HolomorphicMap X Y f) :
    HolomorphicMap X Z (g ∘ f) := by
  exact (show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g from hg).comp
    (show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f from hf)

/--
%%handwave
name:
  Biholomorphic equivalences reverse
statement:
  The inverse of a biholomorphic equivalence is biholomorphic.
-/
noncomputable def Biholomorphic.symm
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (eXY : Biholomorphic X Y) :
    Biholomorphic Y X where
  toHomeomorph := eXY.toHomeomorph.symm
  holomorphic_toFun := eXY.holomorphic_invFun
  holomorphic_invFun := eXY.holomorphic_toFun

/--
%%handwave
name:
  Biholomorphic equivalences compose
statement:
  The composite of two biholomorphic equivalences is biholomorphic.
proof:
  Compose the underlying homeomorphisms.  The forward and inverse holomorphic
  maps are obtained by [composition of holomorphic
  maps](lean:JJMath.Uniformization.HolomorphicMap.comp).
-/
noncomputable def Biholomorphic.trans
    {X Y Z : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z]
    (eXY : Biholomorphic X Y) (eYZ : Biholomorphic Y Z) :
    Biholomorphic X Z where
  toHomeomorph := eXY.toHomeomorph.trans eYZ.toHomeomorph
  holomorphic_toFun := by
    change HolomorphicMap X Z (eYZ.toHomeomorph ∘ eXY.toHomeomorph)
    exact eYZ.holomorphic_toFun.comp eXY.holomorphic_toFun
  holomorphic_invFun := by
    change HolomorphicMap Z X (eXY.toHomeomorph.symm ∘ eYZ.toHomeomorph.symm)
    exact eXY.holomorphic_invFun.comp eYZ.holomorphic_invFun

/--
%%handwave
name:
  Biholomorphic surface equivalence is transitive
statement:
  If one surface is biholomorphic to a second surface and the second is
  biholomorphic to a third, then the first and third surfaces are
  biholomorphic.
proof:
  Choose representatives and compose the biholomorphic equivalences.
-/
theorem BiholomorphicSurfaces.trans
    {X Y Z : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z]
    (hXY : BiholomorphicSurfaces X Y) (hYZ : BiholomorphicSurfaces Y Z) :
    BiholomorphicSurfaces X Z := by
  rcases hXY with ⟨eXY⟩
  rcases hYZ with ⟨eYZ⟩
  exact ⟨eXY.trans eYZ⟩

/--
%%handwave
name:
  Biholomorphic surface equivalence is symmetric
statement:
  If one surface is biholomorphic to a second surface, then the second is
  biholomorphic to the first.
proof:
  Choose a biholomorphic equivalence and invert it.
-/
theorem BiholomorphicSurfaces.symm
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (hXY : BiholomorphicSurfaces X Y) :
    BiholomorphicSurfaces Y X := by
  rcases hXY with ⟨eXY⟩
  exact ⟨eXY.symm⟩

/--
%%handwave
name:
  Pointed disk maps are complex-continuous
statement:
  The underlying complex-valued function of a pointed holomorphic disk map is
  continuous.
proof:
  The disk-valued map is holomorphic, hence continuous, and the inclusion of
  the unit disk into the complex plane is continuous.
-/
theorem PointedHolomorphicMap.continuous_coe_unitDisc
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0) :
    Continuous (fun x : X ↦ (F.toFun x : ℂ)) := by
  exact Complex.UnitDisc.continuous_coe.comp F.holomorphic.continuous

/--
%%handwave
name:
  Pointed disk maps are complex-holomorphic
statement:
  The underlying complex-valued function of a pointed holomorphic disk map is
  holomorphic.
proof:
  The inclusion of the unit disk into the complex plane is holomorphic for
  the charted structure induced by its open embedding.  Compose it with the
  disk-valued holomorphic map.
-/
theorem PointedHolomorphicMap.holomorphic_coe_unitDisc
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0) :
    HolomorphicMap X ℂ (fun x : X ↦ (F.toFun x : ℂ)) := by
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (((↑) : Complex.UnitDisc → ℂ) ∘ F.toFun)
  exact holomorphicMap_unitDisc_coe.comp F.holomorphic

/--
%%handwave
name:
  Radó gives a sigma-compact surface
statement:
  Every Riemann surface is sigma compact.
proof:
  By [Radó's theorem](lean:JJMath.Uniformization.rado_secondCountableTopology_riemannSurface),
  the surface is second countable.  Riemann surfaces are locally compact, and
  mathlib turns locally compact second-countable spaces into sigma-compact
  spaces.
-/
theorem riemannSurface_sigmaCompactSpace
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    SigmaCompactSpace X := by
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  infer_instance

/--
%%handwave
name:
  Radó gives a compact exhaustion
statement:
  Every Riemann surface admits an exhaustion by compact subsets.
proof:
  A Riemann surface is
  [sigma compact](lean:JJMath.Uniformization.riemannSurface_sigmaCompactSpace).
  Since Riemann surfaces are locally compact, mathlib's compact-exhaustion
  construction supplies an increasing sequence of compact subsets whose
  interiors eventually contain every compact set.
-/
theorem riemannSurface_compactExhaustion
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    Nonempty (CompactExhaustion X) := by
  letI : SigmaCompactSpace X :=
    riemannSurface_sigmaCompactSpace X
  exact ⟨CompactExhaustion.choice X⟩

/--
%%handwave
name:
  Unbranched pointed disk maps are local homeomorphisms
statement:
  A pointed holomorphic disk map whose coordinate derivative never vanishes is
  a local homeomorphism.
proof:
  In source and target coordinates this is the one-complex-dimensional inverse
  function theorem.  The nonvanishing coordinate derivative is the nonzero
  complex-linear differential, so the map has a holomorphic local inverse
  around every point.
-/
theorem unbranched_pointedDiskMap_isLocalHomeomorph
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx
        (fun y ↦ (F.toFun y : ℂ)) ≠ 0) :
    IsLocalHomeomorph F.toFun := by
  classical
  refine IsLocalHomeomorph.mk F.toFun ?_
  intro x
  let χx : PointedSurfaceCoordinate X x :=
    { chart := chartAt ℂ x
      chart_mem_atlas := chart_mem_atlas ℂ x
      base_mem_source := mem_chart_source ℂ x }
  let e : OpenPartialHomeomorph X ℂ := χx.chart
  let a : ℂ := e x
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ (F.toFun (e.symm z) : ℂ)
  have ha_target : a ∈ e.target := by
    dsimp [a, e, χx]
    exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hdiff_on : DifferentiableOn ℂ fcoord e.target := by
    simpa [fcoord, e] using
      differentiableOn_surfaceCoordinate_symm
        (X := X) F.holomorphic_coe_unitDisc χx
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
  let diskOpen : Topology.IsOpenEmbedding ((↑) : Complex.UnitDisc → ℂ) :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
  let diskChart : OpenPartialHomeomorph Complex.UnitDisc ℂ :=
    diskOpen.toOpenPartialHomeomorph ((↑) : Complex.UnitDisc → ℂ)
  let E : OpenPartialHomeomorph X Complex.UnitDisc :=
    (e.trans einv).trans diskChart.symm
  refine ⟨E, ?_, ?_⟩
  · have hx_source_e_trans : x ∈ (e.trans einv).source := by
      rw [OpenPartialHomeomorph.trans_source]
      exact ⟨χx.base_mem_source, ha_einv⟩
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hx_source_e_trans, ?_⟩
    change einv (e x) ∈ diskChart.symm.source
    have hcoerange :
        (F.toFun x : ℂ) ∈ Set.range ((↑) : Complex.UnitDisc → ℂ) :=
      ⟨F.toFun x, rfl⟩
    simpa [diskChart, einv, fcoord, a, e, χx] using hcoerange
  · intro y hy
    have hy_source : y ∈ e.source := by
      have hy_e_trans : y ∈ (e.trans einv).source := hy.1
      rw [OpenPartialHomeomorph.trans_source] at hy_e_trans
      exact hy_e_trans.1
    have hdisk_left :
        diskChart.symm ((F.toFun y : ℂ)) = F.toFun y := by
      simpa [diskChart] using
        (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
          (f := ((↑) : Complex.UnitDisc → ℂ)) diskOpen (x := F.toFun y))
    calc
      F.toFun y
          = diskChart.symm ((F.toFun y : ℂ)) := hdisk_left.symm
      _ = diskChart.symm (einv (e y)) := by
          simp [einv, fcoord, e.left_inv hy_source]
      _ = E y := rfl

/--
%%handwave
name:
  The inverse of a bijective unbranched disk map is holomorphic
statement:
  The inverse homeomorphism of a bijective unbranched pointed holomorphic disk
  map is holomorphic.
proof:
  The inverse function theorem gives holomorphic local inverse branches.  The
  global inverse homeomorphism agrees locally with those branches, hence is
  holomorphic.
-/
theorem bijective_unbranched_pointedDiskMap_inverse_holomorphic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx
        (fun y ↦ (F.toFun y : ℂ)) ≠ 0)
    (hinj : Function.Injective F.toFun)
    (hsurj : Function.Surjective F.toFun) :
    HolomorphicMap Complex.UnitDisc X
      ((unbranched_pointedDiskMap_isLocalHomeomorph X F hunbranched).toHomeomorphOfBijective
        ⟨hinj, hsurj⟩).symm := by
  classical
  let hlocal : IsLocalHomeomorph F.toFun :=
    unbranched_pointedDiskMap_isLocalHomeomorph X F hunbranched
  let H : X ≃ₜ Complex.UnitDisc :=
    hlocal.toHomeomorphOfBijective ⟨hinj, hsurj⟩
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H.symm
  intro z
  let x : X := H.symm z
  have hxF : F.toFun x = z := by
    change H x = z
    exact H.apply_symm_apply z
  let χx : PointedSurfaceCoordinate X x :=
    { chart := chartAt ℂ x
      chart_mem_atlas := chart_mem_atlas ℂ x
      base_mem_source := mem_chart_source ℂ x }
  let e : OpenPartialHomeomorph X ℂ := χx.chart
  let a : ℂ := e x
  let fcoord : ℂ → ℂ := fun w : ℂ ↦ (F.toFun (e.symm w) : ℂ)
  have ha_target : a ∈ e.target := by
    dsimp [a, e, χx]
    exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hfa : fcoord a = (z : ℂ) := by
    have hleft : e.symm (e x) = x := e.left_inv χx.base_mem_source
    simpa [fcoord, a, hleft] using congrArg ((↑) : Complex.UnitDisc → ℂ) hxF
  have hdiff_on : DifferentiableOn ℂ fcoord e.target := by
    simpa [fcoord, e] using
      differentiableOn_surfaceCoordinate_symm
        (X := X) F.holomorphic_coe_unitDisc χx
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
  have hinv_diff_at_z : DifferentiableAt ℂ einv.symm (z : ℂ) := by
    have hinv_diff_at_fa : DifferentiableAt ℂ einv.symm (fcoord a) :=
      hinv_strict.hasDerivAt.differentiableAt
    simpa [hfa] using hinv_diff_at_fa
  have hinv_mdiff_at_z :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) einv.symm (z : ℂ) :=
    hinv_diff_at_z.mdifferentiableAt
  have hinv_at_z : einv.symm (z : ℂ) = a := by
    have hleft : einv.symm (einv a) = a := einv.left_inv ha_einv
    simpa [einv, hfa] using hleft
  have he_symm_mdiff_at_a :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm a :=
    mdifferentiableAt_atlas_symm χx.chart_mem_atlas ha_target
  have he_symm_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm (einv.symm (z : ℂ)) := by
    simpa [hinv_at_z] using he_symm_mdiff_at_a
  let branch : Complex.UnitDisc → X :=
    fun w : Complex.UnitDisc ↦ e.symm (einv.symm (w : ℂ))
  have hcoe_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (fun w : Complex.UnitDisc ↦ (w : ℂ)) z :=
    holomorphicMap_unitDisc_coe z
  have hbranch_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) branch z := by
    simpa [branch] using
      he_symm_mdiff.comp z (hinv_mdiff_at_z.comp z hcoe_mdiff)
  have hright :
      ∀ᶠ w in 𝓝 (fcoord a), fcoord (einv.symm w) = w := by
    filter_upwards
      [einv.open_target.mem_nhds (einv.map_source ha_einv)] with w hw
    exact einv.right_inv hw
  have hright_at_z :
      ∀ᶠ w in 𝓝 (z : ℂ), fcoord (einv.symm w) = w := by
    simpa [hfa] using hright
  have hright_unit :
      ∀ᶠ w : Complex.UnitDisc in 𝓝 z,
        fcoord (einv.symm (w : ℂ)) = (w : ℂ) :=
    Complex.UnitDisc.continuous_coe.continuousAt hright_at_z
  have hevent :
      (fun w : Complex.UnitDisc ↦ H.symm w) =ᶠ[𝓝 z] branch := by
    filter_upwards [hright_unit] with w hw
    have hFbranch_coe : ((F.toFun (branch w) : Complex.UnitDisc) : ℂ) = (w : ℂ) := by
      simpa [branch, fcoord] using hw
    have hFbranch : F.toFun (branch w) = w :=
      Subtype.ext hFbranch_coe
    have hHbranch : H (branch w) = w := by
      simpa [H, hlocal] using hFbranch
    exact (H.symm_apply_eq).2 hHbranch.symm
  exact hbranch_mdiff.congr_of_eventuallyEq hevent

/--
%%handwave
name:
  Bijective unbranched pointed disk maps are biholomorphic
statement:
  A bijective pointed holomorphic disk map with nonvanishing coordinate
  derivative everywhere is a biholomorphic equivalence onto the unit disk.
proof:
  By [the inverse function theorem, an unbranched pointed disk map is a local
  homeomorphism](lean:JJMath.Uniformization.unbranched_pointedDiskMap_isLocalHomeomorph).
  A bijective local homeomorphism is a homeomorphism.  The forward map is
  holomorphic by assumption, and [the inverse homeomorphism is
  holomorphic](lean:JJMath.Uniformization.bijective_unbranched_pointedDiskMap_inverse_holomorphic)
  because it agrees locally with the holomorphic inverse branches.
-/
theorem biholomorphicSurfaces_of_bijective_unbranched_pointedDiskMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (_χ : PointedSurfaceCoordinate X p)
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx
        (fun y ↦ (F.toFun y : ℂ)) ≠ 0)
    (hinj : Function.Injective F.toFun)
    (hsurj : Function.Surjective F.toFun) :
    BiholomorphicSurfaces X Complex.UnitDisc := by
  let hloc : IsLocalHomeomorph F.toFun :=
    unbranched_pointedDiskMap_isLocalHomeomorph X F hunbranched
  let e : X ≃ₜ Complex.UnitDisc :=
    hloc.toHomeomorphOfBijective ⟨hinj, hsurj⟩
  refine ⟨{
    toHomeomorph := e
    holomorphic_toFun := ?_
    holomorphic_invFun := ?_
  }⟩
  · simpa [e, hloc] using F.holomorphic
  · simpa [e, hloc] using
      bijective_unbranched_pointedDiskMap_inverse_holomorphic
        X F hunbranched hinj hsurj



/--
%%handwave
name:
  The Cayley transform sends the disk to the upper half-plane
statement:
  For \(z\) in the open unit disk,
  \[
    \operatorname{Im}\!\left(i\,\frac{1+z}{1-z}\right)>0.
  \]
proof:
  The imaginary part is
  \[
    \frac{1-|z|^2}{|1-z|^2},
  \]
  whose numerator is positive in the unit disk and whose denominator is
  positive because \(z\ne 1\).
-/
theorem unitDisc_cayley_im_pos (z : Complex.UnitDisc) :
    0 < (Complex.I * (1 + (z : ℂ)) / (1 - (z : ℂ))).im := by
  have hden : (1 : ℂ) - (z : ℂ) ≠ 0 := by
    intro h
    have hz_eq_one : (z : ℂ) = 1 := by
      linear_combination -h
    have hnorm : ‖(z : ℂ)‖ = 1 := by simp [hz_eq_one]
    linarith [Complex.UnitDisc.norm_lt_one z]
  have hden_pos : 0 < Complex.normSq ((1 : ℂ) - (z : ℂ)) := by
    rw [Complex.normSq_pos]
    exact hden
  have hformula :
      (Complex.I * (1 + (z : ℂ)) / (1 - (z : ℂ))).im =
        (1 - Complex.normSq (z : ℂ)) /
          Complex.normSq ((1 : ℂ) - (z : ℂ)) := by
    simp [Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.normSq_apply]
    ring
  rw [hformula]
  exact div_pos (by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [Complex.UnitDisc.sq_norm_lt_one z]) hden_pos

/--
%%handwave
name:
  The inverse Cayley transform sends the upper half-plane to the disk
statement:
  For \(z\) in the upper half-plane,
  \[
    \left|\frac{z-i}{z+i}\right| < 1.
  \]
proof:
  Squaring both sides reduces the inequality to
  \[
    (\operatorname{Re}z)^2+(\operatorname{Im}z-1)^2
      <(\operatorname{Re}z)^2+(\operatorname{Im}z+1)^2,
  \]
  which is exactly \(\operatorname{Im}z>0\).
-/
theorem upperHalfPlane_cayley_norm_lt_one (z : UpperHalfPlane) :
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
  Cayley transform from the disk to the upper half-plane
statement:
  The Cayley transform sends a disk point \(z\) to
  \[
    i\,\frac{1+z}{1-z}.
  \]
-/
noncomputable def unitDiscToUpperHalfPlane (z : Complex.UnitDisc) : UpperHalfPlane :=
  ⟨Complex.I * (1 + (z : ℂ)) / (1 - (z : ℂ)), unitDisc_cayley_im_pos z⟩

/--
%%handwave
name:
  Cayley transform from the upper half-plane to the disk
statement:
  The inverse Cayley transform sends an upper-half-plane point \(w\) to
  \[
    \frac{w-i}{w+i}.
  \]
-/
noncomputable def upperHalfPlaneToUnitDisc (w : UpperHalfPlane) : Complex.UnitDisc :=
  Complex.UnitDisc.mk (((w : ℂ) - Complex.I) / ((w : ℂ) + Complex.I))
    (upperHalfPlane_cayley_norm_lt_one w)

/--
%%handwave
name:
  The inverse Cayley transform undoes the Cayley transform
statement:
  Applying \(w\mapsto (w-i)/(w+i)\) after
  \(z\mapsto i(1+z)/(1-z)\) gives \(z\).
proof:
  This is a direct rational-function computation; the only denominator to
  exclude is \(1-z\), which is nonzero because \(|z|<1\).
-/
theorem upperHalfPlaneToUnitDisc_unitDiscToUpperHalfPlane
    (z : Complex.UnitDisc) :
    upperHalfPlaneToUnitDisc (unitDiscToUpperHalfPlane z) = z := by
  apply Complex.UnitDisc.coe_injective
  have hden : (1 : ℂ) - (z : ℂ) ≠ 0 := by
    intro h
    have hz_eq_one : (z : ℂ) = 1 := by
      linear_combination -h
    have hnorm : ‖(z : ℂ)‖ = 1 := by simp [hz_eq_one]
    linarith [Complex.UnitDisc.norm_lt_one z]
  simp [upperHalfPlaneToUnitDisc, unitDiscToUpperHalfPlane]
  field_simp [hden]
  ring_nf

/--
%%handwave
name:
  The Cayley transform undoes the inverse Cayley transform
statement:
  Applying \(z\mapsto i(1+z)/(1-z)\) after
  \(w\mapsto (w-i)/(w+i)\) gives \(w\).
proof:
  This is a direct rational-function computation; the only denominator to
  exclude is \(w+i\), which is nonzero in the upper half-plane.
-/
theorem unitDiscToUpperHalfPlane_upperHalfPlaneToUnitDisc
    (w : UpperHalfPlane) :
    unitDiscToUpperHalfPlane (upperHalfPlaneToUnitDisc w) = w := by
  apply UpperHalfPlane.ext
  have hden : (w : ℂ) + Complex.I ≠ 0 := by
    intro hzero
    have him : ((w : ℂ) + Complex.I).im = 0 := by rw [hzero]; simp
    have : w.im + 1 = 0 := by simpa [UpperHalfPlane.coe_im] using him
    linarith [w.im_pos]
  simp [unitDiscToUpperHalfPlane, upperHalfPlaneToUnitDisc]
  field_simp [hden]
  ring

/--
%%handwave
name:
  Cayley homeomorphism from the disk to the upper half-plane
statement:
  The Cayley transform is a homeomorphism from the open unit disk to the upper
  half-plane, with inverse \(w\mapsto (w-i)/(w+i)\).
proof:
  The two rational formulas are inverse by direct algebra, and the maps are
  continuous because their denominators do not vanish on the corresponding
  domains.
-/
noncomputable def unitDiscUpperHalfPlaneHomeomorph :
    Complex.UnitDisc ≃ₜ UpperHalfPlane where
  toFun := unitDiscToUpperHalfPlane
  invFun := upperHalfPlaneToUnitDisc
  left_inv := upperHalfPlaneToUnitDisc_unitDiscToUpperHalfPlane
  right_inv := unitDiscToUpperHalfPlane_upperHalfPlaneToUnitDisc
  continuous_toFun := by
    apply Continuous.upperHalfPlaneMk
    exact
      (continuous_const.mul (continuous_const.add Complex.UnitDisc.continuous_coe)).div
        (continuous_const.sub Complex.UnitDisc.continuous_coe) fun z h ↦ by
          have hz_eq_one : (z : ℂ) = 1 := by
            linear_combination -h
          have hnorm : ‖(z : ℂ)‖ = 1 := by simp [hz_eq_one]
          linarith [Complex.UnitDisc.norm_lt_one z]
  continuous_invFun := by
    apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
    exact
      (UpperHalfPlane.continuous_coe.sub continuous_const).div
        (UpperHalfPlane.continuous_coe.add continuous_const) fun z h ↦ by
          have him : ((z : ℂ) + Complex.I).im = 0 := by rw [h]; simp
          have : z.im + 1 = 0 := by simpa [UpperHalfPlane.coe_im] using him
          linarith [z.im_pos]

/--
%%handwave
name:
  The disk is biholomorphic to the upper half-plane
statement:
  The open unit disk is biholomorphic to the upper half-plane.
proof:
  Use the Cayley transform
  \[
    z \mapsto i\,\frac{1+z}{1-z}
  \]
  from the disk to the upper half-plane, with inverse
  \[
    w \mapsto \frac{w-i}{w+i}.
  \]
  The inequalities are the standard identities
  \[
    \operatorname{Im}\!\left(i\frac{1+z}{1-z}\right)
      = \frac{1-|z|^2}{|1-z|^2}
  \]
  and
  \[
    \left|\frac{w-i}{w+i}\right|^2
      = \frac{(\operatorname{Re} w)^2+(\operatorname{Im} w-1)^2}
             {(\operatorname{Re} w)^2+(\operatorname{Im} w+1)^2}.
  \]
  The two rational formulas are inverse to each other by algebra.  The maps
  are holomorphic because the denominators are nonzero on their domains, the
  [unit disk inclusion is holomorphic](lean:JJMath.Uniformization.holomorphicMap_unitDisc_coe),
  and the
  [upper-half-plane inclusion is holomorphic](lean:JJMath.Uniformization.holomorphicMap_upperHalfPlane_coe).
-/
theorem unitDisc_biholomorphicSurfaces_upperHalfPlane :
    BiholomorphicSurfaces Complex.UnitDisc UpperHalfPlane := by
  refine ⟨{
    toHomeomorph := unitDiscUpperHalfPlaneHomeomorph
    holomorphic_toFun := ?_
    holomorphic_invFun := ?_
  }⟩
  · refine holomorphicMap_upperHalfPlane_of_coe (F := unitDiscToUpperHalfPlane) ?_
    have hcoe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        (fun z : Complex.UnitDisc ↦ (z : ℂ)) :=
      contMDiff_unitDisc_coe
    have hnum : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        (fun z : Complex.UnitDisc ↦ Complex.I * (1 + (z : ℂ))) := by
      have hadd : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
          (fun z : Complex.UnitDisc ↦ 1 + (z : ℂ)) := by
        simpa using (contMDiff_const.add hcoe)
      simpa using (contMDiff_const.mul hadd)
    have hden : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        (fun z : Complex.UnitDisc ↦ 1 - (z : ℂ)) := by
      simpa using (contMDiff_const.sub hcoe)
    have hden_ne : ∀ z : Complex.UnitDisc, (1 : ℂ) - (z : ℂ) ≠ 0 := by
      intro z h
      have hz_eq_one : (z : ℂ) = 1 := by
        linear_combination -h
      have hnorm : ‖(z : ℂ)‖ = 1 := by simp [hz_eq_one]
      linarith [Complex.UnitDisc.norm_lt_one z]
    simpa [HolomorphicMap, unitDiscToUpperHalfPlane] using
      (hnum.div₀ hden hden_ne).mdifferentiable one_ne_zero
  · refine holomorphicMap_unitDisc_of_coe (F := upperHalfPlaneToUnitDisc) ?_
    have hcoe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        (fun z : UpperHalfPlane ↦ (z : ℂ)) :=
      contMDiff_upperHalfPlane_coe
    have hnum : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        (fun z : UpperHalfPlane ↦ (z : ℂ) - Complex.I) := by
      simpa using hcoe.sub contMDiff_const
    have hden : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
        (fun z : UpperHalfPlane ↦ (z : ℂ) + Complex.I) := by
      simpa using hcoe.add contMDiff_const
    have hden_ne : ∀ z : UpperHalfPlane, (z : ℂ) + Complex.I ≠ 0 := by
      intro z h
      have him : ((z : ℂ) + Complex.I).im = 0 := by rw [h]; simp
      have : z.im + 1 = 0 := by simpa [UpperHalfPlane.coe_im] using him
      linarith [z.im_pos]
    simpa [HolomorphicMap, upperHalfPlaneToUnitDisc] using
      (hnum.div₀ hden hden_ne).mdifferentiable one_ne_zero

/--
%%handwave
name:
  Disk and half-plane targets agree
statement:
  Being biholomorphic to the open unit disk implies being biholomorphic to the
  upper half-plane.
proof:
  Compose the disk equivalence with [the Cayley biholomorphism from the disk
  to the upper half-plane](lean:JJMath.Uniformization.unitDisc_biholomorphicSurfaces_upperHalfPlane).
-/
theorem biholomorphicToUpperHalfPlane_of_biholomorphicSurfaces_unitDisc
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : BiholomorphicSurfaces X Complex.UnitDisc) :
    BiholomorphicToUpperHalfPlane X := by
  simpa [BiholomorphicToUpperHalfPlane] using
    BiholomorphicSurfaces.trans h
      unitDisc_biholomorphicSurfaces_upperHalfPlane


end Uniformization

end JJMath
