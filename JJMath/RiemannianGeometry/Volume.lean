import JJMath.RiemannianGeometry.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Riemannian volume on finite-dimensional manifolds

Coordinate densities, chart-measure gluing, and existence of the Riemannian
volume measure for smooth finite-dimensional real Riemannian manifolds.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff Bundle MatrixOrder

namespace Uniformization

noncomputable section

/--
%%handwave
name:
  Smooth positive measure on a manifold
statement:
  A smooth positive measure on a finite-dimensional smooth manifold is a
  Borel measure whose local coordinate densities with respect to Lebesgue
  measure on the model space are smooth and strictly positive, and which is
  finite on compact sets.
-/
structure SmoothPositiveMeasureOnManifold {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] (μ : Measure X) : Prop where
  /-- Compact sets have finite measure. -/
  finite_on_compact : ∀ K : Set X, IsCompact K → μ K ≠ (∞ : ℝ≥0∞)
  /-- In each coordinate chart the measure has a smooth positive density. -/
  chart_density :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X),
      ∃ ρ : H → ℝ,
        ContDiffOn ℝ ∞ ρ e.target ∧
          (∀ z ∈ e.target, 0 < ρ z) ∧
          Measure.map e (μ.restrict e.source) =
            (MeasureTheory.volume.restrict e.target).withDensity
              (fun z : H ↦ ENNReal.ofReal (ρ z))

/--
%%handwave
name:
  Model basis for coordinate volume densities
statement:
  To write the local Riemannian volume density in coordinates on a
  finite-dimensional model vector space, choose a fixed real basis of the
  model space.
-/
abbrev ManifoldRiemannianVolumeBasisIndex (H : Type)
    [NormedAddCommGroup H] [NormedSpace ℝ H] : Type :=
  Module.Basis.ofVectorSpaceIndex ℝ H

/-- The fixed real basis used to write coordinate Gram determinants. -/
noncomputable def manifoldRiemannianVolumeBasis (H : Type)
    [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Module.Basis (ManifoldRiemannianVolumeBasisIndex H) ℝ H :=
  Module.Basis.ofVectorSpace ℝ H

/--
%%handwave
name:
  Transition map between manifold coordinates
statement:
  The transition map from one coordinate chart to another sends the coordinate
  of a point in the second chart to its coordinate in the first.
-/
noncomputable def manifoldChartTransition {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) : H → H :=
  fun z : H ↦ e (e'.symm z)

/--
%%handwave
name:
  Domain of a manifold chart overlap in coordinates
statement:
  The coordinate domain of an overlap consists of the points in the second
  chart whose corresponding manifold point also lies in the first chart.
-/
def manifoldChartOverlapDomain {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) : Set H :=
  e'.target ∩ e'.symm ⁻¹' e.source

/--
%%handwave
name:
  Range of a manifold chart overlap in coordinates
statement:
  The coordinate range of an overlap consists of the points in the first chart
  whose corresponding manifold point also lies in the second chart.
-/
def manifoldChartOverlapRange {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) : Set H :=
  e.target ∩ e.symm ⁻¹' e'.source

/-- The coordinate overlap domain is open. -/
theorem manifoldChartOverlapDomain_isOpen {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) :
    IsOpen (manifoldChartOverlapDomain e e') := by
  simpa [manifoldChartOverlapDomain] using
    (e'.isOpen_inter_preimage_symm e.open_source)

/-- The coordinate overlap range is open. -/
theorem manifoldChartOverlapRange_isOpen {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) :
    IsOpen (manifoldChartOverlapRange e e') := by
  simpa [manifoldChartOverlapRange] using
    (e.isOpen_inter_preimage_symm e'.open_source)

/-- The transition map identifies the two coordinate descriptions of an overlap. -/
theorem manifoldChartTransition_image_overlapDomain {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) :
    manifoldChartTransition e e' '' manifoldChartOverlapDomain e e' =
      manifoldChartOverlapRange e e' := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨hz_target, hz_source⟩
    have hx_source : e'.symm z ∈ e'.source := e'.symm.mapsTo hz_target
    have hT_target : e (e'.symm z) ∈ e.target := e.mapsTo hz_source
    have hsymm_eq : e.symm (e (e'.symm z)) = e'.symm z :=
      e.left_inv hz_source
    exact ⟨hT_target, by simpa [manifoldChartTransition, hsymm_eq] using hx_source⟩
  · intro hy
    rcases hy with ⟨hy_target, hy_source'⟩
    refine ⟨e' (e.symm y), ?_, ?_⟩
    · have hx_source : e.symm y ∈ e.source := e.symm.mapsTo hy_target
      have hz_target : e' (e.symm y) ∈ e'.target := e'.mapsTo hy_source'
      exact ⟨hz_target, by simpa [e'.left_inv hy_source'] using hx_source⟩
    · simp [manifoldChartTransition, e'.left_inv hy_source', e.right_inv hy_target]

/-- The transition map is injective on a coordinate overlap. -/
theorem manifoldChartTransition_injOn_overlapDomain {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) :
    Set.InjOn (manifoldChartTransition e e')
      (manifoldChartOverlapDomain e e') := by
  intro z₁ hz₁ z₂ hz₂ h
  rcases hz₁ with ⟨hz₁_target, hz₁_source⟩
  rcases hz₂ with ⟨hz₂_target, hz₂_source⟩
  have hsymm : e'.symm z₁ = e'.symm z₂ := by
    apply e.injOn hz₁_source hz₂_source
    simpa [manifoldChartTransition] using h
  calc
    z₁ = e' (e'.symm z₁) := (e'.right_inv hz₁_target).symm
    _ = e' (e'.symm z₂) := by rw [hsymm]
    _ = z₂ := e'.right_inv hz₂_target

/-- The transition map is continuous on a coordinate overlap. -/
theorem manifoldChartTransition_continuousOn_overlap {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) :
    ContinuousOn (manifoldChartTransition e e')
      (manifoldChartOverlapDomain e e') := by
  exact e.continuousOn.comp'
    (e'.continuousOn_symm.mono
      (by
        intro z hz
        exact hz.1))
    (by
      intro z hz
      exact hz.2)

/--
%%handwave
name:
  Manifold chart transitions are smooth in raw coordinates
statement:
  For a smooth manifold modeled on a finite-dimensional real normed vector
  space with the ordinary identity model, the transition map between two
  smooth charts is smooth on their raw-coordinate overlap.
proof:
  For the identity model, Mathlib's extended coordinate transition is exactly
  the ordinary raw coordinate transition.
-/
theorem manifoldChartTransition_contDiffOn_overlap {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] [IsManifold (𝓘(ℝ, H)) ∞ X]
    (e e' : OpenPartialHomeomorph X H)
    (_he : e ∈ atlas H X) (_he' : e' ∈ atlas H X) :
    ContDiffOn ℝ ∞ (manifoldChartTransition e e')
      (manifoldChartOverlapDomain e e') := by
  let I : ModelWithCorners ℝ H H := 𝓘(ℝ, H)
  have hI : ContDiff ℝ ∞ (I : H → H) := by
    simpa [I] using (contDiff_id : ContDiff ℝ ∞ (fun z : H ↦ z))
  have hIsymm : ContDiff ℝ ∞ (I.symm : H → H) := by
    simpa [I] using (contDiff_id : ContDiff ℝ ∞ (fun z : H ↦ z))
  let s : Set H := manifoldChartOverlapDomain e e'
  let G : H → H := I.extendCoordChange e' e
  have hG : ContDiffOn ℝ ∞ G (I.extendCoordChange e' e).source := by
    exact I.contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) _he')
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) _he)
  have hGI : ContDiffOn ℝ ∞ (G ∘ (I : H → H)) s := by
    refine hG.comp hI.contDiffOn ?_
    intro z hz
    rcases hz with ⟨hz_target, hz_source⟩
    rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source]
    constructor
    · rw [PartialEquiv.symm_source, OpenPartialHomeomorph.extend_target']
      exact ⟨z, hz_target, rfl⟩
    · rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_source]
      simpa [Function.comp_def, I.left_inv z] using hz_source
  have hraw :
      ContDiffOn ℝ ∞ ((I.symm : H → H) ∘ (G ∘ (I : H → H))) s :=
    hIsymm.comp_contDiffOn hGI
  refine hraw.congr ?_
  intro z hz
  rcases hz with ⟨hz_target, hz_source⟩
  show manifoldChartTransition e e' z = I.symm (G (I z))
  have hGz : G (I z) = I (manifoldChartTransition e e' z) := by
    simp only [G, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply, manifoldChartTransition, I.left_inv]
  rw [hGz]
  exact (I.left_inv _).symm

/--
%%handwave
name:
  Manifold chart transitions are differentiable in raw coordinates
statement:
  For a smooth manifold modeled on a finite-dimensional real normed vector
  space with the ordinary identity model, the ordinary transition map between
  two smooth charts is differentiable on the raw-coordinate overlap, with
  derivative given by its within-set Fréchet derivative.
proof:
  The transition is smooth on the overlap, hence differentiable there.
-/
theorem manifoldChartTransition_hasFDerivWithinAt_on_overlap {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] [IsManifold (𝓘(ℝ, H)) 1 X]
    (e e' : OpenPartialHomeomorph X H)
    (_he : e ∈ atlas H X) (_he' : e' ∈ atlas H X) :
    ∀ z ∈ manifoldChartOverlapDomain e e',
      HasFDerivWithinAt (manifoldChartTransition e e')
        (fderivWithin ℝ (manifoldChartTransition e e')
          (manifoldChartOverlapDomain e e') z)
        (manifoldChartOverlapDomain e e') z := by
  let I : ModelWithCorners ℝ H H := 𝓘(ℝ, H)
  have hI : ContDiff ℝ 1 (I : H → H) := by
    simpa [I] using (contDiff_id : ContDiff ℝ 1 (fun z : H ↦ z))
  have hIsymm : ContDiff ℝ 1 (I.symm : H → H) := by
    simpa [I] using (contDiff_id : ContDiff ℝ 1 (fun z : H ↦ z))
  let s : Set H := manifoldChartOverlapDomain e e'
  let G : H → H := I.extendCoordChange e' e
  have hG : ContDiffOn ℝ 1 G (I.extendCoordChange e' e).source := by
    exact I.contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := I) (n := 1) _he')
      (IsManifold.subset_maximalAtlas (I := I) (n := 1) _he)
  have hGI : ContDiffOn ℝ 1 (G ∘ (I : H → H)) s := by
    refine hG.comp hI.contDiffOn ?_
    intro z hz
    rcases hz with ⟨hz_target, hz_source⟩
    rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source]
    constructor
    · rw [PartialEquiv.symm_source, OpenPartialHomeomorph.extend_target']
      exact ⟨z, hz_target, rfl⟩
    · rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_source]
      simpa [Function.comp_def, I.left_inv z] using hz_source
  have hraw :
      ContDiffOn ℝ 1 ((I.symm : H → H) ∘ (G ∘ (I : H → H))) s :=
    hIsymm.comp_contDiffOn hGI
  have hcontDiff :
      ContDiffOn ℝ 1 (manifoldChartTransition e e') s := by
    refine hraw.congr ?_
    intro z hz
    rcases hz with ⟨hz_target, hz_source⟩
    show manifoldChartTransition e e' z = I.symm (G (I z))
    have hGz : G (I z) = I (manifoldChartTransition e e' z) := by
      simp only [G, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
        OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe,
        Function.comp_apply, manifoldChartTransition, I.left_inv]
    rw [hGz]
    exact (I.left_inv _).symm
  intro z hz
  exact (hcontDiff.differentiableOn (by simp) z hz).hasFDerivWithinAt

/--
%%handwave
name:
  Coordinate tangent frames transform by the transition derivative
statement:
  On the overlap of two smooth manifold charts, the coordinate tangent frame
  from the second chart is obtained from the coordinate tangent frame of the
  first chart by applying the derivative of the transition map.
proof:
  Apply the chain rule to the identity
  \(e'^{-1}=e^{-1}\circ(e\circ e'^{-1})\) on the coordinate overlap.  The
  differentiability set can be enlarged from the overlap to the full chart
  image because the overlap is a neighbourhood of the point inside the chart
  image.
-/
theorem manifoldChartTangentMap_comp_transition_on_overlap {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] [IsManifold (𝓘(ℝ, H)) ∞ X]
    (e e' : OpenPartialHomeomorph X H)
    (_he : e ∈ atlas H X) (_he' : e' ∈ atlas H X) :
    ∀ z ∈ manifoldChartOverlapDomain e e',
      fderivWithin ℝ
          (fun w : H ↦ chartAt H (e'.symm z) (e'.symm w)) e'.target z =
        (fderivWithin ℝ
            (fun w : H ↦
              chartAt H (e.symm (manifoldChartTransition e e' z)) (e.symm w))
            e.target (manifoldChartTransition e e' z)).comp
          (fderivWithin ℝ (manifoldChartTransition e e')
            (manifoldChartOverlapDomain e e') z) := by
  intro z hz
  let I : ModelWithCorners ℝ H H := 𝓘(ℝ, H)
  let s : Set H := manifoldChartOverlapDomain e e'
  let T : H → H := manifoldChartTransition e e'
  let x : X := e'.symm z
  let c : OpenPartialHomeomorph X H := chartAt H x
  rcases hz with ⟨hz_target, hz_source⟩
  have hz_s : z ∈ s := ⟨hz_target, hz_source⟩
  have hTz_target : T z ∈ e.target := by
    exact e.mapsTo hz_source
  have hbase_z : e.symm (T z) = e'.symm z := by
    simpa [T, manifoldChartTransition, x] using e.left_inv hz_source
  have hx_c_source : x ∈ c.source := by
    exact mem_chart_source H x
  let u : Set H := e.target ∩ e.symm ⁻¹' c.source
  let F : H → H := fun w ↦ c (e.symm w)
  have hcontDiff_F_u : ContDiffOn ℝ ∞ F u := by
    have h := I.contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) _he)
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) x)
    simpa [I, F, u, c, ModelWithCorners.extendCoordChange,
      PartialEquiv.trans_source] using h
  have hTz_u : T z ∈ u := by
    exact ⟨hTz_target, by simp [hbase_z, c, x, hx_c_source]⟩
  have hu_mem : u ∈ 𝓝[e.target] (T z) := by
    have hpre : e.symm ⁻¹' c.source ∈ 𝓝 (T z) := by
      exact (e.symm.continuousAt hTz_target).preimage_mem_nhds
        (c.open_source.mem_nhds (by simp [hbase_z, c, x, hx_c_source]))
    exact Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hpre)
  have hFdiff_u : DifferentiableWithinAt ℝ F u (T z) :=
    hcontDiff_F_u.differentiableOn (by simp) (T z) hTz_u
  have hFdiff : DifferentiableWithinAt ℝ F e.target (T z) :=
    hFdiff_u.mono_of_mem_nhdsWithin hu_mem
  have hFderiv :
      HasFDerivWithinAt F (fderivWithin ℝ F e.target (T z)) e.target (T z) :=
    hFdiff.hasFDerivWithinAt
  have hTderiv :
      HasFDerivWithinAt T
        (fderivWithin ℝ T s z) s z := by
    simpa [T, s] using
      manifoldChartTransition_hasFDerivWithinAt_on_overlap e e' _he _he' z hz_s
  have hmaps : Set.MapsTo T s e.target := by
    intro w hw
    exact e.mapsTo hw.2
  have hcomp :
      HasFDerivWithinAt (F ∘ T)
        ((fderivWithin ℝ F e.target (T z)).comp
          (fderivWithin ℝ T s z)) s z :=
    hFderiv.comp z hTderiv hmaps
  let F' : H → H := fun w ↦ chartAt H (e'.symm z) (e'.symm w)
  have hEq : Set.EqOn F' (F ∘ T) s := by
    intro w hw
    have hw_source : e'.symm w ∈ e.source := hw.2
    have hbase_w : e.symm (T w) = e'.symm w := by
      simpa [T, manifoldChartTransition] using e.left_inv hw_source
    simp [F', F, T, c, x, hbase_w]
  have hderiv_s :
      HasFDerivWithinAt F'
        ((fderivWithin ℝ F e.target (T z)).comp
          (fderivWithin ℝ T s z)) s z :=
    hcomp.congr hEq (hEq hz_s)
  have hs_nhds : s ∈ 𝓝[e'.target] z := by
    have hs_open : IsOpen s := by
      simpa [s] using manifoldChartOverlapDomain_isOpen e e'
    exact mem_nhdsWithin_of_mem_nhds (hs_open.mem_nhds hz_s)
  have hderiv_target :
      HasFDerivWithinAt F'
        ((fderivWithin ℝ F e.target (T z)).comp
          (fderivWithin ℝ T s z)) e'.target z :=
    hderiv_s.mono_of_mem_nhdsWithin hs_nhds
  have huniq : UniqueDiffWithinAt ℝ e'.target z :=
    e'.open_target.uniqueDiffWithinAt hz_target
  have hfinal := hderiv_target.fderivWithin huniq
  simpa [F', F, T, s, c, x, hbase_z] using hfinal

/--
%%handwave
name:
  Coordinate tangent vector fields are smooth on a manifold
statement:
  On a smooth manifold modeled on a finite-dimensional real normed vector
  space with the ordinary identity model, pushing a fixed coordinate tangent
  vector through the inverse of a smooth chart gives a smooth tangent-bundle
  valued map on the chart image.
proof:
  The inverse chart is smooth on its target.  Apply smoothness of the
  tangent map to this inverse chart, and evaluate it on the constant tangent
  vector in the model space.
-/
theorem manifoldChartCoordinateVector_contDiffOn {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] [IsManifold (𝓘(ℝ, H)) ∞ X]
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) (u : H) :
    ContMDiffOn (𝓘(ℝ, H)) (𝓘(ℝ, H)).tangent ∞
      (fun z : H ↦ (Bundle.TotalSpace.mk' H (e.symm z)
        (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z u) :
          TangentBundle (𝓘(ℝ, H)) X)) e.target := by
  let I : ModelWithCorners ℝ H H := 𝓘(ℝ, H)
  have hsymm : ContMDiffOn I I ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) _he)
  have hbaseVec : ContMDiffOn I I.tangent ∞
      (fun z : H ↦ (⟨z, u⟩ : TangentBundle I H)) e.target := by
    change ContMDiffOn I I.tangent ∞
        ((tangentBundleModelSpaceHomeomorph I).symm ∘
          fun z : H ↦ ((z, u) : ModelProd H H)) e.target
    refine (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := I)).contMDiffOn.comp (t := Set.univ) ?_ ?_
    · rw [← modelWithCornersSelf_prod]
      apply ContDiffOn.contMDiffOn
      fun_prop
    · intro z hz
      simp
  have htangent : ContMDiffOn I.tangent I.tangent ∞
      (tangentMapWithin I I e.symm e.target)
      (Bundle.TotalSpace.proj ⁻¹' e.target) := by
    exact hsymm.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      e.open_target.uniqueMDiffOn
  have hcomp : ContMDiffOn I I.tangent ∞
      ((tangentMapWithin I I e.symm e.target) ∘
        (fun z : H ↦ (⟨z, u⟩ : TangentBundle I H))) e.target := by
    exact htangent.comp hbaseVec (fun z hz => by simpa using hz)
  refine hcomp.congr ?_
  intro z hz
  have hmd : MDifferentiableWithinAt I I e.symm e.target z :=
    mdifferentiableOn_atlas_symm (I := I) _he z hz
  simp [tangentMapWithin, manifoldChartTangentVector, mfderivWithin,
    writtenInExtChartAt, I, hmd]
  rfl

/--
%%handwave
name:
  Metric Gram entries are smooth in a manifold coordinate chart
statement:
  In a smooth coordinate chart on a finite-dimensional Riemannian manifold,
  evaluating the Riemannian metric on two fixed coordinate tangent directions
  gives a smooth real-valued function.
proof:
  The metric is a smooth section of the bundle of tangent bilinear forms, and
  fixed coordinate tangent directions give smooth tangent-bundle sections.
  Smooth bundle-bilinear evaluation gives a smooth real-valued function.
-/
theorem manifoldMetricGramEntryInChart_contDiffOn {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] [IsManifold (𝓘(ℝ, H)) ∞ X]
    (g : ContMDiffRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) (u v : H) :
    ContDiffOn ℝ ∞ (fun z : H ↦
      g.inner (e.symm z)
        (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z u)
        (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v)) e.target := by
  let I : ModelWithCorners ℝ H H := 𝓘(ℝ, H)
  have hsymm : ContMDiffOn I I ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) _he)
  have hmetric : ContMDiffOn I
      (I.prod 𝓘(ℝ, H →L[ℝ] H →L[ℝ] ℝ)) ∞
      (fun z : H ↦ Bundle.TotalSpace.mk' (H →L[ℝ] H →L[ℝ] ℝ)
        (E := fun x : X ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (e.symm z) (g.inner (e.symm z))) e.target := by
    exact g.contMDiff.contMDiffOn.comp (t := Set.univ) hsymm
      (fun z hz => by simp)
  have hu := manifoldChartCoordinateVector_contDiffOn e _he u
  have hv := manifoldChartCoordinateVector_contDiffOn e _he v
  have htot : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : H ↦ Bundle.TotalSpace.mk' ℝ
        (E := Bundle.Trivial X ℝ) (e.symm z)
        (g.inner (e.symm z)
          (manifoldChartTangentVector (I := I) e z u)
          (manifoldChartTangentVector (I := I) e z v))) e.target := by
    exact ContMDiffOn.clm_bundle_apply₂ hmetric hu hv
  intro z hz
  have hz' := htot z hz
  rw [Bundle.contMDiffWithinAt_totalSpace] at hz'
  rcases hz' with ⟨_, hf⟩
  simpa [Bundle.Trivial.trivialization, I] using hf.contDiffWithinAt

/--
%%handwave
name:
  Metric Gram matrix in a manifold chart
statement:
  In a coordinate chart, the local Gram matrix of a Riemannian metric is the
  matrix of inner products of the coordinate tangent frame associated to a
  fixed basis of the model space.
-/
noncomputable def manifoldMetricGramMatrixInChart {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X)
    (e : OpenPartialHomeomorph X H) (z : H) :
    Matrix (ManifoldRiemannianVolumeBasisIndex H)
      (ManifoldRiemannianVolumeBasisIndex H) ℝ :=
  letI : IsManifold I ∞ X := g.isManifold
  let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
  Matrix.of fun i j ↦
    b (manifoldChartTangentVector (I := I) e z
        (manifoldRiemannianVolumeBasis H i))
      (manifoldChartTangentVector (I := I) e z
        (manifoldRiemannianVolumeBasis H j))

/--
%%handwave
name:
  Metric determinant in a manifold chart
statement:
  In a coordinate chart, the local metric determinant is the determinant of
  the Gram matrix of the coordinate tangent frame.
-/
noncomputable def manifoldMetricGramDetInChart {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X)
    (e : OpenPartialHomeomorph X H) (z : H) : ℝ := by
  classical
  exact (manifoldMetricGramMatrixInChart (I := I) g e z).det

/--
%%handwave
name:
  Riemannian volume density in a manifold chart
statement:
  In a coordinate chart, the Riemannian volume density is the square root of
  the determinant of the metric Gram matrix.
-/
noncomputable def manifoldMetricVolumeDensityInChart {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X)
    (e : OpenPartialHomeomorph X H) (z : H) : ℝ :=
  Real.sqrt (manifoldMetricGramDetInChart (I := I) g e z)

/--
%%handwave
name:
  Coordinate Gram determinant is smooth on a manifold
statement:
  In a smooth coordinate chart of a finite-dimensional Riemannian manifold,
  the determinant of the metric Gram matrix in the coordinate tangent frame is
  a smooth real-valued function on the chart image.
proof:
  The coordinate tangent frame depends smoothly on the chart coordinate, and
  the metric coefficients are smooth.  The determinant is a polynomial
  expression in these finitely many smooth coefficient functions.
-/
theorem manifoldMetricGramDetInChart_contDiffOn {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) :
    ContDiffOn ℝ ∞
      (manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e) e.target := by
  classical
  letI : IsManifold (𝓘(ℝ, H)) ∞ X := g.isManifold
  let ι : Type := ManifoldRiemannianVolumeBasisIndex H
  have hentry : ∀ i j : ι,
      ContDiffOn ℝ ∞
        (fun z : H ↦
          manifoldMetricGramMatrixInChart (I := 𝓘(ℝ, H)) g e z i j)
        e.target := by
    intro i j
    simpa [manifoldMetricGramMatrixInChart, ι] using
      manifoldMetricGramEntryInChart_contDiffOn
        (g := g.toContMDiffRiemannianMetric) e _he
        (manifoldRiemannianVolumeBasis H i)
        (manifoldRiemannianVolumeBasis H j)
  change ContDiffOn ℝ ∞
    (fun z : H ↦
      (manifoldMetricGramMatrixInChart (I := 𝓘(ℝ, H)) g e z).det) e.target
  rw [show
      (fun z : H ↦
        (manifoldMetricGramMatrixInChart (I := 𝓘(ℝ, H)) g e z).det) =
      (fun z : H ↦
        ∑ σ : Equiv.Perm ι,
          Equiv.Perm.sign σ •
            ∏ i : ι,
              manifoldMetricGramMatrixInChart (I := 𝓘(ℝ, H)) g e z (σ i) i) by
    funext z
    simpa [ι] using
      Matrix.det_apply
        (manifoldMetricGramMatrixInChart (I := 𝓘(ℝ, H)) g e z)]
  refine ContDiffOn.sum ?_
  intro σ _hσ
  exact (contDiffOn_prod fun i _hi => hentry (σ i) i).const_smul
    (Equiv.Perm.sign σ)

/--
%%handwave
name:
  Coordinate tangent map is invertible on a manifold
statement:
  In a genuine coordinate chart on a smooth manifold modeled on a
  finite-dimensional real vector space, the derivative of the inverse chart is
  a linear isomorphism from the model tangent space to the tangent fiber.
proof:
  Compare the inverse chart with the extended coordinate change from the
  given chart to the chart centered at the point.  The derivative of a smooth
  coordinate change is invertible, and restricting the differentiability set
  from the overlap to the chart image does not change the derivative near the
  point.
-/
theorem manifoldChartTangentMap_isInvertible_of_isManifold {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] [IsManifold (𝓘(ℝ, H)) ∞ X]
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) :
    ∀ z ∈ e.target,
      (fderivWithin ℝ
        (fun w : H ↦ chartAt H (e.symm z) (e.symm w)) e.target z).IsInvertible := by
  intro z hz
  let I : ModelWithCorners ℝ H H := 𝓘(ℝ, H)
  let c : OpenPartialHomeomorph X H := chartAt H (e.symm z)
  have hx_c : e.symm z ∈ c.source := by
    simp [c]
  have hz_source : z ∈ (I.extendCoordChange e c).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    refine ⟨e.symm z, ⟨?_, hx_c⟩, ?_⟩
    · exact e.symm.mapsTo hz
    · simp [I]
      exact e.right_inv hz
  have hinv_src :
      (fderivWithin ℝ (I.extendCoordChange e c)
        (I.extendCoordChange e c).source z).IsInvertible :=
    ModelWithCorners.isInvertible_fderivWithin_extendCoordChange
      (I := I) (n := ∞) (e := e) (e' := c)
      (by simp)
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) _he)
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) (e.symm z))
      hz_source
  have hpre_nhds : e.symm ⁻¹' c.source ∈ 𝓝 z :=
    (e.symm.continuousAt hz).preimage_mem_nhds (c.open_source.mem_nhds hx_c)
  have hsource_eq :
      (I.extendCoordChange e c).source =
        e.target ∩ e.symm ⁻¹' c.source := by
    simp [I, ModelWithCorners.extendCoordChange,
      PartialEquiv.trans_source, c]
  have hderiv_set :
      fderivWithin ℝ (I.extendCoordChange e c)
        (I.extendCoordChange e c).source z =
      fderivWithin ℝ (I.extendCoordChange e c) e.target z := by
    rw [hsource_eq]
    exact fderivWithin_inter hpre_nhds
  have hderiv_fun :
      fderivWithin ℝ (I.extendCoordChange e c) e.target z =
        fderivWithin ℝ
          (fun w : H ↦ chartAt H (e.symm z) (e.symm w)) e.target z := by
    simp [I, c, ModelWithCorners.extendCoordChange]
    rfl
  rw [hderiv_set, hderiv_fun] at hinv_src
  exact hinv_src

/--
%%handwave
name:
  Coordinate Gram determinant is positive on a manifold
statement:
  In a genuine coordinate chart of a finite-dimensional Riemannian manifold,
  the determinant of the metric Gram matrix in the coordinate tangent frame is
  strictly positive at every point of the chart image.
proof:
  The derivative of the inverse chart carries the fixed model-space basis to
  a basis of the tangent fiber.  A positive definite metric has positive
  definite Gram matrix on every basis, and a positive definite matrix has
  positive determinant.
-/
theorem manifoldMetricGramDetInChart_pos {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) :
    ∀ z ∈ e.target,
      0 < manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e z := by
  intro z hz
  classical
  letI : IsManifold (𝓘(ℝ, H)) ∞ X := g.isManifold
  let metric := g.toContMDiffRiemannianMetric.toRiemannianMetric
  letI : Bundle.RiemannianBundle
      (fun x : X ↦ TangentSpace (𝓘(ℝ, H)) x) := ⟨metric⟩
  let A : H →L[ℝ] H :=
    fderivWithin ℝ
      (fun w : H ↦ chartAt H (e.symm z) (e.symm w)) e.target z
  let v : ManifoldRiemannianVolumeBasisIndex H →
      TangentSpace (𝓘(ℝ, H)) (e.symm z) :=
    fun i ↦ manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z
      (manifoldRiemannianVolumeBasis H i)
  have hAinv : A.IsInvertible := by
    simpa [A] using
      manifoldChartTangentMap_isInvertible_of_isManifold e _he z hz
  have hAinj : Function.Injective A :=
    ContinuousLinearMap.IsInvertible.injective hAinv
  have hv : LinearIndependent ℝ v := by
    simpa [v, A, manifoldChartTangentVector, Function.comp_def] using
      (manifoldRiemannianVolumeBasis H).linearIndependent.map'
        A.toLinearMap (LinearMap.ker_eq_bot.mpr hAinj)
  have hgram : (Matrix.gram ℝ v).PosDef :=
    Matrix.posDef_gram_of_linearIndependent hv
  have hpos :
      (manifoldMetricGramMatrixInChart (I := 𝓘(ℝ, H)) g e z).PosDef := by
    convert hgram using 1
  simpa [manifoldMetricGramDetInChart] using hpos.det_pos

/--
%%handwave
name:
  Riemannian volume in one manifold chart
statement:
  In a coordinate chart, the local Riemannian volume measure is Lebesgue
  measure restricted to the chart image, weighted by the square root of the
  metric determinant.
-/
noncomputable def manifoldRiemannianVolumeChartMeasure {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X)
    (e : OpenPartialHomeomorph X H) : Measure H :=
  (MeasureTheory.volume.restrict e.target).withDensity
    (fun z : H ↦ ENNReal.ofReal
      (manifoldMetricVolumeDensityInChart (I := I) g e z))

/-- The coordinate Riemannian volume measure is supported on the chart image. -/
theorem manifoldRiemannianVolumeChartMeasure_restrict_target {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X)
    (e : OpenPartialHomeomorph X H) :
    (manifoldRiemannianVolumeChartMeasure (I := I) g e).restrict e.target =
      manifoldRiemannianVolumeChartMeasure (I := I) g e := by
  rw [manifoldRiemannianVolumeChartMeasure,
    restrict_withDensity e.open_target.measurableSet]
  rw [Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
    (s := e.target) (t := e.target) (by intro z hz; exact hz)]

/--
%%handwave
name:
  Coordinate Riemannian volume density is smooth and positive on a manifold
statement:
  In a coordinate chart of a finite-dimensional smooth Riemannian manifold,
  the Riemannian volume density is a smooth strictly positive function on the
  chart image.
proof:
  The coordinate tangent frame depends smoothly on the chart coordinate, and
  the metric coefficients are smooth.  Therefore the Gram determinant is
  smooth.  The chart tangent map is a linear isomorphism at each point, and
  positive definiteness of the metric makes the Gram determinant strictly
  positive; smoothness of the square root follows on this positive set.
-/
theorem manifoldMetricVolumeDensityInChart_smooth_positive {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) :
    ContDiffOn ℝ ∞
        (manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e) e.target ∧
      ∀ z ∈ e.target,
        0 < manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e z := by
  constructor
  · have hdet : ContDiffOn ℝ ∞
        (manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e) e.target :=
      manifoldMetricGramDetInChart_contDiffOn g e _he
    have hpos : ∀ z ∈ e.target,
        manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e z ≠ 0 := by
      intro z hz
      exact ne_of_gt (manifoldMetricGramDetInChart_pos g e _he z hz)
    simpa [manifoldMetricVolumeDensityInChart] using hdet.sqrt hpos
  · intro z hz
    rw [manifoldMetricVolumeDensityInChart]
    exact Real.sqrt_pos.mpr
      (manifoldMetricGramDetInChart_pos g e _he z hz)

/--
%%handwave
name:
  Coordinate Riemannian volume is finite on compact subsets
statement:
  The local Riemannian volume measure of a chart is finite on compact subsets
  of the chart image.
proof:
  The density is continuous, hence bounded on compact subsets of the chart
  image.  Compact subsets of the finite-dimensional model space have finite
  Lebesgue measure, so the weighted measure is finite there.
-/
theorem manifoldRiemannianVolumeChartMeasure_finite_on_compact {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) :
    ∀ K : Set H, IsCompact K → K ⊆ e.target →
      manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e K ≠
        (∞ : ℝ≥0∞) := by
  intro K hK hK_subset
  let ρ : H → ℝ := manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e
  have hK_meas : MeasurableSet K := hK.measurableSet
  have hρ_smooth : ContDiffOn ℝ ∞ ρ e.target :=
    (manifoldMetricVolumeDensityInChart_smooth_positive g e _he).1
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_subset
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hρ_cont_K
  have hρ_le_C : ∀ z ∈ K, ENNReal.ofReal (ρ z) ≤ ENNReal.ofReal C := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal ((le_abs_self (ρ z)).trans (hC z hz))
  have hbase_finite :
      (MeasureTheory.volume.restrict e.target) K < (∞ : ℝ≥0∞) :=
    hK.measure_lt_top (μ := MeasureTheory.volume.restrict e.target)
  have hconst_finite :
      (∫⁻ _ in K, ENNReal.ofReal C ∂(MeasureTheory.volume.restrict e.target)) <
        (∞ : ℝ≥0∞) := by
    have hmul :
        ENNReal.ofReal C *
          (MeasureTheory.volume.restrict e.target).restrict K Set.univ <
            (∞ : ℝ≥0∞) := by
      simpa [hK_meas] using ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbase_finite
    simpa [lintegral_const] using hmul
  have hweighted_finite :
      (∫⁻ z in K, ENNReal.ofReal (ρ z) ∂(MeasureTheory.volume.restrict e.target)) <
        (∞ : ℝ≥0∞) :=
    lt_of_le_of_lt
      (setLIntegral_mono' hK_meas hρ_le_C)
      hconst_finite
  rw [manifoldRiemannianVolumeChartMeasure, withDensity_apply _ hK_meas]
  exact hweighted_finite.ne

/--
%%handwave
name:
  Compatibility of manifold coordinate volume measures
statement:
  The local Riemannian volume measures are compatible when, on every overlap
  of two coordinate charts, the transition map carries the measure written in
  one coordinate to the measure written in the other.
-/
def RiemannianVolumeChartMeasuresCompatibleOnManifold {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) : Prop :=
  ∀ (e e' : OpenPartialHomeomorph X H)
      (_he : e ∈ atlas H X) (_he' : e' ∈ atlas H X),
    Measure.map (manifoldChartTransition e e')
      ((manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e').restrict
        (manifoldChartOverlapDomain e e')) =
      (manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e).restrict
        (manifoldChartOverlapRange e e')

/--
%%handwave
name:
  Weighted change of variables on a manifold coordinate overlap
statement:
  Let \(F\) be an injective differentiable transition map between measurable
  subsets of a finite-dimensional model vector space.  If the source density
  is the target density pulled back by \(F\), multiplied by the absolute
  Jacobian determinant, then pushing forward the source weighted Lebesgue
  measure gives the target weighted Lebesgue measure.
proof:
  This is the finite-dimensional differentiable change-of-variables theorem
  for Haar/Lebesgue measure, followed by the elementary identity for
  restricting and pushing forward measures with densities.
-/
theorem weighted_changeOfVariablesOn_manifold_overlap {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [FiniteDimensional ℝ H]
    {s t : Set H} (F : H → H)
    (ρs ρt : H → ℝ≥0∞)
    (hs : MeasurableSet s)
    (_ht : MeasurableSet t)
    (himage : F '' s = t)
    (hF :
      ∀ z ∈ s, HasFDerivWithinAt F (fderivWithin ℝ F s z) s z)
    (hinj : Set.InjOn F s)
    (hdensity :
      ∀ z ∈ s,
        ρs z = ENNReal.ofReal |(fderivWithin ℝ F s z).det| * ρt (F z)) :
    Measure.map F ((MeasureTheory.volume.restrict s).withDensity ρs) =
      (MeasureTheory.volume.restrict t).withDensity ρt := by
  apply Measure.ext
  intro A hA
  have hF_cont : ContinuousOn F s := by
    intro z hz
    exact (hF z hz).continuousWithinAt
  have hF_aemeas_s : AEMeasurable F (MeasureTheory.volume.restrict s) := by
    exact hF_cont.aemeasurable₀ hs.nullMeasurableSet
  have hF_aemeas_source :
      AEMeasurable F ((MeasureTheory.volume.restrict s).withDensity ρs) :=
    hF_aemeas_s.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [Measure.map_apply_of_aemeasurable hF_aemeas_source hA]
  have hpre : NullMeasurableSet (F ⁻¹' A) (MeasureTheory.volume.restrict s) :=
    hF_aemeas_s.nullMeasurableSet_preimage hA
  rw [withDensity_apply₀ _ hpre]
  rw [withDensity_apply _ hA]
  change (∫⁻ x, ρs x ∂((MeasureTheory.volume.restrict s).restrict (F ⁻¹' A))) =
    (∫⁻ x, ρt x ∂((MeasureTheory.volume.restrict t).restrict A))
  rw [Measure.restrict_restrict₀ hpre]
  rw [Measure.restrict_restrict hA]
  let J : H → ℝ≥0∞ :=
    fun x ↦ ENNReal.ofReal |(fderivWithin ℝ F s x).det|
  have hρ :
      (∫⁻ x in F ⁻¹' A ∩ s, ρs x ∂MeasureTheory.volume)
        =
      (∫⁻ x in F ⁻¹' A ∩ s, J x * ρt (F x) ∂MeasureTheory.volume) := by
    apply lintegral_congr_ae
    have hpre_inter :
        NullMeasurableSet (F ⁻¹' A ∩ s) MeasureTheory.volume :=
      (nullMeasurableSet_restrict hs.nullMeasurableSet).1 hpre
    filter_upwards [ae_restrict_mem₀ hpre_inter] with x hx
    have hx_s : x ∈ s := hx.2
    simpa [J] using hdensity x hx_s
  rw [hρ]
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := MeasureTheory.volume) hs hF hinj (fun y : H ↦ A.indicator ρt y)
  rw [himage] at hcov
  have hsource_indicator :
      (∫⁻ x in s, J x * A.indicator ρt (F x) ∂MeasureTheory.volume)
        =
      (∫⁻ x in F ⁻¹' A ∩ s, J x * ρt (F x) ∂MeasureTheory.volume) := by
    rw [← setLIntegral_indicator₀
      (μ := MeasureTheory.volume)
      (f := fun x : H ↦ J x * ρt (F x))
      (s := F ⁻¹' A) (t := s) hpre]
    apply setLIntegral_congr_fun hs
    intro x _hx
    by_cases hxA : F x ∈ A
    · have hxpre : x ∈ F ⁻¹' A := hxA
      rw [Set.indicator_of_mem hxpre]
      change J x * A.indicator ρt (F x) = J x * ρt (F x)
      rw [Set.indicator_of_mem hxA]
    · have hxpre : x ∉ F ⁻¹' A := hxA
      rw [Set.indicator_of_notMem hxpre]
      change J x * A.indicator ρt (F x) = 0
      rw [Set.indicator_of_notMem hxA, mul_zero]
  calc
    (∫⁻ x in F ⁻¹' A ∩ s, J x * ρt (F x) ∂MeasureTheory.volume)
        = ∫⁻ x in s, J x * A.indicator ρt (F x) ∂MeasureTheory.volume :=
      hsource_indicator.symm
    _ = ∫⁻ y in t, A.indicator ρt y ∂MeasureTheory.volume := by
      simpa [J] using hcov.symm
    _ = ∫⁻ y in A ∩ t, ρt y ∂MeasureTheory.volume :=
      setLIntegral_indicator hA ρt

/-- A finite-dimensional Gram determinant transforms by the square of the determinant. -/
theorem manifoldMetricGramDet_comp_continuousLinearMap {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [DecidableEq (ManifoldRiemannianVolumeBasisIndex H)]
    (b : H →L[ℝ] H →L[ℝ] ℝ) (A J : H →L[ℝ] H) :
    (Matrix.of fun i j : ManifoldRiemannianVolumeBasisIndex H ↦
      b ((A.comp J) (manifoldRiemannianVolumeBasis H i))
        ((A.comp J) (manifoldRiemannianVolumeBasis H j))).det =
      J.det ^ 2 *
        (Matrix.of fun i j : ManifoldRiemannianVolumeBasisIndex H ↦
          b (A (manifoldRiemannianVolumeBasis H i))
            (A (manifoldRiemannianVolumeBasis H j))).det := by
  classical
  let ι : Type := ManifoldRiemannianVolumeBasisIndex H
  letI : DecidableEq ι := inferInstance
  let basis : Module.Basis ι ℝ H := manifoldRiemannianVolumeBasis H
  let B : LinearMap.BilinForm ℝ H :=
    LinearMap.mk₂ ℝ (fun x y : H ↦ b x y)
      (by intro x y z; simp)
      (by intro a x y; simp)
      (by intro x y z; simp)
      (by intro a x y; simp)
  let Aₗ : H →ₗ[ℝ] H := A
  let Jₗ : H →ₗ[ℝ] H := J
  let B₀ : LinearMap.BilinForm ℝ H := B.comp Aₗ Aₗ
  let M : Matrix ι ι ℝ := LinearMap.BilinForm.toMatrix basis B₀
  let P : Matrix ι ι ℝ := LinearMap.toMatrix basis basis Jₗ
  have hleft :
      (Matrix.of fun i j : ι ↦
        b ((A.comp J) (basis i)) ((A.comp J) (basis j))) =
        LinearMap.BilinForm.toMatrix basis (B₀.comp Jₗ Jₗ) := by
    ext i j
    simp [B₀, B, Aₗ, Jₗ, basis, ContinuousLinearMap.comp_apply,
      LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.comp_apply]
  have hright :
      (Matrix.of fun i j : ι ↦ b (A (basis i)) (A (basis j))) = M := by
    ext i j
    simp [M, B₀, B, Aₗ, basis, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.comp_apply]
  have hmatrix :
      LinearMap.BilinForm.toMatrix basis (B₀.comp Jₗ Jₗ) =
        P.transpose * M * P := by
    simpa [P, M] using
      (LinearMap.BilinForm.toMatrix_comp
        (b := basis) (c := basis) B₀ Jₗ Jₗ)
  have hdetP : P.det = J.det := by
    simp [P, Jₗ, ContinuousLinearMap.det]
  calc
    (Matrix.of fun i j : ι ↦
      b ((A.comp J) (basis i)) ((A.comp J) (basis j))).det
        = (P.transpose * M * P).det := by
          rw [hleft, hmatrix]
    _ = P.det ^ 2 * M.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring
    _ = J.det ^ 2 *
        (Matrix.of fun i j : ι ↦ b (A (basis i)) (A (basis j))).det := by
      rw [hdetP, hright]

/--
%%handwave
name:
  Transformation law for manifold coordinate volume densities
statement:
  On the overlap of two smooth coordinate charts, the Riemannian density in
  the source coordinates is the target density pulled back by the transition
  map, multiplied by the absolute Jacobian determinant.
proof:
  The coordinate tangent frames are related by the derivative of the
  transition map.  Thus the two Gram matrices are related by
  \(G' = J^\mathsf{T} GJ\).  Taking determinants and then positive square
  roots gives the absolute-Jacobian factor.
-/
theorem manifoldMetricVolumeDensityInChart_transform_on_overlap {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (e e' : OpenPartialHomeomorph X H)
    (_he : e ∈ atlas H X) (_he' : e' ∈ atlas H X) :
    ∀ z ∈ manifoldChartOverlapDomain e e',
      ENNReal.ofReal
          (manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e' z) =
        ENNReal.ofReal
          |(fderivWithin ℝ (manifoldChartTransition e e')
            (manifoldChartOverlapDomain e e') z).det| *
          ENNReal.ofReal
            (manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e
              (manifoldChartTransition e e' z)) := by
  letI : IsManifold (𝓘(ℝ, H)) ∞ X := g.isManifold
  classical
  intro z hz
  let T : H → H := manifoldChartTransition e e'
  let s : Set H := manifoldChartOverlapDomain e e'
  let J : H →L[ℝ] H := fderivWithin ℝ T s z
  let A : H →L[ℝ] H :=
    fderivWithin ℝ
      (fun w : H ↦ chartAt H (e.symm (T z)) (e.symm w)) e.target (T z)
  let A' : H →L[ℝ] H :=
    fderivWithin ℝ
      (fun w : H ↦ chartAt H (e'.symm z) (e'.symm w)) e'.target z
  let b : H →L[ℝ] H →L[ℝ] ℝ :=
    show H →L[ℝ] H →L[ℝ] ℝ from
      g.toContMDiffRiemannianMetric.inner (e'.symm z)
  rcases hz with ⟨hz_target, hz_source⟩
  have hz_s : z ∈ s := ⟨hz_target, hz_source⟩
  have hbase : e.symm (T z) = e'.symm z := by
    simpa [T, manifoldChartTransition] using e.left_inv hz_source
  have hframe : A' = A.comp J := by
    simpa [A, A', J, T, s] using
      manifoldChartTangentMap_comp_transition_on_overlap e e' _he _he' z hz_s
  have hgram :
      manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e' z =
        J.det ^ 2 *
          manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e (T z) := by
    have hlin := manifoldMetricGramDet_comp_continuousLinearMap b A J
    have hleft :
        manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e' z =
          (Matrix.of fun i j : ManifoldRiemannianVolumeBasisIndex H ↦
            b ((A.comp J) (manifoldRiemannianVolumeBasis H i))
              ((A.comp J) (manifoldRiemannianVolumeBasis H j))).det := by
      simp [manifoldMetricGramDetInChart, manifoldMetricGramMatrixInChart,
        manifoldChartTangentVector, A', hframe, b,
        ContinuousLinearMap.comp_apply]
      rfl
    have hright :
        (Matrix.of fun i j : ManifoldRiemannianVolumeBasisIndex H ↦
          b (A (manifoldRiemannianVolumeBasis H i))
            (A (manifoldRiemannianVolumeBasis H j))).det =
          manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e (T z) := by
      have hbase' :
          e.symm (manifoldChartTransition e e' z) = e'.symm z := by
        simpa [T] using hbase
      simp [manifoldMetricGramDetInChart, manifoldMetricGramMatrixInChart,
        manifoldChartTangentVector, A, T, b]
      rw [hbase']
      rfl
    calc
      manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e' z =
          (Matrix.of fun i j : ManifoldRiemannianVolumeBasisIndex H ↦
            b ((A.comp J) (manifoldRiemannianVolumeBasis H i))
              ((A.comp J) (manifoldRiemannianVolumeBasis H j))).det := hleft
      _ = J.det ^ 2 *
          (Matrix.of fun i j : ManifoldRiemannianVolumeBasisIndex H ↦
            b (A (manifoldRiemannianVolumeBasis H i))
              (A (manifoldRiemannianVolumeBasis H j))).det := hlin
      _ = J.det ^ 2 *
          manifoldMetricGramDetInChart (I := 𝓘(ℝ, H)) g e (T z) := by
        rw [hright]
  have hsqrt :
      manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e' z =
        |J.det| *
          manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e (T z) := by
    rw [manifoldMetricVolumeDensityInChart, manifoldMetricVolumeDensityInChart,
      hgram]
    rw [Real.sqrt_mul (sq_nonneg J.det)]
    rw [Real.sqrt_sq_eq_abs]
  rw [show fderivWithin ℝ (manifoldChartTransition e e')
        (manifoldChartOverlapDomain e e') z = J by rfl]
  rw [show manifoldChartTransition e e' z = T z by rfl]
  rw [← ENNReal.ofReal_mul (abs_nonneg J.det)]
  exact congrArg ENNReal.ofReal hsqrt

/--
%%handwave
name:
  Coordinate volume measures agree on manifold chart overlaps
statement:
  If the Riemannian coordinate densities satisfy the Jacobian
  transformation law on a chart overlap, then the transition map carries the
  source coordinate volume measure to the target coordinate volume measure.
proof:
  Restrict both coordinate measures to the overlap and unfold them as
  weighted Lebesgue measures.  The weighted change-of-variables theorem
  applies to the smooth injective transition map.
-/
theorem riemannianVolumeChartMeasure_map_overlap_eq_of_density_transform_on_manifold
    {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (e e' : OpenPartialHomeomorph X H)
    (_he : e ∈ atlas H X) (_he' : e' ∈ atlas H X)
    (_hdensity :
      ∀ z ∈ manifoldChartOverlapDomain e e',
        ENNReal.ofReal
            (manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e' z) =
          ENNReal.ofReal
            |(fderivWithin ℝ (manifoldChartTransition e e')
              (manifoldChartOverlapDomain e e') z).det| *
            ENNReal.ofReal
              (manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e
                (manifoldChartTransition e e' z))) :
    Measure.map (manifoldChartTransition e e')
      ((manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e').restrict
        (manifoldChartOverlapDomain e e')) =
      (manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e).restrict
        (manifoldChartOverlapRange e e') := by
  letI : IsManifold (𝓘(ℝ, H)) ∞ X := g.isManifold
  let s : Set H := manifoldChartOverlapDomain e e'
  let t : Set H := manifoldChartOverlapRange e e'
  let F : H → H := manifoldChartTransition e e'
  let ρs : H → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal
      (manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e' z)
  let ρt : H → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal
      (manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e z)
  have hs_open : IsOpen s := by
    simpa [s] using manifoldChartOverlapDomain_isOpen e e'
  have ht_open : IsOpen t := by
    simpa [t] using manifoldChartOverlapRange_isOpen e e'
  have hs : MeasurableSet s := hs_open.measurableSet
  have ht : MeasurableSet t := ht_open.measurableSet
  have hs_subset : s ⊆ e'.target := by
    intro z hz
    exact hz.1
  have ht_subset : t ⊆ e.target := by
    intro z hz
    exact hz.1
  have hleft :
      (manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e').restrict s =
        (MeasureTheory.volume.restrict s).withDensity ρs := by
    rw [manifoldRiemannianVolumeChartMeasure, restrict_withDensity hs]
    rw [Measure.restrict_restrict_of_subset hs_subset]
  have hright :
      (manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e).restrict t =
        (MeasureTheory.volume.restrict t).withDensity ρt := by
    rw [manifoldRiemannianVolumeChartMeasure, restrict_withDensity ht]
    rw [Measure.restrict_restrict_of_subset ht_subset]
  rw [show manifoldChartOverlapDomain e e' = s by rfl,
    show manifoldChartOverlapRange e e' = t by rfl, hleft, hright]
  exact weighted_changeOfVariablesOn_manifold_overlap F ρs ρt hs ht
    (by simpa [F, s, t] using manifoldChartTransition_image_overlapDomain e e')
    (by
      intro z hz
      simpa [F, s] using
        manifoldChartTransition_hasFDerivWithinAt_on_overlap
          e e' _he _he' z hz)
    (by simpa [F, s] using manifoldChartTransition_injOn_overlapDomain e e')
    (by
      intro z hz
      simpa [F, s, ρs, ρt] using _hdensity z hz)

/--
%%handwave
name:
  Smooth manifold metrics give compatible coordinate volume measures
statement:
  The coordinate volume measures determined by a smooth Riemannian metric are
  compatible on chart overlaps.
proof:
  On an overlap, the two coordinate tangent frames are related by the
  derivative of the transition map.  The Gram determinant changes by the
  square of the absolute Jacobian determinant, so the square-root density
  changes by the absolute Jacobian determinant.  The smooth change-of-
  variables theorem for finite-dimensional Lebesgue measure then identifies
  the pushed-forward weighted measures.
-/
theorem riemannianVolumeChartMeasuresCompatibleOnManifold_of_smoothMetric {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) :
    RiemannianVolumeChartMeasuresCompatibleOnManifold g := by
  intro e e' he he'
  exact riemannianVolumeChartMeasure_map_overlap_eq_of_density_transform_on_manifold
    g e e' he he'
    (manifoldMetricVolumeDensityInChart_transform_on_overlap g e e' he he')

/-- On a second-countable charted space, preferred chart sources cover the space
    after passing to a countable set of centers. -/
theorem exists_countable_manifoldChartAt_source_cover
    (H X : Type) [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    [SecondCountableTopology X] :
    ∃ S : Set X, S.Countable ∧
      (⋃ x ∈ S, (chartAt H x).source) = Set.univ := by
  exact countable_cover_nhds (fun x : X ↦ chart_source_mem_nhds H x)

/-- The `n`-th disjoint source piece of a sequence of manifold charts. -/
def manifoldChartMeasureGluingSourcePiece {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (c : ℕ → X) (n : ℕ) : Set X :=
  disjointed (fun m : ℕ ↦ (chartAt H (c m)).source) n

theorem manifoldChartMeasureGluingSourcePiece_subset {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (c : ℕ → X) (n : ℕ) :
    manifoldChartMeasureGluingSourcePiece (H := H) c n ⊆
      (chartAt H (c n)).source := by
  exact disjointed_subset _ _

theorem pairwise_disjoint_manifoldChartMeasureGluingSourcePiece {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (c : ℕ → X) :
    Pairwise (fun i j ↦
      Disjoint (manifoldChartMeasureGluingSourcePiece (H := H) c i)
        (manifoldChartMeasureGluingSourcePiece (H := H) c j)) := by
  simpa [manifoldChartMeasureGluingSourcePiece] using
    disjoint_disjointed (fun n : ℕ ↦ (chartAt H (c n)).source)

theorem iUnion_manifoldChartMeasureGluingSourcePiece {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (c : ℕ → X) :
    (⋃ n, manifoldChartMeasureGluingSourcePiece (H := H) c n) =
      ⋃ n, (chartAt H (c n)).source := by
  simpa [manifoldChartMeasureGluingSourcePiece] using
    (iUnion_disjointed (f := fun n : ℕ ↦ (chartAt H (c n)).source))

theorem iUnion_manifoldChartMeasureGluingSourcePiece_eq_univ {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt H (c n)).source) = Set.univ) :
    (⋃ n, manifoldChartMeasureGluingSourcePiece (H := H) c n) = Set.univ := by
  rw [iUnion_manifoldChartMeasureGluingSourcePiece (H := H) c, hc_cover]

theorem measurableSet_manifoldChartMeasureGluingSourcePiece {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X]
    (c : ℕ → X) (n : ℕ) :
    MeasurableSet (manifoldChartMeasureGluingSourcePiece (H := H) c n) := by
  exact MeasurableSet.disjointed
    (fun m : ℕ ↦ (chartAt H (c m)).open_source.measurableSet) n

/-- The coordinate image of one disjoint source piece. -/
def manifoldChartMeasureGluingTargetPiece {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (c : ℕ → X) (n : ℕ) : Set H :=
  (chartAt H (c n)) '' manifoldChartMeasureGluingSourcePiece (H := H) c n

theorem manifoldChartMeasureGluingTargetPiece_subset {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (c : ℕ → X) (n : ℕ) :
    manifoldChartMeasureGluingTargetPiece (H := H) c n ⊆
      (chartAt H (c n)).target := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact (chartAt H (c n)).map_source
    (manifoldChartMeasureGluingSourcePiece_subset (H := H) c n hx)

theorem measurableSet_manifoldChartMeasureGluingTargetPiece {H X : Type}
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace X] [ChartedSpace H X] [MeasurableSpace X] [BorelSpace X]
    (c : ℕ → X) (n : ℕ) :
    MeasurableSet (manifoldChartMeasureGluingTargetPiece (H := H) c n) := by
  let e : OpenPartialHomeomorph X H := chartAt H (c n)
  let P : Set X := manifoldChartMeasureGluingSourcePiece (H := H) c n
  let Psub : Set e.source := {x : e.source | (x : X) ∈ P}
  have hP : MeasurableSet P :=
    measurableSet_manifoldChartMeasureGluingSourcePiece (H := H) c n
  have hPsub : MeasurableSet Psub := by
    exact hP.preimage measurable_subtype_coe
  have htarget_sub :
      MeasurableSet (e.toHomeomorphSourceTarget '' Psub) :=
    e.toHomeomorphSourceTarget.measurableEmbedding.measurableSet_image' hPsub
  have htarget :
      MeasurableSet (((↑) : e.target → H) ''
        (e.toHomeomorphSourceTarget '' Psub)) :=
    e.open_target.measurableSet.subtype_image htarget_sub
  convert htarget using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨e x,
        e.map_source (manifoldChartMeasureGluingSourcePiece_subset (H := H) c n hx)⟩,
      ⟨⟨x, manifoldChartMeasureGluingSourcePiece_subset (H := H) c n hx⟩,
        hx, rfl⟩, rfl⟩
  · rintro ⟨z', ⟨x, hx, hz'⟩, hz⟩
    rcases x with ⟨x, hx_source⟩
    subst z
    subst z'
    exact ⟨x, hx, rfl⟩

/-- A source piece viewed in the target coordinates of a fixed chart. -/
def manifoldChartMeasureGluingOverlapTargetPiece {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e : OpenPartialHomeomorph X H) (c : ℕ → X) (n : ℕ) : Set H :=
  e '' (manifoldChartMeasureGluingSourcePiece (H := H) c n ∩ e.source)

theorem manifoldChartMeasureGluingOverlapTargetPiece_subset {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e : OpenPartialHomeomorph X H) (c : ℕ → X) (n : ℕ) :
    manifoldChartMeasureGluingOverlapTargetPiece e c n ⊆ e.target := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact e.map_source hx.2

theorem measurableSet_manifoldChartMeasureGluingOverlapTargetPiece {H X : Type}
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace X] [ChartedSpace H X] [MeasurableSpace X] [BorelSpace X]
    (e : OpenPartialHomeomorph X H) (c : ℕ → X) (n : ℕ) :
    MeasurableSet (manifoldChartMeasureGluingOverlapTargetPiece e c n) := by
  let P : Set X := manifoldChartMeasureGluingSourcePiece (H := H) c n ∩ e.source
  let Psub : Set e.source := {x : e.source | (x : X) ∈ P}
  have hP : MeasurableSet P :=
    (measurableSet_manifoldChartMeasureGluingSourcePiece (H := H) c n).inter
      e.open_source.measurableSet
  have hPsub : MeasurableSet Psub :=
    hP.preimage measurable_subtype_coe
  have htarget_sub :
      MeasurableSet (e.toHomeomorphSourceTarget '' Psub) :=
    e.toHomeomorphSourceTarget.measurableEmbedding.measurableSet_image' hPsub
  have htarget :
      MeasurableSet (((↑) : e.target → H) ''
        (e.toHomeomorphSourceTarget '' Psub)) :=
    e.open_target.measurableSet.subtype_image htarget_sub
  convert htarget using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨e x, e.map_source hx.2⟩, ⟨⟨x, hx.2⟩, hx, rfl⟩, rfl⟩
  · rintro ⟨z', ⟨x, hx, hz'⟩, hz⟩
    rcases x with ⟨x, hx_source⟩
    subst z
    subst z'
    exact ⟨x, hx, rfl⟩

theorem pairwise_disjoint_manifoldChartMeasureGluingOverlapTargetPiece {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e : OpenPartialHomeomorph X H) (c : ℕ → X) :
    Pairwise (fun i j ↦
      Disjoint (manifoldChartMeasureGluingOverlapTargetPiece e c i)
        (manifoldChartMeasureGluingOverlapTargetPiece e c j)) := by
  intro i j hij
  rw [Set.disjoint_iff_inter_eq_empty]
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  rcases hz with ⟨hzi, hzj⟩
  rcases hzi with ⟨x, hx, rfl⟩
  rcases hzj with ⟨y, hy, hyz⟩
  have hyx : y = x := by
    have := congrArg e.symm hyz
    simpa [e.left_inv hy.2, e.left_inv hx.2] using this
  have hdisj :
      Disjoint (manifoldChartMeasureGluingSourcePiece (H := H) c i)
        (manifoldChartMeasureGluingSourcePiece (H := H) c j) :=
    pairwise_disjoint_manifoldChartMeasureGluingSourcePiece (H := H) c hij
  exact Set.disjoint_left.mp hdisj hx.1 (by simpa [hyx] using hy.1)

theorem iUnion_manifoldChartMeasureGluingOverlapTargetPiece_eq_target {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e : OpenPartialHomeomorph X H) (c : ℕ → X)
    (hc_cover : (⋃ n, (chartAt H (c n)).source) = Set.univ) :
    (⋃ n, manifoldChartMeasureGluingOverlapTargetPiece e c n) = e.target := by
  rw [Set.eq_univ_iff_forall] at hc_cover
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨n, hzn⟩
    exact manifoldChartMeasureGluingOverlapTargetPiece_subset e c n hzn
  · intro hz
    let x : X := e.symm z
    have hx_source : x ∈ e.source := e.map_target hz
    have hx_piece :
        x ∈ ⋃ n, manifoldChartMeasureGluingSourcePiece (H := H) c n := by
      rw [iUnion_manifoldChartMeasureGluingSourcePiece_eq_univ c]
      · exact Set.mem_univ x
      · exact Set.eq_univ_iff_forall.mpr hc_cover
    rcases Set.mem_iUnion.mp hx_piece with ⟨n, hxn⟩
    exact Set.mem_iUnion.mpr
      ⟨n, ⟨x, ⟨hxn, hx_source⟩, e.right_inv hz⟩⟩

theorem manifoldChartMeasureGluingOverlapTargetPiece_subset_overlapRange {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e : OpenPartialHomeomorph X H) (c : ℕ → X) (n : ℕ) :
    manifoldChartMeasureGluingOverlapTargetPiece e c n ⊆
      manifoldChartOverlapRange e (chartAt H (c n)) := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  refine ⟨e.map_source hx.2, ?_⟩
  simpa [e.left_inv hx.2] using
    manifoldChartMeasureGluingSourcePiece_subset (H := H) c n hx.1

theorem manifoldChartTransition_preimage_overlapTargetPiece_inter_overlapDomain {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (e : OpenPartialHomeomorph X H) (c : ℕ → X) (n : ℕ) :
    (manifoldChartTransition e (chartAt H (c n))) ⁻¹'
        manifoldChartMeasureGluingOverlapTargetPiece e c n ∩
      manifoldChartOverlapDomain e (chartAt H (c n)) =
        manifoldChartMeasureGluingTargetPiece (H := H) c n ∩
          manifoldChartOverlapDomain e (chartAt H (c n)) := by
  let e' : OpenPartialHomeomorph X H := chartAt H (c n)
  let P : Set X := manifoldChartMeasureGluingSourcePiece (H := H) c n
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hz_pre, hz_overlap⟩
    rcases hz_overlap with ⟨hz_target, hz_source⟩
    rcases hz_pre with ⟨x, hx, hx_eq⟩
    have hx_eq' : e x = e (e'.symm z) := by
      simpa [manifoldChartTransition, e'] using hx_eq
    have hx_source : x ∈ e.source := hx.2
    have hx_base : x = e'.symm z := by
      exact e.injOn hx_source hz_source hx_eq'
    refine ⟨?_, ⟨hz_target, hz_source⟩⟩
    refine ⟨x, hx.1, ?_⟩
    calc
      e' x = e' (e'.symm z) := by rw [hx_base]
      _ = z := e'.right_inv hz_target
  · intro hz
    rcases hz with ⟨hz_targetPiece, hz_overlap⟩
    rcases hz_overlap with ⟨hz_target, hz_source⟩
    rcases hz_targetPiece with ⟨x, hxP, hz_eq⟩
    have hx_source' : x ∈ e'.source :=
      manifoldChartMeasureGluingSourcePiece_subset (H := H) c n hxP
    have hx_source : x ∈ e.source := by
      have hsymm : e'.symm z = x := by
        calc
          e'.symm z = e'.symm (e' x) := by rw [← hz_eq]
          _ = x := e'.left_inv hx_source'
      rw [← hsymm]
      exact hz_source
    refine ⟨?_, ⟨hz_target, hz_source⟩⟩
    refine ⟨x, ⟨hxP, hx_source⟩, ?_⟩
    have hsymm : e'.symm z = x := by
      calc
        e'.symm z = e'.symm (e' x) := by rw [← hz_eq]
        _ = x := e'.left_inv hx_source'
    calc
      e x = e (e'.symm z) := by rw [hsymm]
      _ = manifoldChartTransition e e' z := by
        rfl

/-- The `n`-th pulled-back local piece in the manifold chart gluing construction. -/
noncomputable def manifoldChartMeasureGluingLocalMeasure {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace H] [MeasurableSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (c : ℕ → X) (n : ℕ) : Measure X :=
  Measure.map ((chartAt H (c n)).symm)
    ((ν (chartAt H (c n)) (chart_mem_atlas H (c n))).restrict
      (manifoldChartMeasureGluingTargetPiece (H := H) c n))

/-- The global measure obtained by summing the pulled-back chart pieces. -/
noncomputable def manifoldChartMeasureGluingMeasure {H X : Type}
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace H] [MeasurableSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (c : ℕ → X) : Measure X :=
  Measure.sum (fun n : ℕ ↦ manifoldChartMeasureGluingLocalMeasure (H := H) ν c n)

theorem manifoldChartMeasureGluingOverlapTargetPiece_sum_restrict {H X : Type}
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace X] [ChartedSpace H X] [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
        (ν e he).restrict e.target = ν e he)
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt H (c n)).source) = Set.univ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    Measure.sum (fun n : ℕ ↦
      (ν e he).restrict (manifoldChartMeasureGluingOverlapTargetPiece e c n)) =
        ν e he := by
  have hpartition :
      (ν e he).restrict
          (⋃ n, manifoldChartMeasureGluingOverlapTargetPiece e c n) =
        Measure.sum (fun n : ℕ ↦
          (ν e he).restrict
            (manifoldChartMeasureGluingOverlapTargetPiece e c n)) :=
    Measure.restrict_iUnion
      (pairwise_disjoint_manifoldChartMeasureGluingOverlapTargetPiece e c)
      (fun n ↦ measurableSet_manifoldChartMeasureGluingOverlapTargetPiece e c n)
  calc
    Measure.sum (fun n : ℕ ↦
      (ν e he).restrict (manifoldChartMeasureGluingOverlapTargetPiece e c n))
        = (ν e he).restrict
            (⋃ n, manifoldChartMeasureGluingOverlapTargetPiece e c n) := hpartition.symm
    _ = (ν e he).restrict e.target := by
            rw [iUnion_manifoldChartMeasureGluingOverlapTargetPiece_eq_target e c hc_cover]
    _ = ν e he := hsupport e he

theorem manifoldChartTransition_aemeasurable_restrict_overlapDomain {H X : Type}
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace X] [ChartedSpace H X]
    (e e' : OpenPartialHomeomorph X H) (ν : Measure H) :
    AEMeasurable (manifoldChartTransition e e')
      (ν.restrict (manifoldChartOverlapDomain e e')) := by
  exact (manifoldChartTransition_continuousOn_overlap e e').aemeasurable
    (manifoldChartOverlapDomain_isOpen e e').measurableSet

theorem manifoldChartMeasureGluingLocalMeasure_chart_pushforward_piece
    (H X : Type) [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace X] [ChartedSpace H X] [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X H)
          (he : e ∈ atlas H X) (he' : e' ∈ atlas H X),
        Measure.map (manifoldChartTransition e e')
          ((ν e' he').restrict (manifoldChartOverlapDomain e e')) =
          (ν e he).restrict (manifoldChartOverlapRange e e'))
    (c : ℕ → X) (n : ℕ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    Measure.map e
        ((manifoldChartMeasureGluingLocalMeasure (H := H) ν c n).restrict e.source) =
      (ν e he).restrict (manifoldChartMeasureGluingOverlapTargetPiece e c n) := by
  let e' : OpenPartialHomeomorph X H := chartAt H (c n)
  let T : Set H := manifoldChartMeasureGluingTargetPiece (H := H) c n
  let O : Set H := manifoldChartOverlapDomain e e'
  let B : Set H := manifoldChartMeasureGluingOverlapTargetPiece e c n
  let R : Set H := manifoldChartOverlapRange e e'
  let νe' : Measure H := ν e' (chart_mem_atlas H (c n))
  let νe : Measure H := ν e he
  have he' : e' ∈ atlas H X := chart_mem_atlas H (c n)
  have hT : MeasurableSet T := measurableSet_manifoldChartMeasureGluingTargetPiece (H := H) c n
  have hO : MeasurableSet O := (manifoldChartOverlapDomain_isOpen e e').measurableSet
  have hB : MeasurableSet B := measurableSet_manifoldChartMeasureGluingOverlapTargetPiece e c n
  have hB_subset_R : B ⊆ R := by
    simpa [B, R, e'] using
      manifoldChartMeasureGluingOverlapTargetPiece_subset_overlapRange e c n
  have hT_subset_target : T ⊆ e'.target := by
    simpa [T, e'] using manifoldChartMeasureGluingTargetPiece_subset (H := H) c n
  have hsymm_T : AEMeasurable e'.symm (νe'.restrict T) := by
    exact (e'.continuousOn_symm.mono hT_subset_target).aemeasurable hT
  have hrestrict_source :
      (Measure.map e'.symm (νe'.restrict T)).restrict e.source =
        Measure.map e'.symm
          ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source)) := by
    rw [Measure.restrict_map_of_aemeasurable hsymm_T e.open_source.measurableSet]
  have hpre_source_ae :
      e'.symm ⁻¹' e.source =ᵐ[νe'.restrict T] O := by
    filter_upwards [ae_restrict_mem hT] with z hzT
    apply propext
    constructor
    · intro hz_source
      exact ⟨hT_subset_target hzT, hz_source⟩
    · intro hzO
      exact hzO.2
  have hsource_restrict :
      (νe'.restrict T).restrict (e'.symm ⁻¹' e.source) =
        νe'.restrict (T ∩ O) := by
    calc
      (νe'.restrict T).restrict (e'.symm ⁻¹' e.source)
          = (νe'.restrict T).restrict O := by
              exact Measure.restrict_congr_set hpre_source_ae
      _ = νe'.restrict (O ∩ T) := by
              rw [Measure.restrict_restrict hO]
      _ = νe'.restrict (T ∩ O) := by
              rw [Set.inter_comm]
  have hsymm_piece :
      AEMeasurable e'.symm
        ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source)) :=
    hsymm_T.mono_measure Measure.restrict_le_self
  have he_piece :
      AEMeasurable e
        (Measure.map e'.symm
          ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source))) := by
    rw [← hrestrict_source]
    exact e.continuousOn.aemeasurable e.open_source.measurableSet
  have hlhs :
      Measure.map e
          ((manifoldChartMeasureGluingLocalMeasure (H := H) ν c n).restrict e.source) =
        Measure.map (manifoldChartTransition e e')
          (νe'.restrict (T ∩ O)) := by
    calc
      Measure.map e
          ((manifoldChartMeasureGluingLocalMeasure (H := H) ν c n).restrict e.source)
          = Measure.map e
              ((Measure.map e'.symm (νe'.restrict T)).restrict e.source) := by
                rfl
      _ = Measure.map e
              (Measure.map e'.symm
                ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source))) := by
                rw [hrestrict_source]
      _ = Measure.map (manifoldChartTransition e e')
              ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source)) := by
                simpa [manifoldChartTransition, Function.comp_def] using
                  (AEMeasurable.map_map_of_aemeasurable he_piece hsymm_piece)
      _ = Measure.map (manifoldChartTransition e e')
              (νe'.restrict (T ∩ O)) := by
                rw [hsource_restrict]
  have htrans :
      AEMeasurable (manifoldChartTransition e e') (νe'.restrict O) := by
    exact manifoldChartTransition_aemeasurable_restrict_overlapDomain e e' νe'
  have hpre_piece_ae :
      (manifoldChartTransition e e') ⁻¹' B =ᵐ[νe'.restrict O] T := by
    filter_upwards [ae_restrict_mem hO] with z hzO
    have hset :=
      congrFun
        (show (manifoldChartTransition e e') ⁻¹' B ∩ O =
            T ∩ O from by
          simpa [B, T, O, e'] using
            manifoldChartTransition_preimage_overlapTargetPiece_inter_overlapDomain
              (H := H) e c n)
        z
    apply propext
    constructor
    · intro hzpre
      exact (hset.mp ⟨hzpre, hzO⟩).1
    · intro hzT
      exact (hset.mpr ⟨hzT, hzO⟩).1
  have hcompat_piece :
      Measure.map (manifoldChartTransition e e')
          (νe'.restrict (T ∩ O)) =
        νe.restrict B := by
    have hcomp :=
      congrArg (fun μ : Measure H ↦ μ.restrict B)
        (hcompat e e' he he')
    change (Measure.map (manifoldChartTransition e e') (νe'.restrict O)).restrict B =
      (νe.restrict R).restrict B at hcomp
    rw [Measure.restrict_map_of_aemeasurable htrans hB] at hcomp
    rw [Measure.restrict_congr_set hpre_piece_ae] at hcomp
    rw [Measure.restrict_restrict hT] at hcomp
    rw [Measure.restrict_restrict hB] at hcomp
    rw [show B ∩ R = B from Set.inter_eq_left.mpr hB_subset_R] at hcomp
    simpa [νe, νe', T, O, B, R] using hcomp
  calc
    Measure.map e
        ((manifoldChartMeasureGluingLocalMeasure (H := H) ν c n).restrict e.source)
        = Measure.map (manifoldChartTransition e e')
            (νe'.restrict (T ∩ O)) := hlhs
    _ = (ν e he).restrict (manifoldChartMeasureGluingOverlapTargetPiece e c n) := by
        simpa [νe, B] using hcompat_piece

theorem manifoldChartMeasureGluingMeasure_chart_pushforward
    (H X : Type) [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace X] [ChartedSpace H X] [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X H)
          (he : e ∈ atlas H X) (he' : e' ∈ atlas H X),
        Measure.map (manifoldChartTransition e e')
          ((ν e' he').restrict (manifoldChartOverlapDomain e e')) =
          (ν e he).restrict (manifoldChartOverlapRange e e'))
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt H (c n)).source) = Set.univ) :
    ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
      Measure.map e ((manifoldChartMeasureGluingMeasure (H := H) ν c).restrict e.source) =
        ν e he := by
  intro e he
  rw [manifoldChartMeasureGluingMeasure, Measure.restrict_sum_of_countable]
  have he_sum :
      AEMeasurable e
        (Measure.sum (fun n : ℕ ↦
          (manifoldChartMeasureGluingLocalMeasure (H := H) ν c n).restrict e.source)) := by
    rw [aemeasurable_sum_measure_iff]
    intro n
    exact e.continuousOn.aemeasurable e.open_source.measurableSet
  rw [Measure.map_sum he_sum]
  simp_rw [manifoldChartMeasureGluingLocalMeasure_chart_pushforward_piece
    H X ν hcompat c _ e he]
  exact manifoldChartMeasureGluingOverlapTargetPiece_sum_restrict
    ν hsupport c hc_cover e he

theorem manifoldChartMeasureGluingMeasure_compact_subset_chart_source_ne_top
    (H X : Type) [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [T2Space H]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X H)
          (he : e ∈ atlas H X) (he' : e' ∈ atlas H X),
        Measure.map (manifoldChartTransition e e')
          ((ν e' he').restrict (manifoldChartOverlapDomain e e')) =
          (ν e he).restrict (manifoldChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
        (K : Set H), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞))
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt H (c n)).source) = Set.univ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (K : Set X) (hK : IsCompact K) (hK_subset : K ⊆ e.source) :
    manifoldChartMeasureGluingMeasure (H := H) ν c K ≠ (∞ : ℝ≥0∞) := by
  let μ : Measure X := manifoldChartMeasureGluingMeasure (H := H) ν c
  let L : Set H := e '' K
  have hL_compact : IsCompact L :=
    hK.image_of_continuousOn (e.continuousOn.mono hK_subset)
  have hL_subset : L ⊆ e.target := by
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact e.map_source (hK_subset hxK)
  have hL_finite : ν e he L ≠ (∞ : ℝ≥0∞) :=
    hfinite e he L hL_compact hL_subset
  have hL_meas : MeasurableSet L := hL_compact.measurableSet
  have he_aem : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hpush :
      Measure.map e (μ.restrict e.source) = ν e he := by
    simpa [μ] using
      manifoldChartMeasureGluingMeasure_chart_pushforward
        H X ν hsupport hcompat c hc_cover e he
  have hle : μ K ≤ ν e he L := by
    calc
      μ K = μ.restrict e.source K := by
        exact (Measure.restrict_eq_self μ hK_subset).symm
      _ ≤ μ.restrict e.source (e ⁻¹' L) := by
        exact measure_mono fun x hxK ↦ ⟨x, hxK, rfl⟩
      _ = Measure.map e (μ.restrict e.source) L := by
        exact (Measure.map_apply_of_aemeasurable he_aem hL_meas).symm
      _ = ν e he L := by
        rw [hpush]
  exact ne_top_of_le_ne_top hL_finite hle

theorem manifoldChartMeasureGluingMeasure_finite_on_compact
    (H X : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X H)
          (he : e ∈ atlas H X) (he' : e' ∈ atlas H X),
        Measure.map (manifoldChartTransition e e')
          ((ν e' he').restrict (manifoldChartOverlapDomain e e')) =
          (ν e he).restrict (manifoldChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
        (K : Set H), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞))
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt H (c n)).source) = Set.univ) :
    ∀ K : Set X, IsCompact K →
      manifoldChartMeasureGluingMeasure (H := H) ν c K ≠ (∞ : ℝ≥0∞) := by
  let μ : Measure X := manifoldChartMeasureGluingMeasure (H := H) ν c
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace H X
  have hloc : IsLocallyFiniteMeasure μ := by
    refine ⟨fun x ↦ ?_⟩
    let e : OpenPartialHomeomorph X H := chartAt H x
    have he : e ∈ atlas H X := chart_mem_atlas H x
    have hx_source : x ∈ e.source := by
      simp [e]
    rcases LocallyCompactSpace.local_compact_nhds x e.source
        (e.open_source.mem_nhds hx_source) with
      ⟨C, hC_nhds, hC_subset, hC_compact⟩
    refine ⟨C, hC_nhds, ?_⟩
    have hC_finite :
        μ C ≠ (∞ : ℝ≥0∞) := by
      simpa [μ] using
        manifoldChartMeasureGluingMeasure_compact_subset_chart_source_ne_top
          H X ν hsupport hcompat hfinite c hc_cover e he C hC_compact hC_subset
    exact lt_top_iff_ne_top.mpr hC_finite
  haveI : IsLocallyFiniteMeasure μ := hloc
  intro K hK
  exact (hK.measure_lt_top (μ := μ)).ne

theorem exists_measure_with_compatible_manifold_nat_chart_pushforwards
    (H X : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X H)
          (he : e ∈ atlas H X) (he' : e' ∈ atlas H X),
        Measure.map (manifoldChartTransition e e')
          ((ν e' he').restrict (manifoldChartOverlapDomain e e')) =
          (ν e he).restrict (manifoldChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
        (K : Set H), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞))
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt H (c n)).source) = Set.univ) :
    ∃ μ : Measure X,
      (∀ K : Set X, IsCompact K → μ K ≠ (∞ : ℝ≥0∞)) ∧
        ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
          Measure.map e (μ.restrict e.source) = ν e he := by
  refine ⟨manifoldChartMeasureGluingMeasure (H := H) ν c, ?_, ?_⟩
  · exact manifoldChartMeasureGluingMeasure_finite_on_compact
      H X ν hsupport hcompat hfinite c hc_cover
  · exact manifoldChartMeasureGluingMeasure_chart_pushforward
      H X ν hsupport hcompat c hc_cover

/--
%%handwave
name:
  A compatible family of manifold chart measures glues
statement:
  A compatible family of locally finite Borel measures in coordinate charts,
  supported on their chart images, glues to a global Borel measure whose
  restriction to every chart has the prescribed coordinate pushforward.
proof:
  Choose a countable chart-source cover, split it into disjoint Borel pieces,
  pull the coordinate measures back to those pieces, and sum them.  The
  compatibility hypothesis rewrites every piece inside any target chart as a
  restriction of that target chart measure, while compact finiteness follows
  from finite subcovers.
-/
theorem exists_measure_with_compatible_manifold_chart_pushforwards {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X]
    [FiniteDimensional ℝ H]
    (ν : ∀ e : OpenPartialHomeomorph X H, e ∈ atlas H X → Measure H)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X H)
          (he : e ∈ atlas H X) (he' : e' ∈ atlas H X),
        Measure.map (manifoldChartTransition e e')
          ((ν e' he').restrict (manifoldChartOverlapDomain e e')) =
          (ν e he).restrict (manifoldChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
        (K : Set H), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞)) :
      ∃ μ : Measure X,
      (∀ K : Set X, IsCompact K → μ K ≠ (∞ : ℝ≥0∞)) ∧
        ∀ (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X),
          Measure.map e (μ.restrict e.source) = ν e he := by
  by_cases hnonempty : Nonempty X
  · letI : Nonempty X := hnonempty
    rcases exists_countable_manifoldChartAt_source_cover H X with
      ⟨S, hS_countable, hS_cover⟩
    let c : ℕ → X := Set.enumerateCountable hS_countable Classical.ofNonempty
    have hc_cover : (⋃ n, (chartAt H (c n)).source) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      have hy : y ∈ ⋃ x ∈ S, (chartAt H x).source := by
        simp [hS_cover]
      rcases Set.mem_iUnion.mp hy with ⟨x, hyx⟩
      rcases Set.mem_iUnion.mp hyx with ⟨hxS, hyU⟩
      obtain ⟨n, hn⟩ := Set.subset_range_enumerate hS_countable
        Classical.ofNonempty hxS
      exact Set.mem_iUnion.mpr ⟨n, by simpa [c, hn] using hyU⟩
    exact exists_measure_with_compatible_manifold_nat_chart_pushforwards
      H X ν hsupport hcompat hfinite c hc_cover
  · refine ⟨0, ?_, ?_⟩
    · intro K _hK
      simp
    · intro e he
      have hsource_empty : e.source = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x _hx
        exact hnonempty ⟨x⟩
      have htarget_empty : e.target = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hnonempty ⟨e.symm z⟩
      have hν_zero : ν e he = 0 := by
        have h := hsupport e he
        rw [htarget_empty, Measure.restrict_empty] at h
        exact h.symm
      simp [hsource_empty, hν_zero]

/--
%%handwave
name:
  Riemannian volume measure for a manifold metric
statement:
  A measure is the Riemannian volume measure of a smooth metric when it is a
  smooth positive measure and, in every coordinate chart, its pushforward is
  Lebesgue measure with density given by the square root of the metric
  determinant.
-/
def IsRiemannianVolumeMeasureOnManifold {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) (μ : Measure X) : Prop :=
  SmoothPositiveMeasureOnManifold (I := 𝓘(ℝ, H)) μ ∧
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X),
      Measure.map e (μ.restrict e.source) =
        manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e

/--
%%handwave
name:
  Gluing manifold Riemannian coordinate volumes
statement:
  Compatible smooth positive coordinate volume measures associated to a
  Riemannian metric glue to a global Riemannian volume measure.
proof:
  Apply the chart-measure gluing theorem to the local measures
  \(\sqrt{\det(g_{ij})}\,dx\).  The local density is smooth and positive,
  compact subsets have finite local measure, and compatibility on overlaps is
  the Riemannian change-of-variables formula.
-/
theorem exists_measure_with_riemannian_manifold_chart_pushforwards {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (_hcompat : RiemannianVolumeChartMeasuresCompatibleOnManifold g) :
    ∃ μ : Measure X, IsRiemannianVolumeMeasureOnManifold g μ := by
  rcases exists_measure_with_compatible_manifold_chart_pushforwards
      (fun e _he ↦ manifoldRiemannianVolumeChartMeasure (I := 𝓘(ℝ, H)) g e)
      (by
        intro e _he
        exact manifoldRiemannianVolumeChartMeasure_restrict_target
          (I := 𝓘(ℝ, H)) g e)
      (by
        intro e e' he he'
        exact _hcompat e e' he he')
      (by
        intro e he K hK hK_subset
        exact manifoldRiemannianVolumeChartMeasure_finite_on_compact
          g e he K hK hK_subset)
    with ⟨μ, hμ_finite, hμ_charts⟩
  refine ⟨μ, ⟨?_, hμ_charts⟩⟩
  exact
    { finite_on_compact := hμ_finite
      chart_density := by
        intro e he
        refine ⟨manifoldMetricVolumeDensityInChart (I := 𝓘(ℝ, H)) g e, ?_, ?_, ?_⟩
        · exact (manifoldMetricVolumeDensityInChart_smooth_positive
            g e he).1
        · exact (manifoldMetricVolumeDensityInChart_smooth_positive
            g e he).2
        · simpa [manifoldRiemannianVolumeChartMeasure] using hμ_charts e he }

/--
%%handwave
name:
  Existence of the Riemannian volume measure on a manifold
statement:
  On a finite-dimensional smooth Riemannian manifold whose model-space volume
  is Lebesgue measure, the metric determines a Riemannian volume measure with
  local density \(\sqrt{\det(g_{ij})}\).
proof:
  The local weighted Lebesgue measures associated to the metric determinant
  are compatible on coordinate overlaps by the transformation law for Gram
  determinants and the smooth change-of-variables theorem.  They therefore
  glue to a global Borel measure.
-/
theorem exists_riemannianVolumeMeasureOnManifold {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) :
    ∃ μ : Measure X, IsRiemannianVolumeMeasureOnManifold g μ := by
  exact exists_measure_with_riemannian_manifold_chart_pushforwards g
    (riemannianVolumeChartMeasuresCompatibleOnManifold_of_smoothMetric g)

/--
%%handwave
name:
  Riemannian volume measure has smooth positive coordinate densities
statement:
  On a finite-dimensional smooth Riemannian manifold, the Riemannian volume
  measure has smooth strictly positive local coordinate densities with
  respect to Lebesgue measure on the model space, and compact sets have finite
  volume.
proof:
  In a coordinate chart, the Riemannian density is the square root of the
  determinant of the metric Gram matrix.  The metric coefficients are smooth,
  positive definiteness makes the determinant strictly positive, and the
  coordinate change formula for Gram determinants gives compatible local
  measures which glue to the global Riemannian volume measure.
-/
theorem exists_smoothPositiveRiemannianVolumeMeasureOnManifold {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) :
    ∃ μ : Measure X, SmoothPositiveMeasureOnManifold (I := 𝓘(ℝ, H)) μ := by
  rcases exists_riemannianVolumeMeasureOnManifold g with ⟨μ, hμ⟩
  exact ⟨μ, hμ.1⟩

namespace SmoothRiemannianMetricOnManifold

/--
%%handwave
name:
  Riemannian volume measure of a smooth metric
statement:
  A smooth Riemannian metric on a finite-dimensional smooth manifold
  determines its Riemannian volume measure.
-/
noncomputable def volume {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) : Measure X :=
  Classical.choose
    (exists_riemannianVolumeMeasureOnManifold g)

/--
%%handwave
name:
  The chosen Riemannian volume measure has the metric chart densities
statement:
  The volume measure chosen from the Riemannian metric is a Riemannian volume
  measure: in every coordinate chart its pushforward is the weighted
  Lebesgue measure with density \(\sqrt{\det(g_{ij})}\).
-/
theorem volume_isRiemannian {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) :
    IsRiemannianVolumeMeasureOnManifold g (volume g) :=
  Classical.choose_spec
    (exists_riemannianVolumeMeasureOnManifold g)

/--
%%handwave
name:
  Riemannian volume is a smooth positive measure
statement:
  The Riemannian volume measure of a finite-dimensional smooth Riemannian
  manifold has smooth strictly positive coordinate densities and is finite on
  compact sets.
-/
theorem volume_smooth_positive {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) :
    SmoothPositiveMeasureOnManifold (I := 𝓘(ℝ, H)) (volume g) :=
  (volume_isRiemannian g).1

/--
%%handwave
name:
  Coordinate density of the Riemannian volume
statement:
  In every smooth coordinate chart, the Riemannian volume measure is
  Lebesgue measure multiplied by a smooth strictly positive density.
-/
theorem volume_chart_density {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] [BorelSpace H]
    [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    ∃ ρ : H → ℝ,
      ContDiffOn ℝ ∞ ρ e.target ∧
        (∀ z ∈ e.target, 0 < ρ z) ∧
        Measure.map e ((volume g).restrict e.source) =
          (MeasureTheory.volume.restrict e.target).withDensity
            (fun z : H ↦ ENNReal.ofReal (ρ z)) :=
  (volume_smooth_positive g).chart_density e he

end SmoothRiemannianMetricOnManifold

end

end Uniformization

end JJMath
