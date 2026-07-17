import JJMath.Uniformization.AnnularProperLineTube
import JJMath.Uniformization.ExteriorComponentProperLine
import JJMath.Uniformization.GreenFunctionResidue

/-!
# The radial proper-line tube in Green pole coordinates

The canonical radial tube in the annular cylinder transports through the
Green pole coordinate.  Its transition strip is closed relative to the
punctured coordinate disk.  Extending its positive radial end through an
exterior component is the remaining global geometric step.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [RiemannSurface X]
  {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
  {P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G}

/-- Away from the pole, the closed half-radius coordinate disk lies in the
doubled punctured pole disk. -/
theorem CompactSuperlevelGreenFunctionPoleCoordinateLogData.closedDisk_mem_puncturedPoleDisk
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    {x : X} (hxp : x ≠ p) (hx : x ∈ D.closedDisk.carrier) :
    x ∈ D.puncturedPoleDisk := by
  rw [D.puncturedPoleDisk_mem_iff]
  rw [D.closedDisk.carrier_eq] at hx
  refine ⟨hxp, ?_, ?_⟩
  · simpa [D.closedDisk_openDisk_chart] using hx.1
  · rw [Metric.mem_ball]
    have hdist :
        dist (D.coordinate.chart x) (D.coordinate.chart p) ≤
          D.radius / 2 := by
      simpa [Metric.mem_closedBall, D.closedDisk_openDisk_chart,
        D.closedDisk_openDisk_center, D.closedDisk_closedRadius] using hx.2
    linarith [D.radius_pos]

/-- The closed half-radius disk with its pole removed, as a closed subset of
the full punctured surface. -/
def puncturedClosedPoleDisk
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    Set (puncturedSurfaceOpen p) :=
  {x | (x : X) ∈ D.closedDisk.carrier}

theorem puncturedClosedPoleDisk_isClosed
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    IsClosed (puncturedClosedPoleDisk D) := by
  exact D.closedDisk.compact.isClosed.preimage continuous_subtype_val

/-- Include the punctured closed half-radius disk into the doubled punctured
pole disk. -/
noncomputable def puncturedClosedPoleDiskToPuncturedPoleDisk
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    puncturedClosedPoleDisk D → D.puncturedPoleDisk := fun x =>
  ⟨(x : puncturedSurfaceOpen p),
    D.closedDisk_mem_puncturedPoleDisk
      (x : puncturedSurfaceOpen p).2 x.2⟩

theorem continuous_puncturedClosedPoleDiskToPuncturedPoleDisk
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    Continuous (puncturedClosedPoleDiskToPuncturedPoleDisk D) := by
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Radial position is nonpositive on the closed inner coordinate disk. -/
theorem puncturedClosedPoleDisk_radial_second_nonpos
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (x : puncturedClosedPoleDisk D) :
    (D.radialDiffeomorph
      (puncturedClosedPoleDiskToPuncturedPoleDisk D x)).2 ≤ 0 := by
  apply le_of_not_gt
  intro hpos
  have hout : ((x : puncturedSurfaceOpen p) : X) ∉
      closure D.closedDisk.toSmoothBoundaryDomain.carrier :=
    (D.closedDisk.radialPuncturedCollarDiffeomorph_second_pos_iff
      p D.pole_mem_closedDisk_chart_source
      D.closedDisk_chart_p_eq_center
      D.closedDisk_double_closedRadius.le
      (puncturedClosedPoleDiskToPuncturedPoleDisk D x)).mp hpos
  apply hout
  change ((x : puncturedSurfaceOpen p) : X) ∈
    closure (D.closedDisk.expandedOpenDisk D.closedDisk.closedRadius)
  rw [D.closedDisk.closure_expandedOpenDisk_closedRadius]
  exact x.2

/-- Radial position is nonpositive exactly on the closed inner coordinate
disk. -/
theorem radialDiffeomorph_second_nonpos_iff_mem_closedDisk
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (y : D.puncturedPoleDisk) :
    (D.radialDiffeomorph y).2 ≤ 0 ↔ (y : X) ∈ D.closedDisk.carrier := by
  constructor
  · intro hs
    by_contra hy
    have hout : (y : X) ∉
        closure D.closedDisk.toSmoothBoundaryDomain.carrier := by
      intro hycl
      apply hy
      change (y : X) ∈ D.closedDisk.carrier
      change (y : X) ∈
        closure (D.closedDisk.expandedOpenDisk D.closedDisk.closedRadius) at hycl
      rwa [D.closedDisk.closure_expandedOpenDisk_closedRadius] at hycl
    have hpos : 0 < (D.radialDiffeomorph y).2 :=
      (D.closedDisk.radialPuncturedCollarDiffeomorph_second_pos_iff
        p D.pole_mem_closedDisk_chart_source
        D.closedDisk_chart_p_eq_center
        D.closedDisk_double_closedRadius.le y).mpr hout
    exact (not_lt_of_ge hs) hpos
  · intro hy
    apply le_of_not_gt
    intro hpos
    have hout : (y : X) ∉
        closure D.closedDisk.toSmoothBoundaryDomain.carrier :=
      (D.closedDisk.radialPuncturedCollarDiffeomorph_second_pos_iff
        p D.pole_mem_closedDisk_chart_source
        D.closedDisk_chart_p_eq_center
        D.closedDisk_double_closedRadius.le y).mp hpos
    apply hout
    change (y : X) ∈
      closure (D.closedDisk.expandedOpenDisk D.closedDisk.closedRadius)
    rw [D.closedDisk.closure_expandedOpenDisk_closedRadius]
    exact hy

/-- The radial slit in the pole disk, regarded directly as an open subset of
the full punctured surface. -/
def puncturedSurfacePoleRadialLineTubeOpen
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    TopologicalSpace.Opens (puncturedSurfaceOpen p) :=
  openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v)

/-- The pole-coordinate radial tube with precisely the ambient type used by
the global punctured-surface constructions. -/
noncomputable def puncturedSurfacePoleRadialLineTubeDiffeomorph
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    puncturedSurfacePoleRadialLineTubeOpen D v ≃ₘ⟮
      SurfaceRealModel, ProperLineTubeModel⟯ ℝ × ℝ :=
  (D.annularLeftCutToPuncturedCutDiffeomorph v).symm.trans
    (annularRadialLineTubeDiffeomorph v)

@[simp]
theorem puncturedSurfacePoleRadialLineTubeDiffeomorph_apply
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle)
    (x : puncturedSurfacePoleRadialLineTubeOpen D v) :
    puncturedSurfacePoleRadialLineTubeDiffeomorph D v x =
      annularRadialLineTubeDiffeomorph v
        ((D.annularLeftCutToPuncturedCutDiffeomorph v).symm x) := by
  rfl

/-- The pole-coordinate disk slit along the direction `v`, ordered as a
radial proper-line tube. -/
noncomputable def puncturedPoleRadialLineTubeDiffeomorph
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    D.radialLeftCut v ≃ₘ⟮SurfaceRealModel, ProperLineTubeModel⟯ ℝ × ℝ :=
  (D.radialPreimageDiffeomorph (annularPunctureOpen v)).trans
    (annularRadialLineTubeDiffeomorph v)

/-- The pole-coordinate transition strip is the radial preimage of the
closed annular transition strip. -/
theorem puncturedPoleRadialLineTubeCore_eq_preimage
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    properLineTubeCore SurfaceRealModel (D.radialLeftCut v)
        (puncturedPoleRadialLineTubeDiffeomorph D v) =
      D.radialDiffeomorph ⁻¹'
        properLineTubeCore AnnularCylinderModel (annularPunctureOpen v)
          (annularRadialLineTubeDiffeomorph v) := by
  have hr (y : annularPunctureOpen v) :
      D.radialDiffeomorph
          ((((D.radialPreimageDiffeomorph
            (annularPunctureOpen v)).symm y : D.radialLeftCut v) :
              D.puncturedPoleDisk)) = (y : Circle × ℝ) := by
    change D.radialDiffeomorph
      (D.radialDiffeomorph.symm (y : Circle × ℝ)) = _
    simp
  ext x
  constructor
  · rintro ⟨q, hq, hqx⟩
    show D.radialDiffeomorph x ∈
      properLineTubeCore AnnularCylinderModel (annularPunctureOpen v)
        (annularRadialLineTubeDiffeomorph v)
    refine ⟨q, hq, ?_⟩
    have h := congrArg D.radialDiffeomorph hqx
    change D.radialDiffeomorph
      ((((D.radialPreimageDiffeomorph (annularPunctureOpen v)).symm
        ((annularRadialLineTubeDiffeomorph v).symm q) :
          D.radialLeftCut v) : D.puncturedPoleDisk)) =
        D.radialDiffeomorph x at h
    rw [hr] at h
    exact h
  · intro hx
    change D.radialDiffeomorph x ∈
      properLineTubeCore AnnularCylinderModel (annularPunctureOpen v)
        (annularRadialLineTubeDiffeomorph v) at hx
    rcases hx with ⟨q, hq, hqeq⟩
    refine ⟨q, hq, ?_⟩
    apply D.radialDiffeomorph.injective
    change D.radialDiffeomorph
      ((((D.radialPreimageDiffeomorph (annularPunctureOpen v)).symm
        ((annularRadialLineTubeDiffeomorph v).symm q) :
          D.radialLeftCut v) : D.puncturedPoleDisk)) =
        D.radialDiffeomorph x
    rw [hr]
    exact hqeq

/-- In radial coordinates, the inverse tube coordinate keeps its first
coordinate as radial position and applies inverse stereographic projection
to its transverse coordinate. -/
theorem puncturedPoleRadialLineTubeDiffeomorph_symm_radial
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) (s t : ℝ) :
    D.radialDiffeomorph
        ((((puncturedPoleRadialLineTubeDiffeomorph D v).symm (s, t) :
          D.radialLeftCut v) : D.puncturedPoleDisk)) =
      ((stereographic' 1 v).symm
        ((EuclideanSpace.equiv (Fin 1) ℝ).symm
          ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm t)), s) := by
  change D.radialDiffeomorph
      (D.radialDiffeomorph.symm
        (((annularRadialLineTubeDiffeomorph v).symm (s, t) :
          annularPunctureOpen v) : Circle × ℝ)) = _
  rw [D.radialDiffeomorph.apply_symm_apply]
  exact annularRadialLineTubeDiffeomorph_symm_apply v s t

/-- The negative transition tail, first regarded as a map into the punctured
pole-coordinate disk. -/
noncomputable def puncturedPoleRadialNegativeTailMap
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    properLineTransitionNegativeTail 0 → D.puncturedPoleDisk := fun q =>
  (((puncturedPoleRadialLineTubeDiffeomorph D v).symm
      ((q : properLineTransitionCore) : ℝ × ℝ) : D.radialLeftCut v) :
    D.puncturedPoleDisk)

/-- The negative radial transition tail in the full punctured surface. -/
noncomputable def puncturedSurfacePoleRadialNegativeTailMap
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    properLineTransitionNegativeTail 0 → puncturedSurfaceOpen p := fun q =>
  ⟨((puncturedPoleRadialNegativeTailMap D v q : D.puncturedPoleDisk) : X),
    D.puncturedPoleDisk_le_puncturedSurfaceOpen
      (puncturedPoleRadialNegativeTailMap D v q).2⟩

theorem puncturedSurfacePoleRadialNegativeTailMap_mem_closedDisk
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle)
    (q : properLineTransitionNegativeTail 0) :
    ((puncturedSurfacePoleRadialNegativeTailMap D v q :
      puncturedSurfaceOpen p) : X) ∈ D.closedDisk.carrier := by
  let y : D.radialLeftCut v :=
    (puncturedPoleRadialLineTubeDiffeomorph D v).symm
      ((q : properLineTransitionCore) : ℝ × ℝ)
  have hs : (((q : properLineTransitionCore) : ℝ × ℝ)).1 ≤ 0 := by
    have hs' : (((q : properLineTransitionCore) : ℝ × ℝ)).1 ≤ -0 := q.2
    simpa only [neg_zero] using hs'
  change ((y : D.puncturedPoleDisk) : X) ∈ D.closedDisk.carrier
  rw [← radialDiffeomorph_second_nonpos_iff_mem_closedDisk D
    (y : D.puncturedPoleDisk)]
  change (D.radialDiffeomorph
    ((((puncturedPoleRadialLineTubeDiffeomorph D v).symm
      (((q : properLineTransitionCore) : ℝ × ℝ)) : D.radialLeftCut v) :
        D.puncturedPoleDisk))).2 ≤ 0
  rw [puncturedPoleRadialLineTubeDiffeomorph_symm_radial]
  exact hs

/-- Factor the negative radial transition tail through the punctured closed
inner coordinate disk. -/
noncomputable def puncturedClosedPoleDiskRadialNegativeTailMap
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    properLineTransitionNegativeTail 0 → puncturedClosedPoleDisk D := fun q =>
  ⟨puncturedSurfacePoleRadialNegativeTailMap D v q,
    puncturedSurfacePoleRadialNegativeTailMap_mem_closedDisk D v q⟩

/-- The angular core strip inside the punctured closed pole disk. -/
def puncturedClosedPoleDiskRadialCore
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    Set (puncturedClosedPoleDisk D) :=
  {x | (D.radialDiffeomorph
      (puncturedClosedPoleDiskToPuncturedPoleDisk D x)).1 ∈
    annularRadialCoreAngleSet v}

theorem puncturedClosedPoleDiskRadialCore_isClosed
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    IsClosed (puncturedClosedPoleDiskRadialCore D v) := by
  exact (annularRadialCoreAngleSet_isClosed v).preimage
    (continuous_fst.comp
      (D.radialDiffeomorph.continuous.comp
        (continuous_puncturedClosedPoleDiskToPuncturedPoleDisk D)))

theorem puncturedClosedPoleDiskRadialNegativeTailMap_range
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    Set.range (puncturedClosedPoleDiskRadialNegativeTailMap D v) =
      puncturedClosedPoleDiskRadialCore D v := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    let t : Set.Icc (-1 : ℝ) 1 :=
      ⟨(((q : properLineTransitionCore) : ℝ × ℝ)).2, q.1.2⟩
    change (D.radialDiffeomorph
      (puncturedClosedPoleDiskToPuncturedPoleDisk D
        (puncturedClosedPoleDiskRadialNegativeTailMap D v q))).1 ∈
          annularRadialCoreAngleSet v
    refine ⟨t, ?_⟩
    change (annularRadialCoreAngleMap v t) = _
    rw [show puncturedClosedPoleDiskToPuncturedPoleDisk D
        (puncturedClosedPoleDiskRadialNegativeTailMap D v q) =
      (((puncturedPoleRadialLineTubeDiffeomorph D v).symm
        (((q : properLineTransitionCore) : ℝ × ℝ)) : D.radialLeftCut v) :
          D.puncturedPoleDisk) from rfl]
    rw [puncturedPoleRadialLineTubeDiffeomorph_symm_radial]
    rfl
  · intro hx
    rcases hx with ⟨t, ht⟩
    have hs : (D.radialDiffeomorph
        (puncturedClosedPoleDiskToPuncturedPoleDisk D x)).2 ≤ 0 :=
      puncturedClosedPoleDisk_radial_second_nonpos D x
    let q0 : properLineTransitionCore :=
      ⟨((D.radialDiffeomorph
          (puncturedClosedPoleDiskToPuncturedPoleDisk D x)).2,
        (t : ℝ)), t.2⟩
    let q : properLineTransitionNegativeTail 0 :=
      ⟨q0, by
        change (q0 : ℝ × ℝ).1 ≤ -0
        simpa only [q0, neg_zero] using hs⟩
    refine ⟨q, ?_⟩
    have heq :
        (((puncturedPoleRadialLineTubeDiffeomorph D v).symm
          (((q : properLineTransitionCore) : ℝ × ℝ)) : D.radialLeftCut v) :
            D.puncturedPoleDisk) =
          puncturedClosedPoleDiskToPuncturedPoleDisk D x := by
      apply D.radialDiffeomorph.injective
      have hradial :=
        puncturedPoleRadialLineTubeDiffeomorph_symm_radial D v
          (((q : properLineTransitionCore) : ℝ × ℝ)).1
          (((q : properLineTransitionCore) : ℝ × ℝ)).2
      rw [show (((q : properLineTransitionCore) : ℝ × ℝ)) =
          ((((q : properLineTransitionCore) : ℝ × ℝ)).1,
            (((q : properLineTransitionCore) : ℝ × ℝ)).2) from
              (Prod.eta _).symm]
      change D.radialDiffeomorph
          ((((puncturedPoleRadialLineTubeDiffeomorph D v).symm
            ((((q : properLineTransitionCore) : ℝ × ℝ)).1,
              (((q : properLineTransitionCore) : ℝ × ℝ)).2) :
                D.radialLeftCut v) : D.puncturedPoleDisk)) =
        D.radialDiffeomorph
          (puncturedClosedPoleDiskToPuncturedPoleDisk D x)
      rw [hradial]
      change (annularRadialCoreAngleMap v t,
        (D.radialDiffeomorph
          (puncturedClosedPoleDiskToPuncturedPoleDisk D x)).2) =
        D.radialDiffeomorph
          (puncturedClosedPoleDiskToPuncturedPoleDisk D x)
      ext
      · exact congrArg Subtype.val ht
      · rfl
    have hX :
        (((puncturedClosedPoleDiskRadialNegativeTailMap D v q :
          puncturedClosedPoleDisk D) : puncturedSurfaceOpen p) : X) =
          (((x : puncturedClosedPoleDisk D) : puncturedSurfaceOpen p) : X) :=
      congrArg (fun z : D.puncturedPoleDisk => (z : X)) heq
    have hsurface :
        ((puncturedClosedPoleDiskRadialNegativeTailMap D v q :
          puncturedClosedPoleDisk D) : puncturedSurfaceOpen p) =
          ((x : puncturedClosedPoleDisk D) : puncturedSurfaceOpen p) :=
      Subtype.ext hX
    exact Subtype.ext hsurface

theorem puncturedClosedPoleDiskRadialNegativeTailMap_isEmbedding
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    Topology.IsEmbedding
      (puncturedClosedPoleDiskRadialNegativeTailMap D v) := by
  have hcoord : Topology.IsEmbedding
      (fun q : properLineTransitionNegativeTail 0 =>
        ((q : properLineTransitionCore) : ℝ × ℝ)) := by
    exact Topology.IsEmbedding.subtypeVal.comp
      Topology.IsEmbedding.subtypeVal
  have hpole : Topology.IsEmbedding
      (puncturedPoleRadialNegativeTailMap D v) := by
    have hlocal :=
      (puncturedPoleRadialLineTubeDiffeomorph D v).symm.toHomeomorph.isEmbedding.comp
        hcoord
    have hinc := Topology.IsEmbedding.subtypeVal.comp hlocal
    simpa only [puncturedPoleRadialNegativeTailMap, Function.comp_apply] using hinc
  have hsurface : Topology.IsEmbedding
      (puncturedSurfacePoleRadialNegativeTailMap D v) := by
    have hinc : Topology.IsEmbedding
        (Set.inclusion D.puncturedPoleDisk_le_puncturedSurfaceOpen) :=
      Topology.IsEmbedding.inclusion _
    have hcomp := hinc.comp hpole
    simpa only [puncturedSurfacePoleRadialNegativeTailMap,
      puncturedPoleRadialNegativeTailMap, Set.inclusion,
      Function.comp_apply] using hcomp
  have hcod := hsurface.codRestrict (puncturedClosedPoleDisk D)
    (puncturedSurfacePoleRadialNegativeTailMap_mem_closedDisk D v)
  simpa only [puncturedClosedPoleDiskRadialNegativeTailMap,
    Set.codRestrict] using hcod

/-- The negative radial transition tail is a closed embedding in the
punctured closed pole disk. -/
theorem puncturedClosedPoleDiskRadialNegativeTailMap_isClosedEmbedding
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    Topology.IsClosedEmbedding
      (puncturedClosedPoleDiskRadialNegativeTailMap D v) := by
  refine ⟨puncturedClosedPoleDiskRadialNegativeTailMap_isEmbedding D v, ?_⟩
  rw [puncturedClosedPoleDiskRadialNegativeTailMap_range]
  exact puncturedClosedPoleDiskRadialCore_isClosed D v

/-- The pole-coordinate negative transition tail is proper in the punctured
surface. -/
theorem puncturedSurfacePoleRadialNegativeTailMap_isProper
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    IsProperMap (puncturedSurfacePoleRadialNegativeTailMap D v) := by
  have hc : Topology.IsClosedEmbedding
      (puncturedClosedPoleDiskRadialNegativeTailMap D v) :=
    puncturedClosedPoleDiskRadialNegativeTailMap_isClosedEmbedding D v
  have hi : Topology.IsClosedEmbedding
      ((↑) : puncturedClosedPoleDisk D → puncturedSurfaceOpen p) :=
    (puncturedClosedPoleDisk_isClosed D).isClosedEmbedding_subtypeVal
  exact (hi.comp hc).isProperMap

/-- The exact negative tail of the ambient pole tube is proper. -/
theorem puncturedSurfacePoleRadialLineTube_negativeTail_isProper
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    IsProperMap
      (fun q : properLineTransitionNegativeTail 0 =>
        (((puncturedSurfacePoleRadialLineTubeDiffeomorph D v).symm
          ((q : properLineTransitionCore) : ℝ × ℝ) :
            puncturedSurfacePoleRadialLineTubeOpen D v) :
          puncturedSurfaceOpen p)) := by
  convert puncturedSurfacePoleRadialNegativeTailMap_isProper D v using 1

/-- The radial transition strip is closed in the punctured pole-coordinate
disk. -/
theorem puncturedPoleRadialLineTubeCore_isClosed
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    IsClosed
      (properLineTubeCore SurfaceRealModel (D.radialLeftCut v)
        (puncturedPoleRadialLineTubeDiffeomorph D v)) := by
  rw [puncturedPoleRadialLineTubeCore_eq_preimage]
  exact (annularRadialLineTubeCore_isClosed v).preimage
    D.radialDiffeomorph.continuous

/-- The central radial line in pole coordinates, regarded as a map into the
full punctured surface. -/
noncomputable def puncturedSurfacePoleRadialLine
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) (t : ℝ) :
    puncturedSurfaceOpen p :=
  ⟨((D.radialDiffeomorph.symm (v, t) : D.puncturedPoleDisk) : X),
    D.puncturedPoleDisk_le_puncturedSurfaceOpen
      (D.radialDiffeomorph.symm (v, t)).2⟩

/-- The central radial pole line is smooth. -/
theorem contMDiff_puncturedSurfacePoleRadialLine
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞
      (puncturedSurfacePoleRadialLine D v) := by
  let radial : ℝ → D.puncturedPoleDisk := fun t =>
    D.radialDiffeomorph.symm (v, t)
  have hpair : ContMDiff (modelWithCornersSelf ℝ ℝ)
      JJMath.Manifold.AnnularCylinderModel ∞ (fun t : ℝ => (v, t)) :=
    contMDiff_const.prodMk contMDiff_id
  have hradial : ContMDiff (modelWithCornersSelf ℝ ℝ)
      SurfaceRealModel ∞ radial :=
    D.radialDiffeomorph.symm.contMDiff.comp hpair
  have hambient : ContMDiff (modelWithCornersSelf ℝ ℝ)
      SurfaceRealModel ∞ (fun t => (radial t : X)) :=
    (contMDiff_subtype_val (I := SurfaceRealModel)).comp hradial
  exact ContMDiff.codRestrict_open hambient (puncturedSurfaceOpen p)
    (fun t => D.puncturedPoleDisk_le_puncturedSurfaceOpen (radial t).2)

/-- Distinct radial parameters give distinct points of the punctured
surface. -/
theorem injective_puncturedSurfacePoleRadialLine
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    Function.Injective (puncturedSurfacePoleRadialLine D v) := by
  intro s t hst
  have hpole : D.radialDiffeomorph.symm (v, s) =
      D.radialDiffeomorph.symm (v, t) := by
    apply Subtype.ext
    exact congrArg (fun z : puncturedSurfaceOpen p => (z : X)) hst
  have hpair : (v, s) = (v, t) :=
    D.radialDiffeomorph.symm.injective hpole
  exact congrArg Prod.snd hpair

/-- The radial pole collar and the exterior-component escape ray combine to
give a proper continuous line in the punctured surface which agrees exactly
with the central radial line on the pole-side half.  This theorem isolates the
remaining geometric upgrade: smoothing and removing self-intersections on a
bounded region and on the exterior ray, relative to the already smooth radial
half. -/
theorem exists_proper_continuous_line_puncturedSurface_with_negativeRadial
    [NoncompactSpace X]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    ∃ line : C(ℝ, puncturedSurfaceOpen p),
      IsProperMap line ∧
        ∀ t : ℝ, t ≤ 0 → line t = puncturedSurfacePoleRadialLine D v t := by
  let D0 := D.closedDisk.toSmoothBoundaryDomain
  let V : Set X := D.closedDisk.carrierᶜ
  let hVext : IsExteriorComponent (closure D0.carrier) V := by
    simpa [D0, V] using D.closedDisk.smoothDomain_complement_isExteriorComponent
  let hV := hVext.isComponentOf
  let hVopen : IsOpen V :=
    hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
  let W := D.puncturedPoleDisk
  let phi := D.radialDiffeomorph
  let y : W := phi.symm (v, 0)
  have hysecond : (phi y).2 = 0 := by simp [y, phi]
  have hyclosed : (y : X) ∈ D.closedDisk.carrier := by
    rw [← radialDiffeomorph_second_nonpos_iff_mem_closedDisk D y]
    rw [hysecond]
  have hynotDomain : (y : X) ∉ D0.carrier := by
    intro hy
    have hneg : (phi y).2 < 0 :=
      (D.closedDisk.radialPuncturedCollarDiffeomorph_second_lt_zero_iff
        p D.pole_mem_closedDisk_chart_source
        D.closedDisk_chart_p_eq_center
        D.closedDisk_double_closedRadius.le y).2 hy
    linarith
  have hyclosureDomain : (y : X) ∈ closure D0.carrier := by
    change (y : X) ∈ closure
      (D.closedDisk.expandedOpenDisk D.closedDisk.closedRadius)
    rw [D.closedDisk.closure_expandedOpenDisk_closedRadius]
    exact hyclosed
  let b : frontier D0.carrier := by
    refine ⟨(y : X), ?_⟩
    rw [frontier, D0.isOpen.interior_eq]
    exact ⟨hyclosureDomain, hynotDomain⟩
  have hbW : (b : X) ∈ W := y.2
  have hbVfront : (b : X) ∈ frontier V := by
    rw [frontier, hVopen.interior_eq]
    refine ⟨?_, ?_⟩
    · have hcl : (y : X) ∈ closure ((W : Set X) ∩
          (closure D0.carrier)ᶜ) :=
        sidePreservingAnnularCollar_zeroSlice_mem_closure_exteriorSide
          D0 W phi
          (fun z => by
            simpa [D0, W, phi] using
              (D.closedDisk.radialPuncturedCollarDiffeomorph_second_pos_iff
                p D.pole_mem_closedDisk_chart_source
                D.closedDisk_chart_p_eq_center
                D.closedDisk_double_closedRadius.le z).symm)
          y hysecond
      apply closure_mono _ hcl
      rintro x ⟨_hxW, hxout⟩
      change x ∉ closure
        (D.closedDisk.expandedOpenDisk D.closedDisk.closedRadius) at hxout
      rw [D.closedDisk.closure_expandedOpenDisk_closedRadius] at hxout
      exact hxout
    · simpa [V] using hyclosed
  have hexterior : ∀ z : W,
      ((z : X) ∉ closure D0.carrier ↔ 0 < (phi z).2) := by
    intro z
    simpa [D0, W, phi] using
      (D.closedDisk.radialPuncturedCollarDiffeomorph_second_pos_iff
        p D.pole_mem_closedDisk_chart_source
        D.closedDisk_chart_p_eq_center
        D.closedDisk_double_closedRadius.le z).symm
  rcases hVext.exists_proper_line_in_collarUnion_with_negativeRay
      E D0 W phi hexterior V b hbW hbVfront with
    ⟨line, hline, hnegative⟩
  have hU : exteriorComponentCollarUnion W V hVopen =
      puncturedSurfaceOpen p := by
    simpa [W, V] using
      D.closedDisk.radialPuncturedCollarUnion_eq_puncturedSurfaceOpen
        p D.pole_mem_closedDisk_chart_source
        D.closedDisk_chart_p_eq_center hVopen
  let e : exteriorComponentCollarUnion W V hVopen ≃ₘ⟮
      SurfaceRealModel, SurfaceRealModel⟯ puncturedSurfaceOpen p :=
    opensDiffeomorphOfMutualLE _ _ hU.le hU.ge
  let ambientLine : C(ℝ, puncturedSurfaceOpen p) :=
    ⟨fun t => e (line t), e.continuous.comp line.continuous⟩
  refine ⟨ambientLine, e.toHomeomorph.isProperMap.comp hline, ?_⟩
  intro t ht
  have hlineNegative := hnegative t ht
  apply Subtype.ext
  change ((ambientLine t : puncturedSurfaceOpen p) : X) =
    ((puncturedSurfacePoleRadialLine D v t : puncturedSurfaceOpen p) : X)
  change (line t : X) =
    ((D.radialDiffeomorph.symm (v, t) : D.puncturedPoleDisk) : X)
  rw [hlineNegative]
  have hbangle : (phi ⟨(b : X), hbW⟩).1 = v := by
    simp [b, y, phi]
  rw [hbangle]
  change
    ((D.radialDiffeomorph.symm
      (v, -(((-t).toNNReal : NNReal) : ℝ)) : D.puncturedPoleDisk) : X) =
      ((D.radialDiffeomorph.symm (v, t) : D.puncturedPoleDisk) : X)
  congr 3
  have hneg : 0 ≤ -t := neg_nonneg.mpr ht
  rw [Real.coe_toNNReal _ hneg]
  ring

/-- The radial pole collar and an exterior-component escape ray combine to
give a proper continuous line in the punctured surface. -/
theorem exists_proper_continuous_line_puncturedSurface
    [NoncompactSpace X]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    ∃ line : C(ℝ, puncturedSurfaceOpen p), IsProperMap line := by
  rcases exists_proper_continuous_line_puncturedSurface_with_negativeRadial
      E D v with ⟨line, hproper, _hnegative⟩
  exact ⟨line, hproper⟩

end

end JJMath.Uniformization
