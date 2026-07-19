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

/--
%%handwave
name:
  The punctured closed pole disk lies in the doubled pole disk
statement:
  Every point \(x\ne p\) of the closed coordinate disk of radius \(r/2\)
  belongs to the punctured coordinate disk of radius \(r\).
proof:
  The point lies in the chart source and its coordinate distance from the
  pole is at most \(r/2<r\); together with \(x\ne p\), these are precisely the
  defining conditions of the punctured pole disk.
-/
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

/--
%%handwave
name:
  Closedness of the punctured closed pole disk
statement:
  The closed pole-coordinate disk with its center removed is closed relative
  to the punctured surface.
proof:
  It is the inverse image of the compact, hence closed, coordinate disk under
  the continuous inclusion of the punctured surface into \(X\).
-/
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

/--
%%handwave
name:
  Continuity of the inclusion into the punctured pole disk
statement:
  The natural inclusion of the punctured closed half-radius disk into the
  doubled punctured pole disk is continuous.
proof:
  Its underlying map is the composite of the two continuous subtype
  inclusions.
-/
theorem continuous_puncturedClosedPoleDiskToPuncturedPoleDisk
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    Continuous (puncturedClosedPoleDiskToPuncturedPoleDisk D) := by
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/--
%%handwave
name:
  Nonpositive radial coordinate on the closed inner disk
statement:
  Every point of the punctured closed inner coordinate disk has radial collar
  coordinate at most zero.
proof:
  A positive radial coordinate characterizes the exterior of the closure of
  the inner disk.  Such exterior membership contradicts that the point lies
  in the closed disk.
-/
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

/--
%%handwave
name:
  Radial characterization of the closed inner pole disk
statement:
  For a point \(y\) in the doubled punctured pole disk,
  \[
    \Phi(y)_2\le0\quad\Longleftrightarrow\quad
    y\text{ lies in the closed inner coordinate disk}.
  \]
proof:
  The side-preserving radial collar identifies positive second coordinate
  exactly with the complement of the closed disk.  Negating this strict
  characterization gives the stated equivalence.
-/
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

/--
%%handwave
name:
  Formula for the punctured-surface radial tube coordinate
statement:
  The pole-coordinate radial tube map on the punctured surface is the
  annular radial tube map applied after transporting the point back to the
  annular slit.
proof:
  This is the defining composition of the two diffeomorphisms.
-/
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

/--
%%handwave
name:
  The pole-coordinate tube core is the radial pullback of the annular core
statement:
  The transition core of the pole-coordinate line tube is exactly the inverse
  image, under radial coordinates, of the transition core of the standard
  annular line tube.
proof:
  Expand both cores as inverse images of the same closed rectangle.  The
  radial preimage diffeomorphism and its inverse cancel, so membership on
  either side is equivalent.
-/
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

/--
%%handwave
name:
  Radial coordinates of the inverse pole tube map
statement:
  For tube coordinates \((s,t)\in\mathbb R^2\), the radial coordinates of the
  inverse pole-tube point are
  \[
    \bigl(\sigma_v^{-1}(t),s\bigr),
  \]
  where \(\sigma_v^{-1}\) is inverse stereographic projection from the cut
  direction \(v\).
proof:
  The pole radial diffeomorphism cancels its inverse, reducing the formula to
  the explicit inverse of the standard annular radial tube map.
-/
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

/--
%%handwave
name:
  The negative tube tail lies in the closed pole disk
statement:
  Every point of the negative transition tail of the pole-coordinate tube
  lies in the closed inner coordinate disk.
proof:
  Its tube radial parameter is nonpositive.  The inverse-tube coordinate
  formula makes this the second radial coordinate, and the radial
  characterization then places the point in the closed disk.
-/
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

/--
%%handwave
name:
  Closedness of the angular core in the punctured pole disk
statement:
  Inside the punctured closed pole disk, the subset whose radial angle lies
  in the closed annular core arc is closed.
proof:
  It is the inverse image of the closed core arc under the continuous angular
  component of the radial coordinate map.
-/
theorem puncturedClosedPoleDiskRadialCore_isClosed
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    IsClosed (puncturedClosedPoleDiskRadialCore D v) := by
  exact (annularRadialCoreAngleSet_isClosed v).preimage
    (continuous_fst.comp
      (D.radialDiffeomorph.continuous.comp
        (continuous_puncturedClosedPoleDiskToPuncturedPoleDisk D)))

/--
%%handwave
name:
  Range of the negative radial transition tail
statement:
  The negative transition-tail map has image exactly the angular core strip
  inside the punctured closed pole disk.
proof:
  A tail point has arbitrary nonpositive radial coordinate and transverse
  coordinate in \([-1,1]\), hence its angle lies on the core arc.  Conversely,
  combine the radial coordinate of a core point with a parameter of its core
  angle to construct a unique tail point mapping to it.
-/
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

/--
%%handwave
name:
  The negative radial tail is embedded in the closed pole disk
statement:
  The negative transition-tail map into the punctured closed pole disk is a
  topological embedding.
proof:
  The tail inclusion into \(\mathbb R^2\) is an embedding, as are the inverse
  tube diffeomorphism and all successive subtype inclusions.  Their composite
  remains an embedding, and codomain restriction to the closed disk preserves
  this property.
-/
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

/--
%%handwave
name:
  The negative radial tail is a closed embedding
statement:
  The negative transition tail is a closed topologically embedded subset of
  the punctured closed pole disk.
proof:
  The map is an embedding and its range is the closed angular core strip.
-/
theorem puncturedClosedPoleDiskRadialNegativeTailMap_isClosedEmbedding
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    Topology.IsClosedEmbedding
      (puncturedClosedPoleDiskRadialNegativeTailMap D v) := by
  refine ⟨puncturedClosedPoleDiskRadialNegativeTailMap_isEmbedding D v, ?_⟩
  rw [puncturedClosedPoleDiskRadialNegativeTailMap_range]
  exact puncturedClosedPoleDiskRadialCore_isClosed D v

/--
%%handwave
name:
  Properness of the negative radial tail in the punctured surface
statement:
  The negative pole-coordinate transition-tail map into the full punctured
  surface is proper.
proof:
  It factors as a closed embedding into the punctured closed pole disk,
  followed by the closed embedding of that disk into the punctured surface.
  A composite closed embedding is proper.
-/
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

/--
%%handwave
name:
  Properness of the negative tail of the ambient pole tube
statement:
  The negative transition tail obtained from the inverse ambient radial tube
  diffeomorphism is a proper map into the punctured surface.
proof:
  It is the same map as the previously constructed proper negative radial
  tail, after unfolding the two equivalent tube descriptions.
-/
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

/--
%%handwave
name:
  Closedness of the pole-coordinate radial transition core
statement:
  The transition core of the radial line tube is closed in the punctured
  pole-coordinate disk.
proof:
  It is the inverse image under the continuous radial diffeomorphism of the
  closed transition core of the standard annular tube.
-/
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

/--
%%handwave
name:
  Smoothness of the central radial pole line
statement:
  Fixing an angular direction \(v\in S^1\), the curve obtained by varying the
  radial coordinate through all \(t\in\mathbb R\) is a smooth curve in the
  punctured surface.
proof:
  The map \(t\mapsto(v,t)\) is smooth, as is the inverse radial
  diffeomorphism.  Compose them and restrict the resulting ambient curve to
  the punctured surface.
-/
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

/--
%%handwave
name:
  Injectivity of the central radial pole line
statement:
  For fixed \(v\in S^1\), distinct radial parameters determine distinct
  points on the central pole-coordinate radial line.
proof:
  Equality of two curve values gives equality after applying the injective
  inverse radial diffeomorphism, hence \((v,s)=(v,t)\) and therefore \(s=t\).
-/
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

/--
%%handwave
name:
  A proper line with prescribed negative radial half
statement:
  On a noncompact Riemann surface with a Green pole coordinate, for every
  \(v\in S^1\) there is a proper continuous line
  \(\ell:\mathbb R\to X\setminus\{p\}\) satisfying
  \[
    \ell(t)=\Phi^{-1}(v,t)\qquad(t\le0),
  \]
  where \(\Phi\) is the radial pole-coordinate diffeomorphism.
proof:
  The zero-radius point lies on the frontier of the closed inner disk.  Join
  the negative radial collar ray there to a proper escape ray in the exterior
  component supplied by the exhaustion theorem.  The collar–exterior union
  is the whole punctured surface, and its canonical identification preserves
  properness and the prescribed negative ray.
-/
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

/--
%%handwave
name:
  Existence of a proper line in the punctured surface
statement:
  A noncompact Riemann surface equipped with the Green pole coordinate admits
  a proper continuous map \(\ell:\mathbb R\to X\setminus\{p\}\).
proof:
  Use the proper line constructed by gluing the negative radial pole ray to
  an exterior escape ray, and forget its prescribed-half property.
-/
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
