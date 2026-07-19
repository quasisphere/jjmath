import JJMath.Manifold.AnnularCohomology
import JJMath.Manifold.ProperLineThom

/-!
# A radial proper-line tube in the annular cylinder

Deleting one radial line from the annular cylinder gives a plane.  Ordering
the resulting coordinates as radial position followed by stereographic
angular position identifies this plane with the standard proper-line tube.
The transition strip has compact angular width, so its image is closed in the
full annular cylinder.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

/-- The canonical global product chart on the annular cylinder with one
radial line deleted. -/
noncomputable def canonicalAnnularPuncturePlaneDiffeomorph (v : Circle) :
    annularPunctureOpen v ≃ₘ⟮AnnularCylinderModel,
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × ℝ)⟯
      (⊤ : TopologicalSpace.Opens
        (EuclideanSpace ℝ (Fin 1) × ℝ)) := by
  exact deRham_boundarylessExtendedChart_restrictionDiffeomorph
    AnnularCylinderModel
    (e := annularPunctureChart v)
    (annularPunctureChart_mem_atlas v)
    (annularPunctureOpen v) ⊤
    (by
      simpa [annularPunctureOpen, deRham_boundarylessExtendedChart] using
        ((annularPunctureChart v).extend_source
          (I := AnnularCylinderModel)).symm)
    (by
      intro y hy
      change y ∈ ((annularPunctureChart v).extend AnnularCylinderModel).target
      rw [OpenPartialHomeomorph.extend_target]
      simp [annularPunctureChart, AnnularCylinderModel]
      exact Set.mem_univ y)

/--
%%handwave
name:
  Formula for the canonical slit-cylinder plane coordinate
statement:
  On the annular cylinder with the radial line at \(v\) removed, the canonical
  plane coordinate sends \((q,s)\) to
  \((\sigma_v(q),s)\), where \(\sigma_v\) is stereographic projection from
  \(v\).
proof:
  This is the defining formula of the extended-chart restriction used to
  construct the diffeomorphism.
-/
@[simp]
theorem canonicalAnnularPuncturePlaneDiffeomorph_apply
    (v : Circle) (x : annularPunctureOpen v) :
    (((canonicalAnnularPuncturePlaneDiffeomorph v x :
      (⊤ : TopologicalSpace.Opens
        (EuclideanSpace ℝ (Fin 1) × ℝ))) :
          EuclideanSpace ℝ (Fin 1) × ℝ)) =
      (stereographic' 1 v (x : Circle × ℝ).1, (x : Circle × ℝ).2) := by
  rfl

/-- The terminal open submanifold of a normed space is canonically
diffeomorphic to the space itself. -/
noncomputable def topOpenToAmbientDiffeomorph
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (⊤ : TopologicalSpace.Opens E) ≃ₘ⟮
      modelWithCornersSelf ℝ E, modelWithCornersSelf ℝ E⟯ E where
  toEquiv :=
    { toFun := fun x => x
      invFun := fun x => ⟨x, Set.mem_univ x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := by
    classical
    change ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞
        (fun x : E => (⟨x, Set.mem_univ x⟩ :
          (⊤ : TopologicalSpace.Opens E)))
    intro x
    let q : (⊤ : TopologicalSpace.Opens E) := ⟨x, Set.mem_univ x⟩
    let retract : E → (⊤ : TopologicalSpace.Opens E) := fun y =>
      if hy : y ∈ (⊤ : TopologicalSpace.Opens E) then ⟨y, hy⟩ else q
    have hretract : ContMDiffAt (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ E) ∞ retract x := by
      rw [← contMDiffAt_subtype_iff (x := q)]
      have heq : (fun y : (⊤ : TopologicalSpace.Opens E) => retract y) = id := by
        funext y
        simp [retract]
      rw [heq]
      exact contMDiffAt_id
    simpa [retract] using hretract

/-- Identify the one-dimensional Euclidean angular coordinate with the
second real coordinate and swap it past the radial coordinate. -/
noncomputable def euclideanFinOneProdRealToProperLineDiffeomorph :
    (EuclideanSpace ℝ (Fin 1) × ℝ) ≃ₘ⟮
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × ℝ),
      ProperLineTubeModel⟯ ℝ × ℝ := by
  let e : (EuclideanSpace ℝ (Fin 1) × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (((EuclideanSpace.equiv (Fin 1) ℝ).trans
      (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).prodCongr
        (ContinuousLinearEquiv.refl ℝ ℝ)).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        change ContMDiff
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × ℝ))
          (modelWithCornersSelf ℝ (ℝ × ℝ)) ∞ e
        exact e.contDiff.contMDiff
      contMDiff_invFun := by
        change ContMDiff
          (modelWithCornersSelf ℝ (ℝ × ℝ))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × ℝ))
          ∞ e.symm
        exact e.symm.contDiff.contMDiff }

/-- The slit annular cylinder as a proper-line tube.  The first coordinate
runs radially and the second crosses the slit. -/
noncomputable def annularRadialLineTubeDiffeomorph (v : Circle) :
    annularPunctureOpen v ≃ₘ⟮AnnularCylinderModel,
      ProperLineTubeModel⟯ ℝ × ℝ :=
  (canonicalAnnularPuncturePlaneDiffeomorph v).trans
    ((topOpenToAmbientDiffeomorph
      (EuclideanSpace ℝ (Fin 1) × ℝ)).trans
      euclideanFinOneProdRealToProperLineDiffeomorph)

/--
%%handwave
name:
  Formula for the radial proper-line tube coordinate
statement:
  The proper-line tube coordinate on the slit annular cylinder sends
  \((q,s)\) to \((s,\sigma_v(q))\), with the one-dimensional stereographic
  coordinate identified with a real number.
proof:
  Compose the canonical slit-cylinder plane coordinate with the linear
  identification of the one-dimensional Euclidean coordinate and swap the
  angular and radial factors.
-/
@[simp]
theorem annularRadialLineTubeDiffeomorph_apply
    (v : Circle) (x : annularPunctureOpen v) :
    annularRadialLineTubeDiffeomorph v x =
      ((x : Circle × ℝ).2,
        (stereographic' 1 v (x : Circle × ℝ).1) 0) := by
  rfl

/--
%%handwave
name:
  Inverse formula for the radial proper-line tube coordinate
statement:
  The inverse tube coordinate sends \((s,t)\in\mathbb R^2\) to the annular
  point whose radial coordinate is \(s\) and whose circle coordinate is the
  inverse stereographic image of \(t\).
proof:
  Invert the factor swap, the one-dimensional Euclidean identification, and
  the stereographic coordinate in the defining composite.
-/
@[simp]
theorem annularRadialLineTubeDiffeomorph_symm_apply
    (v : Circle) (s t : ℝ) :
    (((annularRadialLineTubeDiffeomorph v).symm (s, t) :
      annularPunctureOpen v) : Circle × ℝ) =
      ((stereographic' 1 v).symm
        ((EuclideanSpace.equiv (Fin 1) ℝ).symm
          ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm t)), s) := by
  rfl

/-- The compact angular arc swept out by the closed transition interval. -/
noncomputable def annularRadialCoreAngleMap (v : Circle) :
    Set.Icc (-1 : ℝ) 1 → Circle := fun t =>
  (stereographic' 1 v).symm
    ((EuclideanSpace.equiv (Fin 1) ℝ).symm
      ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm (t : ℝ)))

/--
%%handwave
name:
  Continuity of the annular core-angle parameterization
statement:
  The map from \([-1,1]\) to \(S^1\) obtained by applying inverse
  stereographic projection from \(v\) to the real angular coordinate is
  continuous.
proof:
  The linear identifications of the interval coordinate with the
  one-dimensional Euclidean space are continuous, and inverse stereographic
  projection is continuous on its target; compose them.
-/
theorem continuous_annularRadialCoreAngleMap (v : Circle) :
    Continuous (annularRadialCoreAngleMap v) := by
  let f : Set.Icc (-1 : ℝ) 1 → EuclideanSpace ℝ (Fin 1) := fun t =>
    (EuclideanSpace.equiv (Fin 1) ℝ).symm
      ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm (t : ℝ))
  have hf : Continuous f := by fun_prop
  have htarget : ∀ t, f t ∈ (stereographic' 1 v).target := by
    intro t
    simp [stereographic'_target]
  exact (stereographic' 1 v).continuousOn_symm.comp_continuous hf htarget

def annularRadialCoreAngleSet (v : Circle) : Set Circle :=
  Set.range (annularRadialCoreAngleMap v)

/--
%%handwave
name:
  Compactness of the annular core-angle arc
statement:
  The circle arc obtained as the inverse stereographic image of
  \([-1,1]\) is compact.
proof:
  It is the continuous image of the compact interval \([-1,1]\).
-/
theorem annularRadialCoreAngleSet_isCompact (v : Circle) :
    IsCompact (annularRadialCoreAngleSet v) := by
  exact isCompact_range (continuous_annularRadialCoreAngleMap v)

/--
%%handwave
name:
  Closedness of the annular core-angle arc
statement:
  The inverse-stereographic image in \(S^1\) of the interval \([-1,1]\) is
  closed.
proof:
  The arc is compact, and the circle is Hausdorff.
-/
theorem annularRadialCoreAngleSet_isClosed (v : Circle) :
    IsClosed (annularRadialCoreAngleSet v) :=
  (annularRadialCoreAngleSet_isCompact v).isClosed

/--
%%handwave
name:
  Product description of the radial proper-line transition core
statement:
  In the annular cylinder, the inverse image of the tube strip
  \(\mathbb R\times[-1,1]\) is exactly \(A_v\times\mathbb R\), where \(A_v\)
  is the compact circle arc obtained from angular stereographic coordinates
  in \([-1,1]\).
proof:
  Use the explicit inverse tube-coordinate formula.  A point in the strip has
  circle coordinate in \(A_v\), and conversely an angle in \(A_v\) supplies a
  parameter \(t\in[-1,1]\) whose tube preimage is the given annular point.
-/
theorem annularRadialLineTubeCore_eq (v : Circle) :
    properLineTubeCore AnnularCylinderModel (annularPunctureOpen v)
        (annularRadialLineTubeDiffeomorph v) =
      annularRadialCoreAngleSet v ×ˢ (Set.univ : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    let t : Set.Icc (-1 : ℝ) 1 := ⟨q.2, hq⟩
    refine ⟨?_, Set.mem_univ _⟩
    exact ⟨t, rfl⟩
  · rintro ⟨⟨t, ht⟩, _⟩
    refine ⟨(x.2, (t : ℝ)), t.2, ?_⟩
    change (annularRadialCoreAngleMap v t, x.2) = x
    ext
    · exact congrArg Subtype.val ht
    · rfl

/--
%%handwave
name:
  Closedness of the annular radial proper-line core
statement:
  The transition core of the radial proper-line tube is closed in the full
  annular cylinder \(S^1\times\mathbb R\).
proof:
  By the product description, the core is \(A_v\times\mathbb R\).  The
  angular arc \(A_v\) is closed and \(\mathbb R\) is closed in itself, so
  their product is closed.
-/
theorem annularRadialLineTubeCore_isClosed (v : Circle) :
    IsClosed
      (properLineTubeCore AnnularCylinderModel (annularPunctureOpen v)
        (annularRadialLineTubeDiffeomorph v)) := by
  rw [annularRadialLineTubeCore_eq]
  exact (annularRadialCoreAngleSet_isClosed v).prod isClosed_univ

end

end JJMath.Uniformization
