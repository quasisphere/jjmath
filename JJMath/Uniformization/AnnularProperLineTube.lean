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

@[simp]
theorem annularRadialLineTubeDiffeomorph_apply
    (v : Circle) (x : annularPunctureOpen v) :
    annularRadialLineTubeDiffeomorph v x =
      ((x : Circle × ℝ).2,
        (stereographic' 1 v (x : Circle × ℝ).1) 0) := by
  rfl

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

theorem annularRadialCoreAngleSet_isCompact (v : Circle) :
    IsCompact (annularRadialCoreAngleSet v) := by
  exact isCompact_range (continuous_annularRadialCoreAngleMap v)

theorem annularRadialCoreAngleSet_isClosed (v : Circle) :
    IsClosed (annularRadialCoreAngleSet v) :=
  (annularRadialCoreAngleSet_isCompact v).isClosed

/-- The transition core is the product of a compact angular arc with the
entire radial line. -/
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

/-- The closed transition strip remains closed in the full annular cylinder,
even though the surrounding tube omits one radial line. -/
theorem annularRadialLineTubeCore_isClosed (v : Circle) :
    IsClosed
      (properLineTubeCore AnnularCylinderModel (annularPunctureOpen v)
        (annularRadialLineTubeDiffeomorph v)) := by
  rw [annularRadialLineTubeCore_eq]
  exact (annularRadialCoreAngleSet_isClosed v).prod isClosed_univ

end

end JJMath.Uniformization
