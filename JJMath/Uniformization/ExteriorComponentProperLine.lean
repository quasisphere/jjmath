import JJMath.Uniformization.SurfaceEndPath
import JJMath.Uniformization.SmoothFrontierMayerVietoris

/-!
# Proper lines through an exterior-component collar

The negative radial half of a side-preserving annular collar is proper in the
union of the collar with its exterior component.  The proof glues the inward
collar depth to the constant zero function on the exterior component.  This
is the collar half of the proper line used to carry the angular period class.
-/

open Set
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-- The two open patches of a collar--component union: the collar and the
exterior component itself. -/
def exteriorComponentCollarDepthPatch
    (W : TopologicalSpace.Opens X) (V : Set X) (hVopen : IsOpen V) :
    Bool → Set (exteriorComponentCollarUnion W V hVopen)
  | false => {y | (y : X) ∈ W}
  | true => {y | (y : X) ∈ V}

theorem isOpen_exteriorComponentCollarDepthPatch
    (W : TopologicalSpace.Opens X) (V : Set X) (hVopen : IsOpen V)
    (b : Bool) :
    IsOpen (exteriorComponentCollarDepthPatch W V hVopen b) := by
  cases b
  · exact W.isOpen.preimage continuous_subtype_val
  · exact hVopen.preimage continuous_subtype_val

/-- On the collar patch use the nonnegative inward depth; on the exterior
component patch use zero. -/
noncomputable def exteriorComponentCollarDepthLocalMap
    (W : TopologicalSpace.Opens X) (V : Set X) (hVopen : IsOpen V)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ)) :
    (b : Bool) →
      C(exteriorComponentCollarDepthPatch W V hVopen b, NNReal)
  | false =>
      { toFun := fun y =>
          (-((phi ⟨(y : X), y.2⟩).2)).toNNReal
        continuous_toFun := by fun_prop }
  | true =>
      { toFun := fun _ => 0
        continuous_toFun := continuous_const }

theorem exteriorComponentCollarDepthLocalMap_agree
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (i j : Bool) (y : exteriorComponentCollarUnion W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
    (hyi : y ∈ exteriorComponentCollarDepthPatch W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) i)
    (hyj : y ∈ exteriorComponentCollarDepthPatch W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) j) :
    exteriorComponentCollarDepthLocalMap W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) phi i ⟨y, hyi⟩ =
      exteriorComponentCollarDepthLocalMap W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) phi j ⟨y, hyj⟩ := by
  cases i <;> cases j
  · rfl
  · change (-((phi ⟨(y : X), hyi⟩).2)).toNNReal = 0
    have hpositive : 0 < (phi ⟨(y : X), hyi⟩).2 :=
      (hexteriorSide ⟨(y : X), hyi⟩).mp (hV.subset hyj)
    exact Real.toNNReal_of_nonpos (neg_nonpos.mpr hpositive.le)
  · change 0 = (-((phi ⟨(y : X), hyj⟩).2)).toNNReal
    have hpositive : 0 < (phi ⟨(y : X), hyj⟩).2 :=
      (hexteriorSide ⟨(y : X), hyj⟩).mp (hV.subset hyi)
    exact (Real.toNNReal_of_nonpos (neg_nonpos.mpr hpositive.le)).symm
  · rfl

theorem exteriorComponentCollarDepthPatch_cover
    (W : TopologicalSpace.Opens X) (V : Set X) (hVopen : IsOpen V)
    (y : exteriorComponentCollarUnion W V hVopen) :
    ∃ b : Bool, exteriorComponentCollarDepthPatch W V hVopen b ∈ 𝓝 y := by
  have hy := y.2
  change (y : X) ∈ W ∨ (y : X) ∈ V at hy
  rcases hy with hyW | hyV
  · exact ⟨false,
      (isOpen_exteriorComponentCollarDepthPatch W V hVopen false).mem_nhds hyW⟩
  · exact ⟨true,
      (isOpen_exteriorComponentCollarDepthPatch W V hVopen true).mem_nhds hyV⟩

/-- The inward collar depth, extended continuously by zero over the exterior
component. -/
noncomputable def exteriorComponentCollarDepth
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    C(exteriorComponentCollarUnion W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl), NNReal) :=
  ContinuousMap.liftCover
    (exteriorComponentCollarDepthPatch W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
    (exteriorComponentCollarDepthLocalMap W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) phi)
    (exteriorComponentCollarDepthLocalMap_agree
      D W phi hexteriorSide V hV)
    (exteriorComponentCollarDepthPatch_cover W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))

theorem exteriorComponentCollarDepth_apply_of_mem_collar
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (y : exteriorComponentCollarUnion W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
    (hyW : (y : X) ∈ W) :
    exteriorComponentCollarDepth D W phi hexteriorSide V hV y =
      (-((phi ⟨(y : X), hyW⟩).2)).toNNReal := by
  unfold exteriorComponentCollarDepth
  convert
    (ContinuousMap.liftCover_coe
      (S := exteriorComponentCollarDepthPatch W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
      (φ := exteriorComponentCollarDepthLocalMap W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) phi)
      (hφ := exteriorComponentCollarDepthLocalMap_agree
        D W phi hexteriorSide V hV)
      (hS := exteriorComponentCollarDepthPatch_cover W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
      (i := false) ⟨y, hyW⟩) using 1

/-- The radial ray running inward through the collar at a fixed angular
coordinate. -/
noncomputable def exteriorComponentCollarNegativeRay
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (V : Set X) (hVopen : IsOpen V) (v : Circle) :
    C(NNReal, exteriorComponentCollarUnion W V hVopen) where
  toFun s :=
    ⟨((phi.symm (v, -(s : ℝ)) : W) : X),
      Or.inl (phi.symm (v, -(s : ℝ))).2⟩
  continuous_toFun := by fun_prop

theorem exteriorComponentCollarDepth_negativeRay
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (v : Circle) (s : NNReal) :
    exteriorComponentCollarDepth D W phi hexteriorSide V hV
        (exteriorComponentCollarNegativeRay W phi V
          (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) v s) = s := by
  rw [exteriorComponentCollarDepth_apply_of_mem_collar]
  · change
      (-((phi (phi.symm (v, -(s : ℝ)))).2)).toNNReal = s
    rw [phi.apply_symm_apply]
    simp

/-- The inward radial collar ray is proper in the union of the collar and the
exterior component. -/
theorem isProperMap_exteriorComponentCollarNegativeRay
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (v : Circle) :
    IsProperMap
      (exteriorComponentCollarNegativeRay W phi V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) v) := by
  letI : LocallyCompactSpace
      (exteriorComponentCollarUnion W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl)) :=
    (exteriorComponentCollarUnion W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl)).isOpen.locallyCompactSpace
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(exteriorComponentCollarNegativeRay W phi V
    (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) v).continuous, ?_⟩
  intro C hC
  let depth := exteriorComponentCollarDepth D W phi hexteriorSide V hV
  have himage : IsCompact (depth '' C) := hC.image depth.continuous
  have hpre_closed : IsClosed
      ((exteriorComponentCollarNegativeRay W phi V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) v) ⁻¹' C) :=
    hC.isClosed.preimage
      (exteriorComponentCollarNegativeRay W phi V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) v).continuous
  apply himage.of_isClosed_subset hpre_closed
  intro s hs
  refine ⟨exteriorComponentCollarNegativeRay W phi V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) v s, hs, ?_⟩
  exact exteriorComponentCollarDepth_negativeRay
    D W phi hexteriorSide V hV v s

/-! ## Bringing an exterior proper ray into the collar union -/

/-- Regard a ray whose range lies in the exterior component as a ray in the
collar--component union. -/
noncomputable def exteriorProperRayInCollarUnion
    (W : TopologicalSpace.Opens X) (V : Set X) (hVopen : IsOpen V)
    (r : C(NNReal, X)) (hrange : Set.range r ⊆ V) :
    C(NNReal, exteriorComponentCollarUnion W V hVopen) where
  toFun t := ⟨r t, Or.inr (hrange ⟨t, rfl⟩)⟩
  continuous_toFun :=
    Continuous.subtype_mk r.continuous
      (fun t => Or.inr (hrange ⟨t, rfl⟩))

theorem isProperMap_exteriorProperRayInCollarUnion
    (W : TopologicalSpace.Opens X) (V : Set X) (hVopen : IsOpen V)
    (r : C(NNReal, X)) (hrange : Set.range r ⊆ V)
    (hr : IsProperMap r) :
    IsProperMap (exteriorProperRayInCollarUnion W V hVopen r hrange) := by
  let U : TopologicalSpace.Opens X := exteriorComponentCollarUnion W V hVopen
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(exteriorProperRayInCollarUnion W V hVopen r hrange).continuous, ?_⟩
  intro C hC
  have hCimage : IsCompact (((↑) : U → X) '' C) :=
    hC.image continuous_subtype_val
  have hrpre : IsCompact (r ⁻¹' (((↑) : U → X) '' C)) :=
    (isProperMap_iff_isCompact_preimage.mp hr).2 hCimage
  have hpreClosed : IsClosed
      ((exteriorProperRayInCollarUnion W V hVopen r hrange) ⁻¹' C) :=
    hC.isClosed.preimage
      (exteriorProperRayInCollarUnion W V hVopen r hrange).continuous
  apply hrpre.of_isClosed_subset hpreClosed
  intro t ht
  exact ⟨exteriorProperRayInCollarUnion W V hVopen r hrange t, ht, rfl⟩

/-- An incident exterior component supplies a proper continuous line through
the collar union: one end runs inward through the collar, while the other
runs to infinity inside the exterior component. -/
theorem IsExteriorComponent.exists_proper_line_in_collarUnion_with_negativeRay
    (E : SmoothRelativelyCompactExhaustion X)
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsExteriorComponent (closure D.carrier) V)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    ∃ line : C(ℝ, exteriorComponentCollarUnion W V
        (hV.isComponentOf.isOpen_of_isOpen
          isClosed_closure.isOpen_compl)),
      IsProperMap line ∧
        ∀ t : ℝ, t ≤ 0 →
          line t = exteriorComponentCollarNegativeRay W phi V
            (hV.isComponentOf.isOpen_of_isOpen
              isClosed_closure.isOpen_compl)
            (phi ⟨(p : X), hpW⟩).1 (-t).toNNReal := by
  let hVopen : IsOpen V :=
    hV.isComponentOf.isOpen_of_isOpen isClosed_closure.isOpen_compl
  letI : LocallyCompactSpace
      (exteriorComponentCollarUnion W V hVopen) :=
    (exteriorComponentCollarUnion W V hVopen).isOpen.locallyCompactSpace
  rcases hV.exists_proper_ray_along_smoothExhaustion E D.compact_closure with
    ⟨_N, r, _hD, hrproper, hrrange, _hrescape⟩
  let rpos : C(NNReal, exteriorComponentCollarUnion W V hVopen) :=
    exteriorProperRayInCollarUnion W V hVopen r hrrange
  have hrpos : IsProperMap rpos :=
    isProperMap_exteriorProperRayInCollarUnion
      W V hVopen r hrrange hrproper
  let v : Circle := (phi ⟨(p : X), hpW⟩).1
  let rneg : C(NNReal, exteriorComponentCollarUnion W V hVopen) :=
    exteriorComponentCollarNegativeRay W phi V hVopen v
  have hrneg : IsProperMap rneg :=
    isProperMap_exteriorComponentCollarNegativeRay
      D W phi hexteriorSide V hV.isComponentOf v
  let zW : W := phi.symm (v, 1)
  have hzExterior : (zW : X) ∉ closure D.carrier := by
    apply (hexteriorSide zW).mpr
    rw [phi.apply_symm_apply]
    norm_num
  have hzV : (zW : X) ∈ V :=
    sidePreservingAnnularCollar_exteriorSide_subset_component
      D W phi hexteriorSide V hV.isComponentOf p hpW hpV
        ⟨zW.2, hzExterior⟩
  let zU : exteriorComponentCollarUnion W V hVopen :=
    ⟨(zW : X), Or.inl zW.2⟩
  let radial : Path (rneg 0) zU :=
    Path.mk
      { toFun := fun t =>
          ⟨((phi.symm (v, (t : ℝ)) : W) : X),
            Or.inl (phi.symm (v, (t : ℝ))).2⟩
        continuous_toFun := by fun_prop }
      (by
        apply Subtype.ext
        simp [rneg, exteriorComponentCollarNegativeRay])
      (by
        apply Subtype.ext
        simp [zU, zW])
  have hjoined : JoinedIn V (zW : X) (r 0) :=
    (hV.isComponentOf.isPathConnected_of_compl_isClosed isClosed_closure).joinedIn
      (zW : X) hzV (r 0) (hrrange ⟨0, rfl⟩)
  let throughV : Path zU (rpos 0) :=
    Path.mk
      { toFun := fun t =>
          ⟨hjoined.somePath t,
            Or.inr (hjoined.somePath_mem t)⟩
        continuous_toFun := by fun_prop }
      (by
        apply Subtype.ext
        exact hjoined.somePath.source)
      (by
        apply Subtype.ext
        exact hjoined.somePath.target)
  let connector : Path (rneg 0) (rpos 0) := radial.trans throughV
  let rpos' : C(NNReal, exteriorComponentCollarUnion W V hVopen) :=
    pathPrependRay rpos connector
  have hrpos' : IsProperMap rpos' :=
    isProperMap_pathPrependRay rpos connector hrpos
  have hstart : rneg 0 = rpos' 0 := by
    rw [pathPrependRay_zero]
  let line : C(ℝ, exteriorComponentCollarUnion W V hVopen) :=
    twoRaysLine rneg rpos' hstart
  refine ⟨line,
    isProperMap_twoRaysLine rneg rpos' hstart hrneg hrpos', ?_⟩
  intro t ht
  simp [line, twoRaysLine, ht, rneg, v]

/-- An incident exterior component supplies a proper continuous line through
the collar union. -/
theorem IsExteriorComponent.exists_proper_line_in_collarUnion
    (E : SmoothRelativelyCompactExhaustion X)
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsExteriorComponent (closure D.carrier) V)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    ∃ line : C(ℝ, exteriorComponentCollarUnion W V
        (hV.isComponentOf.isOpen_of_isOpen
          isClosed_closure.isOpen_compl)),
      IsProperMap line := by
  rcases hV.exists_proper_line_in_collarUnion_with_negativeRay
      E D W phi hexteriorSide V p hpW hpV with
    ⟨line, hproper, _hnegative⟩
  exact ⟨line, hproper⟩

end

end JJMath.Uniformization
