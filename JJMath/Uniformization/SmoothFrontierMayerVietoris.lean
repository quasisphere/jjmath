import JJMath.Uniformization.SmoothFrontierPeriodicFlow
import JJMath.Uniformization.BoundaryComponentPrimitive

/-!
# The Mayer--Vietoris cover cut out by a frontier collar

A side-preserving annular collar around the frontier of a complementary
component determines the two-open cover used in the cohomological hole-filling
argument.  This file contains only the topological and smooth bookkeeping for
that cover; the extension of the angular class over the noncompact side is a
separate input.
-/

open Set
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-- When ambient first de Rham cohomology vanishes, the connected frontier of
a complementary component is precisely the smooth frontier component through
any incident point. -/
theorem smoothBoundaryDomain_complement_component_frontier_eq_frontierComponentCarrier
    [Subsingleton
      (JJMath.Manifold.DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (D : SmoothBoundaryDomain X) (hDnonempty : D.carrier.Nonempty)
    (hDpre : IsPreconnected D.carrier)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpV : (p : X) ∈ frontier V) :
    frontier V = frontierComponentCarrier D.carrier p := by
  have hfrontierConnected : IsConnected (frontier V) :=
    smoothBoundaryDomain_complement_component_frontier_isConnected_of_deRhamH1_subsingleton
      hnoncompact D hDnonempty hDpre V hV
  have hfrontierSubset : frontier V ⊆ frontier D.carrier :=
    hV.frontier_subset_smoothBoundaryDomain_frontier D V
  apply Subset.antisymm
  · intro x hxV
    let liftToDomainFrontier : frontier V → frontier D.carrier := fun y =>
      ⟨(y : X), hfrontierSubset y.2⟩
    have hlift : Continuous liftToDomainFrontier :=
      Continuous.subtype_mk continuous_subtype_val
        (fun y : frontier V => hfrontierSubset y.2)
    letI : ConnectedSpace (frontier V) :=
      isConnected_iff_connectedSpace.mp hfrontierConnected
    have himagePre : IsPreconnected
        (liftToDomainFrontier '' (univ : Set (frontier V))) :=
      isPreconnected_univ.image liftToDomainFrontier hlift.continuousOn
    let pV : frontier V := ⟨(p : X), hpV⟩
    let xV : frontier V := ⟨x, hxV⟩
    have hpImage : p ∈
        liftToDomainFrontier '' (univ : Set (frontier V)) := by
      exact ⟨pV, mem_univ _, rfl⟩
    have hxImage : liftToDomainFrontier xV ∈
        liftToDomainFrontier '' (univ : Set (frontier V)) := by
      exact ⟨xV, mem_univ _, rfl⟩
    have hxComponent : liftToDomainFrontier xV ∈ connectedComponent p :=
      himagePre.subset_connectedComponent hpImage hxImage
    exact ⟨liftToDomainFrontier xV, hxComponent, rfl⟩
  · rintro x ⟨q, hq, rfl⟩
    exact smoothBoundaryDomain_connected_boundary_component_subset_frontier_of_incident
      D p V hV hpV q hq

/-- Every complementary component has a full side-preserving annular collar
which contains its entire frontier. -/
theorem exists_sidePreservingAnnularCollar_of_complementComponent
    [Subsingleton
      (JJMath.Manifold.DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (D : SmoothBoundaryDomain X) (hDnonempty : D.carrier.Nonempty)
    (hDpre : IsPreconnected D.carrier)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    ∃ (p : frontier D.carrier) (W : TopologicalSpace.Opens X)
        (phi : W ≃ₘ⟮SurfaceRealModel,
          JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ)),
      (p : X) ∈ frontier V ∧
      (p : X) ∈ W ∧
      frontier V ⊆ (W : Set X) ∧
      (∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0)) ∧
      (∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2)) := by
  rcases hV.frontier_inter_frontier_nonempty_of_compl_isClosed
      isClosed_closure (hDnonempty.mono subset_closure) with
    ⟨x, hxV, hxClosureD⟩
  have hxD : x ∈ frontier D.carrier := frontier_closure_subset hxClosureD
  let p : frontier D.carrier := ⟨x, hxD⟩
  rcases
      exists_sidePreservingDiffeomorph_annularCylinder_smoothFrontierComponentCollar
        D p with
    ⟨W, hpW, hcomponentW, phi, hside, hexteriorSide⟩
  have hfrontierEq :
      frontier V = frontierComponentCarrier D.carrier p :=
    smoothBoundaryDomain_complement_component_frontier_eq_frontierComponentCarrier
      hnoncompact D hDnonempty hDpre V hV p hxV
  refine ⟨p, W, phi, hxV, hpW, ?_, hside, hexteriorSide⟩
  rw [hfrontierEq]
  exact hcomponentW

/-- The exterior half of a side-preserving collar belongs to the complementary
component incident to the chosen frontier point. -/
theorem sidePreservingAnnularCollar_exteriorSide_subset_component
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    (W : Set X) ∩ (closure D.carrier)ᶜ ⊆ V := by
  have hpre : IsPreconnected
      ((W : Set X) ∩ (closure D.carrier)ᶜ) :=
    sidePreservingAnnularCollar_exteriorSide_isPreconnected
      D W phi hexteriorSide
  have hWmeetV : ((W : Set X) ∩ V).Nonempty :=
    (mem_closure_iff.mp (frontier_subset_closure hpV))
      (W : Set X) W.isOpen hpW
  rcases hWmeetV with ⟨x, hxW, hxV⟩
  have hxExterior : x ∈ (closure D.carrier)ᶜ := hV.subset hxV
  have hxHalf : x ∈ (W : Set X) ∩ (closure D.carrier)ᶜ :=
    ⟨hxW, hxExterior⟩
  have hhalfComponent :
      (W : Set X) ∩ (closure D.carrier)ᶜ ⊆
        connectedComponentIn (closure D.carrier)ᶜ x :=
    hpre.subset_connectedComponentIn hxHalf inter_subset_right
  rw [← hV.eq_connectedComponentIn_of_mem hxV] at hhalfComponent
  exact hhalfComponent

/-- Inside a side-preserving collar, the incident complementary component is
exactly the positive, exterior half. -/
theorem sidePreservingAnnularCollar_inter_component_eq_exteriorSide
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    (W : Set X) ∩ V = (W : Set X) ∩ (closure D.carrier)ᶜ := by
  apply Subset.antisymm
  · rintro x ⟨hxW, hxV⟩
    exact ⟨hxW, hV.subset hxV⟩
  · intro x hx
    exact ⟨hx.1,
      sidePreservingAnnularCollar_exteriorSide_subset_component
        D W phi hexteriorSide V hV p hpW hpV hx⟩

/-- The zero slice of a side-preserving collar lies in the closure of its
positive half. -/
theorem sidePreservingAnnularCollar_zeroSlice_mem_closure_exteriorSide
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (y : W) (hyzero : (phi y).2 = 0) :
    (y : X) ∈ closure ((W : Set X) ∩ (closure D.carrier)ᶜ) := by
  let T : Set (Circle × ℝ) := univ ×ˢ Ioi 0
  have hphiClosure : phi y ∈ closure T := by
    rw [show closure T = (univ : Set Circle) ×ˢ Ici 0 by
      simp [T, closure_prod_eq, closure_Ioi]]
    exact ⟨mem_univ _, by simp [hyzero]⟩
  have hyClosureW : y ∈ closure (phi ⁻¹' T) := by
    change y ∈ closure (phi.toHomeomorph ⁻¹' T)
    rw [← phi.toHomeomorph.preimage_closure]
    exact hphiClosure
  have hyImageClosure : (y : X) ∈
      closure (((↑) : W → X) '' (phi ⁻¹' T)) := by
    exact image_closure_subset_closure_image continuous_subtype_val
      (mem_image_of_mem ((↑) : W → X) hyClosureW)
  have himage : ((↑) : W → X) '' (phi ⁻¹' T) =
      (W : Set X) ∩ (closure D.carrier)ᶜ := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      apply (hexteriorSide z).mpr
      simpa [T] using hz.2
    · rintro ⟨hxW, hxExterior⟩
      let z : W := ⟨x, hxW⟩
      refine ⟨z, ?_, rfl⟩
      exact ⟨mem_univ _, (hexteriorSide z).mp hxExterior⟩
  rwa [himage] at hyImageClosure

/-- In an incident side-preserving collar, deleting the closure of the
complementary component leaves exactly the domain half of the collar. -/
theorem sidePreservingAnnularCollar_compl_componentClosure_eq_domainSide
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    (W : Set X) ∩ (closure V)ᶜ = (W : Set X) ∩ D.carrier := by
  have hhalfV : (W : Set X) ∩ (closure D.carrier)ᶜ ⊆ V :=
    sidePreservingAnnularCollar_exteriorSide_subset_component
      D W phi hexteriorSide V hV p hpW hpV
  apply Subset.antisymm
  · rintro x ⟨hxW, hxNotClosureV⟩
    let y : W := ⟨x, hxW⟩
    rcases lt_trichotomy (phi y).2 0 with hnegative | hzero | hpositive
    · exact ⟨hxW, (hside y).mpr hnegative⟩
    · have hyClosureHalf : x ∈
          closure ((W : Set X) ∩ (closure D.carrier)ᶜ) :=
        sidePreservingAnnularCollar_zeroSlice_mem_closure_exteriorSide
          D W phi hexteriorSide y hzero
      exact False.elim (hxNotClosureV (closure_mono hhalfV hyClosureHalf))
    · have hxHalf : x ∈ (W : Set X) ∩ (closure D.carrier)ᶜ :=
        ⟨hxW, (hexteriorSide y).mpr hpositive⟩
      exact False.elim (hxNotClosureV (subset_closure (hhalfV hxHalf)))
  · rintro x ⟨hxW, hxD⟩
    refine ⟨hxW, ?_⟩
    intro hxClosureV
    rcases (mem_closure_iff.mp hxClosureV) D.carrier D.isOpen hxD with
      ⟨z, hzD, hzV⟩
    exact hV.subset hzV (subset_closure hzD)

/-- The open union of an incident complementary component and its full
annular collar. -/
def exteriorComponentCollarUnion
    (W : TopologicalSpace.Opens X) (V : Set X) (hVopen : IsOpen V) :
    TopologicalSpace.Opens X :=
  W ⊔ ⟨V, hVopen⟩

/-- The open complement of the closure of a complementary component. -/
def complementComponentClosureOpen (V : Set X) :
    TopologicalSpace.Opens X :=
  ⟨(closure V)ᶜ, isClosed_closure.isOpen_compl⟩

/-- A full collar of the component frontier, together with the component on
one side and the complement of its closure on the other, covers the surface. -/
theorem exteriorComponentCollarUnion_sup_complementComponentClosureOpen
    (W : TopologicalSpace.Opens X) (V : Set X) (hVopen : IsOpen V)
    (hfrontierW : frontier V ⊆ (W : Set X)) :
    exteriorComponentCollarUnion W V hVopen ⊔
      complementComponentClosureOpen V = ⊤ := by
  ext x
  change ((x ∈ (W : Set X) ∨ x ∈ V) ∨ x ∉ closure V) ↔ True
  rw [iff_true]
  by_cases hxClosure : x ∈ closure V
  · by_cases hxV : x ∈ V
    · exact Or.inl (Or.inr hxV)
    · have hxFrontier : x ∈ frontier V := by
        rw [frontier, hVopen.interior_eq]
        exact ⟨hxClosure, hxV⟩
      exact Or.inl (Or.inl (hfrontierW hxFrontier))
  · exact Or.inr hxClosure

/-- The overlap of the complementary-side collar union with the open
complement of the component closure is exactly the domain half-collar. -/
theorem exteriorComponentCollarUnion_inf_complementComponentClosureOpen
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    exteriorComponentCollarUnion W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) ⊓
      complementComponentClosureOpen V =
        W ⊓ ⟨D.carrier, D.isOpen⟩ := by
  ext x
  change (((x ∈ (W : Set X) ∨ x ∈ V) ∧ x ∉ closure V) ↔
    x ∈ (W : Set X) ∧ x ∈ D.carrier)
  have hcollar := sidePreservingAnnularCollar_compl_componentClosure_eq_domainSide
    D W phi hside hexteriorSide V hV p hpW hpV
  constructor
  · rintro ⟨hxWV, hxNotClosure⟩
    rcases hxWV with hxW | hxV
    · have hxCollar : x ∈ (W : Set X) ∩ (closure V)ᶜ :=
        ⟨hxW, hxNotClosure⟩
      rw [hcollar] at hxCollar
      exact hxCollar
    · exact False.elim (hxNotClosure (subset_closure hxV))
  · intro hx
    have hx' : x ∈ (W : Set X) ∩ (closure V)ᶜ := by
      rw [hcollar]
      exact hx
    exact ⟨Or.inl hx'.1, hx'.2⟩

/-- The Mayer--Vietoris overlap cut out by an incident side-preserving collar
is smoothly an annular cylinder. -/
noncomputable def exteriorComponentCollarMayerVietorisOverlapDiffeomorph
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    ((exteriorComponentCollarUnion W V
          (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) ⊓
        complementComponentClosureOpen V) : TopologicalSpace.Opens X) ≃ₘ⟮
      SurfaceRealModel, JJMath.Manifold.AnnularCylinderModel⟯
        (Circle × ℝ) := by
  rw [exteriorComponentCollarUnion_inf_complementComponentClosureOpen
    D W phi hside hexteriorSide V hV p hpW hpV]
  exact sidePreservingAnnularCollarDomainDiffeomorph D W phi hside

end

end JJMath.Uniformization
