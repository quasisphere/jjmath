import JJMath.Manifold.DeRhamPoincare
import JJMath.Topology.FineSheaf
import JJMath.Topology.SheafAcyclicResolution
import JJMath.Topology.SingularCohomology
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.Topology.Sheaves.Points
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Comparison architecture for de Rham's theorem

This file records the global pieces which turn the local Poincare lemma into
the de Rham comparison theorem.  The intended proof is the standard fine
resolution argument: the Poincare lemma gives exactness on stalks, partitions
of unity make the sheaves of smooth forms fine, and sheaf cohomology of the
constant real sheaf is compared with real singular cohomology.
-/

open scoped Manifold ContDiff Topology ZeroObject

namespace TopologicalSpace.Opens

instance instOrderTop (X : Type*) [TopologicalSpace X] :
    OrderTop (TopologicalSpace.Opens X) where
  top := ⊤
  le_top U := by
    intro x hx
    trivial

end TopologicalSpace.Opens

namespace CategoryTheory
namespace GrothendieckTopology

open CategoryTheory.Limits

universe uC vC uA vA uPoint

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable [HasColimitsOfSize.{uPoint, uPoint} A]

instance point_presheafFiber_additive (Φ : Point.{uPoint} J) :
    (Φ.presheafFiber (A := A)).Additive := by
  dsimp [Point.presheafFiber]
  let W : (Cᵒᵖ ⥤ A) ⥤ (Φ.fiber.Elementsᵒᵖ ⥤ A) :=
    (Functor.whiskeringLeft Φ.fiber.Elementsᵒᵖ Cᵒᵖ A).obj
      (CategoryOfElements.π Φ.fiber).op
  haveI : W.Additive := by
    constructor
    intro X Y f g
    ext U
    rfl
  change (W ⋙ colim).Additive
  infer_instance

instance point_sheafFiber_additive [HasSheafify J A] (Φ : Point.{uPoint} J) :
    (Φ.sheafFiber (A := A)).Additive := by
  dsimp [Point.sheafFiber]
  infer_instance

end GrothendieckTopology

namespace ShiftedHom

universe u₁ v₁ u₂ v₂ wM

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {M : Type wM} [AddMonoid M] [HasShift C M] [HasShift D M]

/--
%%handwave
name:
  Fully faithful functors give bijections on shifted morphisms
statement:
  A fully faithful functor which commutes with shifts identifies shifted
  morphisms before and after applying the functor.
proof:
  A shifted morphism \(X\to Y[a]\) maps to the composite
  \(F(X)\to F(Y[a])\to F(Y)[a]\).  The inverse first composes with the inverse
  shift-commutation isomorphism and then uses full faithfulness of \(F\).
  The two inverse laws are the two triangle identities for that isomorphism.
-/
noncomputable def mapEquivOfFullyFaithful (F : C ⥤ D) [F.CommShift M]
    (hF : F.FullyFaithful) (X Y : C) (a : M) :
    ShiftedHom X Y a ≃ ShiftedHom (F.obj X) (F.obj Y) a := by
  letI : F.Full := hF.full
  letI : F.Faithful := hF.faithful
  refine
    { toFun := fun f => f.map F
      invFun := fun g => F.preimage (g ≫ (F.commShiftIso a).inv.app Y)
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply F.map_injective
    dsimp [ShiftedHom.map]
    rw [Functor.map_preimage]
    simpa [Category.assoc] using
      congrArg (fun k => F.map f ≫ k) ((F.commShiftIso a).hom_inv_id_app Y)
  · intro g
    dsimp [ShiftedHom.map]
    rw [Functor.map_preimage]
    simpa [Category.assoc] using
      congrArg (fun k => g ≫ k) ((F.commShiftIso a).inv_hom_id_app Y)

/--
%%handwave
name:
  The shifted-morphism map of a fully faithful functor is bijective
statement:
  A fully faithful functor which commutes with shifts induces a bijection on
  each shifted morphism set.
proof:
  Take the bijectivity of [the shifted-morphism equivalence induced by a fully faithful functor](lean:CategoryTheory.ShiftedHom.mapEquivOfFullyFaithful).
-/
theorem map_bijective_of_fullyFaithful (F : C ⥤ D) [F.CommShift M]
    (hF : F.FullyFaithful) (X Y : C) (a : M) :
    Function.Bijective (fun f : ShiftedHom X Y a => f.map F) :=
  (mapEquivOfFullyFaithful F hF X Y a).bijective

variable {X X' Y Y' : C}

/--
%%handwave
name:
  Isomorphic source and target identify shifted morphisms
statement:
  An isomorphism of sources and an isomorphism of targets induce a bijection
  on shifted morphism sets.
proof:
  Send a shifted morphism \(X\to Y[a]\) to the composite obtained by
  precomposing with the source isomorphism and postcomposing with the shifted
  target isomorphism.  The inverse uses the inverse source and target
  isomorphisms, and the two inverse laws are the ordinary isomorphism
  identities after applying the shift functor.
-/
noncomputable def isoCongrEquiv (eX : X' ≅ X) (eY : Y ≅ Y') (a : M) :
    ShiftedHom X Y a ≃ ShiftedHom X' Y' a where
  toFun f := eX.hom ≫ f ≫ eY.hom⟦a⟧'
  invFun g := eX.inv ≫ g ≫ eY.inv⟦a⟧'
  left_inv f := by
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
    simp only [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.comp_id]
  right_inv g := by
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc]
    simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]

end ShiftedHom

namespace Sheaf

universe uC vC uA vA uB vB z z'

open CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {K : Type z} [Category.{z'} K]
variable {F : A ⥤ B} [J.HasSheafCompose F]

instance sheafCompose_additive [Preadditive A] [Preadditive B] [F.Additive] :
    (sheafCompose J F).Additive where
  map_add {X Y} f g := by
    apply (sheafToPresheaf J B).map_injective
    ext U
    change F.map ((f + g).hom.app U) = F.map (f.hom.app U) + F.map (g.hom.app U)
    have hfg : (f + g).hom.app U = f.hom.app U + g.hom.app U := rfl
    rw [hfg]
    simp

theorem sheafCompose_preservesLimitsOfShape_of_preserves
    [HasLimitsOfShape K A] [HasLimitsOfShape K B] [PreservesLimitsOfShape K F] :
    PreservesLimitsOfShape K (sheafCompose J F) := by
  have hcomp :
      PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) := by
    exact preservesLimitsOfShape_of_natIso
      (F := sheafToPresheaf J A ⋙ (Functor.whiskeringRight Cᵒᵖ A B).obj F)
      (G := sheafCompose J F ⋙ sheafToPresheaf J B)
      (Iso.refl _)
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (sheafCompose J F) (sheafToPresheaf J B)

/-- The standard sheafified colimit cocone commutes with postcomposition by a
functor which commutes with sheafification. -/
noncomputable def sheafifyCocone_composeIso
    [HasSheafify J A] [HasSheafify J B] [J.PreservesSheafification F]
    {G : K ⥤ Sheaf J A}
    (E : Cocone (G ⋙ sheafToPresheaf J A)) :
    Sheaf.sheafifyCocone (((Functor.whiskeringRight Cᵒᵖ A B).obj F).mapCocone E) ≅
      (sheafCompose J F).mapCocone (Sheaf.sheafifyCocone E) := by
  refine Cocone.ext (ObjectProperty.isoMk _ (sheafifyComposeIso J F E.pt)) ?_
  intro k
  apply (sheafToPresheaf J B).map_injective
  dsimp [Functor.mapCocone]
  rw [Sheaf.sheafifyCocone_ι_app_val]
  change (Functor.whiskerRight (E.ι.app k) F ≫ toSheafify J (E.pt ⋙ F)) ≫
      (sheafifyComposeIso J F E.pt).hom =
    Functor.whiskerRight ((sheafifyCocone E).ι.app k).hom F
  calc
    (Functor.whiskerRight (E.ι.app k) F ≫ toSheafify J (E.pt ⋙ F)) ≫
        (sheafifyComposeIso J F E.pt).hom
        = Functor.whiskerRight (E.ι.app k) F ≫
            (toSheafify J (E.pt ⋙ F) ≫ (sheafifyComposeIso J F E.pt).hom) := by
          rw [Category.assoc]
    _ = Functor.whiskerRight (E.ι.app k) F ≫
          Functor.whiskerRight (toSheafify J E.pt) F := by
          exact congrArg (fun q => Functor.whiskerRight (E.ι.app k) F ≫ q)
            (sheafComposeIso_hom_fac (J := J) (F := F) E.pt)
    _ = Functor.whiskerRight ((sheafifyCocone E).ι.app k).hom F := by
          rw [Sheaf.sheafifyCocone_ι_app_val]
          exact (Functor.whiskerRight_comp (E.ι.app k) (toSheafify J E.pt) F).symm

/--
%%handwave
name:
  Sheaf composition preserves colimits when it commutes with sheafification
statement:
  If a coefficient functor preserves the relevant colimits and commutes with
  sheafification, then postcomposition by that functor preserves those
  colimits of sheaves.
proof:
  A colimit of sheaves is obtained by sheafifying the objectwise colimit of
  the underlying presheaves.  Since the coefficient functor preserves the
  objectwise colimit and commutes with sheafification, applying it to the
  sheaf colimit gives the sheafification of the objectwise colimit of the
  transformed diagram, which is the colimit in the target sheaf category.
-/
theorem sheafCompose_preservesColimitsOfShape_of_preservesSheafification
    [HasSheafify J A] [HasSheafify J B]
    [HasColimitsOfShape K A] [HasColimitsOfShape K B]
    [PreservesColimitsOfShape K F] [J.PreservesSheafification F] :
    PreservesColimitsOfShape K (sheafCompose J F) := by
  constructor
  intro G
  let W : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ B) :=
    (Functor.whiskeringRight Cᵒᵖ A B).obj F
  haveI : PreservesColimitsOfShape K W := by
    dsimp [W]
    infer_instance
  let E : Cocone (G ⋙ sheafToPresheaf J A) := colimit.cocone _
  have hE : IsColimit E := colimit.isColimit _
  let tA : Cocone G := Sheaf.sheafifyCocone E
  have hA : IsColimit tA := by
    dsimp [tA]
    exact Sheaf.isColimitSheafifyCocone E hE
  let EB : Cocone ((G ⋙ sheafCompose J F) ⋙ sheafToPresheaf J B) := W.mapCocone E
  have hW : IsColimit EB := by
    dsimp [EB, W]
    exact isColimitOfPreserves ((Functor.whiskeringRight Cᵒᵖ A B).obj F) hE
  let tB : Cocone (G ⋙ sheafCompose J F) := Sheaf.sheafifyCocone EB
  have hB : IsColimit tB := by
    dsimp [tB]
    exact Sheaf.isColimitSheafifyCocone EB hW
  refine preservesColimit_of_preserves_colimit_cocone hA ?_
  refine IsColimit.ofIsoColimit hB ?_
  dsimp [tA, tB, EB, W]
  exact sheafifyCocone_composeIso (J := J) (F := F) E

end Sheaf

namespace LocalizerMorphism

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {D₁ : Type u₃} [Category.{v₃} D₁]
variable {D₂ : Type u₄} [Category.{v₄} D₂]
variable {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

noncomputable def localizedFunctor_fullyFaithful_of_homMap_bijective
    (Φ : LocalizerMorphism W₁ W₂)
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
    (G : D₁ ⥤ D₂) [CatCommSq Φ.functor L₁ L₂ G]
    (hbij :
      ∀ X Y : C₁,
        Function.Bijective
          (Φ.homMap L₁ L₂ :
            (L₁.obj X ⟶ L₁.obj Y) →
              (L₂.obj (Φ.functor.obj X) ⟶
                L₂.obj (Φ.functor.obj Y)))) :
    G.FullyFaithful := by
  classical
  letI : L₁.EssSurj := Localization.essSurj L₁ W₁
  refine
    { preimage := fun {A B} f => ?_
      map_preimage := ?_
      preimage_map := ?_ }
  · let X := L₁.objPreimage A
    let Y := L₁.objPreimage B
    let eA := L₁.objObjPreimageIso A
    let eB := L₁.objObjPreimageIso B
    let e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso Φ.functor L₁ L₂ G
    let u :
        L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y) :=
      e.hom.app X ≫ G.map eA.hom ≫ f ≫ G.map eB.inv ≫ e.inv.app Y
    exact eA.inv ≫ Classical.choose ((hbij X Y).2 u) ≫ eB.hom
  · intro A B f
    let X := L₁.objPreimage A
    let Y := L₁.objPreimage B
    let eA := L₁.objObjPreimageIso A
    let eB := L₁.objObjPreimageIso B
    let e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso Φ.functor L₁ L₂ G
    let u :
        L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y) :=
      e.hom.app X ≫ G.map eA.hom ≫ f ≫ G.map eB.inv ≫ e.inv.app Y
    let g := Classical.choose ((hbij X Y).2 u)
    have hg : Φ.homMap L₁ L₂ g = u :=
      Classical.choose_spec ((hbij X Y).2 u)
    rw [LocalizerMorphism.homMap_apply
      (Φ := Φ) (L₁ := L₁) (L₂ := L₂) (G := G) (e := e)] at hg
    have hgmap : G.map g = G.map eA.hom ≫ f ≫ G.map eB.inv := by
      apply (cancel_epi (e.hom.app X)).1
      apply (cancel_mono (e.inv.app Y)).1
      simpa [u, Category.assoc] using hg
    change G.map (eA.inv ≫ g ≫ eB.hom) = f
    simp [Functor.map_comp, hgmap, Category.assoc]
  · intro A B f
    let X := L₁.objPreimage A
    let Y := L₁.objPreimage B
    let eA := L₁.objObjPreimageIso A
    let eB := L₁.objObjPreimageIso B
    let e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso Φ.functor L₁ L₂ G
    let u :
        L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y) :=
      e.hom.app X ≫ G.map eA.hom ≫ G.map f ≫ G.map eB.inv ≫ e.inv.app Y
    let g := Classical.choose ((hbij X Y).2 u)
    have hg : Φ.homMap L₁ L₂ g = u :=
      Classical.choose_spec ((hbij X Y).2 u)
    have hg' : g = eA.hom ≫ f ≫ eB.inv := by
      apply (hbij X Y).1
      rw [hg]
      dsimp [u]
      rw [LocalizerMorphism.homMap_apply
        (Φ := Φ) (L₁ := L₁) (L₂ := L₂) (G := G) (e := e)]
      simp [Functor.map_comp, Category.assoc]
    change eA.inv ≫ g ≫ eB.hom = f
    simp [hg', Category.assoc]

end LocalizerMorphism

namespace Functor

universe u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

set_option checkBinderAnnotations false in
/--
%%handwave
name:
  Fully faithful derived functors identify Ext groups
statement:
  If an exact functor induces a fully faithful functor on derived categories,
  then it induces a bijection on all Ext groups.
proof:
  Interpret Ext groups as morphisms from a single complex to a shifted single
  complex in the derived category.  The exact functor commutes with the single
  complex embedding and with shifts, and the induced derived functor is fully
  faithful, so the corresponding map on these morphism groups is bijective.
tags:
  milestone
-/
theorem mapExtAddHom_bijective_of_mapDerivedCategory_fullyFaithful
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    (hF : F.mapDerivedCategory.FullyFaithful) (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) := by
  let eSingle := F.mapDerivedCategorySingleFunctor 0
  let eShifted :=
    ShiftedHom.mapEquivOfFullyFaithful F.mapDerivedCategory hF
      ((DerivedCategory.singleFunctor C 0).obj X)
      ((DerivedCategory.singleFunctor C 0).obj Y) (n : ℤ)
  let eTransport :=
    ShiftedHom.isoCongrEquiv ((eSingle.app X).symm) (eSingle.app Y) (n : ℤ)
  let eExt : Abelian.Ext.{w₁} X Y n ≃ Abelian.Ext.{w₂} (F.obj X) (F.obj Y) n :=
    Abelian.Ext.homEquiv.trans
      (eShifted.trans (eTransport.trans Abelian.Ext.homEquiv.symm))
  have hfun : ⇑(F.mapExtAddHom X Y n) = eExt := by
    funext α
    apply Abelian.Ext.homEquiv.injective
    dsimp [eExt, eShifted, eTransport, ShiftedHom.isoCongrEquiv,
      ShiftedHom.mapEquivOfFullyFaithful]
    change (Abelian.Ext.mapExactFunctor F α).hom = _
    rw [Abelian.Ext.mapExactFunctor_hom]
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hfun]
  exact eExt.bijective

/--
%%handwave
name:
  Exact functors carry degree-zero postcomposition in Ext to degree-zero postcomposition
statement:
  For an exact additive functor, the induced map on Ext sends postcomposition
  by a morphism in degree zero to postcomposition by the image of that
  morphism.
proof:
  Compare the two Ext classes as shifted morphisms in the derived category.
  The exact functor commutes with single complexes and with shifts, and the
  shifted-morphism map respects composition and degree-zero morphisms.
tags:
  milestone
-/
theorem mapExtAddHom_comp_mk₀
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    {X Y Z : C} (n : ℕ) (α : Abelian.Ext X Y n) (f : Y ⟶ Z) :
    F.mapExtAddHom X Z n
        (α.comp (Abelian.Ext.mk₀ f) (add_zero n)) =
      (F.mapExtAddHom X Y n α).comp
        (Abelian.Ext.mk₀ (F.map f)) (add_zero n) := by
  apply Abelian.Ext.homEquiv.injective
  rw [Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply]
  simp only [Abelian.Ext.mapExactFunctor_hom, Abelian.Ext.comp_hom,
    Abelian.Ext.mk₀_hom, ShiftedHom.map_comp, ShiftedHom.map_mk₀]
  rw [ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀]
  have hnat :
      (shiftFunctor (DerivedCategory D) (n : ℤ)).map
          (F.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map f)) ≫
        (shiftFunctor (DerivedCategory D) (n : ℤ)).map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app Z) =
      (shiftFunctor (DerivedCategory D) (n : ℤ)).map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
        (shiftFunctor (DerivedCategory D) (n : ℤ)).map
          ((DerivedCategory.singleFunctor D 0).map (F.map f)) := by
    simpa [Functor.comp_map] using
      congrArg ((shiftFunctor (DerivedCategory D) (n : ℤ)).map)
        ((F.mapDerivedCategorySingleFunctor 0).hom.naturality f)
  simpa [Category.assoc] using
    congrArg (fun k =>
      (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        α.hom.map F.mapDerivedCategory ≫ k) hnat

noncomputable def mapHomologicalComplex_fullyFaithful
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (hF : F.FullyFaithful)
    {ι : Type*} (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).FullyFaithful := by
  refine
    { preimage := fun {K L} φ =>
        { f := fun i => hF.preimage (φ.f i)
          comm' := fun i j hij => ?_ }
      map_preimage := ?_
      preimage_map := ?_ }
  · apply hF.map_injective
    simpa [Functor.mapHomologicalComplex_obj_d] using φ.comm i j
  · intro K L φ
    ext i
    exact hF.map_preimage (φ.f i)
  · intro K L φ
    ext i
    exact hF.preimage_map (φ.f i)

noncomputable def homotopyOfMapHomotopy
    (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful)
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} {f g : K ⟶ L}
    (h : Homotopy ((F.mapHomologicalComplex c).map f)
      ((F.mapHomologicalComplex c).map g)) :
    Homotopy f g := by
  refine
    { hom := fun i j => hF.preimage (h.hom i j)
      zero := ?_
      comm := ?_ }
  · intro i j hij
    apply hF.map_injective
    simpa using h.zero i j hij
  · intro i
    apply hF.map_injective
    simpa [dNext, prevD, Functor.mapHomologicalComplex_obj_d] using h.comm i

noncomputable def mapHomotopyCategory_fullyFaithful_of_mapHomologicalComplex
    (F : C ⥤ D) [F.Additive]
    {ι : Type*} (c : ComplexShape ι)
    (hComplex : (F.mapHomologicalComplex c).FullyFaithful)
    (hreflect :
      ∀ {K L : HomologicalComplex C c} {f g : K ⟶ L},
        Homotopy ((F.mapHomologicalComplex c).map f)
          ((F.mapHomologicalComplex c).map g) →
        Homotopy f g) :
    (F.mapHomotopyCategory c).FullyFaithful := by
  refine
    { preimage := fun {X Y} φ =>
        (HomotopyCategory.quotient C c).map (hComplex.preimage φ.out)
      map_preimage := ?_
      preimage_map := ?_ }
  · intro X Y φ
    change
      (HomotopyCategory.quotient D c).map
        ((F.mapHomologicalComplex c).map (hComplex.preimage φ.out)) = φ
    rw [hComplex.map_preimage]
    exact HomotopyCategory.quotient_map_out φ
  · intro X Y φ
    let ψ := ((F.mapHomotopyCategory c).map φ).out
    have hq :
        (HomotopyCategory.quotient D c).map
            ψ =
          (HomotopyCategory.quotient D c).map
            ((F.mapHomologicalComplex c).map φ.out) := by
      have hleft :
          (HomotopyCategory.quotient D c).map ψ =
            (F.mapHomotopyCategory c).map φ := by
        dsimp [ψ]
        exact HomotopyCategory.quotient_map_out ((F.mapHomotopyCategory c).map φ)
      have hright :
          (F.mapHomotopyCategory c).map φ =
            (HomotopyCategory.quotient D c).map
              ((F.mapHomologicalComplex c).map φ.out) := by
        have hφ :
            (F.mapHomotopyCategory c).map φ =
              (F.mapHomotopyCategory c).map
                ((HomotopyCategory.quotient C c).map φ.out) :=
          congrArg (fun η => (F.mapHomotopyCategory c).map η)
            (HomotopyCategory.quotient_map_out φ).symm
        exact hφ.trans (Functor.mapHomotopyCategory_map (F := F) (c := c) φ.out)
      exact hleft.trans hright
    have Hup :
        Homotopy ψ
          ((F.mapHomologicalComplex c).map φ.out) :=
      HomotopyCategory.homotopyOfEq _ _ hq
    have Hmap :
        Homotopy
          ((F.mapHomologicalComplex c).map
            (hComplex.preimage ψ))
          ((F.mapHomologicalComplex c).map φ.out) := by
      simpa [hComplex.map_preimage] using Hup
    dsimp [ψ] at Hmap
    calc
      (HomotopyCategory.quotient C c).map
          (hComplex.preimage (((F.mapHomotopyCategory c).map φ).out)) =
          (HomotopyCategory.quotient C c).map φ.out := by
            exact HomotopyCategory.eq_of_homotopy _ _ (hreflect Hmap)
      _ = φ := HomotopyCategory.quotient_map_out φ

noncomputable def mapDerivedCategory_fullyFaithful_of_localizedHom_bijective
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (Φ :
      LocalizerMorphism
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
        (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)))
    [CatCommSq Φ.functor (DerivedCategory.Qh (C := C))
      (DerivedCategory.Qh (C := D)) F.mapDerivedCategory]
    (hbij :
      ∀ K L : HomotopyCategory C (ComplexShape.up ℤ),
        Function.Bijective
          (Φ.homMap (DerivedCategory.Qh (C := C))
            (DerivedCategory.Qh (C := D)) :
              ((DerivedCategory.Qh (C := C)).obj K ⟶
                (DerivedCategory.Qh (C := C)).obj L) →
              ((DerivedCategory.Qh (C := D)).obj (Φ.functor.obj K) ⟶
                (DerivedCategory.Qh (C := D)).obj (Φ.functor.obj L)))) :
    F.mapDerivedCategory.FullyFaithful := by
  exact
    LocalizerMorphism.localizedFunctor_fullyFaithful_of_homMap_bijective
      (Φ := Φ)
      (L₁ := DerivedCategory.Qh (C := C))
      (L₂ := DerivedCategory.Qh (C := D))
      (G := F.mapDerivedCategory) hbij

end Functor

end CategoryTheory

namespace AddCommGrpCat

universe u

theorem finset_sum_apply {A B : AddCommGrpCat.{u}} {ι : Type*}
    (s : Finset ι) (f : ι → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, (f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih]

end AddCommGrpCat

namespace JJMath
namespace Manifold

open Set
open Topology
open Filter
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe v w m uC vC tSmall tBig

variable {E : Type v} [NormedAddCommGroup E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]

noncomputable local instance realConstantSheafCohomologyModule_topCatOf
    {M0 : Type m} [TopologicalSpace M0]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M0 : TopCat.{m}))
      AddCommGrpCat.{m}]
    [HasExt.{m}
      (Sheaf (Opens.grothendieckTopology (TopCat.of M0 : TopCat.{m}))
        AddCommGrpCat.{m})]
    (n : ℕ) :
    Module ℝ
      (JJMath.Cohomology.RealConstantSheafCohomology
        (TopCat.of M0 : TopCat.{m}) n) :=
  JJMath.Cohomology.realConstantSheafCohomologyModule
    (TopCat.of M0 : TopCat.{m}) n

/--
%%handwave
name:
  Convex subtargets of boundaryless charts
statement:
  Around every point of a finite-dimensional smooth real manifold modeled on a
  vector space without boundary, one can choose a chart and shrink its target
  to a nonempty convex open set still lying in the chart target.
proof:
  Since the chart target is open in the normed model vector space, choose a
  sufficiently small open ball around the coordinate of the point.  Open balls
  in a normed vector space are convex.
-/
theorem deRham_selfModel_exists_convex_chart_restriction
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [FiniteDimensional ℝ E0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace E0 M0]
    [IsManifold 𝓘(ℝ, E0) ∞ M0]
    (x : M0) :
    ∃ (e : OpenPartialHomeomorph M0 E0)
      (U : TopologicalSpace.Opens M0) (V : TopologicalSpace.Opens E0),
      e ∈ atlas E0 M0 ∧
        x ∈ U ∧
          Convex ℝ (V : Set E0) ∧
            (V : Set E0).Nonempty ∧
              (U : Set M0) = e.source ∩ e ⁻¹' (V : Set E0) ∧
                (V : Set E0) ⊆ e.target := by
  let e : OpenPartialHomeomorph M0 E0 := chartAt E0 x
  have hx_source : x ∈ e.source := by
    simp [e]
  have hx_target : e x ∈ e.target := e.map_source hx_source
  rcases Metric.isOpen_iff.1 e.open_target (e x) hx_target with
    ⟨r, hr, hball⟩
  let V : TopologicalSpace.Opens E0 :=
    ⟨Metric.ball (e x) r, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens M0 :=
    ⟨e.source ∩ e ⁻¹' (V : Set E0), e.isOpen_inter_preimage V.2⟩
  refine ⟨e, U, V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [e]
  · exact ⟨hx_source, by simpa [V] using Metric.mem_ball_self (x := e x) hr⟩
  · simpa [V] using convex_ball (e x) r
  · exact ⟨e x, by simpa [V] using Metric.mem_ball_self (x := e x) hr⟩
  · rfl
  · simpa [V] using hball

/--
%%handwave
name:
  Subordinate convex subtargets of boundaryless charts
statement:
  Around every point of an open set in a finite-dimensional smooth real
  manifold modeled on a vector space without boundary, one can choose a chart
  and shrink its target to a nonempty convex open set whose source
  restriction is contained in the given open set.
proof:
  Intersect the chart source with the prescribed open set and take its image
  under the chart.  This image is open and contains the coordinate of the
  point, so it contains a small convex ball.  The inverse image of that ball
  inside the chart source is contained in the prescribed open set by
  injectivity of the chart on its source.
-/
theorem deRham_selfModel_exists_convex_chart_restriction_subordinate
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [FiniteDimensional ℝ E0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace E0 M0]
    [IsManifold 𝓘(ℝ, E0) ∞ M0]
    (x : M0) (W : TopologicalSpace.Opens M0) (hxW : x ∈ W) :
    ∃ (e : OpenPartialHomeomorph M0 E0)
      (U : TopologicalSpace.Opens M0) (V : TopologicalSpace.Opens E0),
      e ∈ atlas E0 M0 ∧
        x ∈ U ∧
          U ≤ W ∧
            Convex ℝ (V : Set E0) ∧
              (V : Set E0).Nonempty ∧
                (U : Set M0) = e.source ∩ e ⁻¹' (V : Set E0) ∧
                  (V : Set E0) ⊆ e.target := by
  let e : OpenPartialHomeomorph M0 E0 := chartAt E0 x
  have hx_source : x ∈ e.source := by
    simp [e]
  let s : Set M0 := e.source ∩ (W : Set M0)
  have hs_open : IsOpen s := e.open_source.inter W.2
  have hs_subset : s ⊆ e.source := inter_subset_left
  have hs_image_open : IsOpen (e '' s) :=
    e.isOpen_image_of_subset_source hs_open hs_subset
  have hx_image : e x ∈ e '' s := ⟨x, ⟨hx_source, hxW⟩, rfl⟩
  rcases Metric.isOpen_iff.1 hs_image_open (e x) hx_image with
    ⟨r, hr, hball⟩
  let V : TopologicalSpace.Opens E0 :=
    ⟨Metric.ball (e x) r, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens M0 :=
    ⟨e.source ∩ e ⁻¹' (V : Set E0), e.isOpen_inter_preimage V.2⟩
  refine ⟨e, U, V, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [e]
  · exact ⟨hx_source, by simpa [V] using Metric.mem_ball_self (x := e x) hr⟩
  · intro y hyU
    have hy_source : y ∈ e.source := hyU.1
    have hey_image : e y ∈ e '' s := hball hyU.2
    rcases hey_image with ⟨z, hz, hzy⟩
    have hyz : y = z := e.injOn hy_source hz.1 hzy.symm
    simpa [hyz] using hz.2
  · simpa [V] using convex_ball (e x) r
  · exact ⟨e x, by simpa [V] using Metric.mem_ball_self (x := e x) hr⟩
  · rfl
  · intro y hyV
    rcases hball hyV with ⟨z, hz, rfl⟩
    exact e.map_source hz.1

/--
%%handwave
name:
  The image of a two-sided chart restriction
statement:
  If an open subset of a chart source is the preimage of an open subset of the
  chart target, then the chart maps the source subset onto the target subset.
proof:
  One inclusion is immediate from the definition of the source subset.  For
  the other, apply the inverse chart to a point of the target subset and use
  the inverse identities for the partial homeomorphism.
-/
theorem deRham_selfModel_chart_restriction_image
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {M0 : Type m} [TopologicalSpace M0]
    (e : OpenPartialHomeomorph M0 E0)
    (U : TopologicalSpace.Opens M0) (V : TopologicalSpace.Opens E0)
    (hU : (U : Set M0) = e.source ∩ e ⁻¹' (V : Set E0))
    (hV : (V : Set E0) ⊆ e.target) :
    e '' (U : Set M0) = (V : Set E0) := by
  ext y
  constructor
  · rintro ⟨x, hxU, rfl⟩
    rw [hU] at hxU
    exact hxU.2
  · intro hyV
    have hyTarget : y ∈ e.target := hV hyV
    refine ⟨e.symm y, ?_, e.right_inv hyTarget⟩
    rw [hU]
    exact ⟨e.map_target hyTarget, by simpa [e.right_inv hyTarget] using hyV⟩

/--
%%handwave
name:
  A two-sided chart restriction is a homeomorphism
statement:
  If an open subset of a chart source is the preimage of an open subset of the
  chart target, then the chart restricts to a homeomorphism between the two
  open subspaces.
proof:
  The source subset lies in the chart source, and the previous image statement
  identifies its image with the target subset.  Restrict the partial
  homeomorphism to this subset.
-/
theorem deRham_selfModel_chart_restriction_homeomorph
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {M0 : Type m} [TopologicalSpace M0]
    (e : OpenPartialHomeomorph M0 E0)
    (U : TopologicalSpace.Opens M0) (V : TopologicalSpace.Opens E0)
    (hU : (U : Set M0) = e.source ∩ e ⁻¹' (V : Set E0))
    (hV : (V : Set E0) ⊆ e.target) :
    Nonempty (U ≃ₜ V) := by
  have hUsource : (U : Set M0) ⊆ e.source := by
    intro x hxU
    rw [hU] at hxU
    exact hxU.1
  have himage :
      e '' (U : Set M0) = (V : Set E0) :=
    deRham_selfModel_chart_restriction_image (e := e) U V hU hV
  exact ⟨e.homeomorphOfImageSubsetSource hUsource himage⟩

/--
%%handwave
name:
  Smoothness of a two-sided restricted chart
statement:
  The homeomorphism obtained by restricting a smooth chart to an open subset
  of its source and to the corresponding open subset of its target is smooth
  in both directions.
proof:
  The forward map is locally the original smooth chart, and the inverse map is
  locally the inverse smooth chart.  Smoothness is local on open submanifolds.
-/
theorem deRham_selfModel_chart_restriction_homeomorph_smooth
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace E0 M0]
    [IsManifold 𝓘(ℝ, E0) ∞ M0]
    (e : OpenPartialHomeomorph M0 E0) (he : e ∈ atlas E0 M0)
    (U : TopologicalSpace.Opens M0) (V : TopologicalSpace.Opens E0)
    (hUsource : (U : Set M0) ⊆ e.source)
    (himage : e '' (U : Set M0) = (V : Set E0)) :
    let φ : U ≃ₜ V := e.homeomorphOfImageSubsetSource hUsource himage
    ContMDiff 𝓘(ℝ, E0) 𝓘(ℝ, E0) ∞ φ ∧
      ContMDiff 𝓘(ℝ, E0) 𝓘(ℝ, E0) ∞ φ.symm := by
  let φ : U ≃ₜ V := e.homeomorphOfImageSubsetSource hUsource himage
  change ContMDiff 𝓘(ℝ, E0) 𝓘(ℝ, E0) ∞ φ ∧
    ContMDiff 𝓘(ℝ, E0) 𝓘(ℝ, E0) ∞ φ.symm
  have heMax : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E0) ∞ M0 :=
    IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, E0)) (n := ∞) he
  have heSmooth : ContMDiffOn 𝓘(ℝ, E0) 𝓘(ℝ, E0) ∞ e e.source :=
    contMDiffOn_of_mem_maximalAtlas heMax
  constructor
  · intro x
    rw [contMDiffAt_iff_target_of_mem_source
      (I := 𝓘(ℝ, E0)) (I' := 𝓘(ℝ, E0)) (y := φ x)]
    constructor
    · exact φ.continuous.continuousAt
    · have hchart : ContMDiffAt 𝓘(ℝ, E0) 𝓘(ℝ, E0) ∞
          (fun z : U => e (z : M0)) x := by
        rw [contMDiffAt_subtype_iff]
        exact heSmooth.contMDiffAt (e.open_source.mem_nhds (hUsource x.2))
      simpa [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
        extChartAt_model_space_eq_id, φ,
        OpenPartialHomeomorph.homeomorphOfImageSubsetSource,
        Function.comp_def] using hchart
    · exact mem_chart_source E0 (φ x)
  · intro y
    have hUne : Nonempty U := ⟨φ.symm y⟩
    let eU : OpenPartialHomeomorph U E0 := e.subtypeRestr hUne
    have heU : eU ∈ IsManifold.maximalAtlas 𝓘(ℝ, E0) ∞ U := by
      dsimp [eU]
      exact StructureGroupoid.subtypeRestr_mem_maximalAtlas
        (G := contDiffGroupoid ∞ 𝓘(ℝ, E0)) he hUne
    have hy_src : y ∈ (chartAt E0 y).source := mem_chart_source E0 y
    have hy_tgt : φ.symm y ∈ eU.source := by
      dsimp [eU]
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact hUsource (φ.symm y).2
    have hsourceMax : chartAt E0 y ∈ IsManifold.maximalAtlas 𝓘(ℝ, E0) ∞ V :=
      IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E0)) (n := ∞) y
    have hsrc_subset : (univ : Set V) ⊆ (chartAt E0 y).source := by
      intro z _
      exact mem_chart_source E0 z
    rw [← contMDiffWithinAt_univ]
    rw [contMDiffWithinAt_iff_image
      (I := 𝓘(ℝ, E0)) (I' := 𝓘(ℝ, E0))
      (e := chartAt E0 y) (e' := eU)
      (f := φ.symm) (s := univ) hsourceMax heU hsrc_subset hy_src hy_tgt]
    constructor
    · exact φ.symm.continuous.continuousWithinAt
    · refine contDiffWithinAt_id.congr_of_mem ?_ ?_
      · intro z hz
        rcases hz with ⟨zV, _hzV, rfl⟩
        have hztarget :
            (chartAt E0 y).extend 𝓘(ℝ, E0) zV ∈ (chartAt E0 y).target := by
          change (chartAt E0 y) zV ∈ (chartAt E0 y).target
          exact (chartAt E0 y).map_source (mem_chart_source E0 zV)
        let w : V := (chartAt E0 y).symm ((chartAt E0 y).extend 𝓘(ℝ, E0) zV)
        have hwcoe : (w : E0) = (chartAt E0 y).extend 𝓘(ℝ, E0) zV :=
          (chartAt E0 y).right_inv hztarget
        have hφcoe : e ((φ.symm w : U) : M0) = (w : E0) := by
          change ((φ (φ.symm w) : V) : E0) = (w : E0)
          exact congrArg (fun q : V => (q : E0)) (φ.apply_symm_apply w)
        change e ((φ.symm w : U) : M0) = (chartAt E0 y).extend 𝓘(ℝ, E0) zV
        exact hφcoe.trans hwcoe
      · simp [TopologicalSpace.Opens.chartAt_eq]

/--
%%handwave
name:
  A restricted smooth chart is a diffeomorphism
statement:
  If an open subset of a smooth boundaryless chart source is exactly the
  preimage of an open subset of the chart target, then the chart restricts to
  a diffeomorphism between the two open submanifolds.
proof:
  Restrict the chart homeomorphism to the prescribed source and target.  The
  smoothness of the two restricted maps follows from smoothness of charts and
  inverse charts.
-/
theorem deRham_selfModel_chart_restriction_diffeomorph
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace E0 M0]
    [IsManifold 𝓘(ℝ, E0) ∞ M0]
    (e : OpenPartialHomeomorph M0 E0) (he : e ∈ atlas E0 M0)
    (U : TopologicalSpace.Opens M0) (V : TopologicalSpace.Opens E0)
    (hU : (U : Set M0) = e.source ∩ e ⁻¹' (V : Set E0))
    (hV : (V : Set E0) ⊆ e.target) :
    Nonempty (U ≃ₘ⟮𝓘(ℝ, E0), 𝓘(ℝ, E0)⟯ V) := by
  have hUsource : (U : Set M0) ⊆ e.source := by
    intro x hxU
    rw [hU] at hxU
    exact hxU.1
  have himage :
      e '' (U : Set M0) = (V : Set E0) :=
    deRham_selfModel_chart_restriction_image (e := e) U V hU hV
  let φ : U ≃ₜ V := e.homeomorphOfImageSubsetSource hUsource himage
  have hsmooth :=
    deRham_selfModel_chart_restriction_homeomorph_smooth
      (e := e) he U V hUsource himage
  refine ⟨{ toEquiv := φ.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }⟩
  · simpa [φ] using hsmooth.1
  · simpa [φ] using hsmooth.2

/--
%%handwave
name:
  Convex coordinate neighborhoods
statement:
  Around every point of a finite-dimensional smooth real manifold modeled on a
  vector space without boundary, there is an open neighborhood diffeomorphic
  to a nonempty convex open subset of the model vector space.
proof:
  Choose a smooth chart and shrink its target to a convex coordinate ball.
  Restricting the chart gives the required diffeomorphism.
-/
theorem deRham_selfModel_chart_convex_neighborhood
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [FiniteDimensional ℝ E0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace E0 M0]
    [IsManifold 𝓘(ℝ, E0) ∞ M0]
    (x : M0) :
    ∃ (U : TopologicalSpace.Opens M0) (V : TopologicalSpace.Opens E0),
      x ∈ U ∧
        Convex ℝ (V : Set E0) ∧
          (V : Set E0).Nonempty ∧
            Nonempty (U ≃ₘ⟮𝓘(ℝ, E0), 𝓘(ℝ, E0)⟯ V) := by
  rcases deRham_selfModel_exists_convex_chart_restriction
      (E0 := E0) (M0 := M0) x with
    ⟨e, U, V, he, hxU, hconvex, hne, hU, hV⟩
  exact
    ⟨U, V, hxU, hconvex, hne,
      deRham_selfModel_chart_restriction_diffeomorph
        (E0 := E0) (M0 := M0) e he U V hU hV⟩

/--
%%handwave
name:
  Local Poincare lemma in boundaryless charts
statement:
  Around every point of a finite-dimensional smooth real manifold modeled on a
  vector space without boundary, there is an open neighborhood on which all
  positive-degree real de Rham cohomology vanishes.
proof:
  Choose [a coordinate neighborhood diffeomorphic to a nonempty convex open subset of the model vector space](lean:JJMath.Manifold.deRham_selfModel_chart_convex_neighborhood).  The convex open set has vanishing positive-degree de Rham cohomology by the Poincare homotopy operator, and the diffeomorphism transports this vanishing back to the manifold neighborhood.
-/
theorem deRham_local_poincareLemma_selfModel
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [FiniteDimensional ℝ E0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace E0 M0]
    [IsManifold 𝓘(ℝ, E0) ∞ M0]
    (x : M0) :
    ∃ U : TopologicalSpace.Opens M0,
      x ∈ U ∧
        ∀ n : ℕ,
          Subsingleton
            (DeRhamCohomology (I := 𝓘(ℝ, E0)) (M := U) (A := ℝ) (n + 1)) := by
  rcases deRham_selfModel_chart_convex_neighborhood
      (E0 := E0) (M0 := M0) x with
    ⟨U, V, hxU, hconvex, hne, hUV⟩
  refine ⟨U, hxU, fun n ↦ ?_⟩
  rcases hUV with ⟨φ⟩
  exact
    deRhamCohomology_subsingleton_of_diffeomorphic
      (𝓘(ℝ, E0)) (𝓘(ℝ, E0)) φ (n + 1)
      (deRham_poincareLemma_convex_open (E := E0) V hconvex hne n)

/--
%%handwave
name:
  Extended charts for boundaryless models
statement:
  If a model with corners has no boundary, then an ordinary chart followed by
  the model embedding is an open partial homeomorphism from the manifold into
  the ambient model vector space.
proof:
  The source is the original chart source.  The target is open because the
  model embedding has full range, and the forward and inverse maps are
  continuous by the standard extended-chart lemmas.
-/
def deRham_boundarylessExtendedChart
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    (e : OpenPartialHomeomorph M H) : OpenPartialHomeomorph M E where
  toPartialEquiv := e.extend Iℝ
  open_source := by
    simpa using (OpenPartialHomeomorph.isOpen_extend_source (f := e) (I := Iℝ))
  open_target := by
    simpa using (OpenPartialHomeomorph.isOpen_extend_target (f := e) (I := Iℝ))
  continuousOn_toFun := by
    simpa using (OpenPartialHomeomorph.continuousOn_extend (f := e) (I := Iℝ))
  continuousOn_invFun := by
    simpa using (OpenPartialHomeomorph.continuousOn_extend_symm (f := e) (I := Iℝ))

/-- The canonical restriction of a boundaryless extended chart to prescribed
open source and target sets. -/
noncomputable def deRham_boundarylessExtendedChart_restrictionDiffeomorph
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M]
    (e : OpenPartialHomeomorph M H) (he : e ∈ atlas H M)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens E)
    (hU :
      (U : Set M) =
        (deRham_boundarylessExtendedChart (M := M) Iℝ e).source ∩
          deRham_boundarylessExtendedChart (M := M) Iℝ e ⁻¹' (V : Set E))
    (hV :
      (V : Set E) ⊆
        (deRham_boundarylessExtendedChart (M := M) Iℝ e).target) :
    U ≃ₘ⟮Iℝ, 𝓘(ℝ, E)⟯ V := by
  let eI : OpenPartialHomeomorph M E :=
    deRham_boundarylessExtendedChart (M := M) Iℝ e
  have hUsource : (U : Set M) ⊆ eI.source := by
    intro x hxU
    rw [hU] at hxU
    exact hxU.1
  have himage : eI '' (U : Set M) = (V : Set E) :=
    deRham_selfModel_chart_restriction_image (E0 := E) (M0 := M)
      eI U V hU hV
  let φ : U ≃ₜ V := eI.homeomorphOfImageSubsetSource hUsource himage
  have heMax : e ∈ IsManifold.maximalAtlas Iℝ ∞ M :=
    IsManifold.subset_maximalAtlas (I := Iℝ) (n := ∞) he
  have heSmooth : ContMDiffOn Iℝ 𝓘(ℝ, E) ∞ (e.extend Iℝ) e.source :=
    contMDiffOn_extend heMax
  refine { toEquiv := φ.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    rw [contMDiffAt_iff_target_of_mem_source
      (I := Iℝ) (I' := 𝓘(ℝ, E)) (y := φ x)]
    constructor
    · exact φ.continuous.continuousAt
    · have hx_source : (x : M) ∈ e.source := by
        have hx : (x : M) ∈ eI.source := hUsource x.2
        dsimp [eI, deRham_boundarylessExtendedChart] at hx
        exact hx.1
      have hchart : ContMDiffAt Iℝ 𝓘(ℝ, E) ∞
          (fun z : U => e.extend Iℝ (z : M)) x := by
        rw [contMDiffAt_subtype_iff]
        exact heSmooth.contMDiffAt (e.open_source.mem_nhds hx_source)
      simpa [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
        extChartAt_model_space_eq_id, φ, eI,
        deRham_boundarylessExtendedChart,
        OpenPartialHomeomorph.homeomorphOfImageSubsetSource,
        Function.comp_def] using hchart
    · exact mem_chart_source E (φ x)
  · intro y
    have hUne : Nonempty U := ⟨φ.symm y⟩
    let eU : OpenPartialHomeomorph U H := e.subtypeRestr hUne
    have heU : eU ∈ IsManifold.maximalAtlas Iℝ ∞ U := by
      dsimp [eU]
      exact StructureGroupoid.subtypeRestr_mem_maximalAtlas
        (G := contDiffGroupoid ∞ Iℝ) he hUne
    have hy_src : y ∈ (chartAt E y).source := mem_chart_source E y
    have hy_tgt : φ.symm y ∈ eU.source := by
      have hy_eI : (((φ.symm y : U) : M)) ∈ eI.source :=
        hUsource (φ.symm y).2
      have hy_e : (((φ.symm y : U) : M)) ∈ e.source := by
        dsimp [eI, deRham_boundarylessExtendedChart] at hy_eI
        exact hy_eI.1
      dsimp [eU]
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact hy_e
    have hsourceMax :
        chartAt E y ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ V :=
      IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) y
    have hsrc_subset : (univ : Set V) ⊆ (chartAt E y).source := by
      intro z _
      exact mem_chart_source E z
    rw [← contMDiffWithinAt_univ]
    refine (contMDiffWithinAt_iff_image
      (I := 𝓘(ℝ, E)) (I' := Iℝ)
      (e := chartAt E y) (e' := eU)
      (f := φ.symm) (s := univ) hsourceMax heU hsrc_subset hy_src hy_tgt).2 ?_
    constructor
    · exact φ.symm.continuous.continuousWithinAt
    · refine contDiffWithinAt_id.congr_of_mem ?_ ?_
      · intro z hz
        rcases hz with ⟨zV, _hzV, rfl⟩
        have hztarget :
            (chartAt E y).extend 𝓘(ℝ, E) zV ∈ (chartAt E y).target := by
          change (chartAt E y) zV ∈ (chartAt E y).target
          exact (chartAt E y).map_source (mem_chart_source E zV)
        let w : V := (chartAt E y).symm ((chartAt E y).extend 𝓘(ℝ, E) zV)
        have hwcoe : (w : E) = (chartAt E y).extend 𝓘(ℝ, E) zV :=
          (chartAt E y).right_inv hztarget
        have hφcoe : eI (((φ.symm w : U) : M)) = (w : E) := by
          change ((φ (φ.symm w) : V) : E) = (w : E)
          exact congrArg (fun q : V => (q : E)) (φ.apply_symm_apply w)
        change eI (((φ.symm w : U) : M)) =
          (chartAt E y).extend 𝓘(ℝ, E) zV
        exact hφcoe.trans hwcoe
      · simp [TopologicalSpace.Opens.chartAt_eq]

@[simp]
theorem deRham_boundarylessExtendedChart_restrictionDiffeomorph_coe_apply
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M]
    (e : OpenPartialHomeomorph M H) (he : e ∈ atlas H M)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens E)
    (hU :
      (U : Set M) =
        (deRham_boundarylessExtendedChart (M := M) Iℝ e).source ∩
          deRham_boundarylessExtendedChart (M := M) Iℝ e ⁻¹' (V : Set E))
    (hV :
      (V : Set E) ⊆
        (deRham_boundarylessExtendedChart (M := M) Iℝ e).target)
    (x : U) :
    ((deRham_boundarylessExtendedChart_restrictionDiffeomorph
      Iℝ e he U V hU hV x : V) : E) =
      deRham_boundarylessExtendedChart (M := M) Iℝ e (x : M) := by
  rfl

/--
%%handwave
name:
  Restricted boundaryless extended charts are diffeomorphisms
statement:
  Let \(U\) be the preimage, inside a chart source, of an open subset \(V\) of
  the target of a boundaryless extended chart.  Then the extended chart
  restricts to a diffeomorphism from \(U\) to \(V\).
proof:
  The restricted extended chart is a homeomorphism by the inverse identities
  for partial homeomorphisms.  Its forward smoothness is the smoothness of
  extended charts, and its inverse smoothness is the smoothness of inverse
  extended charts.
tags:
  milestone
-/
theorem deRham_boundarylessExtendedChart_restriction_diffeomorph
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M]
    (e : OpenPartialHomeomorph M H) (he : e ∈ atlas H M)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens E)
    (hU :
      (U : Set M) =
        (deRham_boundarylessExtendedChart (M := M) Iℝ e).source ∩
          deRham_boundarylessExtendedChart (M := M) Iℝ e ⁻¹' (V : Set E))
    (hV :
      (V : Set E) ⊆
        (deRham_boundarylessExtendedChart (M := M) Iℝ e).target) :
    Nonempty (U ≃ₘ⟮Iℝ, 𝓘(ℝ, E)⟯ V) := by
  exact ⟨deRham_boundarylessExtendedChart_restrictionDiffeomorph
    Iℝ e he U V hU hV⟩

/--
%%handwave
name:
  Convex subtargets of boundaryless extended charts
statement:
  Around every point of a finite-dimensional smooth manifold modeled by a
  boundaryless real model, one can choose an extended chart and shrink
  its target to a nonempty convex open set still lying in the extended-chart
  target.
proof:
  Since the extended-chart target is open in the normed model vector space,
  choose a sufficiently small open ball around the coordinate of the point.
  Open balls in a normed vector space are convex.
-/
theorem deRham_boundarylessModel_exists_convex_extendedChart_restriction
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    (x : M) :
    ∃ (e : OpenPartialHomeomorph M H)
      (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens E),
      e ∈ atlas H M ∧
        x ∈ U ∧
          Convex ℝ (V : Set E) ∧
            (V : Set E).Nonempty ∧
              (U : Set M) =
                (deRham_boundarylessExtendedChart (M := M) Iℝ e).source ∩
                  deRham_boundarylessExtendedChart (M := M) Iℝ e ⁻¹' (V : Set E) ∧
                (V : Set E) ⊆
                  (deRham_boundarylessExtendedChart (M := M) Iℝ e).target := by
  let e : OpenPartialHomeomorph M H := chartAt H x
  let eI : OpenPartialHomeomorph M E :=
    deRham_boundarylessExtendedChart (M := M) Iℝ e
  have hx_source : x ∈ eI.source := by
    dsimp [eI, deRham_boundarylessExtendedChart]
    exact ⟨mem_chart_source H x, by simp [ModelWithCorners.source_eq]⟩
  have hx_target : eI x ∈ eI.target := eI.map_source hx_source
  rcases Metric.isOpen_iff.1 eI.open_target (eI x) hx_target with
    ⟨r, hr, hball⟩
  let V : TopologicalSpace.Opens E :=
    ⟨Metric.ball (eI x) r, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens M :=
    ⟨eI.source ∩ eI ⁻¹' (V : Set E), eI.isOpen_inter_preimage V.2⟩
  refine ⟨e, U, V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chart_mem_atlas H x
  · exact ⟨hx_source, by simpa [V] using Metric.mem_ball_self (x := eI x) hr⟩
  · simpa [V] using convex_ball (eI x) r
  · exact ⟨eI x, by simpa [V] using Metric.mem_ball_self (x := eI x) hr⟩
  · rfl
  · simpa [V] using hball

/--
%%handwave
name:
  Subordinate convex subtargets of boundaryless extended charts
statement:
  Around every point of an open set in a finite-dimensional smooth manifold
  modeled by a boundaryless real model, one can choose an extended chart and
  shrink its ambient target to a nonempty convex open set whose source
  restriction is contained in the given open set.
proof:
  Intersect the source of an extended chart with the prescribed open set and
  take its image in the ambient model vector space.  This image is open and
  contains the coordinate of the point, hence contains a small convex ball.
  The inverse image of that ball inside the extended-chart source is
  contained in the prescribed open set by injectivity of the extended chart on
  its source.
-/
theorem deRham_boundarylessModel_exists_convex_extendedChart_restriction_subordinate
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    (x : M) (W : TopologicalSpace.Opens M) (hxW : x ∈ W) :
    ∃ (e : OpenPartialHomeomorph M H)
      (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens E),
      e ∈ atlas H M ∧
        x ∈ U ∧
          U ≤ W ∧
            Convex ℝ (V : Set E) ∧
              (V : Set E).Nonempty ∧
                (U : Set M) =
                  (deRham_boundarylessExtendedChart (M := M) Iℝ e).source ∩
                    deRham_boundarylessExtendedChart (M := M) Iℝ e ⁻¹' (V : Set E) ∧
                  (V : Set E) ⊆
                    (deRham_boundarylessExtendedChart (M := M) Iℝ e).target := by
  let e : OpenPartialHomeomorph M H := chartAt H x
  let eI : OpenPartialHomeomorph M E :=
    deRham_boundarylessExtendedChart (M := M) Iℝ e
  have hx_source : x ∈ eI.source := by
    dsimp [eI, deRham_boundarylessExtendedChart]
    exact ⟨mem_chart_source H x, by simp [ModelWithCorners.source_eq]⟩
  let s : Set M := eI.source ∩ (W : Set M)
  have hs_open : IsOpen s := eI.open_source.inter W.2
  have hs_subset : s ⊆ eI.source := inter_subset_left
  have hs_image_open : IsOpen (eI '' s) :=
    eI.isOpen_image_of_subset_source hs_open hs_subset
  have hx_image : eI x ∈ eI '' s := ⟨x, ⟨hx_source, hxW⟩, rfl⟩
  rcases Metric.isOpen_iff.1 hs_image_open (eI x) hx_image with
    ⟨r, hr, hball⟩
  let V : TopologicalSpace.Opens E :=
    ⟨Metric.ball (eI x) r, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens M :=
    ⟨eI.source ∩ eI ⁻¹' (V : Set E), eI.isOpen_inter_preimage V.2⟩
  refine ⟨e, U, V, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chart_mem_atlas H x
  · exact ⟨hx_source, by simpa [V] using Metric.mem_ball_self (x := eI x) hr⟩
  · intro y hyU
    have hy_source : y ∈ eI.source := hyU.1
    have hey_image : eI y ∈ eI '' s := hball hyU.2
    rcases hey_image with ⟨z, hz, hzy⟩
    have hyz : y = z := eI.injOn hy_source hz.1 hzy.symm
    simpa [hyz] using hz.2
  · simpa [V] using convex_ball (eI x) r
  · exact ⟨eI x, by simpa [V] using Metric.mem_ball_self (x := eI x) hr⟩
  · rfl
  · intro y hyV
    rcases hball hyV with ⟨z, hz, rfl⟩
    exact eI.map_source hz.1

/--
%%handwave
name:
  Convex coordinate neighborhoods for boundaryless models
statement:
  Around every point of a finite-dimensional smooth manifold modeled by a
  boundaryless real model, there is an open neighborhood
  diffeomorphic to a nonempty convex open subset of the ambient model vector
  space.
proof:
  Choose a boundaryless extended chart and shrink its target to a convex
  coordinate ball.  Restricting the extended chart gives the required
  diffeomorphism.
-/
theorem deRham_boundarylessModel_chart_convex_neighborhood
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    (x : M) :
    ∃ (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens E),
      x ∈ U ∧
        Convex ℝ (V : Set E) ∧
          (V : Set E).Nonempty ∧
            Nonempty (U ≃ₘ⟮Iℝ, 𝓘(ℝ, E)⟯ V) := by
  rcases deRham_boundarylessModel_exists_convex_extendedChart_restriction
      (M := M) Iℝ x with
    ⟨e, U, V, he, hxU, hconvex, hne, hU, hV⟩
  exact
    ⟨U, V, hxU, hconvex, hne,
      deRham_boundarylessExtendedChart_restriction_diffeomorph
        (M := M) Iℝ e he U V hU hV⟩

/--
%%handwave
name:
  Local Poincare lemma for boundaryless models
statement:
  Around every point of a finite-dimensional smooth real manifold modeled by a
  boundaryless real model, there is an open neighborhood on which all
  positive-degree real de Rham cohomology vanishes.
proof:
  Choose [a coordinate neighborhood diffeomorphic to a nonempty convex open subset of the ambient model vector space](lean:JJMath.Manifold.deRham_boundarylessModel_chart_convex_neighborhood).  The convex open set has vanishing positive-degree de Rham cohomology by the Poincare homotopy operator, and the diffeomorphism transports this vanishing back to the manifold neighborhood.
-/
theorem deRham_local_poincareLemma_boundarylessModel
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    (x : M) :
    ∃ U : TopologicalSpace.Opens M,
      x ∈ U ∧
        ∀ n : ℕ,
          Subsingleton
            (DeRhamCohomology (I := Iℝ) (M := U) (A := ℝ) (n + 1)) := by
  rcases deRham_boundarylessModel_chart_convex_neighborhood
      (M := M) Iℝ x with
    ⟨U, V, hxU, hconvex, hne, hUV⟩
  refine ⟨U, hxU, fun n ↦ ?_⟩
  rcases hUV with ⟨φ⟩
  exact
    deRhamCohomology_subsingleton_of_diffeomorphic
      Iℝ (𝓘(ℝ, E)) φ (n + 1)
      (deRham_poincareLemma_convex_open (E := E) V hconvex hne n)

/--
%%handwave
name:
  Local Poincare neighborhoods form a basis
statement:
  A smooth real manifold has a local Poincare basis if, inside every open
  neighborhood of every point, there is a smaller open neighborhood whose
  positive-degree real de Rham cohomology vanishes.
proof:
  This is the explicit local hypothesis needed for sheaf-level exactness:
  germs may be represented on arbitrary open neighborhoods, so the Poincare
  neighborhood must be chosen after that representative has been fixed.
-/
def DeRhamLocalPoincareBasis [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] : Prop :=
  ∀ x : M, ∀ W : TopologicalSpace.Opens M, x ∈ W →
    ∃ U : TopologicalSpace.Opens M,
      x ∈ U ∧ U ≤ W ∧
        ∀ n : ℕ,
          Subsingleton
            (DeRhamCohomology (I := Iℝ) (M := U) (A := ℝ) (n + 1))

/--
%%handwave
name:
  Boundaryless vector-space models have a local Poincare basis
statement:
  On a finite-dimensional smooth real manifold modeled on a real vector space,
  every point has arbitrarily small open neighborhoods with vanishing
  positive-degree real de Rham cohomology.
proof:
  Given an open neighborhood, choose a smooth chart at the point and shrink
  the chart target to a convex open ball whose preimage is contained in the
  prescribed neighborhood.  The convex Poincare lemma kills positive-degree
  de Rham cohomology on that ball, and the restricted chart transports the
  vanishing to the manifold neighborhood.
-/
theorem deRham_local_poincareBasis_selfModel
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [FiniteDimensional ℝ E0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace E0 M0]
    [IsManifold 𝓘(ℝ, E0) ∞ M0] :
    DeRhamLocalPoincareBasis (M := M0) (𝓘(ℝ, E0)) := by
  intro x W hxW
  rcases deRham_selfModel_exists_convex_chart_restriction_subordinate
      (E0 := E0) (M0 := M0) x W hxW with
    ⟨e, U, V, he, hxU, hUW, hconvex, hne, hU, hV⟩
  refine ⟨U, hxU, hUW, fun n ↦ ?_⟩
  rcases
    deRham_selfModel_chart_restriction_diffeomorph
      (E0 := E0) (M0 := M0) e he U V hU hV with
    ⟨φ⟩
  exact
    deRhamCohomology_subsingleton_of_diffeomorphic
      (𝓘(ℝ, E0)) (𝓘(ℝ, E0)) φ (n + 1)
      (deRham_poincareLemma_convex_open (E := E0) V hconvex hne n)

/--
%%handwave
name:
  Boundaryless models have a local Poincare basis
statement:
  On a finite-dimensional smooth real manifold modeled by a boundaryless real
  model, every point has arbitrarily small open neighborhoods with vanishing
  positive-degree real de Rham cohomology.
proof:
  Given an open neighborhood, use a boundaryless extended chart and shrink its
  image to a convex open subset contained in the prescribed neighborhood.
  The convex Poincare lemma gives vanishing on the model open set, and the
  restricted extended chart transports it back to the manifold.
tags:
  milestone
-/
theorem deRham_local_poincareBasis_boundarylessModel
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] :
    DeRhamLocalPoincareBasis (M := M) Iℝ := by
  intro x W hxW
  rcases deRham_boundarylessModel_exists_convex_extendedChart_restriction_subordinate
      (M := M) Iℝ x W hxW with
    ⟨e, U, V, he, hxU, hUW, hconvex, hne, hU, hV⟩
  refine ⟨U, hxU, hUW, fun n ↦ ?_⟩
  rcases
    deRham_boundarylessExtendedChart_restriction_diffeomorph
      (M := M) Iℝ e he U V hU hV with
    ⟨φ⟩
  exact
    deRhamCohomology_subsingleton_of_diffeomorphic
      Iℝ (𝓘(ℝ, E)) φ (n + 1)
      (deRham_poincareLemma_convex_open (E := E) V hconvex hne n)

/--
%%handwave
name:
  A local Poincare basis gives local primitives
statement:
  If a smooth real manifold has a local Poincare basis, then any closed
  positive-degree form on an open set becomes exact after restricting to a
  smaller neighborhood of any chosen point.
proof:
  Choose, inside the given open set, a smaller Poincare neighborhood.  The
  restricted form is still closed because exterior differentiation commutes
  with restriction.  Vanishing of the positive-degree de Rham cohomology of
  the smaller neighborhood makes that closed form exact.
tags:
  milestone
-/
theorem DeRhamLocalPoincareBasis.exists_primitive_on_smaller_open
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (hlocal : DeRhamLocalPoincareBasis (M := M) Iℝ)
    (x : M) (W : TopologicalSpace.Opens M) (hxW : x ∈ W)
    (n : ℕ) (omega : SmoothForms (I := Iℝ) (M := W) ℝ (n + 1))
    (hclosed :
      deRhamDifferential (I := Iℝ) (M := W) (A := ℝ) (n + 1) omega = 0) :
    ∃ U : TopologicalSpace.Opens M,
      ∃ hUW : U ≤ W,
      x ∈ U ∧
        ∃ theta : SmoothForms (I := Iℝ) (M := U) ℝ n,
          deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n theta =
            restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
              (V := W) (W := U) hUW (n + 1) omega := by
  rcases hlocal x W hxW with ⟨U, hxU, hUW, hvanish⟩
  let omegaU : SmoothForms (I := Iℝ) (M := U) ℝ (n + 1) :=
    restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
      (V := W) (W := U) hUW (n + 1) omega
  have hclosedU :
      deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) (n + 1) omegaU = 0 := by
    have hnat :=
      deRhamDifferential_restrictSmoothFormsOfLE
        (I := Iℝ) (A := ℝ) hUW omega
    change
      deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) (n + 1) omegaU =
        0
    calc
      deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) (n + 1) omegaU =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := W) (W := U) hUW (n + 2)
            (deRhamDifferential (I := Iℝ) (M := W) (A := ℝ) (n + 1) omega) := by
            simpa [omegaU] using hnat
      _ = 0 := by
            rw [hclosed]
            apply DifferentialForm.ext
            intro y
            ext v
            rfl
  let omegaClosed : DeRhamClosedForms (I := Iℝ) (M := U) (A := ℝ) (n + 1) :=
    ⟨omegaU, hclosedU⟩
  haveI :
      Subsingleton
        (DeRhamCohomology (I := Iℝ) (M := U) (A := ℝ) (n + 1)) :=
    hvanish n
  rcases
    deRhamClosedSuccForm_has_primitive_of_cohomology_subsingleton
      (I := Iℝ) (M := U) (A := ℝ) (n := n) omegaClosed with
    ⟨theta, htheta⟩
  refine ⟨U, hUW, hxU, theta, ?_⟩
  simpa [omegaU] using htheta

/--
%%handwave
name:
  Sigma-compact Hausdorff finite-dimensional manifolds are paracompact
statement:
  A finite-dimensional Hausdorff sigma-compact smooth real manifold is
  paracompact.
proof:
  Finite-dimensional model spaces over \(\mathbb R\) are locally compact, and
  local compactness transfers to manifolds through charts.  A locally compact
  sigma-compact Hausdorff space is paracompact.
-/
theorem smoothManifold_paracompactSpace_of_t2_sigmaCompact
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] :
    ParacompactSpace M := by
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional Iℝ
  infer_instance

/--
%%handwave
name:
  Convex subspaces are strongly locally contractible
statement:
  A convex subset of a real normed vector space has a basis of contractible
  neighborhoods at every point.
proof:
  Relative metric balls form a neighborhood basis.  A relative ball is
  homeomorphic to the intersection of the convex set with an ambient ball,
  which is convex and nonempty, hence contractible by straight-line
  homotopy.
-/
theorem convexSubset_stronglyLocallyContractibleSpace
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {s : Set E0} (hs : Convex ℝ s) :
    StronglyLocallyContractibleSpace s := by
  refine StronglyLocallyContractibleSpace.of_bases
    (p := fun (_ : s) (r : ℝ) => 0 < r)
    (s := fun x r => Metric.ball x r) ?_ ?_
  · intro x
    exact Metric.nhds_basis_ball
  · intro x r hr
    let t : Set E0 := s ∩ Metric.ball (x : E0) r
    have ht_convex : Convex ℝ t := hs.inter (convex_ball _ _)
    have ht_nonempty : t.Nonempty :=
      ⟨x, x.2, Metric.mem_ball_self hr⟩
    have ht_contractible : ContractibleSpace t :=
      ht_convex.contractibleSpace ht_nonempty
    let e0 : Metric.ball x r ≃ₜ ((fun y : s => (y : E0)) '' Metric.ball x r) :=
      IsEmbedding.subtypeVal.homeomorphImage (Metric.ball x r)
    have himage :
        ((fun y : s => (y : E0)) '' Metric.ball x r) = t := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, by simpa [Metric.mem_ball, Subtype.dist_eq] using hz⟩
      · rintro ⟨hys, hyball⟩
        refine ⟨⟨y, hys⟩, ?_, rfl⟩
        simpa [Metric.mem_ball, Subtype.dist_eq] using hyball
    let e : Metric.ball x r ≃ₜ t := e0.trans (Homeomorph.setCongr himage)
    exact e.contractibleSpace_iff.mpr ht_contractible

/--
%%handwave
name:
  A model with corners is homeomorphic to its range
statement:
  The coordinate map of a model with corners identifies the model space with
  its range in the ambient normed vector space.
proof:
  The model map is a partial equivalence whose source is the whole model
  space and whose target is exactly its range.  Its forward and inverse maps
  are continuous by the definition of a model with corners.
-/
noncomputable def modelWithCornersRangeHomeomorph
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) :
    H ≃ₜ range (Iℝ : H → E) where
  toFun x := ⟨Iℝ x, ⟨x, rfl⟩⟩
  invFun y := Iℝ.symm y
  left_inv x := by
    exact Iℝ.left_inv (by trivial)
  right_inv y := by
    rcases y with ⟨y, hy⟩
    apply Subtype.ext
    exact Iℝ.right_inv (by simpa [ModelWithCorners.target_eq] using hy)
  continuous_toFun := by
    exact Continuous.subtype_mk Iℝ.continuous_toFun _
  continuous_invFun := by
    exact Iℝ.continuous_invFun.comp continuous_subtype_val

/--
%%handwave
name:
  Model spaces with corners are strongly locally contractible
statement:
  The model space of a finite-dimensional real model with corners has a basis
  of contractible neighborhoods at every point.
proof:
  The model space is homeomorphic to the range of the model map.  This range
  is convex in the ambient real normed vector space, and convex subspaces are
  strongly locally contractible.
-/
theorem modelWithCorners_stronglyLocallyContractibleSpace
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) :
    StronglyLocallyContractibleSpace H := by
  let e : H ≃ₜ range (Iℝ : H → E) := modelWithCornersRangeHomeomorph Iℝ
  have hconv : Convex ℝ (range (Iℝ : H → E)) := Iℝ.convex_range
  haveI : StronglyLocallyContractibleSpace (range (Iℝ : H → E)) :=
    convexSubset_stronglyLocallyContractibleSpace hconv
  exact e.isOpenEmbedding.stronglyLocallyContractibleSpace

/--
%%handwave
name:
  Strong local contractibility is local on open covers
statement:
  If every point of a topological space lies in an open subspace which has a
  basis of contractible neighborhoods, then the whole space has a basis of
  contractible neighborhoods.
proof:
  Given a neighborhood of a point, restrict it to a contractible neighborhood
  inside the chosen open subspace.  The inclusion of the open subspace is an
  open embedding, so the image is again a neighborhood in the ambient space,
  and it is homeomorphic to the chosen contractible neighborhood.
-/
theorem stronglyLocallyContractibleSpace_of_open_cover
    {X : Type v} [TopologicalSpace X]
    (U : X → Set X)
    (hUopen : ∀ x, IsOpen (U x))
    (hxU : ∀ x, x ∈ U x)
    (hUlc : ∀ x, StronglyLocallyContractibleSpace (U x)) :
    StronglyLocallyContractibleSpace X := by
  refine ⟨fun x => ?_⟩
  rw [hasBasis_self]
  intro t ht
  let Ux : Set X := U x
  let xU : Ux := ⟨x, hxU x⟩
  haveI : StronglyLocallyContractibleSpace Ux := hUlc x
  have htU : ((fun y : Ux => (y : X)) ⁻¹' t) ∈ 𝓝 xU :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds ht
  rcases (contractible_basis xU).mem_iff.mp htU with ⟨s, hs, hs_subset⟩
  refine ⟨(fun y : Ux => (y : X)) '' s, ?_, ?_, ?_⟩
  · exact (hUopen x).isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hs.1
  · let e : s ≃ₜ ((fun y : Ux => (y : X)) '' s) :=
      IsEmbedding.subtypeVal.homeomorphImage s
    exact e.contractibleSpace_iff.mp hs.2
  · rintro y ⟨z, hz, rfl⟩
    exact hs_subset hz

/--
%%handwave
name:
  Strong local contractibility transfers through charts
statement:
  A charted space modeled on a strongly locally contractible space is strongly
  locally contractible.
proof:
  At a point, restrict to a chart source.  The chart source is open and
  homeomorphic to an open subset of the model space, hence has a basis of
  contractible neighborhoods.  Transport those neighborhoods back through the
  chart and view them as neighborhoods in the ambient space.
tags:
  milestone
-/
theorem chartedSpace_stronglyLocallyContractibleSpace_of_model
    [StronglyLocallyContractibleSpace H] :
    StronglyLocallyContractibleSpace M := by
  refine stronglyLocallyContractibleSpace_of_open_cover
    (fun x : M => (chartAt H x).source)
    (fun x => (chartAt H x).open_source)
    (fun x => mem_chart_source H x) ?_
  intro x
  let e : OpenPartialHomeomorph M H := chartAt H x
  haveI : StronglyLocallyContractibleSpace e.target :=
    e.open_target.stronglyLocallyContractibleSpace
  exact e.toHomeomorphSourceTarget.isOpenEmbedding.stronglyLocallyContractibleSpace

/--
%%handwave
name:
  Finite-dimensional manifolds are locally contractible
statement:
  A finite-dimensional smooth real manifold, possibly with boundary or
  corners, is locally contractible.
proof:
  In a chart, choose a sufficiently small convex neighborhood in the model
  with corners.  Straight-line contraction in the ambient finite-dimensional
  vector space stays inside the convex neighborhood and gives the required
  null-homotopy after transporting back through the chart.
tags:
  milestone
-/
theorem smoothManifold_locallyContractibleSpace
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] :
    LocallyContractibleSpace M := by
  letI : StronglyLocallyContractibleSpace H :=
    modelWithCorners_stronglyLocallyContractibleSpace Iℝ
  letI : StronglyLocallyContractibleSpace M :=
    chartedSpace_stronglyLocallyContractibleSpace_of_model (H := H) (M := M)
  exact StronglyLocallyContractibleSpace.locallyContractible

/--
%%handwave
name:
  Restricting forms along the identity inclusion is the identity
statement:
  Restricting a smooth real-valued differential form on an open subset to the
  same open subset gives back the original form.
proof:
  The inclusion map is the identity, so its manifold derivative is the identity
  on tangent spaces.  The pullback formula for restriction therefore leaves
  each alternating form unchanged pointwise.
-/
theorem restrictSmoothFormsOfLE_id [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (U : TopologicalSpace.Opens M) (n : ℕ)
    [IsManifold Iℝ ∞ M]
    (omega : SmoothForms (I := Iℝ) (M := U) ℝ n) :
    restrictSmoothFormsOfLE (I := Iℝ) (A := ℝ) (le_refl U) n omega = omega := by
  apply DifferentialForm.ext
  intro x
  ext v
  change
    (omega.toFun (TopologicalSpace.Opens.inclusion (le_refl U) x)).compContinuousLinearMap
        (mfderiv Iℝ Iℝ (TopologicalSpace.Opens.inclusion (le_refl U)) x) v =
      omega.toFun x v
  have hinc : TopologicalSpace.Opens.inclusion (le_refl U) = (id : U → U) := by
    funext x
    rfl
  rw [hinc]
  simp only [mfderiv_id, ContinuousAlternatingMap.compContinuousLinearMap_apply, id_eq]
  congr 1

/--
%%handwave
name:
  The presheaf of smooth differential forms
statement:
  For each degree \(n\), assigning to an open set \(U\) the real vector space
  of smooth real-valued \(n\)-forms on \(U\), and to an inclusion \(V\subseteq U\)
  the restriction map from \(U\) to \(V\), defines a presheaf of real vector
  spaces.
proof:
  The functor laws are exactly the identity and composition laws for restriction
  of smooth forms along open inclusions.
-/
noncomputable def smoothFormsPresheaf [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    TopCat.Presheaf (ModuleCat.{max v m} ℝ) (TopCat.of M : TopCat.{m}) where
  obj U := ModuleCat.of ℝ (SmoothForms (I := Iℝ) (M := U.unop) ℝ n)
  map {U V} f :=
    ModuleCat.ofHom
      (restrictSmoothFormsOfLE (I := Iℝ) (A := ℝ)
        (M := M) (V := U.unop) (W := V.unop)
        (CategoryTheory.leOfHom f.unop) n)
  map_id U := by
    ext omega x v
    have h :=
      restrictSmoothFormsOfLE_id (M := M) Iℝ U.unop n omega
    have hx :=
      congrArg
        (fun eta : SmoothForms (I := Iℝ) (M := U.unop) ℝ n => eta.toFun x) h
    simpa using congrArg (fun phi => phi v) hx
  map_comp {U V W} f g := by
    ext omega x v
    have h :=
      restrictSmoothFormsOfLE_comp (I := Iℝ) (M := M)
        (U := U.unop) (V := V.unop) (W := W.unop)
        (CategoryTheory.leOfHom f.unop) (CategoryTheory.leOfHom g.unop) n omega
    have hx :=
      congrArg
        (fun eta : SmoothForms (I := Iℝ) (M := W.unop) ℝ n => eta.toFun x) h.symm
    simpa using congrArg (fun phi => phi v) hx

/--
%%handwave
name:
  The form presheaf restricts by the usual open-inclusion map
statement:
  The restriction map of the presheaf of smooth \(n\)-forms associated to an
  inclusion \(V\subseteq U\) is the usual restriction of forms from \(U\) to
  \(V\).
proof:
  This is the definition of the presheaf map.
-/
@[simp]
theorem smoothFormsPresheaf_map_homOfLE [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) {U V : TopologicalSpace.Opens M}
    [IsManifold Iℝ ∞ M] (hVU : V ≤ U) (n : ℕ) :
    (smoothFormsPresheaf (M := M) Iℝ n).map
        (CategoryTheory.homOfLE hVU).op =
      ModuleCat.ofHom
        (restrictSmoothFormsOfLE (I := Iℝ) (A := ℝ) (M := M) hVU n) := by
  rfl

/--
%%handwave
name:
  Exterior differentiation is natural for the form presheaves
statement:
  For every inclusion of open subsets \(V\subseteq U\), exterior
  differentiation after restricting a smooth form from \(U\) to \(V\) is the
  same as restricting its exterior derivative from \(U\) to \(V\).
proof:
  This is the compatibility of the exterior derivative with restriction along
  open inclusions, expressed as a naturality square between the presheaves of
  \(n\)-forms and \((n+1)\)-forms.
-/
theorem deRhamDifferential_smoothFormsPresheaf_naturality [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) {U V : TopologicalSpace.Opens M}
    [IsManifold Iℝ ∞ M] (hVU : V ≤ U) {n : ℕ}
    (omega : SmoothForms (I := Iℝ) (M := U) ℝ n) :
    deRhamDifferential (I := Iℝ) (M := V) (A := ℝ) n
        ((smoothFormsPresheaf (M := M) Iℝ n).map
          (CategoryTheory.homOfLE hVU).op omega) =
      (smoothFormsPresheaf (M := M) Iℝ (n + 1)).map
        (CategoryTheory.homOfLE hVU).op
        (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n omega) := by
  simpa [smoothFormsPresheaf] using
    deRhamDifferential_restrictSmoothFormsOfLE (I := Iℝ) (A := ℝ) hVU omega

/--
%%handwave
name:
  Exterior differentiation as a morphism of form presheaves
statement:
  For every \(n\), exterior differentiation defines a morphism from the
  presheaf of smooth \(n\)-forms to the presheaf of smooth \((n+1)\)-forms.
proof:
  On each open set the component is the usual exterior derivative.  Naturality
  is compatibility of exterior differentiation with restriction to smaller
  open sets.
-/
noncomputable def deRhamDifferentialPresheafNatTrans [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    smoothFormsPresheaf (M := M) Iℝ n ⟶
      smoothFormsPresheaf (M := M) Iℝ (n + 1) where
  app U :=
    ModuleCat.ofHom
      (deRhamDifferential (I := Iℝ) (M := U.unop) (A := ℝ) n)
  naturality {U V} f := by
    ext omega
    apply DifferentialForm.ext
    intro x
    ext v
    have h :=
      deRhamDifferential_smoothFormsPresheaf_naturality (M := M) Iℝ
        (CategoryTheory.leOfHom f.unop) (n := n) omega
    simpa [smoothFormsPresheaf] using congrArg (fun eta => eta.toFun x v) h

/--
%%handwave
name:
  Exterior differentiation squares to zero on form presheaves
statement:
  The composite of two successive exterior-differentiation morphisms between
  presheaves of smooth forms is zero.
proof:
  This is checked on every open set, where it is the usual identity \(d^2=0\)
  for smooth differential forms.
-/
theorem deRhamDifferentialPresheafNatTrans_comp_eq_zero [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    deRhamDifferentialPresheafNatTrans (M := M) Iℝ n ≫
        deRhamDifferentialPresheafNatTrans (M := M) Iℝ (n + 1) =
      0 := by
  ext U omega
  apply DifferentialForm.ext
  intro x
  ext v
  simpa [deRhamDifferentialPresheafNatTrans] using
    congrArg (fun eta => eta.toFun x v)
      (deRhamDifferential_comp_eq_zero
        (I := Iℝ) (M := U) (A := ℝ) (n := n) omega)

/--
%%handwave
name:
  The presheaf de Rham complex
statement:
  The presheaves of smooth real-valued differential forms, together with
  exterior differentiation, form a cochain complex on the open-set category.
proof:
  The object in degree \(n\) is the presheaf of smooth \(n\)-forms.  The
  differential in an allowed cochain degree is exterior differentiation, and
  all other differentials are zero.  The complex identity is the presheaf-level
  statement that exterior differentiation squares to zero.
-/
noncomputable def smoothFormsPresheafCochainComplex [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] :
    CochainComplex
      (TopCat.Presheaf (ModuleCat.{max v m} ℝ) (TopCat.of M : TopCat.{m})) ℕ where
  X n := smoothFormsPresheaf (M := M) Iℝ n
  d i j :=
    if h : i + 1 = j then
      deRhamDifferentialPresheafNatTrans (M := M) Iℝ i ≫
        eqToHom (by rw [h])
    else
      0
  shape i j hij := by
    rw [dif_neg]
    intro h
    exact hij (ComplexShape.up_mk i j h)
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := by
      simpa [ComplexShape.up, ComplexShape.up'] using hij
    subst j
    have hjk' : i + 1 + 1 = k := by
      simpa [ComplexShape.up, ComplexShape.up'] using hjk
    subst k
    simp [deRhamDifferentialPresheafNatTrans_comp_eq_zero]

/--
%%handwave
name:
  Terms of the presheaf de Rham complex
statement:
  The term of the presheaf de Rham complex in degree \(n\) is the presheaf of
  smooth \(n\)-forms.
proof:
  This is the definition of the presheaf de Rham complex.
-/
@[simp]
theorem smoothFormsPresheafCochainComplex_X [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] (n : ℕ) :
    (smoothFormsPresheafCochainComplex (M := M) Iℝ).X n =
      smoothFormsPresheaf (M := M) Iℝ n := rfl

/--
%%handwave
name:
  Differential of the presheaf de Rham complex
statement:
  The differential from degree \(n\) to degree \(n+1\) in the presheaf de Rham
  complex is exterior differentiation.
proof:
  This is the allowed cochain differential in the defining complex.
-/
@[simp]
theorem smoothFormsPresheafCochainComplex_d_succ [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] (n : ℕ) :
    (smoothFormsPresheafCochainComplex (M := M) Iℝ).d n (n + 1) =
      deRhamDifferentialPresheafNatTrans (M := M) Iℝ n := by
  simp [smoothFormsPresheafCochainComplex]

/--
%%handwave
name:
  The additive presheaf of smooth differential forms
statement:
  Forgetting scalar multiplication, the presheaf of smooth real-valued
  \(n\)-forms is a presheaf of abelian groups.
proof:
  Postcompose the real-vector-space-valued presheaf of smooth forms with the
  forgetful functor from real vector spaces to abelian groups.
-/
noncomputable def smoothFormsAddPresheaf [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
  smoothFormsPresheaf (M := M) Iℝ n ⋙
    forget₂ (ModuleCat.{max v m} ℝ) AddCommGrpCat.{max v m}

/--
%%handwave
name:
  The additive presheaf de Rham complex
statement:
  Forgetting scalar multiplication in each degree, the presheaf de Rham
  complex is a cochain complex of abelian-group-valued presheaves.
proof:
  Apply the forgetful functor from real vector spaces to abelian groups degree
  by degree to the presheaf de Rham complex.
-/
noncomputable def smoothFormsAddPresheafCochainComplex [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] :
    CochainComplex
      (TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m})) ℕ :=
  (((CategoryTheory.Functor.whiskeringRight
      (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ
      (ModuleCat.{max v m} ℝ) AddCommGrpCat.{max v m}).obj
        (forget₂ (ModuleCat.{max v m} ℝ) AddCommGrpCat.{max v m})).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
    (smoothFormsPresheafCochainComplex (M := M) Iℝ)

/--
%%handwave
name:
  Terms of the additive presheaf de Rham complex
statement:
  The term of the additive presheaf de Rham complex in degree \(n\) is the
  additive presheaf underlying smooth \(n\)-forms.
proof:
  This is the definition of the additive presheaf de Rham complex.
-/
@[simp]
theorem smoothFormsAddPresheafCochainComplex_X [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] (n : ℕ) :
    (smoothFormsAddPresheafCochainComplex (M := M) Iℝ).X n =
      smoothFormsAddPresheaf (M := M) Iℝ n := rfl

/--
%%handwave
name:
  Smooth forms are separated by an arbitrary open cover
statement:
  If two smooth forms on the union of an open cover have equal restrictions to
  every member of the cover, then the two forms are equal.
proof:
  Compare values at a point and choose a member of the cover containing that
  point.  The equality of the two restrictions gives equality after pullback by
  the tangent map of the corresponding open inclusion, and that tangent map is
  invertible.
-/
theorem smoothForms_iSup_eq_of_forall_restrict_eq [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    {s t : SmoothForms (I := Iℝ) (M := (iSup U : TopologicalSpace.Opens M)) ℝ n}
    (h :
      ∀ i : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
          (V := (iSup U : TopologicalSpace.Opens M)) (W := U i) (le_iSup U i) n s =
            restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
              (V := (iSup U : TopologicalSpace.Opens M)) (W := U i) (le_iSup U i) n t) :
    s = t := by
  apply DifferentialForm.ext
  intro x
  rcases TopologicalSpace.Opens.mem_iSup.mp x.2 with ⟨i, hxi⟩
  let xUi : U i := ⟨(x : M), hxi⟩
  have hxinc : TopologicalSpace.Opens.inclusion (le_iSup U i) xUi = x := by
    ext
    rfl
  let L : TangentSpace Iℝ xUi →L[ℝ] TangentSpace Iℝ x :=
    mfderiv Iℝ Iℝ (TopologicalSpace.Opens.inclusion (le_iSup U i)) xUi
  have hpoint :
      (s.toFun x).compContinuousLinearMap L =
        (t.toFun x).compContinuousLinearMap L := by
    have hrestr :=
      congrArg (fun omega : SmoothForms (I := Iℝ) (M := U i) ℝ n => omega.toFun xUi) (h i)
    simpa [restrictSmoothFormsOfLE, restrictSmoothFormOfLE, L, hxinc] using hrestr
  exact continuousAlternatingMap_compContinuousLinearMap_injective L
    (mfderiv_opens_inclusion_isInvertible (I := Iℝ)
      (U i) (iSup U : TopologicalSpace.Opens M) (le_iSup U i) xUi).surjective hpoint

/--
%%handwave
name:
  Pointwise glued form on an arbitrary open cover
statement:
  Given local smooth forms on an open cover, define a pointwise form on the
  union by choosing a cover member containing the point and transporting that
  local form through the ambient tangent space.
proof:
  At a point of the union, choose an index \(i\) with \(x\in U_i\).  Extend the
  value of the \(U_i\)-form to the ambient tangent space and restrict it back to
  the tangent space of the union.
-/
noncomputable def smoothForms_iSupGlueFun [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n)
    (x : (iSup U : TopologicalSpace.Opens M)) :
    FormAt (I := Iℝ) (M := (iSup U : TopologicalSpace.Opens M)) ℝ n x :=
  let i : ι := Classical.choose (TopologicalSpace.Opens.mem_iSup.mp x.2)
  let hxi : (x : M) ∈ U i := Classical.choose_spec (TopologicalSpace.Opens.mem_iSup.mp x.2)
  (smoothFormOpenExtensionValue (I := Iℝ) (A := ℝ) (U i) (sf i) (x : M) hxi).compContinuousLinearMap
    (mfderiv Iℝ Iℝ
      (fun y : (iSup U : TopologicalSpace.Opens M) => (y : M)) x)

/--
%%handwave
name:
  The pointwise glued form is independent of the chosen cover member
statement:
  If the local forms agree on pairwise overlaps, then the pointwise glued form
  on the union agrees with the value obtained from any cover member containing
  the point.
proof:
  Compare two choices on their overlap.  The compatibility hypothesis gives
  equality after restriction to the overlap, and invertibility of the relevant
  open-inclusion tangent maps transports this equality through the ambient
  tangent space.
-/
theorem smoothForms_iSupGlueFun_eq_of_mem [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n)
    (hcompat :
      ∀ i j : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U i) (W := U i ⊓ U j) inf_le_left n (sf i) =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U j) (W := U i ⊓ U j) inf_le_right n (sf j))
    (x : (iSup U : TopologicalSpace.Opens M)) (i : ι) (hxi : (x : M) ∈ U i) :
    smoothForms_iSupGlueFun (M := M) Iℝ n U sf x =
      (smoothFormOpenExtensionValue (I := Iℝ) (A := ℝ) (U i) (sf i) (x : M) hxi).compContinuousLinearMap
        (mfderiv Iℝ Iℝ
          (fun y : (iSup U : TopologicalSpace.Opens M) => (y : M)) x) := by
  let S : TopologicalSpace.Opens M := iSup U
  let j : ι := Classical.choose (TopologicalSpace.Opens.mem_iSup.mp x.2)
  let hxj : (x : M) ∈ U j :=
    Classical.choose_spec (TopologicalSpace.Opens.mem_iSup.mp x.2)
  let W : TopologicalSpace.Opens M := U j ⊓ U i
  let xW : W := ⟨(x : M), ⟨hxj, hxi⟩⟩
  let xUj : U j := TopologicalSpace.Opens.inclusion (inf_le_left : W ≤ U j) xW
  let xUi : U i := TopologicalSpace.Opens.inclusion (inf_le_right : W ≤ U i) xW
  let LWM : TangentSpace Iℝ xW →L[ℝ] TangentSpace Iℝ (x : M) :=
    mfderiv Iℝ Iℝ (fun y : W => (y : M)) xW
  let LWj : TangentSpace Iℝ xW →L[ℝ] TangentSpace Iℝ xUj :=
    mfderiv Iℝ Iℝ (TopologicalSpace.Opens.inclusion (inf_le_left : W ≤ U j)) xW
  let LWi : TangentSpace Iℝ xW →L[ℝ] TangentSpace Iℝ xUi :=
    mfderiv Iℝ Iℝ (TopologicalSpace.Opens.inclusion (inf_le_right : W ≤ U i)) xW
  let LSM : TangentSpace Iℝ x →L[ℝ] TangentSpace Iℝ (x : M) :=
    mfderiv Iℝ Iℝ (fun y : S => (y : M)) x
  let ηj : FormAt (I := Iℝ) (M := M) ℝ n (x : M) :=
    smoothFormOpenExtensionValue (I := Iℝ) (A := ℝ) (U j) (sf j) (x : M) hxj
  let ηi : FormAt (I := Iℝ) (M := M) ℝ n (x : M) :=
    smoothFormOpenExtensionValue (I := Iℝ) (A := ℝ) (U i) (sf i) (x : M) hxi
  have hoverlap :
      ((sf j).toFun xUj).compContinuousLinearMap LWj =
        ((sf i).toFun xUi).compContinuousLinearMap LWi := by
    have h :=
      congrArg (fun omega : SmoothForms (I := Iℝ) (M := W) ℝ n => omega.toFun xW)
        (hcompat j i)
    simpa [W, xUj, xUi, LWj, LWi, restrictSmoothFormsOfLE, restrictSmoothFormOfLE] using h
  have hj :
      ηj.compContinuousLinearMap LWM =
        ((sf j).toFun xUj).compContinuousLinearMap LWj := by
    simpa [W, xW, xUj, LWM, LWj, ηj] using
      smoothFormOpenExtensionValue_restrictOfLE (I := Iℝ) (A := ℝ)
        W (U j) (inf_le_left : W ≤ U j) (sf j) xW
  have hi :
      ηi.compContinuousLinearMap LWM =
        ((sf i).toFun xUi).compContinuousLinearMap LWi := by
    simpa [W, xW, xUi, LWM, LWi, ηi] using
      smoothFormOpenExtensionValue_restrictOfLE (I := Iℝ) (A := ℝ)
        W (U i) (inf_le_right : W ≤ U i) (sf i) xW
  have hηcomp : ηj.compContinuousLinearMap LWM = ηi.compContinuousLinearMap LWM :=
    hj.trans (hoverlap.trans hi.symm)
  have hη : ηj = ηi :=
    continuousAlternatingMap_compContinuousLinearMap_injective LWM
      (mfderiv_subtypeVal_isInvertible (I := Iℝ) W xW).surjective hηcomp
  change ηj.compContinuousLinearMap LSM = ηi.compContinuousLinearMap LSM
  rw [hη]

/--
%%handwave
name:
  The induced cover of the union is a cover
statement:
  If \(S=\bigcup_i U_i\), then the open subsets \(S\cap U_i\) cover \(S\).
proof:
  A point of \(S\) belongs to some \(U_i\) by definition of the union, hence it
  belongs to \(S\cap U_i\).
-/
theorem iSup_openInOpen_iSup_eq_top
    {ι : Type m} (U : ι → TopologicalSpace.Opens M) :
    iSup (fun i : ι => openInOpen (iSup U : TopologicalSpace.Opens M) (U i)) =
      ⊤ := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    rcases TopologicalSpace.Opens.mem_iSup.mp x.2 with ⟨i, hxi⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, by simpa [openInOpen] using hxi⟩

/--
%%handwave
name:
  The local form on an induced cover member
statement:
  A smooth form on \(U_i\) restricts to a smooth form on \(S\cap U_i\), viewed
  as an open subset of \(S\).
proof:
  First restrict the form from \(U_i\) to \(S\cap U_i\) as an open subset of
  the ambient manifold.  Then identify this intersection with the corresponding
  open subset of \(S\).
-/
noncomputable def smoothForms_iSupGlueLocalForm [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n) (i : ι) :
    SmoothForms (I := Iℝ)
      (M := openInOpen (iSup U : TopologicalSpace.Opens M) (U i)) ℝ n :=
  openInOpenInfForm (I := Iℝ) (M := M) (A := ℝ)
    (iSup U : TopologicalSpace.Opens M) (U i)
    (restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
      (W := (iSup U : TopologicalSpace.Opens M) ⊓ U i) (V := U i)
      inf_le_right n (sf i))

/--
%%handwave
name:
  Pointwise gluing agrees with the induced local form
statement:
  On \(S\cap U_i\), the pointwise glued form agrees with the ambient extension
  of the local form induced on this open subset of \(S\).
proof:
  Use independence of the chosen cover member to write the glued form using the
  \(U_i\)-form.  Then compare the two ways of passing through the tangent maps
  for \(S\cap U_i\subset S\subset M\).
-/
theorem smoothForms_iSupGlueFun_eq_localOpenExtension [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n)
    (hcompat :
      ∀ i j : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U i) (W := U i ⊓ U j) inf_le_left n (sf i) =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U j) (W := U i ⊓ U j) inf_le_right n (sf j))
    (x : (iSup U : TopologicalSpace.Opens M)) (i : ι)
    (hxi : x ∈ openInOpen (iSup U : TopologicalSpace.Opens M) (U i)) :
    smoothForms_iSupGlueFun (M := M) Iℝ n U sf x =
      smoothFormOpenExtensionValue (I := Iℝ)
        (M := (iSup U : TopologicalSpace.Opens M)) (A := ℝ)
        (openInOpen (iSup U : TopologicalSpace.Opens M) (U i))
        (smoothForms_iSupGlueLocalForm (M := M) Iℝ n U sf i) x hxi := by
  let S : TopologicalSpace.Opens M := iSup U
  let V : TopologicalSpace.Opens M := U i
  let W : TopologicalSpace.Opens M := S ⊓ V
  let WU : TopologicalSpace.Opens S := openInOpen S V
  let omega : SmoothForms (I := Iℝ) (M := W) ℝ n :=
    restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
      (W := W) (V := V) inf_le_right n (sf i)
  let alpha : SmoothForms (I := Iℝ) (M := WU) ℝ n :=
    openInOpenInfForm (I := Iℝ) (M := M) (A := ℝ) S V omega
  let xWU : WU := ⟨x, by simpa [S, V, WU] using hxi⟩
  let xW : W := openInOpenEquivInf S V xWU
  have hxiM : (x : M) ∈ V := by
    simpa [S, V, WU] using hxi
  let LSM : TangentSpace Iℝ x →L[ℝ] TangentSpace Iℝ (x : M) :=
    mfderiv Iℝ Iℝ (fun y : S => (y : M)) x
  let LWUS : TangentSpace Iℝ xWU →L[ℝ] TangentSpace Iℝ x :=
    mfderiv Iℝ Iℝ (fun y : WU => (y : S)) xWU
  let LWM : TangentSpace Iℝ xW →L[ℝ] TangentSpace Iℝ (x : M) :=
    mfderiv Iℝ Iℝ (fun y : W => (y : M)) xW
  let η : FormAt (I := Iℝ) (M := M) ℝ n (x : M) :=
    smoothFormOpenExtensionValue (I := Iℝ) (A := ℝ) V (sf i) (x : M) hxiM
  let θ : FormAt (I := Iℝ) (M := M) ℝ n (x : M) :=
    smoothFormOpenExtensionValue (I := Iℝ) (A := ℝ) W omega (x : M)
      (by
        change (x : M) ∈ (S ⊓ V : TopologicalSpace.Opens M)
        exact ⟨x.2, hxiM⟩)
  have hglue :
      smoothForms_iSupGlueFun (M := M) Iℝ n U sf x =
        η.compContinuousLinearMap LSM := by
    simpa [S, V, LSM, η] using
      smoothForms_iSupGlueFun_eq_of_mem (M := M) Iℝ n U sf hcompat x i hxiM
  have hθ_restrict :
      θ.compContinuousLinearMap LWM = omega.toFun xW := by
    simpa [S, V, W, xW, LWM, θ, omega] using
      smoothFormOpenExtensionValue_restrict (I := Iℝ) (A := ℝ) W omega xW
  have hη_restrict :
      η.compContinuousLinearMap LWM = omega.toFun xW := by
    simpa [S, V, W, xW, LWM, η, omega, restrictSmoothFormsOfLE, restrictSmoothFormOfLE] using
      smoothFormOpenExtensionValue_restrictOfLE (I := Iℝ) (A := ℝ)
        W V (inf_le_right : W ≤ V) (sf i) xW
  have hθη : θ = η :=
    continuousAlternatingMap_compContinuousLinearMap_injective LWM
      (mfderiv_subtypeVal_isInvertible (I := Iℝ) W xW).surjective
      (hθ_restrict.trans hη_restrict.symm)
  apply continuousAlternatingMap_compContinuousLinearMap_injective LWUS
    (mfderiv_subtypeVal_isInvertible (I := Iℝ) (M := S) WU xWU).surjective
  rw [hglue]
  have hright :
      (smoothFormOpenExtensionValue (I := Iℝ) (M := S) (A := ℝ) WU alpha x hxi).compContinuousLinearMap
          LWUS =
        alpha.toFun xWU := by
    simpa [S, V, WU, xWU, alpha, LWUS] using
      smoothFormOpenExtensionValue_restrict (I := Iℝ) (M := S) (A := ℝ) WU alpha xWU
  have hright' :
      (smoothFormOpenExtensionValue (I := Iℝ)
        (M := (iSup U : TopologicalSpace.Opens M)) (A := ℝ)
        (openInOpen (iSup U : TopologicalSpace.Opens M) (U i))
        (smoothForms_iSupGlueLocalForm (M := M) Iℝ n U sf i) x hxi).compContinuousLinearMap
          LWUS =
        alpha.toFun xWU := by
    simpa [S, V, WU, xWU, alpha, LWUS, smoothForms_iSupGlueLocalForm] using hright
  change
    (η.compContinuousLinearMap LSM).compContinuousLinearMap LWUS =
      (smoothFormOpenExtensionValue (I := Iℝ)
        (M := (iSup U : TopologicalSpace.Opens M)) (A := ℝ)
        (openInOpen (iSup U : TopologicalSpace.Opens M) (U i))
        (smoothForms_iSupGlueLocalForm (M := M) Iℝ n U sf i) x hxi).compContinuousLinearMap
          LWUS
  rw [hright']
  have halpha :
      alpha.toFun xWU =
        θ.compContinuousLinearMap (LSM.comp LWUS) := by
    simp [alpha, omega, openInOpenInfForm, openInOpenInfFormFun, S, V, W, WU,
      xWU, θ, LSM, LWUS]
  rw [halpha, hθη]
  ext v
  rfl

/--
%%handwave
name:
  The pointwise glued form on an arbitrary cover is smooth
statement:
  If local smooth forms agree on pairwise overlaps, then the pointwise glued
  form on the union of the cover is a smooth differential form.
proof:
  On the part of the union lying over each cover member, the pointwise glued
  form agrees with that member's smooth form after the standard ambient tangent
  transport.  Smoothness is therefore local on the cover.
-/
theorem isContMDiffForm_smoothForms_iSupGlueFun [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n)
    (hcompat :
      ∀ i j : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U i) (W := U i ⊓ U j) inf_le_left n (sf i) =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U j) (W := U i ⊓ U j) inf_le_right n (sf j)) :
    IsContMDiffForm (I := Iℝ)
      (M := (iSup U : TopologicalSpace.Opens M)) (F := ℝ) (n := n) ∞
      (smoothForms_iSupGlueFun (M := M) Iℝ n U sf) := by
  let S : TopologicalSpace.Opens M := iSup U
  let US : ι → TopologicalSpace.Opens S := fun i => openInOpen S (U i)
  let alpha : ∀ i : ι, SmoothForms (I := Iℝ) (M := US i) ℝ n :=
    fun i => smoothForms_iSupGlueLocalForm (M := M) Iℝ n U sf i
  have hcover : iSup US = ⊤ := by
    simpa [S, US] using iSup_openInOpen_iSup_eq_top (M := M) U
  exact isContMDiffForm_of_eqOn_iSup_open_cover
    (I := Iℝ) (M := S) (A := ℝ) US hcover
    (smoothForms_iSupGlueFun (M := M) Iℝ n U sf) alpha
    (fun i hx => by
      simpa [S, US, alpha] using
        smoothForms_iSupGlueFun_eq_localOpenExtension
          (M := M) Iℝ n U sf hcompat hx i)


/--
%%handwave
name:
  Smooth form glued from an arbitrary open cover
statement:
  Compatible smooth forms on an open cover define a smooth form on the union.
proof:
  Use the pointwise glued form and the local smoothness statement.
-/
noncomputable def smoothForms_iSupGlue [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n)
    (hcompat :
      ∀ i j : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U i) (W := U i ⊓ U j) inf_le_left n (sf i) =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U j) (W := U i ⊓ U j) inf_le_right n (sf j)) :
    SmoothForms (I := Iℝ) (M := (iSup U : TopologicalSpace.Opens M)) ℝ n where
  toFun := smoothForms_iSupGlueFun (M := M) Iℝ n U sf
  isContMDiff := isContMDiffForm_smoothForms_iSupGlueFun (M := M) Iℝ n U sf hcompat

/--
%%handwave
name:
  Restricting the arbitrary-cover glued form
statement:
  The smooth form glued from a compatible family on an arbitrary open cover
  restricts to the original form on every cover member.
proof:
  At a point of a cover member, use the independence statement to write the
  glued value using that member.  The tangent map from the member to the union
  followed by the tangent map from the union to the ambient manifold equals the
  tangent map from the member to the ambient manifold, and ambient extension
  then restricts back to the original local form.
-/
theorem restrictSmoothFormsOfLE_smoothForms_iSupGlue [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n)
    (hcompat :
      ∀ i j : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U i) (W := U i ⊓ U j) inf_le_left n (sf i) =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U j) (W := U i ⊓ U j) inf_le_right n (sf j))
    (i : ι) :
    restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
      (V := (iSup U : TopologicalSpace.Opens M)) (W := U i) (le_iSup U i) n
      (smoothForms_iSupGlue (M := M) Iℝ n U sf hcompat) =
        sf i := by
  apply DifferentialForm.ext
  intro x
  let S : TopologicalSpace.Opens M := iSup U
  let xS : S := TopologicalSpace.Opens.inclusion (le_iSup U i) x
  let LUS : TangentSpace Iℝ x →L[ℝ] TangentSpace Iℝ xS :=
    mfderiv Iℝ Iℝ (TopologicalSpace.Opens.inclusion (le_iSup U i)) x
  let LSM : TangentSpace Iℝ xS →L[ℝ] TangentSpace Iℝ (x : M) :=
    mfderiv Iℝ Iℝ (fun y : S => (y : M)) xS
  let LUM : TangentSpace Iℝ x →L[ℝ] TangentSpace Iℝ (x : M) :=
    mfderiv Iℝ Iℝ (fun y : U i => (y : M)) x
  let η : FormAt (I := Iℝ) (M := M) ℝ n (x : M) :=
    smoothFormOpenExtensionValue (I := Iℝ) (A := ℝ) (U i) (sf i) (x : M) x.2
  have hvalue :
      smoothForms_iSupGlueFun (M := M) Iℝ n U sf xS =
        η.compContinuousLinearMap LSM := by
    simpa [S, xS, LSM, η] using
      smoothForms_iSupGlueFun_eq_of_mem (M := M) Iℝ n U sf hcompat xS i
        (by simp [xS])
  have hfactor : LSM.comp LUS = LUM := by
    simpa [S, xS, LSM, LUS, LUM] using
      mfderiv_subtypeVal_comp_inclusion_eq
        (I := Iℝ) (U i) S (le_iSup U i) x
  have hη : η.compContinuousLinearMap LUM = (sf i).toFun x := by
    simpa [η, LUM] using
      smoothFormOpenExtensionValue_restrict (I := Iℝ) (A := ℝ) (U i) (sf i) x
  change
    (smoothForms_iSupGlueFun (M := M) Iℝ n U sf xS).compContinuousLinearMap LUS =
      (sf i).toFun x
  rw [hvalue]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have harg :
      (fun k => LSM (LUS (v k))) = fun k => LUM (v k) := by
    funext k
    exact congrArg
      (fun L : TangentSpace Iℝ x →L[ℝ] TangentSpace Iℝ (x : M) => L (v k))
      hfactor
  change η (fun k => LSM (LUS (v k))) = ((sf i).toFun x) v
  rw [harg]
  simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply] using
    congrArg (fun omega : FormAt (I := Iℝ) (M := M) ℝ n (x : M) => omega v) hη

/--
%%handwave
name:
  Compatible smooth forms have a glued form on an arbitrary cover
statement:
  For an open cover \(\{U_i\}\), a compatible family of smooth real-valued
  \(n\)-forms on the \(U_i\) has a smooth form on \(\bigcup_i U_i\) whose
  restriction to each \(U_i\) is the given form.
proof:
  Define the form pointwise by choosing a cover member containing the point.
  Compatibility on overlaps makes this independent of the choice, and
  smoothness follows from the local open-cover smoothness criterion.
-/
theorem exists_smoothForms_iSup_gluing [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n)
    (hcompat :
      ∀ i j : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U i) (W := U i ⊓ U j) inf_le_left n (sf i) =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U j) (W := U i ⊓ U j) inf_le_right n (sf j)) :
    ∃ s : SmoothForms (I := Iℝ) (M := (iSup U : TopologicalSpace.Opens M)) ℝ n,
      ∀ i : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
          (V := (iSup U : TopologicalSpace.Opens M)) (W := U i) (le_iSup U i) n s =
            sf i := by
  exact ⟨smoothForms_iSupGlue (M := M) Iℝ n U sf hcompat,
    restrictSmoothFormsOfLE_smoothForms_iSupGlue (M := M) Iℝ n U sf hcompat⟩

/--
%%handwave
name:
  Compatible smooth forms glue on arbitrary open covers
statement:
  For an open cover \(\{U_i\}\), a compatible family of smooth real-valued
  \(n\)-forms on the \(U_i\) has a unique smooth form on \(\bigcup_i U_i\)
  whose restriction to each \(U_i\) is the given form.
proof:
  Define the form pointwise by choosing a cover member containing the point.
  Compatibility on pairwise overlaps makes this independent of the choice.
  Smoothness follows from the local open-cover smoothness criterion, and
  uniqueness follows because the \(U_i\) cover the union.
tags:
  milestone
-/
theorem existsUnique_smoothForms_iSup_gluing [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M]
    {ι : Type m} (U : ι → TopologicalSpace.Opens M)
    (sf : ∀ i : ι, SmoothForms (I := Iℝ) (M := U i) ℝ n)
    (hcompat :
      ∀ i j : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U i) (W := U i ⊓ U j) inf_le_left n (sf i) =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U j) (W := U i ⊓ U j) inf_le_right n (sf j)) :
    ∃! s : SmoothForms (I := Iℝ) (M := (iSup U : TopologicalSpace.Opens M)) ℝ n,
      ∀ i : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
          (V := (iSup U : TopologicalSpace.Opens M)) (W := U i) (le_iSup U i) n s =
            sf i := by
  rcases exists_smoothForms_iSup_gluing (M := M) Iℝ n U sf hcompat with ⟨s, hs⟩
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact smoothForms_iSup_eq_of_forall_restrict_eq (M := M) Iℝ n U
    (s := t) (t := s) (fun i => (ht i).trans (hs i).symm)

/--
%%handwave
name:
  Compatible smooth forms glue uniquely
statement:
  For every open cover, a compatible family of smooth real-valued
  \(n\)-forms has a unique smooth glued form on the union.
proof:
  Glue the underlying alternating forms pointwise on tangent spaces.  The
  compatibility hypotheses make this independent of the chosen member of the
  cover, and smoothness is local in charts.
tags:
  milestone
-/
theorem smoothFormsAddPresheaf_isSheafUniqueGluing [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    (smoothFormsAddPresheaf (M := M) Iℝ n).IsSheafUniqueGluing := by
  intro ι U sf hcompat
  have hcompat' :
      ∀ i j : ι,
        restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U i) (W := U i ⊓ U j) inf_le_left n (sf i) =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            (V := U j) (W := U i ⊓ U j) inf_le_right n (sf j) := by
    intro i j
    simpa [smoothFormsAddPresheaf, smoothFormsPresheaf] using hcompat i j
  rcases existsUnique_smoothForms_iSup_gluing
      (M := M) Iℝ n U sf hcompat' with ⟨s, hs, hs_unique⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    simpa [smoothFormsAddPresheaf, smoothFormsPresheaf] using hs i
  · intro t ht
    exact hs_unique t (fun i => by
      simpa [smoothFormsAddPresheaf, smoothFormsPresheaf] using ht i)

/--
%%handwave
name:
  Smooth forms satisfy the sheaf condition
statement:
  The abelian-group-valued presheaf of smooth real-valued \(n\)-forms is a
  sheaf on the open-set site.
proof:
  Apply the unique-gluing criterion to [compatible smooth forms glue uniquely](lean:JJMath.Manifold.smoothFormsAddPresheaf_isSheafUniqueGluing).
tags:
  milestone
-/
theorem smoothFormsAddPresheaf_isSheaf [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    (smoothFormsAddPresheaf (M := M) Iℝ n).IsSheaf := by
  exact
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
      (smoothFormsAddPresheaf (M := M) Iℝ n)).2
      (smoothFormsAddPresheaf_isSheafUniqueGluing (M := M) Iℝ n)

/--
%%handwave
name:
  The sheaf of smooth differential forms
statement:
  For every \(n\), smooth real-valued \(n\)-forms form a sheaf of abelian
  groups on the open-set site.
proof:
  Bundle [the sheaf condition for smooth forms](lean:JJMath.Manifold.smoothFormsAddPresheaf_isSheaf) with the additive presheaf of smooth forms.
-/
noncomputable def smoothFormsAddSheaf [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    TopCat.Sheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) where
  obj := smoothFormsAddPresheaf (M := M) Iℝ n
  property := smoothFormsAddPresheaf_isSheaf (M := M) Iℝ n

/--
%%handwave
name:
  The presheaf underlying the sheaf of smooth forms
statement:
  The underlying presheaf of the sheaf of smooth \(n\)-forms is the additive
  presheaf of smooth \(n\)-forms.
proof:
  This is the definition of the sheaf of smooth forms.
-/
@[simp]
theorem smoothFormsAddSheaf_obj [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    (smoothFormsAddSheaf (M := M) Iℝ n).obj =
      smoothFormsAddPresheaf (M := M) Iℝ n := rfl

/--
%%handwave
name:
  A smooth function acts linearly on the presheaf of smooth forms
statement:
  Multiplication by a global smooth real-valued function defines an
  endomorphism of the vector-space-valued presheaf of smooth differential
  forms in each degree.
proof:
  On each open set, restrict the function and multiply forms pointwise.
  Naturality is the compatibility of pointwise multiplication with restriction
  along open inclusions.
-/
noncomputable def smoothFormsPointwiseSMulPresheafHom [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (χ : C^∞⟮Iℝ, M; ℝ⟯) :
    smoothFormsPresheaf (M := M) Iℝ n ⟶
      smoothFormsPresheaf (M := M) Iℝ n where
  app U :=
    ModuleCat.ofHom
      { toFun := fun omega =>
          smoothFormsPointwiseSMul (I := Iℝ) (M := U.unop) (A := ℝ)
            (smoothFunctionRestrictToOpen (I := Iℝ) (M := M) U.unop χ) omega
        map_add' := by
          intro omega eta
          apply DifferentialForm.ext
          intro x
          ext v
          change
            χ (x : M) * (omega.toFun x v + eta.toFun x v) =
              χ (x : M) * omega.toFun x v + χ (x : M) * eta.toFun x v
          ring
        map_smul' := by
          intro c omega
          apply DifferentialForm.ext
          intro x
          ext v
          change
            χ (x : M) * (c * omega.toFun x v) =
              c * (χ (x : M) * omega.toFun x v)
          ring }
  naturality {U V} f := by
    ext omega
    apply DifferentialForm.ext
    intro x
    ext v
    have h :=
      restrictSmoothFormsOfLE_smoothFormsPointwiseSMul
        (I := Iℝ) (M := M) (A := ℝ)
        (CategoryTheory.leOfHom f.unop) (n := n) χ omega
    simpa [smoothFormsPresheaf] using
      congrArg (fun eta => eta.toFun x v) h

/--
%%handwave
name:
  A smooth function acts on the additive presheaf of smooth forms
statement:
  Forgetting scalar multiplication, multiplication by a global smooth
  real-valued function defines an endomorphism of the additive presheaf of
  smooth differential forms in each degree.
proof:
  Apply the forgetful functor from real vector spaces to abelian groups to
  [the linear presheaf endomorphism induced by the smooth function](lean:JJMath.Manifold.smoothFormsPointwiseSMulPresheafHom).
-/
noncomputable def smoothFormsPointwiseSMulAddPresheafHom [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (χ : C^∞⟮Iℝ, M; ℝ⟯) :
    smoothFormsAddPresheaf (M := M) Iℝ n ⟶
      smoothFormsAddPresheaf (M := M) Iℝ n :=
  Functor.whiskerRight
    (smoothFormsPointwiseSMulPresheafHom (M := M) Iℝ n χ)
    (forget₂ (ModuleCat.{max v m} ℝ) AddCommGrpCat.{max v m})

/--
%%handwave
name:
  Constant scalar multiplication commutes with exterior differentiation on presheaves
statement:
  Multiplication of smooth forms by a constant real function commutes with
  exterior differentiation on every open set.
proof:
  On an open set, multiplication by the restricted constant function is
  ordinary scalar multiplication by that real number.  The result is then
  \(d(r\omega)=r\,d\omega\).
-/
theorem smoothFormsPointwiseSMulAddPresheafHom_const_comp_d [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (r : ℝ) :
    smoothFormsPointwiseSMulAddPresheafHom (M := M) Iℝ n
        (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r) ≫
      (smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d n (n + 1) =
    (smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d n (n + 1) ≫
      smoothFormsPointwiseSMulAddPresheafHom (M := M) Iℝ (n + 1)
        (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r) := by
  ext U omega
  change SmoothForms (I := Iℝ) (M := U) ℝ n at omega
  let χU : C^∞⟮Iℝ, U; ℝ⟯ :=
    smoothFunctionRestrictToOpen (I := Iℝ) (M := M) U
      (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r)
  have hmul :
      smoothFormsPointwiseSMul (I := Iℝ) (M := U) (A := ℝ)
          χU omega =
        r • omega := by
    apply DifferentialForm.ext
    intro x
    ext v
    change χU x * omega.toFun x v = r * omega.toFun x v
    simp [χU, smoothFunctionRestrictToOpen,
      smoothRealConstantFunction]
  have hmul_d :
      smoothFormsPointwiseSMul (I := Iℝ) (M := U) (A := ℝ)
          χU (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n omega) =
        r • deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n omega := by
    apply DifferentialForm.ext
    intro x
    ext v
    change
      χU x *
          (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n omega).toFun x v =
        r *
          (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n omega).toFun x v
    simp [χU, smoothFunctionRestrictToOpen,
      smoothRealConstantFunction]
  have hform :
      deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n
          (smoothFormsPointwiseSMul (I := Iℝ) (M := U) (A := ℝ)
            χU omega) =
        smoothFormsPointwiseSMul (I := Iℝ) (M := U) (A := ℝ)
          χU (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n omega) := by
    calc
      deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n
          (smoothFormsPointwiseSMul (I := Iℝ) (M := U) (A := ℝ)
            χU omega)
          =
        deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n (r • omega) := by
          rw [hmul]
      _ = r • deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n omega := by
          simpa [deRhamDifferential_apply] using
            exteriorDerivative_smul (I := Iℝ) (M := U) (A := ℝ)
              r omega
      _ =
        smoothFormsPointwiseSMul (I := Iℝ) (M := U) (A := ℝ)
          χU (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n omega) := by
          rw [hmul_d]
  apply DifferentialForm.ext
  intro x
  ext v
  simpa [χU, smoothFormsPointwiseSMulAddPresheafHom,
    smoothFormsPointwiseSMulPresheafHom, smoothFormsAddPresheafCochainComplex,
    smoothFormsPresheafCochainComplex, deRhamDifferentialPresheafNatTrans] using
    congrArg (fun eta => eta.toFun x v) hform

/--
%%handwave
name:
  Constant scalar multiplication acts on the presheaf de Rham complex
statement:
  Every real scalar defines an endomorphism of the additive presheaf de Rham
  complex by multiplying forms in every degree by the corresponding constant
  function.
proof:
  Use constant scalar multiplication in each degree.  The cochain-map
  condition is [the commutation of constant scalar multiplication with exterior differentiation on presheaves](lean:JJMath.Manifold.smoothFormsPointwiseSMulAddPresheafHom_const_comp_d).
-/
noncomputable def smoothFormsAddPresheafCochainComplexScalarEnd [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (r : ℝ) :
    smoothFormsAddPresheafCochainComplex (M := M) Iℝ ⟶
      smoothFormsAddPresheafCochainComplex (M := M) Iℝ where
  f n :=
    smoothFormsPointwiseSMulAddPresheafHom (M := M) Iℝ n
      (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r)
  comm' i j hij := by
    have hij' : i + 1 = j := by
      simpa [ComplexShape.up, ComplexShape.up'] using hij
    subst j
    simpa using
      smoothFormsPointwiseSMulAddPresheafHom_const_comp_d (M := M) Iℝ i r

/--
%%handwave
name:
  A smooth function acts on the sheaf of smooth forms
statement:
  Multiplication by a global smooth real-valued function defines an
  endomorphism of the sheaf of smooth differential forms in each degree.
proof:
  Bundle [the corresponding presheaf endomorphism](lean:JJMath.Manifold.smoothFormsPointwiseSMulAddPresheafHom) as a morphism between sheaves.
-/
noncomputable def smoothFormsPointwiseSMulAddSheafHom [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (χ : C^∞⟮Iℝ, M; ℝ⟯) :
    smoothFormsAddSheaf (M := M) Iℝ n ⟶
      smoothFormsAddSheaf (M := M) Iℝ n :=
  ObjectProperty.homMk
    (smoothFormsPointwiseSMulAddPresheafHom (M := M) Iℝ n χ)

/--
%%handwave
name:
  The smooth-function sheaf endomorphism is pointwise multiplication
statement:
  On each open set, the sheaf endomorphism induced by a smooth function sends
  a form to its pointwise product with the restricted function.
proof:
  This is the construction of the sheaf endomorphism.
-/
@[simp]
theorem smoothFormsPointwiseSMulAddSheafHom_app_apply [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (χ : C^∞⟮Iℝ, M; ℝ⟯)
    (U : (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ)
    (omega : (smoothFormsAddSheaf (M := M) Iℝ n).obj.obj U) :
    (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ n χ).hom.app U omega =
      smoothFormsPointwiseSMul (I := Iℝ) (M := U.unop) (A := ℝ)
        (smoothFunctionRestrictToOpen (I := Iℝ) (M := M) U.unop χ) omega :=
  rfl

/--
%%handwave
name:
  Cutoff multiplication is zero on stalks outside the support
statement:
  If a point is outside the topological support of a smooth function, then
  multiplication by that function induces the zero endomorphism on the stalk
  of the sheaf of smooth forms at that point.
proof:
  Represent a stalk element by a form on an open neighborhood.  Shrink the
  neighborhood inside the complement of the support.  On that smaller
  neighborhood the scalar function vanishes, so the restricted cutoff multiple
  is the zero form and hence has zero germ.
tags:
  milestone
-/
theorem smoothFormsPointwiseSMulAddSheafHom_point_presheafFiber_map_eq_zero_of_notMem_tsupport
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (χ : C^∞⟮Iℝ, M; ℝ⟯) {x : M} (hx : x ∉ tsupport χ) :
    ((Opens.pointGrothendieckTopology x).presheafFiber
      (A := AddCommGrpCat.{max v m})).map
        (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ n χ).hom = 0 := by
  let Φ : Point.{m} (Opens.grothendieckTopology M) :=
    Opens.pointGrothendieckTopology x
  let F : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ n).obj
  ext η
  haveI : PreservesFilteredColimitsOfSize.{m, m}
      (forget AddCommGrpCat.{max v m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max v m})
  rcases Φ.toPresheafFiber_jointly_surjective (A := AddCommGrpCat.{max v m})
      (P := F) η with
    ⟨U, hxUΦ, omega, homega⟩
  have hxU : x ∈ U := hxUΦ.down.down
  let supportCompl : TopologicalSpace.Opens M :=
    { carrier := (tsupport χ)ᶜ
      is_open' := (isClosed_tsupport χ).isOpen_compl }
  let W : TopologicalSpace.Opens M := U ⊓ supportCompl
  have hxW : x ∈ W := ⟨hxU, hx⟩
  let hxWΦ : Φ.fiber.obj W := ⟨⟨hxW⟩⟩
  let hWU : W ≤ U := inf_le_left
  let cutoff :
      (smoothFormsAddSheaf (M := M) Iℝ n).obj.obj (Opposite.op U) :=
    (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ n χ).hom.app
      (Opposite.op U) omega
  have hres_zero : F.map (CategoryTheory.homOfLE hWU).op cutoff = 0 := by
    have hzero :
        ∀ y : W,
          smoothFunctionRestrictToOpen (I := Iℝ) (M := M) U χ
              (TopologicalSpace.Opens.inclusion hWU y) = 0 := by
      intro y
      exact smoothFunction_eq_zero_of_notMem_tsupport (I := Iℝ) χ y.2.2
    have hz :=
      restrictSmoothFormsOfLE_smoothFormsPointwiseSMul_eq_zero
        (I := Iℝ) (M := M) (A := ℝ)
        (W := W) (V := U) hWU
        (smoothFunctionRestrictToOpen (I := Iℝ) (M := M) U χ)
        omega hzero
    simpa [F, cutoff, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
      smoothFormsPresheaf, smoothFormsPointwiseSMulAddSheafHom,
      smoothFormsPointwiseSMulAddPresheafHom,
      smoothFormsPointwiseSMulPresheafHom] using hz
  rw [← homega]
  rw [Point.toPresheafFiber_naturality_apply]
  change Φ.toPresheafFiber U hxUΦ F cutoff = 0
  haveI : Subsingleton (Φ.fiber.obj U) := by
    dsimp [Φ, Opens.pointGrothendieckTopology]
    infer_instance
  have hto_W :
      Φ.toPresheafFiber W hxWΦ F (F.map (CategoryTheory.homOfLE hWU).op cutoff) =
        Φ.toPresheafFiber U hxUΦ F cutoff := by
    have h :=
      Point.toPresheafFiber_w_apply (Φ := Φ)
        (CategoryTheory.homOfLE hWU) hxWΦ F cutoff
    simpa [Subsingleton.elim (Φ.fiber.map (CategoryTheory.homOfLE hWU) hxWΦ) hxUΦ]
      using h
  calc
    Φ.toPresheafFiber U hxUΦ F cutoff =
        Φ.toPresheafFiber W hxWΦ F (F.map (CategoryTheory.homOfLE hWU).op cutoff) := by
      exact hto_W.symm
    _ = Φ.toPresheafFiber W hxWΦ F 0 := by
      rw [hres_zero]
    _ = 0 := by
      simp

/--
%%handwave
name:
  Cutoff multiplication has germ support in the function support
statement:
  The germ support of multiplication by a smooth function on the sheaf of
  smooth forms is contained in the topological support of that function.
proof:
  At any point outside the topological support, [cutoff multiplication is zero
  on the stalk](lean:JJMath.Manifold.smoothFormsPointwiseSMulAddSheafHom_point_presheafFiber_map_eq_zero_of_notMem_tsupport).
tags:
  milestone
-/
theorem smoothFormsPointwiseSMulAddSheafHom_germSupport_subset_tsupport
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (χ : C^∞⟮Iℝ, M; ℝ⟯) :
    TopCat.Sheaf.endomorphismGermSupport
        (X := TopCat.of M)
        (smoothFormsAddSheaf (M := M) Iℝ n)
        (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ n χ) ⊆
      tsupport χ := by
  intro x hx_support
  by_contra hx_not
  change
    ((Opens.pointGrothendieckTopology x).presheafFiber
      (A := AddCommGrpCat.{max v m})).map
        (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ n χ).hom ≠ 0 at hx_support
  exact hx_support
    (smoothFormsPointwiseSMulAddSheafHom_point_presheafFiber_map_eq_zero_of_notMem_tsupport
      (M := M) Iℝ n χ hx_not)

/--
%%handwave
name:
  The finite support of a smooth partition of unity sums to the identity on stalks
statement:
  For a smooth partition of unity \(\rho_i\), the finite sum of the stalk
  endomorphisms given by multiplication by those \(\rho_i\) whose topological
  supports contain a point is the identity on the stalk of the sheaf of smooth
  forms at that point.
proof:
  Shrink to a neighborhood on which every nonzero partition function is among
  the finite topological support at the point.  On that neighborhood the finite
  sum of the corresponding smooth functions is \(1\), so multiplication by the
  finite sum is the identity on every representative of every germ.
tags:
  milestone
-/
theorem smoothPartitionOfUnity_smoothFormsPointwiseSMulAddSheafHom_stalk_sum_eq_identity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] (p : ℕ)
    {ι : Type m} (ρ : SmoothPartitionOfUnity ι Iℝ M univ)
    (x : M) :
      (∑ i ∈ ρ.fintsupport x,
        ((Opens.pointGrothendieckTopology x).sheafFiber
          (A := AddCommGrpCat.{max v m})).map
            (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i))) = 𝟙 _ := by
  let Φ : Point.{m} (Opens.grothendieckTopology M) :=
    Opens.pointGrothendieckTopology x
  let F : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ p).obj
  change
    (∑ i ∈ ρ.fintsupport x,
      (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
        (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom) = 𝟙 _
  ext η
  haveI : PreservesFilteredColimitsOfSize.{m, m}
      (forget AddCommGrpCat.{max v m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max v m})
  rcases Φ.toPresheafFiber_jointly_surjective (A := AddCommGrpCat.{max v m})
      (P := F) η with
    ⟨U, hxUΦ, omega, homega⟩
  have hxU : x ∈ U := hxUΦ.down.down
  have hU_nhds : (U : Set M) ∈ 𝓝 x := U.is_open'.mem_nhds hxU
  have hfin_event : {y : M | ρ.finsupport y ⊆ ρ.fintsupport x} ∈ 𝓝 x := by
    exact ρ.eventually_finsupport_subset x
  have hboth :
      ((U : Set M) ∩ {y : M | ρ.finsupport y ⊆ ρ.fintsupport x}) ∈ 𝓝 x :=
    inter_mem hU_nhds hfin_event
  rcases mem_nhds_iff.mp hboth with ⟨Wset, hWsubset, hWopen, hxWset⟩
  let W : TopologicalSpace.Opens M := ⟨Wset, hWopen⟩
  have hxW : x ∈ W := hxWset
  let hxWΦ : Φ.fiber.obj W := ⟨⟨hxW⟩⟩
  let hWU : W ≤ U := fun y hy => (hWsubset hy).1
  have hWfin : ∀ y : W, ρ.finsupport (y : M) ⊆ ρ.fintsupport x := by
    intro y
    exact (hWsubset y.2).2
  have hsumW : ∀ y : W, ∑ i ∈ ρ.fintsupport x, ρ i (y : M) = 1 := by
    intro y
    exact ρ.sum_finsupport' (x₀ := (y : M))
      (show (y : M) ∈ (univ : Set M) by simp) (hWfin y)
  have hsection :
      (∑ i ∈ ρ.fintsupport x,
        F.map (CategoryTheory.homOfLE hWU).op
          ((smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom.app
            (Opposite.op U) omega)) =
        F.map (CategoryTheory.homOfLE hWU).op omega := by
    have h :=
      restrictSmoothFormsOfLE_smoothFormsPointwiseSMul_finset_sum_eq_self_of_sum_eq_one
        (I := Iℝ) (M := M) (A := ℝ) (W := W) (V := U)
        (hWV := hWU) (n := p)
        (s := ρ.fintsupport x) (χ := fun i => ρ i) omega hsumW
    simpa [F, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
      smoothFormsPresheaf, smoothFormsPointwiseSMulAddSheafHom,
      smoothFormsPointwiseSMulAddPresheafHom,
      smoothFormsPointwiseSMulPresheafHom] using h
  rw [← homega]
  have hto_restrict :
      Φ.toPresheafFiber W hxWΦ F
          (F.map (CategoryTheory.homOfLE hWU).op omega) =
        Φ.toPresheafFiber U hxUΦ F omega := by
    haveI : Subsingleton (Φ.fiber.obj U) := by
      dsimp [Φ, Opens.pointGrothendieckTopology]
      infer_instance
    have h :=
      Point.toPresheafFiber_w_apply (Φ := Φ)
        (CategoryTheory.homOfLE hWU) hxWΦ F omega
    simpa [Subsingleton.elim (Φ.fiber.map (CategoryTheory.homOfLE hWU) hxWΦ) hxUΦ]
      using h
  calc
    ((∑ i ∈ ρ.fintsupport x,
      (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
        (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom)
        (Φ.toPresheafFiber U hxUΦ F omega)) =
        ∑ i ∈ ρ.fintsupport x,
          Φ.toPresheafFiber U hxUΦ F
            ((smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom.app
              (Opposite.op U) omega) := by
      rw [AddCommGrpCat.finset_sum_apply]
      apply Finset.sum_congr rfl
      intro i _hi
      exact Point.toPresheafFiber_naturality_apply (Φ := Φ)
        (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom U hxUΦ omega
    _ =
        ∑ i ∈ ρ.fintsupport x,
          Φ.toPresheafFiber W hxWΦ F
            (F.map (CategoryTheory.homOfLE hWU).op
              ((smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom.app
                (Opposite.op U) omega)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hto_i :
          Φ.toPresheafFiber W hxWΦ F
              (F.map (CategoryTheory.homOfLE hWU).op
                ((smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom.app
                  (Opposite.op U) omega)) =
            Φ.toPresheafFiber U hxUΦ F
              ((smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom.app
                (Opposite.op U) omega) := by
        haveI : Subsingleton (Φ.fiber.obj U) := by
          dsimp [Φ, Opens.pointGrothendieckTopology]
          infer_instance
        have h :=
          Point.toPresheafFiber_w_apply (Φ := Φ)
            (CategoryTheory.homOfLE hWU) hxWΦ F
            ((smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom.app
              (Opposite.op U) omega)
        simpa [Subsingleton.elim (Φ.fiber.map (CategoryTheory.homOfLE hWU) hxWΦ) hxUΦ]
          using h
      exact hto_i.symm
    _ =
        Φ.toPresheafFiber W hxWΦ F
          (∑ i ∈ ρ.fintsupport x,
            F.map (CategoryTheory.homOfLE hWU).op
              ((smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)).hom.app
                (Opposite.op U) omega)) := by
      simp
    _ =
        Φ.toPresheafFiber W hxWΦ F
          (F.map (CategoryTheory.homOfLE hWU).op omega) := by
      rw [hsection]
    _ = Φ.toPresheafFiber U hxUΦ F omega := hto_restrict

/--
%%handwave
name:
  A smooth partition of unity gives a stalkwise partition of the identity
statement:
  Let \(\rho_i\) be a smooth partition of unity on a smooth manifold.  On the
  stalk of the sheaf of smooth \(p\)-forms at any point, multiplication by the
  finitely many \(\rho_i\) whose supports meet the point sums to the identity,
  and all other multiplication maps vanish.
proof:
  Local finiteness gives a neighborhood on which only finitely many
  \(\rho_i\) are nonzero.  On that neighborhood their finite sum is the
  constant function \(1\), so the corresponding finite sum of cutoff
  endomorphisms sends every germ of a form to itself.
tags:
  milestone
-/
theorem smoothPartitionOfUnity_smoothFormsPointwiseSMulAddSheafHom_stalk_partitionOfIdentity
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] (p : ℕ)
    {ι : Type m} (ρ : SmoothPartitionOfUnity ι Iℝ M univ)
    (x : M) :
    ∃ s : Finset ι,
      (∀ i, i ∉ s →
        ((Opens.pointGrothendieckTopology x).sheafFiber
          (A := AddCommGrpCat.{max v m})).map
            (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i)) = 0) ∧
      (∑ i ∈ s,
        ((Opens.pointGrothendieckTopology x).sheafFiber
          (A := AddCommGrpCat.{max v m})).map
            (smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i))) = 𝟙 _ := by
  refine ⟨ρ.fintsupport x, ?_, ?_⟩
  · intro i hi
    have hx_not : x ∉ tsupport (ρ i) := by
      intro hxi
      exact hi ((ρ.mem_fintsupport_iff x i).2 hxi)
    simpa [Point.sheafFiber] using
      smoothFormsPointwiseSMulAddSheafHom_point_presheafFiber_map_eq_zero_of_notMem_tsupport
        (M := M) Iℝ p (ρ i) hx_not
  · exact
      smoothPartitionOfUnity_smoothFormsPointwiseSMulAddSheafHom_stalk_sum_eq_identity
        (M := M) Iℝ p ρ x

/--
%%handwave
name:
  Exterior differentiation as a morphism of sheaves
statement:
  Exterior differentiation defines a morphism from the sheaf of smooth
  \(n\)-forms to the sheaf of smooth \((n+1)\)-forms.
proof:
  The underlying morphism of presheaves is the exterior-differentiation
  morphism in the additive presheaf de Rham complex.
-/
noncomputable def deRhamDifferentialAddSheafHom [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    smoothFormsAddSheaf (M := M) Iℝ n ⟶
      smoothFormsAddSheaf (M := M) Iℝ (n + 1) :=
  ObjectProperty.homMk
    ((smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d n (n + 1))

/--
%%handwave
name:
  The underlying presheaf morphism of exterior differentiation
statement:
  The morphism of sheaves given by exterior differentiation has, as its
  underlying presheaf morphism, the differential in the additive presheaf
  de Rham complex.
proof:
  This is the construction of the sheaf morphism.
-/
@[simp]
theorem deRhamDifferentialAddSheafHom_hom [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) (n : ℕ) [IsManifold Iℝ ∞ M] :
    (deRhamDifferentialAddSheafHom (M := M) Iℝ n).hom =
      (smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d n (n + 1) := rfl

/--
%%handwave
name:
  The sheaf de Rham complex
statement:
  The sheaves of smooth real-valued differential forms, together with exterior
  differentiation, form a cochain complex of sheaves of abelian groups.
proof:
  Use the sheaf of smooth \(n\)-forms in degree \(n\), exterior differentiation
  in adjacent cochain degrees, and zero maps otherwise.  The complex identity
  follows after forgetting to presheaves from the additive presheaf de Rham
  complex.
-/
noncomputable def smoothFormsAddSheafCochainComplex [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m})) ℕ where
  X n := smoothFormsAddSheaf (M := M) Iℝ n
  d i j :=
    if h : i + 1 = j then
      deRhamDifferentialAddSheafHom (M := M) Iℝ i ≫
        eqToHom (by rw [h])
    else
      0
  shape i j hij := by
    rw [dif_neg]
    intro h
    exact hij (ComplexShape.up_mk i j h)
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := by
      simpa [ComplexShape.up, ComplexShape.up'] using hij
    subst j
    have hjk' : i + 1 + 1 = k := by
      simpa [ComplexShape.up, ComplexShape.up'] using hjk
    subst k
    apply ObjectProperty.hom_ext
    simpa [deRhamDifferentialAddSheafHom] using
      (smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d_comp_d i (i + 1) (i + 1 + 1)

/--
%%handwave
name:
  Terms of the sheaf de Rham complex
statement:
  The term of the sheaf de Rham complex in degree \(n\) is the sheaf of smooth
  \(n\)-forms.
proof:
  This is the definition of the sheaf de Rham complex.
-/
@[simp]
theorem smoothFormsAddSheafCochainComplex_X [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] (n : ℕ) :
    (smoothFormsAddSheafCochainComplex (M := M) Iℝ).X n =
      smoothFormsAddSheaf (M := M) Iℝ n := rfl

/--
%%handwave
name:
  Differential of the sheaf de Rham complex
statement:
  The differential from degree \(n\) to degree \(n+1\) in the sheaf de Rham
  complex is exterior differentiation.
proof:
  This is the allowed cochain differential in the defining sheaf complex.
-/
@[simp]
theorem smoothFormsAddSheafCochainComplex_d_succ [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] (n : ℕ) :
    (smoothFormsAddSheafCochainComplex (M := M) Iℝ).d n (n + 1) =
      deRhamDifferentialAddSheafHom (M := M) Iℝ n := by
  simp [smoothFormsAddSheafCochainComplex]

/--
%%handwave
name:
  Constant scalar multiplication commutes with exterior differentiation on sheaves
statement:
  Multiplication of smooth forms by a constant real function commutes with
  exterior differentiation.
proof:
  This is the \(C^\infty\)-linearity of exterior differentiation for constant
  functions: \(d(r\omega)=r\,d\omega\).  Check the identity on each open set
  of the sheaf.
tags:
  milestone
-/
theorem smoothFormsPointwiseSMulAddSheafHom_const_comp_d [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (n : ℕ) (r : ℝ) :
    smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ n
        (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r) ≫
      deRhamDifferentialAddSheafHom (M := M) Iℝ n =
    deRhamDifferentialAddSheafHom (M := M) Iℝ n ≫
      smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ (n + 1)
        (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r) := by
  apply ObjectProperty.hom_ext
  simpa [smoothFormsPointwiseSMulAddSheafHom, deRhamDifferentialAddSheafHom,
    smoothFormsAddPresheafCochainComplex] using
    smoothFormsPointwiseSMulAddPresheafHom_const_comp_d (M := M) Iℝ n r

/--
%%handwave
name:
  Constant scalar multiplication acts on the sheaf de Rham complex
statement:
  Every real scalar defines an endomorphism of the sheaf de Rham complex by
  multiplying forms in every degree by the corresponding constant function.
proof:
  Use constant scalar multiplication in each degree.  The preceding
  commutation with exterior differentiation is exactly the cochain-map
  condition.
-/
noncomputable def smoothFormsAddSheafCochainComplexScalarEnd [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (r : ℝ) :
    smoothFormsAddSheafCochainComplex (M := M) Iℝ ⟶
      smoothFormsAddSheafCochainComplex (M := M) Iℝ where
  f n :=
    smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ n
      (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r)
  comm' i j hij := by
    have hij' : i + 1 = j := by
      simpa [ComplexShape.up, ComplexShape.up'] using hij
    subst j
    simpa [smoothFormsAddSheafCochainComplex_d_succ] using
      smoothFormsPointwiseSMulAddSheafHom_const_comp_d (M := M) Iℝ i r

/--
%%handwave
name:
  Global sections of the sheaf de Rham complex
statement:
  Applying global sections to the sheaf de Rham complex gives a cochain
  complex of abelian groups.
proof:
  Use the global-sections functor on the site of open subsets and map the
  sheaf de Rham complex through it.
-/
noncomputable def smoothFormsAddSheafGlobalSectionsCochainComplex [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    CochainComplex AddCommGrpCat.{max v m} ℕ :=
  ((CategoryTheory.Sheaf.Γ
      (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (smoothFormsAddSheafCochainComplex (M := M) Iℝ)

/--
%%handwave
name:
  Terms of the global sheaf de Rham complex
statement:
  The \(n\)-th term of the global-sections sheaf de Rham complex is the group
  of global sections of the sheaf of smooth \(n\)-forms.
proof:
  This is the definition of the complex obtained by applying global sections
  degreewise.
-/
@[simp]
theorem smoothFormsAddSheafGlobalSectionsCochainComplex_X [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] (n : ℕ) :
    (smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ).X n =
      (CategoryTheory.Sheaf.Γ
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}).obj (smoothFormsAddSheaf (M := M) Iℝ n) :=
  rfl

/--
%%handwave
name:
  Top-open sections of the presheaf de Rham complex
statement:
  Evaluating the additive presheaf de Rham complex on the whole space gives a
  cochain complex of abelian groups.
proof:
  Apply the evaluation functor at the terminal open subset to the additive
  presheaf de Rham complex.
-/
noncomputable def smoothFormsAddPresheafTopCochainComplex [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] :
    CochainComplex AddCommGrpCat.{max v m} ℕ :=
  (((CategoryTheory.evaluation
      (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ
      AddCommGrpCat.{max v m}).obj
          (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
      ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (smoothFormsAddPresheafCochainComplex (M := M) Iℝ)

/--
%%handwave
name:
  Constant scalar multiplication acts on top-open smooth-form cochains
statement:
  Evaluating the presheaf scalar endomorphism on the terminal open subset
  gives an endomorphism of the top-open smooth-form complex.
proof:
  Apply the terminal-open evaluation functor degreewise to
  [constant scalar multiplication on the presheaf de Rham complex](lean:JJMath.Manifold.smoothFormsAddPresheafCochainComplexScalarEnd).
-/
noncomputable def smoothFormsAddPresheafTopCochainComplexScalarEnd [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (r : ℝ) :
    smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ ⟶
      smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ :=
  (((CategoryTheory.evaluation
      (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ
      AddCommGrpCat.{max v m}).obj
        (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
      ).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (smoothFormsAddPresheafCochainComplexScalarEnd (M := M) Iℝ r)

/--
%%handwave
name:
  Terminal-open constant scalar multiplication is scalar multiplication on forms
statement:
  In degree \(n\), the terminal-open cochain endomorphism associated to a
  real number \(r\) sends a smooth form \(\omega\) to \(r\omega\).
proof:
  Unfold the evaluated presheaf endomorphism.  It is multiplication by the
  constant function \(r\), which is pointwise scalar multiplication on forms.
-/
theorem smoothFormsAddPresheafTopCochainComplexScalarEnd_f_apply
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (r : ℝ)
    (omega : SmoothForms (I := Iℝ)
      (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) :
    AddCommGrpCat.Hom.hom
        ((smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r).f n)
        omega = r • omega := by
  apply DifferentialForm.ext
  intro x
  ext v
  change r • omega.toFun x v = ((r • omega).toFun x) v
  rfl

/--
%%handwave
name:
  Terms of the top-open presheaf de Rham complex
statement:
  The \(n\)-th term of the top-open presheaf de Rham complex is the group of
  smooth \(n\)-forms on the whole space, viewed as the top open subset.
proof:
  This is the definition of the additive presheaf of smooth forms evaluated
  on the terminal open subset.
-/
@[simp]
theorem smoothFormsAddPresheafTopCochainComplex_X [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] (n : ℕ) :
    (smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).X n =
      AddCommGrpCat.of
        (SmoothForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) := by
  rfl

/--
%%handwave
name:
  Differential of the top-open presheaf de Rham complex
statement:
  The differential from degree \(n\) to \(n+1\) in the top-open presheaf de
  Rham complex is the exterior derivative on the whole space, viewed as the
  top open subset.
proof:
  This is the defining presheaf differential, evaluated on the terminal open
  subset.
-/
@[simp]
theorem smoothFormsAddPresheafTopCochainComplex_d_succ [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] (n : ℕ) :
    (smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).d n (n + 1) =
      ((CategoryTheory.evaluation
        (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ
        AddCommGrpCat.{max v m}).obj
          (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        ).map ((smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d n (n + 1)) := by
  rfl

/--
%%handwave
name:
  The terminal-open differential is exterior differentiation
statement:
  Applying the degree \(n\) differential of the top-open presheaf de Rham
  complex to a global \(n\)-form gives its exterior derivative.
proof:
  Unfold the additive presheaf de Rham complex and the evaluation at the
  terminal open subset.
-/
theorem smoothFormsAddPresheafTopCochainComplex_d_succ_apply [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] (n : ℕ)
    (omega : SmoothForms (I := Iℝ)
      (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) :
    AddCommGrpCat.Hom.hom
        ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).d n (n + 1))
        omega =
      exteriorDerivative (I := Iℝ) (r := ∞) omega := by
  simp [smoothFormsAddPresheafTopCochainComplex,
    smoothFormsAddPresheafCochainComplex, smoothFormsPresheafCochainComplex,
    deRhamDifferentialPresheafNatTrans, smoothFormsPresheaf,
    Functor.mapHomologicalComplex_obj_d]
  change
    (deRhamDifferential (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        (A := ℝ) n) omega =
      exteriorDerivative (I := Iℝ) (r := ∞) omega
  exact deRhamDifferential_apply
    (I := Iℝ)
    (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
    (A := ℝ) omega

/--
%%handwave
name:
  Terminal-open sections of the sheaf de Rham complex
statement:
  Evaluating the sheaf de Rham complex on the terminal open subset gives a
  cochain complex of abelian groups.
proof:
  Apply the sections functor at the whole space to the sheaf de Rham complex.
-/
noncomputable def smoothFormsAddSheafTopSectionsCochainComplex
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    CochainComplex AddCommGrpCat.{max v m} ℕ :=
  ((((CategoryTheory.sheafSections
      (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}).obj
        (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))))
    ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (smoothFormsAddSheafCochainComplex (M := M) Iℝ)

/--
%%handwave
name:
  Global sections are terminal-open sheaf sections
statement:
  The global-sections complex of the sheaf de Rham complex is isomorphic to
  the complex obtained by evaluating the sheaf de Rham complex on the whole
  space.
proof:
  The category of open subsets has the whole space as a terminal object.
  Mathlib identifies sheaf global sections with evaluation on a terminal
  object; applying this natural isomorphism degreewise gives the complex
  isomorphism.
-/
noncomputable def smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopSectionsCochainComplex
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ ≅
      smoothFormsAddSheafTopSectionsCochainComplex (M := M) Iℝ := by
  letI : HasTerminal (TopologicalSpace.Opens (TopCat.of M : TopCat.{m})) :=
    (CategoryTheory.Limits.isTerminalTop
      (α := TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))).hasTerminal
  let e : CategoryTheory.Sheaf.Γ
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m} ≅
      (CategoryTheory.sheafSections
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}).obj
        (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}
      (T := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
      (CategoryTheory.Limits.isTerminalTop
        (α := TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
  exact (NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).app
    (smoothFormsAddSheafCochainComplex (M := M) Iℝ)

/--
%%handwave
name:
  Terminal sheaf sections are top-open presheaf sections
statement:
  The terminal-open sections complex of the sheaf de Rham complex is
  isomorphic to the complex obtained by evaluating the underlying presheaf
  de Rham complex on the whole space.
proof:
  The sheaf of smooth forms was defined from the smooth-form presheaf, and
  the sheaf differential was defined from the presheaf exterior derivative.
  Evaluating at the terminal open subset therefore gives the same terms and
  differentials as the top-open presheaf complex.
-/
noncomputable def smoothFormsAddSheafTopSectionsCochainComplexIsoPresheafTopCochainComplex
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    smoothFormsAddSheafTopSectionsCochainComplex (M := M) Iℝ ≅
      smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ := by
  refine HomologicalComplex.Hom.isoOfComponents (C₁ :=
    smoothFormsAddSheafTopSectionsCochainComplex (M := M) Iℝ) (C₂ :=
    smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ) (fun n => ?_) ?_
  · change
      AddCommGrpCat.of
          (SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) ≅
        AddCommGrpCat.of
          (SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n)
    exact Iso.refl _
  · intro i j hij
    have hij' : i + 1 = j := by
      simpa [ComplexShape.up, ComplexShape.up'] using hij
    subst j
    change
      (𝟙
          (AddCommGrpCat.of
            (SmoothForms (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ i))) ≫
          (smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).d i (i + 1) =
        (smoothFormsAddSheafTopSectionsCochainComplex (M := M) Iℝ).d i (i + 1) ≫
          (𝟙
            (AddCommGrpCat.of
              (SmoothForms (I := Iℝ)
                (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ (i + 1))))
    simp [smoothFormsAddSheafTopSectionsCochainComplex,
      smoothFormsAddPresheafTopCochainComplex,
      smoothFormsAddSheafCochainComplex_d_succ,
      deRhamDifferentialAddSheafHom_hom]
    exact (Category.comp_id
      (((smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d i (i + 1)).app
        (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))))).symm

/--
%%handwave
name:
  Global sheaf sections are top-open presheaf sections
statement:
  The global-sections complex of the sheaf de Rham complex is isomorphic to
  the complex obtained by evaluating the presheaf de Rham complex on the
  terminal open subset.
proof:
  Compose [the global-sections-to-terminal-sections isomorphism](lean:JJMath.Manifold.smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopSectionsCochainComplex) with [the identification of terminal sheaf sections with top-open presheaf sections](lean:JJMath.Manifold.smoothFormsAddSheafTopSectionsCochainComplexIsoPresheafTopCochainComplex).
-/
noncomputable def smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ ≅
      smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ :=
  (smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopSectionsCochainComplex
    (M := M) Iℝ).trans
    (smoothFormsAddSheafTopSectionsCochainComplexIsoPresheafTopCochainComplex
      (M := M) Iℝ)

/--
%%handwave
name:
  Global sections and top-open sections preserve constant scalar multiplication
statement:
  The isomorphism from the global-sections de Rham complex to the top-open
  presheaf de Rham complex intertwines constant scalar multiplication on the
  two complexes.
proof:
  Check each degree.  The global-sections-to-terminal-sections part is
  natural in the sheaf, and the terminal sheaf sections are the same
  presheaf sections by construction of the smooth-form sheaf.
-/
theorem smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex_hom_comp_scalarEnd
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (r : ℝ) :
    (smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex
        (M := M) Iℝ).hom ≫
      smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r =
    (((CategoryTheory.Sheaf.Γ
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
        (smoothFormsAddSheafCochainComplexScalarEnd (M := M) Iℝ r)) ≫
      (smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex
        (M := M) Iℝ).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  let T : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}) := ⊤
  let e : CategoryTheory.Sheaf.Γ
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m} ≅
      (CategoryTheory.sheafSections
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}).obj (Opposite.op T) :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}
      (T := T)
      (CategoryTheory.Limits.isTerminalTop
        (α := TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
  let f : smoothFormsAddSheaf (M := M) Iℝ n ⟶
      smoothFormsAddSheaf (M := M) Iℝ n :=
    smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ n
      (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r)
  have hnat :
      ((CategoryTheory.Sheaf.Γ
          (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
          AddCommGrpCat.{max v m}).map f) ≫
        e.hom.app (smoothFormsAddSheaf (M := M) Iℝ n) =
      e.hom.app (smoothFormsAddSheaf (M := M) Iℝ n) ≫
        ((CategoryTheory.sheafSections
          (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
          AddCommGrpCat.{max v m}).obj (Opposite.op T)).map f := by
    simpa [e] using e.hom.naturality f
  simpa [T, e, f,
    smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex,
    smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopSectionsCochainComplex,
    smoothFormsAddSheafTopSectionsCochainComplexIsoPresheafTopCochainComplex,
    smoothFormsAddPresheafTopCochainComplexScalarEnd,
    smoothFormsAddSheafCochainComplexScalarEnd,
    smoothFormsAddPresheafCochainComplexScalarEnd,
    smoothFormsPointwiseSMulAddSheafHom,
    Category.assoc] using hnat.symm

/--
%%handwave
name:
  Constants as smooth zero-forms on an open set
statement:
  A real constant determines a smooth zero-form on every open subset by the
  corresponding constant function.
proof:
  Use the smooth constant function and then regard a smooth function as a
  zero-form.
-/
noncomputable def realConstantZeroForm [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (U : TopologicalSpace.Opens M) (c : ULift.{max v m} ℝ) :
    SmoothForms (I := Iℝ) (M := U) ℝ 0 :=
  smoothRealFunctionToZeroForm (I0 := Iℝ) (M0 := U)
    (smoothRealConstantFunction (I0 := Iℝ) (M0 := U) c.down)

/--
%%handwave
name:
  Constant zero-forms vanish only for the zero constant
statement:
  On a nonempty open set, the zero-form attached to a real constant is zero
  if and only if the constant is zero.
proof:
  Evaluate the equality of zero-forms at one point of the open set and then
  evaluate the resulting alternating map on the unique empty tuple of tangent
  vectors.  This recovers the original real constant.
-/
@[simp]
theorem realConstantZeroForm_eq_zero_iff [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (U : TopologicalSpace.Opens M) [Nonempty U] (c : ULift.{max v m} ℝ) :
    realConstantZeroForm (M := M) Iℝ U c = 0 ↔ c = 0 := by
  constructor
  · intro h
    rcases c with ⟨r⟩
    rcases (inferInstance : Nonempty U) with ⟨x⟩
    have hfun :
        (realConstantZeroForm (M := M) Iℝ U (ULift.up r)).toFun x =
          (0 : SmoothForms (I := Iℝ) (M := U) ℝ 0).toFun x := by
      exact congrArg (fun omega : SmoothForms (I := Iℝ) (M := U) ℝ 0 => omega.toFun x) h
    have hval :=
      congrArg
        (fun eta : (TangentSpace Iℝ x [⋀^Fin 0]→L[ℝ] ℝ) =>
          eta (fun i : Fin 0 => False.elim i.elim0)) hfun
    have hr : r = 0 := by
      simpa [realConstantZeroForm, smoothRealFunctionToZeroForm,
        smoothRealConstantFunction] using hval
    ext
    exact hr
  · intro h
    rw [h]
    apply DifferentialForm.ext
    intro x
    ext v
    rfl

/--
%%handwave
name:
  Constant zero-forms have zero differential on open sets
statement:
  On every open subset, the de Rham differential of the zero-form associated
  to a real constant is zero.
proof:
  This is [the fact that constant zero-forms are closed](lean:JJMath.Manifold.deRhamDifferential_smoothRealFunctionToZeroForm_const).
-/
@[simp]
theorem deRhamDifferential_realConstantZeroForm [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (U : TopologicalSpace.Opens M) (c : ULift.{max v m} ℝ) :
    deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) 0
      (realConstantZeroForm (M := M) Iℝ U c) = 0 := by
  simpa [realConstantZeroForm] using
    deRhamDifferential_smoothRealFunctionToZeroForm_const
      (I0 := Iℝ) (M0 := U) c.down

/--
%%handwave
name:
  Closed model-open zero-forms have zero scalar derivative
statement:
  Let a zero-form be defined on an open subset of a finite-dimensional real
  normed vector space.  If its exterior derivative vanishes, then the
  Fréchet derivative, within the open subset, of its scalar coefficient is
  zero at every point.
proof:
  On model opens the exterior derivative is the model-space exterior
  derivative of the coefficient field.  In degree zero, the coefficient field
  is a scalar-valued function viewed through the canonical identification of
  scalars with alternating maps on the empty set.  The formula for the
  exterior derivative of such a zero-form identifies it with the one-form
  associated to the Fréchet derivative of the scalar coefficient.  Since this
  one-form is zero, the derivative is zero.
-/
theorem modelOpen_closed_zeroForm_scalar_fderivWithin_eq_zero
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [FiniteDimensional ℝ E0]
    (U : TopologicalSpace.Opens E0)
    (omega : SmoothForms (I := 𝓘(ℝ, E0)) (M := U) ℝ 0)
    (hclosed :
      deRhamDifferential (I := 𝓘(ℝ, E0)) (M := U) (A := ℝ) 0 omega = 0)
    (x : U) :
    fderivWithin ℝ
      (fun y : E0 =>
        ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E0 ℝ (Fin 0)).symm
          (modelOpenFormCoeffExtension (E := E0) U 0
            (fun z ↦ smoothFormModelCoeff (E := E0) U 0 omega z) y)))
      (U : Set E0) (x : E0) = 0 := by
  let coeff : E0 → E0 [⋀^Fin 0]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E0) U 0
      (fun z ↦ smoothFormModelCoeff (E := E0) U 0 omega z)
  let scalar : E0 → ℝ :=
    fun y ↦
      ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E0 ℝ (Fin 0)).symm
        (coeff y))
  have hcoeff :
      coeff = fun y : E0 =>
        ContinuousAlternatingMap.constOfIsEmpty ℝ E0 (Fin 0) (scalar y) := by
    funext y
    exact
      ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E0 ℝ (Fin 0)).right_inv
        (coeff y)).symm
  have hDcoeff :
      extDerivWithin coeff (U : Set E0) (x : E0) = 0 := by
    have hpoint :
        ((deRhamDifferential (I := 𝓘(ℝ, E0)) (M := U) (A := ℝ) 0 omega).toFun x :
            E0 [⋀^Fin 1]→L[ℝ] ℝ) = 0 := by
      rw [hclosed]
      rfl
    have hmodel :=
      deRhamDifferential_modelOpen_toFun (E := E0) U 0 omega x
    exact hmodel.symm.trans hpoint
  have hDscalar :
      extDerivWithin
          (fun y : E0 =>
            ContinuousAlternatingMap.constOfIsEmpty ℝ E0 (Fin 0) (scalar y))
          (U : Set E0) (x : E0) = 0 := by
    simpa [hcoeff] using hDcoeff
  have hformula :=
    extDerivWithin_constOfIsEmpty (𝕜 := ℝ) (E := E0) (F := ℝ)
      (f := scalar) (s := (U : Set E0)) (x := (x : E0))
      (U.2.uniqueDiffWithinAt x.2)
  have hone :
      ContinuousAlternatingMap.ofSubsingleton ℝ E0 ℝ (0 : Fin 1)
          (fderivWithin ℝ scalar (U : Set E0) (x : E0)) = 0 := by
    simpa [hformula] using hDscalar
  have hlin :=
    congrArg
      ((ContinuousAlternatingMap.ofSubsingleton ℝ E0 ℝ (0 : Fin 1)).symm)
      hone
  simpa [scalar, coeff] using hlin

/--
%%handwave
name:
  Closed model-open zero-forms are constant on convex subopens
statement:
  Let a closed smooth zero-form be defined on an open subset of a
  finite-dimensional real normed vector space.  On any nonempty convex open
  subdomain, its restriction is the zero-form associated to a single real
  constant.
proof:
  Apply the scalar derivative statement to the scalar coefficient of the
  zero-form.  The coefficient is differentiable on the open set, and its
  derivative vanishes on the convex subdomain.  The mean-value theorem on
  convex sets makes the coefficient constant there.  Extensionality for
  zero-forms identifies the restricted zero-form with the constant zero-form.
-/
theorem modelOpen_closed_zeroForm_eq_realConstantZeroForm_on_convex
    {E0 : Type v} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [FiniteDimensional ℝ E0]
    (U V : TopologicalSpace.Opens E0) (hVU : V ≤ U)
    (hconvex : Convex ℝ (V : Set E0)) (hne : (V : Set E0).Nonempty)
    (omega : SmoothForms (I := 𝓘(ℝ, E0)) (M := U) ℝ 0)
    (hclosed :
      deRhamDifferential (I := 𝓘(ℝ, E0)) (M := U) (A := ℝ) 0 omega = 0) :
    ∃ c : ULift.{v} ℝ,
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, E0)) (M := E0) (A := ℝ)
          hVU 0 omega =
        realConstantZeroForm (M := E0) 𝓘(ℝ, E0) V c := by
  let coeff : E0 → E0 [⋀^Fin 0]→L[ℝ] ℝ :=
    modelOpenFormCoeffExtension (E := E0) U 0
      (fun z ↦ smoothFormModelCoeff (E := E0) U 0 omega z)
  let L : (E0 [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    { toFun := fun eta ↦ eta 0
      map_add' := by
        intro eta theta
        simp
      map_smul' := by
        intro c eta
        simp
      cont :=
        (ContinuousAlternatingMap.uniformContinuous_eval_const (𝕜 := ℝ)
          (E := E0) (F := ℝ) (x := (0 : Fin 0 → E0))).continuous }
  let scalar : E0 → ℝ := fun y ↦ L (coeff y)
  have hscalar_smooth :
      ContDiffOn ℝ ∞ scalar (U : Set E0) := by
    have hcoeff_smooth :=
      contDiffOn_smoothFormModelCoeff_modelOpen (E := E0) U 0 omega
    simpa [scalar, coeff, L, Function.comp_def] using
      hcoeff_smooth.continuousLinearMap_comp L
  have hscalar_diff : DifferentiableOn ℝ scalar (V : Set E0) :=
    (hscalar_smooth.differentiableOn (by simp)).mono hVU
  have hscalar_deriv :
      ∀ y ∈ (V : Set E0), fderivWithin ℝ scalar (V : Set E0) y = 0 := by
    intro y hy
    have hyU : y ∈ (U : Set E0) := hVU hy
    have hUzero :
        fderivWithin ℝ scalar (U : Set E0) y = 0 := by
      simpa [scalar, coeff, L] using
        modelOpen_closed_zeroForm_scalar_fderivWithin_eq_zero
          (E0 := E0) U omega hclosed ⟨y, hyU⟩
    calc
      fderivWithin ℝ scalar (V : Set E0) y = fderiv ℝ scalar y :=
        fderivWithin_of_isOpen V.2 hy
      _ = fderivWithin ℝ scalar (U : Set E0) y :=
        (fderivWithin_of_isOpen U.2 hyU).symm
      _ = 0 := hUzero
  rcases hne with ⟨y₀, hy₀⟩
  let c : ULift.{v} ℝ := ULift.up (scalar y₀)
  refine ⟨c, ?_⟩
  apply DifferentialForm.ext
  intro x
  ext v
  have hxV : (x : E0) ∈ (V : Set E0) := x.2
  have hxU : (x : E0) ∈ (U : Set E0) := hVU hxV
  have hconst :
      scalar (x : E0) = scalar y₀ :=
    hconvex.is_const_of_fderivWithin_eq_zero hscalar_diff hscalar_deriv hxV hy₀
  have hy₀U : y₀ ∈ (U : Set E0) := hVU hy₀
  have hleft :
      (omega.toFun (TopologicalSpace.Opens.inclusion hVU x))
          ((mfderiv 𝓘(ℝ, E0) 𝓘(ℝ, E0)
              (TopologicalSpace.Opens.inclusion hVU) x) ∘ v) =
        scalar (x : E0) := by
    have hpoint :
        TopologicalSpace.Opens.inclusion hVU x = (⟨(x : E0), hxU⟩ : U) :=
      Subtype.ext rfl
    have hcoeffx :
        coeff (x : E0) = omega.toFun (⟨(x : E0), hxU⟩ : U) := by
      dsimp [coeff, modelOpenFormCoeffExtension, smoothFormModelCoeff]
      rw [dif_pos hxU]
    calc
      (omega.toFun (TopologicalSpace.Opens.inclusion hVU x))
          ((mfderiv 𝓘(ℝ, E0) 𝓘(ℝ, E0)
              (TopologicalSpace.Opens.inclusion hVU) x) ∘ v)
          =
        (omega.toFun (⟨(x : E0), hxU⟩ : U)) 0 := by
          rw [hpoint]
          apply congrArg (omega.toFun (⟨(x : E0), hxU⟩ : U))
          exact Subsingleton.elim _ _
      _ = L (coeff (x : E0)) := by
          rw [hcoeffx]
          rfl
      _ = scalar (x : E0) := rfl
  calc
    (restrictSmoothFormsOfLE (I := 𝓘(ℝ, E0)) (M := E0) (A := ℝ)
        hVU 0 omega).toFun x v
        = scalar (x : E0) := by
          simpa [restrictSmoothFormsOfLE, restrictSmoothFormOfLE] using hleft
    _ = scalar y₀ := hconst
    _ = (realConstantZeroForm (M := E0) 𝓘(ℝ, E0) V c).toFun x v := by
          simp [realConstantZeroForm, smoothRealFunctionToZeroForm,
            smoothRealConstantFunction, c]

/--
%%handwave
name:
  Pullback preserves constant zero-forms
statement:
  Pulling back a constant zero-form along a diffeomorphism gives the constant
  zero-form with the same value on the source.
proof:
  Evaluate at a point.  In degree zero there is only the empty tuple of tangent
  vectors, so composing with the derivative of the diffeomorphism has no
  effect on the constant alternating form.
-/
theorem smoothFormsPullbackDiffeomorph_realConstantZeroForm
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens E)
    (φ : U ≃ₘ⟮Iℝ, 𝓘(ℝ, E)⟯ V)
    (c : ULift.{max v m} ℝ) :
    smoothFormsPullbackDiffeomorph Iℝ (𝓘(ℝ, E)) φ 0
        (realConstantZeroForm (M := E) 𝓘(ℝ, E) V
          (ULift.up c.down : ULift.{v} ℝ)) =
      realConstantZeroForm (M := M) Iℝ U c := by
  apply DifferentialForm.ext
  intro x
  ext v
  simp [smoothFormsPullbackDiffeomorph, smoothFormPullbackDiffeomorph,
    smoothDifferentialFormPullbackDiffeomorph, realConstantZeroForm,
    smoothRealFunctionToZeroForm, smoothRealConstantFunction]

/--
%%handwave
name:
  Constants form an additive map to zero-forms
statement:
  On each open subset, sending a real constant to the corresponding smooth
  zero-form is a homomorphism of abelian groups.
proof:
  Evaluate at each point and on the unique empty tuple of tangent vectors.
-/
noncomputable def realConstantToZeroFormsAddHom [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (U : TopologicalSpace.Opens M) :
    AddCommGrpCat.of (ULift.{max v m} ℝ) ⟶
      (smoothFormsAddPresheaf (M := M) Iℝ 0).obj (Opposite.op U) :=
  AddCommGrpCat.ofHom
    { toFun := realConstantZeroForm (M := M) Iℝ U
      map_zero' := by
        apply DifferentialForm.ext
        intro x
        ext v
        rfl
      map_add' := by
        intro a b
        apply DifferentialForm.ext
        intro x
        ext v
        rfl }

/--
%%handwave
name:
  Constants define a presheaf map to smooth zero-forms
statement:
  The maps sending a real constant to the corresponding constant zero-form on
  each open subset commute with restriction, hence define a morphism from the
  constant presheaf to the presheaf of smooth zero-forms.
proof:
  Restricting a constant zero-form along an inclusion is again the same
  constant zero-form.
-/
noncomputable def realConstantAddPresheafToSmoothFormsAddPresheaf [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] :
    ((Functor.const (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{max v m} ℝ))) ⟶
      smoothFormsAddPresheaf (M := M) Iℝ 0 where
  app U := realConstantToZeroFormsAddHom (M := M) Iℝ U.unop
  naturality {U V} f := by
    ext c
    apply DifferentialForm.ext
    intro x
    ext v
    rfl

/--
%%handwave
name:
  Constants map to closed zero-forms at the presheaf level
statement:
  The presheaf morphism from constants to smooth zero-forms has zero composite
  with exterior differentiation.
proof:
  Check on every open set and every constant; the resulting smooth zero-form is
  closed.
-/
theorem realConstantAddPresheafToSmoothFormsAddPresheaf_comp_d [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] :
    realConstantAddPresheafToSmoothFormsAddPresheaf (M := M) Iℝ ≫
        (smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d 0 1 =
      0 := by
  ext U c
  apply DifferentialForm.ext
  intro x
  ext v
  simpa [realConstantAddPresheafToSmoothFormsAddPresheaf,
    realConstantToZeroFormsAddHom, smoothFormsAddPresheafCochainComplex,
    smoothFormsPresheafCochainComplex, deRhamDifferentialPresheafNatTrans] using
    congrArg (fun omega : SmoothForms (I := Iℝ) (M := U.unop) ℝ 1 =>
      omega.toFun x v)
      (deRhamDifferential_realConstantZeroForm (M := M) Iℝ U.unop c)

/--
%%handwave
name:
  The constant real sheaf in the smooth-form universe
statement:
  In the coefficient universe used by the sheaves of smooth forms, the
  constant real sheaf is the sheafification of the constant abelian group
  \(\mathbb R\).
proof:
  Apply the constant-sheaf functor for abelian groups to the universe-lifted
  additive group of real numbers.
-/
abbrev realConstantAddSheafSmoothFormsUniverse (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m} :=
  (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{max v m}).obj
      (AddCommGrpCat.of (ULift.{max v m} ℝ))

/--
%%handwave
name:
  Scalar endomorphisms of the smooth-universe constant real sheaf
statement:
  Multiplication by a real number induces an endomorphism of the constant real
  sheaf in the coefficient universe used for smooth forms.
proof:
  Apply the constant-sheaf functor to the additive homomorphism
  \(x\mapsto rx\), with coefficients placed in the smooth-form universe.
-/
noncomputable def realConstantAddSheafSmoothFormsUniverseScalarEnd (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    (r : ℝ) :
    realConstantAddSheafSmoothFormsUniverse X ⟶
      realConstantAddSheafSmoothFormsUniverse X :=
  (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{max v m}).map
    (AddCommGrpCat.ofHom
      (JJMath.Cohomology.realULiftScalarAddMonoidHom.{max v m} r))

/--
%%handwave
name:
  Iterated universe lifts of the real additive group agree
statement:
  The additive group obtained by first placing \(\mathbb R\) in the manifold
  universe and then applying the smooth-form universe lift is canonically
  isomorphic to the additive group obtained by placing \(\mathbb R\) directly
  in the smooth-form coefficient universe.
proof:
  Send an iterated lift to the same real number in the single larger lift, and
  use the inverse operation in the other direction.  Both additive laws are
  definitionally inherited from \(\mathbb R\).
-/
def realULiftULiftAddEquiv : ULift.{v} (ULift.{m} ℝ) ≃+ ULift.{max v m} ℝ where
  toFun x := ULift.up x.down.down
  invFun x := ULift.up (ULift.up x.down)
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl
  map_add' x y := by
    cases x
    cases y
    rfl

/--
%%handwave
name:
  Iterated universe lifts of the integer additive group agree
statement:
  The additive group obtained by first placing \(\mathbb Z\) in the manifold
  universe and then applying the smooth-form universe lift is canonically
  isomorphic to the additive group obtained by placing \(\mathbb Z\) directly
  in the smooth-form coefficient universe.
proof:
  Send an iterated lift to the same integer in the single larger lift, and use
  the inverse operation in the other direction.
-/
def intULiftULiftAddEquiv : ULift.{v} (ULift.{m} ℤ) ≃+ ULift.{max v m} ℤ where
  toFun x := ULift.up x.down.down
  invFun x := ULift.up (ULift.up x.down)
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl
  map_add' x y := by
    cases x
    cases y
    rfl

/--
%%handwave
name:
  The constant sheaf maps to smooth zero-forms
statement:
  The constant real sheaf maps canonically to the sheaf of smooth zero-forms by
  sending a locally constant real section to the associated smooth zero-form.
proof:
  Sheafify the presheaf morphism from constants to smooth zero-forms and use
  the fact that smooth zero-forms already form a sheaf.
-/
noncomputable def realConstantAddSheafToSmoothFormsAddSheaf [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    realConstantAddSheafSmoothFormsUniverse (TopCat.of M : TopCat.{m}) ⟶
      smoothFormsAddSheaf (M := M) Iℝ 0 :=
  ObjectProperty.homMk
    (CategoryTheory.sheafifyLift
      (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      (realConstantAddPresheafToSmoothFormsAddPresheaf (M := M) Iℝ)
      (smoothFormsAddSheaf (M := M) Iℝ 0).property)

/--
%%handwave
name:
  Constants map to closed zero-forms at the sheaf level
statement:
  The morphism from the constant real sheaf to smooth zero-forms has zero
  composite with exterior differentiation.
proof:
  By the universal property of sheafification, it is enough to check after
  precomposing with the sheafification map from the constant presheaf.  This
  reduces to the presheaf-level statement that constant zero-forms are closed.
-/
theorem realConstantAddSheafToSmoothFormsAddSheaf_comp_d [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ ≫
        deRhamDifferentialAddSheafHom (M := M) Iℝ 0 =
      0 := by
  apply Sheaf.hom_ext
  let J := Opens.grothendieckTopology (TopCat.of M : TopCat.{m})
  let P : (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ ⥤
      AddCommGrpCat.{max v m} :=
    ((Functor.const (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max v m} ℝ)))
  let Q0 : (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ ⥤
      AddCommGrpCat.{max v m} :=
    smoothFormsAddPresheaf (M := M) Iℝ 0
  let Q1 : (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ ⥤
      AddCommGrpCat.{max v m} :=
    smoothFormsAddPresheaf (M := M) Iℝ 1
  let η : P ⟶ Q0 := realConstantAddPresheafToSmoothFormsAddPresheaf (M := M) Iℝ
  let δ : Q0 ⟶ Q1 := (smoothFormsAddPresheafCochainComplex (M := M) Iℝ).d 0 1
  change CategoryTheory.sheafifyLift J η
      (smoothFormsAddSheaf (M := M) Iℝ 0).property ≫ δ = 0
  apply CategoryTheory.sheafify_hom_ext J
  · exact (smoothFormsAddSheaf (M := M) Iℝ 1).property
  · simpa [η, δ] using
      realConstantAddPresheafToSmoothFormsAddPresheaf_comp_d (M := M) Iℝ

/--
%%handwave
name:
  The constant-to-zero-forms presheaf map preserves scalar multiplication
statement:
  On the constant presheaf, multiplying a constant by \(r\) and then viewing it
  as a smooth zero-form agrees with first viewing it as a zero-form and then
  multiplying that zero-form by the constant smooth function \(r\).
proof:
  Evaluate on an open set, a real constant, a point, and the unique tangent
  input of a zero-form.
-/
theorem realConstantAddPresheafToSmoothFormsAddPresheaf_comp_scalarEnd
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (r : ℝ) :
    realConstantAddPresheafToSmoothFormsAddPresheaf (M := M) Iℝ ≫
        smoothFormsPointwiseSMulAddPresheafHom (M := M) Iℝ 0
          (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r) =
      ((Functor.const
          (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ).map
        (AddCommGrpCat.ofHom
          (JJMath.Cohomology.realULiftScalarAddMonoidHom.{max v m} r))) ≫
        realConstantAddPresheafToSmoothFormsAddPresheaf (M := M) Iℝ := by
  ext U c
  apply DifferentialForm.ext
  intro x
  ext v
  change
    (r • (realConstantZeroForm (M := M) Iℝ U.unop c).toFun x) v =
      (realConstantZeroForm (M := M) Iℝ U.unop
        (ULift.up (r * c.down) : ULift.{max v m} ℝ)).toFun x v
  simp [realConstantZeroForm, smoothRealFunctionToZeroForm,
    smoothRealConstantFunction]

/--
%%handwave
name:
  The constant-to-zero-forms augmentation preserves scalar multiplication
statement:
  The canonical map from the constant real sheaf to smooth zero-forms
  intertwines scalar multiplication on the constant sheaf with multiplication
  of zero-forms by the same constant function.
proof:
  Check after pulling back to the constant presheaf.  A constant section sent
  to its associated zero-form and then multiplied by \(r\) is the same
  zero-form as first multiplying the constant section by \(r\).
tags:
  milestone
-/
theorem realConstantAddSheafToSmoothFormsAddSheaf_comp_scalarEnd [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (r : ℝ) :
    realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ ≫
      (smoothFormsAddSheafCochainComplexScalarEnd (M := M) Iℝ r).f 0 =
    realConstantAddSheafSmoothFormsUniverseScalarEnd
        (TopCat.of M : TopCat.{m}) r ≫
      realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ := by
  apply Sheaf.hom_ext
  let J := Opens.grothendieckTopology (TopCat.of M : TopCat.{m})
  let P : (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ ⥤
      AddCommGrpCat.{max v m} :=
    ((Functor.const (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max v m} ℝ)))
  let Q : (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ ⥤
      AddCommGrpCat.{max v m} :=
    smoothFormsAddPresheaf (M := M) Iℝ 0
  let η : P ⟶ Q := realConstantAddPresheafToSmoothFormsAddPresheaf (M := M) Iℝ
  let σP : P ⟶ P :=
    ((Functor.const
      (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ).map
        (AddCommGrpCat.ofHom
          (JJMath.Cohomology.realULiftScalarAddMonoidHom.{max v m} r)))
  let σQ : Q ⟶ Q :=
    smoothFormsPointwiseSMulAddPresheafHom (M := M) Iℝ 0
      (smoothRealConstantFunction (I0 := Iℝ) (M0 := M) r)
  change
    CategoryTheory.sheafifyLift J η
        (smoothFormsAddSheaf (M := M) Iℝ 0).property ≫ σQ =
      CategoryTheory.sheafifyMap J σP ≫
        CategoryTheory.sheafifyLift J η
          (smoothFormsAddSheaf (M := M) Iℝ 0).property
  rw [← CategoryTheory.sheafifyLift_comp (J := J) η
    (smoothFormsAddSheaf (M := M) Iℝ 0).property σQ
    (smoothFormsAddSheaf (M := M) Iℝ 0).property]
  rw [CategoryTheory.sheafifyMap_sheafifyLift]
  congr 1

universe uLift uTop

set_option backward.isDefEq.respectTransparency false in
def liftedPointGrothendieckTopology {X : Type uTop} [TopologicalSpace X] (x : X) :
    Point.{max uLift uTop} (Opens.grothendieckTopology X) where
  fiber :=
    { obj := fun U => ULift.{max uLift uTop} (PLift (x ∈ U))
      map := fun {U V} f =>
        ↾fun h : ULift.{max uLift uTop} (PLift (x ∈ U)) =>
          (⟨⟨leOfHom f h.down.down⟩⟩ :
            ULift.{max uLift uTop} (PLift (x ∈ V))) }
  isCofiltered :=
    { nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
        exact ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩, ⟨homOfLE (by simp), rfl⟩,
          ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨hU⟩⟩
    obtain ⟨V, f, hf, hV⟩ := hR x hU
    exact ⟨_, _, hf, ⟨⟨hV⟩⟩, rfl⟩

def liftedPointsGrothendieckTopology (X : Type uTop) [TopologicalSpace X] :
    ObjectProperty (Point.{max uLift uTop} (Opens.grothendieckTopology X)) :=
  ObjectProperty.ofObj liftedPointGrothendieckTopology
  deriving ObjectProperty.Small.{max uLift uTop}

lemma isConservativeFamilyOfPoints_liftedPointsGrothendieckTopology
    (X : Type uTop) [TopologicalSpace X] :
    (liftedPointsGrothendieckTopology.{uLift, uTop} X).IsConservativeFamilyOfPoints :=
  .mk' (fun U S hS x hx ↦ by
    let Φ : (liftedPointsGrothendieckTopology.{uLift, uTop} X).FullSubcategory :=
      ⟨liftedPointGrothendieckTopology.{uLift, uTop} x, ⟨x⟩⟩
    have hxΦ : Φ.obj.fiber.obj U := by
      change ULift.{max uLift uTop} (PLift (x ∈ U))
      exact ⟨⟨hx⟩⟩
    obtain ⟨V, f, hf, hVΦ, _⟩ := hS Φ hxΦ
    change ULift.{max uLift uTop} (PLift (x ∈ V)) at hVΦ
    have hV : x ∈ V := hVΦ.down.down
    exact ⟨V, f, hf, hV⟩)

theorem sheaf_exact_iff_sheafFiber_map_exact_of_conservativePoints
    {X : Type m} [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    {P : ObjectProperty (Point.{max v m} (Opens.grothendieckTopology (TopCat.of X : TopCat.{m})))}
    (hP : P.IsConservativeFamilyOfPoints)
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of X : TopCat.{m}))
      AddCommGrpCat.{max v m})) :
    S.Exact ↔
      ∀ Φ : P.FullSubcategory,
        (S.map (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m}))).Exact := by
  constructor
  · intro h Φ
    haveI : (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).PreservesHomology := by
      haveI : (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).Additive := by
        infer_instance
      haveI : PreservesFiniteLimits (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})) := by
        infer_instance
      haveI : PreservesFiniteColimits (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})) := by
        infer_instance
      have hlim : PreservesFiniteLimits (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})) ∧
          PreservesFiniteColimits (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})) :=
        ⟨inferInstance, inferInstance⟩
      exact ((Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).exact_tfae.out 3 2).mp hlim
    have hpres : (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).PreservesHomology :=
      inferInstance
    have hexactPres :
        ∀ T : ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of X : TopCat.{m}))
          AddCommGrpCat.{max v m}),
          T.Exact → (T.map (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m}))).Exact :=
      ((Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).exact_tfae.out 2 1).mp hpres
    exact hexactPres S h
  · intro h
    simp_rw [ShortComplex.exact_iff_isZero_homology] at h
    rw [ShortComplex.exact_iff_isZero_homology]
    rw [show IsZero S.homology ↔
        ∀ Φ : P.FullSubcategory,
          IsZero ((Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).obj S.homology) by
      constructor
      · intro hS Φ
        exact Functor.map_isZero _ hS
      · intro hS
        let f : S.homology ⟶ 0 :=
          (isZero_zero (Sheaf (Opens.grothendieckTopology (TopCat.of X : TopCat.{m}))
            AddCommGrpCat.{max v m})).from_ S.homology
        have hf : IsIso f := by
          rw [(hP.jointlyReflectIsomorphisms AddCommGrpCat.{max v m}).isIso_iff]
          intro Φ
          exact isIso_of_source_target_iso_zero _
            (hS Φ).isoZero
            ((Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).map_isZero
              (isZero_zero _)).isoZero
        exact (isZero_zero _).of_iso (asIso f)]
    intro Φ
    haveI : (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).PreservesHomology := by
      haveI : (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).Additive := by
        infer_instance
      haveI : PreservesFiniteLimits (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})) := by
        infer_instance
      haveI : PreservesFiniteColimits (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})) := by
        infer_instance
      have hlim : PreservesFiniteLimits (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})) ∧
          PreservesFiniteColimits (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})) :=
        ⟨inferInstance, inferInstance⟩
      exact ((Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m})).exact_tfae.out 3 2).mp hlim
    exact (h Φ).of_iso
      (ShortComplex.mapHomologyIso S (Φ.obj.sheafFiber (A := AddCommGrpCat.{max v m}))).symm

/--
%%handwave
name:
  Closed zero-forms are locally constant
statement:
  If a smooth zero-form is defined near a point and has vanishing exterior
  derivative there, then after shrinking to a smaller neighborhood of the
  point it is the zero-form associated to a real constant.
proof:
  Work in a connected coordinate neighborhood.  In coordinates the vanishing
  exterior derivative says that the derivative of the associated smooth
  function is zero.  The mean-value theorem then shows that the function is
  constant on the coordinate ball, and this constant gives the required
  zero-form.
tags:
  milestone
-/
theorem closed_zeroForm_eq_realConstantZeroForm_near_liftedPoint
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    (x : M) (W : TopologicalSpace.Opens M)
    (hxWΦ : (liftedPointGrothendieckTopology.{v, m} x).fiber.obj W)
    (omega : SmoothForms (I := Iℝ) (M := W) ℝ 0)
    (hclosed :
      deRhamDifferential (I := Iℝ) (M := W) (A := ℝ) 0 omega = 0) :
    ∃ (U : TopologicalSpace.Opens M) (hUW : U ≤ W)
      (_hxUΦ : (liftedPointGrothendieckTopology.{v, m} x).fiber.obj U)
      (c : ULift.{max v m} ℝ),
      restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ) hUW 0 omega =
        realConstantZeroForm (M := M) Iℝ U c := by
  have hxW : x ∈ (W : Set M) := by
    change ULift.{max v m} (PLift (x ∈ W)) at hxWΦ
    exact hxWΦ.down.down
  rcases deRham_boundarylessModel_exists_convex_extendedChart_restriction_subordinate
      (M := M) Iℝ x W hxW with
    ⟨e, U, V, he, hxU, hUW, hconvex, hne, hU, hV⟩
  rcases
    deRham_boundarylessExtendedChart_restriction_diffeomorph
      (M := M) Iℝ e he U V hU hV with
    ⟨φ⟩
  let omegaU : SmoothForms (I := Iℝ) (M := U) ℝ 0 :=
    restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ) hUW 0 omega
  have hclosedU :
      deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) 0 omegaU = 0 := by
    have hnat :=
      deRhamDifferential_restrictSmoothFormsOfLE
        (I := Iℝ) (M := M) (A := ℝ) hUW omega
    calc
      deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) 0 omegaU =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            hUW 1
            (deRhamDifferential (I := Iℝ) (M := W) (A := ℝ) 0 omega) := by
        simpa [omegaU] using hnat
      _ = 0 := by
        rw [hclosed]
        apply DifferentialForm.ext
        intro y
        ext v
        rfl
  let omegaV : SmoothForms (I := 𝓘(ℝ, E)) (M := V) ℝ 0 :=
    smoothFormsPullbackDiffeomorph (𝓘(ℝ, E)) Iℝ φ.symm 0 omegaU
  have hclosedV :
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := V) (A := ℝ) 0 omegaV = 0 := by
    change
      deRhamDifferential (I := 𝓘(ℝ, E)) (M := V) (A := ℝ) 0
          (smoothFormsPullbackDiffeomorph (𝓘(ℝ, E)) Iℝ φ.symm 0 omegaU) = 0
    rw [deRhamDifferential_smoothFormsPullbackDiffeomorph]
    rw [hclosedU]
    simp
  rcases
      modelOpen_closed_zeroForm_eq_realConstantZeroForm_on_convex
        (E0 := E) V V (le_refl V) hconvex hne omegaV hclosedV with
    ⟨cV, homegaVrestrict⟩
  let c : ULift.{max v m} ℝ := ULift.up cV.down
  have hxUΦ : (liftedPointGrothendieckTopology.{v, m} x).fiber.obj U := by
    change ULift.{max v m} (PLift (x ∈ U))
    exact ⟨⟨hxU⟩⟩
  refine ⟨U, hUW, hxUΦ, c, ?_⟩
  have homegaV :
      omegaV =
        realConstantZeroForm (M := E) 𝓘(ℝ, E) V cV := by
    simpa [restrictSmoothFormsOfLE_id] using homegaVrestrict
  have hrecover :
      smoothFormsPullbackDiffeomorph Iℝ (𝓘(ℝ, E)) φ 0 omegaV = omegaU := by
    simpa [omegaV] using
      smoothFormsPullbackDiffeomorph_comp_symm Iℝ (𝓘(ℝ, E)) φ
        (n := 0) omegaU
  calc
    restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ) hUW 0 omega = omegaU := rfl
    _ = smoothFormsPullbackDiffeomorph Iℝ (𝓘(ℝ, E)) φ 0 omegaV :=
        hrecover.symm
    _ =
        smoothFormsPullbackDiffeomorph Iℝ (𝓘(ℝ, E)) φ 0
          (realConstantZeroForm (M := E) 𝓘(ℝ, E) V cV) := by
        rw [homegaV]
    _ = realConstantZeroForm (M := M) Iℝ U c := by
        simpa [c] using
          smoothFormsPullbackDiffeomorph_realConstantZeroForm
            (M := M) Iℝ U V φ c

/--
%%handwave
name:
  Constant germs map to constant zero-form germs
statement:
  The canonical map from the constant real sheaf to smooth zero-forms sends
  the germ of a real constant over a neighborhood to the germ of the
  corresponding constant zero-form.
proof:
  Transport the presheaf constant germ through the point-fiber
  sheafification isomorphism.  The universal property of sheafification says
  that the canonical morphism to smooth zero-forms is induced by the presheaf
  map sending constants to constant zero-forms, and the point-fiber map
  respects this natural transformation.
tags:
  milestone
-/
theorem realConstantAddSheafToSmoothFormsAddSheaf_liftedPoint_const_germ
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (x : M) (U : TopologicalSpace.Opens M)
    (hxUΦ : (liftedPointGrothendieckTopology.{v, m} x).fiber.obj U)
    (c : ULift.{max v m} ℝ) :
    let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
      liftedPointGrothendieckTopology.{v, m} x
    let S : ShortComplex AddCommGrpCat.{max v m} :=
      (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
          g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
          zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
        ShortComplex
          (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
            AddCommGrpCat.{max v m})).map
        (Φ.sheafFiber (A := AddCommGrpCat.{max v m})))
    let F0 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
      (smoothFormsAddSheaf (M := M) Iℝ 0).obj
    ∃ c₀ : S.X₁, S.f c₀ =
      Φ.toPresheafFiber U hxUΦ F0 (realConstantZeroForm (M := M) Iℝ U c) := by
  let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
    liftedPointGrothendieckTopology.{v, m} x
  let S : ShortComplex AddCommGrpCat.{max v m} :=
    (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
        g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
        zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
      ShortComplex
        (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
          AddCommGrpCat.{max v m})).map
      (Φ.sheafFiber (A := AddCommGrpCat.{max v m})))
  let F0 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ 0).obj
  let J := Opens.grothendieckTopology (TopCat.of M : TopCat.{m})
  let P : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    ((Functor.const (TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max v m} ℝ)))
  let Q : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    smoothFormsAddPresheaf (M := M) Iℝ 0
  let η : P ⟶ Q := realConstantAddPresheafToSmoothFormsAddPresheaf (M := M) Iℝ
  let c₀ : S.X₁ :=
    ((Φ.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max v m}).app P).inv
      (Φ.toPresheafFiber U hxUΦ P c)
  refine ⟨c₀, ?_⟩
  change
    (Φ.sheafFiber (A := AddCommGrpCat.{max v m})).map
        (realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ) c₀ =
      Φ.toPresheafFiber U hxUΦ F0 (realConstantZeroForm (M := M) Iℝ U c)
  have hcomp :
      (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
            (CategoryTheory.toSheafify J P) ≫
          (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
            (CategoryTheory.sheafifyLift J η
              (smoothFormsAddSheaf (M := M) Iℝ 0).property) =
        (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map η := by
    rw [← Functor.map_comp]
    rw [CategoryTheory.toSheafify_sheafifyLift]
  have hmap :=
    congrArg
      (fun f : (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).obj P ⟶
          (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).obj Q =>
        f (Φ.toPresheafFiber U hxUΦ P c))
      hcomp
  have hnatural :
      (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map η
          (Φ.toPresheafFiber U hxUΦ P c) =
        Φ.toPresheafFiber U hxUΦ Q (η.app (Opposite.op U) c) := by
    exact Point.toPresheafFiber_naturality_apply (Φ := Φ) η U hxUΦ c
  have hconstant :
      η.app (Opposite.op U) c = realConstantZeroForm (M := M) Iℝ U c := by
    rfl
  have hfirst :
      (Φ.sheafFiber (A := AddCommGrpCat.{max v m})).map
        (realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ) c₀
          =
        (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map η
          (Φ.toPresheafFiber U hxUΦ P c) := by
    simpa [c₀, S, P, Q, η, J, realConstantAddSheafToSmoothFormsAddSheaf,
      realConstantAddSheafSmoothFormsUniverse] using hmap
  have hsecond :
      (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map η
          (Φ.toPresheafFiber U hxUΦ P c) =
        Φ.toPresheafFiber U hxUΦ F0
          (realConstantZeroForm (M := M) Iℝ U c) := by
    rw [hnatural, hconstant]
    rfl
  exact hfirst.trans hsecond

/--
%%handwave
name:
  Locally constant representatives lift to constant germs
statement:
  If a smooth zero-form agrees near a lifted point with the zero-form attached
  to a real constant, then its germ lies in the image of the constant real
  sheaf.
proof:
  Represent the constant germ in the sheafified constant sheaf by the
  presheaf constant over the smaller neighborhood.  Naturality of point
  fibers and the defining property of sheafification identify its image with
  the germ of the corresponding constant zero-form, which is the given germ
  after restricting to the smaller neighborhood.
tags:
  milestone
-/
theorem realConstantAddSheafToSmoothFormsAddSheaf_liftedPoint_lift_of_eq_on_open
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (x : M) (W : TopologicalSpace.Opens M)
    (hxWΦ : (liftedPointGrothendieckTopology.{v, m} x).fiber.obj W)
    (omega : SmoothForms (I := Iℝ) (M := W) ℝ 0)
    (U : TopologicalSpace.Opens M) (hUW : U ≤ W)
    (hxUΦ : (liftedPointGrothendieckTopology.{v, m} x).fiber.obj U)
    (c : ULift.{max v m} ℝ)
    (homegaU :
      restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ) hUW 0 omega =
        realConstantZeroForm (M := M) Iℝ U c) :
    let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
      liftedPointGrothendieckTopology.{v, m} x
    let S : ShortComplex AddCommGrpCat.{max v m} :=
      (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
          g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
          zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
        ShortComplex
          (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
            AddCommGrpCat.{max v m})).map
        (Φ.sheafFiber (A := AddCommGrpCat.{max v m})))
    let F0 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
      (smoothFormsAddSheaf (M := M) Iℝ 0).obj
    ∃ c₀ : S.X₁, S.f c₀ = Φ.toPresheafFiber W hxWΦ F0 omega := by
  let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
    liftedPointGrothendieckTopology.{v, m} x
  let S : ShortComplex AddCommGrpCat.{max v m} :=
    (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
        g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
        zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
      ShortComplex
        (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
          AddCommGrpCat.{max v m})).map
      (Φ.sheafFiber (A := AddCommGrpCat.{max v m})))
  let F0 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ 0).obj
  rcases
      realConstantAddSheafToSmoothFormsAddSheaf_liftedPoint_const_germ
        (M := M) Iℝ x U hxUΦ c with
    ⟨c₀, hc₀⟩
  refine ⟨c₀, ?_⟩
  have hconst_to_omega :
      Φ.toPresheafFiber U hxUΦ F0
          (realConstantZeroForm (M := M) Iℝ U c) =
        Φ.toPresheafFiber W hxWΦ F0 omega := by
    have htoW :=
      Point.toPresheafFiber_w_apply (Φ := Φ) (homOfLE hUW) hxUΦ F0 omega
    haveI : Subsingleton (Φ.fiber.obj W) := by
      dsimp [Φ, liftedPointGrothendieckTopology]
      infer_instance
    have htoW' :
        Φ.toPresheafFiber U hxUΦ F0
            (restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ) hUW 0 omega) =
          Φ.toPresheafFiber W hxWΦ F0 omega := by
      simpa [F0, hUW, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
        smoothFormsPresheaf, Subsingleton.elim (Φ.fiber.map (homOfLE hUW) hxUΦ) hxWΦ]
        using htoW
    simpa [homegaU] using htoW'
  exact hc₀.trans hconst_to_omega

/--
%%handwave
name:
  Closed zero-form representatives lift to constant germs
statement:
  Let a smooth zero-form be defined on an open neighborhood of a lifted
  topological point.  If its exterior derivative vanishes on that
  neighborhood, then its germ at the lifted point lies in the image of the
  constant real sheaf.
proof:
  Shrink to a connected coordinate ball.  The zero derivative condition says
  that the associated smooth real-valued function has zero Fréchet derivative
  there, hence is constant on the ball by the mean-value theorem.  The
  resulting real constant defines a local section of the constant real sheaf,
  and the sheafification map sends its germ to the original zero-form germ.
tags:
  milestone
-/
theorem realConstantAddSheafToSmoothFormsAddSheaf_liftedPoint_lift_closed_representative
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (x : M) (W : TopologicalSpace.Opens M)
    (hxWΦ : (liftedPointGrothendieckTopology.{v, m} x).fiber.obj W)
    (omega : SmoothForms (I := Iℝ) (M := W) ℝ 0)
    (hclosed :
      deRhamDifferential (I := Iℝ) (M := W) (A := ℝ) 0 omega = 0) :
    let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
      liftedPointGrothendieckTopology.{v, m} x
    let S : ShortComplex AddCommGrpCat.{max v m} :=
      (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
          g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
          zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
        ShortComplex
          (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
            AddCommGrpCat.{max v m})).map
        (Φ.sheafFiber (A := AddCommGrpCat.{max v m})))
    let F0 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
      (smoothFormsAddSheaf (M := M) Iℝ 0).obj
    ∃ c : S.X₁, S.f c = Φ.toPresheafFiber W hxWΦ F0 omega := by
  rcases closed_zeroForm_eq_realConstantZeroForm_near_liftedPoint
      (M := M) Iℝ x W hxWΦ omega hclosed with
    ⟨U, hUW, hxUΦ, c, homegaU⟩
  exact
    realConstantAddSheafToSmoothFormsAddSheaf_liftedPoint_lift_of_eq_on_open
      (M := M) Iℝ x W hxWΦ omega U hUW hxUΦ c homegaU

/--
%%handwave
name:
  Closed zero-form lifted germs lift to constant germs
statement:
  At every lifted topological point, every germ of a smooth zero-form whose
  exterior derivative germ vanishes is the image of a constant real germ.
proof:
  Represent the germ by a smooth function on a neighborhood of the point and
  shrink to a connected coordinate neighborhood.  The vanishing exterior
  derivative says that the ordinary differential of the representative is
  zero there; by the mean-value argument on connected coordinate balls the
  function is constant on a smaller neighborhood.  This constant represents a
  section of the constant real sheaf with the required germ.
tags:
  milestone
-/
theorem realConstantAddSheaf_to_smoothFormsAddSheaf_liftedPoint_lift_closed_germ
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (x : M) :
    let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
      liftedPointGrothendieckTopology.{v, m} x
    let S : ShortComplex AddCommGrpCat.{max v m} :=
      (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
          g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
          zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
        ShortComplex
          (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
            AddCommGrpCat.{max v m})).map
        (Φ.sheafFiber (A := AddCommGrpCat.{max v m})))
    ∀ η : S.X₂, S.g η = 0 → ∃ c : S.X₁, S.f c = η := by
  let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
    liftedPointGrothendieckTopology.{v, m} x
  let S : ShortComplex AddCommGrpCat.{max v m} :=
    (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
        g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
        zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
      ShortComplex
        (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
          AddCommGrpCat.{max v m})).map
      (Φ.sheafFiber (A := AddCommGrpCat.{max v m})))
  let F0 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ 0).obj
  let F1 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ 1).obj
  change ∀ η : S.X₂, S.g η = 0 → ∃ c : S.X₁, S.f c = η
  intro η hη
  have hη' :
      (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
        (deRhamDifferentialAddSheafHom (M := M) Iℝ 0).hom η = 0 := by
    simpa [S, Φ, Point.sheafFiber] using hη
  rcases Φ.toPresheafFiber_jointly_surjective (A := AddCommGrpCat.{max v m})
      (P := F0) η with
    ⟨W, hxWΦ, omega, homega⟩
  have hclosed_fiber :
      Φ.toPresheafFiber W hxWΦ F1
          ((deRhamDifferentialAddSheafHom (M := M) Iℝ 0).hom.app
            (Opposite.op W) omega) =
        Φ.toPresheafFiber W hxWΦ F1 0 := by
    have hη'' := hη'
    rw [← homega] at hη''
    rw [Point.toPresheafFiber_naturality_apply] at hη''
    calc
      Φ.toPresheafFiber W hxWΦ F1
          ((deRhamDifferentialAddSheafHom (M := M) Iℝ 0).hom.app
            (Opposite.op W) omega) = 0 := by
        simpa [F1] using hη''
      _ = Φ.toPresheafFiber W hxWΦ F1 0 := by
        simp
  rcases (Φ.toPresheafFiber_eq_iff' (P := F1) W hxWΦ
      ((deRhamDifferentialAddSheafHom (M := M) Iℝ 0).hom.app
        (Opposite.op W) omega) 0).1 hclosed_fiber with
    ⟨W₀, iW₀W, hxW₀Φ, _hmap, hclosed_restrict⟩
  have hclosed_restrict' :
      F1.map iW₀W.op
          ((deRhamDifferentialAddSheafHom (M := M) Iℝ 0).hom.app
            (Opposite.op W) omega) = 0 := by
    simpa using hclosed_restrict
  let hW₀W : W₀ ≤ W := CategoryTheory.leOfHom iW₀W
  let omegaW₀ : SmoothForms (I := Iℝ) (M := W₀) ℝ 0 :=
    restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ) hW₀W 0 omega
  have hclosedW₀ :
      deRhamDifferential (I := Iℝ) (M := W₀) (A := ℝ) 0 omegaW₀ = 0 := by
    have hnat :=
      deRhamDifferential_restrictSmoothFormsOfLE
        (I := Iℝ) (M := M) (A := ℝ) hW₀W omega
    calc
      deRhamDifferential (I := Iℝ) (M := W₀) (A := ℝ) 0 omegaW₀ =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            hW₀W 1
            (deRhamDifferential (I := Iℝ) (M := W) (A := ℝ) 0 omega) := by
        simpa [omegaW₀, hW₀W] using hnat
      _ = 0 := by
        simpa [F1, hW₀W, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
          smoothFormsPresheaf, deRhamDifferentialAddSheafHom,
          smoothFormsAddPresheafCochainComplex, smoothFormsPresheafCochainComplex,
          deRhamDifferentialPresheafNatTrans] using hclosed_restrict'
  rcases
      realConstantAddSheafToSmoothFormsAddSheaf_liftedPoint_lift_closed_representative
        (M := M) Iℝ x W₀ hxW₀Φ omegaW₀ hclosedW₀ with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hfirst :
      S.f c = Φ.toPresheafFiber W₀ hxW₀Φ F0 omegaW₀ := by
    simpa [S, Φ, F0] using hc
  have hto_W :
      Φ.toPresheafFiber W₀ hxW₀Φ F0 omegaW₀ =
        Φ.toPresheafFiber W hxWΦ F0 omega := by
    haveI : Subsingleton (Φ.fiber.obj W) := by
      dsimp [Φ, liftedPointGrothendieckTopology]
      infer_instance
    have h :=
      Point.toPresheafFiber_w_apply (Φ := Φ) iW₀W hxW₀Φ F0 omega
    simpa [omegaW₀, hW₀W, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
      smoothFormsPresheaf, F0, Subsingleton.elim (Φ.fiber.map iW₀W hxW₀Φ) hxWΦ] using h
  exact hfirst.trans (hto_W.trans homega)

/--
%%handwave
name:
  Closed zero-form lifted germs come from constants
statement:
  At every lifted topological point, the short complex consisting of constant
  real germs, smooth zero-form germs, and smooth one-form germs is exact.
proof:
  Use the elementwise exactness criterion for short complexes of abelian
  groups, together with [every closed smooth zero-form germ at a lifted point
  lifts to a constant real germ](lean:JJMath.Manifold.realConstantAddSheaf_to_smoothFormsAddSheaf_liftedPoint_lift_closed_germ).
tags:
  milestone
-/
theorem realConstantAddSheaf_to_smoothFormsAddSheaf_liftedPoint_exact
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (x : M) :
    let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
      liftedPointGrothendieckTopology.{v, m} x
    (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
        g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
        zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
      ShortComplex
        (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
          AddCommGrpCat.{max v m})).map
      (Φ.sheafFiber (A := AddCommGrpCat.{max v m}))).Exact := by
  let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
    liftedPointGrothendieckTopology.{v, m} x
  let S : ShortComplex AddCommGrpCat.{max v m} :=
    (({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
        g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
        zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
      ShortComplex
        (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
          AddCommGrpCat.{max v m})).map
      (Φ.sheafFiber (A := AddCommGrpCat.{max v m})))
  change S.Exact
  rw [ShortComplex.ab_exact_iff]
  exact
    realConstantAddSheaf_to_smoothFormsAddSheaf_liftedPoint_lift_closed_germ
      (M := M) Iℝ x

/--
%%handwave
name:
  Closed smooth zero-forms are locally constant
statement:
  The constant real sheaf, the sheaf of smooth zero-forms, and exterior
  differentiation form an exact short complex of sheaves.
proof:
  Exactness may be checked on stalks.  A germ of a smooth zero-form in the
  kernel of exterior differentiation is represented by a smooth function with
  zero differential on a neighborhood.  In a coordinate ball, the ordinary
  derivative of that function is zero, so the function is constant on a
  smaller connected coordinate ball.  Thus the germ comes from the constant
  real sheaf, and constants are already known to have zero differential.
tags:
  milestone
-/
theorem realConstantAddSheaf_to_smoothFormsAddSheaf_exact [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    ({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ,
       g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
       zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ } :
      ShortComplex
        (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
          AddCommGrpCat.{max v m})).Exact := by
  let Sraw : ShortComplex
      (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}) :=
    { f := realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ
      g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0
      zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ }
  change Sraw.Exact
  rw [sheaf_exact_iff_sheafFiber_map_exact_of_conservativePoints
    (X := M) (P := liftedPointsGrothendieckTopology.{v, m} M)
    (isConservativeFamilyOfPoints_liftedPointsGrothendieckTopology.{v, m} M) Sraw]
  intro Φ
  rcases (ObjectProperty.ofObj_iff
      (liftedPointGrothendieckTopology.{v, m} (X := M)) Φ.obj).1 Φ.property with
    ⟨x, hx⟩
  simpa [Sraw, ← hx] using
    realConstantAddSheaf_to_smoothFormsAddSheaf_liftedPoint_exact (M := M) Iℝ x



/--
%%handwave
name:
  Closed smooth zero-forms are locally constant in the same universe
statement:
  If the smooth-form coefficient groups and the underlying space live in the
  same universe, the constant real sheaf, the sheaf of smooth zero-forms, and
  exterior differentiation form an exact short complex of sheaves.
proof:
  Specialize [the sheaf-level local constancy statement for closed smooth
  zero-forms](lean:JJMath.Manifold.realConstantAddSheaf_to_smoothFormsAddSheaf_exact)
  to the case where the model vector space and the manifold have the same
  universe.
tags:
  milestone
-/
theorem realConstantAddSheaf_to_smoothFormsAddSheaf_exact_sameUniverse
    {E0 : Type m} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    (Iℝ : ModelWithCorners ℝ E0 H0) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M0] [FiniteDimensional ℝ E0]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M0 : TopCat.{m}))
      AddCommGrpCat.{m}] :
    ({ f := realConstantAddSheafToSmoothFormsAddSheaf (M := M0) Iℝ,
       g := deRhamDifferentialAddSheafHom (M := M0) Iℝ 0,
       zero := realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M0) Iℝ } :
      ShortComplex
        (TopCat.Sheaf AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}))).Exact := by
  simpa using
    realConstantAddSheaf_to_smoothFormsAddSheaf_exact (M := M0) Iℝ


/--
%%handwave
name:
  The sheaf de Rham complex is exact at constants
statement:
  The constant real sheaf maps into smooth functions so that the resulting
  short complex with exterior derivative is exact.
proof:
  The map sends a locally constant real function to the corresponding smooth
  zero-form.  Exactness says precisely that a smooth zero-form has zero
  differential iff it is locally constant.
tags:
  milestone
-/
theorem exists_realConstantAddSheaf_to_smoothFormsAddSheaf_exact
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [Iℝ.Boundaryless] [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}] :
    ∃ ε :
      realConstantAddSheafSmoothFormsUniverse (TopCat.of M : TopCat.{m}) ⟶
        smoothFormsAddSheaf (M := M) Iℝ 0,
      ∃ hε : ε ≫ deRhamDifferentialAddSheafHom (M := M) Iℝ 0 = 0,
        ({ f := ε,
           g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
           zero := hε } :
          ShortComplex
            (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
              AddCommGrpCat.{max v m})).Exact := by
  refine ⟨realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ, ?_⟩
  refine ⟨realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ, ?_⟩
  exact realConstantAddSheaf_to_smoothFormsAddSheaf_exact (M := M) Iℝ

/--
%%handwave
name:
  Same-universe sheaf exactness follows from stalk exactness
statement:
  If the model vector space and manifold live in the same universe, exactness
  of the sheaf de Rham complex in a positive degree follows from exactness of
  the corresponding complex on all ordinary stalks.
proof:
  Apply the standard theorem that exactness of a short complex of sheaves of
  abelian groups may be checked on stalks.  The same-universe hypothesis is
  what lets the topological-space universe match the coefficient-group
  universe of the smooth-form sheaves.
-/
theorem smoothFormsAddSheafCochainComplex_exactAt_succ_of_stalk_exact_sameUniverse
    {E0 : Type m} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    (Iℝ : ModelWithCorners ℝ E0 H0) [IsManifold Iℝ ∞ M0]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M0 : TopCat.{m}))
      AddCommGrpCat.{m}]
    (n : ℕ)
    (hstalk :
      ∀ x : (TopCat.of M0 : TopCat.{m}),
        (((smoothFormsAddSheafCochainComplex (M := M0) Iℝ).sc (n + 1)).map
          (TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x)).Exact) :
    (smoothFormsAddSheafCochainComplex (M := M0) Iℝ).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  exact
    (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
      ((smoothFormsAddSheafCochainComplex (M := M0) Iℝ).sc (n + 1))).2 hstalk

theorem smoothFormsAddSheaf_stalk_lift_closed_germ_of_local_poincare_sameUniverse
    {E0 : Type m} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    (Iℝ : ModelWithCorners ℝ E0 H0) [IsManifold Iℝ ∞ M0]
    (hlocal : DeRhamLocalPoincareBasis (M := M0) Iℝ)
    (n : ℕ) (x : (TopCat.of M0 : TopCat.{m}))
    (η : ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m})).obj
      (smoothFormsAddSheaf (M := M0) Iℝ (n + 1))).stalk x)
    (hη :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).map
        (deRhamDifferentialAddSheafHom (M := M0) Iℝ (n + 1)).hom) η = 0) :
    ∃ θ : ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m})).obj
      (smoothFormsAddSheaf (M := M0) Iℝ n)).stalk x,
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).map
        (deRhamDifferentialAddSheafHom (M := M0) Iℝ n).hom) θ = η := by
  let Fnp1 : TopCat.Presheaf AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M0) Iℝ (n + 1)).obj
  let Fnp2 : TopCat.Presheaf AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M0) Iℝ (n + 2)).obj
  let Fn : TopCat.Presheaf AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M0) Iℝ n).obj
  rcases Fnp1.exists_germ_eq η with ⟨W, hxW, omega, homega⟩
  have hclosed_germ :
      Fnp2.germ W x hxW
          ((deRhamDifferentialAddSheafHom (M := M0) Iℝ (n + 1)).hom.app
            (Opposite.op W) omega) =
        Fnp2.germ W x hxW 0 := by
    have hη' := hη
    rw [← homega] at hη'
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hη'
    calc
      Fnp2.germ W x hxW
          ((deRhamDifferentialAddSheafHom (M := M0) Iℝ (n + 1)).hom.app
            (Opposite.op W) omega) = 0 := by
        simpa [Fnp2] using hη'
      _ = Fnp2.germ W x hxW 0 := by
        simp
  rcases Fnp2.germ_eq x hxW hxW
      ((deRhamDifferentialAddSheafHom (M := M0) Iℝ (n + 1)).hom.app
        (Opposite.op W) omega) 0 hclosed_germ with
    ⟨W₀, hxW₀, iW₀W, iW₀W', hclosed_restrict⟩
  have hclosed_restrict' :
      Fnp2.map iW₀W.op
          ((deRhamDifferentialAddSheafHom (M := M0) Iℝ (n + 1)).hom.app
            (Opposite.op W) omega) = 0 := by
    simpa [Subsingleton.elim iW₀W' iW₀W] using hclosed_restrict
  let hW₀W : W₀ ≤ W := CategoryTheory.leOfHom iW₀W
  let omegaW₀ : SmoothForms (I := Iℝ) (M := W₀) ℝ (n + 1) :=
    restrictSmoothFormsOfLE (I := Iℝ) (M := M0) (A := ℝ) hW₀W (n + 1) omega
  have hclosedW₀ :
      deRhamDifferential (I := Iℝ) (M := W₀) (A := ℝ) (n + 1) omegaW₀ = 0 := by
    have hnat :=
      deRhamDifferential_restrictSmoothFormsOfLE
        (I := Iℝ) (M := M0) (A := ℝ) hW₀W omega
    calc
      deRhamDifferential (I := Iℝ) (M := W₀) (A := ℝ) (n + 1) omegaW₀ =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M0) (A := ℝ)
            hW₀W (n + 2)
            (deRhamDifferential (I := Iℝ) (M := W) (A := ℝ) (n + 1) omega) := by
        simpa [omegaW₀, hW₀W] using hnat
      _ = 0 := by
        simpa [Fnp2, hW₀W, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
          smoothFormsPresheaf, deRhamDifferentialAddSheafHom,
          smoothFormsAddPresheafCochainComplex, smoothFormsPresheafCochainComplex,
          deRhamDifferentialPresheafNatTrans] using hclosed_restrict'
  rcases hlocal.exists_primitive_on_smaller_open Iℝ x W₀ hxW₀ n omegaW₀ hclosedW₀ with
    ⟨U, hUW₀, hxU, theta, htheta⟩
  refine ⟨Fn.germ U x hxU theta, ?_⟩
  have hmap_theta :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).map
        (deRhamDifferentialAddSheafHom (M := M0) Iℝ n).hom)
          (Fn.germ U x hxU theta) =
        Fnp1.germ U x hxU
          (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n theta) := by
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    congr 1
    simp [deRhamDifferentialAddSheafHom, smoothFormsAddPresheafCochainComplex,
      smoothFormsPresheafCochainComplex, deRhamDifferentialPresheafNatTrans,
      smoothFormsPresheaf, ObjectProperty.homMk_hom, Functor.mapHomologicalComplex_obj_d]
    change (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n) theta =
      exteriorDerivative (I := Iℝ) (r := ∞) theta
    exact deRhamDifferential_apply (I := Iℝ) (M := U) (A := ℝ) theta
  rw [hmap_theta, htheta]
  have hgerm_restrict_W₀ :
      Fnp1.germ U x hxU
        (restrictSmoothFormsOfLE (I := Iℝ) (M := M0) (A := ℝ)
          (V := W₀) (W := U) hUW₀ (n + 1) omegaW₀) =
      Fnp1.germ W₀ x hxW₀ omegaW₀ := by
    simpa [omegaW₀, hW₀W, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
      smoothFormsPresheaf, Fnp1] using
      (Fnp1.germ_res_apply'
        (CategoryTheory.homOfLE hUW₀).op x hxU omegaW₀)
  rw [hgerm_restrict_W₀]
  have hgerm_restrict_W :
      Fnp1.germ W₀ x hxW₀ omegaW₀ =
      Fnp1.germ W x hxW omega := by
    simpa [omegaW₀, hW₀W, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
      smoothFormsPresheaf, Fnp1] using
      (Fnp1.germ_res_apply'
        iW₀W.op x hxW₀ omega)
  exact hgerm_restrict_W.trans homega

theorem smoothFormsAddSheaf_stalk_lift_closed_germ_of_local_poincare_forget_map_sameUniverse
    {E0 : Type m} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    (Iℝ : ModelWithCorners ℝ E0 H0) [IsManifold Iℝ ∞ M0]
    (hlocal : DeRhamLocalPoincareBasis (M := M0) Iℝ)
    (n : ℕ) (x : (TopCat.of M0 : TopCat.{m}))
    (η : ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m})).obj
      (smoothFormsAddSheaf (M := M0) Iℝ (n + 1))).stalk x)
    (hη :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).map
        ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m})).map
          (deRhamDifferentialAddSheafHom (M := M0) Iℝ (n + 1)))) η = 0) :
    ∃ θ : ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m})).obj
      (smoothFormsAddSheaf (M := M0) Iℝ n)).stalk x,
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).map
        ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m})).map
          (deRhamDifferentialAddSheafHom (M := M0) Iℝ n))) θ = η := by
  have hηhom :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).map
        (deRhamDifferentialAddSheafHom (M := M0) Iℝ (n + 1)).hom) η = 0 := by
    simpa [ObjectProperty.homMk_hom] using hη
  rcases smoothFormsAddSheaf_stalk_lift_closed_germ_of_local_poincare_sameUniverse
      (M0 := M0) Iℝ hlocal n x η hηhom with
    ⟨θ, hθ⟩
  refine ⟨θ, ?_⟩
  simpa [ObjectProperty.homMk_hom] using hθ

theorem smoothFormsAddSheafCochainComplex_stalk_scPrime_exact_of_local_poincare_sameUniverse
    {E0 : Type m} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    (Iℝ : ModelWithCorners ℝ E0 H0) [IsManifold Iℝ ∞ M0]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M0 : TopCat.{m}))
      AddCommGrpCat.{m}]
    (hlocal : DeRhamLocalPoincareBasis (M := M0) Iℝ)
    (n : ℕ) (x : (TopCat.of M0 : TopCat.{m})) :
    let K : CochainComplex AddCommGrpCat.{m} ℕ :=
      ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (smoothFormsAddSheafCochainComplex (M := M0) Iℝ)
    (K.sc' n (n + 1) (n + 2)).Exact := by
  let K : CochainComplex AddCommGrpCat.{m} ℕ :=
    ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (smoothFormsAddSheafCochainComplex (M := M0) Iℝ)
  change (K.sc' n (n + 1) (n + 2)).Exact
  rw [ShortComplex.ab_exact_iff]
  intro η hη
  have hη' :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).map
        ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m})).map
          (deRhamDifferentialAddSheafHom (M := M0) Iℝ (n + 1)))) η = 0 := by
    simpa [K, HomologicalComplex.shortComplexFunctor',
      smoothFormsAddSheafCochainComplex_d_succ] using hη
  rcases smoothFormsAddSheaf_stalk_lift_closed_germ_of_local_poincare_forget_map_sameUniverse
      (M0 := M0) Iℝ hlocal n x η hη' with
    ⟨θ, hθ⟩
  refine ⟨θ, ?_⟩
  simpa [K, HomologicalComplex.shortComplexFunctor',
    smoothFormsAddSheafCochainComplex_d_succ] using hθ

/--
%%handwave
name:
  Local Poincare lifts closed positive-degree germs
statement:
  On a smooth real manifold whose form sheaves live in the same universe as
  the space, if every point has arbitrarily small neighborhoods with
  vanishing positive-degree real de Rham cohomology, then every closed germ of
  a positive-degree form has a local primitive germ.
proof:
  A germ in the kernel of \(d:\Omega^{n+1}\to\Omega^{n+2}\) is represented by
  a form on some neighborhood of the point whose differential germ vanishes.
  Shrink inside that representative neighborhood until the differential
  actually vanishes, and then shrink again to a Poincare neighborhood.
  Vanishing of \(H^{n+1}\) there gives a primitive, and the primitive
  represents a germ mapping to the original germ.
tags:
  milestone
-/
theorem smoothFormsAddSheafCochainComplex_stalk_lift_closed_germ_of_local_poincare_sameUniverse
    {E0 : Type m} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    (Iℝ : ModelWithCorners ℝ E0 H0) [IsManifold Iℝ ∞ M0]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M0 : TopCat.{m}))
      AddCommGrpCat.{m}]
    (hlocal : DeRhamLocalPoincareBasis (M := M0) Iℝ)
    (n : ℕ) (x : (TopCat.of M0 : TopCat.{m})) :
    let S : ShortComplex AddCommGrpCat.{m} :=
      (((smoothFormsAddSheafCochainComplex (M := M0) Iℝ).sc (n + 1)).map
        (TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x))
    ∀ η : S.X₂, S.g η = 0 → ∃ θ : S.X₁, S.f θ = η := by
  intro S η hη
  have hExact : S.Exact := by
    let K : CochainComplex AddCommGrpCat.{m} ℕ :=
      ((TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (smoothFormsAddSheafCochainComplex (M := M0) Iℝ)
    change (K.sc (n + 1)).Exact
    change K.ExactAt (n + 1)
    exact
      (HomologicalComplex.exactAt_iff' (K := K) (i := n) (j := n + 1) (k := n + 2)
        (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).2
        (smoothFormsAddSheafCochainComplex_stalk_scPrime_exact_of_local_poincare_sameUniverse
          (M0 := M0) Iℝ hlocal n x)
  rw [ShortComplex.ab_exact_iff] at hExact
  exact hExact η hη

/--
%%handwave
name:
  Local Poincare gives exact germs in positive degree
statement:
  On a smooth real manifold whose form sheaves live in the same universe as
  the space, if every point has arbitrarily small neighborhoods with
  vanishing positive-degree real de Rham cohomology, then the stalk complex of
  smooth forms is exact in every positive degree at every point.
proof:
  Use the elementwise exactness criterion for short complexes of abelian
  groups.  Exactness is precisely [the statement that every closed
  positive-degree form germ has a local primitive germ](lean:JJMath.Manifold.smoothFormsAddSheafCochainComplex_stalk_lift_closed_germ_of_local_poincare_sameUniverse).
tags:
  milestone
-/
theorem smoothFormsAddSheafCochainComplex_stalk_exactAt_succ_of_local_poincare_sameUniverse
    {E0 : Type m} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    (Iℝ : ModelWithCorners ℝ E0 H0) [IsManifold Iℝ ∞ M0]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M0 : TopCat.{m}))
      AddCommGrpCat.{m}]
    (hlocal : DeRhamLocalPoincareBasis (M := M0) Iℝ)
    (n : ℕ) (x : (TopCat.of M0 : TopCat.{m})) :
    (((smoothFormsAddSheafCochainComplex (M := M0) Iℝ).sc (n + 1)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x)).Exact := by
  let S : ShortComplex AddCommGrpCat.{m} :=
    (((smoothFormsAddSheafCochainComplex (M := M0) Iℝ).sc (n + 1)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{m} (TopCat.of M0 : TopCat.{m}) ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{m} x))
  change S.Exact
  rw [ShortComplex.ab_exact_iff]
  exact
    smoothFormsAddSheafCochainComplex_stalk_lift_closed_germ_of_local_poincare_sameUniverse
      (M0 := M0) Iℝ hlocal n x

/--
%%handwave
name:
  Same-universe local Poincare gives positive-degree sheaf exactness
statement:
  If the smooth-form coefficient groups and the underlying space live in the
  same universe and every point has arbitrarily small neighborhoods with
  vanishing
  positive-degree real de Rham cohomology, then the sheaf de Rham complex is
  exact in every positive degree.
proof:
  Apply the stalk criterion for sheaf exactness to [the germwise exactness
  supplied by local Poincare neighborhoods](lean:JJMath.Manifold.smoothFormsAddSheafCochainComplex_stalk_exactAt_succ_of_local_poincare_sameUniverse).
tags:
  milestone
-/
theorem smoothFormsAddSheafCochainComplex_exactAt_succ_of_local_poincare_sameUniverse
    {E0 : Type m} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type w} [TopologicalSpace H0]
    {M0 : Type m} [TopologicalSpace M0] [ChartedSpace H0 M0]
    (Iℝ : ModelWithCorners ℝ E0 H0) [IsManifold Iℝ ∞ M0]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M0 : TopCat.{m}))
      AddCommGrpCat.{m}]
    (hlocal : DeRhamLocalPoincareBasis (M := M0) Iℝ)
    (n : ℕ) :
    (smoothFormsAddSheafCochainComplex (M := M0) Iℝ).ExactAt (n + 1) := by
  exact
    smoothFormsAddSheafCochainComplex_exactAt_succ_of_stalk_exact_sameUniverse
      (M0 := M0) Iℝ n
      (fun x =>
        smoothFormsAddSheafCochainComplex_stalk_exactAt_succ_of_local_poincare_sameUniverse
          (M0 := M0) Iℝ hlocal n x)


theorem smoothFormsAddSheaf_liftedPoint_lift_closed_germ_of_local_poincare
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (hlocal : DeRhamLocalPoincareBasis (M := M) Iℝ)
    (n : ℕ) (x : M)
    (η :
      ((liftedPointGrothendieckTopology.{v, m} x).presheafFiber
        (A := AddCommGrpCat.{max v m})).obj
        ((smoothFormsAddSheaf (M := M) Iℝ (n + 1)).obj))
    (hη :
      (((liftedPointGrothendieckTopology.{v, m} x).presheafFiber
        (A := AddCommGrpCat.{max v m})).map
        (deRhamDifferentialAddSheafHom (M := M) Iℝ (n + 1)).hom) η = 0) :
    ∃ θ :
      ((liftedPointGrothendieckTopology.{v, m} x).presheafFiber
        (A := AddCommGrpCat.{max v m})).obj
        ((smoothFormsAddSheaf (M := M) Iℝ n).obj),
      (((liftedPointGrothendieckTopology.{v, m} x).presheafFiber
        (A := AddCommGrpCat.{max v m})).map
        (deRhamDifferentialAddSheafHom (M := M) Iℝ n).hom) θ = η := by
  let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
    liftedPointGrothendieckTopology.{v, m} x
  let Fnp1 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ (n + 1)).obj
  let Fnp2 : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ (n + 2)).obj
  let Fn : TopCat.Presheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m}) :=
    (smoothFormsAddSheaf (M := M) Iℝ n).obj
  change ∃ θ : (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).obj Fn,
    (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
      (deRhamDifferentialAddSheafHom (M := M) Iℝ n).hom θ = η
  change (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
    (deRhamDifferentialAddSheafHom (M := M) Iℝ (n + 1)).hom η = 0 at hη
  rcases Φ.toPresheafFiber_jointly_surjective (A := AddCommGrpCat.{max v m})
      (P := Fnp1) η with
    ⟨W, hxWΦ, omega, homega⟩
  have hxW : x ∈ W := by
    change ULift.{max v m} (PLift (x ∈ W)) at hxWΦ
    exact hxWΦ.down.down
  have hclosed_fiber :
      Φ.toPresheafFiber W hxWΦ Fnp2
          ((deRhamDifferentialAddSheafHom (M := M) Iℝ (n + 1)).hom.app
            (Opposite.op W) omega) =
        Φ.toPresheafFiber W hxWΦ Fnp2 0 := by
    have hη' := hη
    rw [← homega] at hη'
    rw [Point.toPresheafFiber_naturality_apply] at hη'
    calc
      Φ.toPresheafFiber W hxWΦ Fnp2
          ((deRhamDifferentialAddSheafHom (M := M) Iℝ (n + 1)).hom.app
            (Opposite.op W) omega) = 0 := by
        simpa [Fnp2] using hη'
      _ = Φ.toPresheafFiber W hxWΦ Fnp2 0 := by
        simp
  rcases (Φ.toPresheafFiber_eq_iff' (P := Fnp2) W hxWΦ
      ((deRhamDifferentialAddSheafHom (M := M) Iℝ (n + 1)).hom.app
        (Opposite.op W) omega) 0).1 hclosed_fiber with
    ⟨W₀, iW₀W, hxW₀Φ, _hmap, hclosed_restrict⟩
  have hxW₀ : x ∈ W₀ := by
    change ULift.{max v m} (PLift (x ∈ W₀)) at hxW₀Φ
    exact hxW₀Φ.down.down
  have hclosed_restrict' :
      Fnp2.map iW₀W.op
          ((deRhamDifferentialAddSheafHom (M := M) Iℝ (n + 1)).hom.app
            (Opposite.op W) omega) = 0 := by
    simpa using hclosed_restrict
  let hW₀W : W₀ ≤ W := CategoryTheory.leOfHom iW₀W
  let omegaW₀ : SmoothForms (I := Iℝ) (M := W₀) ℝ (n + 1) :=
    restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ) hW₀W (n + 1) omega
  have hclosedW₀ :
      deRhamDifferential (I := Iℝ) (M := W₀) (A := ℝ) (n + 1) omegaW₀ = 0 := by
    have hnat :=
      deRhamDifferential_restrictSmoothFormsOfLE
        (I := Iℝ) (M := M) (A := ℝ) hW₀W omega
    calc
      deRhamDifferential (I := Iℝ) (M := W₀) (A := ℝ) (n + 1) omegaW₀ =
          restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
            hW₀W (n + 2)
            (deRhamDifferential (I := Iℝ) (M := W) (A := ℝ) (n + 1) omega) := by
        simpa [omegaW₀, hW₀W] using hnat
      _ = 0 := by
        simpa [Fnp2, hW₀W, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
          smoothFormsPresheaf, deRhamDifferentialAddSheafHom,
          smoothFormsAddPresheafCochainComplex, smoothFormsPresheafCochainComplex,
          deRhamDifferentialPresheafNatTrans] using hclosed_restrict'
  rcases hlocal.exists_primitive_on_smaller_open Iℝ x W₀ hxW₀ n omegaW₀ hclosedW₀ with
    ⟨U, hUW₀, hxU, theta, htheta⟩
  let hxUΦ : Φ.fiber.obj U := by
    change ULift.{max v m} (PLift (x ∈ U))
    exact ⟨⟨hxU⟩⟩
  refine ⟨Φ.toPresheafFiber U hxUΦ Fn theta, ?_⟩
  have hmap_theta :
      (Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
        (deRhamDifferentialAddSheafHom (M := M) Iℝ n).hom
          (Φ.toPresheafFiber U hxUΦ Fn theta) =
        Φ.toPresheafFiber U hxUΦ Fnp1
          (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n theta) := by
    rw [Point.toPresheafFiber_naturality_apply]
    congr 1
    simp [deRhamDifferentialAddSheafHom, smoothFormsAddPresheafCochainComplex,
      smoothFormsPresheafCochainComplex, deRhamDifferentialPresheafNatTrans,
      smoothFormsPresheaf, ObjectProperty.homMk_hom, Functor.mapHomologicalComplex_obj_d]
    change (deRhamDifferential (I := Iℝ) (M := U) (A := ℝ) n) theta =
      exteriorDerivative (I := Iℝ) (r := ∞) theta
    exact deRhamDifferential_apply (I := Iℝ) (M := U) (A := ℝ) theta
  rw [hmap_theta, htheta]
  have hto_W₀ :
      Φ.toPresheafFiber U hxUΦ Fnp1
        (restrictSmoothFormsOfLE (I := Iℝ) (M := M) (A := ℝ)
          (V := W₀) (W := U) hUW₀ (n + 1) omegaW₀) =
      Φ.toPresheafFiber W₀ hxW₀Φ Fnp1 omegaW₀ := by
    haveI : Subsingleton (Φ.fiber.obj W₀) := by
      dsimp [Φ, liftedPointGrothendieckTopology]
      infer_instance
    have h :=
      Point.toPresheafFiber_w_apply (Φ := Φ)
        (CategoryTheory.homOfLE hUW₀) hxUΦ Fnp1 omegaW₀
    simpa [omegaW₀, hW₀W, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
      smoothFormsPresheaf, Fnp1, Subsingleton.elim (Φ.fiber.map
        (CategoryTheory.homOfLE hUW₀) hxUΦ) hxW₀Φ] using h
  rw [hto_W₀]
  have hto_W :
      Φ.toPresheafFiber W₀ hxW₀Φ Fnp1 omegaW₀ =
      Φ.toPresheafFiber W hxWΦ Fnp1 omega := by
    haveI : Subsingleton (Φ.fiber.obj W) := by
      dsimp [Φ, liftedPointGrothendieckTopology]
      infer_instance
    have h :=
      Point.toPresheafFiber_w_apply (Φ := Φ)
        iW₀W hxW₀Φ Fnp1 omega
    simpa [omegaW₀, hW₀W, smoothFormsAddSheaf_obj, smoothFormsAddPresheaf,
      smoothFormsPresheaf, Fnp1, Subsingleton.elim (Φ.fiber.map iW₀W hxW₀Φ) hxWΦ] using h
  exact hto_W.trans homega

theorem smoothFormsAddSheafCochainComplex_liftedPoint_scPrime_exact_of_local_poincare
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (hlocal : DeRhamLocalPoincareBasis (M := M) Iℝ)
    (n : ℕ) (x : M) :
    let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
      liftedPointGrothendieckTopology.{v, m} x
    let K : CochainComplex AddCommGrpCat.{max v m} ℕ :=
      (((Φ.sheafFiber (A := AddCommGrpCat.{max v m})).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (smoothFormsAddSheafCochainComplex (M := M) Iℝ))
    (K.sc' n (n + 1) (n + 2)).Exact := by
  let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
    liftedPointGrothendieckTopology.{v, m} x
  let K : CochainComplex AddCommGrpCat.{max v m} ℕ :=
    (((Φ.sheafFiber (A := AddCommGrpCat.{max v m})).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (smoothFormsAddSheafCochainComplex (M := M) Iℝ))
  change (K.sc' n (n + 1) (n + 2)).Exact
  rw [ShortComplex.ab_exact_iff]
  intro η hη
  have hη' :
      ((Φ.presheafFiber (A := AddCommGrpCat.{max v m})).map
        (deRhamDifferentialAddSheafHom (M := M) Iℝ (n + 1)).hom) η = 0 := by
    simpa [K, Point.sheafFiber, HomologicalComplex.shortComplexFunctor',
      smoothFormsAddSheafCochainComplex_d_succ] using hη
  rcases smoothFormsAddSheaf_liftedPoint_lift_closed_germ_of_local_poincare
      (M := M) Iℝ hlocal n x η hη' with
    ⟨θ, hθ⟩
  refine ⟨θ, ?_⟩
  simpa [K, Point.sheafFiber, HomologicalComplex.shortComplexFunctor',
    smoothFormsAddSheafCochainComplex_d_succ] using hθ

theorem smoothFormsAddSheafCochainComplex_liftedPoint_exactAt_succ_of_local_poincare
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (hlocal : DeRhamLocalPoincareBasis (M := M) Iℝ)
    (n : ℕ) (x : M) :
    let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
      liftedPointGrothendieckTopology.{v, m} x
    let K : CochainComplex AddCommGrpCat.{max v m} ℕ :=
      (((Φ.sheafFiber (A := AddCommGrpCat.{max v m})).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (smoothFormsAddSheafCochainComplex (M := M) Iℝ))
    (K.sc (n + 1)).Exact := by
  let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
    liftedPointGrothendieckTopology.{v, m} x
  let K : CochainComplex AddCommGrpCat.{max v m} ℕ :=
    (((Φ.sheafFiber (A := AddCommGrpCat.{max v m})).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (smoothFormsAddSheafCochainComplex (M := M) Iℝ))
  change (K.sc (n + 1)).Exact
  change K.ExactAt (n + 1)
  exact
    (HomologicalComplex.exactAt_iff' (K := K) (i := n) (j := n + 1) (k := n + 2)
      (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).2
      (smoothFormsAddSheafCochainComplex_liftedPoint_scPrime_exact_of_local_poincare
        (M := M) Iℝ hlocal n x)

/--
%%handwave
name:
  Lifted pointwise exactness implies sheaf exactness
statement:
  If a short part of the sheaf de Rham complex becomes exact after taking the
  fiber at every lifted topological point, then it is exact as a sheaf complex.
proof:
  This is the conservative-points criterion for exactness, with the usual
  topological points lifted to the universe of the coefficient groups.  The
  statement is kept separate because the `TopCat` sheaf category uses a
  wrapper category instance around the underlying site-sheaf category.
tags:
  milestone
-/
theorem smoothFormsAddSheafCochainComplex_exactAt_succ_of_liftedPoint_exact
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (n : ℕ)
    (hpoint : ∀ x : M,
      let Φ : Point.{max v m} (Opens.grothendieckTopology M) :=
        liftedPointGrothendieckTopology.{v, m} x
      let K : CochainComplex AddCommGrpCat.{max v m} ℕ :=
        (((Φ.sheafFiber (A := AddCommGrpCat.{max v m})).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (smoothFormsAddSheafCochainComplex (M := M) Iℝ))
      (K.sc (n + 1)).Exact) :
    (smoothFormsAddSheafCochainComplex (M := M) Iℝ).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  let C : CochainComplex (TopCat.Sheaf AddCommGrpCat.{max v m} (TopCat.of M : TopCat.{m})) ℕ :=
    smoothFormsAddSheafCochainComplex (M := M) Iℝ
  let Craw : CochainComplex
      (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}) ℕ := C
  let Sraw : ShortComplex
      (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}) := Craw.sc (n + 1)
  have hraw : Sraw.Exact := by
    rw [sheaf_exact_iff_sheafFiber_map_exact_of_conservativePoints
      (X := M) (P := liftedPointsGrothendieckTopology.{v, m} M)
      (isConservativeFamilyOfPoints_liftedPointsGrothendieckTopology.{v, m} M) Sraw]
    intro Φ
    rcases (ObjectProperty.ofObj_iff
        (liftedPointGrothendieckTopology.{v, m} (X := M)) Φ.obj).1 Φ.property with
      ⟨x, hx⟩
    simpa [Sraw, Craw, C, ← hx, HomologicalComplex.sc] using hpoint x
  change Sraw.Exact
  exact hraw

/--
%%handwave
name:
  Local Poincare gives germwise exactness in positive degree
statement:
  If every point has arbitrarily small neighborhoods on which positive-degree
  de Rham cohomology vanishes, then the sheaf de Rham complex is exact in
  every positive degree.
proof:
  Use the conservative family of topological points, lifted to the coefficient
  universe of smooth-form sheaves, to check exactness on germs.  A germ in the
  kernel of the exterior derivative is represented by a closed form on some
  open neighborhood after shrinking.  Restrict to a smaller Poincare
  neighborhood from the hypothesis; vanishing de Rham cohomology there
  supplies a primitive, and hence the original germ lies in the image of the
  previous exterior derivative.
tags:
  milestone
-/
theorem smoothFormsAddSheafCochainComplex_exactAt_succ_of_local_poincare_enlarged_points
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (hlocal : DeRhamLocalPoincareBasis (M := M) Iℝ)
    (n : ℕ) :
    (smoothFormsAddSheafCochainComplex (M := M) Iℝ).ExactAt (n + 1) := by
  exact
    smoothFormsAddSheafCochainComplex_exactAt_succ_of_liftedPoint_exact
      (M := M) Iℝ n
      (fun x =>
        smoothFormsAddSheafCochainComplex_liftedPoint_exactAt_succ_of_local_poincare
          (M := M) Iℝ hlocal n x)

/--
%%handwave
name:
  The sheaf de Rham complex is locally exact in positive degree
statement:
  If every point has arbitrarily small neighborhoods with vanishing
  positive-degree real de Rham cohomology, then the sheaf de Rham complex is
  exact in every positive degree.
proof:
  Exactness of sheaves may be checked on germs.  A germ of a closed
  positive-degree form is represented on a local Poincare neighborhood, where
  it has a primitive by hypothesis.
tags:
  milestone
-/
theorem smoothFormsAddSheafCochainComplex_exactAt_succ_of_local_poincare
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (hlocal : DeRhamLocalPoincareBasis (M := M) Iℝ)
    (n : ℕ) :
    (smoothFormsAddSheafCochainComplex (M := M) Iℝ).ExactAt (n + 1) := by
  exact
    smoothFormsAddSheafCochainComplex_exactAt_succ_of_local_poincare_enlarged_points
      (M := M) Iℝ hlocal n

/--
%%handwave
name:
  Smooth-form sheaves are fine
statement:
  On a finite-dimensional Hausdorff sigma-compact smooth real manifold, every
  sheaf of smooth real-valued differential forms is fine.
proof:
  Given a locally finite open cover, choose a smooth partition of unity
  subordinate to it.  Multiplication by the partition functions gives
  endomorphisms of the sheaf of smooth differential forms.  Their germ
  supports lie in the corresponding open sets, and the local finiteness of the
  cover makes the pointwise germwise sum equal to the identity.
tags:
  milestone
-/
theorem smoothFormsAddSheaf_isFine [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (p : ℕ) :
    TopCat.Sheaf.IsFine (X := TopCat.of M)
      (smoothFormsAddSheaf (M := M) Iℝ p) := by
  constructor
  intro ι U _hU_locallyFinite hcover
  have hUopen : ∀ i, IsOpen (U i : Set M) := fun i => (U i).is_open'
  have hUcover : (univ : Set M) ⊆ ⋃ i, (U i : Set M) := by
    intro x _hx
    rcases hcover x with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      (I := Iℝ) (M := M) (s := (univ : Set M))
      isClosed_univ (fun i => (U i : Set M)) hUopen hUcover with
    ⟨ρ, hρU⟩
  refine ⟨fun i => smoothFormsPointwiseSMulAddSheafHom (M := M) Iℝ p (ρ i), ?_, ?_⟩
  · intro i
    exact
      (smoothFormsPointwiseSMulAddSheafHom_germSupport_subset_tsupport
        (M := M) Iℝ p (ρ i)).trans (hρU i)
  · intro x
    exact
      smoothPartitionOfUnity_smoothFormsPointwiseSMulAddSheafHom_stalk_partitionOfIdentity
        (M := M) Iℝ p ρ x


/--
%%handwave
name:
  Global smooth-form homology is top-open smooth-form homology
statement:
  The homology of the global-sections sheaf de Rham complex is additively
  isomorphic to the homology of the top-open presheaf de Rham complex.
proof:
  Apply homology to [the isomorphism between the two cochain complexes](lean:JJMath.Manifold.smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex) and forget the resulting categorical isomorphism to an additive equivalence.
-/
theorem smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_smoothFormsAddPresheafTopCohomology
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (n : ℕ) :
    Nonempty
      (↥((smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ).homology n) ≃+
        ↥((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).homology n)) := by
  exact ⟨(HomologicalComplex.homologyMapIso
    (smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex
      (M := M) Iℝ) n).addCommGroupIsoToAddEquiv⟩

/--
%%handwave
name:
  Global smooth-form homology is top-open smooth-form homology compatibly with constants
statement:
  The homology equivalence between global sections of the sheaf de Rham
  complex and top-open presheaf cochains may be chosen to intertwine constant
  scalar multiplication.
proof:
  Use the equivalence induced by the isomorphism of complexes.  The
  chain-level isomorphism [intertwines constant scalar multiplication](lean:JJMath.Manifold.smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex_hom_comp_scalarEnd), and functoriality of homology turns that square into the desired equality on homology classes.
tags:
  milestone
-/
theorem exists_smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (n : ℕ) :
    ∃ e :
      ↥((smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ).homology n) ≃+
        ↥((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).homology n),
      ∀ (r : ℝ)
        (x : ↥((smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ).homology n)),
        e ((HomologicalComplex.homologyMap
          (((CategoryTheory.Sheaf.Γ
              (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
              AddCommGrpCat.{max v m}).mapHomologicalComplex
                (ComplexShape.up ℕ)).map
            (smoothFormsAddSheafCochainComplexScalarEnd (M := M) Iℝ r)) n) x) =
          (HomologicalComplex.homologyMap
            (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r) n)
            (e x) := by
  let iso :=
    smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex
      (M := M) Iℝ
  refine ⟨(HomologicalComplex.homologyMapIso iso n).addCommGroupIsoToAddEquiv, ?_⟩
  intro r x
  let globalEnd :
      smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ ⟶
        smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ :=
    (((CategoryTheory.Sheaf.Γ
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
      (smoothFormsAddSheafCochainComplexScalarEnd (M := M) Iℝ r))
  let topEnd :
      smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ ⟶
        smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ :=
    smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r
  have hchain : globalEnd ≫ iso.hom = iso.hom ≫ topEnd := by
    simpa [iso, globalEnd, topEnd] using
      (smoothFormsAddSheafGlobalSectionsCochainComplexIsoTopCochainComplex_hom_comp_scalarEnd
        (M := M) Iℝ r).symm
  have hhom :=
    congrArg
      (fun φ => (ConcreteCategory.hom (HomologicalComplex.homologyMap φ n)) x)
      hchain
  simpa [iso, globalEnd, topEnd, HomologicalComplex.homologyMap_comp,
    Iso.addCommGroupIsoToAddEquiv_apply] using hhom

/--
%%handwave
name:
  Explicit quotient for terminal-open smooth-form homology
statement:
  The homology of the terminal-open smooth-form complex is the quotient of
  cycles by boundaries for the short complex centered in degree \(n\).
proof:
  Apply the explicit homology computation for short complexes of abelian
  groups to the short complex associated to degree \(n\).
-/
abbrev smoothFormsAddPresheafTopCochainHomologyQuotient [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] (n : ℕ) : Type _ :=
  AddMonoidHom.ker
      ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).g.hom ⧸
    AddMonoidHom.range
      ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abToCycles

/--
%%handwave
name:
  Constant multiplication acts on the explicit terminal-open quotient
statement:
  Multiplying terminal-open smooth forms by a constant real number induces an
  additive endomorphism of the explicit cycle-boundary quotient in degree
  \(n\).
proof:
  Apply the left-homology map associated to the short-complex endomorphism
  obtained from constant multiplication in the terminal-open de Rham complex.
-/
noncomputable def smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (r : ℝ) :
    smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n →+
      smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n := by
  let K := smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ
  let S := K.sc n
  let φ : S ⟶ S :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{max v m}
      (ComplexShape.up ℕ) n).map
      (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r)
  exact AddCommGrpCat.Hom.hom
    (ShortComplex.leftHomologyMap' φ S.abLeftHomologyData S.abLeftHomologyData)

/--
%%handwave
name:
  Chosen explicit quotient equivalence for terminal-open smooth-form homology
statement:
  The homology of the terminal-open smooth-form complex is additively
  equivalent to its explicit cycle-boundary quotient.
proof:
  Use the canonical explicit homology isomorphism for short complexes of
  abelian groups in degree \(n\).
-/
noncomputable def smoothFormsAddPresheafTopCohomologyExplicitQuotientAddEquiv
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    ↥((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).homology n) ≃+
      smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n :=
  (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abHomologyIso
    ).addCommGroupIsoToAddEquiv

/--
%%handwave
name:
  Terminal-open smooth-form homology is its explicit quotient
statement:
  The homology of the terminal-open smooth-form complex is additively
  isomorphic to the explicit quotient of cycles by boundaries in degree \(n\).
proof:
  This is the explicit quotient model for homology of short complexes of
  abelian groups, applied to the short complex centered in degree \(n\).
-/
theorem smoothFormsAddPresheafTopCohomology_addEquiv_explicitQuotient
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    Nonempty
      (↥((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).homology n) ≃+
        smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n) := by
  exact ⟨smoothFormsAddPresheafTopCohomologyExplicitQuotientAddEquiv
    (M := M) Iℝ n⟩

/--
%%handwave
name:
  The explicit quotient equivalence intertwines constant multiplication
statement:
  Under the canonical explicit quotient equivalence for terminal-open
  smooth-form homology, the homology map induced by constant multiplication
  corresponds to the left-homology map on the explicit cycle-boundary quotient.
proof:
  This is the naturality of the homology isomorphism attached to the explicit
  left-homology data for short complexes of abelian groups.
tags:
  milestone
-/
theorem smoothFormsAddPresheafTopCohomologyExplicitQuotientAddEquiv_symm_scalarEnd
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (r : ℝ)
    (q : smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n) :
    (smoothFormsAddPresheafTopCohomologyExplicitQuotientAddEquiv
        (M := M) Iℝ n).symm
      (smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd
        (M := M) Iℝ n r q) =
      (HomologicalComplex.homologyMap
        (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r) n)
        ((smoothFormsAddPresheafTopCohomologyExplicitQuotientAddEquiv
          (M := M) Iℝ n).symm q) := by
  let K := smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ
  let S := K.sc n
  let φ : S ⟶ S :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{max v m}
      (ComplexShape.up ℕ) n).map
      (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r)
  have hnat :
      S.abLeftHomologyData.homologyIso.inv ≫ ShortComplex.homologyMap φ =
        ShortComplex.leftHomologyMap' φ S.abLeftHomologyData S.abLeftHomologyData ≫
          S.abLeftHomologyData.homologyIso.inv :=
    ShortComplex.LeftHomologyData.leftHomologyIso_inv_naturality
      φ S.abLeftHomologyData S.abLeftHomologyData
  have happ :=
    congrArg (fun f => AddCommGrpCat.Hom.hom f q) hnat
  simpa [K, S, φ, smoothFormsAddPresheafTopCohomologyExplicitQuotientAddEquiv,
    smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd,
    HomologicalComplex.homologyMap] using happ.symm

/--
%%handwave
name:
  Additive quotient congruence
statement:
  An additive isomorphism carrying one additive subgroup onto another induces
  an additive isomorphism of the corresponding quotient groups.
proof:
  Map quotient classes by the additive isomorphism and by its inverse.  The
  subgroup equality makes both maps well defined, and quotient induction shows
  that the two induced maps are inverse to each other.
-/
noncomputable def addQuotientEquivOfMapEq
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) (K : AddSubgroup B)
    (hHK : H.map e.toAddMonoidHom = K) :
    A ⧸ H ≃+ B ⧸ K := by
  let f : A ⧸ H →+ B ⧸ K :=
    QuotientAddGroup.map H K e.toAddMonoidHom (by
      intro x hx
      rw [← hHK]
      exact AddSubgroup.mem_map_of_mem e.toAddMonoidHom hx)
  have hKH : K.map e.symm.toAddMonoidHom = H := by
    rw [← hHK]
    ext x
    constructor
    · intro hx
      rcases (AddSubgroup.mem_map.mp hx) with ⟨y, hy, hxy⟩
      rcases (AddSubgroup.mem_map.mp hy) with ⟨z, hz, hyz⟩
      change e.symm y = x at hxy
      change e z = y at hyz
      subst y
      subst x
      simpa using hz
    · intro hx
      simpa using
        (AddSubgroup.mem_map_of_mem e.symm.toAddMonoidHom
          (AddSubgroup.mem_map_of_mem e.toAddMonoidHom hx))
  let g : B ⧸ K →+ A ⧸ H :=
    QuotientAddGroup.map K H e.symm.toAddMonoidHom (by
      intro x hx
      rw [← hKH]
      exact AddSubgroup.mem_map_of_mem e.symm.toAddMonoidHom hx)
  refine AddEquiv.mk
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_ } ?_
  · intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp [f, g]
  · intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp [f, g]
  · intro x y
    exact f.map_add x y

/--
%%handwave
name:
  A manifold is diffeomorphic to its terminal open subset
statement:
  The map sending a point of a smooth manifold to the same point regarded as a
  point of the terminal open subset is a smooth diffeomorphism.
proof:
  The terminal open subset is the whole underlying set.  The inclusion of the
  terminal open subset into the manifold and its inverse are both smooth in
  the inherited open-submanifold chart structure.
tags:
  milestone
-/
theorem topOpen_diffeomorph [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] :
    Nonempty
      (M ≃ₘ⟮Iℝ, Iℝ⟯
        (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) := by
  let U : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}) := ⊤
  let f : M → U := fun x => ⟨x, by trivial⟩
  have hf : ContMDiff Iℝ Iℝ ∞ f := by
    intro x
    rw [contMDiffAt_iff_target_of_mem_source
      (I := Iℝ) (I' := Iℝ) (y := (⟨x, by trivial⟩ : U))]
    constructor
    · exact (continuous_id.subtype_mk (fun _ => by trivial)).continuousAt
    · have hchart : ContMDiffAt Iℝ 𝓘(ℝ, E) ∞ (extChartAt Iℝ x) x :=
        contMDiffAt_extChartAt
      simpa [f, U, Function.comp, TopologicalSpace.Opens.chartAt_eq] using hchart
    · exact mem_chart_source H (⟨x, by trivial⟩ : U)
  let e : M ≃ U :=
    { toFun := f,
      invFun := fun x : U => (x : M),
      left_inv := fun _ => rfl,
      right_inv := fun _ => Subtype.ext rfl }
  have hg : ContMDiff Iℝ Iℝ ∞ (fun x : U => (x : M)) := by
    simpa [U] using (contMDiff_subtype_val (I := Iℝ) (n := ∞) (U := U))
  exact ⟨{ toEquiv := e, contMDiff_toFun := hf, contMDiff_invFun := hg }⟩

/--
%%handwave
name:
  Restriction to the whole open subset preserves de Rham cohomology
statement:
  Restricting differential forms from a manifold to its terminal open subset
  induces an additive isomorphism on de Rham cohomology.
proof:
  The terminal open subset is canonically homeomorphic, and smoothly
  diffeomorphic, to the original manifold.  Pulling forms back along the two
  inverse smooth maps gives mutually inverse cochain maps, hence mutually
  inverse maps on the quotient of closed forms by exact forms.
tags:
  milestone
-/
theorem deRhamCohomology_addEquiv_topOpenDeRhamCohomology
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    Nonempty
      (DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n) := by
  rcases topOpen_diffeomorph (M := M) Iℝ with ⟨φ⟩
  rcases deRhamCohomology_linearEquiv_of_diffeomorphic Iℝ Iℝ φ n with ⟨e⟩
  exact ⟨e.toAddEquiv⟩

/--
%%handwave
name:
  Restriction to the whole open subset preserves scalar multiplication
statement:
  The additive isomorphism from de Rham cohomology of a manifold to de Rham
  cohomology of its terminal open subset may be chosen to commute with real
  scalar multiplication.
proof:
  Use the linear equivalence induced by the smooth diffeomorphism between the
  manifold and its terminal open subset.
tags:
  milestone
-/
theorem exists_deRhamCohomology_addEquiv_topOpenDeRhamCohomology_with_smul
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    ∃ e :
      DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n,
      ∀ (r : ℝ) (α : DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n),
        e (r • α) = r • e α := by
  rcases topOpen_diffeomorph (M := M) Iℝ with ⟨φ⟩
  rcases deRhamCohomology_linearEquiv_of_diffeomorphic Iℝ Iℝ φ n with ⟨e⟩
  exact ⟨e.toAddEquiv, fun r α => e.map_smul r α⟩

set_option synthInstance.maxHeartbeats 80000

/--
The algebraic data identifying the de Rham quotient on the terminal open set
with the cycle-boundary quotient of the evaluated presheaf complex.
-/
structure TopOpenDeRhamCycleBoundaryIdentification [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M] (n : ℕ) where
  cycles :
    DeRhamClosedForms (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        (A := ℝ) n ≃+
      AddMonoidHom.ker
        ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).g.hom
  boundaries :
    (DeRhamExactClosedForms (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        (A := ℝ) n).toAddSubgroup.map cycles.toAddMonoidHom =
      AddMonoidHom.range
        ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abToCycles

/--
%%handwave
name:
  Closed forms are terminal-open cycles
statement:
  For the additive de Rham complex evaluated on the terminal open subset,
  the kernel of the outgoing differential in degree \(n\) is additively
  equivalent to the group of closed \(n\)-forms.
proof:
  Both sides have the same underlying forms.  The differential in the
  terminal-open complex is exterior differentiation, so its kernel condition
  is exactly closedness.
-/
noncomputable def topOpenDeRhamCyclesAddEquivClosedForms [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    DeRhamClosedForms (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        (A := ℝ) n ≃+
      AddMonoidHom.ker
        ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).g.hom where
  toFun omega := by
    refine ⟨omega.1, ?_⟩
    have hclosed :
        exteriorDerivative (I := Iℝ) (r := ∞) (omega : SmoothForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) = 0 := by
      have hdiff :
          deRhamDifferential (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
              (A := ℝ) n
              (omega : SmoothForms (I := Iℝ)
                (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) = 0 :=
        LinearMap.mem_ker.mp omega.2
      exact hdiff
    rw [AddMonoidHom.mem_ker]
    change
      AddCommGrpCat.Hom.hom
          ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).d n
            ((ComplexShape.up ℕ).next n))
          (omega : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) = 0
    rw [CochainComplex.next ℕ n]
    calc
      AddCommGrpCat.Hom.hom
          ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).d n (n + 1))
          (omega : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n)
          =
        exteriorDerivative (I := Iℝ) (r := ∞)
          (omega : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) :=
        smoothFormsAddPresheafTopCochainComplex_d_succ_apply
          (M := M) Iℝ n
          (omega : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n)
      _ = 0 := hclosed
  invFun eta := by
    refine ⟨eta.1, ?_⟩
    have hcycle := eta.2
    rw [AddMonoidHom.mem_ker] at hcycle
    change
      AddCommGrpCat.Hom.hom
          ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).d n
            ((ComplexShape.up ℕ).next n))
          (eta.1 : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) = 0 at hcycle
    rw [CochainComplex.next ℕ n] at hcycle
    change
      (eta.1 : SmoothForms (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) ∈
        LinearMap.ker
          (deRhamDifferential (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) n)
    change
      deRhamDifferential (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n
          (eta.1 : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) = 0
    calc
      deRhamDifferential (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n
          (eta.1 : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n)
          =
        exteriorDerivative (I := Iℝ) (r := ∞)
          (eta.1 : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) :=
        deRhamDifferential_apply
          (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ)
          (eta.1 : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n)
      _ =
        AddCommGrpCat.Hom.hom
          ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).d n (n + 1))
          (eta.1 : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) :=
        (smoothFormsAddPresheafTopCochainComplex_d_succ_apply
          (M := M) Iℝ n
          (eta.1 : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n)).symm
      _ = 0 := hcycle
  left_inv omega := by
    ext
    rfl
  right_inv eta := by
    ext
    rfl
  map_add' omega eta := by
    ext
    rfl

/--
%%handwave
name:
  A previous-degree form is an incoming terminal-open cochain
statement:
  A smooth \(n\)-form on the terminal open subset is the same object as an
  input to the incoming differential of the short complex centered in degree
  \(n+1\).
proof:
  The previous degree of \(n+1\) in the natural-number cochain complex is
  \(n\).
-/
noncomputable def topOpenDeRhamPrevFormAsIncomingCochain [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ)
    (theta : SmoothForms (I := Iℝ)
      (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) :
    (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc (n + 1)).X₁) := by
  let K := smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ
  change K.X ((ComplexShape.up ℕ).prev (n + 1))
  exact AddCommGrpCat.Hom.hom
    (K.XIsoOfEq (CochainComplex.prev_nat_succ n)).inv theta

/--
%%handwave
name:
  An incoming terminal-open cochain is a previous-degree form
statement:
  An input to the incoming differential of the short complex centered in
  degree \(n+1\) is a smooth \(n\)-form on the terminal open subset.
proof:
  The previous degree of \(n+1\) in the natural-number cochain complex is
  \(n\).
-/
noncomputable def topOpenDeRhamIncomingCochainAsPrevForm [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ)
    (theta :
      (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc (n + 1)).X₁)) :
    SmoothForms (I := Iℝ)
      (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n := by
  let K := smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ
  change K.X n
  exact AddCommGrpCat.Hom.hom
    (K.XIsoOfEq (CochainComplex.prev_nat_succ n)).hom theta

/--
%%handwave
name:
  Incoming terminal-open boundary is exterior differentiation
statement:
  The incoming boundary in the short complex centered in degree \(n+1\), when
  applied to a terminal-open \(n\)-form, is its exterior derivative.
proof:
  Identify the previous index of \(n+1\) with \(n\), then use the defining
  formula for the terminal-open differential.
-/
theorem topOpenDeRham_abToCycles_succ_apply [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ)
    (theta : SmoothForms (I := Iℝ)
      (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) :
    (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc (n + 1)).abToCycles
        (topOpenDeRhamPrevFormAsIncomingCochain (M := M) Iℝ n theta)).1 =
      exteriorDerivative (I := Iℝ) (r := ∞) theta := by
  let K := smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ
  have htransport :
      AddCommGrpCat.Hom.hom
          (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1))
          (topOpenDeRhamPrevFormAsIncomingCochain (M := M) Iℝ n theta) =
        AddCommGrpCat.Hom.hom (K.d n (n + 1)) theta := by
    have hcomp :=
      HomologicalComplex.XIsoOfEq_inv_comp_d
        K (CochainComplex.prev_nat_succ n) (n + 1)
    have happ :=
      congrArg (fun f => AddCommGrpCat.Hom.hom f theta) hcomp
    simpa only [K, topOpenDeRhamPrevFormAsIncomingCochain,
      CategoryTheory.comp_apply] using happ
  rw [← smoothFormsAddPresheafTopCochainComplex_d_succ_apply
    (M := M) Iℝ n theta]
  change
    AddCommGrpCat.Hom.hom
        (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1))
        (topOpenDeRhamPrevFormAsIncomingCochain (M := M) Iℝ n theta) =
      AddCommGrpCat.Hom.hom (K.d n (n + 1)) theta
  exact htransport

/--
%%handwave
name:
  Incoming terminal-open boundary is exterior differentiation, reverse form
statement:
  The incoming boundary of a short-complex input, viewed as a previous-degree
  form, is its exterior derivative.
proof:
  Convert the incoming cochain to the corresponding previous-degree form and
  apply the incoming-boundary formula.
-/
theorem topOpenDeRham_abToCycles_succ_apply_incoming [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ)
    (theta :
      (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc (n + 1)).X₁)) :
    (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc (n + 1)).abToCycles
        theta).1 =
      exteriorDerivative (I := Iℝ) (r := ∞)
        (topOpenDeRhamIncomingCochainAsPrevForm (M := M) Iℝ n theta) := by
  let K := smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ
  have htransport :
      AddCommGrpCat.Hom.hom
          (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1))
          theta =
        AddCommGrpCat.Hom.hom (K.d n (n + 1))
          (topOpenDeRhamIncomingCochainAsPrevForm (M := M) Iℝ n theta) := by
    have hcomp :=
      HomologicalComplex.XIsoOfEq_hom_comp_d
        K (CochainComplex.prev_nat_succ n) (n + 1)
    have happ :=
      congrArg (fun f => AddCommGrpCat.Hom.hom f theta) hcomp
    simpa only [K, topOpenDeRhamIncomingCochainAsPrevForm,
      CategoryTheory.comp_apply] using happ.symm
  rw [← smoothFormsAddPresheafTopCochainComplex_d_succ_apply
    (M := M) Iℝ n (topOpenDeRhamIncomingCochainAsPrevForm (M := M) Iℝ n theta)]
  change
    AddCommGrpCat.Hom.hom
        (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1))
        theta =
      AddCommGrpCat.Hom.hom (K.d n (n + 1))
        (topOpenDeRhamIncomingCochainAsPrevForm (M := M) Iℝ n theta)
  exact htransport

/--
%%handwave
name:
  Exact forms are terminal-open boundaries
statement:
  Under the identification of terminal-open cycles with closed forms, the
  exact closed forms correspond exactly to the image of the incoming
  differential in the terminal-open additive de Rham complex.
proof:
  In positive degree, both subgroups consist of forms of the shape
  \(d\theta\), using that the incoming differential is exterior
  differentiation in the previous degree.  In degree zero, the exact
  subgroup is zero and the incoming differential in the natural-number
  cochain complex is also zero.
tags:
  milestone
-/
theorem topOpenDeRhamExactClosedForms_map_cycles_eq_boundaries [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    (DeRhamExactClosedForms (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        (A := ℝ) n).toAddSubgroup.map
        (topOpenDeRhamCyclesAddEquivClosedForms (M := M) Iℝ n).toAddMonoidHom =
      AddMonoidHom.range
        ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abToCycles := by
  classical
  cases n with
  | zero =>
      ext z
      constructor
      · intro hz
        rcases AddSubgroup.mem_map.mp hz with ⟨omega, homega, hzomega⟩
        change omega ∈
          (DeRhamExactClosedForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) 0) at homega
        have hzero : (omega :
            DeRhamClosedForms (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
              (A := ℝ) 0) = 0 := by
          exact Subtype.ext (by
            change (omega : SmoothForms (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ 0) = 0
            simpa [DeRhamExactClosedForms, DeRhamExactForms] using homega)
        rw [← hzomega, hzero]
        simpa using
          (AddSubgroup.zero_mem
            (AddMonoidHom.range
              ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc 0).abToCycles))
      · intro hz
        rcases AddMonoidHom.mem_range.mp hz with ⟨theta, htheta⟩
        have hz0 : z = 0 := by
          rw [← htheta]
          ext
          change
            AddCommGrpCat.Hom.hom
                ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).d
                  ((ComplexShape.up ℕ).prev 0) 0)
                theta = 0
          simp
        rw [hz0]
        exact AddSubgroup.zero_mem _
  | succ n =>
      ext z
      constructor
      · intro hz
        rcases AddSubgroup.mem_map.mp hz with ⟨omega, homega, hzomega⟩
        change omega ∈
          (DeRhamExactClosedForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) (n + 1)) at homega
        change (omega : SmoothForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ (n + 1)) ∈
          DeRhamExactForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) (n + 1) at homega
        rw [DeRhamExactForms] at homega
        rcases homega with ⟨theta, htheta⟩
        rw [← hzomega]
        refine AddMonoidHom.mem_range.mpr
          ⟨topOpenDeRhamPrevFormAsIncomingCochain (M := M) Iℝ n theta, ?_⟩
        ext
        change
          (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc (n + 1)).abToCycles
            (topOpenDeRhamPrevFormAsIncomingCochain (M := M) Iℝ n theta)).1 =
            (omega : SmoothForms (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ (n + 1))
        rw [topOpenDeRham_abToCycles_succ_apply]
        rw [← htheta]
        exact (deRhamDifferential_apply
          (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) theta).symm
      · intro hz
        rcases AddMonoidHom.mem_range.mp hz with ⟨theta, htheta⟩
        rw [← htheta]
        refine AddSubgroup.mem_map.mpr ?_
        let thetaForm : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n :=
          topOpenDeRhamIncomingCochainAsPrevForm (M := M) Iℝ n theta
        let alphaForm : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ (n + 1) :=
          exteriorDerivative (I := Iℝ) (r := ∞) thetaForm
        have halpha_closed :
            alphaForm ∈ DeRhamClosedForms (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
              (A := ℝ) (n + 1) := by
          change
            deRhamDifferential (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
              (A := ℝ) (n + 1) alphaForm = 0
          simpa [alphaForm, deRhamDifferential_apply] using
            deRhamDifferential_comp_eq_zero (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
              (A := ℝ) thetaForm
        let alpha : DeRhamClosedForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) (n + 1) := ⟨alphaForm, halpha_closed⟩
        refine ⟨alpha, ?_, ?_⟩
        · change alpha ∈
            (DeRhamExactClosedForms (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
              (A := ℝ) (n + 1))
          change (alpha : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ (n + 1)) ∈
            DeRhamExactForms (I := Iℝ)
              (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
              (A := ℝ) (n + 1)
          rw [DeRhamExactForms]
          refine ⟨thetaForm, ?_⟩
          dsimp [alpha, alphaForm]
        · ext
          change
            (topOpenDeRhamCyclesAddEquivClosedForms (M := M) Iℝ (n + 1) alpha).1 =
              (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc (n + 1)).abToCycles
                theta).1
          change
            alphaForm =
              (((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc (n + 1)).abToCycles
                theta).1
          rw [topOpenDeRham_abToCycles_succ_apply_incoming]

/--
%%handwave
name:
  Terminal-open cycles and boundaries are closed and exact forms
statement:
  For the additive de Rham complex evaluated on the terminal open subset,
  cycles are precisely closed forms and boundaries are precisely exact closed
  forms.
proof:
  The outgoing differential of the evaluated presheaf complex is exterior
  differentiation, so its kernel is the subgroup of closed forms.  In positive
  degree the incoming differential is the previous exterior derivative, so its
  image is the subgroup of exact forms; in degree zero the incoming map is
  zero, matching the convention that exact zero-forms form the zero subgroup.
tags:
  milestone
-/
theorem topOpenDeRhamCycleBoundaryIdentification [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    Nonempty (TopOpenDeRhamCycleBoundaryIdentification (M := M) Iℝ n) := by
  refine ⟨{ cycles := topOpenDeRhamCyclesAddEquivClosedForms (M := M) Iℝ n
            boundaries := ?_ }⟩
  exact topOpenDeRhamExactClosedForms_map_cycles_eq_boundaries (M := M) Iℝ n

/--
%%handwave
name:
  Constant multiplication sends a represented terminal-open cycle to the scaled cycle
statement:
  On the explicit terminal-open cycle-boundary quotient, the endomorphism
  induced by constant multiplication sends the quotient class represented by a
  closed form \(\omega\) to the class represented by \(r\omega\).
proof:
  The left-homology naturality square identifies the quotient endomorphism on
  representatives with the induced map on cycles.  The induced map on cycles
  is determined by its inclusion into the middle term of the short complex,
  where it is exactly the degree-\(n\) cochain endomorphism, namely
  multiplication by \(r\).
tags:
  milestone
-/
theorem smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd_mk_cycles
    [NormedSpace ℝ E]
    (Iℝ : ModelWithCorners ℝ E H) [IsManifold Iℝ ∞ M]
    (n : ℕ) (r : ℝ)
    (omega : DeRhamClosedForms (I := Iℝ)
      (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
      (A := ℝ) n) :
    smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd
        (M := M) Iℝ n r
      (QuotientAddGroup.mk'
        (AddMonoidHom.range
          ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abToCycles)
        (topOpenDeRhamCyclesAddEquivClosedForms (M := M) Iℝ n omega)) =
      QuotientAddGroup.mk'
        (AddMonoidHom.range
          ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abToCycles)
        (topOpenDeRhamCyclesAddEquivClosedForms (M := M) Iℝ n (r • omega)) := by
  let K := smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ
  let S := K.sc n
  let φ : S ⟶ S :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{max v m}
      (ComplexShape.up ℕ) n).map
      (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r)
  let c := topOpenDeRhamCyclesAddEquivClosedForms (M := M) Iℝ n omega
  let c' := topOpenDeRhamCyclesAddEquivClosedForms (M := M) Iℝ n (r • omega)
  have hcycle : AddCommGrpCat.Hom.hom
      (ShortComplex.cyclesMap' φ S.abLeftHomologyData S.abLeftHomologyData) c = c' := by
    apply Subtype.ext
    have h :=
      congrArg (fun f => AddCommGrpCat.Hom.hom f c)
        (ShortComplex.cyclesMap'_i φ S.abLeftHomologyData S.abLeftHomologyData)
    change
      AddCommGrpCat.Hom.hom S.abLeftHomologyData.i
          (AddCommGrpCat.Hom.hom
            (ShortComplex.cyclesMap' φ S.abLeftHomologyData S.abLeftHomologyData) c) =
        AddCommGrpCat.Hom.hom φ.τ₂
          (AddCommGrpCat.Hom.hom S.abLeftHomologyData.i c) at h
    change
      (AddCommGrpCat.Hom.hom
            (ShortComplex.cyclesMap' φ S.abLeftHomologyData S.abLeftHomologyData) c).1 =
        c'.1
    rw [show
      (AddCommGrpCat.Hom.hom
            (ShortComplex.cyclesMap' φ S.abLeftHomologyData S.abLeftHomologyData) c).1 =
          AddCommGrpCat.Hom.hom φ.τ₂ c.1 by
        simpa [S] using h]
    change
      AddCommGrpCat.Hom.hom φ.τ₂
          (omega : SmoothForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n) =
        r • (omega : SmoothForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n)
    simpa [K, S, φ] using
      smoothFormsAddPresheafTopCochainComplexScalarEnd_f_apply
        (M := M) Iℝ n r
        (omega : SmoothForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m}))) ℝ n)
  have hπ :=
    congrArg (fun f => AddCommGrpCat.Hom.hom f c)
      (ShortComplex.leftHomologyπ_naturality' φ
        S.abLeftHomologyData S.abLeftHomologyData)
  simpa [smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd,
    K, S, φ, c, c', hcycle] using hπ

/--
%%handwave
name:
  Top-open de Rham cohomology is the explicit smooth-form quotient
statement:
  The de Rham cohomology of the terminal open subset is additively isomorphic
  to the explicit quotient of terminal-open cycles by terminal-open
  boundaries in degree \(n\).
proof:
  The outgoing differential in the terminal-open complex is exterior
  differentiation, so its cycles are closed forms.  In positive degree the
  incoming differential is the previous exterior derivative, so its boundaries
  are exact forms; in degree \(0\) the incoming differential is zero because
  the natural-number-indexed cochain complex has no negative predecessor.
tags:
  milestone
-/
theorem topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCochainHomologyQuotient
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    Nonempty
      (DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n ≃+
        smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n) := by
  rcases topOpenDeRhamCycleBoundaryIdentification (M := M) Iℝ n with
    ⟨identification⟩
  let eDeRham :
      DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n ≃+
        (DeRhamClosedForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) n ⧸
          (DeRhamExactClosedForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) n).toAddSubgroup) :=
    AddEquiv.refl _
  let eQuot :
      (DeRhamClosedForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n ⧸
        (DeRhamExactClosedForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n).toAddSubgroup) ≃+
        smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n :=
    addQuotientEquivOfMapEq identification.cycles
      (DeRhamExactClosedForms (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        (A := ℝ) n).toAddSubgroup
      (AddMonoidHom.range
        ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abToCycles)
      identification.boundaries
  exact ⟨eDeRham.trans eQuot⟩

/--
%%handwave
name:
  Top-open de Rham cohomology is top-open smooth-form homology
statement:
  The de Rham cohomology of the terminal open subset is additively
  isomorphic to the homology of the terminal-open presheaf de Rham complex.
proof:
  Compose [the identification of terminal-open de Rham cohomology with the explicit cycle-boundary quotient](lean:JJMath.Manifold.topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCochainHomologyQuotient) with [the explicit quotient model for terminal-open smooth-form homology](lean:JJMath.Manifold.smoothFormsAddPresheafTopCohomology_addEquiv_explicitQuotient).
tags:
  milestone
-/
theorem topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    Nonempty
      (DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n ≃+
        ↥((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).homology n)) := by
  rcases
    topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCochainHomologyQuotient
      (M := M) Iℝ n with
    ⟨eDeRhamQuot⟩
  rcases smoothFormsAddPresheafTopCohomology_addEquiv_explicitQuotient
      (M := M) Iℝ n with
    ⟨eHomologyQuot⟩
  exact ⟨eDeRhamQuot.trans eHomologyQuot.symm⟩

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

/--
%%handwave
name:
  The terminal-open de Rham quotient comparison respects constant multiplication
statement:
  The additive comparison between terminal-open de Rham cohomology and the
  explicit terminal-open cycle-boundary quotient may be chosen so that scalar
  multiplication of de Rham classes corresponds to the quotient endomorphism
  induced by constant multiplication on the terminal-open de Rham complex.
proof:
  Use quotient induction on closed forms.  Multiplication by a constant
  preserves closed forms and exact forms, and the identification of closed
  forms with terminal-open cycles carries \(r\omega\) to the cycle obtained by
  applying the degree-\(n\) scalar endomorphism to the cycle represented by
  \(\omega\).
tags:
  milestone
-/
theorem exists_topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCochainHomologyQuotient_with_leftHomologyMap_smul
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    ∃ e :
      DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n ≃+
        smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n,
      ∀ (r : ℝ)
        (α : DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n),
        e (r • α) =
          smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd
            (M := M) Iℝ n r (e α) := by
  let cycles :=
    topOpenDeRhamCyclesAddEquivClosedForms (M := M) Iℝ n
  have hboundaries :
      (DeRhamExactClosedForms (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        (A := ℝ) n).toAddSubgroup.map cycles.toAddMonoidHom =
        AddMonoidHom.range
          ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abToCycles := by
    simpa [cycles] using
      topOpenDeRhamExactClosedForms_map_cycles_eq_boundaries (M := M) Iℝ n
  let eDeRham :
      DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n ≃+
        (DeRhamClosedForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) n ⧸
          (DeRhamExactClosedForms (I := Iℝ)
            (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
            (A := ℝ) n).toAddSubgroup) :=
    AddEquiv.refl _
  let eQuot :
      (DeRhamClosedForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n ⧸
        (DeRhamExactClosedForms (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n).toAddSubgroup) ≃+
        smoothFormsAddPresheafTopCochainHomologyQuotient (M := M) Iℝ n :=
    addQuotientEquivOfMapEq cycles
      (DeRhamExactClosedForms (I := Iℝ)
        (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
        (A := ℝ) n).toAddSubgroup
      (AddMonoidHom.range
        ((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).sc n).abToCycles)
      hboundaries
  refine ⟨eDeRham.trans eQuot, ?_⟩
  intro r α
  refine Quotient.inductionOn' α ?_
  intro omega
  simpa [eDeRham, eQuot, cycles, addQuotientEquivOfMapEq] using
    (smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd_mk_cycles
      (M := M) Iℝ n r omega).symm

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 80000

/--
%%handwave
name:
  Top-open de Rham cohomology is top-open smooth-form homology compatibly with constants
statement:
  The additive comparison between de Rham cohomology of the terminal open
  subset and top-open smooth-form homology may be chosen so that multiplying a
  de Rham class by a real number corresponds to the homology map induced by
  multiplying top-open forms by the same constant.
proof:
  Refine the explicit cycle-boundary quotient comparison.  Constant
  multiplication preserves closed forms and exact forms, and under the
  identification of closed forms with cycles it is the same operation as the
  chain endomorphism obtained by evaluating the presheaf scalar endomorphism
  on the terminal open subset.
tags:
  milestone
-/
theorem exists_topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    ∃ e :
      DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n ≃+
        ↥((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).homology n),
      ∀ (r : ℝ)
        (α : DeRhamCohomology (I := Iℝ)
          (M := (⊤ : TopologicalSpace.Opens (TopCat.of M : TopCat.{m})))
          (A := ℝ) n),
        e (r • α) =
          (HomologicalComplex.homologyMap
            (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r) n)
            (e α) := by
  rcases
    exists_topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCochainHomologyQuotient_with_leftHomologyMap_smul
      (M := M) Iℝ n with
    ⟨eDeRhamQuot, hDeRhamQuot⟩
  let eHomologyQuot :=
    smoothFormsAddPresheafTopCohomologyExplicitQuotientAddEquiv
      (M := M) Iℝ n
  refine ⟨eDeRhamQuot.trans eHomologyQuot.symm, ?_⟩
  intro r α
  have hquot := hDeRhamQuot r α
  have hnat :=
    smoothFormsAddPresheafTopCohomologyExplicitQuotientAddEquiv_symm_scalarEnd
      (M := M) Iℝ n r (eDeRhamQuot α)
  calc
    (eDeRhamQuot.trans eHomologyQuot.symm) (r • α)
        = eHomologyQuot.symm (eDeRhamQuot (r • α)) := rfl
    _ = eHomologyQuot.symm
        (smoothFormsAddPresheafTopCochainHomologyQuotientScalarEnd
          (M := M) Iℝ n r (eDeRhamQuot α)) := by
          rw [hquot]
    _ =
        (HomologicalComplex.homologyMap
          (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r) n)
          (eHomologyQuot.symm (eDeRhamQuot α)) := by
          simpa [eHomologyQuot] using hnat
    _ =
        (HomologicalComplex.homologyMap
          (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r) n)
          ((eDeRhamQuot.trans eHomologyQuot.symm) α) := rfl

/--
%%handwave
name:
  Ordinary de Rham cohomology is top-open smooth-form homology
statement:
  The usual quotient of closed smooth forms by exact smooth forms is
  additively isomorphic to the homology of the top-open presheaf de Rham
  complex.
proof:
  Compose [the isomorphism induced by restriction to the terminal open subset](lean:JJMath.Manifold.deRhamCohomology_addEquiv_topOpenDeRhamCohomology) with [the quotient comparison for the terminal-open complex](lean:JJMath.Manifold.topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology).
tags:
  milestone
-/
theorem deRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    Nonempty
      (DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        ↥((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).homology n)) := by
  rcases deRhamCohomology_addEquiv_topOpenDeRhamCohomology
      (M := M) Iℝ n with
    ⟨eTopOpen⟩
  rcases topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology
      (M := M) Iℝ n with
    ⟨eTopComplex⟩
  exact ⟨eTopOpen.trans eTopComplex⟩

/--
%%handwave
name:
  Ordinary de Rham cohomology is top-open smooth-form homology compatibly with constants
statement:
  The additive comparison between ordinary real de Rham cohomology and
  top-open smooth-form homology may be chosen so that multiplying a de Rham
  class by a real number corresponds to the homology map induced by
  multiplying top-open forms by the same constant.
proof:
  Compose [the scalar-compatible comparison with the terminal open subset](lean:JJMath.Manifold.exists_deRhamCohomology_addEquiv_topOpenDeRhamCohomology_with_smul) with [the scalar-compatible quotient comparison for the terminal open subset](lean:JJMath.Manifold.exists_topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul).
tags:
  milestone
-/
theorem exists_deRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    (n : ℕ) :
    ∃ e :
      DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        ↥((smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ).homology n),
      ∀ (r : ℝ) (α : DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n),
        e (r • α) =
          (HomologicalComplex.homologyMap
            (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r) n)
            (e α) := by
  rcases exists_deRhamCohomology_addEquiv_topOpenDeRhamCohomology_with_smul
      (M := M) Iℝ n with
    ⟨eTopOpen, hTopOpen⟩
  rcases
    exists_topOpenDeRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul
      (M := M) Iℝ n with
    ⟨eTopComplex, hTopComplex⟩
  refine ⟨eTopOpen.trans eTopComplex, ?_⟩
  intro r α
  calc
    (eTopOpen.trans eTopComplex) (r • α)
        = eTopComplex (r • eTopOpen α) := by
          change eTopComplex (eTopOpen (r • α)) =
            eTopComplex (r • eTopOpen α)
          rw [hTopOpen]
    _ = (HomologicalComplex.homologyMap
          (smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r) n)
        ((eTopOpen.trans eTopComplex) α) := by
          exact hTopComplex r (eTopOpen α)

/--
%%handwave
name:
  Ordinary de Rham cohomology is the homology of global smooth forms
statement:
  The usual quotient of closed smooth forms by exact smooth forms is
  additively isomorphic to the homology of the global-sections complex of the
  sheaf de Rham complex.
proof:
  Combine [the quotient comparison with top-open smooth-form homology](lean:JJMath.Manifold.deRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology) and [the homology equivalence between global sections and top-open sections](lean:JJMath.Manifold.smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_smoothFormsAddPresheafTopCohomology).
tags:
  milestone
-/
theorem deRhamCohomology_addEquiv_smoothFormsAddSheafGlobalSectionsCohomology
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (n : ℕ) :
    Nonempty
      (DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        ↥((smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ).homology n)) := by
  rcases deRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology
      (M := M) Iℝ n with
    ⟨eDeRhamTop⟩
  rcases
    smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_smoothFormsAddPresheafTopCohomology
      (M := M) Iℝ n with
    ⟨eGlobalTop⟩
  exact ⟨eDeRhamTop.trans eGlobalTop.symm⟩

/--
%%handwave
name:
  De Rham cohomology is global smooth-form homology compatibly with constants
statement:
  The additive comparison between ordinary real de Rham cohomology and the
  homology of the global-sections sheaf de Rham complex may be chosen so that
  multiplying a de Rham class by a real number corresponds to the homology map
  induced by multiplying each sheaf of smooth forms by the same constant.
proof:
  Compose [the scalar-compatible comparison with top-open smooth-form homology](lean:JJMath.Manifold.exists_deRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul) with [the scalar-compatible comparison between global smooth-form homology and top-open smooth-form homology](lean:JJMath.Manifold.exists_smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul).
tags:
  milestone
-/
theorem exists_deRhamCohomology_addEquiv_smoothFormsAddSheafGlobalSectionsCohomology_with_map_smul
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    (n : ℕ) :
    ∃ e :
      DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        ↥((smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ).homology n),
      ∀ (r : ℝ) (α : DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n),
        e (r • α) =
          (HomologicalComplex.homologyMap
            (((CategoryTheory.Sheaf.Γ
                (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
                AddCommGrpCat.{max v m}).mapHomologicalComplex
                  (ComplexShape.up ℕ)).map
              (smoothFormsAddSheafCochainComplexScalarEnd (M := M) Iℝ r)) n)
            (e α) := by
  rcases
    exists_deRhamCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul
      (M := M) Iℝ n with
    ⟨eDeRhamTop, hDeRhamTop⟩
  rcases
    exists_smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_smoothFormsAddPresheafTopCohomology_with_map_smul
      (M := M) Iℝ n with
    ⟨eGlobalTop, hGlobalTop⟩
  refine ⟨eDeRhamTop.trans eGlobalTop.symm, ?_⟩
  intro r α
  apply eGlobalTop.injective
  let globalEnd :
      smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ ⟶
        smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ :=
    (((CategoryTheory.Sheaf.Γ
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
      (smoothFormsAddSheafCochainComplexScalarEnd (M := M) Iℝ r))
  let topEnd :
      smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ ⟶
        smoothFormsAddPresheafTopCochainComplex (M := M) Iℝ :=
    smoothFormsAddPresheafTopCochainComplexScalarEnd (M := M) Iℝ r
  let β : ↥((smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ).homology n) :=
    (eDeRhamTop.trans eGlobalTop.symm) α
  have hβ : eGlobalTop β = eDeRhamTop α := by
    simp [β]
  have hlast :
      (HomologicalComplex.homologyMap topEnd n) (eDeRhamTop α) =
        eGlobalTop ((HomologicalComplex.homologyMap globalEnd n)
          ((eDeRhamTop.trans eGlobalTop.symm) α)) := by
    change (HomologicalComplex.homologyMap topEnd n) (eDeRhamTop α) =
      eGlobalTop ((HomologicalComplex.homologyMap globalEnd n) β)
    rw [← hβ]
    simpa [globalEnd, topEnd] using (hGlobalTop r β).symm
  calc
    eGlobalTop ((eDeRhamTop.trans eGlobalTop.symm) (r • α))
        = eDeRhamTop (r • α) := by
          simp
    _ = (HomologicalComplex.homologyMap topEnd n) (eDeRhamTop α) := by
          simpa [topEnd] using hDeRhamTop r α
    _ = eGlobalTop ((HomologicalComplex.homologyMap globalEnd n)
          ((eDeRhamTop.trans eGlobalTop.symm) α)) := hlast

/--
%%handwave
name:
  Acyclic smooth-form resolutions compute smooth-universe constant-sheaf cohomology
statement:
  Suppose the augmented sheaf de Rham complex is exact, and suppose all
  smooth-form sheaves have vanishing positive sheaf cohomology.  Then the
  cohomology of the global-sections complex of smooth forms is additively
  isomorphic to the sheaf cohomology of the constant real sheaf in the
  smooth-form coefficient universe.
proof:
  Apply [the acyclic-resolution theorem for sheaf cohomology](lean:CategoryTheory.Sheaf.globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution) to the augmented sheaf de Rham complex.
-/
theorem smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_realConstantSheafSmoothFormsUniverseCohomology_of_acyclic_deRham_resolution
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H)
    [IsManifold Iℝ ∞ M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      AddCommGrpCat.{max v m}]
    [HasExt.{max v m}
      (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m})]
    (hexact_zero :
      ∃ ε :
        realConstantAddSheafSmoothFormsUniverse (TopCat.of M : TopCat.{m}) ⟶
          smoothFormsAddSheaf (M := M) Iℝ 0,
        ∃ hε : ε ≫ deRhamDifferentialAddSheafHom (M := M) Iℝ 0 = 0,
          ({ f := ε,
             g := deRhamDifferentialAddSheafHom (M := M) Iℝ 0,
             zero := hε } :
            ShortComplex
              (Sheaf (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
                AddCommGrpCat.{max v m})).Exact ∧ Mono ε)
    (hexact_pos :
      ∀ n : ℕ,
        (smoothFormsAddSheafCochainComplex (M := M) Iℝ).ExactAt (n + 1))
    (hacyclic :
      ∀ p q : ℕ, 0 < q →
        Subsingleton ((smoothFormsAddSheaf (M := M) Iℝ p).H q))
    (n : ℕ) :
    Nonempty
      (↥((smoothFormsAddSheafGlobalSectionsCochainComplex (M := M) Iℝ).homology n) ≃+
        (realConstantAddSheafSmoothFormsUniverse (TopCat.of M : TopCat.{m})).H n) := by
  classical
  haveI : PreservesFilteredColimitsOfSize.{m, m}
      (forget AddCommGrpCat.{max v m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max v m})
  rcases hexact_zero with ⟨ε, hε, hexact_zero, hmono_ε⟩
  exact
    CategoryTheory.Sheaf.globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution
      (J := Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
      (F := realConstantAddSheafSmoothFormsUniverse (TopCat.of M : TopCat.{m}))
      (K := smoothFormsAddSheafCochainComplex (M := M) Iℝ)
      ε hε hexact_zero hmono_ε hexact_pos hacyclic n

/--
%%handwave
name:
  Universe lift preserves abelian sheafification under plus-plus hypotheses
statement:
  If the site has the cover-indexed colimits and multiequalizer limits used by
  the plus-plus sheafification construction, then applying the universe-lift
  functor to abelian groups commutes with sheafification.
proof:
  Apply the standard plus-plus compatibility theorem.  The universe-lift
  functor for abelian groups preserves the required cover colimits and
  multiequalizer limits, and the forgetful functors detect the concrete
  sheafification construction.
tags:
  milestone
-/
theorem addCommGrp_uliftFunctor_preservesSheafification_of_plusPlus
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [∀ (S : MulticospanShape.{max vC uC, max vC uC}),
      HasLimitsOfShape (WalkingMulticospan S) AddCommGrpCat.{m}]
    [∀ (S : MulticospanShape.{max vC uC, max vC uC}),
      HasLimitsOfShape (WalkingMulticospan S) AddCommGrpCat.{max v m}]
    [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ AddCommGrpCat.{m}]
    [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ AddCommGrpCat.{max v m}]
    [∀ X : C,
      PreservesColimitsOfShape (J.Cover X)ᵒᵖ AddCommGrpCat.uliftFunctor.{v, m}]
    [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ AddCommGrpCat.{m}),
      PreservesLimit (W.index P).multicospan AddCommGrpCat.uliftFunctor.{v, m}]
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget AddCommGrpCat.{m})]
    [∀ X : C,
      PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget AddCommGrpCat.{max v m})]
    [PreservesLimitsOfSize.{max vC uC, max vC uC} (forget AddCommGrpCat.{m})]
    [PreservesLimitsOfSize.{max vC uC, max vC uC}
      (forget AddCommGrpCat.{max v m})] :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{v, m} := by
  exact CategoryTheory.GrothendieckTopology.instPreservesSheafification
    (C := C) (J := J) (D := AddCommGrpCat.{m}) (E := AddCommGrpCat.{max v m})
    AddCommGrpCat.uliftFunctor.{v, m}

/--
%%handwave
name:
  Universe lift preserves abelian sheafification on open-set sites
statement:
  On the open-set site of a topological space, applying the universe-lift
  functor to abelian groups commutes with sheafification.
proof:
  The cover categories of the open-set site are filtered in the universe of
  the space.  The universe-lift functor for abelian groups preserves the
  cover-indexed colimits and the multiequalizer limits used in the plus-plus
  construction, and the forgetful functors preserve the corresponding cover
  colimits.  Apply the plus-plus compatibility theorem.
tags:
  milestone
-/
theorem opens_addCommGrp_uliftFunctor_preservesSheafification
    (X : TopCat.{m}) :
    (Opens.grothendieckTopology X).PreservesSheafification
      AddCommGrpCat.uliftFunctor.{v, m} := by
  classical
  haveI : PreservesFilteredColimitsOfSize.{m, m}
      (forget AddCommGrpCat.{m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{m})
  haveI : PreservesFilteredColimitsOfSize.{m, m}
      (forget AddCommGrpCat.{max v m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max v m})
  haveI : PreservesLimitsOfSize.{m, m} (forget AddCommGrpCat.{m}) :=
    preservesLimitsOfSize_shrink (forget AddCommGrpCat.{m})
  haveI : PreservesLimitsOfSize.{m, m} (forget AddCommGrpCat.{max v m}) :=
    preservesLimitsOfSize_shrink (forget AddCommGrpCat.{max v m})
  exact
    (addCommGrp_uliftFunctor_preservesSheafification_of_plusPlus.{v, m, m, m}
      (J := Opens.grothendieckTopology X) :
      (Opens.grothendieckTopology X).PreservesSheafification
        AddCommGrpCat.uliftFunctor.{v, m})

/--
%%handwave
name:
  The universe-lifted integer constant sheaf is the larger integer constant sheaf
statement:
  The constant sheaf with value \(\mathbb Z\) in the larger coefficient
  universe is isomorphic to the universe lift of the ordinary integer constant
  sheaf.
proof:
  Use compatibility of universe lift with sheafification and the canonical
  additive isomorphism between the two universe-lifted copies of \(\mathbb Z\).
tags:
  milestone
-/
theorem intConstantAddSheafUniverse_iso_sheafCompose_ulift_intConstantAddSheaf
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    Nonempty
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}).obj
          (AddCommGrpCat.of (ULift.{max v m} ℤ)) ≅
        (sheafCompose (Opens.grothendieckTopology X)
          AddCommGrpCat.uliftFunctor.{v, m}).obj
            ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m}).obj
              (AddCommGrpCat.of (ULift.{m} ℤ)))) := by
  let J := Opens.grothendieckTopology X
  let A : AddCommGrpCat.{m} := AddCommGrpCat.of (ULift.{m} ℤ)
  let U : AddCommGrpCat.{m} ⥤ AddCommGrpCat.{max v m} :=
    AddCommGrpCat.uliftFunctor.{v, m}
  let B : AddCommGrpCat.{max v m} := AddCommGrpCat.of (ULift.{max v m} ℤ)
  haveI : J.PreservesSheafification U := by
    dsimp [U]
    exact opens_addCommGrp_uliftFunctor_preservesSheafification X
  let coeffIso : U.obj A ≅ B :=
    intULiftULiftAddEquiv.{v, m}.toAddCommGrpIso
  let hconst :
      (sheafCompose J U).obj ((constantSheaf J AddCommGrpCat.{m}).obj A) ≅
      (constantSheaf J AddCommGrpCat.{max v m}).obj (U.obj A) :=
    (constantCommuteCompose J U).app A
  let hcoeff :
      (constantSheaf J AddCommGrpCat.{max v m}).obj (U.obj A) ≅
      (constantSheaf J AddCommGrpCat.{max v m}).obj B :=
    (constantSheaf J AddCommGrpCat.{max v m}).mapIso coeffIso
  exact ⟨(hconst ≪≫ hcoeff).symm⟩

/--
%%handwave
name:
  Universe lift preserves finite limits of abelian sheaves
statement:
  Applying the universe-lift functor for abelian groups to an abelian sheaf
  preserves finite limits.
proof:
  Limits of sheaves are computed on the underlying presheaves.  The
  universe-lift functor for abelian groups preserves finite limits, so
  objectwise postcomposition with it sends limiting cones of sheaves to
  limiting cones.
tags:
  milestone
-/
noncomputable instance sheafCompose_uliftFunctor_preservesFiniteLimits
    (X : TopCat.{m}) :
    PreservesFiniteLimits
      (sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{v, m}) := by
  let J := Opens.grothendieckTopology X
  let U : AddCommGrpCat.{m} ⥤ AddCommGrpCat.{max v m} :=
    AddCommGrpCat.uliftFunctor.{v, m}
  constructor
  intro K _ _
  change PreservesLimitsOfShape K (sheafCompose J U)
  exact CategoryTheory.Sheaf.sheafCompose_preservesLimitsOfShape_of_preserves
    (J := J) (F := U)

/--
%%handwave
name:
  Universe lift preserves finite colimits of abelian sheaves
statement:
  Applying the universe-lift functor for abelian groups to an abelian sheaf
  preserves finite colimits.
proof:
  Finite colimits of abelian sheaves are formed by sheafifying the objectwise
  finite colimit.  The universe-lift functor for abelian groups preserves
  finite colimits and commutes with sheafification, so it preserves the
  resulting finite colimits of sheaves.
tags:
  milestone
-/
noncomputable instance sheafCompose_uliftFunctor_preservesFiniteColimits
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    PreservesFiniteColimits
      (sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{v, m}) := by
  let J := Opens.grothendieckTopology X
  let U : AddCommGrpCat.{m} ⥤ AddCommGrpCat.{max v m} :=
    AddCommGrpCat.uliftFunctor.{v, m}
  haveI : J.PreservesSheafification U := by
    dsimp [U]
    exact opens_addCommGrp_uliftFunctor_preservesSheafification X
  constructor
  intro K _ _
  change PreservesColimitsOfShape K (sheafCompose J U)
  exact
    CategoryTheory.Sheaf.sheafCompose_preservesColimitsOfShape_of_preservesSheafification
      (J := J) (F := U) (K := K)

/--
%%handwave
name:
  Universe lift is fully faithful on abelian sheaves
statement:
  Applying the universe-lift functor for abelian groups to all values of a
  sheaf identifies morphisms of abelian sheaves before and after the universe
  change.
proof:
  The universe-lift functor for abelian groups is fully faithful.  Since
  morphisms of sheaves are morphisms of the underlying presheaves, and
  postcomposition by a fully faithful functor is fully faithful on presheaves,
  the same holds after restricting to sheaves.
tags:
  milestone
-/
noncomputable def sheafCompose_uliftFunctor_fullyFaithful
    (X : TopCat.{m}) :
    (sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{v, m}).FullyFaithful := by
  exact CategoryTheory.fullyFaithfulSheafCompose
    (J := Opens.grothendieckTopology X)
    AddCommGrpCat.uliftFunctorFullyFaithful

/--
%%handwave
name:
  Universe lift is fully faithful on complexes of abelian sheaves
statement:
  The universe-lift functor on abelian sheaves induces a fully faithful
  functor on cochain complexes.
proof:
  Apply full faithfulness component by component.  A chain map between lifted
  complexes has a unique componentwise preimage, and the commutation with the
  differentials follows because universe lift is faithful.
tags:
  milestone
-/
noncomputable def sheafCompose_uliftFunctor_mapHomologicalComplex_fullyFaithful
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    ((sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{v, m}).mapHomologicalComplex
        (ComplexShape.up ℤ)).FullyFaithful := by
  exact
    CategoryTheory.Functor.mapHomologicalComplex_fullyFaithful
      (sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{v, m})
      (sheafCompose_uliftFunctor_fullyFaithful (X := X))
      (ComplexShape.up ℤ)

/--
%%handwave
name:
  Fully faithful complex-level universe lift descends to the homotopy category
statement:
  If universe lift is fully faithful on cochain complexes of abelian sheaves,
  then it is fully faithful after quotienting chain maps by chain homotopy.
proof:
  The homotopy category is the quotient of the category of complexes by chain
  homotopy.  Since componentwise universe lift identifies both chain maps and
  homotopies, it identifies the quotient hom-sets as well.
tags:
  milestone
-/
noncomputable def sheafCompose_uliftFunctor_mapHomotopyCategory_fullyFaithful_of_mapHomologicalComplex
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    (h :
      ((sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{v, m}).mapHomologicalComplex
          (ComplexShape.up ℤ)).FullyFaithful) :
    ((sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{v, m}).mapHomotopyCategory
        (ComplexShape.up ℤ)).FullyFaithful := by
  let F :=
    sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{v, m}
  exact
    CategoryTheory.Functor.mapHomotopyCategory_fullyFaithful_of_mapHomologicalComplex
      (F := F) (c := ComplexShape.up ℤ) h
      (fun {K L f g} hhom =>
        CategoryTheory.Functor.homotopyOfMapHomotopy
          (F := F) (sheafCompose_uliftFunctor_fullyFaithful (X := X)) hhom)

/--
%%handwave
name:
  Universe lift is fully faithful on homotopy categories of complexes of abelian sheaves
statement:
  The universe-lift functor on abelian sheaves induces a fully faithful
  functor on the homotopy category of cochain complexes.
proof:
  A chain map between lifted complexes is uniquely the lift of a chain map
  before universe change because universe lift is fully faithful objectwise.
  The same argument applies to homotopies, so quotienting by homotopy
  preserves full faithfulness.
tags:
  milestone
-/
noncomputable def sheafCompose_uliftFunctor_mapHomotopyCategory_fullyFaithful
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    ((sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{v, m}).mapHomotopyCategory
        (ComplexShape.up ℤ)).FullyFaithful := by
  exact
    sheafCompose_uliftFunctor_mapHomotopyCategory_fullyFaithful_of_mapHomologicalComplex
      (X := X)
      (sheafCompose_uliftFunctor_mapHomologicalComplex_fullyFaithful (X := X))

/--
%%handwave
name:
  Universe lift preserves homotopy-category quasi-isomorphisms
statement:
  The universe-lift functor on abelian sheaves sends quasi-isomorphisms of
  cochain complexes, viewed in the homotopy category, to quasi-isomorphisms.
proof:
  Universe lift is exact, hence preserves homology of cochain complexes.  A
  morphism in the homotopy category is a quasi-isomorphism precisely when it
  induces isomorphisms on all homology objects, so exactness carries this
  property across universe change.
tags:
  milestone
-/
theorem sheafCompose_uliftFunctor_mapHomotopyCategory_preserves_quasiIso
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})
        (ComplexShape.up ℤ)
      ≤
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})
        (ComplexShape.up ℤ)).inverseImage
          ((sheafCompose (Opens.grothendieckTopology X)
            AddCommGrpCat.uliftFunctor.{v, m}).mapHomotopyCategory
              (ComplexShape.up ℤ)) := by
  intro K L f hf
  let F :=
    sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{v, m}
  obtain ⟨φ, rfl⟩ :=
    (HomotopyCategory.quotient
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})
      (ComplexShape.up ℤ)).map_surjective f
  change HomotopyCategory.quasiIso _ _
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})
        (ComplexShape.up ℤ)).map φ))
  rw [Functor.mapHomotopyCategory_map]
  have hφ :
      HomologicalComplex.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})
        (ComplexShape.up ℤ) φ :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff
      (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})
      (c := ComplexShape.up ℤ) φ).1 (by simpa using hf)
  haveI : QuasiIso φ := hφ
  letI : F.PreservesHomology := by
    infer_instance
  have hmap :
      HomologicalComplex.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})
        (ComplexShape.up ℤ)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
    change QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
    infer_instance
  exact
    (HomotopyCategory.quotient_map_mem_quasiIso_iff
      (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})
      (c := ComplexShape.up ℤ)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).2 hmap

noncomputable def sheafCompose_uliftFunctor_mapHomotopyCategory_quasiIsoLocalizerMorphism
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    LocalizerMorphism
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})
        (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})
        (ComplexShape.up ℤ)) where
  functor :=
    (sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{v, m}).mapHomotopyCategory
        (ComplexShape.up ℤ)
  map :=
    sheafCompose_uliftFunctor_mapHomotopyCategory_preserves_quasiIso (X := X)

/--
%%handwave
name:
  The localized hom-set map induced by universe lift
statement:
  Between two ordinary-universe complexes of abelian sheaves, universe lift
  induces the natural map on morphisms in the homotopy category localized at
  quasi-isomorphisms.
proof:
  This is the canonical map associated to the morphism of localizing systems
  given by universe lift and preservation of quasi-isomorphisms.
tags:
  milestone
-/
noncomputable abbrev sheafCompose_uliftFunctor_mapHomotopyCategory_localizedHomMap
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasDerivedCategory
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})]
    [HasDerivedCategory
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})]
    (K L :
      HomotopyCategory
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})
        (ComplexShape.up ℤ)) :
    ((DerivedCategory.Qh
      (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})).obj K ⟶
      (DerivedCategory.Qh
        (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})).obj L) →
    ((DerivedCategory.Qh
      (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})).obj
        ((sheafCompose_uliftFunctor_mapHomotopyCategory_quasiIsoLocalizerMorphism
          (X := X)).functor.obj K) ⟶
      (DerivedCategory.Qh
        (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})).obj
        ((sheafCompose_uliftFunctor_mapHomotopyCategory_quasiIsoLocalizerMorphism
          (X := X)).functor.obj L)) :=
  (sheafCompose_uliftFunctor_mapHomotopyCategory_quasiIsoLocalizerMorphism
      (X := X)).homMap
    (DerivedCategory.Qh
      (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m}))
    (DerivedCategory.Qh
      (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}))











/--
%%handwave
name:
  The smooth-form universe constant sheaf is the lifted constant sheaf
statement:
  The constant real sheaf in the smooth-form coefficient universe is
  isomorphic to the universe lift of the ordinary constant real sheaf.
proof:
  The universe-lift functor is compatible with sheafification and with
  constant presheaves.  The two coefficient groups
  \(\mathrm{ULift}^{\max(v,m)}\mathbb R\) and the universe lift of
  \(\mathrm{ULift}^{m}\mathbb R\) are canonically additively isomorphic.
tags:
  milestone
-/
theorem realConstantAddSheafSmoothFormsUniverse_iso_sheafCompose_ulift_realConstantAddSheaf
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    Nonempty
      (realConstantAddSheafSmoothFormsUniverse X ≅
        (sheafCompose (Opens.grothendieckTopology X)
          AddCommGrpCat.uliftFunctor.{v, m}).obj
            (JJMath.Cohomology.RealConstantAddSheaf X)) := by
  let J := Opens.grothendieckTopology X
  let A : AddCommGrpCat.{m} := AddCommGrpCat.of (ULift.{m} ℝ)
  let U : AddCommGrpCat.{m} ⥤ AddCommGrpCat.{max v m} :=
    AddCommGrpCat.uliftFunctor.{v, m}
  let B : AddCommGrpCat.{max v m} := AddCommGrpCat.of (ULift.{max v m} ℝ)
  haveI : J.PreservesSheafification U := by
    dsimp [U]
    exact opens_addCommGrp_uliftFunctor_preservesSheafification X
  let coeffIso : U.obj A ≅ B :=
    realULiftULiftAddEquiv.{v, m}.toAddCommGrpIso
  let hconst :
      (sheafCompose J U).obj ((constantSheaf J AddCommGrpCat.{m}).obj A) ≅
      (constantSheaf J AddCommGrpCat.{max v m}).obj (U.obj A) :=
    (constantCommuteCompose J U).app A
  let hcoeff :
      (constantSheaf J AddCommGrpCat.{max v m}).obj (U.obj A) ≅
      (constantSheaf J AddCommGrpCat.{max v m}).obj B :=
    (constantSheaf J AddCommGrpCat.{max v m}).mapIso coeffIso
  exact ⟨(hconst ≪≫ hcoeff).symm⟩

/--
%%handwave
name:
  The smooth-universe constant real sheaf is the lifted one, compatibly with scalars
statement:
  The isomorphism from the smooth-form-universe constant real sheaf to the
  universe lift of the ordinary constant real sheaf may be chosen to
  intertwine multiplication by every real scalar.
proof:
  Use the canonical coefficient isomorphism between the direct universe lift of
  \(\mathbb R\) and the iterated universe lift.  It commutes with
  multiplication by each real number.  Naturality of constant sheaves and of
  the compatibility isomorphism between sheafification and universe lift then
  gives the corresponding commutative square of sheaves.
tags:
  milestone
-/
theorem exists_realConstantAddSheafSmoothFormsUniverse_iso_sheafCompose_ulift_realConstantAddSheaf_with_scalarEnd
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    ∃ e :
      realConstantAddSheafSmoothFormsUniverse X ≅
        (sheafCompose (Opens.grothendieckTopology X)
          AddCommGrpCat.uliftFunctor.{v, m}).obj
            (JJMath.Cohomology.RealConstantAddSheaf X),
      ∀ r : ℝ,
        realConstantAddSheafSmoothFormsUniverseScalarEnd X r ≫ e.hom =
          e.hom ≫
            (sheafCompose (Opens.grothendieckTopology X)
              AddCommGrpCat.uliftFunctor.{v, m}).map
              (JJMath.Cohomology.realConstantSheafScalarEnd X r) := by
  let J := Opens.grothendieckTopology X
  let A : AddCommGrpCat.{m} := AddCommGrpCat.of (ULift.{m} ℝ)
  let U : AddCommGrpCat.{m} ⥤ AddCommGrpCat.{max v m} :=
    AddCommGrpCat.uliftFunctor.{v, m}
  let B : AddCommGrpCat.{max v m} := AddCommGrpCat.of (ULift.{max v m} ℝ)
  haveI : J.PreservesSheafification U := by
    dsimp [U]
    exact opens_addCommGrp_uliftFunctor_preservesSheafification X
  let coeffIso : U.obj A ≅ B :=
    realULiftULiftAddEquiv.{v, m}.toAddCommGrpIso
  let hconst :
      (sheafCompose J U).obj ((constantSheaf J AddCommGrpCat.{m}).obj A) ≅
      (constantSheaf J AddCommGrpCat.{max v m}).obj (U.obj A) :=
    (constantCommuteCompose J U).app A
  let hcoeff :
      (constantSheaf J AddCommGrpCat.{max v m}).obj (U.obj A) ≅
      (constantSheaf J AddCommGrpCat.{max v m}).obj B :=
    (constantSheaf J AddCommGrpCat.{max v m}).mapIso coeffIso
  refine ⟨(hconst ≪≫ hcoeff).symm, ?_⟩
  intro r
  let fA : A ⟶ A :=
    AddCommGrpCat.ofHom
      (JJMath.Cohomology.realULiftScalarAddMonoidHom.{m} r)
  let fB : B ⟶ B :=
    AddCommGrpCat.ofHom
      (JJMath.Cohomology.realULiftScalarAddMonoidHom.{max v m} r)
  have h_smooth :
      realConstantAddSheafSmoothFormsUniverseScalarEnd X r =
        (constantSheaf J AddCommGrpCat.{max v m}).map fB := by
    rfl
  have h_small :
      JJMath.Cohomology.realConstantSheafScalarEnd X r =
        (constantSheaf J AddCommGrpCat.{m}).map fA := by
    rfl
  have h_coeff :
      fB ≫ coeffIso.inv = coeffIso.inv ≫ U.map fA := by
    ext x
    cases x
    rfl
  have h_hcoeff :
      (constantSheaf J AddCommGrpCat.{max v m}).map fB ≫ hcoeff.inv =
        hcoeff.inv ≫
          (constantSheaf J AddCommGrpCat.{max v m}).map (U.map fA) := by
    simpa [hcoeff, Functor.map_comp] using
      congrArg ((constantSheaf J AddCommGrpCat.{max v m}).map) h_coeff
  have h_hconst :
      (constantSheaf J AddCommGrpCat.{max v m}).map (U.map fA) ≫ hconst.inv =
        hconst.inv ≫
          (sheafCompose J U).map ((constantSheaf J AddCommGrpCat.{m}).map fA) := by
    simpa [hconst, Functor.comp_map] using
      ((constantCommuteCompose J U).inv.naturality fA)
  calc
    realConstantAddSheafSmoothFormsUniverseScalarEnd X r ≫
        ((hconst ≪≫ hcoeff).symm).hom =
      (constantSheaf J AddCommGrpCat.{max v m}).map fB ≫
        hcoeff.inv ≫ hconst.inv := by
        simp [h_smooth]
    _ =
      hcoeff.inv ≫
        (constantSheaf J AddCommGrpCat.{max v m}).map (U.map fA) ≫
          hconst.inv := by
        rw [← Category.assoc, h_hcoeff, Category.assoc]
    _ =
      hcoeff.inv ≫ hconst.inv ≫
        (sheafCompose J U).map ((constantSheaf J AddCommGrpCat.{m}).map fA) := by
        rw [h_hconst]
    _ =
      ((hconst ≪≫ hcoeff).symm).hom ≫
        (sheafCompose J U).map
          (JJMath.Cohomology.realConstantSheafScalarEnd X r) := by
        simp [h_small, J, U, Category.assoc]

/--
%%handwave
name:
  Lifted constant real cohomology is ordinary constant real cohomology
statement:
  If universe lift identifies Ext groups of abelian sheaves, then the
  cohomology of the lifted ordinary constant real sheaf is additively
  isomorphic to ordinary real constant-sheaf cohomology.
proof:
  Sheaf cohomology is an Ext group out of the integer constant sheaf.  Identify
  the large integer constant sheaf with the universe lift of the ordinary
  integer constant sheaf, then apply the Ext bijection induced by universe
  lift.
tags:
  milestone
-/
theorem sheafCompose_ulift_realConstantAddSheaf_cohomology_addEquiv_realConstantSheafCohomology_of_mapExt
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasExt.{m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasExt.{max v m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})]
    (n : ℕ)
    (hExt :
      Function.Bijective
        ((sheafCompose (Opens.grothendieckTopology X)
          AddCommGrpCat.uliftFunctor.{v, m}).mapExtAddHom
            ((constantSheaf (Opens.grothendieckTopology X)
              AddCommGrpCat.{m}).obj (AddCommGrpCat.of (ULift.{m} ℤ)))
            (JJMath.Cohomology.RealConstantAddSheaf X) n)) :
    Nonempty
      (((sheafCompose (Opens.grothendieckTopology X)
          AddCommGrpCat.uliftFunctor.{v, m}).obj
            (JJMath.Cohomology.RealConstantAddSheaf X)).H n ≃+
        JJMath.Cohomology.RealConstantSheafCohomology X n) := by
  let J := Opens.grothendieckTopology X
  let U :=
    sheafCompose J AddCommGrpCat.uliftFunctor.{v, m}
  let Zsmall : Sheaf J AddCommGrpCat.{m} :=
    (constantSheaf J AddCommGrpCat.{m}).obj (AddCommGrpCat.of (ULift.{m} ℤ))
  let Zbig : Sheaf J AddCommGrpCat.{max v m} :=
    (constantSheaf J AddCommGrpCat.{max v m}).obj
      (AddCommGrpCat.of (ULift.{max v m} ℤ))
  let Rsmall : Sheaf J AddCommGrpCat.{m} :=
    JJMath.Cohomology.RealConstantAddSheaf X
  let Rbig : Sheaf J AddCommGrpCat.{max v m} := U.obj Rsmall
  rcases intConstantAddSheafUniverse_iso_sheafCompose_ulift_intConstantAddSheaf
      (X := X) with
    ⟨eZ⟩
  let eSource :
      CategoryTheory.Abelian.Ext (U.obj Zsmall) Rbig n ≃+
        CategoryTheory.Abelian.Ext Zbig Rbig n :=
    { toFun := fun α =>
        (CategoryTheory.Abelian.Ext.mk₀ eZ.hom).comp α (zero_add n)
      invFun := fun α =>
        (CategoryTheory.Abelian.Ext.mk₀ eZ.inv).comp α (zero_add n)
      left_inv := by
        intro α
        change
          (CategoryTheory.Abelian.Ext.mk₀ eZ.inv).comp
              ((CategoryTheory.Abelian.Ext.mk₀ eZ.hom).comp α (zero_add n))
              (zero_add n) = α
        rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]
        rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, Iso.inv_hom_id]
        exact CategoryTheory.Abelian.Ext.mk₀_id_comp α
      right_inv := by
        intro α
        change
          (CategoryTheory.Abelian.Ext.mk₀ eZ.hom).comp
              ((CategoryTheory.Abelian.Ext.mk₀ eZ.inv).comp α (zero_add n))
              (zero_add n) = α
        rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]
        rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id]
        exact CategoryTheory.Abelian.Ext.mk₀_id_comp α
      map_add' := by
        intro α β
        exact (CategoryTheory.Abelian.Ext.precomp
          (CategoryTheory.Abelian.Ext.mk₀ eZ.hom) Rbig (zero_add n)).map_add α β }
  let eLift :
      JJMath.Cohomology.RealConstantSheafCohomology X n ≃+
        CategoryTheory.Abelian.Ext (U.obj Zsmall) Rbig n :=
    AddEquiv.ofBijective (U.mapExtAddHom Zsmall Rsmall n) hExt
  exact ⟨eSource.symm.trans eLift.symm⟩



set_option maxHeartbeats 800000

/--
%%handwave
name:
  The direct and lifted smooth-universe constant sheaves have scalar-compatible cohomology
statement:
  The cohomology isomorphism from the smooth-form-universe constant real sheaf
  to the universe lift of the ordinary constant real sheaf may be chosen to
  intertwine the two scalar endomorphisms.
proof:
  The sheaf isomorphism is induced by the canonical identification between
  the direct lift of \(\mathbb R\) and the iterated universe lift of
  \(\mathbb R\).  This identification commutes with multiplication by every
  real scalar, and applying sheaf cohomology preserves the commutative square.
tags:
  milestone
-/
theorem exists_realConstantSheafSmoothFormsUniverseCohomology_addEquiv_sheafCompose_ulift_realConstantAddSheaf_cohomology_with_map_smul
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasExt.{max v m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})]
    (n : ℕ) :
    ∃ e :
      (realConstantAddSheafSmoothFormsUniverse X).H n ≃+
        (((sheafCompose (Opens.grothendieckTopology X)
          AddCommGrpCat.uliftFunctor.{v, m}).obj
            (JJMath.Cohomology.RealConstantAddSheaf X)).H n),
      ∀ (r : ℝ) (α : (realConstantAddSheafSmoothFormsUniverse X).H n),
        e (((CategoryTheory.Sheaf.functorH
            (Opens.grothendieckTopology X) n).map
            (realConstantAddSheafSmoothFormsUniverseScalarEnd X r)) α) =
          (((CategoryTheory.Sheaf.functorH
              (Opens.grothendieckTopology X) n).map
              ((sheafCompose (Opens.grothendieckTopology X)
                AddCommGrpCat.uliftFunctor.{v, m}).map
                (JJMath.Cohomology.realConstantSheafScalarEnd X r))) (e α)) := by
  rcases
    exists_realConstantAddSheafSmoothFormsUniverse_iso_sheafCompose_ulift_realConstantAddSheaf_with_scalarEnd
      (X := X) with
    ⟨e_sheaf, h_sheaf⟩
  let J := Opens.grothendieckTopology X
  let U := sheafCompose J AddCommGrpCat.uliftFunctor.{v, m}
  let e :
      (realConstantAddSheafSmoothFormsUniverse X).H n ≃+
        ((U.obj (JJMath.Cohomology.RealConstantAddSheaf X)).H n) :=
    ((CategoryTheory.Sheaf.functorH J n).mapIso
      e_sheaf).addCommGroupIsoToAddEquiv
  refine ⟨e, ?_⟩
  intro r α
  let σSmooth :=
    realConstantAddSheafSmoothFormsUniverseScalarEnd X r
  let σLift :=
    U.map (JJMath.Cohomology.realConstantSheafScalarEnd X r)
  have hmap :
      ((CategoryTheory.Sheaf.functorH J n).map σSmooth) ≫
        ((CategoryTheory.Sheaf.functorH J n).map e_sheaf.hom) =
      ((CategoryTheory.Sheaf.functorH J n).map e_sheaf.hom) ≫
        ((CategoryTheory.Sheaf.functorH J n).map σLift) := by
    simpa only [Functor.map_comp] using
      congrArg
        (fun f => (CategoryTheory.Sheaf.functorH J n).map f)
        (h_sheaf r)
  have hpoint :=
    congrArg
      (fun φ => φ α)
      hmap
  simpa [e, J, U, σSmooth, σLift, Iso.addCommGroupIsoToAddEquiv_apply,
    Category.assoc] using hpoint

set_option maxHeartbeats 200000



















end

end Manifold
end JJMath
