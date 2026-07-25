import JJMath.Topology.FineSheaf
import JJMath.Topology.SingularCohomology
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.ShrinkingLemma
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Acyclicity of fine sheaves

This file proves that fine sheaves of abelian groups on paracompact Hausdorff
spaces are acyclic.  The proof uses the discontinuous-sections (Godement)
embedding rather than a Čech comparison theorem.

For a sheaf $\mathcal F$, the discontinuous-sections sheaf assigns to an open
set $U$ the product of the fibers $\mathcal F_x$ over $x \in U$.  It is
flasque, and the canonical map from $\mathcal F$ is a monomorphism.  If
$\mathcal F$ is fine, its cokernel is fine and the induced map on global
sections is surjective.  The long exact cohomology sequence then gives the
result by dimension shifting.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace

namespace CategoryTheory.GrothendieckTopology

universe uC vC uA vA uPoint

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable [HasColimitsOfSize.{uPoint, uPoint} A]

/--
%%handwave
name:
  Additivity of the presheaf fiber at a point
statement:
  For a point $\Phi$ of a site and a preadditive target category with the
  required colimits, the functor taking a presheaf to its fiber at $\Phi$
  preserves zero morphisms and sums of morphisms.
proof:
  The fiber functor is restriction to the category of elements of $\Phi$
  followed by a colimit.  Both functors are additive.
-/
instance point_presheafFiber_additive (Φ : Point.{uPoint} J) :
    (Φ.presheafFiber (A := A)).Additive := by
  dsimp [Point.presheafFiber]
  let W : (Cᵒᵖ ⥤ A) ⥤ (Φ.fiber.Elementsᵒᵖ ⥤ A) :=
    (Functor.whiskeringLeft Φ.fiber.Elementsᵒᵖ Cᵒᵖ A).obj
      (CategoryOfElements.π Φ.fiber).op
  haveI : W.Additive := by
    constructor
    intro P Q f g
    ext U
    rfl
  change (W ⋙ colim).Additive
  infer_instance

/--
%%handwave
name:
  Additivity of the sheaf fiber at a point
statement:
  For a point $\Phi$ of a site, the functor taking a sheaf of objects in a
  preadditive category to its fiber at $\Phi$ preserves zero morphisms and
  sums of morphisms.
proof:
  The sheaf fiber is the additive presheaf-fiber functor composed with the
  additive forgetful functor from sheaves to presheaves.
-/
instance point_sheafFiber_additive
    [HasSheafify J A] (Φ : Point.{uPoint} J) :
    (Φ.sheafFiber (A := A)).Additive := by
  dsimp [Point.sheafFiber]
  infer_instance

end CategoryTheory.GrothendieckTopology

namespace TopCat.Sheaf

universe u w

variable {X : TopCat.{u}}
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{max w u}]

local instance :
    HasLimitsOfSize.{u, u} AddCommGrpCat.{max w u} :=
  AddCommGrpCat.hasLimitsOfSize.{u, max w u, u}

local instance :
    PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{max w u}) :=
  preservesFilteredColimitsOfSize_shrink
    (CategoryTheory.forget AddCommGrpCat.{max w u})

local instance :
    PreservesLimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{max w u}) :=
  preservesLimitsOfSize_shrink
    (CategoryTheory.forget AddCommGrpCat.{max w u})

/--
%%handwave
name:
  Fiber used in the discontinuous-sections construction
statement:
  For a sheaf $\mathcal F$ and a point $x$, this is the fiber
  $\mathcal F_x$ obtained from the point of the open-set site determined by
  $x$.
-/
noncomputable abbrev discontinuousFiber
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) (x : X) :=
  ((Opens.pointGrothendieckTopology x).presheafFiber
    (A := AddCommGrpCat.{max w u})).obj F.obj

/--
%%handwave
name:
  Presheaf of discontinuous sections
statement:
  For a sheaf $\mathcal F$ on $X$, the group of discontinuous sections over
  an open set $U$ is $\prod_{x\in U}\mathcal F_x$, with restriction given by
  restricting a family to the smaller open set.
-/
noncomputable def discontinuousPresheaf
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :
    TopCat.Presheaf AddCommGrpCat.{max w u} X where
  obj U := AddCommGrpCat.of
    ((x : U.unop) → ↥(discontinuousFiber F x.1))
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s x => s (i.unop x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
%%handwave
name:
  Discontinuous sections satisfy the sheaf condition
statement:
  For every sheaf $\mathcal F$, the presheaf
  $U\mapsto\prod_{x\in U}\mathcal F_x$ is a sheaf.
proof:
  Compatible families glue pointwise: at each point choose one member of the
  cover containing it.  Compatibility makes the choice independent, and
  pointwise evaluation proves uniqueness.
-/
theorem discontinuousPresheaf_isSheaf
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :
    (discontinuousPresheaf F).IsSheaf := by
  apply
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
      (discontinuousPresheaf F)).mpr
  intro ι U sf hsf
  choose index index_spec using
    fun x : ↑(iSup U) => Opens.mem_iSup.mp x.2
  let s : (x : ↑(iSup U)) → ↥(discontinuousFiber F x.1) :=
    fun x => sf (index x) ⟨x.1, index_spec x⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    funext x
    exact congr_fun (hsf (index ⟨x, _⟩) i)
      ⟨x, ⟨index_spec ⟨x.1, _⟩, x.2⟩⟩
  · intro t ht
    funext x
    exact congr_fun (ht (index x)) ⟨x.1, index_spec x⟩

/--
%%handwave
name:
  Sheaf of discontinuous sections
statement:
  The discontinuous-sections sheaf of $\mathcal F$ is the sheaf
  $U\mapsto\prod_{x\in U}\mathcal F_x$.
-/
noncomputable def discontinuousSheaf
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :
    TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X :=
  ⟨discontinuousPresheaf F,
    discontinuousPresheaf_isSheaf F⟩

/--
%%handwave
name:
  The discontinuous-sections sheaf is flasque
statement:
  Every restriction map of the discontinuous-sections sheaf
  $U\mapsto\prod_{x\in U}\mathcal F_x$ is surjective.
proof:
  Extend a family of fiber elements by zero at every point outside the
  smaller open set.
-/
instance discontinuousSheaf_isFlasque
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :
    TopCat.Sheaf.IsFlasque (discontinuousSheaf F) where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    change
      Function.Surjective
        (fun (a : (x : U.unop) → ↥(discontinuousFiber F x.1))
          (x : V.unop) => a (i.unop x))
    intro s
    classical
    let t : (x : U.unop) → ↥(discontinuousFiber F x.1) :=
      fun x =>
        if hx : x.1 ∈ V.unop then
          s ⟨x.1, hx⟩
        else 0
    refine ⟨t, ?_⟩
    funext x
    change t (i.unop x) = s x
    simp [t]

/--
%%handwave
name:
  Morphism on discontinuous-sections sheaves
statement:
  A morphism $\mathcal F\to\mathcal G$ induces a morphism between their
  discontinuous-sections sheaves by applying the induced fiber map at every
  point.
-/
noncomputable def discontinuousSheafMap
    {F G : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X}
    (f : F ⟶ G) :
    discontinuousSheaf F ⟶ discontinuousSheaf G :=
  ⟨{
    app := fun U => AddCommGrpCat.ofHom
      { toFun := fun s x =>
          ((Opens.pointGrothendieckTopology x.1).presheafFiber
            (A := AddCommGrpCat.{max w u})).map f.hom (s x)
        map_zero' := by
          funext x
          exact (((Opens.pointGrothendieckTopology x.1).presheafFiber
            (A := AddCommGrpCat.{max w u})).map f.hom).hom.map_zero
        map_add' := fun a b => by
          funext x
          exact (((Opens.pointGrothendieckTopology x.1).presheafFiber
            (A := AddCommGrpCat.{max w u})).map f.hom).hom.map_add _ _ }
    naturality := by
      intro U V i
      ext s
      funext x
      rfl }⟩

/--
%%handwave
name:
  Discontinuous-sections functor
statement:
  Sending $\mathcal F$ to its discontinuous-sections sheaf and applying
  morphisms pointwise defines an endofunctor on sheaves of abelian groups.
-/
noncomputable def discontinuousSheafFunctor :
    TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X ⥤
      TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X where
  obj := discontinuousSheaf
  map := discontinuousSheafMap
  map_id F := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    funext x
    dsimp [discontinuousSheafMap]
    change
      ((Opens.pointGrothendieckTopology x.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map (𝟙 F.obj) (s x) = s x
    exact
      ConcreteCategory.congr_hom
        (((Opens.pointGrothendieckTopology x.1).presheafFiber
          (A := AddCommGrpCat.{max w u})).map_id F.obj)
        (s x)
  map_comp f g := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    funext x
    dsimp [discontinuousSheafMap]
    change
      ((Opens.pointGrothendieckTopology x.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map (f.hom ≫ g.hom) (s x) =
      ((Opens.pointGrothendieckTopology x.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map g.hom
        (((Opens.pointGrothendieckTopology x.1).presheafFiber
          (A := AddCommGrpCat.{max w u})).map f.hom (s x))
    rw [Functor.map_comp]
    rfl

/--
%%handwave
name:
  Canonical map to discontinuous sections
statement:
  Every sheaf $\mathcal F$ has a canonical morphism
  $\mathcal F\to\prod_x\mathcal F_x$ sending a section to its fiber at each
  point.
-/
noncomputable def toDiscontinuousSheaf
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :
    F ⟶ discontinuousSheaf F :=
  ⟨{
    app := fun U => AddCommGrpCat.ofHom
      { toFun := fun s x =>
          (Opens.pointGrothendieckTopology x.1).toPresheafFiber
            U.unop ⟨⟨x.2⟩⟩ F.obj s
        map_zero' := by
          funext x
          exact ((Opens.pointGrothendieckTopology x.1).toPresheafFiber
            U.unop ⟨⟨x.2⟩⟩ F.obj).hom.map_zero
        map_add' := fun a b => by
          funext x
          exact ((Opens.pointGrothendieckTopology x.1).toPresheafFiber
            U.unop ⟨⟨x.2⟩⟩ F.obj).hom.map_add _ _ }
    naturality := by
      intro U V i
      ext s
      funext x
      exact
        (CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w_apply
          (Φ := Opens.pointGrothendieckTopology x.1)
          i.unop ⟨⟨x.2⟩⟩ F.obj s) }⟩

/--
%%handwave
name:
  Naturality of the map to discontinuous sections
statement:
  For every morphism $f:\mathcal F\to\mathcal G$, taking point fibers
  commutes with the canonical maps into the discontinuous-sections sheaves.
proof:
  Evaluate on an open set and a point and apply naturality of the canonical
  map from a presheaf section to its point fiber.
-/
theorem toDiscontinuousSheaf_naturality
    {F G : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X}
    (f : F ⟶ G) :
    f ≫ toDiscontinuousSheaf G =
      toDiscontinuousSheaf F ≫
        discontinuousSheafMap f := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  funext x
  dsimp [toDiscontinuousSheaf, discontinuousSheafMap]
  change
    (Opens.pointGrothendieckTopology x.1).toPresheafFiber
        U.unop ⟨⟨x.2⟩⟩ G.obj (f.hom.app U s) =
      ((Opens.pointGrothendieckTopology x.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map f.hom
        ((Opens.pointGrothendieckTopology x.1).toPresheafFiber
          U.unop ⟨⟨x.2⟩⟩ F.obj s)
  exact
    (CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_apply
      (Φ := Opens.pointGrothendieckTopology x.1)
      f.hom U.unop ⟨⟨x.2⟩⟩ s).symm

/--
%%handwave
name:
  Sections embed in discontinuous sections
statement:
  The canonical morphism from a sheaf $\mathcal F$ to its
  discontinuous-sections sheaf is a monomorphism.
proof:
  If two sections have equal images, their fibers agree at every point.
  Equality of sheaf sections follows from equality of all germs.
-/
instance toDiscontinuousSheaf_mono
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :
    Mono (toDiscontinuousSheaf F) := by
  apply
    (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono
      (Opens.grothendieckTopology X) AddCommGrpCat.{max w u}
      (toDiscontinuousSheaf F)).mpr
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [AddCommGrpCat.mono_iff_injective]
  intro s t hst
  have hfiber :
      ∀ (x : X) (hx : x ∈ U.unop),
        (Opens.pointGrothendieckTopology x).toPresheafFiber
            U.unop ⟨⟨hx⟩⟩ F.obj s =
          (Opens.pointGrothendieckTopology x).toPresheafFiber
            U.unop ⟨⟨hx⟩⟩ F.obj t := by
    intro x hx
    exact congr_fun hst ⟨x, hx⟩
  choose V i y hy hres using
    fun z : U.unop =>
      ((Opens.pointGrothendieckTopology z.1).toPresheafFiber_eq_iff'
        U.unop ⟨⟨z.2⟩⟩ s t).mp (hfiber z.1 z.2)
  apply F.eq_of_locally_eq' V U.unop i
  · intro x hx
    rw [Opens.mem_iSup]
    exact ⟨⟨x, hx⟩, (y ⟨x, hx⟩).down.down⟩
  · exact hres

/--
%%handwave
name:
  Fine quotient of a sheaf
statement:
  For a sheaf $\mathcal F$, its fine quotient is the cokernel
  $\mathcal Q(\mathcal F)$ of the canonical monomorphism from $\mathcal F$
  to its discontinuous-sections sheaf.
-/
noncomputable abbrev fineQuotient
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :=
  cokernel (toDiscontinuousSheaf F)

/--
%%handwave
name:
  The discontinuous-sections quotient projection is an epimorphism
statement:
  The canonical projection
  $D(\mathcal F)\to\mathcal Q(\mathcal F)$ is an epimorphism.
proof:
  It is the defining coequalizer morphism of the cokernel.
-/
instance (priority := 2000) fineQuotientProjection_epi
    (F : TopCat.Sheaf.{u, max w u, max w u + 1}
      AddCommGrpCat.{max w u} X) :
    Epi (cokernel.π (toDiscontinuousSheaf F)) where
  left_cancellation _ _ h :=
    CategoryTheory.Limits.coequalizer.hom_ext h

/--
%%handwave
name:
  Induced morphism on fine quotients
statement:
  A morphism $f:\mathcal F\to\mathcal G$ induces a morphism
  $\mathcal Q(\mathcal F)\to\mathcal Q(\mathcal G)$ between the cokernels of
  the canonical discontinuous-sections embeddings.
-/
noncomputable def fineQuotientMap
    {F G : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X}
    (f : F ⟶ G) :
    fineQuotient F ⟶ fineQuotient G :=
  cokernel.map
    (toDiscontinuousSheaf F)
    (toDiscontinuousSheaf G)
    f
    (discontinuousSheafMap f)
    (toDiscontinuousSheaf_naturality f).symm

/--
%%handwave
name:
  Naturality of the fine-quotient projection
statement:
  For every $f:\mathcal F\to\mathcal G$, the induced quotient morphism
  commutes with the cokernel projections from the discontinuous-sections
  sheaves.
proof:
  This is the defining factorization equation for the morphism induced
  between cokernels.
-/
theorem fineQuotient_π_naturality
    {F G : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X}
    (f : F ⟶ G) :
    cokernel.π (toDiscontinuousSheaf F) ≫
        fineQuotientMap f =
      discontinuousSheafMap f ≫
        cokernel.π (toDiscontinuousSheaf G) := by
  apply cokernel.π_desc

/--
%%handwave
name:
  The zero morphism acts trivially on discontinuous sections
statement:
  The morphism induced on the discontinuous-sections sheaf by the zero
  endomorphism of $\mathcal F$ is zero.
proof:
  Evaluate at every point and use additivity of the point-fiber functor.
-/
theorem discontinuousSheafMap_zero
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :
    discontinuousSheafMap (0 : F ⟶ F) = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  funext x
  dsimp [discontinuousSheafMap]
  change
    ((Opens.pointGrothendieckTopology x.1).presheafFiber
      (A := AddCommGrpCat.{max w u})).map
        (0 : F.obj ⟶ F.obj) (s x) = 0
  have hzero :
      ((Opens.pointGrothendieckTopology x.1).presheafFiber
          (A := AddCommGrpCat.{max w u})).map
          (0 : F.obj ⟶ F.obj) = 0 :=
    ((Opens.pointGrothendieckTopology x.1).presheafFiber
      (A := AddCommGrpCat.{max w u})).map_zero F.obj F.obj
  rw [hzero]
  exact (0 : discontinuousFiber F x.1 ⟶ discontinuousFiber F x.1).hom.map_zero

/--
%%handwave
name:
  Addition acts pointwise on discontinuous sections
statement:
  The morphism induced on discontinuous sections by $f+g$ is the sum of the
  morphisms induced by $f$ and by $g$.
proof:
  Evaluate at each point and use additivity of the point-fiber functor.
-/
theorem discontinuousSheafMap_add
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (f g : F ⟶ F) :
    discontinuousSheafMap (f + g) =
      discontinuousSheafMap f +
        discontinuousSheafMap g := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  funext x
  dsimp [discontinuousSheafMap]
  change
    ((Opens.pointGrothendieckTopology x.1).presheafFiber
      (A := AddCommGrpCat.{max w u})).map (f.hom + g.hom) (s x) =
      ((Opens.pointGrothendieckTopology x.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map f.hom (s x) +
      ((Opens.pointGrothendieckTopology x.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map g.hom (s x)
  have hadd :
      ((Opens.pointGrothendieckTopology x.1).presheafFiber
          (A := AddCommGrpCat.{max w u})).map (f.hom + g.hom) =
        ((Opens.pointGrothendieckTopology x.1).presheafFiber
          (A := AddCommGrpCat.{max w u})).map f.hom +
          ((Opens.pointGrothendieckTopology x.1).presheafFiber
            (A := AddCommGrpCat.{max w u})).map g.hom :=
    ((Opens.pointGrothendieckTopology x.1).presheafFiber
      (A := AddCommGrpCat.{max w u})).map_add
  rw [hadd]
  rfl

/--
%%handwave
name:
  The zero endomorphism induces zero on the fine quotient
statement:
  The endomorphism of $\mathcal Q(\mathcal F)$ induced by the zero
  endomorphism of $\mathcal F$ is zero.
proof:
  Precompose with the epimorphic cokernel projection and use naturality and
  the corresponding zero statement for discontinuous sections.
-/
theorem fineQuotientMap_zero
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X) :
    fineQuotientMap (0 : F ⟶ F) = 0 := by
  rw [← cancel_epi (cokernel.π (toDiscontinuousSheaf F))]
  rw [fineQuotient_π_naturality]
  rw [discontinuousSheafMap_zero]
  exact zero_comp.trans comp_zero.symm

/--
%%handwave
name:
  Addition descends to the fine quotient
statement:
  For endomorphisms $f,g$ of $\mathcal F$, the map induced by $f+g$ on
  $\mathcal Q(\mathcal F)$ is the sum of the maps induced by $f$ and $g$.
proof:
  Precompose with the epimorphic cokernel projection, apply naturality, and
  use pointwise additivity on discontinuous sections.
-/
theorem fineQuotientMap_add
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (f g : F ⟶ F) :
    fineQuotientMap (f + g) =
      fineQuotientMap f + fineQuotientMap g := by
  rw [← cancel_epi (cokernel.π (toDiscontinuousSheaf F))]
  rw [fineQuotient_π_naturality]
  rw [discontinuousSheafMap_add]
  rw [Preadditive.add_comp, Preadditive.comp_add]
  rw [fineQuotient_π_naturality,
    fineQuotient_π_naturality]

/--
%%handwave
name:
  Finite sums descend to the fine quotient
statement:
  For a finite set $s$ and endomorphisms $(f_i)$ of $\mathcal F$, the map
  induced by $\sum_{i\in s}f_i$ on $\mathcal Q(\mathcal F)$ equals the sum
  of the individually induced maps.
proof:
  Induct on the finite set using preservation of zero and addition.
-/
theorem fineQuotientMap_sum
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    {ι : Type*} (s : Finset ι) (f : ι → (F ⟶ F)) :
    fineQuotientMap (∑ i ∈ s, f i) =
      ∑ i ∈ s, fineQuotientMap (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fineQuotientMap_zero]
  | @insert a s ha ih =>
      simp [ha, ih, fineQuotientMap_add]

/--
%%handwave
name:
  Locally finite shrinking with the same index set
statement:
  Let $(U_i)_{i\in I}$ be a locally finite open cover of a paracompact
  Hausdorff space.  There is a locally finite open cover $(V_i)_{i\in I}$
  such that $\overline{V_i}\subseteq U_i$ for every $i$.
proof:
  A paracompact Hausdorff space is normal.  Apply the locally finite shrinking
  lemma and retain the original index set.
-/
theorem existsLocallyFiniteOpenShrinking
    [T2Space X] [ParacompactSpace X]
    {ι : Type u} (U : ι → Opens X)
    (hfinite : LocallyFinite (fun i => (U i : Set X)))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    ∃ V : ι → Opens X,
      (∀ i, closure (V i : Set X) ⊆ (U i : Set X)) ∧
      LocallyFinite (fun i => (V i : Set X)) ∧
      ∀ x : X, ∃ i, x ∈ V i := by
  classical
  letI : T4Space X := T4Space.of_paracompactSpace_t2Space
  have hUcover : ⋃ i, (U i : Set X) = (Set.univ : Set X) := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases hcover x with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  rcases
      exists_iUnion_eq_closure_subset
        (fun i => (U i).isOpen) hfinite.point_finite hUcover with
    ⟨V, hVcover, hVopen, hVclosure⟩
  let VO : ι → Opens X := fun i => ⟨V i, hVopen i⟩
  have hVU : ∀ i, (VO i : Set X) ⊆ (U i : Set X) := by
    intro i
    exact subset_closure.trans (hVclosure i)
  refine ⟨VO, ?_, hfinite.subset hVU, ?_⟩
  · exact hVclosure
  · intro x
    have hx : x ∈ ⋃ i, V i := by rw [hVcover]; trivial
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact ⟨i, hxi⟩

/--
%%handwave
name:
  Locally finite shrinking of an arbitrary open cover
statement:
  Let $(U_i)_{i\in I}$ be an open cover of a paracompact Hausdorff space.
  There is a locally finite open cover $(V_i)_{i\in I}$ with
  $\overline{V_i}\subseteq U_i$ for every $i$.
proof:
  First take a precise locally finite refinement indexed by $I$, then apply
  the locally finite shrinking theorem to that refinement.
-/
theorem existsLocallyFiniteOpenShrinkingOfCover
    [T2Space X] [ParacompactSpace X]
    {ι : Type u} (U : ι → Opens X)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    ∃ V : ι → Opens X,
      (∀ i, closure (V i : Set X) ⊆ (U i : Set X)) ∧
      LocallyFinite (fun i => (V i : Set X)) ∧
      ∀ x : X, ∃ i, x ∈ V i := by
  classical
  have hUcover : ⋃ i, (U i : Set X) = (Set.univ : Set X) := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases hcover x with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  rcases
      precise_refinement
        (fun i => (U i : Set X))
        (fun i => (U i).isOpen) hUcover with
    ⟨Q, hQopen, hQcover, hQfinite, hQU⟩
  let QO : ι → Opens X := fun i => ⟨Q i, hQopen i⟩
  have hQOcover : ∀ x : X, ∃ i, x ∈ QO i := by
    intro x
    have hx : x ∈ ⋃ i, Q i := by rw [hQcover]; trivial
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact ⟨i, hxi⟩
  rcases
      existsLocallyFiniteOpenShrinking
        QO hQfinite hQOcover with
    ⟨V, hVQclosure, hVfinite, hVcover⟩
  exact
    ⟨V, fun i => (hVQclosure i).trans (hQU i),
      hVfinite, hVcover⟩

/--
%%handwave
name:
  Local vanishing induces zero on a discontinuous fiber
statement:
  Suppose an endomorphism $f$ of $\mathcal F$ induces the zero map on every
  fiber over an open neighborhood $W$ of $x$.  Then the induced endomorphism
  of the fiber at $x$ of the discontinuous-sections sheaf is zero.
proof:
  Represent an element of the fiber by a section over an open neighborhood,
  restrict it to the intersection with $W$, and evaluate pointwise.
-/
theorem discontinuousSheafMap_pointFiber_eq_zero_of_locally_zero
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (f : F ⟶ F) (x : X) (W : Opens X) (hxW : x ∈ W)
    (hW :
      ∀ y : X, y ∈ W →
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map f.hom = 0) :
    ((Opens.pointGrothendieckTopology x).sheafFiber
      (A := AddCommGrpCat.{max w u})).map
        (discontinuousSheafMap f) = 0 := by
  let Φ := Opens.pointGrothendieckTopology x
  change
    (Φ.presheafFiber (A := AddCommGrpCat.{max w u})).map
      (discontinuousSheafMap f).hom = 0
  ext z
  rcases
      Φ.toPresheafFiber_jointly_surjective
        (A := AddCommGrpCat.{max w u})
        (P := (discontinuousSheaf F).obj) z with
    ⟨U, hxUΦ, s, rfl⟩
  let V : Opens X := U ⊓ W
  have hxU : x ∈ U := hxUΦ.down.down
  have hxV : x ∈ V := ⟨hxU, hxW⟩
  let hxVΦ : Φ.fiber.obj V := ⟨⟨hxV⟩⟩
  let iVU : V ⟶ U := homOfLE inf_le_left
  have hres :
      (discontinuousSheaf F).obj.map iVU.op
          ((discontinuousSheafMap f).hom.app (op U) s) = 0 := by
    funext y
    change
      ((Opens.pointGrothendieckTopology y.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map f.hom
          (s (iVU y)) = 0
    have hyW : y.1 ∈ W := y.2.2
    rw [hW y.1 hyW]
    exact (0 :
      discontinuousFiber F y.1 ⟶ discontinuousFiber F y.1).hom.map_zero
  rw [CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  have hto :
      Φ.toPresheafFiber U hxUΦ (discontinuousSheaf F).obj
          ((discontinuousSheafMap f).hom.app (op U) s) =
        Φ.toPresheafFiber V hxVΦ (discontinuousSheaf F).obj
          ((discontinuousSheaf F).obj.map iVU.op
            ((discontinuousSheafMap f).hom.app (op U) s)) := by
    have h :=
      CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w_apply
        (Φ := Φ) iVU hxVΦ (discontinuousSheaf F).obj
        ((discontinuousSheafMap f).hom.app (op U) s)
    simpa [Subsingleton.elim (Φ.fiber.map iVU hxVΦ) hxUΦ] using h.symm
  rw [hto, hres]
  simp

/--
%%handwave
name:
  Support enlargement for discontinuous sections
statement:
  For an endomorphism $f$ of $\mathcal F$, the germ support of its induced
  endomorphism on the discontinuous-sections sheaf is contained in the
  closure of the germ support of $f$.
proof:
  Outside that closure there is an open neighborhood on which every fiber
  map of $f$ is zero, so local vanishing gives a zero map on the
  discontinuous fiber.
-/
theorem discontinuousSheafMap_germSupport_subset_closure
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (f : F ⟶ F) :
    endomorphismGermSupport (discontinuousSheaf F)
        (discontinuousSheafMap f) ⊆
      closure (endomorphismGermSupport F f) := by
  intro x hx
  by_contra hxclosure
  apply hx
  let W : Opens X :=
    ⟨(closure (endomorphismGermSupport F f))ᶜ,
      isClosed_closure.isOpen_compl⟩
  have hxW : x ∈ W := hxclosure
  apply
    discontinuousSheafMap_pointFiber_eq_zero_of_locally_zero
      F f x W hxW
  intro y hyW
  by_contra hy
  exact hyW (subset_closure hy)

/--
%%handwave
name:
  Support enlargement for the fine quotient
statement:
  For an endomorphism $f$ of $\mathcal F$, the germ support of the induced
  endomorphism on $\mathcal Q(\mathcal F)$ is contained in the closure of the
  germ support of $f$.
proof:
  Outside the closure, the induced map on the discontinuous fiber is zero.
  The fiber of the cokernel projection is surjective, so naturality forces
  the induced quotient-fiber map to be zero.
-/
theorem fineQuotientMap_germSupport_subset_closure
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (f : F ⟶ F) :
    endomorphismGermSupport (fineQuotient F)
        (fineQuotientMap f) ⊆
      closure (endomorphismGermSupport F f) := by
  intro x hx
  by_contra hxclosure
  apply hx
  let Φ := Opens.pointGrothendieckTopology x
  have hD :
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (discontinuousSheafMap f) = 0 := by
    apply not_ne_iff.mp
    intro hne
    exact hxclosure
      (discontinuousSheafMap_germSupport_subset_closure F f hne)
  haveI :
      Epi ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
        (cokernel.π (toDiscontinuousSheaf F))) := by
    exact @Functor.map_epi _ _ _ _
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u}))
      (Functor.preservesEpimorphisms_of_adjunction
        (Φ.skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max w u})))
      _ _
      (cokernel.π (toDiscontinuousSheaf F))
      (fineQuotientProjection_epi F)
  rw [← cancel_epi
    ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
      (cokernel.π (toDiscontinuousSheaf F)))]
  calc
    (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (cokernel.π (toDiscontinuousSheaf F)) ≫
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (fineQuotientMap f) =
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
        (cokernel.π (toDiscontinuousSheaf F) ≫
          fineQuotientMap f) := by
            rw [Functor.map_comp]
    _ = (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
        (discontinuousSheafMap f ≫
          cokernel.π (toDiscontinuousSheaf F)) := by
            exact congrArg
              (fun k => (Φ.sheafFiber
                (A := AddCommGrpCat.{max w u})).map k)
              (fineQuotient_π_naturality
                (F := F) (G := F) f)
    _ = (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (discontinuousSheafMap f) ≫
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (cokernel.π (toDiscontinuousSheaf F)) := by
            rw [Functor.map_comp]
    _ = 0 := by rw [hD]; simp
    _ = (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (cokernel.π (toDiscontinuousSheaf F)) ≫ 0 := by
            simp

/--
%%handwave
name:
  Locally equal maps agree on a discontinuous fiber
statement:
  If two endomorphisms $f,g$ of $\mathcal F$ induce equal maps on every
  fiber over a neighborhood $W$ of $x$, then their induced endomorphisms on
  the fiber at $x$ of the discontinuous-sections sheaf are equal.
proof:
  Represent a fiber element by a local section, restrict to its intersection
  with $W$, and use the assumed pointwise equality.
-/
theorem discontinuousSheafMap_pointFiber_eq_of_locally_eq
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (f g : F ⟶ F) (x : X) (W : Opens X) (hxW : x ∈ W)
    (hW :
      ∀ y : X, y ∈ W →
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map f.hom =
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map g.hom) :
    ((Opens.pointGrothendieckTopology x).sheafFiber
      (A := AddCommGrpCat.{max w u})).map
        (discontinuousSheafMap f) =
      ((Opens.pointGrothendieckTopology x).sheafFiber
        (A := AddCommGrpCat.{max w u})).map
          (discontinuousSheafMap g) := by
  let Φ := Opens.pointGrothendieckTopology x
  change
    (Φ.presheafFiber (A := AddCommGrpCat.{max w u})).map
        (discontinuousSheafMap f).hom =
      (Φ.presheafFiber (A := AddCommGrpCat.{max w u})).map
        (discontinuousSheafMap g).hom
  ext z
  rcases
      Φ.toPresheafFiber_jointly_surjective
        (A := AddCommGrpCat.{max w u})
        (P := (discontinuousSheaf F).obj) z with
    ⟨U, hxUΦ, s, rfl⟩
  let V : Opens X := U ⊓ W
  have hxU : x ∈ U := hxUΦ.down.down
  have hxV : x ∈ V := ⟨hxU, hxW⟩
  let hxVΦ : Φ.fiber.obj V := ⟨⟨hxV⟩⟩
  let iVU : V ⟶ U := homOfLE inf_le_left
  have hres :
      (discontinuousSheaf F).obj.map iVU.op
          ((discontinuousSheafMap f).hom.app (op U) s) =
        (discontinuousSheaf F).obj.map iVU.op
          ((discontinuousSheafMap g).hom.app (op U) s) := by
    funext y
    change
      ((Opens.pointGrothendieckTopology y.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map f.hom (s (iVU y)) =
      ((Opens.pointGrothendieckTopology y.1).presheafFiber
        (A := AddCommGrpCat.{max w u})).map g.hom (s (iVU y))
    rw [hW y.1 y.2.2]
  simp only [
    CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  have hto (k : F ⟶ F) :
      Φ.toPresheafFiber U hxUΦ (discontinuousSheaf F).obj
          ((discontinuousSheafMap k).hom.app (op U) s) =
        Φ.toPresheafFiber V hxVΦ (discontinuousSheaf F).obj
          ((discontinuousSheaf F).obj.map iVU.op
            ((discontinuousSheafMap k).hom.app (op U) s)) := by
    have h :=
      CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w_apply
        (Φ := Φ) iVU hxVΦ (discontinuousSheaf F).obj
        ((discontinuousSheafMap k).hom.app (op U) s)
    simpa [Subsingleton.elim (Φ.fiber.map iVU hxVΦ) hxUΦ] using h.symm
  rw [hto f, hto g, hres]

/--
%%handwave
name:
  A locally identity map acts identically on a discontinuous fiber
statement:
  If an endomorphism $f$ of $\mathcal F$ induces the identity on every fiber
  over a neighborhood of $x$, then its induced map on the fiber at $x$ of
  the discontinuous-sections sheaf is the identity.
proof:
  Compare $f$ locally with the identity endomorphism and use functoriality of
  the discontinuous-sections construction.
-/
theorem discontinuousSheafMap_pointFiber_eq_id_of_locally_eq_id
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (f : F ⟶ F) (x : X) (W : Opens X) (hxW : x ∈ W)
    (hW :
      ∀ y : X, y ∈ W →
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map f.hom = 𝟙 _) :
    ((Opens.pointGrothendieckTopology x).sheafFiber
      (A := AddCommGrpCat.{max w u})).map
        (discontinuousSheafMap f) = 𝟙 _ := by
  have h :=
    discontinuousSheafMap_pointFiber_eq_of_locally_eq
      F f (𝟙 F) x W hxW
  have hlocal :
      ∀ y : X, y ∈ W →
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map f.hom =
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map ((𝟙 F : F ⟶ F).hom) := by
    intro y hy
    rw [hW y hy]
    exact
      (((Opens.pointGrothendieckTopology y).presheafFiber
        (A := AddCommGrpCat.{max w u})).map_id F.obj).symm
  specialize h hlocal
  calc
    ((Opens.pointGrothendieckTopology x).sheafFiber
      (A := AddCommGrpCat.{max w u})).map
        (discontinuousSheafMap f) =
      ((Opens.pointGrothendieckTopology x).sheafFiber
        (A := AddCommGrpCat.{max w u})).map
          (discontinuousSheafMap (𝟙 F)) := h
    _ = ((Opens.pointGrothendieckTopology x).sheafFiber
        (A := AddCommGrpCat.{max w u})).map
          (𝟙 (discontinuousSheaf F)) := by
            exact congrArg
              (fun k =>
                ((Opens.pointGrothendieckTopology x).sheafFiber
                  (A := AddCommGrpCat.{max w u})).map k)
              (discontinuousSheafFunctor.map_id F)
    _ = 𝟙 _ :=
      ((Opens.pointGrothendieckTopology x).sheafFiber
        (A := AddCommGrpCat.{max w u})).map_id _

/--
%%handwave
name:
  A locally identity map acts identically on the fine quotient
statement:
  If an endomorphism $f$ of $\mathcal F$ induces the identity on every fiber
  over a neighborhood of $x$, then the induced endomorphism of the fiber at
  $x$ of $\mathcal Q(\mathcal F)$ is the identity.
proof:
  The corresponding map on the discontinuous fiber is the identity.  Use
  naturality and cancel the surjective fiber map of the cokernel projection.
-/
theorem fineQuotientMap_pointFiber_eq_id_of_locally_eq_id
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (f : F ⟶ F) (x : X) (W : Opens X) (hxW : x ∈ W)
    (hW :
      ∀ y : X, y ∈ W →
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map f.hom = 𝟙 _) :
    ((Opens.pointGrothendieckTopology x).sheafFiber
      (A := AddCommGrpCat.{max w u})).map
        (fineQuotientMap f) = 𝟙 _ := by
  let Φ := Opens.pointGrothendieckTopology x
  have hD :
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (discontinuousSheafMap f) = 𝟙 _ :=
    discontinuousSheafMap_pointFiber_eq_id_of_locally_eq_id
      F f x W hxW hW
  haveI :
      Epi ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
        (cokernel.π (toDiscontinuousSheaf F))) := by
    exact @Functor.map_epi _ _ _ _
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u}))
      (Functor.preservesEpimorphisms_of_adjunction
        (Φ.skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max w u})))
      _ _
      (cokernel.π (toDiscontinuousSheaf F))
      (fineQuotientProjection_epi F)
  rw [← cancel_epi
    ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
      (cokernel.π (toDiscontinuousSheaf F)))]
  calc
    (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (cokernel.π (toDiscontinuousSheaf F)) ≫
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (fineQuotientMap f) =
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
        (cokernel.π (toDiscontinuousSheaf F) ≫
          fineQuotientMap f) := by
            rw [Functor.map_comp]
    _ = (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
        (discontinuousSheafMap f ≫
          cokernel.π (toDiscontinuousSheaf F)) := by
            exact congrArg
              (fun k => (Φ.sheafFiber
                (A := AddCommGrpCat.{max w u})).map k)
              (fineQuotient_π_naturality
                (F := F) (G := F) f)
    _ = (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (discontinuousSheafMap f) ≫
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (cokernel.π (toDiscontinuousSheaf F)) := by
            rw [Functor.map_comp]
    _ = (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (cokernel.π (toDiscontinuousSheaf F)) := by
            rw [hD]
            simp
    _ = (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (cokernel.π (toDiscontinuousSheaf F)) ≫ 𝟙 _ := by
            simp

/--
%%handwave
name:
  The quotient of a fine sheaf by discontinuous sections is fine
statement:
  If $\mathcal F$ is fine on a paracompact Hausdorff space, then
  $\mathcal Q(\mathcal F)$ is fine.
proof:
  Shrink a locally finite cover so that the closures remain subordinate.
  Transfer a fine partition for the shrinking to the quotient.  The support
  enlargement is contained in those closures, and local finiteness turns the
  stalkwise sum into the identity.
-/
instance fineQuotient_isFine
    [T2Space X] [ParacompactSpace X]
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    [IsFine F] :
    IsFine (fineQuotient F) where
  exists_subordinate_partition := by
    intro ι U hUfinite hUcover
    classical
    rcases
        existsLocallyFiniteOpenShrinking U hUfinite hUcover with
      ⟨V, hVUclosure, hVfinite, hVcover⟩
    rcases
        IsFine.exists_subordinate_partition
          (F := F) V hVfinite hVcover with
      ⟨φ, hφsupport, hφpartition⟩
    refine ⟨fun i => fineQuotientMap (φ i), ?_, ?_⟩
    · intro i
      exact
        (fineQuotientMap_germSupport_subset_closure F (φ i)).trans
          ((closure_mono (hφsupport i)).trans (hVUclosure i))
    · intro x
      rcases hVfinite x with ⟨T, hTnhds, hTfinite⟩
      rcases mem_nhds_iff.mp hTnhds with
        ⟨Oset, hOT, hOopen, hxO⟩
      let O : Opens X := ⟨Oset, hOopen⟩
      let s : Finset ι := hTfinite.toFinset
      have hnotV :
          ∀ {i : ι}, i ∉ s → ∀ {y : X}, y ∈ O → y ∉ V i := by
        intro i hi y hyO hyV
        apply hi
        apply hTfinite.mem_toFinset.mpr
        exact ⟨y, hyV, hOT hyO⟩
      have houtside :
          ∀ i, i ∉ s →
            ((Opens.pointGrothendieckTopology x).sheafFiber
              (A := AddCommGrpCat.{max w u})).map
                (fineQuotientMap (φ i)) = 0 := by
        intro i hi
        apply not_ne_iff.mp
        intro hne
        have hxclosureSupport :
            x ∈ closure (endomorphismGermSupport F (φ i)) :=
          fineQuotientMap_germSupport_subset_closure
            F (φ i) hne
        have hxclosureV : x ∈ closure (V i : Set X) :=
          closure_mono (hφsupport i) hxclosureSupport
        rcases
            (mem_closure_iff.mp hxclosureV)
              O hOopen hxO with
          ⟨y, hyO, hyV⟩
        exact hnotV hi hyO hyV
      refine ⟨s, houtside, ?_⟩
      let fsum : F ⟶ F := ∑ i ∈ s, φ i
      have hlocal :
          ∀ y : X, y ∈ O →
            ((Opens.pointGrothendieckTopology y).presheafFiber
              (A := AddCommGrpCat.{max w u})).map fsum.hom = 𝟙 _ := by
        intro y hyO
        let Ψ := Opens.pointGrothendieckTopology y
        rcases hφpartition y with ⟨t, htzero, htsum⟩
        let a : ι →
            ((Ψ.sheafFiber (A := AddCommGrpCat.{max w u})).obj F ⟶
              (Ψ.sheafFiber (A := AddCommGrpCat.{max w u})).obj F) :=
          fun i => (Ψ.sheafFiber
            (A := AddCommGrpCat.{max w u})).map (φ i)
        have hzeroS : ∀ i, i ∉ s → a i = 0 := by
          intro i hi
          apply not_ne_iff.mp
          intro hne
          exact hnotV hi hyO (hφsupport i hne)
        have hsumEq :
            (∑ i ∈ s, a i) = ∑ i ∈ t, a i := by
          calc
            (∑ i ∈ s, a i) =
                ∑ i ∈ s ∪ t, a i :=
              Finset.sum_subset Finset.subset_union_left
                (by
                  intro i _hiUnion hi
                  exact hzeroS i hi)
            _ = ∑ i ∈ t, a i :=
              (Finset.sum_subset Finset.subset_union_right
                (by
                  intro i _hiUnion hi
                  exact htzero i hi)).symm
        change
          (Ψ.sheafFiber (A := AddCommGrpCat.{max w u})).map fsum = 𝟙 _
        dsimp only [fsum]
        calc
          (Ψ.sheafFiber (A := AddCommGrpCat.{max w u})).map
              (∑ i ∈ s, φ i) =
              ∑ i ∈ s, a i :=
            CategoryTheory.Functor.map_sum
              (Ψ.sheafFiber (A := AddCommGrpCat.{max w u})) φ s
          _ = ∑ i ∈ t, a i := hsumEq
          _ = 𝟙 _ := htsum
      have hid :
          ((Opens.pointGrothendieckTopology x).sheafFiber
            (A := AddCommGrpCat.{max w u})).map
              (fineQuotientMap fsum) = 𝟙 _ :=
        fineQuotientMap_pointFiber_eq_id_of_locally_eq_id
          F fsum x O hxO hlocal
      calc
        (∑ i ∈ s,
          ((Opens.pointGrothendieckTopology x).sheafFiber
            (A := AddCommGrpCat.{max w u})).map
              (fineQuotientMap (φ i))) =
            ((Opens.pointGrothendieckTopology x).sheafFiber
              (A := AddCommGrpCat.{max w u})).map
                (∑ i ∈ s, fineQuotientMap (φ i)) := by
                  exact
                    (CategoryTheory.Functor.map_sum
                      ((Opens.pointGrothendieckTopology x).sheafFiber
                        (A := AddCommGrpCat.{max w u}))
                      (fun i => fineQuotientMap (φ i)) s).symm
        _ = ((Opens.pointGrothendieckTopology x).sheafFiber
              (A := AddCommGrpCat.{max w u})).map
                (fineQuotientMap fsum) := by
                  apply congrArg
                  exact
                    (fineQuotientMap_sum F s φ).symm
        _ = 𝟙 _ := hid

/--
%%handwave
name:
  Restriction does not change a point fiber
statement:
  If $V\subseteq U$, $x\in V$, and $s\in\mathcal G(U)$, then the image of
  $s|_V$ in the fiber $\mathcal G_x$ equals the image of $s$.
proof:
  Apply the transition relation defining the colimit that forms the point
  fiber.
-/
theorem toPresheafFiber_restrict
    (G : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    {V U : Opens X} (i : V ⟶ U) (x : X)
    (hxV : x ∈ V) (hxU : x ∈ U)
    (s : G.obj.obj (op U)) :
    (Opens.pointGrothendieckTopology x).toPresheafFiber
        V ⟨⟨hxV⟩⟩ G.obj (G.obj.map i.op s) =
      (Opens.pointGrothendieckTopology x).toPresheafFiber
        U ⟨⟨hxU⟩⟩ G.obj s := by
  let Φ := Opens.pointGrothendieckTopology x
  let hxVΦ : Φ.fiber.obj V := ⟨⟨hxV⟩⟩
  let hxUΦ : Φ.fiber.obj U := ⟨⟨hxU⟩⟩
  have h :=
    CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w_apply
      (Φ := Φ) i hxVΦ G.obj s
  change
    Φ.toPresheafFiber V hxVΦ G.obj (G.obj.map i.op s) =
      Φ.toPresheafFiber U hxUΦ G.obj s
  simpa only [Subsingleton.elim (Φ.fiber.map i hxVΦ) hxUΦ] using h

/--
%%handwave
name:
  Point fibers detect equality of sheaf sections
statement:
  If two sections $s,t\in\mathcal G(U)$ have equal images in
  $\mathcal G_x$ for every $x\in U$, then $s=t$.
proof:
  Equality in each point fiber yields equality after restriction to some
  neighborhood of the point.  Hence all germs agree, and the sheaf
  separation property gives equality.
-/
theorem section_eq_of_pointFiber_eq
    (G : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    (U : Opens X) (s t : G.obj.obj (op U))
    (h :
      ∀ (x : X) (hx : x ∈ U),
        (Opens.pointGrothendieckTopology x).toPresheafFiber
            U ⟨⟨hx⟩⟩ G.obj s =
          (Opens.pointGrothendieckTopology x).toPresheafFiber
            U ⟨⟨hx⟩⟩ G.obj t) :
    s = t := by
  choose V i y hy hres using
    fun z : U =>
      ((Opens.pointGrothendieckTopology z.1).toPresheafFiber_eq_iff'
        U ⟨⟨z.2⟩⟩ s t).mp (h z.1 z.2)
  apply G.eq_of_locally_eq' V U i
  · intro x hx
    rw [Opens.mem_iSup]
    exact ⟨⟨x, hx⟩, (y ⟨x, hx⟩).down.down⟩
  · exact hres

/--
%%handwave
name:
  Fine-quotient sections lift locally
statement:
  Let $\mathcal F\to D(\mathcal F)\to\mathcal Q(\mathcal F)$ be the
  discontinuous-sections cokernel sequence.  Given
  $q\in\mathcal Q(\mathcal F)(U)$ and $x\in U$, there is an open
  neighborhood $V\subseteq U$ of $x$ on which $q|_V$ lifts to a section of
  $D(\mathcal F)$.
proof:
  The point-fiber functor is a left adjoint, hence preserves the epimorphic
  cokernel projection.  Lift the fiber of $q$ at $x$, represent that lifted
  fiber by a section on a neighborhood, and use equality in the filtered
  colimit defining the point fiber to shrink until the two representatives
  agree.
-/
theorem fineQuotient_exists_local_lift
    (F : TopCat.Sheaf.{u, max w u, max w u + 1}
      AddCommGrpCat.{max w u} X)
    (U : Opens X) (q : (fineQuotient F).obj.obj (op U))
    (x : X) (hxU : x ∈ U) :
    ∃ (V : Opens X) (i : V ⟶ U)
      (t : (discontinuousSheaf F).obj.obj (op V)),
      (cokernel.π (toDiscontinuousSheaf F)).hom.app (op V) t =
          (fineQuotient F).obj.map i.op q ∧
        x ∈ V := by
  let Φ := Opens.pointGrothendieckTopology x
  let π : discontinuousSheaf F ⟶ fineQuotient F :=
    cokernel.π (toDiscontinuousSheaf F)
  let fiber :=
    Φ.sheafFiber (A := AddCommGrpCat.{max w u})
  haveI : Epi (fiber.map π) := by
    exact @Functor.map_epi _ _ _ _ fiber
      (Functor.preservesEpimorphisms_of_adjunction
        (Φ.skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max w u})))
      _ _ π (by
        dsimp [π]
        exact fineQuotientProjection_epi F)
  have hsurj : Function.Surjective (fiber.map π) := by
    exact (AddCommGrpCat.epi_iff_surjective (fiber.map π)).mp inferInstance
  let qx : fiber.obj (fineQuotient F) :=
    Φ.toPresheafFiber U ⟨⟨hxU⟩⟩ (fineQuotient F).obj q
  obtain ⟨d, hd⟩ := hsurj qx
  obtain ⟨W, hxWΦ, t, ht⟩ :=
    Φ.toPresheafFiber_jointly_surjective
      (A := AddCommGrpCat.{max w u})
      (P := (discontinuousSheaf F).obj) d
  have hxW : x ∈ W := hxWΦ.down.down
  let W₀ : Opens X := W ⊓ U
  let jW : W₀ ⟶ W := homOfLE inf_le_left
  let jU : W₀ ⟶ U := homOfLE inf_le_right
  have hxW₀ : x ∈ W₀ := ⟨hxW, hxU⟩
  let hxW₀Φ : Φ.fiber.obj W₀ := ⟨⟨hxW₀⟩⟩
  let t₀ : (discontinuousSheaf F).obj.obj (op W₀) :=
    (discontinuousSheaf F).obj.map jW.op t
  have ht₀ :
      Φ.toPresheafFiber W₀ hxW₀Φ
          (discontinuousSheaf F).obj t₀ = d := by
    calc
      Φ.toPresheafFiber W₀ hxW₀Φ
          (discontinuousSheaf F).obj t₀ =
        Φ.toPresheafFiber W hxWΦ
          (discontinuousSheaf F).obj t := by
            have h :=
              CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w_apply
                (Φ := Φ) jW hxW₀Φ (discontinuousSheaf F).obj t
            simpa only [
              Subsingleton.elim (Φ.fiber.map jW hxW₀Φ) hxWΦ] using h
      _ = d := ht
  have hq₀ :
      Φ.toPresheafFiber W₀ hxW₀Φ (fineQuotient F).obj
          ((fineQuotient F).obj.map jU.op q) = qx := by
    have h :=
      CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w_apply
        (Φ := Φ) jU hxW₀Φ (fineQuotient F).obj q
    simpa only [
      Subsingleton.elim (Φ.fiber.map jU hxW₀Φ) ⟨⟨hxU⟩⟩] using h
  have heqFiber :
      Φ.toPresheafFiber W₀ hxW₀Φ (fineQuotient F).obj
          (π.hom.app (op W₀) t₀) =
        Φ.toPresheafFiber W₀ hxW₀Φ (fineQuotient F).obj
          ((fineQuotient F).obj.map jU.op q) := by
    rw [hq₀]
    calc
      Φ.toPresheafFiber W₀ hxW₀Φ (fineQuotient F).obj
          (π.hom.app (op W₀) t₀) =
        fiber.map π
          (Φ.toPresheafFiber W₀ hxW₀Φ
            (discontinuousSheaf F).obj t₀) :=
        (CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_apply
          (Φ := Φ) π.hom W₀ hxW₀Φ t₀).symm
      _ = fiber.map π d := by rw [ht₀]
      _ = qx := hd
  rcases
      (Φ.toPresheafFiber_eq_iff' W₀ hxW₀Φ
        (π.hom.app (op W₀) t₀)
        ((fineQuotient F).obj.map jU.op q)).mp heqFiber with
    ⟨V, k, y, _hy, hres⟩
  let i : V ⟶ U := k ≫ jU
  let lift : (discontinuousSheaf F).obj.obj (op V) :=
    (discontinuousSheaf F).obj.map k.op t₀
  refine ⟨V, i, lift, ?_, y.down.down⟩
  calc
    π.hom.app (op V) lift =
        (fineQuotient F).obj.map k.op
          (π.hom.app (op W₀) t₀) := by
      simpa only [lift, ConcreteCategory.comp_apply] using
        (ConcreteCategory.congr_hom
          (π.hom.naturality k.op) t₀)
    _ = (fineQuotient F).obj.map k.op
          ((fineQuotient F).obj.map jU.op q) := by rw [hres]
    _ = (fineQuotient F).obj.map i.op q := by
      simp only [i, op_comp, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp]

/--
%%handwave
name:
  Fine quotients lift global sections
statement:
  If $\mathcal F$ is fine on a paracompact Hausdorff space, every global
  section of $\mathcal Q(\mathcal F)$ lifts to a global discontinuous section.
proof:
  Lift the quotient section locally, shrink the resulting cover, and choose
  a subordinate fine partition $(\varphi_i)$.  Apply $\varphi_i$ to each
  local lift, extend the resulting pointwise family by zero, and sum the
  locally finite family.  On every point fiber its image is
  $\sum_i\varphi_i$ applied to the original quotient section, hence is the
  original section.
-/
theorem fineQuotient_top_app_surjective
    [T2Space X] [ParacompactSpace X]
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    [IsFine F] :
    Function.Surjective
      ((cokernel.π (toDiscontinuousSheaf F)).hom.app
        (op (⊤ : Opens X))) := by
  intro q
  classical
  let π :
      discontinuousSheaf F ⟶ fineQuotient F :=
    cokernel.π (toDiscontinuousSheaf F)
  have hlift :
      ∀ x : X,
        ∃ (O : Opens X) (_ : O ≤ ⊤),
          (∃ t : (discontinuousSheaf F).obj.obj (op O),
            π.hom.app (op O) t =
              (fineQuotient F).obj.map
                (homOfLE (show O ≤ (⊤ : Opens X) from le_top)).op q) ∧
          x ∈ O := by
    intro x
    rcases fineQuotient_exists_local_lift
        F (⊤ : Opens X) q x (by trivial) with
      ⟨O, i, t, ht, hxO⟩
    refine ⟨O, i.le, ⟨t, ?_⟩, hxO⟩
    simpa only [π, Subsingleton.elim i (homOfLE i.le)] using ht
  choose O hO using hlift
  choose hOtop hrest using hO
  choose t ht using fun x => (hrest x).1
  have hxO : ∀ x : X, x ∈ O x := fun x => (hrest x).2
  rcases
      existsLocallyFiniteOpenShrinkingOfCover O
        (fun x => ⟨x, hxO x⟩) with
    ⟨W, hWOclosure, hWfinite, hWcover⟩
  rcases
      IsFine.exists_subordinate_partition
        (F := F) W hWfinite hWcover with
    ⟨φ, hφsupport, hφpartition⟩
  let piece :
      X → (discontinuousSheaf F).obj.obj
        (op (⊤ : Opens X)) :=
    fun i y =>
      if hy : y.1 ∈ O i then
        ((Opens.pointGrothendieckTopology y.1).presheafFiber
          (A := AddCommGrpCat.{max w u})).map (φ i).hom
            (t i ⟨y.1, hy⟩)
      else 0
  let activeFinite (y : X) :
      ({i : X | y ∈ W i} : Set X).Finite :=
    hWfinite.point_finite y
  let active (y : X) : Finset X :=
    (activeFinite y).toFinset
  let lift :
      (discontinuousSheaf F).obj.obj
        (op (⊤ : Opens X)) :=
    fun y => ∑ i ∈ active y.1, piece i y
  refine ⟨lift, ?_⟩
  apply
    section_eq_of_pointFiber_eq
      (fineQuotient F) (⊤ : Opens X)
  intro x hxTop
  let Φ := Opens.pointGrothendieckTopology x
  rcases hWfinite x with ⟨T, hTnhds, hTfinite⟩
  rcases mem_nhds_iff.mp hTnhds with
    ⟨Nset, hNT, hNopen, hxN⟩
  let N : Opens X := ⟨Nset, hNopen⟩
  let s : Finset X := hTfinite.toFinset
  have hactive_subset :
      ∀ {y : X}, y ∈ N → active y ⊆ s := by
    intro y hyN i hi
    apply hTfinite.mem_toFinset.mpr
    have hiW : y ∈ W i :=
      (activeFinite y).mem_toFinset.mp hi
    exact ⟨y, hiW, hNT hyN⟩
  have hpiece_zero :
      ∀ {i y : X}, y ∉ W i →
        piece i ⟨y, (show y ∈ (⊤ : Opens X) by trivial)⟩ = 0 := by
    intro i y hyW
    have hmap :
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map (φ i).hom = 0 := by
      apply not_ne_iff.mp
      intro hne
      exact hyW (hφsupport i hne)
    by_cases hyO : y ∈ O i
    · simp only [piece, dif_pos hyO]
      rw [hmap]
      exact
        (0 : discontinuousFiber F y ⟶ discontinuousFiber F y).hom.map_zero
    · simp [piece, hyO]
  let pieceSum :
      (discontinuousSheaf F).obj.obj
        (op (⊤ : Opens X)) :=
    ∑ i ∈ s, piece i
  have hlift_local :
      (discontinuousSheaf F).obj.map
          (homOfLE (show N ≤ (⊤ : Opens X) from le_top)).op lift =
        (discontinuousSheaf F).obj.map
          (homOfLE (show N ≤ (⊤ : Opens X) from le_top)).op pieceSum := by
    funext y
    change
      lift ⟨y.1, (by simp)⟩ =
        pieceSum ⟨y.1, (by simp)⟩
    dsimp only [lift, pieceSum]
    let ytop : (⊤ : Opens X) := ⟨y.1, by trivial⟩
    have heval (r : Finset X) :
        (∑ i ∈ r, piece i) ytop =
          ∑ i ∈ r, piece i ytop := by
      induction r using Finset.induction_on with
      | empty =>
          change (0 : discontinuousFiber F y.1) = 0
          rfl
      | @insert i r hi ihr =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          change
            piece i ytop +
                (∑ j ∈ r, piece j) ytop =
              piece i ytop + ∑ j ∈ r, piece j ytop
          rw [ihr]
    rw [heval]
    apply Finset.sum_subset (hactive_subset y.2)
    intro i _his hiActive
    have hiW : y.1 ∉ W i := by
      intro hiW
      apply hiActive
      exact (activeFinite y.1).mem_toFinset.mpr hiW
    exact hpiece_zero hiW
  have hlift_germ :
      Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
          (discontinuousSheaf F).obj lift =
        Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
          (discontinuousSheaf F).obj pieceSum := by
    rw [← toPresheafFiber_restrict
          (discontinuousSheaf F)
          (homOfLE (show N ≤ (⊤ : Opens X) from le_top))
          x hxN hxTop lift,
      ← toPresheafFiber_restrict
          (discontinuousSheaf F)
          (homOfLE (show N ≤ (⊤ : Opens X) from le_top))
          x hxN hxTop pieceSum,
      hlift_local]
  have hpiece :
      ∀ i : X,
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map π
            (Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
              (discontinuousSheaf F).obj (piece i)) =
          (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
              (fineQuotientMap (φ i))
            (Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
              (fineQuotient F).obj q) := by
    intro i
    by_cases hxclosure : x ∈ closure (W i : Set X)
    · have hxOi : x ∈ O i := hWOclosure i hxclosure
      let iOtop : O i ⟶ (⊤ : Opens X) :=
        homOfLE (hOtop i)
      have hpiece_restrict :
          (discontinuousSheaf F).obj.map iOtop.op (piece i) =
            (discontinuousSheafMap (φ i)).hom.app
              (op (O i)) (t i) := by
        funext y
        change
          piece i ⟨y.1, (hOtop i y.2)⟩ =
            ((Opens.pointGrothendieckTopology y.1).presheafFiber
              (A := AddCommGrpCat.{max w u})).map (φ i).hom (t i y)
        simp [piece, y.2]
      have hpiece_germ :
          Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
              (discontinuousSheaf F).obj (piece i) =
            Φ.toPresheafFiber (O i) ⟨⟨hxOi⟩⟩
              (discontinuousSheaf F).obj
              ((discontinuousSheafMap (φ i)).hom.app
                (op (O i)) (t i)) := by
        rw [← toPresheafFiber_restrict
              (discontinuousSheaf F) iOtop
              x hxOi hxTop (piece i),
          hpiece_restrict]
      have hπφ :
          π.hom.app (op (O i))
              ((discontinuousSheafMap (φ i)).hom.app
                (op (O i)) (t i)) =
            (fineQuotientMap (φ i)).hom.app
              (op (O i)) (π.hom.app (op (O i)) (t i)) := by
        have hcomp :=
          congrArg
            (fun k =>
              k.hom.app (op (O i)))
            (fineQuotient_π_naturality
              (F := F) (G := F) (φ i))
        exact
          (ConcreteCategory.congr_hom hcomp (t i)).symm
      have hπt :
          π.hom.app (op (O i)) (t i) =
            (fineQuotient F).obj.map iOtop.op q := by
        simpa [π, iOtop] using ht i
      have h₁ :=
        congrArg
          (fun z =>
            (ConcreteCategory.hom
              ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map π)) z)
          hpiece_germ
      have h₂ :=
        CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_apply
          (Φ := Φ) π.hom (O i) ⟨⟨hxOi⟩⟩
          ((discontinuousSheafMap (φ i)).hom.app
            (op (O i)) (t i))
      have h₃ :=
        congrArg
          (fun z =>
            Φ.toPresheafFiber (O i) ⟨⟨hxOi⟩⟩
              (fineQuotient F).obj z)
          hπφ
      have h₄ :=
        (CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_apply
          (Φ := Φ) (fineQuotientMap (φ i)).hom
          (O i) ⟨⟨hxOi⟩⟩
          (π.hom.app (op (O i)) (t i))).symm
      have h₅ :=
        congrArg
          (fun z =>
            (ConcreteCategory.hom
              ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
                (fineQuotientMap (φ i)))) z)
          (congrArg
            (fun z =>
              Φ.toPresheafFiber (O i) ⟨⟨hxOi⟩⟩
                (fineQuotient F).obj z)
            hπt)
      have h₆ :=
        congrArg
          (fun z =>
            (ConcreteCategory.hom
              ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
                (fineQuotientMap (φ i)))) z)
          (toPresheafFiber_restrict
            (fineQuotient F) iOtop x hxOi hxTop q)
      exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))
    · let C : Opens X :=
        ⟨(closure (W i : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
      have hxC : x ∈ C := hxclosure
      let iCtop : C ⟶ (⊤ : Opens X) :=
        homOfLE le_top
      have hpiece_restrict_zero :
          (discontinuousSheaf F).obj.map iCtop.op
              (piece i) = 0 := by
        funext y
        change piece i ⟨y.1, (by trivial)⟩ = 0
        apply hpiece_zero
        intro hyW
        exact y.2 (subset_closure hyW)
      have hpiece_germ_zero :
          Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
              (discontinuousSheaf F).obj (piece i) = 0 := by
        rw [← toPresheafFiber_restrict
              (discontinuousSheaf F) iCtop
              x hxC hxTop (piece i),
          hpiece_restrict_zero]
        simp
      have hqmap :
          (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
              (fineQuotientMap (φ i)) = 0 := by
        apply not_ne_iff.mp
        intro hne
        have hxclosureSupport :
            x ∈ closure (endomorphismGermSupport F (φ i)) :=
          fineQuotientMap_germSupport_subset_closure
            F (φ i) hne
        exact hxclosure
          (closure_mono (hφsupport i) hxclosureSupport)
      rw [hpiece_germ_zero, hqmap]
      exact
        ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map π).hom.map_zero
  have hnotW :
      ∀ {i : X}, i ∉ s → ∀ {y : X}, y ∈ N → y ∉ W i := by
    intro i hi y hyN hyW
    apply hi
    apply hTfinite.mem_toFinset.mpr
    exact ⟨y, hyW, hNT hyN⟩
  let fsum : F ⟶ F := ∑ i ∈ s, φ i
  have hlocalF :
      ∀ y : X, y ∈ N →
        ((Opens.pointGrothendieckTopology y).presheafFiber
          (A := AddCommGrpCat.{max w u})).map fsum.hom = 𝟙 _ := by
    intro y hyN
    let Ψ := Opens.pointGrothendieckTopology y
    rcases hφpartition y with ⟨r, hrzero, hrsum⟩
    let a : X →
        ((Ψ.sheafFiber (A := AddCommGrpCat.{max w u})).obj F ⟶
          (Ψ.sheafFiber (A := AddCommGrpCat.{max w u})).obj F) :=
      fun i => (Ψ.sheafFiber
        (A := AddCommGrpCat.{max w u})).map (φ i)
    have hzeroS : ∀ i, i ∉ s → a i = 0 := by
      intro i hi
      apply not_ne_iff.mp
      intro hne
      exact hnotW hi hyN (hφsupport i hne)
    have hsumEq :
        (∑ i ∈ s, a i) = ∑ i ∈ r, a i := by
      calc
        (∑ i ∈ s, a i) =
            ∑ i ∈ s ∪ r, a i :=
          Finset.sum_subset Finset.subset_union_left
            (by
              intro i _hiUnion hi
              exact hzeroS i hi)
        _ = ∑ i ∈ r, a i :=
          (Finset.sum_subset Finset.subset_union_right
            (by
              intro i _hiUnion hi
              exact hrzero i hi)).symm
    change
      (Ψ.sheafFiber (A := AddCommGrpCat.{max w u})).map fsum = 𝟙 _
    dsimp only [fsum]
    calc
      (Ψ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (∑ i ∈ s, φ i) =
          ∑ i ∈ s, a i :=
        CategoryTheory.Functor.map_sum
          (Ψ.sheafFiber (A := AddCommGrpCat.{max w u})) φ s
      _ = ∑ i ∈ r, a i := hsumEq
      _ = 𝟙 _ := hrsum
  have hQfsum :
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (fineQuotientMap fsum) = 𝟙 _ :=
    fineQuotientMap_pointFiber_eq_id_of_locally_eq_id
      F fsum x N hxN hlocalF
  have hQsum :
      (∑ i ∈ s,
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (fineQuotientMap (φ i))) = 𝟙 _ := by
    calc
      (∑ i ∈ s,
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (fineQuotientMap (φ i))) =
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (∑ i ∈ s, fineQuotientMap (φ i)) :=
        (CategoryTheory.Functor.map_sum
          (Φ.sheafFiber (A := AddCommGrpCat.{max w u}))
          (fun i => fineQuotientMap (φ i)) s).symm
      _ =
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (fineQuotientMap fsum) := by
            apply congrArg
            exact (fineQuotientMap_sum F s φ).symm
      _ = 𝟙 _ := hQfsum
  let dgerm :
      (discontinuousSheaf F).obj.obj
          (op (⊤ : Opens X)) →
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).obj
          (discontinuousSheaf F) :=
    fun z =>
      Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
        (discontinuousSheaf F).obj z
  let qgerm :
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).obj
        (fineQuotient F) :=
    Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
      (fineQuotient F).obj q
  let mapπx :
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).obj
          (discontinuousSheaf F) →
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).obj
          (fineQuotient F) :=
    (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map π
  let mapQx (i : X) :
      (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).obj
          (fineQuotient F) →
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).obj
          (fineQuotient F) :=
    (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
      (fineQuotientMap (φ i))
  have hgermPieceSum :
      dgerm pieceSum = ∑ i ∈ s, dgerm (piece i) := by
    dsimp only [dgerm, pieceSum]
    exact
      map_sum
        (Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
          (discontinuousSheaf F).obj).hom piece s
  have hsumApply :
      (∑ i ∈ s,
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (fineQuotientMap (φ i))) qgerm =
        ∑ i ∈ s, mapQx i qgerm := by
    induction s using Finset.induction_on with
    | empty =>
        change (0 :
          (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).obj
            (fineQuotient F)) = 0
        rfl
    | @insert i r hi ihr =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        change
          mapQx i qgerm +
              (∑ j ∈ r,
                (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
                  (fineQuotientMap (φ j))) qgerm =
            mapQx i qgerm + ∑ j ∈ r, mapQx j qgerm
        rw [ihr]
  have hπnat :=
    (CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_apply
      (Φ := Φ) π.hom (⊤ : Opens X) ⟨⟨hxTop⟩⟩ lift).symm
  change
    Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
        (fineQuotient F).obj
        (π.hom.app (op (⊤ : Opens X)) lift) =
      qgerm
  calc
    Φ.toPresheafFiber (⊤ : Opens X) ⟨⟨hxTop⟩⟩
        (fineQuotient F).obj
        (π.hom.app (op (⊤ : Opens X)) lift) =
      mapπx (dgerm lift) := hπnat
    _ = mapπx (dgerm pieceSum) := congrArg mapπx hlift_germ
    _ = mapπx (∑ i ∈ s, dgerm (piece i)) := by
      rw [hgermPieceSum]
    _ = ∑ i ∈ s, mapπx (dgerm (piece i)) := by
      exact map_sum
        ((Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map π).hom
        (fun i => dgerm (piece i)) s
    _ = ∑ i ∈ s, mapQx i qgerm := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hpiece i
    _ =
      (∑ i ∈ s,
        (Φ.sheafFiber (A := AddCommGrpCat.{max w u})).map
          (fineQuotientMap (φ i))) qgerm := hsumApply.symm
    _ = qgerm := by
      rw [hQsum]
      rfl

/--
%%handwave
name:
  Fine quotients are surjective on global sections
statement:
  If $\mathcal F$ is fine on a paracompact Hausdorff space, the morphism
  $\Gamma(D(\mathcal F))\to\Gamma(\mathcal Q(\mathcal F))$ induced by the
  quotient projection is an epimorphism.
proof:
  Identify global sections with sections over the whole space.  Surjectivity
  there is the global lifting construction for the fine quotient, and
  epimorphisms of abelian groups are precisely surjective homomorphisms.
-/
theorem fineQuotient_globalSections_map_epi
    [T2Space X] [ParacompactSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w u}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{max w u}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w u}]
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    [IsFine F] :
    Epi
      ((CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X)
        AddCommGrpCat.{max w u}).map
        (cokernel.π (toDiscontinuousSheaf F))) := by
  let J := Opens.grothendieckTopology X
  let Γ :
      CategoryTheory.Sheaf J AddCommGrpCat.{max w u} ⥤ AddCommGrpCat.{max w u} :=
    CategoryTheory.Sheaf.Γ J AddCommGrpCat.{max w u}
  let sectionsTop :
      CategoryTheory.Sheaf J AddCommGrpCat.{max w u} ⥤ AddCommGrpCat.{max w u} :=
    (CategoryTheory.sheafSections J AddCommGrpCat.{max w u}).obj
      (op (⊤ : Opens X))
  let η : Γ ≅ sectionsTop :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{max w u})
      (T := (⊤ : Opens X))
      (CategoryTheory.Limits.isTerminalTop (α := Opens X))
  let π :
      discontinuousSheaf F ⟶ fineQuotient F :=
    cokernel.π (toDiscontinuousSheaf F)
  have hsections : Epi (sectionsTop.map π) := by
    change Epi (π.hom.app (op (⊤ : Opens X)))
    rw [AddCommGrpCat.epi_iff_surjective]
    exact fineQuotient_top_app_surjective F
  have hcomp : Epi (η.hom.app (discontinuousSheaf F) ≫
      sectionsTop.map π) := by
    haveI : Epi (η.hom.app (discontinuousSheaf F)) := inferInstance
    haveI : Epi (sectionsTop.map π) := hsections
    infer_instance
  have hnat :
      Γ.map π ≫ η.hom.app (fineQuotient F) =
        η.hom.app (discontinuousSheaf F) ≫
          sectionsTop.map π :=
    η.hom.naturality π
  have hΓcomp :
      Epi (Γ.map π ≫ η.hom.app (fineQuotient F)) := by
    rw [hnat]
    exact hcomp
  exact
    (epi_comp_iff_of_isIso
      (Γ.map π) (η.hom.app (fineQuotient F))).mp hΓcomp

/--
%%handwave
name:
  Fine sheaves are acyclic
statement:
  Let $X$ be a paracompact Hausdorff space and let $\mathcal F$ be a fine
  sheaf of abelian groups on $X$.  Then
  $H^q(X;\mathcal F)=0$ for every $q>0$.
proof:
  Use the short exact sequence
  $0\to\mathcal F\to D(\mathcal F)\to\mathcal Q(\mathcal F)\to0$.
  The middle sheaf is flasque, hence acyclic; the quotient is fine; and the
  map from its middle term is surjective on global sections.  The degree-one
  edge of the long exact sequence gives $H^1(X;\mathcal F)=0$.  In higher
  degrees the connecting isomorphism identifies
  $H^{q+1}(X;\mathcal F)$ with $H^q(X;\mathcal Q(\mathcal F))$, and strong
  induction completes the proof.
-/
theorem cohomology_subsingleton_of_isFine
    [T2Space X] [ParacompactSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w u}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{max w u}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w u}]
    [HasExt.{max w u}
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{max w u})]
    (F : TopCat.Sheaf.{u, max w u, max w u + 1} AddCommGrpCat.{max w u} X)
    [IsFine F] :
    ∀ q : ℕ, 0 < q → Subsingleton (F.H q) := by
  let J := Opens.grothendieckTopology X
  letI : IsGrothendieckAbelian.{max w u}
      (CategoryTheory.Sheaf J AddCommGrpCat.{max w u}) :=
    CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall
      J AddCommGrpCat.{max w u}
  suffices
      ∀ q : ℕ, 0 < q →
        ∀ (G : CategoryTheory.Sheaf J AddCommGrpCat.{max w u}),
          IsFine G →
          Subsingleton (G.H q) by
    intro q hq
    exact this q hq F inferInstance
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro hq G hG
      cases q with
      | zero =>
          exact (Nat.not_lt_zero 0 hq).elim
      | succ q =>
          let S :
              ShortComplex
                (CategoryTheory.Sheaf J AddCommGrpCat.{max w u}) :=
            ShortComplex.mk
              (toDiscontinuousSheaf G)
              (cokernel.π (toDiscontinuousSheaf G))
              (cokernel.condition (toDiscontinuousSheaf G))
          haveI hMono_left : Mono S.f := by
            dsimp [S]
            exact toDiscontinuousSheaf_mono G
          haveI hEpi_right : Epi S.g := by
            dsimp [S]
            exact CategoryTheory.Limits.coequalizer.π_epi
          have hS : S.ShortExact :=
            { exact :=
                ShortComplex.exact_cokernel
                  (toDiscontinuousSheaf G) }
          haveI hFine_left : IsFine S.X₁ := by
            dsimp [S]
            exact hG
          haveI hFlasque_middle :
              TopCat.Sheaf.IsFlasque S.X₂ := by
            dsimp [S]
            infer_instance
          haveI hFine_right : IsFine S.X₃ := by
            dsimp [S]
            infer_instance
          have hmiddle_acyclic :
              ∀ r : ℕ, 0 < r → Subsingleton (S.X₂.H r) :=
            JJMath.Cohomology.sheafCohomology_subsingleton_of_flasque
              (X := X) S.X₂
          cases q with
          | zero =>
              have hmiddle_one : Subsingleton (S.X₂.H 1) :=
                hmiddle_acyclic 1 (by norm_num)
              rcases
                CategoryTheory.Sheaf.nonempty_globalSections_cokernel_addEquiv_sheafCohomology_one_of_shortExact_middle_acyclic
                    (J := J) hS hmiddle_one with
                ⟨e⟩
              haveI hΓepi :
                  Epi
                    ((CategoryTheory.Sheaf.Γ J AddCommGrpCat.{max w u}).map
                      S.g) := by
                dsimp [S]
                exact fineQuotient_globalSections_map_epi G
              have hcoker :
                  IsZero
                    (cokernel
                      ((CategoryTheory.Sheaf.Γ J AddCommGrpCat.{max w u}).map
                        S.g)) :=
                isZero_cokernel_of_epi _
              haveI hcoker_subsingleton :
                  Subsingleton
                    (↥(cokernel
                      ((CategoryTheory.Sheaf.Γ J AddCommGrpCat.{max w u}).map
                        S.g))) :=
                AddCommGrpCat.subsingleton_of_isZero hcoker
              change Subsingleton (S.X₁.H 1)
              exact
                ⟨fun x y => by
                  apply e.symm.injective
                  exact Subsingleton.elim _ _⟩
          | succ q =>
              have hright :
                  Subsingleton (S.X₃.H (q + 1)) :=
                ih (q + 1) (by omega) (Nat.succ_pos q)
                  S.X₃ inferInstance
              let e :=
                CategoryTheory.Sheaf.sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos
                    (J := J) hS hmiddle_acyclic
                    (q + 1) (Nat.succ_pos q)
              change Subsingleton (S.X₁.H ((q + 1) + 1))
              exact
                ⟨fun x y => by
                  apply e.symm.injective
                  exact Subsingleton.elim _ _⟩

end TopCat.Sheaf
